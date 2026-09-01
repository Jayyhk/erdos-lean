import Mathlib

set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.commandStart false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos659

attribute [local fun_prop] Real.continuous_fourierChar
attribute [local fun_prop] measurable_coe_nnreal_ennreal

/-
# Problem Description

Erdős Problem 659. Is there a set of `n` points in `ℝ²` such that every subset of `4` points
determines at least `3` distances, yet the total number of distinct distances is
`≪ n / √(log n)`? `erdos_659` answers this in the affirmative.

`erdos_659` is proved unconditionally here: Bernays' theorem on the number of integers up
to `x` represented by a primitive positive-definite binary quadratic form of non-square
discriminant, previously assumed in this repository as `bernays`, is now a theorem —
`Bernays.bernays_theorem` from the vendored `Util.Bernays` development. Its statement is
kept exactly as this repository had it.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos659.lean` with `Erdos659/Geometry.lean` and the
`src/latest/Util/Bernays` development; the geometric argument is Aristotle's, with Boris
Alexeev, and the unconditional Bernays proof is by Codex. It vendors six smoothing modules
from `PrimeNumberTheoremAnd` and uses no `BoundedGaps`. This replaces the repository's
previous copy of the same geometric argument, which was written against Lean 4.24 and no
longer elaborates on 4.33; the final statement is unchanged.

Flattened single-file vendoring of the 157-module import closure, in dependency order, with
project-internal imports removed so that `Mathlib` is the only import, each module wrapped
in its own `section` with any end-of-file scopes closed explicitly. Declarations keep their
upstream names; those that upstream declares into Mathlib's own `Set` namespace are emitted
with explicit `_root_.Set.` prefixes. The outer `Erdos659` namespace is stripped from the
modules that carry it, since the whole file is wrapped in it once. No mathematical content
is changed.
-/

/-! ### Upstream module `Util/Bernays/FiniteCutoffError.lean` -/

section
/-!
# A finite sharp-cutoff error bound for complex coefficients
-/

open scoped Classical

namespace Bernays

theorem sum_subset_eq_indicator {α E : Type*} [DecidableEq α] [AddCommMonoid E]
    (A B : Finset α) (hAB : A ⊆ B) (a : α → E) :
    (∑ x ∈ A, a x) = ∑ x ∈ B, if x ∈ A then a x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hAB h, h⟩, fun h => h.2⟩

theorem norm_mul_real_le {z : ℂ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖z * (r : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₀]
  exact mul_le_of_le_one_right (norm_nonneg z) hr₁

theorem norm_sub_mul_real_le {z : ℂ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖z - z * (r : ℂ)‖ ≤ ‖z‖ := by
  have hid : z - z * (r : ℂ) = z * ((1 - r : ℝ) : ℂ) := by push_cast; ring
  rw [hid]
  exact norm_mul_real_le (by linarith) (by linarith)

theorem finite_cutoff_error {α : Type*} [DecidableEq α] (A B S : Finset α) (hAB : A ⊆ B) (hSB : S ⊆ B)
    (a : α → ℂ) (r : α → ℝ)
    (hr : ∀ x ∈ B, 0 ≤ r x ∧ r x ≤ 1)
    (hone : ∀ x ∈ A, x ∉ S → r x = 1) :
    ‖(∑ x ∈ A, a x) - ∑ x ∈ B, a x * (r x : ℂ)‖ ≤
      (∑ x ∈ S, ‖a x‖) + ∑ x ∈ B \ A, ‖a x‖ := by
  rw [sum_subset_eq_indicator A B hAB, ← Finset.sum_sub_distrib,
    sum_subset_eq_indicator S B hSB,
    sum_subset_eq_indicator (B \ A) B Finset.sdiff_subset, ← Finset.sum_add_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hr₀, hr₁⟩ := hr x hx
  by_cases hxA : x ∈ A
  · have hxBA : x ∉ B \ A := by simp [hxA]
    rw [if_pos hxA, if_neg hxBA, add_zero]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS]
      exact norm_sub_mul_real_le hr₀ hr₁
    · rw [if_neg hxS, hone x hxA hxS, Complex.ofReal_one, mul_one, sub_self, norm_zero]
  · have hxBA : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
    rw [if_neg hxA, if_pos hxBA, zero_sub, norm_neg]
    apply (norm_mul_real_le hr₀ hr₁).trans
    exact le_add_of_nonneg_left (by split_ifs <;> positivity)

end Bernays

end

/-! ### Upstream module `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` -/

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

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end

end

/-! ### Upstream module `PrimeNumberTheoremAnd/Sobolev.lean` -/

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

/-! ### Upstream module `PrimeNumberTheoremAnd/Fourier.lean` -/

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

/-! ### Upstream module `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` -/

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

/-! ### Upstream module `PrimeNumberTheoremAnd/SmoothExistence.lean` -/

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

/-! ### Upstream module `PrimeNumberTheoremAnd/Wiener.lean` -/

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
    convert (nnabla_bound C hx).natCast_atTop ; simp [nnabla, a]   -- `IsBigO.natCast` was renamed `natCast_atTop`

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
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
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
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

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
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
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
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
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
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
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
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
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

/-! ### Upstream module `Util/Bernays/CharacterPrimeDistribution.lean` -/

section
/-!
# Character-weighted prime distribution

The already proved PNT in arithmetic progressions and character orthogonality
give cancellation of the character-twisted Mangoldt sum. No prime-distribution
statement is assumed in this module.
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem character_sum_by_residues {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ Finset.range X, χ n * w n) =
      ∑ a : ZMod q, χ a * ∑ n ∈ Finset.range X, if n % q = a.val then w n else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  symm
  rw [Finset.sum_eq_single (n : ZMod q)]
  · simp only [ZMod.val_natCast, ite_true]
  · intro a _ ha
    have hne : n % q ≠ a.val := by
      intro h
      apply ha
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using h.symm
    rw [if_neg hne, mul_zero]
  · simp

theorem twistedMangoldt_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.range X, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) / (X : ℂ))
      atTop (𝓝 0) := by
  have hterm (a : ZMod q) :
      Tendsto (fun X : ℕ => χ a *
        ((∑ n ∈ Finset.range X,
          if n % q = a.val then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) / (X : ℂ)))
        atTop (𝓝 (χ a * ((1 / (q.totient : ℝ) : ℝ) : ℂ))) := by
    by_cases ha : IsUnit a
    · have hcop : a.val.Coprime q := (ZMod.isUnit_iff_coprime a.val q).mp (by simpa using ha)
      have hAP := WeakPNT_AP (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hcop (ZMod.val_lt a)
      have hc : Tendsto (fun X : ℕ =>
          ((cumsum (fun n => if n % q = a.val then ArithmeticFunction.vonMangoldt n else 0) X /
            (X : ℝ) : ℝ) : ℂ)) atTop (𝓝 ((1 / (q.totient : ℝ) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hAP
      have hm := hc.const_mul (χ a)
      simpa only [cumsum, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hm
    · have hzero : χ a = 0 := χ.map_nonunit ha
      simp only [hzero, zero_mul]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => hterm a)
  have horth : (∑ a : ZMod q, χ a * ((1 / (q.totient : ℝ) : ℝ) : ℂ)) = 0 := by
    rw [← Finset.sum_mul, χ.sum_eq_zero_of_ne_one hχ, zero_mul]
  rw [horth] at hsum
  apply hsum.congr'
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  rw [character_sum_by_residues χ (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) X,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem realTwistedMangoldt_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.range X, (χ n).re * ArithmeticFunction.vonMangoldt n) / (X : ℝ))
      atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (twistedMangoldt_div_tendsto_zero χ hχ)
  simpa only [Function.comp_def, Complex.zero_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/Moments.lean` -/

section
/-!
# Compact moment convergence

The polynomial approximation step in the Laplace Tauberian argument: convergence
of all moments on a compact interval implies weak convergence of finite measures.
In particular no density theorem for the arithmetic sequence is assumed here.
-/

open MeasureTheory Filter Topology
open scoped unitInterval

namespace Bernays

private theorem continuous_integrable (μ : FiniteMeasure I) (g : C(I, ℝ)) :
    Integrable g (μ : Measure I) :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem integral_continuousMap_sub_le (μ : FiniteMeasure I) (f g : C(I, ℝ)) :
    |(∫ x, f x ∂(μ : Measure I)) - ∫ x, g x ∂(μ : Measure I)| ≤
      ‖f - g‖ * (μ : Measure I).real Set.univ := by
  rw [← integral_sub (continuous_integrable μ f) (continuous_integrable μ g), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun x => (f - g).norm_coe_le_norm x)

theorem polynomial_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I)))) (p : Polynomial ℝ) :
    Tendsto (fun i => ∫ x : I, p.eval (x : ℝ) ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, p.eval (x : ℝ) ∂(ν : Measure I))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd (ρ : FiniteMeasure I) :
          (∫ x : I, (p + q).eval (x : ℝ) ∂(ρ : Measure I)) =
            (∫ x : I, p.eval (x : ℝ) ∂(ρ : Measure I)) +
            ∫ x : I, q.eval (x : ℝ) ∂(ρ : Measure I) := by
        simpa only [Polynomial.eval_add, Polynomial.toContinuousMapOn_apply,
          Polynomial.toContinuousMap_apply] using
          integral_add (continuous_integrable ρ (p.toContinuousMapOn I))
            (continuous_integrable ρ (q.toContinuousMapOn I))
      simpa only [hadd] using hp.add hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial, integral_const_mul]
      exact (h n).const_mul a

theorem continuous_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I)))) (g : C(I, ℝ)) :
    Tendsto (fun i => ∫ x, g x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, g x ∂(ν : Measure I))) := by
  have hmass := h 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at hmass
  let M : ℝ := (ν : Measure I).real Set.univ + 1
  have hν : 0 ≤ (ν : Measure I).real Set.univ := measureReal_nonneg
  have hM : 0 < M := add_pos_of_nonneg_of_pos hν zero_lt_one
  have hmass_bound : ∀ᶠ i in l, (μ i : Measure I).real Set.univ < M :=
    hmass.eventually (gt_mem_nhds (lt_add_one _))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (M + 1) = ε / 4 := by
    dsimp [δ]
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ (by linarith : M + 1 ≠ 0)]
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 g δ hδ
  let P : C(I, ℝ) := p.toContinuousMapOn I
  have hP : ‖P - g‖ < δ := hp
  have hpoly := polynomial_integral_tendsto_of_moments h p
  have hpoly_bound := (Metric.tendsto_nhds.mp hpoly) (ε / 2) (half_pos hε)
  filter_upwards [hmass_bound, hpoly_bound] with i hi hpi
  rw [Real.dist_eq] at hpi ⊢
  have hleft : |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, P x ∂(μ i : Measure I)| ≤ δ * M := by
    refine (integral_continuousMap_sub_le (μ i) g P).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul hP.le hi.le measureReal_nonneg hδ.le
  have hright : |(∫ x, P x ∂(ν : Measure I)) - ∫ x, g x ∂(ν : Measure I)| ≤ δ * M := by
    refine (integral_continuousMap_sub_le ν P g).trans ?_
    exact mul_le_mul hP.le (le_add_of_nonneg_right zero_le_one) hν hδ.le
  have htri :
      |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, g x ∂(ν : Measure I)| ≤
        |(∫ x, g x ∂(μ i : Measure I)) - ∫ x, P x ∂(μ i : Measure I)| +
        |(∫ x, P x ∂(μ i : Measure I)) - ∫ x, P x ∂(ν : Measure I)| +
        |(∫ x, P x ∂(ν : Measure I)) - ∫ x, g x ∂(ν : Measure I)| := by
    linarith [abs_sub_le (∫ x, g x ∂(μ i : Measure I))
      (∫ x, P x ∂(μ i : Measure I)) (∫ x, g x ∂(ν : Measure I)),
      abs_sub_le (∫ x, P x ∂(μ i : Measure I))
        (∫ x, P x ∂(ν : Measure I)) (∫ x, g x ∂(ν : Measure I))]
  change |(∫ x, P x ∂(μ i : Measure I)) - ∫ x, P x ∂(ν : Measure I)| < ε / 2 at hpi
  nlinarith

end Bernays

end

/-! ### Upstream module `Util/Bernays/CutoffConvergence.lean` -/

section
/-!
# Passing compact moment convergence through a cutoff

Continuous ramps above and below a cutoff allow its integral to pass to the
limit whenever the limiting measure has no atom at the cutoff.
-/

open MeasureTheory Filter Topology
open scoped unitInterval

namespace Bernays

theorem integral_tendsto_of_continuous_sandwich {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (hμ : ∀ g : C(I, ℝ), Tendsto (fun i => ∫ x, g x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, g x ∂(ν : Measure I))))
    {f : I → ℝ} (hf : ∀ i, Integrable f (μ i : Measure I))
    (L U : ℕ → C(I, ℝ)) (hL : ∀ n x, L n x ≤ f x) (hU : ∀ n x, f x ≤ U n x)
    {c : ℝ}
    (hLc : Tendsto (fun n => ∫ x, L n x ∂(ν : Measure I)) atTop (𝓝 c))
    (hUc : Tendsto (fun n => ∫ x, U n x ∂(ν : Measure I)) atTop (𝓝 c)) :
    Tendsto (fun i => ∫ x, f x ∂(μ i : Measure I)) l (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨n, hn⟩ := (hLc.eventually (lt_mem_nhds hb)).exists
    filter_upwards [(hμ (L n)).eventually (lt_mem_nhds hn)] with i hi
    exact hi.trans_le (integral_mono
      ((L n).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (hf i) (hL n))
  · intro b hb
    obtain ⟨n, hn⟩ := (hUc.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hμ (U n)).eventually (gt_mem_nhds hn)] with i hi
    exact (integral_mono (hf i)
      ((U n).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (hU n)).trans_lt hi

/-- A continuous approximation to the indicator of the positive half-line. -/
def ramp (n : ℕ) (t : ℝ) : ℝ := min 1 (max 0 ((n : ℝ) * t))

theorem ramp_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ramp n t :=
  le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (n : ℕ) (t : ℝ) : ramp n t ≤ 1 := min_le_left _ _

theorem ramp_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) : ramp n t = 0 := by
  rw [ramp, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht)]
  norm_num

theorem ramp_eq_one {n : ℕ} {t : ℝ} (ht : 1 ≤ (n : ℝ) * t) : ramp n t = 1 := by
  rw [ramp, max_eq_right (zero_le_one.trans ht), min_eq_left ht]

theorem continuous_ramp (n : ℕ) : Continuous (ramp n) := by
  unfold ramp
  fun_prop

theorem ramp_tendsto_of_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ramp n t) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (1 / t))] with n hn
  exact (ramp_eq_one ((div_le_iff₀ ht).mp hn)).symm

def lowerCutoff (g : C(I, ℝ)) (a : ℝ) (n : ℕ) : C(I, ℝ) where
  toFun x := g x * ramp n ((x : ℝ) - a)
  continuous_toFun := g.continuous.mul
    ((continuous_ramp n).comp (continuous_subtype_val.sub continuous_const))

def upperCutoff (g : C(I, ℝ)) (a : ℝ) (n : ℕ) : C(I, ℝ) where
  toFun x := g x * (1 - ramp n (a - (x : ℝ)))
  continuous_toFun := g.continuous.mul
    (continuous_const.sub ((continuous_ramp n).comp (continuous_const.sub continuous_subtype_val)))

noncomputable def cutoff (g : C(I, ℝ)) (a : ℝ) (x : I) : ℝ :=
  if a ≤ (x : ℝ) then g x else 0

theorem lowerCutoff_le_cutoff {g : C(I, ℝ)} (hg : ∀ x, 0 ≤ g x) (a : ℝ) (n : ℕ) (x : I) :
    lowerCutoff g a n x ≤ cutoff g a x := by
  change g x * ramp n ((x : ℝ) - a) ≤ if a ≤ (x : ℝ) then g x else 0
  split_ifs with hx
  · exact (mul_le_mul_of_nonneg_left (ramp_le_one _ _) (hg x)).trans_eq (mul_one _)
  · rw [ramp_eq_zero_of_nonpos n (by linarith : (x : ℝ) - a ≤ 0), mul_zero]

theorem cutoff_le_upperCutoff {g : C(I, ℝ)} (hg : ∀ x, 0 ≤ g x) (a : ℝ) (n : ℕ) (x : I) :
    cutoff g a x ≤ upperCutoff g a n x := by
  change (if a ≤ (x : ℝ) then g x else 0) ≤ g x * (1 - ramp n (a - (x : ℝ)))
  split_ifs with hx
  · rw [ramp_eq_zero_of_nonpos n (sub_nonpos.mpr hx), sub_zero, mul_one]
  · exact mul_nonneg (hg x) (sub_nonneg.mpr (ramp_le_one _ _))

theorem lowerCutoff_tendsto {g : C(I, ℝ)} {a : ℝ} {x : I} (hx : (x : ℝ) ≠ a) :
    Tendsto (fun n => lowerCutoff g a n x) atTop (𝓝 (cutoff g a x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · simp only [lowerCutoff, ContinuousMap.coe_mk,
      ramp_eq_zero_of_nonpos _ (sub_nonpos.mpr hx.le), mul_zero,
      cutoff, if_neg (not_le.mpr hx)]
    exact tendsto_const_nhds
  · have h := (ramp_tendsto_of_pos (sub_pos.mpr hx)).const_mul (g x)
    simpa only [mul_one, lowerCutoff, ContinuousMap.coe_mk, cutoff, if_pos hx.le] using h

theorem upperCutoff_tendsto {g : C(I, ℝ)} {a : ℝ} {x : I} (hx : (x : ℝ) ≠ a) :
    Tendsto (fun n => upperCutoff g a n x) atTop (𝓝 (cutoff g a x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (ramp_tendsto_of_pos (sub_pos.mpr hx))).const_mul (g x)
    simpa only [sub_self, mul_zero, upperCutoff, ContinuousMap.coe_mk,
      cutoff, if_neg (not_le.mpr hx)] using h
  · simp only [upperCutoff, ContinuousMap.coe_mk,
      ramp_eq_zero_of_nonpos _ (sub_nonpos.mpr hx.le), sub_zero, mul_one,
      cutoff, if_pos hx.le]
    exact tendsto_const_nhds

theorem cutoff_integrable (μ : FiniteMeasure I) (g : C(I, ℝ)) (a : ℝ) :
    Integrable (cutoff g a) (μ : Measure I) := by
  have h := g.continuous.integrable_of_hasCompactSupport
    (μ := (μ : Measure I)) (HasCompactSupport.of_compactSpace g)
  exact h.indicator (measurableSet_le measurable_const continuous_subtype_val.measurable)

private theorem norm_mul_le_norm (g : C(I, ℝ)) (x : I) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) : ‖g x * r‖ ≤ ‖g‖ := by
  rw [norm_mul, Real.norm_of_nonneg hr₀]
  exact (mul_le_mul (g.norm_coe_le_norm x) hr₁ hr₀ (norm_nonneg g)).trans_eq (mul_one _)

theorem norm_lowerCutoff_le (g : C(I, ℝ)) (a : ℝ) (n : ℕ) (x : I) :
    ‖lowerCutoff g a n x‖ ≤ ‖g‖ :=
  norm_mul_le_norm g x (ramp_nonneg _ _) (ramp_le_one _ _)

theorem norm_upperCutoff_le (g : C(I, ℝ)) (a : ℝ) (n : ℕ) (x : I) :
    ‖upperCutoff g a n x‖ ≤ ‖g‖ :=
  norm_mul_le_norm g x (sub_nonneg.mpr (ramp_le_one _ _))
    (by linarith [ramp_nonneg n (a - (x : ℝ))])

theorem cutoff_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I))))
    (g : C(I, ℝ)) (hg : ∀ x, 0 ≤ g x) (a : ℝ)
    (hν : (ν : Measure I) {x : I | (x : ℝ) = a} = 0) :
    Tendsto (fun i => ∫ x, cutoff g a x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, cutoff g a x ∂(ν : Measure I))) := by
  have hne : ∀ᵐ (x : I) ∂(ν : Measure I), (x : ℝ) ≠ a := by
    simpa only [ae_iff, not_not] using hν
  apply integral_tendsto_of_continuous_sandwich
    (continuous_integral_tendsto_of_moments h)
    (fun i => cutoff_integrable (μ i) g a)
    (lowerCutoff g a) (upperCutoff g a)
    (lowerCutoff_le_cutoff hg a) (cutoff_le_upperCutoff hg a)
  · apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖g‖)
    · intro n
      exact (lowerCutoff g a n).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall (norm_lowerCutoff_le g a n)
    · exact hne.mono fun _ hx => lowerCutoff_tendsto hx
  · apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖g‖)
    · intro n
      exact (upperCutoff g a n).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall (norm_upperCutoff_le g a n)
    · exact hne.mono fun _ hx => upperCutoff_tendsto hx

end Bernays

end

/-! ### Upstream module `Util/Bernays/HalfPowerMeasure.lean` -/

section
/-!
# The measure for the half-power Tauberian law

Pushing the Gaussian density `exp (-t²) / sqrt π` forward by `t ↦ exp (-t²)`
gives a measure on `[0,1]` with moments `1 / sqrt (k+1)`. The weighted cutoff
at `exp (-1)` has integral `2 / sqrt π`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped unitInterval NNReal

namespace Bernays

noncomputable def expNegSq (t : ℝ) : I :=
  ⟨exp (-(t ^ 2)), (exp_pos _).le, exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))⟩

theorem continuous_expNegSq : Continuous expNegSq := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp (continuous_id.pow 2).neg

noncomputable def halfPowerMeasure : FiniteMeasure I :=
  FiniteMeasure.map (⟨gaussianReal 0 (1 / 2), inferInstance⟩ : FiniteMeasure ℝ) expNegSq

theorem gaussianPDFReal_half (t : ℝ) :
    gaussianPDFReal 0 (1 / 2) t = (sqrt π)⁻¹ * exp (-(t ^ 2)) := by
  have hv : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  simp only [gaussianPDFReal, hv, sub_zero,
    show 2 * π * (1 / 2 : ℝ) = π by ring,
    show 2 * (1 / 2 : ℝ) = 1 by norm_num, div_one]

theorem halfPowerMeasure_integral (f : I → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(halfPowerMeasure : Measure I)) =
      (sqrt π)⁻¹ * ∫ t : ℝ, exp (-(t ^ 2)) * f (expNegSq t) := by
  change (∫ x, f x ∂(gaussianReal 0 (1 / 2)).map expNegSq) = _
  rw [integral_map continuous_expNegSq.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal_half, mul_assoc, integral_const_mul]

theorem halfPowerMeasure_moment (k : ℕ) :
    (∫ x : I, (x : ℝ) ^ k ∂(halfPowerMeasure : Measure I)) =
      1 / sqrt ((k : ℝ) + 1) := by
  rw [halfPowerMeasure_integral (fun x : I => (x : ℝ) ^ k) (by fun_prop)]
  have heq (t : ℝ) : exp (-(t ^ 2)) * (expNegSq t : ℝ) ^ k =
      exp (-((k : ℝ) + 1) * t ^ 2) := by
    change exp (-(t ^ 2)) * exp (-(t ^ 2)) ^ k = _
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [heq]
  rw [integral_gaussian, sqrt_div pi_pos.le]
  have hπ : sqrt π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  field_simp

noncomputable def reciprocalCutWeight (a : ℝ) (ha : 0 < a) : C(I, ℝ) where
  toFun x := (max a (x : ℝ))⁻¹
  continuous_toFun := (continuous_const.max continuous_subtype_val).inv₀
    (fun x => (ha.trans_le (le_max_left a (x : ℝ))).ne')

theorem reciprocalCutWeight_nonneg (a : ℝ) (ha : 0 < a) (x : I) :
    0 ≤ reciprocalCutWeight a ha x :=
  inv_nonneg.mpr (ha.le.trans (le_max_left _ _))

theorem halfPowerMeasure_null_cutoff :
    (halfPowerMeasure : Measure I) {x : I | (x : ℝ) = exp (-1)} = 0 := by
  change ((gaussianReal 0 (1 / 2)).map expNegSq) _ = 0
  rw [Measure.map_apply continuous_expNegSq.measurable
    (measurableSet_eq_fun continuous_subtype_val.measurable measurable_const)]
  have : NullSingletonClass (gaussianReal 0 (1 / 2)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  apply measure_mono_null (t := ({-1, 1} : Set ℝ))
  · intro t ht
    change exp (-(t ^ 2)) = exp (-1) at ht
    have he := Real.exp_injective ht
    have hm : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with hm | hm
    · have : t = 1 := by linarith
      simp [this]
    · have : t = -1 := by linarith
      simp [this]
  · exact (Set.toFinite ({-1, 1} : Set ℝ)).measure_zero (gaussianReal 0 (1 / 2))

theorem cutoff_reciprocal_expNegSq (t : ℝ) :
    exp (-(t ^ 2)) *
      cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) (expNegSq t) =
      (Set.Icc (-1) 1).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  have he : exp (-1) ≤ exp (-(t ^ 2)) ↔ t ∈ Set.Icc (-1) 1 := by
    rw [Real.exp_le_exp, Set.mem_Icc]
    constructor
    · intro ht
      constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
    · rintro ⟨hl, hu⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ t + 1)]
  change exp (-(t ^ 2)) *
    (if exp (-1) ≤ exp (-(t ^ 2)) then (max (exp (-1)) (exp (-(t ^ 2))))⁻¹ else 0) = _
  by_cases ht : t ∈ Set.Icc (-1) 1
  · rw [if_pos (he.mpr ht), max_eq_right (he.mpr ht),
      mul_inv_cancel₀ (exp_ne_zero _), Set.indicator_of_mem ht]
  · rw [if_neg (fun h => ht (he.mp h)), mul_zero, Set.indicator_of_notMem ht]

theorem halfPowerMeasure_cutoff_integral :
    (∫ x, cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) x
      ∂(halfPowerMeasure : Measure I)) = 2 / sqrt π := by
  rw [halfPowerMeasure_integral]
  · simp_rw [cutoff_reciprocal_expNegSq]
    rw [integral_indicator measurableSet_Icc, integral_const]
    norm_num [Measure.real, Real.volume_Icc]
    ring
  · exact (reciprocalCutWeight (exp (-1)) (exp_pos _)).continuous.measurable.ite
      (measurableSet_le measurable_const continuous_subtype_val.measurable) measurable_const

end Bernays

end

/-! ### Upstream module `Util/Bernays/LaplaceMeasure.lean` -/

section
/-!
# Compact measures associated with a Laplace transform

For a positive measure on the nonnegative real line, exponential weighting and
the map `y ↦ exp (-s*y)` turn ratios of its Laplace transform into moments on
the compact unit interval. This is the transform step in the Tauberian proof.
-/

open MeasureTheory Filter Topology Real
open scoped unitInterval NNReal ENNReal

namespace Bernays

noncomputable def laplace (μ : Measure ℝ≥0) (s : ℝ) : ℝ :=
  ∫ y : ℝ≥0, exp (-s * y) ∂μ

theorem laplace_nonneg (μ : Measure ℝ≥0) (s : ℝ) : 0 ≤ laplace μ s :=
  integral_nonneg fun _ => (exp_pos _).le

noncomputable def expNegMul (s : ℝ) (hs : 0 < s) (y : ℝ≥0) : I :=
  ⟨exp (-s * y), (exp_pos _).le,
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) y.coe_nonneg)⟩

theorem continuous_expNegMul (s : ℝ) (hs : 0 < s) : Continuous (expNegMul s hs) := by
  apply Continuous.subtype_mk
  exact continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)

noncomputable def laplaceWeightedMeasure (μ : Measure ℝ≥0) (s : ℝ)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) : FiniteMeasure ℝ≥0 :=
  ⟨μ.withDensity (fun y : ℝ≥0 => ENNReal.ofReal (exp (-s * y))),
    isFiniteMeasure_withDensity
      ((lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
        (Filter.Eventually.of_forall fun _ => (exp_pos _).le)).mpr h)⟩

noncomputable def compactLaplaceMeasure (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) : FiniteMeasure I :=
  ((laplace μ s).toNNReal)⁻¹ •
    FiniteMeasure.map (laplaceWeightedMeasure μ s h) (expNegMul s hs)

theorem compactLaplaceMeasure_integral (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ)
    (f : I → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      (laplace μ s)⁻¹ * ∫ y : ℝ≥0, exp (-s * y) * f (expNegMul s hs y) ∂μ := by
  rw [compactLaplaceMeasure, FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_inv, Real.coe_toNNReal _ (laplace_nonneg μ s)]
  change (laplace μ s)⁻¹ *
    (∫ x, f x ∂(μ.withDensity (fun y : ℝ≥0 => ENNReal.ofReal (exp (-s * y)))).map
      (expNegMul s hs)) = _
  rw [integral_map (continuous_expNegMul s hs).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]

theorem compactLaplaceMeasure_moment (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) (k : ℕ) :
    (∫ x : I, (x : ℝ) ^ k ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      laplace μ (((k : ℝ) + 1) * s) / laplace μ s := by
  rw [compactLaplaceMeasure_integral μ s hs h (fun x : I => (x : ℝ) ^ k) (by fun_prop)]
  have heq (y : ℝ≥0) : exp (-s * y) * (expNegMul s hs y : ℝ) ^ k =
      exp (-(((k : ℝ) + 1) * s) * y) := by
    change exp (-s * y) * exp (-s * y) ^ k = _
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [heq]
  change (laplace μ s)⁻¹ * laplace μ (((k : ℝ) + 1) * s) = _
  ring

theorem expNegMul_mem_cutoff_iff (s : ℝ) (hs : 0 < s) (y : ℝ≥0) :
    exp (-1) ≤ (expNegMul s hs y : ℝ) ↔ (y : ℝ) ≤ s⁻¹ := by
  change exp (-1) ≤ exp (-s * y) ↔ _
  rw [Real.exp_le_exp]
  constructor
  · intro hy
    rw [← one_div]
    apply (le_div_iff₀ hs).mpr
    change (y : ℝ) * s ≤ 1
    nlinarith
  · intro hy
    rw [← one_div] at hy
    have hys : (y : ℝ) * s ≤ 1 := (le_div_iff₀ hs).mp hy
    nlinarith

theorem compactLaplaceMeasure_cutoff (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) :
    (∫ x, cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) x
      ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      μ.real {y : ℝ≥0 | (y : ℝ) ≤ s⁻¹} / laplace μ s := by
  rw [compactLaplaceMeasure_integral]
  · have heq (y : ℝ≥0) : exp (-s * y) *
        cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) (expNegMul s hs y) =
        {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}.indicator (fun _ => (1 : ℝ)) y := by
      change exp (-s * y) *
        (if exp (-1) ≤ exp (-s * y) then (max (exp (-1)) (exp (-s * y)))⁻¹ else 0) = _
      by_cases hy : (y : ℝ) ≤ s⁻¹
      · have he := (expNegMul_mem_cutoff_iff s hs y).mpr hy
        change exp (-1) ≤ exp (-s * y) at he
        rw [if_pos he, max_eq_right he, mul_inv_cancel₀ (exp_ne_zero _),
          Set.indicator_of_mem (s := {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}) hy]
      · have he : ¬ exp (-1) ≤ exp (-s * y) :=
          fun h => hy ((expNegMul_mem_cutoff_iff s hs y).mp h)
        rw [if_neg he, mul_zero,
          Set.indicator_of_notMem (s := {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}) hy]
    simp_rw [heq]
    rw [integral_indicator (measurableSet_le NNReal.continuous_coe.measurable measurable_const),
      integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      div_eq_mul_inv, mul_comm]
  · exact (reciprocalCutWeight (exp (-1)) (exp_pos _)).continuous.measurable.ite
      (measurableSet_le measurable_const continuous_subtype_val.measurable) measurable_const

end Bernays

end

/-! ### Upstream module `Util/Bernays/HalfPowerTauberian.lean` -/

section
/-!
# A half-power Laplace Tauberian theorem

A positive measure whose Laplace transform is asymptotic to `C / sqrt s`
has cumulative mass asymptotic to `2*C*sqrt x / sqrt π`. The proof uses
compact moment convergence and the two-sided cutoff approximations.
-/

open MeasureTheory Filter Topology Real
open scoped unitInterval NNReal

namespace Bernays

theorem laplace_ratio_tendsto {ι : Type*} {l : Filter ι}
    (μ : Measure ℝ≥0) {C : ℝ} (hC : 0 < C)
    (hL : Tendsto (fun t : ℝ => sqrt t * laplace μ t) (𝓝[Set.Ioi 0] 0) (𝓝 C))
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (hs₀ : Tendsto s l (𝓝 0))
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun i => laplace μ (K * s i) / laplace μ (s i)) l (𝓝 (1 / sqrt K)) := by
  have hst : Tendsto s l (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs₀, Filter.Eventually.of_forall hs⟩
  have hKst : Tendsto (fun i => K * s i) l (𝓝[Set.Ioi 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using hs₀.const_mul K
    · exact Filter.Eventually.of_forall fun i => mul_pos hK (hs i)
  have hrat := ((hL.comp hKst).div (hL.comp hst) hC.ne').div_const (sqrt K)
  rw [div_self hC.ne'] at hrat
  apply hrat.congr'
  apply Filter.Eventually.of_forall
  intro i
  change (sqrt (K * s i) * laplace μ (K * s i) /
    (sqrt (s i) * laplace μ (s i))) / sqrt K = _
  rw [sqrt_mul hK.le]
  have hsi : sqrt (s i) ≠ 0 := (sqrt_pos.mpr (hs i)).ne'
  have hKi : sqrt K ≠ 0 := (sqrt_pos.mpr hK).ne'
  calc
    (sqrt K * sqrt (s i) * laplace μ (K * s i) /
        (sqrt (s i) * laplace μ (s i))) / sqrt K =
      (sqrt (s i) * (sqrt K * laplace μ (K * s i)) /
        (sqrt (s i) * laplace μ (s i))) / sqrt K := by ring
    _ = (sqrt K * laplace μ (K * s i) / laplace μ (s i)) / sqrt K := by
      rw [mul_div_mul_left _ _ hsi]
    _ = laplace μ (K * s i) / laplace μ (s i) := by
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hKi]

theorem halfPowerTauberian {ι : Type*} {l : Filter ι}
    (μ : Measure ℝ≥0)
    (hIntegrable : ∀ t : ℝ, 0 < t → Integrable (fun y : ℝ≥0 => exp (-t * y)) μ)
    {C : ℝ} (hC : 0 < C)
    (hL : Tendsto (fun t : ℝ => sqrt t * laplace μ t) (𝓝[Set.Ioi 0] 0) (𝓝 C))
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (hs₀ : Tendsto s l (𝓝 0)) :
    Tendsto (fun i => sqrt (s i) * μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹}) l
      (𝓝 (2 * C / sqrt π)) := by
  let ν : ι → FiniteMeasure I := fun i =>
    compactLaplaceMeasure μ (s i) (hs i) (hIntegrable (s i) (hs i))
  have hm (k : ℕ) : Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(ν i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(halfPowerMeasure : Measure I))) := by
    simp only [ν, compactLaplaceMeasure_moment, halfPowerMeasure_moment]
    exact laplace_ratio_tendsto μ hC hL s hs hs₀ (by positivity)
  have hcut := cutoff_integral_tendsto_of_moments hm
    (reciprocalCutWeight (exp (-1)) (exp_pos _))
    (reciprocalCutWeight_nonneg _ _) (exp (-1)) halfPowerMeasure_null_cutoff
  simp only [ν, compactLaplaceMeasure_cutoff, halfPowerMeasure_cutoff_integral] at hcut
  have hst : Tendsto s l (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs₀, Filter.Eventually.of_forall hs⟩
  have hmain := hcut.mul (hL.comp hst)
  have hfinal : Tendsto
      (fun i => sqrt (s i) * μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹}) l
      (𝓝 (2 / sqrt π * C)) := by
    apply hmain.congr'
    filter_upwards [(hL.comp hst).eventually (lt_mem_nhds hC)] with i hi
    change 0 < sqrt (s i) * laplace μ (s i) at hi
    have hne : laplace μ (s i) ≠ 0 := by
      intro heq
      simp only [heq, mul_zero, lt_self_iff_false] at hi
    change μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹} / laplace μ (s i) *
      (sqrt (s i) * laplace μ (s i)) = _
    field_simp
  convert hfinal using 1
  congr 1
  ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/DirichletTauberian.lean` -/

section
/-!
# The half-power Tauberian theorem for arithmetic Dirichlet series

The logarithmic atomic measure has mass `a(n)/n` at `log n`. Its Laplace
transform is the real Dirichlet series at `1+s`; its cumulative mass is the
exact reciprocal partial sum, including all endpoint conventions.
-/

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal

namespace Bernays

noncomputable def realDirichlet (a : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ z

noncomputable def reciprocalSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, a (n + 1) / ((n + 1 : ℕ) : ℝ)

noncomputable def logAtom (n : ℕ) : ℝ≥0 :=
  ⟨log ((n + 1 : ℕ) : ℝ), log_natCast_nonneg _⟩

noncomputable def logarithmicMeasure (a : ℕ → ℝ) : Measure ℝ≥0 :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (a (n + 1) / ((n + 1 : ℕ) : ℝ)) • Measure.dirac (logAtom n)

theorem logarithmicMeasure_integral {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (f : ℝ≥0 → ℝ) :
    (∫ y, f y ∂logarithmicMeasure a) =
      ∑' n : ℕ, a (n + 1) / ((n + 1 : ℕ) : ℝ) * f (logAtom n) := by
  rw [logarithmicMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (div_nonneg (ha _) (by positivity)), smul_eq_mul]

theorem weighted_exponential_eq_dirichletTerm (b x s : ℝ) (hx : 0 < x) :
    b / x * exp (-s * log x) = b / x ^ (1 + s) := by
  rw [rpow_add hx, rpow_one, rpow_def_of_pos hx,
    show -s * log x = -(log x * s) by ring, exp_neg]
  ring

theorem logarithmicMeasure_laplace {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (s : ℝ) :
    laplace (logarithmicMeasure a) s = realDirichlet a (1 + s) := by
  rw [laplace, logarithmicMeasure_integral ha]
  apply tsum_congr
  intro n
  exact weighted_exponential_eq_dirichletTerm _ _ _ (by positivity)

theorem logarithmicMeasure_exp_integrable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (s : ℝ)
    (h : Summable (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (1 + s))) :
    Integrable (fun y : ℝ≥0 => exp (-s * y)) (logarithmicMeasure a) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  convert h using 1
  ext n
  rw [ENNReal.toReal_ofReal (div_nonneg (ha _) (by positivity)),
    Real.norm_of_nonneg (exp_pos _).le]
  exact weighted_exponential_eq_dirichletTerm _ _ _ (by positivity)

theorem logAtom_mem_cutoff_iff (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (logAtom n : ℝ) ≤ log x ↔ n < ⌊x⌋₊ := by
  change log ((n + 1 : ℕ) : ℝ) ≤ log x ↔ _
  rw [log_le_log_iff (by positivity) hx, Nat.lt_iff_add_one_le, Nat.le_floor_iff hx.le]

theorem logarithmicMeasure_cutoff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {x : ℝ} (hx : 0 < x) :
    (logarithmicMeasure a).real {y : ℝ≥0 | (y : ℝ) ≤ log x} = reciprocalSum a ⌊x⌋₊ := by
  classical
  let S : Set ℝ≥0 := {y | (y : ℝ) ≤ log x}
  have hS : MeasurableSet S := measurableSet_le NNReal.continuous_coe.measurable measurable_const
  have hmem (n : ℕ) : logAtom n ∈ S ↔ n ∈ Finset.range ⌊x⌋₊ := by
    exact (logAtom_mem_cutoff_iff n hx).trans Finset.mem_range.symm
  change (logarithmicMeasure a).real S = _
  rw [← integral_indicator_one hS, logarithmicMeasure_integral ha]
  rw [tsum_eq_sum (s := Finset.range ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Set.indicator_of_mem ((hmem n).mpr hn), Pi.one_apply, mul_one]
  · intro n hn
    rw [Set.indicator_of_notMem (fun h => hn ((hmem n).mp h)), mul_zero]

theorem summable_realDirichletTerm_of_bounded {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {z : ℝ} (hz : 1 < z) :
    Summable (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ z) := by
  have hp := (summable_one_div_nat_rpow.mpr hz).comp_injective
    (fun n m h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (ha _) (by positivity)) _ hp
  intro n
  exact div_le_div_of_nonneg_right (ha₁ _) (by positivity)

theorem reciprocalSum_div_sqrt_log_tendsto {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {C : ℝ} (hC : 0 < C)
    (hD : Tendsto (fun s : ℝ => sqrt s * realDirichlet a (1 + s))
      (𝓝[Set.Ioi 0] 0) (𝓝 C)) :
    Tendsto (fun x : ℝ => reciprocalSum a ⌊x⌋₊ / sqrt (log x)) atTop
      (𝓝 (2 * C / sqrt π)) := by
  let s : ℝ → ℝ := fun x => (log (max 2 x))⁻¹
  have hs (x : ℝ) : 0 < s x :=
    inv_pos.mpr (log_pos (lt_of_lt_of_le (by norm_num) (le_max_left 2 x)))
  have hmax : Tendsto (fun x : ℝ => max 2 x) atTop atTop :=
    tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hs₀ : Tendsto s atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_log_atTop.comp hmax)
  have hint (t : ℝ) (ht : 0 < t) :
      Integrable (fun y : ℝ≥0 => exp (-t * y)) (logarithmicMeasure a) :=
    logarithmicMeasure_exp_integrable ha t
      (summable_realDirichletTerm_of_bounded ha ha₁ (by linarith))
  have hL : Tendsto (fun t : ℝ => sqrt t * laplace (logarithmicMeasure a) t)
      (𝓝[Set.Ioi 0] 0) (𝓝 C) := by
    simpa only [logarithmicMeasure_laplace ha] using hD
  have ht := halfPowerTauberian (logarithmicMeasure a) hint hC hL s hs hs₀
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  dsimp only [s]
  rw [max_eq_right hx, inv_inv, logarithmicMeasure_cutoff ha (by linarith : 0 < x), sqrt_inv]
  ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogWeightRemoval.lean` -/

section
/-!
# Removing logarithmic weights

For coefficients between zero and one, replacing `log n` by `log N` in a
partial sum costs at most `4*N`. This elementary estimate follows from a
telescoping square-root bound and is negligible on the Bernays weighted scale.
-/

open Filter Topology Real

namespace Bernays

noncomputable def ordinarySum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n

noncomputable def logarithmicSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * log (n : ℝ)

theorem inv_sqrt_step (n : ℕ) :
    1 / sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (sqrt ((n + 1 : ℕ) : ℝ) - sqrt (n : ℝ)) := by
  have hpos : 0 < sqrt ((n + 1 : ℕ) : ℝ) := sqrt_pos.mpr (by positivity)
  have h₁ : sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 :=
    (sq_sqrt (Nat.cast_nonneg (n + 1))).trans (by norm_num)
  have h₀ := sq_sqrt (Nat.cast_nonneg n)
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg (sqrt ((n + 1 : ℕ) : ℝ) - sqrt (n : ℝ))]

theorem sum_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / sqrt (n : ℝ)) ≤ 2 * sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      linarith [inv_sqrt_step N]

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 2 * sqrt x := by
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hx)
  rw [log_sqrt hx.le] at h
  linarith

theorem log_weight_error_bounds {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ log (N : ℝ) * ordinarySum a N - logarithmicSum a N ∧
      log (N : ℝ) * ordinarySum a N - logarithmicSum a N ≤ 4 * N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have heq : log (N : ℝ) * ordinarySum a N - logarithmicSum a N =
      ∑ n ∈ Finset.Icc 1 N, a n * (log (N : ℝ) - log (n : ℝ)) := by
    simp only [ordinarySum, logarithmicSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hnpos (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  have hlog (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : 0 ≤ log (N : ℝ) - log (n : ℝ) :=
    sub_nonneg.mpr (log_le_log (hnpos n hn) (by exact_mod_cast (Finset.mem_Icc.mp hn).2))
  rw [heq]
  constructor
  · exact Finset.sum_nonneg fun n hn => mul_nonneg (ha n) (hlog n hn)
  · calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (log (N : ℝ) - log (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact (mul_le_mul_of_nonneg_right (ha₁ n) (hlog n hn)).trans_eq (one_mul _)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, 2 * sqrt (N : ℝ) * (1 / sqrt (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [← log_div hNpos.ne' (hnpos n hn).ne']
        have h := log_le_two_sqrt (div_pos hNpos (hnpos n hn))
        rw [sqrt_div hNpos.le] at h
        simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h
      _ = 2 * sqrt (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, 1 / sqrt (n : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * sqrt (N : ℝ) * (2 * sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)
      _ = 4 * N := by nlinarith [sq_sqrt hNpos.le]

theorem ordinarySum_asymptotic_of_logarithmicSum {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {C : ℝ}
    (hlog : Tendsto (fun N : ℕ => logarithmicSum a N /
      ((N : ℝ) * sqrt (log (N : ℝ)))) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => ordinarySum a N / ((N : ℝ) / sqrt (log (N : ℝ))))
      atTop (𝓝 C) := by
  let E : ℕ → ℝ := fun N =>
    (log (N : ℝ) * ordinarySum a N - logarithmicSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))
  have hden : Tendsto (fun N : ℕ => sqrt (log (N : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbound : Tendsto (fun N : ℕ => 4 / sqrt (log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ← div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (4 : ℝ)
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact div_nonneg (log_weight_error_bounds ha ha₁ (by omega)).1 (by positivity)
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
      calc
        E N ≤ (4 * N) / ((N : ℝ) * sqrt (log (N : ℝ))) :=
          div_le_div_of_nonneg_right (log_weight_error_bounds ha ha₁ (by omega)).2 (by positivity)
        _ = 4 / sqrt (log (N : ℝ)) := by field_simp
  have hsum := hlog.add hE
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hsqrt : sqrt (log (N : ℝ)) ≠ 0 := (sqrt_pos.mpr hLp).ne'
  change logarithmicSum a N / ((N : ℝ) * sqrt (log (N : ℝ))) + E N = _
  dsimp only [E]
  field_simp
  rw [sq_sqrt hLp.le]
  ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/PrimeThetaLimits.lean` -/

section
/-!
# Natural-endpoint limits for prime logarithmic sums
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem ordinarySum_eq_cumsum_succ {a : ℕ → ℝ} (ha₀ : a 0 = 0) (N : ℕ) :
    ordinarySum a N = cumsum a (N + 1) := by
  rw [cumsum, Nat.range_succ_eq_Icc_zero, Finset.Icc_eq_cons_Ioc (Nat.zero_le N),
    Finset.sum_cons, ha₀, zero_add]
  simp only [ordinarySum, ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add]

theorem nat_succ_div_self_tendsto :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_add 1
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp only [Function.comp_def]
  push_cast
  field_simp

theorem ordinarySum_div_tendsto_of_cumsum {a : ℕ → ℝ} (ha₀ : a 0 = 0) {c : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum a N / (N : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => ordinarySum a N / (N : ℝ)) atTop (𝓝 c) := by
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hm := hshift.mul nat_succ_div_self_tendsto
  rw [mul_one] at hm
  apply hm.congr'
  apply Filter.Eventually.of_forall
  intro N
  change (cumsum a (N + 1) / ((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ) / N) =
    ordinarySum a N / N
  rw [ordinarySum_eq_cumsum_succ ha₀]
  have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact div_mul_div_cancel₀ hne

theorem psi_eq_ordinarySum (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ordinarySum ArithmeticFunction.vonMangoldt N := by
  simp only [Chebyshev.psi, Nat.floor_natCast, ordinarySum,
    ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add]

theorem psi_div_tendsto_one :
    Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  simpa only [psi_eq_ordinarySum] using
    ordinarySum_div_tendsto_of_cumsum (by simp : ArithmeticFunction.vonMangoldt 0 = 0) WeakPNT

theorem primePowerError_div_tendsto_zero :
    Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ) / sqrt (N : ℝ)) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbound : Tendsto (fun N : ℕ => 2 * sqrt (N : ℝ) * log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    have h := hlog.const_mul 2
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hsp : sqrt (N : ℝ) ≠ 0 := (sqrt_pos.mpr hNp).ne'
    change 2 * (log (N : ℝ) / sqrt (N : ℝ)) = _
    field_simp
    rw [sq_sqrt hNp.le]
  apply squeeze_zero' _ _ hbound
  · exact Filter.Eventually.of_forall fun N => div_nonneg
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_le_div_of_nonneg_right
      ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hN)))
      (Nat.cast_nonneg N)

theorem theta_div_tendsto_one :
    Tendsto (fun N : ℕ => Chebyshev.theta (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have h := psi_div_tendsto_one.sub primePowerError_div_tendsto_zero
  rw [sub_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun _ => by dsimp only; ring

noncomputable def realCharacterTheta {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, (χ p).re * log p

theorem characterTheta_error_le {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    |ordinarySum (fun n => (χ n).re * ArithmeticFunction.vonMangoldt n) N - realCharacterTheta χ N| ≤
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  have heq : ordinarySum (fun n => (χ n).re * ArithmeticFunction.vonMangoldt n) N -
      realCharacterTheta χ N = ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0 else (χ n).re * ArithmeticFunction.vonMangoldt n := by
    rw [realCharacterTheta, ← Nat.primesLE, Nat.primesLE_eq_filter_Icc_one,
      ordinarySum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime
    · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
    · simp [hn]
  rw [heq, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add, Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : n.Prime
  · simp [hn]
  · simp only [hn, if_false, not_false_eq_true, if_true, abs_mul,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_mul_of_nonneg_right
      ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))
      ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)

theorem realCharacterTheta_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => realCharacterTheta χ N / (N : ℝ)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => (χ n).re * ArithmeticFunction.vonMangoldt n
  have hψ : Tendsto (fun N : ℕ => ordinarySum a N / (N : ℝ)) atTop (𝓝 0) :=
    ordinarySum_div_tendsto_of_cumsum (by simp [a]) (realTwistedMangoldt_div_tendsto_zero χ hχ)
  have he : Tendsto (fun N : ℕ => (ordinarySum a N - realCharacterTheta χ N) / (N : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ primePowerError_div_tendsto_zero
    intro N
    rw [Real.norm_eq_abs, abs_div]
    rw [show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
    exact div_le_div_of_nonneg_right (characterTheta_error_le χ N) (Nat.cast_nonneg N)
  have h := hψ.sub he
  rw [sub_self] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun _ => by dsimp only; ring

end Bernays

end

/-! ### Upstream module `ErdosProblems/Erdos448/PrimePowerConvolution448.lean` -/

section
open scoped BigOperators
open Finset

namespace PrimePowerConvolution448

lemma log_eq_sum_primeFactors (n : ℕ) :
    Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  simp only [Finsupp.sum, Nat.support_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_pow, Real.log_pow]

lemma weighted_log_eq_sum_primeFactors
    (h : ℕ → ℝ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    {n : ℕ} (hn : n ≠ 0) :
    h n * Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by
  rw [log_eq_sum_primeFactors, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hcop : (ordProj[p] n).Coprime (ordCompl[p] n) :=
    (Nat.coprime_ordCompl hp hn).pow_left _
  have hdecomp : ordProj[p] n * ordCompl[p] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  calc
    h n * Real.log ((ordProj[p] n : ℕ) : ℝ) =
        h (ordProj[p] n * ordCompl[p] n) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hdecomp]
    _ = (h (ordProj[p] n) * h (ordCompl[p] n)) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hmul hcop]
    _ = h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by ring

end PrimePowerConvolution448

end

/-! ### Upstream module `Util/Bernays/PrimePowerReindex.lean` -/

section
/-!
# Reindexing logarithmic prime-power convolutions

The finite bijection `(n,p,k) ↦ (n/p^k,p,k)` is adapted from the counting
infrastructure of Erdős 1081 and stated here for an arbitrary weight.
-/

namespace Bernays

private abbrev LocalLogSourceIndex :=
  Sigma fun _n : ℕ => Sigma fun _l : ℕ => ℕ

private abbrev LocalLogTargetIndex :=
  Sigma fun _m : ℕ => Sigma fun _l : ℕ => ℕ

/-- Indices `(n,l,k)` with `n ≤ N`, `l | n`, and
`1 ≤ k ≤ v_l(n)`. -/
private def localLogSourceSet (N : ℕ) : Finset LocalLogSourceIndex :=
  (Finset.Icc 1 N).sigma fun n =>
    n.primeFactors.sigma fun l => Finset.Icc 1 (n.factorization l)

/-- Convolution indices `(m,l,k)` with `m l^k ≤ N`. -/
private def localLogTargetSet (N : ℕ) : Finset LocalLogTargetIndex :=
  (Finset.Icc 1 N).sigma fun m =>
    ((N / m + 1).primesBelow).sigma fun l =>
      Finset.Icc 1 (Nat.log l (N / m))

/-- Removing `l^k` from a source integer produces its convolution index. -/
private def localLogSourceToTarget (z : LocalLogSourceIndex) :
    LocalLogTargetIndex :=
  ⟨z.1 / z.2.1 ^ z.2.2, z.2⟩

private theorem localLogSource_pow_dvd {N : ℕ} {z : LocalLogSourceIndex}
    (hz : z ∈ localLogSourceSet N) : z.2.1 ^ z.2.2 ∣ z.1 := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hz.2.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hz.1).1)
  exact (hl.pow_dvd_iff_le_factorization hn0).2
    (Finset.mem_Icc.mp hz.2.2).2

private theorem localLogSource_reconstruct {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    (localLogSourceToTarget z).1 *
        (localLogSourceToTarget z).2.1 ^
          (localLogSourceToTarget z).2.2 = z.1 := by
  rcases z with ⟨n, l, k⟩
  exact Nat.div_mul_cancel (localLogSource_pow_dvd hz)

private theorem localLogSourceToTarget_injOn (N : ℕ) :
    Set.InjOn localLogSourceToTarget
      (localLogSourceSet N : Set LocalLogSourceIndex) := by
  intro z hz w hw heq
  have htail : z.2 = w.2 := congrArg Sigma.snd heq
  have hhead : z.1 = w.1 := by
    calc
      z.1 = (localLogSourceToTarget z).1 *
          (localLogSourceToTarget z).2.1 ^
            (localLogSourceToTarget z).2.2 :=
        (localLogSource_reconstruct hz).symm
      _ = (localLogSourceToTarget w).1 *
          (localLogSourceToTarget w).2.1 ^
            (localLogSourceToTarget w).2.2 := by rw [heq]
      _ = w.1 := localLogSource_reconstruct hw
  cases z
  cases w
  simp_all

private theorem localLogSourceToTarget_mem {N : ℕ}
    {z : LocalLogSourceIndex} (hz : z ∈ localLogSourceSet N) :
    localLogSourceToTarget z ∈ localLogTargetSet N := by
  rcases z with ⟨n, l, k⟩
  simp only [localLogSourceSet, Finset.mem_sigma] at hz
  rcases hz with ⟨hnIcc, hlmem, hkIcc⟩
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
  have hn0 : n ≠ 0 := hnpos.ne'
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hpowpos : 0 < l ^ k := pow_pos hl.pos k
  have hpowdvd : l ^ k ∣ n :=
    (hl.pow_dvd_iff_le_factorization hn0).2 (Finset.mem_Icc.mp hkIcc).2
  have hmpos : 0 < n / l ^ k :=
    Nat.div_pos (Nat.le_of_dvd hnpos hpowdvd) hpowpos
  have hmN : n / l ^ k ≤ N := (Nat.div_le_self n _).trans (Finset.mem_Icc.mp hnIcc).2
  have hmul : l ^ k * (n / l ^ k) ≤ N := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hpowdvd]
    exact (Finset.mem_Icc.mp hnIcc).2
  have hpowQ : l ^ k ≤ N / (n / l ^ k) := by
    rw [Nat.le_div_iff_mul_le hmpos]
    exact hmul
  have hlQ : l < N / (n / l ^ k) + 1 :=
    Nat.lt_succ_of_le ((Nat.le_self_pow hkpos.ne' l).trans hpowQ)
  have hklog : k ≤ Nat.log l (N / (n / l ^ k)) :=
    Nat.le_log_of_pow_le hl.one_lt hpowQ
  simp only [localLogSourceToTarget, localLogTargetSet, Finset.mem_sigma]
  exact ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩,
    Nat.mem_primesBelow.mpr ⟨hlQ, hl⟩,
    Finset.mem_Icc.mpr ⟨hkpos, hklog⟩⟩

private theorem localLogSourceToTarget_surjOn (N : ℕ) :
    ∀ w ∈ localLogTargetSet N,
      ∃ z ∈ localLogSourceSet N, localLogSourceToTarget z = w := by
  intro w hw
  rcases w with ⟨m, l, k⟩
  simp only [localLogTargetSet, Finset.mem_sigma] at hw
  rcases hw with ⟨hmIcc, hlmem, hkIcc⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmIcc).1
  have hl : l.Prime := Nat.prime_of_mem_primesBelow hlmem
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkIcc).1
  have hQ0 : N / m ≠ 0 := by
    intro hQ
    have : k ≤ 0 := by simpa [hQ] using (Finset.mem_Icc.mp hkIcc).2
    omega
  have hpowQ : l ^ k ≤ N / m :=
    Nat.pow_le_of_le_log hQ0 (Finset.mem_Icc.mp hkIcc).2
  have hmulN : m * l ^ k ≤ N := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hpowQ
  have hnpos : 0 < m * l ^ k := Nat.mul_pos hmpos (pow_pos hl.pos k)
  have hl_dvd : l ∣ m * l ^ k := by
    exact dvd_mul_of_dvd_right (dvd_pow_self l hkpos.ne') m
  have hlpf : l ∈ (m * l ^ k).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, hl_dvd, hnpos.ne'⟩
  have hkfac : k ≤ (m * l ^ k).factorization l := by
    apply (hl.pow_dvd_iff_le_factorization hnpos.ne').1
    exact dvd_mul_left (l ^ k) m
  let z : LocalLogSourceIndex := ⟨m * l ^ k, l, k⟩
  have hz : z ∈ localLogSourceSet N := by
    simp only [z, localLogSourceSet, Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hnpos, hmulN⟩, hlpf,
      Finset.mem_Icc.mpr ⟨hkpos, hkfac⟩⟩
  refine ⟨z, hz, ?_⟩
  simp only [z, localLogSourceToTarget]
  congr 1
  exact Nat.mul_div_left m (pow_pos hl.pos k)

theorem primePower_divisor_sum (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors,
      ∑ k ∈ Finset.Icc 1 (n.factorization p), w (n / p ^ k) p k) =
    ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ (N / m + 1).primesBelow,
      ∑ k ∈ Finset.Icc 1 (Nat.log p (N / m)), w m p k := by
  have hsum :
      (∑ z ∈ localLogSourceSet N, w (z.1 / z.2.1 ^ z.2.2) z.2.1 z.2.2) =
        ∑ z ∈ localLogTargetSet N, w z.1 z.2.1 z.2.2 := by
    apply Finset.sum_bij (fun z _ => localLogSourceToTarget z)
    · intro z hz
      exact localLogSourceToTarget_mem hz
    · intro z hz z' hz' hzz'
      exact localLogSourceToTarget_injOn N hz hz' hzz'
    · intro b hb
      obtain ⟨a, ha, hab⟩ := localLogSourceToTarget_surjOn N b hb
      exact ⟨a, ha, hab⟩
    · intro z _
      rfl
  simpa only [localLogSourceSet, localLogTargetSet, Finset.sum_sigma] using hsum

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalParity.lean` -/

section
/-!
# The multiplicative local norm indicator

For an arbitrary set of obstruction primes, the admissible positive integers
are those having even valuation at each obstruction prime. The construction
does not restrict the discriminant or the quadratic form.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

def ParityAdmissible (S : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → S p → Even (padicValNat p n)

theorem parityAdmissible_prime_pow_iff (S : ℕ → Prop) {p k : ℕ} (hp : p.Prime) :
    ParityAdmissible S (p ^ k) ↔ ¬ S p ∨ Even k := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    by_cases hS : S p
    · exact Or.inr (by simpa only [padicValNat.prime_pow] using h p hp hS)
    · exact Or.inl hS
  · intro h q hq hSq
    by_cases hqp : q = p
    · subst q
      have hk : Even k := h.resolve_left (not_not.mpr hSq)
      simpa only [padicValNat.prime_pow] using hk
    · have hnot : ¬ q ∣ p ^ k := by
        intro hdvd
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd))
      rw [padicValNat.eq_zero_of_not_dvd hnot]
      exact Even.zero

theorem parityAdmissible_mul_iff (S : ℕ → Prop) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    ParityAdmissible S (m * n) ↔ ParityAdmissible S m ∧ ParityAdmissible S n := by
  have left {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
      (h : ParityAdmissible S (m * n)) : ParityAdmissible S m := by
    intro p hp hS
    let : Fact p.Prime := ⟨hp⟩
    by_cases hpm : p ∣ m
    · have hpn : ¬ p ∣ n := by
        intro hdvd
        exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hdvd)
      have hsum := h p hp hS
      rwa [padicValNat.mul hm.ne' hn.ne', padicValNat.eq_zero_of_not_dvd hpn, add_zero] at hsum
    · rw [padicValNat.eq_zero_of_not_dvd hpm]
      exact Even.zero
  constructor
  · intro h
    exact ⟨left hm hn hmn h, left hn hm hmn.symm (by simpa only [mul_comm] using h)⟩
  · rintro ⟨h₁, h₂⟩ p hp hS
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hm.ne' hn.ne']
    exact (h₁ p hp hS).add (h₂ p hp hS)

noncomputable def localParity (S : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n ∧ ParityAdmissible S n then 1 else 0

@[simp] theorem localParity_zero (S : ℕ → Prop) : localParity S 0 = 0 := by
  simp [localParity]

@[simp] theorem localParity_one (S : ℕ → Prop) : localParity S 1 = 1 := by
  simp [localParity, ParityAdmissible]

theorem localParity_nonneg (S : ℕ → Prop) (n : ℕ) : 0 ≤ localParity S n := by
  unfold localParity
  split_ifs <;> norm_num

theorem localParity_le_one (S : ℕ → Prop) (n : ℕ) : localParity S n ≤ 1 := by
  unfold localParity
  split_ifs <;> norm_num

theorem localParity_mul (S : ℕ → Prop) {m n : ℕ} (hmn : m.Coprime n) :
    localParity S (m * n) = localParity S m * localParity S n := by
  classical
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · simp only [localParity, hm, hn, Nat.mul_pos hm hn, true_and,
        parityAdmissible_mul_iff S hm hn hmn]
      by_cases h₁ : ParityAdmissible S m <;> by_cases h₂ : ParityAdmissible S n <;> simp [h₁, h₂]
    · have hn₀ : n = 0 := Nat.eq_zero_of_not_pos hn
      simp [hn₀]
  · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    simp [hm₀]

theorem localParity_prime_pow (S : ℕ → Prop) {p k : ℕ} (hp : p.Prime) :
    localParity S (p ^ k) = if S p ∧ Odd k then 0 else 1 := by
  classical
  simp only [localParity, pow_pos hp.pos k, true_and, parityAdmissible_prime_pow_iff S hp]
  by_cases hS : S p
  · by_cases hk : Even k
    · simp [hS, hk, Nat.not_odd_iff_even.mpr hk]
    · simp [hS, hk, Nat.not_even_iff_odd.mp hk]
  · simp [hS]

noncomputable def localDirichletTerm (S : ℕ → Prop) (s : ℝ) (n : ℕ) : ℝ :=
  localParity S n / (n : ℝ) ^ s

theorem localDirichletTerm_mul (S : ℕ → Prop) (s : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    localDirichletTerm S s (m * n) = localDirichletTerm S s m * localDirichletTerm S s n := by
  rw [localDirichletTerm, localDirichletTerm, localDirichletTerm,
    localParity_mul S hmn, Nat.cast_mul, mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem localDirichletTerm_nonneg (S : ℕ → Prop) (s : ℝ) (n : ℕ) :
    0 ≤ localDirichletTerm S s n :=
  div_nonneg (localParity_nonneg S n) (rpow_nonneg (Nat.cast_nonneg n) s)

theorem localDirichletTerm_summable (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    Summable (localDirichletTerm S s) := by
  apply Summable.of_nonneg_of_le (localDirichletTerm_nonneg S s) _
    (summable_one_div_nat_rpow.mpr hs)
  intro n
  exact div_le_div_of_nonneg_right (localParity_le_one S n) (by positivity)

theorem localDirichletTerm_tsum (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, localDirichletTerm S s n) = realDirichlet (localParity S) s := by
  rw [(localDirichletTerm_summable S hs).tsum_eq_zero_add]
  simp only [localDirichletTerm, localParity_zero, zero_div, zero_add, realDirichlet]

theorem localParity_eulerProduct (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => ∑' k : ℕ, localDirichletTerm S s (p ^ k))
      (realDirichlet (localParity S) s) := by
  rw [← localDirichletTerm_tsum S hs]
  apply EulerProduct.eulerProduct_hasProd
    (by simp [localDirichletTerm]) (fun {_ _} h => localDirichletTerm_mul S s h)
    (localDirichletTerm_summable S hs).norm
  simp [localDirichletTerm]

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalLogCoefficient.lean` -/

section
/-!
# Logarithmic coefficients for general local norm conditions

The exact prime-power convolution generalizes the corresponding argument in
Erdős 1081 to any set of obstruction primes.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

/-- Logarithmic-derivative coefficient of the local Euler factor.  It is
`log l` at every positive exponent of an allowed prime, while at an
obstruction prime it is `2 log l` at positive even exponents and zero at odd
exponents. -/
noncomputable def localLogCoeff (S : ℕ → Prop) (l k : ℕ) : ℝ :=
  if k = 0 then 0
  else if S l then
    if Even k then 2 * Real.log l else 0
  else Real.log l

theorem localLogCoeff_nonneg
    (S : ℕ → Prop) (k : ℕ) {l : ℕ} (_hl : l.Prime) :
    0 ≤ localLogCoeff S l k := by
  classical
  unfold localLogCoeff
  split_ifs <;> positivity

/-- Among `1,...,2r`, exactly the even indices contribute to the doubled
logarithmic coefficient.  The formulation as a real-valued sum is the one
used directly in the local convolution identity. -/
theorem sum_Icc_even_two (r : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * r),
        if Even k then (2 : ℝ) else 0) = 2 * r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 2 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 2),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 1)]
      simp only [ih]
      have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
      simp [heven]
      ring

/-- Exact one-prime logarithmic convolution.  This is the coefficient-level
identity behind the Wirsing recurrence for the local norm indicator. -/
theorem localParity_prime_pow_log_convolution
    (S : ℕ → Prop) {l e : ℕ} (hl : l.Prime) :
    localParity S (l ^ e) * Real.log ((l ^ e : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc 1 e,
        localParity S (l ^ (e - k)) *
          localLogCoeff S l k := by
  classical
  by_cases hobs : S l
  · by_cases he : Even e
    · obtain ⟨r, rfl⟩ := he
      simp only [show r + r = 2 * r by omega]
      have heven : Even (2 * r) := ⟨r, by omega⟩
      have hind : localParity S (l ^ (2 * r)) = 1 := by
        rw [localParity_prime_pow S hl]
        simp [hobs, Nat.not_odd_iff_even.mpr heven]
      have hsumPoint (k : ℕ) (hk : k ∈ Finset.Icc 1 (2 * r)) :
          localParity S (l ^ (2 * r - k)) *
              localLogCoeff S l k =
            (if Even k then (2 : ℝ) else 0) * Real.log l := by
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [localLogCoeff, if_neg hk0, if_pos hobs]
        by_cases hke : Even k
        · rcases hke with ⟨s, hs⟩
          have hdiff : Even (2 * r - k) := ⟨r - s, by omega⟩
          have hke' : Even k := ⟨s, hs⟩
          have hdiffNotOdd : ¬ Odd (2 * r - k) :=
            Nat.not_odd_iff_even.mpr hdiff
          simp [hke', hdiffNotOdd, localParity_prime_pow S hl, hobs]
        · simp [hke]
      calc
        localParity S (l ^ (2 * r)) *
            Real.log ((l ^ (2 * r) : ℕ) : ℝ) =
            (2 * r : ℝ) * Real.log l := by
              rw [hind, one_mul, Nat.cast_pow, Real.log_pow]
              push_cast
              ring
        _ = (∑ k ∈ Finset.Icc 1 (2 * r),
              if Even k then (2 : ℝ) else 0) * Real.log l := by
              rw [sum_Icc_even_two]
        _ = ∑ k ∈ Finset.Icc 1 (2 * r),
              localParity S (l ^ (2 * r - k)) *
                localLogCoeff S l k := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k hk
              exact (hsumPoint k hk).symm
    · have heodd : Odd e := Nat.not_even_iff_odd.mp he
      rw [localParity_prime_pow S hl]
      simp only [hobs, true_and, heodd, if_pos, zero_mul]
      apply (Finset.sum_eq_zero ?_).symm
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      have hk0 : k ≠ 0 := by omega
      rw [localLogCoeff, if_neg hk0, if_pos hobs]
      by_cases hke : Even k
      · rcases heodd with ⟨r, hr⟩
        rcases hke with ⟨s, hs⟩
        have hdiff : Odd (e - k) := ⟨r - s, by omega⟩
        have hke' : Even k := ⟨s, hs⟩
        rw [localParity_prime_pow S hl]
        simp [hobs, hke', hdiff]
      · simp [hke]
  · rw [localParity_prime_pow S hl]
    simp only [hobs, false_and, if_false]
    rw [Nat.cast_pow, Real.log_pow]
    calc
      (1 : ℝ) * ((e : ℝ) * Real.log l) =
          ∑ k ∈ Finset.Icc 1 e, Real.log l := by simp
      _ = ∑ k ∈ Finset.Icc 1 e,
          localParity S (l ^ (e - k)) *
            localLogCoeff S l k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [localLogCoeff, if_neg hk0, if_neg hobs,
          localParity_prime_pow S hl]
        simp [hobs]

/-- Cumulative logarithmic-derivative mass through `Q`. -/
noncomputable def localLogMass (S : ℕ → Prop) (Q : ℕ) : ℝ :=
  ∑ l ∈ (Q + 1).primesBelow,
    ∑ k ∈ Finset.Icc 1 (Nat.log l Q), localLogCoeff S l k

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalLogConvolution.lean` -/

section
/-!
# Exact logarithmic convolution for the local norm indicator
-/

namespace Bernays

theorem localParity_log_eq_primePower_sum
    (S : ℕ → Prop) {n : ℕ} (hn : n ≠ 0) :
    localParity S n * Real.log (n : ℝ) =
      ∑ l ∈ n.primeFactors,
        ∑ k ∈ Finset.Icc 1 (n.factorization l),
          localParity S (n / l ^ k) *
            localLogCoeff S l k := by
  rw [PrimePowerConvolution448.weighted_log_eq_sum_primeFactors
    (localParity S) (fun {_ _} hcop =>
      localParity_mul S hcop) hn]
  apply Finset.sum_congr rfl
  intro l hlmem
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  let e := n.factorization l
  have hdecomp : l ^ e * ordCompl[l] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n l
  rw [show ordProj[l] n = l ^ e by rfl,
    localParity_prime_pow_log_convolution S hl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := (Finset.mem_Icc.mp hk).2
  have hquot : n / l ^ k = l ^ (e - k) * ordCompl[l] n := by
    calc
      n / l ^ k = (l ^ e * ordCompl[l] n) / l ^ k := by rw [hdecomp]
      _ = (l ^ k * l ^ (e - k) * ordCompl[l] n) / l ^ k := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hke]
      _ = l ^ (e - k) * ordCompl[l] n := by
        rw [Nat.mul_assoc, Nat.mul_div_right _ (pow_pos hl.pos k)]
  have hcop : (l ^ (e - k)).Coprime (ordCompl[l] n) :=
    (Nat.coprime_ordCompl hl hn).pow_left _
  rw [hquot, localParity_mul S hcop]
  ring

theorem localParity_logarithmic_convolution (S : ℕ → Prop) (N : ℕ) :
    logarithmicSum (localParity S) N =
      ∑ m ∈ Finset.Icc 1 N, localParity S m * localLogMass S (N / m) := by
  calc
    logarithmicSum (localParity S) N =
        ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors,
          ∑ k ∈ Finset.Icc 1 (n.factorization p),
            localParity S (n / p ^ k) * localLogCoeff S p k := by
      apply Finset.sum_congr rfl
      intro n hn
      exact localParity_log_eq_primePower_sum S
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ (N / m + 1).primesBelow,
        ∑ k ∈ Finset.Icc 1 (Nat.log p (N / m)), localParity S m * localLogCoeff S p k :=
      primePower_divisor_sum N (fun m p k => localParity S m * localLogCoeff S p k)
    _ = _ := by
      simp only [localLogMass, Finset.mul_sum]

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalKernelBounds.lean` -/

section
/-!
# Reducing the logarithmic kernel to primes

Higher prime powers contribute at most twice `ψ(N)-θ(N)`. Thus the linear
asymptotic for the full kernel is reduced to the first-prime-power term.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def localAllowedPrimeLog (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, if S p then 0 else log p

theorem localLogCoeff_one (S : ℕ → Prop) (p : ℕ) :
    localLogCoeff S p 1 = if S p then 0 else log p := by
  simp [localLogCoeff]

theorem localLogCoeff_le_two_log (S : ℕ → Prop) (p k : ℕ) :
    localLogCoeff S p k ≤ 2 * log p := by
  have hp := log_natCast_nonneg p
  unfold localLogCoeff
  split_ifs <;> linarith

theorem localLogCoeff_sum_bounds (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    {K : ℕ} (hK : 1 ≤ K) :
    (if S p then 0 else log p) ≤ ∑ k ∈ Finset.Icc 1 K, localLogCoeff S p k ∧
      (∑ k ∈ Finset.Icc 1 K, localLogCoeff S p k) ≤
        (if S p then 0 else log p) + 2 * ((K : ℝ) * log p - log p) := by
  have hmem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
  constructor
  · rw [← localLogCoeff_one S p]
    exact Finset.single_le_sum (fun k _ => localLogCoeff_nonneg S k hp) hmem
  · have hrest : (∑ k ∈ (Finset.Icc 1 K).erase 1, localLogCoeff S p k) ≤
        2 * ((K : ℝ) * log p - log p) := by
      calc
        _ ≤ ∑ _k ∈ (Finset.Icc 1 K).erase 1, 2 * log p :=
          Finset.sum_le_sum (fun k _ => localLogCoeff_le_two_log S p k)
        _ = 2 * ((K : ℝ) * log p - log p) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hmem]
          simp only [Nat.card_Icc, Nat.add_sub_cancel]
          rw [Nat.cast_sub hK, Nat.cast_one]
          ring
    have hsum := Finset.sum_erase_add (Finset.Icc 1 K) (localLogCoeff S p) hmem
    rw [localLogCoeff_one S p] at hsum
    linarith

theorem localLogMass_prime_bounds (S : ℕ → Prop) (N : ℕ) :
    localAllowedPrimeLog S N ≤ localLogMass S N ∧
      localLogMass S N ≤ localAllowedPrimeLog S N +
        2 * (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) := by
  have hpoint (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :=
    localLogCoeff_sum_bounds S (Nat.prime_of_mem_primesBelow hp)
      (Nat.le_log_of_pow_le (Nat.prime_of_mem_primesBelow hp).one_lt
        (by have := (Nat.mem_primesBelow.mp hp).1; simpa using (show p ≤ N by omega)))
  constructor
  · apply Finset.sum_le_sum
    intro p hp
    exact (hpoint p hp).1
  · calc
      localLogMass S N ≤ ∑ p ∈ (N + 1).primesBelow,
          ((if S p then 0 else log p) + 2 * ((Nat.log p N : ℝ) * log p - log p)) :=
        Finset.sum_le_sum fun p hp => (hpoint p hp).2
      _ = _ := by
        rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log]
        simp only [Nat.primesLE, localAllowedPrimeLog, Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_sub_distrib]
        exact (Finset.mul_sum _ _ _).symm

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalEulerFactor.lean` -/

section
/-!
# Exact Euler factors of the local norm indicator
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem tsum_even_geometric {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    (∑' k : ℕ, if Even k then r ^ k else 0) = (1 - r ^ 2)⁻¹ := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have he (k : ℕ) : (if Even (2 * k) then r ^ (2 * k) else 0) = (r ^ 2) ^ k := by
    rw [if_pos (show Even (2 * k) from ⟨k, by omega⟩), pow_mul]
  have ho (k : ℕ) : (if Even (2 * k + 1) then r ^ (2 * k + 1) else 0) = 0 := by
    apply if_neg
    rintro ⟨j, hj⟩
    omega
  have heS : Summable (fun k : ℕ => if Even (2 * k) then r ^ (2 * k) else 0) := by
    simpa only [he] using summable_geometric_of_lt_one (sq_nonneg r) hr₂
  have hoS : Summable (fun k : ℕ => if Even (2 * k + 1) then r ^ (2 * k + 1) else 0) := by
    simp only [ho]
    exact summable_zero
  have hsum := tsum_even_add_odd (f := fun k : ℕ => if Even k then r ^ k else 0) heS hoS
  simpa only [he, ho, tsum_zero, add_zero, tsum_geometric_of_lt_one (sq_nonneg r) hr₂] using hsum.symm

theorem localDirichletTerm_prime_pow (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    (s : ℝ) (k : ℕ) :
    localDirichletTerm S s (p ^ k) =
      (if S p ∧ Odd k then 0 else 1) * (((p : ℝ) ^ s)⁻¹) ^ k := by
  rw [localDirichletTerm, localParity_prime_pow S hp, Nat.cast_pow,
    ← rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    rpow_mul_natCast (Nat.cast_nonneg p), div_eq_mul_inv, inv_pow]

theorem localDirichletTerm_eulerFactor (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 0 < s) :
    (∑' k : ℕ, localDirichletTerm S s (p ^ k)) =
      if S p then (1 - (((p : ℝ) ^ s)⁻¹) ^ 2)⁻¹ else (1 - ((p : ℝ) ^ s)⁻¹)⁻¹ := by
  classical
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr₀ : 0 ≤ ((p : ℝ) ^ s)⁻¹ := inv_nonneg.mpr (rpow_nonneg (Nat.cast_nonneg p) s)
  have hr₁ : ((p : ℝ) ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_rpow hpR hs)
  simp_rw [localDirichletTerm_prime_pow S hp s]
  by_cases hS : S p
  · rw [if_pos hS]
    have heq (k : ℕ) :
        (if S p ∧ Odd k then (0 : ℝ) else 1) * (((p : ℝ) ^ s)⁻¹) ^ k =
          if Even k then (((p : ℝ) ^ s)⁻¹) ^ k else 0 := by
      by_cases hk : Even k
      · simp [hS, hk, Nat.not_odd_iff_even.mpr hk]
      · simp [hS, hk, Nat.not_even_iff_odd.mp hk]
    simp_rw [heq]
    exact tsum_even_geometric hr₀ hr₁
  · simp only [hS, false_and, if_false, one_mul]
    exact tsum_geometric_of_lt_one hr₀ hr₁

theorem localParity_explicitEulerProduct (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes =>
        if S p then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2)⁻¹
        else (1 - (((p : ℕ) : ℝ) ^ s)⁻¹)⁻¹)
      (realDirichlet (localParity S) s) := by
  convert localParity_eulerProduct S hs using 1
  ext p
  exact (localDirichletTerm_eulerFactor S p.property (zero_lt_one.trans hs)).symm

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareEulerCorrection.lean` -/

section
/-!
# The convergent square Euler correction

The inert-prime correction to the square of the local Dirichlet series is
positive and continuous at `s = 1`. Uniform summability is proved on a whole
neighborhood of `1`, using the convergent `p^(-3/2)` majorant.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem neg_log_one_sub_bound {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1 / 2) :
    0 ≤ -log (1 - u) ∧ -log (1 - u) ≤ 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  refine ⟨neg_nonneg.mpr (log_nonpos hpos.le (by linarith)), ?_⟩
  have hlog : -log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    simpa only [log_inv] using log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have heq : (1 - u)⁻¹ - 1 = u / (1 - u) := by
    field_simp
    ring
  rw [heq] at hlog
  refine hlog.trans ((div_le_iff₀ hpos).mpr ?_)
  nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 1 - 2 * u)]

theorem squarePrimePower_bounds (p : Nat.Primes) (s : ℝ) :
    0 ≤ (((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) ∧
    (((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) ≤ (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
    (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 1 / 2 := by
  have hp₂ : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hp₁ : (1 : ℝ) ≤ (p : ℕ) := by linarith
  have hp₀ : (0 : ℝ) < (p : ℕ) := by linarith
  refine ⟨rpow_nonneg hp₀.le _, rpow_le_rpow_of_exponent_le hp₁ ?_, ?_⟩
  · have := le_max_left (3 / 4 : ℝ) s
    linarith
  · calc
      _ ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) := rpow_le_rpow_of_exponent_le hp₁ (by norm_num)
      _ = 1 / ((p : ℕ) : ℝ) := by rw [rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp₂

noncomputable def squareLogTerm (S : ℕ → Prop) (p : Nat.Primes) (s : ℝ) : ℝ :=
  if S p then -log (1 - ((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) else 0

theorem squareLogTerm_norm_le (S : ℕ → Prop) (p : Nat.Primes) (s : ℝ) :
    ‖squareLogTerm S p s‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨hu₀, hu₁, hu₂⟩ := squarePrimePower_bounds p s
  have hlog := neg_log_one_sub_bound hu₀ (hu₁.trans hu₂)
  unfold squareLogTerm
  split_ifs
  · rw [Real.norm_of_nonneg hlog.1]
    exact hlog.2.trans (mul_le_mul_of_nonneg_left hu₁ (by norm_num))
  · rw [norm_zero]
    positivity

theorem squareLogMajorant_summable :
    Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    summable_nat_rpow.mpr (by norm_num)
  exact (h.subtype Nat.Prime).mul_left 2

theorem squareLogTerm_summable (S : ℕ → Prop) (s : ℝ) :
    Summable (fun p : Nat.Primes => squareLogTerm S p s) :=
  Summable.of_norm_bounded squareLogMajorant_summable (fun p => squareLogTerm_norm_le S p s)

theorem continuous_squareLogTerm (S : ℕ → Prop) (p : Nat.Primes) :
    Continuous (squareLogTerm S p) := by
  unfold squareLogTerm
  split_ifs
  · apply Continuous.neg
    apply Continuous.log
    · apply continuous_const.sub
      exact (continuous_const_rpow (by exact_mod_cast p.property.ne_zero)).comp
        ((continuous_const.mul (continuous_const.max continuous_id)).neg)
    · intro s
      obtain ⟨_, h₁, h₂⟩ := squarePrimePower_bounds p s
      linarith
  · exact continuous_const

noncomputable def squareCorrection (S : ℕ → Prop) (s : ℝ) : ℝ :=
  exp (∑' p : Nat.Primes, squareLogTerm S p s)

theorem squareCorrection_pos (S : ℕ → Prop) (s : ℝ) : 0 < squareCorrection S s := exp_pos _

theorem continuous_squareCorrection (S : ℕ → Prop) : Continuous (squareCorrection S) :=
  continuous_exp.comp (continuous_tsum (continuous_squareLogTerm S)
    squareLogMajorant_summable (squareLogTerm_norm_le S))

theorem squareCorrection_hasProd (S : ℕ → Prop) {s : ℝ} (hs : 3 / 4 ≤ s) :
    HasProd (fun p : Nat.Primes =>
      if S p then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2)⁻¹ else 1)
      (squareCorrection S s) := by
  change HasProd _ (exp (∑' p : Nat.Primes, squareLogTerm S p s))
  apply (squareLogTerm_summable S s).hasSum.rexp.congr_fun
  intro p
  change (if S p then _ else 1) = exp (squareLogTerm S p s)
  unfold squareLogTerm
  by_cases hS : S p
  · rw [if_pos hS, if_pos hS, exp_neg]
    have hpos : 0 < 1 - ((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s)) := by
      have h := (squarePrimePower_bounds p s).2.1.trans (squarePrimePower_bounds p s).2.2
      linarith
    rw [exp_log hpos, max_eq_right hs]
    have hpow : ((p : ℕ) : ℝ) ^ (-(2 * s)) = ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2 := by
      let x : ℝ := (p : ℕ)
      have hx : 0 ≤ x := Nat.cast_nonneg (p : ℕ)
      change x ^ (-(2 * s)) = ((x ^ s)⁻¹) ^ 2
      rw [rpow_neg hx, mul_comm (2 : ℝ) s]
      exact (congrArg (fun t : ℝ => t⁻¹) (rpow_mul_natCast hx s 2)).trans (inv_pow _ _).symm
    exact (congrArg (fun t : ℝ => (1 - t)⁻¹) hpow).symm
  · simp only [if_neg hS, exp_zero]

end Bernays

end

/-! ### Upstream module `Util/Bernays/RamifiedEulerCorrection.lean` -/

section
/-!
# The finite ramified-prime correction
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def ramifiedPrimes (N : ℕ) : Finset Nat.Primes :=
  N.primeFactors.subtype Nat.Prime

theorem mem_ramifiedPrimes_iff {N : ℕ} (hN : N ≠ 0) (p : Nat.Primes) :
    p ∈ ramifiedPrimes N ↔ (p : ℕ) ∣ N := by
  constructor
  · intro hp
    have hm : (p : ℕ) ∈ N.primeFactors := Finset.mem_subtype.mp hp
    exact (Nat.mem_primeFactors.mp hm).2.1
  · intro hp
    exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property, hp, hN⟩)

theorem char_prime_eq_zero_iff {N : ℕ} (χ : DirichletCharacter ℂ N) (p : Nat.Primes) :
    χ p = 0 ↔ (p : ℕ) ∣ N := by
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime,
    p.property.coprime_iff_not_dvd, not_not]

theorem primeInversePower_lt_one (p : Nat.Primes) {s : ℝ} (hs : 0 < s) :
    ((((p : ℕ) : ℝ) ^ s)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_rpow (by exact_mod_cast p.property.one_lt) hs)

noncomputable def ramifiedCorrection (R : Finset Nat.Primes) (s : ℝ) : ℝ :=
  ∏ p ∈ R, (1 - ((((p : ℕ) : ℝ) ^ (max (3 / 4) s))⁻¹))⁻¹

theorem ramifiedCorrection_pos (R : Finset Nat.Primes) (s : ℝ) :
    0 < ramifiedCorrection R s := by
  apply Finset.prod_pos
  intro p _
  exact inv_pos.mpr (sub_pos.mpr (primeInversePower_lt_one p
    (lt_of_lt_of_le (by norm_num) (le_max_left (3 / 4 : ℝ) s))))

theorem continuous_ramifiedCorrection (R : Finset Nat.Primes) :
    Continuous (ramifiedCorrection R) := by
  apply continuous_finsetProd
  intro p _
  have hp₀ : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hpow : Continuous (fun s : ℝ => (((p : ℕ) : ℝ) ^ max (3 / 4) s)⁻¹) :=
    ((continuous_const_rpow hp₀.ne').comp (continuous_const.max continuous_id)).inv₀
      (fun _ => (rpow_pos_of_pos hp₀ _).ne')
  exact (continuous_const.sub hpow).inv₀ (fun s =>
    (sub_pos.mpr (primeInversePower_lt_one p
      (lt_of_lt_of_le (by norm_num) (le_max_left (3 / 4 : ℝ) s)))).ne')

theorem ramifiedCorrection_hasProd (R : Finset Nat.Primes) {s : ℝ} (hs : 3 / 4 ≤ s) :
    HasProd (fun p : Nat.Primes =>
      if p ∈ R then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹))⁻¹ else 1)
      (ramifiedCorrection R s) := by
  have h := hasProd_prod_of_ne_finset_one
    (L := SummationFilter.unconditional Nat.Primes) (s := R) (f := fun p : Nat.Primes =>
      if p ∈ R then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹))⁻¹ else 1)
    (by intro p hp; exact if_neg hp)
  simpa only [ramifiedCorrection, max_eq_right hs, Finset.prod_ite_mem, Finset.inter_self] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/CharacterKernelLimit.lean` -/

section
/-!
# Linear asymptotic of the quadratic-character logarithmic kernel
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def ramifiedPrimeLog {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, if χ p = 0 then log p else 0

theorem ramifiedPrimeLog_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {N : ℕ} (hN : q ≤ N) :
    ramifiedPrimeLog χ N = ∑ p ∈ q.primeFactors, log p := by
  have hset : ((N + 1).primesBelow.filter fun p : ℕ => χ p = 0) = q.primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hz⟩ := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primesBelow hp
      exact Nat.mem_primeFactors.mpr ⟨hprime,
        (char_prime_eq_zero_iff χ ⟨p, hprime⟩).mp hz, NeZero.ne q⟩
    · intro hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd).trans hN
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩,
        (char_prime_eq_zero_iff χ ⟨p, hprime⟩).mpr hdvd⟩
  rw [ramifiedPrimeLog, ← Finset.sum_filter, hset]

theorem ramifiedPrimeLog_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Tendsto (fun N : ℕ => ramifiedPrimeLog χ N / (N : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
    (∑ p ∈ q.primeFactors, log p)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop q] with N hN
  simp only [Function.comp_def, ramifiedPrimeLog_eq χ hN, div_eq_mul_inv]

theorem quadratic_allowedPrimeLog_identity {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (N : ℕ) :
    localAllowedPrimeLog (fun p : ℕ => χ p = -1) N =
      (Chebyshev.theta (N : ℝ) + realCharacterTheta χ N + ramifiedPrimeLog χ N) / 2 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  simp only [Nat.primesLE, realCharacterTheta, ramifiedPrimeLog, localAllowedPrimeLog,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₂ p with h | h | h
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]

theorem localAllowedPrimeLog_div_tendsto_half {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => localAllowedPrimeLog (fun p : ℕ => χ p = -1) N / (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have h := ((theta_div_tendsto_one.add (realCharacterTheta_div_tendsto_zero χ hχ)).add
    (ramifiedPrimeLog_div_tendsto_zero χ)).div_const 2
  simp only [add_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    rw [quadratic_allowedPrimeLog_identity χ hχ₂]
    ring

theorem localLogMass_div_tendsto_half {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => localLogMass (fun p : ℕ => χ p = -1) N / (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hbase := localAllowedPrimeLog_div_tendsto_half χ hχ₂ hχ
  have hupper := hbase.add (primePowerError_div_tendsto_zero.const_mul 2)
  simp only [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hbase hupper
  · intro N
    exact
      (div_le_div_of_nonneg_right (localLogMass_prime_bounds (fun p : ℕ => χ p = -1) N).1
        (Nat.cast_nonneg N))
  · intro N
    have h := div_le_div_of_nonneg_right
      (localLogMass_prime_bounds (fun p : ℕ => χ p = -1) N).2 (Nat.cast_nonneg N)
    simpa only [add_div, mul_div_assoc] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/CharacterEulerProduct.lean` -/

section
/-!
# The quadratic-character identity for the local Dirichlet series

Squaring the local norm series gives the product of zeta, a quadratic
Dirichlet L-function, and the convergent inert and ramified corrections.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem quadratic_euler_factor_identity (a r : ℂ) (ha : a = 0 ∨ a = 1 ∨ a = -1) :
    (if a = -1 then (1 - r ^ 2)⁻¹ else (1 - r)⁻¹) ^ 2 =
      (1 - r)⁻¹ * (1 - a * r)⁻¹ *
        (if a = -1 then (1 - r ^ 2)⁻¹ else 1) *
        (if a = 0 then (1 - r)⁻¹ else 1) := by
  rcases ha with rfl | rfl | rfl
  · norm_num
    simp only [← mul_inv, pow_two]
  · norm_num
    simp only [← mul_inv, pow_two]
  · norm_num
    have h : (1 - r)⁻¹ * (1 + r)⁻¹ = (1 - r ^ 2)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ring
    rw [h]
    simp only [← mul_inv, pow_two]

theorem prime_cpow_neg_real (p : Nat.Primes) (s : ℝ) :
    ((p : ℕ) : ℂ) ^ (-(s : ℂ)) = (((((p : ℕ) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.cpow_neg, Complex.ofReal_inv,
    Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) s]
  rfl

theorem localParity_dirichlet_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {s : ℝ} (hs : 1 < s) :
    (realDirichlet (localParity (fun p : ℕ => χ p = -1)) s : ℂ) ^ 2 =
      riemannZeta (s : ℂ) * χ.LFunction (s : ℂ) *
        (squareCorrection (fun p : ℕ => χ p = -1) s : ℂ) *
        (ramifiedCorrection (ramifiedPrimes N) s : ℂ) := by
  let S : ℕ → Prop := fun p => χ p = -1
  let r : Nat.Primes → ℂ := fun p => (((((p : ℕ) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)
  have hsC : 1 < (s : ℂ).re := hs
  have hs' : (3 / 4 : ℝ) ≤ s := by linarith
  have hf : HasProd (fun p : Nat.Primes =>
      if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹)
      (realDirichlet (localParity S) s : ℂ) := by
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (localParity_explicitEulerProduct S hs).map Complex.ofRealHom Complex.continuous_ofReal
  have hg : HasProd (fun p : Nat.Primes => if S p then (1 - r p ^ 2)⁻¹ else 1)
      (squareCorrection S s : ℂ) := by
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (squareCorrection_hasProd S hs').map Complex.ofRealHom Complex.continuous_ofReal
  have hR : HasProd (fun p : Nat.Primes => if χ p = 0 then (1 - r p)⁻¹ else 1)
      (ramifiedCorrection (ramifiedPrimes N) s : ℂ) := by
    have hz (p : Nat.Primes) : p ∈ ramifiedPrimes N ↔ χ p = 0 :=
      (mem_ramifiedPrimes_iff (NeZero.ne N) p).trans (char_prime_eq_zero_iff χ p).symm
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, hz] using
      (ramifiedCorrection_hasProd (ramifiedPrimes N) hs').map
        Complex.ofRealHom Complex.continuous_ofReal
  have hζ : HasProd (fun p : Nat.Primes => (1 - r p)⁻¹) (riemannZeta (s : ℂ)) := by
    apply (riemannZeta_eulerProduct_hasProd hsC).congr_fun
    intro p
    rw [prime_cpow_neg_real]
  have hL : HasProd (fun p : Nat.Primes => (1 - χ p * r p)⁻¹) (χ.LFunction (s : ℂ)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hsC]
    apply (χ.LSeries_eulerProduct_hasProd hsC).congr_fun
    intro p
    rw [prime_cpow_neg_real]
  have hright := ((hζ.mul hL).mul hg).mul hR
  have hright' : HasProd
      (fun p : Nat.Primes => (if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹) ^ 2)
      (riemannZeta (s : ℂ) * χ.LFunction (s : ℂ) *
        (squareCorrection S s : ℂ) * (ramifiedCorrection (ramifiedPrimes N) s : ℂ)) := by
    apply hright.congr_fun
    intro p
    exact quadratic_euler_factor_identity (χ p) (r p)
      (MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p)
  have hleft := hf.mul hf
  have hleft' : HasProd
      (fun p : Nat.Primes => (if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹) ^ 2)
      ((realDirichlet (localParity S) s : ℂ) ^ 2) := by
    simpa only [pow_two] using hleft
  exact hleft'.unique hright'

end Bernays

end

/-! ### Upstream module `Util/Bernays/CharacterNormLimit.lean` -/

section
/-!
# The exact half-pole of the local norm series

The zeta residue and nonvanishing of a nontrivial quadratic Dirichlet
L-function give the positive constant needed by the Tauberian theorem.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem tendsto_real_one_add_zero :
    Tendsto (fun t : ℝ => 1 + t) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  simpa only [add_zero] using
    ((show Continuous (fun t : ℝ => (1 : ℝ) + t) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_complex_one_add_zero :
    Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  simpa only [Complex.ofReal_zero, add_zero] using
    ((show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ)) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_zeta_norm_residue :
    Tendsto (fun t : ℝ => t * ‖riemannZeta ((1 : ℂ) + (t : ℂ))‖)
      (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  have hshift : Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ))
      (𝓝[Set.Ioi 0] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_complex_one_add_zero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (1 : ℂ) + (t : ℂ) ≠ 1
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hr
    have : 0 < t := ht
    linarith
  have h := (riemannZeta_residue_one.comp hshift).norm
  rw [norm_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change ‖((1 : ℂ) + (t : ℂ) - 1) * riemannZeta ((1 : ℂ) + (t : ℂ))‖ = _
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

noncomputable def characterLocalConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  sqrt (‖χ.LFunction 1‖ * squareCorrection (fun p : ℕ => χ p = -1) 1 *
    ramifiedCorrection (ramifiedPrimes N) 1)

theorem characterLocalConstant_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : 0 < characterLocalConstant χ := by
  apply sqrt_pos.mpr
  exact mul_pos (mul_pos (norm_pos_iff.mpr (χ.LFunction_apply_one_ne_zero hχ))
    (squareCorrection_pos _ _)) (ramifiedCorrection_pos _ _)

theorem localParity_realDirichlet_nonneg (S : ℕ → Prop) (s : ℝ) :
    0 ≤ realDirichlet (localParity S) s :=
  tsum_nonneg fun n => div_nonneg (localParity_nonneg S (n + 1))
    (rpow_nonneg (Nat.cast_nonneg _) s)

theorem localParity_dirichlet_halfPole {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun t : ℝ => sqrt t * realDirichlet (localParity (fun p : ℕ => χ p = -1)) (1 + t))
      (𝓝[Set.Ioi 0] 0) (𝓝 (characterLocalConstant χ)) := by
  let S : ℕ → Prop := fun p => χ p = -1
  let F : ℝ → ℝ := realDirichlet (localParity S)
  let G : ℝ → ℝ := squareCorrection S
  let R : ℝ → ℝ := ramifiedCorrection (ramifiedPrimes N)
  have hF (s : ℝ) : 0 ≤ F s := localParity_realDirichlet_nonneg S s
  have hL : Tendsto (fun t : ℝ => ‖χ.LFunction ((1 : ℂ) + (t : ℂ))‖)
      (𝓝[Set.Ioi 0] 0) (𝓝 ‖χ.LFunction 1‖) :=
    (((χ.differentiableAt_LFunction 1 (Or.inr hχ)).continuousAt.tendsto).comp
      tendsto_complex_one_add_zero).norm
  have hG : Tendsto (fun t : ℝ => G (1 + t)) (𝓝[Set.Ioi 0] 0) (𝓝 (G 1)) :=
    (continuous_squareCorrection S).continuousAt.tendsto.comp tendsto_real_one_add_zero
  have hR : Tendsto (fun t : ℝ => R (1 + t)) (𝓝[Set.Ioi 0] 0) (𝓝 (R 1)) :=
    (continuous_ramifiedCorrection (ramifiedPrimes N)).continuousAt.tendsto.comp tendsto_real_one_add_zero
  have hm := ((tendsto_zeta_norm_residue.mul hL).mul hG).mul hR
  simp only [one_mul] at hm
  have hsq : Tendsto (fun t : ℝ => t * (F (1 + t)) ^ 2) (𝓝[Set.Ioi 0] 0)
      (𝓝 (‖χ.LFunction 1‖ * G 1 * R 1)) := by
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hs : 1 < 1 + t := by have : 0 < t := ht; linarith
    have heq := congrArg norm (localParity_dirichlet_square χ hχ₂ hs)
    simp only [Complex.ofReal_add, Complex.ofReal_one] at heq
    have hGn : 0 ≤ G (1 + t) := (squareCorrection_pos S (1 + t)).le
    have hRn : 0 ≤ R (1 + t) := (ramifiedCorrection_pos (ramifiedPrimes N) (1 + t)).le
    change ‖(F (1 + t) : ℂ) ^ 2‖ =
      ‖riemannZeta ((1 : ℂ) + (t : ℂ)) * χ.LFunction ((1 : ℂ) + (t : ℂ)) *
        (G (1 + t) : ℂ) * (R (1 + t) : ℂ)‖ at heq
    simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hF (1 + t)), abs_of_nonneg hGn, abs_of_nonneg hRn] at heq
    change t * ‖riemannZeta ((1 : ℂ) + (t : ℂ))‖ * ‖χ.LFunction ((1 : ℂ) + (t : ℂ))‖ *
      G (1 + t) * R (1 + t) = t * F (1 + t) ^ 2
    rw [heq]
    ring
  have hroot := (continuous_sqrt.tendsto (‖χ.LFunction 1‖ * G 1 * R 1)).comp hsq
  apply hroot.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change sqrt (t * F (1 + t) ^ 2) = sqrt t * F (1 + t)
  rw [sqrt_mul (le_of_lt ht), sqrt_sq (hF (1 + t))]

theorem localParity_reciprocal_asymptotic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => reciprocalSum (localParity (fun p : ℕ => χ p = -1)) ⌊x⌋₊ /
      sqrt (log x)) atTop (𝓝 (2 * characterLocalConstant χ / sqrt π)) :=
  reciprocalSum_div_sqrt_log_tendsto (localParity_nonneg _) (localParity_le_one _)
    (characterLocalConstant_pos χ hχ) (localParity_dirichlet_halfPole χ hχ₂ hχ)

end Bernays

end

/-! ### Upstream module `Util/Bernays/WirsingRecurrence.lean` -/

section
/-!
# Quantitative error control for the logarithmic recurrence

A linear asymptotic for the logarithmic kernel gives an error bounded by
`ε*N*H(N) + O(N)`, where `H` is the reciprocal partial sum. This turns the
half-power reciprocal asymptotic into the ordinary Bernays counting scale.
-/

open Filter Topology Real

namespace Bernays

theorem reciprocalSum_eq_sum_Icc (a : ℕ → ℝ) (N : ℕ) :
    reciprocalSum a N = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) := by
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩
  · intro n _ m _ hnm
    omega
  · intro n hn
    refine ⟨n - 1, Finset.mem_range.mpr ?_, ?_⟩ <;>
      have := Finset.mem_Icc.mp hn <;> omega
  · intro n _
    rfl

theorem ordinarySum_le {a : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (N : ℕ) :
    ordinarySum a N ≤ N := by
  calc
    ordinarySum a N ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum fun n _ => ha n
    _ = N := by simp

theorem kernel_global_linear_error {K : ℕ → ℝ} {κ : ℝ}
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hK ε hε
  let M : ℕ := max N₀ 1
  let C : ℝ := ∑ n ∈ Finset.range M, |K n - κ * n|
  have hC : 0 ≤ C := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hN : N < M
  · have hterm : |K N - κ * N| ≤ C :=
      Finset.single_le_sum (f := fun n : ℕ => |K n - κ * n|)
        (fun n _ => abs_nonneg _) (Finset.mem_range.mpr hN)
    exact hterm.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg N)))
  · have hNM : M ≤ N := Nat.le_of_not_gt hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hNM))
    have hr := hN₀ N ((le_max_left N₀ 1).trans hNM)
    rw [Real.dist_eq] at hr
    have heq : K N - κ * N = (K N / (N : ℝ) - κ) * N := by field_simp
    rw [heq, abs_mul, abs_of_pos hNpos]
    exact (mul_le_mul_of_nonneg_right hr.le hNpos.le).trans (le_add_of_nonneg_right hC)

theorem kernel_quotient_error {K : ℕ → ℝ} {κ ε C : ℝ}
    (hε : 0 ≤ ε) (hK : ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C)
    (N : ℕ) {m : ℕ} (hm : 0 < m) :
    |K (N / m) - κ * ((N : ℝ) / m)| ≤ ε * ((N : ℝ) / m) + C + |κ| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq₀ : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hq₁ : (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hmR).mpr
    have h := Nat.lt_mul_div_succ N hm
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  have hdist : |((N / m : ℕ) : ℝ) - (N : ℝ) / m| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq₀)]
    linarith
  have hκ : |κ * ((N / m : ℕ) : ℝ) - κ * ((N : ℝ) / m)| ≤ |κ| := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left hdist (abs_nonneg κ)).trans_eq (mul_one _)
  calc
    _ ≤ |K (N / m) - κ * ((N / m : ℕ) : ℝ)| +
        |κ * ((N / m : ℕ) : ℝ) - κ * ((N : ℝ) / m)| := abs_sub_le _ _ _
    _ ≤ (ε * ((N / m : ℕ) : ℝ) + C) + |κ| := add_le_add (hK _) hκ
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hq₀ hε]

theorem logarithmicRecurrence_error {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hK : ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C) (N : ℕ) :
    |logarithmicSum a N - κ * N * reciprocalSum a N| ≤
      ε * N * reciprocalSum a N + (C + |κ|) * N := by
  have heq : logarithmicSum a N - κ * N * reciprocalSum a N =
      ∑ m ∈ Finset.Icc 1 N, a m * (K (N / m) - κ * ((N : ℝ) / m)) := by
    rw [hrec, reciprocalSum_eq_sum_Icc, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [heq]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 N, |a m * (K (N / m) - κ * ((N : ℝ) / m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N, a m * (ε * ((N : ℝ) / m) + C + |κ|) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul, abs_of_nonneg (ha m)]
      exact mul_le_mul_of_nonneg_left
        (kernel_quotient_error hε hK N (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)) (ha m)
    _ = ε * N * reciprocalSum a N + (C + |κ|) * ordinarySum a N := by
      rw [reciprocalSum_eq_sum_Icc, ordinarySum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      linarith [mul_le_mul_of_nonneg_left (ordinarySum_le ha₁ N) (add_nonneg hC (abs_nonneg κ))]

theorem logarithmicRecurrence_asymptotic {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ H : ℝ} (hH₀ : 0 ≤ H)
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    (hH : Tendsto (fun N : ℕ => reciprocalSum a N / sqrt (log (N : ℝ))) atTop (𝓝 H)) :
    Tendsto (fun N : ℕ => logarithmicSum a N / ((N : ℝ) * sqrt (log (N : ℝ))))
      atTop (𝓝 (κ * H)) := by
  let D : ℕ → ℝ := fun N =>
    (logarithmicSum a N - κ * N * reciprocalSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))
  have hden : Tendsto (fun N : ℕ => sqrt (log (N : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hD : Tendsto D atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := ε / (4 * (H + 1))
    have hHp : 0 < H + 1 := by linarith
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hHp)
    have hδeq : δ * (H + 1) = ε / 4 := by
      dsimp only [δ]
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hHp.ne']
    obtain ⟨C, hC, hKC⟩ := kernel_global_linear_error hK hδ
    have htail : Tendsto (fun N : ℕ => (C + |κ|) / sqrt (log (N : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero, ← div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp hden).const_mul (C + |κ|)
    filter_upwards [hH.eventually (gt_mem_nhds (lt_add_one H)),
      htail.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop 2] with N hHN htailN hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
    have herror := logarithmicRecurrence_error ha ha₁ hrec hδ.le hC hKC N
    have hdiv := div_le_div_of_nonneg_right herror (mul_pos hNp hLp).le
    have hsplit : (δ * N * reciprocalSum a N + (C + |κ|) * N) /
        ((N : ℝ) * sqrt (log (N : ℝ))) =
        δ * (reciprocalSum a N / sqrt (log (N : ℝ))) + (C + |κ|) / sqrt (log (N : ℝ)) := by
      field_simp
    rw [hsplit] at hdiv
    rw [Real.dist_eq, sub_zero]
    change |(logarithmicSum a N - κ * N * reciprocalSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))| < ε
    rw [abs_div, abs_of_pos (mul_pos hNp hLp)]
    have hmul := mul_lt_mul_of_pos_left hHN hδ
    linarith
  have hsum := (hH.const_mul κ).add hD
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
  change κ * (reciprocalSum a N / sqrt (log (N : ℝ))) + D N = _
  dsimp only [D]
  field_simp
  ring

theorem ordinarySum_asymptotic_of_recurrence {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ H : ℝ} (hH₀ : 0 ≤ H)
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    (hH : Tendsto (fun N : ℕ => reciprocalSum a N / sqrt (log (N : ℝ))) atTop (𝓝 H)) :
    Tendsto (fun N : ℕ => ordinarySum a N / ((N : ℝ) / sqrt (log (N : ℝ))))
      atTop (𝓝 (κ * H)) :=
  ordinarySum_asymptotic_of_logarithmicSum ha ha₁
    (logarithmicRecurrence_asymptotic ha ha₁ hrec hH₀ hK hH)

end Bernays

end

/-! ### Upstream module `Util/BinQuadForm.lean` -/

section
/-!
# Integral binary quadratic forms and their represented-value count

The counting function counts values, not representations. In particular,
changes of integral coordinates preserve it without any multiplicity factor.
-/

/-- An (integral) binary quadratic form `f(X,Y) = a X^2 + b X Y + c Y^2`. -/
structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ

namespace BinQuadForm

/-- Evaluate the form on integer inputs. -/
def eval (f : BinQuadForm) (x y : ℤ) : ℤ :=
  f.a * x * x + f.b * x * y + f.c * y * y

/-- Discriminant `Δ = b^2 - 4ac`. -/
def discr (f : BinQuadForm) : ℤ :=
  f.b * f.b - 4 * f.a * f.c

/-- `f` is primitive if `gcd(a,b,c) = 1`. -/
def Primitive (f : BinQuadForm) : Prop :=
  Int.gcd f.a (Int.gcd f.b f.c) = 1

/--
A convenient (sufficient) positive-definiteness condition for integral binary quadratic forms:
`a > 0` and discriminant is negative.
(For integer forms this is equivalent to positive definiteness over `ℝ`.)
-/
def PosDef (f : BinQuadForm) : Prop :=
  0 < f.a ∧ f.discr < 0

/--
Counting function `B_f(x)`: number of *natural numbers* `n ≤ x` represented by `f`.
(Here “represented” means `∃ u v : ℤ, f(u,v) = n`.)
-/
noncomputable def B (f : BinQuadForm) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)}

theorem eval_zero_zero (f : BinQuadForm) : f.eval 0 0 = 0 := by
  simp [eval]

/-- Completing the square in integral coordinates. -/
theorem four_mul_a_mul_eval (f : BinQuadForm) (u v : ℤ) :
    4 * f.a * f.eval u v = (2 * f.a * u + f.b * v) ^ 2 - f.discr * v ^ 2 := by
  simp only [eval, discr]
  ring

theorem PosDef.eval_nonneg {f : BinQuadForm} (hf : f.PosDef) (u v : ℤ) :
    0 ≤ f.eval u v := by
  have h := f.four_mul_a_mul_eval u v
  have hprod : 0 ≤ -f.discr * v ^ 2 := mul_nonneg (neg_nonneg.mpr hf.2.le) (sq_nonneg v)
  have ha : 0 < 4 * f.a := mul_pos (by norm_num) hf.1
  have hnonneg : 0 ≤ 4 * f.a * f.eval u v := by
    rw [h]
    linarith [sq_nonneg (2 * f.a * u + f.b * v)]
  exact (mul_nonneg_iff_of_pos_left ha).mp hnonneg

theorem PosDef.eval_eq_zero_iff {f : BinQuadForm} (hf : f.PosDef) (u v : ℤ) :
    f.eval u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hzero
    have h := f.four_mul_a_mul_eval u v
    rw [hzero, mul_zero] at h
    have hv : v = 0 := by
      by_contra hv
      have hpos : 0 < -f.discr * v ^ 2 :=
        mul_pos (neg_pos.mpr hf.2) (sq_pos_of_ne_zero hv)
      linarith [sq_nonneg (2 * f.a * u + f.b * v)]
    refine ⟨?_, hv⟩
    have hu : (2 * f.a * u) ^ 2 = 0 := by simpa [hv] using h.symm
    have hmul : 2 * f.a * u = 0 := sq_eq_zero_iff.mp hu
    exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hf.1.ne')
  · rintro ⟨rfl, rfl⟩
    exact f.eval_zero_zero

open scoped Classical in
/-- A finite-set presentation of the exact counting function. -/
theorem B_eq_card_filter (f : BinQuadForm) {x : ℝ} (hx : 0 ≤ x) :
    f.B x = ((Finset.range (⌊x⌋₊ + 1)).filter
      (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ))).card := by
  classical
  unfold B
  have hset : {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)} =
      ↑((Finset.range (⌊x⌋₊ + 1)).filter
        (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ))) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/Normalization.lean` -/

section
/-!
# Endpoint and normalization lemmas for Bernays' theorem

These lemmas retain the original real endpoint count. They permit the arithmetic
argument to be carried out at natural endpoints and then transfer its exact
asymptotic, with the same constant, to the statement over `ℝ`.
-/

open Filter Asymptotics
open scoped Topology

namespace BinQuadForm

theorem B_natFloor (f : BinQuadForm) {x : ℝ} (hx : 0 ≤ x) :
    f.B (⌊x⌋₊ : ℝ) = f.B x := by
  rw [f.B_eq_card_filter (Nat.cast_nonneg _), f.B_eq_card_filter hx]
  simp only [Nat.floor_natCast]

end BinQuadForm

namespace Bernays

/-- The normalization appearing in the original theorem. -/
noncomputable def scale (x : ℝ) : ℝ := x / Real.sqrt (Real.log x)

theorem scale_pos {x : ℝ} (hx : 1 < x) : 0 < scale x :=
  div_pos (zero_lt_one.trans hx) (Real.sqrt_pos.mpr (Real.log_pos hx))

theorem scale_tendsto_atTop : Tendsto scale atTop atTop := by
  have h := (tendsto_exp_div_rpow_atTop (1 / 2)).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, scale, Real.exp_log hx, Real.sqrt_eq_rpow]

theorem sqrt_isEquivalent {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h : f ~[l] g) (hg : ∀ᶠ x in l, 0 < g x) :
    (fun x => Real.sqrt (f x)) ~[l] (fun x => Real.sqrt (g x)) := by
  have ht := (isEquivalent_iff_tendsto_one (hg.mono fun _ hx => hx.ne')).mp h
  apply isEquivalent_of_tendsto_one
  have hs := ht.sqrt
  simp only [Real.sqrt_one] at hs
  apply hs.congr'
  filter_upwards [hg] with x hx
  exact Real.sqrt_div' _ hx.le

theorem scale_natFloor_isEquivalent :
    (fun x : ℝ => scale (⌊x⌋₊ : ℝ)) ~[atTop] scale := by
  have hfloor : (fun x : ℝ => (⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x) :=
    isEquivalent_nat_floor
  have hlog := hfloor.log tendsto_id
  have hsqrt := sqrt_isEquivalent hlog
    (Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0))
  exact hfloor.div hsqrt

theorem constant_scale_natFloor_isEquivalent (C : ℝ) :
    (fun x : ℝ => C * (⌊x⌋₊ : ℝ) / Real.sqrt (Real.log (⌊x⌋₊ : ℝ))) ~[atTop]
      (fun x : ℝ => C * x / Real.sqrt (Real.log x)) := by
  have h := (IsEquivalent.refl : (fun _ : ℝ => C) ~[atTop] (fun _ => C)).mul
    scale_natFloor_isEquivalent
  change (fun x : ℝ => C * ((⌊x⌋₊ : ℝ) / Real.sqrt (Real.log (⌊x⌋₊ : ℝ)))) ~[atTop]
    (fun x : ℝ => C * (x / Real.sqrt (Real.log x))) at h
  simpa only [mul_div_assoc] using h

/-- Natural and real endpoint versions have exactly the same asymptotic constant. -/
theorem real_asymptotic_iff_nat (f : BinQuadForm) (C : ℝ) :
    ((fun x : ℝ => (f.B x : ℝ)) ~[atTop]
      (fun x : ℝ => C * x / Real.sqrt (Real.log x))) ↔
    ((fun N : ℕ => (f.B (N : ℝ) : ℝ)) ~[atTop]
      (fun N : ℕ => C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)))) := by
  constructor
  · intro h
    exact h.comp_tendsto tendsto_natCast_atTop_atTop
  · intro h
    have hfloor := h.comp_tendsto (tendsto_nat_floor_atTop (α := ℝ))
    have hreal := hfloor.trans (constant_scale_natFloor_isEquivalent C)
    apply hreal.congr_left
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact congrArg (fun n : ℕ => (n : ℝ)) (f.B_natFloor hx)

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalCountingAsymptotic.lean` -/

section
/-!
# Exact counting asymptotic for quadratic-character local conditions

This counts positive integers in which each prime with character value `-1`
has even valuation. The result concerns local conditions; representing a number
by a specified quadratic form requires the separate form-class argument.
-/

open Filter Topology Real Asymptotics
open scoped Classical

namespace Bernays

theorem localParity_ordinarySum_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
      ((N : ℝ) / sqrt (log (N : ℝ)))) atTop (𝓝 (characterLocalConstant χ / sqrt π)) := by
  have hH : Tendsto (fun N : ℕ => reciprocalSum (localParity (fun p : ℕ => χ p = -1)) N /
      sqrt (log (N : ℝ))) atTop (𝓝 (2 * characterLocalConstant χ / sqrt π)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      (localParity_reciprocal_asymptotic χ hχ₂ hχ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hC := (characterLocalConstant_pos χ hχ).le
  have h := ordinarySum_asymptotic_of_recurrence (localParity_nonneg _) (localParity_le_one _)
    (localParity_logarithmic_convolution _) (by positivity : 0 ≤ 2 * characterLocalConstant χ / sqrt π)
    (localLogMass_div_tendsto_half χ hχ₂ hχ) hH
  have heq : (1 / 2 : ℝ) * (2 * characterLocalConstant χ / sqrt π) =
      characterLocalConstant χ / sqrt π := by ring
  rwa [heq] at h

theorem localParity_ordinarySum_isEquivalent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (fun N : ℕ => ordinarySum (localParity (fun p : ℕ => χ p = -1)) N) ~[atTop]
      (fun N : ℕ => (characterLocalConstant χ / sqrt π) * (N : ℝ) / sqrt (log (N : ℝ))) := by
  have hC : characterLocalConstant χ / sqrt π ≠ 0 :=
    (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)).ne'
  apply isEquivalent_of_tendsto_one
  have h := (localParity_ordinarySum_limit χ hχ₂ hχ).div_const (characterLocalConstant χ / sqrt π)
  rw [div_self hC] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    change ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
      ((N : ℝ) / sqrt (log (N : ℝ))) / (characterLocalConstant χ / sqrt π) =
      ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
        ((characterLocalConstant χ / sqrt π) * (N : ℝ) / sqrt (log (N : ℝ)))
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

noncomputable def localCount (S : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => ParityAdmissible S n).card

theorem localCount_eq_ordinarySum (S : ℕ → Prop) (N : ℕ) :
    (localCount S N : ℝ) = ordinarySum (localParity S) N := by
  rw [localCount, ordinarySum, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [localParity, hn₀, true_and]

theorem localCount_isEquivalent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (fun x : ℝ => (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => (characterLocalConstant χ / sqrt π) * x / sqrt (log x)) := by
  have h := (localParity_ordinarySum_isEquivalent χ hχ₂ hχ).comp_tendsto
    (tendsto_nat_floor_atTop (α := ℝ))
  have h' := h.trans (constant_scale_natFloor_isEquivalent (characterLocalConstant χ / sqrt π))
  simpa only [localCount_eq_ordinarySum, Function.comp_def] using h'

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalDilation.lean` -/

section
/-!
# Fixed dilations of the local counting asymptotic
-/

open Filter Topology Asymptotics Real
open scoped Classical

namespace Bernays

theorem parityAdmissible_mul_of_unobstructed (S : ℕ → Prop) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) :
    ParityAdmissible S (m * n) ↔ ParityAdmissible S n := by
  have heq (p : ℕ) (hp : p.Prime) (hSp : S p) : padicValNat p (m * n) = padicValNat p n := by
    letI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hm.ne' hn.ne', padicValNat.eq_zero_of_not_dvd (hS p hp hSp), zero_add]
  exact ⟨fun h p hp hSp => (heq p hp hSp) ▸ h p hp hSp,
    fun h p hp hSp => (heq p hp hSp).symm ▸ h p hp hSp⟩

theorem localCount_divisible (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) (N : ℕ) :
    (((Finset.Icc 1 N).filter fun n => ParityAdmissible S n).filter fun n => m ∣ n).card =
      localCount S (N / m) := by
  symm
  unfold localCount
  apply Finset.card_bij (fun n _ => m * n)
  · intro n hn
    obtain ⟨hnI, hnS⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hm hnpos,
        by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp (Finset.mem_Icc.mp hnI).2⟩
    · exact (parityAdmissible_mul_of_unobstructed S hm hnpos hS).mpr hnS
  · intro n _ k _ h
    exact Nat.mul_left_cancel hm h
  · intro n hn
    obtain ⟨hnA, hmn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hnS⟩ := Finset.mem_filter.mp hnA
    obtain ⟨k, rfl⟩ := hmn
    have hk : 0 < k := Nat.pos_of_mul_pos_left (Finset.mem_Icc.mp hnI).1
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, ?_⟩, ?_⟩, rfl⟩
    · apply (Nat.le_div_iff_mul_le hm).mpr
      simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hnI).2
    · exact (parityAdmissible_mul_of_unobstructed S hm hk hS).mp hnS

theorem scale_dilation_limit {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => scale (x / d) / scale x) atTop (𝓝 d⁻¹) := by
  have hsmall : Tendsto (fun x : ℝ => log d / log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_log_atTop).const_mul (log d)
  have hlog : Tendsto (fun x : ℝ => log (x / d) / log x) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [log_div (zero_lt_one.trans hx).ne' hd.ne', sub_div, div_self (log_pos hx).ne']
  have hsqrt : Tendsto (fun x : ℝ => sqrt (log (x / d)) / sqrt (log x)) atTop (𝓝 1) := by
    have h := hlog.sqrt
    rw [sqrt_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sqrt_div' _ (log_pos hx).le
  have h := hsqrt.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h' := h.const_mul d⁻¹
  simp only [inv_one, mul_one] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (max 1 d)] with x hx
  have hx₀ : x ≠ 0 := (zero_lt_one.trans (lt_of_le_of_lt (le_max_left _ _) hx)).ne'
  have hL : sqrt (log x) ≠ 0 := (sqrt_pos.mpr (log_pos (lt_of_le_of_lt (le_max_left _ _) hx))).ne'
  have hLd : sqrt (log (x / d)) ≠ 0 :=
    (sqrt_pos.mpr (log_pos ((one_lt_div hd).mpr (lt_of_le_of_lt (le_max_right _ _) hx)))).ne'
  dsimp only [scale]
  field_simp

theorem localCount_dilation_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => (localCount (fun p : ℕ => χ p = -1) (N / m) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) / m)) := by
  let C := characterLocalConstant χ / sqrt π
  have hC : C ≠ 0 := (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)).ne'
  have hloc : Tendsto (fun x : ℝ =>
      (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) / scale x) atTop (𝓝 C) := by
    have heq := localCount_isEquivalent χ hχ₂ hχ
    have ht := (isEquivalent_iff_tendsto_one (show ∀ᶠ x : ℝ in atTop,
        C * x / sqrt (log x) ≠ 0 by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_ne_zero (mul_ne_zero hC (zero_lt_one.trans hx).ne') (sqrt_pos.mpr (log_pos hx)).ne')).mp heq
    have h := ht.mul_const C
    rw [one_mul] at h
    apply h.congr'
    exact Eventually.of_forall fun x => by
      change (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) /
        (C * x / sqrt (log x)) * C =
        (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) / (x / sqrt (log x))
      rw [mul_div_assoc, mul_comm C, div_mul_eq_div_div, div_mul_cancel₀ _ hC]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (hloc.comp (tendsto_id.atTop_div_const hmR)).mul (scale_dilation_limit hmR)
  have h' := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto _ _ (𝓝 (C * (m : ℝ)⁻¹)) at h'
  rw [← div_eq_mul_inv] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop m] with N hN
  have hscale : scale ((N : ℝ) / m) ≠ 0 :=
    (scale_pos ((one_lt_div hmR).mpr (by exact_mod_cast hN))).ne'
  dsimp only [Function.comp_def, id_eq]
  rw [div_mul_div_cancel₀ hscale, Nat.floor_div_natCast, Nat.floor_natCast]

end Bernays

end

/-! ### Upstream module `Util/Bernays/AnalyticSquareDerivative.lean` -/

section
/-!
# Derivative bounds for a holomorphic square root

These estimates do not choose a branch of the square root. They apply directly
to an analytic function whose square has bounded derivative on a larger region.
-/

open Set Metric

namespace Bernays

theorem deriv_square_norm {f F : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (_hF : DifferentiableAt ℂ F z)
    (heq : F =ᶠ[nhds z] fun w => f w ^ 2) :
    ‖deriv F z‖ = 2 * ‖f z‖ * ‖deriv f z‖ := by
  have hd := (hf.hasDerivAt.pow 2).congr_of_eventuallyEq heq
  rw [hd.deriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, norm_mul, Complex.norm_ofNat]

theorem norm_le_sqrt_of_sq_eq {u v : ℂ} {a : ℝ} (heq : u ^ 2 = v) (hv : ‖v‖ ≤ a) :
    ‖u‖ ≤ Real.sqrt a := by
  apply (Real.le_sqrt (norm_nonneg _) ((norm_nonneg v).trans hv)).mpr
  rw [← norm_pow, heq]
  exact hv

theorem sqrt_mul_norm_deriv_le {f F : ℂ → ℂ} {z : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L)
    (hf : DiffContOnCl ℂ f (ball z r))
    (hF : DifferentiableAt ℂ F z)
    (heq : ∀ w ∈ closedBall z r, F w = f w ^ 2)
    (hderiv : ‖deriv F z‖ ≤ L)
    (hvar : ∀ w ∈ sphere z r, ‖F w - F z‖ ≤ L * r) :
    Real.sqrt r * ‖deriv f z‖ ≤ L + 1 := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsrsq := Real.sq_sqrt hr.le
  have hcenter := heq z (mem_closedBall_self hr.le)
  by_cases hsmall : ‖f z‖ ^ 2 ≤ r
  · have hbound : ∀ w ∈ sphere z r, ‖f w‖ ≤ Real.sqrt ((L + 1) * r) := by
      intro w hw
      apply norm_le_sqrt_of_sq_eq (heq w (sphere_subset_closedBall hw)).symm
      have hval : ‖F z‖ ≤ r := by simpa only [hcenter, norm_pow] using hsmall
      calc
        ‖F w‖ = ‖(F w - F z) + F z‖ := by rw [sub_add_cancel]
        _ ≤ ‖F w - F z‖ + ‖F z‖ := norm_add_le _ _
        _ ≤ L * r + r := add_le_add (hvar w hw) hval
        _ = (L + 1) * r := by ring
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf hbound
    have hsqrt : Real.sqrt ((L + 1) * r) = Real.sqrt (L + 1) * Real.sqrt r :=
      Real.sqrt_mul (by linarith) _
    rw [hsqrt] at hC
    have hprod := (le_div_iff₀ hr).mp hC
    have hstep : Real.sqrt r * ‖deriv f z‖ ≤ Real.sqrt (L + 1) := by
      have hid : ‖deriv f z‖ * r = Real.sqrt r * (Real.sqrt r * ‖deriv f z‖) := by
        calc
          _ = ‖deriv f z‖ * Real.sqrt r ^ 2 := congrArg (‖deriv f z‖ * ·) hsrsq.symm
          _ = _ := by ring
      rw [hid, mul_comm (Real.sqrt (L + 1)) (Real.sqrt r)] at hprod
      exact (mul_le_mul_iff_right₀ hsr).mp hprod
    apply hstep.trans
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  · have hbig : Real.sqrt r ≤ ‖f z‖ := by nlinarith [norm_nonneg (f z)]
    have hevent : F =ᶠ[nhds z] fun w => f w ^ 2 :=
      Filter.eventually_of_mem (closedBall_mem_nhds z hr) heq
    have hnorm := deriv_square_norm (hf.differentiableAt isOpen_ball (mem_ball_self hr)) hF hevent
    have hnonneg := norm_nonneg (deriv f z)
    nlinarith [mul_le_mul_of_nonneg_right hbig hnonneg]

theorem sqrt_mul_norm_deriv_le_of_deriv_bound {f F : ℂ → ℂ} {z : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L)
    (hf : DiffContOnCl ℂ f (ball z r))
    (hF : ∀ w ∈ closedBall z r, DifferentiableAt ℂ F w)
    (heq : ∀ w ∈ closedBall z r, F w = f w ^ 2)
    (hderiv : ∀ w ∈ closedBall z r, ‖deriv F w‖ ≤ L) :
    Real.sqrt r * ‖deriv f z‖ ≤ L + 1 := by
  apply sqrt_mul_norm_deriv_le hr hL hf (hF z (mem_closedBall_self hr.le)) heq
    (hderiv z (mem_closedBall_self hr.le))
  intro w hw
  have h := (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le hF hderiv
    (mem_closedBall_self hr.le) (sphere_subset_closedBall hw)
  simpa only [mem_sphere_iff_norm.mp hw] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/HalfPlaneSquareBounds.lean` -/

section
/-!
# Uniform square-root bounds along a vertical boundary
-/

open Set Metric Filter Topology

namespace Bernays

theorem halfPlane_differentiableOn {F : ℂ → ℂ} {c : ℝ}
    (hF : ∀ z : ℂ, c < z.re → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F {z : ℂ | c < z.re} :=
  fun z hz => (hF z hz).differentiableWithinAt

theorem halfPlane_deriv_continuousOn {F : ℂ → ℂ} {c : ℝ}
    (hF : ∀ z : ℂ, c < z.re → DifferentiableAt ℂ F z) :
    ContinuousOn (deriv F) {z : ℂ | c < z.re} :=
  ((halfPlane_differentiableOn hF).deriv (isOpen_lt continuous_const Complex.continuous_re)).continuousOn

theorem halfPlane_closedBall {δ t : ℝ} (hδ : 0 < δ) :
    closedBall ((1 + δ : ℝ) + t * Complex.I) (δ / 2) ⊆ {z : ℂ | 1 < z.re} := by
  intro z hz
  have hnorm := (mem_closedBall_iff_norm.mp hz)
  have h := (abs_le.mp ((Complex.abs_re_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)).1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  change 1 < z.re
  linarith

theorem halfPlane_closedBall_rectangle {δ t T : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ht : |t| ≤ T) :
    closedBall ((1 + δ : ℝ) + t * Complex.I) (δ / 2) ⊆
      (Icc (3 / 4 : ℝ) 3) ×ℂ (Icc (-T - 1) (T + 1)) := by
  intro z hz
  have hnorm := mem_closedBall_iff_norm.mp hz
  have hr := abs_le.mp ((Complex.abs_re_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)
  have hi := abs_le.mp ((Complex.abs_im_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at hr hi
  have ht' := abs_le.mp ht
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem halfPlane_square_uniform_bounds {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (T : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → |t| ≤ T →
      ‖f ((1 + δ : ℝ) + t * Complex.I)‖ ≤ K ∧
      Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖ ≤ K := by
  let S := (Icc (3 / 4 : ℝ) 3) ×ℂ (Icc (-T - 1) (T + 1))
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hSU : S ⊆ {z : ℂ | (1 / 2 : ℝ) < z.re} := fun z hz => by
    have hz' : 3 / 4 ≤ z.re := hz.1.1
    change 1 / 2 < z.re
    linarith
  obtain ⟨A, hA⟩ := hSc.exists_bound_of_continuousOn
    ((halfPlane_differentiableOn hF).continuousOn.mono hSU)
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn
    ((halfPlane_deriv_continuousOn hF).mono hSU)
  let L := max 1 B
  refine ⟨Real.sqrt (max 0 A) + 2 * (L + 1) + 1, by
    have := le_max_left (1 : ℝ) B
    have := Real.sqrt_nonneg (max 0 A)
    dsimp only [L]
    linarith, ?_⟩
  intro δ t hδ hδ₁ ht
  let z : ℂ := (1 + δ : ℝ) + t * Complex.I
  have hball := halfPlane_closedBall hδ (t := t)
  have hrect := halfPlane_closedBall_rectangle hδ hδ₁ ht
  have hz : z ∈ closedBall z (δ / 2) := mem_closedBall_self (by positivity)
  have hval : ‖f z‖ ≤ Real.sqrt (max 0 A) :=
    norm_le_sqrt_of_sq_eq (heq z (hball hz)).symm ((hA z (hrect hz)).trans (le_max_right _ _))
  have hdiff : DiffContOnCl ℂ f (ball z (δ / 2)) :=
    (halfPlane_differentiableOn hf).diffContOnCl_ball hball
  have hder := sqrt_mul_norm_deriv_le_of_deriv_bound (half_pos hδ) (le_max_left 1 B) hdiff
    (fun w hw => hF w (hSU (hrect hw))) (fun w hw => heq w (hball hw))
    (fun w hw => (hB w (hrect hw)).trans (le_max_right 1 B))
  have hsqrt : Real.sqrt δ ≤ 2 * Real.sqrt (δ / 2) := by
    have h₁ := Real.sq_sqrt hδ.le
    have h₂ := Real.sq_sqrt (show 0 ≤ δ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg δ, Real.sqrt_nonneg (δ / 2)]
  have hmul := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (deriv f z))
  have hL : 1 ≤ L := le_max_left 1 B
  have hnonneg := Real.sqrt_nonneg (max 0 A)
  constructor <;> change _ ≤ Real.sqrt (max 0 A) + 2 * (L + 1) + 1
  · linarith
  · change Real.sqrt (δ / 2) * ‖deriv f z‖ ≤ L + 1 at hder
    change Real.sqrt δ * ‖deriv f z‖ ≤ _
    nlinarith

end Bernays

end

/-! ### Upstream module `Util/Bernays/HalfPlaneSquarePointwise.lean` -/

section
/-!
# Almost-everywhere boundary decay for square-root derivatives
-/

open Set Filter Topology MeasureTheory

namespace Bernays

theorem norm_eq_sqrt_norm_of_square {u v : ℂ} (heq : v = u ^ 2) :
    ‖u‖ = Real.sqrt ‖v‖ := by
  rw [heq, norm_pow, Real.sqrt_sq (norm_nonneg u)]

theorem halfPlane_square_deriv_formula {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    {z : ℂ} (hz : 1 < z.re) (hne : F z ≠ 0) :
    ‖deriv f z‖ = ‖deriv F z‖ / (2 * Real.sqrt ‖F z‖) := by
  have hevent : F =ᶠ[𝓝 z] fun w => f w ^ 2 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz) heq
  have hd := deriv_square_norm (hf z hz) (hF z (by linarith)) hevent
  rw [norm_eq_sqrt_norm_of_square (heq z hz)] at hd
  have hp : 0 < Real.sqrt ‖F z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hne)
  apply (eq_div_iff (mul_pos (by norm_num : (0 : ℝ) < 2) hp).ne').mpr
  linarith

theorem halfPlane_square_scaled_deriv_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (t : ℝ) (hne : F (1 + t * Complex.I) ≠ 0) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  let z : ℝ → ℂ := fun δ => (1 + δ : ℝ) + t * Complex.I
  have hz : Tendsto z (𝓝[>] 0) (𝓝 (1 + t * Complex.I)) := by
    have hc : Continuous z := by dsimp only [z]; fun_prop
    simpa only [z, add_zero, Complex.ofReal_one] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have ht : (1 / 2 : ℝ) < (1 + t * Complex.I).re := by norm_num
  have hFcont := (hF _ ht).continuousAt.tendsto.comp hz
  have hF'cont := ((halfPlane_deriv_continuousOn hF).continuousAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ht)).tendsto.comp hz
  have hden : 2 * Real.sqrt ‖F (1 + t * Complex.I)‖ ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hne))).ne'
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hlim := hsqrt.mul (hF'cont.norm.div ((hFcont.norm.sqrt).const_mul 2) hden)
  rw [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hFcont.eventually_ne hne] with δ hδ hnonzero
  have hδ' : 1 < (z δ).re := by
    dsimp only [z]
    simpa using hδ
  rw [halfPlane_square_deriv_formula hf hF heq hδ' hnonzero]
  rfl

theorem halfPlane_boundary_zeros_countable {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) :
    {t : ℝ | F (1 + t * Complex.I) = 0}.Countable := by
  obtain ⟨w, hw, hFw⟩ := hne
  let U := {z : ℂ | (1 / 2 : ℝ) < z.re}
  have hA : AnalyticOnNhd ℂ F U :=
    (halfPlane_differentiableOn hF).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hU : IsConnected U := (convex_halfSpace_re_gt (1 / 2)).isConnected ⟨w, hw⟩
  have hdisc : IsDiscrete ((F ⁻¹' {0}) ∩ U) :=
    isDiscrete_of_codiscreteWithin (hA.preimage_zero_mem_codiscreteWithin hFw hw hU)
  have hc := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  have hinj : Function.Injective (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
    intro t s h
    simpa using congrArg Complex.im h
  apply (hc.preimage hinj).mono
  intro t ht
  exact ⟨ht, by norm_num [U]⟩

theorem halfPlane_square_scaled_deriv_ae_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) :
    ∀ᵐ t : ℝ, Tendsto (fun δ : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hnull := (halfPlane_boundary_zeros_countable hF hne).measure_zero (μ := volume)
  have hneae : ∀ᵐ t : ℝ, F (1 + t * Complex.I) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hneae] with t ht
  exact halfPlane_square_scaled_deriv_tendsto hf hF heq t ht

end Bernays

end

/-! ### Upstream module `Util/Bernays/HalfPlaneSquareIntegral.lean` -/

section
/-!
# Integral decay of a square root and its derivative on finite vertical segments
-/

open Set Filter Topology MeasureTheory

namespace Bernays

theorem halfPlane_vertical_continuous {f : ℂ → ℂ} {c σ : ℝ}
    (hf : ContinuousOn f {z : ℂ | c < z.re}) (hσ : c < σ) :
    Continuous (fun t : ℝ => f ((σ : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (hf.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simpa using hσ))).comp
  fun_prop

theorem halfPlane_square_scaled_norm_tendsto {f F : ℂ → ℂ}
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (t : ℝ) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hz : Tendsto (fun δ : ℝ => ((1 + δ : ℝ) : ℂ) + t * Complex.I)
      (𝓝[>] 0) (𝓝 (1 + t * Complex.I)) := by
    have hc : Continuous (fun δ : ℝ => ((1 + δ : ℝ) : ℂ) + t * Complex.I) := by fun_prop
    simpa only [add_zero, Complex.ofReal_one] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hcont := ((hF _ (by norm_num : (1 / 2 : ℝ) < (1 + t * Complex.I).re)).continuousAt.tendsto.comp hz).norm.sqrt
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hlim := hsqrt.mul hcont
  rw [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [norm_eq_sqrt_norm_of_square (heq _ (by simpa using hδ))]
  rfl

theorem halfPlane_square_scaled_deriv_integral_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0) (T : ℝ) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ in Icc (-T) T,
      Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := halfPlane_square_uniform_bounds hf hF heq T
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun t : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖)
      (volume.restrict (Icc (-T) T)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf)
      (by simpa using hδ : 1 < 1 + δ)).norm.const_mul _).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      ‖Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with δ hδ hδ₁
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact (hK δ t hδ hδ₁ (abs_le.mpr ht)).2
  have hlim := ae_restrict_of_ae (s := Icc (-T) T)
    (halfPlane_square_scaled_deriv_ae_tendsto hf hF heq hne)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K) hmeas hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hlim
  simpa only [integral_zero] using h

theorem halfPlane_square_scaled_norm_integral_tendsto {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (T : ℝ) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ in Icc (-T) T,
      Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hKpos, hK⟩ := halfPlane_square_uniform_bounds hf hF heq T
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun t : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
      (volume.restrict (Icc (-T) T)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn
      (by simpa using hδ : 1 < 1 + δ)).norm.const_mul _).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      ‖Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with δ hδ hδ₁
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    have hsqrt : Real.sqrt δ ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hδ₁
    calc
      _ ≤ Real.sqrt δ * K := mul_le_mul_of_nonneg_left (hK δ t hδ hδ₁ (abs_le.mpr ht)).1
        (Real.sqrt_nonneg _)
      _ ≤ K := by nlinarith
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Icc (-T) T),
      Tendsto (fun δ : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖)
        (𝓝[>] 0) (𝓝 0) := Eventually.of_forall (halfPlane_square_scaled_norm_tendsto hF heq)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K) hmeas hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hlim
  simpa only [integral_zero] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/VerticalFourierBounds.lean` -/

section
/-!
# Fourier estimates for compactly truncated vertical lines
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

noncomputable def verticalProduct (f : ℂ → ℂ) (ψ : ℝ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  f ((σ : ℂ) + t * Complex.I) * ψ t

theorem vertical_hasDerivAt {f : ℂ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) :
    HasDerivAt (fun t : ℝ => f ((σ : ℂ) + t * Complex.I))
      (deriv f ((σ : ℂ) + t * Complex.I) * Complex.I) t := by
  have hin : HasDerivAt (fun z : ℂ => (σ : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (σ : ℂ)
  exact (hf.hasDerivAt.comp (t : ℂ) hin).comp_ofReal

theorem verticalProduct_hasDerivAt {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) (hψ : DifferentiableAt ℝ ψ t) :
    HasDerivAt (verticalProduct f ψ σ)
      (deriv f ((σ : ℂ) + t * Complex.I) * Complex.I * ψ t +
        f ((σ : ℂ) + t * Complex.I) * deriv ψ t) t :=
  (vertical_hasDerivAt hf).mul hψ.hasDerivAt

theorem verticalProduct_deriv_norm_le {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ t C : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) (hψ : DifferentiableAt ℝ ψ t)
    (hψ₀ : ‖ψ t‖ ≤ C) (hψ₁ : ‖deriv ψ t‖ ≤ C) :
    ‖deriv (verticalProduct f ψ σ) t‖ ≤
      C * (‖deriv f ((σ : ℂ) + t * Complex.I)‖ + ‖f ((σ : ℂ) + t * Complex.I)‖) := by
  rw [(verticalProduct_hasDerivAt hf hψ).deriv]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_I, mul_one]
  have h₀ := mul_le_mul_of_nonneg_left hψ₀ (norm_nonneg (deriv f ((σ : ℂ) + t * Complex.I)))
  have h₁ := mul_le_mul_of_nonneg_left hψ₁ (norm_nonneg (f ((σ : ℂ) + t * Complex.I)))
  nlinarith

theorem verticalProduct_deriv_continuous {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hσ : 1 < σ) (hψ : ContDiff ℝ 1 ψ) : Continuous (deriv (verticalProduct f ψ σ)) := by
  have heq : deriv (verticalProduct f ψ σ) = fun t : ℝ =>
      deriv f ((σ : ℂ) + t * Complex.I) * Complex.I * ψ t +
        f ((σ : ℂ) + t * Complex.I) * deriv ψ t := by
    funext t
    exact (verticalProduct_hasDerivAt (hf _ (by simpa using hσ))
      ((hψ.differentiable (by norm_num)) t)).deriv
  rw [heq]
  exact (((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf) hσ).mul_const _).mul
    hψ.continuous).add (((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn
      hσ)).mul hψ.continuous_deriv_one)

theorem verticalProduct_integrable {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hσ : 1 < σ) (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Integrable (verticalProduct f ψ σ) ∧ Integrable (deriv (verticalProduct f ψ σ)) := by
  have hs : HasCompactSupport (verticalProduct f ψ σ) := hsupp.mul_left
  have hc : Continuous (verticalProduct f ψ σ) :=
    (halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn hσ).mul hψ.continuous
  exact ⟨hc.integrable_of_hasCompactSupport hs,
    (verticalProduct_deriv_continuous hf hσ hψ).integrable_of_hasCompactSupport hs.deriv⟩

theorem fourier_norm_le_integral_norm (g : ℝ → ℂ) (u : ℝ) :
    ‖𝓕 g u‖ ≤ ∫ t : ℝ, ‖g t‖ := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

theorem fourier_deriv_norm_bound {g : ℝ → ℂ} (hg : Integrable g)
    (hgd : Differentiable ℝ g) (hg' : Integrable (deriv g)) (u : ℝ) :
    (2 * Real.pi * |u|) * ‖𝓕 g u‖ ≤ ∫ t : ℝ, ‖deriv g t‖ := by
  have heq := congrArg (fun k : ℝ → ℂ => ‖k u‖) (Real.fourier_deriv hg hgd hg')
  simp only [Pi.smul_apply, norm_smul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at heq
  exact heq ▸ fourier_norm_le_integral_norm (deriv g) u

end Bernays

end

/-! ### Upstream module `Util/Bernays/VerticalProductDecay.lean` -/

section
/-!
# A quantitative Fourier decay estimate from holomorphy of the square
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

theorem verticalProduct_scaled_deriv_integral_le {f : ℂ → ℂ} {ψ : ℝ → ℂ} {δ T C : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hδ : 0 < δ) (hψ : ContDiff ℝ 1 ψ) (hsupp : tsupport ψ ⊆ Icc (-T) T)
    (hψ₀ : ∀ t : ℝ, ‖ψ t‖ ≤ C) (hψ₁ : ∀ t : ℝ, ‖deriv ψ t‖ ≤ C) :
    Real.sqrt δ * (∫ t : ℝ, ‖deriv (verticalProduct f ψ (1 + δ)) t‖) ≤
      C * ((∫ t : ℝ in Icc (-T) T, Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖) +
        ∫ t : ℝ in Icc (-T) T, Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖) := by
  let S := Icc (-T) T
  let g := verticalProduct f ψ (1 + δ)
  have hσ : 1 < 1 + δ := by linarith
  have hs : tsupport g ⊆ S := tsupport_mul_subset_right.trans hsupp
  have hzero : ∀ t : ℝ, t ∉ S → ‖deriv g t‖ = 0 := by
    intro t ht
    rw [deriv_of_notMem_tsupport (fun h => ht (hs h)), norm_zero]
  have hcut := setIntegral_eq_integral_of_forall_compl_eq_zero hzero (μ := volume)
  change Real.sqrt δ * (∫ t : ℝ, ‖deriv g t‖) ≤ _
  rw [← hcut, ← integral_const_mul]
  have hdint : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖deriv g t‖) S :=
    ((verticalProduct_deriv_continuous hf hσ hψ).norm.const_mul _).continuousOn.integrableOn_compact
      isCompact_Icc
  have h₀ : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖) S :=
    ((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf) hσ).norm.const_mul
      _).continuousOn.integrableOn_compact isCompact_Icc
  have h₁ : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖) S :=
    ((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn hσ).norm.const_mul
      _).continuousOn.integrableOn_compact isCompact_Icc
  rw [← integral_add h₀ h₁, ← integral_const_mul]
  apply integral_mono hdint ((h₀.add h₁).const_mul C)
  intro t
  have hbound := verticalProduct_deriv_norm_le (σ := 1 + δ) (hf _ (by simpa using hσ))
    ((hψ.differentiable (by norm_num)) t) (hψ₀ t) (hψ₁ t)
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg δ)
  change Real.sqrt δ * ‖deriv g t‖ ≤ _
  dsimp only [g] at *
  simp only [Pi.add_apply]
  nlinarith

theorem halfPlane_square_verticalProduct_integral_tendsto {f F : ℂ → ℂ} {ψ : ℝ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0)
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ∫ t : ℝ, ‖deriv (verticalProduct f ψ (1 + δ)) t‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨T, _, hT⟩ := hsupp.isBounded.exists_pos_norm_le
  have hTS : tsupport ψ ⊆ Icc (-T) T := fun t ht => abs_le.mp (by simpa using hT t ht)
  obtain ⟨C₀, h₀⟩ := hψ.continuous.bounded_above_of_compact_support hsupp
  obtain ⟨C₁, h₁⟩ := hψ.continuous_deriv_one.bounded_above_of_compact_support hsupp.deriv
  let C := max C₀ C₁
  have hlim := ((halfPlane_square_scaled_deriv_integral_tendsto hf hF heq hne T).add
    (halfPlane_square_scaled_norm_integral_tendsto hf hF heq T)).const_mul C
  simp only [add_zero, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun δ =>
    mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))) _ hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact verticalProduct_scaled_deriv_integral_le hf hδ hψ hTS
    (fun t => (h₀ t).trans (le_max_left _ _)) (fun t => (h₁ t).trans (le_max_right _ _))

theorem halfPlane_square_fourier_decay {f F : ℂ → ℂ} {ψ : ℝ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0)
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ => ‖𝓕 (verticalProduct f ψ (1 + δ)) (-1 / (2 * Real.pi * δ))‖ / Real.sqrt δ)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun δ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))) _
    (halfPlane_square_verticalProduct_integral_tendsto hf hF heq hne hψ hsupp)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  have hσ : 1 < 1 + δ := by linarith
  obtain ⟨hg, hg'⟩ := verticalProduct_integrable hf hσ hψ hsupp
  have hgd : Differentiable ℝ (verticalProduct f ψ (1 + δ)) := fun t =>
    (verticalProduct_hasDerivAt (hf _ (by simpa using hσ)) ((hψ.differentiable (by norm_num)) t)).differentiableAt
  have hbound := fourier_deriv_norm_bound hg hgd hg' (-1 / (2 * Real.pi * δ))
  have hfactor : 2 * Real.pi * |(-1 : ℝ) / (2 * Real.pi * δ)| = 1 / δ := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
    field_simp
  rw [hfactor] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg δ)
  have hid : Real.sqrt δ * (1 / δ) = 1 / Real.sqrt δ := by
    have hs := Real.sq_sqrt hδ.le
    have hsp := Real.sqrt_pos.mpr hδ
    field_simp [hδ.ne', hsp.ne']
    nlinarith
  rw [← mul_assoc, hid, one_div_mul_eq_div] at hmul
  exact hmul

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareSeriesSmoothing.lean` -/

section
/-!
# Smoothed coefficient cancellation from a continued convolution square
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

theorem fourier_eq_oscillatory (g : ℝ → ℂ) (y : ℝ) :
    𝓕 g (-y / (2 * Real.pi)) =
      ∫ t : ℝ, g t * Complex.exp ((y : ℂ) * t * Complex.I) := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Circle.smul_def, Real.fourierChar, AddChar.coe_mk,
    Circle.coe_exp, smul_eq_mul, RCLike.inner_apply', conj_trivial]
  rw [mul_comm (g t)]
  congr 1
  congr 1
  push_cast
  field_simp

theorem smoothed_LSeries_eq_fourier (a : ℕ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (ψ : ℝ → ℂ) (hψ : Integrable ψ) {δ : ℝ} (hδ : 0 < δ) :
    (∑' n : ℕ, LSeries.term a (1 + δ) n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))) =
      𝓕 (verticalProduct (LSeries a) ψ (1 + δ)) (-1 / (2 * Real.pi * δ)) := by
  have hs (σ : ℝ) (hσ : 1 < σ) : Summable (nterm a σ) := by
    have hsum := (ha σ (by simpa using hσ)).norm
    simpa only [norm_term_eq_nterm_re, Complex.ofReal_re] using hsum
  have hid : -1 / (2 * Real.pi * δ) = -(1 / δ) / (2 * Real.pi) := by ring
  rw [hid, fourier_eq_oscillatory]
  rw [show (1 : ℂ) + δ = ((1 + δ : ℝ) : ℂ) by push_cast; rfl]
  rw [first_fourier hs hψ (Real.exp_pos _) (by simpa using hδ)]
  apply integral_congr_ae
  filter_upwards [] with t
  change LSeries a ((1 + δ : ℝ) + t * Complex.I) * ψ t *
    (Real.exp (1 / δ) : ℂ) ^ ((t : ℂ) * Complex.I) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  dsimp only [verticalProduct]
  congr 1
  congr 1
  ring

theorem LSeries_square_smoothed_cancellation (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, LSeries.term a (1 + δ) n *
        𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))‖ / Real.sqrt δ)
      (𝓝[>] 0) (𝓝 0) := by
  apply (halfPlane_square_fourier_decay had hF heq hne hψ hsupp).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [smoothed_LSeries_eq_fourier a ha ψ (hψ.continuous.integrable_of_hasCompactSupport hsupp) hδ]

end Bernays

end

/-! ### Upstream module `Util/Bernays/SmoothedFunctional.lean` -/

section
/-!
# Uniform bounds for the smoothed Dirichlet functional
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

noncomputable def logarithmicKernel (x : ℝ) (n : ℕ) : ℝ :=
  (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)) ^ 2)⁻¹

noncomputable def logarithmicKernelMass (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ / n * logarithmicKernel x n

noncomputable def dirichletTwist (a : ℕ → ℂ) (δ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * LSeries.term a (1 + δ) n

noncomputable def smoothedSeries (a : ℕ → ℂ) (ψ : ℝ → ℂ) (δ : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term a (1 + δ) n *
    𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))

theorem dirichletTwist_div (a : ℕ → ℂ) (δ : ℝ) (n : ℕ) :
    dirichletTwist a δ n / (n : ℂ) = LSeries.term a (1 + δ) n := by
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  · exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

theorem dirichletTwist_norm_le (a : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ‖dirichletTwist a δ n‖ ≤ ‖a n‖ := by
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [dirichletTwist, norm_mul, Complex.norm_natCast, norm_term_eq_nterm_re]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, nterm, if_neg hn]
  rw [Real.rpow_add hnR, Real.rpow_one]
  have hcancel : (n : ℝ) * (‖a n‖ / ((n : ℝ) * (n : ℝ) ^ δ)) = ‖a n‖ / (n : ℝ) ^ δ := by
    field_simp
  rw [hcancel]
  exact div_le_self (norm_nonneg _) (Real.one_le_rpow hn₁ hδ)

theorem dirichletTwist_cheby {a : ℕ → ℂ} (ha : cheby a) {δ : ℝ} (hδ : 0 ≤ δ) :
    cheby (dirichletTwist a δ) := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, fun N => ?_⟩
  apply (Finset.sum_le_sum (fun n _ => dirichletTwist_norm_le a hδ n)).trans (hC N)

theorem logarithmicKernelMass_summable {a : ℕ → ℂ} (ha : cheby a) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖a n‖ / n * logarithmicKernel x n) := by
  simpa only [logarithmicKernel, Complex.ofReal_one, Complex.one_re, Real.rpow_one, one_div] using
    limiting_fourier_lim1_aux ha hx 1 (zero_le_one' ℝ)

theorem logarithmicKernelMass_mono {a b : ℕ → ℂ} (ha : cheby a) (hb : cheby b)
    (hab : ∀ n : ℕ, ‖a n‖ ≤ ‖b n‖) {x : ℝ} (hx : 0 < x) :
    logarithmicKernelMass a x ≤ logarithmicKernelMass b x := by
  apply Summable.tsum_mono (logarithmicKernelMass_summable ha hx)
    (logarithmicKernelMass_summable hb hx)
  intro n
  apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hab n) (Nat.cast_nonneg _))
  exact inv_nonneg.mpr (by positivity)

theorem smoothedSeries_eq_twist (a : ℕ → ℂ) (ψ : ℝ → ℂ) (δ : ℝ) :
    smoothedSeries a ψ δ = ∑' n : ℕ, dirichletTwist a δ n / n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ))) := by
  unfold smoothedSeries
  simp only [dirichletTwist_div]

theorem smoothedSeries_norm_le {a : ℕ → ℂ} (ha : cheby a) (ψ : W21) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖smoothedSeries a ψ δ‖ ≤ W21.norm ψ * logarithmicKernelMass a (Real.exp (1 / δ)) := by
  rw [smoothedSeries_eq_twist]
  have ht := dirichletTwist_cheby ha hδ
  have hbound := bound_I1 (Real.exp (1 / δ)) (Real.exp_pos _) ψ ht
  change _ ≤ W21.norm ψ * logarithmicKernelMass (dirichletTwist a δ) (Real.exp (1 / δ)) at hbound
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left (logarithmicKernelMass_mono ht ha
    (dirichletTwist_norm_le a hδ) (Real.exp_pos _)) W21.norm_nonneg

theorem smoothedSeries_sub {a : ℕ → ℂ} (ha : cheby a) (ψ φ : W21) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothedSeries a (ψ - φ) δ = smoothedSeries a ψ δ - smoothedSeries a φ δ := by
  rw [smoothedSeries_eq_twist, smoothedSeries_eq_twist, smoothedSeries_eq_twist]
  have ht := dirichletTwist_cheby ha hδ
  have hs₁ := (summable_fourier (Real.exp (1 / δ)) (Real.exp_pos _) ψ ht).of_norm
  have hs₂ := (summable_fourier (Real.exp (1 / δ)) (Real.exp_pos _) φ ht).of_norm
  rw [← hs₁.tsum_sub hs₂]
  apply tsum_congr
  intro n
  simp only [Pi.sub_def]
  rw [F_sub ψ.hf φ.hf, mul_sub]

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogKernelCutoffs.lean` -/

section
/-!
# Splitting the logarithmic kernel at the square root of the endpoint
-/

open Set Filter Topology MeasureTheory
open scoped Classical

namespace Bernays

noncomputable def normUpperPart (a : ℕ → ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  if u ≤ (n : ℝ) then a n else 0

noncomputable def normLowerPart (a : ℕ → ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) < u then a n else 0

theorem cheby_of_norm_le {a b : ℕ → ℂ} (hb : cheby b) (h : ∀ n : ℕ, ‖a n‖ ≤ ‖b n‖) :
    cheby a := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun N => (Finset.sum_le_sum (fun n _ => h n)).trans (hC N)⟩

theorem normUpperPart_norm_le (a : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    ‖normUpperPart a u n‖ ≤ ‖a n‖ := by
  unfold normUpperPart
  split_ifs <;> simp

theorem normLowerPart_norm_le (a : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    ‖normLowerPart a u n‖ ≤ ‖a n‖ := by
  unfold normLowerPart
  split_ifs <;> simp

theorem logarithmicKernelMass_split {a : ℕ → ℂ} (ha : cheby a) (u : ℝ) {x : ℝ} (hx : 0 < x) :
    logarithmicKernelMass a x = logarithmicKernelMass (normLowerPart a u) x +
      logarithmicKernelMass (normUpperPart a u) x := by
  have h₀ := cheby_of_norm_le ha (normLowerPart_norm_le a u)
  have h₁ := cheby_of_norm_le ha (normUpperPart_norm_le a u)
  rw [logarithmicKernelMass, logarithmicKernelMass, logarithmicKernelMass,
    ← (logarithmicKernelMass_summable h₀ hx).tsum_add (logarithmicKernelMass_summable h₁ hx)]
  apply tsum_congr
  intro n
  by_cases h : (n : ℝ) < u
  · simp only [normLowerPart, normUpperPart, h, not_le.mpr h, ↓reduceIte, norm_zero,
      zero_div, zero_mul, add_zero]
  · simp only [normLowerPart, normUpperPart, h, le_of_not_gt h, ↓reduceIte, norm_zero,
      zero_div, zero_mul, zero_add]

theorem sqrt_log_le_twice_sqrt_log {x y : ℝ} (hx : 1 ≤ x) (hy : Real.sqrt x ≤ y) :
    Real.sqrt (Real.log x) ≤ 2 * Real.sqrt (Real.log y) := by
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := (Real.sqrt_pos.mpr hx₀).trans_le hy
  have hl := Real.log_le_log (Real.sqrt_pos.mpr hx₀) hy
  rw [Real.log_sqrt hx₀.le] at hl
  have hxL := Real.log_nonneg hx
  have hyL : 0 ≤ Real.log y := by linarith
  have hsx := Real.sq_sqrt hxL
  have hsy := Real.sq_sqrt hyL
  nlinarith [Real.sqrt_nonneg (Real.log x), Real.sqrt_nonneg (Real.log y)]

theorem normUpperPart_cheby_logBound {a : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    chebyWith (2 * C / Real.sqrt (Real.log x)) (normUpperPart a (Real.sqrt x)) := by
  intro N
  by_cases hN : (N : ℝ) ≤ Real.sqrt x
  · have hzero : cumsum (fun n => ‖normUpperPart a (Real.sqrt x) n‖) N = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnR : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
      simp only [normUpperPart, if_neg (not_le.mpr (hnR.trans_le hN)), norm_zero]
    rw [hzero]
    positivity
  · have hsx := Real.sqrt_pos.mpr (Real.log_pos hx)
    have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
    have hlog := sqrt_log_le_twice_sqrt_log hx.le (le_of_not_ge hN)
    apply (Finset.sum_le_sum (fun n _ => normUpperPart_norm_le a (Real.sqrt x) n)).trans
    apply (hcount N).trans
    have hscalar : C / (1 + Real.sqrt (Real.log (N : ℝ))) ≤ 2 * C / Real.sqrt (Real.log x) := by
      apply (div_le_div_iff₀ hden hsx).mpr
      have hmul := mul_le_mul_of_nonneg_left hlog hC
      nlinarith
    calc
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))) =
          (C / (1 + Real.sqrt (Real.log (N : ℝ)))) * N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg N)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SpatialCountBounds.lean` -/

section
/-!
# Uniform counting bounds on fixed multiples of a moving endpoint
-/

namespace Bernays

theorem count_mul_sqrt_log_le {A : ℕ → ℝ} (hA : ∀ N : ℕ, A N ≤ N)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b x : ℝ} (hb : 0 ≤ b) (hx : 1 < x) {N : ℕ} (hN : (N : ℝ) ≤ b * x) :
    A N * Real.sqrt (Real.log x) ≤ (1 + 2 * C * b) * x := by
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hsx : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx)
  by_cases hsmall : (N : ℝ) ≤ Real.sqrt x
  · have hlog : Real.sqrt (Real.log x) ≤ Real.sqrt x := Real.sqrt_le_sqrt (Real.log_le_self hx₀.le)
    have h₁ := mul_le_mul_of_nonneg_right ((hA N).trans hsmall) hsx.le
    have h₂ := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    have hsquare := Real.sq_sqrt hx₀.le
    have hCb : 0 ≤ 2 * C * b * x := by positivity
    nlinarith
  · have hslog := sqrt_log_le_twice_sqrt_log hx.le (le_of_not_ge hsmall)
    have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
    have hscalar : C / (1 + Real.sqrt (Real.log (N : ℝ))) ≤ 2 * C / Real.sqrt (Real.log x) := by
      apply (div_le_div_iff₀ hden hsx).mpr
      have hmul := mul_le_mul_of_nonneg_left hslog hC
      nlinarith
    have hAN : A N ≤ (2 * C * N) / Real.sqrt (Real.log x) := by
      apply (hcount N).trans
      have hmul := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg N)
      convert hmul using 1 <;> ring
    have hAlog := (le_div_iff₀ hsx).mp hAN
    have hlarge := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * C by positivity)
    nlinarith

theorem count_scaled_exponential_le {A : ℕ → ℝ} (hA : ∀ N : ℕ, A N ≤ N)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) {N : ℕ}
    (hN : (N : ℝ) ≤ b * Real.exp (1 / δ)) :
    A N / (Real.exp (1 / δ) * Real.sqrt δ) ≤ 1 + 2 * C * b := by
  have hx : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (by positivity)
  have hbound := count_mul_sqrt_log_le hA hC hcount hb hx hN
  rw [Real.log_exp, one_div, Real.sqrt_inv, ← div_eq_mul_inv] at hbound
  have hsp : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hstep := (div_le_iff₀ (Real.exp_pos (δ⁻¹))).mpr hbound
  simpa only [one_div, div_div, mul_comm (Real.sqrt δ)] using hstep

theorem spatial_sum_eq_finset {a : ℕ → ℂ} {Ψ : ℝ → ℂ} {b x : ℝ}
    (hx : 0 < x) (hb : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b) :
    (∑' n : ℕ, a n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.range (⌈b * x⌉₊ + 1), a n * Ψ ((n : ℝ) / x) := by
  apply tsum_eq_sum
  intro n hn
  have hzero : Ψ ((n : ℝ) / x) = 0 := by
    by_contra hne
    have hnx : (n : ℝ) ≤ b * x := (div_le_iff₀ hx).mp (hb _ hne)
    have hceil : n ≤ ⌈b * x⌉₊ := by
      exact_mod_cast hnx.trans (Nat.le_ceil (b * x))
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hceil))
  rw [hzero, mul_zero]

theorem ceil_mul_add_one_le {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    ((⌈b * x⌉₊ + 1 : ℕ) : ℝ) ≤ (b + 2) * x := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hb (zero_le_one.trans hx))
  push_cast
  nlinarith

end Bernays

end

/-! ### Upstream module `Util/Bernays/DirichletUntwisting.lean` -/

section
/-!
# Uniform removal of a small real Dirichlet twist
-/

namespace Bernays

theorem abs_exp_sub_one_le {u r : ℝ} (hur : |u| ≤ r) :
    |Real.exp u - 1| ≤ Real.exp r - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hur
  have h₁ := Real.exp_le_exp.mpr hlo
  have h₂ := Real.exp_le_exp.mpr hhi
  have hsum : 2 ≤ Real.exp r + Real.exp (-r) := by
    linarith [Real.add_one_le_exp r, Real.add_one_le_exp (-r)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dirichletTwist_eq_exp (a : ℕ → ℂ) (δ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dirichletTwist a δ n = a n * (Real.exp (-δ * Real.log (n : ℝ)) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogC : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
  have hpow : (n : ℂ) ^ (δ : ℂ) = (Real.exp (δ * Real.log (n : ℝ)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hnC, hlogC,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 1
    ring
  rw [dirichletTwist, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC,
    Complex.cpow_one, hpow]
  rw [neg_mul, Real.exp_neg, Complex.ofReal_inv]
  field_simp

theorem dirichletTwist_eq_relative_exp (a : ℕ → ℂ) {δ : ℝ} (hδ : δ ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    dirichletTwist a δ n = a n * (Real.exp (-1) : ℂ) *
      (Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : -δ * Real.log (n : ℝ) =
      -1 + -δ * Real.log ((n : ℝ) / Real.exp (1 / δ)) := by
    rw [Real.log_div hnR.ne' (Real.exp_ne_zero _), Real.log_exp]
    field_simp
    ring
  rw [dirichletTwist_eq_exp a δ hn, hlog, Real.exp_add, Complex.ofReal_mul, mul_assoc]

theorem dirichletTwist_sub_bound (a : ℕ → ℂ) {δ L : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : n ≠ 0)
    (hlog : |Real.log ((n : ℝ) / Real.exp (1 / δ))| ≤ L) :
    ‖dirichletTwist a δ n - (Real.exp (-1) : ℂ) * a n‖ ≤
      ‖a n‖ * Real.exp (-1) * (Real.exp (δ * L) - 1) := by
  rw [dirichletTwist_eq_relative_exp a hδ.ne' hn]
  have hid : a n * (Real.exp (-1) : ℂ) *
      (Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) -
      (Real.exp (-1) : ℂ) * a n =
      a n * (Real.exp (-1) : ℂ) *
        ((Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) - 1) := by ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  apply abs_exp_sub_one_le
  rw [abs_mul, abs_neg, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left hlog hδ.le

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogarithmicTestFunctions.lean` -/

section
/-!
# Compactly supported spatial tests and their logarithmic Fourier preimages
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform ContDiff

namespace Bernays

theorem exists_logarithmic_fourier_test {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, 0 < y →
      𝓕 (g : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log y) = (y : ℂ) * Ψ y := by
  let h (t : ℝ) : ℂ := (Real.exp (2 * Real.pi * t) : ℂ) * Ψ (Real.exp (2 * Real.pi * t))
  have h₁ : ContDiff ℝ ∞ h := by
    have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (2 * Real.pi * t)) :=
      (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp he).mul (hΨ.comp he)
  have h₂ : HasCompactSupport h := by
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hbase : HasCompactSupport (Ψ ∘ Real.exp) := comp_exp_support hsupp hplus
    have hscaled := hbase.comp_smul (c := (2 * Real.pi : ℝ)) hπ
    have he : HasCompactSupport (fun t : ℝ => Ψ (Real.exp (2 * Real.pi * t))) := by
      simpa only [Function.comp_def, smul_eq_mul] using hscaled
    exact he.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h₁ h₂)
  refine ⟨g, fun y hy => ?_⟩
  rw [← SchwartzMap.fourier_coe, hg]
  change (Real.exp (2 * Real.pi * (1 / (2 * Real.pi) * Real.log y)) : ℂ) *
    Ψ (Real.exp (2 * Real.pi * (1 / (2 * Real.pi) * Real.log y))) = _
  have hid : 2 * Real.pi * (1 / (2 * Real.pi) * Real.log y) = Real.log y := by field_simp
  rw [hid, Real.exp_log hy]

theorem smoothedSeries_eq_spatial_twist {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (hplus : tsupport Ψ ⊆ Ioi 0) (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 0 < y → 𝓕 (g : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log y) = (y : ℂ) * Ψ y)
    (δ : ℝ) :
    smoothedSeries a g δ =
      (∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))) /
        (Real.exp (1 / δ) : ℂ) := by
  rw [smoothedSeries_eq_twist, ← tsum_div_const]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  · rw [hg _ (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (Real.exp_pos _))]
    push_cast
    field_simp

theorem spatial_twisted_cancellation_of_smoothed {a : ℕ → ℂ}
    (hsm : ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries a φ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0))
    {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_logarithmic_fourier_test hΨ hsupp hplus
  have h := hsm g
  apply h.congr'
  filter_upwards [] with δ
  change ‖smoothedSeries a g δ‖ / Real.sqrt δ = _
  rw [smoothedSeries_eq_spatial_twist hplus g hg, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, div_div]

end Bernays

end

/-! ### Upstream module `Util/Bernays/SpatialUntwisting.lean` -/

section
/-!
# Removing the real Dirichlet twist from compact spatial tests
-/

open Set Filter Topology
open scoped Classical ContDiff

namespace Bernays

theorem spatial_untwist_error_le {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b L Q : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hΨ₀ : Ψ 0 = 0) (hΨ : ∀ y : ℝ, ‖Ψ y‖ ≤ Q)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b ∧ |Real.log y| ≤ L)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖(∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))) -
      (Real.exp (-1) : ℂ) * (∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ)))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ) ≤
      (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2)) := by
  let x := Real.exp (1 / δ)
  let N := ⌈b * x⌉₊ + 1
  let R := Real.exp (-1) * (Real.exp (δ * L) - 1) * Q
  have hx : 0 < x := Real.exp_pos _
  have hx₁ : 1 ≤ x := (Real.one_lt_exp_iff.mpr (by positivity : 0 < 1 / δ)).le
  have hε : 0 ≤ Real.exp (δ * L) - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hδ.le hL))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hbΨ : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b := fun y hy => (hsupp y hy).1
  have hsum (c : ℕ → ℂ) : (∑' n : ℕ, c n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.range N, c n * Ψ ((n : ℝ) / x) := spatial_sum_eq_finset hx hbΨ
  have hbound : ‖(∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / x)) -
      (Real.exp (-1) : ℂ) * (∑' n : ℕ, a n * Ψ ((n : ℝ) / x))‖ ≤
      R * cumsum (fun n => ‖a n‖) N := by
    rw [hsum, hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    change _ ≤ R * ∑ n ∈ Finset.range N, ‖a n‖
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hterm : dirichletTwist a δ n * Ψ ((n : ℝ) / x) -
        (Real.exp (-1) : ℂ) * (a n * Ψ ((n : ℝ) / x)) =
        (dirichletTwist a δ n - (Real.exp (-1) : ℂ) * a n) * Ψ ((n : ℝ) / x) := by ring
    rw [hterm, norm_mul]
    by_cases hz : Ψ ((n : ℝ) / x) = 0
    · rw [hz, norm_zero, mul_zero]
      exact mul_nonneg hR (norm_nonneg _)
    · have hn : n ≠ 0 := by intro hn; subst n; simp [hΨ₀] at hz
      have htwist := dirichletTwist_sub_bound a hδ hn (hsupp _ hz).2
      have hmul := mul_le_mul htwist (hΨ ((n : ℝ) / x)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hε)
      dsimp only [R]
      convert hmul using 1 <;> ring
  have hAN (k : ℕ) : cumsum (fun n => ‖a n‖) k ≤ k := by
    have h := Finset.sum_le_sum (s := Finset.range k) (fun n _ => ha n)
    simpa only [cumsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using h
  have hN := ceil_mul_add_one_le hb hx₁
  have hc := count_scaled_exponential_le hAN hC hcount (show 0 ≤ b + 2 by linarith) hδ hN
  have hdiv := div_le_div_of_nonneg_right hbound (mul_nonneg hx.le (Real.sqrt_nonneg δ))
  rw [mul_div_assoc] at hdiv
  exact hdiv.trans (mul_le_mul_of_nonneg_left hc hR)

theorem compact_positive_test_bounds {Ψ : ℝ → ℂ} (hΨ : Continuous Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    ∃ b L Q : ℝ, 0 ≤ b ∧ 0 ≤ L ∧ 0 ≤ Q ∧ Ψ 0 = 0 ∧ (∀ y : ℝ, ‖Ψ y‖ ≤ Q) ∧
      ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b ∧ |Real.log y| ≤ L := by
  obtain ⟨b, hb⟩ := hsupp.isBounded.exists_norm_le
  obtain ⟨Q, hQ⟩ := hΨ.bounded_above_of_compact_support hsupp
  have hlog : ContinuousOn Real.log (tsupport Ψ) := fun y hy =>
    (Real.continuousAt_log (ne_of_gt (hplus hy))).continuousWithinAt
  obtain ⟨L, hL⟩ := hsupp.exists_bound_of_continuousOn hlog
  refine ⟨max 0 b, max 0 L, max 0 Q, le_max_left _ _, le_max_left _ _, le_max_left _ _, ?_,
    fun y => (hQ y).trans (le_max_right _ _), ?_⟩
  · by_contra hzero
    exact (lt_irrefl (0 : ℝ)) (hplus (subset_closure hzero))
  · intro y hy
    have hys : y ∈ tsupport Ψ := subset_closure hy
    exact ⟨(le_abs_self y).trans ((hb y hys).trans (le_max_right _ _)),
      (hL y hys).trans (le_max_right _ _)⟩

end Bernays

end

/-! ### Upstream module `ErdosProblems/Erdos1081/Erdos1081Order.lean` -/

section
open scoped nonZeroDivisors

namespace Erdos1081

noncomputable def zsqrtdLinearEquiv (d : ℤ) :
    Zsqrtd d ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re, z.im]
  invFun x := ⟨x 0, x 1⟩
  left_inv z := by ext <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' n x := by funext i; fin_cases i <;> simp

noncomputable def zsqrtdBasis (d : ℤ) : Module.Basis (Fin 2) ℤ (Zsqrtd d) :=
  Module.Basis.ofEquivFun (zsqrtdLinearEquiv d)

noncomputable local instance (d : ℤ) : Module.Free ℤ (Zsqrtd d) :=
  Module.Free.of_basis (zsqrtdBasis d)

noncomputable local instance (d : ℤ) : Module.Finite ℤ (Zsqrtd d) :=
  Module.Finite.of_basis (zsqrtdBasis d)

def zsqrtdNoZeroDivisors (d : ℤ) (hd : d < 0) :
    NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul]
      simp [hab]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff hd a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff hd b).mp hb)

def zsqrtdIsDomain (d : ℤ) (hd : d < 0) : IsDomain (Zsqrtd d) := by
  letI : NoZeroDivisors (Zsqrtd d) := zsqrtdNoZeroDivisors d hd
  exact NoZeroDivisors.to_isDomain _

example (d : ℤ) (hd : d < 0) : Ring.HasFiniteQuotients (Zsqrtd d) := by
  letI : NoZeroDivisors (Zsqrtd d) := zsqrtdNoZeroDivisors d hd
  letI : IsDomain (Zsqrtd d) := zsqrtdIsDomain d hd
  infer_instance

section General

variable {S : Type*} [CommRing S] [IsDomain S]

/-- The index of a principal ideal in a finite free order is the absolute
value of the determinant norm.  Mathlib's corresponding `Ideal.absNorm`
lemma is stated under a Dedekind hypothesis because that bundled norm is
multiplicative on every ideal; the principal-ideal calculation itself needs
only freeness and finiteness. -/
theorem cardQuot_span_singleton_eq_norm_natAbs
    [Module.Free ℤ S] [Module.Finite ℤ S] (r : S) :
    (Ideal.span ({r} : Set S)).cardQuot =
      (Algebra.norm ℤ r).natAbs := by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · subst r
    simp only [Set.singleton_zero, Ideal.span_zero]
    have hInfinite : Infinite S := Module.Free.infinite ℤ S
    rw [Submodule.cardQuot_bot]
    simp
  let b := Module.Free.chooseBasis ℤ S
  rw [Submodule.cardQuot_apply,
    ← Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv ℤ
        (Ideal.span ({r} : Set S))).toEquiv,
    ← Submodule.natAbs_det_equiv
      ((Ideal.span ({r} : Set S)).restrictScalars ℤ)
      (b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _))]
  congr
  refine b.ext fun i => ?_
  change
    ((b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _)) (b i) : S) =
      r * b i
  rw [Module.Basis.equiv_apply]
  exact Ideal.basisSpanSingleton_apply b hr i

/-- Multiplication by a nonzero element identifies an ideal with its
principal multiple. -/
noncomputable def idealSpanMulLinearEquiv
    (I : Ideal S) {a : S} (ha : a ≠ 0) :
    I ≃ₗ[ℤ] Ideal.span ({a} : Set S) * I := by
  let f : I →ₗ[ℤ] Ideal.span ({a} : Set S) * I :=
    { toFun := fun x =>
        ⟨a * (x : S), Ideal.mem_span_singleton_mul.mpr
          ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [mul_add]
      map_smul' := by
        intro n x
        apply Subtype.ext
        simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀ ha
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hxI, hxy⟩ :=
      Ideal.mem_span_singleton_mul.mp y.property
    refine ⟨⟨x, hxI⟩, ?_⟩
    apply Subtype.ext
    exact hxy

@[simp] theorem idealSpanMulLinearEquiv_apply
    (I : Ideal S) {a : S} (ha : a ≠ 0) (x : I) :
    ((idealSpanMulLinearEquiv I ha x :
      Ideal.span ({a} : Set S) * I) : S) = a * (x : S) := rfl

/-- Quotient cardinality is the absolute determinant of any full-rank
integral basis of the ideal. -/
theorem cardQuot_eq_natAbs_det_basis_change
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S)
    (bI : Module.Basis ι ℤ I) :
    I.cardQuot = (b.det ((↑) ∘ bI)).natAbs := by
  rw [Submodule.cardQuot_apply,
    ← Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv ℤ I).toEquiv]
  exact (Submodule.natAbs_det_basis_change
    b (I.restrictScalars ℤ) bI).symm

/-- Scaling a full-rank ideal by a principal ideal multiplies its index by
the absolute algebra norm of the generator. -/
theorem cardQuot_span_singleton_mul
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S)
    (bI : Module.Basis ι ℤ I) {a : S} (ha : a ≠ 0) :
    (Ideal.span ({a} : Set S) * I).cardQuot =
      (Algebra.norm ℤ a).natAbs * I.cardQuot := by
  let bMul : Module.Basis ι ℤ (Ideal.span ({a} : Set S) * I) :=
    bI.map (idealSpanMulLinearEquiv I ha)
  rw [cardQuot_eq_natAbs_det_basis_change b _ bMul,
    cardQuot_eq_natAbs_det_basis_change b I bI]
  have hvec : ((↑) ∘ bMul : ι → S) =
      (Algebra.lmul ℤ S a) ∘ ((↑) ∘ bI) := by
    funext i
    simp [bMul, Function.comp_apply]
  rw [hvec, Module.Basis.det_comp, ← Algebra.norm_apply, Int.natAbs_mul]

/-- A nonzero ideal in a finite free order has a full-rank basis indexed by
the same finite type as a chosen basis of the order. -/
noncomputable def idealFullBasis
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S) (hI : I ≠ ⊥) :
    Module.Basis ι ℤ I :=
  Submodule.smithNormalFormBotBasis b
    (Ideal.finrank_eq_finrank b I hI)

/-- The principal-scaling index formula with the basis of the ideal chosen
canonically by Smith normal form. -/
theorem cardQuot_span_singleton_mul_of_ne_bot
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S) (hI : I ≠ ⊥)
    {a : S} (ha : a ≠ 0) :
    (Ideal.span ({a} : Set S) * I).cardQuot =
      (Algebra.norm ℤ a).natAbs * I.cardQuot :=
  cardQuot_span_singleton_mul b I (idealFullBasis b I hI) ha

/-- Clearing denominators in an equality of nonzero ideals preserves the
expected quotient-cardinality ratio.  This is the non-Dedekind replacement
for the corresponding `Ideal.absNorm` calculation. -/
theorem cardQuot_ratio_of_principal_mul_eq
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) {I J : Ideal S}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) {a c : S}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : Ideal.span ({a} : Set S) * I =
      Ideal.span ({c} : Set S) * J) :
    (Algebra.norm ℤ a).natAbs * I.cardQuot =
      (Algebra.norm ℤ c).natAbs * J.cardQuot := by
  rw [← cardQuot_span_singleton_mul_of_ne_bot b I hI ha,
    h, cardQuot_span_singleton_mul_of_ne_bot b J hJ hc]

open TensorProduct

/-- The subtype of an integral ideal is linearly equivalent to the subtype
of its image in the fraction field. -/
noncomputable def idealSubtypeEquivCoeFractionalIdeal (J : Ideal S) :
    J ≃ₗ[S] ((J : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) := by
  let f : J →ₗ[S] ((J : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) :=
    { toFun := fun x ↦
        ⟨algebraMap S (FractionRing S) x.1,
          FractionalIdeal.mem_coeIdeal_of_mem S⁰ x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (algebraMap S (FractionRing S)) x.1 y.1
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact (Algebra.linearMap S (FractionRing S)).map_smul r x.1 }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact (IsFractionRing.injective S (FractionRing S))
      (congr_arg Subtype.val hxy)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal S⁰).mp hy
    exact ⟨⟨x, hx⟩, rfl⟩

/-- An integral ideal which is a unit in the fractional-ideal monoid is an
invertible module. -/
noncomputable def moduleInvertibleIdealOfIsUnit (J : Ideal S)
    (hJ : IsUnit (J : FractionalIdeal S⁰ (FractionRing S))) :
    Module.Invertible S J := by
  let uF : (FractionalIdeal S⁰ (FractionRing S))ˣ := hJ.unit
  let uS : (Submodule S (FractionRing S))ˣ :=
    FractionalIdeal.unitsMulEquivSubmodule uF
  letI : Module.Invertible S uS := inferInstance
  have hsub : (uS : Submodule S (FractionRing S)) =
      ((J : FractionalIdeal S⁰ (FractionRing S)) :
        Submodule S (FractionRing S)) := by
    change ((uF : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) = _
    rw [hJ.unit_spec]
  let e : uS ≃ₗ[S] J :=
    LinearEquiv.ofEq _ _ hsub ≪≫ₗ (idealSubtypeEquivCoeFractionalIdeal J).symm
  exact Module.Invertible.congr e

/-- The numerator of an invertible fractional ideal is an invertible integral
ideal in the same class; unlike `ClassGroup.mk0_integralRep`, this formulation
does not assume that every integral ideal is invertible. -/
theorem exists_integralUnitRep
    (I : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
    ∃ J : (FractionalIdeal S⁰ (FractionRing S))ˣ,
      (J : FractionalIdeal S⁰ (FractionRing S)) = I.1.num ∧
      ClassGroup.mk (FractionRing S) J = ClassGroup.mk (FractionRing S) I := by
  obtain ⟨J, hJ⟩ := (FractionalIdeal.isUnit_num (I := I.1)).mpr I.isUnit
  refine ⟨J, hJ, ?_⟩
  rw [eq_comm, ClassGroup.mk_eq_mk]
  have hden0 : algebraMap S (FractionRing S) I.1.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.1.den.prop
  refine ⟨Units.mk0 (algebraMap S _ I.1.den) hden0, ?_⟩
  apply Units.ext
  rw [mul_comm, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hJ]
  exact FractionalIdeal.den_mul_self_eq_num' S⁰ (FractionRing S) I

section Approximation

open Module Ring

variable {R S K L : Type*} [EuclideanDomain R] [CommRing S] [IsDomain S]
variable [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]
variable [Algebra R S] [Algebra S L] [IsScalarTower R S L]
variable (abv : AbsoluteValue R ℤ)
variable {iota : Type*} [DecidableEq iota] [Fintype iota]
variable (bS : Module.Basis iota R S)
variable {abv}
variable (adm : abv.IsAdmissible)
variable [Infinite R] [DecidableEq R]

/-- A nonzero ideal contains an element of minimal norm.  This is the
non-Dedekind version of `ClassGroup.exists_min`; its proof only needs the
ideal to be nonzero. -/
theorem exists_min_nonzero (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ b ∈ I, b ≠ 0 ∧
      ∀ c ∈ I, abv (Algebra.norm R c) < abv (Algebra.norm R b) → c = 0 := by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => ∃ b ∈ I, b ≠ (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := I.ne_bot_iff.mp hI
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

/-- Minkowski's approximation argument for an invertible integral ideal.  The
Dedekind hypothesis in Mathlib's class-number theorem is needed only to know
that *all* integral ideals are invertible.  Retaining invertibility as data
gives the form required for nonmaximal quadratic orders. -/
theorem exists_integralUnitRep_mem_fixed
    [Algebra.IsAlgebraic R S]
    (I : (FractionalIdeal S⁰ (FractionRing S))ˣ) (I' : Ideal S)
    (hI : (I : FractionalIdeal S⁰ (FractionRing S)) = I') :
    ∃ J : (FractionalIdeal S⁰ (FractionRing S))ˣ, ∃ J' : Ideal S,
      (J : FractionalIdeal S⁰ (FractionRing S)) = J' ∧
      ClassGroup.mk (FractionRing S) J = ClassGroup.mk (FractionRing S) I ∧
      algebraMap R S (∏ m ∈ ClassGroup.finsetApprox bS adm, m) ∈ J' := by
  set M := ∏ m ∈ ClassGroup.finsetApprox bS adm, m
  have hM : algebraMap R S M ≠ 0 := ClassGroup.prod_finsetApprox_ne_zero bS adm
  have hI' : I' ≠ ⊥ := by
    intro hzero
    have : (I : FractionalIdeal S⁰ (FractionRing S)) = 0 := by simpa [hI, hzero]
    exact I.ne_zero this
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ :=
    exists_min_nonzero (abv := abv) I' hI'
  have hleIdeal : Ideal.span {algebraMap R S M} * I' ≤ Ideal.span {b} := by
    rw [Ideal.mul_le]
    intro r' hr' a ha
    rw [Ideal.mem_span_singleton] at hr' ⊢
    obtain ⟨q, r, r_mem, lt⟩ :=
      ClassGroup.exists_mem_finset_approx' bS adm a b_ne_zero
    apply @dvd_of_mul_left_dvd _ _ q
    simp only [Algebra.smul_def] at lt
    rw [← sub_eq_zero.mp
      (b_min _ (I'.sub_mem (I'.mul_mem_left _ ha) (I'.mul_mem_left _ b_mem)) lt)]
    refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
    exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)
  let P : FractionalIdeal S⁰ (FractionRing S) :=
    ((Ideal.span {b} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
  let Q : FractionalIdeal S⁰ (FractionRing S) :=
    ((Ideal.span {algebraMap R S M} : Ideal S) :
      FractionalIdeal S⁰ (FractionRing S))
  let A : FractionalIdeal S⁰ (FractionRing S) :=
    (I' : FractionalIdeal S⁰ (FractionRing S))
  let JF : FractionalIdeal S⁰ (FractionRing S) := Q * A * P⁻¹
  have hleFrac : Q * A ≤ P := by
    change
      ((Ideal.span {algebraMap R S M} : Ideal S) :
          FractionalIdeal S⁰ (FractionRing S)) *
          (I' : FractionalIdeal S⁰ (FractionRing S)) ≤
        ((Ideal.span {b} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
    rw [← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)]
    exact hleIdeal
  have hbUnit : IsUnit
      P := by
    refine IsUnit.of_mul_eq_one
      P⁻¹ ?_
    dsimp only [P]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) b_ne_zero
  have hMUnit : IsUnit
      Q := by
    refine IsUnit.of_mul_eq_one
      Q⁻¹ ?_
    dsimp only [Q]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) hM
  have hIUnit : IsUnit A := ⟨I, hI⟩
  have hPmul : P * P⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing S)).mpr hbUnit
  have hPinvUnit : IsUnit P⁻¹ := by
    refine IsUnit.of_mul_eq_one P ?_
    rw [mul_comm, hPmul]
  have hJFUnit : IsUnit JF := by
    exact (hMUnit.mul hIUnit).mul hPinvUnit
  have hJFle : JF ≤ 1 := by
    dsimp only [JF]
    have hmul : Q * A * P⁻¹ ≤ P * P⁻¹ := by gcongr
    calc
      Q * A * P⁻¹ ≤ P * P⁻¹ := hmul
      _ = 1 := hPmul
  obtain ⟨J', hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJFle
  obtain ⟨J, hJ⟩ := hJFUnit
  have hcoeJ : (J : FractionalIdeal S⁰ (FractionRing S)) = J' := hJ.trans hJ'.symm
  have hclassFrac : P * (J' : FractionalIdeal S⁰ (FractionRing S)) = Q * A := by
    rw [hJ']
    change P * (Q * A * P⁻¹) = Q * A
    calc
      P * (Q * A * P⁻¹) = (Q * A) * (P * P⁻¹) := by ac_rfl
      _ = Q * A := by rw [hPmul, mul_one]
  have hclassIdeal :
      Ideal.span {b} * J' = Ideal.span {algebraMap R S M} * I' := by
    apply FractionalIdeal.coeIdeal_injective (R := S) (K := FractionRing S)
    simpa only [P, Q, A, FractionalIdeal.coeIdeal_mul] using hclassFrac
  refine ⟨J, J', hcoeJ, ?_, ?_⟩
  · apply (ClassGroup.mk_eq_mk_of_coe_ideal hcoeJ hI).mpr
    exact ⟨b, algebraMap R S M, b_ne_zero, hM, hclassIdeal⟩
  · have hbFrac : P ≤ A := by
      simpa only [P, A, FractionalIdeal.coeIdeal_le_coeIdeal] using
        (Ideal.span_singleton_le_iff_mem I').mpr b_mem
    have hQleJF : Q ≤ JF := by
      have hQP : Q * P ≤ Q * A := by gcongr
      have hmul : (Q * P) * P⁻¹ ≤ (Q * A) * P⁻¹ := by gcongr
      calc
        Q = Q * 1 := (mul_one Q).symm
        _ = Q * (P * P⁻¹) := congrArg (Q * ·) hPmul.symm
        _ = (Q * P) * P⁻¹ := by ac_rfl
        _ ≤ (Q * A) * P⁻¹ := hmul
        _ = JF := rfl
    have hspan : Ideal.span {algebraMap R S M} ≤ J' := by
      apply (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)).mp
      rw [hJ']
      exact hQleJF
    exact (Ideal.span_singleton_le_iff_mem J').mp hspan

/-- The Picard/class group of a finite order is finite.  This version replaces
the Dedekind assumption in Mathlib's class-number theorem by the exact two
properties used here: finite quotients and invertibility of the ideals that
represent class-group elements. -/
noncomputable def fintypeClassGroupOfFiniteQuotients
    [Ring.HasFiniteQuotients S] [Algebra.IsAlgebraic R S] :
    Fintype (ClassGroup S) := by
  classical
  let m : S := algebraMap R S (∏ r ∈ ClassGroup.finsetApprox bS adm, r)
  have hm : m ≠ 0 := by
    simpa only [m] using ClassGroup.prod_finsetApprox_ne_zero bS adm
  let T := {J : Ideal S // m ∈ J ∧
    IsUnit (J : FractionalIdeal S⁰ (FractionRing S))}
  have hfinite :
      {J : Ideal S | m ∈ J ∧
        IsUnit (J : FractionalIdeal S⁰ (FractionRing S))}.Finite :=
    (Ring.HasFiniteQuotients.finite_setOfPred_mem m hm).subset fun _ hJ => hJ.1
  letI : Fintype T := hfinite.fintype
  let f : T → ClassGroup S := fun J =>
    ClassGroup.mk (FractionRing S) J.2.2.unit
  apply Fintype.ofSurjective f
  intro C
  refine ClassGroup.induction (FractionRing S) ?_ C
  intro I
  obtain ⟨Iu, hIu, hclassIu⟩ := exists_integralUnitRep I
  obtain ⟨J, J', hJ, hclassJ, hmemJ⟩ :=
    exists_integralUnitRep_mem_fixed bS adm Iu I.1.num hIu
  have hmemJ' : m ∈ J' := by simpa only [m] using hmemJ
  let t : T := ⟨J', hmemJ', ⟨J, hJ⟩⟩
  refine ⟨t, ?_⟩
  change ClassGroup.mk (FractionRing S) t.2.2.unit =
    ClassGroup.mk (FractionRing S) I
  calc
    ClassGroup.mk (FractionRing S) t.2.2.unit =
        ClassGroup.mk (FractionRing S) J := by
      congr 1
      apply Units.ext
      exact t.2.2.unit_spec.trans hJ.symm
    _ = ClassGroup.mk (FractionRing S) Iu := hclassJ
    _ = ClassGroup.mk (FractionRing S) I := hclassIu

end Approximation

end General

end Erdos1081

end

/-! ### Upstream module `Util/Bernays/QuadraticOrder.lean` -/

section
/-!
# Negative-discriminant quadratic orders

The order `ℤ[ω]`, with `ω² = d + bω`, includes odd as well as even
discriminants. No maximality assumption is imposed.
-/

open scoped nonZeroDivisors

namespace Bernays

theorem four_mul_quadraticNorm (d b : ℤ) (z : QuadraticAlgebra ℤ d b) :
    4 * z.norm = (2 * z.re + b * z.im) ^ 2 - (b ^ 2 + 4 * d) * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem quadraticNorm_nonneg {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : 0 ≤ z.norm := by
  have hn := mul_nonpos_of_nonpos_of_nonneg hD.le (sq_nonneg z.im)
  have hi := four_mul_quadraticNorm d b z
  nlinarith [sq_nonneg (2 * z.re + b * z.im)]

theorem quadraticNorm_eq_zero_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    have hi := four_mul_quadraticNorm d b z
    have him : z.im = 0 := by
      by_contra hz
      have hp : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
      have hn := mul_neg_of_neg_of_pos hD hp
      nlinarith [sq_nonneg (2 * z.re + b * z.im)]
    have hre : z.re = 0 := by
      rw [QuadraticAlgebra.norm_def, him] at hzero
      nlinarith [sq_nonneg z.re]
    exact QuadraticAlgebra.ext hre him
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

def quadraticOrderNoZeroDivisors {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    NoZeroDivisors (QuadraticAlgebra ℤ d b) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    have h : x.norm * y.norm = 0 := by
      rw [← map_mul, hxy, QuadraticAlgebra.norm_zero]
    exact (mul_eq_zero.mp h).imp (quadraticNorm_eq_zero_iff hD x).mp
      (quadraticNorm_eq_zero_iff hD y).mp

def quadraticOrderIsDomain {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    IsDomain (QuadraticAlgebra ℤ d b) := by
  letI := quadraticOrderNoZeroDivisors hD
  exact NoZeroDivisors.to_isDomain _

theorem algebraNorm_quadraticOrder (d b : ℤ) (z : QuadraticAlgebra ℤ d b) :
    Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

noncomputable def quadraticOrderClassGroupFintype {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Fintype (ClassGroup (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  exact Erdos1081.fintypeClassGroupOfFiniteQuotients
    (bS := QuadraticAlgebra.basis d b) AbsoluteValue.absIsAdmissible

/-- Changing the generator by an integer preserves the order. -/
def quadraticOrderShift (d b k : ℤ) :
    QuadraticAlgebra ℤ (d - b * k - k ^ 2) (b + 2 * k) ≃+* QuadraticAlgebra ℤ d b where
  toFun z := ⟨z.re + k * z.im, z.im⟩
  invFun z := ⟨z.re - k * z.im, z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/Coordinates.lean` -/

section
/-!
# Integral coordinate changes for binary quadratic forms

All statements preserve represented integers, rather than the number of their
representations. Determinant one coordinate changes preserve the discriminant,
primitivity, positive definiteness, and the exact counting function.
-/

namespace BinQuadForm

@[ext]
theorem ext {f g : BinQuadForm} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) :
    f = g := by
  cases f
  cases g
  simp_all

/-- Pullback by the integral matrix with rows `(p,q)` and `(r,s)`. -/
def changeVariables (f : BinQuadForm) (p q r s : ℤ) : BinQuadForm where
  a := f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2
  b := 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s
  c := f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2

theorem discr_changeVariables (f : BinQuadForm) (p q r s : ℤ) :
    (f.changeVariables p q r s).discr = (p * s - q * r) ^ 2 * f.discr := by
  simp only [changeVariables, discr]
  ring

theorem changeVariables_one (f : BinQuadForm) : f.changeVariables 1 0 0 1 = f := by
  ext <;> simp [changeVariables]

theorem changeVariables_comp (f : BinQuadForm) (p q r s t u v w : ℤ) :
    (f.changeVariables p q r s).changeVariables t u v w =
      f.changeVariables (p * t + q * v) (p * u + q * w)
        (r * t + s * v) (r * u + s * w) := by
  ext <;> simp only [changeVariables] <;> ring

theorem changeVariables_inv (f : BinQuadForm) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) :
    (f.changeVariables p q r s).changeVariables s (-q) (-r) p = f := by
  rw [changeVariables_comp]
  have h₁ : p * s + q * -r = 1 := by linarith
  have h₂ : p * -q + q * p = 0 := by ring
  have h₃ : r * s + s * -r = 0 := by ring
  have h₄ : r * -q + s * p = 1 := by nlinarith [hdet]
  rw [h₁, h₂, h₃, h₄, changeVariables_one]

theorem PosDef.changeVariables {f : BinQuadForm} (hf : f.PosDef) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : (f.changeVariables p q r s).PosDef := by
  constructor
  · change 0 < f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2
    have hne : f.eval p r ≠ 0 := by
      intro hzero
      obtain ⟨hp, hr⟩ := (hf.eval_eq_zero_iff p r).mp hzero
      simp [hp, hr] at hdet
    have hpos := lt_of_le_of_ne (hf.eval_nonneg p r) (Ne.symm hne)
    simpa only [eval, pow_two, mul_assoc] using hpos
  · rw [discr_changeVariables, hdet, one_pow, one_mul]
    exact hf.2

/-- Proper integral equivalence of forms. -/
def ProperEquiv (f g : BinQuadForm) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ g = f.changeVariables p q r s

theorem ProperEquiv.refl (f : BinQuadForm) : ProperEquiv f f :=
  ⟨1, 0, 0, 1, by norm_num, f.changeVariables_one.symm⟩

theorem ProperEquiv.symm {f g : BinQuadForm} (h : ProperEquiv f g) : ProperEquiv g f := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact ⟨s, -q, -r, p, by nlinarith [hdet], (f.changeVariables_inv hdet).symm⟩

theorem ProperEquiv.trans {f g h : BinQuadForm} (hfg : ProperEquiv f g)
    (hgh : ProperEquiv g h) : ProperEquiv f h := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := hfg
  obtain ⟨t, u, v, w, hdet', rfl⟩ := hgh
  refine ⟨p * t + q * v, p * u + q * w, r * t + s * v, r * u + s * w, ?_,
    f.changeVariables_comp p q r s t u v w⟩
  calc
    _ = (p * s - q * r) * (t * w - u * v) := by ring
    _ = 1 := by rw [hdet, hdet', one_mul]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/FormIdeal.lean` -/

section
/-!
# The invertible ideal attached to a primitive form

For `[a,b,c]` use the order with `ω² = bω-ac` and the ideal `(a,ω)`.
Its norm form is exactly `a` times the original quadratic form.
-/

open scoped nonZeroDivisors

namespace BinQuadForm

abbrev Order (f : BinQuadForm) := QuadraticAlgebra ℤ (-f.a * f.c) f.b

theorem order_discr (f : BinQuadForm) : f.b ^ 2 + 4 * (-f.a * f.c) = f.discr := by
  simp only [discr]
  ring

theorem PosDef.orderIsDomain {f : BinQuadForm} (hf : f.PosDef) : IsDomain f.Order :=
  Bernays.quadraticOrderIsDomain (f.order_discr ▸ hf.2)

def formIdeal (f : BinQuadForm) : Ideal f.Order where
  carrier := {z | f.a ∣ z.re}
  zero_mem' := dvd_zero _
  add_mem' := by intro x y hx hy; exact dvd_add hx hy
  smul_mem' := by
    intro r x hx
    change f.a ∣ r.re * x.re + (-f.a * f.c) * r.im * x.im
    exact dvd_add (hx.mul_left _) (by use -f.c * r.im * x.im; ring)

def conjugateFormIdeal (f : BinQuadForm) : Ideal f.Order where
  carrier := {z | f.a ∣ z.re + f.b * z.im}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change f.a ∣ (x.re + y.re) + f.b * (x.im + y.im)
    rw [show (x.re + y.re) + f.b * (x.im + y.im) =
      (x.re + f.b * x.im) + (y.re + f.b * y.im) by ring]
    exact dvd_add hx hy
  smul_mem' := by
    intro r x hx
    change f.a ∣ r.re * x.re + (-f.a * f.c) * r.im * x.im +
      f.b * (r.re * x.im + r.im * x.re + f.b * r.im * x.im)
    have h := dvd_add (hx.mul_left (r.re + f.b * r.im))
      (show f.a ∣ (-f.a * f.c) * r.im * x.im from by use -f.c * r.im * x.im; ring)
    rw [show r.re * x.re + (-f.a * f.c) * r.im * x.im +
        f.b * (r.re * x.im + r.im * x.re + f.b * r.im * x.im) =
      (r.re + f.b * r.im) * (x.re + f.b * x.im) + (-f.a * f.c) * r.im * x.im by ring]
    exact h

@[simp] theorem mem_formIdeal (f : BinQuadForm) (z : f.Order) :
    z ∈ f.formIdeal ↔ f.a ∣ z.re := Iff.rfl

@[simp] theorem mem_conjugateFormIdeal (f : BinQuadForm) (z : f.Order) :
    z ∈ f.conjugateFormIdeal ↔ f.a ∣ z.re + f.b * z.im := Iff.rfl

theorem quadratic_intCast_dvd {d b : ℤ} (a : ℤ) (z : QuadraticAlgebra ℤ d b) :
    (a : QuadraticAlgebra ℤ d b) ∣ z ↔ a ∣ z.re ∧ a ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id,
      mul_zero, zero_mul, add_zero]
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨u, v⟩, ?_⟩
    ext <;> simp [hu, hv]

theorem primitive_bezout {f : BinQuadForm} (hf : f.Primitive) :
    ∃ r s t : ℤ, r * f.a + s * f.b + t * f.c = 1 := by
  let g : ℤ := Int.gcd f.b f.c
  refine ⟨Int.gcdA f.a g, Int.gcdB f.a g * Int.gcdA f.b f.c,
    Int.gcdB f.a g * Int.gcdB f.b f.c, ?_⟩
  have h₁ := Int.gcd_eq_gcd_ab f.a g
  have h₂ := Int.gcd_eq_gcd_ab f.b f.c
  have hg : Int.gcd f.a g = 1 := hf
  rw [hg] at h₁
  change g = _ at h₂
  linear_combination -h₁ - Int.gcdB f.a g * h₂

theorem formIdeal_mul_conjugate {f : BinQuadForm} (hf : f.Primitive) :
    f.formIdeal * f.conjugateFormIdeal = Ideal.span ({(f.a : f.Order)} : Set f.Order) := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_singleton, quadratic_intCast_dvd]
    constructor
    · change f.a ∣ x.re * y.re + (-f.a * f.c) * x.im * y.im
      exact dvd_add (hx.mul_right _) (by use -f.c * x.im * y.im; ring)
    · change f.a ∣ x.re * y.im + x.im * y.re + f.b * x.im * y.im
      have h := dvd_add (hx.mul_right y.im) (hy.mul_left x.im)
      rw [show x.re * y.im + x.im * y.re + f.b * x.im * y.im =
        x.re * y.im + x.im * (y.re + f.b * y.im) by ring]
      exact h
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    let ω : f.Order := ⟨0, 1⟩
    let ω' : f.Order := ⟨f.b, -1⟩
    have haI : (f.a : f.Order) ∈ f.formIdeal := by simp
    have haJ : (f.a : f.Order) ∈ f.conjugateFormIdeal := by simp
    have hwI : ω ∈ f.formIdeal := by simp [ω]
    have hwJ : ω' ∈ f.conjugateFormIdeal := by simp [ω']
    have haa : ((f.a * f.a : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      simpa only [Int.cast_mul] using Ideal.mul_mem_mul haI haJ
    have hab : ((f.a * f.b : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      have h := (f.formIdeal * f.conjugateFormIdeal).add_mem
        (Ideal.mul_mem_mul haI hwJ) (Ideal.mul_mem_mul hwI haJ)
      convert h using 1 <;> ext <;> simp [ω, ω'] <;> ring
    have hac : ((f.a * f.c : ℤ) : f.Order) ∈ f.formIdeal * f.conjugateFormIdeal := by
      have h := Ideal.mul_mem_mul hwI hwJ
      convert h using 1 <;> ext <;> simp [ω, ω'] <;> ring
    obtain ⟨r, s, t, hst⟩ := primitive_bezout hf
    have h := (f.formIdeal * f.conjugateFormIdeal).add_mem
      ((f.formIdeal * f.conjugateFormIdeal).add_mem
        ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (r : f.Order) haa)
        ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (s : f.Order) hab))
      ((f.formIdeal * f.conjugateFormIdeal).mul_mem_left (t : f.Order) hac)
    have heq : r * (f.a * f.a) + s * (f.a * f.b) + t * (f.a * f.c) = f.a := by
      linear_combination f.a * hst
    simpa only [← Int.cast_mul, ← Int.cast_add, heq] using h

theorem norm_formIdeal_element (f : BinQuadForm) (u v : ℤ) :
    (⟨f.a * u, v⟩ : f.Order).norm = f.a * f.eval u v := by
  simp only [QuadraticAlgebra.norm_def, eval]
  ring

theorem represented_iff_formIdeal_norm {f : BinQuadForm} (ha : f.a ≠ 0) (n : ℤ) :
    (∃ u v : ℤ, f.eval u v = n) ↔ ∃ z ∈ f.formIdeal, z.norm = f.a * n := by
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨⟨f.a * u, v⟩, dvd_mul_right _ _, by rw [norm_formIdeal_element, h]⟩
  · rintro ⟨z, hz, hn⟩
    obtain ⟨u, hu⟩ := hz
    refine ⟨u, z.im, mul_left_cancel₀ ha ?_⟩
    have hzeq : (⟨f.a * u, z.im⟩ : f.Order) = z := QuadraticAlgebra.ext hu.symm rfl
    rw [← norm_formIdeal_element, hzeq, hn]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/InvertibleIdeal.lean` -/

section
/-!
# Integral invertible ideals of a finite order

This packages the general ideal operations used in the ring-class argument,
without restricting the order to `ℤ[√(-p³)]`.
-/

open scoped nonZeroDivisors

namespace Bernays

def InvertibleIdeal (S : Type*) [CommRing S] [IsDomain S] :=
  {I : Ideal S // IsUnit (I : FractionalIdeal S⁰ (FractionRing S))}

namespace InvertibleIdeal

variable {S : Type*} [CommRing S] [IsDomain S]

instance : Coe (InvertibleIdeal S) (Ideal S) := ⟨Subtype.val⟩

@[ext] theorem ext {I J : InvertibleIdeal S} (h : (I : Ideal S) = J) : I = J := Subtype.ext h

instance : One (InvertibleIdeal S) := ⟨⟨⊤, by simpa using
  (isUnit_one : IsUnit (1 : FractionalIdeal S⁰ (FractionRing S)))⟩⟩

instance : Mul (InvertibleIdeal S) := ⟨fun I J => ⟨(I : Ideal S) * J, by
  rw [FractionalIdeal.coeIdeal_mul]
  exact I.2.mul J.2⟩⟩

instance : CommMonoid (InvertibleIdeal S) where
  mul_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)
  one_mul _ := Subtype.ext (Ideal.top_mul _)
  mul_one _ := Subtype.ext (Ideal.mul_top _)
  mul_comm _ _ := Subtype.ext (mul_comm _ _)

@[simp] theorem coe_one : ((1 : InvertibleIdeal S) : Ideal S) = ⊤ := rfl
@[simp] theorem coe_mul (I J : InvertibleIdeal S) : ((I * J : InvertibleIdeal S) : Ideal S) =
    (I : Ideal S) * J := rfl

noncomputable def unit (I : InvertibleIdeal S) : (FractionalIdeal S⁰ (FractionRing S))ˣ := I.2.unit

@[simp] theorem unit_coe (I : InvertibleIdeal S) :
    (I.unit : FractionalIdeal S⁰ (FractionRing S)) = (I : Ideal S) := I.2.unit_spec

theorem unit_injective : Function.Injective (unit : InvertibleIdeal S → _) := by
  intro I J h
  apply ext
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
  simpa only [unit_coe] using congrArg Units.val h

@[simp] theorem unit_one : (1 : InvertibleIdeal S).unit = 1 := by
  apply Units.ext
  simp

@[simp] theorem unit_mul (I J : InvertibleIdeal S) : (I * J).unit = I.unit * J.unit := by
  apply Units.ext
  simp [FractionalIdeal.coeIdeal_mul]

noncomputable def idealClass (I : InvertibleIdeal S) : ClassGroup S :=
  ClassGroup.mk (FractionRing S) I.unit

@[simp] theorem idealClass_one : idealClass (1 : InvertibleIdeal S) = 1 := by
  simp [idealClass]

@[simp] theorem idealClass_mul (I J : InvertibleIdeal S) :
    idealClass (I * J) = idealClass I * idealClass J := by simp [idealClass]

theorem idealClass_surjective : Function.Surjective (idealClass : InvertibleIdeal S → ClassGroup S) := by
  intro C
  refine ClassGroup.induction (FractionRing S) ?_ C
  intro U
  obtain ⟨V, hV, hc⟩ := Erdos1081.exists_integralUnitRep U
  let I : InvertibleIdeal S := ⟨U.1.num, ⟨V, hV⟩⟩
  refine ⟨I, ?_⟩
  have hunit : I.unit = V := Units.ext (I.2.unit_spec.trans hV.symm)
  simpa only [idealClass, hunit] using hc

theorem ne_bot (I : InvertibleIdeal S) : (I : Ideal S) ≠ ⊥ := by
  intro h
  have hz : (I.unit : FractionalIdeal S⁰ (FractionRing S)) = 0 := by simp [h]
  exact I.unit.ne_zero hz

noncomputable def principal (a : S) (ha : a ≠ 0) : InvertibleIdeal S :=
  ⟨Ideal.span {a}, IsUnit.of_mul_eq_one _
    (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) ha)⟩

@[simp] theorem coe_principal (a : S) (ha : a ≠ 0) :
    (principal a ha : Ideal S) = Ideal.span {a} := rfl

@[simp] theorem idealClass_principal (a : S) (ha : a ≠ 0) :
    (principal a ha).idealClass = 1 := by
  exact (ClassGroup.mk_eq_one_of_coe_ideal (unit_coe _)).mpr ⟨a, ha, rfl⟩

theorem idealClass_eq_one_iff (I : InvertibleIdeal S) :
    I.idealClass = 1 ↔ ∃ a : S, ∃ ha : a ≠ 0, I = principal a ha := by
  rw [idealClass, ClassGroup.mk_eq_one_of_coe_ideal (unit_coe I)]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, ext h⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem exists_mul_eq_of_le (P I : InvertibleIdeal S) (hPI : (I : Ideal S) ≤ P) :
    ∃ J : InvertibleIdeal S, P * J = I := by
  let PF : FractionalIdeal S⁰ (FractionRing S) := (P : Ideal S)
  let IF : FractionalIdeal S⁰ (FractionRing S) := (I : Ideal S)
  have hPF : PF * PF⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing S)).mpr P.2
  have hu : IsUnit (PF⁻¹ * IF) :=
    (IsUnit.of_mul_eq_one PF (by rw [mul_comm, hPF])).mul I.2
  have hle : PF⁻¹ * IF ≤ 1 := by
    calc
      PF⁻¹ * IF ≤ PF⁻¹ * PF := by
        gcongr
        exact (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)).mpr hPI
      _ = 1 := by rw [mul_comm, hPF]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨⟨J, ⟨hu.unit, hu.unit_spec.trans hJ.symm⟩⟩, ?_⟩
  apply ext
  change (P : Ideal S) * J = (I : Ideal S)
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing S)
  change (((P : Ideal S) * J : Ideal S) : FractionalIdeal S⁰ (FractionRing S)) =
    ((I : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
  rw [FractionalIdeal.coeIdeal_mul]
  change PF * (J : FractionalIdeal S⁰ (FractionRing S)) = IF
  rw [hJ, ← mul_assoc, hPF, one_mul]

theorem mul_right_cancel (I J K : InvertibleIdeal S) (h : I * K = J * K) : I = J := by
  apply unit_injective
  have hu := congrArg unit h
  simpa only [unit_mul, mul_left_inj] using hu

theorem cardQuot_pos [Ring.HasFiniteQuotients S] (I : InvertibleIdeal S) :
    0 < (I : Ideal S).cardQuot := Ring.HasFiniteQuotients.cardQuot_pos _ I.ne_bot

end InvertibleIdeal

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticPrimeIdeals.lean` -/

section
/-!
# Prime ideals of a quadratic order away from the discriminant
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticReduction (d b : ℤ) (q : ℕ) :
    QuadraticAlgebra ℤ d b →+* QuadraticAlgebra (ZMod q) (d : ZMod q) (b : ZMod q) where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem quadraticReduction_surjective (d b : ℤ) (q : ℕ) :
    Function.Surjective (quadraticReduction d b q) := by
  intro z
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective z.re
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective z.im
  exact ⟨⟨u, v⟩, QuadraticAlgebra.ext hu hv⟩

theorem quadraticReduction_ker (d b : ℤ) (q : ℕ) :
    RingHom.ker (quadraticReduction d b q) =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, BinQuadForm.quadratic_intCast_dvd]
  change (QuadraticAlgebra.mk (z.re : ZMod q) (z.im : ZMod q) = 0) ↔ _
  rw [QuadraticAlgebra.ext_iff]
  simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem cardQuot_ker_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) :
    (RingHom.ker φ).cardQuot = Nat.card S :=
  Nat.card_congr (RingHom.quotientKerEquivOfSurjective hφ).toEquiv

theorem quadraticReduction_cardQuot (d b : ℤ) (q : ℕ) [NeZero q] :
    (RingHom.ker (quadraticReduction d b q)).cardQuot = q ^ 2 := by
  rw [cardQuot_ker_of_surjective _ (quadraticReduction_surjective d b q)]
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (d : ZMod q) (b : ZMod q)),
    Nat.card_prod, Nat.card_zmod, pow_two]

theorem inertIdeal_isMaximal (d b : ℤ) (q : ℕ) [Fact q.Prime]
    (hirr : ∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r) :
    (Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b))).IsMaximal := by
  letI : Fact (∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r) := ⟨hirr⟩
  rw [← quadraticReduction_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (quadraticReduction_surjective d b q)

def quadraticEval (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    QuadraticAlgebra ℤ d b →+* ZMod q where
  toFun z := (z.re : ZMod q) + (z.im : ZMod q) * r
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul]
    linear_combination -(x.im : ZMod q) * (y.im : ZMod q) * hr

theorem quadraticEval_surjective (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    Function.Surjective (quadraticEval d b q r hr) := by
  intro a
  obtain ⟨u, rfl⟩ := ZMod.intCast_surjective a
  exact ⟨⟨u, 0⟩, by simp [quadraticEval]⟩

def rootIdeal (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) : Ideal (QuadraticAlgebra ℤ d b) :=
  RingHom.ker (quadraticEval d b q r hr)

theorem rootIdeal_cardQuot (d b : ℤ) (q : ℕ) (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    (rootIdeal d b q r hr).cardQuot = q := by
  rw [rootIdeal, cardQuot_ker_of_surjective _ (quadraticEval_surjective d b q r hr)]
  exact Nat.card_zmod q

theorem rootIdeal_isMaximal (d b : ℤ) (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) :
    (rootIdeal d b q r hr).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (quadraticEval_surjective d b q r hr)

theorem rootIdeal_ne_of_ne (d b : ℤ) (q : ℕ) [NeZero q] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr ≠ rootIdeal d b q s hs := by
  intro heq
  let z : QuadraticAlgebra ℤ d b := ⟨-(r.val : ℤ), 1⟩
  have hz : z ∈ rootIdeal d b q r hr := by
    simp [rootIdeal, quadraticEval, z, RingHom.mem_ker]
  rw [heq] at hz
  have hz' : -r + s = 0 := by simpa [rootIdeal, quadraticEval, z, RingHom.mem_ker] using hz
  exact hrs (eq_of_sub_eq_zero (by linear_combination -hz'))

theorem rootIdeal_inf (d b : ℤ) (q : ℕ) [Fact q.Prime] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr ⊓ rootIdeal d b q s hs =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  rw [← quadraticReduction_ker]
  ext z
  change ((z.re : ZMod q) + (z.im : ZMod q) * r = 0 ∧
    (z.re : ZMod q) + (z.im : ZMod q) * s = 0) ↔ quadraticReduction d b q z = 0
  constructor
  · rintro ⟨hrz, hsz⟩
    have him : (z.im : ZMod q) = 0 := by
      apply (mul_eq_zero.mp (show (z.im : ZMod q) * (r - s) = 0 from by
        linear_combination hrz - hsz)).resolve_right (sub_ne_zero.mpr hrs)
    have hre : (z.re : ZMod q) = 0 := by simpa [him] using hrz
    exact QuadraticAlgebra.ext hre him
  · intro hz
    have hre := congrArg QuadraticAlgebra.re hz
    have him := congrArg QuadraticAlgebra.im hz
    change (z.re : ZMod q) = 0 at hre
    change (z.im : ZMod q) = 0 at him
    simp [hre, him]

theorem rootIdeal_mul (d b : ℤ) (q : ℕ) [Fact q.Prime] {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r ≠ s) :
    rootIdeal d b q r hr * rootIdeal d b q s hs =
      Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set (QuadraticAlgebra ℤ d b)) := by
  rw [Ideal.mul_eq_inf_of_coprime ((rootIdeal_isMaximal d b q r hr).coprime_of_ne
    (rootIdeal_isMaximal d b q s hs) (rootIdeal_ne_of_ne d b q hr hs hrs))]
  exact rootIdeal_inf d b q hr hs hrs

end Bernays

end

/-! ### Upstream module `Util/Bernays/DiscriminantCharacter.lean` -/

section
/-!
# A quadratic Dirichlet character for any negative discriminant

We use modulus `4|D|`, so the bad primes include `2` and every divisor of
the discriminant. On odd coprime natural numbers the value is the Jacobi symbol.
-/

open scoped Classical

namespace Bernays

def discriminantLevel (D : ℤ) : ℕ := 4 * D.natAbs

theorem discriminantLevel_pos {D : ℤ} (hD : D ≠ 0) : 0 < discriminantLevel D :=
  Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hD)

theorem discriminantLevel_one_lt {D : ℤ} (hD : D ≠ 0) : 1 < discriminantLevel D := by
  have := Int.natAbs_pos.mpr hD
  unfold discriminantLevel
  omega

theorem odd_of_coprime_discriminantLevel {D : ℤ} {n : ℕ}
    (hn : n.Coprime (discriminantLevel D)) : Odd n :=
  (hn.of_dvd_right (show 2 ∣ discriminantLevel D by exact ⟨2 * D.natAbs, by
    unfold discriminantLevel; ring⟩)).odd_of_right

theorem odd_val_of_isUnit_discriminant {D : ℤ} (hD : D ≠ 0) {a : ZMod (discriminantLevel D)}
    (ha : IsUnit a) : Odd a.val := by
  letI : NeZero (discriminantLevel D) := ⟨(discriminantLevel_pos hD).ne'⟩
  apply odd_of_coprime_discriminantLevel (D := D)
  exact (ZMod.isUnit_iff_coprime a.val _).mp (by simpa using ha)

noncomputable def discriminantCharacter (D : ℤ) (hD : D ≠ 0) :
    DirichletCharacter ℂ (discriminantLevel D) where
  toFun a := if IsUnit a then (jacobiSym D a.val : ℂ) else 0
  map_nonunit' a ha := by simp [ha]
  map_one' := by
    simp only [isUnit_one, if_true]
    rw [ZMod.val_one'' (discriminantLevel_one_lt hD).ne', jacobiSym.one_right, Int.cast_one]
  map_mul' a b := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ha, hb, ha.mul hb, if_true]
        have hao := odd_val_of_isUnit_discriminant hD ha
        have hbo := odd_val_of_isUnit_discriminant hD hb
        rw [ZMod.val_mul]
        change (jacobiSym D (a.val * b.val % (4 * D.natAbs)) : ℂ) = _
        rw [← jacobiSym.mod_right D (hao.mul hbo),
          jacobiSym.mul_right' D hao.pos.ne' hbo.pos.ne', Int.cast_mul]
      · simp [ha, hb, IsUnit.mul_iff]
    · simp [ha, IsUnit.mul_iff]

theorem discriminantCharacter_apply_of_coprime (D : ℤ) (hD : D ≠ 0)
    {n : ℕ} (hn : n.Coprime (discriminantLevel D)) :
    discriminantCharacter D hD n = (jacobiSym D n : ℂ) := by
  have hu := (ZMod.isUnit_iff_coprime n (discriminantLevel D)).mpr hn
  change (if IsUnit (n : ZMod (discriminantLevel D)) then
    (jacobiSym D (n : ZMod (discriminantLevel D)).val : ℂ) else 0) = _
  rw [if_pos hu, ZMod.val_natCast]
  exact congrArg (Int.cast : ℤ → ℂ) (jacobiSym.mod_right D (odd_of_coprime_discriminantLevel hn)).symm

theorem discriminantCharacter_sq (D : ℤ) (hD : D ≠ 0) :
    discriminantCharacter D hD ^ 2 = 1 := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mp
  intro a
  change (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = 0 ∨
    (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = 1 ∨
      (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = -1
  by_cases ha : IsUnit a
  · simp only [ha, if_true]
    rcases jacobiSym.trichotomy D a.val with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inr (Or.inr (by simp [h]))
  · exact Or.inl (if_neg ha)

theorem jacobiSym_natAbs_predecessor {D : ℤ} (hD : D ≠ 0) :
    jacobiSym (D.natAbs : ℤ) (discriminantLevel D - 1) = 1 := by
  have hN := discriminantLevel_one_lt hD
  have ho : Odd (discriminantLevel D - 1) := by
    rw [Nat.odd_iff]
    unfold discriminantLevel at *
    omega
  have hmod : (4 * (D.natAbs : ℤ)) % (discriminantLevel D - 1 : ℕ) =
      (1 : ℤ) % (discriminantLevel D - 1 : ℕ) := by
    have hcast : ((discriminantLevel D - 1 : ℕ) : ℤ) = 4 * D.natAbs - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ discriminantLevel D)]
      simp [discriminantLevel]
    rw [hcast]
    simpa only [sub_add_cancel, Int.emod_self, zero_add, Int.emod_emod] using
      (Int.add_emod (4 * (D.natAbs : ℤ) - 1) 1 (4 * D.natAbs - 1))
  have h := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, jacobiSym.at_four ho, one_mul, jacobiSym.one_left] at h
  exact h

theorem discriminantCharacter_ne_one {D : ℤ} (hD : D < 0) :
    discriminantCharacter D hD.ne = 1 → False := by
  intro hχ
  have hN := discriminantLevel_one_lt hD.ne
  have hc : (discriminantLevel D - 1).Coprime (discriminantLevel D) := by
    have h : discriminantLevel D - 1 + 1 = discriminantLevel D := by omega
    have hc := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (discriminantLevel D - 1))
    simpa only [h] using hc
  have ho := odd_of_coprime_discriminantLevel hc
  have hval : jacobiSym D (discriminantLevel D - 1) = -1 := by
    have hneg : D = -(D.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_neg hD, neg_neg]
    nth_rw 1 [hneg]
    rw [jacobiSym.neg _ ho]
    have hthree : (discriminantLevel D - 1) % 4 = 3 := by
      unfold discriminantLevel at *
      omega
    rw [ZMod.χ₄_nat_three_mod_four hthree, jacobiSym_natAbs_predecessor hD.ne, mul_one]
  have hv := discriminantCharacter_apply_of_coprime D hD.ne hc
  rw [hχ, MulChar.one_apply (by exact (ZMod.isUnit_iff_coprime _ _).mpr hc), hval] at hv
  norm_num at hv

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticSplitting.lean` -/

section
/-!
# The character and ideal-theoretic splitting criteria agree
-/

namespace Bernays

theorem quadratic_conjugate_root {K : Type*} [CommRing K] (d b r : K)
    (hr : r ^ 2 = d + b * r) : (b - r) ^ 2 = d + b * (b - r) := by
  linear_combination hr

theorem quadratic_roots_distinct {K : Type*} [Field K] (d b r : K)
    (hr : r ^ 2 = d + b * r) (hD : b ^ 2 + 4 * d ≠ 0) : r ≠ b - r := by
  intro heq
  apply hD
  linear_combination -4 * hr + (2 * r - b) * heq

theorem quadratic_has_root_iff_isSquare {K : Type*} [Field K] [NeZero (2 : K)] (d b : K) :
    (∃ r : K, r ^ 2 = d + b * r) ↔ IsSquare (b ^ 2 + 4 * d) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨2 * r - b, ?_⟩
    linear_combination -4 * hr
  · rintro ⟨s, hs⟩
    refine ⟨(b + s) / 2, ?_⟩
    have ht : (2 : K) ≠ 0 := NeZero.ne 2
    field_simp
    linear_combination -hs

theorem discriminantCharacter_prime_eq_neg_one_iff {D : ℤ} (hD : D ≠ 0)
    {q : ℕ} [Fact q.Prime] (hq : q.Coprime (discriminantLevel D)) :
    discriminantCharacter D hD q = -1 ↔ ¬ IsSquare (D : ZMod q) := by
  rw [discriminantCharacter_apply_of_coprime D hD hq, ← ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
  norm_cast

theorem discriminantCharacter_root_iff {d b : ℤ} {q : ℕ} [Fact q.Prime]
    (hD : b ^ 2 + 4 * d ≠ 0) (hq : q.Coprime (discriminantLevel (b ^ 2 + 4 * d))) :
    (∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) ↔
      discriminantCharacter (b ^ 2 + 4 * d) hD q ≠ -1 := by
  have hq₂ : q ≠ 2 := by
    have ho := Nat.odd_iff.mp (odd_of_coprime_discriminantLevel hq)
    omega
  haveI : NeZero (2 : ZMod q) := ⟨by
    intro hz
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    exact hq₂ ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left (Fact.out : q.Prime).ne_one)⟩
  rw [quadratic_has_root_iff_isSquare, ne_eq, discriminantCharacter_prime_eq_neg_one_iff hD hq,
    not_not]
  simp only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticMaximalIdeals.lean` -/

section
/-!
# Maximal ideals and split-prime classes in arbitrary quadratic orders
-/

open scoped nonZeroDivisors

namespace Bernays

theorem quadraticMaximal_ne_bot (d b : ℤ) (P : Ideal (QuadraticAlgebra ℤ d b))
    (hP : P.IsMaximal) : P ≠ ⊥ := by
  have htwo : Ideal.span ({(2 : QuadraticAlgebra ℤ d b)} : Set _) ≠ ⊤ := by
    intro ht
    have h : (1 : QuadraticAlgebra ℤ d b) ∈ Ideal.span ({2} : Set _) := by rw [ht]; trivial
    rw [Ideal.mem_span_singleton] at h
    have h' := (BinQuadForm.quadratic_intCast_dvd 2 (1 : QuadraticAlgebra ℤ d b)).mp h
    norm_num [QuadraticAlgebra.re_one] at h'
  intro hz
  have heq := hP.eq_of_le htwo (show P ≤ Ideal.span ({2} : Set _) by rw [hz]; exact bot_le)
  have hmem : (2 : QuadraticAlgebra ℤ d b) ∈ (⊥ : Ideal _) := by
    rw [← hz, heq]
    exact Ideal.mem_span_singleton_self 2
  have hre := congrArg QuadraticAlgebra.re (show (2 : QuadraticAlgebra ℤ d b) = 0 from hmem)
  change (2 : ℤ) = 0 at hre
  norm_num at hre

theorem exists_natPrime_under_quadraticMaximal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ P.under ℤ = Ideal.span ({(q : ℤ)} : Set ℤ) := by
  letI := quadraticOrderIsDomain hD
  letI : P.IsMaximal := hP
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have ha₀ : a ≠ 0 := by
    intro hz
    have hpos := Ring.HasFiniteQuotients.cardQuot_pos P (quadraticMaximal_ne_bot d b P hP)
    have hmem : ((P.cardQuot : ℕ) : QuadraticAlgebra ℤ d b) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact Ideal.Quotient.index_eq_zero P
    have hmem' : (P.cardQuot : ℤ) ∈ P.under ℤ := hmem
    rw [ha, hz] at hmem'
    have hzero : (P.cardQuot : ℤ) = 0 := by simpa using hmem'
    have : P.cardQuot = 0 := by exact_mod_cast hzero
    omega
  have hprime : Prime a := by
    apply (Ideal.span_singleton_prime ha₀).mp
    simpa only [← Ideal.submodule_span_eq, ← ha] using hP.isPrime.under ℤ
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  rw [ha]
  rcases abs_choice a with h | h <;> simp [h, Ideal.span_singleton_neg]

theorem quadraticMaximal_split_or_inert (d b : ℤ) (q : ℕ) [Fact q.Prime]
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P)
    (hD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d) :
    P = Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) ∨
      ∃ r : ZMod q, ∃ hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r,
        P = rootIdeal d b q r hr := by
  have hspan := (Ideal.span_singleton_le_iff_mem P).mpr hqP
  by_cases hroot : ∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r
  · obtain ⟨r, hr⟩ := hroot
    have hmod : (b : ZMod q) ^ 2 + 4 * (d : ZMod q) ≠ 0 := by
      intro hz
      apply hD
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hz
    have hs := quadratic_conjugate_root (d : ZMod q) (b : ZMod q) r hr
    have hrs := quadratic_roots_distinct (d : ZMod q) (b : ZMod q) r hr hmod
    have hprod : rootIdeal d b q r hr * rootIdeal d b q ((b : ZMod q) - r) hs ≤ P := by
      rw [rootIdeal_mul d b q hr hs hrs]
      exact hspan
    rcases hP.isPrime.mul_le.mp hprod with h | h
    · exact Or.inr ⟨r, hr, ((rootIdeal_isMaximal d b q r hr).eq_of_le hP.ne_top h).symm⟩
    · exact Or.inr ⟨(b : ZMod q) - r, hs,
        ((rootIdeal_isMaximal d b q _ hs).eq_of_le hP.ne_top h).symm⟩
  · left
    have hirr : ∀ r : ZMod q, r ^ 2 ≠ (d : ZMod q) + (b : ZMod q) * r := by
      simpa only [not_exists] using hroot
    exact ((inertIdeal_isMaximal d b q hirr).eq_of_le hP.ne_top hspan).symm

theorem rootIdeal_isUnit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (q : ℕ) [Fact q.Prime] (r : ZMod q)
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hmod : (b : ZMod q) ^ 2 + 4 * (d : ZMod q) ≠ 0) :
    letI := quadraticOrderIsDomain hD
    IsUnit ((rootIdeal d b q r hr : Ideal (QuadraticAlgebra ℤ d b)) :
      FractionalIdeal (QuadraticAlgebra ℤ d b)⁰ (FractionRing (QuadraticAlgebra ℤ d b))) := by
  letI := quadraticOrderIsDomain hD
  have hs := quadratic_conjugate_root (d : ZMod q) (b : ZMod q) r hr
  have hrs := quadratic_roots_distinct (d : ZMod q) (b : ZMod q) r hr hmod
  have hq₀ : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
    intro hz
    have h := congrArg QuadraticAlgebra.re hz
    have : (q : ℤ) = 0 := by simpa using h
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast this)
  have hu := (InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hq₀).2
  change IsUnit (((Ideal.span ({((q : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) :
    Ideal (QuadraticAlgebra ℤ d b)) : FractionalIdeal (QuadraticAlgebra ℤ d b)⁰
      (FractionRing (QuadraticAlgebra ℤ d b)))) at hu
  rw [← rootIdeal_mul d b q hr hs hrs, FractionalIdeal.coeIdeal_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealNormMultiplicative.lean` -/

section
/-!
# Multiplicativity of the index for invertible ideals in an order

Reduction modulo any nonzero ideal gives a finite ring. Its Picard group is
trivial, so an invertible module has one generator after reduction. This
extends the maximal-ideal index calculation to arbitrary nonzero ideals.
-/

open scoped nonZeroDivisors
open TensorProduct

namespace Bernays

theorem relIndex_invertible_mul {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (P J : Ideal R) (hP : P ≠ ⊥)
    [Module.Invertible R J] :
    (P * J).toAddSubgroup.relIndex J.toAddSubgroup = P.cardQuot := by
  classical
  by_cases htop : P = ⊤
  · subst P
    simp
  let A := R ⧸ P
  let T := A ⊗[R] J
  letI : Nontrivial A := (Ideal.Quotient.nontrivial_iff (R := R) (I := P)).mpr htop
  letI : Finite A := Ring.HasFiniteQuotients.finiteQuotient hP
  letI : IsArtinianRing A := isArtinian_of_finite
  letI : Module.Invertible A T := inferInstance
  letI : Module.Free A T := inferInstance
  let L : Submodule R J := Submodule.comap (J : Submodule R R).subtype (P • (J : Submodule R R))
  change Nat.card (J ⧸ L) = Nat.card A
  let e : (J ⧸ L) ≃ₗ[R] T :=
    Submodule.quotEquivOfEq _ (P • (⊤ : Submodule R J))
      (Submodule.map_injective_of_injective J.injective_subtype
        (by simp [L, Ideal.mul_le_right])) ≪≫ₗ
      (quotTensorEquivQuotSMul J P).symm
  let e' : T ≃ₗ[A] A := (Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free A T)).some
  exact Nat.card_congr (e.toEquiv.trans e'.toEquiv)

theorem cardQuot_mul_invertible {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (P J : Ideal R) (hP : P ≠ ⊥)
    (hJ : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    (P * J).cardQuot = P.cardQuot * J.cardQuot := by
  letI : Module.Invertible R J := Erdos1081.moduleInvertibleIdealOfIsUnit J hJ
  calc
    (P * J).cardQuot =
        (P * J).toAddSubgroup.relIndex J.toAddSubgroup * J.toAddSubgroup.index :=
      (AddSubgroup.relIndex_mul_index (show (P * J).toAddSubgroup ≤ J.toAddSubgroup
        from Ideal.mul_le_right)).symm
    _ = P.cardQuot * J.cardQuot := by rw [relIndex_invertible_mul P J hP]; rfl

namespace InvertibleIdeal

theorem cardQuot_mul {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I J : InvertibleIdeal R) :
    ((I * J : InvertibleIdeal R) : Ideal R).cardQuot =
      (I : Ideal R).cardQuot * (J : Ideal R).cardQuot :=
  cardQuot_mul_invertible _ _ I.ne_bot J.2

end InvertibleIdeal

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealFactorization.lean` -/

section
/-!
# Factorization away from a finite set of bad primes

The only local input is that maximal ideals coprime to the specified modulus
are invertible. Strong induction on the finite index then gives a prime-ideal
factorization, without a Dedekind-domain assumption on the order.
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

theorem coprime_of_le {I J F : Ideal R} (hIJ : I ≤ J) (hI : IsCoprime I F) : IsCoprime J F := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  calc
    ⊤ = I ⊔ F := hI.sup_eq.symm
    _ ≤ J ⊔ F := sup_le_sup_right hIJ F

theorem factor_lt (P I : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal)
    (hIP : (I : Ideal R) ≤ P) :
    ∃ J : InvertibleIdeal R, P * J = I ∧ (J : Ideal R).cardQuot < (I : Ideal R).cardQuot := by
  obtain ⟨J, hJ⟩ := exists_mul_eq_of_le P I hIP
  refine ⟨J, hJ, ?_⟩
  have hcard := cardQuot_mul P J
  rw [hJ] at hcard
  have hP₁ : 1 < (P : Ideal R).cardQuot := by
    have hpos := P.cardQuot_pos
    have hne : (P : Ideal R).cardQuot ≠ 1 := by
      intro h
      exact hP.ne_top (Submodule.cardQuot_eq_one_iff.mp h)
    omega
  rw [hcard]
  exact lt_mul_of_one_lt_left J.cardQuot_pos hP₁

theorem exists_list_maximal_factors (F : Ideal R)
    (hmax : ∀ P : Ideal R, P.IsMaximal → IsCoprime P F →
      IsUnit (P : FractionalIdeal R⁰ (FractionRing R)))
    (I : InvertibleIdeal R) (hI : IsCoprime (I : Ideal R) F) :
    ∃ l : List (InvertibleIdeal R), l.prod = I ∧
      ∀ P ∈ l, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F := by
  suffices ∀ N : ℕ, ∀ I : InvertibleIdeal R, (I : Ideal R).cardQuot = N →
      IsCoprime (I : Ideal R) F →
      ∃ l : List (InvertibleIdeal R), l.prod = I ∧
        ∀ P ∈ l, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F from
    this _ I rfl hI
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro I hN hIF
    by_cases htop : (I : Ideal R) = ⊤
    · exact ⟨[], by simpa using (ext htop).symm, by simp⟩
    · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal (I : Ideal R) htop
      have hPF := coprime_of_le hIP hIF
      let PU : InvertibleIdeal R := ⟨P, hmax P hP hPF⟩
      obtain ⟨J, hmul, hlt⟩ := factor_lt PU I hP hIP
      have hIJ : (I : Ideal R) ≤ (J : Ideal R) := by
        rw [← hmul, coe_mul]
        exact Ideal.mul_le_right
      obtain ⟨l, hl, hmaxl⟩ := ih (J : Ideal R).cardQuot (by rwa [← hN]) J rfl
        (coprime_of_le hIJ hIF)
      refine ⟨PU :: l, by simp only [List.prod_cons, hl, hmul], ?_⟩
      intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨hP, hPF⟩
      · exact hmaxl Q hQ

theorem exists_maximal_factor_class_not_mem (F : Ideal R)
    (hmax : ∀ P : Ideal R, P.IsMaximal → IsCoprime P F →
      IsUnit (P : FractionalIdeal R⁰ (FractionRing R)))
    (H : Subgroup (ClassGroup R)) (I : InvertibleIdeal R)
    (hI : IsCoprime (I : Ideal R) F) (hc : I.idealClass ∉ H) :
    ∃ P J : InvertibleIdeal R, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F ∧
      P.idealClass ∉ H ∧ P * J = I := by
  obtain ⟨l, hl, hmaxl⟩ := exists_list_maximal_factors F hmax I hI
  have hex : ∃ P ∈ l, P.idealClass ∉ H := by
    by_contra hnone
    simp only [not_exists, not_and, not_not] at hnone
    have hprod : l.prod.idealClass ∈ H := by
      clear hl hmaxl
      induction l with
      | nil => simpa using H.one_mem
      | cons P l ih =>
        simp only [List.prod_cons, idealClass_mul]
        exact H.mul_mem (hnone P (by simp)) (ih (by
          intro Q hQ
          exact hnone Q (List.mem_cons_of_mem _ hQ)))
    exact hc (hl ▸ hprod)
  obtain ⟨P, hPl, hcP⟩ := hex
  obtain ⟨l₁, l₂, heq⟩ := List.mem_iff_append.mp hPl
  refine ⟨P, l₁.prod * l₂.prod, (hmaxl P hPl).1, (hmaxl P hPl).2, hcP, ?_⟩
  rw [← hl, heq, List.prod_append, List.prod_cons]
  ac_rfl

end Bernays.InvertibleIdeal

end

/-! ### Upstream module `Util/Bernays/GoodQuadraticIdeals.lean` -/

section
/-!
# Factorization of ideals coprime to the quadratic discriminant
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticBadIdeal (d b : ℤ) : Ideal (QuadraticAlgebra ℤ d b) :=
  Ideal.span ({((discriminantLevel (b ^ 2 + 4 * d) : ℕ) : QuadraticAlgebra ℤ d b)} : Set _)

theorem prime_not_dvd_level_of_coprime {d b : ℤ} {q : ℕ}
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P)
    (hcop : IsCoprime P (quadraticBadIdeal d b)) :
    ¬ q ∣ discriminantLevel (b ^ 2 + 4 * d) := by
  rintro ⟨k, hk⟩
  have hmem : ((discriminantLevel (b ^ 2 + 4 * d) : ℕ) : QuadraticAlgebra ℤ d b) ∈ P := by
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right (k : QuadraticAlgebra ℤ d b) hqP
  have hle : quadraticBadIdeal d b ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  apply hP.ne_top
  apply top_unique
  rw [← hcop.sup_eq]
  exact sup_le le_rfl hle

theorem quadraticMaximal_coprime_isUnit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (P : Ideal (QuadraticAlgebra ℤ d b)) (hP : P.IsMaximal)
    (hcop : IsCoprime P (quadraticBadIdeal d b)) :
    letI := quadraticOrderIsDomain hD
    IsUnit (P : FractionalIdeal (QuadraticAlgebra ℤ d b)⁰
      (FractionRing (QuadraticAlgebra ℤ d b))) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨q, hq, hunder⟩ := exists_natPrime_under_quadraticMaximal hD P hP
  letI : Fact q.Prime := ⟨hq⟩
  have hqP : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ P := by
    change (q : ℤ) ∈ P.under ℤ
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime P hP hqP hcop
  have hqD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro hdvd
    have hn : q ∣ (b ^ 2 + 4 * d).natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    exact hnot (hn.trans (dvd_mul_left _ _))
  rcases quadraticMaximal_split_or_inert d b q P hP hqP hqD with h | ⟨r, hr, h⟩
  · rw [h]
    have hz : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
      intro hz
      have hc := congrArg QuadraticAlgebra.re hz
      have : (q : ℤ) = 0 := by simpa using hc
      exact hq.ne_zero (by exact_mod_cast this)
    exact (InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hz).2
  · rw [h]
    apply rootIdeal_isUnit hD q r hr
    intro hz
    apply hqD
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hz

theorem goodQuadraticIdeal_factorization {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ l : List (InvertibleIdeal (QuadraticAlgebra ℤ d b)), l.prod = I ∧
        ∀ P ∈ l, (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
          IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) := by
  letI := quadraticOrderIsDomain hD
  exact InvertibleIdeal.exists_list_maximal_factors (quadraticBadIdeal d b)
    (quadraticMaximal_coprime_isUnit hD)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SplitPrimeClasses.lean` -/

section
/-!
# Canonical split-prime classes for arbitrary negative quadratic orders
-/

namespace Bernays

def SplitPrime (d b : ℤ) := {q : ℕ // q.Prime ∧ ¬(q : ℤ) ∣ b ^ 2 + 4 * d ∧
  ∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r}

namespace SplitPrime

variable {d b : ℤ}

instance (s : SplitPrime d b) : Fact s.1.Prime := ⟨s.2.1⟩

noncomputable def root (s : SplitPrime d b) : ZMod s.1 := s.2.2.2.choose

theorem root_sq (s : SplitPrime d b) : (root s) ^ 2 =
    (d : ZMod s.1) + (b : ZMod s.1) * root s := s.2.2.2.choose_spec

theorem discr_ne_zero (s : SplitPrime d b) :
    (b : ZMod s.1) ^ 2 + 4 * (d : ZMod s.1) ≠ 0 := by
  intro h
  apply s.2.2.1
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h

noncomputable def orientedRoot (s : SplitPrime d b) (ε : Bool) : ZMod s.1 :=
  if ε then (b : ZMod s.1) - s.root else s.root

theorem orientedRoot_sq (s : SplitPrime d b) (ε : Bool) :
    (s.orientedRoot ε) ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * s.orientedRoot ε := by
  cases ε
  · exact s.root_sq
  · exact quadratic_conjugate_root _ _ _ s.root_sq

noncomputable def ideal (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    InvertibleIdeal (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  ⟨rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε),
    rootIdeal_isUnit hD _ _ (s.orientedRoot_sq ε) s.discr_ne_zero⟩

theorem ideal_cardQuot (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 :=
  rootIdeal_cardQuot d b s.1 _ _

theorem ideal_isMaximal (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal :=
  rootIdeal_isMaximal d b s.1 _ _

noncomputable def idealClass (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  (s.ideal hD false).idealClass

theorem ideal_mul_conjugate (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ((s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)) * (s.ideal hD true : Ideal _)) =
      Ideal.span ({((s.1 : ℤ) : QuadraticAlgebra ℤ d b)} : Set _) := by
  letI := quadraticOrderIsDomain hD
  exact rootIdeal_mul d b s.1 s.root_sq (s.orientedRoot_sq true)
    (quadratic_roots_distinct _ _ _ s.root_sq s.discr_ne_zero)

theorem idealClass_conjugate (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD true).idealClass = (s.idealClass hD)⁻¹ := by
  letI := quadraticOrderIsDomain hD
  have hq : ((s.1 : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : (s.1 : ℤ) = 0 := by simpa using hr
    exact s.2.1.ne_zero (by exact_mod_cast this)
  have hprod : s.ideal hD false * s.ideal hD true =
      InvertibleIdeal.principal ((s.1 : ℤ) : QuadraticAlgebra ℤ d b) hq :=
    InvertibleIdeal.ext (s.ideal_mul_conjugate hD)
  have hc := congrArg InvertibleIdeal.idealClass hprod
  rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at hc
  change (s.ideal hD true).idealClass = (s.ideal hD false).idealClass⁻¹
  calc
    _ = (s.ideal hD false).idealClass⁻¹ *
        ((s.ideal hD false).idealClass * (s.ideal hD true).idealClass) := by simp
    _ = _ := by rw [hc, mul_one]

theorem root_eq_or_conjugate (s : SplitPrime d b) (r : ZMod s.1)
    (hr : r ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * r) :
    r = s.root ∨ r = (b : ZMod s.1) - s.root := by
  have h : (r - s.root) * (r - ((b : ZMod s.1) - s.root)) = 0 := by
    linear_combination hr - s.root_sq
  exact (mul_eq_zero.mp h).imp sub_eq_zero.mp sub_eq_zero.mp

theorem oriented_idealClass_mem_iff (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), ∀ ε : Bool,
      (s.ideal hD ε).idealClass ∈ H ↔ s.idealClass hD ∈ H := by
  letI := quadraticOrderIsDomain hD
  intro H ε
  cases ε
  · rfl
  · rw [s.idealClass_conjugate hD, H.inv_mem_iff]

end SplitPrime

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassPrimeFactors.lean` -/

section
/-!
# Detecting a split-prime class outside a proper subgroup
-/

namespace Bernays

theorem rootIdeal_eq_of_root_eq {d b : ℤ} {q : ℕ} {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r = s) :
    rootIdeal d b q r hr = rootIdeal d b q s hs := by
  subst s
  rfl

theorem exists_splitPrime_factor_outside {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)),
      ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) → I.idealClass ∉ H →
        ∃ s : SplitPrime d b, s.idealClass hD ∉ H ∧
          s.1 ≤ (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∧
          ∃ ε : Bool, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b), s.ideal hD ε * J = I := by
  letI := quadraticOrderIsDomain hD
  intro H I hIF hIH
  obtain ⟨P, J, hP, hPF, hPH, hPJ⟩ := InvertibleIdeal.exists_maximal_factor_class_not_mem
    (quadraticBadIdeal d b) (quadraticMaximal_coprime_isUnit hD) H I hIF hIH
  obtain ⟨q, hq, hqP⟩ := exists_natPrime_under_quadraticMaximal hD
    (P : Ideal (QuadraticAlgebra ℤ d b)) hP
  letI : Fact q.Prime := ⟨hq⟩
  have hmem : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    change (q : ℤ) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)).under ℤ
    rw [hqP]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hPF
  have hqD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro hdvd
    have hn : q ∣ (b ^ 2 + 4 * d).natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    exact hnot (hn.trans (dvd_mul_left _ _))
  rcases quadraticMaximal_split_or_inert d b q (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hqD with
    hprincipal | ⟨r, hr, hroot⟩
  · exfalso
    apply hPH
    have hz : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
      intro hz
      have h := congrArg QuadraticAlgebra.re hz
      have : (q : ℤ) = 0 := by simpa using h
      exact hq.ne_zero (by exact_mod_cast this)
    have heq : P = InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hz :=
      InvertibleIdeal.ext hprincipal
    rw [heq, InvertibleIdeal.idealClass_principal]
    exact H.one_mem
  · let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    have hs : ∃ ε : Bool, P = s.ideal hD ε := by
      rcases s.root_eq_or_conjugate r hr with h | h
      · refine ⟨false, InvertibleIdeal.ext ?_⟩
        change (P : Ideal (QuadraticAlgebra ℤ d b)) = rootIdeal d b q s.root s.root_sq
        exact hroot.trans (rootIdeal_eq_of_root_eq hr s.root_sq h)
      · refine ⟨true, InvertibleIdeal.ext ?_⟩
        change (P : Ideal (QuadraticAlgebra ℤ d b)) =
          rootIdeal d b q ((b : ZMod q) - s.root) (s.orientedRoot_sq true)
        exact hroot.trans (rootIdeal_eq_of_root_eq hr (s.orientedRoot_sq true) h)
    obtain ⟨ε, hε⟩ := hs
    refine ⟨s, ?_, ?_, ε, J, by rwa [← hε]⟩
    · intro h
      apply hPH
      rw [hε]
      exact (s.oriented_idealClass_mem_iff hD H ε).mpr h
    · have hnorm := InvertibleIdeal.cardQuot_mul P J
      rw [hPJ] at hnorm
      have hPnorm : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 := by
        rw [hε, s.ideal_cardQuot hD ε]
      rw [hnorm, ← hPnorm]
      exact Nat.le_mul_of_pos_right _ J.cardQuot_pos

end Bernays

end

/-! ### Upstream module `Util/Bernays/SplitResidues.lean` -/

section
/-!
# Exact local and simultaneous sieve densities at split primes
-/

open scoped Classical

namespace Bernays

def affineScalarEquiv {K : Type*} [Field K] (c μ : K) (hμ : μ ≠ 0) : K ≃ K where
  toFun x := c + μ * x
  invFun y := (y - c) / μ
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring

def rootCoordinateEquiv {K : Type*} [Field K] (r s : K) (hrs : r ≠ s) : K × K ≃ K × K where
  toFun x := (x.1 + x.2 * r, x.1 + x.2 * s)
  invFun y := ((r * y.2 - s * y.1) / (r - s), (y.1 - y.2) / (r - s))
  left_inv x := by
    have h : r - s ≠ 0 := sub_ne_zero.mpr hrs
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring
  right_inv y := by
    have h : r - s ≠ 0 := sub_ne_zero.mpr hrs
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring

def AffineAllowedPairs {K : Type*} [Field K] (r s c₀ c₁ μ : K) :=
  {x : K × K // c₀ + μ * x.1 + (c₁ + μ * x.2) * r ≠ 0 ∧
    c₀ + μ * x.1 + (c₁ + μ * x.2) * s ≠ 0}

def affineAllowedPairsEquiv {K : Type*} [Field K] (r s c₀ c₁ μ : K)
    (hrs : r ≠ s) (hμ : μ ≠ 0) :
    AffineAllowedPairs r s c₀ c₁ μ ≃ {x : K // x ≠ 0} × {y : K // y ≠ 0} :=
  (Equiv.subtypeEquiv
    ((Equiv.prodCongr (affineScalarEquiv c₀ μ hμ) (affineScalarEquiv c₁ μ hμ)).trans
      (rootCoordinateEquiv r s hrs)) (fun _ => Iff.rfl)).trans
    { toFun := fun (x : {x : K × K // x.1 ≠ 0 ∧ x.2 ≠ 0}) =>
        (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun (x : {x : K // x ≠ 0} × {y : K // y ≠ 0}) =>
        ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }

theorem natCard_affineAllowedPairs {q : ℕ} [Fact q.Prime] (r s c₀ c₁ μ : ZMod q)
    (hrs : r ≠ s) (hμ : μ ≠ 0) :
    Nat.card (AffineAllowedPairs r s c₀ c₁ μ) = (q - 1) ^ 2 := by
  have hcard : Nat.card {x : ZMod q // x ≠ 0} = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  rw [Nat.card_congr (affineAllowedPairsEquiv r s c₀ c₁ μ hrs hμ), Nat.card_prod, hcard, pow_two]

variable {d b : ℤ}

def splitSieveModulus (S : Finset (SplitPrime d b)) : ℕ := ∏ s ∈ S, s.1

theorem splitSieveModulus_pos (S : Finset (SplitPrime d b)) : 0 < splitSieveModulus S :=
  Finset.prod_pos fun s _ => s.2.1.pos

theorem splitPrime_pairwise_coprime (S : Finset (SplitPrime d b)) :
    Pairwise (fun a b : {s // s ∈ S} => Nat.Coprime a.1.1 b.1.1) := by
  intro a b hab
  apply (Nat.coprime_primes a.1.2.1 b.1.2.1).mpr
  intro hq
  exact hab (Subtype.ext (Subtype.ext hq))

noncomputable def splitResidueEquivPi (S : Finset (SplitPrime d b)) :
    ZMod (splitSieveModulus S) ≃+* (∀ s : {s // s ∈ S}, ZMod s.1.1) := by
  have hprod : (∏ s : {s // s ∈ S}, s.1.1) = splitSieveModulus S := by
    simpa only [Finset.attach_eq_univ, splitSieveModulus] using S.prod_attach (fun s => s.1)
  exact (ZMod.ringEquivCongr hprod.symm).trans
    (ZMod.prodEquivPi (fun s : {s // s ∈ S} => s.1.1) (splitPrime_pairwise_coprime S))

theorem splitResidueEquivPi_apply (S : Finset (SplitPrime d b))
    (x : ZMod (splitSieveModulus S)) (s : {s // s ∈ S}) :
    splitResidueEquivPi S x s = (x.val : ZMod s.1.1) := by
  letI : NeZero (splitSieveModulus S) := ⟨(splitSieveModulus_pos S).ne'⟩
  have hdiv : s.1.1 ∣ splitSieveModulus S := Finset.dvd_prod_of_mem (fun s => s.1) s.2
  let f : ZMod (splitSieveModulus S) →+* ZMod s.1.1 :=
    (Pi.evalRingHom (fun s : {s // s ∈ S} => ZMod s.1.1) s).comp (splitResidueEquivPi S).toRingHom
  have hf : f = ZMod.castHom hdiv (ZMod s.1.1) := Subsingleton.elim _ _
  change f x = _
  rw [hf, ZMod.castHom_apply, ZMod.cast_eq_val]

noncomputable def splitResiduePairEquivPi (S : Finset (SplitPrime d b)) :
    (ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S)) ≃
      (∀ s : {s // s ∈ S}, ZMod s.1.1 × ZMod s.1.1) := by
  let e := splitResidueEquivPi S
  exact
    { toFun x s := (e x.1 s, e x.2 s)
      invFun y := (e.symm (fun s => (y s).1), e.symm (fun s => (y s).2))
      left_inv x := Prod.ext (e.symm_apply_apply x.1) (e.symm_apply_apply x.2)
      right_inv y := by
        funext s
        exact Prod.ext (congrFun (e.apply_symm_apply (fun s => (y s).1)) s)
          (congrFun (e.apply_symm_apply (fun s => (y s).2)) s) }

theorem splitResiduePairEquivPi_apply (S : Finset (SplitPrime d b))
    (x : ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S)) (s : {s // s ∈ S}) :
    splitResiduePairEquivPi S x s = ((x.1.val : ZMod s.1.1), (x.2.val : ZMod s.1.1)) := by
  apply Prod.ext <;> exact splitResidueEquivPi_apply S _ s

def AffineAllowedResiduePairs (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) :=
  {x : ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S) // ∀ s : {s // s ∈ S},
    (c.re : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).1 +
      ((c.im : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).2) * s.1.root ≠ 0 ∧
    (c.re : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).1 +
      ((c.im : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).2) *
        ((b : ZMod s.1.1) - s.1.root) ≠ 0}

noncomputable def affineAllowedResiduePairsEquivPi (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) :
    AffineAllowedResiduePairs S c μ ≃
      (∀ s : {s // s ∈ S}, AffineAllowedPairs s.1.root ((b : ZMod s.1.1) - s.1.root)
        (c.re : ZMod s.1.1) (c.im : ZMod s.1.1) (μ : ZMod s.1.1)) := by
  let e := splitResiduePairEquivPi S
  exact
    { toFun x s := ⟨e x.1 s, x.2 s⟩
      invFun y := ⟨e.symm (fun s => (y s).1), by
        intro s
        simpa only [e, Equiv.apply_symm_apply] using (y s).2⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x.1)
      right_inv y := by
        funext s
        exact Subtype.ext (congrFun (e.apply_symm_apply (fun s => (y s).1)) s) }

theorem natCard_affineAllowedResiduePairs (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) (hμ : ∀ s ∈ S, (μ : ZMod s.1) ≠ 0) :
    Nat.card (AffineAllowedResiduePairs S c μ) = ∏ s ∈ S, (s.1 - 1) ^ 2 := by
  rw [Nat.card_congr (affineAllowedResiduePairsEquivPi S c μ), Nat.card_pi]
  have hlocal (s : {s // s ∈ S}) : Nat.card
      (AffineAllowedPairs s.1.root ((b : ZMod s.1.1) - s.1.root)
        (c.re : ZMod s.1.1) (c.im : ZMod s.1.1) (μ : ZMod s.1.1)) = (s.1.1 - 1) ^ 2 :=
    natCard_affineAllowedPairs _ _ _ _ _
      (quadratic_roots_distinct _ _ _ s.1.root_sq s.1.discr_ne_zero) (hμ s.1 s.2)
  simp_rw [hlocal]
  simpa only [Finset.attach_eq_univ] using S.prod_attach (fun s => (s.1 - 1) ^ 2)

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticNormBalls.lean` -/

section
/-!
# Uniform lattice-point bounds and finiteness of units

Completing the square sends each norm ball injectively into an integral
square of side `O(√N)`. This also handles the extra units of discriminants
`-3` and `-4` without any exceptional-case assumption.
-/

namespace Bernays

def QuadraticNormBall (d b : ℤ) (N : ℕ) :=
  {z : QuadraticAlgebra ℤ d b // z.norm.natAbs ≤ N}

theorem quadraticNormBall_sq_bounds {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {N : ℕ} (z : QuadraticNormBall d b N) :
    (2 * z.1.re + b * z.1.im) ^ 2 ≤ 4 * (N : ℤ) ∧ z.1.im ^ 2 ≤ 4 * (N : ℤ) := by
  have hn : z.1.norm ≤ (N : ℤ) := Int.le_natAbs.trans (by exact_mod_cast z.2)
  have hform := four_mul_quadraticNorm d b z.1
  have hD₁ : 1 ≤ -(b ^ 2 + 4 * d) := by omega
  have hmul := mul_le_mul_of_nonneg_right hD₁ (sq_nonneg z.1.im)
  constructor <;> nlinarith [sq_nonneg (2 * z.1.re + b * z.1.im), sq_nonneg z.1.im]

theorem quadraticNormBall_abs_bounds {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {N : ℕ} (z : QuadraticNormBall d b N) :
    |2 * z.1.re + b * z.1.im| ≤ ((4 * N).sqrt : ℤ) ∧
      |z.1.im| ≤ ((4 * N).sqrt : ℤ) := by
  have hb := quadraticNormBall_sq_bounds hD z
  have bound (a : ℤ) (ha : a ^ 2 ≤ 4 * (N : ℤ)) : |a| ≤ ((4 * N).sqrt : ℤ) := by
    have ha' : (a.natAbs : ℤ) ^ 2 ≤ 4 * N := by simpa only [Int.natCast_natAbs, sq_abs] using ha
    have hn : a.natAbs ^ 2 ≤ 4 * N := by exact_mod_cast ha'
    have hroot := Nat.le_sqrt'.mpr hn
    have hcast : (a.natAbs : ℤ) ≤ ((4 * N).sqrt : ℤ) := by exact_mod_cast hroot
    simpa only [Int.natCast_natAbs] using hcast
  exact ⟨bound _ hb.1, bound _ hb.2⟩

def quadraticNormBallEmbedding {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    QuadraticNormBall d b N ↪
      {a : ℤ // a ∈ Finset.Icc (-((4 * N).sqrt : ℤ)) ((4 * N).sqrt : ℤ)} ×
      {a : ℤ // a ∈ Finset.Icc (-((4 * N).sqrt : ℤ)) ((4 * N).sqrt : ℤ)} where
  toFun z := (⟨2 * z.1.re + b * z.1.im, Finset.mem_Icc.mpr
    (abs_le.mp (quadraticNormBall_abs_bounds hD z).1)⟩,
    ⟨z.1.im, Finset.mem_Icc.mpr (abs_le.mp (quadraticNormBall_abs_bounds hD z).2)⟩)
  inj' := by
    intro z w h
    have h₁ := congrArg (fun x => x.1.1) h
    have h₂ := congrArg (fun x => x.2.1) h
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · dsimp only at h₁ h₂
      rw [h₂] at h₁
      omega
    · exact h₂

theorem finite_quadraticNormBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    Finite (QuadraticNormBall d b N) :=
  Finite.of_injective (quadraticNormBallEmbedding hD N) (quadraticNormBallEmbedding hD N).injective

theorem natCard_quadraticNormBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    Nat.card (QuadraticNormBall d b N) ≤ 36 * (N + 1) := by
  let s := (4 * N).sqrt
  have hcard := Nat.card_le_card_of_injective (quadraticNormBallEmbedding hD N)
    (quadraticNormBallEmbedding hD N).injective
  have hinterval : Nat.card {a : ℤ // a ∈ Finset.Icc (-(s : ℤ)) (s : ℤ)} = 2 * s + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
    omega
  rw [Nat.card_prod, hinterval] at hcard
  apply hcard.trans
  have hs : s * s ≤ 4 * N := Nat.sqrt_le _
  have hsN : s ≤ 4 * N := Nat.sqrt_le_self _
  nlinarith

theorem quadraticNorm_unit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (u : (QuadraticAlgebra ℤ d b)ˣ) : (u : QuadraticAlgebra ℤ d b).norm = 1 := by
  have hu := u.isUnit.map (QuadraticAlgebra.norm : QuadraticAlgebra ℤ d b →* ℤ)
  have hn := quadraticNorm_nonneg hD (u : QuadraticAlgebra ℤ d b)
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · omega

theorem finite_quadraticOrder_units {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Finite (QuadraticAlgebra ℤ d b)ˣ := by
  letI := finite_quadraticNormBall hD 1
  let f : (QuadraticAlgebra ℤ d b)ˣ → QuadraticNormBall d b 1 := fun u =>
    ⟨u, by rw [quadraticNorm_unit hD, Int.natAbs_one]⟩
  apply Finite.of_injective f
  intro u v h
  apply Units.ext
  exact congrArg Subtype.val h

end Bernays

end

/-! ### Upstream module `Util/Bernays/AffineLatticeBox.lean` -/

section
/-!
# Integral affine boxes with prescribed residue classes
-/

namespace Bernays

theorem quadraticNorm_natAbs_le {d b : ℤ} (z : QuadraticAlgebra ℤ d b) {R : ℕ}
    (hr : z.re.natAbs ≤ R) (hi : z.im.natAbs ≤ R) :
    z.norm.natAbs ≤ (1 + b.natAbs + d.natAbs) * R ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  calc
    _ ≤ (z.re * z.re + b * z.re * z.im).natAbs + (d * z.im * z.im).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ (z.re * z.re).natAbs + (b * z.re * z.im).natAbs + (d * z.im * z.im).natAbs :=
      Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = z.re.natAbs ^ 2 + b.natAbs * z.re.natAbs * z.im.natAbs + d.natAbs * z.im.natAbs ^ 2 := by
      simp only [Int.natAbs_mul]
      ring
    _ ≤ R ^ 2 + b.natAbs * R * R + d.natAbs * R ^ 2 := by gcongr
    _ = _ := by ring

theorem residueGrid_injective {Q : ℕ} (hQ : 0 < Q) {r s : ZMod Q} {i j : ℕ}
    (h : r.val + Q * i = s.val + Q * j) : r = s ∧ i = j := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hm := congrArg (fun n : ℕ => n % Q) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt r),
    Nat.mod_eq_of_lt (ZMod.val_lt s)] at hm
  have hrs : r = s := ZMod.val_injective Q hm
  refine ⟨hrs, ?_⟩
  rw [hm] at h
  exact Nat.mul_left_cancel hQ (Nat.add_left_cancel h)

def affineBoxPoint {d b : ℤ} (c : QuadraticAlgebra ℤ d b) (μ Q L : ℕ)
    (r : ZMod Q × ZMod Q) (i j : Fin L) : QuadraticAlgebra ℤ d b :=
  ⟨c.re + (μ : ℤ) * (r.1.val + Q * (L + i.val)),
    c.im + (μ : ℤ) * (r.2.val + Q * j.val)⟩

theorem affineBoxPoint_injective {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) :
    Function.Injective (fun x : (ZMod Q × ZMod Q) × Fin L × Fin L =>
      affineBoxPoint c μ Q L x.1 x.2.1 x.2.2) := by
  intro x y h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  have hμZ : (μ : ℤ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hx : x.1.1.val + Q * (L + x.2.1.val) = y.1.1.val + Q * (L + y.2.1.val) := by
    exact_mod_cast (mul_left_cancel₀ hμZ (add_left_cancel hre))
  have hy : x.1.2.val + Q * x.2.2.val = y.1.2.val + Q * y.2.2.val := by
    exact_mod_cast (mul_left_cancel₀ hμZ (add_left_cancel him))
  obtain ⟨hr₁, hi⟩ := residueGrid_injective hQ hx
  obtain ⟨hr₂, hj⟩ := residueGrid_injective hQ hy
  exact Prod.ext (Prod.ext hr₁ hr₂) (Prod.ext (Fin.ext (Nat.add_left_cancel hi)) (Fin.ext hj))

theorem affineBoxPoint_re_pos {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) (hL : c.re.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    0 < (affineBoxPoint c μ Q L r i j).re := by
  have hlow : L ≤ μ * (r.1.val + Q * (L + i.val)) := by
    calc
      L ≤ L + i.val := Nat.le_add_right _ _
      _ ≤ Q * (L + i.val) := Nat.le_mul_of_pos_left _ hQ
      _ ≤ r.1.val + Q * (L + i.val) := Nat.le_add_left _ _
      _ ≤ μ * (r.1.val + Q * (L + i.val)) := Nat.le_mul_of_pos_left _ hμ
  have hlowZ : (L : ℤ) ≤ (μ : ℤ) * (r.1.val + Q * (L + i.val)) := by exact_mod_cast hlow
  have hLZ : (c.re.natAbs : ℤ) < L := by exact_mod_cast hL
  have hbase : -(c.re.natAbs : ℤ) ≤ c.re := by simp only [Int.natCast_natAbs]; exact neg_abs_le _
  change 0 < c.re + (μ : ℤ) * (r.1.val + Q * (L + i.val))
  omega

theorem affineBoxPoint_ne_zero {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) (hL : c.re.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) : affineBoxPoint c μ Q L r i j ≠ 0 := by
  intro h
  have hp := affineBoxPoint_re_pos c hμ hQ hL r i j
  rw [h, QuadraticAlgebra.re_zero] at hp
  exact (lt_irrefl 0) hp

theorem affineBoxPoint_norm_le {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hQ : 0 < Q) (hrL : c.re.natAbs < L) (hiL : c.im.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    (affineBoxPoint c μ Q L r i j).norm.natAbs ≤
      (1 + b.natAbs + d.natAbs) * (2 * μ + 1) ^ 2 * Q ^ 2 * L ^ 2 := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hr₁ := ZMod.val_lt r.1
  have hr₂ := ZMod.val_lt r.2
  have hi := i.isLt
  have hj := j.isLt
  have hx : r.1.val + Q * (L + i.val) ≤ 2 * Q * L := by nlinarith
  have hy : r.2.val + Q * j.val ≤ 2 * Q * L := by nlinarith
  have hLQ : L ≤ Q * L := Nat.le_mul_of_pos_left _ hQ
  have bound (a : ℤ) (n : ℕ) (ha : a.natAbs < L) (hn : n ≤ 2 * Q * L) :
      (a + (μ : ℤ) * n).natAbs ≤ (2 * μ + 1) * Q * L := by
    have h := Int.natAbs_add_le a (((μ * n : ℕ) : ℤ))
    have hab : (a + (μ : ℤ) * n).natAbs ≤ a.natAbs + μ * n := by
      simpa only [Nat.cast_mul, Int.natAbs_mul, Int.natAbs_natCast] using h
    have hm := Nat.mul_le_mul_left μ hn
    nlinarith
  have hre : (affineBoxPoint c μ Q L r i j).re.natAbs ≤ (2 * μ + 1) * Q * L := by
    simpa only [affineBoxPoint, Nat.cast_add, Nat.cast_mul] using bound c.re _ hrL hx
  have him : (affineBoxPoint c μ Q L r i j).im.natAbs ≤ (2 * μ + 1) * Q * L := by
    simpa only [affineBoxPoint, Nat.cast_add, Nat.cast_mul] using bound c.im _ hiL hy
  calc
    _ ≤ (1 + b.natAbs + d.natAbs) * ((2 * μ + 1) * Q * L) ^ 2 :=
      quadraticNorm_natAbs_le _ hre him
    _ = _ := by ring

theorem affineBoxPoint_sub_base {d b : ℤ} (c : QuadraticAlgebra ℤ d b) (μ Q L : ℕ)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    affineBoxPoint c μ Q L r i j - c =
      (μ : QuadraticAlgebra ℤ d b) *
        ⟨(r.1.val + Q * (L + i.val) : ℕ), (r.2.val + Q * j.val : ℕ)⟩ := by
  ext <;> simp [affineBoxPoint, sub_eq_add_neg] <;> ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/SieveLatticePoints.lean` -/

section
/-!
# The residue-constrained lattice points avoid both primes above each selected prime
-/

namespace Bernays

theorem quadraticEval_affineBoxPoint {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    (μ Q L q : ℕ) (r : ZMod Q × ZMod Q) (i j : Fin L)
    (s : ZMod q) (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hq : q ∣ Q) :
    quadraticEval d b q s hs (affineBoxPoint c μ Q L r i j) =
      (c.re : ZMod q) + (μ : ZMod q) * (r.1.val : ZMod q) +
        ((c.im : ZMod q) + (μ : ZMod q) * (r.2.val : ZMod q)) * s := by
  have hQ : (Q : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff Q q).mpr hq
  simp [quadraticEval, affineBoxPoint, hQ]

theorem affineBoxPoint_not_mem_splitPrime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (S : Finset (SplitPrime d b)) (c : QuadraticAlgebra ℤ d b) (μ L : ℕ)
    (r : AffineAllowedResiduePairs S c (μ : ℤ)) (i j : Fin L) (s : {s // s ∈ S}) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    affineBoxPoint c μ (splitSieveModulus S) L r.1 i j ∉
      (s.1.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  have hdiv : s.1.1 ∣ splitSieveModulus S := Finset.dvd_prod_of_mem (fun s => s.1) s.2
  change quadraticEval d b s.1.1 (s.1.orientedRoot ε) (s.1.orientedRoot_sq ε)
    (affineBoxPoint c μ (splitSieveModulus S) L r.1 i j) ≠ 0
  rw [quadraticEval_affineBoxPoint _ _ _ _ _ _ _ _ _ _ hdiv]
  cases ε
  · simpa only [SplitPrime.orientedRoot, Bool.false_eq_true, if_false,
      splitResiduePairEquivPi_apply, Int.cast_natCast] using (r.2 s).1
  · simpa only [SplitPrime.orientedRoot, if_true,
      splitResiduePairEquivPi_apply, Int.cast_natCast] using (r.2 s).2

theorem factor_isCoprime_of_generator_not_mem {R : Type*} [CommRing R]
    (I J P : Ideal R) (hP : P.IsMaximal) {x : R}
    (hIJ : I * J = Ideal.span {x}) (hx : x ∉ P) : IsCoprime J P := by
  have hJnot : ¬ J ≤ P := by
    intro h
    apply hx
    have hmem : x ∈ I * J := by rw [hIJ]; exact Ideal.mem_span_singleton_self x
    exact h (Ideal.mul_le_right hmem)
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  exact hJnot (le_sup_left.trans_eq (hP.eq_of_le htop le_sup_right).symm)

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticClassBalls.lean` -/

section
/-!
# Linear upper bounds for ideals in each quadratic ideal class
-/

open scoped nonZeroDivisors

namespace Bernays

def IdealClassBall (R : Type*) [CommRing R] [IsDomain R] (C : ClassGroup R) (N : ℕ) :=
  {I : InvertibleIdeal R // I.idealClass = C ∧ (I : Ideal R).cardQuot ≤ N}

theorem natCard_idealClassBall_zero {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (C : ClassGroup R) : Nat.card (IdealClassBall R C 0) = 0 := by
  haveI : IsEmpty (IdealClassBall R C 0) := ⟨fun I => (not_le_of_gt I.1.cardQuot_pos) I.2.2⟩
  simp

theorem exists_principal_generator_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I J : InvertibleIdeal (QuadraticAlgebra ℤ d b), I.idealClass * J.idealClass = 1 →
      ∃ z : QuadraticAlgebra ℤ d b, ∃ hz : z ≠ 0, I * J = InvertibleIdeal.principal z hz ∧
        z.norm.natAbs = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot *
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro I J hc
  have hclass : (I * J).idealClass = 1 := by rwa [InvertibleIdeal.idealClass_mul]
  obtain ⟨z, hz, heq⟩ := (InvertibleIdeal.idealClass_eq_one_iff (I * J)).mp hclass
  refine ⟨z, hz, heq, ?_⟩
  have hnorm := InvertibleIdeal.cardQuot_mul I J
  rw [heq, InvertibleIdeal.coe_principal,
    Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at hnorm
  exact hnorm

theorem exists_classBall_embedding_normBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ m : ℕ, 0 < m ∧
      ∀ N : ℕ, Nonempty (IdealClassBall (QuadraticAlgebra ℤ d b) C N ↪ QuadraticNormBall d b (m * N)) := by
  letI := quadraticOrderIsDomain hD
  intro C
  obtain ⟨J, hJ⟩ := InvertibleIdeal.idealClass_surjective C⁻¹
  let m := (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot
  refine ⟨m, J.cardQuot_pos, ?_⟩
  intro N
  let B := IdealClassBall (QuadraticAlgebra ℤ d b) C N
  have hex (I : B) : ∃ z : QuadraticAlgebra ℤ d b, ∃ hz : z ≠ 0,
      J * I.1 = InvertibleIdeal.principal z hz ∧ z.norm.natAbs ≤ m * N := by
    have hc : J.idealClass * I.1.idealClass = 1 := by rw [hJ, I.2.1, inv_mul_cancel]
    obtain ⟨z, hz, heq, hnorm⟩ := exists_principal_generator_norm hD J I.1 hc
    exact ⟨z, hz, heq, hnorm ▸ Nat.mul_le_mul_left m I.2.2⟩
  let z : B → QuadraticAlgebra ℤ d b := fun I => (hex I).choose
  have hz (I : B) : z I ≠ 0 := (hex I).choose_spec.choose
  have heq (I : B) : J * I.1 = InvertibleIdeal.principal (z I) (hz I) :=
    (hex I).choose_spec.choose_spec.1
  have hbound (I : B) : (z I).norm.natAbs ≤ m * N := (hex I).choose_spec.choose_spec.2
  refine ⟨⟨fun I => ⟨z I, hbound I⟩, ?_⟩⟩
  intro I K h
  have hzero : z I = z K := congrArg Subtype.val h
  have hprod : J * I.1 = J * K.1 := by
    rw [heq I, heq K]
    apply InvertibleIdeal.ext
    simp only [InvertibleIdeal.coe_principal, hzero]
  apply Subtype.ext
  exact InvertibleIdeal.mul_right_cancel I.1 K.1 J (by simpa only [mul_comm] using hprod)

theorem finite_idealClassBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      Finite (IdealClassBall (QuadraticAlgebra ℤ d b) C N) := by
  letI := quadraticOrderIsDomain hD
  intro C N
  obtain ⟨m, _, hm⟩ := exists_classBall_embedding_normBall hD C
  letI := finite_quadraticNormBall hD (m * N)
  obtain ⟨e⟩ := hm N
  exact Finite.of_injective e e.injective

theorem exists_natCard_idealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ B : ℕ, 0 < B ∧ ∀ N : ℕ, 0 < N →
      Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N := by
  letI := quadraticOrderIsDomain hD
  intro C
  obtain ⟨m, _, hm⟩ := exists_classBall_embedding_normBall hD C
  refine ⟨36 * (m + 1), by positivity, ?_⟩
  intro N hN
  letI := finite_quadraticNormBall hD (m * N)
  obtain ⟨e⟩ := hm N
  have hcard := (Nat.card_le_card_of_injective e e.injective).trans (natCard_quadraticNormBall_le hD (m * N))
  exact hcard.trans (by nlinarith)

theorem exists_uniform_natCard_idealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ B : ℕ, 0 < B ∧ ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
      Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N := by
  classical
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  choose B hBpos hB using exists_natCard_idealClassBall_le hD
  refine ⟨∑ C, B C, ?_, ?_⟩
  · exact (hBpos 1).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 1))
  · intro C N
    by_cases hN : N = 0
    · simp [hN, natCard_idealClassBall_zero]
    · exact (hB C N (Nat.pos_of_ne_zero hN)).trans (Nat.mul_le_mul_right N
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)))

end Bernays

end

/-! ### Upstream module `Util/Bernays/AssociateFibers.lean` -/

section
/-!
# Counting a finite family modulo associates
-/

namespace Bernays

theorem natCard_associate_fiber_le {R X Y : Type*} [CommMonoid R] [Finite Rˣ]
    (z : X → R) (hz : Function.Injective z) (f : X → Y)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y)) (y : Y) :
    Nat.card {x : X // f x = y} ≤ Nat.card Rˣ := by
  classical
  by_cases hne : Nonempty {x : X // f x = y}
  · obtain ⟨x₀⟩ := hne
    have hex (x : {x : X // f x = y}) : ∃ u : Rˣ, z x.1 * u = z x₀.1 :=
      hassoc x.1 x₀.1 (x.2.trans x₀.2.symm)
    let u : {x : X // f x = y} → Rˣ := fun x => (hex x).choose
    have hu (x : {x : X // f x = y}) : z x.1 * u x = z x₀.1 := (hex x).choose_spec
    apply Nat.card_le_card_of_injective u
    intro x w h
    apply Subtype.ext
    apply hz
    apply (u x).isUnit.mul_right_cancel
    rw [hu x, h, hu w]
  · haveI : IsEmpty {x : X // f x = y} := not_nonempty_iff.mp hne
    simp

theorem natCard_le_units_mul_of_associate_fibers {R X Y : Type*}
    [CommMonoid R] [Finite Rˣ] [Finite X] [Finite Y]
    (z : X → R) (hz : Function.Injective z) (f : X → Y)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y)) :
    Nat.card X ≤ Nat.card Rˣ * Nat.card Y := by
  classical
  letI := Fintype.ofFinite Y
  calc
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    _ ≤ ∑ _y : Y, Nat.card Rˣ := Finset.sum_le_sum fun y _ => natCard_associate_fiber_le z hz f hassoc y
    _ = Nat.card Rˣ * Nat.card Y := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem natCard_associate_fiber_eq {R X Y : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [Finite Rˣ] [Finite X]
    (z : X → R) (hz : Function.Injective z) (hz₀ : ∀ x, z x ≠ 0)
    (f : X → Y) (hassoc : ∀ x y, f x = f y → Associated (z x) (z y))
    (hstable : ∀ x : X, ∀ u : Rˣ, ∃ w : X, z w = z x * u ∧ f w = f x)
    (y : Y) (hy : ∃ x, f x = y) : Nat.card {x : X // f x = y} = Nat.card Rˣ := by
  classical
  apply Nat.le_antisymm (natCard_associate_fiber_le z hz f hassoc y)
  obtain ⟨x₀, hx₀⟩ := hy
  let w : Rˣ → X := fun u => (hstable x₀ u).choose
  have hw (u : Rˣ) : z (w u) = z x₀ * u ∧ f (w u) = f x₀ := (hstable x₀ u).choose_spec
  let e : Rˣ → {x : X // f x = y} := fun u => ⟨w u, (hw u).2.trans hx₀⟩
  apply Nat.card_le_card_of_injective e
  intro u v huv
  apply Units.ext
  have heq : z (w u) = z (w v) := congrArg (fun t : {x : X // f x = y} => z t.1) huv
  rw [(hw u).1, (hw v).1] at heq
  exact mul_left_cancel₀ (hz₀ x₀) heq

theorem natCard_eq_units_mul_of_associate_fibers {R X Y : Type*}
    [CommMonoidWithZero R] [IsCancelMulZero R] [Finite Rˣ] [Finite X] [Finite Y]
    (z : X → R) (hz : Function.Injective z) (hz₀ : ∀ x, z x ≠ 0)
    (f : X → Y) (hf : Function.Surjective f)
    (hassoc : ∀ x y, f x = f y → Associated (z x) (z y))
    (hstable : ∀ x : X, ∀ u : Rˣ, ∃ w : X, z w = z x * u ∧ f w = f x) :
    Nat.card X = Nat.card Rˣ * Nat.card Y := by
  classical
  letI := Fintype.ofFinite Y
  calc
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    _ = ∑ _y : Y, Nat.card Rˣ := Finset.sum_congr rfl fun y _ =>
      natCard_associate_fiber_eq z hz hz₀ f hassoc hstable y (hf y)
    _ = Nat.card Rˣ * Nat.card Y := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

end Bernays

end

/-! ### Upstream module `Util/Bernays/LatticeClassCounting.lean` -/

section
/-!
# Passing from a family of lattice points to distinct integral ideals
-/

namespace Bernays

def RestrictedIdealClassBall (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (N : ℕ) (A : InvertibleIdeal R → Prop) :=
  {I : IdealClassBall R C N // A I.1}

theorem lattice_family_class_count {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {X : Type*} [Finite X] :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
      (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop)
      (z : X → QuadraticAlgebra ℤ d b),
      Function.Injective z →
      (∀ x, z x ≠ 0) →
      (∀ x, z x ∈ (I : Ideal (QuadraticAlgebra ℤ d b))) →
      (∀ x, (z x).norm.natAbs ≤ N) →
      (∀ x, ∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)) * J = Ideal.span {z x} → A J) →
      Nat.card X ≤ Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N A) := by
  letI := quadraticOrderIsDomain hD
  intro I N A z hinj hz₀ hzI hzN hA
  let O := QuadraticAlgebra ℤ d b
  let Y := RestrictedIdealClassBall O I.idealClass⁻¹ N A
  have hex (x : X) : ∃ J : InvertibleIdeal O, I * J = InvertibleIdeal.principal (z x) (hz₀ x) :=
    InvertibleIdeal.exists_mul_eq_of_le I (InvertibleIdeal.principal (z x) (hz₀ x))
      ((Ideal.span_singleton_le_iff_mem _).mpr (hzI x))
  let J : X → InvertibleIdeal O := fun x => (hex x).choose
  have hJ (x : X) : I * J x = InvertibleIdeal.principal (z x) (hz₀ x) := (hex x).choose_spec
  have hJideal (x : X) : (I : Ideal O) * (J x : Ideal O) = Ideal.span {z x} :=
    congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) (hJ x)
  have hclass (x : X) : (J x).idealClass = I.idealClass⁻¹ := by
    have hc := congrArg InvertibleIdeal.idealClass (hJ x)
    rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at hc
    calc
      _ = I.idealClass⁻¹ * (I.idealClass * (J x).idealClass) := by simp
      _ = _ := by rw [hc, mul_one]
  have hnorm (x : X) : (J x : Ideal O).cardQuot ≤ N := by
    have hm := InvertibleIdeal.cardQuot_mul I (J x)
    rw [hJ x, InvertibleIdeal.coe_principal,
      Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at hm
    calc
      (J x : Ideal O).cardQuot ≤ (I : Ideal O).cardQuot * (J x : Ideal O).cardQuot :=
        Nat.le_mul_of_pos_left _ I.cardQuot_pos
      _ = (z x).norm.natAbs := hm.symm
      _ ≤ N := hzN x
  let f : X → Y := fun x => ⟨⟨J x, hclass x, hnorm x⟩, hA x (J x) (hJideal x)⟩
  have hassoc (x y : X) (h : f x = f y) : Associated (z x) (z y) := by
    have heq : J x = J y := congrArg (fun t : Y => t.1.1) h
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← hJideal x, ← hJideal y, heq]
  letI := finite_quadraticOrder_units hD
  letI := finite_idealClassBall hD I.idealClass⁻¹ N
  letI : Finite Y := by
    dsimp only [Y, RestrictedIdealClassBall]
    infer_instance
  exact natCard_le_units_mul_of_associate_fibers z hinj f hassoc

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealGenerators.lean` -/

section
/-!
# Generators modulo a finite modulus and coprime class representatives
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

theorem mul_left_cancel_ideal (I : InvertibleIdeal R) {J K : Ideal R}
    (h : (I : Ideal R) * J = (I : Ideal R) * K) : J = K := by
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing R)
  apply I.2.mul_left_cancel
  simpa only [FractionalIdeal.coeIdeal_mul] using
    congrArg (fun A : Ideal R => (A : FractionalIdeal R⁰ (FractionRing R))) h

theorem exists_generator_mod_mul (I : InvertibleIdeal R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ x : (I : Ideal R), (x : R) ≠ 0 ∧
      (I : Ideal R) = Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) := by
  classical
  by_cases htop : F = ⊤
  · obtain ⟨x, hx, hx₀⟩ := (I : Ideal R).ne_bot_iff.mp I.ne_bot
    refine ⟨⟨x, hx⟩, hx₀, ?_⟩
    rw [htop, Ideal.top_mul]
    exact (sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)).symm
  let A := R ⧸ F
  let M := (I : Ideal R)
  let T := TensorProduct R A M
  letI : Nontrivial A := (Ideal.Quotient.nontrivial_iff (R := R) (I := F)).mpr htop
  letI : Finite A := Ring.HasFiniteQuotients.finiteQuotient hF
  letI : IsArtinianRing A := isArtinian_of_finite
  letI : Module.Invertible R M := Erdos1081.moduleInvertibleIdealOfIsUnit (I : Ideal R) I.2
  letI : Module.Invertible A T := inferInstance
  letI : Module.Free A T := inferInstance
  let e : T ≃ₗ[A] A := (Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free A T)).some
  obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R M A Ideal.Quotient.mk_surjective (e.symm 1)
  have hx₀ : (x : R) ≠ 0 := by
    intro hzero
    have hz : x = 0 := Subtype.ext hzero
    have he : e.symm 1 = 0 := by simpa [hz] using hx.symm
    have hone : (1 : A) = 0 := by rw [← e.apply_symm_apply 1, he, map_zero]
    exact one_ne_zero hone
  refine ⟨x, hx₀, le_antisymm ?_ ?_⟩
  · intro y hy
    let ys : M := ⟨y, hy⟩
    let a : A := e (TensorProduct.mk R A M 1 ys)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
    let v : M := ys - r • x
    have hvzero : TensorProduct.mk R A M 1 v = 0 := by
      dsimp only [v]
      rw [map_sub, map_smul, hx]
      apply e.injective
      rw [map_sub, map_zero]
      change a - e (r • e.symm 1) = 0
      rw [← IsScalarTower.algebraMap_smul A r (e.symm 1), map_smul, e.apply_symm_apply,
        smul_eq_mul, mul_one]
      change a - algebraMap R A r = 0
      rw [← hr]
      simp [A, Ideal.Quotient.algebraMap_eq]
    have hvker : v ∈ LinearMap.ker (TensorProduct.mk R A M 1) := LinearMap.mem_ker.mpr hvzero
    rw [LinearMap.ker_tensorProductMk] at hvker
    have hvprod : (v : R) ∈ F * (I : Ideal R) := by
      rw [← Ideal.smul_eq_mul]
      exact Submodule.smul_induction_on hvker
        (fun r hrF w _ => by
          change r * (w : R) ∈ F • (I : Ideal R)
          rw [Ideal.smul_eq_mul]
          exact Ideal.mul_mem_mul hrF w.2)
        (fun _ _ ha hb => add_mem ha hb)
    have hspan : r * (x : R) ∈ Ideal.span ({(x : R)} : Set R) :=
      (Ideal.span ({(x : R)} : Set R)).mul_mem_left r (Ideal.mem_span_singleton_self _)
    have hadd := (Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R)).add_mem
      ((show Ideal.span ({(x : R)} : Set R) ≤
        Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) from le_sup_left) hspan)
      ((show F * (I : Ideal R) ≤
        Ideal.span ({(x : R)} : Set R) + F * (I : Ideal R) from le_sup_right) hvprod)
    have hvval : (v : R) = y - r * (x : R) := rfl
    simpa [hvval, add_comm] using hadd
  · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr x.2) Ideal.mul_le_right

theorem exists_coprime_inverse (I : InvertibleIdeal R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ J : InvertibleIdeal R, J.idealClass = I.idealClass⁻¹ ∧ IsCoprime (J : Ideal R) F := by
  obtain ⟨x, hx₀, hgen⟩ := exists_generator_mod_mul I F hF
  obtain ⟨J, hIJ⟩ := exists_mul_eq_of_le I (principal (x : R) hx₀)
    ((Ideal.span_singleton_le_iff_mem _).mpr x.2)
  have hc : I.idealClass * J.idealClass = 1 := by
    have h := congrArg idealClass hIJ
    simpa only [idealClass_mul, idealClass_principal] using h
  refine ⟨J, ?_, ?_⟩
  · calc
      J.idealClass = I.idealClass⁻¹ * (I.idealClass * J.idealClass) := by simp
      _ = I.idealClass⁻¹ := by rw [hc, mul_one]
  · have hspan : (I : Ideal R) * (J : Ideal R) = Ideal.span {(x : R)} :=
      congrArg (fun K : InvertibleIdeal R => (K : Ideal R)) hIJ
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply mul_left_cancel_ideal I
    change (I : Ideal R) * ((J : Ideal R) + F) = (I : Ideal R) * ⊤
    rw [mul_add, hspan, mul_comm (I : Ideal R) F, ← hgen, Ideal.mul_top]

theorem exists_coprime_representative (C : ClassGroup R) (F : Ideal R) (hF : F ≠ ⊥) :
    ∃ I : InvertibleIdeal R, I.idealClass = C ∧ IsCoprime (I : Ideal R) F := by
  obtain ⟨J, hJ⟩ := idealClass_surjective C⁻¹
  obtain ⟨I, hI, hc⟩ := exists_coprime_inverse J F hF
  exact ⟨I, by simpa only [hJ, inv_inv] using hI, hc⟩

theorem generator_mod_of_sub_mem (I : InvertibleIdeal R) (F : Ideal R) (c : (I : Ideal R))
    (hc : (I : Ideal R) = Ideal.span ({(c : R)} : Set R) + F * (I : Ideal R))
    {x : R} (hx : x - (c : R) ∈ F * (I : Ideal R)) :
    (I : Ideal R) = Ideal.span ({x} : Set R) + F * (I : Ideal R) := by
  have hxI : x ∈ (I : Ideal R) := by
    have h := (I : Ideal R).add_mem (Ideal.mul_le_right hx) c.2
    simpa only [sub_add_cancel] using h
  apply le_antisymm
  · calc
      (I : Ideal R) = Ideal.span ({(c : R)} : Set R) + F * (I : Ideal R) := hc
      _ ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R) := by
        apply sup_le ?_ le_sup_right
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        change (c : R) ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R)
        have h₁ : x ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R) :=
          (show Ideal.span ({x} : Set R) ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R)
            from le_sup_left) (Ideal.mem_span_singleton_self x)
        have h₂ : x - (c : R) ∈ Ideal.span ({x} : Set R) + F * (I : Ideal R) :=
          (show F * (I : Ideal R) ≤ Ideal.span ({x} : Set R) + F * (I : Ideal R)
            from le_sup_right) hx
        simpa only [sub_sub_cancel] using (Ideal.span ({x} : Set R) + F * (I : Ideal R)).sub_mem h₁ h₂
  · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxI) Ideal.mul_le_right

theorem factor_coprime_of_generator_mod (I J : InvertibleIdeal R) (F : Ideal R)
    {x : R} (hx : x ≠ 0) (hIJ : I * J = principal x hx)
    (hgen : (I : Ideal R) = Ideal.span ({x} : Set R) + F * (I : Ideal R)) :
    IsCoprime (J : Ideal R) F := by
  have hspan : (I : Ideal R) * (J : Ideal R) = Ideal.span {x} :=
    congrArg (fun K : InvertibleIdeal R => (K : Ideal R)) hIJ
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply mul_left_cancel_ideal I
  change (I : Ideal R) * ((J : Ideal R) + F) = (I : Ideal R) * ⊤
  rw [mul_add, hspan, mul_comm (I : Ideal R) F, ← hgen, Ideal.mul_top]

end Bernays.InvertibleIdeal

end

/-! ### Upstream module `Util/Bernays/ClassSieveLower.lean` -/

section
/-!
# A uniform lower sieve bound in every quadratic ideal class
-/

namespace Bernays

def ClassSievePredicate {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (M : ℕ) (S : Finset (SplitPrime d b)) (J : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Prop :=
  IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) (Ideal.span {(M : QuadraticAlgebra ℤ d b)}) ∧
    ∀ s ∈ S, ∀ ε : Bool, IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b))
      (rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε))

def ClassSieveBall {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ) (S : Finset (SplitPrime d b)) :=
  RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N (ClassSievePredicate M S)

noncomputable def classSieveMultiplier {R : Type*} [CommRing R] [IsDomain R] (I : InvertibleIdeal R) (M : ℕ) : ℕ :=
  M * (I : Ideal R).cardQuot

def classSieveScale (d b : ℤ) (μ : ℕ) : ℕ :=
  (1 + b.natAbs + d.natAbs) * (2 * μ + 1) ^ 2

theorem affineBoxPoint_sub_mem_ideal {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (M Q L : ℕ)
    (c : (I : Ideal (QuadraticAlgebra ℤ d b))) (r : ZMod Q × ZMod Q) (i j : Fin L) :
    affineBoxPoint (c : QuadraticAlgebra ℤ d b) (classSieveMultiplier I M) Q L r i j - c ∈
      Ideal.span {(M : QuadraticAlgebra ℤ d b)} * (I : Ideal (QuadraticAlgebra ℤ d b)) := by
  have hm : ((I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot : QuadraticAlgebra ℤ d b) ∈
      (I : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  rw [affineBoxPoint_sub_base, classSieveMultiplier, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
    ((I : Ideal (QuadraticAlgebra ℤ d b)).mul_mem_right _ hm)

theorem classSieve_lower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (M : ℕ), 0 < M →
      ∀ c : (I : Ideal (QuadraticAlgebra ℤ d b)),
      (I : Ideal (QuadraticAlgebra ℤ d b)) = Ideal.span {(c : QuadraticAlgebra ℤ d b)} +
        Ideal.span {(M : QuadraticAlgebra ℤ d b)} * (I : Ideal (QuadraticAlgebra ℤ d b)) →
      ∀ S : Finset (SplitPrime d b),
      (∀ s ∈ S, ¬s.1 ∣ classSieveMultiplier I M) →
      ∀ L : ℕ, (c : QuadraticAlgebra ℤ d b).re.natAbs < L →
        (c : QuadraticAlgebra ℤ d b).im.natAbs < L →
        (∏ s ∈ S, (s.1 - 1) ^ 2) * L ^ 2 ≤ Nat.card (QuadraticAlgebra ℤ d b)ˣ *
          Nat.card (ClassSieveBall I.idealClass⁻¹
            (classSieveScale d b (classSieveMultiplier I M) * (splitSieveModulus S) ^ 2 * L ^ 2) M S) := by
  letI := quadraticOrderIsDomain hD
  intro I M hM c hc S hS L hrL hiL
  let O := QuadraticAlgebra ℤ d b
  let μ := classSieveMultiplier I M
  let Q := splitSieveModulus S
  let N := classSieveScale d b μ * Q ^ 2 * L ^ 2
  have hμ : 0 < μ := Nat.mul_pos hM I.cardQuot_pos
  have hQ : 0 < Q := splitSieveModulus_pos S
  letI : NeZero Q := ⟨hQ.ne'⟩
  let X := AffineAllowedResiduePairs S (c : O) (μ : ℤ) × Fin L × Fin L
  letI : Finite X := by
    dsimp only [X, AffineAllowedResiduePairs]
    infer_instance
  let z : X → O := fun x => affineBoxPoint (c : O) μ Q L x.1.1 x.2.1 x.2.2
  have hcoord : Function.Injective (fun x : X => (x.1.1, x.2)) := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun t : (ZMod Q × ZMod Q) × (Fin L × Fin L) => t.2) h)
  have hz : Function.Injective z := (affineBoxPoint_injective (c : O) hμ hQ).comp hcoord
  have hz₀ (x : X) : z x ≠ 0 := affineBoxPoint_ne_zero (c : O) hμ hQ hrL _ _ _
  have hdiff (x : X) : z x - c ∈ Ideal.span {(M : O)} * (I : Ideal O) :=
    affineBoxPoint_sub_mem_ideal I M Q L c x.1.1 x.2.1 x.2.2
  have hzI (x : X) : z x ∈ (I : Ideal O) := by
    have h := (I : Ideal O).add_mem (Ideal.mul_le_right (hdiff x)) c.2
    simpa only [sub_add_cancel] using h
  have hzN (x : X) : (z x).norm.natAbs ≤ N :=
    affineBoxPoint_norm_le (c : O) hQ hrL hiL x.1.1 x.2.1 x.2.2
  have hA (x : X) (J : InvertibleIdeal O) (hIJ : (I : Ideal O) * J = Ideal.span {z x}) :
      ClassSievePredicate M S J := by
    constructor
    · exact InvertibleIdeal.factor_coprime_of_generator_mod I J (Ideal.span {(M : O)})
        (hz₀ x) (InvertibleIdeal.ext hIJ)
        (InvertibleIdeal.generator_mod_of_sub_mem I _ c hc (hdiff x))
    · intro s hs ε
      exact factor_isCoprime_of_generator_not_mem (I : Ideal O) (J : Ideal O)
        (s.ideal hD ε : Ideal O) (s.ideal_isMaximal hD ε) hIJ
        (affineBoxPoint_not_mem_splitPrime hD S (c : O) μ L x.1 x.2.1 x.2.2 ⟨s, hs⟩ ε)
  have hcount := lattice_family_class_count hD I N (ClassSievePredicate M S) z hz hz₀ hzI hzN hA
  have hμmod : ∀ s ∈ S, ((μ : ℤ) : ZMod s.1) ≠ 0 := by
    intro s hs
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff μ s.1).not.mpr (hS s hs)
  have hcard : Nat.card X = (∏ s ∈ S, (s.1 - 1) ^ 2) * L ^ 2 := by
    rw [show X = (AffineAllowedResiduePairs S (c : O) (μ : ℤ) × Fin L × Fin L) from rfl,
      Nat.card_prod, Nat.card_prod, Nat.card_fin, natCard_affineAllowedResiduePairs S (c : O) (μ : ℤ) hμmod]
    ring
  rw [hcard] at hcount
  exact hcount

end Bernays

end

/-! ### Upstream module `Util/Bernays/DivisibleClassBalls.lean` -/

section
/-!
# Counting ideals divisible by a specified invertible ideal
-/

namespace Bernays

def DivisibleIdealClassBall (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (N : ℕ) (P : InvertibleIdeal R) :=
  {I : IdealClassBall R C N // (I.1 : Ideal R) ≤ (P : Ideal R)}

noncomputable def divisibleClassBallEmbedding {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (C : ClassGroup R) (N : ℕ) (P : InvertibleIdeal R) :
    DivisibleIdealClassBall R C N P ↪
      IdealClassBall R (P.idealClass⁻¹ * C) (N / (P : Ideal R).cardQuot) := by
  let B := DivisibleIdealClassBall R C N P
  have hex (I : B) : ∃ J : InvertibleIdeal R, P * J = I.1.1 :=
    InvertibleIdeal.exists_mul_eq_of_le P I.1.1 I.2
  let J : B → InvertibleIdeal R := fun I => (hex I).choose
  have hmul (I : B) : P * J I = I.1.1 := (hex I).choose_spec
  have hclass (I : B) : (J I).idealClass = P.idealClass⁻¹ * C := by
    have hc := congrArg InvertibleIdeal.idealClass (hmul I)
    rw [InvertibleIdeal.idealClass_mul, I.1.2.1] at hc
    calc
      (J I).idealClass = P.idealClass⁻¹ * (P.idealClass * (J I).idealClass) := by simp
      _ = P.idealClass⁻¹ * C := by rw [hc]
  have hnorm (I : B) : (J I : Ideal R).cardQuot ≤ N / (P : Ideal R).cardQuot := by
    have h := InvertibleIdeal.cardQuot_mul P (J I)
    rw [hmul I] at h
    apply (Nat.le_div_iff_mul_le P.cardQuot_pos).mpr
    rw [Nat.mul_comm, ← h]
    exact I.1.2.2
  refine ⟨fun I => ⟨J I, hclass I, hnorm I⟩, ?_⟩
  intro I K h
  have hJ : J I = J K := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  calc
    I.1.1 = P * J I := (hmul I).symm
    _ = P * J K := congrArg (P * ·) hJ
    _ = K.1.1 := hmul K

theorem natCard_divisibleIdealClassBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ B : ℕ,
      (∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
          Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N P) ≤
            B * (N / (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot) := by
  letI := quadraticOrderIsDomain hD
  intro B hB C N P
  letI := finite_idealClassBall hD (P.idealClass⁻¹ * C)
    (N / (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot)
  exact (Nat.card_le_card_of_injective (divisibleClassBallEmbedding C N P)
    (divisibleClassBallEmbedding C N P).injective).trans (hB _ _)

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassSieveUpper.lean` -/

section
/-!
# Upper sieve bounds from prime-ideal divisors
-/

namespace Bernays

theorem natCard_classSieveBall_le_sum_divisible {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ)
      (S T : Finset (SplitPrime d b)),
      (∀ I : ClassSieveBall C N M S, ∃ s ∈ T, ∃ ε : Bool,
        (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b))) →
      Nat.card (ClassSieveBall C N M S) ≤
        ∑ s ∈ T, ∑ ε : Bool,
          Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N (s.ideal hD ε)) := by
  classical
  letI := quadraticOrderIsDomain hD
  intro C N M S T hcover
  let O := QuadraticAlgebra ℤ d b
  choose s hs ε hle using hcover
  let Y := Σ t : {s // s ∈ T}, Σ e : Bool, DivisibleIdealClassBall O C N (t.1.ideal hD e)
  let f : ClassSieveBall C N M S → Y := fun I => ⟨⟨s I, hs I⟩, ε I, ⟨I.1, hle I⟩⟩
  have hf : Function.Injective f := by
    intro I J h
    exact Subtype.ext (congrArg (fun y : Y => y.2.2.1) h)
  letI := finite_idealClassBall hD C N
  letI (t : {s // s ∈ T}) (e : Bool) :
      Finite (DivisibleIdealClassBall O C N (t.1.ideal hD e)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (ClassSieveBall C N M S) ≤ Nat.card Y := Nat.card_le_card_of_injective f hf
    _ = ∑ t : {s // s ∈ T}, ∑ e : Bool,
        Nat.card (DivisibleIdealClassBall O C N (t.1.ideal hD e)) := by
      dsimp only [Y]
      rw [Nat.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Nat.card_sigma)
    _ = _ := by
      simpa only [Finset.attach_eq_univ] using T.sum_attach
        (fun s => ∑ e : Bool, Nat.card (DivisibleIdealClassBall O C N (s.ideal hD e)))

theorem classSieve_upper_of_cover {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ B : ℕ,
      (∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N) →
      ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ) (S T : Finset (SplitPrime d b)),
      (∀ I : ClassSieveBall C N M S, ∃ s ∈ T, ∃ ε : Bool,
        (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b))) →
      (Nat.card (ClassSieveBall C N M S) : ℝ) ≤
        2 * (B : ℝ) * N * ∑ s ∈ T, (s.1 : ℝ)⁻¹ := by
  letI := quadraticOrderIsDomain hD
  intro B hB C N M S T hcover
  have hdiv (s : SplitPrime d b) (ε : Bool) :
      Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N (s.ideal hD ε)) ≤
        B * (N / s.1) := by
    simpa only [s.ideal_cardQuot hD ε] using
      natCard_divisibleIdealClassBall_le hD B hB C N (s.ideal hD ε)
  have hnat := (natCard_classSieveBall_le_sum_divisible hD C N M S T hcover).trans
    (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun ε _ => hdiv s ε)
  have hreal : (Nat.card (ClassSieveBall C N M S) : ℝ) ≤
      ∑ s ∈ T, ∑ _ : Bool, ((B * (N / s.1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hterm (s : SplitPrime d b) : ((B * (N / s.1) : ℕ) : ℝ) ≤
      (B : ℝ) * N * (s.1 : ℝ)⁻¹ := by
    rw [Nat.cast_mul, mul_assoc, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg B)
  calc
    _ ≤ ∑ s ∈ T, ∑ _ : Bool, ((B : ℝ) * N * (s.1 : ℝ)⁻¹) :=
      hreal.trans (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun _ _ => hterm s)
    _ = _ := by
      simp only [Fintype.sum_bool]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem SplitPrime.natCast_mem_ideal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.1 : QuadraticAlgebra ℤ d b) ∈ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  change quadraticEval d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε) (s.1 : _) = 0
  rw [map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl _)

theorem not_dvd_scalar_of_coprime_le {R : Type*} [CommRing R]
    (I P : Ideal R) (hP : P.IsMaximal) (M q : ℕ)
    (hc : IsCoprime I (Ideal.span {(M : R)})) (hIP : I ≤ P) (hq : (q : R) ∈ P) :
    ¬ q ∣ M := by
  rintro ⟨k, hk⟩
  have hMP : Ideal.span {(M : R)} ≤ P := by
    apply (Ideal.span_singleton_le_iff_mem P).mpr
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right _ hq
  apply hP.ne_top
  apply top_unique
  rw [← hc.sup_eq]
  exact sup_le hIP hMP

theorem coprime_scalar_of_dvd {R : Type*} [CommRing R] (I : Ideal R) {M K : ℕ}
    (h : IsCoprime I (Ideal.span {(M : R)})) (hKM : K ∣ M) :
    IsCoprime I (Ideal.span {(K : R)}) := by
  rcases hKM with ⟨k, hk⟩
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [← h.sup_eq]
  apply sup_le_sup_left
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  rw [hk, Nat.cast_mul]
  exact (Ideal.span {(K : R)}).mul_mem_right _ (Ideal.mem_span_singleton_self _)

noncomputable def boundedSplitPrimes (d b : ℤ) (N : ℕ) : Finset (SplitPrime d b) := by
  classical
  let e : {s : SplitPrime d b // s.1 ≤ N} ↪ Fin (N + 1) :=
    ⟨fun s => ⟨s.1.1, Nat.lt_succ_of_le s.2⟩, fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg Fin.val h))⟩
  letI : Finite {s : SplitPrime d b // s.1 ≤ N} := Finite.of_injective e e.injective
  letI : Fintype {s : SplitPrime d b // s.1 ≤ N} := Fintype.ofFinite _
  exact Finset.univ.image (fun s : {s : SplitPrime d b // s.1 ≤ N} => s.1)

theorem mem_boundedSplitPrimes {d b : ℤ} {N : ℕ} (s : SplitPrime d b) :
    s ∈ boundedSplitPrimes d b N ↔ s.1 ≤ N := by
  classical
  unfold boundedSplitPrimes
  simp

theorem classSieve_cover {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))
      (C : ClassGroup (QuadraticAlgebra ℤ d b)), C ∉ H →
      ∀ N M μ : ℕ, discriminantLevel (b ^ 2 + 4 * d) ∣ M →
      (∀ q : ℕ, q.Prime → q ∣ μ → q ∣ M) →
      ∀ S : Finset (SplitPrime d b), ∀ I : ClassSieveBall C N M S,
      ∃ s : SplitPrime d b, s.1 ≤ N ∧ s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S ∧
        ∃ ε : Bool, (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤
          (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  intro H C hC N M μ hDM hμ S I
  have hIF : IsCoprime (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    coprime_scalar_of_dvd _ I.2.1 hDM
  obtain ⟨s, hsH, hsn, ε, J, hIJ⟩ := exists_splitPrime_factor_outside hD H I.1.1 hIF
    (by simpa only [I.1.2.1] using hC)
  have hle : (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤
      (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← hIJ, InvertibleIdeal.coe_mul]
    exact Ideal.mul_le_left
  have hsM := not_dvd_scalar_of_coprime_le _ _ (s.ideal_isMaximal hD ε) M s.1
    I.2.1 hle (s.natCast_mem_ideal hD ε)
  refine ⟨s, hsn.trans I.1.2.2, hsH, fun h => hsM (hμ _ s.2.1 h), ?_, ε, hle⟩
  intro hsS
  have hcop := I.2.2 s hsS ε
  apply (s.ideal_isMaximal hD ε).ne_top
  exact (sup_eq_right.mpr hle).symm.trans hcop.sup_eq

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealNormMonoid.lean` -/

section
/-!
# Norm and class homomorphisms for integral invertible ideals
-/

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

noncomputable def normHom : InvertibleIdeal R →* ℕ where
  toFun I := (I : Ideal R).cardQuot
  map_one' := Submodule.cardQuot_top R R
  map_mul' := cardQuot_mul

noncomputable def classHom : InvertibleIdeal R →* ClassGroup R where
  toFun := idealClass
  map_one' := idealClass_one
  map_mul' := idealClass_mul

theorem cardQuot_prod {ι : Type*} (s : Finset ι) (I : ι → InvertibleIdeal R) :
    ((∏ i ∈ s, I i : InvertibleIdeal R) : Ideal R).cardQuot = ∏ i ∈ s, (I i : Ideal R).cardQuot :=
  map_prod (normHom (R := R)) _ _

theorem idealClass_prod {ι : Type*} (s : Finset ι) (I : ι → InvertibleIdeal R) :
    (∏ i ∈ s, I i).idealClass = ∏ i ∈ s, (I i).idealClass := map_prod classHom _ _

end Bernays.InvertibleIdeal

end

/-! ### Upstream module `Util/Bernays/QuadraticFactorData.lean` -/

section
/-!
# Norm and class data of good maximal ideals
-/

namespace Bernays

theorem quadratic_natCast_ne_zero {d b : ℤ} {q : ℕ} (hq : 0 < q) :
    (q : QuadraticAlgebra ℤ d b) ≠ 0 := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  have hz : (q : ℤ) = 0 := by simpa using hr
  exact hq.ne' (by exact_mod_cast hz)

theorem SplitPrime.rootIdeal_eq_oriented {d b : ℤ} (s : SplitPrime d b)
    (r : ZMod s.1) (hr : r ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * r) :
    ∃ ε : Bool, rootIdeal d b s.1 r hr =
      rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε) := by
  rcases s.root_eq_or_conjugate r hr with h | h
  · exact ⟨false, rootIdeal_eq_of_root_eq hr _ h⟩
  · exact ⟨true, rootIdeal_eq_of_root_eq hr _ h⟩

theorem goodMaximal_prime_description {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ q : ℕ, q.Prime ∧ q.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧
        ((discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1 ∧
          (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q ^ 2 ∧ P.idealClass = 1) ∨
        ∃ s : SplitPrime d b, s.1 = q ∧ ∃ ε : Bool, P = s.ideal hD ε) := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hqP⟩ := exists_natPrime_under_quadraticMaximal hD
    (P : Ideal (QuadraticAlgebra ℤ d b)) hP
  letI : Fact q.Prime := ⟨hq⟩
  have hmem : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    change (q : ℤ) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)).under ℤ
    rw [hqP]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime _ hP hmem hPF
  have hcop := hq.coprime_iff_not_dvd.mpr hnot
  have hqD : ¬(q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    exact hnot ((show q ∣ (b ^ 2 + 4 * d).natAbs by
      simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _))
  refine ⟨q, hq, hcop, ?_⟩
  rcases quadraticMaximal_split_or_inert d b q (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hqD with
    hprincipal | ⟨r, hr, hroot⟩
  · left
    have hnorm : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q ^ 2 := by
      rw [hprincipal, ← quadraticReduction_ker, quadraticReduction_cardQuot]
    have hclass : P.idealClass = 1 := by
      have heq : P = InvertibleIdeal.principal (q : QuadraticAlgebra ℤ d b)
          (quadratic_natCast_ne_zero hq.pos) := InvertibleIdeal.ext (by simpa using hprincipal)
      rw [heq, InvertibleIdeal.idealClass_principal]
    refine ⟨?_, hnorm, hclass⟩
    by_contra hn
    obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hcop).mpr hn
    let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    have hle : (P : Ideal (QuadraticAlgebra ℤ d b)) ≤
        (s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)) := by
      rw [hprincipal]
      exact (Ideal.span_singleton_le_iff_mem _).mpr (s.natCast_mem_ideal hD false)
    have heq := hP.eq_of_le (s.ideal_isMaximal hD false).ne_top hle
    have hqeq : q ^ 2 = q := by
      rw [← hnorm, heq]
      exact s.ideal_cardQuot hD false
    have htwo := hq.two_le
    nlinarith
  · right
    let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    obtain ⟨ε, hε⟩ := s.rootIdeal_eq_oriented r hr
    exact ⟨s, rfl, ε, InvertibleIdeal.ext (hroot.trans hε)⟩

theorem SplitPrime.idealClass_toggle {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b)
    (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD (!ε)).idealClass = ((s.ideal hD ε).idealClass)⁻¹ := by
  letI := quadraticOrderIsDomain hD
  cases ε
  · exact s.idealClass_conjugate hD
  · simpa only [Bool.not_true, s.idealClass_conjugate hD, inv_inv] using
      (show (s.ideal hD false).idealClass = s.idealClass hD from rfl)

theorem goodMaximal_inverseClass_sameNorm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ Q : InvertibleIdeal (QuadraticAlgebra ℤ d b), Q.idealClass = P.idealClass⁻¹ ∧
        (Q : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · exact ⟨P, by simp only [h.2.2, inv_one], rfl⟩
  · exact ⟨s.ideal hD (!ε), s.idealClass_toggle hD ε,
      (s.ideal_cardQuot hD (!ε)).trans (s.ideal_cardQuot hD ε).symm⟩

end Bernays

end

/-! ### Upstream module `Util/Bernays/SignedProducts.lean` -/

section
/-!
# Signed products and finite-group concentration

The finite-group argument from the ring-class proof is isolated here so that
it applies to arbitrary quadratic orders without importing the problem-level assumptions.
-/

namespace Bernays

def signedProduct {G : Type*} [CommGroup G] {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then (x i)⁻¹ else x i

def classSquareSubgroup {G : Type*} [CommGroup G] : Subgroup G :=
  (powMonoidHom 2 : G →* G).range

theorem classSquare_mem {G : Type*} [CommGroup G] (x : G) :
    x ^ 2 ∈ (classSquareSubgroup : Subgroup G) := ⟨x, rfl⟩

section SubsetProductStabilizer

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Left multiplication of a finite subset of a commutative group. -/
def leftMulFinset (a : G) (S : Finset G) : Finset G :=
  S.image fun x => a * x

@[simp] theorem leftMulFinset_one (S : Finset G) :
    leftMulFinset (1 : G) S = S := by
  ext x
  simp [leftMulFinset]

theorem leftMulFinset_mul (a b : G) (S : Finset G) :
    leftMulFinset (a * b) S = leftMulFinset a (leftMulFinset b S) := by
  ext x
  constructor
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    refine ⟨b * y, ?_, by simp [mul_assoc]⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [leftMulFinset, Finset.mem_image] at hz
    rcases hz with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, by simp [mul_assoc]⟩

theorem leftMulFinset_union (a : G) (S T : Finset G) :
    leftMulFinset a (S ∪ T) = leftMulFinset a S ∪ leftMulFinset a T := by
  ext x
  simp only [leftMulFinset, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨y, hyS | hyT, rfl⟩
    · exact Or.inl ⟨y, hyS, rfl⟩
    · exact Or.inr ⟨y, hyT, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

theorem card_leftMulFinset (a : G) (S : Finset G) :
    (leftMulFinset a S).card = S.card := by
  unfold leftMulFinset
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact mul_left_cancel hxy

theorem leftMulFinset_injective (a : G) :
    Function.Injective (leftMulFinset a : Finset G → Finset G) := by
  intro S T h
  have h' := congrArg (leftMulFinset a⁻¹) h
  simpa [← leftMulFinset_mul] using h'

/-- The subgroup of multipliers preserving a finite subset. -/
def finsetMulStabilizer (S : Finset G) : Subgroup G where
  carrier := {a | leftMulFinset a S = S}
  one_mem' := leftMulFinset_one S
  mul_mem' := by
    intro a b ha hb
    change leftMulFinset a S = S at ha
    change leftMulFinset b S = S at hb
    change leftMulFinset (a * b) S = S
    rw [leftMulFinset_mul, hb, ha]
  inv_mem' := by
    intro a ha
    change leftMulFinset a S = S at ha
    change leftMulFinset a⁻¹ S = S
    apply leftMulFinset_injective a
    rw [← leftMulFinset_mul]
    simpa [ha]

@[simp] theorem mem_finsetMulStabilizer_iff {S : Finset G} {a : G} :
    a ∈ finsetMulStabilizer S ↔ leftMulFinset a S = S := Iff.rfl

/-- Products of arbitrary sublists, built one coordinate at a time. -/
def subsetProductsList : List G → Finset G
  | [] => {1}
  | a :: l => subsetProductsList l ∪ leftMulFinset a (subsetProductsList l)

@[simp] theorem subsetProductsList_nil :
    subsetProductsList ([] : List G) = {1} := rfl

@[simp] theorem subsetProductsList_cons (a : G) (l : List G) :
    subsetProductsList (a :: l) =
      subsetProductsList l ∪ leftMulFinset a (subsetProductsList l) := rfl

theorem subsetProductsList_nonempty (l : List G) :
    (subsetProductsList l).Nonempty := by
  induction l with
  | nil => simp
  | cons a l ih => exact ih.mono Finset.subset_union_left

/-- The recursive reachable set is exactly the set of products obtained by
choosing any subset of the indexed coordinates. -/
theorem mem_subsetProductsList_ofFn_iff {k : ℕ}
    (x : Fin k → G) (z : G) :
    z ∈ subsetProductsList (List.ofFn x) ↔
      ∃ sigma : Fin k → Bool,
        z = ∏ i, if sigma i then x i else 1 := by
  induction k generalizing z with
  | zero =>
      simp [subsetProductsList]
  | succ k ih =>
      rw [List.ofFn_succ, subsetProductsList_cons, Finset.mem_union]
      constructor
      · intro hz
        rcases hz with hz | hz
        · obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) z).mp hz
          refine ⟨Fin.cons false sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simpa using hsigma
        · rw [leftMulFinset, Finset.mem_image] at hz
          rcases hz with ⟨w, hw, hwz⟩
          obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) w).mp hw
          refine ⟨Fin.cons true sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, if_true]
          rw [← hsigma]
          exact hwz.symm
      · rintro ⟨sigma, rfl⟩
        rw [Fin.prod_univ_succ]
        have htail :
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1) ∈
              subsetProductsList (List.ofFn fun i => x i.succ) := by
          apply (ih (fun i => x i.succ)
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1)).mpr
          exact ⟨fun i => sigma i.succ, rfl⟩
        cases h0 : sigma 0
        · left
          simpa [h0] using htail
        · right
          rw [leftMulFinset, Finset.mem_image]
          refine ⟨∏ i : Fin k, if sigma i.succ then x i.succ else 1, ?_, ?_⟩
          · exact htail
          · simp [h0]

/-- A multiplier stabilizing the old subset-product set continues to
stabilize it after one more coordinate is adjoined. -/
theorem stabilizer_subsetProductsList_mono (a : G) (l : List G) :
    finsetMulStabilizer (subsetProductsList l) ≤
      finsetMulStabilizer (subsetProductsList (a :: l)) := by
  intro g hg
  rw [mem_finsetMulStabilizer_iff] at hg ⊢
  rw [subsetProductsList_cons, leftMulFinset_union, hg]
  rw [← leftMulFinset_mul, mul_comm g a, leftMulFinset_mul, hg]

/-- If adding a coordinate does not enlarge the subset-product set, that
coordinate stabilizes the enlarged set. -/
theorem mem_stabilizer_of_card_subsetProductsList_cons_eq
    (a : G) (l : List G)
    (hcard : (subsetProductsList (a :: l)).card =
      (subsetProductsList l).card) :
    a ∈ finsetMulStabilizer (subsetProductsList (a :: l)) := by
  let S := subsetProductsList l
  let T := subsetProductsList (a :: l)
  have hST : S ⊆ T := by
    dsimp [S, T]
    exact Finset.subset_union_left
  have hTS : T = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hST
    simpa [S, T] using hcard.le
  rw [mem_finsetMulStabilizer_iff]
  change leftMulFinset a T = T
  rw [hTS]
  have haS : leftMulFinset a S ⊆ S := by
    intro z hz
    rw [← hTS]
    dsimp [T, S]
    exact Finset.mem_union_right _ hz
  exact Finset.eq_of_subset_of_card_le haS (by
    rw [card_leftMulFinset])

/-- Number of list coordinates outside a subgroup, with repetitions
counted. -/
noncomputable def countOutsideSubgroup (H : Subgroup G) (l : List G) : ℕ := by
  classical
  exact (l.filter fun a => decide (a ∉ H)).length

@[simp] theorem countOutsideSubgroup_nil (H : Subgroup G) :
    countOutsideSubgroup H ([] : List G) = 0 := by
  simp [countOutsideSubgroup]

theorem countOutsideSubgroup_cons_of_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∈ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l := by
  classical
  simp [countOutsideSubgroup, ha]

theorem countOutsideSubgroup_cons_of_not_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∉ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l + 1 := by
  classical
  simp [countOutsideSubgroup, ha]

/-- Relative to any subgroup containing the stabilizer of the final
subset-product set, fewer than `|R|` coordinates lie outside that subgroup,
where `R` is the final reachable set. -/
theorem length_filter_not_mem_subgroup_lt_card_subsetProductsList
    (l : List G) (H : Subgroup G)
    (hstab : finsetMulStabilizer (subsetProductsList l) ≤ H) :
    countOutsideSubgroup H l < (subsetProductsList l).card := by
  classical
  induction l generalizing H with
  | nil => simp [subsetProductsList]
  | cons a l ih =>
      have hmono := stabilizer_subsetProductsList_mono a l
      have htail : finsetMulStabilizer (subsetProductsList l) ≤ H :=
        hmono.trans hstab
      have ih' := ih H htail
      have hcardle : (subsetProductsList l).card ≤
          (subsetProductsList (a :: l)).card :=
        Finset.card_le_card Finset.subset_union_left
      by_cases ha : a ∈ H
      · rw [countOutsideSubgroup_cons_of_mem H a l ha]
        exact ih'.trans_le hcardle
      · rw [countOutsideSubgroup_cons_of_not_mem H a l ha]
        have hcardlt : (subsetProductsList l).card <
            (subsetProductsList (a :: l)).card := by
          apply lt_of_le_of_ne hcardle
          intro heq
          have hastab := mem_stabilizer_of_card_subsetProductsList_cons_eq
            a l heq.symm
          exact ha (hstab hastab)
        omega

/-- If the reachable subset products do not fill the group, then all but at
most `|G|-1` coordinates lie in one proper stabilizer subgroup. -/
theorem exists_proper_stabilizer_with_few_outside
    (l : List G) (hproper : subsetProductsList l ≠ Finset.univ) :
    ∃ H : Subgroup G, H ≠ ⊤ ∧
      countOutsideSubgroup H l < Fintype.card G := by
  let H := finsetMulStabilizer (subsetProductsList l)
  have hHproper : H ≠ ⊤ := by
    intro htop
    have htrans : ∀ g : G, leftMulFinset g (subsetProductsList l) =
        subsetProductsList l := by
      intro g
      have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact hg
    obtain ⟨z, hz⟩ := subsetProductsList_nonempty l
    have hall : ∀ g : G, g ∈ subsetProductsList l := by
      intro g
      have hgz : g ∈ leftMulFinset (g * z⁻¹)
          (subsetProductsList l) := by
        rw [leftMulFinset, Finset.mem_image]
        refine ⟨z, hz, ?_⟩
        group
      rw [htrans] at hgz
      exact hgz
    apply hproper
    ext g
    simp [hall]
  refine ⟨H, hHproper, ?_⟩
  have hbound := length_filter_not_mem_subgroup_lt_card_subsetProductsList
    l H (le_refl H)
  exact hbound.trans_le (Finset.card_le_univ _)

end SubsetProductStabilizer

section SignedProductConcentration

variable {G : Type*} [CommGroup G]

/-- Product of the coordinate squares selected by a sign pattern. -/
def selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then x i ^ 2 else 1

theorem signedProduct_mul_selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) :
    signedProduct sigma x * selectedSquareProduct sigma x = ∏ i, x i := by
  classical
  rw [signedProduct, selectedSquareProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : sigma i <;> simp [h, pow_two]

theorem signedProduct_eq_iff_selectedSquareProduct_eq {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) (c : G) :
    signedProduct sigma x = c ↔
      selectedSquareProduct sigma x = (∏ i, x i) / c := by
  have hmul := signedProduct_mul_selectedSquareProduct sigma x
  constructor
  · intro hsigned
    rw [hsigned] at hmul
    calc
      selectedSquareProduct sigma x =
          c⁻¹ * (c * selectedSquareProduct sigma x) := by group
      _ = c⁻¹ * (∏ i, x i) := by rw [hmul]
      _ = (∏ i, x i) / c := by
        rw [div_eq_mul_inv]
        ac_rfl
  · intro hselected
    rw [hselected] at hmul
    calc
      signedProduct sigma x =
          (signedProduct sigma x * ((∏ i, x i) / c)) *
            ((∏ i, x i) / c)⁻¹ := by group
      _ = (∏ i, x i) * ((∏ i, x i) / c)⁻¹ := by rw [hmul]
      _ = c := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          (∏ i, x i) * (c * (∏ i, x i)⁻¹) =
              c * ((∏ i, x i) * (∏ i, x i)⁻¹) := by ac_rfl
          _ = c := by simp

/-- A coordinate square, regarded as an element of the square subgroup. -/
def classSquareElement (x : G) :
    (classSquareSubgroup : Subgroup G) :=
  ⟨x ^ 2, classSquare_mem x⟩

@[simp] theorem classSquareElement_val (x : G) :
    (classSquareElement x : G) = x ^ 2 := rfl

/-- Failure of all sign choices, subject to the necessary square-class
condition, forces all but fewer than `|G²|` coordinate squares into one
proper subgroup of `G²`. -/
theorem exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
    [Fintype G] [DecidableEq G] {k : ℕ}
    (x : Fin k → G) (c : G)
    (hclass :
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c)
    (hmiss : ∀ sigma : Fin k → Bool, signedProduct sigma x ≠ c) :
    ∃ H : Subgroup (classSquareSubgroup : Subgroup G), H ≠ ⊤ ∧
      countOutsideSubgroup H
          (List.ofFn fun i => classSquareElement (x i)) <
        Nat.card (classSquareSubgroup : Subgroup G) := by
  classical
  letI : Fintype (classSquareSubgroup : Subgroup G) := Fintype.ofFinite _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem] at hclass
  let target : (classSquareSubgroup : Subgroup G) :=
    ⟨(∏ i, x i) / c, hclass⟩
  have htarget : target ∉ subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) := by
    intro hmem
    obtain ⟨sigma, hsigma⟩ :=
      (mem_subsetProductsList_ofFn_iff
        (fun i => classSquareElement (x i)) target).mp hmem
    have hsigmaVal := congrArg Subtype.val hsigma
    have hselected : selectedSquareProduct sigma x = (∏ i, x i) / c := by
      rw [selectedSquareProduct]
      calc
        (∏ i, if sigma i then x i ^ 2 else 1) =
            ∏ i, ((if sigma i then classSquareElement (x i) else 1 :
              (classSquareSubgroup : Subgroup G)) : G) := by
          apply Finset.prod_congr rfl
          intro i hi
          cases h : sigma i <;> simp [h]
        _ = (∏ i, x i) / c := by
          simpa [target] using hsigmaVal.symm
    exact hmiss sigma
      ((signedProduct_eq_iff_selectedSquareProduct_eq sigma x c).mpr hselected)
  have hproper : subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) ≠ Finset.univ := by
    intro hall
    exact htarget (by rw [hall]; exact Finset.mem_univ target)
  simpa only [Nat.card_eq_fintype_card] using
    (exists_proper_stabilizer_with_few_outside _ hproper)

end SignedProductConcentration

end Bernays

end

/-! ### Upstream module `Util/Bernays/ReciprocalSieve.lean` -/

section
/-!
# Finite-product and tail estimates for a convergent reciprocal sieve
-/

open Filter Topology

namespace Bernays

theorem exp_neg_two_sum_le_prod_one_sub {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha₀ : ∀ i ∈ S, 0 ≤ a i) (ha₁ : ∀ i ∈ S, a i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ S, a i) ≤ ∏ i ∈ S, (1 - a i) := by
  have hpos : ∀ i ∈ S, 0 < 1 - a i := fun i hi => by linarith [ha₁ i hi]
  have hlog : -2 * ∑ i ∈ S, a i ≤ ∑ i ∈ S, Real.log (1 - a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      linarith [(neg_log_one_sub_bound (ha₀ i hi) (ha₁ i hi)).2]
  calc
    _ ≤ Real.exp (∑ i ∈ S, Real.log (1 - a i)) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (Real.log (∏ i ∈ S, (1 - a i))) := by
      rw [Real.log_prod]
      exact fun i hi => (hpos i hi).ne'
    _ = _ := Real.exp_log (Finset.prod_pos hpos)

theorem exp_neg_two_tsum_le_prod_one_sub {ι : Type*} (a : ι → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1 / 2) (hsum : Summable a) (S : Finset ι) :
    Real.exp (-2 * ∑' i, a i) ≤ ∏ i ∈ S, (1 - a i) := by
  have hsumLe := hsum.sum_le_tsum S (fun i _ => ha₀ i)
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (exp_neg_two_sum_le_prod_one_sub S a (fun i _ => ha₀ i) (fun i _ => ha₁ i))

theorem summable_nonneg_finite_tail {ι : Type*} (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ∀ T : Finset ι, Disjoint T F → ∑ i ∈ T, a i < ε := by
  classical
  have hev : ∀ᶠ F : Finset ι in atTop, (∑' i : {i // i ∉ F}, a i) < ε :=
    (tendsto_tsum_compl_atTop_zero a).eventually (Iio_mem_nhds hε)
  obtain ⟨F, hF⟩ := hev.exists
  refine ⟨F, ?_⟩
  intro T hTF
  let e : {i // i ∈ T} ↪ {i // i ∉ F} :=
    ⟨fun i => ⟨i.1, fun hi => Finset.disjoint_left.mp hTF i.2 hi⟩,
      fun _ _ h => Subtype.ext (congrArg (fun i : {i // i ∉ F} => i.1) h)⟩
  let U := Finset.univ.map e
  have hs : Summable (fun i : {i // i ∉ F} => a i) := (Finset.summable_compl_iff F).mpr hsum
  have heq : ∑ i ∈ T, a i = ∑ i ∈ U, a i := by
    dsimp only [U]
    rw [Finset.sum_map]
    exact (T.sum_attach a).symm
  rw [heq]
  exact (hs.sum_le_tsum U (fun i _ => ha i)).trans_lt hF

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassPrimeDivergence.lean` -/

section
/-!
# Divergence of split primes outside a proper ideal-class subgroup

The proof compares a uniform lattice lower bound with a covering by prime-ideal
divisors. It applies to nonmaximal orders as well as maximal orders.
-/

open Filter Topology

namespace Bernays

noncomputable def badSplitPrimeWeight {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)) → SplitPrime d b → ℝ := by
  classical
  letI := quadraticOrderIsDomain hD
  exact fun H s => if s.idealClass hD ∉ H then (s.1 : ℝ)⁻¹ else 0

theorem badSplitPrimeWeight_nonneg {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), ∀ s : SplitPrime d b,
      0 ≤ badSplitPrimeWeight hD H s := by
  letI := quadraticOrderIsDomain hD
  intro H s
  unfold badSplitPrimeWeight
  split_ifs <;> positivity

theorem splitPrime_inv_le_half {d b : ℤ} (s : SplitPrime d b) : (s.1 : ℝ)⁻¹ ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ s.1 := by exact_mod_cast s.2.1.two_le
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq

theorem badSplitPrimeWeight_headProduct {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)),
      Summable (badSplitPrimeWeight hD H) → ∀ S : Finset (SplitPrime d b),
      (∀ s ∈ S, s.idealClass hD ∉ H) →
      Real.exp (-2 * ∑' s, badSplitPrimeWeight hD H s) ≤
        ∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹) := by
  letI := quadraticOrderIsDomain hD
  intro H hsum S hS
  have hhalf (s : SplitPrime d b) : badSplitPrimeWeight hD H s ≤ 1 / 2 := by
    unfold badSplitPrimeWeight
    split_ifs <;> first | exact splitPrime_inv_le_half s | norm_num
  have h := exp_neg_two_tsum_le_prod_one_sub (badSplitPrimeWeight hD H)
    (badSplitPrimeWeight_nonneg hD H) hhalf hsum S
  convert h using 1
  apply Finset.prod_congr rfl
  intro s hs
  simp only [badSplitPrimeWeight, if_pos (hS s hs)]

theorem cast_prod_splitPrime_sub_one_sq {d b : ℤ} (S : Finset (SplitPrime d b)) :
    ((∏ s ∈ S, (s.1 - 1) ^ 2 : ℕ) : ℝ) =
      (splitSieveModulus S : ℝ) ^ 2 * (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 := by
  have hterm (s : SplitPrime d b) : (((s.1 - 1) ^ 2 : ℕ) : ℝ) =
      (s.1 : ℝ) ^ 2 * (1 - (s.1 : ℝ)⁻¹) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub s.2.1.one_le, Nat.cast_one]
    have hq : (s.1 : ℝ) ≠ 0 := by exact_mod_cast s.2.1.ne_zero
    field_simp [hq]
  rw [Nat.cast_prod]
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
  simp only [splitSieveModulus, Nat.cast_prod]

theorem sieve_bounds_contradiction {A Q L B U K Y E t : ℝ}
    (hQ : 0 < Q) (hL : 0 < L) (hB : 0 < B) (hU : 0 < U) (hK : 0 < K) (hE : 0 < E)
    (hhead : E ^ 2 * Q ^ 2 ≤ A)
    (hlower : A * L ^ 2 ≤ U * Y)
    (hupper : Y ≤ 2 * B * (K * Q ^ 2 * L ^ 2) * t)
    (ht : t < E ^ 2 / (4 * U * B * K)) : False := by
  have hscale : U * (2 * B * (K * Q ^ 2 * L ^ 2) * (E ^ 2 / (4 * U * B * K))) =
      (E ^ 2 * Q ^ 2 * L ^ 2) / 2 := by
    field_simp [hU.ne', hB.ne', hK.ne']
    ring
  have hlt := mul_lt_mul_of_pos_left ht
    (by positivity : 0 < 2 * B * (K * Q ^ 2 * L ^ 2))
  have hlt' := mul_lt_mul_of_pos_left (hupper.trans_lt hlt) hU
  rw [hscale] at hlt'
  have hh := mul_le_mul_of_nonneg_right hhead (sq_nonneg L)
  have hp : 0 < E ^ 2 * Q ^ 2 * L ^ 2 := by positivity
  linarith

theorem not_summable_badSplitPrimeWeight {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), H ≠ ⊤ →
      ¬ Summable (badSplitPrimeWeight hD H) := by
  classical
  letI := quadraticOrderIsDomain hD
  intro H hH hsum
  let O := QuadraticAlgebra ℤ d b
  obtain ⟨B, hB, hbound⟩ := exists_uniform_natCard_idealClassBall_le hD
  have hex : ∃ C : ClassGroup O, C ∉ H := by
    by_contra! h
    apply hH
    ext C
    simp [h C]
  obtain ⟨C, hC⟩ := hex
  obtain ⟨I, hI⟩ := InvertibleIdeal.idealClass_surjective C⁻¹
  let m := (I : Ideal O).cardQuot
  let M := discriminantLevel (b ^ 2 + 4 * d) * m
  let μ := classSieveMultiplier I M
  have hm : 0 < m := I.cardQuot_pos
  have hM : 0 < M := Nat.mul_pos (discriminantLevel_pos hD.ne) hm
  have hMcast : (M : O) ≠ 0 := by
    intro hz
    change (M : QuadraticAlgebra ℤ d b) = 0 at hz
    have hr := congrArg QuadraticAlgebra.re hz
    have : (M : ℤ) = 0 := by simpa using hr
    exact hM.ne' (by exact_mod_cast this)
  obtain ⟨c, _, hc⟩ := InvertibleIdeal.exists_generator_mod_mul I (Ideal.span {(M : O)})
    (by
      intro hbot
      have hmembot : (M : O) ∈ (⊥ : Ideal O) := hbot ▸ Ideal.mem_span_singleton_self (M : O)
      exact hMcast (Ideal.mem_bot.mp hmembot))
  let U := Nat.card Oˣ
  letI := finite_quadraticOrder_units hD
  have hU : 0 < U := Nat.card_pos
  let K := classSieveScale d b μ
  have hK : 0 < K := by dsimp only [K, classSieveScale]; positivity
  let E := Real.exp (-2 * ∑' s, badSplitPrimeWeight hD H s)
  have hE : 0 < E := Real.exp_pos _
  let ε : ℝ := E ^ 2 / (4 * U * B * K)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨F, hF⟩ := summable_nonneg_finite_tail (badSplitPrimeWeight hD H)
    (badSplitPrimeWeight_nonneg hD H) hsum hε
  let S := F.filter fun s => s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ
  have hS (s : SplitPrime d b) (hs : s ∈ S) : s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ :=
    (Finset.mem_filter.mp hs).2
  have hhead := badSplitPrimeWeight_headProduct hD H hsum S (fun s hs => (hS s hs).1)
  let L := (c : O).re.natAbs + (c : O).im.natAbs + 1
  have hrL : (c : O).re.natAbs < L := by omega
  have hiL : (c : O).im.natAbs < L := by omega
  have hL : 0 < L := by omega
  let Q := splitSieveModulus S
  have hQ : 0 < Q := splitSieveModulus_pos S
  let N := K * Q ^ 2 * L ^ 2
  let A := ∏ s ∈ S, (s.1 - 1) ^ 2
  have hlower : A * L ^ 2 ≤ U * Nat.card (ClassSieveBall C N M S) := by
    have h := classSieve_lower hD I M hM c hc S (fun s hs => (hS s hs).2) L hrL hiL
    simpa only [hI, inv_inv] using h
  let T := (boundedSplitPrimes d b N).filter fun s =>
    s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S
  have hT (s : SplitPrime d b) (hs : s ∈ T) :
      s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S := (Finset.mem_filter.mp hs).2
  have hcover : ∀ J : ClassSieveBall C N M S, ∃ s ∈ T, ∃ e : Bool,
      (J.1.1 : Ideal O) ≤ (s.ideal hD e : Ideal O) := by
    intro J
    have hμM (q : ℕ) (hq : q.Prime) (h : q ∣ μ) : q ∣ M := by
      rcases hq.dvd_mul.mp h with h | h
      · exact h
      · exact h.trans (dvd_mul_left _ _)
    obtain ⟨s, hsN, hsH, hsμ, hsS, e, he⟩ := classSieve_cover hD H C hC N M μ
      (dvd_mul_right _ _) hμM S J
    exact ⟨s, Finset.mem_filter.mpr ⟨(mem_boundedSplitPrimes s).mpr hsN, hsH, hsμ, hsS⟩, e, he⟩
  have hupper := classSieve_upper_of_cover hD B hbound C N M S T hcover
  have hTF : Disjoint T F := by
    apply Finset.disjoint_left.mpr
    intro s hsT hsF
    exact (hT s hsT).2.2 (Finset.mem_filter.mpr ⟨hsF, (hT s hsT).1, (hT s hsT).2.1⟩)
  have htail : ∑ s ∈ T, (s.1 : ℝ)⁻¹ < ε := by
    convert hF T hTF using 1
    apply Finset.sum_congr rfl
    intro s hs
    simp only [badSplitPrimeWeight, if_pos (hT s hs).1]
  have hheadSq : E ^ 2 ≤ (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 := by
    have hp : 0 ≤ ∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹) := hE.le.trans hhead
    nlinarith
  have hAQ : E ^ 2 * (Q : ℝ) ^ 2 ≤ (A : ℝ) := by
    rw [show (A : ℝ) = (Q : ℝ) ^ 2 * (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 from
      cast_prod_splitPrime_sub_one_sq S, mul_comm ((Q : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_right hheadSq (sq_nonneg _)
  apply sieve_bounds_contradiction (A := (A : ℝ)) (Q := (Q : ℝ)) (L := (L : ℝ))
    (B := (B : ℝ)) (U := (U : ℝ)) (K := (K : ℝ))
    (Y := (Nat.card (ClassSieveBall C N M S) : ℝ)) (E := E)
    (by exact_mod_cast hQ) (by exact_mod_cast hL) (by exact_mod_cast hB)
    (by exact_mod_cast hU) (by exact_mod_cast hK) hE hAQ
    (by exact_mod_cast hlower) ?_ htail
  simpa only [N, Nat.cast_mul, Nat.cast_pow] using hupper

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareClassPrimes.lean` -/

section
/-!
# Large prime packets outside proper subgroups of the square classes
-/

namespace Bernays

def classSquareMonoidHom {G : Type*} [CommGroup G] : G →* (classSquareSubgroup : Subgroup G) where
  toFun := classSquareElement
  map_one' := Subtype.ext (by simp [classSquareElement])
  map_mul' x y := Subtype.ext (by simp [classSquareElement, mul_pow])

theorem classSquareMonoidHom_surjective {G : Type*} [CommGroup G] :
    Function.Surjective (classSquareMonoidHom : G → (classSquareSubgroup : Subgroup G)) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

theorem squarePreimage_ne_top {G : Type*} [CommGroup G]
    (H : Subgroup (classSquareSubgroup : Subgroup G)) (hH : H ≠ ⊤) :
    H.comap classSquareMonoidHom ≠ ⊤ := by
  intro htop
  apply hH
  ext y
  obtain ⟨x, rfl⟩ := classSquareMonoidHom_surjective y
  have hx : x ∈ H.comap classSquareMonoidHom := htop ▸ Subgroup.mem_top x
  simp only [Subgroup.mem_top, iff_true]
  exact hx

theorem exists_squareBadPrimePacket {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ R : ℝ, ∃ P : Finset (SplitPrime d b),
        (∀ s ∈ P, classSquareElement (s.idealClass hD) ∉ H) ∧
          R < ∑ s ∈ P, (s.1 : ℝ)⁻¹ := by
  classical
  letI := quadraticOrderIsDomain hD
  intro H hH R
  let K := H.comap classSquareMonoidHom
  have hnot := not_summable_badSplitPrimeWeight hD K (squarePreimage_ne_top H hH)
  have hex : ∃ F : Finset (SplitPrime d b), R < ∑ s ∈ F, badSplitPrimeWeight hD K s := by
    by_contra! h
    exact hnot (summable_of_sum_le (badSplitPrimeWeight_nonneg hD K) h)
  obtain ⟨F, hF⟩ := hex
  let P := F.filter fun s => s.idealClass hD ∉ K
  refine ⟨P, fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  have heq : ∑ s ∈ P, (s.1 : ℝ)⁻¹ = ∑ s ∈ F, badSplitPrimeWeight hD K s := by
    simp only [P, Finset.sum_filter, badSplitPrimeWeight]
  rwa [heq]

theorem SplitPrime.character_ne_neg_one {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0)
    (s : SplitPrime d b) : discriminantCharacter (b ^ 2 + 4 * d) hD s.1 ≠ -1 := by
  by_cases hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))
  · exact (discriminantCharacter_root_iff hD hc).mp s.2.2.2
  · have hz : discriminantCharacter (b ^ 2 + 4 * d) hD s.1 = 0 := by
      apply MulChar.map_nonunit
      rwa [ZMod.isUnit_iff_coprime]
    rw [hz]
    norm_num

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodNorms.lean` -/

section
/-!
# Local conditions exactly characterize norms away from the discriminant
-/

namespace Bernays

theorem InvertibleIdeal.coprime_scalar_of_cardQuot_coprime {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I : InvertibleIdeal R) (M : ℕ)
    (h : (I : Ideal R).cardQuot.Coprime M) : IsCoprime (I : Ideal R) (Ideal.span {(M : R)}) := by
  have hc : IsCoprime ((I : Ideal R).cardQuot : R) (M : R) := by
    simpa only [map_natCast] using h.isCoprime.map (Int.castRingHom R)
  obtain ⟨a, b, hab⟩ := hc
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hab]
  have hn : ((I : Ideal R).cardQuot : R) ∈ (I : Ideal R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  exact (I : Ideal R).add_mem_sup
    ((I : Ideal R).mul_mem_left a hn)
    ((Ideal.span {(M : R)}).mul_mem_left b (Ideal.mem_span_singleton_self _))

theorem principal_nat_cardQuot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {n : ℕ} (hn : 0 < n) :
    letI := quadraticOrderIsDomain hD
    (InvertibleIdeal.principal (n : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hn) :
      Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n ^ 2 := by
  letI := quadraticOrderIsDomain hD
  rw [InvertibleIdeal.coe_principal, Erdos1081.cardQuot_span_singleton_eq_norm_natAbs,
    algebraNorm_quadraticOrder, QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]

theorem parityAdmissible_mul (S : ℕ → Prop) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hSm : ParityAdmissible S m) (hSn : ParityAdmissible S n) : ParityAdmissible S (m * n) := by
  intro p hp hSp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul hm.ne' hn.ne']
  exact (hSm p hp hSp).add (hSn p hp hSp)

theorem exists_ideal_primePower_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ p e : ℕ, p.Prime → 0 < e → (p ^ e).Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1) (p ^ e) →
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ e := by
  letI := quadraticOrderIsDomain hD
  intro p e hp he hcop hlocal
  letI : Fact p.Prime := ⟨hp⟩
  have hpcop : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) :=
    hcop.of_dvd_left (dvd_pow_self p he.ne')
  by_cases hχp : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1
  · have heven : Even e := ((parityAdmissible_prime_pow_iff _ hp).mp hlocal).resolve_left
      (not_not.mpr hχp)
    obtain ⟨t, ht⟩ := heven
    refine ⟨InvertibleIdeal.principal ((p ^ t : ℕ) : QuadraticAlgebra ℤ d b)
      (quadratic_natCast_ne_zero (pow_pos hp.pos _)), ?_⟩
    rw [principal_nat_cardQuot hD (pow_pos hp.pos _), ht, pow_add, pow_two]
  · obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hpcop).mpr hχp
    have hpd : ¬(p : ℤ) ∣ b ^ 2 + 4 * d := by
      intro h
      have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
        (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
      exact hp.not_dvd_one (hpcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hdvd)
    let s : SplitPrime d b := ⟨p, hp, hpd, r, hr⟩
    refine ⟨s.ideal hD false ^ e, ?_⟩
    change InvertibleIdeal.normHom (s.ideal hD false ^ e) = p ^ e
    rw [map_pow]
    exact congrArg (fun n : ℕ => n ^ e) (s.ideal_cardQuot hD false)

theorem exists_ideal_norm_of_local {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ n : ℕ, 0 < n → n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      ParityAdmissible (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) n →
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n := by
  letI := quadraticOrderIsDomain hD
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _ hc hl
    exact exists_ideal_primePower_norm hD p e hp he hc hl
  · intro h
    exact False.elim ((Nat.lt_irrefl 0) h)
  · intro _ _ _
    exact ⟨1, Submodule.cardQuot_top _ _⟩
  · intro m n hm hn hmn ih₁ ih₂ _ hc hl
    obtain ⟨hl₁, hl₂⟩ := (parityAdmissible_mul_iff _ (zero_lt_one.trans hm) (zero_lt_one.trans hn) hmn).mp hl
    obtain ⟨I, hI⟩ := ih₁ (zero_lt_one.trans hm) (hc.of_dvd_left (dvd_mul_right _ _)) hl₁
    obtain ⟨J, hJ⟩ := ih₂ (zero_lt_one.trans hn) (hc.of_dvd_left (dvd_mul_left _ _)) hl₂
    exact ⟨I * J, (InvertibleIdeal.cardQuot_mul I J).trans (by rw [hI, hJ])⟩

theorem local_of_goodMaximal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1)
        (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1]
    exact (parityAdmissible_prime_pow_iff _ hq).mpr (Or.inr (by decide))
  · rw [s.ideal_cardQuot hD ε]
    have h := (parityAdmissible_prime_pow_iff
      (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1) (k := 1) s.2.1).mpr
        (Or.inl (SplitPrime.character_ne_neg_one hD.ne s))
    simpa only [pow_one] using h

theorem local_of_goodIdeal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1)
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [ParityAdmissible, Submodule.cardQuot_top]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul]
    have hhead := hP P List.mem_cons_self
    exact parityAdmissible_mul _ P.cardQuot_pos l.prod.cardQuot_pos
      (local_of_goodMaximal_norm hD P hhead.1 hhead.2)
      (ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ)))

end Bernays

end

/-! ### Upstream module `Util/Bernays/CoprimeIdealDecomposition.lean` -/

section
/-!
# Splitting an invertible ideal at coprime factors of its norm
-/

open scoped nonZeroDivisors

namespace Bernays

theorem ideal_scalar_split_product {R : Type*} [CommRing R] (I : Ideal R) {a b : R}
    (hc : IsCoprime a b) (hab : a * b ∈ I) :
    (I + Ideal.span {a}) * (I + Ideal.span {b}) = I := by
  have hcop : IsCoprime (I + Ideal.span {a}) (I + Ideal.span {b}) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    obtain ⟨u, v, huv⟩ := hc
    rw [← huv]
    exact (I + Ideal.span {a}).add_mem_sup
      ((show Ideal.span {a} ≤ I + Ideal.span {a} from le_sup_right)
        ((Ideal.span {a}).mul_mem_left u (Ideal.mem_span_singleton_self _)))
      ((show Ideal.span {b} ≤ I + Ideal.span {b} from le_sup_right)
        ((Ideal.span {b}).mul_mem_left v (Ideal.mem_span_singleton_self _)))
  apply le_antisymm
  · rw [mul_add, add_mul, add_mul]
    apply sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_right)
    apply sup_le Ideal.mul_le_left
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr hab
  · rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf le_sup_left le_sup_left

theorem coprime_factor_norms {a b m n : ℕ} (hmn : m.Coprime n)
    (hab : a * b = m * n) (ha : a ∣ m ^ 2) (hb : b ∣ n ^ 2) : a = m ∧ b = n := by
  have han : a.Coprime n := (hmn.pow_left 2).of_dvd_left ha
  have hmb : m.Coprime b := (hmn.pow_right 2).of_dvd_right hb
  have ham : a ∣ m := han.dvd_mul_right.mp (hab ▸ dvd_mul_right a b)
  have hma : m ∣ a := hmb.dvd_mul_right.mp (hab.symm ▸ dvd_mul_right m n)
  have hbm : b.Coprime m := hmb.symm
  have hna : n.Coprime a := han.symm
  have hbn : b ∣ n := hbm.dvd_mul_left.mp (hab ▸ dvd_mul_left b a)
  have hnb : n ∣ b := hna.dvd_mul_left.mp (hab.symm ▸ dvd_mul_left n m)
  exact ⟨Nat.dvd_antisymm ham hma, Nat.dvd_antisymm hbn hnb⟩

theorem exists_coprime_norm_factors {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b), ∀ m n : ℕ,
      m.Coprime n → (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m * n →
      ∃ J K : InvertibleIdeal (QuadraticAlgebra ℤ d b), J * K = I ∧
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧
        (K : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n := by
  letI := quadraticOrderIsDomain hD
  intro I m n hmn hnorm
  let O := QuadraticAlgebra ℤ d b
  have hmnpos : 0 < m * n := hnorm ▸ I.cardQuot_pos
  have hm : 0 < m := Nat.pos_of_mul_pos_right hmnpos
  have hn : 0 < n := Nat.pos_of_mul_pos_left hmnpos
  have hscalar : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using hmn.isCoprime.map (Int.castRingHom O)
  have hmem : (m : O) * (n : O) ∈ (I : Ideal O) := by
    rw [← Nat.cast_mul, ← hnorm, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  let J₀ : Ideal O := I + Ideal.span {(m : O)}
  let K₀ : Ideal O := I + Ideal.span {(n : O)}
  have hprod : J₀ * K₀ = (I : Ideal O) := ideal_scalar_split_product (I : Ideal O) hscalar hmem
  have hu : IsUnit ((J₀ : FractionalIdeal O⁰ (FractionRing O)) *
      (K₀ : FractionalIdeal O⁰ (FractionRing O))) := by
    rw [← FractionalIdeal.coeIdeal_mul, hprod]
    exact I.2
  let J : InvertibleIdeal O := ⟨J₀, isUnit_of_mul_isUnit_left hu⟩
  let K : InvertibleIdeal O := ⟨K₀, isUnit_of_mul_isUnit_right hu⟩
  have hJK : J * K = I := InvertibleIdeal.ext hprod
  have hJnorm : (J : Ideal O).cardQuot ∣ m ^ 2 := by
    have hdiv := AddSubgroup.index_dvd_of_le (H := (Ideal.span {(m : O)}).toAddSubgroup)
      (K := J₀.toAddSubgroup) (show (Ideal.span {(m : O)}) ≤ J₀ from le_sup_right)
    change (J : Ideal O).cardQuot ∣ (Ideal.span {(m : O)}).cardQuot at hdiv
    have heq : (Ideal.span {(m : O)}).cardQuot = m ^ 2 := principal_nat_cardQuot hD hm
    rwa [heq] at hdiv
  have hKnorm : (K : Ideal O).cardQuot ∣ n ^ 2 := by
    have hdiv := AddSubgroup.index_dvd_of_le (H := (Ideal.span {(n : O)}).toAddSubgroup)
      (K := K₀.toAddSubgroup) (show (Ideal.span {(n : O)}) ≤ K₀ from le_sup_right)
    change (K : Ideal O).cardQuot ∣ (Ideal.span {(n : O)}).cardQuot at hdiv
    have heq : (Ideal.span {(n : O)}).cardQuot = n ^ 2 := principal_nat_cardQuot hD hn
    rwa [heq] at hdiv
  have hmul : (J : Ideal O).cardQuot * (K : Ideal O).cardQuot = m * n := by
    rw [← InvertibleIdeal.cardQuot_mul, hJK, hnorm]
  obtain ⟨hJ, hK⟩ := coprime_factor_norms hmn hmul hJnorm hKnorm
  exact ⟨J, K, hJK, hJ, hK⟩

theorem InvertibleIdeal.coprime_norm_product_add_scalar {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I J : InvertibleIdeal R)
    (hcop : (I : Ideal R).cardQuot.Coprime (J : Ideal R).cardQuot) :
    (I : Ideal R) * (J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} = (I : Ideal R) := by
  have hmI : ((I : Ideal R).cardQuot : R) ∈ (I : Ideal R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hJ := Ideal.isCoprime_iff_sup_eq.mp (J.coprime_scalar_of_cardQuot_coprime _ hcop.symm)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).mpr hmI)
  · calc
      (I : Ideal R) = (I : Ideal R) * ((J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)}) := by
        change (I : Ideal R) = (I : Ideal R) * ((J : Ideal R) ⊔ Ideal.span {((I : Ideal R).cardQuot : R)})
        rw [hJ, Ideal.mul_top]
      _ = (I : Ideal R) * (J : Ideal R) +
          (I : Ideal R) * Ideal.span {((I : Ideal R).cardQuot : R)} := mul_add _ _ _
      _ ≤ _ := sup_le_sup_left Ideal.mul_le_right _

theorem InvertibleIdeal.coprime_norm_factors_unique {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] {I J K L : InvertibleIdeal R}
    (hprod : I * J = K * L)
    (hcop : (I : Ideal R).cardQuot.Coprime (J : Ideal R).cardQuot)
    (hIK : (I : Ideal R).cardQuot = (K : Ideal R).cardQuot)
    (hJL : (J : Ideal R).cardQuot = (L : Ideal R).cardQuot) : I = K ∧ J = L := by
  have hcop' : (K : Ideal R).cardQuot.Coprime (L : Ideal R).cardQuot := by rwa [← hIK, ← hJL]
  have hIK' : I = K := by
    apply InvertibleIdeal.ext
    have hsum := congrArg (fun A : InvertibleIdeal R =>
      (A : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)}) hprod
    change (I : Ideal R) * (J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} =
      (K : Ideal R) * (L : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} at hsum
    rw [I.coprime_norm_product_add_scalar J hcop, hIK,
      K.coprime_norm_product_add_scalar L hcop'] at hsum
    exact hsum
  refine ⟨hIK', ?_⟩
  subst K
  exact InvertibleIdeal.mul_right_cancel _ _ I (by simpa only [mul_comm] using hprod)

end Bernays

end

/-! ### Upstream module `Util/Bernays/NormFiberCounts.lean` -/

section
/-!
# Counting norm fibers and bounded ideal sets
-/

open scoped Classical

namespace Bernays

theorem natCard_bounded_eq_sum_fibers {X : Type*} (f : X → ℕ)
    (hf : ∀ x, 0 < f x) (N : ℕ) [Finite {x : X // f x ≤ N}] :
    Nat.card {x : X // f x ≤ N} =
      ∑ n ∈ Finset.Icc 1 N, Nat.card {x : X // f x = n} := by
  classical
  let S := {n : ℕ // n ∈ Finset.Icc 1 N}
  letI : Fintype S := by dsimp only [S]; infer_instance
  let e : {x : X // f x ≤ N} ≃ Σ n : S, {x : X // f x = n.1} :=
    { toFun := fun x => ⟨⟨f x.1, Finset.mem_Icc.mpr ⟨hf x.1, x.2⟩⟩, ⟨x.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.le.trans (Finset.mem_Icc.mp x.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨n, hn⟩, ⟨x, hx⟩⟩
        change f x = n at hx
        subst n
        rfl }
  letI (n : S) : Finite {x : X // f x = n.1} := by
    let g : {x : X // f x = n.1} → {x : X // f x ≤ N} :=
      fun x => ⟨x.1, x.2.le.trans (Finset.mem_Icc.mp n.2).2⟩
    exact Finite.of_injective g (fun x y h =>
      Subtype.ext (congrArg (fun t : {x : X // f x ≤ N} => t.1) h))
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_coe_sort (Finset.Icc 1 N) (fun n => Nat.card {x : X // f x = n})

abbrev CoprimeIdealsInClass (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) :=
  {I : InvertibleIdeal R // I.idealClass = C ∧ IsCoprime (I : Ideal R) F}

noncomputable def idealClassNormCount {R : Type*} [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) (n : ℕ) : ℕ :=
  Nat.card {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot = n}

def boundedCoprimeClassEquiv {R : Type*} [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) (N : ℕ) :
    {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot ≤ N} ≃
      RestrictedIdealClassBall R C N (fun J => IsCoprime (J : Ideal R) F) where
  toFun I := ⟨⟨I.1.1, I.1.2.1, I.2⟩, I.1.2.2⟩
  invFun I := ⟨⟨I.1.1, I.1.2.1, I.2⟩, I.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealClassNormCount_cumsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (F : Ideal (QuadraticAlgebra ℤ d b)) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, idealClassNormCount C F n) =
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) := by
  letI := quadraticOrderIsDomain hD
  intro C F N
  let O := QuadraticAlgebra ℤ d b
  letI := finite_idealClassBall hD C N
  letI : Finite (RestrictedIdealClassBall O C N (fun J => IsCoprime (J : Ideal O) F)) := by
    dsimp only [RestrictedIdealClassBall]
    infer_instance
  letI : Finite {I : CoprimeIdealsInClass O C F // (I.1 : Ideal O).cardQuot ≤ N} :=
    Finite.of_equiv _ (boundedCoprimeClassEquiv C F N).symm
  exact (natCard_bounded_eq_sum_fibers
    (fun I : CoprimeIdealsInClass O C F => (I.1 : Ideal O).cardQuot)
    (fun I => I.1.cardQuot_pos) N).symm.trans (Nat.card_congr (boundedCoprimeClassEquiv C F N))

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodIdealNormFibers.lean` -/

section
/-!
# Multiplicativity of counts of coprime quadratic ideals of prescribed norm
-/

namespace Bernays

abbrev GoodIdealNormFiber {R : Type*} [CommRing R] [IsDomain R]
    (F : Ideal R) (n : ℕ) :=
  {I : InvertibleIdeal R // (I : Ideal R).cardQuot = n ∧ IsCoprime (I : Ideal R) F}

theorem finite_goodIdealNormFiber {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ), Finite (GoodIdealNormFiber F n) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro F n
  let O := QuadraticAlgebra ℤ d b
  letI (C : ClassGroup O) := finite_idealClassBall hD C n
  let e : GoodIdealNormFiber F n → Σ C : ClassGroup O, IdealClassBall O C n :=
    fun I => ⟨I.1.idealClass, ⟨I.1, rfl, I.2.1.le⟩⟩
  apply Finite.of_injective e
  intro I J hIJ
  exact Subtype.ext (congrArg (fun t : Σ C : ClassGroup O, IdealClassBall O C n => t.2.1) hIJ)

noncomputable def goodIdealNormFiberMulEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (m n : ℕ) (hmn : m.Coprime n) :
    letI := quadraticOrderIsDomain hD
    GoodIdealNormFiber F m × GoodIdealNormFiber F n ≃ GoodIdealNormFiber F (m * n) := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let f : GoodIdealNormFiber F m × GoodIdealNormFiber F n → GoodIdealNormFiber F (m * n) :=
    fun x => ⟨x.1.1 * x.2.1, by rw [InvertibleIdeal.cardQuot_mul, x.1.2.1, x.2.2.1],
      x.1.2.2.mul_left x.2.2.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have hprod : x.1.1 * x.2.1 = y.1.1 * y.2.1 := congrArg Subtype.val hxy
    have hc : (x.1.1 : Ideal O).cardQuot.Coprime (x.2.1 : Ideal O).cardQuot := by
      rwa [x.1.2.1, x.2.2.1]
    obtain ⟨h₁, h₂⟩ := InvertibleIdeal.coprime_norm_factors_unique hprod hc
      (x.1.2.1.trans y.1.2.1.symm) (x.2.2.1.trans y.2.2.1.symm)
    exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  · intro I
    obtain ⟨J, K, hJK, hJ, hK⟩ := exists_coprime_norm_factors hD I.1 m n hmn I.2.1
    have hcop : IsCoprime ((J : Ideal O) * (K : Ideal O)) F := by
      change IsCoprime ((J * K : InvertibleIdeal O) : Ideal O) F
      rw [hJK]
      exact I.2.2
    exact ⟨(⟨J, hJ, hcop.of_mul_left_left⟩, ⟨K, hK, hcop.of_mul_left_right⟩), Subtype.ext hJK⟩

theorem goodIdealNormFiber_card_mul {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (m n : ℕ) (hmn : m.Coprime n) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F (m * n)) =
      Nat.card (GoodIdealNormFiber F m) * Nat.card (GoodIdealNormFiber F n) := by
  letI := quadraticOrderIsDomain hD
  rw [← Nat.card_congr (goodIdealNormFiberMulEquiv hD F m n hmn), Nat.card_prod]

end Bernays

end

/-! ### Upstream module `Util/Bernays/PrimePowerMaximals.lean` -/

section
/-!
# Maximal ideal factors of a good prime-power norm
-/

namespace Bernays

theorem inertMaximal_eq_principal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ 2 →
      P = InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos) := by
  letI := quadraticOrderIsDomain hD
  letI : Fact p.Prime := ⟨hp⟩
  intro P hP hnorm
  have hmem : (p : QuadraticAlgebra ℤ d b) ^ 2 ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← Nat.cast_pow, ← hnorm, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hpd : ¬ (p : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
      (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
    exact (hp.coprime_iff_not_dvd.mp hc) hdvd
  have hpmem : ((p : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    simpa only [Int.cast_natCast] using hP.isPrime.mem_of_pow_mem 2 hmem
  rcases quadraticMaximal_split_or_inert d b p (P : Ideal (QuadraticAlgebra ℤ d b)) hP hpmem hpd with
    hprincipal | ⟨r, hr, _⟩
  · exact InvertibleIdeal.ext (by simpa only [InvertibleIdeal.coe_principal, Int.cast_natCast] using hprincipal)
  · exact False.elim (((discriminantCharacter_root_iff hD.ne hc).mp ⟨r, hr⟩) hχ)

theorem SplitPrime.ideal_ne_conjugate {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    s.ideal hD false ≠ s.ideal hD true := by
  letI := quadraticOrderIsDomain hD
  intro h
  have heq := congrArg (fun I : InvertibleIdeal (QuadraticAlgebra ℤ d b) =>
    (I : Ideal (QuadraticAlgebra ℤ d b))) h
  exact rootIdeal_ne_of_ne d b s.1 s.root_sq (s.orientedRoot_sq true)
    (quadratic_roots_distinct _ _ _ s.root_sq s.discr_ne_zero) heq

theorem goodMaximal_of_primePower_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ p ^ e →
      ((discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1 ∧
        P = InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos)) ∨
        ∃ s : SplitPrime d b, s.1 = p ∧ ∃ ε : Bool, P = s.ideal hD ε) := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF hdiv
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, hP'⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · have hqp : q = p := by
      have hqdvd : q ∣ p ^ e := (dvd_pow_self q (by decide : 2 ≠ 0)).trans (h.2.1 ▸ hdiv)
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)
    subst q
    exact Or.inl ⟨h.1, inertMaximal_eq_principal hD hp hc h.1 P hP h.2.1⟩
  · have hqp : q = p := by
      have hn : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q := by
        rw [hP', s.ideal_cardQuot hD ε, hs]
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hn ▸ hdiv))
    exact Or.inr ⟨s, hs.trans hqp, ε, hP'⟩

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealFactorizationUnique.lean` -/

section
/-!
# Uniqueness of factorization into invertible maximal ideals
-/

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R]

theorem maximal_mem_of_prod_le (P : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal)
    (l : List (InvertibleIdeal R)) (hl : ∀ Q ∈ l, (Q : Ideal R).IsMaximal)
    (hle : ((l.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R)) : P ∈ l := by
  induction l with
  | nil =>
    exact False.elim (hP.ne_top (top_unique hle))
  | cons Q l ih =>
    change (Q : Ideal R) * ((l.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R) at hle
    rcases hP.isPrime.mul_le.mp hle with hQ | htail
    · have heq : Q = P := ext ((hl Q List.mem_cons_self).eq_of_le hP.ne_top hQ)
      exact List.mem_cons.mpr (Or.inl heq.symm)
    · exact List.mem_cons_of_mem Q (ih (fun T hT => hl T (List.mem_cons_of_mem Q hT)) htail)

theorem maximal_factors_perm {l r : List (InvertibleIdeal R)} (hprod : l.prod = r.prod)
    (hl : ∀ P ∈ l, (P : Ideal R).IsMaximal)
    (hr : ∀ P ∈ r, (P : Ideal R).IsMaximal) : l.Perm r := by
  classical
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => exact List.Perm.nil
    | cons Q r =>
      have hle : (⊤ : Ideal R) ≤ (Q : Ideal R) := by
        change ((([] : List (InvertibleIdeal R)).prod : InvertibleIdeal R) : Ideal R) ≤ (Q : Ideal R)
        rw [hprod]
        exact Ideal.mul_le_left
      exact False.elim ((hr Q List.mem_cons_self).ne_top (top_unique hle))
  | cons P l ih =>
    have hP := hl P List.mem_cons_self
    have hle : ((r.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R) := by
      rw [← hprod]
      exact Ideal.mul_le_left
    have hmem := maximal_mem_of_prod_le P hP r hr hle
    have hperm : r.Perm (P :: r.erase P) := List.perm_cons_erase hmem
    have heq : l.prod = (r.erase P).prod := by
      have h := hprod.trans hperm.prod_eq
      simp only [List.prod_cons] at h
      exact mul_right_cancel _ _ P (by simpa only [mul_comm] using h)
    exact ((ih heq (fun Q hQ => hl Q (List.mem_cons_of_mem P hQ))
      (fun Q hQ => hr Q (List.mem_of_mem_erase hQ))).cons P).trans hperm.symm

end Bernays.InvertibleIdeal

end

/-! ### Upstream module `Util/Bernays/TwoMaximalPowers.lean` -/

section
/-!
# Products supported on two distinct maximal ideals
-/

open scoped Classical

namespace Bernays

theorem list_prod_two_values {M : Type*} [CommMonoid M] [DecidableEq M]
    (P Q : M) (hPQ : P ≠ Q) (l : List M) (hl : ∀ x ∈ l, x = P ∨ x = Q) :
    l.prod = P ^ l.count P * Q ^ l.count Q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    have ht := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    rcases hx with rfl | rfl
    · simp only [List.prod_cons, List.count_cons_self, List.count_cons,
        beq_iff_eq, hPQ, if_false, Nat.add_zero, ht, pow_succ]
      ac_rfl
    · simp only [List.prod_cons, List.count_cons_self, List.count_cons,
        beq_iff_eq, Ne.symm hPQ, if_false, Nat.add_zero, ht, pow_succ]
      ac_rfl

theorem InvertibleIdeal.two_maximal_powers_injective {R : Type*} [CommRing R] [IsDomain R]
    (P Q : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal) (hQ : (Q : Ideal R).IsMaximal)
    (hPQ : P ≠ Q) {i j k l : ℕ} (heq : P ^ i * Q ^ j = P ^ k * Q ^ l) : i = k ∧ j = l := by
  classical
  have hprod : (List.replicate i P ++ List.replicate j Q).prod =
      (List.replicate k P ++ List.replicate l Q).prod := by
    simpa only [List.prod_append, List.prod_replicate] using heq
  have hmax (a b : ℕ) : ∀ T ∈ List.replicate a P ++ List.replicate b Q, (T : Ideal R).IsMaximal := by
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · have ht : T = P := (List.mem_replicate.mp hT).2
      exact ht ▸ hP
    · have ht : T = Q := (List.mem_replicate.mp hT).2
      exact ht ▸ hQ
  have hperm := maximal_factors_perm hprod (hmax i j) (hmax k l)
  have hcountP := hperm.count_eq P
  have hcountQ := hperm.count_eq Q
  simpa [List.count_append, List.count_replicate, hPQ, Ne.symm hPQ] using And.intro hcountP hcountQ

end Bernays

end

/-! ### Upstream module `Util/Bernays/SplitPrimePowerIdeals.lean` -/

section
/-!
# Exact enumeration of ideals with a good split-prime-power norm
-/

open scoped Classical

namespace Bernays

theorem InvertibleIdeal.cardQuot_dvd_listProd_of_mem {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] {P : InvertibleIdeal R} {l : List (InvertibleIdeal R)} (hP : P ∈ l) :
    (P : Ideal R).cardQuot ∣ ((l.prod : InvertibleIdeal R) : Ideal R).cardQuot := by
  obtain ⟨K, hK⟩ := List.dvd_prod hP
  exact ⟨(K : Ideal R).cardQuot, hK ▸ InvertibleIdeal.cardQuot_mul P K⟩

theorem SplitPrime.exists_powers_of_norm_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 ^ e →
      ∃ i : ℕ, i ≤ e ∧ I = s.ideal hD false ^ i * s.ideal hD true ^ (e - i) := by
  letI := quadraticOrderIsDomain hD
  intro I hIF hnorm
  obtain ⟨l, hl, hmax⟩ := goodQuadraticIdeal_factorization hD I hIF
  have hsupport : ∀ P ∈ l, P = s.ideal hD false ∨ P = s.ideal hD true := by
    intro P hPl
    have hdiv : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ s.1 ^ e := by
      rw [← hnorm, ← hl]
      exact InvertibleIdeal.cardQuot_dvd_listProd_of_mem hPl
    rcases goodMaximal_of_primePower_norm hD s.2.1 e P (hmax P hPl).1 (hmax P hPl).2 hdiv with
      h | ⟨t, ht, ε, hP⟩
    · exact False.elim (s.character_ne_neg_one hD.ne h.1)
    · have hts : t = s := Subtype.ext ht
      subst t
      cases ε
      · exact Or.inl hP
      · exact Or.inr hP
  let i := l.count (s.ideal hD false)
  let j := l.count (s.ideal hD true)
  have hprod : I = s.ideal hD false ^ i * s.ideal hD true ^ j :=
    hl.symm.trans (list_prod_two_values _ _ (s.ideal_ne_conjugate hD) l hsupport)
  have he : i + j = e := by
    apply Nat.pow_right_injective s.2.1.two_le
    have h := congrArg InvertibleIdeal.normHom hprod
    change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = _ at h
    rw [map_mul, map_pow, map_pow] at h
    change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
      (s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ i *
      (s.ideal hD true : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ j at h
    rw [hnorm, s.ideal_cardQuot hD false, s.ideal_cardQuot hD true, ← pow_add] at h
    exact h.symm
  exact ⟨i, by omega, by simpa only [show e - i = j by omega] using hprod⟩

noncomputable def SplitPrime.normPowerEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Fin (e + 1) ≃ GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e) := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  have hnorm (i : Fin (e + 1)) :
      ((s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1) : InvertibleIdeal O) : Ideal O).cardQuot =
        s.1 ^ e := by
    change InvertibleIdeal.normHom (s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1)) = _
    rw [map_mul, map_pow, map_pow]
    change (s.ideal hD false : Ideal O).cardQuot ^ i.1 * (s.ideal hD true : Ideal O).cardQuot ^ (e - i.1) = _
    rw [s.ideal_cardQuot hD false, s.ideal_cardQuot hD true, ← pow_add, Nat.add_sub_of_le (by omega)]
  let f : Fin (e + 1) → GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e) := fun i =>
    ⟨s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1), hnorm i,
      InvertibleIdeal.coprime_scalar_of_cardQuot_coprime _ _ (by rw [hnorm i]; exact hc.pow_left e)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hprod := congrArg Subtype.val hij
    have h := InvertibleIdeal.two_maximal_powers_injective _ _
      (s.ideal_isMaximal hD false) (s.ideal_isMaximal hD true) (s.ideal_ne_conjugate hD) hprod
    exact Fin.ext h.1
  · intro I
    obtain ⟨i, hie, hI⟩ := s.exists_powers_of_norm_primePower hD e I.1 I.2.2 I.2.1
    exact ⟨⟨i, by omega⟩, Subtype.ext hI.symm⟩

theorem SplitPrime.normPower_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e)) = e + 1 := by
  letI := quadraticOrderIsDomain hD
  rw [← Nat.card_congr (s.normPowerEquiv hD hc e), Nat.card_fin]

end Bernays

end

/-! ### Upstream module `Util/Bernays/InertPrimePowerIdeals.lean` -/

section
/-!
# Exact enumeration of ideals with a good inert-prime-power norm
-/

open scoped Classical

namespace Bernays

theorem list_prod_single_value {M : Type*} [Monoid M] (P : M) (l : List M)
    (hl : ∀ x ∈ l, x = P) : l.prod = P ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, hl x List.mem_cons_self,
      ih (fun y hy => hl y (List.mem_cons_of_mem x hy)), List.length_cons, pow_succ']

theorem exists_inert_principal_power {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime)
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ e →
      ∃ k : ℕ, e = 2 * k ∧ I =
        InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos) ^ k := by
  letI := quadraticOrderIsDomain hD
  intro I hIF hnorm
  obtain ⟨l, hl, hmax⟩ := goodQuadraticIdeal_factorization hD I hIF
  let P := InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos)
  have hsupport : ∀ Q ∈ l, Q = P := by
    intro Q hQl
    have hdiv : (Q : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ p ^ e := by
      rw [← hnorm, ← hl]
      exact InvertibleIdeal.cardQuot_dvd_listProd_of_mem hQl
    rcases goodMaximal_of_primePower_norm hD hp e Q (hmax Q hQl).1 (hmax Q hQl).2 hdiv with
      h | ⟨s, hs, _, _⟩
    · exact h.2
    · exact False.elim (s.character_ne_neg_one hD.ne (hs ▸ hχ))
  have hprod : I = P ^ l.length := hl.symm.trans (list_prod_single_value P l hsupport)
  refine ⟨l.length, ?_, hprod⟩
  apply Nat.pow_right_injective hp.two_le
  have h := congrArg InvertibleIdeal.normHom hprod
  change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = _ at h
  rw [map_pow] at h
  change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
    (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ l.length at h
  rw [hnorm, principal_nat_cardQuot hD hp.pos, ← pow_mul] at h
  exact h

theorem inert_normPower_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) = if Even e then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let X := GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)
  by_cases he : Even e
  · obtain ⟨k, hk⟩ := he
    let P := InvertibleIdeal.principal (p : O) (quadratic_natCast_ne_zero hp.pos)
    have hnorm : ((P ^ k : InvertibleIdeal O) : Ideal O).cardQuot = p ^ e := by
      change InvertibleIdeal.normHom (P ^ k) = _
      rw [map_pow]
      change (P : Ideal O).cardQuot ^ k = p ^ e
      rw [principal_nat_cardQuot hD hp.pos, ← pow_mul, hk]
      congr 1
      omega
    let x : X := ⟨P ^ k, hnorm,
      InvertibleIdeal.coprime_scalar_of_cardQuot_coprime _ _ (by rw [hnorm]; exact hc.pow_left e)⟩
    letI : Unique X :=
      { default := x
        uniq := by
          intro I
          obtain ⟨j, hj, hI⟩ := exists_inert_principal_power hD hp hχ e I.1 I.2.2 I.2.1
          have hjk : j = k := by omega
          apply Subtype.ext
          simpa only [hjk] using hI }
    rw [if_pos (show Even e from ⟨k, hk⟩)]
    exact Nat.card_unique
  · letI : IsEmpty X := ⟨fun I => by
      obtain ⟨k, hk, _⟩ := exists_inert_principal_power hD hp hχ e I.1 I.2.2 I.2.1
      exact he ⟨k, by omega⟩⟩
    rw [if_neg he]
    change Nat.card X = 0
    simp

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodNormSupport.lean` -/

section
/-!
# Support and unit coefficient of the good ideal norm count
-/

namespace Bernays

theorem goodMaximal_norm_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot.Coprime (discriminantLevel (b ^ 2 + 4 * d)) := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, _, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1]
    exact hc.pow_left 2
  · rw [s.ideal_cardQuot hD ε, hs]
    exact hc

theorem goodIdeal_norm_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot.Coprime (discriminantLevel (b ^ 2 + 4 * d)) := by
  letI := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [Submodule.cardQuot_top]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul]
    exact (goodMaximal_norm_coprime hD P (hP P List.mem_cons_self).1 (hP P List.mem_cons_self).2).mul_left
      (ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ)))

theorem goodIdealNormFiber_card_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F 0) = 0 := by
  letI := quadraticOrderIsDomain hD
  letI : IsEmpty (GoodIdealNormFiber F 0) := ⟨fun I => I.1.cardQuot_pos.ne' I.2.1⟩
  simp

theorem goodIdealNormFiber_card_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber F 1) = 1 := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let x : GoodIdealNormFiber F 1 := ⟨(1 : InvertibleIdeal O), by
    change (⊤ : Ideal O).cardQuot = 1
    exact Submodule.cardQuot_top O O, by
    rw [InvertibleIdeal.coe_one]
    exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)⟩
  letI : Unique (GoodIdealNormFiber F 1) :=
    { default := x
      uniq := by
        intro I
        apply Subtype.ext
        apply InvertibleIdeal.ext
        change (I.1 : Ideal O) = ⊤
        exact Submodule.cardQuot_eq_one_iff.mp I.2.1 }
  exact Nat.card_unique

theorem goodIdealNormFiber_card_eq_zero_of_not_coprime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (n : ℕ) (hn : ¬ n.Coprime (discriminantLevel (b ^ 2 + 4 * d))) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) = 0 := by
  letI := quadraticOrderIsDomain hD
  letI : IsEmpty (GoodIdealNormFiber (quadraticBadIdeal d b) n) := ⟨fun I => by
    have h := goodIdeal_norm_coprime hD I.1 I.2.2
    rw [I.2.1] at h
    exact hn h⟩
  simp

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealGeneratorCounting.lean` -/

section
/-!
# Exact ideal-class counts from principal generators
-/

namespace Bernays

def IdealGeneratorBall {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
    (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop) :=
  {z : QuadraticAlgebra ℤ d b // ∃ hz : z ≠ 0,
    ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      I * J = InvertibleIdeal.principal z hz ∧
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ≤ N ∧ A J}

theorem generator_norm_of_product {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    ∀ z : QuadraticAlgebra ℤ d b, ∀ hz : z ≠ 0,
    I * J = InvertibleIdeal.principal z hz →
      z.norm.natAbs = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot *
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro I J z hz hprod
  have h := InvertibleIdeal.cardQuot_mul I J
  rwa [hprod, InvertibleIdeal.coe_principal,
    Erdos1081.cardQuot_span_singleton_eq_norm_natAbs, algebraNorm_quadraticOrder] at h

theorem idealGeneratorBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (N : ℕ)
      (A : InvertibleIdeal (QuadraticAlgebra ℤ d b) → Prop),
      Nat.card (IdealGeneratorBall I N A) = Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N A) := by
  classical
  letI := quadraticOrderIsDomain hD
  intro I N A
  let O := QuadraticAlgebra ℤ d b
  let X := IdealGeneratorBall I N A
  let Y := RestrictedIdealClassBall O I.idealClass⁻¹ N A
  have hz (x : X) : (x.1 : O) ≠ 0 := x.2.choose
  have hex (x : X) : ∃ J : InvertibleIdeal O, I * J = InvertibleIdeal.principal (x.1 : O) (hz x) ∧
      (J : Ideal O).cardQuot ≤ N ∧ A J := x.2.choose_spec
  let J (x : X) := (hex x).choose
  have hJ (x : X) : I * J x = InvertibleIdeal.principal (x.1 : O) (hz x) ∧
      (J x : Ideal O).cardQuot ≤ N ∧ A (J x) := (hex x).choose_spec
  have hclass (x : X) : (J x).idealClass = I.idealClass⁻¹ := by
    have h := congrArg InvertibleIdeal.idealClass (hJ x).1
    rw [InvertibleIdeal.idealClass_mul, InvertibleIdeal.idealClass_principal] at h
    exact (eq_inv_iff_mul_eq_one).mpr (by simpa only [mul_comm] using h)
  let f : X → Y := fun x => ⟨⟨J x, hclass x, (hJ x).2.1⟩, (hJ x).2.2⟩
  have hnorm (x : X) : (x.1 : O).norm.natAbs ≤ (I : Ideal O).cardQuot * N := by
    rw [generator_norm_of_product hD I (J x) x.1 (hz x) (hJ x).1]
    exact Nat.mul_le_mul_left _ (hJ x).2.1
  letI := finite_quadraticNormBall hD ((I : Ideal O).cardQuot * N)
  let e : X → QuadraticNormBall d b ((I : Ideal O).cardQuot * N) := fun x => ⟨x.1, hnorm x⟩
  letI : Finite X := Finite.of_injective e (fun x y h =>
    Subtype.ext (congrArg (fun t : QuadraticNormBall d b ((I : Ideal O).cardQuot * N) => t.1) h))
  letI := finite_idealClassBall hD I.idealClass⁻¹ N
  letI : Finite Y := by dsimp only [Y, RestrictedIdealClassBall]; infer_instance
  letI := finite_quadraticOrder_units hD
  have hcancel (x : X) (K : InvertibleIdeal O)
      (hK : I * K = InvertibleIdeal.principal (x.1 : O) (hz x)) : J x = K :=
    InvertibleIdeal.mul_right_cancel _ _ I (by simpa only [mul_comm] using (hJ x).1.trans hK.symm)
  apply natCard_eq_units_mul_of_associate_fibers (fun x : X => (x.1 : O))
    Subtype.val_injective hz f
  · intro y
    obtain ⟨z, hz₀, hprod, _⟩ := exists_principal_generator_norm hD I y.1.1
      (by rw [y.1.2.1, mul_inv_cancel])
    let x : X := ⟨z, hz₀, y.1.1, hprod, y.1.2.2, y.2⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hcancel x y.1.1 hprod
  · intro x y hxy
    have hJJ : J x = J y := congrArg (fun t : Y => t.1.1) hxy
    apply Ideal.span_singleton_eq_span_singleton.mp
    have hprod : InvertibleIdeal.principal (x.1 : O) (hz x) =
        InvertibleIdeal.principal (y.1 : O) (hz y) := (hJ x).1.symm.trans (hJJ ▸ (hJ y).1)
    exact congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
  · intro x u
    have hu : (x.1 : O) * (u : O) ≠ 0 := mul_ne_zero (hz x) (Units.ne_zero u)
    have hprincipal : InvertibleIdeal.principal ((x.1 : O) * u) hu =
        InvertibleIdeal.principal (x.1 : O) (hz x) := by
      apply InvertibleIdeal.ext
      exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.symm ⟨u, rfl⟩)
    let w : X := ⟨(x.1 : O) * u, hu, J x, (hJ x).1.trans hprincipal.symm, (hJ x).2⟩
    refine ⟨w, rfl, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hcancel w (J x) ((hJ x).1.trans hprincipal.symm)

end Bernays

end

/-! ### Upstream module `Util/Bernays/CoprimeIdealResidues.lean` -/

section
/-!
# Unit residue classes in an ideal coprime to the modulus
-/

namespace Bernays

theorem isCoprime_principal_iff_isUnit_quotient {R : Type*} [CommRing R]
    (F : Ideal R) (x : R) :
    IsCoprime (Ideal.span {x}) F ↔ IsUnit (Ideal.Quotient.mk F x) := by
  constructor
  · intro h
    have htop := Ideal.isCoprime_iff_sup_eq.mp h
    have hone : (1 : R) ∈ Ideal.span {x} + F := by
      change 1 ∈ Ideal.span {x} ⊔ F
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk F r, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk F) hab
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one, hr, map_mul] at hq
    exact hq
  · intro h
    obtain ⟨u, hu⟩ := h
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : R ⧸ F)
    have hmul : Ideal.Quotient.mk F (x * r) = 1 := by rw [map_mul, ← hu, hr, Units.mul_inv]
    have hmem : x * r - 1 ∈ F := Ideal.Quotient.eq.mp (by simpa only [map_one] using hmul)
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    change (1 : R) ∈ Ideal.span {x} + F
    have hx : x * r ∈ Ideal.span {x} := (Ideal.span {x}).mul_mem_right r (Ideal.mem_span_singleton_self x)
    have hsub := (Ideal.span {x} + F).sub_mem
      ((show Ideal.span {x} ≤ Ideal.span {x} + F from le_sup_left) hx)
      ((show F ≤ Ideal.span {x} + F from le_sup_right) hmem)
    simpa only [sub_sub_cancel] using hsub

theorem quotient_surjective_on_coprime_ideal {R : Type*} [CommRing R]
    (I F : Ideal R) (hIF : IsCoprime I F) :
    Function.Surjective (fun x : I => Ideal.Quotient.mk F (x : R)) := by
  have hone : (1 : R) ∈ I + F := by
    change 1 ∈ I ⊔ F
    rw [Ideal.isCoprime_iff_sup_eq.mp hIF]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hone
  have hqi : Ideal.Quotient.mk F i = 1 := by
    have h := congrArg (Ideal.Quotient.mk F) hij
    simpa only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, add_zero, map_one] using h
  intro a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨⟨i * r, I.mul_mem_right r hi⟩, ?_⟩
  change Ideal.Quotient.mk F (i * r) = a
  rw [map_mul, hqi, one_mul, hr]

theorem quotient_eq_iff_sub_mem_product {R : Type*} [CommRing R]
    (I F : Ideal R) (hIF : IsCoprime I F) (x y : I) :
    Ideal.Quotient.mk F (x : R) = Ideal.Quotient.mk F (y : R) ↔
      (x : R) - (y : R) ∈ F * I := by
  rw [Ideal.Quotient.eq, Ideal.mul_eq_inf_of_isCoprime hIF.symm]
  exact (and_iff_left (I.sub_mem x.2 y.2)).symm

end Bernays

end

/-! ### Upstream module `Util/Bernays/LatticeCellBounds.lean` -/

section
/-!
# Counting lattice points by bounded fundamental cells

The two ball inclusions retain a boundary-width error. In dimension two this
gives the square-root error needed for the ideal-class Dirichlet series.
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise Classical

namespace Bernays

theorem fundamental_cell_ball_bounds {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (L : AddSubgroup E) [Countable L]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) {B R : ℝ}
    (hB : ∀ x ∈ F, ‖x‖ ≤ B) (a : E) (S : Finset L)
    (hS : ∀ l : L, l ∈ S ↔ ‖a + (l : E)‖ ≤ R) :
    μ (closedBall 0 (R - B)) ≤ (S.card : ℝ≥0∞) * μ F ∧
      (S.card : ℝ≥0∞) * μ F ≤ μ (closedBall 0 (R + B)) := by
  have hFa := hF.vadd_of_comm a
  have hcell (l : L) : μ (l +ᵥ (a +ᵥ F)) = μ F := by
    rw [measure_vadd, measure_vadd]
  have hnorm (l : L) {x : E} (hx : x ∈ l +ᵥ (a +ᵥ F)) :
      ‖x - (a + (l : E))‖ ≤ B := by
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    change ‖(l : E) + (a + z) - (a + (l : E))‖ ≤ B
    rw [show (l : E) + (a + z) - (a + (l : E)) = z by abel]
    exact hB z hz
  constructor
  · rw [hFa.measure_eq_tsum' (closedBall 0 (R - B))]
    calc
      (∑' l : L, μ (closedBall 0 (R - B) ∩ (l +ᵥ (a +ᵥ F)))) ≤
          ∑' l : L, if l ∈ S then μ F else 0 := by
        apply ENNReal.tsum_le_tsum
        intro l
        by_cases hl : l ∈ S
        · rw [if_pos hl, ← hcell l]
          exact measure_mono inter_subset_right
        · rw [if_neg hl]
          have hempty : closedBall 0 (R - B) ∩ (l +ᵥ (a +ᵥ F)) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hxnorm : ‖x‖ ≤ R - B := by simpa only [mem_closedBall, dist_zero_right] using hx.1
            have hcenter : ‖a + (l : E)‖ ≤ R := by
              have ht := norm_sub_le x (x - (a + (l : E)))
              rw [sub_sub_cancel] at ht
              exact ht.trans (by linarith [hnorm l hx.2])
            exact hl ((hS l).mpr hcenter)
          simp only [hempty, measure_empty, le_refl]
      _ = (S.card : ℝ≥0∞) * μ F := by
        rw [tsum_eq_sum (s := S) (fun l hl => if_neg hl)]
        simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
  · rw [hFa.measure_eq_tsum' (closedBall 0 (R + B))]
    calc
      (S.card : ℝ≥0∞) * μ F =
          ∑ l ∈ S, μ (closedBall 0 (R + B) ∩ (l +ᵥ (a +ᵥ F))) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro l hl
        have hsubset : (l +ᵥ (a +ᵥ F)) ⊆ closedBall 0 (R + B) := by
          intro x hx
          have ht := norm_add_le (x - (a + (l : E))) (a + (l : E))
          rw [sub_add_cancel] at ht
          have hxn : ‖x‖ ≤ R + B := ht.trans (by linarith [hnorm l hx, (hS l).mp hl])
          simpa only [mem_closedBall, dist_zero_right] using hxn
        rw [Set.inter_eq_right.mpr hsubset, hcell]
      _ ≤ _ := ENNReal.sum_le_tsum S

theorem complex_fundamental_cell_error (L : AddSubgroup ℂ) [Countable L]
    {F : Set ℂ} (hF : IsAddFundamentalDomain L F volume) {B R : ℝ}
    (hB₀ : 0 ≤ B) (hB : ∀ z ∈ F, ‖z‖ ≤ B) (hR : 0 ≤ R)
    (a : ℂ) (S : Finset L) (hS : ∀ l : L, l ∈ S ↔ ‖a + (l : ℂ)‖ ≤ R) :
    |(S.card : ℝ) * volume.real F - Real.pi * R ^ 2| ≤
      Real.pi * (2 * B * R + B ^ 2) := by
  obtain ⟨hlo, hhi⟩ := fundamental_cell_ball_bounds L volume hF hB a S hS
  have hFfinite : volume F ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (t := closedBall 0 B) ?_) measure_closedBall_lt_top
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hB z hz
  have hprod : (S.card : ℝ≥0∞) * volume F ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hFfinite
  have hball (r : ℝ) (hr : 0 ≤ r) : (volume (closedBall (0 : ℂ) r)).toReal = Real.pi * r ^ 2 := by
    rw [Complex.volume_closedBall]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.coe_toReal]
    exact mul_comm _ _
  have hhiR := (ENNReal.toReal_le_toReal hprod (ne_of_lt measure_closedBall_lt_top)).mpr hhi
  rw [hball (R + B) (by linarith), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hhiR
  change (S.card : ℝ) * volume.real F ≤ Real.pi * (R + B) ^ 2 at hhiR
  rw [abs_le]
  constructor
  · by_cases hBR : B ≤ R
    · have hloR := (ENNReal.toReal_le_toReal (ne_of_lt measure_closedBall_lt_top) hprod).mpr hlo
      rw [hball (R - B) (sub_nonneg.mpr hBR), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hloR
      change Real.pi * (R - B) ^ 2 ≤ (S.card : ℝ) * volume.real F at hloR
      nlinarith [Real.pi_pos, sq_nonneg B]
    · have hcount : 0 ≤ (S.card : ℝ) * volume.real F := by positivity
      have hsq : R ^ 2 ≤ B ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le,
        mul_nonneg (mul_nonneg Real.pi_pos.le hB₀) hR]
  · nlinarith [Real.pi_pos, sq_nonneg B]

end Bernays

end

/-! ### Upstream module `Util/Bernays/LatticePointAsymptotic.lean` -/

section
/-!
# Uniform boundary error for lattice translates in the complex plane
-/

open MeasureTheory Metric Set Module
open scoped Classical

namespace Bernays

def latticeCosetBall (L : Submodule ℤ ℂ) (a : ℂ) (R : ℝ) : Set L :=
  {l | ‖a + (l : ℂ)‖ ≤ R}

theorem finite_latticeCosetBall (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (a : ℂ) (R : ℝ) : (latticeCosetBall L a R).Finite := by
  have hclosed : IsClosed (L : Set ℂ) :=
    AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hfinite : (closedBall (-a) R ∩ (L : Set ℂ)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall hclosed
  have hpre := hfinite.preimage (f := ((↑) : L → ℂ)) Subtype.val_injective.injOn
  convert hpre using 1
  ext l
  simp only [latticeCosetBall, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
    mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm]
  exact (and_iff_left l.2).symm

theorem latticeCosetBall_error (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℂ, ∀ R : ℝ, 0 ≤ R →
      |(Nat.card (latticeCosetBall L a R) : ℝ) - Real.pi / ZLattice.covolume L * R ^ 2| ≤
        K * (R + 1) := by
  let b := Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  obtain ⟨B₀, hB₀⟩ := (isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)))
  let B := max B₀ 0
  have hB : ∀ z ∈ F, ‖z‖ ≤ B := fun z hz => (hB₀ z hz).trans (le_max_left _ _)
  have hBpos : 0 ≤ B := le_max_right _ _
  have hF := ZLattice.isAddFundamentalDomain b volume
  have hcovol : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hc : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  let K := Real.pi * (2 * B + B ^ 2 + 1) / ZLattice.covolume L
  have hK : 0 < K := div_pos (mul_pos Real.pi_pos (by nlinarith [sq_nonneg B])) hc
  refine ⟨K, hK, ?_⟩
  intro a R hR
  let S := (finite_latticeCosetBall L a R).toFinset
  letI : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hS (l : L) : l ∈ S ↔ ‖a + (l : ℂ)‖ ≤ R := Set.Finite.mem_toFinset _
  have herr := complex_fundamental_cell_error L.toAddSubgroup hF hBpos hB hR a S hS
  have hcard : (S.card : ℝ) = Nat.card (latticeCosetBall L a R) := by
    exact_mod_cast (Set.ncard_eq_toFinset_card (latticeCosetBall L a R)
      (finite_latticeCosetBall L a R)).symm
  rw [hcard, ← hcovol] at herr
  have hdiv := div_le_div_of_nonneg_right herr hc.le
  have heq : |(Nat.card (latticeCosetBall L a R) : ℝ) * ZLattice.covolume L - Real.pi * R ^ 2| /
      ZLattice.covolume L =
      |(Nat.card (latticeCosetBall L a R) : ℝ) - Real.pi / ZLattice.covolume L * R ^ 2| := by
    rw [← abs_of_pos hc]
    rw [← abs_div, abs_of_pos hc]
    congr 1
    field_simp
  rw [heq] at hdiv
  apply hdiv.trans
  dsimp only [K]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hc.le
  rw [mul_assoc Real.pi (2 * B + B ^ 2 + 1) (R + 1)]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) hR]

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticComplexLattice.lean` -/

section
/-!
# The complex lattice of a negative-discriminant quadratic order

We use twice the usual complex embedding, so that the norm-square identity
has no denominators. Its covolume need not be explicitly evaluated.
-/

open MeasureTheory Module Submodule Metric Set
open scoped Classical

namespace Bernays

noncomputable def quadraticComplexMap (d b : ℤ) : QuadraticAlgebra ℤ d b →ₗ[ℤ] ℂ where
  toFun z := ⟨2 * z.re + b * z.im, Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im⟩
  map_add' z w := by apply Complex.ext <;> simp <;> ring
  map_smul' n z := by apply Complex.ext <;> simp <;> ring

theorem quadraticComplexMap_norm_sq {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : ‖quadraticComplexMap d b z‖ ^ 2 = 4 * (z.norm : ℝ) := by
  have hD' : (0 : ℝ) < -(b ^ 2 + 4 * d : ℤ) := by exact_mod_cast neg_pos.mpr hD
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (2 * (z.re : ℝ) + (b : ℝ) * z.im) * (2 * z.re + b * z.im) +
    (Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im) *
      (Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im) = _
  have hi : (4 : ℝ) * z.norm = (2 * (z.re : ℝ) + (b : ℝ) * z.im) ^ 2 -
      (b ^ 2 + 4 * d : ℤ) * (z.im : ℝ) ^ 2 := by
    exact_mod_cast four_mul_quadraticNorm d b z
  rw [hi]
  nlinarith [Real.sq_sqrt hD'.le]

theorem quadraticComplexMap_injective {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Function.Injective (quadraticComplexMap d b) := by
  suffices hzero : ∀ z, quadraticComplexMap d b z = 0 → z = 0 by
    intro z w hzw
    have hsub : quadraticComplexMap d b (z - w) = 0 := by rw [map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (hzero _ hsub)
  intro z hz
  have hn := quadraticComplexMap_norm_sq hD z
  rw [hz, norm_zero, zero_pow (by decide), zero_eq_mul] at hn
  have hzNorm : z.norm = 0 := by exact_mod_cast hn.resolve_left (by norm_num)
  exact (quadraticNorm_eq_zero_iff hD z).mp hzNorm

noncomputable def quadraticIdealLattice (d b : ℤ) (I : Ideal (QuadraticAlgebra ℤ d b)) :
    Submodule ℤ ℂ := (I.restrictScalars ℤ).map (quadraticComplexMap d b)

theorem mem_quadraticIdealLattice (d b : ℤ) (I : Ideal (QuadraticAlgebra ℤ d b)) (w : ℂ) :
    w ∈ quadraticIdealLattice d b I ↔ ∃ z ∈ I, quadraticComplexMap d b z = w := Iff.rfl

theorem quadraticIdealLattice_discrete {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) : DiscreteTopology (quadraticIdealLattice d b I) := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  refine ⟨ball 0 1, isOpen_ball, ?_⟩
  ext w
  simp only [Set.mem_preimage, mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := (mem_quadraticIdealLattice d b I w).mp w.2
    have heq : z = 0 := by
      by_contra hzero
      have hn : 0 < z.norm := lt_of_le_of_ne (quadraticNorm_nonneg hD z)
        (Ne.symm ((quadraticNorm_eq_zero_iff hD z).not.mpr hzero))
      have hnR : (1 : ℝ) ≤ z.norm := by exact_mod_cast hn
      have hnorm := quadraticComplexMap_norm_sq hD z
      rw [hzw] at hnorm
      nlinarith [norm_nonneg (w : ℂ)]
    apply Subtype.ext
    change (w : ℂ) = 0
    simpa only [heq, map_zero] using hzw.symm
  · rintro rfl
    simp

theorem quadraticIdealLattice_full {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    letI := quadraticIdealLattice_discrete hD I
    IsZLattice ℝ (quadraticIdealLattice d b I) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticIdealLattice_discrete hD I
  let O := QuadraticAlgebra ℤ d b
  letI : Finite (O ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  let m := I.cardQuot
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.card_pos (α := O ⧸ I))
  let s := Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast neg_pos.mpr hD)
  have hmI : (m : O) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hzI : (⟨0, (m : ℤ)⟩ : O) ∈ I := by
    have h := I.mul_mem_left (⟨0, 1⟩ : O) hmI
    have heq : (⟨0, 1⟩ : O) * (m : O) = ⟨0, (m : ℤ)⟩ := by
      apply QuadraticAlgebra.ext <;>
        simp only [O, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, zero_mul,
          mul_zero, zero_add, add_zero, one_mul]
    rwa [heq] at h
  let L := quadraticIdealLattice d b I
  have hv₀ : quadraticComplexMap d b (m : O) ∈ Submodule.span ℝ (L : Set ℂ) :=
    Submodule.subset_span ((mem_quadraticIdealLattice d b I _).mpr ⟨_, hmI, rfl⟩)
  have hv₁ : quadraticComplexMap d b (⟨0, (m : ℤ)⟩ : O) ∈ Submodule.span ℝ (L : Set ℂ) :=
    Submodule.subset_span ((mem_quadraticIdealLattice d b I _).mpr ⟨_, hzI, rfl⟩)
  refine ⟨eq_top_iff.mpr ?_⟩
  intro w _
  have hmem := (Submodule.span ℝ (L : Set ℂ)).add_mem
    ((Submodule.span ℝ (L : Set ℂ)).smul_mem ((w.re - (b : ℝ) * w.im / s) / (2 * m)) hv₀)
    ((Submodule.span ℝ (L : Set ℂ)).smul_mem (w.im / (s * m)) hv₁)
  have heq : ((w.re - (b : ℝ) * w.im / s) / (2 * m)) • quadraticComplexMap d b (m : O) +
      (w.im / (s * m)) • quadraticComplexMap d b (⟨0, (m : ℤ)⟩ : O) = w := by
    apply Complex.ext
    · simp only [O, Complex.add_re, Complex.smul_re, quadraticComplexMap, LinearMap.coe_mk,
        AddHom.coe_mk, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        Int.cast_natCast, Int.cast_zero, smul_eq_mul]
      change ((w.re - (b : ℝ) * w.im / s) / (2 * m)) * (2 * m + (b : ℝ) * 0) +
        (w.im / (s * m)) * (2 * 0 + (b : ℝ) * m) = w.re
      field_simp
      ring
    · simp only [O, Complex.add_im, Complex.smul_im, quadraticComplexMap, LinearMap.coe_mk,
        AddHom.coe_mk, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        Int.cast_natCast, Int.cast_zero, smul_eq_mul]
      change ((w.re - (b : ℝ) * w.im / s) / (2 * m)) * (s * 0) +
        (w.im / (s * m)) * (s * m) = w.im
      simp only [mul_zero, zero_add, div_mul_cancel₀ _ (mul_ne_zero hs.ne' hm.ne')]
  exact heq ▸ hmem

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticIdealCovolume.lean` -/

section
/-!
# Covolume and index of arbitrary quadratic-order ideals
-/

namespace Bernays

theorem quadraticIdealLattice_covolume {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    ZLattice.covolume (quadraticIdealLattice d b I) =
      (I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤) := by
  letI := quadraticIdealLattice_discrete hD I
  letI := quadraticIdealLattice_full hD I hI
  letI := quadraticIdealLattice_discrete hD ⊤
  letI := quadraticIdealLattice_full hD ⊤ top_ne_bot
  have hle : quadraticIdealLattice d b I ≤ quadraticIdealLattice d b ⊤ :=
    Submodule.map_mono le_top
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (quadraticIdealLattice d b I) (quadraticIdealLattice d b ⊤) hle
  have hindex : (quadraticIdealLattice d b I).toAddSubgroup.relIndex
      (quadraticIdealLattice d b ⊤).toAddSubgroup = I.cardQuot := by
    change (I.toAddSubgroup.map (quadraticComplexMap d b).toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup (QuadraticAlgebra ℤ d b)).map (quadraticComplexMap d b).toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ (quadraticComplexMap_injective hD),
      AddSubgroup.relIndex_top_right]
    rfl
  rw [hindex] at h
  exact (div_eq_iff (ZLattice.covolume_pos (quadraticIdealLattice d b ⊤)).ne').mp h

end Bernays

end

/-! ### Upstream module `Util/Bernays/QuadraticCosetCounts.lean` -/

section
/-!
# A square-root error for quadratic-ideal coset counts
-/

open scoped Classical

namespace Bernays

noncomputable def quadraticIdealLatticeEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) : I ≃ quadraticIdealLattice d b I :=
  Equiv.ofBijective (fun z : I => ⟨quadraticComplexMap d b z,
    (mem_quadraticIdealLattice d b I _).mpr ⟨z, z.2, rfl⟩⟩) (by
      constructor
      · intro z w hzw
        exact Subtype.ext (quadraticComplexMap_injective hD (congrArg Subtype.val hzw))
      · intro w
        obtain ⟨z, hz, hzw⟩ := (mem_quadraticIdealLattice d b I w).mp w.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩)

theorem quadraticNorm_natAbs_le_iff_complex {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) (N : ℕ) :
    z.norm.natAbs ≤ N ↔ ‖quadraticComplexMap d b z‖ ≤ 2 * Real.sqrt (N : ℝ) := by
  have hn := quadraticComplexMap_norm_sq hD z
  have hcast : (z.norm.natAbs : ℝ) = (z.norm : ℝ) := by
    have hZ : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg (quadraticNorm_nonneg hD z)
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℝ)) hZ
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hs₀ := Real.sqrt_nonneg (N : ℝ)
  have hz₀ := norm_nonneg (quadraticComplexMap d b z)
  constructor
  · intro h
    have hR : (z.norm.natAbs : ℝ) ≤ N := by exact_mod_cast h
    rw [hcast] at hR
    nlinarith
  · intro h
    have hR : (z.norm.natAbs : ℝ) ≤ N := by rw [hcast]; nlinarith
    exact_mod_cast hR

def quadraticIdealCosetBall {d b : ℤ} (I : Ideal (QuadraticAlgebra ℤ d b))
    (a : QuadraticAlgebra ℤ d b) (N : ℕ) :=
  {z : I // (a + (z : QuadraticAlgebra ℤ d b)).norm.natAbs ≤ N}

theorem finite_quadraticIdealCosetBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (a : QuadraticAlgebra ℤ d b) (N : ℕ) :
    Finite (quadraticIdealCosetBall I a N) := by
  letI := finite_quadraticNormBall hD N
  let e : quadraticIdealCosetBall I a N → QuadraticNormBall d b N := fun z => ⟨a + z.1, z.2⟩
  apply Finite.of_injective e
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  exact add_left_cancel (congrArg (fun t : QuadraticNormBall d b N => t.1) hzw)

theorem quadraticIdealCosetBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (a : QuadraticAlgebra ℤ d b) (N : ℕ) :
    Nat.card (quadraticIdealCosetBall I a N) =
      Nat.card (latticeCosetBall (quadraticIdealLattice d b I)
        (quadraticComplexMap d b a) (2 * Real.sqrt (N : ℝ))) := by
  apply Nat.card_congr
  apply (quadraticIdealLatticeEquiv hD I).subtypeEquiv
  intro z
  rw [quadraticNorm_natAbs_le_iff_complex hD, map_add]
  rfl

theorem quadraticIdealCosetBall_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : QuadraticAlgebra ℤ d b, ∀ N : ℕ,
      |(Nat.card (quadraticIdealCosetBall I a N) : ℝ) -
        (4 * Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) * N| ≤
          K * (Real.sqrt (N : ℝ) + 1) := by
  letI := quadraticIdealLattice_discrete hD I
  letI := quadraticIdealLattice_full hD I hI
  obtain ⟨K, hK, hbound⟩ := latticeCosetBall_error (quadraticIdealLattice d b I)
  refine ⟨2 * K, by positivity, ?_⟩
  intro a N
  have h := hbound (quadraticComplexMap d b a) (2 * Real.sqrt (N : ℝ)) (by positivity)
  rw [← quadraticIdealCosetBall_card hD, quadraticIdealLattice_covolume hD I hI] at h
  have hmain : Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤)) *
      (2 * Real.sqrt (N : ℝ)) ^ 2 =
      (4 * Real.pi / ((I.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) * N := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  rw [hmain] at h
  exact h.trans (by nlinarith [Real.sqrt_nonneg (N : ℝ)])

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodIdealGeneratorBall.lean` -/

section
/-!
# Coprime ideal classes as counts of unit-residue generators
-/

namespace Bernays

def CoprimeQuadraticBall {d b : ℤ} (I F : Ideal (QuadraticAlgebra ℤ d b)) (T : ℕ) :=
  {z : QuadraticAlgebra ℤ d b // z ∈ I ∧ z.norm.natAbs ≤ T ∧ IsUnit (Ideal.Quotient.mk F z)}

theorem exists_good_factor_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (F : Ideal (QuadraticAlgebra ℤ d b)), F ≠ ⊤ → IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) F →
    ∀ z : QuadraticAlgebra ℤ d b, ∀ N : ℕ,
      (∃ hz : z ≠ 0, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        I * J = InvertibleIdeal.principal z hz ∧
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ≤ N ∧
          IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F) ↔
      z ∈ (I : Ideal (QuadraticAlgebra ℤ d b)) ∧
        z.norm.natAbs ≤ (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot * N ∧
        IsUnit (Ideal.Quotient.mk F z) := by
  letI := quadraticOrderIsDomain hD
  intro I F hF hIF z N
  let O := QuadraticAlgebra ℤ d b
  letI : Nontrivial (O ⧸ F) := Ideal.Quotient.nontrivial_iff.mpr hF
  constructor
  · rintro ⟨hz, J, hprod, hJN, hJF⟩
    have hspan : (I : Ideal O) * (J : Ideal O) = Ideal.span {z} :=
      congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
    have hzI : z ∈ (I : Ideal O) := Ideal.mul_le_left
      (hspan ▸ Ideal.mem_span_singleton_self z)
    refine ⟨hzI, ?_, (isCoprime_principal_iff_isUnit_quotient F z).mp ?_⟩
    · rw [generator_norm_of_product hD I J z hz hprod]
      exact Nat.mul_le_mul_left _ hJN
    · rw [← hspan]
      exact hIF.mul_left hJF
  · rintro ⟨hzI, hzN, hzunit⟩
    have hz : z ≠ 0 := by
      intro hzero
      have h := hzunit.ne_zero
      exact h (by rw [hzero, map_zero])
    obtain ⟨J, hprod⟩ := InvertibleIdeal.exists_mul_eq_of_le I (InvertibleIdeal.principal z hz)
      ((Ideal.span_singleton_le_iff_mem _).mpr hzI)
    refine ⟨hz, J, hprod, ?_, ?_⟩
    · rw [generator_norm_of_product hD I J z hz hprod] at hzN
      exact (mul_le_mul_iff_right₀ I.cardQuot_pos).mp (by simpa only [Nat.mul_comm] using hzN)
    · have hc := (isCoprime_principal_iff_isUnit_quotient F z).mpr hzunit
      have hspan : (I : Ideal O) * (J : Ideal O) = Ideal.span {z} :=
        congrArg (fun K : InvertibleIdeal O => (K : Ideal O)) hprod
      rw [← hspan] at hc
      exact hc.of_mul_left_right

theorem coprimeQuadraticBall_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (F : Ideal (QuadraticAlgebra ℤ d b)), F ≠ ⊤ → IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) F →
    ∀ N : ℕ,
      Nat.card (CoprimeQuadraticBall (I : Ideal (QuadraticAlgebra ℤ d b)) F
        ((I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot * N)) =
      Nat.card (QuadraticAlgebra ℤ d b)ˣ *
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) I.idealClass⁻¹ N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) := by
  letI := quadraticOrderIsDomain hD
  intro I F hF hIF N
  rw [← idealGeneratorBall_card hD]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun z => (exists_good_factor_iff hD I F hF hIF z N).symm)

end Bernays

end

/-! ### Upstream module `Util/Bernays/ResidueCosetCounts.lean` -/

section
/-!
# Decomposing coprime generators into lattice cosets
-/

open scoped Classical

namespace Bernays

theorem coprimeQuadraticBall_eq_sum_cosets {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I F : Ideal (QuadraticAlgebra ℤ d b)) (hIF : IsCoprime I F)
    [Fintype (QuadraticAlgebra ℤ d b ⧸ F)ˣ]
    (c : (QuadraticAlgebra ℤ d b ⧸ F)ˣ → I)
    (hc : ∀ u, Ideal.Quotient.mk F (c u : QuadraticAlgebra ℤ d b) = u) (T : ℕ) :
    Nat.card (CoprimeQuadraticBall I F T) =
      ∑ u : (QuadraticAlgebra ℤ d b ⧸ F)ˣ,
        Nat.card (quadraticIdealCosetBall (F * I) (c u) T) := by
  let O := QuadraticAlgebra ℤ d b
  let X := Σ u : (O ⧸ F)ˣ, quadraticIdealCosetBall (F * I) (c u) T
  let Y := CoprimeQuadraticBall I F T
  have hmem (u : (O ⧸ F)ˣ) (w : quadraticIdealCosetBall (F * I) (c u) T) :
      (c u : O) + (w.1 : O) ∈ I := I.add_mem (c u).2 (Ideal.mul_le_right w.1.2)
  have hres (u : (O ⧸ F)ˣ) (w : quadraticIdealCosetBall (F * I) (c u) T) :
      Ideal.Quotient.mk F ((c u : O) + (w.1 : O)) = u := by
    rw [map_add, hc, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left w.1.2), add_zero]
  let f : X → Y := fun x => ⟨(c x.1 : O) + (x.2.1 : O), hmem x.1 x.2,
    x.2.2, (hres x.1 x.2).symm ▸ x.1.isUnit⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, x⟩ ⟨v, y⟩ hxy
      have hval : (c u : O) + (x.1 : O) = (c v : O) + (y.1 : O) :=
        congrArg (fun t : Y => t.1) hxy
      have huv : u = v := by
        apply Units.ext
        have hq := congrArg (Ideal.Quotient.mk F) hval
        rwa [hres u x, hres v y] at hq
      subst v
      have hxy' : x = y := Subtype.ext (Subtype.ext (add_left_cancel hval))
      subst y
      rfl
    · intro y
      let u : (O ⧸ F)ˣ := y.2.2.2.unit
      have hu : Ideal.Quotient.mk F y.1 = u := y.2.2.2.unit_spec.symm
      have hdiff : y.1 - (c u : O) ∈ F * I :=
        (quotient_eq_iff_sub_mem_product I F hIF ⟨y.1, y.2.1⟩ (c u)).mp (hu.trans (hc u).symm)
      have hsum : (c u : O) + (y.1 - (c u : O)) = y.1 := by abel
      let w : quadraticIdealCosetBall (F * I) (c u) T :=
        ⟨⟨y.1 - (c u : O), hdiff⟩, by
          change ((c u : O) + (y.1 - (c u : O))).norm.natAbs ≤ T
          rw [hsum]
          exact y.2.2.1⟩
      refine ⟨⟨u, w⟩, ?_⟩
      apply Subtype.ext
      change (c u : O) + (y.1 - (c u : O)) = y.1
      abel
  letI (u : (O ⧸ F)ˣ) : Finite (quadraticIdealCosetBall (F * I) (c u) T) :=
    finite_quadraticIdealCosetBall hD (F * I) (c u) T
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]

end Bernays

end

/-! ### Upstream module `Util/Bernays/CoprimeGeneratorAsymptotic.lean` -/

section
/-!
# The area term for generators in coprime residue classes
-/

open scoped Classical

namespace Bernays

theorem coprimeQuadraticBall_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I F : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) (hF : F ≠ ⊥)
    (hIF : IsCoprime I F) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ,
      |(Nat.card (CoprimeQuadraticBall I F T) : ℝ) -
        ((Nat.card (QuadraticAlgebra ℤ d b ⧸ F)ˣ : ℝ) *
          (4 * Real.pi / (((F * I).cardQuot : ℝ) *
            ZLattice.covolume (quadraticIdealLattice d b ⊤)))) * T| ≤
      K * (Real.sqrt (T : ℝ) + 1) := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  letI : Finite (O ⧸ F) := Ring.HasFiniteQuotients.finiteQuotient hF
  letI := Fintype.ofFinite (O ⧸ F)
  have hFI : F * I ≠ ⊥ := (Ideal.mul_eq_bot).not.mpr (not_or.mpr ⟨hF, hI⟩)
  obtain ⟨K, hK, hbound⟩ := quadraticIdealCosetBall_error hD (F * I) hFI
  have hU : (0 : ℝ) < Nat.card (O ⧸ F)ˣ := by exact_mod_cast Nat.card_pos (α := (O ⧸ F)ˣ)
  refine ⟨Nat.card (O ⧸ F)ˣ * K, mul_pos hU hK, ?_⟩
  intro T
  have hsurj := quotient_surjective_on_coprime_ideal I F hIF
  let c : (O ⧸ F)ˣ → I := fun u => (hsurj (u : O ⧸ F)).choose
  have hc (u : (O ⧸ F)ˣ) : Ideal.Quotient.mk F (c u : O) = u := (hsurj (u : O ⧸ F)).choose_spec
  let C := 4 * Real.pi / (((F * I).cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))
  have heq : (Nat.card (CoprimeQuadraticBall I F T) : ℝ) - (Nat.card (O ⧸ F)ˣ : ℝ) * C * T =
      ∑ u : (O ⧸ F)ˣ, ((Nat.card (quadraticIdealCosetBall (F * I) (c u) T) : ℝ) - C * T) := by
    rw [coprimeQuadraticBall_eq_sum_cosets hD I F hIF c hc, Nat.cast_sum,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Nat.card_eq_fintype_card]
    ring
  change |(Nat.card (CoprimeQuadraticBall I F T) : ℝ) - (Nat.card (O ⧸ F)ˣ : ℝ) * C * T| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ u : (O ⧸ F)ˣ,
        |(Nat.card (quadraticIdealCosetBall (F * I) (c u) T) : ℝ) - C * T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : (O ⧸ F)ˣ, K * (Real.sqrt (T : ℝ) + 1) :=
      Finset.sum_le_sum fun u _ => hbound (c u) T
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Nat.card_eq_fintype_card, mul_assoc]

end Bernays

end

/-! ### Upstream module `Util/Bernays/IdealClassAreaAsymptotic.lean` -/

section
/-!
# The common area term in every coprime quadratic ideal class

The linear term is independent of the ideal class; the error is a constant
times `sqrt N + 1`. This is a count of ideals, not of distinct represented
integers.
-/

namespace Bernays

theorem area_coefficient_cancel (a m f v u n : ℝ) (hm : m ≠ 0) (hf : f ≠ 0)
    (hv : v ≠ 0) (hu : u ≠ 0) :
    a * (4 * Real.pi / ((f * m) * v)) * (m * n) =
      u * ((a * (4 * Real.pi) / (f * v * u)) * n) := by
  field_simp

theorem divide_area_error {a C K m u n : ℝ} (hu : 0 < u) (hm : 0 ≤ m)
    (hK : 0 ≤ K) (_hn : 0 ≤ n)
    (h : |u * a - u * (C * n)| ≤ K * (Real.sqrt (m * n) + 1)) :
    |a - C * n| ≤ (K * (Real.sqrt m + 1) / u) * (Real.sqrt n + 1) := by
  rw [← mul_sub, abs_mul, abs_of_pos hu] at h
  have hdiv : |a - C * n| ≤ (K * (Real.sqrt (m * n) + 1)) / u :=
    (le_div_iff₀ hu).mpr (by simpa only [mul_comm] using h)
  apply hdiv.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hu.le
  rw [mul_assoc K]
  apply mul_le_mul_of_nonneg_left _ hK
  rw [Real.sqrt_mul hm]
  nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg n]

noncomputable def idealClassAreaConstant (d b : ℤ) (F : Ideal (QuadraticAlgebra ℤ d b)) : ℝ :=
  (Nat.card (QuadraticAlgebra ℤ d b ⧸ F)ˣ : ℝ) * (4 * Real.pi) /
    ((F.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤) *
      (Nat.card (QuadraticAlgebra ℤ d b)ˣ : ℝ))

theorem idealClassArea_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      |(Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
        (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ) -
          idealClassAreaConstant d b F * N| ≤ K * (Real.sqrt (N : ℝ) + 1) := by
  letI := quadraticOrderIsDomain hD
  intro C
  let O := QuadraticAlgebra ℤ d b
  letI : Finite (O ⧸ F) := Ring.HasFiniteQuotients.finiteQuotient hF₀
  letI := finite_quadraticOrder_units hD
  letI := quadraticIdealLattice_discrete hD ⊤
  letI := quadraticIdealLattice_full hD ⊤ top_ne_bot
  obtain ⟨I, hIC, hIF⟩ := InvertibleIdeal.exists_coprime_representative C⁻¹ F hF₀
  obtain ⟨K, hK, hbound⟩ := coprimeQuadraticBall_error hD (I : Ideal O) F I.ne_bot hF₀ hIF
  have hu : (0 : ℝ) < Nat.card Oˣ := by exact_mod_cast Nat.card_pos (α := Oˣ)
  have hnormI : (0 : ℝ) < (I : Ideal O).cardQuot := by exact_mod_cast I.cardQuot_pos
  have hnormF : (0 : ℝ) < F.cardQuot := by exact_mod_cast Nat.card_pos (α := O ⧸ F)
  have hcov := ZLattice.covolume_pos (quadraticIdealLattice d b ⊤)
  let m : ℝ := (I : Ideal O).cardQuot
  let u : ℝ := Nat.card Oˣ
  refine ⟨K * (Real.sqrt m + 1) / u, div_pos (mul_pos hK (by positivity)) hu, ?_⟩
  intro N
  have h := hbound ((I : Ideal O).cardQuot * N)
  rw [coprimeQuadraticBall_card hD I F hF₁ hIF, hIC, inv_inv, Nat.cast_mul,
    cardQuot_mul_invertible F (I : Ideal O) hF₀ I.2, Nat.cast_mul, Nat.cast_mul] at h
  have hmain :
      (Nat.card (O ⧸ F)ˣ : ℝ) *
        (4 * Real.pi / (((F.cardQuot : ℝ) * m) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) *
        (m * N) = u * (idealClassAreaConstant d b F * N) := by
    exact area_coefficient_cancel _ _ _ _ _ _ hnormI.ne' hnormF.ne' hcov.ne' hu.ne'
  rw [hmain] at h
  exact divide_area_error hu hnormI.le hK.le (Nat.cast_nonneg N) h

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassCharacterSummatory.lean` -/

section
/-!
# Square-root cancellation in weighted ideal-class counts
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

theorem weighted_common_term_error {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (A K : ι → ℝ) (C B : ℝ) (hw : ∑ i, w i = 0)
    (hA : ∀ i, |A i - C| ≤ K i * B) :
    ‖∑ i, w i * (A i : ℂ)‖ ≤ (∑ i, ‖w i‖ * K i) * B := by
  have heq : (∑ i, w i * (A i : ℂ)) = ∑ i, w i * ((A i - C : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw,
      zero_mul, sub_zero]
  rw [heq]
  calc
    _ ≤ ∑ i, ‖w i * ((A i - C : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖w i‖ * (K i * B) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hA i) (norm_nonneg _)
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

noncomputable def weightedIdealClassCount {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    (ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) → ℕ → ℂ :=
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  fun w N => ∑ C, w C * (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
    (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℂ)

theorem weightedIdealClassCount_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    ∀ w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ, (∑ C, w C) = 0 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
        ‖weightedIdealClassCount hD F w N‖ ≤ K * (Real.sqrt (N : ℝ) + 1) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro w hw
  choose K hKpos hK using idealClassArea_error hD F hF₀ hF₁
  refine ⟨∑ C, ‖w C‖ * K C, Finset.sum_nonneg (fun C _ => mul_nonneg (norm_nonneg _) (hKpos C).le), ?_⟩
  intro N
  have h := weighted_common_term_error w
    (fun C => (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
      (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ))
    K (idealClassAreaConstant d b F * N) (Real.sqrt (N : ℝ) + 1) hw (fun C => hK C N)
  simpa only [weightedIdealClassCount, Complex.ofReal_natCast] using h

theorem sqrt_error_isBigO {f : ℕ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N : ℕ, ‖f N‖ ≤ K * (Real.sqrt (N : ℝ) + 1)) :
    f =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  apply IsBigO.of_bound (2 * K)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by simpa using hNR)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), ← Real.sqrt_eq_rpow]
  exact (h N).trans (by nlinarith)

theorem idealClassCharacter_sum_zero {G : Type*} [CommGroup G] [Fintype G]
    (ψ : AddChar (Additive G) ℂ) (hψ : ψ ≠ 0) :
    (∑ C : G, ψ (Additive.ofMul C)) = 0 := by
  have hsum : (∑ C : G, ψ (Additive.ofMul C)) = ∑ C : Additive G, ψ C :=
    Fintype.sum_equiv (Additive.ofMul : G ≃ Additive G) _ _ (fun _ => rfl)
  rw [hsum]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

theorem idealClassCharacterCount_bigO {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (ClassGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      (fun N => weightedIdealClassCount hD F (fun C => ψ (Additive.ofMul C)) N)
        =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro ψ hψ
  obtain ⟨K, hK, hbound⟩ := weightedIdealClassCount_error hD F hF₀ hF₁
    (fun C => ψ (Additive.ofMul C)) (idealClassCharacter_sum_zero ψ hψ)
  exact sqrt_error_isBigO hK hbound

end Bernays

end

/-! ### Upstream module `Util/Bernays/SummatoryMellin.lean` -/

section
/-!
# Mellin continuation from a bound on summatory coefficients
-/

open Filter Topology Asymptotics MeasureTheory Set

namespace Bernays

noncomputable def realSummatory (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k

theorem realSummatory_zero_of_lt_one (f : ℕ → ℂ) {x : ℝ} (hx : x < 1) :
    realSummatory f x = 0 := by
  unfold realSummatory
  rw [Nat.floor_eq_zero.mpr hx]
  simp

theorem realSummatory_locallyIntegrable (f : ℕ → ℂ) :
    LocallyIntegrableOn (realSummatory f) (Ioi 0) := by
  have h : LocallyIntegrableOn (realSummatory f) (Ici 0) := by
    change LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) (Ici 0)
    simpa only [one_mul] using
      (locallyIntegrableOn_mul_sum_Icc f (m := 1) (a := 0) le_rfl (locallyIntegrableOn_const 1))
  exact h.mono_set Ioi_subset_Ici_self

theorem realSummatory_bigO_atTop {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r) :
    realSummatory f =O[atTop] fun x : ℝ => x ^ r := by
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
    (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))

theorem realSummatory_bigO_zero (f : ℕ → ℂ) (r : ℝ) :
    realSummatory f =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ r := by
  apply IsBigO.of_bound 0
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall] with x hx
  simp only [realSummatory_zero_of_lt_one f hx, norm_zero, zero_mul, le_refl]

noncomputable def summatoryLSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (realSummatory f) (-s)

theorem mellin_realSummatory (f : ℕ → ℂ) (s : ℂ) :
    mellin (realSummatory f) (-s) =
      ∫ t in Ioi (1 : ℝ), realSummatory f t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  simp only [smul_eq_mul]
  have hrestrict : (∫ t in Ici (1 : ℝ), (t : ℂ) ^ (-s - 1) * realSummatory f t) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) * realSummatory f t := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ici_subset_Ioi.mpr zero_lt_one)
    intro t ht
    rw [realSummatory_zero_of_lt_one f (lt_of_not_ge ht.2), mul_zero]
  rw [← hrestrict, integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [show -s - 1 = -(s + 1) by ring, mul_comm]

theorem summatoryLSeries_eq {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s) :
    summatoryLSeries f s = LSeries f s := by
  rw [summatoryLSeries, mellin_realSummatory, LSeries_eq_mul_integral f hr hs hS hO]
  rfl

theorem summatoryLSeries_differentiableAt {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) : DifferentiableAt ℂ (summatoryLSeries f) s := by
  have htop : realSummatory f =O[atTop] fun x : ℝ => x ^ (-(-r)) := by
    simpa only [neg_neg] using realSummatory_bigO_atTop hr hO
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (realSummatory_locallyIntegrable f) htop
    (show (-s).re < -r by simpa only [Complex.neg_re] using neg_lt_neg hs)
    (realSummatory_bigO_zero f (-((-s).re - 1))) (show (-s).re - 1 < (-s).re by linarith)
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassLSeries.lean` -/

section
/-!
# Analytic continuation of nontrivial quadratic ideal-class series
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

noncomputable def weightedIdealNormCoeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    (ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) → ℕ → ℂ :=
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  fun w n => ∑ C, w C * (idealClassNormCount C F n : ℂ)

theorem weightedIdealNormCoeff_cumsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, weightedIdealNormCoeff hD F w n) =
        weightedIdealClassCount hD F w N := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro w N
  unfold weightedIdealNormCoeff weightedIdealClassCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.mul_sum, ← Nat.cast_sum, idealClassNormCount_cumsum hD]

theorem weightedIdealNormCoeff_norm_cumsum_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖) ≤
        ∑ C, ‖w C‖ * (Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro w N
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ C, ‖w C‖ * (idealClassNormCount C F n : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [weightedIdealNormCoeff, norm_mul, Complex.norm_natCast] using
        norm_sum_le (s := Finset.univ) (f := fun C => w C * (idealClassNormCount C F n : ℂ))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.mul_sum, ← Nat.cast_sum, idealClassNormCount_cumsum hD]

theorem weightedIdealNormCoeff_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (s : ℂ), 1 < s.re →
      LSeriesSummable (weightedIdealNormCoeff hD F w) s := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro w s hs
  obtain ⟨B, _, hB⟩ := exists_uniform_natCard_idealClassBall_le hD
  have hle (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N : ℕ) :
      Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
        (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) ≤ B * N := by
    letI := finite_idealClassBall hD C N
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (hB C N)
  have hsum (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖) ≤
      (∑ C, ‖w C‖ * B) * N := by
    apply (weightedIdealNormCoeff_norm_cumsum_le hD F w N).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro C _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact_mod_cast hle C N
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖weightedIdealNormCoeff hD F w n‖)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 : ℝ) := by
    apply IsBigO.of_bound (∑ C, ‖w C‖ * B)
    exact Filter.Eventually.of_forall (fun N => by
      rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      exact hsum N)
  exact LSeriesSummable_of_sum_norm_bigO hO zero_le_one hs

theorem classCharacterLSeries_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (ClassGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ G : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ G s) ∧
        (∀ s : ℂ, 1 < s.re → G s =
          LSeries (weightedIdealNormCoeff hD F (fun C => ψ (Additive.ofMul C))) s) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  let a := weightedIdealNormCoeff hD F (fun C => ψ (Additive.ofMul C))
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [a, weightedIdealNormCoeff_cumsum] using idealClassCharacterCount_bigO hD F hF₀ hF₁ ψ hψ
  refine ⟨summatoryLSeries a, ?_, ?_⟩
  · intro s hs
    exact summatoryLSeries_differentiableAt (by norm_num) hO hs
  · intro s hs
    exact summatoryLSeries_eq (by norm_num) hO (by linarith)
      (weightedIdealNormCoeff_summable hD F _ s hs)

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusNorms.lean` -/

section
/-!
# The genus of an ideal norm

For ideals coprime to the discriminant, the class modulo squares is determined
by the natural norm. This is a factorization statement and does not invoke the
principal genus theorem or a prime-distribution assumption.
-/

namespace Bernays

abbrev GenusGroup (R : Type*) [CommRing R] [IsDomain R] :=
  ClassGroup R ⧸ (classSquareSubgroup : Subgroup (ClassGroup R))

noncomputable def genusMap {R : Type*} [CommRing R] [IsDomain R] : ClassGroup R →* GenusGroup R :=
  QuotientGroup.mk' classSquareSubgroup

theorem genusMap_inv_eq {R : Type*} [CommRing R] [IsDomain R] (x : ClassGroup R) :
    genusMap x⁻¹ = genusMap x := by
  change QuotientGroup.mk x⁻¹ = QuotientGroup.mk x
  rw [QuotientGroup.eq_iff_div_mem]
  exact ⟨x⁻¹, by simp [div_eq_mul_inv, pow_two]⟩

theorem genusGroup_sq {R : Type*} [CommRing R] [IsDomain R] (x : GenusGroup R) : x ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective classSquareSubgroup x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (classSquare_mem y)

noncomputable def primeGenus {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ℕ → GenusGroup (QuadraticAlgebra ℤ d b) := by
  classical
  letI := quadraticOrderIsDomain hD
  exact fun q => if h : ∃ s : SplitPrime d b, s.1 = q then genusMap (h.choose.idealClass hD) else 1

theorem primeGenus_split {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    primeGenus hD s.1 = genusMap (s.idealClass hD) := by
  classical
  letI := quadraticOrderIsDomain hD
  have hex : ∃ t : SplitPrime d b, t.1 = s.1 := ⟨s, rfl⟩
  have heq : hex.choose = s := Subtype.ext hex.choose_spec
  simp only [primeGenus, dif_pos hex, heq]

noncomputable def genusValue {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ℕ → GenusGroup (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  fun n => n.factorization.prod (fun q e => primeGenus hD q ^ e)

theorem genusValue_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    genusValue hD 1 = 1 := by
  simp [genusValue]

theorem genusValue_mul {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    letI := quadraticOrderIsDomain hD
    genusValue hD (m * n) = genusValue hD m * genusValue hD n := by
  letI := quadraticOrderIsDomain hD
  rw [genusValue, Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem genusValue_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    genusValue hD (p ^ e) = primeGenus hD p ^ e := by
  letI := quadraticOrderIsDomain hD
  rw [genusValue, hp.factorization_pow, Finsupp.prod_single_index]
  exact pow_zero _

theorem genusValue_goodMaximal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      genusValue hD (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = genusMap P.idealClass := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, _, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1, h.2.2, map_one, genusValue_primePower hD hq, genusGroup_sq]
  · rw [s.ideal_cardQuot hD ε]
    have hprime : genusValue hD s.1 = genusMap (s.idealClass hD) := by
      have h := genusValue_primePower hD s.2.1 1
      simpa only [pow_one, primeGenus_split] using h
    rw [hprime]
    cases ε
    · rfl
    · rw [s.idealClass_conjugate hD, genusMap_inv_eq]

theorem genusValue_goodIdeal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      genusValue hD (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = genusMap I.idealClass := by
  letI := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [Submodule.cardQuot_top, genusValue_one]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul, genusValue_mul hD P.cardQuot_pos l.prod.cardQuot_pos,
      InvertibleIdeal.idealClass_mul, map_mul]
    have hhead := hP P List.mem_cons_self
    rw [genusValue_goodMaximal_norm hD P hhead.1 hhead.2,
      ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ))]

end Bernays

end

/-! ### Upstream module `Util/Bernays/NormClassPartition.lean` -/

section
/-!
# The genus-character weight is constant on an ideal norm fiber
-/

open scoped Classical

namespace Bernays

def idealNormClassFiberEquiv {R : Type*} [CommRing R] [IsDomain R]
    (F : Ideal R) (n : ℕ) (C : ClassGroup R) :
    {I : GoodIdealNormFiber F n // I.1.idealClass = C} ≃
      {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot = n} where
  toFun I := ⟨⟨I.1.1, I.2, I.1.2.2⟩, I.1.2.1⟩
  invFun I := ⟨⟨I.1.1, I.2, I.1.2.2⟩, I.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealClassNormCount_sum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    letI := quadraticOrderClassGroupFintype hD
    (∑ C, idealClassNormCount C F n) = Nat.card (GoodIdealNormFiber F n) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI := finite_goodIdealNormFiber hD F n
  have hsum : (∑ C, idealClassNormCount C F n) =
      ∑ C, Nat.card {I : GoodIdealNormFiber F n // I.1.idealClass = C} := by
    apply Finset.sum_congr rfl
    intro C _
    exact (Nat.card_congr (idealNormClassFiberEquiv F n C)).symm
  rw [hsum, ← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun I : GoodIdealNormFiber F n => I.1.idealClass))

theorem weightedIdealNormCoeff_eq_const {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ (w : ClassGroup (QuadraticAlgebra ℤ d b) → ℂ) (a : ℂ),
      (∀ I : GoodIdealNormFiber F n, w I.1.idealClass = a) →
      weightedIdealNormCoeff hD F w n = a * (Nat.card (GoodIdealNormFiber F n) : ℂ) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro w a hw
  unfold weightedIdealNormCoeff
  rw [← idealClassNormCount_sum hD F n, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h : Nonempty {I : CoprimeIdealsInClass (QuadraticAlgebra ℤ d b) C F //
      (I.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n}
  · obtain ⟨I⟩ := h
    have hwa := hw ⟨I.1.1, I.2, I.1.2.2⟩
    rw [I.1.2.1] at hwa
    rw [hwa]
  · haveI : IsEmpty {I : CoprimeIdealsInClass (QuadraticAlgebra ℤ d b) C F //
        (I.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n} := not_nonempty_iff.mp h
    have hz : idealClassNormCount C F n = 0 := by simp [idealClassNormCount]
    simp only [hz, Nat.cast_zero, mul_zero]

theorem genusWeightedIdealNormCoeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (n : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      weightedIdealNormCoeff hD (quadraticBadIdeal d b)
        (fun C => ψ (Additive.ofMul (genusMap C))) n =
      ψ (Additive.ofMul (genusValue hD n)) *
        (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ) := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  apply weightedIdealNormCoeff_eq_const hD
  intro I
  rw [← genusValue_goodIdeal_norm hD I.1 I.2.2, I.2.1]

end Bernays

end

/-! ### Upstream module `Util/Bernays/PrimeSupportIndicator.lean` -/

section
/-!
# Multiplicative indicators supported on a prescribed set of primes
-/

open scoped Classical

namespace Bernays

def PrimeSupported (S : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → S p

theorem primeSupported_one (S : ℕ → Prop) : PrimeSupported S 1 := by
  intro p hp hdiv
  exact False.elim (hp.not_dvd_one hdiv)

theorem primeSupported_mul_iff (S : ℕ → Prop) (m n : ℕ) :
    PrimeSupported S (m * n) ↔ PrimeSupported S m ∧ PrimeSupported S n := by
  constructor
  · intro h
    exact ⟨fun p hp hd => h p hp (hd.trans (dvd_mul_right m n)),
      fun p hp hd => h p hp (hd.trans (dvd_mul_left n m))⟩
  · rintro ⟨hm, hn⟩ p hp hd
    exact (hp.dvd_mul.mp hd).elim (hm p hp) (hn p hp)

noncomputable def primeSupportAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  ⟨fun n => if 0 < n ∧ PrimeSupported S n then 1 else 0, by simp⟩

theorem primeSupportAF_isMultiplicative (S : ℕ → Prop) : (primeSupportAF S).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [primeSupportAF, primeSupported_one]
  · intro m n hm hn _
    simp only [primeSupportAF, ArithmeticFunction.coe_mk, Nat.pos_iff_ne_zero, hm, hn,
      mul_ne_zero hm hn, true_and, primeSupported_mul_iff]
    by_cases h₁ : PrimeSupported S m <;> by_cases h₂ : PrimeSupported S n <;> simp [h₁, h₂, hm, hn]

theorem primeSupportAF_primePower (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    primeSupportAF S (p ^ e) = if S p then 1 else 0 := by
  have hs : PrimeSupported S (p ^ e) ↔ S p := by
    constructor
    · exact fun h => h p hp (dvd_pow_self p he.ne')
    · intro h q hq hdiv
      have hqp := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdiv)
      exact hqp ▸ h
  simp only [primeSupportAF, ArithmeticFunction.coe_mk, pow_pos hp.pos e, true_and, hs]

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareSupportArithmetic.lean` -/

section
/-!
# The arithmetic function supported on inert-prime squares
-/

open scoped Classical

namespace Bernays

noncomputable def localParityAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  ⟨fun n => (localParity S n : ℂ), by simp⟩

theorem localParityAF_isMultiplicative (S : ℕ → Prop) : (localParityAF S).IsMultiplicative := by
  constructor
  · simp [localParityAF]
  · intro m n hmn
    change (localParity S (m * n) : ℂ) = (localParity S m : ℂ) * (localParity S n : ℂ)
    rw [localParity_mul S hmn, Complex.ofReal_mul]

theorem parity_all_primes_isSquare {n : ℕ} (hn : 0 < n)
    (h : ParityAdmissible (fun _ => True) n) : ∃ k : ℕ, k ^ 2 = n := by
  let k := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  refine ⟨k, ?_⟩
  conv_rhs => rw [n.prod_primeFactors_pow_factorization hn.ne']
  dsimp only [k]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have heven : Even (n.factorization p) := by
    rw [n.factorization_def hprime]
    exact h p hprime trivial
  rw [← pow_mul]
  congr 1
  obtain ⟨j, hj⟩ := heven
  omega

noncomputable def squareSupportAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  (localParityAF (fun _ => True)).pmul (primeSupportAF S)

theorem squareSupportAF_isMultiplicative (S : ℕ → Prop) : (squareSupportAF S).IsMultiplicative :=
  (localParityAF_isMultiplicative _).pmul (primeSupportAF_isMultiplicative S)

theorem squareSupportAF_eq (S : ℕ → Prop) (n : ℕ) :
    squareSupportAF S n =
      if 0 < n ∧ ParityAdmissible (fun _ => True) n ∧ PrimeSupported S n then 1 else 0 := by
  rw [squareSupportAF, ArithmeticFunction.pmul_apply]
  change (localParity (fun _ => True) n : ℂ) *
    (if 0 < n ∧ PrimeSupported S n then (1 : ℂ) else 0) = _
  rw [localParity]
  split_ifs <;> simp_all

theorem squareSupportAF_primePower (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    squareSupportAF S (p ^ e) = if S p ∧ Even e then 1 else 0 := by
  rw [squareSupportAF, ArithmeticFunction.pmul_apply, primeSupportAF_primePower S hp he]
  change (localParity (fun _ => True) (p ^ e) : ℂ) * (if S p then 1 else 0) = _
  rw [localParity_prime_pow _ hp]
  by_cases hS : S p <;> by_cases hE : Even e <;>
    simp [hS, hE, Nat.not_odd_iff_even, ← Nat.not_even_iff_odd]

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodNormArithmetic.lean` -/

section
/-!
# Arithmetic functions for good norms and their genus twists
-/

open scoped Classical

namespace Bernays

noncomputable def coprimeAF (M : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if 0 < n ∧ n.Coprime M then 1 else 0, by simp⟩

theorem coprimeAF_isMultiplicative (M : ℕ) : (coprimeAF M).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [coprimeAF]
  · intro m n hm hn _
    change (if 0 < m * n ∧ (m * n).Coprime M then (1 : ℂ) else 0) =
      (if 0 < m ∧ m.Coprime M then 1 else 0) * (if 0 < n ∧ n.Coprime M then 1 else 0)
    simp only [Nat.pos_iff_ne_zero, mul_ne_zero hm hn, hm, hn, true_and, Nat.coprime_mul_iff_left]
    split_ifs <;> simp_all

theorem coprimeAF_primePower (M : ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    coprimeAF M (p ^ e) = if p.Coprime M then 1 else 0 := by
  simp only [coprimeAF, ArithmeticFunction.coe_mk, pow_pos hp.pos e, true_and,
    Nat.coprime_pow_left_iff he]

noncomputable def goodIdealNormAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  ⟨fun n => (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ), by
    rw [goodIdealNormFiber_card_zero hD, Nat.cast_zero]⟩

theorem goodIdealNormAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    (goodIdealNormAF hD).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  constructor
  · change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) 1) : ℂ) = 1
    rw [goodIdealNormFiber_card_one hD, Nat.cast_one]
  · intro m n hc
    change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (m * n)) : ℂ) =
      (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) m) : ℂ) *
        (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ)
    rw [goodIdealNormFiber_card_mul hD _ m n hc, Nat.cast_mul]

noncomputable def genusWeightAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => ⟨fun n => if n = 0 then 0 else ψ (Additive.ofMul (genusValue hD n)), by simp⟩

theorem genusWeightAF_apply {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, n ≠ 0 → genusWeightAF hD ψ n = ψ (Additive.ofMul (genusValue hD n)) := by
  letI := quadraticOrderIsDomain hD
  intro ψ n hn
  simp only [genusWeightAF, ArithmeticFunction.coe_mk, if_neg hn]

theorem genusWeightAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusWeightAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · rw [genusWeightAF_apply hD ψ 1 (by decide), genusValue_one]
    exact ψ.map_zero_eq_one
  · intro m n hm hn _
    rw [genusWeightAF_apply hD ψ _ (mul_ne_zero hm hn), genusWeightAF_apply hD ψ m hm,
      genusWeightAF_apply hD ψ n hn, genusValue_mul hD (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn),
      ofMul_mul, AddChar.map_add_eq_mul]

theorem genusWeightAF_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → ∀ e : ℕ,
      genusWeightAF hD ψ (p ^ e) = ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp e
  rw [genusWeightAF_apply hD ψ _ (pow_ne_zero _ hp.ne_zero), genusValue_primePower hD hp,
    ofMul_pow, AddChar.map_nsmul_eq_pow]

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusCharacters.lean` -/

section
/-!
# Genus characters and their pullbacks to the ideal class group
-/

namespace Bernays

noncomputable def genusClassChar {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) : AddChar (Additive (ClassGroup R)) ℂ :=
  ψ.compAddMonoidHom (genusMap (R := R)).toAdditive

theorem genusClassChar_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (hψ : ψ ≠ 0) : genusClassChar ψ ≠ 0 := by
  have hsurj : Function.Surjective (genusMap (R := R)).toAdditive := by
    intro x
    obtain ⟨C, hC⟩ := QuotientGroup.mk'_surjective classSquareSubgroup x.toMul
    exact ⟨Additive.ofMul C, congrArg Additive.ofMul hC⟩
  intro h
  apply hψ
  apply AddChar.compAddMonoidHom_injective_left _ hsurj
  have hz : (0 : AddChar (Additive (GenusGroup R)) ℂ).compAddMonoidHom
      (genusMap (R := R)).toAdditive = 0 := by
    ext C
    rfl
  exact h.trans hz.symm

theorem genusChar_sq {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (g : GenusGroup R) :
    ψ (Additive.ofMul g) ^ 2 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, ← ofMul_pow, genusGroup_sq]
  exact ψ.map_zero_eq_one

theorem genusChar_norm {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (g : GenusGroup R) :
    ‖ψ (Additive.ofMul g)‖ = 1 := by
  have h := congrArg norm (genusChar_sq ψ g)
  rw [norm_pow, norm_one] at h
  nlinarith [norm_nonneg (ψ (Additive.ofMul g))]

theorem quadraticBadIdeal_cardQuot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    (quadraticBadIdeal d b).cardQuot = discriminantLevel (b ^ 2 + 4 * d) ^ 2 :=
  principal_nat_cardQuot hD (discriminantLevel_pos hD.ne)

theorem quadraticBadIdeal_ne_bot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    quadraticBadIdeal d b ≠ ⊥ := by
  rw [quadraticBadIdeal, ne_eq, Ideal.span_singleton_eq_bot]
  exact quadratic_natCast_ne_zero (discriminantLevel_pos hD.ne)

theorem quadraticBadIdeal_ne_top {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    quadraticBadIdeal d b ≠ ⊤ := by
  intro h
  have hnorm := quadraticBadIdeal_cardQuot hD
  rw [h, Submodule.cardQuot_top] at hnorm
  have hp := discriminantLevel_one_lt hD.ne
  nlinarith

theorem genusIdealLSeries_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ G : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ G s) ∧
        (∀ s : ℂ, 1 < s.re → G s = LSeries
          (weightedIdealNormCoeff hD (quadraticBadIdeal d b)
            (fun C => ψ (Additive.ofMul (genusMap C)))) s) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  exact classCharacterLSeries_continuation hD (quadraticBadIdeal d b)
    (quadraticBadIdeal_ne_bot hD) (quadraticBadIdeal_ne_top hD)
    (genusClassChar ψ) (genusClassChar_ne_zero ψ hψ)

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodNormPrimePowers.lean` -/

section
/-!
# Local coefficients of the good ideal counting series
-/

namespace Bernays

theorem discriminantCharacter_eq_zero_of_not_coprime {D : ℤ} (hD : D ≠ 0)
    {n : ℕ} (hn : ¬ n.Coprime (discriminantLevel D)) : discriminantCharacter D hD n = 0 :=
  MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n _).not.mpr hn)

theorem exists_splitPrime_of_coprime_not_inert {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p ≠ -1) :
    ∃ s : SplitPrime d b, s.1 = p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hc).mpr hχ
  have hpd : ¬ (p : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
      (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
    exact (hp.coprime_iff_not_dvd.mp hc) hdvd
  exact ⟨⟨p, hp, hpd, r, hr⟩, rfl⟩

theorem goodIdealNormAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    goodIdealNormAF hD (s.1 ^ e) = (e + 1 : ℕ) := by
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e)) : ℂ) = _
  rw [s.normPower_card hD hc e]

theorem goodIdealNormAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    goodIdealNormAF hD (p ^ e) = if Even e then 1 else 0 := by
  classical
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) : ℂ) = _
  rw [inert_normPower_card hD hp hc hχ e]
  split_ifs <;> simp

theorem goodIdealNormAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hc : ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    {e : ℕ} (he : 0 < e) : goodIdealNormAF hD (p ^ e) = 0 := by
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) : ℂ) = 0
  rw [goodIdealNormFiber_card_eq_zero_of_not_coprime hD (p ^ e)
    ((Nat.coprime_pow_left_iff he _ _).not.mpr hc), Nat.cast_zero]

end Bernays

end

/-! ### Upstream module `Util/Bernays/PrimePowerConvolution.lean` -/

section
/-!
# Local convolution identities for a square-root Euler factor
-/

open scoped Classical

namespace Bernays

theorem arithmetic_mul_primePower (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (f * g) (p ^ e) = ∑ k ∈ Finset.range (e + 1), f (p ^ k) * g (p ^ (e - k)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => f i * g j), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.pow_div (by have := Finset.mem_range.mp hk; omega) hp.pos]

theorem arithmetic_mul_primePower_geometric (f : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (a : ℂ) (hf : ∀ k : ℕ, f (p ^ k) = a ^ k) (e : ℕ) :
    (f * f) (p ^ e) = (e + 1 : ℕ) * a ^ e := by
  rw [arithmetic_mul_primePower f f hp]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (e + 1)) : f (p ^ k) * f (p ^ (e - k)) = a ^ e := by
    rw [hf, hf, ← pow_add, Nat.add_sub_of_le (by have := Finset.mem_range.mp hk; omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem arithmetic_mul_primePower_delta (f g : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (hg : ∀ k : ℕ, g (p ^ k) = if k = 0 then 1 else 0) (e : ℕ) :
    (f * g) (p ^ e) = f (p ^ e) := by
  rw [arithmetic_mul_primePower f g hp]
  rw [Finset.sum_eq_single e]
  · rw [Nat.sub_self, hg, if_pos rfl, mul_one]
  · intro k hk hke
    have hk₀ : e - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    rw [hg, if_neg hk₀, mul_zero]
  · intro he
    exact False.elim (he (Finset.mem_range.mpr (Nat.lt_succ_self e)))

theorem pow_even_eq_one_of_sq_eq_one {a : ℂ} (ha : a ^ 2 = 1) {e : ℕ} (he : Even e) :
    a ^ e = 1 := by
  obtain ⟨k, hk⟩ := he
  rw [hk, ← two_mul, pow_mul, ha, one_pow]

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusTwistedArithmetic.lean` -/

section
/-!
# Genus twists of the local norm indicator and ideal coefficients
-/

open scoped Classical

namespace Bernays

noncomputable def genusLocalAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => ((localParityAF (fun p => discriminantCharacter _ hD.ne p = -1)).pmul
    (coprimeAF (discriminantLevel (b ^ 2 + 4 * d)))).pmul (genusWeightAF hD ψ)

noncomputable def genusIdealAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => (goodIdealNormAF hD).pmul (genusWeightAF hD ψ)

theorem genusLocalAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusLocalAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  exact ((localParityAF_isMultiplicative _).pmul (coprimeAF_isMultiplicative _)).pmul
    (genusWeightAF_isMultiplicative hD ψ)

theorem genusIdealAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusIdealAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  exact (goodIdealNormAF_isMultiplicative hD).pmul (genusWeightAF_isMultiplicative hD ψ)

theorem genusIdealAF_eq_coeff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      ⇑(genusIdealAF hD ψ) = weightedIdealNormCoeff hD (quadraticBadIdeal d b)
        (fun C => ψ (Additive.ofMul (genusMap C))) := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  funext n
  rw [genusWeightedIdealNormCoeff hD]
  by_cases hn : n = 0
  · subst n
    rw [ArithmeticFunction.map_zero, goodIdealNormFiber_card_zero hD, Nat.cast_zero, mul_zero]
  · rw [genusIdealAF, ArithmeticFunction.pmul_apply, genusWeightAF_apply hD ψ n hn]
    exact mul_comm _ _

theorem genusLocalAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p ≠ -1 → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, pow_zero]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_primePower hD ψ p hp e, coprimeAF_primePower _ hp he, if_pos hc]
    change (localParity _ (p ^ e) : ℂ) * 1 * _ = _
    rw [localParity_prime_pow _ hp]
    simp only [hχ, false_and, ↓reduceIte, Complex.ofReal_one, one_mul]

theorem genusIdealAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p ≠ -1 → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = (e + 1 : ℕ) * ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  obtain ⟨s, hs⟩ := exists_splitPrime_of_coprime_not_inert hD hp hc hχ
  have hnorm : goodIdealNormAF hD (p ^ e) = (e + 1 : ℕ) := by
    rw [← hs]
    exact goodIdealNormAF_split_primePower hD s (hs.symm ▸ hc) e
  rw [genusIdealAF, ArithmeticFunction.pmul_apply, hnorm, genusWeightAF_primePower hD ψ p hp e]

theorem genusLocalAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p = -1 → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = if Even e then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, if_pos Even.zero]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_primePower hD ψ p hp e, coprimeAF_primePower _ hp he, if_pos hc]
    change (localParity _ (p ^ e) : ℂ) * 1 * _ = _
    rw [localParity_prime_pow _ hp]
    by_cases hE : Even e
    · rw [if_neg (by simpa only [hχ, true_and] using Nat.not_odd_iff_even.mpr hE),
        if_pos hE, Complex.ofReal_one, one_mul, one_mul]
      exact pow_even_eq_one_of_sq_eq_one (genusChar_sq ψ _) hE
    · simp only [hχ, true_and, Nat.not_even_iff_odd.mp hE, ↓reduceIte, Complex.ofReal_zero,
        zero_mul, hE]

theorem genusIdealAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      discriminantCharacter _ hD.ne p = -1 → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = if Even e then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc hχ e
  rw [genusIdealAF, ArithmeticFunction.pmul_apply, goodIdealNormAF_inert_primePower hD hp hc hχ,
    genusWeightAF_primePower hD ψ p hp e]
  by_cases hE : Even e
  · rw [if_pos hE, one_mul]
    exact pow_even_eq_one_of_sq_eq_one (genusChar_sq ψ _) hE
  · rw [if_neg hE, zero_mul]

theorem genusLocalAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) → ∀ e : ℕ,
      genusLocalAF hD ψ (p ^ e) = if e = 0 then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp hc e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusLocalAF_isMultiplicative hD ψ).1, if_pos rfl]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      coprimeAF_primePower _ hp he, if_neg hc, mul_zero, zero_mul, if_neg he.ne']

theorem genusIdealAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) → ∀ e : ℕ,
      genusIdealAF hD ψ (p ^ e) = if e = 0 then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hc e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (genusIdealAF_isMultiplicative hD ψ).1, if_pos rfl]
  · rw [genusIdealAF, ArithmeticFunction.pmul_apply,
      goodIdealNormAF_bad_primePower hD hc he, zero_mul, if_neg he.ne']

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusSquareConvolution.lean` -/

section
/-!
# The convolution square of a genus-twisted norm indicator

The square correction is supported exactly on squares of inert-prime products.
-/

open scoped Classical

namespace Bernays

theorem squareSupportAF_primePower_of_not {S : ℕ → Prop} {p : ℕ} (hp : p.Prime)
    (hS : ¬ S p) (e : ℕ) :
    squareSupportAF S (p ^ e) = if e = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (squareSupportAF_isMultiplicative S).1, if_pos rfl]
  · rw [squareSupportAF_primePower S hp he, if_neg (not_and.mpr (fun h => False.elim (hS h))),
      if_neg he.ne']

theorem squareSupportAF_primePower_of_mem {S : ℕ → Prop} {p : ℕ} (hp : p.Prime)
    (hS : S p) (e : ℕ) :
    squareSupportAF S (p ^ e) = if Even e then 1 else 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, (squareSupportAF_isMultiplicative S).1, if_pos Even.zero]
  · rw [squareSupportAF_primePower S hp he]
    simp only [hS, true_and]

theorem arithmetic_mul_primePower_congr (f g u v : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (hfu : ∀ e : ℕ, f (p ^ e) = u (p ^ e))
    (hgv : ∀ e : ℕ, g (p ^ e) = v (p ^ e)) (e : ℕ) :
    (f * g) (p ^ e) = (u * v) (p ^ e) := by
  rw [arithmetic_mul_primePower f g hp, arithmetic_mul_primePower u v hp]
  exact Finset.sum_congr rfl (fun k _ => by rw [hfu, hgv])

theorem genusLocalAF_square {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      genusLocalAF hD ψ * genusLocalAF hD ψ =
        genusIdealAF hD ψ * squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1) := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  let f := genusLocalAF hD ψ
  let a := genusIdealAF hD ψ
  let H := squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)
  have hf : f.IsMultiplicative := genusLocalAF_isMultiplicative hD ψ
  have ha : a.IsMultiplicative := genusIdealAF_isMultiplicative hD ψ
  have hH : H.IsMultiplicative := squareSupportAF_isMultiplicative _
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (f * f) (hf.mul hf)
    (a * H) (ha.mul hH)).mpr
  intro p e hp
  by_cases hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d))
  · by_cases hχ : discriminantCharacter _ hD.ne p = -1
    · apply arithmetic_mul_primePower_congr f f a H hp
      · intro k
        exact (genusLocalAF_inert_primePower hD ψ p hp hc hχ k).trans
          (genusIdealAF_inert_primePower hD ψ p hp hc hχ k).symm
      · intro k
        exact (genusLocalAF_inert_primePower hD ψ p hp hc hχ k).trans
          (squareSupportAF_primePower_of_mem hp hχ k).symm
    · rw [arithmetic_mul_primePower_geometric f hp _
        (genusLocalAF_split_primePower hD ψ p hp hc hχ),
        arithmetic_mul_primePower_delta a H hp (squareSupportAF_primePower_of_not hp hχ)]
      exact (genusIdealAF_split_primePower hD ψ p hp hc hχ e).symm
  · have hχ : discriminantCharacter _ hD.ne p ≠ -1 := by
      rw [discriminantCharacter_eq_zero_of_not_coprime hD.ne hc]
      norm_num
    apply arithmetic_mul_primePower_congr f f a H hp
    · intro k
      exact (genusLocalAF_bad_primePower hD ψ p hp hc k).trans
        (genusIdealAF_bad_primePower hD ψ p hc k).symm
    · intro k
      exact (genusLocalAF_bad_primePower hD ψ p hp hc k).trans
        (squareSupportAF_primePower_of_not hp hχ k).symm

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareCorrectionSeries.lean` -/

section
/-!
# Absolute convergence of the square-support correction on `re s > 1/2`
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

theorem squareSupportAF_norm_cumsum_le (S : ℕ → Prop) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖) ≤ Real.sqrt (N : ℝ) + 1 := by
  let P : ℕ → Prop := fun n => 0 < n ∧ ParityAdmissible (fun _ => True) n ∧ PrimeSupported S n
  let T := (Finset.Icc 1 N).filter P
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖) = (T.card : ℝ) := by
    have hnorm (n : ℕ) : ‖squareSupportAF S n‖ = if P n then (1 : ℝ) else 0 := by
      rw [squareSupportAF_eq]
      change ‖if P n then (1 : ℂ) else 0‖ = _
      split_ifs <;> simp
    simp_rw [hnorm]
    convert Finset.sum_boole (R := ℝ) P (Finset.Icc 1 N) using 1 <;> congr
  have hsquare (n : ℕ) (hn : n ∈ T) : Nat.sqrt n ^ 2 = n := by
    have hp := (Finset.mem_filter.mp hn).2
    exact (Nat.exists_mul_self' n).mp (parity_all_primes_isSquare hp.1 hp.2.1)
  have hinj : Set.InjOn Nat.sqrt T := by
    intro n hn m hm hnm
    exact (hsquare n hn).symm.trans ((congrArg (fun k : ℕ => k ^ 2) hnm).trans (hsquare m hm))
  have hsub : T.image Nat.sqrt ⊆ Finset.range (Nat.sqrt N + 1) := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.sqrt_le_sqrt (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2))
  have hcard : T.card ≤ Nat.sqrt N + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    exact_mod_cast Nat.sqrt_le' N
  rw [hsum]
  have hc : (T.card : ℝ) ≤ Nat.sqrt N + 1 := by exact_mod_cast hcard
  linarith

theorem squareSupportAF_summable (S : ℕ → Prop) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    LSeriesSummable (squareSupportAF S) s := by
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr
      exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), ← Real.sqrt_eq_rpow]
    exact (squareSupportAF_norm_cumsum_le S N).trans (by linarith)
  exact LSeriesSummable_of_sum_norm_bigO hO (by norm_num) hs

theorem squareSupportLSeries_differentiableAt (S : ℕ → Prop) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) : DifferentiableAt ℂ (LSeries (squareSupportAF S)) s := by
  have hab : LSeries.abscissaOfAbsConv (squareSupportAF S) ≤ (1 / 2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun x hx =>
      squareSupportAF_summable S (by simpa only [Complex.ofReal_re] using hx))
  exact (LSeries_hasDerivAt (hab.trans_lt (by exact_mod_cast hs))).differentiableAt

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusSquareSeries.lean` -/

section
/-!
# Analytic continuation of the square of a nontrivial genus series
-/

open scoped Classical

namespace Bernays

theorem genusLocalAF_apply {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, genusLocalAF hD ψ n =
      if 0 < n ∧ ParityAdmissible (fun p => discriminantCharacter _ hD.ne p = -1) n ∧
        n.Coprime (discriminantLevel (b ^ 2 + 4 * d))
      then ψ (Additive.ofMul (genusValue hD n)) else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, lt_self_iff_false, false_and, ↓reduceIte]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_apply hD ψ n hn]
    change (localParity _ n : ℂ) * (if 0 < n ∧ n.Coprime _ then 1 else 0) * _ = _
    rw [localParity]
    split_ifs <;> simp_all

theorem genusLocalAF_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, ‖genusLocalAF hD ψ n‖ =
      if 0 < n ∧ ParityAdmissible (fun p => discriminantCharacter _ hD.ne p = -1) n ∧
        n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ n
  rw [genusLocalAF_apply]
  split_ifs
  · exact genusChar_norm ψ _
  · exact norm_zero

theorem genusLocalAF_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (genusLocalAF hD ψ) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  apply LSeriesSummable_of_le_const_mul_rpow hs
  refine ⟨1, fun n _ => ?_⟩
  rw [genusLocalAF_norm]
  norm_num only [sub_self, Real.rpow_zero, mul_one]
  split_ifs <;> norm_num

theorem genusIdealAF_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (genusIdealAF hD ψ) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  rw [genusIdealAF_eq_coeff]
  exact weightedIdealNormCoeff_summable hD (quadraticBadIdeal d b) _ s hs

theorem genusLocalLSeries_square {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re →
      LSeries (genusLocalAF hD ψ) s ^ 2 = LSeries (genusIdealAF hD ψ) s *
        LSeries (squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  rw [pow_two, ← ArithmeticFunction.LSeries_mul' (genusLocalAF_summable hD ψ s hs)
    (genusLocalAF_summable hD ψ s hs), genusLocalAF_square,
    ArithmeticFunction.LSeries_mul' (genusIdealAF_summable hD ψ s hs)
      (squareSupportAF_summable _ (by linarith))]

theorem genusLocalLSeries_square_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ F : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s) ∧
        (∀ s : ℂ, 1 < s.re → F s = LSeries (genusLocalAF hD ψ) s ^ 2) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  obtain ⟨G, hG, hGeq⟩ := genusIdealLSeries_continuation hD ψ hψ
  let H := squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)
  refine ⟨fun s => G s * LSeries H s, ?_, ?_⟩
  · intro s hs
    exact (hG s hs).mul (squareSupportLSeries_differentiableAt _ hs)
  · intro s hs
    dsimp only
    rw [hGeq s hs, genusLocalLSeries_square hD ψ s hs, genusIdealAF_eq_coeff]

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusSeriesNonzero.lean` -/

section
/-!
# The continued genus-series square is not identically zero
-/

open Filter Topology

namespace Bernays

theorem LSeries_exists_ne_zero_of_coeff_one {a : ℕ → ℂ} (ha : a 1 ≠ 0)
    (hs : LSeriesSummable a (2 : ℂ)) : ∃ x : ℝ, 1 < x ∧ LSeries a x ≠ 0 := by
  by_contra! h
  have hevent : (fun x : ℝ => LSeries a x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact h x hx
  have halt : LSeries.abscissaOfAbsConv a ≠ ⊤ := by
    intro htop
    have hb := hs.abscissaOfAbsConv_le
    rw [htop] at hb
    norm_num at hb
  exact ha ((LSeries_eventually_eq_zero_iff'.mp hevent).resolve_right halt 1 (by decide))

theorem genusLocalLSeries_differentiableAt {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries (genusLocalAF hD ψ)) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  have hab : LSeries.abscissaOfAbsConv (genusLocalAF hD ψ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun x hx =>
      genusLocalAF_summable hD ψ x (by simpa only [Complex.ofReal_re] using hx))
  exact (LSeries_hasDerivAt (hab.trans_lt (by exact_mod_cast hs))).differentiableAt

theorem genusLocalLSeries_continuation_nonzero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ F : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s) ∧
        (∀ s : ℂ, 1 < s.re → F s = LSeries (genusLocalAF hD ψ) s ^ 2) ∧
        (∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  obtain ⟨F, hF, heq⟩ := genusLocalLSeries_square_continuation hD ψ hψ
  have ha : genusLocalAF hD ψ 1 ≠ 0 := by
    rw [(genusLocalAF_isMultiplicative hD ψ).1]
    exact one_ne_zero
  obtain ⟨x, hx, hxne⟩ := LSeries_exists_ne_zero_of_coeff_one ha
    (genusLocalAF_summable hD ψ 2 (by norm_num))
  refine ⟨F, hF, heq, x, by simpa only [Complex.ofReal_re] using (by linarith : (1 / 2 : ℝ) < x), ?_⟩
  rw [heq x (by simpa only [Complex.ofReal_re] using hx)]
  exact pow_ne_zero _ hxne

end Bernays

end

/-! ### Upstream module `Util/Bernays/FiniteVariance.lean` -/

section
/-!
# A finite second-moment bound for rare event packets

Pairwise asymptotic independence is enough to make packets with large expected
size unlikely to contain only a bounded number of events.
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def eventCount {α : Type*} (A : Finset α) (E : α → Prop) : ℕ :=
  (A.filter E).card

theorem sum_event_indicator {α : Type*} (A : Finset α) (E : α → Prop) [DecidablePred E] :
    (∑ x ∈ A, if E x then (1 : ℝ) else 0) = (eventCount A E : ℝ) := by
  rw [Finset.sum_boole, eventCount]
  congr

noncomputable def packetCount {α ι : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) : ℝ :=
  ∑ p ∈ P, if E p x then 1 else 0

theorem packetCount_eq_eventCount {α ι : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) :
    packetCount P E x = (eventCount P (fun p => E p x) : ℝ) := by
  unfold packetCount
  convert sum_event_indicator P (fun p => E p x) using 1

noncomputable def packetVariance {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) : ℝ :=
  ∑ x ∈ A, (packetCount P E x - ∑ p ∈ P, u p) ^ 2

theorem centered_event_sum {α : Type*} (A : Finset α) (E F : α → Prop) (u v : ℝ) :
    (∑ x ∈ A, ((if E x then 1 else 0) - u) * ((if F x then 1 else 0) - v)) =
      (eventCount A (fun x => E x ∧ F x) : ℝ) - v * eventCount A E -
        u * eventCount A F + u * v * A.card := by
  classical
  have hpoint (x : α) : ((if E x then 1 else 0) - u) * ((if F x then 1 else 0) - v) =
      (if E x ∧ F x then 1 else 0) - v * (if E x then 1 else 0) -
        u * (if F x then 1 else 0) + u * v := by
    by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF] <;> ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_event_indicator, Finset.sum_const, nsmul_eq_mul]
  ring

theorem packetVariance_eq {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) :
    packetVariance A P E u = ∑ p ∈ P, ∑ q ∈ P,
      ((eventCount A (fun x => E p x ∧ E q x) : ℝ) - u q * eventCount A (E p) -
        u p * eventCount A (E q) + u p * u q * A.card) := by
  unfold packetVariance packetCount
  simp_rw [← Finset.sum_sub_distrib, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q _ => centered_event_sum A (E p) (E q) (u p) (u q))

theorem packetVariance_limit {α ι : Type*} (A : ℕ → Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) (s : ℕ → ℝ) (C : ℝ)
    (hA : Tendsto (fun N => (A N).card / s N) atTop (𝓝 C))
    (h₁ : ∀ p ∈ P, Tendsto (fun N => (eventCount (A N) (E p) : ℝ) / s N)
      atTop (𝓝 (C * u p)))
    (h₂ : ∀ p ∈ P, ∀ q ∈ P,
      Tendsto (fun N => (eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) / s N)
        atTop (𝓝 (C * (if p = q then u p else u p * u q)))) :
    Tendsto (fun N => packetVariance (A N) P E u / s N) atTop
      (𝓝 (C * ∑ p ∈ P, (u p - (u p) ^ 2))) := by
  have hpair (p) (hp : p ∈ P) (q) (hq : q ∈ P) :
      Tendsto (fun N =>
        ((eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) - u q * eventCount (A N) (E p) -
          u p * eventCount (A N) (E q) + u p * u q * (A N).card) / s N) atTop
        (𝓝 (if p = q then C * (u p - (u p) ^ 2) else 0)) := by
    have h := (((h₂ p hp q hq).sub ((h₁ p hp).const_mul (u q))).sub
      ((h₁ q hq).const_mul (u p))).add (hA.const_mul (u p * u q))
    have heq : C * (if p = q then u p else u p * u q) - u q * (C * u p) -
        u p * (C * u q) + u p * u q * C =
        (if p = q then C * (u p - (u p) ^ 2) else 0) := by
      by_cases hpq : p = q
      · subst q; simp only [if_true]; ring
      · simp only [if_neg hpq]; ring
    rw [heq] at h
    convert h using 1 <;> ext N <;> ring
  have h := tendsto_finsetSum P (fun p hp => tendsto_finsetSum P (fun q hq => hpair p hp q hq))
  have heq : (∑ p ∈ P, ∑ q ∈ P, if p = q then C * (u p - (u p) ^ 2) else 0) =
      C * ∑ p ∈ P, (u p - (u p) ^ 2) := by
    simp only [Finset.sum_ite_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [if_pos hp]
  rw [heq] at h
  convert h using 1
  · ext N
    rw [packetVariance_eq, Finset.sum_div]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_div _ _ _)

theorem fewPacketCount_mul_sq_le_variance {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) {k : ℝ} (hk : k ≤ ∑ p ∈ P, u p) :
    (eventCount A (fun x => packetCount P E x ≤ k) : ℝ) * ((∑ p ∈ P, u p) - k) ^ 2 ≤
      packetVariance A P E u := by
  have hpoint (x : α) (hx : packetCount P E x ≤ k) :
      ((∑ p ∈ P, u p) - k) ^ 2 ≤ (packetCount P E x - ∑ p ∈ P, u p) ^ 2 := by
    nlinarith
  calc
    _ = ∑ x ∈ A.filter (fun x => packetCount P E x ≤ k), ((∑ p ∈ P, u p) - k) ^ 2 := by
      simp [eventCount]
    _ ≤ ∑ x ∈ A.filter (fun x => packetCount P E x ≤ k),
        (packetCount P E x - ∑ p ∈ P, u p) ^ 2 :=
      Finset.sum_le_sum fun x hx => hpoint x (Finset.mem_filter.mp hx).2
    _ ≤ packetVariance A P E u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

theorem eventually_fewPacketCount_le {α ι : Type*} (A : ℕ → Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) (s : ℕ → ℝ) {C k : ℝ}
    (hC : 0 < C) (hs : ∀ᶠ N in atTop, 0 < s N)
    (hM : 0 < ∑ p ∈ P, u p) (hk : 2 * k ≤ ∑ p ∈ P, u p) (hk₀ : 0 ≤ k)
    (hA : Tendsto (fun N => (A N).card / s N) atTop (𝓝 C))
    (h₁ : ∀ p ∈ P, Tendsto (fun N => (eventCount (A N) (E p) : ℝ) / s N)
      atTop (𝓝 (C * u p)))
    (h₂ : ∀ p ∈ P, ∀ q ∈ P,
      Tendsto (fun N => (eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) / s N)
        atTop (𝓝 (C * (if p = q then u p else u p * u q)))) :
    ∀ᶠ N in atTop, (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) ≤
      (8 * C / (∑ p ∈ P, u p)) * s N := by
  let M := ∑ p ∈ P, u p
  have hlim := packetVariance_limit A P E u s C hA h₁ h₂
  have hlimle : C * ∑ p ∈ P, (u p - (u p) ^ 2) ≤ C * M := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Finset.sum_le_sum fun p _ => sub_le_self _ (sq_nonneg _)
  have hlt : C * ∑ p ∈ P, (u p - (u p) ^ 2) < 2 * C * M := by nlinarith
  filter_upwards [hs, hlim.eventually (gt_mem_nhds hlt)] with N hsN hV
  have hV' : packetVariance (A N) P E u ≤ 2 * C * M * s N :=
    ((div_lt_iff₀ hsN).mp hV).le
  have hrare := fewPacketCount_mul_sq_le_variance (A N) P E u (by linarith : k ≤ M)
  have hgap : M ^ 2 / 4 ≤ (M - k) ^ 2 := by nlinarith
  have hrare₀ : 0 ≤ (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) := Nat.cast_nonneg _
  have hbound := (mul_le_mul_of_nonneg_left hgap hrare₀).trans (hrare.trans hV')
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hM).mpr
  change _ * M ≤ 8 * C * s N
  have hcancel : (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) * M * M ≤
      (8 * C * s N) * M := by nlinarith [hbound]
  exact le_of_mul_le_mul_right hcancel hM

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalPrimePackets.lean` -/

section
/-!
# Pairwise independent prime divisibility in the local norm set
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def localValues (S : ℕ → Prop) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (ParityAdmissible S)

theorem localValues_card (S : ℕ → Prop) (N : ℕ) : (localValues S N).card = localCount S N := rfl

theorem eventCount_localValues_dvd (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) (N : ℕ) :
    eventCount (localValues S N) (fun n => m ∣ n) = localCount S (N / m) := by
  unfold eventCount localValues
  convert localCount_divisible S hm hS N using 1
  congr

theorem unobstructed_prime (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) (hSp : ¬S p) :
    ∀ q : ℕ, q.Prime → S q → ¬q ∣ p := by
  intro q hq hSq hdvd
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
  exact hSp (heq ▸ hSq)

theorem localValues_card_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ((localValues (fun p : ℕ => χ p = -1) N).card : ℝ) / scale N)
      atTop (𝓝 (characterLocalConstant χ / sqrt π)) := by
  simpa only [Nat.div_one, Nat.cast_one, div_one, localValues_card] using
    localCount_dilation_limit χ hχ₂ hχ (m := 1) (by decide)

theorem local_prime_divisor_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {p : ℕ} (hp : p.Prime) (hχp : χ p ≠ -1) :
    Tendsto (fun N : ℕ =>
      (eventCount (localValues (fun r : ℕ => χ r = -1) N) (fun n => p ∣ n) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) * (p : ℝ)⁻¹)) := by
  simp_rw [eventCount_localValues_dvd _ hp.pos
    (unobstructed_prime (fun r : ℕ => χ r = -1) hp hχp)]
  simpa only [div_eq_mul_inv] using localCount_dilation_limit χ hχ₂ hχ hp.pos

theorem local_prime_pair_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hχp : χ p ≠ -1) (hχr : χ r ≠ -1) :
    Tendsto (fun N : ℕ =>
      (eventCount (localValues (fun l : ℕ => χ l = -1) N) (fun n => p ∣ n ∧ r ∣ n) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) *
        (if p = r then (p : ℝ)⁻¹ else (p : ℝ)⁻¹ * (r : ℝ)⁻¹))) := by
  by_cases hpr : p = r
  · subst r
    simpa only [and_self, if_true] using local_prime_divisor_limit χ hχ₂ hχ hp hχp
  · have hcop : p.Coprime r := hp.coprime_iff_not_dvd.mpr fun h =>
      hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h)
    have heq : (fun n : ℕ => p ∣ n ∧ r ∣ n) = (fun n : ℕ => p * r ∣ n) := by
      funext n
      exact propext ⟨fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2,
        fun h => ⟨(dvd_mul_right p r).trans h, (dvd_mul_left r p).trans h⟩⟩
    rw [heq, if_neg hpr]
    have hS : ∀ l : ℕ, l.Prime → χ l = -1 → ¬l ∣ p * r := by
      intro l hl hχl hdiv
      rcases hl.dvd_mul.mp hdiv with h | h
      · exact unobstructed_prime (fun r : ℕ => χ r = -1) hp hχp l hl hχl h
      · exact unobstructed_prime (fun r : ℕ => χ r = -1) hr hχr l hl hχl h
    simp_rw [eventCount_localValues_dvd _ (Nat.mul_pos hp.pos hr.pos) hS]
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, mul_comm] using
      localCount_dilation_limit χ hχ₂ hχ (Nat.mul_pos hp.pos hr.pos)

theorem eventually_local_fewPacketCount_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p ≠ -1)
    {k : ℝ} (hk₀ : 0 ≤ k) (hM : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hk : 2 * k ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    ∀ᶠ N in atTop,
      (eventCount (localValues (fun p : ℕ => χ p = -1) N)
        (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) : ℝ) ≤
      (8 * (characterLocalConstant χ / sqrt π) / (∑ p ∈ P, (p : ℝ)⁻¹)) * scale N := by
  apply eventually_fewPacketCount_le _ P (fun p n => p ∣ n) (fun p => (p : ℝ)⁻¹)
    (fun N => scale N) (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos))
    ?_ hM hk hk₀ (localValues_card_limit χ hχ₂ hχ)
    (fun p hp => local_prime_divisor_limit χ hχ₂ hχ (hP p hp).1 (hP p hp).2)
    (fun p hp r hr => by
      have h := local_prime_pair_limit χ hχ₂ hχ
        (hP p hp).1 (hP r hr).1 (hP p hp).2 (hP r hr).2
      by_cases hpr : p = r
      · simpa only [if_pos hpr] using h
      · simpa only [if_neg hpr] using h)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact scale_pos (by exact_mod_cast (show 1 < N by omega))

end Bernays

end

/-! ### Upstream module `Util/Bernays/FiniteAvoidance.lean` -/

section
/-!
# Exact finite inclusion-exclusion for avoided events
-/

open scoped Classical

namespace Bernays

theorem indicator_all_eq_prod {ι : Type*} (P : Finset ι) (E : ι → Prop) :
    (if ∀ p ∈ P, E p then (1 : ℝ) else 0) = ∏ p ∈ P, if E p then 1 else 0 := by
  classical
  by_cases h : ∀ p ∈ P, E p
  · rw [if_pos h]
    symm
    exact Finset.prod_eq_one (fun p hp => if_pos (h p hp))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hp, hE⟩ := h
    symm
    exact Finset.prod_eq_zero hp (if_neg hE)

theorem indicator_all_not_eq_prod {ι : Type*} (P : Finset ι) (E : ι → Prop) :
    (if ∀ p ∈ P, ¬E p then (1 : ℝ) else 0) = ∏ p ∈ P, (1 - if E p then 1 else 0) := by
  calc
    _ = ∏ p ∈ P, if ¬E p then (1 : ℝ) else 0 := by
      convert indicator_all_eq_prod P (fun p => ¬E p) using 1 <;> congr
      funext p
      split_ifs <;> rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : E p <;> simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false] <;> ring

theorem eventCount_avoid_eq_sum_powerset {α ι : Type*} [DecidableEq ι]
    (A : Finset α) (P : Finset ι) (E : ι → α → Prop) :
    (eventCount A (fun x => ∀ p ∈ P, ¬E p x) : ℝ) =
      ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * eventCount A (fun x => ∀ p ∈ T, E p x) := by
  rw [← sum_event_indicator A (fun x => ∀ p ∈ P, ¬E p x)]
  simp_rw [indicator_all_not_eq_prod, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← indicator_all_eq_prod]
  exact sum_event_indicator A (fun x => ∀ p ∈ T, E p x)

end Bernays

end

/-! ### Upstream module `Util/Bernays/LocalAvoidance.lean` -/

section
/-!
# The exact local asymptotic after removing finitely many allowed primes
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem prime_prod_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    apply (hP p hp).coprime_iff_not_dvd.mpr
    exact fun hdvd => hpq ((Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q hq)).mp hdvd)

noncomputable def localAvoidValues (S : ℕ → Prop) (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (localValues S N).filter fun n => ∀ p ∈ P, ¬p ∣ n

noncomputable def avoidFactor (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

theorem avoidFactor_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 < avoidFactor P := by
  apply Finset.prod_pos
  intro p hp
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hP p hp).one_lt))

theorem localAvoidValues_card_eq (S : ℕ → Prop) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬S p) (N : ℕ) :
    ((localAvoidValues S P N).card : ℝ) =
      ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * localCount S (N / ∏ p ∈ T, p) := by
  have heq : ((localAvoidValues S P N).card : ℝ) =
      (eventCount (localValues S N) (fun n => ∀ p ∈ P, ¬p ∣ n) : ℝ) := by
    unfold localAvoidValues eventCount
    congr
  rw [heq, eventCount_avoid_eq_sum_powerset]
  apply Finset.sum_congr rfl
  intro T hT
  have hTP : T ⊆ P := Finset.mem_powerset.mp hT
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (hP p (hTP hp)).1
  have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos (fun p hp => (hTprime p hp).pos)
  have hS : ∀ q : ℕ, q.Prime → S q → ¬q ∣ ∏ p ∈ T, p := by
    intro q hq hSq hdiv
    obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff (fun p : ℕ => p)).mp hdiv
    have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq (hTprime p hp)).mp hqp
    exact (hP p (hTP hp)).2 (hqp' ▸ hSq)
  have hevent : (fun n : ℕ => ∀ p ∈ T, p ∣ n) = (fun n : ℕ => (∏ p ∈ T, p) ∣ n) := by
    funext n
    exact propext (prime_prod_dvd_iff T hTprime n).symm
  rw [hevent, eventCount_localValues_dvd S hpos hS]

theorem avoidFactor_eq_sum_powerset (P : Finset ℕ) :
    avoidFactor P = ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ) := by
  rw [avoidFactor, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib]

theorem localAvoidValues_card_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p ≠ -1) :
    Tendsto (fun N : ℕ => ((localAvoidValues (fun p : ℕ => χ p = -1) P N).card : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) * avoidFactor P)) := by
  let C := characterLocalConstant χ / sqrt π
  have hterm (T : Finset ℕ) (hT : T ∈ P.powerset) :
      Tendsto (fun N : ℕ => (-1 : ℝ) ^ T.card *
        (localCount (fun p : ℕ => χ p = -1) (N / ∏ p ∈ T, p) : ℝ) / scale N)
        atTop (𝓝 (C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)))) := by
    have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp =>
      (hP p ((Finset.mem_powerset.mp hT) hp)).1.pos
    have h := (localCount_dilation_limit χ hχ₂ hχ hpos).const_mul ((-1 : ℝ) ^ T.card)
    change Tendsto _ _ (𝓝 ((-1 : ℝ) ^ T.card * (C / ((∏ p ∈ T, p : ℕ) : ℝ)))) at h
    have heq : (-1 : ℝ) ^ T.card * (C / ((∏ p ∈ T, p : ℕ) : ℝ)) =
        C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)) := by ring
    rw [heq] at h
    convert h using 1
    ext N
    ring
  have h := tendsto_finsetSum P.powerset hterm
  have hvalue : (∑ T ∈ P.powerset, C * ((-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ))) =
      C * avoidFactor P := by rw [avoidFactor_eq_sum_powerset, Finset.mul_sum]
  rw [hvalue] at h
  convert h using 1
  ext N
  rw [localAvoidValues_card_eq _ P hP N, Finset.sum_div]

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodLocalCounting.lean` -/

section
/-!
# Exact counting of local norms coprime to the discriminant
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem coprime_iff_primeFactors_avoid {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    n.Coprime M ↔ ∀ p ∈ M.primeFactors, ¬p ∣ n := by
  constructor
  · intro hc p hp hpn
    have hdata := Nat.mem_primeFactors.mp hp
    exact hdata.1.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpn hdata.2.1)
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpn, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩) hpn

noncomputable def goodLocalValues (d b : ℤ) (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) : Finset ℕ :=
  (localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD p = -1) N).filter
    fun n => n.Coprime (discriminantLevel (b ^ 2 + 4 * d))

noncomputable def goodLocalConstant (d b : ℤ) (hD : b ^ 2 + 4 * d ≠ 0) : ℝ := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD).ne'⟩
  exact (characterLocalConstant (discriminantCharacter (b ^ 2 + 4 * d) hD) / sqrt π) *
    avoidFactor (discriminantLevel (b ^ 2 + 4 * d)).primeFactors

theorem goodLocalConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : 0 < goodLocalConstant d b hD.ne := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  exact mul_pos
    (div_pos (characterLocalConstant_pos _ (discriminantCharacter_ne_one hD)) (sqrt_pos.mpr pi_pos))
    (avoidFactor_pos _ (fun _ hp => (Nat.mem_primeFactors.mp hp).1))

theorem goodLocalValues_eq_avoid {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) :
    goodLocalValues d b hD N =
      localAvoidValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD p = -1)
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors N := by
  ext n
  simp only [goodLocalValues, localAvoidValues, Finset.mem_filter,
    coprime_iff_primeFactors_avoid (discriminantLevel_pos hD).ne']

theorem goodLocalValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Tendsto (fun N : ℕ => ((goodLocalValues d b hD.ne N).card : ℝ) / scale N)
      atTop (𝓝 (goodLocalConstant d b hD.ne)) := by
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  simp_rw [goodLocalValues_eq_avoid]
  unfold goodLocalConstant
  apply localAvoidValues_card_limit _ (discriminantCharacter_sq _ hD.ne)
    (discriminantCharacter_ne_one hD)
  intro p hp
  have hdata := Nat.mem_primeFactors.mp hp
  refine ⟨hdata.1, ?_⟩
  have hz : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = 0 :=
    (char_prime_eq_zero_iff _ ⟨p, hdata.1⟩).mpr hdata.2.1
  rw [hz]
  norm_num

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogCountBound.lean` -/

section
/-!
# Global logarithmic counting bounds from the proved asymptotic
-/

open Filter Topology

namespace Bernays

theorem exists_logCountBound {A : ℕ → ℝ} (hA₀ : ∀ N : ℕ, 0 ≤ A N)
    (hA₁ : ∀ N : ℕ, A N ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hAB : ∀ᶠ N : ℕ in atTop, A N ≤ B * scale N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))).eventually (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hAB.and (hlog.and (eventually_ge_atTop 2)))
  let M := 1 + Real.sqrt (Real.log (N₀ : ℝ))
  let C := max (2 * B) M
  have hM : 0 < M := by dsimp only [M]; positivity
  have hC : 0 < C := lt_of_lt_of_le hM (le_max_right _ _)
  refine ⟨C, hC, fun N => ?_⟩
  have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hN : N₀ ≤ N
  · obtain ⟨hAN, hsqrt, hN₂⟩ := hN₀ N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hspos : 0 < Real.sqrt (Real.log (N : ℝ)) := by linarith
    have hmain : A N * Real.sqrt (Real.log (N : ℝ)) ≤ B * N := by
      apply (le_div_iff₀ hspos).mp
      simpa only [scale, mul_div_assoc] using hAN
    have htwice := mul_le_mul_of_nonneg_left hsqrt (hA₀ N)
    have hCB : 2 * B * (N : ℝ) ≤ C * N :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg N)
    nlinarith
  · by_cases hNz : N = 0
    · subst N
      have hzero : A 0 = 0 := le_antisymm (by simpa using hA₁ 0) (hA₀ 0)
      simp only [hzero, Nat.cast_zero, zero_mul, mul_zero, le_refl]
    · have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNz
      have hNN : (N : ℝ) ≤ N₀ := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hN))
      have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log hNp hNN)
      have hdenM : 1 + Real.sqrt (Real.log (N : ℝ)) ≤ M := by dsimp only [M]; linarith
      calc
        _ ≤ (N : ℝ) * (1 + Real.sqrt (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (hA₁ N) hden.le
        _ ≤ (N : ℝ) * M := mul_le_mul_of_nonneg_left hdenM (Nat.cast_nonneg N)
        _ ≤ C * N := by
          rw [mul_comm (N : ℝ) M]
          exact mul_le_mul_of_nonneg_right (le_max_right (2 * B) M) (Nat.cast_nonneg N)

theorem exists_logCountBound_of_limit {A : ℕ → ℝ} (hA₀ : ∀ N : ℕ, 0 ≤ A N)
    (hA₁ : ∀ N : ℕ, A N ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hlim : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 B)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  apply exists_logCountBound hA₀ hA₁ (show 0 ≤ B + 1 by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one B)), eventually_ge_atTop 2] with N hN hN₂
  have hscale := scale_pos (show (1 : ℝ) < N by exact_mod_cast hN₂)
  exact (div_le_iff₀ hscale).mp hN.le

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusCountBounds.lean` -/

section
/-!
# Counting bounds for all genus twists
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem goodLocalValues_card_le {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) :
    (goodLocalValues d b hD N).card ≤ N := by
  have hsub : goodLocalValues d b hD N ⊆ Finset.Icc 1 N :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  simpa using Finset.card_le_card hsub

theorem genusLocalAF_norm_le_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, ‖genusLocalAF hD ψ n‖ ≤ 1 := by
  letI := quadraticOrderIsDomain hD
  intro ψ n
  rw [genusLocalAF_norm]
  split_ifs <;> norm_num

theorem genusLocalAF_sum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, genusLocalAF hD ψ n) =
      ∑ n ∈ goodLocalValues d b hD.ne N, ψ (Additive.ofMul (genusValue hD n)) := by
  letI := quadraticOrderIsDomain hD
  intro ψ N
  rw [goodLocalValues, localValues, Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  simp only [genusLocalAF_apply, hn₀, true_and]

theorem genusLocalAF_sum_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖genusLocalAF hD ψ n‖) =
      ((goodLocalValues d b hD.ne N).card : ℝ) := by
  letI := quadraticOrderIsDomain hD
  intro ψ N
  have hcard : ((goodLocalValues d b hD.ne N).card : ℝ) =
      ∑ _n ∈ goodLocalValues d b hD.ne N, (1 : ℝ) := by simp
  rw [hcard]
  rw [goodLocalValues, localValues, Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  simp only [genusLocalAF_norm, hn₀, true_and]

theorem cumsum_le_sum_Icc {a : ℕ → ℝ} (ha₀ : a 0 = 0) (ha : ∀ n : ℕ, 0 ≤ a n) (N : ℕ) :
    cumsum a N ≤ ∑ n ∈ Finset.Icc 1 N, a n := by
  have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro n hn
    by_cases hz : n = 0
    · simp only [hz, Finset.mem_insert, true_or]
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hz, (Finset.mem_range.mp hn).le⟩))
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ha n)
  simpa only [cumsum, Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 N), ha₀, zero_add] using h

theorem genusLocalAF_cheby {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      cheby (genusLocalAF hD ψ) := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  refine ⟨1, fun N => ?_⟩
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => genusLocalAF_norm_le_one hD ψ n)
  simpa only [cumsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul] using h

theorem genusLocalAF_logCountBound {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, cumsum (fun n => ‖genusLocalAF hD ψ n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨C, hC, hbound⟩ := exists_logCountBound_of_limit
    (fun N => Nat.cast_nonneg (goodLocalValues d b hD.ne N).card)
    (fun N => by exact_mod_cast goodLocalValues_card_le hD.ne N)
    (goodLocalConstant_pos hD).le (goodLocalValues_card_limit hD)
  refine ⟨C, hC, fun ψ N => ?_⟩
  have hsum := cumsum_le_sum_Icc (show ‖genusLocalAF hD ψ 0‖ = 0 by simp)
    (fun n => norm_nonneg (genusLocalAF hD ψ n)) N
  rw [genusLocalAF_sum_norm hD ψ N] at hsum
  exact hsum.trans (hbound N)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareSeriesApproximation.lean` -/

section
/-!
# Removal of compact frequency support by Sobolev approximation
-/

open Filter Topology

namespace Bernays

theorem smoothedSeries_scaled_norm_le {a : ℕ → ℂ} (ha : cheby a) (ψ : W21)
    {δ K : ℝ} (hδ : 0 < δ)
    (hK : logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) :
    ‖smoothedSeries a ψ δ‖ / Real.sqrt δ ≤ W21.norm ψ * K := by
  apply (div_le_div_of_nonneg_right (smoothedSeries_norm_le ha ψ hδ.le) (Real.sqrt_nonneg _)).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hK W21.norm_nonneg

theorem smoothedSeries_scaled_sub_le {a : ℕ → ℂ} (ha : cheby a) (ψ φ : W21)
    {δ K : ℝ} (hδ : 0 < δ)
    (hK : logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) :
    ‖smoothedSeries a ψ δ‖ / Real.sqrt δ ≤ W21.norm (ψ - φ) * K +
      ‖smoothedSeries a φ δ‖ / Real.sqrt δ := by
  have hnorm : ‖smoothedSeries a ψ δ‖ ≤
      ‖smoothedSeries a (ψ - φ) δ‖ + ‖smoothedSeries a φ δ‖ := by
    rw [smoothedSeries_sub ha ψ φ hδ.le]
    calc
      _ = ‖(smoothedSeries a ψ δ - smoothedSeries a φ δ) + smoothedSeries a φ δ‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  apply (div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg _)).trans
  rw [add_div]
  exact add_le_add (smoothedSeries_scaled_norm_le ha (ψ - φ) hδ hK) le_rfl

theorem LSeries_square_W21_cancellation (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (hcheby : cheby a) {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) (ψ : W21) :
    Tendsto (fun δ : ℝ => ‖smoothedSeries a ψ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
  obtain g := exists_trunc
  let Ψ (R : ℝ) : CS 2 ℂ := g.scale R * ψ
  have happrox : Tendsto (fun R : ℝ => W21.norm (ψ - (Ψ R : W21))) atTop (𝓝 0) :=
    W21_approximation ψ g
  have hcompact (R : ℝ) : Tendsto
      (fun δ : ℝ => ‖smoothedSeries a (Ψ R) δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) :=
    LSeries_square_smoothed_cancellation a F ha had hF heq hne (Ψ R)
      ((Ψ R).h1.of_le (by norm_num)) (Ψ R).h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htol : 0 < ε / (2 * (K + 1)) := by positivity
  obtain ⟨R, hR⟩ := (happrox.eventually (gt_mem_nhds htol)).exists
  have hsmall := (hcompact R).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hK, hsmall] with δ hδ hKδ hsmallδ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
  have hbound := smoothedSeries_scaled_sub_le hcheby ψ (Ψ R) hδ hKδ
  have hscale : W21.norm (ψ - (Ψ R : W21)) * K < ε / 2 := by
    have hn := W21.norm_nonneg (f := (ψ - (Ψ R : W21) : W21))
    have hprod := (lt_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp hR
    nlinarith
  change ‖smoothedSeries a (Ψ R) δ‖ / Real.sqrt δ < ε / 2 at hsmallδ
  simp only [W21.ofCS2_toFun] at hbound hscale
  exact hbound.trans_lt (by linarith)

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogKernelSmallPart.lean` -/

section
/-!
# The small-index contribution to the logarithmic kernel
-/

open scoped Classical

namespace Bernays

theorem logarithmicKernel_le_of_le_sqrt {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y)
    (hyx : y ≤ Real.sqrt x) :
    (1 + (1 / (2 * Real.pi) * Real.log (y / x)) ^ 2)⁻¹ ≤
      (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ := by
  have hx₀ := zero_lt_one.trans_le hx
  have hlog := Real.log_le_log hy hyx
  rw [Real.log_sqrt hx₀.le] at hlog
  rw [Real.log_div hy.ne' hx₀.ne']
  have hπ : 0 < 2 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left (show Real.log y - Real.log x ≤ -(Real.log x / 2) by linarith)
    (inv_nonneg.mpr hπ.le)
  have hlt : (1 / (2 * Real.pi)) * (Real.log y - Real.log x) ≤ -(Real.log x / (4 * Real.pi)) := by
    calc
      _ ≤ (2 * Real.pi)⁻¹ * -(Real.log x / 2) := by simpa only [one_div] using hmul
      _ = _ := by ring
  have hnonneg : 0 ≤ Real.log x / (4 * Real.pi) := div_nonneg (Real.log_nonneg hx) (by positivity)
  apply inv_anti₀ (by positivity)
  nlinarith

theorem logarithmicKernelMass_lower_le {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    logarithmicKernelMass (normLowerPart a (Real.sqrt x)) x ≤
      (1 + Real.log x) * (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ := by
  let B := (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hroot : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  have hxs : 0 ≤ x := zero_le_one.trans hx
  rw [logarithmicKernelMass, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ * B := by
        apply Finset.sum_le_sum
        intro n hn
        have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn₀
        by_cases hsmall : (n : ℝ) < Real.sqrt x
        · rw [normLowerPart, if_pos hsmall]
          simpa only [one_div, logarithmicKernel, B] using
            mul_le_mul (div_le_div_of_nonneg_right (ha n) hnR.le)
              (logarithmicKernel_le_of_le_sqrt hx hnR hsmall.le) (by positivity) (by positivity)
        · rw [normLowerPart, if_neg hsmall, norm_zero, zero_div, zero_mul]
          positivity
      _ = (harmonic ⌊x⌋₊ : ℝ) * B := by
        rw [← Finset.sum_mul, harmonic_eq_sum_Icc, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
      _ ≤ (1 + Real.log x) * B := mul_le_mul_of_nonneg_right (harmonic_floor_le_one_add_log x hx) hB
  · intro n hn
    by_cases hn₀ : n = 0
    · simp only [hn₀, Nat.cast_zero, div_zero, zero_mul]
    · have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn₀
      have hnx : ¬ n ≤ ⌊x⌋₊ := fun h => hn (Finset.mem_Icc.mpr ⟨hn₁, h⟩)
      have hnot : ¬ (n : ℝ) < Real.sqrt x := by
        intro h
        exact hnx ((Nat.le_floor_iff hxs).mpr (h.le.trans hroot))
      rw [normLowerPart, if_neg hnot, norm_zero, zero_div, zero_mul]

theorem logarithmicKernelMass_upper_le {a : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    logarithmicKernelMass (normUpperPart a (Real.sqrt x)) x ≤
      (2 * C / Real.sqrt (Real.log x)) * (1 + 2 * Real.pi ^ 2) :=
  bound_sum_log' (normUpperPart_cheby_logBound hC hcount hx) hx.le

theorem logarithmicKernelMass_le {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    logarithmicKernelMass a x ≤
      (1 + Real.log x) * (1 + (Real.log x / (4 * Real.pi)) ^ 2)⁻¹ +
        (2 * C / Real.sqrt (Real.log x)) * (1 + 2 * Real.pi ^ 2) := by
  rw [logarithmicKernelMass_split hcheby (Real.sqrt x) (zero_lt_one.trans hx)]
  exact add_le_add (logarithmicKernelMass_lower_le ha hx.le)
    (logarithmicKernelMass_upper_le hC hcount hx)

end Bernays

end

/-! ### Upstream module `Util/Bernays/LogKernelUniformBound.lean` -/

section
/-!
# The uniform weighted bound used to remove frequency truncation
-/

open Filter Topology

namespace Bernays

theorem smallLogKernel_scaled_le {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt y * ((1 + y) * (1 + (y / (4 * Real.pi)) ^ 2)⁻¹) ≤ 32 * Real.pi ^ 2 := by
  have hroot : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  have hden : 0 < 1 + (y / (4 * Real.pi)) ^ 2 := by positivity
  rw [← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ hden]
  have hnum : Real.sqrt y * (1 + y) ≤ 2 * y ^ 2 := by
    have := mul_le_mul_of_nonneg_right hroot (by linarith : 0 ≤ 1 + y)
    nlinarith
  have hid : 32 * Real.pi ^ 2 * (y / (4 * Real.pi)) ^ 2 = 2 * y ^ 2 := by
    field_simp
    ring
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

theorem logarithmicKernelMass_scaled_bound {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤
      32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2) := by
  have hy : 1 ≤ (1 : ℝ) / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ₁)
  have hx : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (by positivity)
  have hbound := logarithmicKernelMass_le ha hcheby hC hcount hx
  rw [Real.log_exp] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (1 / δ))
  have hs : Real.sqrt (1 / δ) = (Real.sqrt δ)⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  have hsp : Real.sqrt (1 / δ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcancel : Real.sqrt (1 / δ) *
      ((2 * C / Real.sqrt (1 / δ)) * (1 + 2 * Real.pi ^ 2)) =
      2 * C * (1 + 2 * Real.pi ^ 2) := by field_simp
  rw [mul_add, hcancel] at hmul
  have hfinal := hmul.trans (add_le_add (smallLogKernel_scaled_le hy) le_rfl)
  simpa only [hs, inv_mul_eq_div] using hfinal

theorem logarithmicKernelMass_eventually_scaled_bound {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hcheby : cheby a) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ)))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤
      32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2) := by
  filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds] with δ hδ hδ₁
  exact logarithmicKernelMass_scaled_bound ha hcheby hC hcount hδ hδ₁

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusSmoothedCancellation.lean` -/

section
/-!
# Unconditional smoothed cancellation for every nontrivial genus character
-/

open Filter Topology

namespace Bernays

theorem LSeries_square_W21_cancellation_of_logCountBound (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (hcheby : cheby a) (hbound : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ)))) (ψ : W21) :
    Tendsto (fun δ : ℝ => ‖smoothedSeries a ψ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
  apply LSeries_square_W21_cancellation a F ha had hF heq hne hcheby
    (K := 32 * Real.pi ^ 2 + 2 * C * (1 + 2 * Real.pi ^ 2)) (by positivity)
  exact logarithmicKernelMass_eventually_scaled_bound hbound hcheby hC hcount

theorem genusLocal_smoothed_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
    ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries (genusLocalAF hD ψ) φ δ‖ / Real.sqrt δ)
        (𝓝[>] 0) (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ φ
  obtain ⟨F, hF, heq, hne⟩ := genusLocalLSeries_continuation_nonzero hD ψ hψ
  obtain ⟨C, hC, hcount⟩ := genusLocalAF_logCountBound hD
  exact LSeries_square_W21_cancellation_of_logCountBound (genusLocalAF hD ψ) F
    (genusLocalAF_summable hD ψ) (genusLocalLSeries_differentiableAt hD ψ)
    hF heq hne (genusLocalAF_cheby hD ψ) (genusLocalAF_norm_le_one hD ψ) hC.le (hcount ψ) φ

end Bernays

end

/-! ### Upstream module `Util/Bernays/SpatialSmoothCancellation.lean` -/

section
/-!
# Cancellation against arbitrary smooth compact spatial tests
-/

open Set Filter Topology
open scoped ContDiff

namespace Bernays

theorem spatial_smooth_cancellation_of_smoothed {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    (hsm : ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries a φ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0))
    {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨b, L, Q, hb, hL, hQ, hΨ₀, hΨQ, hΨsupp⟩ :=
    compact_positive_test_bounds hΨ.continuous hsupp hplus
  let U (δ : ℝ) : ℂ := ∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))
  let T (δ : ℝ) : ℂ := ∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))
  let D (δ : ℝ) : ℝ := Real.exp (1 / δ) * Real.sqrt δ
  let e : ℝ := Real.exp (-1)
  have he : 0 < e := Real.exp_pos _
  have hT : Tendsto (fun δ => ‖T δ‖ / D δ) (𝓝[>] 0) (𝓝 0) :=
    spatial_twisted_cancellation_of_smoothed hsm hΨ hsupp hplus
  have hE : Tendsto (fun δ => ‖T δ - (e : ℂ) * U δ‖ / D δ) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun δ : ℝ =>
        (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2)))
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ =>
          (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2))) := by fun_prop
      simpa only [zero_mul, Real.exp_zero, sub_self, mul_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    apply squeeze_zero' (Eventually.of_forall (fun δ =>
      div_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))) _ hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact spatial_untwist_error_le ha hC hcount hb hL hQ hΨ₀ hΨQ hΨsupp hδ
  have hlim := (hT.add hE).div_const e
  simp only [add_zero, zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun δ =>
    div_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))) _ hlim
  filter_upwards [] with δ
  have hnorm : e * ‖U δ‖ ≤ ‖T δ‖ + ‖T δ - (e : ℂ) * U δ‖ := by
    have h := norm_sub_le (T δ) (T δ - (e : ℂ) * U δ)
    rw [sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_of_nonneg he.le] at h
    exact h
  have hnorm' : ‖U δ‖ ≤ (‖T δ‖ + ‖T δ - (e : ℂ) * U δ‖) / e := by
    apply (le_div_iff₀ he).mpr
    simpa only [mul_comm e] using hnorm
  have hdiv := div_le_div_of_nonneg_right hnorm'
    (show 0 ≤ D δ from mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  change ‖U δ‖ / D δ ≤ (‖T δ‖ / D δ + ‖T δ - (e : ℂ) * U δ‖ / D δ) / e
  exact hdiv.trans_eq (by ring)

theorem genusLocal_spatial_smooth_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
    ∀ Ψ : ℝ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ioi 0 →
      Tendsto (fun δ : ℝ =>
        ‖∑' n : ℕ, genusLocalAF hD ψ n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
          (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ Ψ hΨ hsupp hplus
  obtain ⟨C, hC, hcount⟩ := genusLocalAF_logCountBound hD
  exact spatial_smooth_cancellation_of_smoothed (genusLocalAF_norm_le_one hD ψ) hC.le (hcount ψ)
    (genusLocal_smoothed_cancellation hD ψ hψ) hΨ hsupp hplus

end Bernays

end

/-! ### Upstream module `Util/Bernays/CountingReparametrization.lean` -/

section
/-!
# Real endpoints and exponential reparametrization of counting limits
-/

open Filter Topology Asymptotics
open scoped ContDiff

namespace Bernays

theorem scale_mul_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => scale (c * x) / scale x) atTop (𝓝 c) := by
  simpa only [div_inv_eq_mul, inv_inv, mul_comm] using scale_dilation_limit (inv_pos.mpr hc)

theorem count_floor_scale_limit {A : ℕ → ℝ} {C : ℝ}
    (hA : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ => A ⌊x⌋₊ / scale x) atTop (𝓝 C) := by
  have hscale : ∀ᶠ x : ℝ in atTop, scale x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (scale_pos hx).ne'
  have hratio := (isEquivalent_iff_tendsto_one hscale).mp scale_natFloor_isEquivalent
  have h := (hA.comp (tendsto_nat_floor_atTop (α := ℝ))).mul hratio
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually (eventually_ge_atTop 2)] with x hx
  have hs : scale (⌊x⌋₊ : ℝ) ≠ 0 := (scale_pos (by exact_mod_cast hx)).ne'
  change (A ⌊x⌋₊ / scale (⌊x⌋₊ : ℝ)) * (scale (⌊x⌋₊ : ℝ) / scale x) = _
  field_simp

theorem count_floor_dilation_limit {A : ℕ → ℝ} {C c : ℝ}
    (hA : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 C)) (hc : 0 < c) :
    Tendsto (fun x : ℝ => A ⌊c * x⌋₊ / scale x) atTop (𝓝 (C * c)) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h := ((count_floor_scale_limit hA).comp hcx).mul (scale_mul_limit hc)
  apply h.congr'
  filter_upwards [hcx.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
  have hs : scale (c * x) ≠ 0 := (scale_pos hx).ne'
  change (A ⌊c * x⌋₊ / scale (c * x)) * (scale (c * x) / scale x) = _
  field_simp

theorem inverse_log_tendsto :
    Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact one_div_pos.mpr (Real.log_pos hx)

theorem spatial_smooth_cancellation_atTop {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (h : Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x : ℝ => ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / x)‖ / scale x)
      atTop (𝓝 0) := by
  apply (h.comp inverse_log_tendsto).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := zero_lt_one.trans hx
  change ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / (1 / Real.log x)))‖ /
    (Real.exp (1 / (1 / Real.log x)) * Real.sqrt (1 / Real.log x)) = _
  rw [one_div_one_div, Real.exp_log hx₀, one_div, Real.sqrt_inv]
  rfl

end Bernays

end

/-! ### Upstream module `Util/Bernays/SharpCutoffError.lean` -/

section
/-!
# Exact natural-endpoint cutoff errors
-/

open Set Filter Topology
open scoped Classical ContDiff

namespace Bernays

theorem spatial_sum_eq_Icc {a : ℕ → ℂ} {Ψ : ℝ → ℂ} {b x : ℝ}
    (hx : 0 < x) (hb : 0 ≤ b) (hzero : Ψ 0 = 0)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b) :
    (∑' n : ℕ, a n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.Icc 1 ⌊b * x⌋₊, a n * Ψ ((n : ℝ) / x) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hz : n = 0
  · simp only [hz, Nat.cast_zero, zero_div, hzero, mul_zero]
  · have hΨ : Ψ ((n : ℝ) / x) = 0 := by
      by_contra hne
      have hnx : (n : ℝ) ≤ b * x := (div_le_iff₀ hx).mp (hsupp _ hne)
      exact hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz,
        (Nat.le_floor_iff (mul_nonneg hb hx.le)).mpr hnx⟩)
    rw [hΨ, mul_zero]

theorem natural_sharp_cutoff_error (a : ℕ → ℂ) {ε : ℝ} (hε : 0 < ε)
    (Ψ : ℝ → ℝ) (hΨ : ∀ y : ℝ, 0 ≤ Ψ y ∧ Ψ y ≤ 1) (hΨ₀ : Ψ 0 = 0)
    (hone : ∀ y ∈ Icc ε 1, Ψ y = 1)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ 1 + ε)
    {N : ℕ} (hN : 0 < N) :
    ‖(∑ n ∈ Finset.Icc 1 N, a n) - ∑' n : ℕ, a n * (Ψ ((n : ℝ) / N) : ℂ)‖ ≤
      (∑ n ∈ Finset.Icc 1 ⌊ε * N⌋₊, ‖a n‖) +
        (∑ n ∈ Finset.Icc 1 ⌊(1 + ε) * N⌋₊, ‖a n‖) - ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 ≤ 1 + ε := by linarith
  have hAB : Finset.Icc 1 N ⊆ Finset.Icc 1 ⌊(1 + ε) * N⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    apply (Nat.le_floor_iff (mul_nonneg hb hNR.le)).mpr
    nlinarith
  have hSB : Finset.Icc 1 ⌊ε * N⌋₊ ⊆ Finset.Icc 1 ⌊(1 + ε) * N⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    apply Nat.floor_mono
    nlinarith
  have hcut := finite_cutoff_error (Finset.Icc 1 N) (Finset.Icc 1 ⌊(1 + ε) * N⌋₊)
    (Finset.Icc 1 ⌊ε * N⌋₊) hAB hSB a (fun n => Ψ ((n : ℝ) / N))
    (fun n _ => hΨ _) (fun n hn hnot => ?_)
  · rw [spatial_sum_eq_Icc (a := a) (Ψ := fun y : ℝ => (Ψ y : ℂ)) hNR hb
      (by simp only [hΨ₀, Complex.ofReal_zero])
      (fun y hy => hsupp y (by simpa only [ne_eq, Complex.ofReal_eq_zero] using hy))]
    rw [Finset.sum_sdiff_eq_sub (f := fun n : ℕ => ‖a n‖) hAB] at hcut
    linarith
  · have hn₁ : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnotfloor : ¬ n ≤ ⌊ε * N⌋₊ := fun h => hnot (Finset.mem_Icc.mpr ⟨hn₁, h⟩)
    have hnε : ε * N < (n : ℝ) := by
      exact lt_of_not_ge (fun h => hnotfloor ((Nat.le_floor_iff (mul_nonneg hε.le hNR.le)).mpr h))
    exact hone _ ⟨((le_div_iff₀ hNR).mpr hnε.le),
      (div_le_one hNR).mpr (by exact_mod_cast hnN)⟩

theorem exists_sharp_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ Ioi 0 ∧
      (∀ y : ℝ, 0 ≤ Ψ y ∧ Ψ y ≤ 1) ∧ Ψ 0 = 0 ∧
      (∀ y ∈ Icc ε 1, Ψ y = 1) ∧ (∀ y : ℝ, Ψ y ≠ 0 → y ≤ 1 + ε) := by
  obtain ⟨Ψ, hΨ, hsupp, hlo, hhi, hs⟩ := smooth_urysohn_support_Ioo
    (show ε / 2 < ε by linarith) (show (1 : ℝ) < 1 + ε by linarith)
  have hbounds (y : ℝ) : 0 ≤ Ψ y ∧ Ψ y ≤ 1 :=
    ⟨(Set.indicator_nonneg (fun _ _ => zero_le_one) y).trans (hlo y),
      (hhi y).trans (Set.indicator_le_self' (fun _ _ => zero_le_one) y)⟩
  have hplus : tsupport Ψ ⊆ Ioi 0 := by
    rw [tsupport, hs]
    apply (closure_mono Ioo_subset_Icc_self).trans
    rw [isClosed_Icc.closure_eq]
    intro y hy
    exact lt_of_lt_of_le (half_pos hε) hy.1
  refine ⟨Ψ, hΨ, hsupp, hplus, hbounds, ?_, ?_, ?_⟩
  · by_contra hzero
    exact (lt_irrefl (0 : ℝ)) (hplus (subset_closure hzero))
  · intro y hy
    have h := hlo y
    rw [Set.indicator_of_mem hy, Pi.one_apply] at h
    exact le_antisymm (hbounds y).2 h
  · intro y hy
    have hmem : y ∈ Function.support Ψ := hy
    rw [hs] at hmem
    exact hmem.2.le

end Bernays

end

/-! ### Upstream module `Util/Bernays/SharpCancellation.lean` -/

section
/-!
# Removal of smoothing at the Bernays counting scale
-/

open Set Filter Topology
open scoped ContDiff

namespace Bernays

theorem sharp_cancellation_of_smooth (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖) / scale N) atTop (𝓝 C))
    (hsm : ∀ Ψ : ℝ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ioi 0 →
      Tendsto (fun x : ℝ => ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / x)‖ / scale x) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, a n‖ / scale N) atTop (𝓝 0) := by
  let A (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖
  rw [Metric.tendsto_nhds]
  intro η hη
  let ε := η / (8 * (C + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨Ψ, hΨ, hsupp, hplus, hΨbounds, hΨ₀, hone, hsup⟩ := exists_sharp_cutoff hε
  have hΨC : ContDiff ℝ ∞ (fun y : ℝ => (Ψ y : ℂ)) := contDiff_ofReal.comp hΨ
  have hsuppC : HasCompactSupport (fun y : ℝ => (Ψ y : ℂ)) :=
    hsupp.comp_left (g := Complex.ofReal) rfl
  have hplusC : tsupport (fun y : ℝ => (Ψ y : ℂ)) ⊆ Ioi 0 := by
    have heq : Function.support (fun y : ℝ => (Ψ y : ℂ)) = Function.support Ψ := by
      ext y
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    simpa only [tsupport, heq] using hplus
  have hS := (hsm (fun y : ℝ => (Ψ y : ℂ)) hΨC hsuppC hplusC).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo := (count_floor_dilation_limit hA hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhi := (count_floor_dilation_limit hA (show 0 < 1 + ε by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hE : Tendsto (fun N : ℕ =>
      (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N) atTop (𝓝 (2 * C * ε)) := by
    have h := (hlo.add hhi).sub hA
    have hid : C * ε + C * (1 + ε) - C = 2 * C * ε := by ring
    rw [hid] at h
    convert h using 1
    funext N
    dsimp only [Function.comp_def, A]
    ring
  have hεbound : 2 * C * ε ≤ η / 4 := by
    have hden : 0 < 8 * (C + 1) := by positivity
    have hid : ε * (8 * (C + 1)) = η := by
      dsimp only [ε]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith
  filter_upwards [eventually_ge_atTop 2,
    hS.eventually (gt_mem_nhds (show (0 : ℝ) < η / 4 by positivity)),
    hE.eventually (gt_mem_nhds (show 2 * C * ε < 2 * C * ε + η / 4 by linarith))]
    with N hN hSN hEN
  have hN₀ : 0 < N := by omega
  have hscale : 0 < scale N := scale_pos (by exact_mod_cast hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (norm_nonneg _) hscale.le)]
  have herror := natural_sharp_cutoff_error a hε Ψ hΨbounds hΨ₀ hone hsup hN₀
  let S : ℂ := ∑' n : ℕ, a n * (Ψ ((n : ℝ) / N) : ℂ)
  have htri : ‖∑ n ∈ Finset.Icc 1 N, a n‖ ≤
      ‖(∑ n ∈ Finset.Icc 1 N, a n) - S‖ + ‖S‖ := by
    calc
      _ = ‖((∑ n ∈ Finset.Icc 1 N, a n) - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum := htri.trans (add_le_add herror le_rfl)
  have hdiv := div_le_div_of_nonneg_right hsum hscale.le
  rw [add_div] at hdiv
  change ‖S‖ / scale N < η / 4 at hSN
  change (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N < 2 * C * ε + η / 4 at hEN
  change ‖∑ n ∈ Finset.Icc 1 N, a n‖ / scale N ≤
    (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N + ‖S‖ / scale N at hdiv
  linarith

theorem genusLocal_sharp_norm_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, genusLocalAF hD ψ n‖ / scale N)
        atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  apply sharp_cancellation_of_smooth (genusLocalAF hD ψ) (goodLocalConstant_pos hD).le
  · simpa only [genusLocalAF_sum_norm] using goodLocalValues_card_limit hD
  · intro Ψ hΨ hsupp hplus
    exact spatial_smooth_cancellation_atTop (genusLocal_spatial_smooth_cancellation hD ψ hψ Ψ hΨ hsupp hplus)

end Bernays

end

/-! ### Upstream module `Util/Bernays/FiniteGroupDistribution.lean` -/

section
/-!
# Finite-group distribution from character cancellation
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem character_fiber_indicator {G : Type*} [CommGroup G] [Fintype G] (g h : G) :
    (if g = h then (1 : ℂ) else 0) =
      (∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul g) / ψ (Additive.ofMul h)) /
        (Fintype.card G : ℂ) := by
  have hsum := AddChar.sum_apply_eq_ite (Additive.ofMul (g / h))
  simp only [ofMul_div, AddChar.map_sub_eq_div, sub_eq_zero, Additive.ofMul.injective.eq_iff] at hsum
  rw [Fintype.card_congr (Additive.ofMul : G ≃ Additive G).symm] at hsum
  rw [hsum]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hgh : g = h
  · simp only [if_pos hgh]
    exact (div_self hcard).symm
  · simp only [if_neg hgh, zero_div]

theorem fiber_card_eq_character_sum {α G : Type*} [CommGroup G] [Fintype G]
    (A : Finset α) (f : α → G) (g : G) :
    (eventCount A (fun x => f x = g) : ℂ) =
      (∑ ψ : AddChar (Additive G) ℂ,
        (∑ x ∈ A, ψ (Additive.ofMul (f x))) / ψ (Additive.ofMul g)) / (Fintype.card G : ℂ) := by
  have hcard : (eventCount A (fun x => f x = g) : ℂ) =
      ∑ x ∈ A, if f x = g then (1 : ℂ) else 0 := by
    unfold eventCount
    convert (Finset.sum_boole (R := ℂ) (fun x => f x = g) A).symm using 1 <;> congr
  rw [hcard]
  simp_rw [character_fiber_indicator]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => (Finset.sum_div _ _ _).symm)

theorem fiber_card_limit_of_character_cancellation {α G : Type*} [CommGroup G] [Fintype G]
    (A : ℕ → Finset α) (f : α → G) (s : ℕ → ℝ) {C : ℝ}
    (hA : Tendsto (fun N => ((A N).card : ℝ) / s N) atTop (𝓝 C))
    (hχ : ∀ ψ : AddChar (Additive G) ℂ, ψ ≠ 0 →
      Tendsto (fun N => (∑ x ∈ A N, ψ (Additive.ofMul (f x))) / (s N : ℂ)) atTop (𝓝 0))
    (g : G) :
    Tendsto (fun N => (eventCount (A N) (fun x => f x = g) : ℝ) / s N)
      atTop (𝓝 (C / Fintype.card G)) := by
  have htotal : Tendsto (fun N => ((A N).card : ℂ) / (s N : ℂ)) atTop (𝓝 (C : ℂ)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hA.ofReal
  have hterm (ψ : AddChar (Additive G) ℂ) :
      Tendsto (fun N => ((∑ x ∈ A N, ψ (Additive.ofMul (f x))) / ψ (Additive.ofMul g)) / (s N : ℂ))
        atTop (𝓝 (if ψ = 0 then (C : ℂ) else 0)) := by
    by_cases hψ : ψ = 0
    · subst ψ
      simpa only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one, div_one, if_true] using htotal
    · have h := (hχ ψ hψ).div_const (ψ (Additive.ofMul g))
      simp only [zero_div] at h
      rw [if_neg hψ]
      convert h using 1
      ext N
      ring
  have h := (tendsto_finsetSum Finset.univ (fun ψ _ => hterm ψ)).div_const (Fintype.card G : ℂ)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hfiber : Tendsto (fun N => (eventCount (A N) (fun x => f x = g) : ℂ) / (s N : ℂ))
      atTop (𝓝 ((C : ℂ) / (Fintype.card G : ℂ))) := by
    convert h using 1
    ext N
    rw [fiber_card_eq_character_sum, ← Finset.sum_div]
    ring
  have hre := (Complex.continuous_re.tendsto _).comp hfiber
  simpa only [Function.comp_def, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.ofReal_re] using hre

end Bernays

end

/-! ### Upstream module `Util/Bernays/SignedIdealProducts.lean` -/

section
/-!
# Realizing sign choices by ideals of unchanged norm
-/

namespace Bernays

theorem exists_ideal_of_signed_goodMaximals {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ σ : Fin k → Bool, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        J.idealClass = signedProduct σ (fun i => (P i).idealClass) ∧
          (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
            ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) :
              Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  letI := quadraticOrderIsDomain hD
  intro k P hP σ
  choose Q hQc hQN using fun i => goodMaximal_inverseClass_sameNorm hD (P i) (hP i).1 (hP i).2
  let T : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b) := fun i => if σ i then Q i else P i
  refine ⟨∏ i, T i, ?_, ?_⟩
  · rw [InvertibleIdeal.idealClass_prod, signedProduct]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : σ i
    · simp only [T, hi, Bool.false_eq_true, if_false]
    · simpa only [T, hi, if_true] using hQc i
  · rw [InvertibleIdeal.cardQuot_prod, InvertibleIdeal.cardQuot_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : σ i
    · simp only [T, hi, Bool.false_eq_true, if_false]
    · simpa only [T, hi, if_true] using hQN i

theorem exists_goodMaximal_tuple {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ k : ℕ, ∃ P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (∏ i, P i) = I ∧ ∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
          IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) := by
  letI := quadraticOrderIsDomain hD
  intro I hI
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hI
  refine ⟨l.length, l.get, ?_, fun i => hP _ (List.get_mem l i)⟩
  rw [← Fin.prod_ofFn, List.ofFn_get, hl]

theorem exists_squareSubgroup_of_missing_ideal_class {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))))
          (∏ i, (P i).idealClass) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) C →
      (∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
          ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot →
        J.idealClass ≠ C) →
      ∃ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))), H ≠ ⊤ ∧
        countOutsideSubgroup H (List.ofFn fun i => classSquareElement (P i).idealClass) <
          Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) := by
  classical
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  intro k P hP C hgenus hmiss
  apply exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
    (fun i => (P i).idealClass) C hgenus
  intro σ hσ
  obtain ⟨J, hJc, hJn⟩ := exists_ideal_of_signed_goodMaximals hD P hP σ
  exact hmiss J hJn (hJc.trans hσ)

end Bernays

end

/-! ### Upstream module `Util/Bernays/FewPrimeFactors.lean` -/

section
/-!
# Integers with few prime divisors from a divergent allowed family

The estimate is relative to the exact `x / sqrt(log x)` local count, rather
than merely an `o(x)` density estimate.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def fewPrimeFactorValues (S E : ℕ → Prop) (k N : ℕ) : Finset ℕ :=
  (localValues S N).filter fun n => (n.primeFactors.filter E).card ≤ k

theorem packetCount_dvd_le_primeFactors (P : Finset ℕ) (E : ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime ∧ E p) {n : ℕ} (hn : 0 < n) :
    packetCount P (fun p n => p ∣ n) n ≤ (n.primeFactors.filter E).card := by
  rw [packetCount_eq_eventCount]
  unfold eventCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  have h : p ∈ P ∧ p ∣ n := by simpa only [Finset.mem_filter] using hp
  exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨(hP p h.1).1, h.2, hn.ne'⟩, (hP p h.1).2⟩

theorem fewPrimeFactorValues_card_le_packet (S E : ℕ → Prop) (k N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ E p) :
    (fewPrimeFactorValues S E k N).card ≤
      eventCount (localValues S N) (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnA, hnk⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnA, ?_⟩
  have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnA).1).1
  exact (packetCount_dvd_le_primeFactors P E hP hnpos).trans (by exact_mod_cast hnk)

theorem eventually_fewPrimeFactorValues_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (E : ℕ → Prop)
    (hE : ∀ R : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ χ p ≠ -1 ∧ E p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) ≤ ε * scale N := by
  let C := characterLocalConstant χ / sqrt π
  have hC : 0 < C := div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)
  obtain ⟨P, hP, hmass⟩ := hE (max (2 * (k : ℝ)) (8 * C / ε))
  have hM : 0 < ∑ p ∈ P, (p : ℝ)⁻¹ :=
    (by positivity : (0 : ℝ) ≤ 2 * k).trans_lt ((le_max_left _ _).trans_lt hmass)
  have hk : 2 * (k : ℝ) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := (le_max_left _ _).trans hmass.le
  have hratio : 8 * C / (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ε := by
    apply (div_le_iff₀ hM).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hmass)
    nlinarith
  have hbound := eventually_local_fewPacketCount_le χ hχ₂ hχ P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) (Nat.cast_nonneg k) hM hk
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hN hN₂
  have hs : 0 < scale (N : ℝ) := scale_pos (by exact_mod_cast (show 1 < N by omega))
  have hle : ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) ≤
      (eventCount (localValues (fun p : ℕ => χ p = -1) N)
        (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) : ℝ) := by
    exact_mod_cast fewPrimeFactorValues_card_le_packet (fun p : ℕ => χ p = -1) E k N P
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩)
  exact (hle.trans hN).trans (mul_le_mul_of_nonneg_right hratio hs.le)

theorem fewPrimeFactorValues_div_scale_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (E : ℕ → Prop)
    (hE : ∀ R : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ χ p ≠ -1 ∧ E p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹)
    (k : ℕ) :
    Tendsto (fun N : ℕ => ((fewPrimeFactorValues (fun p : ℕ => χ p = -1) E k N).card : ℝ) /
      scale N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbound := eventually_fewPrimeFactorValues_le χ hχ₂ hχ E hE k (half_pos hε)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hN hN₂
  have hs : 0 < scale (N : ℝ) := scale_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hs.le)]
  exact ((div_le_iff₀ hs).mpr hN).trans_lt (half_lt_self hε)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareClassExceptional.lean` -/

section
/-!
# Negligibility of square-class prime obstructions
-/

open Filter Topology
open scoped Classical

namespace Bernays

def squareBadPrime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) → ℕ → Prop :=
  letI := quadraticOrderIsDomain hD
  fun H p => ∃ s : SplitPrime d b, s.1 = p ∧ classSquareElement (s.idealClass hD) ∉ H

theorem exists_squareBadPrime_natPacket {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ R : ℝ, ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ discriminantCharacter (b ^ 2 + 4 * d) hD.ne p ≠ -1 ∧
          squareBadPrime hD H p) ∧ R < ∑ p ∈ P, (p : ℝ)⁻¹ := by
  classical
  letI := quadraticOrderIsDomain hD
  intro H hH R
  obtain ⟨S, hS, hmass⟩ := exists_squareBadPrimePacket hD H hH R
  refine ⟨S.image (fun s : SplitPrime d b => s.1), ?_, ?_⟩
  · intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨s.2.1, SplitPrime.character_ne_neg_one hD.ne s, s, rfl, hS s hs⟩
  · rw [Finset.sum_image (fun (s : SplitPrime d b) _ (t : SplitPrime d b) _ h => Subtype.ext h)]
    exact hmass

theorem squareBadPrime_few_values_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ k : ℕ,
      Tendsto (fun N : ℕ =>
        ((fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
          (squareBadPrime hD H) k N).card : ℝ) / scale N) atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  letI : NeZero (discriminantLevel (b ^ 2 + 4 * d)) := ⟨(discriminantLevel_pos hD.ne).ne'⟩
  intro H hH k
  exact fewPrimeFactorValues_div_scale_tendsto_zero _ (discriminantCharacter_sq _ hD.ne)
    (discriminantCharacter_ne_one hD) _ (exists_squareBadPrime_natPacket hD H hH) k

end Bernays

end

/-! ### Upstream module `Util/Bernays/PrimeFactorConcentration.lean` -/

section
/-!
# From missing ideal classes to few rational prime factors
-/

open scoped Classical

namespace Bernays

theorem countOutsideSubgroup_ofFn {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) {k : ℕ} (x : Fin k → G) :
    countOutsideSubgroup H (List.ofFn x) = Nat.card {i : Fin k // x i ∉ H} := by
  classical
  have hlist (l : List G) : countOutsideSubgroup H l =
      (l.map fun a => if a ∉ H then 1 else 0).sum := by
    induction l with
    | nil => simp [countOutsideSubgroup]
    | cons a l ih =>
      by_cases ha : a ∈ H <;> simp [countOutsideSubgroup, ha] at * <;> omega
  rw [hlist, List.map_ofFn, Fin.sum_ofFn, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert Finset.sum_boole (R := ℕ) (fun i => x i ∉ H) Finset.univ using 1 <;>
    simp only [Function.comp_def, Nat.cast_id] <;> congr

theorem goodMaximal_unique_prime_divisor {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ q : ℕ, q.Prime ∧ ∀ p : ℕ, p.Prime →
        p ∣ (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot → p = q := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, _, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · refine ⟨q, hq, ?_⟩
    intro p hp hdvd
    rw [h.2.1] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
  · refine ⟨q, hq, ?_⟩
    intro p hp hdvd
    rw [s.ideal_cardQuot hD ε, hs] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd

theorem SplitPrime.oriented_squareClass_mem_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      ∀ ε : Bool, classSquareElement (s.ideal hD ε).idealClass ∈ H ↔
        classSquareElement (s.idealClass hD) ∈ H := by
  letI := quadraticOrderIsDomain hD
  intro H ε
  cases ε
  · rfl
  · have heq : classSquareElement (s.ideal hD true).idealClass =
        (classSquareElement (s.idealClass hD))⁻¹ := by
      apply Subtype.ext
      simp only [classSquareElement, s.idealClass_conjugate hD, inv_pow, Subgroup.coe_inv]
    rw [heq, H.inv_mem_iff]

theorem goodMaximal_squareClass_outside_of_bad_dvd {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      ∀ s : SplitPrime d b, classSquareElement (s.idealClass hD) ∉ H →
      s.1 ∣ (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot → classSquareElement P.idealClass ∉ H := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF H s hs hdvd
  obtain ⟨q, hq, _, h | ⟨t, ht, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1] at hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq s.2.1 hq).mp (s.2.1.dvd_of_dvd_pow hdvd)
    exact False.elim (s.character_ne_neg_one hD.ne (heq ▸ h.1))
  · rw [t.ideal_cardQuot hD ε] at hdvd
    have hst : s = t := Subtype.ext ((Nat.prime_dvd_prime_iff_eq s.2.1 t.2.1).mp hdvd)
    subst t
    exact fun h => hs ((s.oriented_squareClass_mem_iff hD H ε).mp h)

theorem badPrimeFactors_card_le_outside_coordinates {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
        ((((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) :
          Ideal (QuadraticAlgebra ℤ d b)).cardQuot).primeFactors.filter (squareBadPrime hD H)).card ≤
          countOutsideSubgroup H (List.ofFn fun i => classSquareElement (P i).idealClass) := by
  classical
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) := Fintype.ofFinite _
  intro k P hP H
  let n := ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot
  let A := n.primeFactors.filter (squareBadPrime hD H)
  let X := {p // p ∈ A}
  let Y := {i : Fin k // classSquareElement (P i).idealClass ∉ H}
  have hex (p : X) : ∃ i : Y, p.1 ∣ (P i.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
    obtain ⟨hpN, hpBad⟩ := Finset.mem_filter.mp p.2
    obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp hpN
    change p.1 ∣ ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hpn
    rw [InvertibleIdeal.cardQuot_prod] at hpn
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff
      (fun i => (P i : Ideal (QuadraticAlgebra ℤ d b)).cardQuot)).mp hpn
    obtain ⟨s, hs, hsb⟩ := hpBad
    refine ⟨⟨i, goodMaximal_squareClass_outside_of_bad_dvd hD (P i) (hP i).1 (hP i).2 H s hsb ?_⟩, hi⟩
    simpa only [hs] using hi
  let f : X → Y := fun p => (hex p).choose
  have hf : Function.Injective f := by
    intro p q hpq
    have hpdiv := (hex p).choose_spec
    have hqdiv := (hex q).choose_spec
    change p.1 ∣ (P (f p).1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hpdiv
    change q.1 ∣ (P (f q).1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hqdiv
    rw [← hpq] at hqdiv
    obtain ⟨r, _, hr⟩ := goodMaximal_unique_prime_divisor hD (P (f p).1) (hP _).1 (hP _).2
    have hpprime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp p.2).1).1
    have hqprime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp q.2).1).1
    exact Subtype.ext ((hr p.1 hpprime hpdiv).trans (hr q.1 hqprime hqdiv).symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [show Nat.card X = A.card from Nat.card_eq_fintype_card.trans (Fintype.card_coe A)] at hc
  rw [countOutsideSubgroup_ofFn]
  exact hc

end Bernays

end

/-! ### Upstream module `Util/Bernays/SquareExceptionalUnion.lean` -/

section
/-!
# One negligible exceptional set for all form classes of a discriminant
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem finiteUnion_card_div_tendsto_zero {α ι : Type*} [DecidableEq α] [Fintype ι]
    (F : ι → ℕ → Finset α) (s : ℕ → ℝ) (hs : ∀ N, 0 ≤ s N)
    (hF : ∀ i, Tendsto (fun N => ((F i N).card : ℝ) / s N) atTop (𝓝 0)) :
    Tendsto (fun N => ((Finset.univ.biUnion fun i => F i N).card : ℝ) / s N) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hF i)
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (hs N)) _ hsum
  intro N
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (hs N)
  exact_mod_cast Finset.card_biUnion_le

noncomputable def squareExceptionalValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (k N : ℕ) : Finset ℕ := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  let G := ClassGroup (QuadraticAlgebra ℤ d b)
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup G)) := Fintype.ofFinite _
  exact Finset.univ.biUnion fun H : Subgroup (classSquareSubgroup : Subgroup G) =>
    if H = ⊤ then ∅ else
      fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
        (squareBadPrime hD H) k N

theorem squareExceptionalValues_div_scale_tendsto_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((squareExceptionalValues hD k N).card : ℝ) / scale N) atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  let G := ClassGroup (QuadraticAlgebra ℤ d b)
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup G)) := Fintype.ofFinite _
  apply finiteUnion_card_div_tendsto_zero _ (fun N => scale N)
    (fun N => div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))
  intro H
  by_cases hH : H = ⊤
  · simp only [if_pos hH, Finset.card_empty, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  · simp only [if_neg hH]
    exact squareBadPrime_few_values_limit hD H hH k

theorem mem_squareExceptionalValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ k N n : ℕ,
      n ∈ fewPrimeFactorValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1)
        (squareBadPrime hD H) k N → n ∈ squareExceptionalValues hD k N := by
  letI := quadraticOrderIsDomain hD
  intro H hH k N n hn
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) :=
    Fintype.ofFinite _
  unfold squareExceptionalValues
  exact Finset.mem_biUnion.mpr ⟨H, Finset.mem_univ _, by simpa only [if_neg hH] using hn⟩

theorem missing_same_genus_mem_exceptional {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) I.idealClass =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) C →
      (∀ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot →
        J.idealClass ≠ C) →
      ∀ N : ℕ, (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∈
        localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) N →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∈ squareExceptionalValues hD
        (Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) N := by
  letI := quadraticOrderIsDomain hD
  intro I hIF C hIC hmiss N hIN
  obtain ⟨k, P, hPI, hP⟩ := exists_goodMaximal_tuple hD I hIF
  have hclass : (∏ i, (P i).idealClass) = I.idealClass := by
    rw [← InvertibleIdeal.idealClass_prod, hPI]
  obtain ⟨H, hH, hfew⟩ := exists_squareSubgroup_of_missing_ideal_class hD P hP C
    (hclass ▸ hIC) (by simpa only [hPI] using hmiss)
  apply mem_squareExceptionalValues hD H hH _ N _
  apply Finset.mem_filter.mpr
  refine ⟨hIN, ?_⟩
  have hcount := badPrimeFactors_card_le_outside_coordinates hD P hP H
  rw [hPI] at hcount
  exact (hcount.trans_lt hfew).le

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodClassCounts.lean` -/

section
/-!
# Class counts differ from genus counts by a negligible exceptional set
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def genusValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    GenusGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun g N => (localValues (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) N).filter
    fun n => n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧ genusValue hD n = g

end Bernays

end

/-! ### Upstream module `Util/Bernays/GoodClassAsymptotic.lean` -/

section
/-!
# The same positive leading constant for all coprime ideal classes
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem genusLocal_character_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ goodLocalValues d b hD.ne N, ψ (Additive.ofMul (genusValue hD n))) / (scale N : ℂ))
        atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := genusLocal_sharp_norm_cancellation hD ψ hψ
  apply h.congr'
  filter_upwards [] with N
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg
    (show 0 ≤ scale N from div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)), genusLocalAF_sum]

noncomputable def goodClassConstant {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ℝ :=
  letI := quadraticOrderIsDomain hD
  goodLocalConstant d b hD.ne / Nat.card (GenusGroup (QuadraticAlgebra ℤ d b))

theorem goodClassConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : 0 < goodClassConstant hD := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  change 0 < goodLocalConstant d b hD.ne / (Nat.card (GenusGroup (QuadraticAlgebra ℤ d b)) : ℝ)
  exact div_pos (goodLocalConstant_pos hD) (Nat.cast_pos.mpr Nat.card_pos)

theorem genusValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ g : GenusGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ((genusValues hD g N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (GenusGroup (QuadraticAlgebra ℤ d b)) := Fintype.ofFinite _
  intro g
  have h := fiber_card_limit_of_character_cancellation (goodLocalValues d b hD.ne)
    (genusValue hD) (fun N : ℕ => scale N) (goodLocalValues_card_limit hD)
    (genusLocal_character_cancellation hD) g
  have hcount (N : ℕ) : eventCount (goodLocalValues d b hD.ne N) (fun n => genusValue hD n = g) =
      (genusValues hD g N).card := by
    unfold eventCount goodLocalValues genusValues
    rw [Finset.filter_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter]
  simpa only [hcount, goodClassConstant, Nat.card_eq_fintype_card] using h

end Bernays

end

/-! ### Upstream module `Util/Bernays/NormGenusSets.lean` -/

section
/-!
# The finite genus sets of ideals of a prescribed norm
-/

open scoped Classical

namespace Bernays

noncomputable def normGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (m : ℕ) :
    letI := quadraticOrderIsDomain hD
    Finset (GenusGroup (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  letI := quadraticOrderClassGroupFintype hD
  letI : Fintype (GenusGroup (QuadraticAlgebra ℤ d b)) := Fintype.ofFinite _
  exact Finset.univ.filter fun g => ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧ genusMap J.idealClass = g

theorem mem_normGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (m : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ g : GenusGroup (QuadraticAlgebra ℤ d b),
      g ∈ normGenusSet hD m ↔ ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧ genusMap J.idealClass = g := by
  letI := quadraticOrderIsDomain hD
  intro g
  simp only [normGenusSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normGenusSet_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    normGenusSet hD 1 = {1} := by
  letI := quadraticOrderIsDomain hD
  ext g
  rw [mem_normGenusSet, Finset.mem_singleton]
  constructor
  · rintro ⟨J, hJ, hg⟩
    have hJ₁ : J = 1 := InvertibleIdeal.ext (Submodule.cardQuot_eq_one_iff.mp hJ)
    simpa only [hJ₁, InvertibleIdeal.idealClass_one, map_one] using hg.symm
  · intro hg
    refine ⟨1, ?_, ?_⟩
    · exact Submodule.cardQuot_top _ _
    · simp only [InvertibleIdeal.idealClass_one, map_one, hg]

noncomputable def remainderGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset (GenusGroup (QuadraticAlgebra ℤ d b)) :=
  letI := quadraticOrderIsDomain hD
  fun C m => (normGenusSet hD m).image (fun g => genusMap C * g⁻¹)

theorem remainderGenusSet_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ m : ℕ,
      (remainderGenusSet hD C m).card = (normGenusSet hD m).card := by
  letI := quadraticOrderIsDomain hD
  intro C m
  apply Finset.card_image_of_injective
  intro g h heq
  exact inv_injective (mul_left_cancel heq)

theorem mem_remainderGenusSet {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ) (g : GenusGroup (QuadraticAlgebra ℤ d b)),
      g ∈ remainderGenusSet hD C m ↔ ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧
          genusMap (C * J.idealClass⁻¹) = g := by
  letI := quadraticOrderIsDomain hD
  intro C m g
  rw [remainderGenusSet, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, heq⟩
    obtain ⟨J, hJ, hgen⟩ := (mem_normGenusSet hD m h).mp hh
    refine ⟨J, hJ, ?_⟩
    rw [map_mul, map_inv, hgen]
    exact heq
  · rintro ⟨J, hJ, heq⟩
    refine ⟨genusMap J.idealClass, (mem_normGenusSet hD m _).mpr ⟨J, hJ, rfl⟩, ?_⟩
    simpa only [map_mul, map_inv] using heq

end Bernays

end

/-! ### Upstream module `Util/Bernays/GenusSlices.lean` -/

section
/-!
# Genus slices at a fixed discriminant-prime part
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def genusSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C m N => (goodLocalValues d b hD.ne N).filter fun n =>
    genusValue hD n ∈ remainderGenusSet hD C m

theorem genusValues_eq_goodLocal_filter {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (g : GenusGroup (QuadraticAlgebra ℤ d b)) (N : ℕ),
      genusValues hD g N = (goodLocalValues d b hD.ne N).filter (fun n => genusValue hD n = g) := by
  letI := quadraticOrderIsDomain hD
  intro g N
  ext n
  simp only [genusValues, goodLocalValues, Finset.mem_filter, and_assoc]

theorem genusSliceValues_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m N : ℕ),
      (genusSliceValues hD C m N).card =
        ∑ g ∈ remainderGenusSet hD C m, (genusValues hD g N).card := by
  letI := quadraticOrderIsDomain hD
  intro C m N
  simp_rw [genusValues_eq_goodLocal_filter]
  exact (Finset.sum_card_fiberwise_eq_card_filter (goodLocalValues d b hD.ne N)
    (remainderGenusSet hD C m) (genusValue hD)).symm

theorem genusSliceValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      Tendsto (fun N : ℕ => ((genusSliceValues hD C m N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card)) := by
  letI := quadraticOrderIsDomain hD
  intro C m
  have h := tendsto_finsetSum (remainderGenusSet hD C m) (fun g _ => genusValues_card_limit hD g)
  simp only [Finset.sum_const, nsmul_eq_mul, remainderGenusSet_card] at h
  rw [mul_comm] at h
  apply h.congr'
  filter_upwards [] with N
  rw [genusSliceValues_card, Nat.cast_sum, Finset.sum_div]

end Bernays

end

/-! ### Upstream module `Util/Bernays/SmoothDecomposition.lean` -/

section
/-!
# Unique separation of a positive integer into its finite-prime and coprime parts
-/

open scoped Classical

namespace Bernays

def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ := (n.primeFactorsList.filter (· ∈ P)).prod

def avoidingPart (P : Finset ℕ) (n : ℕ) : ℕ := (n.primeFactorsList.filter (· ∉ P)).prod

theorem smoothPart_mem (P : Finset ℕ) (n : ℕ) : smoothPart P n ∈ Nat.factoredNumbers P :=
  Nat.prod_mem_factoredNumbers P n

theorem avoidingPart_pos (P : Finset ℕ) (n : ℕ) : 0 < avoidingPart P n := by
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro h
  have hprime := Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter h)
  exact Nat.not_prime_zero hprime

theorem smoothPart_mul_avoidingPart (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothPart P n * avoidingPart P n = n := by
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => p ∈ P) id n.primeFactorsList
  simpa only [smoothPart, avoidingPart, List.map_id, Nat.prod_primeFactorsList hn] using h

theorem avoidingPart_not_dvd (P : Finset ℕ) (n : ℕ) {p : ℕ} (hp : p.Prime) (hP : p ∈ P) :
    ¬ p ∣ avoidingPart P n := by
  intro hdvd
  have hmem := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hdvd
  have hnot : p ∉ P := by
    simpa only [decide_eq_true_eq] using List.of_mem_filter hmem
  exact hnot hP

theorem factored_coprime_of_avoiding {P : Finset ℕ} {m k : ℕ}
    (hm : m ∈ Nat.factoredNumbers P) (hk : ∀ p ∈ P, p.Prime → ¬ p ∣ k) : m.Coprime k := by
  by_contra h
  obtain ⟨p, hp, hpm, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hk p (Nat.mem_factoredNumbers'.mp hm p hp hpm) hp hpk

theorem smooth_decomposition_unique {P : Finset ℕ} {m k m' k' : ℕ}
    (hm : m ∈ Nat.factoredNumbers P) (hm' : m' ∈ Nat.factoredNumbers P)
    (hk : ∀ p ∈ P, p.Prime → ¬ p ∣ k) (hk' : ∀ p ∈ P, p.Prime → ¬ p ∣ k')
    (heq : m * k = m' * k') : m = m' ∧ k = k' := by
  have hc := factored_coprime_of_avoiding hm hk'
  have hc' := factored_coprime_of_avoiding hm' hk
  have hdiv : m ∣ m' := hc.dvd_mul_right.mp (heq ▸ dvd_mul_right m k)
  have hdiv' : m' ∣ m := hc'.dvd_mul_right.mp (heq.symm ▸ dvd_mul_right m' k')
  have heqm : m = m' := Nat.dvd_antisymm hdiv hdiv'
  refine ⟨heqm, ?_⟩
  rw [← heqm] at heq
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hm.1) heq

theorem avoidingPart_coprime {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    (avoidingPart M.primeFactors n).Coprime M := by
  by_contra h
  obtain ⟨p, hp, hpk, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact avoidingPart_not_dvd M.primeFactors n hp (Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩) hpk

theorem factored_coprime_of_coprime_level {M m k : ℕ}
    (hm : m ∈ Nat.factoredNumbers M.primeFactors) (hk : k.Coprime M) : m.Coprime k := by
  apply factored_coprime_of_avoiding hm
  intro p hp hprime hpk
  have hpM := (Nat.mem_primeFactors.mp hp).2.1
  exact hprime.not_dvd_one (hk.gcd_eq_one ▸ Nat.dvd_gcd hpk hpM)

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassSlices.lean` -/

section
/-!
# Class slices and their common negligible exceptional set
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def classSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C m N => (Finset.Icc 1 N).filter fun n =>
    n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m * n ∧ I.idealClass = C

theorem classSliceValues_subset_genusSliceValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, classSliceValues hD C m N ⊆ genusSliceValues hD C m N := by
  letI := quadraticOrderIsDomain hD
  intro C m hm N n hn
  obtain ⟨hnN, hnc, I, hIn, hIC⟩ := Finset.mem_filter.mp hn
  obtain ⟨J, K, hJK, hJ, hK⟩ := exists_coprime_norm_factors hD I m n
    (factored_coprime_of_coprime_level hm hnc) hIn
  have hKF : IsCoprime (K : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    K.coprime_scalar_of_cardQuot_coprime _ (hK.symm ▸ hnc)
  have hclass : K.idealClass = C * J.idealClass⁻¹ := by
    rw [← hIC, ← hJK, InvertibleIdeal.idealClass_mul]
    rw [mul_comm J.idealClass K.idealClass, mul_assoc, mul_inv_cancel, mul_one]
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnN,
      by simpa only [hK] using local_of_goodIdeal_norm hD K hKF⟩, hnc⟩
  · apply (mem_remainderGenusSet hD C m (genusValue hD n)).mpr
    refine ⟨J, hJ, ?_⟩
    rw [← hclass, ← genusValue_goodIdeal_norm hD K hKF, hK]

theorem genusSlice_sdiff_classSlice_subset_exceptional {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m N : ℕ),
      genusSliceValues hD C m N \ classSliceValues hD C m N ⊆ squareExceptionalValues hD
        (Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))) N := by
  letI := quadraticOrderIsDomain hD
  intro C m N n hn
  obtain ⟨hng, hnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hngood, hngen⟩ := Finset.mem_filter.mp hng
  obtain ⟨hnlocal, hnc⟩ := Finset.mem_filter.mp hngood
  obtain ⟨hnN, hnpar⟩ := Finset.mem_filter.mp hnlocal
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hnN).1
  obtain ⟨J, hJ, hJgen⟩ := (mem_remainderGenusSet hD C m (genusValue hD n)).mp hngen
  obtain ⟨K, hK⟩ := exists_ideal_norm_of_local hD n hn₀ hnc hnpar
  have hKF : IsCoprime (K : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    K.coprime_scalar_of_cardQuot_coprime _ (hK.symm ▸ hnc)
  have hgen : genusMap K.idealClass = genusMap (C * J.idealClass⁻¹) := by
    rw [← genusValue_goodIdeal_norm hD K hKF, hK]
    exact hJgen.symm
  have hmiss (L : InvertibleIdeal (QuadraticAlgebra ℤ d b))
      (hL : (L : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
        (K : Ideal (QuadraticAlgebra ℤ d b)).cardQuot) : L.idealClass ≠ C * J.idealClass⁻¹ := by
    intro hLC
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨hnN, hnc, J * L, ?_, ?_⟩
    · rw [InvertibleIdeal.cardQuot_mul, hJ, hL, hK]
    · rw [InvertibleIdeal.idealClass_mul, hLC]
      rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hex := missing_same_genus_mem_exceptional hD K hKF (C * J.idealClass⁻¹) hgen hmiss N
    (hK.symm ▸ hnlocal)
  simpa only [hK] using hex

theorem classSlice_genus_count_error_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ =>
        (((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card) / scale N)
        atTop (𝓝 0) := by
  letI := quadraticOrderIsDomain hD
  intro C m hm
  let k := Nat.card (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))
  have heq (N : ℕ) : ((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card =
      ((genusSliceValues hD C m N \ classSliceValues hD C m N).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card (classSliceValues_subset_genusSliceValues hD C m hm N)
    have h' : ((genusSliceValues hD C m N \ classSliceValues hD C m N).card : ℝ) +
        (classSliceValues hD C m N).card = (genusSliceValues hD C m N).card := by exact_mod_cast h
    linarith
  apply squeeze_zero _ _ (squareExceptionalValues_div_scale_tendsto_zero hD k)
  · intro N
    rw [heq N]
    exact div_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  · intro N
    rw [heq N]
    apply div_le_div_of_nonneg_right _ (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    exact_mod_cast Finset.card_le_card (genusSlice_sdiff_classSlice_subset_exceptional hD C m N)

theorem classSliceValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ => ((classSliceValues hD C m N).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card)) := by
  letI := quadraticOrderIsDomain hD
  intro C m hm
  have h := (genusSliceValues_card_limit hD C m).sub (classSlice_genus_count_error_limit hD C m hm)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  change ((genusSliceValues hD C m N).card : ℝ) / scale N -
    (((genusSliceValues hD C m N).card : ℝ) - (classSliceValues hD C m N).card) / scale N = _
  ring

end Bernays

end

/-! ### Upstream module `Util/Bernays/DilatedCountBound.lean` -/

section
/-!
# A summable majorant for all fixed-factor counting slices
-/

namespace Bernays

theorem sqrt_log_mul_bound {m k x : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hx : 0 < x) (hupper : x ≤ 2 * m * k) :
    Real.sqrt (Real.log x) ≤ 2 * Real.sqrt m * (1 + Real.sqrt (Real.log k)) := by
  have hm₀ : 0 < m := zero_lt_one.trans_le hm
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  have hlog := Real.log_le_log hx hupper
  rw [Real.log_mul (mul_pos (by norm_num) hm₀).ne' hk₀.ne',
    Real.log_mul (by norm_num) hm₀.ne'] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hlogm := Real.log_le_self hm₀.le
  have hlogk := Real.log_nonneg hk
  have hsm := Real.sq_sqrt hm₀.le
  have hsk := Real.sq_sqrt hlogk
  have hsm₁ : 1 ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) hm₀.le).mpr (by simpa using hm)
  have hsum : Real.sqrt (Real.log x) ≤ 1 + Real.sqrt m + Real.sqrt (Real.log k) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg (Real.log k)]
  apply hsum.trans
  have hprod := mul_nonneg (sub_nonneg.mpr hsm₁) (Real.sqrt_nonneg (Real.log k))
  nlinarith [Real.sqrt_nonneg (Real.log k)]

theorem count_dilation_scale_bound {A : ℕ → ℝ} (hA₀ : A 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    A (N / m) / scale N ≤ 2 * C / Real.sqrt (m : ℝ) := by
  by_cases hN : N < 2
  · interval_cases N <;> simp only [scale, Nat.cast_zero, Nat.cast_one, Real.log_zero,
      Real.log_one, Real.sqrt_zero, div_zero] <;> positivity
  by_cases hk : N / m = 0
  · rw [hk, hA₀, zero_div]
    positivity
  let k := N / m
  have hk₀ : 0 < k := Nat.pos_of_ne_zero hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₀
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hmk : (m : ℝ) * k ≤ N := by exact_mod_cast Nat.mul_div_le N m
  have hNk : (N : ℝ) ≤ 2 * m * k := by
    have h := Nat.lt_mul_div_succ N hm
    have h' : N < m * (k + 1) := h
    have h'' : N ≤ 2 * m * k := by nlinarith
    exact_mod_cast h''
  have hlog := sqrt_log_mul_bound (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    (show (1 : ℝ) ≤ k by exact_mod_cast hk₀) (zero_lt_one.trans hNR) hNk
  have hden : 0 < 1 + Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hslog : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hmain : A k * Real.sqrt (Real.log (N : ℝ)) / N ≤
      (C * k / (1 + Real.sqrt (Real.log (k : ℝ)))) * Real.sqrt (Real.log (N : ℝ)) /
        ((m : ℝ) * k) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcount k) hslog)
      (Nat.cast_nonneg N)).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hmR hkR) hmk
  have hcancel : (C * k / (1 + Real.sqrt (Real.log (k : ℝ)))) * Real.sqrt (Real.log (N : ℝ)) /
      ((m : ℝ) * k) = C * Real.sqrt (Real.log (N : ℝ)) /
        ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) := by field_simp
  rw [hcancel] at hmain
  have hbound : C * Real.sqrt (Real.log (N : ℝ)) /
      ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) ≤ 2 * C / Real.sqrt (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hC
    apply (div_le_iff₀ (mul_pos hmR hden)).mpr
    have hid : (2 * C / Real.sqrt (m : ℝ)) *
        ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) =
        C * (2 * Real.sqrt (m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) := by
      have hsquare := Real.sq_sqrt hmR.le
      field_simp
      nlinarith
    rw [hid]
    exact hmul
  have heq : A (N / m) / scale N = A k * Real.sqrt (Real.log (N : ℝ)) / N := by
    dsimp only [scale, k]
    rw [div_div_eq_mul_div]
  rw [heq]
  exact hmain.trans hbound

end Bernays

end

/-! ### Upstream module `Util/Bernays/ClassSliceDilation.lean` -/

section
/-!
# Fixed-factor class limits and their uniform summable bound
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem classSliceValues_zero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      classSliceValues hD C m 0 = ∅ := by
  letI := quadraticOrderIsDomain hD
  intro C m
  simp [classSliceValues]

theorem classSliceValues_card_le_goodLocal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, (classSliceValues hD C m N).card ≤ (goodLocalValues d b hD.ne N).card := by
  letI := quadraticOrderIsDomain hD
  intro C m hm N
  apply Finset.card_le_card
  exact (classSliceValues_subset_genusSliceValues hD C m hm N).trans (Finset.filter_subset _ _)

theorem classSliceValues_card_dilation_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      Tendsto (fun N : ℕ => ((classSliceValues hD C m (N / m)).card : ℝ) / scale N)
        atTop (𝓝 (goodClassConstant hD * (normGenusSet hD m).card / m)) := by
  letI := quadraticOrderIsDomain hD
  intro C m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm.1
  have h := (count_floor_dilation_limit (classSliceValues_card_limit hD C m hm)
    (one_div_pos.mpr hmR)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast,
    mul_one_div] using h

theorem exists_classSlice_dilation_bound {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ B : ℝ, 0 < B ∧ ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (m : ℕ),
      m ∈ Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors →
      ∀ N : ℕ, ‖((classSliceValues hD C m (N / m)).card : ℝ) / scale N‖ ≤
        B / Real.sqrt (m : ℝ) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨B, hB, hcount⟩ := exists_logCountBound_of_limit
    (fun N => Nat.cast_nonneg (goodLocalValues d b hD.ne N).card)
    (fun N => (Nat.cast_le (α := ℝ)).mpr (goodLocalValues_card_le hD.ne N))
    (goodLocalConstant_pos hD).le (goodLocalValues_card_limit hD)
  refine ⟨2 * B, mul_pos (by norm_num) hB, fun C m hm N => ?_⟩
  have hs : 0 ≤ scale (N : ℝ) := div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hs)]
  apply count_dilation_scale_bound (A := fun k => ((classSliceValues hD C m k).card : ℝ))
    (by rw [classSliceValues_zero, Finset.card_empty, Nat.cast_zero])
    hB.le _ (Nat.pos_of_ne_zero hm.1) N
  intro k
  exact ((Nat.cast_le (α := ℝ)).mpr (classSliceValues_card_le_goodLocal hD C m hm k)).trans (hcount k)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SmoothSummability.lean` -/

section
/-!
# Summability of reciprocal square roots on a fixed finite prime support
-/

namespace Bernays

theorem sqrt_nat_pow (p k : ℕ) : Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt (p : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ih, pow_succ]

theorem summable_factored_inv_sqrt (P : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers P => 1 / Real.sqrt (m.val : ℝ)) := by
  let f : ℕ → ℝ := fun n => 1 / Real.sqrt (n : ℝ)
  have hf₁ : f 1 = 1 := by simp [f]
  have hmul {m n : ℕ} (_ : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), one_div, mul_inv]
  have hsum {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖f (p ^ k)‖) := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hs : 1 < Real.sqrt (p : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hpR
    have hr : 1 / Real.sqrt (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hs
    have hg := summable_geometric_of_lt_one (by positivity : 0 ≤ 1 / Real.sqrt (p : ℝ)) hr
    have hge : Summable (fun k : ℕ => f (p ^ k)) := by
      simpa only [f, sqrt_nat_pow, one_div, inv_pow] using hg
    apply hge.congr
    intro k
    exact (Real.norm_of_nonneg (by dsimp only [f]; positivity)).symm
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁
    (fun h => hmul h) (fun hp => hsum hp) P).1
  exact h.of_norm

end Bernays

end

/-! ### Upstream module `Util/Bernays/FullClassConstant.lean` -/

section
/-!
# The convergent, positive common constant, including discriminant-prime factors
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def fullClassConstant {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ℝ :=
  letI := quadraticOrderIsDomain hD
  ∑' m : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
    goodClassConstant hD * (normGenusSet hD m.val).card / m.val

theorem summable_fullClassCoefficients {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Summable (fun m : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors =>
      goodClassConstant hD * (normGenusSet hD m.val).card / m.val) := by
  letI := quadraticOrderIsDomain hD
  obtain ⟨B, hB, hbound⟩ := exists_classSlice_dilation_bound hD
  have hs : Summable (fun m : Nat.factoredNumbers
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors => B / Real.sqrt (m.val : ℝ)) := by
    simpa only [mul_one_div] using (summable_factored_inv_sqrt
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors).mul_left B
  apply hs.of_norm_bounded
  intro m
  exact le_of_tendsto (classSliceValues_card_dilation_limit hD 1 m.val m.property).norm
    (Eventually.of_forall fun N => hbound 1 m.val m.property N)

theorem fullClassConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    0 < fullClassConstant hD := by
  letI := quadraticOrderIsDomain hD
  let m₁ : Nat.factoredNumbers (discriminantLevel (b ^ 2 + 4 * d)).primeFactors :=
    ⟨1, Nat.mem_factoredNumbers'.mpr (fun p hp hp₁ => (hp.not_dvd_one hp₁).elim)⟩
  have hpos : 0 < goodClassConstant hD * (normGenusSet hD m₁.val).card / m₁.val := by
    simpa only [m₁, normGenusSet_one, Finset.card_singleton, Nat.cast_one, mul_one, div_one]
      using goodClassConstant_pos hD
  exact (summable_fullClassCoefficients hD).tsum_pos
    (fun m => div_nonneg (mul_nonneg (goodClassConstant_pos hD).le (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) m₁ hpos

theorem classSlice_tsum_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ∑' m : Nat.factoredNumbers
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
        ((classSliceValues hD C m.val (N / m.val)).card : ℝ) / scale N)
      atTop (𝓝 (fullClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  intro C
  obtain ⟨B, hB, hbound⟩ := exists_classSlice_dilation_bound hD
  have hs : Summable (fun m : Nat.factoredNumbers
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors => B / Real.sqrt (m.val : ℝ)) := by
    simpa only [mul_one_div] using (summable_factored_inv_sqrt
      (discriminantLevel (b ^ 2 + 4 * d)).primeFactors).mul_left B
  exact tendsto_tsum_of_dominated_convergence hs
    (fun m => classSliceValues_card_dilation_limit hD C m.val m.property)
    (Eventually.of_forall fun N m => hbound C m.val m.property N)

end Bernays

end

/-! ### Upstream module `Util/Bernays/SmoothCounting.lean` -/

section
/-!
# Exact counting by the unique discriminant-prime part
-/

open scoped Classical

namespace Bernays

noncomputable def positiveValues (R : ℕ → Prop) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter R

noncomputable def smoothValues (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m => m ∈ Nat.factoredNumbers P

noncomputable def coprimeSliceValues (R : ℕ → Prop) (M m N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun k => k.Coprime M ∧ R (m * k)

theorem coprime_avoids_primeFactors {k M : ℕ} (hk : k.Coprime M) :
    ∀ p ∈ M.primeFactors, p.Prime → ¬ p ∣ k := by
  intro p hp hprime hpk
  exact hprime.not_dvd_one (hk.gcd_eq_one ▸ Nat.dvd_gcd hpk (Nat.mem_primeFactors.mp hp).2.1)

theorem positiveValues_card_smooth_sum (R : ℕ → Prop) {M : ℕ} (hM : M ≠ 0) (N : ℕ) :
    (positiveValues R N).card = ∑ m ∈ smoothValues M.primeFactors N,
      (coprimeSliceValues R M m (N / m)).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun a _ => a.1 * a.2)
  · intro a ha
    obtain ⟨hm, hk⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hmI, hms⟩ := Finset.mem_filter.mp hm
    obtain ⟨hkI, hkc, hR⟩ := Finset.mem_filter.mp hk
    obtain ⟨hmpos, hmN⟩ := Finset.mem_Icc.mp hmI
    obtain ⟨hkpos, hkN⟩ := Finset.mem_Icc.mp hkI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hmpos hkpos, ?_⟩, hR⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hkN
  · intro a ha b hb heq
    obtain ⟨ham, hak⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hbm, hbk⟩ := Finset.mem_sigma.mp hb
    have ham' := (Finset.mem_filter.mp ham).2
    have hbm' := (Finset.mem_filter.mp hbm).2
    have hak' := (Finset.mem_filter.mp hak).2.1
    have hbk' := (Finset.mem_filter.mp hbk).2.1
    have h := smooth_decomposition_unique ham' hbm'
      (coprime_avoids_primeFactors hak') (coprime_avoids_primeFactors hbk') heq
    cases a
    cases b
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro n hn
    obtain ⟨hnI, hnR⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    let m := smoothPart M.primeFactors n
    let k := avoidingPart M.primeFactors n
    have hms : m ∈ Nat.factoredNumbers M.primeFactors := smoothPart_mem _ _
    have hmpos : 0 < m := Nat.pos_of_ne_zero hms.1
    have hkpos : 0 < k := avoidingPart_pos _ _
    have hmk : m * k = n := smoothPart_mul_avoidingPart _ (by omega)
    have hmN : m ≤ N := by nlinarith
    have hkN : k ≤ N / m := by
      apply (Nat.le_div_iff_mul_le hmpos).mpr
      rw [Nat.mul_comm k m, hmk]
      exact hnN
    refine ⟨⟨m, k⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, hmk⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩, hms⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkN⟩,
        avoidingPart_coprime hM n, hmk.symm ▸ hnR⟩

end Bernays

end

/-! ### Upstream module `Util/Bernays/SmoothCountingSeries.lean` -/

section
/-!
# The exact smooth-part decomposition as a series
-/

open scoped Classical

namespace Bernays

theorem coprimeSliceValues_eq_empty_of_lt (R : ℕ → Prop) {M m N : ℕ} (hNm : N < m) :
    coprimeSliceValues R M m (N / m) = ∅ := by
  simp [coprimeSliceValues, Nat.div_eq_of_lt hNm]

theorem positiveValues_card_eq_tsum (R : ℕ → Prop) {M : ℕ} (hM : M ≠ 0) (N : ℕ) :
    ((positiveValues R N).card : ℝ) = ∑' m : Nat.factoredNumbers M.primeFactors,
      ((coprimeSliceValues R M m.val (N / m.val)).card : ℝ) := by
  let S := (Finset.Icc 1 N).subtype (fun m => m ∈ Nat.factoredNumbers M.primeFactors)
  have hz (m : Nat.factoredNumbers M.primeFactors) (hm : m ∉ S) :
      ((coprimeSliceValues R M m.val (N / m.val)).card : ℝ) = 0 := by
    have hmpos : 0 < m.val := Nat.pos_of_ne_zero m.property.1
    have hNm : N < m.val := by
      have hnot : m.val ∉ Finset.Icc 1 N := by simpa only [S, Finset.mem_subtype] using hm
      simp only [Finset.mem_Icc, not_and] at hnot
      exact Nat.lt_of_not_ge (hnot hmpos)
    rw [coprimeSliceValues_eq_empty_of_lt R hNm, Finset.card_empty, Nat.cast_zero]
  rw [tsum_eq_sum hz]
  dsimp only [S]
  rw [Finset.sum_subtype_eq_sum_filter
    (fun m : ℕ => ((coprimeSliceValues R M m (N / m)).card : ℝ)), ← Nat.cast_sum]
  exact congrArg (fun n : ℕ => (n : ℝ)) (positiveValues_card_smooth_sum R hM N)

end Bernays

end

/-! ### Upstream module `Util/Bernays/FullClassAsymptotic.lean` -/

section
/-!
# Full asymptotic for represented norms in every ideal class
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def classValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C N => positiveValues (fun n => ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n ∧ I.idealClass = C) N

theorem classValues_card_eq_tsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N : ℕ),
      ((classValues hD C N).card : ℝ) = ∑' m : Nat.factoredNumbers
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
        ((classSliceValues hD C m.val (N / m.val)).card : ℝ) := by
  letI := quadraticOrderIsDomain hD
  intro C N
  exact positiveValues_card_eq_tsum _ (discriminantLevel_pos hD.ne).ne' N

theorem classValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ((classValues hD C N).card : ℝ) / scale N)
        atTop (𝓝 (fullClassConstant hD)) := by
  letI := quadraticOrderIsDomain hD
  intro C
  apply (classSlice_tsum_limit hD C).congr'
  filter_upwards [] with N
  rw [tsum_div_const, ← classValues_card_eq_tsum]

end Bernays

end

/-! ### Upstream module `Util/Bernays/DiscriminantOrder.lean` -/

section
/-!
# A common order for every form of a given discriminant
-/

namespace Bernays

def discriminantTrace (D : ℤ) : ℤ := D % 2

def discriminantConstant (D : ℤ) : ℤ := (D - (discriminantTrace D) ^ 2) / 4

abbrev DiscriminantOrder (D : ℤ) :=
  QuadraticAlgebra ℤ (discriminantConstant D) (discriminantTrace D)

def quadraticOrderCongr {d b d' b' : ℤ} (hd : d = d') (hb : b = b') :
    QuadraticAlgebra ℤ d b ≃+* QuadraticAlgebra ℤ d' b' := by
  subst d'
  subst b'
  exact RingEquiv.refl _

end Bernays

namespace BinQuadForm

theorem b_emod_two (f : BinQuadForm) : f.b % 2 = f.discr % 2 := by
  have h : f.b % 2 = 0 ∨ f.b % 2 = 1 := by omega
  rcases h with h | h <;> simp [discr, Int.sub_emod, Int.mul_emod, h]

theorem b_eq_discriminantTrace (f : BinQuadForm) :
    f.b = Bernays.discriminantTrace f.discr + 2 * (f.b / 2) := by
  rw [Bernays.discriminantTrace, ← f.b_emod_two]
  omega

theorem discriminantConstant_eq (f : BinQuadForm) :
    Bernays.discriminantConstant f.discr =
      -f.a * f.c + Bernays.discriminantTrace f.discr * (f.b / 2) + (f.b / 2) ^ 2 := by
  have heq : f.discr - (Bernays.discriminantTrace f.discr) ^ 2 =
      4 * (-f.a * f.c + Bernays.discriminantTrace f.discr * (f.b / 2) + (f.b / 2) ^ 2) := by
    have hD : f.discr = f.b ^ 2 - 4 * f.a * f.c := by simp only [discr, pow_two]
    linear_combination hD +
      (f.b + Bernays.discriminantTrace f.discr + 2 * (f.b / 2)) * f.b_eq_discriminantTrace
  rw [Bernays.discriminantConstant, heq]
  omega

theorem canonical_order_discr (f : BinQuadForm) :
    (Bernays.discriminantTrace f.discr) ^ 2 + 4 * Bernays.discriminantConstant f.discr =
      f.discr := by
  rw [f.discriminantConstant_eq]
  conv_rhs => rw [discr, f.b_eq_discriminantTrace]
  ring

theorem orderConstant_eq_shift (f : BinQuadForm) :
    -f.a * f.c = Bernays.discriminantConstant f.discr -
      Bernays.discriminantTrace f.discr * (f.b / 2) - (f.b / 2) ^ 2 := by
  rw [f.discriminantConstant_eq]
  ring

def orderEquivDiscriminant (f : BinQuadForm) : f.Order ≃+* Bernays.DiscriminantOrder f.discr :=
  (Bernays.quadraticOrderCongr f.orderConstant_eq_shift f.b_eq_discriminantTrace).trans
    (Bernays.quadraticOrderShift (Bernays.discriminantConstant f.discr)
      (Bernays.discriminantTrace f.discr) (f.b / 2))

theorem PosDef.discriminantOrderIsDomain {f : BinQuadForm} (hf : f.PosDef) :
    IsDomain (Bernays.DiscriminantOrder f.discr) :=
  Bernays.quadraticOrderIsDomain (f.canonical_order_discr.trans_lt hf.2)

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/FormIdealNorm.lean` -/

section
/-!
# Norm and invertibility of the form ideal
-/

open scoped nonZeroDivisors

namespace BinQuadForm

theorem formIdeal_isUnit {f : BinQuadForm} (hf : f.PosDef) (hprim : f.Primitive) :
    letI := hf.orderIsDomain
    IsUnit (f.formIdeal : FractionalIdeal f.Order⁰ (FractionRing f.Order)) := by
  letI := hf.orderIsDomain
  have ha : (f.a : f.Order) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : f.a = 0 := by simpa using hr
    exact hf.1.ne' this
  have hunit : IsUnit
      ((Ideal.span ({(f.a : f.Order)} : Set f.Order) : Ideal f.Order) :
        FractionalIdeal f.Order⁰ (FractionRing f.Order)) := by
    apply IsUnit.of_mul_eq_one _
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing f.Order) ha
  rw [← formIdeal_mul_conjugate hprim, FractionalIdeal.coeIdeal_mul] at hunit
  exact isUnit_of_mul_isUnit_left hunit

def formIdealLinearMap (f : BinQuadForm) : (Fin 2 → ℤ) →ₗ[ℤ] f.formIdeal where
  toFun x := ⟨⟨f.a * x 0, x 1⟩, dvd_mul_right _ _⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp <;> ring
  map_smul' r x := by apply Subtype.ext; ext <;> simp <;> ring

@[simp] theorem formIdealLinearMap_re (f : BinQuadForm) (x : Fin 2 → ℤ) :
    ((f.formIdealLinearMap x : f.formIdeal) : f.Order).re = f.a * x 0 := rfl

@[simp] theorem formIdealLinearMap_im (f : BinQuadForm) (x : Fin 2 → ℤ) :
    ((f.formIdealLinearMap x : f.formIdeal) : f.Order).im = x 1 := rfl

theorem formIdealLinearMap_bijective {f : BinQuadForm} (ha : f.a ≠ 0) :
    Function.Bijective f.formIdealLinearMap := by
  constructor
  · intro x y h
    have hval := congrArg (fun z : f.formIdeal => (z : f.Order)) h
    have hre := congrArg QuadraticAlgebra.re hval
    have him := congrArg QuadraticAlgebra.im hval
    funext i
    fin_cases i
    · exact mul_left_cancel₀ ha hre
    · exact him
  · intro z
    obtain ⟨u, hu⟩ := z.property
    refine ⟨![u, (z : f.Order).im], ?_⟩
    apply Subtype.ext
    exact QuadraticAlgebra.ext hu.symm rfl

noncomputable def formIdealBasis {f : BinQuadForm} (ha : f.a ≠ 0) :
    Module.Basis (Fin 2) ℤ f.formIdeal :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective f.formIdealLinearMap
    (formIdealLinearMap_bijective ha)).symm

theorem formIdeal_cardQuot {f : BinQuadForm} (hf : f.PosDef) :
    f.formIdeal.cardQuot = f.a.natAbs := by
  letI := hf.orderIsDomain
  rw [Erdos1081.cardQuot_eq_natAbs_det_basis_change
    (QuadraticAlgebra.basis (-f.a * f.c) f.b) f.formIdeal (formIdealBasis hf.1.ne')]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [formIdealBasis, Module.Basis.coe_ofEquivFun, formIdealLinearMap,
    Module.Basis.toMatrix_apply]

noncomputable def formIdealClass {f : BinQuadForm} (hf : f.PosDef) (hprim : f.Primitive) :
    letI := hf.orderIsDomain
    ClassGroup f.Order :=
  letI := hf.orderIsDomain
  ClassGroup.mk (FractionRing f.Order) (formIdeal_isUnit hf hprim).unit

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/IdealNormCorrespondence.lean` -/

section
/-!
# Represented values as norms in a specified ideal class
-/

open scoped nonZeroDivisors

namespace Bernays

def quadraticConjugation (d b : ℤ) : QuadraticAlgebra ℤ d b ≃+* QuadraticAlgebra ℤ d b where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_mul' x y := by rw [star_mul, mul_comm]

theorem cardQuot_map_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    (I.map e.toRingHom).cardQuot = I.cardQuot := by
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map e.toRingHom) e rfl).symm.toEquiv

end Bernays

namespace BinQuadForm

theorem conjugateFormIdeal_eq_map (f : BinQuadForm) :
    f.conjugateFormIdeal = f.formIdeal.map
      (Bernays.quadraticConjugation (-f.a * f.c) f.b).toRingHom := by
  ext z
  rw [Ideal.mem_map_iff_of_surjective
    (Bernays.quadraticConjugation (-f.a * f.c) f.b).toRingHom
    (Bernays.quadraticConjugation _ _).surjective]
  constructor
  · intro hz
    refine ⟨star z, ?_, star_star z⟩
    exact hz
  · rintro ⟨x, hx, rfl⟩
    change f.a ∣ (star x).re + f.b * (star x).im
    simpa using hx

theorem conjugateFormIdeal_cardQuot {f : BinQuadForm} (hf : f.PosDef) :
    f.conjugateFormIdeal.cardQuot = f.a.natAbs := by
  rw [conjugateFormIdeal_eq_map, Bernays.cardQuot_map_equiv, formIdeal_cardQuot hf]

theorem formIdeal_product_principal_norm {f : BinQuadForm}
    (hf : f.PosDef) (hp : f.Primitive) (J : Ideal f.Order) (hJ : J ≠ ⊥)
    {z : f.Order} (hz : z ≠ 0)
    (heq : f.formIdeal * J = Ideal.span ({z} : Set f.Order)) :
    z.norm = f.a * (J.cardQuot : ℤ) := by
  letI := hf.orderIsDomain
  have ha : (f.a : f.Order) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : f.a = 0 := by simpa using hr
    exact hf.1.ne' this
  have hconj : f.conjugateFormIdeal ≠ ⊥ := by
    intro hzero
    have hm : (f.a : f.Order) ∈ f.conjugateFormIdeal := by simp
    rw [hzero] at hm
    exact ha hm
  have hprod : Ideal.span ({(f.a : f.Order)} : Set f.Order) * J =
      Ideal.span ({z} : Set f.Order) * f.conjugateFormIdeal := by
    rw [← formIdeal_mul_conjugate hp, ← heq]
    ac_rfl
  have hnorm := Erdos1081.cardQuot_ratio_of_principal_mul_eq
    (QuadraticAlgebra.basis (-f.a * f.c) f.b) hJ hconj ha hz hprod
  rw [Bernays.algebraNorm_quadraticOrder, Bernays.algebraNorm_quadraticOrder,
    QuadraticAlgebra.norm_intCast, Int.cast_id, Int.natAbs_pow,
    conjugateFormIdeal_cardQuot hf] at hnorm
  have hnat : f.a.natAbs * J.cardQuot = z.norm.natAbs := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < f.a.natAbs from Int.natAbs_pos.mpr hf.1.ne')
    nlinarith [hnorm]
  have hnonneg := Bernays.quadraticNorm_nonneg (f.order_discr.trans_lt hf.2) z
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
  simpa only [Nat.cast_mul, Int.natCast_natAbs, abs_of_pos hf.1, abs_of_nonneg hnonneg] using hcast.symm

theorem represented_pos_iff_idealClass_norm {f : BinQuadForm} (hf : f.PosDef)
    (hp : f.Primitive) {n : ℕ} (hn : 0 < n) :
    letI := hf.orderIsDomain
    (∃ u v : ℤ, f.eval u v = (n : ℤ)) ↔
      ∃ J : Bernays.InvertibleIdeal f.Order,
        J.idealClass * f.formIdealClass hf hp = 1 ∧ (J : Ideal f.Order).cardQuot = n := by
  letI := hf.orderIsDomain
  let I : Bernays.InvertibleIdeal f.Order := ⟨f.formIdeal, formIdeal_isUnit hf hp⟩
  have hIclass : I.idealClass = f.formIdealClass hf hp := rfl
  rw [represented_iff_formIdeal_norm hf.1.ne']
  constructor
  · rintro ⟨z, hzI, hz⟩
    have hz₀ : z ≠ 0 := by
      intro hzero
      have hnp : (0 : ℤ) < n := by exact_mod_cast hn
      simp only [hzero, QuadraticAlgebra.norm_zero] at hz
      have := mul_pos hf.1 hnp
      linarith
    obtain ⟨J, hJ⟩ := Bernays.InvertibleIdeal.exists_mul_eq_of_le I
      (Bernays.InvertibleIdeal.principal z hz₀) ((Ideal.span_singleton_le_iff_mem _).mpr hzI)
    refine ⟨J, ?_, ?_⟩
    · have hc := congrArg Bernays.InvertibleIdeal.idealClass hJ
      simpa only [Bernays.InvertibleIdeal.idealClass_mul,
        Bernays.InvertibleIdeal.idealClass_principal, hIclass, mul_comm] using hc
    · have heq : f.formIdeal * (J : Ideal f.Order) = Ideal.span {z} :=
        congrArg (fun K : Bernays.InvertibleIdeal f.Order => (K : Ideal f.Order)) hJ
      have hnorm := formIdeal_product_principal_norm hf hp _ J.ne_bot hz₀ heq
      have heq' : ((J : Ideal f.Order).cardQuot : ℤ) = n :=
        mul_left_cancel₀ hf.1.ne' (hnorm.symm.trans hz)
      exact_mod_cast heq'
  · rintro ⟨J, hc, hnJ⟩
    have hclass : (I * J).idealClass = 1 := by
      rw [Bernays.InvertibleIdeal.idealClass_mul, hIclass]
      exact (mul_comm _ _).trans hc
    obtain ⟨z, hz₀, hz⟩ := (Bernays.InvertibleIdeal.idealClass_eq_one_iff (I * J)).mp hclass
    have heq : f.formIdeal * (J : Ideal f.Order) = Ideal.span {z} :=
      congrArg (fun K : Bernays.InvertibleIdeal f.Order => (K : Ideal f.Order)) hz
    refine ⟨z, ?_, ?_⟩
    · apply Ideal.mul_le_left (I := f.formIdeal) (J := (J : Ideal f.Order))
      rw [heq]
      exact Ideal.mem_span_singleton_self z
    · rw [formIdeal_product_principal_norm hf hp _ J.ne_bot hz₀ heq, hnJ]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/IdealTransport.lean` -/

section
/-!
# Transport of integral invertible ideals under ring isomorphisms
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

theorem exists_mul_principal (I : InvertibleIdeal R) :
    ∃ J : InvertibleIdeal R, ∃ a : R, ∃ ha : a ≠ 0, I * J = principal a ha := by
  obtain ⟨J, hJ⟩ := idealClass_surjective I.idealClass⁻¹
  have h : (I * J).idealClass = 1 := by rw [idealClass_mul, hJ, mul_inv_cancel]
  obtain ⟨a, ha, heq⟩ := (idealClass_eq_one_iff (I * J)).mp h
  exact ⟨J, a, ha, heq⟩

theorem map_isUnit (e : R ≃+* S) (I : InvertibleIdeal R) :
    IsUnit (((I : Ideal R).map e.toRingHom) : FractionalIdeal S⁰ (FractionRing S)) := by
  obtain ⟨J, a, ha, hIJ⟩ := exists_mul_principal I
  have heq : (I : Ideal R) * J = Ideal.span {a} := congrArg (fun K : InvertibleIdeal R =>
    (K : Ideal R)) hIJ
  have hmap := congrArg (Ideal.map e.toRingHom) heq
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hmap
  change (I : Ideal R).map e.toRingHom * (J : Ideal R).map e.toRingHom = Ideal.span {e a} at hmap
  have he : e a ≠ 0 := by exact fun hz => ha (e.injective (hz.trans (map_zero e).symm))
  have hu : IsUnit (((Ideal.span {e a} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))) :=
    (principal (e a) he).2
  rw [← hmap, FractionalIdeal.coeIdeal_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

noncomputable def map (e : R ≃+* S) (I : InvertibleIdeal R) : InvertibleIdeal S :=
  ⟨(I : Ideal R).map e.toRingHom, map_isUnit e I⟩

@[simp] theorem coe_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I : Ideal S) = (I : Ideal R).map e.toRingHom := rfl

@[simp] theorem map_one (e : R ≃+* S) : map e (1 : InvertibleIdeal R) = 1 := by
  apply ext
  exact Ideal.map_top _

@[simp] theorem map_mul (e : R ≃+* S) (I J : InvertibleIdeal R) :
    map e (I * J) = map e I * map e J := by
  apply ext
  simp only [coe_map, coe_mul, Ideal.map_mul]

@[simp] theorem map_symm_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    map e.symm (map e I) = I := by
  apply ext
  simp only [coe_map, Ideal.map_map]
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [hcomp, Ideal.map_id]

@[simp] theorem map_map_symm (e : R ≃+* S) (I : InvertibleIdeal S) :
    map e (map e.symm I) = I := map_symm_map e.symm I

@[simp] theorem map_principal (e : R ≃+* S) (a : R) (ha : a ≠ 0) :
    map e (principal a ha) = principal (e a) (by simpa using ha) := by
  apply ext
  simp only [coe_map, coe_principal, Ideal.map_span, Set.image_singleton]
  rfl

theorem map_idealClass_eq_one_iff (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I).idealClass = 1 ↔ I.idealClass = 1 := by
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := (idealClass_eq_one_iff (map e I)).mp h
    have heq' := congrArg (map e.symm) heq
    rw [map_symm_map, map_principal] at heq'
    rw [heq', idealClass_principal]
  · intro h
    obtain ⟨a, ha, rfl⟩ := (idealClass_eq_one_iff I).mp h
    rw [map_principal, idealClass_principal]

theorem map_idealClass_mul_eq_one_iff (e : R ≃+* S) (I J : InvertibleIdeal R) :
    (map e I).idealClass * (map e J).idealClass = 1 ↔ I.idealClass * J.idealClass = 1 := by
  rw [← idealClass_mul, ← map_mul, map_idealClass_eq_one_iff, idealClass_mul]

theorem cardQuot_map (e : R ≃+* S) (I : InvertibleIdeal R) :
    (map e I : Ideal S).cardQuot = (I : Ideal R).cardQuot :=
  Nat.card_congr (Ideal.quotientEquiv _ _ e rfl).symm.toEquiv

end Bernays.InvertibleIdeal

end

/-! ### Upstream module `Util/Bernays/CanonicalFormClass.lean` -/

section
/-!
# The represented-value problem in the common discriminant class group
-/

namespace BinQuadForm

noncomputable def canonicalIdeal {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    letI := hf.discriminantOrderIsDomain
    Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr) :=
  letI := hf.orderIsDomain
  letI := hf.discriminantOrderIsDomain
  Bernays.InvertibleIdeal.map f.orderEquivDiscriminant ⟨f.formIdeal, formIdeal_isUnit hf hp⟩

noncomputable def canonicalClass {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    letI := hf.discriminantOrderIsDomain
    ClassGroup (Bernays.DiscriminantOrder f.discr) :=
  letI := hf.discriminantOrderIsDomain
  (canonicalIdeal hf hp).idealClass

theorem represented_pos_iff_canonicalClass_norm {f : BinQuadForm}
    (hf : f.PosDef) (hp : f.Primitive) {n : ℕ} (hn : 0 < n) :
    letI := hf.discriminantOrderIsDomain
    (∃ u v : ℤ, f.eval u v = (n : ℤ)) ↔
      ∃ J : Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr),
        J.idealClass * f.canonicalClass hf hp = 1 ∧
          (J : Ideal (Bernays.DiscriminantOrder f.discr)).cardQuot = n := by
  letI := hf.orderIsDomain
  letI := hf.discriminantOrderIsDomain
  let I : Bernays.InvertibleIdeal f.Order := ⟨f.formIdeal, formIdeal_isUnit hf hp⟩
  let e := f.orderEquivDiscriminant
  rw [represented_pos_iff_idealClass_norm hf hp hn]
  change (∃ J : Bernays.InvertibleIdeal f.Order,
    J.idealClass * I.idealClass = 1 ∧ (J : Ideal f.Order).cardQuot = n) ↔
    ∃ J : Bernays.InvertibleIdeal (Bernays.DiscriminantOrder f.discr),
      J.idealClass * (Bernays.InvertibleIdeal.map e I).idealClass = 1 ∧
        (J : Ideal (Bernays.DiscriminantOrder f.discr)).cardQuot = n
  constructor
  · rintro ⟨J, hc, hN⟩
    refine ⟨Bernays.InvertibleIdeal.map e J,
      (Bernays.InvertibleIdeal.map_idealClass_mul_eq_one_iff e J I).mpr hc, ?_⟩
    rwa [Bernays.InvertibleIdeal.cardQuot_map]
  · rintro ⟨J, hc, hN⟩
    refine ⟨Bernays.InvertibleIdeal.map e.symm J, ?_, ?_⟩
    · apply (Bernays.InvertibleIdeal.map_idealClass_mul_eq_one_iff e _ I).mp
      rwa [Bernays.InvertibleIdeal.map_map_symm]
    · rwa [Bernays.InvertibleIdeal.cardQuot_map]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/FormCounting.lean` -/

section
/-!
# Exact transport from ideal-class norm counts to the original form count
-/

open Filter Topology
open scoped Classical

namespace BinQuadForm

theorem B_nat_eq_positiveValues_add_one (f : BinQuadForm) (N : ℕ) :
    f.B (N : ℝ) = (Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N).card + 1 := by
  rw [f.B_eq_card_filter (Nat.cast_nonneg N), Nat.floor_natCast]
  have hset : (Finset.range (N + 1)).filter (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ)) =
      insert 0 (Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_lt_succ, Nat.cast_zero,
        true_and, Finset.mem_insert, true_or]
      exact iff_true_intro ⟨0, 0, f.eval_zero_zero⟩
    · simp only [Finset.mem_filter, Finset.mem_range, Bernays.positiveValues,
        Finset.mem_insert, hn, false_or, Finset.mem_filter, Finset.mem_Icc, Nat.lt_succ_iff]
      have hpos : 1 ≤ n := by omega
      simp only [hpos, true_and]
  rw [hset, Finset.card_insert_of_notMem]
  simp [Bernays.positiveValues]

theorem positiveValues_eq_canonicalClassValues {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive)
    (N : ℕ) :
    let hD := f.canonical_order_discr.trans_lt hf.2
    letI := Bernays.quadraticOrderIsDomain hD
    Bernays.positiveValues (fun n => ∃ u v : ℤ, f.eval u v = (n : ℤ)) N =
      Bernays.classValues hD (f.canonicalClass hf hp)⁻¹ N := by
  let hD := f.canonical_order_discr.trans_lt hf.2
  letI := Bernays.quadraticOrderIsDomain hD
  ext n
  simp only [Bernays.classValues, Bernays.positiveValues, Finset.mem_filter]
  apply and_congr_right
  intro hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [represented_pos_iff_canonicalClass_norm hf hp hnpos]
  apply exists_congr
  intro J
  rw [eq_inv_iff_mul_eq_one]
  exact and_comm

theorem B_nat_limit {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    Tendsto (fun N : ℕ => (f.B (N : ℝ) : ℝ) / Bernays.scale N)
      atTop (𝓝 (Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2))) := by
  let hD := f.canonical_order_discr.trans_lt hf.2
  letI := Bernays.quadraticOrderIsDomain hD
  have hclass := Bernays.classValues_card_limit hD (f.canonicalClass hf hp)⁻¹
  have hone : Tendsto (fun N : ℕ => 1 / Bernays.scale N) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Bernays.scale_tendsto_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := hclass.add hone
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [B_nat_eq_positiveValues_add_one, positiveValues_eq_canonicalClassValues hf hp,
    Nat.cast_add, Nat.cast_one, add_div]

end BinQuadForm

end

/-! ### Upstream module `Util/Bernays/Theorem.lean` -/

section
/-!
# Bernays' theorem with one positive constant for every form of a discriminant

The constant combines the uniform coprime-class asymptotic with the convergent
sum over discriminant-prime parts. The counting function and normalization are
those of the original statement, including the represented value zero.
-/

open Filter Topology Asymptotics

namespace BinQuadForm

theorem B_isEquivalent {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    (fun x : ℝ => (f.B x : ℝ)) ~[atTop]
      (fun x : ℝ => Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2) *
        x / Real.sqrt (Real.log x)) := by
  let C := Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2)
  have hC : C ≠ 0 := (Bernays.fullClassConstant_pos _).ne'
  apply (Bernays.real_asymptotic_iff_nat f C).mpr
  apply isEquivalent_of_tendsto_one
  have h := (B_nat_limit hf hp).div_const C
  rw [div_self hC] at h
  apply h.congr'
  filter_upwards [] with N
  change ((f.B (N : ℝ) : ℝ) / Bernays.scale N) / C = _
  rw [div_div, mul_comm (Bernays.scale N) C]
  simp only [Bernays.scale, mul_div_assoc, Pi.div_apply]

end BinQuadForm

namespace Bernays

noncomputable def discriminantBernaysConstant (Δ : ℤ) : ℝ :=
  if h : (discriminantTrace Δ) ^ 2 + 4 * discriminantConstant Δ < 0 then fullClassConstant h else 1

theorem discriminantBernaysConstant_pos (Δ : ℤ) : 0 < discriminantBernaysConstant Δ := by
  unfold discriminantBernaysConstant
  split_ifs with h
  · exact fullClassConstant_pos h
  · norm_num

theorem bernays_theorem
    (Δ : ℤ) (_hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x)) := by
  refine ⟨discriminantBernaysConstant Δ, discriminantBernaysConstant_pos Δ, ?_⟩
  intro f hp hf hdiscr
  rw [← hdiscr]
  have hD := f.canonical_order_discr.trans_lt hf.2
  rw [discriminantBernaysConstant, dif_pos hD]
  exact BinQuadForm.B_isEquivalent hf hp

end Bernays

end

/-! ### Upstream module `ErdosProblems/Erdos659/Geometry.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Shared geometry for the two proofs of Erdős Problem 659

The rectangular lattice, its forbidden four-point configurations, and the
conversion to the Euclidean plane are independent of all counting estimates.
The Bernays proof is in `ErdosProblems.Erdos659`; the separate upper-bound
proof is in `ErdosProblems.Erdos659b`.

Original formalization: Aristotle and Boris Alexeev.
Default-limit geometry refinements and module organization: Codex.
-/

open scoped Real

open Filter

open Asymptotics

/-
Define the set of points P_m as the image of the m x m grid under the lattice map (x, y) -> (x,
sqrt(2)y).
-/
noncomputable def latticePoint (p : ℤ × ℤ) : ℝ × ℝ :=
  (p.1, Real.sqrt 2 * p.2)

noncomputable def P (m : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.product (Finset.range m) (Finset.range m)).map ⟨fun (i, j) => latticePoint (i, j), by
    unfold latticePoint;
    norm_num [ Function.Injective ]⟩

/-
Define D(P) as the set of nonzero distances between pairs of points in P.
-/

/-
The set L is closed under subtraction.
-/
def L_set : Set (ℝ × ℝ) := Set.range latticePoint

lemma L_set_sub_closed : ∀ p q, p ∈ L_set → q ∈ L_set → p - q ∈ L_set := by
  unfold L_set;
  unfold latticePoint;
  norm_num +zetaDelta at *;
  exact fun a b a_1 b_1 x y hx hy z w hz hw =>
    ⟨ ⟨ x - z, by push_cast; linarith ⟩, ⟨ y - w, by push_cast; linarith ⟩ ⟩

/-
If n = m * sqrt(2) for integers n, m, then n = m = 0.
-/

/-
The lattice L contains no non-zero vector v such that its 90-degree rotation is also in L.
-/
lemma L_set_no_square_vector : ∀ v, v ∈ L_set → (-v.2, v.1) ∈ L_set → v = 0 := by
  norm_num +zetaDelta at *;
  rintro a b ⟨ x, hx ⟩ ⟨ y, hy ⟩;
  -- From the equations $a = x.1$ and $b = \sqrt{2} x.2$, and $b = -y.1$ and $a = \sqrt{2} y.2$, we
  -- can deduce that $y.1 = -\sqrt{2} x.2$ and $y.2 = x.1 / \sqrt{2}$.
  have hy1 : y.1 = -Real.sqrt 2 * x.2 := by
    unfold latticePoint at *; aesop;
  have hy2 : y.2 = x.1 / Real.sqrt 2 := by
    unfold latticePoint at *; aesop;
  -- Since $y.1$ and $y.2$ are integers, and $\sqrt{2}$ is irrational, this implies that $x.2 = 0$
  -- and $x.1 = 0$.
  have hx2 : x.2 = 0 := by
    by_contra hx2_nonzero;
    exact irrational_sqrt_two <| ⟨ -y.1 / x.2,
      by push_cast [ hy1 ] ; rw [ div_eq_iff <| Int.cast_ne_zero.mpr hx2_nonzero ] ; ring ⟩
  have hx1 : x.1 = 0 := by
    by_contra hx1_nonzero;
    exact irrational_sqrt_two <| ⟨ x.1 / y.2,
      by push_cast [ hy2 ] ; rw [ div_div_cancel₀ ] ; positivity ⟩;
  unfold latticePoint at hx; aesop;

/-
If a vector v is in L and its 60-degree rotation is also in L, then v must be 0.
-/
lemma L_set_rotation_60 (v : ℝ × ℝ) (hv : v ∈ L_set) :
    let v_rot := (v.1 / 2 - v.2 * Real.sqrt 3 / 2, v.1 * Real.sqrt 3 / 2 + v.2 / 2)
    v_rot ∈ L_set → v = 0 := by
      field_simp;
      obtain ⟨ u, v, hv ⟩ := hv;
      rintro ⟨ m, hm ⟩;
      norm_num [ Prod.ext_iff, latticePoint ] at hm ⊢;
      -- If $u.2 \neq 0$, then $\sqrt{6}$ must be rational, which is a contradiction.
      by_cases hu2 : u.2 = 0;
      · by_cases hu1 : u.1 = 0 <;> simp_all +decide;
        -- Squaring both sides of the equation $\sqrt{2} * m.2 = u.1 * \sqrt{3} / 2$, we get $2 *
        -- m.2^2 = 3 * u.1^2 / 4$, which simplifies to $8 * m.2^2 = 3 * u.1^2$.
        have h_sq : 8 * m.2 ^ 2 = 3 * u.1 ^ 2 := by
          have := congr_arg ( · ^ 2 ) hm.2
          ring_nf at this
          norm_num at this
          norm_cast at this
          push_cast [ ← @Int.cast_inj ℝ ] at *; linarith;
        -- Since $u.1 \neq 0$, we can divide both sides of the equation $8 * m.2^2 = 3 * u.1^2$ by
        -- $u.1^2$ to get $8 * (m.2 / u.1)^2 = 3$.
        obtain ⟨k, hk⟩ : ∃ k : ℚ, k^2 = 3 / 8 := by
          use m.2 / u.1;
          rw [ div_pow, div_eq_div_iff ] <;> norm_cast <;> first |linarith|aesop;
        apply_fun ( fun x => x.num ) at hk ; norm_num [ sq,
          Rat.mul_self_num ] at hk ; nlinarith [ show k.num ≤ 1 by nlinarith,
          show k.num ≥ -1 by nlinarith ];
      · have h_sqrt6_rat : ∃ q : ℚ, Real.sqrt 6 = q := by
          have h_eq : u.1 - 2 * m.1 = Real.sqrt 6 * u.2 := by
            rw [ show ( 6 : ℝ ) = 2 * 3 by norm_num,
              Real.sqrt_mul ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
              Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ]
          exact ⟨ ( u.1 - 2 * m.1 ) / u.2,
            by
              push_cast [ h_eq ]
              rw [ mul_div_cancel_right₀ _ ( Int.cast_ne_zero.mpr hu2 ) ] ⟩;
        exact False.elim <| by
          obtain ⟨ q, hq ⟩ := h_sqrt6_rat
          have := congr_arg ( · ^ 2 ) hq
          norm_num at this
          norm_cast at this
          exact absurd ( congr_arg ( ·.num ) this ) ( by
            norm_num [ sq, Rat.mul_self_num ]
            intros h
            nlinarith [ show q.num ≤ 2 by nlinarith, show q.num ≥ -2 by nlinarith ] ) ;

/-
If z1 and z2 form an equilateral triangle with the origin in the complex plane, then z2 is a
rotation of z1 by +/ - 60 degrees.
-/
lemma complex_equilateral (z1 z2 : ℂ)
  (h : Complex.normSq z1 = Complex.normSq z2)
  (h2 : Complex.normSq (z1 - z2) = Complex.normSq z1) :
  z2 = z1 * Complex.exp (Complex.I * Real.pi / 3) ∨
  z2 = z1 * Complex.exp (-Complex.I * Real.pi / 3) := by
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
    norm_num [ Complex.normSq, neg_div ] at *;
    by_cases h_case : z2.re = z1.re * (1 / 2) - z1.im * (Real.sqrt 3 / 2) ∨
      z2.re = z1.re * (1 / 2) + z1.im * (Real.sqrt 3 / 2);
    · grind;
    · exact False.elim <| h_case <| Classical.or_iff_not_imp_left.2 fun h =>
        mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by
          ring_nf
          norm_num
          nlinarith;

/-
Multiplication by exp(i pi/3) corresponds to the rotation formula.
-/

/-
If a vector v is in L and its -60 degree rotation is also in L, then v must be 0.
-/
lemma L_set_rotation_neg_60 (v : ℝ × ℝ) (hv : v ∈ L_set) :
    let v_rot := (v.1 / 2 + v.2 * Real.sqrt 3 / 2, -v.1 * Real.sqrt 3 / 2 + v.2 / 2)
    v_rot ∈ L_set → v = 0 := by
      intro h;
      -- Let w = v_rot. Then v is the rotation of w by 60 degrees.
      set w := h
      have hw : v = (w.1 / 2 - w.2 * Real.sqrt 3 / 2, w.1 * Real.sqrt 3 / 2 + w.2 / 2) := by
        grind;
      intro hw';
      -- Apply the lemma L_set_rotation_60 to w (with v as the rotated vector).
      have := L_set_rotation_60 w hw'
      simp at this;
      rw [ hw, this ];
      · norm_num;
      · exact hw ▸ hv

/-
If two vectors in L form an equilateral triangle with the origin, they must be zero.
-/

/-
The lattice L contains no non-degenerate equilateral triangle.
-/

/-
The squared distance between any two points in L is an integer.
-/

/-
The number (3+sqrt(5))/2 is irrational.
-/

/-
The lattice L contains no four-point set forming a regular-pentagon trapezoid.
-/

/-
A set of 4 points forms a square if the sides are equal and the diagonals are equal (and related to
the side by sqrt(2)).
-/

/-
A set of points has an equilateral triangle if it contains 3 distinct points with equal pairwise
distances.
-/

/-
A set of 4 points forms a pentagon trapezoid if it consists of 3 equal sides and the diagonals are
in golden ratio to the side.
-/

/-
A set has golden ratio distances if the ratio of two distinct distances is the golden ratio.
-/

/-
The set of points P_m is a subset of the lattice L.
-/
lemma P_subset_L (m : ℕ) : (P m : Set (ℝ × ℝ)) ⊆ L_set := by
  unfold L_set P;
  intro x hx; aesop

/-
The lattice L contains no set of points determining distances in the golden ratio.
-/

/-
If two vectors u and v are orthogonal and have the same norm, then v is a 90 degree or -90 degree
rotation of u.
-/

/-
The distance on R x R is the L-infinity distance.
-/

/-
Define Euclidean distance on R^2 and prove the expansion of its square.
-/
noncomputable def dist_euc (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

lemma dist_euc_comm (p q : ℝ × ℝ) : dist_euc p q = dist_euc q p := by
  unfold dist_euc
  congr 1
  ring

lemma dist_euc_eq_zero {p q : ℝ × ℝ} : dist_euc p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold dist_euc at h
    have hs_le : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h
    have hs_nonneg : 0 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hs : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := le_antisymm hs_le hs_nonneg
    apply Prod.ext
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  · intro h
    subst h
    simp [dist_euc]

/-
The set of distinct Euclidean distances in a set of points.
-/
noncomputable def distinctDistances'_euc (S : Finset (ℝ × ℝ)) : Finset ℝ :=
  (S.product S).image (fun (p, q) => dist_euc p q) \ {0}

/-
Definition of a square using Euclidean distance.
-/
def is_square_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r s, S = {p, q, r, s} ∧ p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ p ∧
  dist_euc p q = dist_euc q r ∧ dist_euc q r = dist_euc r s ∧ dist_euc r s = dist_euc s p ∧
  dist_euc p r = dist_euc q s ∧ dist_euc p r = dist_euc p q * Real.sqrt 2

/-
Definition of a set containing an equilateral triangle using Euclidean distance.
-/
def has_equilateral_triangle_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ p q r, {p, q, r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
  dist_euc p q = dist_euc q r ∧ dist_euc q r = dist_euc r p

/-
Definition of a set containing golden ratio distances using Euclidean distance.
-/
def has_golden_ratio_distances_euc (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ d1 d2, d1 ∈ distinctDistances'_euc S ∧ d2 ∈ distinctDistances'_euc S ∧
    d1 = d2 * ((1 + Real.sqrt 5) / 2)

/-
If a vector u is in L and its 90 degree rotation is in L, then u is 0.
-/
def rotate90 (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1)

lemma L_no_rotate90 (u : ℝ × ℝ) (hu : u ∈ L_set) (hrot : rotate90 u ∈ L_set) : u = 0 := by
  -- Apply `L_set_no_square_vector` to obtain that $u = 0$.
  apply L_set_no_square_vector u hu hrot

/-
If p, q, r form a right isosceles triangle at q, then r-q is a rotation of p-q.
-/
lemma right_isosceles_euc_implies_rotation (p q r : ℝ × ℝ)
  (h_eq : dist_euc p q = dist_euc q r)
  (h_diag : dist_euc p r = dist_euc p q * Real.sqrt 2) :
  let u := (p.1 - q.1, p.2 - q.2)
  let v := (r.1 - q.1, r.2 - q.2)
  v = rotate90 u ∨ v = - rotate90 u := by
    -- By squaring both sides of the equation dist_euc p r = dist_euc p q * sqrt(2), we get (p.1 -
    -- r.1)^2 + (p.2 - r.2)^2 = 2 * ((p.1 - q.1)^2 + (p.2 - q.2)^2).
    have h_sq : (p.1 - r.1)^2 + (p.2 - r.2)^2 = 2 * ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
      unfold dist_euc at *;
      rw [ ← Real.sq_sqrt ( by positivity : 0 ≤ ( p.1 - r.1 ) ^ 2 + ( p.2 - r.2 ) ^ 2 ), h_diag,
        mul_pow, Real.sq_sqrt ( by positivity : 0 ≤ ( p.1 - q.1 ) ^ 2 + ( p.2 - q.2 ) ^ 2 ),
        Real.sq_sqrt ( by positivity : 0 ≤ ( 2 : ℝ ) ) ] ; ring;
    have h_ortho : (p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2) = 0 := by
      unfold dist_euc at h_eq;
      rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at h_eq ; linarith;
    simp_all +decide [ rotate90 ];
    have h_rotate : (r.1 - q.1) = -(p.2 - q.2) ∨ (r.1 - q.1) = (p.2 - q.2) := by
      have h_rotate : (p.1 - q.1)^2 + (p.2 - q.2)^2 = (r.1 - q.1)^2 + (r.2 - q.2)^2 := by
        grind;
      exact Classical.or_iff_not_imp_left.2 fun h =>
        mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith;
    cases h_rotate <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · exact Classical.or_iff_not_imp_left.2 fun h =>
        ⟨ mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith,
          mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by nlinarith ⟩;
    · exact Classical.or_iff_not_imp_right.2 fun h =>
        ⟨ mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith,
          mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith ⟩

/-
The lattice L contains no square (Euclidean version).
-/
lemma L_no_square_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ is_square_euc S := by
      rintro ⟨ p, q, r, s, rfl, hpq, hqr, hrs, hsp, h_dist ⟩;
      -- Let u = p - q and v = r - q.
      set u : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)
      set v : ℝ × ℝ := (r.1 - q.1, r.2 - q.2);
      -- By right_isosceles_euc_implies_rotation, v = rotate90(u) or v = -rotate90(u).
      have hv : v = rotate90 u ∨ v = -rotate90 u := by
        apply right_isosceles_euc_implies_rotation;
        · exact h_dist.1;
        · exact h_dist.2.2.2.2;
      -- Since p, q, r are in L, u and v are in L (by closure under subtraction).
      have hu : u ∈ L_set := by
        have hu : p ∈ L_set ∧ q ∈ L_set := by
          exact ⟨ hS <| by norm_num, hS <| by norm_num ⟩;
        exact L_set_sub_closed _ _ hu.1 hu.2
      have hv : v ∈ L_set := by
        have hv : r ∈ L_set ∧ q ∈ L_set := by
          exact ⟨ hS <| by norm_num, hS <| by norm_num ⟩;
        apply L_set_sub_closed
        · exact hv.left
        · exact hv.right
      -- By L_no_rotate90, u = 0.
      have hu_zero : u = 0 := by
        rcases ‹v = rotate90 u ∨ v = -rotate90 u› with hv | hv <;>
          simp_all +decide [ Set.subset_def ];
        · exact L_no_rotate90 u hu ‹_›;
        · exact L_no_rotate90 u hu ( by
            simpa using L_set_sub_closed _ _
              ( show 0 ∈ L_set from ⟨ ( 0, 0 ), by norm_num [ latticePoint ] ⟩ )
              ‹-rotate90 u ∈ L_set› );
      exact hpq ( Prod.mk_inj.mpr ⟨ sub_eq_zero.mp ( congr_arg Prod.fst hu_zero ),
        sub_eq_zero.mp ( congr_arg Prod.snd hu_zero ) ⟩ )

/-
If a vector u is in L and its 60 degree rotation is in L, then u is 0.
-/
noncomputable def rotate60 (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 / 2 - u.2 * Real.sqrt 3 / 2, u.1 * Real.sqrt 3 / 2 + u.2 / 2)

lemma L_no_rotate60 (u : ℝ × ℝ) (hu : u ∈ L_set) (hrot : rotate60 u ∈ L_set) : u = 0 := by
  by_contra hu_nonzero;
  exact hu_nonzero <| L_set_rotation_60 u hu hrot

/-
If a vector u is in L and its -60 degree rotation is in L, then u is 0.
-/
noncomputable def rotate_neg60 (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 / 2 + u.2 * Real.sqrt 3 / 2, -u.1 * Real.sqrt 3 / 2 + u.2 / 2)

lemma L_no_rotate_neg60 (u : ℝ × ℝ) (hu : u ∈ L_set)
    (hrot : rotate_neg60 u ∈ L_set) : u = 0 := by
  apply L_set_rotation_neg_60 u hu hrot

/-
If p, q, r form an equilateral triangle, then r-p is a rotation of q-p by 60 or -60 degrees.
-/
lemma equilateral_euc_implies_rotation (p q r : ℝ × ℝ)
  (h_eq1 : dist_euc p q = dist_euc q r)
  (h_eq2 : dist_euc q r = dist_euc r p)
  (_h_neq : p ≠ q) :
  let u := (q.1 - p.1, q.2 - p.2)
  let v := (r.1 - p.1, r.2 - p.2)
  v = rotate60 u ∨ v = rotate_neg60 u := by
    let z₁ : ℂ := (q.1 - p.1) + (q.2 - p.2) * Complex.I
    let z₂ : ℂ := (r.1 - p.1) + (r.2 - p.2) * Complex.I
    have hsq1 :
        (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 =
          (q.1 - r.1) ^ 2 + (q.2 - r.2) ^ 2 := by
      have h := congrArg (fun x : ℝ => x ^ 2) h_eq1
      unfold dist_euc at h
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at h
      exact h
    have hsq2 :
        (q.1 - r.1) ^ 2 + (q.2 - r.2) ^ 2 =
          (r.1 - p.1) ^ 2 + (r.2 - p.2) ^ 2 := by
      have h := congrArg (fun x : ℝ => x ^ 2) h_eq2
      unfold dist_euc at h
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at h
      exact h
    have h_norm : Complex.normSq z₁ = Complex.normSq z₂ := by
      simp [z₁, z₂, Complex.normSq]
      nlinarith [hsq1, hsq2]
    have h_diff : Complex.normSq (z₁ - z₂) = Complex.normSq z₁ := by
      simp [z₁, z₂, Complex.normSq]
      nlinarith [hsq1]
    rcases complex_equilateral z₁ z₂ h_norm h_diff with hrot | hrot
    · left
      apply Prod.ext
      · have hre := congrArg Complex.re hrot
        norm_num [z₁, z₂, Complex.exp_re, Complex.exp_im] at hre
        change r.1 - p.1 = (q.1 - p.1) / 2 - (q.2 - p.2) * Real.sqrt 3 / 2
        calc
          r.1 - p.1 =
              (q.1 - p.1) * (1 / 2) - (q.2 - p.2) * (Real.sqrt 3 / 2) := hre
          _ = (q.1 - p.1) / 2 - (q.2 - p.2) * Real.sqrt 3 / 2 := by ring
      · have him := congrArg Complex.im hrot
        norm_num [z₁, z₂, Complex.exp_re, Complex.exp_im] at him
        change r.2 - p.2 = (q.1 - p.1) * Real.sqrt 3 / 2 + (q.2 - p.2) / 2
        calc
          r.2 - p.2 =
              (q.1 - p.1) * (Real.sqrt 3 / 2) + (q.2 - p.2) * (1 / 2) := him
          _ = (q.1 - p.1) * Real.sqrt 3 / 2 + (q.2 - p.2) / 2 := by ring
    · right
      apply Prod.ext
      · have hre := congrArg Complex.re hrot
        norm_num [z₁, z₂, Complex.exp_re, Complex.exp_im, neg_div] at hre
        change r.1 - p.1 = (q.1 - p.1) / 2 + (q.2 - p.2) * Real.sqrt 3 / 2
        calc
          r.1 - p.1 =
              (q.1 - p.1) * (1 / 2) + (q.2 - p.2) * (Real.sqrt 3 / 2) := hre
          _ = (q.1 - p.1) / 2 + (q.2 - p.2) * Real.sqrt 3 / 2 := by ring
      · have him := congrArg Complex.im hrot
        norm_num [z₁, z₂, Complex.exp_re, Complex.exp_im, neg_div] at him
        change r.2 - p.2 = -(q.1 - p.1) * Real.sqrt 3 / 2 + (q.2 - p.2) / 2
        calc
          r.2 - p.2 =
              -((q.1 - p.1) * (Real.sqrt 3 / 2)) + (q.2 - p.2) * (1 / 2) := him
          _ = -(q.1 - p.1) * Real.sqrt 3 / 2 + (q.2 - p.2) / 2 := by ring

/-
The lattice L contains no equilateral triangle (Euclidean version).
-/
lemma L_no_equilateral_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ has_equilateral_triangle_euc S := by
      intro h;
      obtain ⟨ p, q, r, hp, hq, hr, hneq, hdist ⟩ := h;
      have h_rotate : let u := (q.1 - p.1, q.2 - p.2); let v := (r.1 - p.1,
        r.2 - p.2); v = rotate60 u ∨ v = rotate_neg60 u := by
        apply equilateral_euc_implies_rotation;
        · exact hdist.1;
        · exact hdist.2;
        · assumption;
      -- Since p, q, r ∈ L, u and v are in L.
      have h_u_v_in_L : (q.1 - p.1, q.2 - p.2) ∈ L_set ∧ (r.1 - p.1, r.2 - p.2) ∈ L_set := by
        have h_u_v_in_L : ∀ x ∈ S, ∀ y ∈ S, (x.1 - y.1, x.2 - y.2) ∈ L_set := by
          intros x hx y hy; exact L_set_sub_closed x y (hS hx) (hS hy);
        exact ⟨ h_u_v_in_L q ( hp ( by simp +decide ) ) p ( hp ( by simp +decide ) ),
          h_u_v_in_L r ( hp ( by simp +decide ) ) p ( hp ( by simp +decide ) ) ⟩;
      cases h_rotate <;> simp_all +decide;
      · have := L_no_rotate60 _ h_u_v_in_L.1 h_u_v_in_L.2;
        simp_all +decide [ Prod.ext_iff, sub_eq_zero ];
      · have := L_no_rotate_neg60 _ h_u_v_in_L.1 h_u_v_in_L.2
        simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact hq ( Prod.ext this.1 this.2 ▸ rfl )

/-
Squared Euclidean distances in L are integers.
-/
lemma L_set_squared_dist_euc_is_int (p q : ℝ × ℝ) (hp : p ∈ L_set) (hq : q ∈ L_set) :
    ∃ n : ℤ, (dist_euc p q) ^ 2 = n := by
      unfold dist_euc;
      obtain ⟨ x, y, rfl, rfl ⟩ := hp
      obtain ⟨ u, v, rfl, rfl ⟩ := hq
      norm_num [ Real.sq_sqrt, add_nonneg, sq_nonneg ] ;
      norm_num [ latticePoint ];
      ring_nf; norm_num; norm_cast; aesop;

/-
The lattice L contains no set of points determining Euclidean distances in the golden ratio.
-/
lemma L_no_golden_ratio_euc (S : Finset (ℝ × ℝ)) (hS : (S : Set (ℝ × ℝ)) ⊆ L_set) :
    ¬ has_golden_ratio_distances_euc S := by
      rintro ⟨ d1, d2, hd1, hd2, h ⟩;
      -- Since S is in L, d1^2 and d2^2 are integers.
      obtain ⟨n1, hn1⟩ : ∃ n1 : ℤ, d1^2 = n1 := by
        unfold distinctDistances'_euc at hd1;
        norm_num +zetaDelta at *;
        rcases hd1.1 with ⟨ a, b, c, d, ⟨ ha, hb ⟩,
          rfl ⟩ ; exact L_set_squared_dist_euc_is_int _ _ ( hS ha ) ( hS hb ) ;
      obtain ⟨n2, hn2⟩ : ∃ n2 : ℤ, d2^2 = n2 := by
        unfold distinctDistances'_euc at hd2;
        norm_num +zetaDelta at *;
        rcases hd2.1 with ⟨ a, b, a', b', ⟨ ha, hb ⟩,
          rfl ⟩ ;
        exact L_set_squared_dist_euc_is_int ( a, b ) ( a', b' ) ( hS ha ) ( hS hb ) ;
      have h_phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = n1 / n2 := by
        rw [ ← hn1, ← hn2, h ];
        rw [ mul_pow, mul_div_cancel_left₀ _ ( pow_ne_zero 2 <| by
          rintro rfl
          exact absurd hd2 <| by
            unfold distinctDistances'_euc
            aesop ) ];
      exact False.elim <| Nat.Prime.irrational_sqrt ( show Nat.Prime 5 by norm_num )
        ⟨ ↑n1 / ↑n2 * 2 - 3, by
          push_cast [ ← h_phi_sq ]
          linarith [ Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ⟩

/-
The statement of Perucca's classification theorem.
-/
def PeruccaClassificationStatement : Prop :=
  ∀ (S : Finset (ℝ × ℝ)), S.card = 4 → (distinctDistances'_euc S).card = 2 →
    is_square_euc S ∨ has_equilateral_triangle_euc S ∨ has_golden_ratio_distances_euc S

/-
Every 4-point subset of P_m determines at least 3 distinct Euclidean distances (assuming Perucca's
classification).
-/
theorem P_local_constraint (m : ℕ) (h_perucca : PeruccaClassificationStatement) :
    ∀ S, S ⊆ (P m) → S.card = 4 → (distinctDistances'_euc S).card ≥ 3 := by
      intro S hS_sub hS_card
      by_contra h_contra;
      interval_cases _ : Finset.card ( distinctDistances'_euc S ) <;> simp_all +decide;
      · simp_all +decide [ Finset.ext_iff, distinctDistances'_euc ];
        have := Finset.one_lt_card.1 ( by linarith ) ; obtain ⟨ p, hp, q, hq,
          hpq ⟩ := this; specialize ‹∀ a x x_1 x_2 x_3 : ℝ, ( x, x_1 ) ∈ S → ( x_2,
          x_3 ) ∈ S → dist_euc ( x, x_1 ) ( x_2,
          x_3 ) = a → a = 0› _ _ _ _ _ hp hq rfl; simp_all +decide [ dist_euc ] ;
        exact hpq ( Prod.mk_inj.mpr ⟨ by rw [ Real.sqrt_eq_zero' ] at *; nlinarith,
          by rw [ Real.sqrt_eq_zero' ] at *; nlinarith ⟩ );
      · have := Finset.card_eq_one.mp ‹_›;
        -- If all pairs of points in S have the same distance, then any three points in S form an
        -- equilateral triangle.
        obtain ⟨a, ha⟩ := this
        have h_equilateral : ∀ p q r : ℝ × ℝ,
          p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → r ≠ p →
            dist_euc p q = dist_euc q r ∧
            dist_euc q r = dist_euc r p := by
          intros p q r hp hq hr hpq hqr hrp
          have h_dist_eq : dist_euc p q ∈ distinctDistances'_euc S ∧
            dist_euc q r ∈ distinctDistances'_euc S ∧
              dist_euc r p ∈ distinctDistances'_euc S := by
            simp [distinctDistances'_euc];
            exact ⟨
              ⟨ ⟨ p.1, p.2, q.1, q.2, ⟨ hp, hq ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hpq <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩,
              ⟨ ⟨ q.1, q.2, r.1, r.2, ⟨ hq, hr ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hqr <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩,
              ⟨ ⟨ r.1, r.2, p.1, p.2, ⟨ hr, hp ⟩, rfl ⟩,
                by
                  exact ne_of_gt ( Real.sqrt_pos.mpr ( by
                    exact not_le.mp fun h =>
                      hrp <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) ⟩ ⟩;
          aesop;
        -- Let's choose any three points from S and show that they form an equilateral triangle.
        obtain ⟨p, q, r, hpS, hqS, hrS, hpq, hqr, hrp⟩ : ∃ p q r : ℝ × ℝ,
          p ∈ S ∧ q ∈ S ∧ r ∈ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p := by
          rcases Finset.two_lt_card.1 ( by linarith : 2 < Finset.card S ) with ⟨ p, hp, q, hq,
            hpq ⟩ ; use p, q ; aesop;
        have h_equilateral_triangle : has_equilateral_triangle_euc S := by
          use p, q, r;
          grind;
        exact absurd
          ( L_no_equilateral_euc S ( fun x hx => P_subset_L m <| hS_sub hx )
            h_equilateral_triangle )
          ( by tauto );
      · -- By Perucca's classification, S must be a square, contain an equilateral triangle, or
        -- have
        -- golden ratio distances.
        have h_perucca_applied : is_square_euc S ∨ has_equilateral_triangle_euc S ∨
          has_golden_ratio_distances_euc S := by
          exact h_perucca S hS_card ‹_›;
        contrapose! h_perucca_applied;
        exact ⟨
          fun h => L_no_square_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h,
          fun h => L_no_equilateral_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h,
          fun h => L_no_golden_ratio_euc S ( fun x hx => by
            have := hS_sub ( Finset.mem_coe.mp hx )
            exact P_subset_L m this ) h ⟩

/-
Characterization of points in P_m.
-/
lemma P_coords (m : ℕ) (p : ℝ × ℝ) (hp : p ∈ P m) :
    ∃ i j : ℕ, i < m ∧ j < m ∧ p = ((i : ℝ), Real.sqrt 2 * (j : ℝ)) := by
      unfold P at hp;
      unfold latticePoint at hp; erw [ Finset.mem_map ] at hp; obtain ⟨ x, hx,
        rfl ⟩ := hp; exact ⟨ x.1, x.2, Finset.mem_range.mp ( Finset.mem_product.mp hx |>.1 ),
        Finset.mem_range.mp ( Finset.mem_product.mp hx |>.2 ), rfl ⟩ ;

/-- A nonzero distance is realized by two distinct points. -/
lemma mem_distinctDistances_euc {S : Finset (ℝ × ℝ)} {d : ℝ} :
    d ∈ distinctDistances'_euc S ↔
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ dist_euc p q = d := by
  classical
  constructor
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hi, hz⟩
    rcases Finset.mem_image.mp hi with ⟨⟨p, q⟩, hpq, rfl⟩
    rcases Finset.mem_product.mp hpq with ⟨hp, hq⟩
    refine ⟨p, hp, q, hq, ?_, rfl⟩
    intro heq
    apply hz
    simp [dist_euc_eq_zero.mpr heq]
  · rintro ⟨p, hp, q, hq, hne, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    · simpa only [Finset.mem_singleton, dist_euc_eq_zero] using hne

lemma distinctDistances_euc_pos {S : Finset (ℝ × ℝ)} {d : ℝ}
    (hd : d ∈ distinctDistances'_euc S) : 0 < d := by
  rcases mem_distinctDistances_euc.mp hd with ⟨p, _, q, _, hne, rfl⟩
  exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm (dist_euc_eq_zero.not.mpr hne))

/-- Squared Euclidean distances in `P m` have the form `u² + 2v²`,
with `|u|, |v| < m`. -/
lemma P_dist_sq_form (m : ℕ) (p q : ℝ × ℝ) (hp : p ∈ P m) (hq : q ∈ P m) :
    ∃ u v : ℤ, |u| < m ∧ |v| < m ∧ (dist_euc p q)^2 = u^2 + 2 * v^2 := by
      -- Let's unfold the definitions of P_coords and use the provided solution's approach.
      obtain ⟨i1, j1, hi1, hj1, hp_def⟩ : ∃ i1 j1 : ℕ,
        i1 < m ∧ j1 < m ∧ p = ((i1 : ℝ),
        Real.sqrt 2 * (j1 : ℝ)) := by
        exact P_coords m p hp
      obtain ⟨i2, j2, hi2, hj2, hq_def⟩ : ∃ i2 j2 : ℕ,
        i2 < m ∧ j2 < m ∧ q = ((i2 : ℝ),
        Real.sqrt 2 * (j2 : ℝ)) := by
        exact P_coords m q hq;
      -- Let's calculate the squared Euclidean distance between p and q.
      have h_dist_sq : (dist_euc p q) ^ 2 = (i1 - i2 : ℝ) ^ 2 + 2 * (j1 - j2 : ℝ) ^ 2 := by
        rw [ hp_def, hq_def, dist_euc ];
        rw [ Real.sq_sqrt <| by positivity ] ; ring_nf ; norm_num;
        ring;
      exact ⟨ i1 - i2, j1 - j2, abs_lt.mpr ⟨ by linarith, by linarith ⟩,
        abs_lt.mpr ⟨ by linarith, by linarith ⟩, by simpa using h_dist_sq ⟩

/-
m_of_n(n) squared is at least n.
-/
noncomputable def m_of_n (n : ℕ) : ℕ := Nat.sqrt n + 1

lemma m_of_n_sq_ge_n (n : ℕ) : (m_of_n n) ^ 2 ≥ n := by
  exact Nat.le_of_lt ( Nat.lt_succ_sqrt' _ )

/-
Sequence of sets P_n with |P_n| = n.
-/
noncomputable def P_seq (n : ℕ) : Finset (ℝ × ℝ) :=
  if h : n = 0 then ∅ else
  let m := m_of_n n
  let S := P m
  have h_card : n ≤ S.card := by
    rw [ show S.card = m ^ 2 by
          erw [ Finset.card_map, Finset.card_product ] ; norm_num ; ring ];
    exact m_of_n_sq_ge_n n
  (Finset.exists_subset_card_eq h_card).choose

/-
Properties of P_seq.
-/
lemma P_seq_spec (n : ℕ) : (P_seq n).card = n ∧ P_seq n ⊆ P (m_of_n n) := by
  unfold P_seq;
  split_ifs <;> simp_all +decide;
  have := Finset.exists_subset_card_eq ( show n ≤ ( P ( m_of_n n ) |> Finset.card ) from ?_ );
  · exact ⟨ this.choose_spec.2, this.choose_spec.1 ⟩;
  · unfold P m_of_n;
    norm_num +zetaDelta at *;
    linarith [ Nat.lt_succ_sqrt n ]

/-
Helper lemma 2: A rhombus with equal diagonals is a square. Specifically, if 4 points have sides a,
a, a, a and diagonals b, b, then b = a * sqrt(2).
-/
lemma configuration_4_2_implies_square (p1 p2 p3 p4 : ℝ × ℝ) (a b : ℝ)
    (h_distinct : p1 ≠ p2 ∧ p2 ≠ p3 ∧ p3 ≠ p4 ∧ p4 ≠ p1 ∧ p1 ≠ p3 ∧ p2 ≠ p4)
    (ha : a > 0) (hb : b > 0) (hab : a ≠ b)
    (h12 : dist_euc p1 p2 = a) (h23 : dist_euc p2 p3 = a)
    (h34 : dist_euc p3 p4 = a) (h41 : dist_euc p4 p1 = a)
    (h13 : dist_euc p1 p3 = b) (h24 : dist_euc p2 p4 = b) :
    b = a * Real.sqrt 2 := by
      unfold dist_euc at *;
      rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> try linarith;
      -- By contradiction, assume $b \neq a \sqrt{2}$.
      by_contra h_contra;
      -- By expanding and simplifying, we can derive that $b^2 = 2a^2$.
      have h_b_sq : b^2 = 2 * a^2 := by
        by_cases h_eq : p1.1 = p3.1;
        · by_cases h_eq2 : p2.2 = p4.2;
          · grind (ringSteps := 500000);
          · grind;
        · grind;
      exact h_contra ( by
        nlinarith only [ ha, hb, h_b_sq, show 0 < a * Real.sqrt 2 by positivity,
          Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] )

/-
Roots of the polynomial t ^ 3 - 2 * t ^ 2 - 2 * t + 1 are -1, (3+sqrt(5))/2,
and (3-sqrt(5))/2.
-/

/-
Algebraic helper: roots of 2(1-x) = (2x-1)^2 are (1 ± sqrt(5))/4.
-/

/-
Algebraic helper: 2(1-x) = 5-4x has no solution with x <= 1.
-/

/-
Helper lemma 1: A specific 3-3 distance configuration implies the golden ratio.
-/
lemma configuration_3_3_implies_golden (p1 p2 p3 p4 : ℝ × ℝ) (a b : ℝ)
    (_h_distinct : p1 ≠ p2 ∧ p2 ≠ p3 ∧ p3 ≠ p4 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4)
    (ha : a > 0) (hb : b > 0) (hab : a ≠ b)
    (h12 : dist_euc p1 p2 = a) (h23 : dist_euc p2 p3 = a) (h34 : dist_euc p3 p4 = a)
    (h13 : dist_euc p1 p3 = b) (h24 : dist_euc p2 p4 = b) (h14 : dist_euc p1 p4 = b) :
    b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) := by
      -- Squaring both sides of each distance equation, we get $a^2 = (p1.1 - p2.1)^2 + (p1.2 -
      -- p2.2)^2$, $a^2 = (p2.1 - p3.1)^2 + (p2.2 - p3.2)^2$, $a^2 = (p3.1 - p4.1)^2 + (p3.2 -
      -- p4.2)^2$, $b^2 = (p1.1 - p3.1)^2 + (p1.2 - p3.2)^2$, $b^2 = (p2.1 - p4.1)^2 + (p2.2 -
      -- p4.2)^2$, and $b^2 = (p1.1 - p4.1)^2 + (p1.2 - p4.2)^2$.
      have h_sq_eqs : a^2 = (p1.1 - p2.1)^2 + (p1.2 - p2.2)^2 ∧
        a^2 = (p2.1 - p3.1)^2 + (p2.2 - p3.2)^2 ∧ a^2 = (p3.1 - p4.1)^2 + (p3.2 - p4.2)^2 ∧
        b^2 = (p1.1 - p3.1)^2 + (p1.2 - p3.2)^2 ∧ b^2 = (p2.1 - p4.1)^2 + (p2.2 - p4.2)^2 ∧
        b^2 = (p1.1 - p4.1)^2 + (p1.2 - p4.2)^2 := by
        unfold dist_euc at *;
        exact ⟨ by rw [ ← h12, Real.sq_sqrt <| by positivity ], by rw [ ← h23,
          Real.sq_sqrt <| by positivity ], by rw [ ← h34, Real.sq_sqrt <| by positivity ],
          by rw [ ← h13, Real.sq_sqrt <| by positivity ], by rw [ ← h24,
          Real.sq_sqrt <| by positivity ], by rw [ ← h14, Real.sq_sqrt <| by positivity ] ⟩;
      -- Let's assume without loss of generality that $p_2 = (0, 0)$ and $p_3 = (a, 0)$.
      suffices h_wlog : ∀ (p1 p2 p3 p4 : ℝ × ℝ), p2 = (0, 0) → p3 = (a,
        0) → a > 0 → b > 0 → a ≠ b → (dist_euc p1 p2 = a ∧ dist_euc p2 p3 = a ∧
          dist_euc p3 p4 = a ∧ dist_euc p1 p3 = b ∧ dist_euc p2 p4 = b ∧
            dist_euc p1 p4 = b) →
          b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) by
        -- By translating and rotating the points, we can assume without loss of generality that
        -- $p_2 = (0, 0)$ and $p_3 = (a, 0)$.
        obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
          p3.1 - p2.1 = a * Real.cos θ ∧ p3.2 - p2.2 = a * Real.sin θ := by
          use ( Complex.arg ( p3.1 - p2.1 + ( p3.2 - p2.2 ) * Complex.I ) );
          rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff ];
          · norm_num [ Complex.normSq, Complex.norm_def ];
            norm_num [ ← sq, h_sq_eqs.2.1.symm, ha.le, hb.le ];
            norm_num [ show ( p3.1 - p2.1 ) ^ 2 + ( p3.2 - p2.2 ) ^ 2 = a ^ 2 by linarith ];
            norm_num [ ha.le, ha.ne', mul_div_cancel₀ ];
          · intro h1 h2; simp_all +decide [ sub_eq_iff_eq_add ] ;
        contrapose! h_wlog;
        use ( ( p1.1 - p2.1 ) * Real.cos θ + ( p1.2 - p2.2 ) * Real.sin θ,
          - ( p1.1 - p2.1 ) * Real.sin θ + ( p1.2 - p2.2 ) * Real.cos θ ), ( 0, 0 ), ( a, 0 ),
          ( ( p4.1 - p2.1 ) * Real.cos θ + ( p4.2 - p2.2 ) * Real.sin θ,
          - ( p4.1 - p2.1 ) * Real.sin θ + ( p4.2 - p2.2 ) * Real.cos θ )
        simp_all +decide ;
        unfold dist_euc at *; simp_all +decide ;
        refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩ <;>
          rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;>
          try linarith;
        · nlinarith only [ h_sq_eqs.1, Real.sin_sq_add_cos_sq θ ];
        · grind +ring;
        · grind;
        · ring_nf at *;
          rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf at * ; linarith;
        · rw [ ← sq, h_sq_eqs.2.2.2.2.2 ] ; ring_nf;
          rw [ Real.sin_sq, Real.cos_sq ] ; ring;
      intros p1 p2 p3 p4 hp2 hp3 ha hb hab h_eqs
      have h_coords : ∃ x1 y1 x4 y4 : ℝ, p1 = (x1, y1) ∧ p4 = (x4,
        y4) ∧ x1^2 + y1^2 = a^2 ∧ (x1 - a)^2 + y1^2 = b^2 ∧ (x4 - a)^2 + y4^2 = a^2 ∧
          x4^2 + y4^2 = b^2 ∧ (x1 - x4)^2 + (y1 - y4)^2 = b^2 := by
        have h_coords : ∀ (p q : ℝ × ℝ),
          dist_euc p q = Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
          exact fun p q => rfl;
        simp_all +decide [ Real.sqrt_eq_iff_mul_self_eq_of_pos ];
        exact ⟨ p1.1, p1.2, rfl, p4.1, p4.2, rfl, by linarith, by linarith, by linarith,
          by linarith, by linarith ⟩;
      -- Let's consider the two cases: $y1 = y4$ and $y1 = -y4$.
      obtain ⟨x1, y1, x4, y4, hp1, hp4, h1, h2, h3, h4, h5⟩ := h_coords
      by_cases hy : y1 = y4;
      · -- By solving the system of equations given by h1, h2, h3, and h4, we can find the
        -- relationship between a and b.
        have h_rel : b^2 = a^2 - a * b ∨ b^2 = a^2 + a * b := by
          grind;
        rcases h_rel with h_rel | h_rel;
        · exact Or.inr <| by
            nlinarith only [ ha, hb, h_rel, show 0 < a * Real.sqrt 5 by positivity,
              show 0 < b * Real.sqrt 5 by positivity, Real.sqrt_nonneg 5,
              Real.sq_sqrt <| show 0 ≤ 5 by norm_num ]
        · exact Or.inl <| by
            nlinarith only [ ha, hb, h_rel, show 0 < a * Real.sqrt 5 by positivity,
              show 0 < b * Real.sqrt 5 by positivity, Real.sqrt_nonneg 5,
              Real.sq_sqrt <| show 0 ≤ 5 by norm_num ]
      · -- If $y1 \neq y4$, then $y1 = -y4$.
        have hy_neg : y1 = -y4 := by
          grind;
        subst hy_neg;
        have hxsum : x1 + x4 = a := by
          nlinarith only [h1, h2, h3, h4, ha]
        nlinarith only [h1, h4, h5, sq_nonneg (x1 - x4),
          sq_nonneg (x1 + x4), sq_nonneg (x1 + x4 - a), hxsum, ha, hb]

/-
Definition of C4+2K2 configuration: 4 points forming a rhombus with sides a and diagonals b.
-/
def is_C4_2K2 (S : Finset (ℝ × ℝ)) (a b : ℝ) : Prop :=
  ∃ p1 p2 p3 p4, S = {p1, p2, p3, p4} ∧ p1 ≠ p2 ∧ p2 ≠ p3 ∧
  p3 ≠ p4 ∧ p4 ≠ p1 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ dist_euc p1 p2 = a ∧
  dist_euc p2 p3 = a ∧ dist_euc p3 p4 = a ∧ dist_euc p4 p1 = a ∧
  dist_euc p1 p3 = b ∧ dist_euc p2 p4 = b

/-
Definition of P4+P4 configuration: 4 points where one distance forms a path of length 3, and the
other distance forms the complement (also a path of length 3).
-/
def is_P4_P4 (S : Finset (ℝ × ℝ)) (a b : ℝ) : Prop :=
  ∃ p1 p2 p3 p4, S = {p1, p2, p3, p4} ∧ p1 ≠ p2 ∧ p2 ≠ p3 ∧
  p3 ≠ p4 ∧ p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4 ∧ dist_euc p1 p2 = a ∧
  dist_euc p2 p3 = a ∧ dist_euc p3 p4 = a ∧ dist_euc p1 p3 = b ∧
  dist_euc p2 p4 = b ∧ dist_euc p1 p4 = b

/-
Lemma: A C4+2K2 configuration implies a square.
-/
lemma C4_2K2_implies_square (S : Finset (ℝ × ℝ)) (a b : ℝ) (ha : a > 0)
    (hb : b > 0) (hab : a ≠ b) (h : is_C4_2K2 S a b) : is_square_euc S := by
  rcases h with ⟨ p1, p2, p3, p4, rfl, h1, h2, h3, h4, h5, h6 ⟩;
  have h_square : b = a * Real.sqrt 2 := by
    apply configuration_4_2_implies_square p1 p2 p3 p4 a b
    · aesop
    all_goals tauto
  refine ⟨ p1, p2, p3, p4, ?_, ?_, ?_, ?_, ?_ ⟩ <;> aesop

/-
Lemma: A P4+P4 configuration implies golden ratio distances.
-/
lemma P4_P4_implies_golden (S : Finset (ℝ × ℝ)) (a b : ℝ) (ha : a > 0)
    (hb : b > 0) (hab : a ≠ b) (h : is_P4_P4 S a b) :
    has_golden_ratio_distances_euc S := by
  -- Apply configuration_3_3_implies_golden to conclude the existence of distances in the golden
  -- ratio.
  obtain ⟨p1, p2, p3, p4, hS, h_distinct, h12, h23, h34, h13, h24, h14⟩ := h;
  have h_gold : b = a * ((1 + Real.sqrt 5) / 2) ∨ a = b * ((1 + Real.sqrt 5) / 2) := by
    have := configuration_3_3_implies_golden p1 p2 p3 p4 a b ⟨ h_distinct, h12, h23, h34, h13,
      h24 ⟩ ha hb hab; aesop;
  use if b = a * ((1 + Real.sqrt 5) / 2) then b else a,
    if b = a * ((1 + Real.sqrt 5) / 2) then a else b;
  split_ifs <;> simp_all +decide [ distinctDistances'_euc ];
  · exact ⟨
      ⟨ ⟨ p1.1, p1.2, p3.1, p3.2, by aesop ⟩, by positivity, by positivity ⟩,
      ⟨ ⟨ p1.1, p1.2, p2.1, p2.2, by aesop ⟩, by positivity ⟩ ⟩;
  · exact ⟨
      ⟨ ⟨ p1.1, p1.2, p2.1, p2.2, by aesop ⟩, by positivity, by positivity ⟩,
      ⟨ ⟨ p1.1, p1.2, p3.1, p3.2, by aesop ⟩, by positivity ⟩ ⟩

/-
Helper lemma: A graph on 4 vertices with no monochromatic triangle of color 'a' has at most 4 edges
of color 'a'.
-/

lemma num_edges_le_4_of_no_triangle (S : Finset (ℝ × ℝ)) (d : ℝ)
    (h4 : S.card = 4)
    (h_no_triangle : ¬ ∃ p q r, {p, q, r} ⊆ S ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p ∧
      dist_euc p q = d ∧ dist_euc q r = d ∧ dist_euc r p = d) :
    (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card ≤ 8 := by
  classical
  let G : SimpleGraph S := {
    Adj := fun (x y : S) => x ≠ y ∧ dist_euc x.1 y.1 = d
    symm := {
      symm := by
        intro x y h
        exact ⟨h.1.symm, by rw [dist_euc_comm]; exact h.2⟩
    }
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  have h_directed :
      (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card =
        ((Finset.univ : Finset (S × S)).filter fun xy => G.Adj xy.1 xy.2).card := by
    have hS_nonempty : S.Nonempty := by
      apply Finset.card_pos.mp
      omega
    let defaultS : S := ⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩
    let toS (p : ℝ × ℝ) : S := if hp : p ∈ S then ⟨p, hp⟩ else defaultS
    let i (xy : (ℝ × ℝ) × (ℝ × ℝ)) : S × S := (toS xy.1, toS xy.2)
    refine Finset.card_nbij i ?_ ?_ ?_
    · intro xy hxy
      rcases Finset.mem_filter.mp hxy with ⟨hxy_off, hxy_dist⟩
      rcases Finset.mem_offDiag.mp hxy_off with ⟨hxS, hyS, _⟩
      rcases Finset.mem_offDiag.mp hxy_off with ⟨_, _, hne⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [i, toS, G, hxS, hyS, hne, hxy_dist]
    · intro xy₁ hxy₁ xy₂ hxy₂ heq
      rcases Finset.mem_filter.mp hxy₁ with ⟨hxy₁_off, _⟩
      rcases Finset.mem_offDiag.mp hxy₁_off with ⟨hx₁S, hy₁S, _⟩
      rcases Finset.mem_filter.mp hxy₂ with ⟨hxy₂_off, _⟩
      rcases Finset.mem_offDiag.mp hxy₂_off with ⟨hx₂S, hy₂S, _⟩
      have hx_eq := congrArg (fun z : S × S => (z.1 : ℝ × ℝ)) heq
      have hy_eq := congrArg (fun z : S × S => (z.2 : ℝ × ℝ)) heq
      simp [i, toS, hx₁S, hx₂S] at hx_eq
      simp [i, toS, hy₁S, hy₂S] at hy_eq
      exact Prod.ext hx_eq hy_eq
    · intro xy hxy
      rcases xy with ⟨x, y⟩
      have hAdj : G.Adj x y := (Finset.mem_filter.mp hxy).2
      refine ⟨(x.1, y.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨x.2, y.2, fun h => hAdj.1 (Subtype.ext h)⟩, hAdj.2⟩
      · ext <;> simp [i, toS]
  have h_clique_free : G.CliqueFree 3 := by
    intro t ht
    rw [SimpleGraph.is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := ht
    apply h_no_triangle
    refine ⟨a.1, b.1, c.1, ?_, ?_, ?_, ?_, hab.2, hbc.2, ?_⟩
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simp
    · exact fun h => hab.1 (Subtype.ext h)
    · exact fun h => hbc.1 (Subtype.ext h)
    · exact fun h => hac.1 ((Subtype.ext h).symm)
    · rw [dist_euc_comm]
      exact hac.2
  have h_edge_le : G.edgeFinset.card ≤ 4 := by
    have hT := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 2) h_clique_free
    simpa [Fintype.card_coe, h4] using hT
  calc
    (S.offDiag.filter (fun (x, y) => dist_euc x y = d)).card =
        2 * G.edgeFinset.card := by
          rw [h_directed]
          exact (SimpleGraph.two_mul_card_edgeFinset (G := G)).symm
    _ ≤ 8 := by omega

/-
Lemma: If a vertex is connected to 3 others by distance 'a', then there is a monochromatic triangle.
-/
lemma star_graph_implies_triangle (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (p : ℝ × ℝ) (hp : p ∈ S)
    (h_star : ∀ q ∈ S, q ≠ p → dist_euc p q = a) :
    has_equilateral_triangle_euc S := by
      -- Let $N = S \setminus \{p\}$. Since $|S|=4$, $|N|=3$.
      set N := S \ {p} with hN_def
      have hN_card : N.card = 3 := by
        rw [ Finset.card_sdiff ] ; aesop;
      -- Let $q, r, s$ be the elements of $N$.
      obtain ⟨q, r, s, hq, hr, hs, hN⟩ : ∃ q r s,
        q ∈ N ∧ r ∈ N ∧ s ∈ N ∧ q ≠ r ∧ r ≠ s ∧ s ≠ q := by
        rcases Finset.card_eq_three.mp hN_card with ⟨ q, r, s, hq, hr, hs ⟩
        use q, r, s
        aesop;
      -- If for all pairs in $N$, the distance is not $a$, then for all pairs the distance is $b$.
      by_cases h_all_b : dist_euc q r = b ∧ dist_euc r s = b ∧ dist_euc s q = b;
      · use q, r, s;
        aesop_cat;
      · -- If for any pair in $N$, the distance is $a$, then $\{p, x, y\}$ forms an equilateral
        -- triangle of side $a$.
        obtain ⟨x, y, hxN, hyN, hxy⟩ : ∃ x y,
          x ∈ N ∧ y ∈ N ∧ x ≠ y ∧ dist_euc x y = a := by
          grind;
        use p, x, y;
        simp_all +decide [ Finset.subset_iff, dist_euc ];
        exact ⟨ Ne.symm hxN.2, by rw [ ← h_star _ _ hyN.1 hyN.2 ] ; ring_nf ⟩

/-
Definition of edge count for a given distance, and lemma stating that the sum of edge counts for
distances a and b in a 4-point set is 12 (since there are 12 directed edges in total).
-/
noncomputable def edge_count (S : Finset (ℝ × ℝ)) (r : ℝ) : ℕ :=
  (S.offDiag.filter (fun (x, y) => dist_euc x y = r)).card

lemma edge_count_sum (S : Finset (ℝ × ℝ)) (a b : ℝ) (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b) :
    edge_count S a + edge_count S b = 12 := by
      -- Since there are 4 points, the total number of edges is 4 * 3 = 12.
      have h_total_edges : (Finset.offDiag S).card = 12 := by
        norm_num [ h4 ];
      rw [ ← h_total_edges,
        show edge_count S a =
          Finset.card
            ( Finset.filter ( fun x => dist_euc x.1 x.2 = a ) ( Finset.offDiag S ) ) from rfl,
        show edge_count S b =
          Finset.card
            ( Finset.filter ( fun x => dist_euc x.1 x.2 = b ) ( Finset.offDiag S ) ) from rfl,
        ← Finset.card_union_of_disjoint ];
      · congr with x ; aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => hab <| by linarith

/-
Lemma: If a graph on 4 vertices has 4 edges of color 'a' and no monochromatic triangle, it is a C4
(cycle of length 4) in color 'a'.
-/
lemma C4_of_edge_count_8 (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 8)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    is_C4_2K2 S a b := by
      -- Since $G_a$ has no triangle and its edge count is 4, it has a star graph by
      -- Lemma~\ref{lem:star_graph_implies_triangle}. Therefore, every vertex in $G_a$ has degree 2.
      have h_deg2 : ∀ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card = 2 := by
        have h_deg2 : ∀ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card ≤ 2 := by
          intro p hp
          by_contra h_contra;
          obtain ⟨q1, q2, q3, hq1, hq2, hq3, h_distinct⟩ : ∃ q1 q2 q3,
            q1 ∈ S ∧ q2 ∈ S ∧ q3 ∈ S ∧ q1 ≠ q2 ∧ q2 ≠ q3 ∧ q3 ≠ q1 ∧
              q1 ≠ p ∧ q2 ≠ p ∧ q3 ≠ p ∧
              dist_euc p q1 = a ∧ dist_euc p q2 = a ∧ dist_euc p q3 = a := by
            obtain ⟨ s, hs ⟩ := Finset.two_lt_card.mp ( lt_of_not_ge h_contra );
            obtain ⟨ hs₁, t, ht₁, u, hu₁, hst, hsu, htu ⟩ := hs; use s, t, u; aesop;
          have h_triangle : has_equilateral_triangle_euc S := by
            apply star_graph_implies_triangle S a b h4 h_dist hab p hp;
            have h_triangle : (S.erase p).card = 3 := by
              rw [ Finset.card_erase_of_mem hp, h4 ];
            rw [ Finset.card_eq_three ] at h_triangle;
            obtain ⟨ x, y, z, hxy, hxz, hyz,
              h ⟩ := h_triangle; simp_all +decide [ Finset.Subset.antisymm_iff,
              Finset.subset_iff ] ;
            grind +ring;
          contradiction;
        have h_deg2 : ∑ p ∈ S,
          (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card = 8 := by
          have h_degree_sum :
              ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card =
                edge_count S a := by
            let T : Finset (Σ p : ℝ × ℝ, ℝ × ℝ) :=
              S.sigma (fun p => (S.erase p).filter (fun q => dist_euc p q = a))
            have hT_card :
                T.card =
                  ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) (S.erase p)).card := by
              simp [T, Finset.sigma, Finset.card]
            rw [← hT_card]
            unfold edge_count
            refine Finset.card_bij (fun x hx => (x.1, x.2)) ?_ ?_ ?_
            · intro x hx
              rcases Finset.mem_sigma.mp hx with ⟨hpS, hq⟩
              rcases Finset.mem_filter.mp hq with ⟨hqerase, hpq⟩
              rcases Finset.mem_erase.mp hqerase with ⟨hqp, hqS⟩
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_offDiag.mpr ⟨hpS, hqS, hqp.symm⟩, hpq⟩
            · intro x hx y hy hxy
              cases x
              cases y
              simp at hxy
              simp [hxy]
            · intro y hy
              rcases y with ⟨p, q⟩
              rcases Finset.mem_filter.mp hy with ⟨hoff, hpq⟩
              rcases Finset.mem_offDiag.mp hoff with ⟨hpS, hqS, hpne⟩
              refine ⟨⟨p, q⟩, ?_, rfl⟩
              exact Finset.mem_sigma.mpr
                ⟨hpS,
                  Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpne.symm, hqS⟩, hpq⟩⟩
          rw [h_degree_sum, h_count]
        contrapose! h_deg2;
        exact ne_of_lt ( lt_of_lt_of_le
          ( Finset.sum_lt_sum ( fun x hx => by aesop ) ( show ∃ x, x ∈ S ∧
              Finset.card
                ( Finset.filter ( fun y => dist_euc x y = a ) ( Finset.erase S x ) ) < 2 from by
              obtain ⟨ p, hp₁, hp₂ ⟩ := h_deg2
              exact ⟨ p, hp₁, lt_of_le_of_ne ( by aesop ) hp₂ ⟩ ) )
          ( by norm_num [ * ] ) );
      have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p1, hp1S⟩ := hS_nonempty
      let N1 := (S.erase p1).filter (fun q => dist_euc p1 q = a)
      have hN1_card : N1.card = 2 := h_deg2 p1 hp1S
      obtain ⟨p2, p4, hp24, hN1_eq⟩ := Finset.card_eq_two.mp hN1_card
      have hp2N1 : p2 ∈ N1 := by simp [hN1_eq]
      have hp4N1 : p4 ∈ N1 := by simp [hN1_eq]
      have hp2_erase : p2 ∈ S.erase p1 := (Finset.mem_filter.mp hp2N1).1
      have hp4_erase : p4 ∈ S.erase p1 := (Finset.mem_filter.mp hp4N1).1
      have hp2S : p2 ∈ S := (Finset.mem_erase.mp hp2_erase).2
      have hp4S : p4 ∈ S := (Finset.mem_erase.mp hp4_erase).2
      have hp1_ne_p2 : p1 ≠ p2 := (Finset.mem_erase.mp hp2_erase).1.symm
      have hp1_ne_p4 : p1 ≠ p4 := (Finset.mem_erase.mp hp4_erase).1.symm
      have hp1p2 : dist_euc p1 p2 = a := (Finset.mem_filter.mp hp2N1).2
      have hp1p4 : dist_euc p1 p4 = a := (Finset.mem_filter.mp hp4N1).2
      have hthree_subset : ({p1, p2, p4} : Finset (ℝ × ℝ)) ⊆ S := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl | rfl
        · exact hp1S
        · exact hp2S
        · exact hp4S
      have hthree_card : ({p1, p2, p4} : Finset (ℝ × ℝ)).card = 3 := by
        simp [hp1_ne_p2, hp1_ne_p4, hp24]
      have hR_card : (S \ ({p1, p2, p4} : Finset (ℝ × ℝ))).card = 1 := by
        rw [Finset.card_sdiff, h4]
        have hinter : (({p1, p2, p4} : Finset (ℝ × ℝ)) ∩ S).card = 3 := by
          rw [Finset.inter_eq_left.mpr hthree_subset, hthree_card]
        rw [hinter]
      obtain ⟨p3, hR_eq⟩ := Finset.card_eq_one.mp hR_card
      have hp3R : p3 ∈ S \ ({p1, p2, p4} : Finset (ℝ × ℝ)) := by simp [hR_eq]
      have hp3S : p3 ∈ S := (Finset.mem_sdiff.mp hp3R).1
      have hp3_not : p3 ∉ ({p1, p2, p4} : Finset (ℝ × ℝ)) := (Finset.mem_sdiff.mp hp3R).2
      have hp3_ne_p1 : p3 ≠ p1 := by intro h; exact hp3_not (by simp [h])
      have hp3_ne_p2 : p3 ≠ p2 := by intro h; exact hp3_not (by simp [h])
      have hp3_ne_p4 : p3 ≠ p4 := by intro h; exact hp3_not (by simp [h])
      have hS_eq : S = {p1, p2, p3, p4} := by
        ext x
        constructor
        · intro hx
          by_cases hx1 : x = p1
          · simp [hx1]
          by_cases hx2 : x = p2
          · simp [hx2]
          by_cases hx4 : x = p4
          · simp [hx4]
          have hxR : x ∈ S \ ({p1, p2, p4} : Finset (ℝ × ℝ)) := by
            simp [hx, hx1, hx2, hx4]
          have hx3 : x = p3 := by simpa [hR_eq] using hxR
          simp [hx3]
        · intro hx
          simp at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hp1S
          · exact hp2S
          · exact hp3S
          · exact hp4S
      have hp2p4_not_a : dist_euc p2 p4 ≠ a := by
        intro hp2p4
        apply h_no_tri
        refine ⟨p1, p2, p4, ?_, hp1_ne_p2, hp24, hp1_ne_p4.symm, ?_, ?_⟩
        · intro x hx
          simp at hx
          rcases hx with rfl | rfl | rfl
          · exact hp1S
          · exact hp2S
          · exact hp4S
        · rw [hp1p2, hp2p4]
        · rw [hp2p4]
          rw [dist_euc_comm]
          exact hp1p4.symm
      have hp1p3_not_a : dist_euc p1 p3 ≠ a := by
        intro hp1p3
        have hp3N1 : p3 ∈ N1 := by
          simp [N1, hp3S, hp3_ne_p1, hp1p3]
        have : p3 = p2 ∨ p3 = p4 := by simpa [hN1_eq] using hp3N1
        rcases this with h | h
        · exact hp3_ne_p2 h
        · exact hp3_ne_p4 h
      have neighbor_forced
          (p q r s : ℝ × ℝ)
          (hpS : p ∈ S) (hqS : q ∈ S) (hrS : r ∈ S) (hsS : s ∈ S)
          (hS : S = {p, q, r, s})
          (hpq : dist_euc p q = a)
          (hps_not : dist_euc p s ≠ a)
          (hqp_ne : q ≠ p) (hpr_ne : p ≠ r) (hqr_ne : q ≠ r) (hrs_ne : r ≠ s) :
          dist_euc p r = a := by
        by_contra hpr_not
        let N := (S.erase p).filter (fun x => dist_euc p x = a)
        have hN_card : N.card = 2 := h_deg2 p hpS
        have hqN : q ∈ N := by
          simp [N, hqS, hqp_ne, hpq]
        have hN_subset : N ⊆ {q} := by
          intro x hx
          have hx_erase := (Finset.mem_filter.mp hx).1
          have hxS := (Finset.mem_erase.mp hx_erase).2
          have hxp : x ≠ p := (Finset.mem_erase.mp hx_erase).1
          have hxa := (Finset.mem_filter.mp hx).2
          have hx_cases : x = p ∨ x = q ∨ x = r ∨ x = s := by simpa [hS] using hxS
          rcases hx_cases with rfl | rfl | rfl | rfl
          · exact False.elim (hxp rfl)
          · simp
          · exact False.elim (hpr_not hxa)
          · exact False.elim (hps_not hxa)
        have : N.card ≤ 1 := by
          exact le_trans (Finset.card_le_card hN_subset) (by simp)
        omega
      have hp2p3 : dist_euc p2 p3 = a := by
        refine neighbor_forced p2 p1 p3 p4 hp2S hp1S hp3S hp4S ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · ext x
          simp [hS_eq]
          tauto
        · rw [dist_euc_comm]; exact hp1p2
        · exact hp2p4_not_a
        · exact hp1_ne_p2
        · exact hp3_ne_p2.symm
        · exact hp3_ne_p1.symm
        · exact hp3_ne_p4
      have hp4p3 : dist_euc p4 p3 = a := by
        refine neighbor_forced p4 p1 p3 p2 hp4S hp1S hp3S hp2S ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · ext x
          simp [hS_eq]
          tauto
        · rw [dist_euc_comm]; exact hp1p4
        · rw [dist_euc_comm]; exact hp2p4_not_a
        · exact hp1_ne_p4
        · exact hp3_ne_p4.symm
        · exact hp3_ne_p1.symm
        · exact hp3_ne_p2
      have hp1p3_b : dist_euc p1 p3 = b := by
        rcases h_dist p1 p3 hp1S hp3S hp3_ne_p1.symm with h | h
        · exact False.elim (hp1p3_not_a h)
        · exact h
      have hp2p4_b : dist_euc p2 p4 = b := by
        rcases h_dist p2 p4 hp2S hp4S hp24 with h | h
        · exact False.elim (hp2p4_not_a h)
        · exact h
      refine ⟨p1, p2, p3, p4, hS_eq, hp1_ne_p2, hp3_ne_p2.symm, hp3_ne_p4,
        hp1_ne_p4.symm, hp3_ne_p1.symm, hp24, hp1p2, hp2p3, ?_, ?_, hp1p3_b,
        hp2p4_b⟩
      · rw [dist_euc_comm]
        exact hp4p3
      · rw [dist_euc_comm]
        exact hp1p4

/-
In a 4-point set with 2 distances and no equilateral triangle, every vertex has at most 2 neighbors
at distance a.
-/
lemma max_degree_le_2 (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2 := by
      intros p hp
      by_contra h_contra;
      -- If p has degree ≥ 3 in the graph of a-edges, then there are at least 3 other points in S
      -- that are at distance a from p.
      obtain ⟨q1, q2, q3, hq1, hq2, hq3, h_distinct⟩ :
          ∃ q1 q2 q3 : ℝ × ℝ,
        q1 ∈ S ∧ q2 ∈ S ∧ q3 ∈ S ∧ q1 ≠ p ∧ q2 ≠ p ∧ q3 ≠ p ∧
          q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧
          dist_euc p q1 = a ∧ dist_euc p q2 = a ∧ dist_euc p q3 = a := by
        obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq
          ( show 3 ≤ Finset.card ( Finset.filter ( fun q => dist_euc p q = a ) S ) from by
            linarith );
        rcases Finset.card_eq_three.mp hs.2 with ⟨ q1, q2, q3, hq1, hq2, hq3 ⟩ ; use q1, q2,
          q3 ; simp_all +decide [ Finset.subset_iff ];
        refine ⟨ ?_, ?_, ?_ ⟩ <;> intro h <;> simp_all +decide;
        · unfold dist_euc at hs; norm_num at hs;
          have hpos : 0 < ( p.1 - q2.1 ) ^ 2 + ( p.2 - q2.2 ) ^ 2 := by
            exact not_le.mp fun h =>
              hq1 <| Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩
          exact hq1 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ Real.sqrt_pos.mpr hpos ],
            by nlinarith [ Real.sqrt_pos.mpr hpos ] ⟩ );
        · unfold dist_euc at hs; simp_all +decide ;
          have hsqrt : 0 ≤ Real.sqrt ( ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 ) :=
            Real.sqrt_nonneg _
          have hmul := Real.mul_self_sqrt
            ( by positivity : 0 ≤ ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 )
          exact hq1 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ hsqrt, hmul ],
            by nlinarith [ hsqrt, hmul ] ⟩ );
        · unfold dist_euc at hs; simp_all +decide ;
          have hsqrt : 0 ≤ Real.sqrt ( ( p.1 - q1.1 ) ^ 2 + ( p.2 - q1.2 ) ^ 2 ) :=
            Real.sqrt_nonneg _
          have hmul := Real.mul_self_sqrt
            ( add_nonneg ( sq_nonneg ( p.1 - q1.1 ) ) ( sq_nonneg ( p.2 - q1.2 ) ) )
          exact hq2 ( Prod.mk_inj.mpr ⟨
            by nlinarith [ hsqrt, hmul ],
            by nlinarith [ hsqrt, hmul ] ⟩ );
      have h_star : ∀ q ∈ S, q ≠ p → dist_euc p q = a := by
        intro q hq hqp; have := Finset.eq_of_subset_of_card_le ( show { q1, q2, q3,
          p } ⊆ S from by aesop_cat ) ; aesop;
      exact h_no_tri <| star_graph_implies_triangle S a b h4 h_dist hab p hp h_star

lemma edge_count_zero (S : Finset (ℝ × ℝ)) : edge_count S 0 = 0 := by
  unfold edge_count
  rw [Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hoff, hdist⟩
    rcases Finset.mem_offDiag.mp hoff with ⟨_, _, hne⟩
    exact False.elim (hne (dist_euc_eq_zero.mp hdist))
  · intro hx
    simp at hx

lemma sum_degrees_filter_eq_edge_count (S : Finset (ℝ × ℝ)) (a : ℝ) (ha : a ≠ 0) :
    ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = edge_count S a := by
  let T : Finset (Σ p : ℝ × ℝ, ℝ × ℝ) :=
    S.sigma (fun p => S.filter (fun q => dist_euc p q = a))
  have hT_card :
      T.card = ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card := by
    simp [T, Finset.sigma, Finset.card]
  rw [← hT_card]
  unfold edge_count
  refine Finset.card_bij (fun x hx => (x.1, x.2)) ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hpS, hq⟩
    rcases Finset.mem_filter.mp hq with ⟨hqS, hpq⟩
    have hne : x.1 ≠ x.2 := by
      intro h
      apply ha
      rw [← hpq, h]
      exact dist_euc_eq_zero.mpr rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hpS, hqS, hne⟩, hpq⟩
  · intro x hx y hy hxy
    cases x
    cases y
    simp at hxy
    simp [hxy]
  · intro y hy
    rcases y with ⟨p, q⟩
    rcases Finset.mem_filter.mp hy with ⟨hoff, hpq⟩
    rcases Finset.mem_offDiag.mp hoff with ⟨hpS, hqS, _⟩
    refine ⟨⟨p, q⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨hpS, Finset.mem_filter.mpr ⟨hqS, hpq⟩⟩

/-
If a 4-point set has edge count 6 and degrees are only 2 or 0, then it contains an equilateral
triangle.
-/
lemma case_2_2_2_0_implies_triangle (S : Finset (ℝ × ℝ)) (a : ℝ)
    (_h4 : S.card = 4)
    (h_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 2 ∨
      (S.filter (fun q => dist_euc p q = a)).card = 0)
    (h_count : edge_count S a = 6) :
    has_equilateral_triangle_euc S := by
      have ha : a ≠ 0 := by
        intro h
        rw [h, edge_count_zero] at h_count
        norm_num at h_count
      have h_sum_degrees : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [sum_degrees_filter_eq_edge_count S a ha, h_count]
      have h_card_two :
          (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 3 := by
        have h_degrees : ∑ p ∈ S, (Finset.filter (fun q => dist_euc p q = a) S).card =
            ∑ p ∈ S,
          if (Finset.filter (fun q => dist_euc p q = a) S).card = 2 then 2 else 0 := by
          exact Finset.sum_congr rfl fun x hx => by cases h_deg x hx <;> simp +decide [ * ] ;
        simp_all +decide [ Finset.sum_ite ];
        linarith;
      have := Finset.card_eq_three.mp h_card_two;
      obtain ⟨ x, y, z, hxy, hxz, hyz, h ⟩ := this
      simp_all +decide [ Finset.Subset.antisymm_iff,
        Finset.subset_iff ] ;
      have h_triangle : (S.filter (fun q => dist_euc x q = a)) = {y,
        z} ∧ (S.filter (fun q => dist_euc y q = a)) = {x,
        z} ∧ (S.filter (fun q => dist_euc z q = a)) = {x, y} := by
        have h_triangle : ∀ p ∈ ({x, y, z} : Finset (ℝ × ℝ)),
          (S.filter (fun q => dist_euc p q = a)).card = 2 →
            (S.filter (fun q => dist_euc p q = a)) = {x, y, z} \ {p} := by
          intros p hp hp_card
          have h_subset : {q ∈ S | dist_euc p q = a} ⊆ {x, y, z} \ {p} := by
            simp_all +decide [ Finset.subset_iff ];
            exact fun a b ha hb => ⟨ h.1 a b ha ( by
              have h_symm : ∀ p q : ℝ × ℝ,
                  p ∈ S → q ∈ S → dist_euc p q = dist_euc q p := by
                exact fun p q hp hq =>
                  Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2 ( by ring );
              grind ), by
              rintro rfl; simp_all +decide [ dist_euc ] ⟩;
          refine Finset.eq_of_subset_of_card_le h_subset ?_;
          rw [ Finset.card_sdiff ] ; aesop;
        have hyx : y ≠ x := Ne.symm hxy
        have hzx : z ≠ x := Ne.symm hxz
        have hzy : z ≠ y := Ne.symm hyz
        have hx_sdiff :
            ({x, y, z} : Finset (ℝ × ℝ)) \ {x} = {y, z} := by
          ext w
          by_cases hwx : w = x <;> by_cases hwy : w = y <;>
            by_cases hwz : w = z <;>
              simp [hwx, hwy, hwz, hxy, hxz, hyz, hyx, hzx, hzy] at *
        have hy_sdiff :
            ({x, y, z} : Finset (ℝ × ℝ)) \ {y} = {x, z} := by
          ext w
          by_cases hwx : w = x <;> by_cases hwy : w = y <;>
            by_cases hwz : w = z <;>
              simp [hwx, hwy, hwz, hxy, hxz, hyz, hyx, hzx, hzy] at *
        have hz_sdiff :
            ({x, y, z} : Finset (ℝ × ℝ)) \ {z} = {x, y} := by
          ext w
          by_cases hwx : w = x <;> by_cases hwy : w = y <;>
            by_cases hwz : w = z <;>
              simp [hwx, hwy, hwz, hxy, hxz, hyz, hyx, hzx, hzy] at *
        constructor
        · rw [← hx_sdiff]
          exact h_triangle x (by simp) h.2.1.2
        constructor
        · rw [← hy_sdiff]
          exact h_triangle y (by simp) h.2.2.1.2
        · rw [← hz_sdiff]
          exact h_triangle z (by simp) h.2.2.2.2
      use x, y, z; simp_all +decide [ Finset.ext_iff ] ;
      have := h_triangle.1 y.1 y.2
      have := h_triangle.2.1 z.1 z.2
      have := h_triangle.2.2 x.1 x.2
      simp_all +decide ;
      exact ⟨ by aesop_cat, Ne.symm hxz ⟩

/-
Arithmetic lemma: if 4 numbers <= 2 sum to 6, they are either {2,2,2,0} or {2,2,1,1}.
-/

/-
If a function on a 4-element set sums to 6 and is bounded by 2, then the values are either {2,2,2,0}
or {2,2,1,1}.
-/
lemma degree_sum_6_max_2_finset {α : Type*} (S : Finset α) (f : α → ℕ)
    (h4 : S.card = 4)
    (h_le : ∀ x ∈ S, f x ≤ 2)
    (h_sum : ∑ x ∈ S, f x = 6) :
    ((S.filter (fun x => f x = 2)).card = 3 ∧ (S.filter (fun x => f x = 0)).card = 1) ∨
    ((S.filter (fun x => f x = 2)).card = 2 ∧ (S.filter (fun x => f x = 1)).card = 2) := by
      classical
      -- Let's count the total number of elements in S with values 2, 1, and 0.
      have h_total :
          (Finset.filter (fun x => f x = 2) S).card +
            (Finset.filter (fun x => f x = 1) S).card +
              (Finset.filter (fun x => f x = 0) S).card = 4 := by
        rw [ ← h4, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones S ▸ by
          rw [ Finset.sum_congr rfl ]
          intro x hx
          have := h_le x hx
          interval_cases f x <;> simp +decide
      have h_sum :
          (Finset.filter (fun x => f x = 2) S).card * 2 +
            (Finset.filter (fun x => f x = 1) S).card * 1 +
              (Finset.filter (fun x => f x = 0) S).card * 0 = 6 := by
        rw [ ← h_sum, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        simpa only [ Finset.sum_mul _ _ _ ] using by
          rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ]
          exact Finset.sum_congr rfl fun x hx => by
            have := h_le x hx
            interval_cases f x <;> trivial
      omega

/-
The case where 3 vertices have degree 2 and 1 has degree 0 is impossible because it implies an
equilateral triangle.
-/
lemma eliminate_case_2_2_2_0 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (_h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_no_tri : ¬ has_equilateral_triangle_euc S)
    (h_case : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 3 ∧
              (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 0)).card = 1) :
    False := by
      have h_deg : ∀ p ∈ S,
        (S.filter (fun q => dist_euc p q = a)).card = 2 ∨
          (S.filter (fun q => dist_euc p q = a)).card = 0 := by
        have h_deg :
            Finset.card
              (Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2) S) +
              Finset.card (Finset.filter (fun p =>
                (S.filter (fun q => dist_euc p q = a)).card = 0) S) = S.card := by
          grind;
        have h_deg :
            Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2) S ∪
              Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 0) S = S := by
          exact Finset.eq_of_subset_of_card_le
            ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )
            ( by
              rw [ Finset.card_union_of_disjoint
                ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ), h_deg ] );
        intro p hp; replace h_deg := Finset.ext_iff.mp h_deg p; aesop;
      exact h_no_tri <| case_2_2_2_0_implies_triangle S a h4 h_deg h_count

/-
If a graph on 4 vertices has 6 directed edges, max degree 2, and no triangle, then it has 2 vertices
of degree 2 and 2 vertices of degree 1.
-/
lemma degrees_2_2_1_1 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
    (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2 := by
      have ha : a ≠ 0 := by
        intro h
        rw [h, edge_count_zero] at h_count
        norm_num at h_count
      have h_deg_sum : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [sum_degrees_filter_eq_edge_count S a ha, h_count]
      exact Or.resolve_left ( degree_sum_6_max_2_finset S _ h4 h_max_deg h_deg_sum ) fun h =>
        eliminate_case_2_2_2_0 S a h4 h_count h_max_deg h_no_tri h

/-
The sum of degrees equals the edge count (assuming a != 0).
-/
lemma sum_degrees_eq_edge_count (S : Finset (ℝ × ℝ)) (a : ℝ) (ha : a ≠ 0) :
    ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = edge_count S a := by
  exact sum_degrees_filter_eq_edge_count S a ha

/-
If two vertices have degree 1 in a graph with 6 directed edges on 4 vertices, they cannot be
connected to each other.
-/
lemma degree_1_vertices_not_connected (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (u v : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1) :
    dist_euc u v ≠ a := by
      -- Assume for contradiction that dist_euc u v = a.
      by_contra h_contra
      have h_neighborhoods : {q ∈ S | dist_euc u q = a} = {v} ∧
        {q ∈ S | dist_euc v q = a} = {u} := by
        have h_neighborhoods : v ∈ {q ∈ S | dist_euc u q = a} ∧
            u ∈ {q ∈ S | dist_euc v q = a} := by
          simp [h_contra];
          exact ⟨ hv, hu, by
            rw [ ← h_contra, dist_euc ]
            exact Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2
              ( by simpa [ dist_comm ] using by ring ) ⟩;
        exact ⟨ Finset.card_eq_one.mp h_deg_u |> fun ⟨ x, hx ⟩ => by aesop,
          Finset.card_eq_one.mp h_deg_v |> fun ⟨ x, hx ⟩ => by aesop ⟩;
      -- Let S' = S \ {u, v}. S' has size 2. Let S' = {x, y}.
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℝ × ℝ,
        x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧
          S = {u, v, x, y} := by
        have h_card_S' : (S \ {u, v}).card = 2 := by
          rw [ Finset.card_sdiff ] ; aesop_cat;
        obtain ⟨ x, y, hx, hy ⟩ := Finset.card_eq_two.mp h_card_S';
        use x, y; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
        grind;
      -- The sum of degrees in S is 6. deg(u) + deg(v) = 1 + 1 = 2. So ∑ p ∈ S',
      -- deg(p) = 6 - 2 = 4.
      have h_sum_degrees_S' :
          (S.filter (fun q => dist_euc x q = a)).card +
            (S.filter (fun q => dist_euc y q = a)).card = 4 := by
        have h_total : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
          rw [← h_count, sum_degrees_eq_edge_count]
          rintro rfl
          simp_all +decide [Finset.card_eq_one]
          exact huv (by
            rw [dist_euc] at h_contra
            have hsqrt : 0 ≤ Real.sqrt ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) :=
              Real.sqrt_nonneg _
            have hsq := Real.sq_sqrt
              (add_nonneg (sq_nonneg (u.1 - v.1)) (sq_nonneg (u.2 - v.2)))
            exact Prod.mk_inj.mpr ⟨
              by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, hsqrt, hsq],
              by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, hsqrt, hsq]⟩)
        rcases hxy with ⟨hxy_ne, hxu, hxv, hyu, hyv, hS_eq⟩
        rw [hS_eq]
        rw [hS_eq] at h_total h_deg_u h_deg_v
        have hsum :
            (1 : ℕ) + (1 +
              ((({u, v, x, y} : Finset (ℝ × ℝ)).filter
                    (fun q => dist_euc x q = a)).card +
                (({u, v, x, y} : Finset (ℝ × ℝ)).filter
                  (fun q => dist_euc y q = a)).card)) = 6 := by
          simpa [huv, hxy_ne, hxy_ne.symm, hxu, hxu.symm, hxv, hxv.symm,
            hyu, hyu.symm, hyv, hyv.symm, h_deg_u, h_deg_v, Finset.sum_insert]
            using h_total
        omega
      -- Since $u$ and $v$ have no neighbors in $S'$, neighbors of $p$ must be in $S'$.
      have h_neighborhoods_S' : (S.filter (fun q => dist_euc x q = a)) ⊆ {x,
        y} ∧ (S.filter (fun q => dist_euc y q = a)) ⊆ {x, y} := by
        simp_all +decide [ Finset.subset_iff ];
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        simp_all +decide [ dist_euc ];
        exact ⟨
          ⟨
            fun h => False.elim <| h_neighborhoods.1.2.1 <| by
              rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring,
            fun h => False.elim <| h_neighborhoods.2.2.2.1 <| by
              rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
              ring ⟩,
          fun h => False.elim <| h_neighborhoods.1.2.2 <| by
            rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
            ring,
          fun h => False.elim <| h_neighborhoods.2.2.2.2 <| by
            rw [ ← h, Real.sqrt_inj ( by positivity ) ( by positivity ) ]
            ring ⟩;
      have ha : a ≠ 0 := by
        intro ha0
        rw [ha0, edge_count_zero] at h_count
        norm_num at h_count
      have hx_not_mem : x ∉ S.filter (fun q => dist_euc x q = a) := by
        intro hx_mem
        have hxx : dist_euc x x = a := (Finset.mem_filter.mp hx_mem).2
        exact ha (by simpa [dist_euc] using hxx.symm)
      have hx_sub : S.filter (fun q => dist_euc x q = a) ⊆ {y} := by
        intro z hz
        have hz' := h_neighborhoods_S'.1 hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz' ⊢
        rcases hz' with rfl | rfl
        · exact False.elim (hx_not_mem hz)
        · rfl
      have hx_card : (S.filter (fun q => dist_euc x q = a)).card ≤ 1 := by
        simpa using Finset.card_le_card hx_sub
      have hy_card : (S.filter (fun q => dist_euc y q = a)).card ≤ 2 :=
        h_max_deg y hy
      omega

/-
If two degree 1 vertices share a neighbor x (degree 2), it leads to a contradiction (sum of degrees
too low).
-/
lemma degree_1_neighbors_distinct (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (u v x : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (hx : x ∈ S)
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1)
    (h_deg_x : (S.filter (fun q => dist_euc x q = a)).card = 2)
    (h_ux : dist_euc u x = a)
    (h_vx : dist_euc v x = a) :
    False := by
      have h_y_deg : ∀ y ∈ S,
        y ≠ u ∧ y ≠ v ∧ y ≠ x →
          dist_euc y u ≠ a ∧ dist_euc y v ≠ a ∧ dist_euc y x ≠ a := by
        intros y hy hy_ne
        have h_y_u : dist_euc y u ≠ a := by
          intro H; have := Finset.card_eq_one.mp h_deg_u; obtain ⟨ q,
            hq ⟩ := this; simp_all +decide ;
          rw [ Finset.eq_singleton_iff_unique_mem ] at hq ; simp_all +decide [ dist_euc ];
          grind
        have h_y_v : dist_euc y v ≠ a := by
          intro H;
          have := Finset.card_eq_one.mp h_deg_v; obtain ⟨ z,
            hz ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
          have := hz _ _ |>.1 ⟨ hy, ?_ ⟩ <;> simp_all +decide;
          · specialize hz x.1 x.2 ; aesop;
          · convert H using 1;
            unfold dist_euc; ring_nf;
        have h_y_x : dist_euc y x ≠ a := by
          intro H;
          have h_y_x : Finset.card (Finset.filter (fun q => dist_euc x q = a) S) ≥ 3 := by
            refine Finset.two_lt_card.mpr ⟨u, ?_, v, ?_, y, ?_, huv, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨hu, by rw [dist_euc_comm]; exact h_ux⟩
            · exact Finset.mem_filter.mpr ⟨hv, by rw [dist_euc_comm]; exact h_vx⟩
            · exact Finset.mem_filter.mpr ⟨hy, by rw [dist_euc_comm]; exact H⟩
            · exact hy_ne.1.symm
            · exact hy_ne.2.1.symm
          linarith [ h_max_deg x hx ]
        exact ⟨h_y_u, h_y_v, h_y_x⟩;
      have h_sum_degrees : ∑ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card = 6 := by
        rw [ ← h_count, ← sum_degrees_eq_edge_count ];
        rintro rfl; simp_all +decide [ dist_euc ];
        exact hux <| Prod.mk_inj.mpr ⟨
          by
            rw [ Real.sqrt_eq_zero' ] at h_ux
            nlinarith only [ h_ux ],
          by
            rw [ Real.sqrt_eq_zero' ] at h_ux
            nlinarith only [ h_ux ] ⟩;
      rw [ ← Finset.sum_sdiff
        ( Finset.insert_subset hu
          ( Finset.insert_subset hv ( Finset.singleton_subset_iff.mpr hx ) ) )
        ] at *
      simp_all +decide [ Finset.sum_insert ] ;
      have h_card_S_minus : (S \ {u, v, x}).card = 1 := by
        rw [ Finset.card_sdiff ] ; simp +decide [ * ];
      rw [ Finset.card_eq_one ] at h_card_S_minus ; obtain ⟨ y,
        hy ⟩ := h_card_S_minus ; simp_all +decide [ Finset.sum_singleton ];
      rw [ Finset.card_eq_two ] at h_sum_degrees ; obtain ⟨ z, w,
        hzw ⟩ := h_sum_degrees ; simp_all +decide [ Finset.ext_iff ];
      grind

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, any vertex with degree 1 is connected to a
vertex with degree 2.
-/
lemma degree_1_connects_to_degree_2 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
             (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (u : ℝ × ℝ) (hu : u ∈ S) (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1) :
    ∃ x ∈ S, (S.filter (fun q => dist_euc x q = a)).card = 2 ∧ dist_euc u x = a := by
      obtain ⟨v, hv, h_deg_v⟩ : ∃ v ∈ S, v ≠ u ∧ dist_euc u v = a := by
        obtain ⟨ v, hv ⟩ := Finset.card_eq_one.mp h_deg_u;
        rw [ Finset.eq_singleton_iff_unique_mem ] at hv;
        by_cases hvu : v = u;
        · subst v
          have ha0 : a = 0 := by
            have hdist := (Finset.mem_filter.mp hv.1).2
            simpa [dist_euc] using hdist.symm
          rw [ha0, edge_count_zero] at h_count
          norm_num at h_count
        · exact ⟨ v, Finset.mem_filter.mp hv.1 |>.1, hvu, Finset.mem_filter.mp hv.1 |>.2 ⟩;
      refine ⟨ v, hv, ?_, h_deg_v.2 ⟩;
      -- Since $v$ is not in the set of vertices with degree 1, its degree must be 2.
      have h_not_in_deg1 :
          v ∉ Finset.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1) S := by
        have := degree_1_vertices_not_connected S a h4 h_count h_max_deg u v hu hv; aesop;
      have := h_max_deg v hv
      interval_cases _ : Finset.card ( Finset.filter ( fun q => dist_euc v q = a ) S ) <;>
        simp_all +decide ;
      specialize ‹∀ a_1 b : ℝ, ( a_1, b ) ∈ S → ¬dist_euc v ( a_1,
        b ) = a› u.1 u.2 ; simp_all +decide;
      exact ‹¬dist_euc v u = a› ( by
        rw [ ← h_deg_v.2, dist_euc ]
        exact Real.sqrt_inj ( by positivity ) ( by positivity ) |>.2 <| by ring )

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, the two degree 1 vertices are connected to
distinct degree 2 vertices.
-/
lemma degree_1_connects_to_distinct_degree_2 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (u v : ℝ × ℝ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1) :
    ∃ x y : ℝ × ℝ, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
      (S.filter (fun q => dist_euc x q = a)).card = 2 ∧
      (S.filter (fun q => dist_euc y q = a)).card = 2 ∧
      dist_euc u x = a ∧ dist_euc v y = a := by
        obtain ⟨x, hx⟩ : ∃ x ∈ S,
          (S.filter (fun q => dist_euc x q = a)).card = 2 ∧ dist_euc u x = a := by
          exact degree_1_connects_to_degree_2 S a h4 h_count h_max_deg h_deg u hu h_deg_u
        obtain ⟨y, hy⟩ : ∃ y ∈ S,
          (S.filter (fun q => dist_euc y q = a)).card = 2 ∧ dist_euc v y = a := by
          exact degree_1_connects_to_degree_2 S a h4 h_count h_max_deg h_deg v hv h_deg_v;
        by_cases hxy : x = y;
        · have := degree_1_neighbors_distinct S a h4 h_count h_max_deg u v x hu hv hx.1
            huv ( by aesop ) ( by aesop ) h_deg_u h_deg_v hx.2.1 ( by aesop ) ( by aesop )
          aesop;
        · exact ⟨ x, y, hx.1, hy.1, hxy, hx.2.1, hy.2.1, hx.2.2, hy.2.2 ⟩

/-
The number of directed edges of a given length in a graph is even (because edges come in pairs (u,v)
and (v,u)).
-/
lemma edge_count_even (S : Finset (ℝ × ℝ)) (r : ℝ) : Even (edge_count S r) := by
  unfold edge_count;
  -- The set of edges is symmetric because `dist_euc` is symmetric.
  have h_symm : ∀ (x y : ℝ × ℝ),
      x ∈ S ∧ y ∈ S ∧ x ≠ y → dist_euc x y = r → dist_euc y x = r := by
    unfold dist_euc; intro x y h h'; ring_nf at *; aesop;
  -- Let's consider the set of edges in the graph where the distance is r.
  set E := (S.offDiag.filter (fun (x, y) => dist_euc x y = r)) with hE_def;
  -- Since $E$ is symmetric, we can pair each element $(x, y)$ with $(y, x)$.
  have h_pair : ∃ T : Finset ((ℝ × ℝ) × ℝ × ℝ),
      E = T ∪ Finset.image (fun p => (p.2, p.1)) T ∧
        Disjoint T (Finset.image (fun p => (p.2, p.1)) T) := by
    refine ⟨ E.filter fun p => p.1.1 < p.2.1 ∨ p.1.1 = p.2.1 ∧ p.1.2 < p.2.2, ?_, ?_ ⟩;
    · ext ⟨x, y⟩; simp [E];
      cases lt_trichotomy x.1 y.1 <;> cases lt_trichotomy x.2 y.2 <;> aesop;
    · norm_num [ Finset.disjoint_right ];
      grind;
  obtain ⟨ T, hT₁, hT₂ ⟩ := h_pair; rw [ hT₁,
    Finset.card_union_of_disjoint hT₂ ] ; simp_all +decide [ parity_simps ] ;
  rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ]

/-
If x (degree 2) is connected to u (degree 1), then x is connected to y (the other degree 2 vertex).
-/
lemma degree_2_connected_to_degree_2_if_connected_to_degree_1 (S : Finset (ℝ × ℝ)) (a : ℝ)
    (h4 : S.card = 4)
    (h_count : edge_count S a = 6)
    (h_max_deg : ∀ p ∈ S, (S.filter (fun q => dist_euc p q = a)).card ≤ 2)
    (_h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2)
    (x y u v : ℝ × ℝ) (hx : x ∈ S) (hy : y ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≠ y) (huv : u ≠ v)
    (h_deg_x : (S.filter (fun q => dist_euc x q = a)).card = 2)
    (h_deg_y : (S.filter (fun q => dist_euc y q = a)).card = 2)
    (h_deg_u : (S.filter (fun q => dist_euc u q = a)).card = 1)
    (h_deg_v : (S.filter (fun q => dist_euc v q = a)).card = 1)
    (h_conn : dist_euc x u = a) :
    dist_euc x y = a := by
  have hxu : x ≠ u := by
    intro h
    subst u
    omega
  have hxv : x ≠ v := by
    intro h
    subst v
    omega
  have hyu : y ≠ u := by
    intro h
    subst u
    omega
  have hyv : y ≠ v := by
    intro h
    subst v
    omega
  have ha : a ≠ 0 := by
    intro ha0
    exact hxu (dist_euc_eq_zero.mp (h_conn.trans ha0))
  have hux : dist_euc u x = a := by
    rw [dist_euc_comm]
    exact h_conn
  by_contra hxy_conn
  obtain ⟨z, hz_mem, hzu⟩ := Finset.exists_mem_ne
    (by omega : 1 < (S.filter (fun q => dist_euc x q = a)).card) u
  have hzS : z ∈ S := (Finset.mem_filter.mp hz_mem).1
  have hxz : dist_euc x z = a := (Finset.mem_filter.mp hz_mem).2
  have hzx : z ≠ x := by
    intro h
    subst z
    exact ha (by simpa [dist_euc] using hxz.symm)
  have hzy : z ≠ y := by
    intro h
    subst z
    exact hxy_conn hxz
  have hfour_subset : ({x, y, u, v} : Finset (ℝ × ℝ)) ⊆ S := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx, hy, hu, hv⟩
  have hfour_card : ({x, y, u, v} : Finset (ℝ × ℝ)).card = 4 := by
    simp [hxy, hxu, hxv, hyu, hyv, huv]
  have hfour_eq : ({x, y, u, v} : Finset (ℝ × ℝ)) = S :=
    Finset.eq_of_subset_of_card_le hfour_subset (by omega)
  have hz_cases : z = x ∨ z = y ∨ z = u ∨ z = v := by
    have : z ∈ ({x, y, u, v} : Finset (ℝ × ℝ)) := by
      rw [hfour_eq]
      exact hzS
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hzv : z = v := by
    rcases hz_cases with h | h | h | h
    · exact False.elim (hzx h)
    · exact False.elim (hzy h)
    · exact False.elim (hzu h)
    · exact h
  subst z
  have hvx_dist : dist_euc v x = a := by
    rw [dist_euc_comm]
    exact hxz
  exact degree_1_neighbors_distinct S a h4 h_count h_max_deg u v x hu hv hx huv
    hxu.symm hxv.symm h_deg_u h_deg_v h_deg_x hux hvx_dist

/-
In a graph with 4 vertices and degrees {2, 2, 1, 1}, the two degree 2 vertices are connected to each
other.
-/

/-- The two degree-one vertices and their distinct degree-two neighbors
give the required path ordering. -/
lemma path_graph_structure (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 6)
    (h_no_tri : ¬ has_equilateral_triangle_euc S)
    (h_deg : (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 2)).card = 2 ∧
      (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card = 2) :
    is_P4_P4 S a b := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp
    (show 1 < (S.filter (fun p => (S.filter (fun q => dist_euc p q = a)).card = 1)).card
      by omega)
  rcases Finset.mem_filter.mp hu with ⟨hu, hdu⟩
  rcases Finset.mem_filter.mp hv with ⟨hv, hdv⟩
  have hmax := max_degree_le_2 S a b h4 h_dist hab h_no_tri
  obtain ⟨x, y, hx, hy, hxy, hdx, hdy, hux, hvy⟩ :=
    degree_1_connects_to_distinct_degree_2 S a h4 h_count hmax h_deg u v hu hv huv hdu hdv
  have huxne : u ≠ x := by intro h; subst x; omega
  have huyne : u ≠ y := by intro h; subst y; omega
  have hvxne : v ≠ x := by intro h; subst x; omega
  have hvyne : v ≠ y := by intro h; subst y; omega
  have hxyedge : dist_euc x y = a :=
    degree_2_connected_to_degree_2_if_connected_to_degree_1 S a h4 h_count hmax h_deg
      x y u v hx hy hu hv hxy huv hdx hdy hdu hdv (by rw [dist_euc_comm]; exact hux)
  have huunique : ∀ z ∈ S, dist_euc u z = a → z = x := by
    intro z hz he
    exact Finset.card_le_one.mp (by omega : (S.filter (fun q => dist_euc u q = a)).card ≤ 1)
      z (Finset.mem_filter.mpr ⟨hz, he⟩) x (Finset.mem_filter.mpr ⟨hx, hux⟩)
  have hvunique : ∀ z ∈ S, dist_euc v z = a → z = y := by
    intro z hz he
    exact Finset.card_le_one.mp (by omega : (S.filter (fun q => dist_euc v q = a)).card ≤ 1)
      z (Finset.mem_filter.mpr ⟨hz, he⟩) y (Finset.mem_filter.mpr ⟨hy, hvy⟩)
  have huy : dist_euc u y = b :=
    (h_dist u y hu hy huyne).resolve_left (fun he => hxy (huunique y hy he).symm)
  have hvx : dist_euc v x = b :=
    (h_dist v x hv hx hvxne).resolve_left (fun he => hxy (hvunique x hx he))
  have huv' : dist_euc u v = b :=
    (h_dist u v hu hv huv).resolve_left (fun he => hvxne (huunique v hv he))
  have hset : S = {u, x, y, v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro hu (And.intro hx (And.intro hy hv))
    · simp [h4, huxne, huyne, huv, hxy, hvxne.symm, hvyne.symm]
  exact ⟨u, x, y, v, hset, huxne, hxy, hvyne.symm, huyne, hvxne.symm, huv,
    hux, hxyedge, by rw [dist_euc_comm]; exact hvy, huy,
    by rw [dist_euc_comm]; exact hvx, huv'⟩

/-
If a 4-point graph has 6 edges of color 'a' and no equilateral triangle, it has golden ratio
distances.
-/
lemma count_6_implies_golden (S : Finset (ℝ × ℝ)) (a b : ℝ)
    (h4 : S.card = 4)
    (h_dist : ∀ x y, x ∈ S → y ∈ S → x ≠ y → dist_euc x y = a ∨ dist_euc x y = b)
    (hab : a ≠ b)
    (h_count : edge_count S a = 6)
    (h_no_tri : ¬ has_equilateral_triangle_euc S) :
    has_golden_ratio_distances_euc S := by
      -- Apply `path_graph_structure` to show that the graph is a P4 path graph (`is_P4_P4`).
      have h_path : is_P4_P4 S a b := by
        apply path_graph_structure S a b h4 h_dist hab h_count h_no_tri;
        have := degrees_2_2_1_1 S a h4 h_count
          ( max_degree_le_2 S a b h4 h_dist hab h_no_tri ) h_no_tri
        aesop;
      apply_rules [ P4_P4_implies_golden ];
      · contrapose! hab;
        obtain ⟨ p1, p2, p3, p4, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
          h11, h12 ⟩ := h_path
        exact absurd h7 ( by
          linarith [ show 0 < dist_euc p1 p2 from Real.sqrt_pos.mpr ( by
            exact not_le.mp fun h => h1 <| by
              exact Prod.mk_inj.mpr <| ⟨
                by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ],
                by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩ ) ] );
      · contrapose! h_no_tri;
        obtain ⟨ p1, p2, p3, p4, hS, h12, h23, h34, h13, h24, h14 ⟩ := h_path;
        exact False.elim <| h_no_tri.not_gt <| h14.2.2.2.2.1 ▸
          Real.sqrt_pos.2 ( by
            exact not_le.mp fun h =>
              h13 <| Prod.mk_inj.mpr ⟨ by nlinarith only [ h ], by nlinarith only [ h ] ⟩ )

/-
Proof of Perucca's classification theorem: any 4-point set with 2 distances is a square, has an
equilateral triangle, or has golden ratio distances.
-/
theorem PeruccaClassificationStatement_proof : PeruccaClassificationStatement := by
  classical
  intro S h4 h_distinct
  by_cases htri : has_equilateral_triangle_euc S
  · exact Or.inr (Or.inl htri)
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp h_distinct
  have ha : 0 < a := distinctDistances_euc_pos (by rw [hset]; simp)
  have hb : 0 < b := distinctDistances_euc_pos (by rw [hset]; simp)
  have hd : ∀ x y, x ∈ S → y ∈ S → x ≠ y →
      dist_euc x y = a ∨ dist_euc x y = b := by
    intro x y hx hy hxy
    have hm := mem_distinctDistances_euc.mpr ⟨x, hx, y, hy, hxy, rfl⟩
    rw [hset] at hm
    simpa using hm
  have hsum := edge_count_sum S a b h4 hd hab
  have hbound (d : ℝ) : edge_count S d ≤ 8 := by
    apply num_edges_le_4_of_no_triangle S d h4
    rintro ⟨p, q, r, hsub, hpq, hqr, hrp, h1, h2, h3⟩
    apply htri
    exact ⟨p, q, r, hsub, hpq, hqr, hrp, by rw [h1, h2], by rw [h2, h3]⟩
  have he := edge_count_even S a
  have hc : edge_count S a = 4 ∨ edge_count S a = 6 ∨ edge_count S a = 8 := by
    obtain ⟨k, hk⟩ := he
    have hba := hbound a
    have hbb := hbound b
    omega
  rcases hc with hc | hc | hc
  · have hcb : edge_count S b = 8 := by omega
    exact Or.inl (C4_2K2_implies_square S b a hb ha hab.symm
      (C4_of_edge_count_8 S b a h4
        (fun x y hx hy hxy => (hd x y hx hy hxy).symm) hab.symm hcb htri))
  · exact Or.inr (Or.inr (count_6_implies_golden S a b h4 hd hab hc htri))
  · exact Or.inl (C4_2K2_implies_square S a b ha hb hab
      (C4_of_edge_count_8 S a b h4 hd hab hc htri))

/-
Any 4-point subset of P_m determines at least 3 distinct Euclidean distances.
-/

open EuclideanGeometry Finset Real

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

scoped notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

/--
Given a finite set of points in the plane, we define the number of distinct distances between pairs
of points.
-/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card

noncomputable def toEuclideanPoint (p : ℝ × ℝ) : ℝ² :=
  !₂[p.1, p.2]

lemma toEuclideanPoint_injective : Function.Injective toEuclideanPoint := by
  rintro ⟨x, y⟩ ⟨z, t⟩ h
  apply Prod.ext
  · simpa [toEuclideanPoint] using
      congrArg (fun v : ℝ² => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2) v) 0) h
  · simpa [toEuclideanPoint] using
      congrArg (fun v : ℝ² => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2) v) 1) h

lemma dist_toEuclideanPoint (p q : ℝ × ℝ) :
    dist (toEuclideanPoint p) (toEuclideanPoint q) = dist_euc p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨z, t⟩
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  norm_num [toEuclideanPoint, dist_euc, Fin.sum_univ_two]

lemma distinctDistances'_euc_eq_offDiag_image (S : Finset (ℝ × ℝ)) :
    distinctDistances'_euc S =
      S.offDiag.image (fun pair : (ℝ × ℝ) × (ℝ × ℝ) => dist_euc pair.1 pair.2) := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hd_image, hd_zero⟩
    rcases Finset.mem_image.mp hd_image with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_product.mp hpair with ⟨hp, hq⟩
    have hpq : pair.1 ≠ pair.2 := by
      intro hpq
      apply hd_zero
      simp [dist_euc_eq_zero.mpr hpq]
    exact Finset.mem_image.mpr
      ⟨pair, Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨pair, Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    · simp [dist_euc_eq_zero, hpq]

lemma distinctDistances_image_toEuclideanPoint (S : Finset (ℝ × ℝ)) :
    distinctDistances (S.image toEuclideanPoint) = (distinctDistances'_euc S).card := by
  unfold distinctDistances
  rw [distinctDistances'_euc_eq_offDiag_image]
  apply congrArg Finset.card
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    rcases Finset.mem_image.mp hp with ⟨p, hpS, hp_eq⟩
    rcases Finset.mem_image.mp hq with ⟨q, hqS, hq_eq⟩
    refine Finset.mem_image.mpr ⟨(p, q), ?_, ?_⟩
    · exact Finset.mem_offDiag.mpr
        ⟨hpS, hqS, fun hpq' => hpq (by
          rw [← hp_eq, ← hq_eq]
          exact congrArg toEuclideanPoint hpq')⟩
    · calc
        dist_euc (p, q).1 (p, q).2 = dist (toEuclideanPoint p) (toEuclideanPoint q) :=
          (dist_toEuclideanPoint p q).symm
        _ = dist pair.1 pair.2 := by rw [hp_eq, hq_eq]
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pair, hpair, rfl⟩
    rcases Finset.mem_offDiag.mp hpair with ⟨hp, hq, hpq⟩
    refine Finset.mem_image.mpr
      ⟨(toEuclideanPoint pair.1, toEuclideanPoint pair.2), ?_, ?_⟩
    · exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_image.mpr ⟨pair.1, hp, rfl⟩,
          Finset.mem_image.mpr ⟨pair.2, hq, rfl⟩,
          fun h => hpq (toEuclideanPoint_injective h)⟩
    · exact dist_toEuclideanPoint pair.1 pair.2

end

/-! ### Upstream module `ErdosProblems/Erdos659.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 659.
https://www.erdosproblems.com/forum/thread/659

Formalization status:
- Unconditional

Informal authors:
- Benjamin Grayzel
- Adam Sheffer
- Pieter Moree
- Robert Osburn
- Desmond Weisenberg
- Gemini

Statement authors:
- Formal Conjectures authors

Formal authors:
- Aristotle
- Boris Alexeev
- Codex (unconditional Bernays proof and integration)

URLs:
- https://adamsheffer.wordpress.com/2014/07/16/point-sets-with-few-distinct-distances/
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos659.md
-/
/-
We formalized the solution to the Erdős problem concerning distances and points.
We defined the lattice `L` and the point sets `P_m`.
We proved that `P_m` satisfies the local constraint (every 4 points determine at least 3 distances)
by reducing it to the absence of squares, equilateral triangles, and golden ratio distances in `L`,
which we verified.
We proved that the number of distinct distances in `P_m` is bounded by `B_Q(3m^2)`, where `Q` is the
quadratic form `x^2 + 2y^2`.
Using the proved Bernays theorem, we established the asymptotic bound `O(n /
sqrt(log n))` for the number of distinct distances in a subset of size `n`.
--
I have proved Perucca's classification theorem (`PeruccaClassificationStatement_proof`) using some
helper lemmas I established.
-/

open Filter Asymptotics EuclideanGeometry Finset Real
open scoped Real

/-
Define the quadratic form Q(u,v) = u^2 + 2v^2 and prove it is primitive and positive definite with
discriminant -8.
-/
def Q_form : BinQuadForm := ⟨1, 0, 2⟩

lemma Q_form_primitive : Q_form.Primitive := by
  unfold BinQuadForm.Primitive Q_form
  decide

lemma Q_form_posDef : Q_form.PosDef := by
  unfold BinQuadForm.PosDef BinQuadForm.discr Q_form
  decide

lemma Q_form_discr : Q_form.discr = -8 := by
  unfold BinQuadForm.discr Q_form
  rfl

/-
The number of distinct Euclidean distances in P_m is bounded by B_Q(3m^2).
-/
theorem distinctDistances'_euc_bound (m : ℕ) (_hm : m ≥ 1) :
    (distinctDistances'_euc (P m)).card ≤ BinQuadForm.B Q_form (3 * m ^ 2) := by
      -- The number of distinct squared distances in P_m is at most the number of integers ≤ 3m^2
      -- represented by the quadratic form Q(u,v) = u^2 + 2v^2.
      have h_card_dist_sq : (distinctDistances'_euc (P m)).card ≤
          (Nat.card {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n}) := by
        -- By definition of $distinctDistances'_euc$, every element in $distinctDistances'_euc (P
        -- m)$ is a square root of an integer in the set $\{n \mid (n : ℝ) \leq 3 *
        -- m ^ 2 ∧ \exists
        -- u v : ℤ, (Q_form.eval u v : ℤ) = n\}$.
        have h_subset : ∀ d ∈ distinctDistances'_euc (P m),
          ∃ n ∈ {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n},
          d = Real.sqrt n := by
          intro d hd
          obtain ⟨p, q, hp, hq, hd_eq⟩ : ∃ p q : ℝ × ℝ,
            p ∈ P m ∧ q ∈ P m ∧ dist_euc p q = d := by
            unfold distinctDistances'_euc at hd;
            simp +zetaDelta at *;
            tauto;
          obtain ⟨ u, v, hu, hv, h ⟩ := P_dist_sq_form m p q hp hq;
          use Int.natAbs (u^2 + 2 * v^2);
          field_simp;
          constructor;
          · constructor;
            · norm_cast;
              nlinarith only [ abs_lt.mp hu, abs_lt.mp hv,
                abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ];
            · use u, v;
              unfold Q_form
              norm_num [ abs_of_nonneg ( by positivity : 0 ≤ u ^ 2 + 2 * v ^ 2 ) ] ;
              unfold BinQuadForm.eval; norm_num; ring;
          · norm_num [ ← hd_eq, ← h ];
            rw [ Real.sqrt_sq ( by exact Real.sqrt_nonneg _ ) ];
        have h_finite : Set.Finite {n : ℕ | (n : ℝ) ≤ 3 * m ^ 2 ∧
            ∃ u v : ℤ, (Q_form.eval u v : ℤ) = n} := by
          exact Set.finite_iff_bddAbove.mpr
            ⟨ ⌊ ( 3 * m ^ 2 : ℝ ) ⌋₊, fun n hn => Nat.le_floor hn.1 ⟩
        have h_card : (distinctDistances'_euc (P m)).card ≤
            (Finset.image (fun n : ℕ => Real.sqrt n) (Set.Finite.toFinset h_finite)).card := by
          exact Finset.card_le_card fun x hx => by
            obtain ⟨ n, hn, rfl ⟩ := h_subset x hx
            exact Finset.mem_image.mpr ⟨ n, by aesop ⟩ ;
        generalize_proofs at *;
        exact h_card.trans ( Finset.card_image_le.trans ( by
          rw [ ← Nat.card_eq_finsetCard ]
          aesop ) );
      simpa [BinQuadForm.B] using h_card_dist_sq

/-
The quadratic form Q satisfies the conditions of Bernays' theorem.
-/

/-
Main theorem: Existence of sets P_n satisfying the local constraint and the distinct distance bound.
-/
theorem main_theorem (h_perucca : PeruccaClassificationStatement)
    (h_bernays : ∀ (Δ : ℤ) (_hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ),
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))) :
    ∃ (P : ℕ → Finset (ℝ × ℝ)),
      (∀ n, (P n).card = n) ∧
      (∀ n, n ≥ 4 → ∀ S, S ⊆ P n → S.card = 4 →
        (distinctDistances'_euc S).card ≥ 3) ∧
      (Asymptotics.IsBigO Filter.atTop (fun n => ((distinctDistances'_euc (P n)).card : ℝ))
        (fun n => (n : ℝ) / Real.sqrt (Real.log n))) := by
          -- Apply Bernays' theorem to the quadratic form Q.
          obtain ⟨CΔ, hCΔ_pos, hCΔ⟩ : ∃ CΔ : ℝ,
            0 < CΔ ∧ (fun x => (Q_form.B x : ℝ)) ~[Filter.atTop]
              (fun x => CΔ * x / Real.sqrt (Real.log x)) := by
            exact h_bernays _
              (by
                rintro ⟨ z, hz ⟩
                nlinarith [ show z ≤ 2 by nlinarith, show z ≥ -2 by nlinarith ])
              |> fun ⟨ CΔ, hCΔ₁, hCΔ₂ ⟩ =>
                ⟨ CΔ, hCΔ₁, hCΔ₂ _ Q_form_primitive Q_form_posDef Q_form_discr ⟩;
          refine ⟨ fun n => P_seq n, ?_, ?_, ?_ ⟩;
          · exact fun n => P_seq_spec n |>.1;
          · intro n hn S hS hS_card
            have h_subset : S ⊆ P (m_of_n n) := by
              exact hS.trans ( P_seq_spec n |>.2 );
            exact P_local_constraint (m_of_n n) h_perucca S h_subset hS_card;
          · -- Since $B_Q(3 * (m_of_n n)^2) \leq B_Q(3n + 6\sqrt{n} + 3)$, we can
            -- use the bound from
            -- Bernays' theorem.
            have h_bound : ∀ n : ℕ,
              n ≥ 1 →
                (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) := by
              intros n hn
              have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                  (Q_form.B (3 * (m_of_n n) ^ 2) : ℝ) := by
                have h_bound : (distinctDistances'_euc (P_seq n)).card ≤
                    (distinctDistances'_euc (P (m_of_n n))).card := by
                  have h_subset : P_seq n ⊆ P (m_of_n n) := by
                    exact P_seq_spec n |>.2;
                  apply_rules [ Finset.card_le_card ];
                  simp_all +decide [ Finset.subset_iff ];
                  unfold distinctDistances'_euc; aesop;
                exact_mod_cast h_bound.trans ( distinctDistances'_euc_bound _ <| Nat.succ_pos _ );
              refine le_trans h_bound ?_;
              refine Nat.cast_le.mpr ?_;
              refine Nat.card_mono ?_ ?_;
              · refine Set.finite_iff_bddAbove.mpr ⟨ ⌊3 * n + 6 * Real.sqrt n + 3⌋₊,
                fun x hx => Nat.le_floor <| hx.1 ⟩;
              · refine fun x hx => ⟨ ?_, hx.2 ⟩;
                refine le_trans hx.1 ?_;
                norm_num [ m_of_n ];
                nlinarith only [ show ( n.sqrt : ℝ ) ^ 2 ≤ n by exact_mod_cast Nat.sqrt_le' n,
                  Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n,
                  show ( n.sqrt : ℝ ) ≥ 0 by positivity ];
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$.
            have h_bernays_bound : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) /
                  Real.sqrt (Real.log (3 * n + 6 * Real.sqrt n + 3)) * 2 := by
              have h_bernays_bound : ∀ᶠ x in Filter.atTop,
                (Q_form.B x : ℝ) ≤ CΔ * x / Real.sqrt (Real.log x) * 2 := by
                have := hCΔ.def ( show 0 < 1 by norm_num );
                filter_upwards [ this, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
                norm_num [ abs_of_nonneg, div_nonneg, Real.sqrt_nonneg, hCΔ_pos.le,
                  hx₂.le ] at hx₁ ⊢;
                rw [ abs_of_nonneg ( by positivity : 0 ≤ x ) ] at hx₁
                linarith [ abs_le.mp hx₁ ];
              rw [ Filter.eventually_atTop ] at *;
              obtain ⟨ a, ha ⟩ := h_bernays_bound
              use Max.max a 1
              intro b hb
              specialize ha ( 3 * b + 6 * Real.sqrt b + 3 )
                ( by linarith [ le_max_left a 1, le_max_right a 1, Real.sqrt_nonneg b ] )
              aesop;
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log(3n + 6\sqrt{n} + 3)}$ for sufficiently large $n$.
            have h_bernays_bound_simplified : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                CΔ * (3 * n + 6 * Real.sqrt n + 3) / Real.sqrt (Real.log n) * 2 := by
              filter_upwards [ h_bernays_bound,
                Filter.eventually_gt_atTop 1 ] with n hn hn' using
                le_trans hn ( mul_le_mul_of_nonneg_right
                  ( div_le_div_of_nonneg_left ( by positivity )
                    ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) <|
                      Real.sqrt_le_sqrt <| Real.log_le_log ( by positivity ) <|
                        by linarith [ Real.sqrt_nonneg n ] )
                  zero_le_two );
            -- Using the bound from Bernays' theorem, we get $B_Q(3n + 6\sqrt{n} + 3) \leq CΔ * (3n
            -- + 6\sqrt{n} + 3) / \sqrt{\log n}$ for sufficiently large $n$.
            have h_bernays_bound_final : ∀ᶠ n in Filter.atTop,
              (Q_form.B (3 * n + 6 * Real.sqrt n + 3) : ℝ) ≤
                12 * CΔ * n / Real.sqrt (Real.log n) := by
              filter_upwards [ h_bernays_bound_simplified,
                Filter.eventually_gt_atTop 16 ] with n hn hn';
              refine le_trans hn ?_;
              rw [ div_mul_eq_mul_div,
                div_le_div_iff_of_pos_right ( Real.sqrt_pos.mpr <| Real.log_pos <| by linarith ) ];
              nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n,
                mul_le_mul_of_nonneg_left
                  ( show Real.sqrt n ≤ n / 2 by
                    nlinarith [ sq_nonneg ( Real.sqrt n - 4 ),
                      Real.mul_self_sqrt ( show 0 ≤ n by linarith ), Real.sqrt_nonneg n ] )
                  hCΔ_pos.le ];
            rw [ Asymptotics.isBigO_iff ];
            exact ⟨ 12 * CΔ, by
              filter_upwards [ Filter.eventually_ge_atTop 1,
                h_bernays_bound_final.natCast_atTop ] with n hn hn'
              rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ),
                Real.norm_of_nonneg ( by positivity ) ]
              exact le_trans ( h_bound n hn ) ( by simpa [ mul_div_assoc ] using hn' ) ⟩

/-! ### Bernays' theorem, now proved -/

theorem bernays
    (Δ : ℤ) (hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x)) :=
  Bernays.bernays_theorem Δ hΔnonsq

/-! ### Erdős Problem 659 -/

theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  obtain ⟨P, hP_card, hP_local, hP_bigO⟩ :=
    main_theorem PeruccaClassificationStatement_proof
      (by intro Δ hΔ; exact bernays Δ hΔ)
  refine ⟨fun n => (P n).image toEuclideanPoint, ?_, ?_⟩
  · intro n
    constructor
    · rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
    · intro S hS hS_card
      have hA_card : ((P n).image toEuclideanPoint).card = n := by
        rw [Finset.card_image_of_injective _ toEuclideanPoint_injective, hP_card n]
      have hn : n ≥ 4 := by
        have hle := Finset.card_le_card hS
        rw [hA_card, hS_card] at hle
        omega
      let S' : Finset (ℝ × ℝ) := (P n).filter (fun p => toEuclideanPoint p ∈ S)
      have hS'_subset : S' ⊆ P n := by
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      have hS_image : S'.image toEuclideanPoint = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
          exact (Finset.mem_filter.mp hp).2
        · intro hx
          have hxA : x ∈ (P n).image toEuclideanPoint := hS hx
          rcases Finset.mem_image.mp hxA with ⟨p, hp, rfl⟩
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩
      have hS'_card : S'.card = 4 := by
        rw [← hS_card, ← hS_image,
          Finset.card_image_of_injective _ toEuclideanPoint_injective]
      have hdist := hP_local n hn S' hS'_subset hS'_card
      rw [← hS_image, distinctDistances_image_toEuclideanPoint]
      exact hdist
  · simpa [distinctDistances_image_toEuclideanPoint] using hP_bigO

end

#print axioms erdos_659
-- 'Erdos659.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos659
