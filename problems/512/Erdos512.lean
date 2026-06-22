import Mathlib

namespace Erdos512

-- ============================================================
-- Hardy
-- ============================================================

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Complex

noncomputable section

namespace Littlewood

/-- The harmonic sum `∑_{k=1}^{N} 1/k`. -/
def harmonic (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, 1 / (k + 1 : ℝ)

/-- `log N` is bounded above by the `N`-th harmonic number. -/
theorem log_le_harmonic (N : ℕ) : Real.log N ≤ harmonic N := by
  by_contra! h_contra
  have h_ind : ∀ N : ℕ, Real.log (N + 1) ≤ harmonic N := by
    intro N; induction' N with N ih <;> norm_num [ Finset.sum_range_succ, harmonic ] at *
    rw [ Real.log_le_iff_le_exp ( by positivity ) ] at *
    rw [ Real.exp_add ]
    nlinarith [ Real.add_one_le_exp ( ( N:ℝ ) + 1 ) ⁻¹, Real.exp_pos ( ( N:ℝ ) + 1 ) ⁻¹, mul_inv_cancel₀ ( by linarith : ( N:ℝ ) + 1 ≠ 0 ) ]
  exact h_contra.not_ge ( le_trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num [ harmonic ] at h_contra ) <| by norm_num ) <| h_ind N )

/-- A function on the circle is *co-analytic* (spectrum in `ℤ≤0`) if all its Fourier
coefficients of strictly positive index vanish. -/
def CoAnalytic (φ : AddCircle (1 : ℝ) → ℂ) : Prop :=
  ∀ n : ℤ, 0 < n → fourierCoeff φ n = 0

/-- A *co-analytic trigonometric polynomial*: a finite ℂ-linear combination of the monomials
`fourier a` with `a ≤ 0`. -/
def TrigPolyNeg (φ : AddCircle (1 : ℝ) → ℂ) : Prop :=
  ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ a ∈ s, a ≤ 0) ∧ ∀ x, φ x = ∑ a ∈ s, c a * fourier a x

/-
Each monomial `c • fourier a` with `a ≤ 0` is integrable (continuous on a probability space).
-/
theorem integrable_fourier_smul (a : ℤ) (c : ℂ) :
    Integrable (fun x => c * fourier a x) (@AddCircle.haarAddCircle 1 _) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => ‖c‖ * 1;
  · fun_prop;
  · exact Continuous.aestronglyMeasurable ( continuous_const.mul ( by continuity ) );
  · simp +decide [ fourier ]

theorem TrigPolyNeg.continuous {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    Continuous φ := by
  obtain ⟨ s, c, h₁, h₂ ⟩ := h;
  rw [ show φ = _ from funext h₂ ] ; continuity;

theorem TrigPolyNeg.integrable {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    Integrable φ (@AddCircle.haarAddCircle 1 _) :=
  h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-
A co-analytic trigonometric polynomial is co-analytic.
-/
theorem TrigPolyNeg.coAnalytic {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    CoAnalytic φ := by
  intro n hn;
  obtain ⟨ s, c, hs, he ⟩ := h;
  rw [ show φ = _ from funext he, fourierCoeff ];
  simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, smul_smul, ← fourier_add ];
  rw [ MeasureTheory.integral_finset_sum _ fun i hi => ?_ ];
  · refine Finset.sum_eq_zero fun a ha => ?_;
    -- Since $n > 0$ and $a \leq 0$, we have $n - a > 0$, thus the integral of $e^{i(n-a)x}$ over the circle is zero.
    have h_int : ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier (n - a) x) ∂AddCircle.haarAddCircle = 0 := by
      have h_int : ∀ k : ℤ, k ≠ 0 → ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier k x) ∂AddCircle.haarAddCircle = 0 := by
        intro k hk_ne_zero
        have h_int : ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier k x) ∂AddCircle.haarAddCircle = (starRingEnd ℂ) (∫ x : AddCircle 1, fourier k x ∂AddCircle.haarAddCircle) := by
          rw [ ← integral_conj ];
        have := @fourierCoeff_fourier;
        specialize @this 1 ( by exact ⟨ by norm_num ⟩ ) k; simp_all +decide [ funext_iff, fourierCoeff ] ;
        specialize this 0; simp_all +decide [ Pi.single_apply ] ;
      exact h_int _ ( by linarith [ hs a ha ] );
    simp_all +decide [ fourier, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg ];
    rw [ MeasureTheory.integral_const_mul, h_int, MulZeroClass.mul_zero ];
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop;
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq, Filter.Eventually ]

theorem TrigPolyNeg.const (c : ℂ) : TrigPolyNeg (fun _ => c) := by
  refine ⟨{0}, (fun _ => c), by simp, ?_⟩
  intro x; simp

theorem TrigPolyNeg.fourier_neg {a : ℤ} (ha : a ≤ 0) : TrigPolyNeg (fun x => fourier a x) := by
  refine ⟨{a}, (fun _ => 1), by simpa using ha, ?_⟩
  intro x; simp

theorem TrigPolyNeg.add {φ ψ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (hψ : TrigPolyNeg ψ) :
    TrigPolyNeg (fun x => φ x + ψ x) := by
  -- By definition of TrigPolyNeg, we can write φ and ψ as finite sums of the form ∑ a ∈ s, c a * fourier a x.
  obtain ⟨s₁, c₁, h₁, e₁⟩ := hφ
  obtain ⟨s₂, c₂, h₂, e₂⟩ := hψ;
  refine' ⟨ s₁ ∪ s₂, fun a => ( if a ∈ s₁ then c₁ a else 0 ) + ( if a ∈ s₂ then c₂ a else 0 ), _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, Finset.sum_union ];
  · rintro a ( ha | ha ) <;> [ exact h₁ a ha; exact h₂ a ha ];
  · simp +decide [ Finset.sum_add_distrib, add_mul, Finset.sum_union ]

theorem TrigPolyNeg.smul {φ : AddCircle (1 : ℝ) → ℂ} (c : ℂ) (hφ : TrigPolyNeg φ) :
    TrigPolyNeg (fun x => c * φ x) := by
  obtain ⟨ s, c', hc ⟩ := hφ;
  exact ⟨ s, fun a => c * c' a, fun a ha => hc.1 a ha, fun x => by simp +decide [ hc.2, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩

theorem TrigPolyNeg.neg {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) :
    TrigPolyNeg (fun x => - φ x) := by
  simpa using hφ.smul (-1)

theorem TrigPolyNeg.mul {φ ψ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (hψ : TrigPolyNeg ψ) :
    TrigPolyNeg (fun x => φ x * ψ x) := by
  obtain ⟨ s₁, c₁, h₁, e₁ ⟩ := hφ
  obtain ⟨ s₂, c₂, h₂, e₂ ⟩ := hψ;
  -- Consider the finite set of pairs `(a,b)` with `a ∈ s₁` and `b ∈ s₂`. For each such pair, `fourier a x * fourier b x = fourier (a+b) x`. The coefficients in the product are products of the coefficients of `φ` and `ψ`.
  have h_prod_expansion : ∀ x, φ x * ψ x = ∑ p ∈ s₁ ×ˢ s₂, (c₁ p.1 * c₂ p.2) * fourier (p.1 + p.2) x := by
    simp +decide [ e₁, e₂, Finset.sum_product, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, fourier_add ];
    exact fun x => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  refine' ⟨ Finset.image ( fun p : ℤ × ℤ => p.1 + p.2 ) ( s₁ ×ˢ s₂ ), fun n => ∑ p ∈ Finset.filter ( fun p : ℤ × ℤ => p.1 + p.2 = n ) ( s₁ ×ˢ s₂ ), c₁ p.1 * c₂ p.2, _, _ ⟩;
  · grind;
  · simp +decide [ h_prod_expansion, Finset.sum_filter, Finset.sum_mul ];
    intro x; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
    rw [ Finset.sum_filter_of_ne ] ; aesop

theorem TrigPolyNeg.sum {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ) → ℂ)
    (hf : ∀ i ∈ s, TrigPolyNeg (f i)) : TrigPolyNeg (fun x => ∑ i ∈ s, f i x) := by
  induction' s using Finset.induction with i s hi ih;
  · convert TrigPolyNeg.const 0;
  · simpa [ Finset.sum_insert hi ] using TrigPolyNeg.add ( hf i ( Finset.mem_insert_self i s ) ) ( ih fun j hj => hf j ( Finset.mem_insert_of_mem hj ) )

theorem TrigPolyNeg.pow {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (k : ℕ) :
    TrigPolyNeg (fun x => (φ x) ^ k) := by
  induction' k with k ih;
  · simpa using TrigPolyNeg.const 1;
  · convert TrigPolyNeg.mul hφ ih using 1 ; ext ; ring

/-
**Shift formula.** Multiplying by `fourier a` shifts Fourier coefficients by `a`.
-/
theorem fourierCoeff_fourier_mul {G : AddCircle (1 : ℝ) → ℂ} (a n : ℤ) :
    fourierCoeff (fun x => fourier a x * G x) n = fourierCoeff G (n - a) := by
  unfold fourier fourierCoeff;
  simp +decide [ sub_eq_add_neg, fourier_add, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, smul_eq_mul ]

/-
Fourier coefficients are bounded by the sup norm (on a probability space).
-/
theorem norm_fourierCoeff_le {G : AddCircle (1 : ℝ) → ℂ} (M : ℝ)
    (hM : ∀ x, ‖G x‖ ≤ M) (n : ℤ) : ‖fourierCoeff G n‖ ≤ M := by
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun x => M;
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · norm_num;
  · filter_upwards [ ] with x using by simpa [ norm_mul ] using hM x;
  · norm_num [ MeasureTheory.measureReal_def ]

/-
Co-analyticity passes to uniform limits of continuous functions.
-/
theorem coAnalytic_of_tendstoUniformly {f : ℕ → (AddCircle (1 : ℝ) → ℂ)}
    {g : AddCircle (1 : ℝ) → ℂ} (hcont : ∀ K, Continuous (f K)) (hg : Continuous g)
    (hf : ∀ K, CoAnalytic (f K))
    (h : TendstoUniformly f g Filter.atTop) : CoAnalytic g := by
  intro n hn;
  -- From the uniform convergence of $f_K$ to $g$, we have that $\|f_K - g\|_\infty \to 0$.
  have h_unif : Filter.Tendsto (fun K => sSup (Set.range (fun x => ‖f K x - g x‖))) Filter.atTop (nhds 0) := by
    rw [ Metric.tendstoUniformly_iff ] at h;
    rw [ Metric.tendsto_nhds ];
    simp_all +decide [ dist_eq_norm' ];
    intro ε hε; obtain ⟨ a, ha ⟩ := h ( ε / 2 ) ( half_pos hε ) ; use a; intro b hb; rw [ abs_of_nonneg ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ] ; exact lt_of_le_of_lt ( csSup_le ( Set.range_nonempty _ ) <| Set.forall_mem_range.2 fun x => le_of_lt <| ha b hb x ) <| by linarith;
  -- By the triangle inequality, we have $\|fourierCoeff (f_K) n - fourierCoeff g n\| \leq \|f_K - g\|_\infty$.
  have h_triangle : ∀ K, ‖fourierCoeff (f K) n - fourierCoeff g n‖ ≤ sSup (Set.range (fun x => ‖f K x - g x‖)) := by
    intro K
    have h_triangle : ‖fourierCoeff (fun x => f K x - g x) n‖ ≤ sSup (Set.range (fun x => ‖f K x - g x‖)) := by
      apply_rules [ norm_fourierCoeff_le ];
      · exact fun x => le_csSup ( IsCompact.bddAbove ( isCompact_range ( show Continuous fun x => ‖f K x - g x‖ from Continuous.norm ( hcont K |> Continuous.sub <| hg ) ) ) ) ( Set.mem_range_self x );
    convert h_triangle using 1;
    unfold fourierCoeff; norm_num [ sub_mul ] ;
    rw [ ← MeasureTheory.integral_sub ] ; congr ; ext ; ring;
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · fun_prop (disch := norm_num);
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · fun_prop (disch := norm_num);
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  exact tendsto_nhds_unique ( tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => norm_nonneg _ ) h_triangle h_unif ) ( tendsto_const_nhds.congr fun K => by simp +decide [ hf K n hn ] )

/-
Uniform convergence of the exponential partial sums of a bounded continuous function.
-/
theorem expPartialSum_tendstoUniformly {φ : AddCircle (1 : ℝ) → ℂ} (hφ : Continuous φ) :
    TendstoUniformly
      (fun K x => ∑ k ∈ Finset.range K, (φ x) ^ k / (k.factorial : ℂ))
      (fun x => Complex.exp (φ x)) Filter.atTop := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M := by
    exact IsCompact.exists_bound_of_continuousOn ( isCompact_univ ) hφ.continuousOn |> Exists.imp fun M hM => by tauto;
  rw [ Metric.tendstoUniformly_iff ];
  -- Using the bound on the exponential series, we have:
  have h_exp_bound : ∀ n, ∀ x, ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ ≤ ∑' k, (M ^ (k + n) / (Nat.factorial (k + n))) := by
    intro n x
    have h_exp_bound : ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ ≤ ∑' k, ‖(φ x) ^ (k + n) / (Nat.factorial (k + n))‖ := by
      have h_exp_bound : ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ = ‖∑' k, (φ x) ^ (k + n) / (Nat.factorial (k + n))‖ := by
        have h_exp_bound : cexp (φ x) = ∑' k, (φ x) ^ k / (k.factorial : ℂ) := by
          simp +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
        rw [ h_exp_bound, ← Summable.sum_add_tsum_nat_add n ];
        · norm_num;
        · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial ‖φ x‖;
      convert norm_tsum_le_tsum_norm _ ; norm_num;
      exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective n;
    refine' le_trans h_exp_bound ( Summable.tsum_le_tsum _ _ _ );
    · exact fun k => by simpa using div_le_div_of_nonneg_right ( pow_le_pow_left₀ ( norm_nonneg _ ) ( hM x ) _ ) ( Nat.cast_nonneg _ ) ;
    · simpa using summable_nat_add_iff n |>.2 <| Real.summable_pow_div_factorial _;
    · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective _;
  -- The series $\sum_{k=n}^{\infty} \frac{M^k}{k!}$ converges to $0$ as $n \to \infty$.
  have h_series_zero : Filter.Tendsto (fun n => ∑' k, (M ^ (k + n) / (Nat.factorial (k + n)))) Filter.atTop (nhds 0) := by
    convert tendsto_sum_nat_add fun k => M ^ k / ( k.factorial : ℝ ) using 1;
  exact fun ε ε_pos => by rcases Metric.tendsto_atTop.mp h_series_zero ε ε_pos with ⟨ N, hN ⟩ ; exact Filter.eventually_atTop.mpr ⟨ N, fun n hn x => lt_of_le_of_lt ( h_exp_bound n x ) ( by linarith [ abs_lt.mp ( hN n hn ) ] ) ⟩ ;

/-
**`exp` of a co-analytic trigonometric polynomial is co-analytic.**
-/
theorem TrigPolyNeg.coAnalytic_exp {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) :
    CoAnalytic (fun x => Complex.exp (φ x)) := by
  convert coAnalytic_of_tendstoUniformly _ _ _ _ using 1;
  use fun K x => ∑ k ∈ Finset.range K, ( ( k.factorial : ℂ ) ⁻¹ ) * ( φ x ) ^ k;
  · exact fun K => continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) ( hφ.continuous.pow _ );
  · exact Complex.continuous_exp.comp ( TrigPolyNeg.continuous hφ );
  · intro K; exact (by
    convert TrigPolyNeg.coAnalytic ( TrigPolyNeg.sum ( Finset.range K ) ( fun k => fun x => ( k.factorial : ℂ ) ⁻¹ * φ x ^ k ) _ ) using 1;
    exact fun i hi => TrigPolyNeg.smul _ ( TrigPolyNeg.pow hφ i ));
  · convert expPartialSum_tendstoUniformly ( TrigPolyNeg.continuous hφ ) using 1;
    exact funext fun K => funext fun x => Finset.sum_congr rfl fun _ _ => by ring;

/-! ## Stage 2 : L² machinery, `exp` bounds, and the co-analytic majorant -/

/-- The `L²` norm on the circle. -/
def L2nrm (g : AddCircle (1 : ℝ) → ℂ) : ℝ :=
  Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _))

theorem L2nrm_nonneg (g : AddCircle (1 : ℝ) → ℂ) : 0 ≤ L2nrm g := Real.sqrt_nonneg _

/-
`(L2nrm g)^2 = ∫ ‖g‖²`.
-/
theorem sq_L2nrm (g : AddCircle (1 : ℝ) → ℂ) :
    (L2nrm g) ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _) := by
  unfold L2nrm; rw [ Real.sq_sqrt <| MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ] ;

/-
The integral of `fourier k` over the circle is `1` if `k = 0` and `0` otherwise.
-/
theorem integral_fourier (k : ℤ) :
    (∫ x, fourier k x ∂(@AddCircle.haarAddCircle 1 _)) = if k = 0 then 1 else 0 := by
  split_ifs <;> simp_all +decide [ fourier ];
  -- Use the fact that the integral of a non-zero frequency exponential over the circle is zero.
  have h_int_zero : ∀ k : ℤ, k ≠ 0 → ∫ x : AddCircle (1 : ℝ), (fourier k x : ℂ) ∂ (@AddCircle.haarAddCircle 1 _) = 0 := by
    intro k hk_ne;
    have := @fourierCoeff_fourier;
    convert congr_fun ( @this 1 ⟨ by norm_num ⟩ k ) 0 using 1;
    · unfold fourierCoeff; aesop;
    · rw [ Pi.single_eq_of_ne ( Ne.symm hk_ne ) ];
  convert h_int_zero k ‹_› using 1

/-
**Parseval for trigonometric polynomials.**
-/
theorem parseval_trigpoly (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ x, ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _))
      = ∑ a ∈ s, ‖c a‖ ^ 2 := by
  -- Expand the square of the absolute value and use the orthogonality relation.
  have h_expand : ∫ x, ‖∑ a ∈ s, c a * fourier a x‖^2 ∂(@AddCircle.haarAddCircle 1 _) = ∑ a ∈ s, ∑ b ∈ s, c a * starRingEnd ℂ (c b) * ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) := by
    have h_expand : ∀ x : AddCircle (1 : ℝ), ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 = ∑ a ∈ s, ∑ b ∈ s, c a * starRingEnd ℂ (c b) * fourier a x * starRingEnd ℂ (fourier b x) := by
      intro x
      have h_expand : ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 = (∑ a ∈ s, c a * fourier a x) * (∑ b ∈ s, starRingEnd ℂ (c b) * starRingEnd ℂ (fourier b x)) := by
        have h_expand : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        aesop;
      exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul, ← MeasureTheory.integral_const_mul ];
    convert integral_ofReal.symm;
    convert ( MeasureTheory.integral_finset_sum s fun i hi => ?_ ) |> Eq.symm using 1;
    convert rfl;
    convert MeasureTheory.integral_finset_sum s _;
    · intro i hi; apply_rules [ Continuous.integrable_of_hasCompactSupport ];
      · fun_prop;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
    · exact congr_arg _ ( funext fun x => mod_cast h_expand x );
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · fun_prop;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  -- Evaluate the integral $\int x, fourier a x * starRingEnd ℂ (fourier b x) ∂haar$.
  have h_integral : ∀ a b : ℤ, ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) = if a = b then 1 else 0 := by
    intro a b
    have h_integral : ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) = ∫ x, fourier (a - b) x ∂(@AddCircle.haarAddCircle 1 _) := by
      simp +decide [ sub_eq_add_neg, fourier_add, fourier_neg ];
    convert integral_fourier ( a - b ) using 1;
    grind;
  convert congr_arg Complex.re h_expand using 1;
  simp_all +decide [ Complex.normSq, Complex.sq_norm ]

/-
`L²` norm is bounded by the sup norm.
-/
theorem L2nrm_le_sup {g : AddCircle (1 : ℝ) → ℂ} {M : ℝ} (h0 : 0 ≤ M) (hM : ∀ x, ‖g x‖ ≤ M) :
    L2nrm g ≤ M := by
  refine' Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩;
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun x => M ^ 2;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · norm_num;
  · filter_upwards [ ] using fun x => pow_le_pow_left₀ ( norm_nonneg _ ) ( hM x ) 2;
  · norm_num [ MeasureTheory.measureReal_def ]

/-
**Integral Cauchy–Schwarz (core form).**
-/
theorem integral_norm_mul_le_L2 {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u) (hv : Continuous v) :
    (∫ x, ‖u x‖ * ‖v x‖ ∂(@AddCircle.haarAddCircle 1 _)) ≤ L2nrm u * L2nrm v := by
  convert MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg _ _ _ _ _ using 1;
  rotate_left;
  exact 2;
  exact 2;
  all_goals norm_num [ Real.holderConjugate_iff ];
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · refine' MeasureTheory.MemLp.norm _;
    refine' hu.memLp_of_hasCompactSupport _;
    exact HasCompactSupport.of_compactSpace u;
  · refine' MemLp.mono' _ _ _;
    exact fun x => ( SupSet.sSup ( Set.range ( fun x => ‖v x‖ ) ) );
    · exact MeasureTheory.memLp_const _;
    · exact hv.norm.aestronglyMeasurable;
    · filter_upwards [ ] with x using by simpa using le_csSup ( IsCompact.bddAbove ( isCompact_range ( show Continuous fun x => ‖v x‖ from hv.norm ) ) ) ( Set.mem_range_self x ) ;
  · norm_num [ ← Real.sqrt_eq_rpow, L2nrm ]

/-
A Fourier coefficient of a product is bounded by the product of `L²` norms.
-/
theorem norm_fourierCoeff_mul_le {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u)
    (hv : Continuous v) (n : ℤ) :
    ‖fourierCoeff (fun x => u x * v x) n‖ ≤ L2nrm u * L2nrm v := by
  refine' le_trans _ ( integral_norm_mul_le_L2 hu hv );
  convert MeasureTheory.norm_integral_le_integral_norm ( _ : AddCircle ( 1 : ℝ ) → ℂ ) using 1;
  simp +decide [ norm_smul, fourier_apply ]

/-
**Minkowski inequality** for `L2nrm`.
-/
theorem L2nrm_add_le {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u) (hv : Continuous v) :
    L2nrm (fun x => u x + v x) ≤ L2nrm u + L2nrm v := by
  unfold L2nrm;
  -- By the properties of the integral, we can pull the square root out of the integral.
  have h_integral : ∫ x, ‖u x + v x‖ ^ 2 ∂AddCircle.haarAddCircle ≤ (∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) + 2 * (∫ x, ‖u x‖ * ‖v x‖ ∂AddCircle.haarAddCircle) + (∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ];
    · refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
      · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
          rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ] );
      · filter_upwards [ ] with x using by nlinarith only [ norm_nonneg ( u x + v x ), norm_add_le ( u x ) ( v x ), norm_nonneg ( u x ), norm_nonneg ( v x ) ] ;
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        exact IsClosed.isCompact ( isClosed_closure ) );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
  have h_integral : ∫ x, ‖u x‖ * ‖v x‖ ∂AddCircle.haarAddCircle ≤ Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    convert integral_norm_mul_le_L2 hu hv using 1;
  rw [ Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( ∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle ), Real.sqrt_nonneg ( ∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle ), Real.mul_self_sqrt ( show 0 ≤ ∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ), Real.mul_self_sqrt ( show 0 ≤ ∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ]

theorem L2nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ) → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    L2nrm (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, L2nrm (f i) := by
  induction' s using Finset.induction_on with a s ha notMem ih;
  · -- The L2 norm of the zero function is zero.
    simp [L2nrm];
  · convert le_trans _ ( add_le_add_left ( notMem fun i hi => hf i ( Finset.mem_insert_of_mem hi ) ) _ ) using 1;
    rw [ Finset.sum_insert ha, add_comm ];
    convert L2nrm_add_le _ _ using 2;
    · exact funext fun x => by rw [ Finset.sum_insert ha, add_comm ] ;
    · exact continuous_finset_sum _ fun i hi => hf i ( Finset.mem_insert_of_mem hi );
    · exact hf a ( Finset.mem_insert_self _ _ )

/-
For a co-analytic trig polynomial, `∫ φ² = (∫ φ)²`.
-/
theorem integral_sq_trigPolyNeg {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    (∫ x, (φ x) ^ 2 ∂(@AddCircle.haarAddCircle 1 _))
      = (∫ x, φ x ∂(@AddCircle.haarAddCircle 1 _)) ^ 2 := by
  -- By definition of $TrigPolyNeg$, we know that $\varphi(x) = \sum_{a \in s} c_a e^{2\pi i a x}$ for some finite set $s$ of integers $a \leq 0$ and some coefficients $c_a \in \mathbb{C}$.
  obtain ⟨s, c, hs, hc⟩ := h;
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∫ x, (∑ a ∈ s, c a * fourier a x) ^ 2 ∂(@AddCircle.haarAddCircle 1 _) = ∑ a ∈ s, ∑ b ∈ s, c a * c b * ∫ x, fourier (a + b) x ∂(@AddCircle.haarAddCircle 1 _) := by
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, ← integral_const_mul];
    rw [ MeasureTheory.integral_finset_sum ];
    · refine' Finset.sum_congr rfl fun i hi => _;
      rw [ MeasureTheory.integral_finset_sum ];
      · simp +decide only [fourier_add, mul_assoc];
      · exact fun j hj => Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
          rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq, Filter.eventually_inf_principal ] );
    · intro a ha; apply_rules [ Continuous.integrable_of_hasCompactSupport ];
      · fun_prop;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq, Filter.Eventually ];
  -- Evaluate the integral $\int_{\mathbb{T}} e^{2\pi i (a+b) x} \, dx$.
  have h_integral : ∀ a b : ℤ, ∫ x, fourier (a + b) x ∂(@AddCircle.haarAddCircle 1 _) = if a + b = 0 then 1 else 0 := by
    exact fun a b => integral_fourier (a + b);
  simp_all +decide [ ← sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  rw [ MeasureTheory.integral_finset_sum ];
  · rw [ sq, Finset.sum_mul ];
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, h_integral ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    have := h_integral x 0; have := h_integral y 0; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
    grind;
  · exact fun a ha => integrable_fourier_smul a ( c a )

/-
Pointwise: `|exp(-z) - 1| ≤ |z|` when `Re z ≥ 0`.
-/
theorem norm_exp_neg_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) : ‖Complex.exp (-z) - 1‖ ≤ ‖z‖ := by
  -- By the fundamental theorem of calculus, we have $\int_0^1 -z e^{-tz} dt = e^{-z} - 1$.
  have h_ftc : ∫ t in (0 : ℝ)..1, -z * Complex.exp (-(t : ℂ) * z) = Complex.exp (-z) - 1 := by
    have := @integral_exp_mul_complex 0 1;
    by_cases h : z = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_comm ];
    have := @this ( -z ) ; simp_all +decide [ mul_comm ];
  rw [ ← h_ftc, intervalIntegral.integral_of_le zero_le_one ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
  norm_num [ Complex.norm_exp ];
  exact le_trans ( MeasureTheory.setIntegral_mono_on ( by exact Continuous.integrableOn_Ioc ( by continuity ) ) ( by exact Continuous.integrableOn_Ioc ( by continuity ) ) measurableSet_Ioc fun x hx => mul_le_of_le_one_right ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by nlinarith [ hx.1, hx.2 ] ) ) ( by norm_num )

/-
Pointwise: `|exp(-z)| ≤ 1` when `Re z ≥ 0`.
-/
theorem norm_exp_neg_le_one {z : ℂ} (hz : 0 ≤ z.re) : ‖Complex.exp (-z)‖ ≤ 1 := by
  norm_num [ Complex.norm_exp, hz ]

/-
`L²` form of Lemma 1(b).
-/
theorem L2nrm_exp_neg_sub_one_le {φ : AddCircle (1 : ℝ) → ℂ} (hφ : Continuous φ)
    (hre : ∀ x, 0 ≤ (φ x).re) :
    L2nrm (fun x => Complex.exp (-φ x) - 1) ≤ L2nrm φ := by
  refine' Real.sqrt_le_sqrt <| MeasureTheory.integral_mono_of_nonneg _ _ _;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
      rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ] );
  · filter_upwards [ ] with x using pow_le_pow_left₀ ( norm_nonneg _ ) ( norm_exp_neg_sub_one_le ( hre x ) ) 2

/-
If `φ` is a co-analytic trig polynomial whose mean `∫ φ` is real, then its `L²` norm is at most
`√2` times the `L²` norm of its real part.
-/
theorem L2nrm_le_sqrt2_re {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ)
    (hint : (∫ x, φ x ∂(@AddCircle.haarAddCircle 1 _)).im = 0) :
    L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => (((φ x).re : ℝ) : ℂ)) := by
  have h_sq_le_sqrt2_sq : (∫ x, ‖φ x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _)) ≤ 2 * (∫ x, ‖((φ x).re : ℂ)‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _)) := by
    -- Pointwise identity: for `z : ℂ`, `‖z‖^2 = 2 * (z.re)^2 - (z^2).re`.
    have h_pointwise : ∀ x, ‖φ x‖ ^ 2 = 2 * (φ x).re ^ 2 - (φ x ^ 2).re := by
      norm_num [ Complex.normSq, Complex.sq_norm ] ; intros ; ring;
      simpa [ sq ] using by ring;
    -- Substitute the pointwise identity into the integral.
    suffices h_integral : ∫ x, (2 * (φ x).re ^ 2 - (φ x ^ 2).re) ∂(@AddCircle.haarAddCircle 1 _) ≤ 2 * ∫ x, (φ x).re ^ 2 ∂(@AddCircle.haarAddCircle 1 _) by
      aesop;
    rw [ MeasureTheory.integral_sub ];
    · rw [ MeasureTheory.integral_const_mul ] ; norm_num [ integral_sq_trigPolyNeg hφ ] ; ring_nf ;
      have h_integral_sq : ∫ x, (φ x ^ 2).re ∂(@AddCircle.haarAddCircle 1 _) = (∫ x, φ x ^ 2 ∂(@AddCircle.haarAddCircle 1 _)).re := by
        convert ( integral_re ( hφ.continuous.pow 2 |> Continuous.integrable_of_hasCompactSupport <| ?_ ) );
        · infer_instance;
        · rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ];
      rw [ h_integral_sq, integral_sq_trigPolyNeg hφ ] ; norm_num [ Complex.ext_iff, sq ] at * ; nlinarith;
    · exact Continuous.integrable_of_hasCompactSupport ( by exact Continuous.mul continuous_const <| by exact Continuous.pow ( by exact Complex.continuous_re.comp <| TrigPolyNeg.continuous hφ ) _ ) <| by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · exact Complex.continuous_re.comp ( hφ.continuous.pow 2 );
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  convert Real.sqrt_le_sqrt h_sq_le_sqrt2_sq using 1 ; ring! ; norm_num [ Real.sqrt_sq, L2nrm ] ; ring!;

/-
**Co-analytic completion.** Given any complex trigonometric polynomial `p = ∑ c a • fourier a`,
there is a co-analytic trig polynomial `φ` with the same real part and `L²` norm at most `√2` times
that of `Re p`.
-/
theorem exists_completion (s : Finset ℤ) (c : ℤ → ℂ) :
    ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧
      (∀ x, (φ x).re = (∑ a ∈ s, c a * fourier a x).re) ∧
      L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re : ℝ) : ℂ)) := by
  refine' ⟨ fun x => ∑ a ∈ s, ( if a < 0 then c a * fourier a x else if a = 0 then ( c a |> Complex.re ) * fourier 0 x else ( starRingEnd ℂ ( c a ) ) * fourier ( -a ) x ), _, _, _ ⟩;
  · refine' TrigPolyNeg.sum s _ _;
    intro i hi; split_ifs <;> simp_all +decide [ TrigPolyNeg.smul, TrigPolyNeg.fourier_neg ] ;
    · exact TrigPolyNeg.smul _ ( TrigPolyNeg.fourier_neg ( by linarith ) );
    · exact TrigPolyNeg.const _;
    · refine' ⟨ { -i }, fun _ => ( starRingEnd ℂ ) ( c i ), _, _ ⟩ <;> simp +decide [ *, fourier ];
  · simp +zetaDelta at *;
    intro x; rw [ ← Finset.sum_sub_distrib ] ; congr; ext i; split_ifs <;> simp_all +decide [ Complex.ext_iff ] ;
  · convert L2nrm_le_sqrt2_re _ _ using 1;
    · congr! 2;
      ext x; simp +decide [ Complex.exp_re, Complex.exp_im, fourier ] ;
      rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun i hi => _ ; split_ifs <;> simp_all +decide [ Complex.ext_iff ] ;
    · refine' TrigPolyNeg.sum s _ _;
      intro i hi; split_ifs <;> simp_all +decide [ TrigPolyNeg.smul, TrigPolyNeg.fourier_neg ] ;
      · exact TrigPolyNeg.smul _ ( TrigPolyNeg.fourier_neg ( by linarith ) );
      · exact TrigPolyNeg.const _;
      · refine' ⟨ { -i }, fun _ => ( starRingEnd ℂ ) ( c i ), _, _ ⟩ <;> simp +decide [ *, fourier ];
    · rw [ MeasureTheory.integral_finset_sum ];
      · -- Evaluate the integral of each term individually.
        have h_integral : ∀ a ∈ s, ∫ x, (if a < 0 then c a * fourier a x else if a = 0 then (c a).re * fourier 0 x else (starRingEnd ℂ (c a)) * fourier (-a) x) ∂(@AddCircle.haarAddCircle 1 _) = if a < 0 then 0 else if a = 0 then (c a).re else 0 := by
          intro a ha; split_ifs <;> simp_all +decide [ MeasureTheory.integral_const_mul, integral_fourier ] ;
          · exact Or.inr ( by simpa using integral_fourier a |> fun h => h.trans ( if_neg ( by linarith ) ) );
          · -- Since $a \neq 0$, we have $\int_{\mathbb{T}} \overline{e^{2\pi i a x}} \, dx = 0$.
            have h_int_zero : ∫ x : AddCircle (1 : ℝ), (starRingEnd ℂ) (fourier a x) ∂(@AddCircle.haarAddCircle 1 _) = 0 := by
              convert integral_fourier ( -a ) using 1 ; aesop;
              aesop;
            aesop;
        rw [ Finset.sum_congr rfl h_integral ] ; norm_cast;
      · intro i hi; split_ifs <;> [ exact integrable_fourier_smul _ _; exact integrable_fourier_smul _ _; exact integrable_fourier_smul _ _ ] ;

/-
**Stone–Weierstrass approximation by trigonometric polynomials.** Every continuous function on
the circle is uniformly approximable by finite linear combinations of the `fourier` monomials.
-/
theorem exists_trigPoly_approx (G : AddCircle (1 : ℝ) → ℂ) (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ x, ‖(∑ a ∈ s, c a * fourier a x) - G x‖ < ε := by
  obtain ⟨y, hy⟩ : ∃ y : C(AddCircle (1 : ℝ), ℂ), y ∈ Submodule.span ℂ (Set.range fourier) ∧ (dist y ⟨G, hG⟩) < ε := by
    have h_closure : (Submodule.span ℂ (Set.range (fun a : ℤ => fourier a : ℤ → C(AddCircle (1 : ℝ), ℂ)))).topologicalClosure = ⊤ := by
      convert span_fourier_closure_eq_top;
      exact ⟨ by norm_num ⟩;
    rw [ SetLike.ext_iff ] at h_closure;
    specialize h_closure ⟨ G, hG ⟩;
    simpa [ dist_comm ] using Metric.mem_closure_iff.mp ( h_closure.mpr trivial ) ε hε;
  obtain ⟨l, hl⟩ : ∃ l : ℤ →₀ ℂ, y = ∑ a ∈ l.support, l a • fourier a := by
    rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hy ; tauto;
  use l.support, fun a => l a;
  simp_all +decide [ dist_eq_norm, ContinuousMap.norm_lt_iff ]

/-
**The co-analytic majorant.** For every continuous real `g` and every `ε > 0`, there is a
co-analytic trig polynomial `φ` whose real part dominates `g`, with `L²` norm controlled by that
of `g`.
-/
theorem exists_majorant {g : AddCircle (1 : ℝ) → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧ (∀ x, g x ≤ (φ x).re) ∧
      L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => ((g x : ℝ) : ℂ)) + ε := by
  set ε' : ℝ := ε / (Real.sqrt 2 + 1) with hε';
  have h_approx : ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ x, ‖(∑ a ∈ s, c a * fourier a x) - (fun x => ((g x : ℝ) : ℂ)) x‖ < ε' := by
    apply exists_trigPoly_approx;
    · exact Complex.continuous_ofReal.comp hg;
    · positivity;
  obtain ⟨ s, c, h ⟩ := h_approx; obtain ⟨ φ₀, hφ₀₁, hφ₀₂, hφ₀₃ ⟩ := exists_completion s c; use fun x => φ₀ x + ( ε' : ℂ ) ; refine' ⟨ _, _, _ ⟩ <;> norm_num [ hφ₀₁ ] ;
  · exact TrigPolyNeg.add hφ₀₁ ( TrigPolyNeg.const _ );
  · intro x; specialize h x; norm_num [ Complex.normSq, Complex.norm_def ] at h;
    rw [ Real.sqrt_lt' ( by positivity ) ] at h;
    simp_all +decide [ Complex.ext_iff, Finset.sum_add_distrib ];
    nlinarith [ show 0 ≤ ε / ( Real.sqrt 2 + 1 ) by positivity ];
  · -- Apply the triangle inequality to the L2 norm.
    have h_triangle : L2nrm (fun x => φ₀ x + (ε' : ℂ)) ≤ L2nrm φ₀ + L2nrm (fun _ => (ε' : ℂ)) := by
      convert L2nrm_add_le ( TrigPolyNeg.continuous hφ₀₁ ) continuous_const using 1;
    -- Apply the triangle inequality to the L2 norm of the real part.
    have h_triangle_real : L2nrm (fun x => ((∑ a ∈ s, c a * fourier a x).re : ℂ)) ≤ L2nrm (fun x => ((g x : ℝ) : ℂ)) + L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re - g x) : ℂ)) := by
      convert L2nrm_add_le _ _ using 2 <;> norm_num [ hg ];
      · exact Complex.continuous_ofReal.comp hg;
      · fun_prop (disch := norm_num);
    -- Apply the bound on the L2 norm of the difference.
    have h_diff : L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re - g x) : ℂ)) ≤ ε' := by
      apply L2nrm_le_sup;
      · positivity;
      · intro x; specialize h x; norm_cast at *; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
        exact le_trans ( Real.abs_le_sqrt <| by nlinarith ) h.le;
    -- Apply the bound on the L2 norm of the constant function.
    have h_const : L2nrm (fun _ => (ε' : ℂ)) = ε' := by
      unfold L2nrm; norm_num [ hε'.symm ] ; ring;
      rw [ Real.sqrt_sq ( by positivity ) ];
    nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ε ( show ( Real.sqrt 2 + 1 ) ≠ 0 by positivity ) ]

end Littlewood

end

-- ============================================================
-- Construction
-- ============================================================

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Complex

noncomputable section

namespace Littlewood

/-- The recursively-defined dual function `F_m` of McGehee–Pigno–Smith:
`F₀ = α f₀`, `F_{m+1} = F_m · exp(-h_{m+1}) + α f_{m+1}`. -/
noncomputable def Frec (α : ℂ) (f h : ℕ → AddCircle (1 : ℝ) → ℂ) : ℕ → AddCircle (1 : ℝ) → ℂ
  | 0 => fun x => α * f 0 x
  | (m + 1) => fun x => Frec α f h m x * Complex.exp (- h (m + 1) x) + α * f (m + 1) x

/-- The cumulative exponential factor `exp(-∑_{i < l ≤ m} h_l)`. -/
noncomputable def prodexp (h : ℕ → AddCircle (1 : ℝ) → ℂ) (i m : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => Complex.exp (- ∑ l ∈ Finset.Ioc i m, h l x)

theorem prodexp_self (h : ℕ → AddCircle (1 : ℝ) → ℂ) (m : ℕ) (x) : prodexp h m m x = 1 := by
  -- By definition of `prodexp`, we have `prodexp h m m x = Complex.exp (- ∑ l ∈ Finset.Ioc m m, h l x)`.
  simp [prodexp]

theorem prodexp_succ (h : ℕ → AddCircle (1 : ℝ) → ℂ) {i m : ℕ} (him : i ≤ m) (x) :
    prodexp h i (m + 1) x = prodexp h i m x * Complex.exp (- h (m + 1) x) := by
  unfold prodexp; simp +decide [ *, Finset.sum_Ioc_succ_top, Complex.exp_add ] ;
  ring

theorem prodexp_continuous {h : ℕ → AddCircle (1 : ℝ) → ℂ} (hh : ∀ l, Continuous (h l))
    (i m : ℕ) : Continuous (prodexp h i m) := by
  exact Complex.continuous_exp.comp ( Continuous.neg ( continuous_finset_sum _ fun l hl => hh l ) )

theorem prodexp_coAnalytic {h : ℕ → AddCircle (1 : ℝ) → ℂ} (hh : ∀ l, TrigPolyNeg (h l))
    (i m : ℕ) : CoAnalytic (prodexp h i m) := by
  -- The function ψ is the negative of a sum of trigonometric polynomials, hence it's a trigonometric polynomial itself. We can use the fact that the sum of trigonometric polynomials is a trigonometric polynomial.
  have h_psi : TrigPolyNeg (fun x => -∑ l ∈ Finset.Ioc i m, h l x) := by
    convert TrigPolyNeg.neg ( TrigPolyNeg.sum ( Finset.Ioc i m ) ( fun l => h l ) fun l hl => hh l ) using 1;
  convert TrigPolyNeg.coAnalytic_exp h_psi using 1

/-
Closed form for `Frec`.
-/
theorem Frec_closed (α : ℂ) (f h : ℕ → AddCircle (1 : ℝ) → ℂ) (m : ℕ) (x) :
    Frec α f h m x = α * ∑ i ∈ Finset.range (m + 1), f i x * prodexp h i m x := by
  induction' m with m ih generalizing x;
  · simp +decide [ Frec, prodexp ];
  · simp_all +decide [ Finset.sum_range_succ, Frec ];
    simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, prodexp ];
    exact Finset.sum_congr rfl fun i hi => by rw [ ← Complex.exp_add ] ; rw [ Finset.sum_Ioc_succ_top ( by linarith [ Finset.mem_range.mp hi ] ) ] ; ring;

/-
Calculus inequality `exp(-t/4) + t/5 ≤ 1` for `t ∈ [0,1]`.
-/
theorem exp_calc_ineq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp (-(t / 4)) + t / 5 ≤ 1 := by
  rw [ Real.exp_neg ];
  rw [ inv_eq_one_div, div_add_div, div_le_iff₀ ] <;> try positivity;
  nlinarith [ Real.add_one_le_exp ( t / 4 ), Real.exp_pos ( t / 4 ), sq_nonneg ( t - 1 ) ]

/-
The sup-norm bound `‖F_m‖∞ ≤ 1`.
-/
theorem Frec_norm_le {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hf : ∀ j x, ‖f j x‖ ≤ 1) (hh : ∀ j x, (1 / 4 : ℝ) * ‖f j x‖ ≤ (h j x).re) (m : ℕ) (x) :
    ‖Frec (1 / 5 : ℂ) f h m x‖ ≤ 1 := by
  induction' m with m ih generalizing x;
  · exact le_trans ( by simpa [ Frec ] using mul_le_mul_of_nonneg_left ( hf 0 x ) ( by norm_num ) ) ( by norm_num );
  · convert le_trans ( norm_add_le ( Frec ( 1 / 5 ) f h m x * Complex.exp ( -h ( m + 1 ) x ) ) ( ( 1 / 5 : ℂ ) * f ( m + 1 ) x ) ) _ using 1 ; norm_num [ Complex.norm_exp ];
    refine' le_trans ( add_le_add ( mul_le_of_le_one_left ( Real.exp_nonneg _ ) ( by linarith [ ih x ] ) ) le_rfl ) _;
    have := exp_calc_ineq ( show 0 ≤ ‖f ( m + 1 ) x‖ by positivity ) ( show ‖f ( m + 1 ) x‖ ≤ 1 by exact hf _ _ );
    linarith [ Real.exp_le_exp.mpr ( show - ( h ( m + 1 ) x |> Complex.re ) ≤ - ( ‖f ( m + 1 ) x‖ / 4 ) by linarith [ hh ( m + 1 ) x ] ) ]

/-
Fourier coefficient of `Frec` in expanded (telescoped) form.
-/
theorem Frec_coeff (α : ℂ) {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l)) (m : ℕ) (n : ℤ) :
    fourierCoeff (Frec α f h m) n
      = α * ∑ i ∈ Finset.range (m + 1),
          fourierCoeff (fun x => f i x * prodexp h i m x) n := by
  -- Expand Frec α f h m using Frec_closed (note that Frec_closed needs pointwise equality).
  have h_Frec_closed : ∀ x, (Frec α f h m x) = α * ∑ i ∈ Finset.range (m + 1), (f i x) * (prodexp h i m x) := by
    exact fun x => Frec_closed α f h m x;
  rw [ show Frec α f h m = _ from funext h_Frec_closed ];
  convert congr_arg _ ( MeasureTheory.integral_finset_sum _ fun i hi => ?_ ) using 1;
  · unfold fourierCoeff; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; rw [ Finset.mul_sum _ _ _ ] ;
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · exact Continuous.smul ( by continuity ) ( by exact Continuous.mul ( hfc i ) ( prodexp_continuous hhc i m ) );
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ]

/-
Geometric tail bound `∑_{i < l ≤ m} (1/2)^l ≤ (1/2)^i`.
-/
theorem geom_sum_half_Ioc (i m : ℕ) :
    ∑ l ∈ Finset.Ioc i m, (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ i := by
  by_cases vim : m ≤ i;
  · aesop;
  · induction' m with m ih <;> norm_num [ pow_succ', Finset.sum_Ioc_succ_top ] at *;
    cases vim.eq_or_lt <;> simp_all +decide [ Finset.sum_Ioc_succ_top ];
    · gcongr <;> norm_num;
    · have h_sum : ∑ k ∈ Finset.Ioc i m, (2 ^ k : ℝ)⁻¹ = (2 ^ i : ℝ)⁻¹ - (2 ^ m : ℝ)⁻¹ := by
        exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by rw [ Finset.sum_Ioc_succ_top ( by linarith ), pow_succ' ] ; norm_num ; linarith ) m vim;
      norm_num [ pow_succ' ] at * ; linarith [ inv_pos.mpr ( pow_pos ( zero_lt_two' ℝ ) m ) ]

/-
`L²` bound on `exp(-∑ h) - 1`.
-/
theorem L2nrm_prodexp_sub_one_le {h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hhc : ∀ l, Continuous (h l)) (hhre : ∀ l x, 0 ≤ (h l x).re)
    (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l) (i m : ℕ) :
    L2nrm (fun x => prodexp h i m x - 1) ≤ B * (1 / 2 : ℝ) ^ i := by
  -- Apply `L2nrm_exp_neg_sub_one_le` to the function `φ = fun x => ∑ l ∈ Finset.Ioc i m, h l x`.
  have hφ_cont : Continuous (fun x => ∑ l ∈ Finset.Ioc i m, h l x) := by
    exact continuous_finset_sum _ fun _ _ => hhc _
  have hφ_re : ∀ x, 0 ≤ (∑ l ∈ Finset.Ioc i m, h l x).re := by
    exact fun x => by simpa using Finset.sum_nonneg fun l hl => hhre l x;
  have hL2 : L2nrm (fun x => Complex.exp (- ∑ l ∈ Finset.Ioc i m, h l x) - 1) ≤ L2nrm (fun x => ∑ l ∈ Finset.Ioc i m, h l x) := by
    convert L2nrm_exp_neg_sub_one_le hφ_cont hφ_re using 1;
  refine le_trans ?_ ( hL2.trans ?_ );
  · unfold prodexp; norm_num;
  · refine le_trans ( L2nrm_sum_le ( Finset.Ioc i m ) ( fun l => h l ) ( fun l hl => hhc l ) ) ?_;
    refine le_trans ( Finset.sum_le_sum fun l hl => hh2 l ) ?_;
    rw [ ← Finset.mul_sum _ _ _ ] ; exact mul_le_mul_of_nonneg_left ( geom_sum_half_Ioc i m ) hB;

/-
`Frec` is continuous when the data are.
-/
theorem Frec_continuous (α : ℂ) {f h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l)) (m : ℕ) :
    Continuous (Frec α f h m) := by
  induction' m with m ih;
  · exact continuous_const.mul ( hfc 0 );
  · exact Continuous.add ( ih.mul ( Complex.continuous_exp.comp ( Continuous.neg ( hhc _ ) ) ) ) ( continuous_const.mul ( hfc _ ) )

/-
Geometric tail bound `∑_{j ≤ i ≤ m} (1/4)^i ≤ (4/3)(1/4)^j`.
-/
theorem geom_sum_quarter_Ico (j m : ℕ) :
    ∑ i ∈ Finset.Ico j (m + 1), (1 / 4 : ℝ) ^ i ≤ (4 / 3) * (1 / 4 : ℝ) ^ j := by
  by_cases h : j ≤ m;
  · rw [ geom_sum_Ico ] <;> ring <;> norm_num;
    linarith;
  · rw [ Finset.Ico_eq_empty ] <;> norm_num ; linarith

/-
**The per-element coefficient estimate.**
-/
theorem re_coeff_ge {f h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ} (hB : 0 ≤ B) (m : ℕ)
    (hfc : ∀ i, Continuous (f i)) (hhc : ∀ l, Continuous (h l))
    (hhre : ∀ l x, 0 ≤ (h l x).re)
    (hf2 : ∀ i, L2nrm (f i) ≤ (1 / 2 : ℝ) ^ i) (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l)
    {j : ℕ} (hj : j ≤ m) {n : ℤ}
    (hmain : (∑ i ∈ Finset.range (m + 1), fourierCoeff (f i) n) = (((1 / 4 : ℝ) ^ j : ℝ) : ℂ))
    (hvanish : ∀ i, i < j → fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n = 0) :
    (1 / 5 : ℝ) * ((1 / 4 : ℝ) ^ j - B * (4 / 3) * (1 / 4 : ℝ) ^ j)
      ≤ (fourierCoeff (Frec (1 / 5 : ℂ) f h m) n).re := by
  -- Let `D := ∑ i ∈ Finset.range (m+1), fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n`.
  set D := ∑ i ∈ Finset.range (m + 1), fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n;
  have hD : (fourierCoeff (Frec (1 / 5) f h m) n).re = (1 / 5 : ℝ) * (D.re + (1 / 4 : ℝ) ^ j) := by
    convert congr_arg Complex.re ( Frec_coeff ( 1 / 5 ) hfc hhc m n ) using 1;
    rw [ Finset.sum_congr rfl fun i hi => show fourierCoeff ( fun x => f i x * prodexp h i m x ) n = fourierCoeff ( fun x => f i x * ( prodexp h i m x - 1 ) ) n + fourierCoeff ( f i ) n from ?_ ];
    · norm_num [ Finset.sum_add_distrib, hmain ];
      norm_num [ D ];
      norm_num [ show ( 1 / 4 : ℂ ) ^ j = ( 1 / 4 : ℝ ) ^ j by norm_num [ Complex.ext_iff, pow_succ ] ];
      norm_cast;
    · unfold fourierCoeff; simp +decide [ mul_sub ] ; ring;
      rw [ MeasureTheory.integral_add ];
      · rw [ MeasureTheory.integral_neg ] ; ring;
      · refine' Continuous.integrable_of_hasCompactSupport _ _;
        · fun_prop;
        · rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ];
      · refine' Continuous.integrable_of_hasCompactSupport _ _;
        · refine' Continuous.mul _ _;
          · refine' Continuous.mul _ ( hfc i );
            exact Complex.continuous_conj.comp ( by continuity );
          · exact prodexp_continuous hhc i m;
        · rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq, Filter.eventually_inf_principal ];
  -- By definition of $D$, we know that $‖D‖ ≤ ∑ i ∈ Finset.Ico j (m+1), B * (1/4)^i$.
  have hD_norm : ‖D‖ ≤ ∑ i ∈ Finset.Ico j (m + 1), B * (1 / 4 : ℝ) ^ i := by
    have hD_bound : ∀ i ∈ Finset.Ico j (m + 1), ‖fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n‖ ≤ B * (1 / 4 : ℝ) ^ i := by
      intros i hi
      have h_bound : ‖fourierCoeff (fun x => f i x * (prodexp h i m x - 1)) n‖ ≤ L2nrm (f i) * L2nrm (fun x => prodexp h i m x - 1) := by
        apply_rules [ norm_fourierCoeff_mul_le ];
        exact Continuous.sub ( prodexp_continuous hhc i m ) continuous_const;
      refine le_trans h_bound ?_;
      refine' le_trans ( mul_le_mul ( hf2 i ) ( L2nrm_prodexp_sub_one_le hB hhc hhre hh2 i m ) ( by exact L2nrm_nonneg _ ) ( by positivity ) ) _ ; ring ; norm_num;
      norm_num [ pow_mul' ];
    convert norm_sum_le _ _ |> le_trans <| Finset.sum_le_sum hD_bound using 1;
    rw [ Finset.sum_Ico_eq_sub _ ( by linarith ) ];
    rw [ Finset.sum_congr rfl fun i hi => hvanish i ( Finset.mem_range.mp hi ), Finset.sum_const_zero, sub_zero ];
  -- By definition of $D$, we know that $‖D‖ ≤ B * (4 / 3) * (1 / 4) ^ j$.
  have hD_norm_le : ‖D‖ ≤ B * (4 / 3) * (1 / 4 : ℝ) ^ j := by
    exact hD_norm.trans ( by rw [ ← Finset.mul_sum _ _ _ ] ; exact le_trans ( mul_le_mul_of_nonneg_left ( geom_sum_quarter_Ico j m ) hB ) ( by ring_nf; norm_num ) );
  linarith [ abs_le.mp ( Complex.abs_re_le_norm D ) ]

/-! ### Per-set construction -/

/-- Block index of the `k`-th smallest element (0-indexed rank `k`): block `j` consists of the
ranks `k` with `4^j ≤ 3k+1 < 4^{j+1}`, so `|block j| = 4^j`. -/
def blk (k : ℕ) : ℕ := Nat.log 4 (3 * k + 1)

theorem blk_mono {a b : ℕ} (h : a ≤ b) : blk a ≤ blk b := by
  exact Nat.log_mono_right ( by linarith )

theorem pow_blk_le (k : ℕ) : (4 : ℕ) ^ blk k ≤ 3 * k + 1 := by
  -- By definition of `blk`, we know that `4 ^ blk k ≤ 3 * k + 1`.
  apply Nat.pow_log_le_self 4 (by linarith)

theorem card_block_le (N j : ℕ) :
    (Finset.univ.filter (fun k : Fin N => blk (k : ℕ) = j)).card ≤ 4 ^ j := by
  refine' le_trans _ ( show 4 ^ j ≥ ( Finset.Ico ( ( 4 ^ j - 1 ) / 3 ) ( ( 4 ^ j - 1 ) / 3 + 4 ^ j ) |> Finset.card ) from _ );
  · -- Let's choose any $k$ such that $blk k = j$.
    have h_filter : ∀ k : Fin N, blk k = j → (k : ℕ) ∈ Finset.Ico ((4^j - 1) / 3) ((4^j - 1) / 3 + 4^j) := by
      intro k hk
      have h_bounds : 4^j ≤ 3 * k.val + 1 ∧ 3 * k.val + 1 < 4^(j+1) := by
        exact ⟨ hk ▸ pow_blk_le _, hk ▸ Nat.lt_pow_succ_log_self ( by decide ) _ ⟩;
      have h_div : 3 ∣ 4^j - 1 := by
        exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div ( 4 ^ j ) 3 ] ; norm_num [ Nat.pow_mod ] );
      grind;
    convert Finset.card_le_card ( show Finset.image ( fun k : Fin N => ( k : ℕ ) ) ( Finset.filter ( fun k : Fin N => blk k = j ) Finset.univ ) ⊆ Finset.Ico ( ( 4 ^ j - 1 ) / 3 ) ( ( 4 ^ j - 1 ) / 3 + 4 ^ j ) from Finset.image_subset_iff.mpr fun k hk => h_filter k <| Finset.mem_filter.mp hk |>.2 ) using 1;
    rw [ Finset.card_image_of_injective _ fun a b h => by simpa [ Fin.ext_iff ] using h ];
  · norm_num

/-- The set of elements of `A` in block `j` (image of the rank-block under the increasing
enumeration). -/
def blockSet (A : Finset ℤ) (j : ℕ) : Finset ℤ :=
  (Finset.univ.filter (fun k : Fin A.card => blk (k : ℕ) = j)).image (A.orderEmbOfFin rfl)

/-- The trigonometric polynomial `f_j = ∑_{a ∈ S_j} 4^{-j} fourier a`. -/
def fpoly (A : Finset ℤ) (j : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ a ∈ blockSet A j, ((1 / 4 : ℂ) ^ j) * fourier a x

theorem fpoly_continuous (A : Finset ℤ) (j : ℕ) : Continuous (fpoly A j) := by
  exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) ( by continuity )

theorem card_blockSet_le (A : Finset ℤ) (j : ℕ) : (blockSet A j).card ≤ 4 ^ j := by
  exact Finset.card_image_le.trans ( card_block_le _ _ )

theorem fpoly_norm_le (A : Finset ℤ) (j : ℕ) (x) : ‖fpoly A j x‖ ≤ 1 := by
  have h_norm : ‖fpoly A j x‖ ≤ (blockSet A j).card * (1 / 4 : ℝ) ^ j := by
    convert norm_sum_le _ _ using 2;
    norm_num [ fourier_apply ];
  exact h_norm.trans ( by have := card_blockSet_le A j; exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr this ) ( by positivity ) ) ( by norm_num [ ← mul_pow ] ) )

theorem fpoly_L2_le (A : Finset ℤ) (j : ℕ) : L2nrm (fpoly A j) ≤ (1 / 2 : ℝ) ^ j := by
  refine' Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩;
  -- By parseval_trigpoly, the integral of the squared norm is equal to the sum of the squared norms of the coefficients.
  have h_parseval : ∫ x, ‖fpoly A j x‖ ^ 2 ∂AddCircle.haarAddCircle = ∑ a ∈ blockSet A j, ‖((1 / 4 : ℂ) ^ j)‖ ^ 2 := by
    convert parseval_trigpoly ( blockSet A j ) ( fun _ => ( 1 / 4 : ℂ ) ^ j ) using 1;
  norm_num [ h_parseval ];
  exact le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( card_blockSet_le A j ) ) ( by positivity ) ) ( by norm_num [ sq, ← mul_pow ] )

theorem fpoly_coeff (A : Finset ℤ) (j : ℕ) (n : ℤ) :
    fourierCoeff (fpoly A j) n = if n ∈ blockSet A j then (1 / 4 : ℂ) ^ j else 0 := by
  unfold fourierCoeff;
  unfold fpoly; simp +decide [ mul_assoc, Finset.mul_sum _ _ _, MeasureTheory.integral_const_mul ] ;
  rw [ MeasureTheory.integral_finset_sum ];
  · -- Evaluate the integral $\int_{\mathbb{T}} \overline{e^{2\pi i n x}} e^{2\pi i i x} \, dx$.
    have h_integral : ∀ n i : ℤ, ∫ x : AddCircle (1 : ℝ), (starRingEnd ℂ) (fourier n x) * (fourier i x) ∂AddCircle.haarAddCircle = if n = i then 1 else 0 := by
      intro n i; split_ifs with h; simp_all +decide [ ← mul_assoc, ← Complex.exp_add ] ;
      · simp +decide [ mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
      · convert integral_fourier ( i - n ) using 1;
        · simp +decide [ fourier, sub_eq_add_neg, Complex.exp_add ];
          ac_rfl;
        · rw [ if_neg ( sub_ne_zero_of_ne <| Ne.symm h ) ];
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul ];
  · intro i hi; exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
      rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ] ) ;

/-
An element `e k` lies in `blockSet A i` iff `i` is its block index.
-/
theorem mem_blockSet_iff (A : Finset ℤ) (k : Fin A.card) (i : ℕ) :
    (A.orderEmbOfFin rfl) k ∈ blockSet A i ↔ blk (k : ℕ) = i := by
  unfold blockSet; aesop;

/-
Elements of earlier blocks are strictly smaller.
-/
theorem blockSet_lt (A : Finset ℤ) (k : Fin A.card) {i : ℕ} (hik : i < blk (k : ℕ))
    {a : ℤ} (ha : a ∈ blockSet A i) : a < (A.orderEmbOfFin rfl) k := by
  obtain ⟨ k', hk', rfl ⟩ := Finset.mem_image.mp ha;
  contrapose! hik; simp_all +decide [ Finset.mem_filter ] ;
  exact hk'.symm ▸ blk_mono hik

/-
For a co-analytic `G`, `G - 1` has vanishing positive Fourier coefficients.
-/
theorem coAnalytic_sub_one {G : AddCircle (1 : ℝ) → ℂ} (hGc : Continuous G) (hG : CoAnalytic G)
    {p : ℤ} (hp : 0 < p) : fourierCoeff (fun x => G x - 1) p = 0 := by
  unfold fourierCoeff at *; simp_all +decide [ MeasureTheory.integral_sub ] ;
  convert hG p hp using 1 ; ring;
  convert integral_add _ _ using 1;
  · rw [ MeasureTheory.integral_neg, show ( ∫ a : AddCircle 1, ( starRingEnd ℂ ) ↑ ( p • a ).toCircle ∂AddCircle.haarAddCircle ) = 0 from ?_ ] ; norm_num [ fourierCoeff ];
    convert integral_fourier ( -p ) using 1 ; norm_num [ hp.ne' ];
    lia;
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop (disch := norm_num);
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ];
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop (disch := norm_num);
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq, Filter.Eventually ]

/-
Vanishing of the off-diagonal coefficient contributions.
-/
theorem fpoly_mul_prodexp_sub_one_vanish (A : Finset ℤ) {h : ℕ → AddCircle (1 : ℝ) → ℂ}
    (hhc : ∀ l, Continuous (h l)) (hhT : ∀ l, TrigPolyNeg (h l)) (i m : ℕ) (k : Fin A.card)
    (hik : i < blk (k : ℕ)) :
    fourierCoeff (fun x => fpoly A i x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = 0 := by
  -- By additivity and `fourierCoeff.const_mul` (each summand `fun x => (1/4:ℂ)^i * (fourier a x * Gm1 x)` is integrable: continuous on the compact probability space),
  have h_fourier_sum : fourierCoeff (fun x => (fpoly A i x) * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = ∑ a ∈ blockSet A i, (1 / 4 : ℂ) ^ i * fourierCoeff (fun x => fourier a x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) := by
    unfold fourierCoeff;
    simp +decide [ fpoly, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, ← MeasureTheory.integral_const_mul ];
    rw [ ← MeasureTheory.integral_finset_sum ];
    · simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
    · intro a ha; apply_rules [ Continuous.integrable_of_hasCompactSupport ] ;
      · apply_rules [ Continuous.mul, Continuous.sub, continuous_const, continuous_id ];
        · fun_prop;
        · fun_prop (disch := norm_num);
        · exact prodexp_continuous hhc i m;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  -- By the shift formula `fourierCoeff_fourier_mul` (with `Gm1` continuous), `fourierCoeff (fun x => fourier a x * Gm1 x) n = fourierCoeff Gm1 (n - a)`.
  have h_shift : ∀ a ∈ blockSet A i, fourierCoeff (fun x => fourier a x * (prodexp h i m x - 1)) ((A.orderEmbOfFin rfl) k) = fourierCoeff (fun x => prodexp h i m x - 1) ((A.orderEmbOfFin rfl) k - a) := by
    intros a ha
    exact fourierCoeff_fourier_mul a ((A.orderEmbOfFin rfl) k);
  -- By `coAnalytic_sub_one`, `fourierCoeff Gm1 p = 0` for all `p > 0`.
  have h_coAnalytic : ∀ p : ℤ, 0 < p → fourierCoeff (fun x => prodexp h i m x - 1) p = 0 := by
    apply coAnalytic_sub_one;
    · exact prodexp_continuous hhc i m;
    · exact prodexp_coAnalytic hhT i m;
  exact h_fourier_sum.trans ( Finset.sum_eq_zero fun a ha => by rw [ h_shift a ha, h_coAnalytic _ ( sub_pos.mpr ( blockSet_lt A k hik ha ) ) ] ; ring )

/-
Sum over `A` rewritten as a sum over ranks.
-/
theorem sum_eq_sum_enum (A : Finset ℤ) (g : ℤ → ℝ) :
    ∑ n ∈ A, g n = ∑ k : Fin A.card, g ((A.orderEmbOfFin rfl) k) := by
  convert Finset.sum_image ?_;
  · exact Eq.symm (Finset.image_orderEmbOfFin_univ A rfl);
  · exact fun x _ y _ hxy => by simpa [ Fin.ext_iff ] using hxy;

/-
**Lower bound for the coefficient sum** of the constructed function.
-/
theorem construction_sum_bound (A : Finset ℤ) {h : ℕ → AddCircle (1 : ℝ) → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hBle : 4 * B ≤ 3)
    (hhc : ∀ l, Continuous (h l)) (hhT : ∀ l, TrigPolyNeg (h l))
    (hhre : ∀ l x, 0 ≤ (h l x).re) (hh2 : ∀ l, L2nrm (h l) ≤ B * (1 / 2 : ℝ) ^ l) :
    (1 - 4 * B / 3) / 15 * harmonic A.card
      ≤ ∑ n ∈ A, (fourierCoeff (Frec (1 / 5 : ℂ) (fpoly A) h (blk (A.card - 1))) n).re := by
  rw [ sum_eq_sum_enum, harmonic ];
  -- By `Finset.sum_le_sum`, it suffices to prove for each `k : Fin N`:
  suffices h_per_k : ∀ k : Fin A.card, ((1 - 4 * B / 3) / 15) * (1 / (k + 1 : ℝ)) ≤ (fourierCoeff (Frec (1 / 5) (fpoly A) h (blk (A.card - 1))) ((A.orderEmbOfFin rfl) k)).re by
    simpa only [ Finset.mul_sum _ _ _, Finset.sum_range ] using Finset.sum_le_sum fun i _ => h_per_k i;
  intro k;
  have := @re_coeff_ge ( fpoly A ) h B hB ( blk ( A.card - 1 ) );
  refine' le_trans _ ( this ( fun i => fpoly_continuous A i ) hhc hhre ( fun i => fpoly_L2_le A i ) hh2 ( show blk ( k : ℕ ) ≤ blk ( A.card - 1 ) from _ ) _ _ );
  · -- By simplifying, we can see that the inequality holds.
    have h_simp : (1 / 4 : ℝ) ^ blk (k : ℕ) ≥ 1 / (3 * (k + 1)) := by
      have := pow_blk_le k;
      rw [ one_div, inv_pow ];
      rw [ ge_iff_le, inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast at * <;> linarith [ pow_pos ( by decide : 0 < 4 ) ( blk k ) ];
    norm_num at * ; nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ) ];
  · exact blk_mono ( Nat.le_sub_one_of_lt k.2 );
  · rw [ Finset.sum_eq_single ( blk k ) ] <;> norm_num [ fpoly_coeff ];
    · exact fun h => False.elim <| h <| mem_blockSet_iff A k _ |>.2 rfl;
    · intro b hb hb'; rw [ mem_blockSet_iff ] ; aesop;
    · exact fun h => False.elim <| h.not_ge <| blk_mono <| Nat.le_sub_one_of_lt <| Fin.is_lt k;
  · exact fun i hi => fpoly_mul_prodexp_sub_one_vanish A hhc hhT i ( blk ( A.card - 1 ) ) k hi

/-
**The dual construction** (refactored with an existential absolute constant).
-/
theorem exists_good_F : ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ,
    ∃ F : AddCircle (1 : ℝ) → ℂ, Continuous F ∧ (∀ x, ‖F x‖ ≤ 1) ∧
      c * harmonic A.card ≤ ∑ n ∈ A, (fourierCoeff F n).re := by
  refine' ⟨ ( 2 - Real.sqrt 2 ) / 45, by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ], _ ⟩;
  intro A
  obtain ⟨h, hhT, hhc, hhre, hh2⟩ : ∃ h : ℕ → AddCircle (1 : ℝ) → ℂ,
    (∀ l, TrigPolyNeg (h l)) ∧
    (∀ l, Continuous (h l)) ∧
    (∀ l x, 0 ≤ (h l x).re) ∧
    (∀ l, L2nrm (h l) ≤ ((Real.sqrt 2 + 1) / 4) * (1 / 2 : ℝ) ^ l) ∧
    (∀ l x, (1 / 4 : ℝ) * ‖fpoly A l x‖ ≤ (h l x).re) := by
      have h_majorant : ∀ l, ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧ (∀ x, (1 / 4 : ℝ) * ‖fpoly A l x‖ ≤ (φ x).re) ∧ L2nrm φ ≤ (Real.sqrt 2 + 1) / 4 * (1 / 2 : ℝ) ^ l := by
        intro l
        set g : AddCircle (1 : ℝ) → ℝ := fun x => (1 / 4 : ℝ) * ‖fpoly A l x‖
        have hg_cont : Continuous g := by
          exact Continuous.mul continuous_const <| Continuous.norm <| fpoly_continuous A l
        have hg_nonneg : ∀ x, 0 ≤ g x := by
          exact fun x => mul_nonneg ( by norm_num ) ( norm_nonneg _ )
        have hg_L2 : L2nrm (fun x => ((g x : ℝ) : ℂ)) ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ l := by
          have hg_L2 : L2nrm (fun x => ((g x : ℝ) : ℂ)) = (1 / 4 : ℝ) * L2nrm (fpoly A l) := by
            unfold L2nrm;
            norm_num [ g, mul_pow, MeasureTheory.integral_const_mul ];
          exact hg_L2.symm ▸ mul_le_mul_of_nonneg_left ( fpoly_L2_le A l ) ( by norm_num );
        have := exists_majorant hg_cont ( show 0 < ( 1 / 4 : ℝ ) * ( 1 / 2 ) ^ l by positivity );
        exact this.imp fun φ hφ => ⟨ hφ.1, hφ.2.1, by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) l ] ⟩;
      choose φ hφ₁ hφ₂ hφ₃ using h_majorant;
      exact ⟨ φ, hφ₁, fun l => TrigPolyNeg.continuous ( hφ₁ l ), fun l x => le_trans ( by positivity ) ( hφ₂ l x ), hφ₃, hφ₂ ⟩;
  refine' ⟨ Frec ( 1 / 5 : ℂ ) ( fpoly A ) h ( blk ( A.card - 1 ) ), _, _, _ ⟩;
  · exact Frec_continuous _ ( fun l => fpoly_continuous _ _ ) hhc _;
  · apply Frec_norm_le;
    · grind +suggestions;
    · exact hh2.2;
  · convert construction_sum_bound A ( show 0 ≤ ( Real.sqrt 2 + 1 ) / 4 by positivity ) ( show 4 * ( ( Real.sqrt 2 + 1 ) / 4 ) ≤ 3 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ) hhc hhT hhre hh2.1 using 1;
    ring

end Littlewood

end

-- ============================================================
-- Main
-- ============================================================

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

/-!
# The Littlewood conjecture on the `L¹` norm of exponential sums

This file proves the Littlewood conjecture, following the outline of
McGehee, Pigno and Smith, *Hardy's inequality and the `L¹` norm of exponential sums*
(Annals of Mathematics, 1981).

The main result `littlewood_L1_lower_bound` states that there is an absolute constant
`K > 0` such that for every finite set `A ⊆ ℤ` of size `N`,
`∫₀¹ |∑_{n ∈ A} e(nθ)| dθ ≥ K · log N`, where `e(x) = exp(2πix)`.

The analytic core (the McGehee–Pigno–Smith dual construction) is developed in
`RequestProject.Hardy` and `RequestProject.Construction`; here it is exposed through
`Littlewood.exists_good_F`.  The helper definitions `harmonic` and `log_le_harmonic`
also live in `RequestProject.Hardy`.
-/

namespace Littlewood

/-- The exponential sum kernel function on the circle group `AddCircle 1`. -/
def expSum (A : Finset ℤ) : AddCircle (1 : ℝ) → ℂ := fun x => ∑ n ∈ A, fourier n x

/-- The user's interval integral equals the integral over the circle group. -/
theorem intervalIntegral_eq_circleIntegral (A : Finset ℤ) :
    (∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * π * I * n * θ)‖)
      = ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  convert ( AddCircle.intervalIntegral_preimage ( 1 : ℝ ) ( 0 : ℝ ) ( fun x => ‖expSum A x‖ ) ) using 1 ; norm_num [ expSum ];
  unfold AddCircle.haarAddCircle; norm_num [ MeasureTheory.MeasureSpace.volume ] ;

/-
The pairing inequality: for any measurable `F` bounded by `1`, the sum over `A` of the
real parts of the Fourier coefficients of `F` is at most the `L¹` norm of `expSum A`.
This is Parseval together with `|∫ F · conj g| ≤ ‖F‖_∞ · ‖g‖₁`.
-/
theorem pairing_le (A : Finset ℤ) (F : AddCircle (1 : ℝ) → ℂ)
    (hFmeas : Measurable F) (hFbound : ∀ x, ‖F x‖ ≤ 1) :
    (∑ n ∈ A, (fourierCoeff F n).re)
      ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  -- Let `μ = AddCircle.haarAddCircle (T=1)`, a probability measure (`IsProbabilityMeasure`).
  set μ := @AddCircle.haarAddCircle (1 : ℝ);
  -- Let `g = expSum A = fun x => ∑ n ∈ A, fourier n x`, which is continuous (finite sum of continuous `fourier n`), hence integrable and bounded.
  set g : AddCircle (1 : ℝ) → ℂ := fun x => expSum A x;
  have hg_cont : Continuous g := by
    exact continuous_finset_sum _ fun _ _ => Continuous.comp ( by continuity ) ( by continuity );
  have hg_integrable : MeasureTheory.Integrable g μ := by
    apply_rules [ Continuous.integrable_of_hasCompactSupport ];
    grind +suggestions;
  have hg_norm : ∀ x, ‖g x‖ ≤ A.card := by
    intro x; exact le_trans ( norm_sum_le _ _ ) ( by simp )
  -- Let `J := ∫ x, F x * (starRingEnd ℂ) (g x) ∂μ`.
  set J := ∫ x, F x * starRingEnd ℂ (g x) ∂μ;
  have hJ : J = ∑ n ∈ A, fourierCoeff F n := by
    -- Using the linearity of the integral, we can interchange the sum and the integral.
    have hJ_sum : J = ∑ n ∈ A, ∫ x, F x * starRingEnd ℂ (fourier n x) ∂μ := by
      rw [ ← MeasureTheory.integral_finset_sum ];
      · simp +zetaDelta at *;
        simp +decide [ expSum, Finset.mul_sum _ _ _ ];
      · intro n hn; refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => 1;
        · norm_num +zetaDelta at *;
        · exact hFmeas.aestronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) );
        · simp_all +decide [ fourier ];
    convert hJ_sum using 2;
    unfold fourierCoeff; simp +decide [ mul_comm ] ;
    rfl;
  have hJ_re : (∑ n ∈ A, (fourierCoeff F n).re) = J.re := by
    rw [ hJ, Complex.re_sum ];
  have hJ_norm : ‖J‖ ≤ ∫ x, ‖F x‖ * ‖g x‖ ∂μ := by
    convert MeasureTheory.norm_integral_le_integral_norm _ using 1 ; norm_num [ Complex.norm_exp ];
  have hJ_le : J.re ≤ ∫ x, ‖g x‖ ∂μ := by
    refine' le_trans ( Complex.re_le_norm J ) ( hJ_norm.trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) );
    · exact Filter.Eventually.of_forall fun x => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ );
    · exact hg_integrable.norm;
    · filter_upwards [ ] using fun x => mul_le_of_le_one_left ( norm_nonneg _ ) ( hFbound x );
  linarith;

/-- **The generalized Hardy inequality (special case).** There is an absolute constant `C > 0`
such that for any finite set `A`, the harmonic sum of length `|A|` is bounded by `C` times the
`L¹` norm of the exponential sum `expSum A`.  This combines the dual construction
`exists_good_F` with the elementary `pairing_le`. -/
theorem hardy_key :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      harmonic A.card ≤ C * ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  obtain ⟨c, hc, hF⟩ := exists_good_F
  refine ⟨1 / c, by positivity, ?_⟩
  intro A
  obtain ⟨F, hFcont, hFbound, hFcoeff⟩ := hF A
  have hpair := pairing_le A F hFcont.measurable hFbound
  have hch : c * harmonic A.card
      ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := le_trans hFcoeff hpair
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  linarith [hch]

/-- **Littlewood's conjecture.** There is an absolute constant `K > 0` such that for every
finite set `A ⊆ ℤ` of cardinality `N`,
`∫₀¹ |∑_{n ∈ A} e(nθ)| dθ ≥ K · log N`, where `e(x) = exp(2πix)`. -/
theorem littlewood_L1_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : Finset ℤ,
      K * Real.log A.card
        ≤ ∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * π * I * n * θ)‖ := by
  obtain ⟨c, hc, hF⟩ := exists_good_F
  refine ⟨c, hc, ?_⟩
  intro A
  rw [intervalIntegral_eq_circleIntegral A]
  obtain ⟨F, hFcont, hFbound, hFcoeff⟩ := hF A
  have hpair := pairing_le A F hFcont.measurable hFbound
  have hlog := log_le_harmonic A.card
  calc c * Real.log A.card
      ≤ c * harmonic A.card := by
        exact mul_le_mul_of_nonneg_left hlog (le_of_lt hc)
    _ ≤ ∑ n ∈ A, (fourierCoeff F n).re := hFcoeff
    _ ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := hpair

end Littlewood

end

/-- **Erdős Problem 512 (Littlewood's conjecture).** Proved independently by Konyagin
[Ko81] and McGehee–Pigno–Smith [MPS81]: there is an absolute constant `K > 0` such
that for every finite set `A ⊆ ℤ` of size `N`,
`∫₀¹ |∑_{n ∈ A} e(nθ)| dθ ≥ K · log N`, where `e(x) = exp(2πix)`. -/
theorem erdos_512 :
    ∃ K : ℝ, 0 < K ∧ ∀ A : Finset ℤ,
      K * Real.log A.card
        ≤ ∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * Real.pi * Complex.I * n * θ)‖ :=
  Littlewood.littlewood_L1_lower_bound

#print axioms erdos_512
-- 'Erdos512.erdos_512' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos512
