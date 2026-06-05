import Mathlib

namespace Mertens

open scoped BigOperators Topology
open Nat Real Finset Filter MeasureTheory ArithmeticFunction


noncomputable section

/-! ### Step 1: Von Mangoldt sum identity

Using ∑_{d|n} Λ(d) = log n, we get:
∑_{n=1}^{N} Λ(n) · ⌊N/n⌋ = ∑_{n=1}^{N} log n = log(N!)
-/

/-
∑_{n=1}^{N} log n = log(N!).
-/
lemma sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) = Real.log (N ! : ℝ) := by
  erw [ Finset.sum_Ico_eq_sum_range ];
  rw [ ← Real.log_prod ] <;> norm_cast <;> norm_num [ add_comm, Finset.prod_range_succ' ]

/-
∑_{n=1}^{N} Λ(n) · ⌊N/n⌋ = log(N!).
This follows from ∑_{d|n} Λ(d) = log n by swapping the order of summation.
-/
lemma sum_vonMangoldt_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = Real.log (N ! : ℝ) := by
  -- By interchanging the order of summation, we get:
  have h_interchange : ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, (Λ d : ℝ)) = ∑ d ∈ Finset.Icc 1 N, (Λ d : ℝ) * (N / d : ℕ) := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (Λ d : ℝ) = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (Λ d : ℝ) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +contextual [ Finset.sum_ite, Nat.mem_divisors ];
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 N ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.divisor_le hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop;
    simp_all +decide [ Finset.sum_ite ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( N / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ] ; aesop;
    ext y; simp [Finset.mem_image];
    exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self N x ] ⟩, by simp +decide ⟩ ⟩;
  simp_all +decide [ ArithmeticFunction.vonMangoldt_sum ];
  exact h_interchange ▸ sum_log_eq_log_factorial N

/-! ### Step 2: Stirling-type bound for log(N!)

We need log(N!) = N log N - N + O(log N).
-/

/-
log(N!) ≤ N · log N. This is a weak upper bound.
-/
lemma log_factorial_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N ! : ℝ) ≤ N * Real.log N := by
  rw [ ← Real.log_pow ] ; gcongr ; norm_cast ; induction hN <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
  exact le_trans ‹_› ( by gcongr ; linarith )

/-
log(N!) ≥ N · log N - N. This follows from Stirling or direct estimation.
-/
lemma log_factorial_ge (N : ℕ) (hN : 1 ≤ N) :
    N * Real.log N - N ≤ Real.log (N ! : ℝ) := by
  induction hN <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_mul ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) / ( Nat.cast:ℕ →ℝ ) ‹_› );
  rw [ Real.log_div ] at this <;> first | positivity | ring_nf at * ; nlinarith [ mul_inv_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ] ;

/-! ### Step 3: ∑ Λ(n)/n = log N + O(1) -/

/-
∑_{n=1}^{N} Λ(n)/n is bounded between log N - C and log N + C.
-/
lemma vonMangoldt_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 →
      |∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n - Real.log N| ≤ C := by
  use Real.log 4 + 5;
  intro N hN
  have h_sum : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = Real.log (N ! : ℝ) := by
    convert sum_vonMangoldt_floor N using 1;
  -- Write ⌊N/n⌋ = N/n - frac(N/n) where 0 ≤ frac < 1. Then:
  have h_frac : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = N * ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n - ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (Int.fract (N / n : ℝ)) := by
    rw [ Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Int.fract ] ; ring;
    rw [ show ⌊ ( N : ℝ ) * ( x : ℝ ) ⁻¹⌋ = N / x from Int.floor_eq_iff.mpr ⟨ by rw [ ← div_eq_mul_inv ] ; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hx |>.1 ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N x ], by rw [ ← div_eq_mul_inv ] ; rw [ div_lt_iff₀ ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hx |>.1 ) ] ; norm_cast; linarith [ Nat.div_add_mod N x, Nat.mod_lt N ( Finset.mem_Icc.mp hx |>.1 ) ] ⟩ ];
    norm_cast;
  -- Now: 0 ≤ ∑ Λ(n) · frac(N/n) ≤ ∑ Λ(n) = ψ(N) ≤ (log 4 + 4) · N (by Chebyshev.psi_le_const_mul_self)
  have h_frac_bound : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (Int.fract (N / n : ℝ)) ≤ (Real.log 4 + 4) * N := by
    have h_frac_bound : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) ≤ (Real.log 4 + 4) * N := by
      convert Chebyshev.psi_le_const_mul_self ( show 0 ≤ ( N : ℝ ) by positivity ) using 1;
      refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> aesop;
    exact le_trans ( Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Int.fract_lt_one _ |> le_of_lt ) ) h_frac_bound;
  -- Now: log(N!) is between N·log(N) - N and N·log(N) (by log_factorial_ge and log_factorial_le)
  have h_log_factorial : N * Real.log N - N ≤ Real.log (N ! : ℝ) ∧ Real.log (N ! : ℝ) ≤ N * Real.log N := by
    exact ⟨ log_factorial_ge N ( by linarith ), log_factorial_le N ( by linarith ) ⟩;
  rw [ abs_le ];
  constructor <;> nlinarith [ show ( N : ℝ ) ≥ 2 by norm_cast, show ( ∑ n ∈ Finset.Icc 1 N, Λ n * Int.fract ( N / n : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => mul_nonneg ( by exact_mod_cast vonMangoldt_nonneg ) ( Int.fract_nonneg _ ) ]

/-! ### Step 4: ∑_{p≤N} log(p)/p = log N + O(1)

Subtracting the prime power contributions. -/

/-
The prime power contribution ∑_{p^k, k≥2} log(p)/p^k converges.
-/
lemma prime_power_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ,
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 2 (Nat.log p N),
          Real.log p / (p : ℝ) ^ k ≤ C := by
  -- We bound the inner sum using the formula $\sum_{k=2}^{\infty} \frac{\log p}{p^k} = \frac{\log p}{p^2} \frac{1}{1 - 1/p} = \frac{\log p}{p(p-1)}$.
  have h_inner_bound : ∀ p : ℕ, p.Prime → ∑' k : ℕ, Real.log p / (p ^ (k + 2) : ℝ) ≤ Real.log p / (p * (p - 1) : ℝ) := by
    intro p hp
    have h_inner_sum : ∑' k : ℕ, (Real.log p) / (p ^ (k + 2) : ℝ) = (Real.log p) / (p ^ 2 : ℝ) * (1 / (1 - 1 / (p : ℝ))) := by
      ring_nf;
      rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( mod_cast hp.one_lt ) ) ];
    convert h_inner_sum.le using 1 ; ring;
    grind;
  -- We sum the inner bounds over all primes $p$.
  have h_sum_inner_bound : Summable (fun p : ℕ => if p.Prime then Real.log p / (p * (p - 1) : ℝ) else 0) := by
    -- We compare our sum to a convergent p-series.
    have h_compare : ∀ p : ℕ, p ≥ 2 → (if p.Prime then Real.log p / (p * (p - 1) : ℝ) else 0) ≤ 2 * (Real.log p / p ^ 2 : ℝ) := by
      intro p hp; split_ifs <;> ring_nf <;> norm_num;
      · field_simp;
        rw [ div_le_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by norm_cast, Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      · positivity;
    -- We know that $\sum_{p} \frac{\log p}{p^2}$ converges.
    have h_sum_log_p : Summable (fun p : ℕ => Real.log p / p ^ 2 : ℕ → ℝ) := by
      -- We can compare our series with the convergent p-series $\sum_{n=1}^{\infty} \frac{1}{n^{3/2}}$.
      have h_compare : ∀ n : ℕ, n ≥ 2 → (Real.log n / n ^ 2 : ℝ) ≤ 1 / n ^ (3 / 2 : ℝ) := by
        intro n hn
        have : Real.log n ≤ Real.sqrt n := by
          have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt n / 2 );
          rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
          have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
        rw [ div_le_div_iff₀ ] <;> try positivity;
        exact le_trans ( mul_le_mul_of_nonneg_right this <| by positivity ) <| by rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add <| by positivity ] ; norm_num;
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => if hn : n < 2 then by interval_cases n <;> norm_num else h_compare n ( le_of_not_gt hn ) ) ( Real.summable_one_div_nat_rpow.2 ( by norm_num ) );
    rw [ ← summable_nat_add_iff 2 ] at *;
    exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> first | positivity | exact div_nonneg ( Real.log_nonneg <| by norm_cast; linarith ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) ( fun n => h_compare _ <| by linarith ) <| h_sum_log_p.mul_left 2;
  -- We use the bound on the inner sum to bound the outer sum.
  have h_outer_bound : ∀ N : ℕ, ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.Icc 2 (Nat.log p N), Real.log p / (p ^ k : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), Real.log p / (p * (p - 1) : ℝ) := by
    intro N
    apply Finset.sum_le_sum
    intro p hp
    have h_inner_bound_p : ∑ k ∈ Finset.Icc 2 (Nat.log p N), Real.log p / (p ^ k : ℝ) ≤ ∑' k : ℕ, Real.log p / (p ^ (k + 2) : ℝ) := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      simpa only [ add_comm ] using Summable.sum_le_tsum ( Finset.range ( Nat.log p N + 1 - 2 ) ) ( fun _ _ => by positivity ) ( by exact Summable.mul_left _ <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ) |> Summable.comp_injective <| by intro a; aesop );
    exact le_trans h_inner_bound_p <| h_inner_bound p <| Finset.mem_filter.mp hp |>.2;
  exact ⟨ _, fun N => le_trans ( h_outer_bound N ) ( by simpa [ Finset.sum_filter ] using Summable.sum_le_tsum ( Finset.range ( N + 1 ) ) ( fun _ _ => by split_ifs <;> first | positivity | exact div_nonneg ( Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by assumption ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.2 <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by assumption ) h_sum_inner_bound ) ⟩

/-
∑_{p≤N} log(p)/p = log N + O(1).
-/
lemma prime_log_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 →
      |∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log p / (p : ℝ) - Real.log N| ≤ C := by
  -- By definition of von Mangoldt function, we have $\sum_{n=1}^{N} \Lambda(n)/n = \sum_{p \leq N, p \text{ prime}} \sum_{k=1}^{\log_p(N)} \frac{\log(p)}{p^k}$.
  have h_vonMangoldt_sum : ∀ N : ℕ, N ≥ 2 → (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n) = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 1 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) := by
    intro N hN;
    have h_sum_prime_powers : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p N), (vonMangoldt (p^k) : ℝ) / p^k := by
      have h_sum_prime_powers : Finset.filter (fun n => vonMangoldt n ≠ 0) (Finset.Icc 1 N) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (N + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p N))) := by
        ext n
        simp [vonMangoldt];
        constructor <;> intro hn
        all_goals generalize_proofs at *;
        · obtain ⟨ p, k, hp, hk, rfl ⟩ := hn.2.1;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hn.1.2 ⟩, rfl ⟩;
        · rcases hn with ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ ; refine' ⟨ ⟨ Nat.one_le_pow _ _ hp₂.pos, Nat.pow_le_of_le_log ( by linarith [ hp₂.pos ] ) hk₂ ⟩, _, _, _, _ ⟩ <;> norm_cast <;> simp_all +decide [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
          · exact hp₂.isPrimePow.pow ( by linarith );
          · exact Nat.ne_of_gt ( Nat.minFac_pos _ );
          · lia
      generalize_proofs at *; (
      have h_sum_prime_powers : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n = ∑ n ∈ Finset.filter (fun n => vonMangoldt n ≠ 0) (Finset.Icc 1 N), (vonMangoldt n : ℝ) / n := by
        rw [ Finset.sum_filter_of_ne ] ; aesop
      generalize_proofs at *; (
      rw [ h_sum_prime_powers, ‹ { n ∈ Icc 1 N | Λ n ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;))
    generalize_proofs at *; (
    convert h_sum_prime_powers using 3;
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.Prime.pow_minFac ] ; aesop;
      linarith [ Finset.mem_Icc.mp ‹_› ];
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] ));
  obtain ⟨ C₁, hC₁ ⟩ := vonMangoldt_reciprocal_bounded
  obtain ⟨ C₂, hC₂ ⟩ := prime_power_reciprocal_bounded
  use C₁ + C₂
  intro N hN
  have h_sum_eq : (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 1 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (Real.log p) / (p : ℝ)) + (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 2 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) := by
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
    intro p hp; erw [ Finset.Icc_eq_cons_Ioc ( Nat.succ_le_of_lt ( Nat.log_pos ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ) ), Finset.sum_cons ] ; aesop;
  have := hC₁ N hN; rw [ abs_le ] at *; constructor <;> linarith [ hC₂ N, h_vonMangoldt_sum N hN, show ( 0 : ℝ ) ≤ ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( N + 1 ) ), ∑ k ∈ Finset.Icc 2 ( Nat.log p N ), Real.log p / p ^ k from Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg <| mod_cast Nat.Prime.pos <| by aesop ) <| pow_nonneg ( Nat.cast_nonneg _ ) _ ] ;

/-! ### Step 5: Abel summation gives convergence of ∑ 1/p - log log N

The key idea: from the bounded estimate |∑ log(p)/p - log N| ≤ C,
Abel summation converts this into convergence of ∑ 1/p - log log N.

Abel summation: ∑_{p≤N} 1/p = S(N)/log N + ∫₂^N S(t)/(t·log²t) dt
where S(t) = ∑_{p≤t} log(p)/p = log t + O(1).

The integral ∫ (log t + O(1))/(t·log²t) dt = ∫ 1/(t·log t) dt + ∫ O(1)/(t·log²t) dt
= log log t + convergent integral.

So ∑ 1/p - log log N → some constant M.
-/

/-
The prime reciprocal sum ∑_{p≤N} 1/p - log(log N) converges to some limit.
This follows from Abel summation applied to the bounded estimate
|∑ log(p)/p - log N| ≤ C.
-/
set_option maxHeartbeats 800000 in
lemma prime_reciprocal_sum_convergence :
    ∃ M : ℝ, Tendsto
      (fun N : ℕ => ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        1 / (p : ℝ) - Real.log (Real.log N))
      atTop (𝓝 M) := by
  obtain ⟨ C, hC ⟩ := prime_log_reciprocal_bounded;
  -- Let $S(N) = \sum_{p \leq N} \frac{\log p}{p}$. Then $S(N) = \log N + e(N)$ where $|e(N)| \leq C$.
  set S : ℕ → ℝ := fun N => ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (Real.log p) / (p : ℝ)
  have hS : ∀ N : ℕ, N ≥ 2 → |S N - Real.log N| ≤ C := by
    assumption;
  -- By Abel's summation formula, we have $\sum_{p \leq N} \frac{1}{p} = \frac{S(N)}{\log N} + \int_{2}^{N} \frac{S(t)}{t \log^2 t} dt$.
  have h_abel : ∀ N : ℕ, N ≥ 2 → (∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (1 : ℝ) / p) = S N / Real.log N + ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) := by
    intro N hN
    have h_abel_step : ∀ n : ℕ, 2 ≤ n → (∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime), (1 : ℝ) / p) = S n / Real.log n + ∑ k ∈ Finset.Ico 2 n, S k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
      intro n hn;
      induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
      · norm_num [ Finset.sum_filter, Finset.sum_range_succ, S ];
        ring_nf; norm_num;
      · simp_all +decide [ Finset.sum_filter, Finset.sum_range_succ ];
        simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ Finset.sum_filter, Finset.sum_range_succ ];
        · field_simp;
          rw [ eq_comm, div_add', div_eq_iff ] <;> ring;
          · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.log_pos ( show ( 1 + ( ‹ℕ› : ℝ ) ) > 1 by norm_cast; linarith ) ), ne_of_gt ( Real.log_pos ( show ( ‹ℕ› : ℝ ) > 1 by norm_cast ) ) ] ; ring;
          · exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith;
          · exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith;
        · ring;
    -- The integral of $S(t)/(t \log^2 t)$ over $[k, k+1]$ is equal to $S(k) \cdot (1/\log k - 1/\log(k+1))$.
    have h_integral_step : ∀ k : ℕ, 2 ≤ k → ∫ t in (k : ℝ)..((k + 1) : ℝ), S (Nat.floor t) / (t * (Real.log t)^2) = S k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
      intro k hk; erw [ intervalIntegral.integral_of_le ( by norm_num ) ] ; erw [ MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; erw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ show ⌊x⌋₊ = k from Nat.floor_eq_iff ( by linarith [ hx.1 ] ) |>.2 ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ] ] ; norm_num;
      rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ] <;> norm_num;
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => -S k / Real.log x;
      · ring;
      · intro x hx; convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 from by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) using 1 ; ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ;
    induction hN <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
    rename_i k hk ih; rw [ h_abel_step _ ( by linarith ) ] ; simp_all +decide [ Finset.sum_Ico_succ_top ] ;
    rw [ ← h_integral_step k hk, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( Real.log t + C ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.add ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) continuousAt_const ) ( ContinuousAt.mul continuousAt_id ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) 2 ) ) ( ne_of_gt ( mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ) );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ );
        · have := hS ⌊x⌋₊ ( Nat.le_floor <| by norm_num; cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ; rw [ abs_le ] at this ; linarith [ Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| Nat.floor_le <| show 0 ≤ x by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ] ;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( ∑ p ∈ Finset.range ( k + 2 ), Real.log p / p ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ );
        · exact fun p hp => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ( Nat.floor_le_of_le ( by cases Set.mem_uIcc.mp hx <;> norm_num at * <;> linarith ) ) ) );
  -- We'll use the fact that $\int_{2}^{N} \frac{S(t)}{t \log^2 t} dt$ converges to a constant as $N \to \infty$.
  have h_integral : ∃ M : ℝ, Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t)) Filter.atTop (nhds M) := by
    -- We'll use the fact that $\int_{2}^{N} \frac{S(t) - \log t}{t \log^2 t} dt$ converges to a constant as $N \to \infty$.
    have h_integral : ∃ M : ℝ, Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) Filter.atTop (nhds M) := by
      -- We'll use the fact that $\int_{2}^{N} \frac{S(t) - \log t}{t \log^2 t} dt$ is absolutely convergent.
      have h_abs_conv : MeasureTheory.IntegrableOn (fun t : ℝ => |(S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)|) (Set.Ici 2) := by
        -- We'll use the fact that $|S(t) - \log t| \leq C$ for all $t \geq 2$.
        have h_bound : ∀ t : ℝ, 2 ≤ t → |(S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)| ≤ (C + 1) / (t * (Real.log t)^2) := by
          intros t ht
          have h_abs : |S (Nat.floor t) - Real.log t| ≤ C + 1 := by
            have := hS ⌊t⌋₊ ( Nat.le_floor <| mod_cast ht );
            rw [ abs_le ] at *;
            constructor <;> linarith [ show Real.log t ≤ Real.log ⌊t⌋₊ + 1 by rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) ] ; nlinarith [ Nat.lt_floor_add_one t, Real.add_one_le_exp 1, Real.log_le_sub_one_of_pos <| show 0 < ( ⌊t⌋₊ : ℝ ) by exact Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ], show Real.log ⌊t⌋₊ ≤ Real.log t by exact Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity ];
          rw [ abs_div, abs_of_nonneg ( by positivity : 0 ≤ t * Real.log t ^ 2 ) ] ; gcongr;
        -- We'll use the fact that $\int_{2}^{\infty} \frac{1}{t \log^2 t} dt$ converges.
        have h_integral_conv : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Ici 2) := by
          -- We can use the substitution $u = \log t$, then $du = \frac{1}{t} dt$.
          suffices h_subst : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u^2) (Set.Ici (Real.log 2)) by
            have h_subst : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Ici 2) := by
              have : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u^2) (Set.image Real.log (Set.Ici 2)) := by
                exact h_subst.mono_set <| Set.image_subset_iff.mpr fun x hx => Real.log_le_log ( by norm_num ) hx
              rw [ MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul ] at this;
              any_goals intro x hx; exact Real.hasDerivAt_log ( by linarith [ Set.mem_Ici.mp hx ] ) |> HasDerivAt.hasDerivWithinAt;
              · refine' this.congr_fun _ _;
                · intro x hx; simp +decide [ abs_of_nonneg ( inv_nonneg.mpr ( show 0 ≤ x by linarith [ Set.mem_Ici.mp hx ] ) ), mul_comm ] ;
                · norm_num;
              · norm_num;
              · exact fun x hx y hy hxy => Real.log_injOn_pos ( show 0 < x by linarith [ Set.mem_Ici.mp hx ] ) ( show 0 < y by linarith [ Set.mem_Ici.mp hy ] ) hxy;
            convert h_subst using 1;
          have h_integral_conv : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ici (Real.log 2)) := by
            rw [ integrableOn_Ici_iff_integrableOn_Ioi ] ; rw [ integrableOn_Ioi_rpow_iff ] <;> norm_num ; positivity;
          norm_cast at * ; aesop;
        refine' h_integral_conv.const_mul ( C + 1 ) |> fun h => h.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with t ht using by simpa [ div_eq_mul_inv ] using h_bound t ht;
      have h_abs_conv : MeasureTheory.IntegrableOn (fun t : ℝ => (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) (Set.Ici 2) := by
        refine' h_abs_conv.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with x hx using le_rfl;
      have h_abs_conv : Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) Filter.atTop (nhds (∫ t in Set.Ici 2, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2))) := by
        rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ];
        apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
        · exact h_abs_conv.mono_set <| Set.Ioi_subset_Ici_self;
        · exact tendsto_natCast_atTop_atTop;
      exact ⟨ _, h_abs_conv ⟩;
    convert h_integral using 4;
    grind +qlia;
  obtain ⟨ M, hM ⟩ := h_integral;
  have h_integral_split : ∀ N : ℕ, N ≥ 2 → ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t) = (∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2)) - (Real.log (Real.log N) - Real.log (Real.log 2)) := by
    intro N hN; rw [ intervalIntegral.integral_sub ] <;> norm_num;
    · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => Real.log ( Real.log x );
      · norm_cast;
      · intro x hx; convert HasDerivAt.log ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) using 1 ; ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) );
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( C + Real.log N ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ );
        · have := hS ⌊t⌋₊ ( Nat.le_floor <| by norm_num; cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
          linarith [ abs_le.mp this, Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) <| Nat.floor_le ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] : 0 ≤ t ) |> le_trans <| show ( t : ℝ ) ≤ N by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) );
  have h_limit : Filter.Tendsto (fun N : ℕ => S N / Real.log N + (Real.log (Real.log N) - Real.log (Real.log 2)) + (∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t)) - Real.log (Real.log N)) Filter.atTop (nhds (1 + M - Real.log (Real.log 2))) := by
    have h_limit : Filter.Tendsto (fun N : ℕ => S N / Real.log N) Filter.atTop (nhds 1) := by
      have h_limit : Filter.Tendsto (fun N : ℕ => (S N - Real.log N) / Real.log N) Filter.atTop (nhds 0) := by
        refine' squeeze_zero_norm' _ _;
        use fun N => C / Real.log N;
        · filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ] ; exact div_le_div_of_nonneg_right ( hS N hN ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ;
        · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      simpa using h_limit.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN using by rw [ sub_div, div_self <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hN ] ; ring );
    convert Filter.Tendsto.add ( Filter.Tendsto.add h_limit hM ) tendsto_const_nhds using 2 ; ring;
  exact ⟨ _, Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN; rw [ h_abel N hN, h_integral_split N hN ] ; ring ) h_limit ⟩

end


noncomputable section

/-! ### Helper lemmas -/

/-- The integral of log(u) * exp(-u) over (0, ∞) equals -γ (Euler-Mascheroni constant). -/
lemma gamma_integral :
    ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-u) =
    -Real.eulerMascheroniConstant := by
  convert ( HasDerivAt.deriv ( Real.hasDerivAt_Gamma_one ) ) using 1;
  have h_gamma_deriv : deriv Gamma 1 = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) := by
    have h_lim : Filter.Tendsto (fun s : ℝ => (Gamma s - Gamma 1) / (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
      have h_dominate : ∀ s ∈ Set.Ioo (1 : ℝ) 2, ∀ u ∈ Set.Ioi 0, abs ((u^(s-1) - 1) / (s - 1) * Real.exp (-u)) ≤ abs (Real.log u) * Real.exp (-u) * (u + 1) := by
        have h_mean_value : ∀ s ∈ Set.Ioo (1 : ℝ) 2, ∀ u ∈ Set.Ioi 0, ∃ c ∈ Set.Ioo 0 (s - 1), u^(s-1) - 1 = (s - 1) * Real.log u * u^c := by
          intro s hs u hu;
          have := exists_deriv_eq_slope ( f := fun x => u ^ x ) ( show 0 < s - 1 by linarith [ hs.1 ] );
          norm_num [ Real.rpow_def_of_pos hu, mul_comm ] at *;
          exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by norm_num ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
        intro s hs u hu; obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value s hs u hu; rw [ hc₂ ] ; simp +decide [ abs_mul, abs_div, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
        by_cases h : s - 1 = 0 <;> simp_all +decide [ ne_of_gt ];
        by_cases hu₁ : u ≤ 1;
        · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.le _ ) ] ; exact le_trans ( Real.rpow_le_one hu.le hu₁ hc₁.1.le ) ( by linarith ) ) ( by positivity );
        · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith ) ) ( by norm_num ) ) ( by positivity );
      have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u) * (u + 1)) (Set.Ioi 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u) * u) (Set.Ioi 0) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * abs (Real.log u)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.log u) (Set.Ioc 0 1) := by
                  exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                refine' h_integrable.norm.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.aestronglyMeasurable );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ mul_right_comm ] ; exact by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hx.1.le ) <| by positivity;
              have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioi 1) := by
                have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * u) (Set.Ioi 1) := by
                  have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u^2 * Real.exp (-u)) (Set.Ioi 1) := by
                    have h_gamma : ∫ u in Set.Ioi 0, u^2 * Real.exp (-u) = Real.Gamma 3 := by
                      rw [ Real.Gamma_eq_integral ( by norm_num ) ];
                      norm_cast ; ac_rfl;
                    exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                  exact h_integrable'.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                refine' h_integrable'.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ( Real.log_nonneg ( by linarith [ hu.out ] ) ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ;
              convert h_integrable.union h_integrable' using 1 ; norm_num;
            refine' h_integrable.norm.congr _;
            filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hu.out.le, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ;
          exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
        have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioi 0) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioc 0 1) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u)) (Set.Ioc 0 1) := by
              have h_integrable : ∫ u in Set.Ioc 0 1, abs (Real.log u) = 1 := by
                rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le ] <;> norm_num;
              exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
            refine' h_integrable.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hu.1.le ) <| abs_nonneg <| Real.log u;
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioi 1) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Set.Ioi 1) := by
              have := @integral_rpow_mul_exp_neg_rpow 1;
              specialize @this 1 ; norm_num at this;
              exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ( Set.Ioi_subset_Ioi zero_le_one );
            refine' h_integrable.mono' _ _;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.log_nonneg hu.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( by positivity ) ;
          convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun u : ℝ => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun u : ℝ => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioi 1 ) volume› using 1 ; norm_num;
        simp_all +decide [ mul_add ];
        exact MeasureTheory.Integrable.add ‹_› ‹_›;
      have h_dominated_convergence : Filter.Tendsto (fun s : ℝ => ∫ u in Set.Ioi 0, (u^(s-1) - 1) / (s - 1) * Real.exp (-u)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
        apply_rules [ MeasureTheory.tendsto_integral_filter_of_dominated_convergence ];
        · filter_upwards [ self_mem_nhdsWithin ] with s hs using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
        · filter_upwards [ Ioo_mem_nhdsGT one_lt_two ] with s hs using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun u hu => h_dominate s hs u hu;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
          have h_lim : Filter.Tendsto (fun s : ℝ => (u^(s-1) - 1) / (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log u)) := by
            have h_pointwise : HasDerivAt (fun s : ℝ => u^(s-1)) (Real.log u) 1 := by
              convert HasDerivAt.rpow ( hasDerivAt_const _ _ ) ( hasDerivAt_id 1 |> HasDerivAt.sub <| hasDerivAt_const _ _ ) _ using 1 <;> aesop;
            rw [ hasDerivAt_iff_tendsto_slope ] at h_pointwise;
            convert h_pointwise.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope_def_field ];
          exact h_lim.mul tendsto_const_nhds;
      refine' h_dominated_convergence.congr' _;
      filter_upwards [ Ioo_mem_nhdsGT one_lt_two ] with s hs;
      have h_split : ∫ u in Set.Ioi 0, (u^(s-1) - 1) * Real.exp (-u) = (∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u)) - (∫ u in Set.Ioi 0, Real.exp (-u)) := by
        rw [ ← MeasureTheory.integral_sub ] ; congr ; ext u ; ring;
        · have h_gamma : ∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u) = Real.Gamma s := by
            rw [ Real.Gamma_eq_integral ( by linarith [ hs.1 ] ) ] ; congr ; ext ; ring;
          exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; linarith [ Real.Gamma_pos_of_pos ( show 0 < s by linarith [ hs.1 ] ) ] );
        · exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
      simp_all +decide [ div_mul_eq_mul_div, MeasureTheory.integral_div ];
      rw [ Real.Gamma_eq_integral ( by linarith : 0 < s ) ];
      simp +decide [ mul_comm, integral_exp_Iic ]
    refine' tendsto_nhds_unique _ h_lim;
    have h_deriv : HasDerivAt Gamma (deriv Gamma 1) 1 := by
      exact DifferentiableAt.hasDerivAt ( Real.differentiableAt_Gamma fun m => by linarith );
    rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv;
    convert h_deriv.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope ];
  exact h_gamma_deriv.symm

/-- The integral of exp(-u) over (a, b] equals exp(-a) - exp(-b). -/
lemma integral_exp_neg_Ioc (a b : ℝ) (hab : a ≤ b) :
    ∫ u in Set.Ioc a b, Real.exp (-u) = Real.exp (-a) - Real.exp (-b) := by
  rw [ ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_neg ] ; norm_num

/-- The integral of |log u| over (0, δ] tends to 0 as δ → 0+. -/
lemma integral_abs_log_near_zero_tendsto :
    Tendsto (fun δ : ℝ => ∫ u in Set.Ioc 0 δ, |Real.log u|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_small_delta : ∀ δ > 0, δ ≤ 1 → ∫ u in Set.Ioc 0 δ, |Real.log u| = δ * (1 - Real.log δ) := by
    intro δ hδ_pos hδ_le_one
    have h_integral : ∫ u in Set.Ioc (0 : ℝ) δ, |Real.log u| = ∫ u in Set.Ioc (0 : ℝ) δ, -Real.log u := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonpos ( Real.log_nonpos hx.1.le ( hx.2.trans hδ_le_one ) ) ] ;
    rw [ h_integral, ← intervalIntegral.integral_of_le hδ_pos.le ];
    norm_num [ hδ_pos.le ] ; ring;
  have h_lim : Filter.Tendsto (fun δ : ℝ => δ * (1 - Real.log δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := Real.continuous_mul_log.tendsto 0;
    simpa [ mul_sub ] using Filter.Tendsto.mono_left ( Filter.tendsto_id.mul_const ( 1 : ℝ ) |> Filter.Tendsto.sub <| this ) nhdsWithin_le_nhds;
  exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT zero_lt_one ) fun x hx => by rw [ h_small_delta x hx.1 hx.2.le ] ) h_lim

/-- For n ≥ 2 and ε ∈ (0, 1], n^{-ε} - (n+1)^{-ε} ≤ ε/n. -/
lemma rpow_diff_le_eps_div (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε / n := by
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), deriv (fun x : ℝ => x ^ (-ε)) c = ((n + 1 : ℝ) ^ (-ε) - (n : ℝ) ^ (-ε)) / ((n + 1 : ℝ) - n) := by
    have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
    exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] );
  norm_num [ show c ≠ 0 by linarith [ hc.1.1 ] ] at hc;
  rw [ show ( -ε - 1 : ℝ ) = - ( 1 + ε ) by ring, Real.rpow_neg ( by linarith ) ] at hc;
  ring_nf at *;
  nlinarith [ inv_anti₀ ( by positivity ) ( show ( c : ℝ ) ^ ( 1 + ε ) ≥ n by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) hc.1.1.le ( by positivity ) ) |> le_trans <| Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( n :ℝ ) ≥ 2 by norm_cast ] ) ( show 1 + ε ≥ 1 by linarith ) ) ]

/-- For n ≥ 2, ε > 0, and u ∈ [ε log n, ε log(n+1)]:
|log u - log(ε log n)| ≤ 1/(n log n). -/
lemma log_diff_on_interval (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (u : ℝ) (hu1 : ε * Real.log n ≤ u) (hu2 : u ≤ ε * Real.log ((n : ℝ) + 1)) :
    |Real.log u - Real.log (ε * Real.log n)| ≤ 1 / ((n : ℝ) * Real.log n) := by
  have h_mean_value : ∃ c ∈ Set.Ioo (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u - Real.log (ε * Real.log n) = (u - ε * Real.log n) / c := by
    cases eq_or_lt_of_le hu1;
    · exact ⟨ ε * Real.log ( n + 1 ) / 2 + ε * Real.log n / 2, ⟨ by linarith [ show ε * Real.log ( n + 1 ) > ε * Real.log n from mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε ], by linarith [ show ε * Real.log ( n + 1 ) > ε * Real.log n from mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε ] ⟩, by aesop ⟩;
    · have := exists_deriv_eq_slope ( Real.log ) ‹_›;
      norm_num at *;
      exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| ne_of_gt <| lt_of_lt_of_le ( mul_pos hε <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) hx.1 ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| ne_of_gt <| lt_of_lt_of_le ( mul_pos hε <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) hx.1.le ) |> fun ⟨ c, hc1, hc2 ⟩ => ⟨ c, ⟨ hc1.1, hc1.2.trans_le hu2 ⟩, by rw [ eq_div_iff ] at hc2 <;> ring_nf at * <;> linarith ⟩;
  obtain ⟨c, hc1, hc2⟩ := h_mean_value
  have h_bound : (u - ε * Real.log n) / c ≤ (Real.log (n + 1) - Real.log n) / Real.log n := by
    rw [ div_le_div_iff₀ ] <;> nlinarith [ hc1.1, hc1.2, Real.log_pos <| show ( n:ℝ ) > 1 by norm_cast, Real.log_lt_log ( by positivity ) <| show ( n:ℝ ) + 1 > n by norm_num ];
  have h_log_bound : Real.log (n + 1) - Real.log n ≤ 1 / n := by
    rw [ ← Real.log_div ( by positivity ) ( by positivity ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by ring_nf; norm_num [ show n ≠ 0 by positivity ] ) ;
  rw [ abs_of_nonneg ( sub_nonneg_of_le <| Real.log_le_log ( by exact mul_pos hε <| Real.log_pos <| by norm_cast ) hu1 ) ] ; convert h_bound.trans <| div_le_div_of_nonneg_right h_log_bound <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith using 1 ; ring;

/-- The series ∑_{n≥2} 1/(n² log n) converges. -/
lemma summable_inv_sq_log :
    Summable (fun n : ℕ => if (n : ℕ) ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
  have h_pseries : Summable (fun n : ℕ => if n ≥ 2 then 1 / (n ^ 2 * Real.log 2) else 0) := by
    rw [ ← summable_nat_add_iff 2 ];
    norm_num;
    exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
  refine Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => ?_ ) h_pseries;
  split_ifs <;> first | positivity | gcongr ; norm_cast

/-- log ε * (1 - 2^{-ε}) → 0 as ε → 0+. -/
lemma log_eps_one_minus_rpow_tendsto :
    Tendsto (fun ε : ℝ => Real.log ε * (1 - (2 : ℝ) ^ (-ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_approx : Filter.Tendsto (fun ε : ℝ => (1 - 2 ^ (-ε)) / ε) (𝓝[>] 0) (nhds (Real.log 2)) := by
    simpa [ div_eq_inv_mul, Real.rpow_def_of_pos ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.const_sub 1 <| HasDerivAt.exp <| HasDerivAt.const_mul ( -Real.log 2 ) <| hasDerivAt_id 0 );
  convert h_approx.mul ( Real.continuous_mul_log.continuousWithinAt ) using 2 <;> ring;
  by_cases h : ‹ℝ› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] ; ring

/-- The function log(u) * exp(-u) is integrable on (0, ∞). -/
lemma integrable_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
  have h_split : MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioc 0 1) ∧ MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 1) := by
    constructor;
    · have h_integrable_left : MeasureTheory.IntegrableOn (fun u => Real.log u) (Set.Ioc 0 1) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> norm_num;
      refine' h_integrable_left.norm.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable_left.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul, Real.norm_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_of_le_one_right ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1, hx.2 ] ) ;
    · have h_integrable : MeasureTheory.IntegrableOn (fun u => u * Real.exp (-u)) (Set.Ioi 1) := by
        have := @integral_rpow_mul_exp_neg_rpow 1;
        specialize @this 1 ; norm_num at this;
        exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ( Set.Ioi_subset_Ioi zero_le_one );
      refine' h_integrable.mono' _ _;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( Real.log_nonneg hx.out.le ) ( Real.exp_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx.out ) ) ( by linarith ) ) ( Real.exp_nonneg _ ) ;
  convert h_split.1.union h_split.2 using 1 ; norm_num

/-- The integral of |log u * exp(-u)| over (0, δ] tends to 0 as δ → 0+. -/
lemma integral_log_exp_near_zero_tendsto :
    Tendsto (fun δ : ℝ => ∫ u in Set.Ioc 0 δ, |Real.log u * Real.exp (-u)|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_log_abs : ∀ δ : ℝ, 0 < δ → ∫ u in Set.Ioc 0 δ, |Real.log u * Real.exp (-u)| ≤ ∫ u in Set.Ioc 0 δ, |Real.log u| := by
    intro δ hδ; refine' MeasureTheory.integral_mono_of_nonneg _ _ _ <;> norm_num [ abs_mul ];
    · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => by positivity );
    · have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.log u) (Set.Ioc 0 δ) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le ] ; aesop;
      exact h_integrable.abs;
    · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => mul_le_of_le_one_right ( abs_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1 ] ) );
  refine' squeeze_zero_norm' _ integral_abs_log_near_zero_tendsto;
  filter_upwards [ self_mem_nhdsWithin ] with δ hδ using by rw [ Real.norm_of_nonneg ( MeasureTheory.integral_nonneg fun _ => abs_nonneg _ ) ] ; exact h_log_abs δ hδ

/-- The integral of |log u * exp(-u)| over (A, ∞) tends to 0 as A → ∞. -/
lemma integral_log_exp_tail_tendsto :
    Tendsto (fun A : ℝ => ∫ u in Set.Ioi A, |Real.log u * Real.exp (-u)|)
      atTop (𝓝 0) := by
  convert MeasureTheory.tendsto_setIntegral_of_antitone _ _ _ using 1;
  · rw [ show ( ⋂ n : ℝ, Set.Ioi n ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x hx; exact absurd ( Set.mem_iInter.mp hx ( x + 1 ) ) ( by norm_num ) ] ; norm_num;
  · infer_instance;
  · exact fun i => measurableSet_Ioi;
  · exact fun x y hxy => Set.Ioi_subset_Ioi hxy;
  · use 1;
    have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
      convert integrable_log_mul_exp_neg using 1;
    exact MeasureTheory.IntegrableOn.mono_set ( h_integrable.abs ) ( Set.Ioi_subset_Ioi zero_le_one )

/-! ### Change of variables and main Riemann sum lemma -/

/-
Change of variables: ε ∫₁^∞ log(log t) t^{-(1+ε)} dt = ε ∫₀^∞ log(u) exp(-εu) du.
Combined with laplace_log_identity, gives the value -γ - log ε.
-/
lemma laplace_log_change_var (ε : ℝ) (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-(1 + ε)) =
    -Real.eulerMascheroniConstant - Real.log ε := by
  -- Use the substitution $u = \log t$ to transform the integral.
  have h_subst : ∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-(1 + ε)) = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) := by
    -- Apply the substitution $u = \log t$ to transform the integral.
    have h_subst : ∫ t in Set.Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-(1 + ε)) = ∫ u in (fun t => Real.log t) '' Set.Ioi (1 : ℝ), Real.log u * Real.exp (-ε * u) := by
      rw [ MeasureTheory.integral_image_eq_integral_abs_deriv_smul ] <;> norm_num [ Real.deriv_log ];
      any_goals intro x hx; exact Real.hasDerivAt_log ( by linarith ) |> HasDerivAt.hasDerivWithinAt;
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ abs_of_pos ( inv_pos.mpr <| zero_lt_one.trans hx ) ] ; rw [ Real.rpow_def_of_pos ( zero_lt_one.trans hx ) ] ; ring;
        rw [ sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log ( zero_lt_one.trans hx ) ] ; ring;
      · exact fun x hx y hy hxy => Real.log_injOn_pos ( show 0 < x by linarith [ hx.out ] ) ( show 0 < y by linarith [ hy.out ] ) hxy;
    convert h_subst using 3 ; norm_num [ Set.ext_iff ];
    exact fun x => ⟨ fun hx => ⟨ Real.exp x, by norm_num; linarith, by norm_num ⟩, fun ⟨ y, hy, hy' ⟩ => hy'.symm ▸ Real.log_pos hy ⟩;
  -- Use the substitution $v = \epsilon u$ to transform the integral.
  have h_subst_v : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ v in Set.Ioi 0, (Real.log v - Real.log ε) * Real.exp (-v) := by
    have h_subst_v : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ v in Set.Ioi 0, Real.log (v / ε) * Real.exp (-v) := by
      have h_subst' : ∀ {f : ℝ → ℝ}, ∫ u in Set.Ioi 0, f u = (1 / ε) * ∫ v in Set.Ioi 0, f (v / ε) := by
        intro f; simp +decide [ div_eq_inv_mul, MeasureTheory.integral_const_mul, hε.ne' ] ;
        rw [ MeasureTheory.integral_comp_mul_left_Ioi ] <;> norm_num [ hε.ne' ];
        positivity;
      convert h_subst' using 3 ; ring_nf ; norm_num [ hε.ne' ];
      ac_rfl;
    exact h_subst_v.trans ( by refine' congr_arg _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ Real.log_div hx.out.ne' hε.ne' ] ) );
  -- Use the fact that $\int_0^\infty \log v \exp(-v) dv = -\gamma$ and $\int_0^\infty \exp(-v) dv = 1$.
  have h_integrals : ∫ v in Set.Ioi 0, Real.log v * Real.exp (-v) = -Real.eulerMascheroniConstant ∧ ∫ v in Set.Ioi 0, Real.exp (-v) = 1 := by
    exact ⟨ by simpa using gamma_integral, by simpa using integral_exp_neg_Ioi 0 ⟩;
  simp_all +decide [ sub_mul ];
  rw [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul ] <;> norm_num [ h_integrals, hε.ne' ];
  · have := @integrable_log_mul_exp_neg;
    exact this;
  · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) _

/-- Splitting an integral at a point: ∫_{Ioi 0} f = ∫_{Ioc 0 δ} f + ∫_{Ioi δ} f -/
lemma integral_Ioi_split (δ : ℝ) (hδ : 0 < δ)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi 0)) :
    ∫ u in Set.Ioi 0, f u = (∫ u in Set.Ioc 0 δ, f u) + ∫ u in Set.Ioi δ, f u := by
  have h : Set.Ioi (0 : ℝ) = Set.Ioc 0 δ ∪ Set.Ioi δ := (Set.Ioc_union_Ioi_eq_Ioi hδ.le).symm
  simp only [h, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hf.mono_set Set.Ioc_subset_Ioi_self)
    (hf.mono_set (Set.Ioi_subset_Ioi hδ.le))]

/-
Decomposing ∫_{Ioi a₀} f as a tsum of integrals over (aₙ, aₙ₊₁] for a strictly monotone
sequence aₙ tending to ∞.
-/
lemma integral_Ioi_eq_tsum_Ioc (a : ℕ → ℝ) (ha : StrictMono a) (ha_lim : Tendsto a atTop atTop)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (a 0))) :
    ∫ u in Set.Ioi (a 0), f u = ∑' n, ∫ u in Set.Ioc (a n) (a (n + 1)), f u := by
  convert MeasureTheory.integral_iUnion ?_ ?_ ?_ using 1;
  · congr with x;
    simp +zetaDelta at *;
    constructor <;> intro hx;
    · -- Since $a$ is strictly monotone and tends to infinity, there exists some $n$ such that $a n \geq x$.
      obtain ⟨n, hn⟩ : ∃ n, a n ≥ x := by
        exact ( ha_lim.eventually_ge_atTop x ) |> fun h => h.exists;
      contrapose! hn;
      exact Nat.recOn n ( by linarith ) hn;
    · exact lt_of_le_of_lt ( ha.monotone ( Nat.zero_le _ ) ) hx.choose_spec.1;
  · infer_instance;
  · exact fun i => measurableSet_Ioc;
  · exact fun i j hij => Set.disjoint_left.mpr fun x hx₁ hx₂ => hij <| le_antisymm ( le_of_not_gt fun hi => by linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, ha.monotone hi, ha.monotone ( Nat.succ_le_of_lt hi ) ] ) ( le_of_not_gt fun hj => by linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, ha.monotone hj, ha.monotone ( Nat.succ_le_of_lt hj ) ] );
  · refine' hf.mono_set _;
    exact Set.iUnion_subset fun i => Set.Ioc_subset_Ioi_self.trans ( Set.Ioi_subset_Ioi <| ha.monotone <| Nat.zero_le _ )

/-
Quantitative bound: the Riemann sum T(ε) = ∑ log(ε log n)(n^{-ε} - (n+1)^{-ε})
is within O(ε) + o(1) of -γ.
-/
set_option maxHeartbeats 3200000 in
lemma riemann_sum_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∑' n : ℕ, (if n ≥ 2 then
      Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
    else 0) - (-Real.eulerMascheroniConstant)| ≤
    (∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) +
    ε * ∑' n : ℕ, (if n ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
  -- The proof decomposes -γ = ∫_0^∞ log(u) e^{-u} du into pieces and bounds the Riemann sum error.
  have h_decomp : -Real.eulerMascheroniConstant = (∫ u in Set.Ioc 0 (ε * Real.log 2), Real.log u * Real.exp (-u)) + (∑' n : ℕ, if n ≥ 2 then (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u)) else 0) := by
    have h_decomp : -Real.eulerMascheroniConstant = (∫ u in Set.Ioc 0 (ε * Real.log 2), Real.log u * Real.exp (-u)) + (∑' n : ℕ, ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u)) := by
      rw [ ← gamma_integral, integral_Ioi_split, integral_Ioi_eq_tsum_Ioc ];
      case a => exact fun n => ε * Real.log ( n + 2 );
      all_goals norm_num [ add_assoc ];
      · exact fun n m hnm => mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε;
      · exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      · exact MeasureTheory.IntegrableOn.mono_set ( integrable_log_mul_exp_neg ) ( Set.Ioi_subset_Ioi <| by positivity );
      · positivity;
      · exact?;
    rw [ h_decomp, ← tsum_eq_tsum_of_ne_zero_bij ];
    use fun x => x + 2;
    · aesop_cat;
    · intro x hx; use ⟨ x - 2, by
        rcases x with ( _ | _ | x ) <;> simp_all +decide [ Function.support ];
        exact_mod_cast hx ⟩ ; aesop;
    · norm_num [ add_assoc ];
  -- For each term in the sum, we have:
  have h_term : ∀ n : ℕ, n ≥ 2 → |Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u))| ≤ ε / ((n : ℝ) ^ 2 * Real.log n) := by
    intro n hn
    have h_term : |Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u))| ≤ (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log (ε * Real.log n) - Real.log u| * Real.exp (-u)) := by
      have h_term : Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) = ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log (ε * Real.log n) * Real.exp (-u) := by
        rw [ ← intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ), intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg ] ; norm_num;
        rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring ; norm_num;
      rw [ h_term, ← MeasureTheory.integral_sub ];
      · convert MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) using 1;
        norm_num [ ← sub_mul, abs_mul, Real.exp_pos ];
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun u hu => by exact ContinuousAt.mul ( Real.continuousAt_log ( by nlinarith [ hu.1, hu.2, show ( 0 :ℝ ) < ε * Real.log n by exact mul_pos hε ( Real.log_pos ( by norm_cast ) ) ] ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) ) ) |> fun h => h.mono_set ( Set.Ioc_subset_Icc_self );
    -- Using the bound from `log_diff_on_interval`, we get:
    have h_bound : ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log (ε * Real.log n) - Real.log u| * Real.exp (-u) ≤ ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), (1 / ((n : ℝ) * Real.log n)) * Real.exp (-u) := by
      refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
      · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( ContinuousOn.abs ( continuousOn_const.sub ( Real.continuousOn_log.mono <| by intro u hu; exact ne_of_gt <| lt_of_lt_of_le ( by exact mul_pos hε <| Real.log_pos <| by norm_cast ) hu.1 ) ) ) <| ContinuousOn.rexp <| ContinuousOn.neg continuousOn_id ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · intro u hu₁ hu₂; rw [ abs_sub_comm ] ; gcongr;
        convert log_diff_on_interval n hn ε hε u hu₁.le hu₂ using 1 ; ring;
    -- Using the bound from `rpow_diff_le_eps_div`, we get:
    have h_bound2 : ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.exp (-u) ≤ ε / (n : ℝ) := by
      rw [ ← intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ), intervalIntegral.integral_comp_neg ] ; norm_num;
      have := rpow_diff_le_eps_div n hn ε hε hε1; simp_all +decide [ Real.rpow_def_of_pos ( by positivity : 0 < ( n : ℝ ) ), Real.rpow_def_of_pos ( by positivity : 0 < ( n + 1 : ℝ ) ) ] ; ring_nf at *; aesop;
    simp_all +decide [ MeasureTheory.integral_const_mul ];
    refine le_trans h_term <| h_bound.trans ?_;
    convert mul_le_mul_of_nonneg_left h_bound2 ( show 0 ≤ ( Real.log n ) ⁻¹ * ( n : ℝ ) ⁻¹ by positivity ) using 1 ; ring;
  -- Applying the triangle inequality to the sum, we get:
  have h_triangle : |(∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) else 0) - (∑' n : ℕ, if n ≥ 2 then (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u)) else 0)| ≤ ε * ∑' n : ℕ, if n ≥ 2 then (1 / ((n : ℝ) ^ 2 * Real.log n)) else 0 := by
    rw [ ← Summable.tsum_sub, ← tsum_mul_left ];
    · refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
      · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ ) ( Summable.mul_left ε <| summable_inv_sq_log );
        split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
      · refine' Summable.tsum_le_tsum _ _ _;
        · intro n; split_ifs <;> simp_all +decide [ div_eq_mul_inv ] ;
        · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ ) ( Summable.mul_left ε <| summable_inv_sq_log );
          split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
        · exact Summable.mul_left _ <| by simpa using summable_inv_sq_log;
    · rw [ ← summable_nat_add_iff 2 ] at *;
      have h_summable : Summable (fun n : ℕ => ε / ((n + 2 : ℝ) ^ 2 * Real.log (n + 2))) := by
        have h_summable : Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2 * Real.log (n + 2))) := by
          have h_summable : Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2 * Real.log 2)) := by
            norm_num +zetaDelta at *;
            exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
          exact h_summable.of_nonneg_of_le ( fun n => one_div_nonneg.mpr <| mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) fun n => one_div_le_one_div_of_le ( mul_pos ( sq_pos_of_pos <| by linarith ) <| Real.log_pos <| by linarith ) <| mul_le_mul_of_nonneg_left ( Real.log_le_log ( by linarith ) <| by linarith ) <| sq_nonneg _;
        convert h_summable.mul_left ε using 2 ; ring;
      have h_summable : Summable (fun n : ℕ => Real.log (ε * Real.log (n + 2)) * ((n + 2 : ℝ) ^ (-ε : ℝ) - (n + 3 : ℝ) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u))) := by
        have h_summable : Summable (fun n : ℕ => |Real.log (ε * Real.log (n + 2)) * ((n + 2 : ℝ) ^ (-ε : ℝ) - (n + 3 : ℝ) ^ (-ε : ℝ)) - ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u)|) := by
          exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => by exact_mod_cast h_term ( n + 2 ) ( by linarith ) ) h_summable;
        exact h_summable.of_abs;
      convert h_summable.add ( show Summable fun n : ℕ => ∫ u in Set.Ioc ( ε * Real.log ( n + 2 ) ) ( ε * Real.log ( n + 3 ) ), Real.log u * Real.exp ( -u ) from ?_ ) using 2 ; norm_num [ add_assoc ];
      have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
        have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
          have h_integrable : IntegrableOn (fun u : ℝ => |Real.log u * Real.exp (-u)|) (Set.Ioi (ε * Real.log 2)) := by
            have h_integrable : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
              exact?;
            exact MeasureTheory.IntegrableOn.mono_set ( h_integrable.abs ) ( Set.Ioi_subset_Ioi ( by positivity ) )
          have h_summable : Summable (fun n : ℕ => ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
            have h_integral_split : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)| = ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)| := by
              intro N; induction N <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; ring;
              rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
              · exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.abs ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) ≤ 2 + ↑‹ℕ› ) ] ) ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) );
              · exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.abs ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.log_pos ( show ( 2 : ℝ ) + ↑‹ℕ› > 1 by linarith ), Real.log_pos ( show ( 3 : ℝ ) + ↑‹ℕ› > 1 by linarith ) ] ) ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) )
            have h_integral_split : Filter.Tendsto (fun N : ℕ => ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)|) Filter.atTop (nhds (∫ u in Set.Ioi (ε * Real.log 2), |Real.log u * Real.exp (-u)|)) := by
              apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
              exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
            rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
            · exact fun h => not_tendsto_atTop_of_tendsto_nhds h_integral_split <| h.congr <| by aesop;
            · exact fun n => intervalIntegral.integral_nonneg ( by gcongr ; linarith ) fun u hu => abs_nonneg _;
          exact h_summable.congr fun n => by rw [ intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ) ] ;
        convert h_summable using 1;
      convert h_summable.of_norm_bounded _ using 2;
      · infer_instance;
      · exact fun n => MeasureTheory.norm_integral_le_integral_norm _;
    · -- The series $\sum_{n=2}^\infty \int_{\epsilon \log n}^{\epsilon \log (n+1)} |\log u| e^{-u} du$ is absolutely convergent.
      have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log u * Real.exp (-u)| else 0) := by
        have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log u * Real.exp (-u)| else 0) := by
          have h_integrable : IntegrableOn (fun u : ℝ => |Real.log u * Real.exp (-u)|) (Set.Ioi 0) := by
            exact MeasureTheory.Integrable.abs ( integrable_log_mul_exp_neg )
          have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
            have h_summable : Summable (fun n : ℕ => ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
              have h_integral_split : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)| = ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)| := by
                intro N; induction N <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; ring;
                rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
                · exact h_integrable.mono_set ( fun x hx => by cases Set.mem_uIcc.mp hx <;> exact Set.mem_Ioi.mpr <| by nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) ≤ 2 + ↑‹ℕ› ) ] );
                · exact h_integrable.mono_set ( fun x hx => by cases Set.mem_uIcc.mp hx <;> exact Set.mem_Ioi.mpr <| by nlinarith [ Real.log_pos <| show ( 2 : ℝ ) + ↑‹ℕ› > 1 by linarith, Real.log_pos <| show ( 3 : ℝ ) + ↑‹ℕ› > 1 by linarith ] )
              have h_integral_split : Filter.Tendsto (fun N : ℕ => ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)|) Filter.atTop (nhds (∫ u in Set.Ioi (ε * Real.log 2), |Real.log u * Real.exp (-u)|)) := by
                apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
                · exact h_integrable.mono_set <| Set.Ioi_subset_Ioi <| by positivity;
                · exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
              rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
              · exact fun h => not_tendsto_atTop_of_tendsto_nhds h_integral_split <| h.congr <| by aesop;
              · exact fun n => intervalIntegral.integral_nonneg ( by gcongr ; linarith ) fun u hu => abs_nonneg _;
            exact h_summable.congr fun n => by rw [ intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ) ] ;
          rw [ ← summable_nat_add_iff 2 ];
          convert h_summable using 2 ; norm_num [ add_assoc ];
        convert h_abs_conv using 1;
      refine' .of_norm <| h_abs_conv.of_nonneg_of_le ( fun n => _ ) ( fun n => _ );
      · positivity;
      · split_ifs <;> [ exact MeasureTheory.norm_integral_le_integral_norm _; norm_num ];
  refine' le_trans _ ( add_le_add ( le_of_eq _ ) h_triangle );
  rotate_left;
  exact |∫ u in Set.Ioc 0 ( ε * Real.log 2 ), Real.log u * Real.exp ( -u )|;
  · rw [ abs_of_nonpos ];
    · rw [ ← MeasureTheory.integral_neg ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _ ; rw [ abs_of_nonpos ] ; exact mul_nonpos_of_nonpos_of_nonneg ( Real.log_nonpos hx.1.le <| by nlinarith [ hx.2, Real.log_le_sub_one_of_pos zero_lt_two ] ) ( Real.exp_nonneg _ ) ;
    · exact MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun x hx => mul_nonpos_of_nonpos_of_nonneg ( Real.log_nonpos hx.1.le ( by nlinarith [ hx.2, Real.log_le_sub_one_of_pos zero_lt_two ] ) ) ( Real.exp_nonneg _ );
  · grind

end


noncomputable section

/-- The mertensH' constant from the main file, restated here for convenience. -/
def mertensH_val : ℝ := ∑' (p : Nat.Primes), (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-! ### Step 1: The limit of ζ(σ)(σ-1) as σ → 1+ -/

/-
For real σ > 1, the Riemann zeta function equals 1/(σ-1) + γ + O(σ-1).
In particular, (σ-1)·ζ(σ) → 1 and ζ(σ) - 1/(σ-1) → γ.
-/
lemma zeta_near_one_real :
    Filter.Tendsto (fun σ : ℝ => (riemannZeta (σ : ℂ)).re - 1 / (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 Real.eulerMascheroniConstant) := by
  have h_zeta : Filter.Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1)) (nhdsWithin 1 {1}ᶜ) (nhds (Complex.ofReal (Real.eulerMascheroniConstant))) := by
    convert tendsto_riemannZeta_sub_one_div using 1;
  have := h_zeta.comp ( show Filter.Tendsto ( fun σ : ℝ => ↑σ ) ( nhdsWithin 1 ( Set.Ioi 1 ) ) ( nhdsWithin 1 { 1 } ᶜ ) from ?_ );
  · convert Complex.continuous_re.continuousAt.tendsto.comp this using 2 ; norm_num;
    norm_num [ Complex.normSq, sq ];
  · refine' Filter.Tendsto.inf _ _ <;> norm_num;
    · exact Complex.continuous_ofReal.tendsto 1;
    · exact fun x hx => ne_of_gt hx

/-! ### Step 2: Log ζ(σ) = -log(σ-1) + O(σ-1) -/

/-
As σ → 1+ (real), log(ζ(σ)) + log(σ-1) → 0.
-/
lemma log_zeta_plus_log_sigma_minus_one :
    Filter.Tendsto (fun σ : ℝ => Real.log ((riemannZeta (σ : ℂ)).re) + Real.log (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 0) := by
  -- Use the fact that $(σ-1)ζ(σ) → 1$ as $σ → 1+$.
  have h_prod : Filter.Tendsto (fun σ : ℝ => (σ - 1) * (riemannZeta (σ : ℂ)).re) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have h_zeta_approx : Filter.Tendsto (fun σ : ℝ => (σ - 1) * ((riemannZeta (σ : ℂ)).re - 1 / (σ - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      convert Filter.Tendsto.mul ( continuousWithinAt_id.sub continuousWithinAt_const ) ( zeta_near_one_real ) using 2 ; norm_num;
    have := h_zeta_approx.const_add 1;
    simpa using this.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ mul_sub, mul_div_cancel₀ _ ( sub_ne_zero_of_ne hx.out.ne' ) ] ; ring );
  convert Filter.Tendsto.congr' _ ( Filter.Tendsto.log h_prod _ ) using 1 <;> norm_num;
  filter_upwards [ h_prod.eventually ( lt_mem_nhds one_pos ) ] with x hx using by rw [ Real.log_mul ( by aesop ) ( by aesop ) ] ; ring;

/-! ### Step 3: Euler product identity (real-valued) -/

/-
For real σ > 1, ζ(σ) equals the Euler product ∏_p (1 - p^{-σ})^{-1}.
-/
lemma zeta_real_eq_euler_product (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re =
      ∏' (p : Nat.Primes), (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have h_euler : ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-σ : ℂ))⁻¹ = riemannZeta σ := by
    convert riemannZeta_eulerProduct_tprod _;
    exact_mod_cast hσ;
  convert congr_arg Complex.re h_euler.symm using 1;
  have h_prod_real : ∀ p : Nat.Primes, (1 - (p : ℂ) ^ (-σ : ℂ))⁻¹ = (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ := by
    norm_num [ Complex.ofReal_cpow, Real.rpow_neg ];
    exact fun p => by rw [ Complex.cpow_neg ] ;
  rw [ tprod_congr h_prod_real ];
  have h_prod_real : Multipliable (fun p : Nat.Primes => (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹) := by
    have h_prod_real : Summable (fun p : Nat.Primes => Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹) := by
      have h_prod_real : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ : ℝ)) := by
        exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow.2 <| by linarith ) Subtype.coe_injective;
      have h_prod_real : ∀ p : Nat.Primes, Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ ≤ 2 * (p : ℝ) ^ (-σ : ℝ) := by
        intro p
        have h_log_bound : Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ ≤ 2 * (p : ℝ) ^ (-σ : ℝ) := by
          have h_log_bound_step : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → Real.log (1 - x)⁻¹ ≤ 2 * x := by
            norm_num +zetaDelta at *;
            exact fun x hx₁ hx₂ => by nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
          apply h_log_bound_step;
          norm_num [ Real.rpow_neg ];
          exact ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.prop.two_le, show ( p : ℝ ) ^ σ ≥ 2 ^ σ by gcongr ; exact_mod_cast p.prop.two_le, Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hσ.le ] ⟩;
        exact h_log_bound;
      exact Summable.of_nonneg_of_le ( fun p => Real.log_nonneg <| by exact le_trans ( by norm_num ) <| inv_anti₀ ( sub_pos.mpr <| by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.2.one_lt ) <| neg_lt_zero.mpr <| by positivity ) <| sub_le_self _ <| by positivity ) h_prod_real <| Summable.mul_left _ <| by assumption;
    have h_prod_real : Multipliable (fun p : Nat.Primes => Real.exp (Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹)) := by
      refine' ⟨ _, _ ⟩;
      exact Real.exp ( ∑' p : Nat.Primes, Real.log ( 1 - ( p : ℝ ) ^ ( -σ ) ) ⁻¹ );
      convert h_prod_real.hasSum.exp using 1;
      · exact funext fun p => by rw [ Function.comp_apply, Real.exp_eq_exp_ℝ ] ;
      · rw [ Real.exp_eq_exp_ℝ ];
    convert h_prod_real using 1;
    exact funext fun p => by rw [ Real.exp_log ( inv_pos.mpr ( sub_pos.mpr ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.2.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ) ) ) ] ;
  convert rfl;
  convert Complex.ofReal_re _;
  convert HasProd.tprod_eq ( HasProd.map ( h_prod_real.hasProd ) ( algebraMap ℝ ℂ ) _ ) using 1;
  exact Complex.continuous_ofReal

/-
For real σ > 1, log ζ(σ) = ∑_p [-log(1 - p^{-σ})].
-/
lemma log_zeta_eq_sum_primes (σ : ℝ) (hσ : 1 < σ) :
    Real.log ((riemannZeta (σ : ℂ)).re) =
      ∑' (p : Nat.Primes), (-Real.log (1 - (p : ℝ) ^ (-σ))) := by
  -- From riemannZeta_eulerProduct_exp_log (Mathlib): exp(∑' p, -log(1 - p^{-s})) = ζ(s) for Re(s) > 1.
  have h_exp_sum : Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))) = (riemannZeta (σ : ℂ)).re := by
    convert congr_arg Complex.re ( riemannZeta_eulerProduct_exp_log ( show 1 < ( σ : ℂ ).re from mod_cast hσ ) ) using 1;
    convert Complex.ofReal_re _;
    rw [ Complex.ofReal_tsum ] ; congr ; ext ; norm_cast ; norm_num [ Real.rpow_def_of_pos, Nat.Prime.pos ];
    rw [ Complex.ofReal_log ( sub_nonneg.2 <| by simpa using Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.2 <| Nat.Prime.pos <| Subtype.property _ ) <| neg_nonpos.2 <| by positivity ) ];
    norm_num [ Complex.ofReal_cpow, Nat.Prime.pos ];
  rw [ ← h_exp_sum, Real.log_exp ]

/-! ### Step 4: Decompose log ζ(σ) = P(σ) + H(σ) -/

/-- The "prime zeta function" P(σ) = ∑_p p^{-σ}. -/
def primeZetaReal (σ : ℝ) : ℝ := ∑' (p : Nat.Primes), (p : ℝ) ^ (-σ)

/-- The "tail" H(σ) = ∑_p ∑_{k≥2} p^{-kσ}/k. -/
def mertensH_sigma (σ : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), ((-Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ))

/-
H(σ) → mertensH_val as σ → 1+.
-/
lemma mertensH_sigma_tendsto :
    Filter.Tendsto mertensH_sigma (nhdsWithin 1 (Set.Ioi 1)) (𝓝 mertensH_val) := by
  refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
  refine' fun p => ( p : ℝ ) ⁻¹ ^ 2 * 2;
  · exact Summable.mul_right _ <| by simpa using Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _;
  · intro p; convert Filter.Tendsto.sub ( Filter.Tendsto.neg ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) ) _ ) ) ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) using 2 <;> norm_num ; ring;
    rotate_left;
    congr! 1;
    · exact ne_of_gt ( sub_pos_of_lt ( inv_lt_one_of_one_lt₀ ( mod_cast p.2.one_lt ) ) );
    · norm_num [ Real.rpow_neg, Real.inv_rpow ];
  · -- For any prime $p$, we have $|-\log(1 - p^{-\sigma}) - p^{-\sigma}| \leq \frac{p^{-2\sigma}}{1 - p^{-\sigma}}$.
    have h_bound : ∀ p : Nat.Primes, ∀ σ : ℝ, 1 ≤ σ → |-(Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)| ≤ (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) := by
      intros p σ hσ
      have h_log_bound : ∀ x : ℝ, 0 < x ∧ x < 1 → |-(Real.log (1 - x)) - x| ≤ x^2 / (1 - x) := by
        intro x hx; rw [ abs_le ] ; constructor <;> nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ), div_mul_cancel₀ ( x ^ 2 ) ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
      convert h_log_bound ( ( p : ℝ ) ^ ( -σ ) ) ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.prop.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ⟩ using 1 ; ring;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
    -- For any prime $p$, we have $|-\log(1 - p^{-\sigma}) - p^{-\sigma}| \leq \frac{p^{-2\sigma}}{1 - p^{-\sigma}} \leq \frac{p^{-2}}{1 - p^{-1}}$.
    have h_bound_simplified : ∀ p : Nat.Primes, ∀ σ : ℝ, 1 ≤ σ → |-(Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)| ≤ (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) := by
      intros p σ hσ
      specialize h_bound p σ hσ
      have h_bound_simplified : (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) ≤ (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) := by
        gcongr <;> norm_num;
        · exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( mod_cast p.2.one_lt ) ( show ( -1 : ℝ ) < 0 by norm_num ) ) ( by norm_num );
        · exact_mod_cast p.2.one_lt.le;
        · linarith;
        · exact_mod_cast p.2.one_lt.le;
      exact h_bound.trans h_bound_simplified;
    -- For any prime $p$, we have $\frac{p^{-2}}{1 - p^{-1}} \leq \frac{1}{p^2} \cdot 2$.
    have h_bound_final : ∀ p : Nat.Primes, (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) ≤ (p : ℝ) ^ (-2 : ℝ) * 2 := by
      norm_cast ; norm_num;
      exact fun p => by rw [ div_eq_mul_inv ] ; exact mul_le_mul_of_nonneg_left ( by rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le, inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by exact_mod_cast p.2.ne_zero ) ] ) ( by positivity ) ;
    filter_upwards [ self_mem_nhdsWithin ] with σ hσ using fun p => le_trans ( h_bound_simplified p σ hσ.out.le ) ( le_trans ( h_bound_final p ) ( by norm_cast; norm_num ) )

/-
P(σ) + log(σ-1) → -mertensH_val as σ → 1+.
-/
lemma primeZeta_plus_log_tendsto :
    Filter.Tendsto (fun σ : ℝ => primeZetaReal σ + Real.log (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 (-mertensH_val)) := by
  have h_decomp : ∀ σ : ℝ, 1 < σ → primeZetaReal σ + Real.log (σ - 1) = (Real.log ((riemannZeta (σ : ℂ)).re) + Real.log (σ - 1)) - mertensH_sigma σ := by
    intro σ hσ
    have h_sum : ∑' (p : Nat.Primes), (-Real.log (1 - (p : ℝ) ^ (-σ))) = ∑' (p : Nat.Primes), (p : ℝ) ^ (-σ) + ∑' (p : Nat.Primes), ((-Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)) := by
      rw [ ← Summable.tsum_add ] ; congr ; ext p ; ring;
      · exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
      · -- We'll use the fact that if the series $\sum_{p} p^{-\sigma}$ converges, then the series $\sum_{p} (-\log(1 - p^{-\sigma}) - p^{-\sigma})$ also converges.
        have h_summable : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) := by
          exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
        refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_summable.mul_left 2 );
        · linarith [ Real.log_le_sub_one_of_pos ( show 0 < 1 - ( p : ℝ ) ^ ( -σ ) by exact sub_pos.mpr ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.prop.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ) ) ];
        · have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → -Real.log (1 - x) ≤ 2 * x := by
            exact fun x hx => by nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
          have h_log_bound : 0 < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
            norm_num [ Real.rpow_neg ];
            exact ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.prop.two_le, show ( p : ℝ ) ^ σ ≥ p by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr p.prop.pos ) hσ.le ) ] ⟩;
          linarith [ ‹∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → -Real.log ( 1 - x ) ≤ 2 * x› _ h_log_bound ];
    linarith! [ log_zeta_eq_sum_primes σ hσ ];
  rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_decomp x hx ] ) ] ; convert ( log_zeta_plus_log_sigma_minus_one.sub mertensH_sigma_tendsto ) using 1 ; ring;

/-! ### Step 5: Abel summation + Abelian theorem -/

/-
Abel summation for the prime zeta function: discrete version.
For ε > 0: ∑_p (1/p)·p^{-ε} = ∑_{n≥2} A(n)·(n^{-ε} - (n+1)^{-ε}) where A(n) = ∑_{p≤n} 1/p.
-/
lemma abel_summation_primeZeta (ε : ℝ) (hε : 0 < ε) :
    primeZetaReal (1 + ε) =
      ∑' n : ℕ, (if n ≥ 2 then
        (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 1 / (p : ℝ)) *
        ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
      else 0) := by
  -- By definition of primeZetaReal, we have primeZetaReal (1 + ε) = ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε)).
  have h_primeZetaReal : primeZetaReal (1 + ε) = ∑' p : Nat.Primes, (1 / (p : ℝ)) * (p : ℝ) ^ (-ε) := by
    unfold primeZetaReal;
    norm_num [ Real.rpow_add, Real.rpow_neg, mul_comm ];
    exact tsum_congr fun p => by rw [ Real.rpow_add ( Nat.cast_pos.mpr p.2.pos ), Real.rpow_neg ( Nat.cast_nonneg _ ), Real.rpow_neg_one ] ; ring;
  have h_abel_summation : ∀ N : ℕ, ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ)) * (p : ℝ) ^ (-ε) = (∑ n ∈ Finset.Icc 2 N, (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) * (N + 1 : ℝ) ^ (-ε) := by
    intro N; induction' N with N ih <;> norm_num [ Finset.sum_range_succ, Finset.sum_filter ] at *;
    rcases N with ( _ | N ) <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    norm_num [ Finset.sum_range_succ ] ; ring;
    grind;
  -- Let's choose any $N$ and look at the expression.
  have h_limit : Filter.Tendsto (fun N : ℕ => ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ)) * (p : ℝ) ^ (-ε)) Filter.atTop (nhds (primeZetaReal (1 + ε))) := by
    have h_limit : Summable (fun p : Nat.Primes => (1 / (p : ℝ)) * (p : ℝ) ^ (-ε)) := by
      have h_summable : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + ε))) := by
        exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
      convert h_summable using 2 ; norm_num [ Real.rpow_add, Real.rpow_neg ] ; ring;
      rw [ ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_neg_one, ← Real.rpow_add ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Subtype.property _ ) ] ; ring;
    convert h_limit.hasSum.comp _;
    rotate_left;
    use fun N => Finset.filter ( fun p => Nat.Prime p.val ) ( Finset.filter ( fun p => p.val ≤ N ) ( Finset.subtype ( fun p => Nat.Prime p ) ( Finset.range ( N + 1 ) ) ) );
    · simp +decide [ SummationFilter.unconditional ];
      rw [ Filter.tendsto_atTop_atTop ];
      intro b; use b.sup ( fun p => p.val ) ; intro a ha; intro p hp; simp_all +decide [ Finset.subset_iff ] ;
      exact ⟨ Finset.mem_subtype.mpr ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ( ha p hp ) ) ), p.2 ⟩;
    · refine' Finset.sum_bij ( fun p hp => ⟨ p, by aesop ⟩ ) _ _ _ _ <;> simp +decide;
      · exact fun a ha ha' => ⟨ ⟨ Finset.mem_subtype.mpr <| Finset.mem_range.mpr <| Nat.lt_succ_of_le ha, ha ⟩, ha' ⟩;
      · grind;
      · exact fun p hp hp' hp'' => ⟨ p, ⟨ hp', hp'' ⟩, rfl ⟩;
  have h_limit_zero : Filter.Tendsto (fun N : ℕ => (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\sum_{p \leq N} \frac{1}{p}$ is bounded above by $\log \log N + C$ for some constant $C$.
    have h_bound : ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 → (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) ≤ Real.log (Real.log N) + C := by
      obtain ⟨ M, hM ⟩ := prime_reciprocal_sum_convergence;
      have := hM.bddAbove_range;
      exact ⟨ this.choose, fun N hN => by linarith [ this.choose_spec ( Set.mem_range_self N ) ] ⟩;
    -- Using the bound, we can show that the limit is zero.
    obtain ⟨C, hC⟩ := h_bound;
    have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log N) + C) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $(N + 1)^{-\epsilon}$ tends to $0$ faster than $\log \log N$ tends to infinity.
      have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log N)) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $(N + 1)^{-\epsilon}$ tends to $0$ faster than $\log \log N$ tends to infinity.
        have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log N) * (N : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
          -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y \epsilon}}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y * ε)) Filter.atTop (nhds 0) by
            have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hN ), mul_comm ] );
          -- Let $z = y \epsilon$, therefore the expression becomes $\frac{z}{e^z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => z * Real.exp (-z)) Filter.atTop (nhds 0) by
            have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hε );
            convert this.div_const ε using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm ε, hε.ne' ];
          convert ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) using 2 ; norm_num;
        refine' squeeze_zero_norm' _ h_lim_zero;
        filter_upwards [ Filter.eventually_gt_atTop 2 ] with N hN;
        rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log N by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ) ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ];
        exact mul_le_mul ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) |> le_trans <| by linarith ) ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ( by positivity ) ( by exact Real.log_nonneg <| by linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] );
      simpa [ add_mul ] using h_lim_zero.add ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
    refine' squeeze_zero_norm' _ h_lim_zero;
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( by positivity ) ) ] ; exact mul_le_mul_of_nonneg_right ( hC N hN ) ( by positivity ) ;
  have h_limit_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 2 N, (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε))) Filter.atTop (nhds (primeZetaReal (1 + ε))) := by
    simpa using h_limit.sub h_limit_zero |> Filter.Tendsto.congr ( by aesop );
  refine' tendsto_nhds_unique h_limit_sum _;
  have h_limit_sum : Summable (fun n : ℕ => if n ≥ 2 then (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε)) else 0) := by
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
    · intro H;
      convert not_tendsto_atTop_of_tendsto_nhds h_limit_sum _;
      convert H.comp ( Filter.tendsto_add_atTop_nat 1 ) using 2 ; norm_num [ Finset.sum_range_succ' ];
      erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
      cases ‹_› <;> norm_num [ add_comm, add_left_comm, add_assoc, Finset.sum_range_succ' ];
    · intro n; split_ifs <;> norm_num;
      exact mul_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith );
  convert h_limit_sum.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
  ext ( _ | N ) <;> norm_num [ Finset.sum_range_succ' ];
  erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ]

/-
Abelian theorem for bounded convergent sequences: if r(n) → 0 and r is bounded,
then ∑ r(n) · (n^{-ε} - (n+1)^{-ε}) → 0 as ε → 0+.
-/
lemma abelian_theorem_bounded_convergent (r : ℕ → ℝ) (hr_bdd : ∃ C, ∀ n, |r n| ≤ C)
    (hr_lim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  rcases hr_bdd with ⟨ C, hC ⟩ ; have := @hC 0 ; norm_num at this ⊢;
  -- For any $\delta > 0$, choose $N$ large enough that $\sup_{n > N} |r(n)| < \delta$.
  have h_sup : ∀ δ > 0, ∃ N : ℕ, ∀ n > N, |r n| < δ := by
    exact fun δ δ_pos => by rcases Metric.tendsto_atTop.mp hr_lim δ δ_pos with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa using hN n hn.le ⟩ ;
  -- For any $\delta > 0$, choose $N$ large enough that $\sup_{n > N} |r(n)| < \delta$. Then for $\varepsilon$ sufficiently small, the sum can be bounded.
  have h_bound : ∀ δ > 0, ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 → |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ C * (2 ^ (-ε) - (N + 1 : ℝ) ^ (-ε)) + δ * (N + 1 : ℝ) ^ (-ε) := by
    intro δ hδ_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n > N, |r n| < δ := h_sup δ hδ_pos
    use N + 1
    intro ε hε_pos hε_lt_1
    have h_split : |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| + |∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| := by
      have h_split : ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))) + (∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
        have h_split : ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = ∑' n : ℕ, (if n ≥ 2 ∧ n ≤ N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + ∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          rw [ ← Summable.tsum_add ];
          · grind;
          · refine' summable_of_ne_finset_zero _;
            exacts [ Finset.Icc 2 ( N + 1 ), fun n hn => if_neg fun h => hn <| Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ];
          · have h_summable : Summable (fun n : ℕ => r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))) := by
              have h_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) := by
                have h_telescope : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-ε) - (n + 2 : ℝ) ^ (-ε)) = 1 - (N + 1 : ℝ) ^ (-ε) := by
                  exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
                rw [ ← summable_nat_add_iff 1 ];
                rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
                · norm_num [ add_assoc, h_telescope ];
                  exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop ( by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
                · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
              exact Summable.of_norm <| by simpa [ abs_mul ] using Summable.of_nonneg_of_le ( fun n => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( fun n => mul_le_mul_of_nonneg_right ( hC n ) ( abs_nonneg _ ) ) ( h_summable.norm.mul_left C ) ;
            rw [ ← summable_nat_add_iff ( N + 2 ) ] at *;
            exact h_summable.congr fun n => by rw [ if_pos ( by linarith ) ] ;
        convert h_split using 2;
        rw [ tsum_eq_sum ];
        exacts [ Finset.sum_congr rfl fun x hx => by rw [ if_pos ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩ ], fun x hx => if_neg <| by simpa using hx ];
      grind +qlia;
    -- Bound the first part of the sum.
    have h_first_part : |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * (2 ^ (-ε) - (N + 2 : ℝ) ^ (-ε)) := by
      have h_first_part : |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * ∑ n ∈ Finset.Icc 2 (N + 1), ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) := by
        rw [ Finset.mul_sum _ _ _ ];
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rw [ abs_mul, abs_of_nonneg ( sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ( by linarith ) <| by linarith ) ] ; exact mul_le_mul_of_nonneg_right ( hC i ) <| sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ( by linarith ) <| by linarith );
      convert h_first_part using 2;
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert rfl using 1;
      convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
    -- Bound the second part of the sum.
    have h_second_part : |∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ δ * ∑' n : ℕ, (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      rw [ ← tsum_mul_left ];
      have h_second_part : ∀ n : ℕ, |(if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ δ * (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
        intro n; split_ifs <;> norm_num [ abs_mul, abs_of_nonneg, Real.rpow_nonneg, hε_pos.le ];
        rw [ abs_of_nonneg ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ] ; exact mul_le_mul_of_nonneg_right ( le_of_lt <| hN n <| by linarith ) <| sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
      refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
      · refine' Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_second_part n ) _;
        refine' Summable.mul_left _ _;
        rw [ ← summable_nat_add_iff ( N + 2 ) ];
        -- The series $\sum_{n=0}^{\infty} (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon}$ is a telescoping series.
        have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => (n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε)) := by
          intro N;
          refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
          -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
          have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
            exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
          exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
        convert h_telescoping N using 2 ; norm_num ; ring;
        rw [ if_pos ( by linarith ) ];
      · refine' Summable.tsum_le_tsum h_second_part _ _;
        · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_second_part n ) _;
          refine' Summable.mul_left _ _;
          rw [ ← summable_nat_add_iff ( N + 2 ) ];
          -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => ((n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε))) := by
            intro N;
            refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
            -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
            have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
              exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
            exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
          convert h_telescoping N using 2 ; norm_num ; ring;
          rw [ if_pos ( by linarith ) ];
        · refine' Summable.mul_left _ _;
          rw [ ← summable_nat_add_iff ( N + 2 ) ];
          -- The series $\sum_{n=0}^{\infty} \left( \frac{1}{(n+N+2)^{\varepsilon}} - \frac{1}{(n+N+3)^{\varepsilon}} \right)$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => (n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε)) := by
            intro N;
            refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
            -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
            have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
              exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
            exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
          convert h_telescoping N using 2 ; norm_num ; ring;
          rw [ if_pos ( by linarith ) ];
    -- The series $\sum_{n=N+2}^{\infty} (n^{-\varepsilon} - (n+1)^{-\varepsilon})$ is a telescoping series.
    have h_telescoping : ∑' n : ℕ, (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (N + 2 : ℝ) ^ (-ε) := by
      have h_telescoping : ∀ M : ℕ, M > N + 1 → ∑ n ∈ Finset.range (M + 1), (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (N + 2 : ℝ) ^ (-ε) - (M + 1 : ℝ) ^ (-ε) := by
        intro M hM; induction hM <;> simp_all +decide [ Finset.sum_range_succ ] ;
        · rw [ Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring;
        · rw [ if_pos ( by linarith ) ] ; ring;
      have h_telescoping_limit : Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) Filter.atTop (nhds ((N + 2 : ℝ) ^ (-ε))) := by
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ioi_mem_atTop ( N + 1 ) ) h_telescoping ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | exact sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
    grind;
  -- As $\varepsilon \to 0^+$, $(N+1)^{-\varepsilon} \to 1$, so the bound tends to $C \cdot (1 - 1) + \delta \cdot 1 = \delta$.
  have h_tendsto : ∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ 2 * δ := by
    intros δ hδ_pos
    obtain ⟨N, hN⟩ := h_bound δ hδ_pos
    have h_lim : Filter.Tendsto (fun ε : ℝ => C * (2 ^ (-ε) - (N + 1 : ℝ) ^ (-ε)) + δ * (N + 1 : ℝ) ^ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * (1 - 1) + δ * 1)) := by
      convert Filter.Tendsto.add ( tendsto_const_nhds.mul ( Filter.Tendsto.sub ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) ) ( tendsto_const_nhds.mul ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) using 2 <;> norm_num; all_goals linarith;
    have := Metric.tendsto_nhdsWithin_nhds.mp h_lim δ hδ_pos;
    obtain ⟨ ε₀, hε₀_pos, hε₀ ⟩ := this; exact ⟨ Min.min ε₀ 1, lt_min hε₀_pos zero_lt_one, fun ε hε₁ hε₂ => le_trans ( hN ε hε₁ ( lt_of_lt_of_le hε₂ ( min_le_right _ _ ) ) ) ( by linarith [ abs_lt.mp ( hε₀ hε₁ ( by simpa [ abs_of_pos hε₁ ] using lt_of_lt_of_le hε₂ ( min_le_left _ _ ) ) ) ] ) ⟩ ;
  rw [ Metric.tendsto_nhdsWithin_nhds ];
  exact fun ε hε => by rcases h_tendsto ( ε / 4 ) ( by positivity ) with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => by simpa [ abs_mul ] using lt_of_le_of_lt ( H x hx₁ ( by linarith [ abs_lt.mp hx₂ ] ) ) ( by linarith ) ⟩ ;

/-
The integral identity: ε ∫_0^∞ log(u) e^{-εu} du = -γ - log ε.
This follows from Γ'(1) = -γ via substitution v = εu.
-/
lemma laplace_log_identity (ε : ℝ) (hε : 0 < ε) :
    ε * ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-ε * u) =
    -Real.eulerMascheroniConstant - Real.log ε := by
  have h_int : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) = -Real.eulerMascheroniConstant := by
    -- The integral of log(u) * exp(-u) is the derivative of the Gamma function at 1.
    have h_gamma_deriv : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) = deriv (fun s => Real.Gamma s) 1 := by
      have h_gamma_deriv : deriv (fun s => Real.Gamma s) 1 = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) := by
        have h_gamma_int : ∀ s > 0, Real.Gamma s = ∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u) := by
          exact fun s hs => by rw [ Real.Gamma_eq_integral hs ] ; congr; ext; ring;
        -- Apply the dominated convergence theorem to interchange the derivative and the integral.
        have h_dominated_convergence : Filter.Tendsto (fun h => ∫ u in Set.Ioi 0, (u^h - 1) / h * Real.exp (-u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
          -- To apply the dominated convergence theorem, we need to show that the integrand is dominated by an integrable function.
          have h_dominated : ∀ h ∈ Set.Ioo 0 1, ∀ u ∈ Set.Ioi 0, |(u^h - 1) / h * Real.exp (-u)| ≤ |Real.log u| * Real.exp (-u) * (u + 1) := by
            intros h hh u hu
            have h_abs : |(u^h - 1) / h| ≤ |Real.log u| * (u + 1) := by
              -- Using the mean value theorem, we can find a $c \in (0, h)$ such that $u^h - 1 = h \cdot u^c \cdot \log u$.
              obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 h, u^h - 1 = h * u^c * Real.log u := by
                have := exists_deriv_eq_slope ( f := fun x => u ^ x ) hh.1;
                norm_num [ Real.rpow_def_of_pos hu, mul_assoc, mul_comm, mul_left_comm ] at *;
                exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by norm_num ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
              rw [ hc.2, mul_assoc, mul_div_cancel_left₀ _ hh.1.ne' ];
              rw [ abs_mul, mul_comm ];
              by_cases hu1 : u ≤ 1;
              · exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.out.le _ ) ] ; exact le_trans ( Real.rpow_le_one hu.out.le hu1 hc.1.1.le ) ( by linarith [ hu.out ] ) ) ( abs_nonneg _ );
              · exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.out.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith [ hc.1.2, hh.2 ] ) ) ( by norm_num ) ) ( abs_nonneg _ );
            rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] ; nlinarith [ Real.exp_pos ( -u ) ];
          -- The function $| \log u | e^{-u} (u + 1)$ is integrable on $(0, \infty)$.
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u) * (u + 1)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u) * u) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioi 0) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioc 0 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * |Real.log u|) (Set.Ioc 0 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.log u) (Set.Ioc 0 1) := by
                      exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                    refine' h_integrable.norm.congr _;
                    filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1.le ] ;
                  refine' h_integrable.mono' _ _;
                  · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.norm.aestronglyMeasurable );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg hu.1.le ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right hu.1.le ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr hu.1.le ) ) ) ( abs_nonneg _ ) ;
                have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioi 1) := by
                  have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * u) (Set.Ioi 1) := by
                    have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u^2 * Real.exp (-u)) (Set.Ioi 1) := by
                      have h_integrable' : ∫ u in Set.Ioi 0, u^2 * Real.exp (-u) = Real.Gamma 3 := by
                        rw [ h_gamma_int ] <;> norm_num;
                      exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_integrable'; rw [ MeasureTheory.integral_undef h_integrable' ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                    exact h_integrable'.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                  refine' h_integrable'.mono' _ _;
                  · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log.norm ) );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.log_nonneg hu.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ;
                convert h_integrable.union h_integrable' using 1 ; norm_num;
              exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioi 1) := by
                refine' h_integrable.mono_set ( Set.Ioi_subset_Ioi zero_le_one ) |> fun h => h.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_mul_of_one_le_right ( by positivity ) hu.out.le;
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u|) (Set.Ioc 0 1) := by
                  have h_integrable : ∫ u in Set.Ioc 0 1, |Real.log u| = 1 := by
                    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_neg ] ; norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
                refine' h_integrable.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hu.1.le ) <| abs_nonneg <| Real.log u;
              convert h_integrable.union ‹MeasureTheory.IntegrableOn ( fun u => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioi 1 ) MeasureTheory.volume› using 1 ; ext ; aesop;
            simp_all +decide [ mul_add ];
            exact MeasureTheory.Integrable.add ‹_› ‹_›;
          refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
          use fun u => |Real.log u| * Real.exp (-u) * (u + 1);
          · filter_upwards [ self_mem_nhdsWithin ] with n hn using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
          · filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with h hh using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun u hu => h_dominated h hh u hu;
          · exact h_integrable;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
            have h_lim : Filter.Tendsto (fun n => (u^n - 1) / n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log u)) := by
              simpa [ div_eq_inv_mul, Real.rpow_def_of_pos hu ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( HasDerivAt.exp ( HasDerivAt.const_mul ( Real.log u ) ( hasDerivAt_id 0 ) ) ) ( hasDerivAt_const 0 1 ) );
            exact h_lim.mul tendsto_const_nhds;
        have h_deriv : Filter.Tendsto (fun h => (Real.Gamma (1 + h) - Real.Gamma 1) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
          refine' h_dominated_convergence.congr' _;
          filter_upwards [ self_mem_nhdsWithin ] with h hh;
          rw [ h_gamma_int ( 1 + h ) ( by linarith [ hh.out ] ), h_gamma_int 1 zero_lt_one ];
          rw [ ← MeasureTheory.integral_sub ];
          · rw [ ← MeasureTheory.integral_div ] ; congr ; ext u ; norm_num ; ring;
          · have := @integral_rpow_mul_exp_neg_rpow 1;
            norm_num +zetaDelta at *;
            exact ( by have := @this h ( by linarith ) ; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; positivity ) );
          · simpa using MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
        refine' tendsto_nhds_unique _ h_deriv;
        have h_deriv : HasDerivAt (fun s => Real.Gamma s) (deriv (fun s => Real.Gamma s) 1) 1 := by
          exact hasDerivAt_deriv_iff.mpr ( Real.differentiableAt_Gamma fun m => by linarith );
        simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
      exact h_gamma_deriv.symm;
    rw [ h_gamma_deriv, Real.hasDerivAt_Gamma_one.deriv ];
  have h_subst : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ u in Set.Ioi 0, (Real.log u - Real.log ε) * Real.exp (-u) := by
    have h_int_subst : ∀ {f : ℝ → ℝ}, ∫ u in Set.Ioi 0, f u = ∫ u in Set.Ioi 0, f (u / ε) * (1 / ε) := by
      intro f; rw [ MeasureTheory.integral_mul_const ] ; simp +decide [ div_eq_inv_mul, MeasureTheory.integral_const_mul, hε.ne' ] ;
      rw [ mul_comm, MeasureTheory.integral_comp_mul_left_Ioi ] <;> norm_num [ hε.ne' ];
      positivity;
    rw [ h_int_subst, ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; rw [ ← Real.log_div ( ne_of_gt hu ) ( ne_of_gt hε ) ] ; ring;
    norm_num [ hε.ne' ];
  simp_all +decide [ sub_mul ];
  rw [ MeasureTheory.integral_sub, h_int ];
  · rw [ MeasureTheory.integral_const_mul, integral_exp_neg_Ioi ] ; norm_num [ hε.ne' ];
  · contrapose! h_int;
    rw [ MeasureTheory.integral_undef h_int ] ; norm_num;
    grind +suggestions;
  · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) _

/-
Key computation: the weighted sum of log log with Dirichlet weights tends to
-γ - log ε as ε → 0+. Uses Γ'(1) = -γ.
-/
lemma loglog_dirichlet_sum_tendsto :
    Tendsto (fun ε : ℝ =>
      (∑' n : ℕ, (if n ≥ 2 then
        Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
      else 0)) + Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (-Real.eulerMascheroniConstant)) := by
  -- By definition of $S(ε)$, we can write it as $T(ε) + \log ε(1 - 2^{-ε})$.
  have h_decomp : ∀ ε : ℝ, 0 < ε → (∑' n : ℕ, if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε = (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε * (1 - (2 : ℝ) ^ (-ε)) := by
    intro ε hε
    have h_split : (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑' n : ℕ, if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + (∑' n : ℕ, if n ≥ 2 then Real.log ε * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      rw [ ← Summable.tsum_add ];
      · congr with n ; split_ifs <;> simp_all +decide [ Real.log_mul, ne_of_gt ] ; ring;
        rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.log_pos ( by norm_cast ) ) ) ] ; ring;
      · -- Since $\log(\log n)$ is bounded for $n \geq 2$, we can apply the comparison test.
        have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log (Real.log n)| ≤ C * n ^ (ε / 2) := by
          have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log (Real.log n)| ≤ C * Real.log n := by
            use 1;
            intro n hn; rw [ abs_le ] ; constructor <;> norm_num;
            · rw [ ← Real.log_inv ];
              exact Real.log_le_log ( by positivity ) ( by nlinarith [ Real.log_inv ( n : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), show ( n : ℝ ) ≥ 2 by norm_cast ] );
            · exact le_trans ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by norm_cast ) ) ) ( by linarith );
          have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → Real.log n ≤ C * (n : ℝ) ^ (ε / 2) := by
            use 2 / ε;
            intro n hn; rw [ div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ] ; have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ^ ( ε / 2 ) ) ; rw [ Real.log_rpow ( by positivity ) ] at this; ring_nf at *; nlinarith;
          obtain ⟨ C₁, hC₁ ⟩ := ‹∃ C₁ : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log ( Real.log n )| ≤ C₁ * Real.log n›
          obtain ⟨ C₂, hC₂ ⟩ := h_bounded
          use C₁ * C₂;
          intro n hn; convert le_trans ( hC₁ n hn ) ( mul_le_mul_of_nonneg_left ( hC₂ n hn ) ( show 0 ≤ C₁ by have := hC₁ 2 ( by norm_num ) ; norm_num at this ; nlinarith [ abs_le.mp this, Real.log_pos one_lt_two ] ) ) using 1 ; ring;
        obtain ⟨ C, hC ⟩ := h_bounded;
        have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then C * (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
            have h_bound : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) ≤ ε * (n : ℝ) ^ (-1 - ε / 2) := by
              intro n hn
              have h_bound : (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε * (n : ℝ) ^ (-1 - ε) := by
                have h_bound : (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε * (n : ℝ) ^ (-1 - ε) := by
                  have h_mean_val : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), deriv (fun x => x ^ (-ε)) c = ((n + 1 : ℝ) ^ (-ε) - (n : ℝ) ^ (-ε)) / ((n + 1 : ℝ) - (n : ℝ)) := by
                    have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
                    exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] )
                  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_val; norm_num [ show c ≠ 0 by linarith [ hc₁.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ] at hc₂ ⊢;
                  rw [ show ( -1 - ε : ℝ ) = -ε - 1 by ring ];
                  nlinarith [ show ( n : ℝ ) ^ ( -ε - 1 ) ≥ c ^ ( -ε - 1 ) by rw [ ge_iff_le ] ; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc₁.1, hc₁.2, show ( n : ℝ ) ≥ 2 by norm_cast ] ];
                exact h_bound;
              convert mul_le_mul_of_nonneg_left h_bound ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( ε / 2 ) ) using 1 ; ring;
              rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring
            have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then ε * (n : ℝ) ^ (-1 - ε / 2) else 0) := by
              rw [ ← summable_nat_add_iff 2 ];
              simpa using Summable.mul_left _ <| Real.summable_nat_rpow.2 ( by linarith ) |> Summable.comp_injective <| add_left_injective 2;
            refine' h_comparison.of_nonneg_of_le _ _;
            · intro n; split_ifs <;> first | positivity | exact mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
            · grind;
          convert h_comparison.mul_left C using 2 ; split_ifs <;> ring;
        -- Apply the comparison test with the summable series.
        have h_comparison_test : ∀ n : ℕ, |if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0| ≤ |if n ≥ 2 then C * (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0| := by
          intro n; split_ifs <;> norm_num [ abs_mul ];
          exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( show 0 ≤ C by have := hC 2 ( by norm_num ) ; norm_num at this ; nlinarith [ abs_le.mp this, Real.rpow_pos_of_pos zero_lt_two ( ε / 2 ) ] ), abs_of_nonneg ( show 0 ≤ ( n : ℝ ) ^ ( ε / 2 ) by positivity ) ] ; exact hC n ‹_› ) ( abs_nonneg _ );
        -- Apply the comparison test with the summable series to conclude that the original series is summable.
        have h_comparison_test : Summable (fun n : ℕ => |if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0|) := by
          exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_comparison_test n ) ( h_comparison.abs );
        exact h_comparison_test.of_abs;
      · rw [ ← summable_nat_add_iff 2 ];
        -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
        have h_telescoping : Summable (fun n : ℕ => (n + 2 : ℝ) ^ (-ε) - (n + 3 : ℝ) ^ (-ε)) := by
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - (n + 3 : ℝ) ^ (-ε)) = (2 : ℝ) ^ (-ε) - (N + 2 : ℝ) ^ (-ε) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) );
          · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
        convert h_telescoping.mul_left ( Real.log ε ) using 2 ; norm_num [ add_assoc ];
    have h_sum : ∑' n : ℕ, (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = 2 ^ (-ε) := by
      have h_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) Filter.atTop (nhds (2 ^ (-ε))) := by
        have h_sum : ∀ N : ℕ, N ≥ 2 → ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = 2 ^ (-ε) - (N + 1) ^ (-ε) := by
          intro N hN; induction hN <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
          rw [ if_pos ( by linarith ) ] ; ring;
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ici_mem_atTop 2 ) h_sum ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | exact sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
    rw [ h_split, show ( ∑' n : ℕ, if n ≥ 2 then Real.log ε * ( ( n : ℝ ) ^ ( -ε ) - ( n + 1 ) ^ ( -ε ) ) else 0 ) = Real.log ε * ( ∑' n : ℕ, if n ≥ 2 then ( ( n : ℝ ) ^ ( -ε ) - ( n + 1 ) ^ ( -ε ) ) else 0 ) by rw [ ← tsum_mul_left ] ; exact tsum_congr fun n => by split_ifs <;> ring ] ; rw [ h_sum ] ; ring;
  -- By the properties of the Riemann sum and the integral, we know that the difference between the sum and the integral tends to zero.
  have h_diff_zero : Filter.Tendsto (fun ε : ℝ => (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) - (-Real.eulerMascheroniConstant)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_riemann_sum : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), |(∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) - (-Real.eulerMascheroniConstant)| ≤ (∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) + ε * (∑' n : ℕ, if n ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
      filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with ε hε using riemann_sum_bound ε hε.1 hε.2.le;
    have h_integral_zero : Filter.Tendsto (fun ε : ℝ => ∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := integral_log_exp_near_zero_tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => ε * Real.log 2 ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) from Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr <| by intros x hx; exact mul_pos hx.out <| Real.log_pos one_lt_two ) ; aesop;
    exact squeeze_zero_norm' h_riemann_sum ( by simpa using h_integral_zero.add ( Filter.Tendsto.mul ( Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds ) );
  have := h_diff_zero.add ( log_eps_one_minus_rpow_tendsto );
  simpa using this.sub_const ( Real.eulerMascheroniConstant ) |> Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_decomp x hx ] ; ring )

/-
The key identification: the Meissel-Mertens constant equals γ - H.
-/
set_option maxHeartbeats 800000 in
theorem meisselMertens_eq_euler_mascheroni_sub_mertensH :
    ∀ M : ℝ, Tendsto (fun N : ℕ => ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      1 / (p : ℝ) - Real.log (Real.log N)) atTop (𝓝 M) →
    M = Real.eulerMascheroniConstant - mertensH_val := by
  -- Let $A(N) = \sum_{p \leq N} \frac{1}{p}$ and $r(n) = A(n) - \log \log n - M$.
  intros M hM
  set A : ℕ → ℝ := fun N => ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (1 / (p : ℝ))
  set r : ℕ → ℝ := fun n => A n - Real.log (Real.log (n : ℝ)) - M;
  -- From the Abel summation result, we have $P(1+ε) = M \cdot 2^{-ε} + \sum r(n) \cdot (n^{-ε} - (n+1)^{-ε}) + \sum (\log \log n) \cdot (n^{-ε} - (n+1)^{-ε})$.
  have h_abel : ∀ ε > 0, primeZetaReal (1 + ε) = M * 2⁻¹ ^ ε + ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + ∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
    intro ε hε_pos
    have h_abel : primeZetaReal (1 + ε) = ∑' n : ℕ, (if n ≥ 2 then A n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      convert abel_summation_primeZeta ε hε_pos using 1;
    -- Split the sum into three parts: the term involving $M$, the term involving $r(n)$, and the term involving $\log \log n$.
    have h_split : ∑' n : ℕ, (if n ≥ 2 then A n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑' n : ℕ, (if n ≥ 2 then M * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
      rw [ ← Summable.tsum_add, ← Summable.tsum_add ] ; congr ; ext n ; split_ifs <;> ring;
      · have h_summable : Summable (fun n : ℕ => (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0)) := by
          rw [ ← summable_nat_add_iff 2 ];
          -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · norm_num [ h_telescoping ];
            exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop ( by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
          · exact fun n => by rw [ if_pos ( by linarith ) ] ; exact sub_nonneg_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
        have h_summable_r : Summable (fun n : ℕ => (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
          have h_bounded : ∃ C, ∀ n ≥ 2, |r n| ≤ C := by
            have := hM.sub_const M;
            exact ⟨ _, fun n hn => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩;
          obtain ⟨ C, hC ⟩ := h_bounded;
          have h_summable : Summable (fun n : ℕ => if n ≥ 2 then C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| else 0) := by
            convert h_summable.abs.mul_left C using 2 ; aesop;
          -- Since $|r n| \leq C$ for $n \geq 2$, we can apply the comparison test.
          have h_comparison : ∀ n ≥ 2, |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| := by
            exact fun n hn => by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( hC n hn ) ( abs_nonneg _ ) ;
          have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
            exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> first | positivity | exact h_comparison n ‹_› ) h_summable;
          exact Summable.of_norm <| by convert h_comparison using 1; ext n; split_ifs <;> norm_num;
        exact Summable.add ( by simpa [ mul_sub ] using h_summable.mul_left M ) h_summable_r;
      · -- We'll use the fact that if the series $\sum_{n=2}^{\infty} a_n$ converges absolutely, then the series $\sum_{n=2}^{\infty} |a_n|$ also converges.
        have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then |Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
          -- We'll use the fact that if the series $\sum_{n=2}^{\infty} a_n$ converges absolutely, then the series $\sum_{n=2}^{\infty} |a_n|$ also converges. Hence, we need to show that $\sum_{n=2}^{\infty} |\log \log n \cdot (n^{-\epsilon} - (n+1)^{-\epsilon})|$ converges.
          have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then |Real.log (Real.log (n : ℝ))| * (n : ℝ) ^ (-ε - 1) else 0) := by
            -- We'll use the fact that |log log n| grows slower than any polynomial function.
            have h_log_log_growth : ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| ≤ C * (n : ℝ) ^ (ε / 2) := by
              have h_log_log_growth : ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| ≤ C * (n : ℝ) ^ (ε / 2) := by
                have h_log_log_growth_aux : Filter.Tendsto (fun n : ℕ => |Real.log (Real.log (n : ℝ))| / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                  -- We can use the fact that $|\log \log n| \leq \log n$ for all $n \geq 2$.
                  have h_log_log_bound : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                    -- We can use the fact that $\frac{\log \log n}{n^{\epsilon/2}}$ tends to $0$ as $n$ tends to infinity.
                    have h_log_log_div_n_eps : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                      -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y \cdot \frac{\epsilon}{2}}}$.
                      suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * (ε / 2))) Filter.atTop (nhds 0) by
                        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
                        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ), mul_comm ] );
                      -- Let $z = y \cdot \frac{\epsilon}{2}$, therefore the expression becomes $\frac{2z}{\epsilon e^z}$.
                      suffices h_z : Filter.Tendsto (fun z : ℝ => 2 * z / (ε * Real.exp z)) Filter.atTop (nhds 0) by
                        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < ε / 2 by positivity ) ) using 2 ; norm_num ; ring;
                        norm_num [ mul_assoc, mul_comm ε, hε_pos.ne' ];
                      -- We can factor out the constant $2 / \epsilon$ from the limit.
                      suffices h_factor : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
                        convert h_factor.const_mul ( 2 / ε ) using 2 <;> ring;
                      simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
                    refine' squeeze_zero_norm' _ h_log_log_div_n_eps;
                    filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos <| Real.log_pos <| by norm_cast; linarith ) <| by norm_num ) <| by positivity;
                  exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa [ abs_div, abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] using h_log_log_bound.norm )
                have := h_log_log_growth_aux.bddAbove_range;
                exact ⟨ this.choose, fun n hn => by rw [ ← div_le_iff₀ ( by positivity ) ] ; exact this.choose_spec ⟨ n, rfl ⟩ ⟩;
              exact h_log_log_growth;
            obtain ⟨ C, hC ⟩ := h_log_log_growth;
            -- Using the bound from hC, we can show that the series is dominated by a convergent p-series.
            have h_dominate : ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| * (n : ℝ) ^ (-ε - 1) ≤ C * (n : ℝ) ^ (-ε / 2 - 1) := by
              intro n hn; convert mul_le_mul_of_nonneg_right ( hC n hn ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( -ε - 1 ) ) using 1 ; rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring;
            rw [ ← summable_nat_add_iff 2 ];
            exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by simpa using h_dominate ( n + 2 ) ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_nat_rpow.2 <| by linarith );
          -- We'll use the fact that $|n^{-\epsilon} - (n+1)^{-\epsilon}| \leq \epsilon n^{-\epsilon-1}$ for all $n \geq 2$.
          have h_bound : ∀ n : ℕ, n ≥ 2 → |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| ≤ ε * (n : ℝ) ^ (-ε - 1) := by
            -- We'll use the mean value theorem to bound the difference.
            intros n hn
            have h_mean_value : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) = ε * c ^ (-ε - 1) := by
              have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
              norm_num +zetaDelta at *;
              exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by norm_num [ show c ≠ 0 by linarith ] at *; linarith ⟩;
            obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value; rw [ hc₂, abs_mul, abs_of_nonneg hε_pos.le ] ;
            rw [ abs_of_nonneg ( Real.rpow_nonneg ( by linarith [ hc₁.1 ] ) _ ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc₁.1, hc₁.2, show ( n : ℝ ) ≥ 2 by norm_cast ] ) hε_pos.le;
          refine' .of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( h_abs_conv.mul_left ε );
          · positivity;
          · split_ifs <;> simp_all +decide [ abs_mul, mul_assoc, mul_comm, mul_left_comm ];
            simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_bound n ‹_› ) ( abs_nonneg _ );
        -- Since the absolute value of the series is summable, the original series must also be summable.
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          have := h_abs_conv
          rw [ ← summable_nat_add_iff 2 ] at *;
          exact Summable.of_norm <| by simpa using this;
        convert h_summable using 1;
      · rw [ ← summable_nat_add_iff 2 ];
        -- The series $\sum_{n=2}^{\infty} \left( \frac{1}{n^{\epsilon}} - \frac{1}{(n+1)^{\epsilon}} \right)$ is a telescoping series.
        have h_telescoping : Summable (fun n : ℕ => ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε))) := by
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) );
          · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
        simpa using h_telescoping.mul_left M;
      · have h_bounded : ∃ C, ∀ n ≥ 2, |r n| ≤ C := by
          have := hM.sub_const M;
          exact ⟨ _, fun n hn => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩;
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) := by
          rw [ ← summable_nat_add_iff 2 ];
          -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · norm_num [ h_telescoping ];
            exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( by simpa using tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
          · exact fun n => by rw [ if_pos ( by linarith ) ] ; exact sub_nonneg_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
        obtain ⟨ C, hC ⟩ := h_bounded;
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| else 0) := by
          convert h_summable.abs.mul_left C using 2 ; aesop;
        -- Since $|r n| \leq C$ for $n \geq 2$, we can apply the comparison test.
        have h_comparison : ∀ n ≥ 2, |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| := by
          exact fun n hn => by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( hC n hn ) ( abs_nonneg _ ) ;
        have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
          exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> first | positivity | exact h_comparison n ‹_› ) h_summable;
        exact Summable.of_norm <| by convert h_comparison using 1; ext n; split_ifs <;> norm_num;
    -- Evaluate the sum $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$.
    have h_sum : ∑' n : ℕ, (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) = 2⁻¹ ^ ε := by
      have h_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0)) Filter.atTop (nhds (2⁻¹ ^ ε)) := by
        have h_sum : ∀ N : ℕ, N ≥ 2 → ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) = 2⁻¹ ^ ε - ((N + 1) : ℝ) ^ (-ε) := by
          intro N hN; induction hN <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
          · norm_num [ Real.rpow_neg, Real.div_rpow ];
          · rw [ if_pos ( by linarith ) ] ; ring;
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ici_mem_atTop 2 ) h_sum ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | rw [ Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; exact sub_nonneg_of_le <| inv_anti₀ ( by positivity ) <| Real.rpow_le_rpow ( by positivity ) ( by linarith ) <| by positivity;
    rw [ ← h_sum, ← tsum_mul_left ] ; aesop;
  -- From the abelian theorem, we have $\sum r(n) \cdot (n^{-ε} - (n+1)^{-ε}) \to 0$ as $\epsilon \to 0+$.
  have h_abelian : Filter.Tendsto (fun ε : ℝ => ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- Since $r(n)$ is bounded and converges to $0$, we can apply the abelian theorem.
    have hr_bdd : ∃ C, ∀ n, |r n| ≤ C := by
      have := hM.sub_const M;
      exact ⟨ _, fun n => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩
    have hr_lim : Filter.Tendsto r Filter.atTop (nhds 0) := by
      convert hM.sub_const M using 2 ; ring!
    exact abelian_theorem_bounded_convergent r hr_bdd hr_lim;
  -- From the loglog_dirichlet_sum_tendsto, we have $\sum (\log \log n) \cdot (n^{-ε} - (n+1)^{-ε}) + \log ε \to -\gamma$ as $\epsilon \to 0+$.
  have h_loglog : Filter.Tendsto (fun ε : ℝ => ∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
    convert loglog_dirichlet_sum_tendsto using 1;
  -- From the primeZeta_plus_log_tendsto, we have $P(1+ε) + \log ε \to -mertensH_val$ as $\epsilon \to 0+$.
  have h_primeZeta : Filter.Tendsto (fun ε : ℝ => primeZetaReal (1 + ε) + Real.log ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-mertensH_val)) := by
    convert primeZeta_plus_log_tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => 1 + ε ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin 1 ( Set.Ioi 1 ) ) from ?_ ) using 2;
    · norm_num;
    · rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
  -- By combining the results from h_abel, h_abelian, and h_loglog, we get:
  have h_combined : Filter.Tendsto (fun ε : ℝ => M * 2⁻¹ ^ ε + (∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-mertensH_val)) := by
    exact h_primeZeta.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_abel x hx ] ; ring );
  have := tendsto_nhds_unique h_combined ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) ( by norm_num ) ) ) h_abelian ) h_loglog ) ; norm_num at this ; linarith;

end


noncomputable section

/-! ### Definitions -/

/-- The product of `(1 - 1/p)` over primes `p ≤ N`. -/
def mertensProd (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The sum of `1/p` over primes `p ≤ N`. -/
def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, 1 / (p : ℝ)

/-- The "tail" terms: for each prime `p ≤ N`, the sum `∑_{k≥2} 1/(k·p^k)`.
This is `log(1/(1-1/p)) - 1/p`. -/
def mertensTail (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-- Mertens' constant H = lim_{N→∞} mertensTail N. -/
def mertensH' : ℝ := ∑' (p : Nat.Primes), (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-! ### Key lemma: relating log of product to sums -/

/-
For a prime p ≥ 2, we have 0 < 1 - 1/p < 1 and 1 - 1/p > 0.
-/
lemma one_sub_inv_prime_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  exact sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr hp.one_lt ) )

/-
The log of the product equals the sum of logs.
-/
lemma log_mertensProd (N : ℕ) :
    Real.log (mertensProd N) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ)) := by
  rw [ mertensProd, Real.log_prod ];
  exact fun p hp => ne_of_gt <| one_sub_inv_prime_pos p <| Finset.mem_filter.mp hp |>.2

/-
Decompose log(1-1/p) = -1/p + (log(1/(1-1/p)) - 1/p) but with different sign.
-/
lemma log_mertensProd_eq (N : ℕ) :
    Real.log (mertensProd N) = -(primeReciprocalSum N) - mertensTail N := by
  unfold mertensProd primeReciprocalSum mertensTail;
  rw [ Real.log_prod ];
  · simp +zetaDelta at *;
    ring;
  · exact fun x hx => sub_ne_zero_of_ne <| by aesop;

/-! ### The tail converges -/

/-
The tail mertensTail N converges to mertensH' as N → ∞.
-/
lemma mertensTail_tendsto :
    Tendsto mertensTail atTop (𝓝 mertensH') := by
  -- We'll use the fact that mertensTail N is a partial sum of a convergent series.
  have h_series : Summable (fun p : Nat.Primes => (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))) := by
    -- We'll use the fact that $\log(1 + x) \leq x$ for $0 < x < 1$ to bound the terms of the series.
    have h_log_bound : ∀ p : Nat.Primes, Real.log (1 + (1 / ((p : ℝ) - 1))) - 1 / (p : ℝ) ≤ 1 / ((p : ℝ) * (p - 1)) := by
      -- Using the inequality $\log(1 + x) \leq x$ for $x > -1$, we get $\log(1 + 1/(p-1)) \leq 1/(p-1)$.
      have h_log_le : ∀ p : Nat.Primes, Real.log (1 + 1 / ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 1) := by
        exact fun p => le_trans ( Real.log_le_sub_one_of_pos ( by exact add_pos zero_lt_one ( one_div_pos.mpr ( sub_pos.mpr ( Nat.one_lt_cast.mpr p.prop.one_lt ) ) ) ) ) ( by norm_num );
      intro p; convert sub_le_sub ( h_log_le p ) le_rfl using 1 ; rw [ div_sub_div ] <;> ring <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ;
    -- Since $\sum_{p \text{ prime}} \frac{1}{p(p-1)}$ converges, we can apply the comparison test.
    have h_summable : Summable (fun p : Nat.Primes => 1 / ((p : ℝ) * (p - 1))) := by
      -- We can compare our series with the convergent p-series $\sum_{p \text{ prime}} \frac{1}{p^2}$.
      have h_comparison : ∀ p : Nat.Primes, 1 / ((p : ℝ) * (p - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
        intro p; rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ;
      exact Summable.of_nonneg_of_le ( fun p => one_div_nonneg.mpr <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr p.2.pos ) ( fun p => h_comparison p ) <| Summable.mul_left _ <| by simpa using Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _;
    refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_summable;
    · rcases p with ⟨ p, hp ⟩ ; norm_num [ hp.ne_zero ];
      exact le_trans ( by norm_num ) ( neg_le_neg ( Real.log_le_sub_one_of_pos ( sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hp.one_lt ) ) );
    · convert h_log_bound p using 1 ; ring;
      rw [ show ( 1 - ( p : ℝ ) ⁻¹ ) = ( p - 1 : ℝ ) / p by rw [ sub_div, inv_eq_one_div, div_self ( Nat.cast_ne_zero.mpr p.2.ne_zero ) ] ] ; norm_num ; ring;
      exact congrArg Real.log ( by linarith [ inv_mul_cancel₀ ( show ( -1 + p : ℝ ) ≠ 0 from by linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ) ] );
  convert h_series.hasSum.comp _;
  rotate_left;
  use fun N => Finset.filter ( fun p : Nat.Primes => p.val ≤ N ) ( Finset.subtype ( fun p : ℕ => Nat.Prime p ) ( Finset.range ( N + 1 ) ) );
  · refine' Filter.tendsto_atTop_atTop.mpr _;
    exact fun s => ⟨ s.sup ( fun p => p.val ), fun n hn => Finset.le_iff_subset.mpr fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_subtype.mpr <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_trans ( Finset.le_sup ( f := fun p : Primes => p.val ) hp ) hn, le_trans ( Finset.le_sup ( f := fun p : Primes => p.val ) hp ) hn ⟩ ⟩;
  · ext;
    refine' Finset.sum_bij ( fun p hp => ⟨ p, _ ⟩ ) _ _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
    · exact fun a ha ha' => Finset.mem_subtype.mpr ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ha ) );
    · grind;
    · exact fun b hb hb' => ⟨ b, ⟨ hb', b.2 ⟩, rfl ⟩

/-! ### Mertens' second theorem -/

/-- **Mertens' second theorem**: The sum of prime reciprocals up to N
satisfies ∑_{p≤N} 1/p - log(log N) → M, where M is the Meissel–Mertens constant. -/
def meisselMertensConstant : ℝ := eulerMascheroniConstant - mertensH'

/-- The remaining deep step: identifying the limit of ∑ 1/p - log log N as γ - H.
From `prime_reciprocal_sum_convergence`, we know convergence to SOME limit M.
The identification M = γ - H requires connecting the Euler product to the
harmonic series / Euler-Mascheroni constant. -/
lemma mertens_second_theorem :
    Tendsto (fun N : ℕ => primeReciprocalSum N - Real.log (Real.log N))
      atTop (𝓝 meisselMertensConstant) := by
  obtain ⟨M, hM⟩ := prime_reciprocal_sum_convergence
  have hM_eq : M = eulerMascheroniConstant - mertensH' := by
    exact meisselMertens_eq_euler_mascheroni_sub_mertensH M hM
  rw [show meisselMertensConstant = M from by rw [hM_eq]; rfl]
  exact hM

/-! ### Main theorem: Mertens' third theorem (Equation 15) -/

/-
**Equation 15 (Mertens, 1874).** Mertens' third theorem:
the product `∏_{p ≤ N} (1 - 1/p)` is asymptotic to `e^{-γ} / ln N`,
where `γ` is the Euler–Mascheroni constant. Equivalently,
`∏_{p ≤ N} (1 - 1/p) · ln N → e^{-γ}` as `N → ∞`.
-/
theorem mertens_equation_15 :
    Tendsto (fun N : ℕ => mertensProd N * Real.log N)
      atTop (𝓝 (Real.exp (-eulerMascheroniConstant))) := by
  -- From `log_mertensProd_eq`, we have:
  have h_log_prod : Filter.Tendsto (fun N : ℕ => Real.log (mertensProd N) + Real.log (Real.log N)) Filter.atTop (nhds (-eulerMascheroniConstant)) := by
    have := mertens_second_theorem;
    convert Filter.Tendsto.add ( this.neg ) ( mertensTail_tendsto.neg ) using 2 <;> norm_num [ log_mertensProd_eq ] ; ring!;
    unfold meisselMertensConstant; ring;
  convert h_log_prod.exp.congr' _ using 2;
  · rw [ Real.exp_eq_exp_ℝ ];
  · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN;
    rw [ ← Real.exp_eq_exp_ℝ, Real.exp_add, Real.exp_log, Real.exp_log ] <;> norm_cast;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr hN;
    · exact Finset.prod_pos fun p hp => one_sub_inv_prime_pos p <| Finset.mem_filter.mp hp |>.2

end


end Mertens
