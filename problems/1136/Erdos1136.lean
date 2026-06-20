import Mathlib

namespace Erdos1136


open Finset Nat

/-!
# Sum-free sets avoiding power-of-2 sums

We prove that:
1. The set A of positive integers whose odd part is ≡ 3 (mod 4) has the property that
   no two elements (possibly equal) sum to a power of 2.
2. A has natural density 1/2 (proved using an injection argument showing the complement
   of A minus powers of 2 injects into A).
3. Any set of positive integers with this sum-free property has upper density ≤ 1/2
   (shown by proving 2|B| ≤ n for any sum-free B ⊆ {1,...,n}).
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- The set of positive integers whose odd part is ≡ 3 (mod 4).
    Equivalently, n is in A iff n ≡ 3 · 2^i (mod 2^{i+2}) for some i ≥ 0. -/
def A : Set ℕ := {n : ℕ | ∃ i q : ℕ, n = 2 ^ i * (4 * q + 3)}

noncomputable instance : DecidablePred (· ∈ A) := Classical.decPred _

/-- Counting function: |S ∩ {1,...,n}| -/
noncomputable def countIn (S : Set ℕ) (n : ℕ) : ℕ :=
  @Finset.card ℕ ((Finset.Icc 1 n).filter (fun x => @decide (x ∈ S) (Classical.dec _)))

/-- A set is power-of-2 sum-free if no two elements sum to a power of 2. -/
def pow2SumFree (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ k : ℕ, a + b ≠ 2 ^ k

-- ============================================================================
-- Step 2: A is sum-free (no two elements sum to a power of 2)
-- ============================================================================

/-- A product 2^i * m where m is odd and m ≥ 3 is never a power of 2. -/
lemma pow2_mul_odd_ne_pow2 (i m : ℕ) (hm_odd : Odd m) (hm_ge : 3 ≤ m)
    (k : ℕ) : 2 ^ i * m ≠ 2 ^ k := by
  by_contra h_contra
  have h_div : 2 ^ (k - i) = m := by
    exact mul_left_cancel₀ (pow_ne_zero i two_ne_zero)
      (by rw [← pow_add, Nat.add_sub_of_le (le_of_not_gt fun hi => by
        nlinarith [pow_pos (zero_lt_two' ℕ) i,
          pow_lt_pow_right₀ (show 1 < 2 by decide) hi]), h_contra])
  grind

/-- Same-level case: sum has odd factor ≥ 3 -/
lemma sum_same_level_ne_pow2 (i p q : ℕ) (k : ℕ) :
    2 ^ i * (4 * p + 3) + 2 ^ i * (4 * q + 3) ≠ 2 ^ k := by
  have h_sum : 2 ^ i * (4 * p + 3) + 2 ^ i * (4 * q + 3) =
      2 ^ (i + 1) * (2 * (p + q) + 3) := by ring
  by_contra h_contra
  have h_odd : Odd (2 * (p + q) + 3) ∧ 3 ≤ 2 * (p + q) + 3 := by grind
  exact absurd (pow2_mul_odd_ne_pow2 (i + 1) (2 * (p + q) + 3) h_odd.1 h_odd.2 k) (by aesop)

/-- Different-level case: sum has odd factor ≥ 3 -/
lemma sum_diff_level_ne_pow2 (i j p q : ℕ) (h : i < j) (k : ℕ) :
    2 ^ i * (4 * p + 3) + 2 ^ j * (4 * q + 3) ≠ 2 ^ k := by
  have h_factor : 2 ^ i * (4 * p + 3) + 2 ^ j * (4 * q + 3) =
      2 ^ i * ((4 * p + 3) + 2 ^ (j - i) * (4 * q + 3)) := by
    rw [show j = i + (j - i) by rw [Nat.add_sub_cancel' h.le]]; ring_nf
    norm_num
  by_contra h_contra
  have h_inner_odd : Odd ((4 * p + 3) + 2 ^ (j - i) * (4 * q + 3)) := by grind
  have h_inner_ge : 3 ≤ (4 * p + 3) + 2 ^ (j - i) * (4 * q + 3) := by grind
  apply pow2_mul_odd_ne_pow2 i (4 * p + 3 + 2 ^ (j - i) * (4 * q + 3))
    h_inner_odd h_inner_ge k
  aesop

/-- **Step 2**: A is sum-free — no two elements of A sum to a power of 2. -/
theorem A_sumfree : ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k := by
  intro a ha b hb k
  obtain ⟨ia, pa, rfl⟩ := ha
  obtain ⟨ib, pb, rfl⟩ := hb
  rcases lt_trichotomy ia ib with h | rfl | h
  · exact sum_diff_level_ne_pow2 ia ib pa pb h k
  · exact sum_same_level_ne_pow2 ia pa pb k
  · rw [add_comm]; exact sum_diff_level_ne_pow2 ib ia pb pa h k

-- ============================================================================
-- Step 3: Optimality — any sum-free B ⊆ {1,...,n} has 2|B| ≤ n
-- ============================================================================

/-
If B ⊆ Icc (P-n) n is sum-free where P = 2^{l+1} and 2^l ≤ n < P,
then |B| ≤ n - 2^l.
-/
lemma pairing_bound (n l : ℕ) (hl : 2 ^ l ≤ n) (hn : n < 2 ^ (l + 1))
    (B : Finset ℕ) (hB : B ⊆ Finset.Icc (2 ^ (l + 1) - n) n)
    (hfree : ∀ a ∈ B, ∀ b ∈ B, ∀ k : ℕ, a + b ≠ 2 ^ k) :
    B.card ≤ n - 2 ^ l := by
      -- Define f : ℕ → ℕ by f(j) = if j < 2^l then j else 2^{l+1} - j.
      set f : ℕ → ℕ := fun j => if j < 2^l then j else 2^(l+1) - j;
      -- We show f maps B injectively into Finset.Icc (2^{l+1}-n) (2^l - 1).
      have h_inj : ∀ j ∈ B, f j ∈ Finset.Icc (2^(l+1) - n) (2^l - 1) := by
        grind +splitImp
      have h_inj_on : ∀ j₁ ∈ B, ∀ j₂ ∈ B, f j₁ = f j₂ → j₁ = j₂ := by
        grind
      have h_card : Finset.card B ≤ Finset.card (Finset.Icc (2^(l+1) - n) (2^l - 1)) := by
        exact Finset.card_le_card ( show B.image f ⊆ Finset.Icc ( 2 ^ ( l + 1 ) - n ) ( 2 ^ l - 1 ) from Finset.image_subset_iff.mpr h_inj ) |> le_trans ( by rw [ Finset.card_image_of_injOn h_inj_on ] )
      exact (by
      convert h_card using 1 ; norm_num [ Nat.pow_succ' ] at * ; omega;)

/-
**Step 3**: Any sum-free B ⊆ {1,...,n} satisfies 2|B| ≤ n.
-/
theorem sumfree_card_le : ∀ n : ℕ, ∀ B : Finset ℕ,
    B ⊆ Finset.Icc 1 n →
    (∀ a ∈ B, ∀ b ∈ B, ∀ k : ℕ, a + b ≠ 2 ^ k) →
    2 * B.card ≤ n := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      by_cases hn : n = 0;
      · aesop;
      · -- Let $l = \log_2 n$, so $2^l \le n < 2^{l+1}$.
        obtain ⟨l, hl⟩ : ∃ l, 2^l ≤ n ∧ n < 2^(l+1) := by
          exact ⟨ Nat.log 2 n, Nat.pow_le_of_le_log ( by positivity ) ( by linarith ), Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith ) ⟩;
        -- Let $P = 2^{l+1}$, $m = P - n - 1$. Note $m < n$ since $P \le 2n$.
        set P := 2^(l+1)
        set m := P - n - 1
        have hm_lt_n : m < n := by
          grind;
        -- Split B into B₁ = B.filter (· ≤ m) and B₂ = B.filter (fun x => ¬(x ≤ m)).
        intros B hB hfree
        set B₁ := B.filter (· ≤ m)
        set B₂ := B.filter (fun x => ¬(x ≤ m));
        -- By induction (m < n), 2 * B₁.card ≤ m.
        have hB₁ : 2 * B₁.card ≤ m := by
          apply ih m hm_lt_n B₁;
          · exact fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( hB ( Finset.mem_filter.mp hx |>.1 ) ) |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
          · exact fun a ha b hb k => hfree a ( Finset.filter_subset _ _ ha ) b ( Finset.filter_subset _ _ hb ) k;
        -- By pairing_bound, B₂.card ≤ n - 2^l.
        have hB₂ : B₂.card ≤ n - 2^l := by
          apply pairing_bound n l hl.left hl.right B₂ (by
          simp +zetaDelta at *;
          exact fun x hx => Finset.mem_Icc.mpr ⟨ Nat.le_of_pred_lt ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_Icc.mp ( hB ( Finset.mem_filter.mp hx |>.1 ) ) |>.2 ⟩) (by
          exact fun a ha b hb k => hfree a ( Finset.filter_subset _ _ ha ) b ( Finset.filter_subset _ _ hb ) k);
        -- Combine: 2 * B.card = 2 * B₁.card + 2 * B₂.card ≤ m + 2*(n - 2^l) = (2^{l+1} - n - 1) + 2*(n - 2^l) = n - 1 ≤ n.
        have h_combined : 2 * B.card = 2 * B₁.card + 2 * B₂.card := by
          rw [ ← mul_add, Finset.card_filter_add_card_filter_not ];
        lia

/-
============================================================================
Step 1: Lower bound for |A ∩ {1,...,n}| via injection argument
============================================================================

Every positive integer not in A and not a power of 2 has the form 2^i(4q+1)
    with q ≥ 1.
-/
lemma not_A_classification (n : ℕ) (hn : 0 < n) (hnA : n ∉ A) :
    (∃ k : ℕ, n = 2 ^ k) ∨ (∃ i q : ℕ, 1 ≤ q ∧ n = 2 ^ i * (4 * q + 1)) := by
  -- Use Nat.exists_eq_pow_mul_and_not_dvd to decompose n = 2^e * m where m is odd (¬2 ∣ m).
  obtain ⟨e, m, hm⟩ : ∃ e m : ℕ, n = 2^e * m ∧ Odd m := by
    exact ⟨ Nat.factorization n 2, n / 2 ^ Nat.factorization n 2, by rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ], by rw [ Nat.odd_iff ] ; exact Nat.mod_two_ne_zero.mp fun con => absurd ( Nat.dvd_of_mod_eq_zero con ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by aesop ) ) ⟩;
  -- Since m is odd, m % 4 is either 1 or 3. If m % 4 = 3, write m = 4q + 3, then n = 2^e * (4q + 3) ∈ A, contradicting hnA. So m % 4 = 1.
  by_cases hm3 : m % 4 = 3;
  · exact False.elim <| hnA <| by rw [ hm.1 ] ; exact ⟨ e, m / 4, by nlinarith [ Nat.mod_add_div m 4, Nat.pow_le_pow_right two_pos ( show e ≥ 0 by positivity ) ] ⟩ ;
  · -- If m % 4 = 1, then m = 4q + 1 for some q ≥ 0.
    obtain ⟨q, hq⟩ : ∃ q : ℕ, m = 4 * q + 1 := by
      exact ⟨ m / 4, by obtain ⟨ k, rfl ⟩ := hm.2; omega ⟩;
    by_cases hq1 : q ≥ 1 <;> simp_all +decide;
    exact Or.inr ⟨ e, q, hq1, rfl ⟩

/-
The lower bound: n ≤ 2 * |A ∩ {1,...,n}| + ⌊log₂ n⌋ + 1.
-/
lemma A_count_lower (n : ℕ) :
    n ≤ 2 * countIn A n + Nat.log 2 n + 1 := by
  -- By definition of A, we know that every positive integer not in A and not a power of 2 is of the form 2^i*(4q+1) with q ≥ 1.
  have h_not_A : ∀ x ∈ Finset.Icc 1 n, x ∉ A → x ≠ 0 → (∃ k : ℕ, x = 2 ^ k) ∨ (∃ i q : ℕ, 1 ≤ q ∧ x = 2 ^ i * (4 * q + 1)) := by
    exact fun x hx₁ hx₂ hx₃ => not_A_classification x ( Finset.mem_Icc.mp hx₁ |>.1 ) hx₂;
  -- By definition of $A$, we know that for each $x$ in the set $\{1,...,n\} \setminus A$, there exists a unique $y \in A$ such that $x > y$.
  have h_inj : (Finset.filter (fun x => x ∉ A) (Finset.Icc 1 n)).card ≤ (Finset.filter (fun x => x ∈ A) (Finset.Icc 1 n)).card + (Nat.log 2 n + 1) := by
    -- By definition of $A$, we know that for each $x$ in the set $\{1,...,n\} \setminus A$, there exists a unique $y \in A$ such that $x > y$. Hence, we can pair each element in $\{1,...,n\} \setminus A$ with an element in $A$.
    have h_pair : Finset.filter (fun x => x ∉ A) (Finset.Icc 1 n) ⊆ Finset.image (fun x => 2 ^ (Nat.factorization x 2) * (4 * (Nat.floor ((x / 2 ^ (Nat.factorization x 2) - 1) / 4) + 1) + 1)) (Finset.filter (fun x => x ∈ A) (Finset.Icc 1 n)) ∪ Finset.image (fun k => 2 ^ k) (Finset.range (Nat.log 2 n + 1)) := by
      intro x hx;
      simp +zetaDelta at *;
      rcases h_not_A x hx.1.1 hx.1.2 hx.2 ( by linarith ) with ( ⟨ k, rfl ⟩ | ⟨ i, q, hq, rfl ⟩ );
      · exact Or.inr ⟨ k, Nat.le_log_of_pow_le ( by norm_num ) hx.1.2, rfl ⟩;
      · refine Or.inl ⟨ 2 ^ i * ( 4 * ( q - 1 ) + 3 ), ?_, ?_ ⟩ <;> rcases q with ( _ | q ) <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ];
        · exact ⟨ ⟨ Nat.mul_pos ( pow_pos ( by decide ) _ ) ( by linarith ), by nlinarith [ pow_pos ( by decide : 0 < 2 ) i ] ⟩, ⟨ i, q, rfl ⟩ ⟩;
        · norm_num [ Nat.add_div ];
    refine le_trans ( Finset.card_le_card h_pair ) ?_;
    grind +revert;
  convert add_le_add_left h_inj ( Finset.card ( Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 n ) ) ) using 1 ; simp +arith +decide [ Finset.filter_not, Finset.card_sdiff ];
  · rw [ Finset.inter_eq_left.mpr fun x hx => by aesop ] ; rw [ add_tsub_cancel_of_le ] ; exact le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ;
  · unfold countIn; ring_nf;
    grind

-- ============================================================================
-- Step 1b: A has natural density 1/2
-- ============================================================================

/-- Upper bound on countIn from sumfree_card_le. -/
lemma A_count_upper (n : ℕ) : 2 * countIn A n ≤ n := by
  unfold countIn
  apply sumfree_card_le n
  · exact Finset.filter_subset _ _
  · intro a ha b hb
    have ha' : a ∈ A := by simpa using (Finset.mem_filter.mp ha).2
    have hb' : b ∈ A := by simpa using (Finset.mem_filter.mp hb).2
    exact A_sumfree a ha' b hb'

/-
The ratio (Nat.log 2 n + 1) / (2 * n) tends to 0.
-/
lemma log_div_tends_zero :
    Filter.Tendsto (fun n : ℕ => ((Nat.log 2 n : ℝ) + 1) / (2 * n))
      Filter.atTop (nhds 0) := by
  refine' squeeze_zero_norm' _ _;
  refine' fun n => ( Real.log n / Real.log 2 + 1 : ℝ ) / n;
  · norm_num [ div_eq_mul_inv ];
    refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( by positivity ) ] ; ring_nf ; norm_num;
    nlinarith [ inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ), show ( log 2 n : ℝ ) ≤ Real.log n * ( Real.log 2 ) ⁻¹ by rw [ ← div_eq_mul_inv, le_div_iff₀ ( Real.log_pos one_lt_two ) ] ; nth_rw 1 [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; exact Nat.pow_log_le_self 2 <| by positivity ) ];
  · -- We'll use the fact that $\frac{\log n}{n}$ tends to $0$ as $n$ tends to infinity.
    have h_log : Filter.Tendsto (fun n : ℕ => (Real.log n : ℝ) / n) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
      suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
        exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    convert h_log.div_const ( Real.log 2 ) |> Filter.Tendsto.add <| tendsto_inv_atTop_nhds_zero_nat using 2 <;> ring

/-
A has natural density 1/2.
-/
theorem A_density_half :
    Filter.Tendsto (fun n : ℕ => (countIn A n : ℝ) / n)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  -- To prove the both sides are equal, we can use the fact that if the numerator and denominator of a fraction tend to infinity, the fraction tends to the ratio of the limits.
  suffices h_bot : Filter.Tendsto (fun n ↦ (2 * (countIn A n) : ℝ) / n - 1) Filter.atTop (nhds 0) by
    convert h_bot.add_const 1 |> Filter.Tendsto.div_const <| 2 using 2 <;> ring;
  have log_div_tends_zero : Filter.Tendsto (fun n : ℕ => ((Nat.log 2 n : ℝ) + 1) / n) Filter.atTop (nhds 0) := by
    convert log_div_tends_zero.const_mul 2 using 2 <;> ring;
  refine' squeeze_zero_norm' _ log_div_tends_zero;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
  rw [ Real.norm_eq_abs, abs_le ];
  field_simp;
  constructor <;> linarith [ show ( countIn A n : ℝ ) ≥ 0 by positivity, show ( countIn A n : ℝ ) ≤ n / 2 by exact le_div_iff₀' ( by positivity ) |>.2 <| mod_cast A_count_upper n, show ( n : ℝ ) ≤ 2 * countIn A n + Nat.log 2 n + 1 by exact mod_cast A_count_lower n ]


-- ============================================================================
-- Upper density ≤ 1/2 for any pow2SumFree set
-- ============================================================================

/-
Any pow2SumFree set S satisfies 2 * |S ∩ {1,...,n}| ≤ n for all n.
-/
lemma sumfree_countIn_le (S : Set ℕ) (hS : pow2SumFree S) (n : ℕ) :
    2 * countIn S n ≤ n := by
  convert sumfree_card_le n ( Finset.filter ( fun x => x ∈ S ) ( Finset.Icc 1 n ) ) ?_ ?_ using 1;
  convert rfl;
  rotate_left;
  exact Classical.decPred S;
  · grind;
  · grind +locals;
  · congr;
    grind

/-
The upper density of any pow2SumFree set is at most 1/2.
-/
theorem sumfree_upperDensity_le_half (S : Set ℕ) (hS : pow2SumFree S) :
    Filter.limsup (fun n : ℕ => (countIn S n : ℝ) / ↑n)
      Filter.atTop ≤ 1 / 2 := by
  refine' csInf_le _ _ <;> norm_num;
  · exact ⟨ 0, by rintro x ⟨ n, hn ⟩ ; exact le_trans ( by positivity ) ( hn _ le_rfl ) ⟩;
  · exact ⟨ 1, fun n hn => by rw [ div_le_div_iff₀ ] <;> norm_cast ; linarith [ sumfree_countIn_le S hS n ] ⟩

-- ============================================================================
-- Main result
-- ============================================================================

/-- **Main result**: There exists a set with natural density 1/2 that is
    power-of-2 sum-free, and every power-of-2 sum-free set has upper density
    at most 1/2. -/
theorem main_result :
    (∃ S : Set ℕ, pow2SumFree S ∧
      Filter.Tendsto (fun n : ℕ => (countIn S n : ℝ) / ↑n)
        Filter.atTop (nhds (1 / 2 : ℝ))) ∧
    (∀ S : Set ℕ, pow2SumFree S →
      Filter.limsup (fun n : ℕ => (countIn S n : ℝ) / ↑n)
        Filter.atTop ≤ 1 / 2) :=
  ⟨⟨A, A_sumfree, A_density_half⟩, fun S hS => sumfree_upperDensity_le_half S hS⟩

/-- **Erdős Problem 1136.** Wrapper exposing the site question directly:
there exists `A ⊂ ℕ` with **lower density > 1/3** such that `a + b ≠ 2^k`
for any `a, b ∈ A` and `k ≥ 0`. (In fact `A` has natural density `1/2`,
witnessed by `A_density_half`.) -/
theorem erdos_1136 : ∃ A : Set ℕ,
    (∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k) ∧
    (1/3 : ℝ) < Filter.liminf (fun n : ℕ => (countIn A n : ℝ) / n) Filter.atTop := by
  refine ⟨A, A_sumfree, ?_⟩
  have h_lim := A_density_half.liminf_eq
  rw [h_lim]
  norm_num

#print axioms erdos_1136
-- 'Erdos1136.erdos_1136' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1136
