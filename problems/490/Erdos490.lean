import Mathlib

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos490

/-
# Problem Description

Erdős Problem 490. `erdos_490` is proved unconditionally here: the four explicit Dusart
estimates previously assumed in this repository as the axioms `dusart_chebyshev`,
`dusart_mertens_product`, `dusart_pi_lower` and `dusart_pi_upper` are no longer needed.

The original argument is due to Endre Szemerédi; the formalisation is by plby
(github.com/plby/lean-proofs), file `src/latest/ErdosProblems/Erdos490.lean` with its
36-module import closure.

Flattened single-file vendoring of that closure, in dependency order, with
project-internal imports removed so that `Mathlib` is the only import. Declarations keep
their upstream fully-qualified names, so the utility modules that declare at the Lean root
are emitted with an explicit `_root_.` prefix. Upstream has two different functions both
called `chebyshevPsi` — one at the root taking `ℕ`, one in `Erdos490` taking `ℝ` — which a
single namespace cannot distinguish by bare name, so the root one is renamed `chebyshevPsi'`
here. Two `grind` invocations in the analytic section are replaced by explicit proofs of the
same goals (`field_simp` after supplying positivity facts, and
`Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero`). `grind` searches the ambient
environment, and with all 36 modules in one file it sees far more than the upstream module
did, so it no longer closes those goals; the statements proved are unchanged. That and the
`chebyshevPsi'` rename are the only deviations from upstream text.
-/


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Basic.lean` -/

section


/-! Basic definitions and elementary lemmas for Erdős problem 490.
Extracted from the existing formalization; no custom analytic axioms are imported. -/


noncomputable section


/-- Primes up to x -/
def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

def γ : ℝ := Real.eulerMascheroniConstant

/-- ψ(x) = Chebyshev's second function = ∑_{n ≤ x} Λ(n) -/
def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n

open Finset BigOperators Nat Real

/-- S[p] = {s ∈ S : p ∣ s} -/
def sdiv (S : Finset ℕ) (p : ℕ) : Finset ℕ := S.filter (p ∣ ·)

/-- p⁻¹S[p] = {s/p : s ∈ S, p ∣ s} -/
def sinv (S : Finset ℕ) (p : ℕ) : Finset ℕ := (sdiv S p).image (· / p)

/-- A pair (A,B) is n-admissible if A,B ⊆ [n] and (a,b) ↦ ab is injective on A × B -/
def ProductAdmissible (n : ℕ) (A B : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
    a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/-- Y_{λ,k} = 2λ^k -/
def Y_val (lam : ℝ) (k : ℕ) : ℝ := 2 * lam ^ k

/-- Primes in [Y_{λ,k}, Y_{λ,k+1}), as a Finset. -/
def I_layer (lam : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈Y_val lam k⌉₊ ⌈Y_val lam (k + 1)⌉₊).filter Nat.Prime

/-- N_{λ,k} = |I_{λ,k}| -/
def N_layer (lam : ℝ) (k : ℕ) : ℕ := (I_layer lam k).card

/-- M_{λ,k} = ∏_{p ≤ Y_{λ,k+1}} (1 - 1/p) -/
def M_layer (lam : ℝ) (k : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo (Y_val lam (k + 1)), (1 - 1 / (p : ℝ))

/-- E_{λ,k}(r) = max over T ⊆ I_{λ,k} with |T| ≤ r of ∏_{p∈T} (1-1/p)⁻¹ -/
def E_val (lam : ℝ) (k : ℕ) (r : ℕ) : ℝ :=
  ((I_layer lam k).powerset.filter (·.card ≤ r)).sup'
    ⟨∅, by simp [Finset.mem_filter, Finset.mem_powerset]⟩
    (fun T => ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹)

/-- D_{λ,m} = ∏_k E_{λ,k}(m_k) defined as exp(∑' log E_k(m_k)) -/
def D_val (lam : ℝ) (m : ℕ → ℕ) : ℝ :=
  Real.exp (∑' k, Real.log (E_val lam k (m k)))

/-- F_f(X) = ∑_{m ≤ X} f(m), for f : ℕ → ℝ -/
def F_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m

/-- H_f(X) = ∑_{m ≤ X} f(m)/m -/
def H_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m / (m : ℝ)

/-- L_f(X) = ∑_{m ≤ X} f(m) · log(m) -/
def L_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log (m : ℝ)

/-- f is completely multiplicative with values in {0,1} -/
def CompMult01 (f : ℕ → ℝ) : Prop :=
  (∀ m, f m = 0 ∨ f m = 1) ∧
  f 1 = 1 ∧
  (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b)

/-- L_{λ,k}(A,B) = primes in I_{λ,k} dividing some element of both A and B -/
def L_common (lam : ℝ) (k : ℕ) (A B : Finset ℕ) : Finset ℕ :=
  (I_layer lam k).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)

/-- P_S(n,λ,k) = primes p with Y_{λ,k+1} < p ≤ n/Y_{λ,k} and S[p] = ∅ -/
def P_sieve (n : ℕ) (lam : ℝ) (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime).filter
    (fun p => ¬(sdiv S p).Nonempty)

/-- Π_S(n,λ,k) = ∏_{p ∈ P_S(n,λ,k)} (1 - 1/p) -/
def Pi_sieve (n : ℕ) (lam : ℝ) (k : ℕ) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ P_sieve n lam k S, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 800000 in
-- The finite supremum estimate needs extra heartbeats for generated simplification.

/-- E_val is always ≥ 1 (achieved by the empty subset) -/
lemma E_val_ge_one (lam : ℝ) (k : ℕ) (r : ℕ) : 1 ≤ E_val lam k r := by
  refine le_trans ?_ ( Finset.le_sup' _ <| show ∅ ∈ _ from ?_ ) <;> norm_num

/-- A product over a subset T ⊆ I_k with |T| ≤ r is bounded by E_val -/
lemma prod_le_E_val (lam : ℝ) (k : ℕ) (r : ℕ) (T : Finset ℕ)
    (hT : T ⊆ I_layer lam k) (hcard : T.card ≤ r) :
    ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ ≤ E_val lam k r := by
  refine le_trans ?_ ( Finset.le_sup' _ <| show T ∈ Finset.filter ( fun T => #T ≤ r ) ( Finset.powerset ( I_layer lam k ) ) from ?_ ) <;> simp_all +decide [ Finset.subset_iff ]

/-
Finite partial product (over a Finset) is bounded by D_val
-/
lemma partial_prod_le_D_val (lam : ℝ) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (S : Finset ℕ) :
    ∏ j ∈ S, E_val lam j (m j) ≤ D_val lam m := by
  have hsum :
      ∑ j ∈ S, Real.log (E_val lam j (m j)) ≤
        ∑' k, Real.log (E_val lam k (m k)) := by
    exact Summable.sum_le_tsum _ (fun _ _ => Real.log_nonneg <| E_val_ge_one _ _ _) hsumm
  calc
    ∏ j ∈ S, E_val lam j (m j)
        = Real.exp (∑ j ∈ S, Real.log (E_val lam j (m j))) := by
          rw [Real.exp_sum]
          exact Finset.prod_congr rfl fun _ _ =>
            (Real.exp_log (lt_of_lt_of_le zero_lt_one (E_val_ge_one _ _ _))).symm
    _ ≤ Real.exp (∑' k, Real.log (E_val lam k (m k))) :=
          Real.exp_le_exp.mpr hsum
    _ = D_val lam m := rfl

/-
The primes in (Y_{k+1}, n] that are common to A,B can be decomposed by layer
-/
lemma layer_decomp_common_primes (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (n : ℕ)
    (A B : Finset ℕ) :
    let P := ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ n).filter Nat.Prime).filter
        (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)
    ∀ p ∈ P, ∃ j, k < j ∧ p ∈ I_layer lam j := by
  intro P p hpP
  obtain ⟨j, hj⟩ : ∃ j, Y_val lam j ≤ p ∧ p < Y_val lam (j + 1) := by
    have h_exists_j : ∃ j, Y_val lam j ≤ p ∧ p < Y_val lam (j + 1) := by
      have h_unbounded : ∀ M : ℝ, ∃ j, Y_val lam j > M := by
        exact fun M => by rcases pow_unbounded_of_one_lt ( M / 2 ) hlam with ⟨ j, hj ⟩ ; exact ⟨ j, by rw [ Y_val ] ; linarith ⟩ ;
      contrapose! h_unbounded;
      use p;
      intro j; induction j <;> simp_all +decide [ Y_val ] ;
      exact Nat.Prime.two_le ( Finset.mem_filter.mp ( Finset.mem_filter.mp hpP |>.1 ) |>.2 );
    exact h_exists_j;
  have hj_gt_k : j > k := by
    simp +zetaDelta at *;
    contrapose! hpP;
    intro h₁ h₂; rw [ Nat.floor_lt ] at h₁ <;> linarith [ show ( Y_val lam ( k + 1 ) :ℝ ) ≥ Y_val lam ( j + 1 ) from mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ hlam.le ( by linarith ) ) zero_le_two ] ;
  use j;
  simp +zetaDelta at *;
  exact ⟨ hj_gt_k, Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ Nat.ceil_le.mpr hj.1, Nat.lt_ceil.mpr hj.2 ⟩, hpP.1.2 ⟩ ⟩

/-
Key product inequality for small_interval_case:
    ∏_{p∈P_A} · ∏_{p∈P_B} ≤ ∏_{p∈P_A∪P_B}
-/
lemma prod_union_le_of_le_one {P_A P_B : Finset ℕ}
    (hA : ∀ p ∈ P_A, Nat.Prime p) (hB : ∀ p ∈ P_B, Nat.Prime p) :
    (∏ p ∈ P_A, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_B, (1 - 1 / (p : ℝ))) ≤
    ∏ p ∈ P_A ∪ P_B, (1 - 1 / (p : ℝ)) := by
  have h_prod_union_inter : (∏ p ∈ P_A, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_B, (1 - 1 / (p : ℝ))) = (∏ p ∈ P_A ∪ P_B, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_A ∩ P_B, (1 - 1 / (p : ℝ))) := by
    rw [ ← Finset.prod_union_inter ];
  exact h_prod_union_inter ▸ mul_le_of_le_one_right ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) ( Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity )

/-
Elements of sinv S p are ≤ n/p when S ⊆ Icc 1 n
-/
lemma sinv_le_div {S : Finset ℕ} {p n : ℕ} (hS : S ⊆ Finset.Icc 1 n) (_hp : Nat.Prime p)
    {x : ℕ} (hx : x ∈ sinv S p) : x ≤ n / p := by
  obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hx;
  exact Nat.div_le_div_right ( Finset.mem_Icc.mp ( hS ( Finset.mem_filter.mp hs |>.1 ) ) |>.2 )

/-
Elements of sinv S p are ≥ 1 when S ⊆ Icc 1 n
-/
lemma sinv_pos {S : Finset ℕ} {n p : ℕ} (hS : S ⊆ Finset.Icc 1 n) (hp : Nat.Prime p)
    {x : ℕ} (hx : x ∈ sinv S p) : 1 ≤ x := by
  obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hx;
  exact Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( hS ( Finset.mem_filter.mp hs |>.1 ) ) |>.1 ) ( Finset.mem_filter.mp hs |>.2 ) ) hp.pos

/-
If p ∈ I_layer lam k and r ∈ P_sieve n lam k S (so r > Y_{k+1} > p),
    then r does not divide any element of sinv S p.
-/
lemma sieve_prime_not_dvd_sinv {S : Finset ℕ} {n : ℕ} {lam : ℝ} {k : ℕ}
    (_hS : S ⊆ Finset.Icc 1 n) (_hlam : 1 < lam)
    {p : ℕ} (_hp : p ∈ I_layer lam k) (_hp_sdiv : (sdiv S p).Nonempty)
    {r : ℕ} (hr : r ∈ P_sieve n lam k S)
    {x : ℕ} (hx : x ∈ sinv S p) : ¬(r ∣ x) := by
  unfold sinv at hx; simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ a, ha, rfl ⟩ := hx; simp_all +decide [ sdiv, P_sieve ] ;
  exact fun h => hr.2 ha.1 ( dvd_of_mul_left_dvd h )

/-
M_layer identity: M_k · ∏_{Y_{k+1} < p ≤ X, prime} (1-1/p) = ∏_{p ≤ X, prime} (1-1/p)
    when the interval (Y_{k+1}, X] contains all primes in that range
-/
lemma M_layer_prod_eq {lam : ℝ} {k : ℕ} {X : ℕ}
    (hX : ⌊Y_val lam (k + 1)⌋₊ ≤ X) :
    M_layer lam k * ∏ p ∈ (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ X).filter Nat.Prime,
      (1 - 1 / (p : ℝ)) =
    ∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ)) := by
  unfold M_layer primesUpTo;
  norm_num [ Finset.prod_filter ];
  rw [ ← Finset.prod_union ];
  · rcongr x ; norm_num;
    exact ⟨ fun h => h.elim ( fun h => h.trans hX ) fun h => h.2, fun h => or_iff_not_imp_left.mpr fun h' => ⟨ not_le.mp h', h ⟩ ⟩;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp hx₁, Finset.mem_Ioc.mp hx₂ ] ;

/-
The union ⋃_{p∈L} p⁻¹S[p] is contained in the sifted set for sieve_bound application
-/
lemma biUnion_sinv_subset_sifted {S : Finset ℕ} {n : ℕ} {lam : ℝ} {k : ℕ}
    (hS : S ⊆ Finset.Icc 1 n) (hlam : 1 < lam)
    {L : Finset ℕ} (hL : L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty)) :
    L.biUnion (sinv S ·) ⊆
      (Finset.range (⌊(n : ℝ) / Y_val lam k⌋₊ + 1)).filter
        (fun m => m ≥ 1 ∧ ∀ r ∈ P_sieve n lam k S, ¬(r ∣ m)) := by
  intro m hm;
  simp +zetaDelta at *;
  refine ⟨ ?_, ?_, ?_ ⟩;
  · obtain ⟨ p, hp₁, hp₂ ⟩ := hm;
    have h_div : m ≤ n / p := by
      apply sinv_le_div hS (by
      exact Finset.mem_filter.mp ( hL hp₁ |> Finset.mem_filter.mp |>.1 ) |>.2) hp₂;
    refine le_trans h_div ( Nat.le_floor ?_ );
    rw [ le_div_iff₀ ] <;> norm_cast;
    · have h_div : (p : ℝ) ≥ Y_val lam k := by
        have := hL hp₁; simp_all +decide [ I_layer ] ;
      exact le_trans ( mul_le_mul_of_nonneg_left h_div <| Nat.cast_nonneg _ ) <| by norm_cast; nlinarith [ Nat.div_mul_le_self n p ] ;
    · exact mul_pos zero_lt_two ( pow_pos ( zero_lt_one.trans hlam ) _ );
  · obtain ⟨ p, hp₁, hp₂ ⟩ := hm;
    exact sinv_pos hS ( Finset.mem_filter.mp ( hL hp₁ ) |>.1 |> Finset.mem_filter.mp |>.2 ) hp₂;
  · obtain ⟨ p, hp, hm ⟩ := hm;
    intro r hr; exact sieve_prime_not_dvd_sinv hS hlam ( hL hp |> Finset.mem_filter.mp |>.1 ) ( hL hp |> Finset.mem_filter.mp |>.2 ) hr hm;

lemma M_layer_nonneg (lam : ℝ) (k : ℕ) : 0 ≤ M_layer lam k := by
  exact Finset.prod_nonneg fun p hp => sub_nonneg_of_le <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2

/-! ## Euler-Mascheroni constant bound -/

set_option maxHeartbeats 200000000 in
-- The rational harmonic-number bound needs extra heartbeats for `norm_num`.
/-- γ < 579/1000. Proved using eulerMascheroniSeq'(500) with norm_num for harmonic(500). -/
lemma gamma_lt_tight : γ < 579/1000 := by
  unfold γ
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 500
  simp only [Real.eulerMascheroniSeq', show (500 : ℕ) ≠ 0 from by omega, ↓reduceIte] at h
  -- Bound harmonic(500) from above
  have h2 : ((↑(harmonic 500 : ℚ) : ℝ)) < 6793/1000 := by
    rw [show (6793/1000 : ℝ) = ((↑(6793/1000 : ℚ) : ℝ)) from by push_cast; norm_num]
    exact Rat.cast_lt.mpr (by norm_num [harmonic, Finset.sum_range_succ])
  -- Bound Real.log(500) from below: show exp(6214/1000) < 500
  have h3 : Real.log (500 : ℝ) > 6214/1000 := by
    rw [show (6214 : ℝ)/1000 = Real.log (Real.exp (6214/1000)) from (Real.log_exp _).symm]
    exact Real.log_lt_log (Real.exp_pos _) (by
      -- exp(6.214) = exp(1)^6 * exp(0.214)
      have h1 : Real.exp (6214/1000 : ℝ) = Real.exp 1 ^ 6 * Real.exp (214/1000 : ℝ) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      rw [h1]
      have hx : |(214/1000 : ℝ)| ≤ 1 := by norm_num
      have hb := Real.exp_bound hx (n := 8) (by norm_num)
      rw [abs_le] at hb
      calc Real.exp 1 ^ 6 * Real.exp (214/1000 : ℝ)
          ≤ (2.7182818286 : ℝ)^6 * (∑ m ∈ Finset.range 8, (214/1000 : ℝ) ^ m / ↑m.factorial +
            |(214/1000 : ℝ)| ^ 8 * (↑(8 : ℕ).succ / (↑(8 : ℕ).factorial * ↑(8 : ℕ)))) := by
              apply mul_le_mul
              · exact pow_le_pow_left₀ (by positivity) (le_of_lt Real.exp_one_lt_d9) _
              · linarith [hb.2]
              · exact le_of_lt (Real.exp_pos _)
              · positivity
          _ < 500 := by simp [Finset.sum_range_succ]; norm_num)
  have h4 : Real.log ((500 : ℕ) : ℝ) = Real.log (500 : ℝ) := by push_cast; ring
  linarith [h4]

/-
Division Lemma
-/
theorem division_lemma (S : Finset ℕ) (p : ℕ) (_hp : Nat.Prime p) :
    (sinv S p).card = (sdiv S p).card := by
  exact Finset.card_image_of_injOn fun x hx y hy hxy => by
    nlinarith [Nat.div_mul_cancel (Finset.mem_filter.mp hx |>.2),
               Nat.div_mul_cancel (Finset.mem_filter.mp hy |>.2)]

/-
Collision Lemma
-/
theorem collision_lemma (n : ℕ) (A B : Finset ℕ) (p q : ℕ)
    (hadm : ProductAdmissible n A B) (_hp : Nat.Prime p) (_hq : Nat.Prime q) (hpq : p ≠ q)
    (hinter : (sinv A p ∩ sinv A q).Nonempty) :
    sinv B p ∩ sinv B q = ∅ := by
  obtain ⟨x, hx⟩ := hinter
  by_contra h_contra
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr h_contra
  obtain ⟨a1, ha1, ha1_eq⟩ : ∃ a1 ∈ A, a1 = p * x := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hx.1
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      simpa [Nat.mul_div_cancel' (Finset.mem_filter.mp ha |>.2)] using h
  obtain ⟨a2, ha2, ha2_eq⟩ : ∃ a2 ∈ A, a2 = q * x := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hx.2
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      convert h using 1
      nlinarith [Nat.div_mul_cancel (show q ∣ a from Finset.mem_filter.mp ha |>.2)]
  obtain ⟨b1, hb1, hb1_eq⟩ : ∃ b1 ∈ B, b1 = p * y := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hy.1
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      simpa [Nat.mul_div_cancel' (Finset.mem_filter.mp ha |>.2)] using h
  obtain ⟨b2, hb2, hb2_eq⟩ : ∃ b2 ∈ B, b2 = q * y := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hy.2
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      convert h using 1
      nlinarith [Nat.div_mul_cancel (show q ∣ a from Finset.mem_filter.mp ha |>.2)]
  have := hadm.2.2 a1 ha1 b2 hb2 a2 ha2 b1 hb1
  simp_all +decide [mul_comm, mul_left_comm]
  have := hadm.1 ha1; aesop

/-
Admissibility is inherited by subsets
-/
theorem admissible_subset {n : ℕ} {A B A' B' : Finset ℕ}
    (hadm : ProductAdmissible n A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ProductAdmissible n A' B' := by
  exact ⟨hA.trans hadm.1, hB.trans hadm.2.1,
    fun a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ h =>
      hadm.2.2 a₁ (hA ha₁) b₁ (hB hb₁) a₂ (hA ha₂) b₂ (hB hb₂) h⟩

lemma sdiv_subset (S : Finset ℕ) (p : ℕ) : sdiv S p ⊆ S :=
  Finset.filter_subset _ _

lemma sdiv_sdiff_self_empty (S : Finset ℕ) (p : ℕ) : sdiv (S \ sdiv S p) p = ∅ := by
  ext x; simp [sdiv]; tauto

lemma card_sdiff_sdiv_lt (S : Finset ℕ) (p : ℕ) (h : (sdiv S p).Nonempty) :
    (S \ sdiv S p).card < S.card := by
  exact Finset.card_lt_card (Finset.sdiff_ssubset (sdiv_subset S p) h)

lemma sdiv_sdiff_subset (S : Finset ℕ) (p q : ℕ) :
    (sdiv (S \ sdiv S p) q).Nonempty → (sdiv S q).Nonempty := by
  exact fun h => h.imp fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_filter.mp hx |>.2 ⟩

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos49/PNT/EulerMaclaurin.lean` -/

section



/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

section

open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def _root_.B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

@[fun_prop]
lemma _root_.aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma _root_.abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma _root_.integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma _root_.intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma _root_.integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem _root_.sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos49/PNT/IEANTN/Mertens.lean` -/

section

theorem _root_.Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


section
open _root_.Real

open Filter Asymptotics

theorem _root_.Real.inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem _root_.Real.one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end

section Issue1584
open MeasureTheory Set Filter Topology

/-- The integrand `log v * exp (-v)` is integrable on `Ioi 0`. -/
private lemma _root_.integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/-- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma _root_.integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/-- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem _root_.mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens




open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]


theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]


noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind


theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring




theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring


theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩




theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop


theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1


noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind


theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity


theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl


theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq


theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg


theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]



theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩


theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩


theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1


noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)


noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa


private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp


theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one


theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_setOf_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/-- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/-- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/-- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/-- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/-- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/-- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/-- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end


private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs


private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs


private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/-- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/-- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/-- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/-- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2


private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal


private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/-- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

/-- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/-- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/-- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/-- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/-- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/-- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end


theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]


theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr


theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2



theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1


noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)


theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]


theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]


noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring


theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)


theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one


theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]


theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2


theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/-- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring


theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring


noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant


theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le


theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]


theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]


theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one


theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind


theorem E₃.bound''' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p) - exp (-eulerMascheroniConstant) / log x) =O[atTop] (fun x ↦ 1 / (log x)^2) := by
  obtain ⟨c, hc⟩ := E₃.abs_le
  rw [isBigO_iff]
  refine ⟨exp (-eulerMascheroniConstant) * 2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop c.exp] with x hx hx2
  rw [prod_one_minus_div_prime_eq (by linarith)]
  specialize hc x hx
  rw [norm_eq_abs, norm_eq_abs]
  calc
  _ = |exp (-eulerMascheroniConstant) / log x * (exp (E₃ x) - 1)| := by ring_nf
  _ = |exp (-eulerMascheroniConstant) / log x| * |exp (E₃ x) - 1| := by rw [abs_mul]
  _ ≤ _ := by
    have : |E₃ x| ≤ 1 := by
      apply hc.trans
      have := log_le_log (exp_pos _) hx2
      rw [log_exp] at this
      apply div_le_one_iff.mpr <| Or.inl ⟨log_pos (by linarith), this⟩
    grw [abs_exp_sub_one_le this, hc]
    apply le_of_eq
    rw [abs_div, abs_div, abs_one, abs_of_nonneg (exp_nonneg _), abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg (sq_nonneg _)]
    ring

end Mertens

end


/-! ### Upstream module `src/latest/Util/MertensProduct.lean` -/

section


open Filter Finset Real Asymptotics Topology

/-- Mertens' product asymptotic, in reciprocal-product form. -/
theorem _root_.mertens_product :
    Tendsto
      (fun y : ℝ =>
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊y⌋₊), ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))
      atTop (𝓝 1) := by
  have hprod (y : ℝ) :
      (∏ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime, ((p : ℝ) / (p - 1))) =
        (∏ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr (by congr 1)
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    field_simp
  have heq :
      (fun y : ℝ => ∏ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime,
        ((p : ℝ) / (p - 1))) ~[atTop]
      (fun y : ℝ => Real.exp Real.eulerMascheroniConstant * Real.log y) := by
    convert Mertens.E₃.bound''.inv using 1
    · ext y
      exact hprod y
    · ext y
      simp [Real.exp_neg, div_eq_mul_inv, mul_comm]
  apply (isEquivalent_iff_tendsto_one ?_).mp heq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  exact mul_ne_zero (Real.exp_ne_zero _) (Real.log_pos hy).ne'

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Analytic.lean` -/

section


noncomputable section


open Finset BigOperators Nat Real Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 800000

lemma primesUpTo_eq_Ioc (x : ℝ) :
    primesUpTo x = (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, by omega⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨by omega, hprime⟩

/-- Qualitative Mertens, obtained from the proved elementary development. -/
theorem mertens_product_estimate (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
      |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) -
        Real.exp (-γ) / Real.log x| ≤ ε / Real.log x := by
  have h := Mertens.E₃.bound''.isLittleO.def (div_pos hε (Real.exp_pos (-γ)))
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X₀ 2, fun x hx => ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith [le_max_right X₀ 2])
  have hbound := hX₀ x (le_trans (le_max_left _ _) hx)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_pos (div_pos (Real.exp_pos _) hlog)] at hbound
  simpa [primesUpTo_eq_Ioc, γ, div_eq_mul_inv, mul_assoc] using hbound

theorem log_convolution_bound (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (_hX : X ≥ 1) :
    L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
      f a * chebyshevPsi (X / (a : ℝ)) := by
  unfold L_count chebyshevPsi;
  have h_log_convolution : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
    intro m hm hm_ne_zero
    have h_log_convolution_step : f m * Real.log m ≤ ∑ a ∈ Nat.divisors m, f a * ArithmeticFunction.vonMangoldt (m / a) := by
      have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt (m / a) := by
        have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt a := by
          rw [ ArithmeticFunction.vonMangoldt_sum ];
        rw [ h_log_convolution_step, ← Nat.sum_div_divisors ];
      rw [ h_log_convolution_step, Finset.mul_sum _ _ _ ];
      refine Finset.sum_le_sum fun i hi => ?_;
      have h_f_mul : f m = f i * f (m / i) := by
        rw [ ← hf.2.2 i ( m / i ) ( Nat.pos_of_mem_divisors hi ) ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_ne_zero ) ( Nat.dvd_of_mem_divisors hi ) ) ( Nat.pos_of_mem_divisors hi ) ), Nat.mul_div_cancel' ( Nat.dvd_of_mem_divisors hi ) ];
      cases hf.1 i <;> cases hf.1 ( m / i ) <;> simp_all +decide;
    refine le_trans h_log_convolution_step ?_;
    rw [ ← Finset.sum_subset ( show m.divisors ⊆ Finset.range ( ⌊X⌋₊ + 1 ) from fun x hx => Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.divisor_le hx ) <| Finset.mem_range_succ_iff.mp hm ) ];
    · gcongr;
      · cases hf.1 ‹_› <;> aesop;
      · rw [ Finset.sum_eq_single ( m / ‹_› ) ] <;> norm_num;
        · rw [ if_pos ( Nat.div_mul_cancel ( Nat.dvd_of_mem_divisors ‹_› ) ) ];
        · aesop;
        · intro h₁ h₂; contrapose! h₁; simp_all +decide [ Nat.floor_div_natCast ] ;
          exact Nat.div_le_div_right hm;
    · simp +zetaDelta at *;
      exact fun x hx hx' => Or.inr <| Finset.sum_eq_zero fun y hy => if_neg <| by intro H; exact hm_ne_zero <| hx' <| dvd_of_mul_left_eq _ H;
  have h_log_convolution_sum : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if n * a = m then 1 else 0) := by
    have hsum :
        ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤
          ∑ m ∈ Finset.range (⌊X⌋₊ + 1),
            ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
              f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1),
                ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
      refine Finset.sum_le_sum fun m hm => ?_
      by_cases hm0 : m = 0
      · subst m
        simp
        refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
        · cases hf.1 i <;> linarith
        · exact Finset.sum_nonneg fun _ _ => by
            split_ifs <;> simp +decide [ArithmeticFunction.vonMangoldt_nonneg]
      · exact h_log_convolution m hm hm0
    refine hsum.trans_eq ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n hn => by
      rw [← Finset.mul_sum]
  refine le_trans h_log_convolution_sum <| Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ <| ?_;
  · gcongr;
    aesop;
  · cases hf.1 a <;> linarith

/-
Let A > log 2 and C_A = ψ(e^A), with ψ(x) ≤ 1.11x for x ≥ e^A.
    If f is completely multiplicative {0,1}-valued and X > e^{A+C_A}, then
    F_f(X) - F_f(X·e^{-A}) ≤ 1.11·X·H_f(X)/(log X - A - C_A).
-/
theorem block_estimate (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ)
    (hX : X > Real.exp (A + chebyshevPsi (Real.exp A))) :
    F_count f X - F_count f (X * Real.exp (-A)) ≤
      ((111 / 100 : ℝ)) * X * H_count f X /
        (Real.log X - A - chebyshevPsi (Real.exp A)) := by
  -- By log_convolution_bound, L_f(X) ≤ ∑_{a≤X} f(a)·ψ(X/a).
  have h_log_conv : L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) := by
    apply log_convolution_bound f hf X (by
    exact le_trans ( Real.one_le_exp ( by linarith [ Real.log_nonneg one_le_two, show 0 ≤ chebyshevPsi ( Real.exp A ) from Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ] ) ) hX.le);
  -- Split the sum at a = X·e^{-A}:
  have h_split_sum : ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * H_count f (X * Real.exp (-A)) + chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
    have h_split_sum : ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * H_count f (X * Real.exp (-A)) := by
      have h_split_sum : ∀ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), a ≠ 0 → f a * chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * X * (f a / a) := by
        intros a ha ha_ne_zero
        have h_chebyshev : chebyshevPsi (X / a) ≤ ((111 / 100 : ℝ)) * (X / a) := by
          apply hψ;
          rw [ le_div_iff₀ ] <;> norm_num at *;
          · rw [ Nat.le_floor_iff ( mul_nonneg ( le_of_lt ( show 0 < X by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ) ( Real.exp_nonneg _ ) ) ] at ha;
            rw [ Real.exp_neg ] at ha ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
          · positivity;
        calc
          f a * chebyshevPsi (X / a) ≤
              f a * (((111 / 100 : ℝ)) * (X / a)) :=
            mul_le_mul_of_nonneg_left h_chebyshev
              (show 0 ≤ f a by cases hf.1 a <;> linarith)
          _ = ((111 / 100 : ℝ)) * X * (f a / a) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      have hsum :
          ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              f a * chebyshevPsi (X / a) ≤
            ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              ((111 / 100 : ℝ)) * X * (f a / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        by_cases ha0 : a = 0
        · subst a
          unfold chebyshevPsi
          norm_num
        · exact h_split_sum a ha ha0
      refine hsum.trans_eq ?_
      rw [H_count, ← Finset.mul_sum]
    have h_split_sum : ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
      have h_split_sum : ∀ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ f a * chebyshevPsi (Real.exp A) := by
        intros a ha
        have h_chebyshevPsi_le : chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) := by
          have h_chebyshevPsi_le : X / a ≤ Real.exp A := by
            rw [ div_le_iff₀ ] <;> norm_num at *;
            · have := Nat.lt_of_floor_lt ha.1;
              rw [ Real.exp_neg ] at this ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
            · grind;
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
          · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono h_chebyshevPsi_le );
          · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg;
        exact mul_le_mul_of_nonneg_left h_chebyshevPsi_le <| by cases hf.1 a <;> linarith;
      refine (Finset.sum_le_sum h_split_sum).trans_eq ?_
      calc
        (∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1),
            f a * chebyshevPsi (Real.exp A))
            = chebyshevPsi (Real.exp A) *
                ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
        _ = chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
              congr 1
              rw [Finset.sum_Ico_eq_sub _] <;> norm_num [Finset.sum_range_succ, F_count]
              exact Nat.floor_mono <|
                mul_le_of_le_one_right
                  (by linarith [Real.exp_pos (A + chebyshevPsi (Real.exp A))])
                  (Real.exp_le_one_iff.mpr <| by linarith [Real.log_nonneg one_le_two])
    rw [ ← Finset.sum_range_add_sum_Ico _ ( show ⌊X * Real.exp ( -A ) ⌋₊ + 1 ≤ ⌊X⌋₊ + 1 from Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ) ] ; linarith;
  -- By log_convolution_bound, L_f(X) ≥ (F_f(X) - F_f(X·e^{-A})) · (log X - A).
  have h_log_conv_lower : L_count f X ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
    -- Every integer counted by $D$ is larger than $X \cdot e^{-A}$, so $D \cdot (\log X - A) \leq L_f(X)$.
    have h_log_conv_lower : ∑ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
      have h_log_conv_lower : ∀ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ f a * (Real.log X - A) := by
        intros a ha
        have h_log_a : Real.log a ≥ Real.log X - A := by
          have h_log_a : Real.log a ≥ Real.log (X * Real.exp (-A)) := by
            exact Real.log_le_log ( mul_pos ( lt_trans ( by positivity ) hX ) ( Real.exp_pos _ ) ) ( Nat.lt_of_floor_lt ( Finset.mem_Icc.mp ha |>.1 ) |> le_of_lt );
          rw [ Real.log_mul ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ( by positivity ), Real.log_exp ] at h_log_a ; linarith;
        exact mul_le_mul_of_nonneg_left h_log_a <| by cases hf.1 a <;> linarith;
      refine le_trans ?_ ( Finset.sum_le_sum h_log_conv_lower );
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, F_count ];
      · norm_num [ ← Finset.sum_mul _ _ _ ] ; ring_nf ; norm_num;
      · exact Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ;
    refine le_trans h_log_conv_lower ?_;
    refine le_trans
      ( Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range ( ⌊X⌋₊ + 1 )) ?_ ?_ ) ?_;
    · exact fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] );
    · exact fun i hi₁ hi₂ => mul_nonneg ( by cases hf.1 i <;> linarith ) ( by positivity );
    · exact Finset.sum_le_sum fun _ _ => by aesop;
  rw [ le_div_iff₀ ];
  · -- Since $H_f(X) \geq H_f(X \cdot e^{-A})$, we can replace $H_f(X \cdot e^{-A})$ with $H_f(X)$ in the inequality.
    have h_H_ge : H_count f X ≥ H_count f (X * Real.exp (-A)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
      · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] );
      · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ );
    nlinarith [ show 0 ≤ ( (111 / 100 : ℝ) ) * X by exact mul_nonneg (by norm_num) (le_of_lt <| lt_trans (by positivity) hX) ];
  · linarith [ Real.log_exp ( A + chebyshevPsi ( Real.exp A ) ), Real.log_lt_log ( by positivity ) hX ]

/-
Trivial bound: F_f(X) ≤ 1 + X · H_f(X)
-/
lemma F_le_one_add_X_H (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    F_count f X ≤ 1 + X * H_count f X := by
  -- Apply the trivial bound to each term in the sum.
  have h_sum_bound : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m ≤ ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if m = 0 then 1 else X * f m / m) := by
    -- For each term in the sum, if m is not zero, then f(m) ≤ X * f(m) / m. This follows from the fact that m ≤ X.
    have h_term_bound : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m ≤ X * f m / m := by
      intro m hm hm'; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hm' ) ] ; nlinarith [ show ( m : ℝ ) ≤ X by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp hm ) <| Nat.floor_le <| by positivity, show ( f m : ℝ ) ≥ 0 by cases hf.1 m <;> linarith ] ;
    gcongr;
    split_ifs <;> simp_all +decide;
    cases hf.1 0 <;> linarith;
  simp_all +decide [ Finset.sum_range_succ', F_count, H_count ];
  simpa only [ mul_div_assoc, Finset.mul_sum _ _ _, add_comm ] using h_sum_bound

/-
H_f is monotone: H_f(Y) ≤ H_f(X) for Y ≤ X
-/
lemma H_count_mono (f : ℕ → ℝ) (hf : CompMult01 f) (X Y : ℝ) (hY : Y ≤ X) :
    H_count f Y ≤ H_count f X := by
  apply Finset.sum_le_sum_of_subset_of_nonneg;
  · exact Finset.range_mono ( Nat.succ_le_succ ( Nat.floor_mono hY ) );
  · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ )

lemma H_count_ge_one (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    1 ≤ H_count f X := by
  unfold H_count
  have h1 : (1 : ℕ) ∈ Finset.range (⌊X⌋₊ + 1) := by
    simp only [Finset.mem_range]; have : ⌊X⌋₊ ≥ 1 := Nat.floor_pos.mpr hX; omega
  have h2 : ∀ i ∈ Finset.range (⌊X⌋₊ + 1), 0 ≤ f i / (i : ℝ) := by
    intro m _; rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]
  have h3 := Finset.single_le_sum h2 h1
  simp [hf.2.1] at h3; linarith

lemma H_count_nonneg (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) :
    0 ≤ H_count f X := by
  unfold H_count
  exact Finset.sum_nonneg fun m _ => by
    rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]

/-
Block estimate iterated J times with uniform denominator bound L
-/
lemma block_estimate_iter (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ) (J : ℕ)
    (hXj : ∀ j : ℕ, j < J → X * Real.exp (-(j : ℝ) * A) >
      Real.exp (A + chebyshevPsi (Real.exp A)))
    (hXpos : X > 0) (L : ℝ) (hLpos : L > 0)
    (hLbound : ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) -
      A - chebyshevPsi (Real.exp A) ≥ L) :
    F_count f X ≤ F_count f (X * Real.exp (-(J : ℝ) * A)) +
      ((111 / 100 : ℝ)) * X * H_count f X / L *
        ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) := by
  induction J with
  | zero => norm_num;
  | succ J ih =>
    have h_block :
        F_count f (X * Real.exp (-J * A)) -
            F_count f (X * Real.exp (-(J + 1) * A)) ≤
          ((111 / 100 : ℝ)) * X * Real.exp (-J * A) *
              H_count f (X * Real.exp (-J * A)) / L := by
      have hbe :=
        block_estimate A hA hψ f hf (X * Real.exp (-(J : ℝ) * A))
          (hXj J (Nat.lt_succ_self J))
      have hden :
          L ≤
            Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
              chebyshevPsi (Real.exp A) :=
        hLbound J (Nat.lt_succ_self J)
      have hnum_nonneg :
          0 ≤
            ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
              H_count f (X * Real.exp (-(J : ℝ) * A)) := by
        refine mul_nonneg (mul_nonneg ?_ ?_) (H_count_nonneg f hf _)
        · positivity
        · exact mul_nonneg hXpos.le (Real.exp_nonneg _)
      have hden_step :
          ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) /
              (Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
                chebyshevPsi (Real.exp A)) ≤
            ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L := by
        exact div_le_div_of_nonneg_left hnum_nonneg hLpos hden
      have hstep := le_trans hbe hden_step
      have hxexp :
          X * Real.exp (-(J + 1 : ℝ) * A) =
            X * Real.exp (-(J : ℝ) * A) * Real.exp (-A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        norm_num
        ring
      have hrhs :
          ((111 / 100 : ℝ)) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L =
            ((111 / 100 : ℝ)) * X * Real.exp (-J * A) *
                H_count f (X * Real.exp (-J * A)) / L := by
        ring
      rw [hxexp]
      rw [← hrhs]
      exact hstep
    have h_monotone : H_count f (X * Real.exp (-J * A)) ≤ H_count f X := by
      apply H_count_mono;
      · exact hf;
      · exact mul_le_of_le_one_right hXpos.le ( Real.exp_le_one_iff.mpr <| by nlinarith [ Real.log_nonneg one_le_two ] );
    have h_combined : F_count f X ≤ F_count f (X * Real.exp (-(J + 1) * A)) + ((111 / 100 : ℝ)) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) + ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f X / L := by
      have h_combined : F_count f X ≤ F_count f (X * Real.exp (-J * A)) + ((111 / 100 : ℝ)) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) := by
        exact ih ( fun j hj => hXj j ( Nat.lt_succ_of_lt hj ) ) ( fun j hj => hLbound j ( Nat.lt_succ_of_lt hj ) );
      have h_combined : ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f (X * Real.exp (-J * A)) / L ≤ ((111 / 100 : ℝ)) * X * Real.exp (-J * A) * H_count f X / L := by
        gcongr;
      grind;
    convert h_combined using 1 ; push_cast [ Finset.sum_range_succ ] ; ring

lemma geom_sum_le (A : ℝ) (hA : A > 0) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
  have h_geo_series : ∑ j ∈ Finset.range J, (Real.exp (-A)) ^ j ≤ 1 / (1 - Real.exp (-A)) := by
    rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -A ), Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ), pow_pos ( Real.exp_pos ( -A ) ) J, geom_sum_mul ( Real.exp ( -A ) ) J ];
  convert h_geo_series using 2 ; norm_num [ ← Real.exp_nat_mul ]

lemma log_div_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
  -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
  suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
    exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
  norm_num;
  exact tendsto_nhdsWithin_of_tendsto_nhds ( by
    have h := Real.continuous_mul_log.tendsto 0
    simpa using h.neg )

/-
For large X, the denominator in the block estimate is close to log X.
-/
lemma mean_L_improved (A : ℝ) (hA : A > 0) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ →
      ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 →
        ∀ j : ℕ, j < J →
          Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥
            (1 - ε₁) * Real.log X := by
  -- We need to ensure that $2 \log(\log X) + A + \psi(e^A) \leq \epsilon_1 \log X$ for sufficiently large $X$.
  have h_log_log : Filter.Tendsto (fun X : ℝ => (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X) Filter.atTop (nhds 0) := by
    ring_nf;
    -- We'll use the fact that $\frac{\log(\log X)}{\log X}$ tends to $0$ as $X$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) Filter.atTop (nhds 0) := by
      refine (log_div_tendsto_zero.comp Real.tendsto_log_atTop).congr' ?_
      exact Filter.Eventually.of_forall fun X => by rfl
    have h_inv_log :
        Filter.Tendsto (fun X : ℝ => (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hAterm :
        Filter.Tendsto (fun X : ℝ => A * (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hPterm :
        Filter.Tendsto
          (fun X : ℝ => chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hsum :
        Filter.Tendsto
          (fun X : ℝ =>
            2 * (Real.log (Real.log X) / Real.log X) +
              A * (Real.log X)⁻¹ +
              chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa [add_assoc] using (h_log_log.const_mul 2).add (hAterm.add hPterm)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hsum
  -- By the definition of limit, there exists an X₀ such that for all X ≥ X₀, (2 * log(log X) + A + ψ(e^A)) / log X < ε₁.
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ X ≥ X₀, (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X < ε₁ := by
    simpa using h_log_log.eventually ( gt_mem_nhds hε₁ );
  refine ⟨ Max.max X₀ 2, le_max_right _ _, fun X hX J hJ j hj => ?_ ⟩ ; specialize hX₀ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ] at hX₀ <;> norm_num at *;
  · rw [ Real.log_mul ( by linarith ) ( by positivity ), Real.log_exp ];
    rw [ div_add_one, le_div_iff₀ ] at hJ <;> nlinarith [ show ( j : ℝ ) + 1 ≤ J by norm_cast ];
  · exact Real.log_pos <| by linarith

/-
For large X, the tail F_f(X·e^{-JA}) + 1 is bounded by ε * X/log X * H_f(X).
-/
set_option maxHeartbeats 1600000 in
-- The tail estimate combines several asymptotic bounds through generated arithmetic.
lemma mean_tail_small (A : ℝ) (hA : A > Real.log 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) →
        F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤
          ε * X / Real.log X * H_count f X := by
  -- By definition of $F_count$, we know that $F_count f (X * Real.exp (-J * A)) \leq 1 + X * Real.exp (-J * A) * H_count f X$.
  have hF_count_bound : ∀ (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) (J : ℕ), F_count f (X * Real.exp (-J * A)) ≤ 1 + X * Real.exp (-J * A) * H_count f X := by
    intros f hf X hX J
    have hF_count_bound : F_count f (X * Real.exp (-J * A)) ≤ 1 + (X * Real.exp (-J * A)) * H_count f (X * Real.exp (-J * A)) := by
      by_cases hX' : X * Real.exp ( -J * A ) ≥ 1;
      · convert F_le_one_add_X_H f hf ( X * Real.exp ( -J * A ) ) hX' using 1;
      · unfold F_count H_count; norm_num [ Nat.floor_eq_zero.mpr ( not_le.mp hX' ) ] ;
        norm_num [ show ⌊X * Real.exp ( - ( J * A ) ) ⌋₊ = 0 by exact Nat.floor_eq_zero.mpr <| by simpa using hX' ];
        cases hf.1 0 <;> linarith;
    refine le_trans hF_count_bound ?_;
    gcongr;
    exact H_count_mono f hf X _ ( mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ Real.log_pos one_lt_two ] ) ) );
  -- For large X, X·e^{-JA} ≤ X/(log X)².
  have h_exp_bound : ∃ X₀ ≥ 2, ∀ X ≥ X₀, ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → X * Real.exp (-J * A) ≤ X / (Real.log X) ^ 2 := by
    refine ⟨ Real.exp 2, ?_, ?_ ⟩ <;> norm_num;
    · linarith [ Real.add_one_le_exp 2 ];
    · intro X hX J hJ; rw [ div_eq_mul_inv ] ; rw [ ← Real.log_le_log_iff ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( Real.exp_pos _ ) ) ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by positivity ), Real.log_exp ] ; ring_nf;
      rw [ Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by exact ne_of_gt ( sq_pos_of_pos ( inv_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_pow, Real.log_inv ] ; norm_num ; linarith [ Real.log_pos ( show 1 < X by linarith [ Real.add_one_le_exp 2 ] ) ];
  -- By combining the results from hF_count_bound and h_exp_bound, we can derive the desired inequality.
  obtain ⟨X₀, hX₀_ge_2, hX₀_bound⟩ := h_exp_bound;
  have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → 2 + X * Real.exp (-J * A) * H_count f X ≤ ε * X / Real.log X * H_count f X := by
    have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, 2 + X / (Real.log X) ^ 2 ≤ ε * X / Real.log X := by
      have h_combined_bound : Filter.Tendsto (fun X : ℝ => (2 + X / (Real.log X) ^ 2) / (X / Real.log X)) Filter.atTop (nhds 0) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun X : ℝ => 2 * Real.log X / X + 1 / Real.log X) Filter.atTop (nhds 0) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with X hX;
          -- was `grind`: with all 36 upstream modules in one environment the tactic no
          -- longer closes this goal, so the same identity is proved explicitly.
          have hX0 : (0:ℝ) < X := lt_trans zero_lt_one hX
          have hl : (0:ℝ) < Real.log X := Real.log_pos hX
          field_simp;
        -- We'll use the fact that $\frac{\log X}{X}$ tends to $0$ as $X$ tends to infinity.
        have h_log_div_X : Filter.Tendsto (fun X : ℝ => Real.log X / X) Filter.atTop (nhds 0) := by
          -- was `grind +suggestions`; see the note above.
          simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
        simpa [ mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_X.const_mul 2 ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) );
      have := h_combined_bound.eventually ( gt_mem_nhds <| show 0 < ε by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₁, hX₁ ⟩ ; exact ⟨ Max.max X₀ X₁, le_max_left _ _, fun X hX => by have := hX₁ X ( le_trans ( le_max_right _ _ ) hX ) ; rw [ div_lt_iff₀ ( div_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ( Real.log_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ) ) ] at this; ring_nf at *; linarith ⟩ ;
    obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound;
    use X₁, hX₁₁;
    intros X hX f hf J hJ;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( hX₁₂ X hX ) ( H_count_nonneg f hf X ) );
    rw [ add_mul ];
    gcongr;
    · exact le_mul_of_one_le_right ( by norm_num ) ( H_count_ge_one f hf X ( by linarith ) );
    · exact H_count_nonneg f hf X;
    · exact hX₀_bound X ( by linarith ) J hJ;
  obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound; exact ⟨ X₁, by linarith, fun X hX f hf J hJ => by linarith [ hF_count_bound f hf X ( by linarith ) J, hX₁₂ X hX f hf J hJ ] ⟩ ;

set_option maxHeartbeats 6400000 in
-- The fixed-A mean estimate contains the largest generated block estimate.
lemma mean_estimate_fixed_A (A : ℝ) (hA : A > Real.log 2)
    (hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x) (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ (((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε) *
        X / Real.log X * H_count f X := by
  -- Choose ε₁ ∈ (0,1) small enough that 1.11/((1-ε₁)·(1-e^{-A})) ≤ 1.11/(1-e^{-A}) + ε/2.
  obtain ⟨ε₁, hε₁_pos, hε₁_small⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 ∧ ((111 / 100 : ℝ)) / ((1 - ε₁) * (1 - Real.exp (-A))) ≤ ((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε / 2 := by
    have h_lim : Filter.Tendsto (fun ε₁ : ℝ => ((111 / 100 : ℝ)) / ((1 - ε₁) * (1 - Real.exp (-A)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (((111 / 100 : ℝ)) / (1 - Real.exp (-A)))) := by
      have hlim0 :
          Filter.Tendsto
            ((fun _ : ℝ => (111 / 100 : ℝ)) /
              fun ε₁ : ℝ => (1 - ε₁) * (1 - Real.exp (-A)))
            (nhds 0) (nhds (((111 / 100 : ℝ)) / (1 - Real.exp (-A)))) :=
        tendsto_const_nhds.div
          (by
            simpa using
              Continuous.tendsto
                (show Continuous fun ε₁ : ℝ =>
                  (1 - ε₁) * (1 - Real.exp (-A)) by continuity)
                0)
          (show 1 - Real.exp (-A) ≠ 0 by
            exact sub_ne_zero_of_ne
              (Ne.symm
                (by
                  norm_num
                  linarith [Real.log_pos one_lt_two])))
      exact tendsto_nhdsWithin_of_tendsto_nhds
        (hlim0.congr' <| Filter.Eventually.of_forall fun ε₁ => by rfl)
    have := h_lim.eventually ( ge_mem_nhds <| show ( (111 / 100 : ℝ) ) / ( 1 - Real.exp ( -A ) ) < ( (111 / 100 : ℝ) ) / ( 1 - Real.exp ( -A ) ) + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists ; exact ⟨ ε₁, hε₁₂.1, hε₁₂.2, hε₁₁ ⟩ ;
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₁ → ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 → ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥ (1 - ε₁) * Real.log X := by
    apply mean_L_improved A (by linarith [Real.log_pos one_lt_two]) ε₁ hε₁_pos;
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₂ → ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) → F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
    convert mean_tail_small A hA ( ε / 2 ) ( half_pos hε ) using 1;
  refine ⟨ Max.max X₁ X₂, fun X hX f hf => ?_ ⟩;
  by_cases hX_pos : 0 < X;
  · by_cases h_log_pos : 0 < Real.log X;
    · have h_block : F_count f X ≤ F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + ((111 / 100 : ℝ)) * X * H_count f X / ((1 - ε₁) * Real.log X) * (∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A)) := by
        apply block_estimate_iter A hA hψ;
        all_goals norm_num [ hA, hε₁_pos, hε₁_small, hX_pos, h_log_pos ];
        · exact hf;
        · intro j hj;
          have := hX₁.2 X ( le_trans ( le_max_left _ _ ) hX ) ( Nat.ceil ( 2 * Real.log ( Real.log X ) / A ) ) ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                                                                                                contrapose! hj;
                                                                                                                                                                                                                                                                rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                                                                                                exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ] ) j hj;
          rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] at this;
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ];
          norm_num; nlinarith [ Real.log_pos one_lt_two ];
        · simp +zetaDelta at *;
          exact fun j hj => hX₁.2 X hX.1 _ ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                            contrapose! hj;
                                                                                                                                                                                            rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                            exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ] ) _ hj;
      have h_tail : F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
        apply hX₂.right X (by
        exact le_trans ( le_max_right _ _ ) hX) f hf (Nat.ceil (2 * Real.log (Real.log X) / A)) (by
        nlinarith [ Nat.le_ceil ( 2 * Real.log ( Real.log X ) / A ), show 0 < A by linarith [ Real.log_pos one_lt_two ], mul_div_cancel₀ ( 2 * Real.log ( Real.log X ) ) ( show A ≠ 0 by linarith [ Real.log_pos one_lt_two ] ) ]);
      have h_geom_sum : ∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
        convert geom_sum_le A ( show 0 < A by linarith [ Real.log_pos one_lt_two ] ) ⌈2 * Real.log ( Real.log X ) / A⌉₊ using 1;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + ((111 / 100 : ℝ)) * X * H_count f X / ((1 - ε₁) * Real.log X) * (1 / (1 - Real.exp (-A))) := by
        refine le_trans h_block ?_;
        refine add_le_add ?_ ?_;
        · linarith;
        · exact mul_le_mul_of_nonneg_left h_geom_sum <| div_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| H_count_nonneg f hf X ) <| mul_nonneg ( by linarith ) <| by positivity;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + (((111 / 100 : ℝ)) / (1 - Real.exp (-A)) + ε / 2) * X / Real.log X * H_count f X := by
        refine le_trans h_combined ?_;
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] at *;
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( by nlinarith [ inv_pos.mpr h_log_pos ] ) ( H_count_nonneg f hf X ) ) hX_pos.le;
      grind;
    · exact False.elim <| h_log_pos <| Real.log_pos <| by linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ] ;
  · linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ]


/-- The only Chebyshev input required by the sieve. -/
def ElementaryChebyshevBound : Prop :=
  ∃ T : ℝ, ∀ x : ℝ, T ≤ x → chebyshevPsi x ≤ (111 / 100) * x

lemma choose_mean_block (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ A : ℝ, Real.log 2 < A ∧ T ≤ Real.exp A ∧
      (111 / 100 : ℝ) / (1 - Real.exp (-A)) < 111 / 100 + ε := by
  have hlim : Tendsto (fun A : ℝ => (111 / 100 : ℝ) / (1 - Real.exp (-A)))
      atTop (𝓝 (111 / 100)) := by
    have hnum : Tendsto (fun _ : ℝ => (111 / 100 : ℝ)) atTop (𝓝 (111 / 100)) :=
      tendsto_const_nhds
    have hden : Tendsto (fun A : ℝ => 1 - Real.exp (-A)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot) :
        Tendsto (fun A : ℝ => 1 - Real.exp (-A)) atTop (𝓝 (1 - 0)))
    have hdiv := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at hdiv
    exact hdiv.congr' (Filter.Eventually.of_forall fun A => by rfl)
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    (111 / 100 : ℝ) < 111 / 100 + ε))
  obtain ⟨A, hA, hT, hbound⟩ :=
    ((eventually_gt_atTop (Real.log 2)).and
      ((Real.tendsto_exp_atTop.eventually_ge_atTop T).and hbound)).exists
  exact ⟨A, hA, hT, hbound⟩

/-- Uniform mean-value estimate; its proof uses only a one-sided elementary
Chebyshev bound, not the prime number theorem. -/
theorem mean_estimate (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ (111 / 100 + ε) * X / Real.log X * H_count f X := by
  obtain ⟨T, hT⟩ := hCheb
  obtain ⟨A, hA, hAT, hcoeff⟩ := choose_mean_block (ε / 2) (half_pos hε) T
  have hψ : ∀ x : ℝ, Real.exp A ≤ x → chebyshevPsi x ≤ (111 / 100) * x :=
    fun x hx => hT x (hAT.trans hx)
  obtain ⟨X₀, hX₀⟩ := mean_estimate_fixed_A A hA hψ (ε / 2) (half_pos hε)
  refine ⟨max X₀ 1, fun X hX f hf => (hX₀ X (le_of_max_le_left hX) f hf).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (H_count_nonneg f hf X)
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (le_of_max_le_right hX))
  exact mul_le_mul_of_nonneg_right (by linarith) (by linarith [le_of_max_le_right hX])

theorem sieve_bound (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
      ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ X) →
        (((Finset.range (⌊X⌋₊ + 1)).filter
          (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card : ℝ) ≤
          ((111 / 100) * Real.exp γ + ε) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  obtain ⟨ X₁, hX₁ ⟩ := mean_estimate hCheb ( ε / 2 / ( Real.exp γ + ε ) ) ( by positivity );
  -- By Mertens' product theorem, there exists $X₂$ such that for all $X ≥ X₂$, $\prod_{p ≤ X} (1 - 1/p)^{-1} ≤ (e^γ + ε/2) \log X$.
  obtain ⟨ X₂, hX₂ ⟩ : ∃ X₂ : ℝ, ∀ X ≥ X₂, (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + 50 * ε / 111) * Real.log X := by
    have h_mertens : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))) * Real.log X) Filter.atTop (nhds (Real.exp (-γ))) := by
      have := mertens_product_estimate;
      rw [ Metric.tendsto_nhds ];
      intro ε hε; rcases this ( ε / 2 ) ( half_pos hε ) with ⟨ X₀, HX₀ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop X₀, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; specialize HX₀ x hx₁; rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ abs_le.mp HX₀, Real.log_pos hx₂, mul_div_cancel₀ ( ε / 2 ) ( ne_of_gt ( Real.log_pos hx₂ ) ), mul_div_cancel₀ ( Real.exp ( -γ ) ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ] ;
    have h_mertens_inv : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) / Real.log X) Filter.atTop (nhds (Real.exp γ)) := by
      have := h_mertens.inv₀ ; simp_all +decide [ Real.exp_neg ];
      simpa only [ div_eq_inv_mul ] using this;
    have := h_mertens_inv.eventually ( gt_mem_nhds <| show Real.exp γ < Real.exp γ + 50 * ε / 111 by linarith );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₂, hX₂ ⟩ ; exact ⟨ Max.max X₂ 2, fun X hX => by have := hX₂ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₂ 2 ] ) ] at this; linarith ⟩ ;
  refine ⟨ Max.max X₁ ( Max.max X₂ 2 ), fun X hX P hP => ?_ ⟩ ; specialize hX₁ X ( le_trans ( le_max_left ?_ ?_ ) hX ) ( fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0 ) ?_
  focus
    simp_all +decide [ F_count, H_count ]
  · constructor <;> norm_num;
    · exact fun m => Classical.or_iff_not_imp_left.2 fun h => by push Not at h; exact h;
    · constructor;
      · exact fun h => Nat.not_prime_one ( hP _ h |>.1 );
      · intro a b ha hb; split_ifs <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
  · -- By Euler product bound, we have $H_f(X) \leq \prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
    have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) := by
      have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) := by
        unfold H_count; simp +decide ;
        erw [ Finset.sum_filter, Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
        exact Finset.sum_le_sum fun _ _ => by split_ifs <;> ring_nf <;> norm_num;
      -- The sum $\sum_{m \leq X, \forall p \in P, \neg p \mid m} \frac{1}{m}$ is bounded above by the product $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
      have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∏ p ∈ primesUpTo X \ P, (∑ k ∈ Finset.range (Nat.log p ⌊X⌋₊ + 1), (1 / (p ^ k : ℝ))) := by
        have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (∏ p ∈ primesUpTo X \ P, (1 / (p ^ (Nat.factorization m p) : ℝ))) := by
          refine Finset.sum_le_sum fun m hm => ?_;
          have h_factorization : m = ∏ p ∈ primesUpTo X \ P, p ^ (Nat.factorization m p) := by
            conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ] : m ≠ 0 ) ] ;
            rw [ Finsupp.prod_of_support_subset ] <;> simp_all +decide [ Finset.subset_iff ];
            exact fun p pp dp _ => ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd hm.1.1 dp ) hm.1.2 ) ), pp ⟩, fun hp => hm.2 p hp dp ⟩;
          rw [ h_factorization, Nat.cast_prod ];
          norm_num [ ← h_factorization ];
        refine le_trans h_sum_bound ?_;
        rw [ Finset.prod_sum ];
        refine le_trans ?_
          ( Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.image ( fun m => fun p hp => Nat.factorization m p )
              ( Finset.filter ( fun m => ∀ p ∈ P, ¬p ∣ m ) ( Finset.Icc 1 ⌊X⌋₊ ) ))
            ?_ fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity );
        rotate_left;
        · simp +decide [ Finset.subset_iff ];
          rintro x m hm₁ hm₂ hm₃ rfl p hp hq; exact Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( by unfold primesUpTo at hp; aesop ) ) ( Nat.le_trans ( Nat.le_of_dvd hm₁ ( Nat.ordProj_dvd _ _ ) ) hm₂ ) ;
        · rw [ Finset.sum_image ];
          · exact Finset.sum_le_sum fun x hx => by rw [ ← Finset.prod_attach ] ;
          · intro m hm m' hm' h_eq; simp_all +decide [ funext_iff ] ;
            rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : m ≠ 0 ), ← Nat.prod_factorization_pow_eq_self ( by linarith : m' ≠ 0 ) ];
            congr! 1;
            ext p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ ⌊X⌋₊ <;> simp_all +decide [ primesUpTo ] ;
            · by_cases hp'' : p ∈ P <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
            · rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ), Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ) ];
      refine le_trans h_euler <| h_sum_bound.trans ?_;
      gcongr;
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by unfold primesUpTo at *; aesop ) ];
      simpa using Summable.sum_le_tsum ( Finset.range ( Nat.log _ ⌊X⌋₊ + 1 ) ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by unfold primesUpTo at *; aesop ) ) ) ) );
    -- By Mertens' product theorem, we have $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1} \leq (e^γ + ε/2) \log X \prod_{p \in P} (1 - 1/p)$.
    have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + 50 * ε / 111) * Real.log X * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
      have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) = (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
        rw [ ← Finset.prod_sdiff <| show P ⊆ primesUpTo X from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| hP p hp |>.2, hP p hp |>.1 ⟩ ];
        simp +decide ;
        rw [ mul_assoc, inv_mul_cancel₀ ( Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero_of_ne <| by norm_num; linarith [ Nat.Prime.one_lt ( hP p hp |>.1 ) ] ), mul_one ];
      exact h_mertens.symm ▸ mul_le_mul_of_nonneg_right ( hX₂ X ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hX ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    refine le_trans ?_ (hX₁.trans ?_)
    · unfold F_count
      simp +decide
      exact Finset.card_mono fun x hx => by aesop
    · have hxpos : 0 < X := by
        have := le_max_right X₁ (max X₂ 2)
        have := le_max_right X₂ (2 : ℝ)
        linarith
      have hlog : 0 < Real.log X := Real.log_pos (by
        have := le_max_right X₁ (max X₂ 2)
        have := le_max_right X₂ (2 : ℝ)
        linarith)
      have hbpos : 0 < Real.exp γ + ε := by positivity
      have hPnonneg : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
        apply Finset.prod_nonneg
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_lt.le
        exact sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le (by norm_num) hp1)
      have hcoeff :
          (111 / 100 + ε / 2 / (Real.exp γ + ε)) * (Real.exp γ + 50 * ε / 111) ≤
            (111 / 100) * Real.exp γ + ε := by
        have hδpos : 0 ≤ ε / 2 / (Real.exp γ + ε) := by positivity
        have hcancel := div_mul_cancel₀ (ε / 2) hbpos.ne'
        nlinarith
      calc
        (111 / 100 + ε / 2 / (Real.exp γ + ε)) * X / Real.log X *
            H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X
          ≤ (111 / 100 + ε / 2 / (Real.exp γ + ε)) * X / Real.log X *
              ((Real.exp γ + 50 * ε / 111) * Real.log X *
                ∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
                  exact mul_le_mul_of_nonneg_left (h_euler.trans h_mertens) (by positivity)
        _ = ((111 / 100 + ε / 2 / (Real.exp γ + ε)) *
              (Real.exp γ + 50 * ε / 111)) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
                field_simp
        _ ≤ ((111 / 100) * Real.exp γ + ε) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hxpos.le) hPnonneg

theorem sifted_bound_set (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ((S.card : ℝ) ≤ (((111 / 100) * Real.exp γ) + ε) * n * Pi_sieve n lam k S) := by
  obtain ⟨ N₀, hN₀ ⟩ := sieve_bound hCheb ε hε;
  refine ⟨ ⌈N₀⌉₊, fun n hn k S hS =>
    le_trans ?_ ( hN₀ n ( Nat.le_of_ceil_le hn ) (P_sieve n lam k S) ?_ ) ⟩;
  · refine mod_cast Finset.card_le_card ?_;
    intro m hm;
    have hmIcc := Finset.mem_Icc.mp ( hS hm );
    refine Finset.mem_filter.mpr ⟨ ?_, hmIcc.1, ?_ ⟩;
    · simpa using Nat.lt_succ_of_le hmIcc.2;
    intro p hp hp_dvd;
    exact ( Finset.mem_filter.mp hp |>.2 )
      ⟨ m, Finset.mem_filter.mpr ⟨ hm, hp_dvd ⟩ ⟩;
  · simp +zetaDelta at *;
    intro p hp;
    refine ⟨ ?_, ?_ ⟩;
    · exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
    · refine le_trans ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ?_;
      exact Nat.floor_le_of_le ( div_le_self ( Nat.cast_nonneg _ ) ( by exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( one_le_pow₀ hlam.le ) zero_le_two ) ) )

theorem sifted_bound_union (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ∀ L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty),
        (((L.biUnion (sinv S ·)).card : ℝ) ≤
          (((111 / 100) * Real.exp γ) + ε) * n / Y_val lam k * Pi_sieve n lam k S) := by
  obtain ⟨ X₀, hX₀ ⟩ := sieve_bound hCheb ε hε;
  refine ⟨ ⌈X₀ ^ 2 / lam⌉₊ + 1, fun n hn k S hS L hL => ?_ ⟩;
  by_cases hP : P_sieve n lam k S = ∅;
  · have h_card : (L.biUnion (sinv S ·)).card ≤ n / Y_val lam k := by
      have h_card : (L.biUnion (sinv S ·)).card ≤ Finset.card (Finset.Icc 1 (Nat.floor (n / Y_val lam k))) := by
        refine Finset.card_le_card ?_;
        intro x hx; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ a, ha₁, ha₂ ⟩ := hx; specialize hL ha₁; simp_all +decide [ sinv ] ;
        obtain ⟨ y, hy₁, hy₂ ⟩ := ha₂; have := hS ( Finset.mem_filter.mp hy₁ |>.1 ) ; simp_all +decide [ sdiv ] ;
        have h_div : a ≥ Y_val lam k := by
          exact Nat.le_of_ceil_le ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hL.1 |>.1 ) |>.1 );
        exact ⟨ hy₂ ▸ Nat.div_pos ( Nat.le_of_dvd ( hS hy₁.1 |>.1 ) hy₁.2 ) ( Nat.pos_of_dvd_of_pos hy₁.2 ( hS hy₁.1 |>.1 ) ), Nat.le_floor <| by rw [ le_div_iff₀ <| by exact mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ] ; nlinarith [ show ( y : ℝ ) ≤ n by exact_mod_cast hS hy₁.1 |>.2, show ( a : ℝ ) ≥ Y_val lam k by exact_mod_cast h_div, Nat.div_mul_le_self y a, show ( y : ℝ ) = a * x by exact_mod_cast by nlinarith [ Nat.div_mul_cancel hy₁.2 ] ] ⟩;
      exact le_trans ( Nat.cast_le.mpr h_card ) ( by simpa using Nat.floor_le ( show 0 ≤ ( n : ℝ ) / Y_val lam k by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) );
    refine le_trans h_card ?_;
    rw [ show Pi_sieve n lam k S = 1 from _ ];
    · rw [ mul_one ] ; gcongr;
      · exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ );
      · refine le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ?_;
        refine le_add_of_le_of_nonneg ?_ hε.le;
        refine le_trans (Real.one_le_exp (x := γ) ?_)
          (le_mul_of_one_le_left (Real.exp_nonneg γ) (by norm_num : (1 : ℝ) ≤ 111 / 100));
        refine le_of_tendsto_of_tendsto tendsto_const_nhds ( Real.tendsto_eulerMascheroniSeq ) ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        simp +decide [ eulerMascheroniSeq ];
        induction hn <;> simp_all +decide [ harmonic ];
        · exact le_trans ( Real.log_le_sub_one_of_pos ( by norm_num ) ) ( by norm_num );
        · rw [ Finset.sum_range_succ, Real.log_le_iff_le_exp ( by positivity ) ] at *;
          rw [ Real.exp_add ];
          nlinarith [ Real.add_one_le_exp ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, Real.exp_pos ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, mul_inv_cancel₀ ( by positivity : ( ( ↑‹ℕ› : ℝ ) + 1 ) ≠ 0 ) ];
    · unfold Pi_sieve; aesop;
  · have h_n_Yk_ge_X₀ : (n : ℝ) / Y_val lam k ≥ X₀ := by
      have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam ∧ (n : ℝ) / Y_val lam k ≥ Y_val lam (k + 1) := by
        have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam := by
          exact le_of_lt ( Nat.lt_of_ceil_lt hn );
        obtain ⟨ p, hp ⟩ := Finset.nonempty_of_ne_empty hP;
        simp_all +decide [ P_sieve ];
        exact le_trans ( Nat.lt_of_floor_lt hp.1.1.1 |> le_of_lt ) ( Nat.floor_le ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) |> le_trans ( Nat.cast_le.mpr hp.1.1.2 ) );
      unfold Y_val at *;
      field_simp at *;
      ring_nf at *;
      norm_num [ pow_mul ] at *;
      nlinarith [ show ( lam : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ hlam.le, show ( lam : ℝ ) ^ k * lam ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ hlam.le ) hlam.le ];
    have h_card_sifted :
        ((L.biUnion (sinv S ·)).card : ℝ) ≤
          ((Finset.range (⌊(n : ℝ) / Y_val lam k⌋₊ + 1)).filter
            (fun m => m ≥ 1 ∧ ∀ r ∈ P_sieve n lam k S, ¬r ∣ m)).card := by
      exact_mod_cast Finset.card_le_card (biUnion_sinv_subset_sifted hS hlam hL)
    have hP_bound :
        ∀ p ∈ P_sieve n lam k S, Nat.Prime p ∧ (p : ℝ) ≤ (n : ℝ) / Y_val lam k := by
      intro p hp
      exact
        ⟨Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.2,
          by
            exact le_trans
              (Nat.cast_le.mpr <|
                Finset.mem_Ioc.mp
                  (Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1) |>.2)
              (Nat.floor_le <|
                by
                  exact div_nonneg (Nat.cast_nonneg _) <|
                    by exact mul_nonneg zero_le_two <| pow_nonneg (by positivity) _)⟩
    refine le_trans h_card_sifted ?_
    simpa [Pi_sieve, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hX₀ ((n : ℝ) / Y_val lam k) h_n_Yk_ge_X₀ (P_sieve n lam k S) hP_bound

lemma wip_finitely_many (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (ε : ℝ) (hε : ε > 0) (K : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, k ≤ K →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ k ≤ K, ∀ n ≥ N₁, M_layer lam k / g k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
    have h_case1 : ∀ k ≤ K, ∃ N₁ : ℕ, ∀ n ≥ N₁, M_layer lam k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
      intro k hk
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, n ≥ N₁ → (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
        have := mertens_product_estimate ( ε / 4 ) ( by positivity );
        obtain ⟨ X₀, hX₀ ⟩ := this;
        -- Choose N₁ such that for all n ≥ N₁, ⌊n/Y_k⌋ ≥ X₀.
        obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ⌊(n : ℝ) / Y_val lam k⌋₊ ≥ X₀ := by
          have h_floor : Filter.Tendsto (fun n : ℕ => ⌊(n : ℝ) / Y_val lam k⌋₊ : ℕ → ℝ) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| Filter.Tendsto.atTop_div_const ( show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ) <| tendsto_natCast_atTop_atTop;
          exact Filter.eventually_atTop.mp ( h_floor.eventually_ge_atTop X₀ );
        use N₁ + 2; intros n hn; specialize hX₀ ⌊ ( n : ℝ ) / Y_val lam k⌋₊ ( hN₁ n ( by linarith ) ) ; rw [ abs_le ] at hX₀; ring_nf at *; linarith;
      use N₁ + ⌈Y_val lam (k + 1) * Y_val lam k⌉₊ + 1;
      intro n hn
      have h_prod : M_layer lam k * (∏ p ∈ (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) = (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) := by
        apply M_layer_prod_eq;
        refine Nat.le_floor ?_;
        rw [ le_div_iff₀ ] <;> norm_num [ Y_val ] at *;
        · nlinarith [ Nat.floor_le ( show 0 ≤ 2 * lam ^ ( k + 1 ) by positivity ), Nat.le_ceil ( 2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ), show ( n : ℝ ) ≥ N₁ + ⌈2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ⌉₊ + 1 by exact_mod_cast hn, pow_pos ( zero_lt_one.trans hlam ) k, pow_succ' lam k ];
        · positivity;
      exact h_prod.symm ▸ hN₁ n ( by linarith );
    choose! N₁ hN₁ using h_case1;
    use Finset.sup (Finset.range (K + 1)) N₁;
    intro k hk n hn; specialize hN₁ k hk n ( le_trans ( Finset.le_sup ( f := N₁ ) ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hk ) ) ) hn ) ; simp_all +decide [ div_mul_eq_mul_div ] ;
    exact le_trans ( div_le_self ( mul_nonneg ( M_layer_nonneg _ _ ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) ) <| hg1 _ ) hN₁;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ k ≤ K, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) * Real.log n := by
    have h_log_floor : ∀ k ≤ K, Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n) Filter.atTop (nhds 1) := by
      intro k hk
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (n / Y_val lam k) / Real.log n) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => (Real.log n - Real.log (Y_val lam k)) / Real.log n) Filter.atTop (nhds 1) := by
          ring_nf;
          exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( mod_cast hx ) ) ) ] ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num );
        refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( show 0 < Y_val lam k from mul_pos zero_lt_two ( pow_pos ( by positivity ) _ ) ) ) ] );
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log (n / Y_val lam k)) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (⌊x⌋₊) / Real.log x) Filter.atTop (nhds 1) := by
          have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (x - 1) / Real.log x) Filter.atTop (nhds 1) := by
            have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (1 - 1 / x)) / Real.log x) Filter.atTop (nhds 1) := by
              ring_nf;
              exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
            refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; rw [ Real.log_div ] <;> ring_nf <;> linarith );
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_log_floor_aux tendsto_const_nhds ?_ ?_;
          · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith [ Nat.lt_floor_add_one x ] ) ) ( Real.log_nonneg ( by linarith ) );
          · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using div_le_one_of_le₀ ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by linarith ) <| Real.log_nonneg <| by linarith;
        exact h_log_floor_aux.comp <| tendsto_natCast_atTop_atTop.atTop_div_const <| show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _;
      have := h_log_floor_aux.mul ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›;
      simp_all +decide ;
      refine this.congr' ( by filter_upwards [ ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›.eventually_ne one_ne_zero ] with n hn using by rw [ div_mul_div_cancel₀ ( by aesop ) ] );
    have h_log_floor : ∀ k ≤ K, ∃ N₂ : ℕ, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
      exact fun k hk => by rcases Metric.tendsto_atTop.mp ( h_log_floor k hk ) ( 1 - ( Real.exp ( -γ ) + ε / 2 ) / ( Real.exp ( -γ ) + ε ) ) ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ Real.exp_pos ( -γ ) ] ) with ⟨ N₂, hN₂ ⟩ ; exact ⟨ N₂, fun n hn => by linarith [ abs_lt.mp ( hN₂ n hn ) ] ⟩ ;
    choose! N₂ hN₂ using h_log_floor;
    exact ⟨ Finset.sup ( Finset.Iic K ) N₂ + 2, fun k hk n hn => by have := hN₂ k hk n ( by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ; rwa [ ge_iff_le, le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ] at this ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn k hk; specialize hN₁ k hk n ( by linarith [ Nat.le_max_left N₁ N₂ ] ) ; specialize hN₂ k hk n ( by linarith [ Nat.le_max_right N₁ N₂ ] ) ;
  refine le_trans hN₁ ?_;
  rw [ div_le_div_iff₀ ];
  · rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] at hN₂ <;> first | positivity | linarith;
  · refine lt_of_lt_of_le ?_ hN₂;
    exact mul_pos ( div_pos ( by positivity ) ( by positivity ) ) ( Real.log_pos ( by norm_cast; linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) );
  · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ;

/-
M_k * product ≤ (e^{-γ}+δ)/log(max(Y_{k+1}, n/Y_k)). Combined with log(max(...))≥ log(n)/2, this gives
M_k * product ≤ 2(e^{-γ}+δ)/log n.
-/
lemma wip_mertens_bound (lam : ℝ) (hlam : 1 < lam)
    (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        2 * (Real.exp (-γ) + δ) / Real.log n := by
  have := @mertens_product_estimate;
  obtain ⟨ X₀, hX₀ ⟩ := this ( δ / 2 ) ( half_pos hδ );
  refine ⟨ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2, fun n hn k => ?_ ⟩;
  -- Let $x = \max(Y_{k+1}, n/Y_k)$.
  set x := max (Y_val lam (k + 1)) (n / Y_val lam k) with hx;
  -- By definition of $x$, we have $M_k * \prod_{Y_{k+1}<p\le n/Y_k}(1-1/p) \le \prod_{p\le x}(1-1/p)$.
  have h_prod_le : M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) := by
    by_cases h : ⌊Y_val lam ( k + 1 ) ⌋₊ ≤ ⌊ ( n : ℝ ) / Y_val lam k ⌋₊ <;> simp_all +decide [ M_layer, primesUpTo ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_union, Finset.mem_filter ];
        · rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ ) <;> [ exact ⟨ le_trans ha₁ ( Nat.floor_mono <| le_max_left _ _ ), ha₂ ⟩ ; exact ⟨ le_trans ha₂ ( Nat.floor_mono <| le_max_right _ _ ), ha₃ ⟩ ];
        · grind;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    · rw [ max_eq_left ];
      · norm_num [ Finset.Ioc_eq_empty_of_le h.le ];
      · contrapose! h;
        exact Nat.floor_mono h.le;
  -- By definition of $x$, we have $x \geq \sqrt{\lambda n}$.
  have hx_ge_sqrt : x ≥ Real.sqrt (lam * n) := by
    have hx_ge_sqrt : Y_val lam (k + 1) * (n / Y_val lam k) ≥ lam * n := by
      unfold Y_val; ring_nf; norm_num [ show lam ≠ 0 by positivity ] ;
      nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( lam ^ k : ℝ ) ≠ 0 ) ( lam * n ) ];
    refine Real.sqrt_le_iff.mpr ⟨ ?_, ?_ ⟩;
    · exact le_max_of_le_left ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) );
    · cases max_cases ( Y_val lam ( k + 1 ) ) ( n / Y_val lam k ) <;> nlinarith [ show 0 ≤ Y_val lam ( k + 1 ) from by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ), show 0 ≤ ( n : ℝ ) / Y_val lam k from by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $\log x \geq \frac{1}{2} \log n$.
  have hlogx_ge_halflogn : Real.log x ≥ (1 / 2) * Real.log n := by
    have hlogx_ge_halflogn : Real.log x ≥ Real.log (Real.sqrt (lam * n)) := by
      exact Real.log_le_log ( Real.sqrt_pos.mpr ( mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by nlinarith ) ) ) ) hx_ge_sqrt;
    rw [ Real.log_sqrt ( by positivity ), Real.log_mul ( by positivity ) ( by norm_cast; nlinarith ) ] at hlogx_ge_halflogn ; linarith [ Real.log_nonneg hlam.le ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $x \geq X₀$.
  have hx_ge_X₀ : x ≥ X₀ := by
    refine le_trans ?_ hx_ge_sqrt;
    refine le_trans ?_ ( Real.sqrt_le_sqrt <| show lam * n ≥ ⌈X₀⌉₊ ^ 2 by nlinarith [ Nat.le_ceil X₀, show ( n : ℝ ) ≥ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2 by exact_mod_cast hn, show ( ⌈lam ^ 2⌉₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ] );
    rw [ Real.sqrt_sq ] <;> linarith [ Nat.le_ceil X₀ ];
  refine le_trans h_prod_le ?_;
  refine le_trans ( show ∏ p ∈ primesUpTo x, ( 1 - 1 / ( p : ℝ ) ) ≤ Real.exp ( -γ ) / Real.log x + δ / 2 / Real.log x from ?_ ) ?_;
  · linarith [ abs_le.mp ( hX₀ x hx_ge_X₀ ) ];
  · rw [ ← add_div, div_le_div_iff₀ ];
    · nlinarith [ Real.exp_pos ( -γ ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; nlinarith ) ];
    · exact lt_of_lt_of_le ( mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by nlinarith ) ) ) ) hlogx_ge_halflogn;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by nlinarith;

lemma wip_large_k (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : ε > 0) :
    ∃ K : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, K < k →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ 2 * (Real.exp (-γ) + ε / 2) / Real.log n := by
    apply wip_mertens_bound lam hlam (ε / 2) (half_pos hε);
  -- Choose K such that for all k > K, g_k ≥ 2(e^{-γ} + ε/2)/(e^{-γ} + ε).
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k : ℕ, k > K → g k ≥ 2 * (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
    exact Filter.eventually_atTop.mp ( hg.eventually_ge_atTop _ ) |> fun ⟨ K, hK ⟩ => ⟨ K, fun k hk => hK k hk.le ⟩;
  use K, N₁;
  intro n hn k hk; specialize hN₁ n hn k; specialize hK k hk; rw [ div_mul_eq_mul_div, div_le_iff₀ ] at * <;> try linarith [ hg1 k ];
  rw [ div_mul_eq_mul_div, le_div_iff₀ ] at *;
  · rw [ ge_iff_le, div_le_iff₀ ] at hK <;> nlinarith [ Real.exp_pos ( -γ ) ];
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith;
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith

/-- M_{λ,k}/g_k · ∏_{Y_{λ,k+1} < p ≤ n/Y_{λ,k}} (1-1/p) ≤ (e^{-γ}+o(1))/log n -/
theorem weighted_interval_product (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨K, N₂, hN₂⟩ := wip_large_k lam hlam g hg1 hg ε hε
  obtain ⟨N₁, hN₁⟩ := wip_finitely_many lam hlam g hg1 ε hε K
  exact ⟨max N₁ N₂, fun n hn k => by
    by_cases hk : k ≤ K
    · exact hN₁ n (le_of_max_le_left hn) k hk
    · exact hN₂ n (le_of_max_le_right hn) k (by omega)⟩

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/CommonProducts.lean` -/

section


noncomputable section
open Finset BigOperators Nat Real
set_option maxHeartbeats 800000

theorem high_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (k : ℕ) (A B : Finset ℕ) (n : ℕ)
    (hL : ∀ j, k < j → (L_common lam j A B).card ≤ m j) :
    ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ n).filter Nat.Prime).filter
        (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By layer_decomp_common_primes, each such p ∈ I_layer lam j for some j > k.
  have h_layer : ∀ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ j > k, p ∈ I_layer lam j := by
    apply layer_decomp_common_primes;
    linarith;
  choose! j hj using h_layer;
  -- By definition of $j$, we can rewrite the product as a product over the layers $j > k$.
  have h_prod_layers : ∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹ = ∏ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  -- By definition of $j$, we know that for each $j'$ in the image of $j$, the product over the primes in layer $j'$ is bounded by $E_{λ,j'}(m_{j'})$.
  have h_prod_layer_bound : ∀ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j' (m j') := by
    intros j' hj'
    have h_card : (Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty))).card ≤ m j' := by
      refine le_trans ?_ ( hL j' ?_ );
      · refine Finset.card_le_card ?_;
        simp +contextual [ Finset.subset_iff, L_common ];
        grind;
      · grind;
    convert prod_le_E_val lam j' ( m j' ) _ _ h_card using 1;
    grind;
  refine h_prod_layers ▸ le_trans ( Finset.prod_le_prod ?_ h_prod_layer_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]

/-
If |L_{λ,k}(A,B)| ≤ m_k for all k, then
    ∏_{p≤n, A[p]≠∅, B[p]≠∅} (1-1/p)⁻¹ ≤ D_{λ,m}.
-/
theorem euler_common_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (n : ℕ) (A B : Finset ℕ)
    (hL : ∀ k, (L_common lam k A B).card ≤ m k) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p =>
        Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By definition of $L_{\lambda,k}(A,B)$, we know that every prime $p$ in the product satisfies $p \leq Y_{\lambda,k+1}$.
  have h_subset : ∀ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ k, p ∈ I_layer lam k := by
    intro p hp; by_cases hp2 : p ≥ 2 <;> simp_all +decide [ I_layer ] ;
    · have h_log : ∃ k : ℕ, Y_val lam k ≤ p ∧ p < Y_val lam (k + 1) := by
        have h_unbounded : ∀ M : ℝ, ∃ k : ℕ, Y_val lam k > M := by
          exact fun M => by rcases pow_unbounded_of_one_lt ( M / 2 ) hlam with ⟨ k, hk ⟩ ; exact ⟨ k, by rw [ Y_val ] ; linarith ⟩ ;
        contrapose! h_unbounded;
        exact ⟨ p, fun k => Nat.recOn k ( by norm_num [ Y_val ] ; linarith ) h_unbounded ⟩;
      exact ⟨ h_log.choose, h_log.choose_spec.1, Nat.lt_ceil.mpr h_log.choose_spec.2 ⟩;
    · interval_cases p <;> simp_all +decide;
  choose! k hk using h_subset;
  have h_group : ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)), (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  have h_bound : ∀ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j (m j) := by
    intros j hj
    have h_subset : Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))) ⊆ L_common lam j A B := by
      simp +contextual [ Finset.subset_iff, L_common ];
      grind;
    apply prod_le_E_val;
    · exact fun x hx => Finset.mem_filter.mp ( h_subset hx ) |>.1;
    · exact le_trans ( Finset.card_le_card h_subset ) ( hL j );
  refine le_trans h_group <| le_trans ( Finset.prod_le_prod ?_ h_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]


theorem Pi_sieve_mul_le (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
  (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
  (n k : ℕ) (A B : Finset ℕ)
  (hk : ∀ j, k < j → (L_common lam j A B).card ≤ m j) :
  Pi_sieve n lam k A * Pi_sieve n lam k B ≤ (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ))) * D_val lam m := by
  have h_prod : (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹) ≤ D_val lam m := by
    apply high_product;
    · exact hlam;
    · exact hsumm;
    · assumption;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_prod ?_ );
  · unfold Pi_sieve;
    unfold P_sieve; simp +decide [ Finset.prod_filter ] ;
    rw [ ← div_eq_mul_inv, le_div_iff₀ ];
    · rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ];
      refine Finset.prod_le_prod ?_ ?_ <;> norm_num;
      · intro i hi₁ hi₂; split_ifs <;> norm_num;
        any_goals exact inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
        · exact mul_nonneg ( mul_nonneg ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
        · exact mul_self_nonneg _;
        · exact mul_self_nonneg _;
        · exact mul_self_nonneg _;
      · intro i hi₁ hi₂; split_ifs <;> norm_num;
        · aesop;
        · grind;
        · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
        · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
        · exact False.elim <| ‹¬ ( ( sdiv A i ).Nonempty ∧ ( sdiv B i ).Nonempty ) › ⟨ Finset.nonempty_of_ne_empty ‹_›, Finset.nonempty_of_ne_empty ‹_› ⟩;
    · refine Finset.prod_pos fun p hp => ?_;
      split_ifs <;> norm_num;
      exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt ‹_›;
  · exact Finset.prod_nonneg fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;

end

end


/-! ### Upstream module `src/latest/Util/MertensThird.lean` -/

section

/-
Below you can find a formalization of (a version of) Mertens third theorem,
which is used in the conditional Lean proofs of Erdős Problems #237
(https://www.erdosproblems.com/237) and #1141
(https://www.erdosproblems.com/1141) that you can find here:

https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean

https://github.com/yuta0x89/ErdosProblems/blob/9eebc7a51466e6ad1b57318302cdc821d30df4ff/Erdos1141.lean

The formalization of Mertens third theorem was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

-/



open Finset ArithmeticFunction Real
open scoped BigOperators

set_option maxRecDepth 4000

/-- ψ(n) = Σ_{m=1}^{n} Λ(m), the first Chebyshev function. -/
noncomputable def _root_.chebyshevPsi' (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), vonMangoldt m

/-- L_n = lcm(1, 2, ..., n). -/
def _root_.lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm _root_.id

/-- S(n) = Σ_{m=2}^{n} Λ(m)/m. -/
noncomputable def _root_.sumS (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / m

/-- T(n) = Σ_{m=2}^{n} Λ(m)/(m * log m). -/
noncomputable def _root_.sumT (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, vonMangoldt m / (m * Real.log m)

/-- P(n) = ∏_{p ≤ n, p prime} (1 - 1/p). -/
noncomputable def _root_.prodP (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-! # Lemma: Central Binomial Coefficient Bounds -/

lemma _root_.centralBinom_le_four_pow (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) r ≤ 4 ^ r := by
  rw [show 4 ^ r = (2 : ℕ) ^ (2 * r) by norm_num [pow_mul]]
  rw [← Nat.sum_range_choose]
  exact Finset.single_le_sum (fun x _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by linarith))

lemma _root_.choose_odd_le_four_pow (r : ℕ) (_hr : 1 ≤ r) :
    Nat.choose (2 * r + 1) r ≤ 4 ^ r := by
  exact Nat.choose_middle_le_pow r

/-! # LCM helpers -/

lemma _root_.lcmRange_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < lcmRange n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

lemma _root_.lcmRange_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ lcmRange n := by
  exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hm, hmn ⟩ )

/-! # LCM Divisibility Lemmas -/

set_option linter.flexible false in
lemma _root_.lcmRange_dvd_even (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r) ∣ lcmRange r * Nat.choose (2 * r) r := by
  -- By definition of lcmRange, we need to show that for every prime power $p^a$ dividing $m \in (1, 2r]$, $p^a$ divides $lcmRange(r) * \binom{2r}{r}$.
  have h_div : ∀ m ∈ Finset.Icc 1 (2 * r), ∀ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm p hp
    by_cases hpa : p ^ Nat.factorization m p ≤ r;
    · exact dvd_mul_of_dvd_left ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), hpa ⟩ ) ) _;
    · -- Since $p^a > r$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p ^ (Nat.factorization m p - 1) ≤ r := by
        rcases k : Nat.factorization m p with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.1.two_le, Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show m ≥ p ^ ( Nat.factorization m p ) from Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd m p ), show p ^ ( Nat.factorization m p ) = p * p ^ ‹_› from by rw [ ← pow_succ', k ] ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r)$.
      have hpa_minus_one_div : p ^ (Nat.factorization m p - 1) ∣ lcmRange r := by
        exact lcmRange_dvd_of_le ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hpa_minus_one;
      -- Since $p^a > r$, we have $p \mid \binom{2r}{r}$.
      have hpa_div_choose : p ∣ Nat.choose (2 * r) r := by
        have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p ≥ 1 := by
          have hpa_div_choose : Nat.factorization (Nat.choose (2 * r) r) p = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * r) + 1), (Nat.floor ((2 * r) / p ^ k) - 2 * Nat.floor (r / p ^ k))) := by
            have := Fact.mk ( Nat.prime_of_mem_primeFactors hp ) ; rw [ Nat.factorization_def ];
            · rw [ padicValNat_choose ];
              any_goals exact Nat.lt_succ_self _;
              · norm_num [ two_mul, Nat.add_div ];
                rw [ Finset.card_filter ];
                refine Finset.sum_congr rfl fun x hx => ?_
                rw [ Nat.add_div ( pow_pos ( Nat.Prime.pos ( Nat.prime_of_mem_primeFactors hp ) ) _ ) ] ; aesop;
              · linarith;
            · exact Nat.prime_of_mem_primeFactors hp;
          rw [hpa_div_choose];
          refine le_trans ?_ ( Finset.single_le_sum ( fun x hx => Nat.zero_le _ ) ( Finset.mem_Ico.mpr ⟨ Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( show m.factorization p ≠ 0 from Finsupp.mem_support_iff.mp hp ) ), Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( show p ^ m.factorization p ≤ 2 * r from ?_ ) ) ⟩ ) )
          · norm_num [ Nat.div_eq_of_lt ( show r < p ^ m.factorization p from lt_of_not_ge hpa ) ];
            exact Nat.div_pos ( by linarith [ Finset.mem_Icc.mp hm, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd m p ) ] ) ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ );
          · exact le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith [ Finset.mem_Icc.mp hm ] );
        exact Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) ( Nat.ordProj_dvd _ _ );
      convert Nat.mul_dvd_mul hpa_minus_one_div hpa_div_choose using 1 ; rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ) ];
  -- Since every prime power in the lcm divides the product, the lcm itself must divide the product.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r), m ∣ lcmRange r * Nat.choose (2 * r) r := by
    intro m hm
    have h_prod_div : ∏ p ∈ Nat.primeFactors m, p ^ Nat.factorization m p ∣ lcmRange r * Nat.choose (2 * r) r := by
      -- The least common multiple of a set of numbers is equal to their product divided by their greatest common divisor.
      have h_lcm_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p q : ℕ, p ∈ S → q ∈ S → p ≠ q → Nat.gcd (p ^ f p) (q ^ f q) = 1) → Finset.lcm S (fun p => p ^ f p) = ∏ p ∈ S, p ^ f p := by
        intros S f hprime hgcd; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => hgcd _ _ ( Or.inl rfl ) ( Or.inr hp ) <| by aesop;
      rw [ ← h_lcm_prod ( fun p hp => Nat.prime_of_mem_primeFactors hp ) ( fun p q hp hq hpq => by simpa [ hpq ] using Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors hp ) ( Nat.prime_of_mem_primeFactors hq ) ) ];
      exact Finset.lcm_dvd fun p hp => h_div m hm p hp;
    rwa [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ];
  exact Finset.lcm_dvd h_lcm_div

set_option linter.flexible false in
lemma _root_.lcmRange_dvd_odd (r : ℕ) (hr : 1 ≤ r) :
    lcmRange (2 * r + 1) ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
  -- For any prime power $p^a \leq 2r+1$, we need to show that $p^a$ divides $lcmRange(r+1) * (2r+1 choose r)$.
  have h_prime_power : ∀ p a : ℕ, Nat.Prime p → p^a ≤ 2 * r + 1 → p^a ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro p a hp ha
    by_cases hpa : p^a ≤ r + 1;
    · exact dvd_mul_of_dvd_left
        (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, hpa ⟩))
        (Nat.choose (2 * r + 1) r)
    · -- Since $p^a > r + 1$, we have $p^{a-1} \leq r$.
      have hpa_minus_one : p^(a-1) ≤ r := by
        rcases a <;> simp_all +decide [ pow_succ' ];
        nlinarith [ hp.two_le ];
      -- Since $p^{a-1} \leq r$, we have $p^a \mid \binom{2r+1}{r}$.
      have hpa_div_choose : p^a ∣ Nat.choose (2 * r + 1) r * p^(a-1) := by
        have hpa_div_choose : padicValNat p (Nat.choose (2 * r + 1) r) ≥ 1 := by
          have := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine Finset.card_pos.mpr ⟨ a, ?_ ⟩ ; norm_num;
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt ha ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        have hpa_div_choose : p ∣ Nat.choose (2 * r + 1) r := by
          contrapose! hpa_div_choose; simp_all +decide ;
        rcases a with ( _ | a ) <;> simp_all +decide [ pow_succ', mul_dvd_mul ];
      -- Since $p^{a-1} \leq r$, we have $p^{a-1} \mid lcmRange(r+1)$.
      have hpa_minus_one_div_lcm : p^(a-1) ∣ lcmRange (r + 1) := by
        have hpa_minus_one_div_lcm : p^(a-1) ∈ Finset.Icc 1 (r + 1) := by
          exact Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, by linarith ⟩;
        exact Finset.dvd_lcm hpa_minus_one_div_lcm;
      exact dvd_trans hpa_div_choose ( by rw [ mul_comm ] ; exact mul_dvd_mul hpa_minus_one_div_lcm dvd_rfl );
  -- By definition of lcmRange, lcmRange (2 * r + 1) divides the product of all numbers in the range 1 to 2r+1.
  have h_lcm_div : ∀ m ∈ Finset.Icc 1 (2 * r + 1), m ∣ lcmRange (r + 1) * Nat.choose (2 * r + 1) r := by
    intro m hm; rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ m <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      have := h_prime_power p ( Nat.factorization m p ) hp ( Nat.le_trans ( Nat.le_of_dvd hm.1 ( Nat.ordProj_dvd _ _ ) ) hm.2 ) ; rw [ ← Nat.factorization_le_iff_dvd ] at this <;> simp_all +decide ;
      exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
    · linarith [ Finset.mem_Icc.mp hm ];
    · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, Nat.ne_of_gt <| Nat.choose_pos <| by linarith ⟩;
  exact Finset.lcm_dvd fun x hx => h_lcm_div x hx

/-! # LCM Bound: L_n ≤ 4^n -/

lemma _root_.lcmRange_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmRange n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases h₂ : n ≤ 4;
  · interval_cases n <;> decide;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
    · -- By lcmRange_dvd_even, lcmRange(2k) | lcmRange(k) * choose(2k,k).
      have h_div : lcmRange (2 * k) ∣ lcmRange k * Nat.choose (2 * k) k := by
        exact lcmRange_dvd_even k ( by linarith );
      -- Since $\binom{2k}{k} \leq 4^k$, we have $lcmRange (2 * k) \leq lcmRange k * 4^k$.
      have h_bound : lcmRange (2 * k) ≤ lcmRange k * 4 ^ k := by
        refine le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmRange_pos k ( by linarith ) ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) ?_
        exact Nat.mul_le_mul_left _ ( centralBinom_le_four_pow k ( by linarith ) );
      exact h_bound.trans ( by rw [ pow_mul' ] ; exact Nat.mul_le_mul_right _ ( ih k ( by linarith ) ( by linarith ) ) |> le_trans <| by ring_nf; norm_num );
    · -- By lcmRange_dvd_odd, lcmRange(2k+1) | lcmRange(k+1) * choose(2k+1,k).
      have h_div : lcmRange (2 * k + 1) ∣ lcmRange (k + 1) * Nat.choose (2 * k + 1) k := by
        convert lcmRange_dvd_odd k ( by linarith ) using 1;
      -- By choose_odd_le_four_pow, choose(2k+1,k) ≤ 4^k.
      have h_choose : Nat.choose (2 * k + 1) k ≤ 4 ^ k := by
        convert choose_odd_le_four_pow k ( by linarith ) using 1;
      refine le_trans ( Nat.le_of_dvd ?_ h_div ) ?_
      · exact mul_pos ( lcmRange_pos _ ( by linarith ) ) ( Nat.choose_pos ( by linarith ) );
      · exact le_trans ( Nat.mul_le_mul ( ih _ ( by linarith ) ( by linarith ) ) h_choose ) ( by ring_nf; norm_num )

/-! # Chebyshev ψ bound -/

set_option linter.flexible false in
lemma _root_.chebyshevPsi_eq_log_lcmRange (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi' n = Real.log (lcmRange n) := by
  -- By definition of ψ, we know that ψ(n) = Σ_{m=0}^n Λ(m)
  have h_psi_def : chebyshevPsi' n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.log p n * Real.log p := by
    have h_psi_def : chebyshevPsi' n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p) := by
      unfold chebyshevPsi';
      have h_sum_floor : ∑ m ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p ^ k)) := by
        have h_sum_floor : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.range (n + 1)) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
          ext m;
          simp [ArithmeticFunction.vonMangoldt];
          constructor;
          · intro hm;
            obtain ⟨ p, k, hp, hk, rfl ⟩ := hm.2.1;
            exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm.1 ⟩, rfl ⟩;
          · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
            exact ⟨ Nat.pow_le_of_le_log ( by linarith ) hk₂, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
        rw [ ← Finset.sum_filter_ne_zero, h_sum_floor, Finset.sum_biUnion ];
        · exact Finset.sum_congr rfl fun p hp => Finset.sum_image <| fun a ha b hb h => Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) h;
        · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
          intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      convert h_sum_floor using 3;
      rw [ ArithmeticFunction.vonMangoldt_apply ];
      rw [ if_pos ];
      · rw [ Nat.Prime.pow_minFac ] <;> aesop;
      · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] );
    aesop;
  -- By definition of $lcmRange$, we know that $lcmRange n = \prod_{p \leq n} p^{e_p(n)}$ where $e_p(n) = \lfloor \log_p n \rfloor$.
  have h_lcm_def : lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
    clear h_psi_def;
    -- By definition of lcmRange, we know that lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n).
    have h_lcmRange_def : ∀ m ∈ Finset.Icc 1 n, m ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) := by
      intro m hm; rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hm ] : m ≠ 0 ) ] ;
      rw [ ← Finset.prod_sdiff <| show m.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) <| Finset.mem_Icc.mp hm |>.2, Nat.prime_of_mem_primeFactors hp ⟩ ];
      exact dvd_mul_of_dvd_right ( Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p <| Nat.le_log_of_pow_le ( Nat.prime_of_mem_primeFactors hp |> Nat.Prime.one_lt ) <| Nat.le_trans ( Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hm ] ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hm |>.2 ) _;
    refine Nat.dvd_antisymm ?_ ?_
    · exact Finset.lcm_dvd fun x hx => h_lcmRange_def x hx;
    · -- By definition of lcmRange, we know that lcmRange n is divisible by each prime power p^k where p is prime and k is such that p^k ≤ n.
      have h_lcmRange_div : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.log p n) ∣ lcmRange n := by
        intros p hp
        have h_div : p ^ (Nat.log p n) ≤ n := by
          exact Nat.pow_log_le_self p ( by linarith );
        exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), h_div ⟩ );
      -- The least common multiple of a set of numbers is equal to the product of the highest powers of all primes dividing any of the numbers.
      have h_lcm_eq_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Finset.lcm S (fun p => p ^ (Nat.log p n)) = ∏ p ∈ S, p ^ (Nat.log p n) := by
        intros S hS; induction S using Finset.induction <;> simp_all +decide ;
        exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow _ _ <| hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop;
      rw [ ← h_lcm_eq_prod fun p hp => Finset.mem_filter.mp hp |>.2 ];
      exact Finset.lcm_dvd h_lcmRange_div;
  rw [ h_psi_def, h_lcm_def, Nat.cast_prod, Real.log_prod ] <;> aesop

lemma _root_.chebyshevPsi_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi' n ≤ 2 * n * Real.log 2 := by
  have h_log : Real.log (lcmRange n) ≤ Real.log (4 ^ n) := by
    gcongr;
    · exact_mod_cast lcmRange_pos n hn;
    · exact_mod_cast lcmRange_le_four_pow n hn;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, pow_right_comm ] at h_log ; norm_num at *;
  rw [ chebyshevPsi_eq_log_lcmRange n hn ] ; linarith

/-! # S(n) Upper Bound -/

/-
S(n) ≤ (log(n!) + ψ(n)) / n
-/
set_option linter.flexible false in
lemma _root_.sumS_le_basic (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≤ (Real.log (n.factorial) + chebyshevPsi' n) / n := by
  -- By the properties of logarithms and the definition of S(n), we can rewrite the inequality.
  have h_rewrite : ∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n ≤ Real.log (Nat.factorial n) + ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    -- We'll use that $\sum_{m=1}^n \Lambda(m) \left\lfloor \frac{n}{m} \right\rfloor = \log(n!)$.
    have h_log_factorial : ∑ m ∈ Finset.Icc 1 n, (vonMangoldt m : ℝ) * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
      -- By definition of von Mangoldt function, we know that $\sum_{d \mid m} \Lambda(d) = \log m$.
      have h_von_mangoldt : ∀ m : ℕ, 1 ≤ m → ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = Real.log m := by
        exact fun m a => vonMangoldt_sum;
      -- Applying the definition of von Mangoldt function to the sum.
      have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * Nat.floor (n / d) := by
        have h_sum_von_mangoldt : ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) = ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d : ℝ) * (if d ∣ m then 1 else 0) := by
          rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          simp +zetaDelta at *;
          intro x hx₁ hx₂; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ Nat.mem_divisors ] ;
          exact ⟨ fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hx₁, Nat.le_trans ( Nat.le_of_dvd hx₁ h.1 ) hx₂ ⟩, h.1 ⟩, fun h => ⟨ h.2, by linarith ⟩ ⟩;
        simp_all +decide [ Finset.sum_ite ];
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 n ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( n / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ];
        · norm_num;
        · ext y; simp [Finset.mem_image];
          exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self n x ] ⟩, by simp +decide ⟩ ⟩;
      rw [ ← h_sum_von_mangoldt, Finset.sum_congr rfl fun m hm => h_von_mangoldt m <| Finset.mem_Icc.mp hm |>.1 ];
      erw [ ← Real.log_prod ] <;> norm_cast <;> norm_num;
      · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
      · grind;
    -- Applying the inequality $\frac{n}{m} \leq \left\lfloor \frac{n}{m} \right\rfloor + 1$ to each term in the sum, we get:
    have h_ineq : ∀ m ∈ Finset.Icc 2 n, (vonMangoldt m : ℝ) * (n / m) ≤ (vonMangoldt m : ℝ) * Nat.floor (n / m) + (vonMangoldt m : ℝ) := by
      intros m hm
      have h_floor : (n / m : ℝ) ≤ Nat.floor (n / m) + 1 := by
        rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n m, Nat.mod_lt n ( by linarith [ Finset.mem_Icc.mp hm ] : 0 < m ), Nat.lt_floor_add_one ( n / m ) ];
      simpa only [ mul_add, mul_one ] using mul_le_mul_of_nonneg_left h_floor <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ;
    refine le_trans ( Finset.sum_le_sum fun m hm => by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_ineq m hm ) ?_;
    rw [ ← h_log_factorial, Finset.sum_add_distrib ];
    have hsub : Finset.Icc 2 n ⊆ Finset.Icc 1 n :=
      Finset.Icc_subset_Icc (by norm_num) le_rfl
    exact add_le_add
      (by
        simpa [mul_comm] using
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
            mul_nonneg (Nat.cast_nonneg (n / x)) (ArithmeticFunction.vonMangoldt_nonneg (n := x))))
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg (n := x));
  have h_left :
      (∑ m ∈ Finset.Icc 2 n, (vonMangoldt m / m : ℝ) * n) / n = sumS n := by
    rw [Finset.sum_div]
    unfold sumS
    exact Finset.sum_congr rfl fun _ _ => by
      rw [mul_div_cancel_right₀ _ (by positivity)]
  have h_psi : chebyshevPsi' n = ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
    unfold chebyshevPsi'
    erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
  simpa [h_left, h_psi] using div_le_div_of_nonneg_right h_rewrite (Nat.cast_nonneg n)

/-
log(n!) ≤ n*log(n) - n + 1 + log(n)
-/
set_option linter.flexible false in
lemma _root_.log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_comm ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ↑‹ℕ› : ℝ ) / ( ↑‹ℕ› + 1 ) );
  rw [ Real.log_div ] at this <;> first | positivity | nlinarith [ mul_div_cancel₀ ( ( ↑‹ℕ› : ℝ ) : ℝ ) ( by positivity : ( ↑‹ℕ› + 1 : ℝ ) ≠ 0 ) ] ;

lemma _root_.sumS_le_logn_plus (n : ℕ) (hn : 200 ≤ n) :
    sumS n ≤ Real.log n + 0.418 := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : Real.log (n.factorial) + chebyshevPsi' n ≤ n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n := by
    linarith [ log_factorial_le n ( by linarith ), chebyshevPsi_le n ( by linarith ) ];
  -- Divide both sides by $n$ and simplify the expression.
  have h_div : sumS n ≤ Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      sumS n ≤ (Real.log (n.factorial) + chebyshevPsi' n) / n :=
        sumS_le_basic n (by linarith)
      _ ≤ (n * Real.log n + 2 * n * Real.log 2 - n + 1 + Real.log n) / n :=
        div_le_div_of_nonneg_right h_final (Nat.cast_nonneg _)
      _ = Real.log n + 2 * Real.log 2 - 1 + (Real.log n + 1) / n := by
        field_simp [hn0]
        ring
  -- We'll use that $Real.log n + 1 \leq Real.log 200 + 1$ for $n \geq 200$.
  have h_log_bound : (Real.log n + 1) / n ≤ (Real.log 200 + 1) / 200 := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) / 200 );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ ( by norm_cast : ( 200 :ℝ ) ≤ n ), Real.le_log_iff_exp_le ( by positivity : ( 0 :ℝ ) < 200 ) |>.2 <| show ( Real.exp 1 :ℝ ) ≤ 200 by exact le_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ];
  -- We'll use that $Real.log 200 < 5.3$.
  have h_log_200 : Real.log 200 < 5.3 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to remove the fraction.
    suffices h_exp : (200 : ℝ) ^ 10 < Real.exp 53 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 53 = ( Real.exp 1 ) ^ 53 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-! # Tail bound -/

/-
-log P(n) ≤ T(n) + 1/10 via log series truncation
-/
set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- The generated tail-bound proof uses large `norm_num` and summability terms.
lemma _root_.neg_log_prodP_le_sumT_plus (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) ≤ sumT n + 1/10 := by
  -- Let's rewrite the sum in terms of the prime number theorem and the bound we have.
  have h_sum_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ 1 / 10 := by
    -- For each prime $p$, the tail $\sum_{k > \lfloor \log_p n \rfloor} \frac{1}{k p^k}$ is bounded by $\frac{1}{(K+1)(p-1)p^K}$ where $K = \lfloor \log_p n \rfloor$.
    have h_tail_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
      intro p hp
      have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k) ≤ ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) := by
        have h_tail_bound : -Real.log (1 - 1 / (p : ℝ)) = ∑' k : ℕ, 1 / ((k + 1) * (p : ℝ) ^ (k + 1)) := by
          have := @Real.hasSum_pow_div_log_of_abs_lt_one ( 1 / ( p : ℝ ) ) ?_ <;> norm_num at *;
          · exact this.tsum_eq.symm ▸ rfl;
          · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.2.one_lt;
        erw [ h_tail_bound, ← Summable.sum_add_tsum_nat_add ( Nat.log p n ) ];
        · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          norm_num [ Finset.sum_range_succ' ];
        · norm_num +zetaDelta at *;
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.2 hp.2.one_lt;
      -- We'll use the fact that $\sum_{k=K+1}^{\infty} \frac{1}{k p^k} \leq \frac{1}{(K+1)p^K} \sum_{k=0}^{\infty} \frac{1}{p^k}$.
      have h_sum_bound : ∑' k : ℕ, 1 / ((Nat.log p n + k + 1) * (p : ℝ) ^ (Nat.log p n + k + 1)) ≤ 1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) * ∑' k : ℕ, (1 / (p : ℝ)) ^ k := by
        rw [ ← tsum_mul_left ];
        refine Summable.tsum_le_tsum ?_ ?_ ?_
        · intro i; rw [ div_pow ] ; rw [ div_mul_div_comm ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
          · exact Or.inr ⟨ ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩, pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ⟩;
        · norm_num +zetaDelta at *;
          have hgeom :
              Summable (((fun q : ℕ => ((p : ℝ) ^ q)⁻¹) ∘
                fun k : ℕ => Nat.log p n + k + 1)) := by
            exact Summable.comp_injective
              (by
                simpa using
                  summable_geometric_of_lt_one (by positivity)
                    (inv_lt_one_of_one_lt₀ (by
                      norm_cast
                      exact hp.2.one_lt)))
              (by
                intro a b h
                exact Nat.add_left_cancel (Nat.add_right_cancel h))
          exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun k => mul_le_of_le_one_right ( by positivity ) <| inv_le_one_of_one_le₀ <| by linarith ) <| by
            simpa [Function.comp_def] using hgeom
        · exact Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
      calc
        -Real.log (1 - 1 / (p : ℝ)) -
            ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)
            ≤
              1 / ((Nat.log p n + 1) * (p : ℝ) ^ (Nat.log p n + 1)) *
                ∑' k : ℕ, (1 / (p : ℝ)) ^ k :=
          h_tail_bound.trans h_sum_bound
        _ = 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) := by
          have hp_gt_one : (1 : ℝ) < p := by
            norm_cast
            exact Nat.Prime.one_lt (Finset.mem_filter.mp hp |>.2)
          rw [tsum_geometric_of_lt_one (r := 1 / (p : ℝ)) (by positivity)
            (by simpa [one_div] using inv_lt_one_of_one_lt₀ hp_gt_one)]
          ring_nf
          rw [ ← mul_inv ]
          congr
          nlinarith only [
            inv_mul_cancel_left₀
              ( show ( p : ℝ ) ≠ 0 by
                  norm_cast
                  exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) )
              ( p ^ Nat.log p n ),
            inv_mul_cancel₀
              ( show ( p : ℝ ) ≠ 0 by
                  norm_cast
                  exact Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ),
            show ( p : ℝ ) ≥ 2 by
              norm_cast
              exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ]
    -- Split the sum into two parts: one for primes $p \leq 13$ and one for primes $p > 13$.
    have h_split_sum : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (-Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p n), 1 / (k * (p : ℝ) ^ k)) ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ) ^ 1)) := by
      refine le_trans ( Finset.sum_le_sum h_tail_bound ) ?_;
      have h_split_sum : Finset.filter Nat.Prime (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range 14) ∪ Finset.filter Nat.Prime (Finset.Icc 17 n) := by
        simp +decide [ Finset.subset_iff ];
        exact fun p hp₁ hp₂ => if h : p < 14 then Or.inl ⟨ h, hp₂ ⟩ else Or.inr ⟨ ⟨ not_lt.mp fun h' => by interval_cases p <;> trivial, hp₁ ⟩, hp₂ ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split_sum ?_ ) ?_;
      · exact fun _ _ _ => one_div_nonneg.mpr ( mul_nonneg ( mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by positivity ) );
      · rw [ Finset.sum_union ];
        · gcongr;
          all_goals norm_num at *;
          any_goals linarith [ Nat.Prime.one_lt ( by tauto ) ];
          · exact mul_pos ( mul_pos two_pos ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ( Nat.cast_pos.mpr ( by linarith ) );
          · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( mod_cast Nat.Prime.pos ( by tauto ) ) );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
          · exact Nat.le_log_of_pow_le ( by linarith ) ( by linarith );
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- For primes $p \leq 13$, we can bound the sum individually.
    have h_small_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.range 14), 1 / ((Nat.log p n + 1) * (p - 1) * (p : ℝ) ^ (Nat.log p n)) ≤ 1 / 50 := by
      norm_num [ Finset.sum_filter, Finset.sum_range_succ ];
      -- Since $n \geq 200$, we have $\log_2 n \geq 7$, $\log_3 n \geq 4$, $\log_5 n \geq 3$, $\log_7 n \geq 2$, $\log_{11} n \geq 2$, and $\log_{13} n \geq 2$.
      have h_log_bounds : Nat.log 2 n ≥ 7 ∧ Nat.log 3 n ≥ 4 ∧ Nat.log 5 n ≥ 3 ∧ Nat.log 7 n ≥ 2 ∧ Nat.log 11 n ≥ 2 ∧ Nat.log 13 n ≥ 2 := by
        exact ⟨ Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ), Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ⟩;
      refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 2 n : ℝ ) + 1 ≥ 8 by norm_cast; linarith ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 3 n : ℝ ) + 1 ≥ 5 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 5 n : ℝ ) + 1 ≥ 4 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 7 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 11 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( show ( Nat.log 13 n : ℝ ) + 1 ≥ 3 by norm_cast; linarith ) ) ( by positivity ) ) ( by positivity ) ) ) ?_ ; norm_num;
      exact le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.1 ) ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.1 ) ) ( by positivity ) ) ) ( mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) h_log_bounds.2.2.2.2.2 ) ) ( by positivity ) ) ) ( by norm_num );
    -- For primes $p > 13$, we can bound the sum using the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
    have h_large_primes : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 17 (n)), 1 / ((1 + 1) * (p - 1) * (p : ℝ)) ≤ 1 / 32 := by
      -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)} \leq \frac{1}{32}$.
      have h_large_primes_bound : ∑ p ∈ Finset.Icc 17 n, (1 / ((p - 1) * (p : ℝ))) ≤ 1 / 16 := by
        -- We'll use the fact that $\sum_{p \geq 17} \frac{1}{p(p-1)}$ is a telescoping series.
        have h_telescoping : ∀ m : ℕ, 17 ≤ m → ∑ p ∈ Finset.Icc 17 m, (1 / ((p - 1) * (p : ℝ))) = 1 / 16 - 1 / (m : ℝ) := by
          intro m hm; induction hm <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 16 _, _ = _› ] ; norm_num;
          -- Combine and simplify the terms on the left-hand side.
          field_simp
          ring;
        exact h_telescoping n ( by linarith ) ▸ sub_le_self _ ( by positivity );
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith [ Finset.mem_Icc.1 ‹_› ] ) ) ) ) ) ( by norm_num ) ) ( by linarith );
    norm_num at * ; linarith;
  convert add_le_add_left h_sum_bound ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( n + 1 ) ), ∑ k ∈ Finset.Icc 1 ( Nat.log p n ), 1 / ( k * ( p : ℝ ) ^ k ) ) using 1;
  · unfold prodP; rw [ Real.log_prod ] <;> norm_num;
    exact fun p hp hp' => sub_ne_zero_of_ne <| by aesop;
  · rw [ add_comm, sumT ];
    -- Let's rewrite the sum $\sum_{m=2}^n \frac{\Lambda(m)}{m \log m}$ using the definition of $\Lambda$.
    have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (ArithmeticFunction.vonMangoldt (p^k) : ℝ) / (p^k * Real.log (p^k)) := by
      have h_sum_eq : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p n))) := by
        ext m; simp [ArithmeticFunction.vonMangoldt];
        constructor;
        · rintro ⟨ ⟨ hm₁, hm₂ ⟩, hm₃, hm₄, hm₅, hm₆ ⟩;
          obtain ⟨ p, k, hp, hk, rfl ⟩ := hm₃;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hm₂ ⟩, rfl ⟩;
        · rintro ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
          exact ⟨ ⟨ one_lt_pow₀ hp₂.one_lt ( by linarith ), Nat.pow_le_of_le_log ( by linarith ) hk₂ ⟩, hp₂.isPrimePow.pow ( by linarith ), Nat.ne_of_gt ( Nat.minFac_pos _ ), ne_of_gt ( one_lt_pow₀ hp₂.one_lt ( by linarith ) ), by linarith ⟩;
      have h_sum_eq : ∑ m ∈ Finset.Icc 2 n, (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) = ∑ m ∈ Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 2 n), (ArithmeticFunction.vonMangoldt m : ℝ) / (m * Real.log m) := by
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      rw [ h_sum_eq, ‹ { m ∈ Icc 2 n | Λ m ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
    rw [ h_sum_eq ];
    refine congr rfl ( Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun k hk => ?_ )
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.pow_minFac ] <;> norm_num [ Nat.Prime.ne_zero ( Finset.mem_filter.mp hp |>.2 ) ];
      · rw [ Nat.Prime.minFac_eq ( Finset.mem_filter.mp hp |>.2 ) ] ; ring_nf;
        rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ), one_mul ];
      · grind;
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hk ] )

/-! ### Helper lemmas for sumT_sub_199_bound -/

set_option linter.flexible false in
private lemma _root_.log_factorial_ge' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≥ n * Real.log n - n + 1 := by
  induction hn <;> simp_all +decide [ Nat.factorial ]
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm; rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( by positivity ) ]
    nlinarith [ Real.add_one_le_exp ( 1 / ( m : ℝ ) ), one_div_mul_cancel ( by positivity : ( m : ℝ ) ≠ 0 ) ]
  have := h_log _ ‹_›; norm_num at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ]

set_option linter.flexible false in
private lemma _root_.sumS_ge_log_sub_one (n : ℕ) (hn : 2 ≤ n) :
    sumS n ≥ Real.log n - 1 := by
  have h_sum_floor : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) = Real.log (Nat.factorial n) := by
    have h_sum_floor : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log (Nat.factorial n) := by
      have h_sum_floor : ∀ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = Real.log k := by
        exact fun _ _ => vonMangoldt_sum
      rw [ Finset.sum_congr rfl h_sum_floor ]
      exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; linarith
    have h_interchange : ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors k, vonMangoldt d = ∑ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, vonMangoldt d * (if d ∣ k then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ]
      simp +contextual [ Finset.sum_ite ]
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 n ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.le_of_dvd hx₁ <| Nat.dvd_of_mem_divisors hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop
    have h_inner : ∀ d ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then 1 else 0) = Nat.floor (n / d) := by
      intros d hd
      have h_divisors : Finset.filter (fun k => d ∣ k) (Finset.Icc 1 n) = Finset.image (fun k => d * k) (Finset.Icc 1 (n / d)) := by
        ext k; simp [Finset.mem_image]
        exact ⟨ fun h => ⟨ k / d, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hd |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hd |>.1 ], by nlinarith [ Finset.mem_Icc.mp hd |>.2, Nat.div_mul_le_self n d ] ⟩, by norm_num ⟩ ⟩
      simp_all +decide [ Finset.sum_ite ]
      rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( by linarith ) hxy ] ; aesop
    simp_all +decide [ Finset.sum_ite ]
    exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; ring ) h_sum_floor
  have h_floor_le : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m * Nat.floor (n / m) ≤ n * ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := by
    rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun x hx => ?_ ; rcases eq_or_ne x 0 with rfl | hx' <;> simp_all +decide ; ring_nf
    rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by rw [ ← div_eq_mul_inv ] ; exact ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n x ] ) ) ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ ArithmeticFunction.vonMangoldt_apply ] ; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) = sumS n := by
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop
  nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), log_factorial_ge' n ( by linarith ) ]

private lemma _root_.sumS_mono {a b : ℕ} (h : a ≤ b) : sumS a ≤ sumS b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right h ) fun _ _ _ ↦ div_nonneg ( by
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( by norm_cast; linarith [ Finset.mem_Icc.mp ‹_› ] )

private lemma _root_.div_sub_le_log_sub' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h_mul : b - a ≤ b * (Real.log b - Real.log a) := by
    have := Real.log_le_sub_one_of_pos ( div_pos ha ( show 0 < b by linarith ) )
    rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ a ( by linarith : b ≠ 0 ) ]
  rwa [ div_le_iff₀' ( by linarith ) ]

set_option linter.flexible false in
private lemma _root_.sum_log_ratio_le_log_log' (a n : ℕ) (ha : 3 ≤ a) (hn : a ≤ n) :
    ∑ m ∈ Finset.Ico a n,
      (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1) ≤
    Real.log (Real.log n) - Real.log (Real.log a) := by
  have h_term : ∀ m ∈ Finset.Ico a n, (Real.log (m + 1) - Real.log m) / Real.log (m + 1) ≤ Real.log (Real.log (m + 1)) - Real.log (Real.log m) := by
    intro m hm
    rw [ ← Real.log_div ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ( ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ]
    convert Real.one_sub_inv_le_log_of_pos _ using 1
    · rw [ inv_div, sub_div, div_self <| ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ]
    · exact div_pos ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) )
  calc
    ∑ m ∈ Finset.Ico a n,
        (Real.log (↑m + 1) - Real.log m) / Real.log (↑m + 1)
        ≤ ∑ m ∈ Finset.Ico a n,
            (Real.log (Real.log (m + 1)) - Real.log (Real.log m)) :=
      Finset.sum_le_sum h_term
    _ = Real.log (Real.log n) - Real.log (Real.log a) := by
      let F : ℕ → ℝ := fun m => Real.log (Real.log m)
      have htel : ∑ m ∈ Finset.Ico a n, (F (m + 1) - F m) = F n - F a := by
        induction n, hn using Nat.le_induction with
        | base =>
            simp [F]
        | succ n hn ih =>
            rw [Finset.sum_Ico_succ_top hn,
              ih (fun m hm => h_term m (Finset.mem_Ico.mpr
                ⟨(Finset.mem_Ico.mp hm).1, Nat.lt_succ_of_lt (Finset.mem_Ico.mp hm).2⟩))]
            ring
      simpa [F, Nat.cast_add, Nat.cast_one] using htel

private lemma _root_.log_200_ge' : Real.log 200 ≥ 1418 / 270 := by
  have h_log_200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    norm_num [ ← Real.log_rpow, ← Real.log_mul ]
  rw [ h_log_200, show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;> norm_num
  have := Real.log_two_gt_d9 ; norm_num at * ; have := Real.log_inv ( 5 / 4 ) ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < 4 / 5 by norm_num ) ]

set_option linter.flexible false in
private lemma _root_.abel_identity_sumT (n : ℕ) (hn : 200 ≤ n) :
    ∑ m ∈ Finset.Icc 200 n, (Λ m) / (m * Real.log m) = ((sumS n) - (sumS 199)) / Real.log n + ∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
  induction hn with
  | refl =>
    simp [sumS]
    rw [ show ( Finset.Icc 2 200 : Finset ℕ ) = Finset.Icc 2 199 ∪ { 200 } by decide, Finset.sum_union ] <;> norm_num ; ring
  | step hk ih =>
    rename_i k
    simp_all +decide [(Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
    rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Ioc 199 k, _ = _› ]
    rw [ Finset.sum_Ico_succ_top ( by linarith ), show sumS ( k + 1 ) = sumS k + Λ ( k + 1 ) / ( k + 1 : ℝ ) from ?_ ]
    · norm_num [ div_eq_mul_inv ] ; ring
    · exact_mod_cast Finset.sum_Ioc_succ_top ( by linarith ) _

/-
T(n) - T(199) ≤ log(log n) - log(log 199) + 27/100, using Abel summation and S(m) ≤ log m + 0.418
-/
lemma _root_.sumT_sub_199_bound (n : ℕ) (hn : 200 ≤ n) :
    sumT n ≤ sumT 199 + Real.log (Real.log ↑n) - Real.log (Real.log 199) + 27/100 := by
  -- Step 1: Split sumT
  have h_split : sumT n = sumT 199 + ∑ m ∈ Finset.Icc 200 n, vonMangoldt m / (m * Real.log m) := by
    unfold sumT; erw [ Finset.sum_Ico_consecutive ] <;> norm_cast ; linarith
  rw [h_split]
  -- Step 2: Abel summation identity
  have h_identity := abel_identity_sumT n hn
  -- Step 3: Bound the Abel sum terms
  have h_bound : (∑ m ∈ Finset.Ico 200 n, ((sumS m) - (sumS 199)) * (1 / Real.log m - 1 / Real.log (m + 1))) ≤ (∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1)))) := by
    refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ ?_ <;> norm_num at *
    · have := sumS_le_logn_plus m ( by linarith ) ; ( have := sumS_ge_log_sub_one 199 ( by norm_num ) ; ( norm_num at * ; linarith ) )
    · exact inv_anti₀ ( Real.log_pos <| by norm_cast; linarith ) ( Real.log_le_log ( by norm_cast; linarith ) <| by linarith )
  -- Step 4: Expand and telescope the sum
  have h_expand : ∑ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log 200 - 1 / Real.log n) := by
    have h_expand : ∀ m ∈ Finset.Ico 200 n, ((Real.log m - Real.log 199 + 1.418) * (1 / Real.log m - 1 / Real.log (m + 1))) = ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) + (1.418 - Real.log 199) * (1 / Real.log m - 1 / Real.log (m + 1)) := by
      intro m hm; ring_nf
      rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( by norm_cast; linarith [ Finset.mem_Ico.mp hm ] ) ) ) ] ; ring
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_add_distrib ]
    norm_num [ Finset.sum_Ico_eq_sum_range ]
    rw [ ← Finset.mul_sum _ _ _ ]
    exact congrArg _ ( by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast [ Nat.cast_sub hn ] <;> ring_nf )
  -- Step 5: Apply log ratio telescoping bound
  have h_log_ratio : ∑ m ∈ Finset.Ico 200 n, ((Real.log (m + 1) - Real.log m) / Real.log (m + 1)) ≤ Real.log (Real.log n) - Real.log (Real.log 200) := by
    simpa using sum_log_ratio_le_log_log' 200 n ( by norm_num ) hn
  -- Step 6: Bound the boundary term
  have h_sumS_le : (sumS n - sumS 199) / Real.log n ≤ (Real.log n + 0.418 - (Real.log 199 - 1)) / Real.log n := by
    gcongr
    · exact sumS_le_logn_plus n hn
    · exact sumS_ge_log_sub_one 199 ( by norm_num )
  -- Step 7: Numerical bound
  have h_num : 1 + (1.418 - Real.log 199) / Real.log 200 + Real.log (Real.log 199) - Real.log (Real.log 200) ≤ 27 / 100 := by
    have h_log_diff : Real.log (Real.log 200) - Real.log (Real.log 199) ≥ (Real.log 200 - Real.log 199) / Real.log 200 := by
      exact div_sub_le_log_sub' ( show 0 < Real.log 199 by positivity ) ( show Real.log 199 ≤ Real.log 200 by gcongr ; norm_num )
    ring_nf at *
    nlinarith [ inv_mul_cancel₀ ( show Real.log 200 ≠ 0 by positivity ), Real.log_pos ( show 199 > 1 by norm_num ), Real.log_lt_log ( by norm_num ) ( show 200 > 199 by norm_num ), show Real.log 200 ≥ 1418 / 270 from log_200_ge' ]
  -- Step 8: Combine all bounds
  ring_nf at *
  nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ), inv_pos.mpr ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ) ), Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ), Real.log_pos ( show ( 200 : ℝ ) > 1 by norm_num ) ]

/-
Computational upper bound on T(199)
-/
set_option linter.flexible false in
lemma _root_.sumT_199_lt : sumT 199 < 23/10 := by
  -- By definition of sumT, we can rewrite the sum as a sum over prime powers.
  have h_sum_prime_powers : ∀ n : ℕ, sumT n = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (1 / (p^k * k : ℝ)) := by
    intro n
    have h_sumT_prime_powers : ∀ m ∈ Finset.Icc 2 n, vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0) := by
      intro m hm
      by_cases hm_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ m = p^k ∧ p^k ≤ n;
      · obtain ⟨ p, k, hp, hk, rfl, hk' ⟩ := hm_prime_power; simp +decide [Finset.sum_ite] ;
        rw [ Finset.sum_eq_single p ];
        · rw [ Finset.card_eq_one.mpr ] <;> norm_num [ hp, hk ];
          · grind +suggestions;
          · exact ⟨ k, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk, Nat.le_log_of_pow_le hp.one_lt hk' ⟩, rfl ⟩, fun x hx => Nat.pow_right_injective hp.one_lt <| Finset.mem_filter.mp hx |>.2.symm ⟩ ⟩;
        · intro q hq hqp; simp_all +decide [ Finset.ext_iff ] ;
          exact Or.inl fun a ha₁ ha₂ ha₃ => hqp <| by have := congr_arg ( ·.factorization ( q : ℕ ) ) ha₃; norm_num at this; have := congr_arg ( ·.factorization ( p : ℕ ) ) ha₃; norm_num at this; aesop;
        · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.two_le, by linarith [ pow_le_pow_right₀ hp.one_lt.le hk ] ⟩, hp ⟩;
      · rw [ ArithmeticFunction.vonMangoldt_apply ];
        rw [ if_neg ];
        · exact Eq.symm ( Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun k hk => if_neg fun h => hm_prime_power ⟨ p, k, Finset.mem_filter.mp hp |>.2, Finset.mem_Icc.mp hk |>.1, h, by linarith [ Finset.mem_Icc.mp hm, Finset.mem_Icc.mp hk |>.2, Nat.pow_log_le_self p ( show m ≠ 0 by linarith [ Finset.mem_Icc.mp hm ] ) ] ⟩ );
        · contrapose! hm_prime_power;
          rw [ isPrimePow_nat_iff ] at hm_prime_power ; aesop;
    -- By interchanging the order of summation, we can rewrite the sum.
    have h_interchange : ∑ m ∈ Finset.Icc 2 n, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (if m = p^k then Real.log p else 0)) / (m * Real.log m) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), (Real.log p) / (p^k * Real.log (p^k)) := by
      simp +decide only [Finset.sum_div _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro p hp; rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv ] ;
      exact Finset.sum_congr rfl fun x hx => if_pos ⟨ le_trans ( Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ) ( Nat.le_self_pow ( by linarith [ Finset.mem_Icc.mp hx ] ) _ ), Nat.pow_le_of_le_log ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩;
    convert h_interchange using 2;
    · exact Finset.sum_congr rfl fun x hx => h_sumT_prime_powers x hx ▸ rfl;
    · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by aesop ) ) ) ) ) ] ; ring;
  rw [ h_sum_prime_powers ];
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rw [ show ( Finset.filter Nat.Prime ( Finset.Ioc 1 199 ) ) = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199 } by decide ] ; simp +decide ;
  norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *

/-
Lower bound on log(log 199)
-/
lemma _root_.log_log_199_gt : Real.log (Real.log 199) > 163/100 := by
  -- We'll use that $Real.log 199 > 5.11$.
  have h_log_199 : Real.log 199 > 5.11 := by
    norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 100 to remove the fraction.
    suffices h_exp : Real.exp 511 < 199 ^ 100 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 100 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We can raise both sides to the power of 511 to remove the fraction.
    have : Real.exp 511 ≤ (2.7182818286 : ℝ) ^ 511 := by
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) this _ );
    grind;
  refine lt_of_lt_of_le ?_ ( Real.log_le_log ( by positivity ) h_log_199.le )
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 163 = ( Real.exp 1 ) ^ 163 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma _root_.neg_log_prodP_bound (n : ℕ) (hn : 200 ≤ n) :
    -Real.log (prodP n) < Real.log (Real.log n) + 1.095 := by
  have h1 := neg_log_prodP_le_sumT_plus n hn
  have h2 := sumT_sub_199_bound n hn
  have h3 := sumT_199_lt
  have h4 := log_log_199_gt
  -- -log P(n) ≤ T(n) + 1/10
  --           ≤ T(199) + log(log n) - log(log 199) + 27/100 + 1/10
  --           < 23/10 + log(log n) - 163/100 + 27/100 + 1/10
  --           = log(log n) + (2300 + 270 + 100 - 1630)/1000
  --           = log(log n) + 1040/1000 = log(log n) + 1.04
  --           < log(log n) + 1.095
  linarith

/-! # Finite Check -/

lemma _root_.prodP_le_of_le {m n : ℕ} (h : m ≤ n) : prodP n ≤ prodP m := by
  unfold prodP;
  rw [ ← Finset.prod_sdiff ( Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.succ_le_succ h ) ];
  exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;

lemma _root_.mertens_finite_check (n : ℕ) (hn3 : 3 ≤ n) (hn199 : n ≤ 199) :
    1 / (3 * Real.log n) ≤ prodP n := by
  by_cases hn : n ≤ 10;
  · interval_cases n <;> norm_num [ Finset.prod_filter, Finset.prod_range_succ, prodP ];
    any_goals rw [ inv_mul_le_iff₀ ( by positivity ) ];
    any_goals rw [ inv_le_comm₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals rw [ ← div_le_iff₀ ] <;> norm_num [ Real.le_log_iff_exp_le ];
    any_goals positivity;
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 5 : ℝ ) / 4 = 1 + 1 / 4 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 1 / 4 ), Real.exp_neg ( 1 / 4 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 4 ) ) ), Real.add_one_le_exp ( 1 / 4 ), Real.add_one_le_exp ( - ( 1 / 4 ) ) ];
    any_goals have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 35 / 24 : ℝ ) = 1 + 11 / 24 by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( 11 / 24 ), Real.exp_neg ( 11 / 24 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 11 / 24 ) ) ), Real.add_one_le_exp ( 11 / 24 ), Real.add_one_le_exp ( - ( 11 / 24 ) ) ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
    · exact Real.exp_one_lt_d9.le.trans ( by norm_num );
  · by_cases hn : n ≤ 30;
    · -- For $11 \leq n \leq 30$, we use the fact that $prodP(n) \geq prodP(30)$ and $prodP(30) \geq 1/7$.
      have h_prod_bound : prodP n ≥ prodP 30 := by
        exact prodP_le_of_le hn
      have h_prod_30 : prodP 30 ≥ 1 / 7 := by
        unfold prodP; norm_num [ Finset.prod_filter, Finset.prod_range_succ ] ;
      have h_log_bound : 7 ≤ 3 * Real.log 11 := by
        norm_num [ ← Real.log_rpow, Real.le_log_iff_exp_le ] at *;
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
      have h_final : 1 / (3 * Real.log n) ≤ 1 / 7 := by
        exact one_div_le_one_div_of_le ( by positivity ) ( by linarith [ Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 11 by norm_cast; linarith ) ] )
      exact le_trans h_final (le_trans h_prod_30 h_prod_bound);
    · have h_prodP_199 : prodP 199 ≥ 1 / 10 := by
        unfold prodP; norm_num;
        norm_num [ Finset.prod_filter, Finset.prod_range_succ ];
      have h_log_bound : Real.log n ≥ 10 / 3 := by
        rw [ ge_iff_le, div_le_iff₀' ] <;> norm_num;
        rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_cast <;> try linarith;
        · exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 10 = ( Real.exp 1 ) ^ 10 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) ( Nat.cast_le.mpr ( Nat.pow_le_pow_left ( show n ≥ 31 by linarith ) 3 ) );
        · positivity;
      exact le_trans ( by rw [ div_le_iff₀ ] <;> linarith ) ( h_prodP_199.trans ( prodP_le_of_le ( by linarith ) ) )

/-! # Main Theorem -/

theorem _root_.mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  by_cases hn2 : n ≥ 200;
  · have := neg_log_prodP_bound n hn2;
    -- Exponentiating both sides, we get $prodP n > \frac{1}{3 \log n}$.
    have h_exp : prodP n > 1 / (3 * Real.log n) := by
      have h_exp : Real.log (prodP n) > -Real.log (3 * Real.log n) := by
        rw [ Real.log_mul ] <;> norm_num;
        · have h_log3 : Real.log 3 > 1.095 := by
            norm_num [ Real.log_lt_log ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 219 = ( Real.exp 1 ) ^ 219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
          linarith;
        · grind;
      rw [ gt_iff_lt, Real.lt_log_iff_exp_lt ] at h_exp;
      · simpa [ Real.exp_neg, Real.exp_log ( show 0 < 3 * Real.log n by exact mul_pos zero_lt_three ( Real.log_pos ( by norm_cast; linarith ) ) ) ] using h_exp;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_filter.mp hp, Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    exact h_exp.le;
  · -- Apply the finite check lemma to conclude the proof.
    apply mertens_finite_check n hn (by linarith)

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Dyadic.lean` -/

section


noncomputable section


open Finset BigOperators Nat Real

def dyadicScale (k : ℕ) : ℕ := 2 ^ (k + 1)

lemma Y_val_two (k : ℕ) : Y_val 2 k = (dyadicScale k : ℝ) := by
  simp [Y_val, dyadicScale, pow_succ, mul_comm]

lemma dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

lemma dyadicScale_succ (k : ℕ) : dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, pow_succ, mul_comm]

lemma I_layer_two (k : ℕ) : I_layer 2 k =
    (Finset.Ico (dyadicScale k) (2 * dyadicScale k)).filter Nat.Prime := by
  simp only [I_layer, Y_val_two, Nat.ceil_natCast, dyadicScale_succ]

lemma M_layer_positive (lam : ℝ) (k : ℕ) : 0 < M_layer lam k := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  exact sub_pos.mpr ((div_lt_one hp0).mpr hp1)

lemma dyadic_prime_count (k : ℕ) (hk : 1 ≤ k) :
    (N_layer 2 k : ℝ) ≤
      2 * dyadicScale k * Real.log 2 / Real.log (dyadicScale k) := by
  let Y := dyadicScale k
  have hY : 2 ≤ Y := by
    dsimp [Y, dyadicScale]
    exact Nat.le_self_pow (by omega) 2
  have hYnot : ¬ Y.Prime := Nat.Prime.not_prime_pow (by omega : 2 ≤ k + 1)
  have hprime (p : ℕ) (hp : p ∈ I_layer 2 k) : p.Prime := (Finset.mem_filter.mp hp).2
  have hbounds (p : ℕ) (hp : p ∈ I_layer 2 k) : Y < p ∧ p < 2 * Y := by
    rw [I_layer_two] at hp
    have h := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1)
    exact ⟨lt_of_le_of_ne h.1 (by intro he; exact hYnot (he ▸ (Finset.mem_filter.mp hp).2)), h.2⟩
  have hdvd : (∏ p ∈ I_layer 2 k, p) ∣ Nat.choose (2 * Y) Y := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (hprime p hp).prime
    · intro p hp
      have hb := hbounds p hp
      exact (hprime p hp).dvd_choose hb.1 (by omega) hb.2.le
  have hchoose : 0 < Nat.choose (2 * Y) Y := Nat.choose_pos (by omega)
  have hprod : (∏ p ∈ I_layer 2 k, (p : ℝ)) ≤ (4 : ℝ)^Y := by
    have hle := (Nat.le_of_dvd hchoose hdvd).trans (Nat.centralBinom_le_four_pow Y)
    have hcast := Nat.cast_le (α := ℝ).mpr hle
    simpa only [Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat] using hcast
  have hprodpos : 0 < ∏ p ∈ I_layer 2 k, (p : ℝ) := by
    exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (hprime p hp).pos
  have hsum : (N_layer 2 k : ℝ) * Real.log Y ≤ Real.log (∏ p ∈ I_layer 2 k, (p : ℝ)) := by
    rw [Real.log_prod (fun p hp => (Nat.cast_pos.mpr (hprime p hp).pos).ne')]
    calc
      _ = ∑ p ∈ I_layer 2 k, Real.log (Y : ℝ) := by simp [N_layer]
      _ ≤ _ := Finset.sum_le_sum fun p hp => Real.log_le_log
        (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast (hbounds p hp).1.le)
  have hlog := Real.log_le_log hprodpos hprod
  rw [Real.log_pow, Real.log_four_eq] at hlog
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))).mpr
  dsimp [Y] at hsum hlog ⊢
  nlinarith

lemma dyadic_mertens_lower (k : ℕ) :
    1 / (3 * Real.log (2 * (dyadicScale k : ℝ))) ≤ M_layer 2 k := by
  have hY : 3 ≤ 2 * dyadicScale k := by
    have := dyadicScale_pos k
    have h2 : 2 ≤ dyadicScale k := by
      unfold dyadicScale
      exact Nat.le_self_pow (by omega) 2
    omega
  have h := mertens_third_theorem (2 * dyadicScale k) hY
  have hf : ⌊(2 : ℝ) * (dyadicScale k : ℝ)⌋₊ = 2 * dyadicScale k := by
    norm_cast
    exact Nat.floor_natCast _
  simpa only [M_layer, primesUpTo, Y_val_two, dyadicScale_succ,
    Nat.cast_mul, Nat.cast_ofNat, hf] using h

lemma dyadicScale_log (k : ℕ) : Real.log (dyadicScale k : ℝ) = ((k : ℝ)+1)*Real.log 2 := by
  simp [dyadicScale, Real.log_pow]

lemma dyadic_density_bound (k : ℕ) (hk : 16 ≤ k) :
    (N_layer 2 k : ℝ) / (Y_val 2 k * Real.sqrt (M_layer 2 k)) ≤ (72/100 : ℝ) := by
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM : 0 < M_layer 2 k := M_layer_positive _ _
  have hs : 0 < Real.sqrt (M_layer 2 k) := Real.sqrt_pos.mpr hM
  have hK : (16 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := dyadic_prime_count k (by omega)
  rw [dyadicScale_log, ← Y_val_two] at hn
  have hn' : (N_layer 2 k : ℝ) ≤ 2 * Y_val 2 k / ((k : ℝ)+1) := by
    convert hn using 1
    field_simp
  have hm := dyadic_mertens_lower k
  rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr (dyadicScale_pos k)).ne',
    dyadicScale_log] at hm
  have hm' : 1 ≤ 3 * ((k : ℝ)+2) * Real.log 2 * M_layer 2 k := by
    have heq : 3 * (Real.log 2 + ((k : ℝ)+1)*Real.log 2) =
        3 * ((k : ℝ)+2) * Real.log 2 := by ring
    rw [heq, div_le_iff₀ (by positivity)] at hm
    nlinarith
  have hcoef : 3 * ((k : ℝ)+2) * Real.log 2 ≤ (72/100 : ℝ)^2/4 * ((k : ℝ)+1)^2 := by
    have hl : Real.log 2 < (6932/10000 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hquad : 289 * ((k : ℝ)+2) ≤ 18 * ((k : ℝ)+1)^2 := by
      nlinarith [sq_nonneg ((k : ℝ)-16)]
    nlinarith [mul_le_mul_of_nonneg_left hl.le (show 0 ≤ 3*((k : ℝ)+2) by positivity)]
  have hsquare : 4 ≤ (72/100 : ℝ)^2 * ((k : ℝ)+1)^2 * M_layer 2 k := by
    have := mul_le_mul_of_nonneg_right hcoef hM.le
    nlinarith
  have hroot : 2 ≤ (72/100 : ℝ) * ((k : ℝ)+1) * Real.sqrt (M_layer 2 k) := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hM.le]
    norm_num at hsquare ⊢
    exact hsquare
  apply (div_le_iff₀ (mul_pos hY hs)).mpr
  refine hn'.trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hroot hY.le]

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Deletion.lean` -/

section


noncomputable section


open Finset BigOperators

def WeightRegular (w : ℕ → ℝ) (S : Finset ℕ) : Prop :=
  ∀ k, ∀ p ∈ I_layer 2 k, 0 < w k → (sdiv S p).Nonempty →
    w k * S.card < (sdiv S p).card

def weightTotal (w : ℕ → ℝ) : ℝ := ∑' k, w k * (N_layer 2 k : ℝ)

def activeWeight (w : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑' k, w k * ((I_layer 2 k).filter (fun p => (sdiv S p).Nonempty)).card

lemma activeWeight_summable (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    Summable (fun k => w k * ((I_layer 2 k).filter (fun p => (sdiv S p).Nonempty)).card) := by
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (hw k) (Nat.cast_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hw k)

lemma activeWeight_nonneg (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (S : Finset ℕ) :
    0 ≤ activeWeight w S := by
  exact tsum_nonneg fun k => mul_nonneg (hw k) (Nat.cast_nonneg _)

lemma activeWeight_le_total (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    activeWeight w S ≤ weightTotal w := by
  apply Summable.tsum_le_tsum _ (activeWeight_summable w hw hs S) hs
  intro k
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hw k)

lemma activeWeight_delete (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ)))
    (S : Finset ℕ) (k p : ℕ) (hp : p ∈ I_layer 2 k) (hne : (sdiv S p).Nonempty) :
    activeWeight w (S \ sdiv S p) + w k ≤ activeWeight w S := by
  have hsub (j : ℕ) :
      (I_layer 2 j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty) ⊆
        (I_layer 2 j).filter (fun q => (sdiv S q).Nonempty) := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hq).1, sdiv_sdiff_subset S p q (Finset.mem_filter.mp hq).2⟩
  have hstrict :
      ((I_layer 2 k).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card + 1 ≤
        ((I_layer 2 k).filter (fun q => (sdiv S q).Nonempty)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub k, ?_⟩
    intro heq
    have hp' : p ∈ (I_layer 2 k).filter (fun q => (sdiv S q).Nonempty) :=
      Finset.mem_filter.mpr ⟨hp, hne⟩
    rw [← heq] at hp'
    have h := (Finset.mem_filter.mp hp').2
    simp only [sdiv_sdiff_self_empty, Finset.not_nonempty_empty] at h
  have hterm (j : ℕ) :
      w j * ((I_layer 2 j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card +
        (if j = k then w k else 0) ≤
          w j * ((I_layer 2 j).filter (fun q => (sdiv S q).Nonempty)).card := by
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl]
      have hc :
          (((I_layer 2 k).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card : ℝ) + 1 ≤
            ((I_layer 2 k).filter (fun q => (sdiv S q).Nonempty)).card := by
        exact_mod_cast hstrict
      nlinarith [hw k]
    · simp only [if_neg hj, add_zero]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card (hsub j))) (hw j)
  have hsingle : Summable (fun j : ℕ => if j = k then w k else 0) :=
    ⟨_, hasSum_single k (by intro j hj; simp [hj])⟩
  have hsum := Summable.tsum_le_tsum hterm
    ((activeWeight_summable w hw hs (S \ sdiv S p)).add hsingle)
    (activeWeight_summable w hw hs S)
  rw [Summable.tsum_add (activeWeight_summable w hw hs (S \ sdiv S p)) hsingle] at hsum
  simpa [activeWeight] using hsum

theorem weighted_subset (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    ∃ S' ⊆ S, WeightRegular w S' ∧
      (1 - weightTotal w) * S.card ≤ (S'.card : ℝ) := by
  suffices h : ∀ n : ℕ, ∀ T : Finset ℕ, T.card = n →
      ∃ S' ⊆ T, WeightRegular w S' ∧
        (T.card : ℝ) - S'.card ≤ activeWeight w T * T.card by
    obtain ⟨S', hS', hreg, hbound⟩ := h S.card S rfl
    exact ⟨S', hS', hreg, by nlinarith [activeWeight_le_total w hw hs S]⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro T hT
    by_cases hreg : WeightRegular w T
    · refine ⟨T, Finset.Subset.refl T, hreg, ?_⟩
      simp only [sub_self]
      exact mul_nonneg (activeWeight_nonneg w hw T) (Nat.cast_nonneg _)
    · simp only [WeightRegular, not_forall] at hreg
      obtain ⟨k, p, hp, hwp, hne, hbad⟩ := hreg
      have hbound : ((sdiv T p).card : ℝ) ≤ w k * T.card := le_of_not_gt hbad
      let T₁ := T \ sdiv T p
      have hlt : T₁.card < T.card := card_sdiff_sdiv_lt T p hne
      obtain ⟨S', hS', hreg', hbound'⟩ := ih T₁.card (hT ▸ hlt) T₁ rfl
      refine ⟨S', hS'.trans Finset.sdiff_subset, hreg', ?_⟩
      have hcard : (T.card : ℝ) - T₁.card = (sdiv T p).card := by
        have h := Finset.card_sdiff_add_card_inter T (sdiv T p)
        rw [Finset.inter_eq_right.mpr (sdiv_subset T p)] at h
        have h' : (T₁.card : ℝ) + (sdiv T p).card = T.card := by exact_mod_cast h
        linarith
      have hmu := activeWeight_delete w hw hs T k p hp hne
      have hmono : activeWeight w T₁ * T₁.card ≤ activeWeight w T₁ * T.card :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlt.le) (activeWeight_nonneg w hw T₁)
      dsimp [T₁] at hmu hmono hbound' hcard ⊢
      nlinarith

theorem weighted_pair_subset (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (hΩ : weightTotal w < 1)
    {n : ℕ} {A B : Finset ℕ} (hAB : ProductAdmissible n A B) :
    ∃ A' B' : Finset ℕ, ProductAdmissible n A' B' ∧ WeightRegular w A' ∧
      WeightRegular w B' ∧
        (1 - weightTotal w)^2 * ((A.card : ℝ) * B.card) ≤ (A'.card : ℝ) * B'.card := by
  obtain ⟨A', hA', hrA, hcA⟩ := weighted_subset w hw hs A
  obtain ⟨B', hB', hrB, hcB⟩ := weighted_subset w hw hs B
  refine ⟨A', B', admissible_subset hAB hA' hB', hrA, hrB, ?_⟩
  have hnonneg : 0 ≤ 1 - weightTotal w := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcA hnonneg,
    mul_le_mul_of_nonneg_left hcB hnonneg]

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Rectangles.lean` -/

section


noncomputable section


open Finset BigOperators

def rectangleWeight (m : ℕ → ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  if m k < N_layer 2 k then
    g k / (Y_val 2 k * Real.sqrt (M_layer 2 k) * Real.sqrt ((m k : ℝ) + 1))
  else 0

lemma rectangleWeight_nonneg (m : ℕ → ℕ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (k : ℕ) :
    0 ≤ rectangleWeight m g k := by
  unfold rectangleWeight
  split_ifs
  · have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
    exact div_nonneg (hg k) (by positivity)
  · rfl

lemma quotient_rectangles_disjoint {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint ((sinv A p) ×ˢ (sinv B p)) ((sinv A q) ×ˢ (sinv B q)) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  have hA : (sinv A p ∩ sinv A q).Nonempty :=
    ⟨z.1, Finset.mem_inter.mpr
      ⟨(Finset.mem_product.mp hz₁).1, (Finset.mem_product.mp hz₂).1⟩⟩
  have hB := collision_lemma n A B p q hAB hp hq hpq hA
  have hz : z.2 ∈ sinv B p ∩ sinv B q :=
    Finset.mem_inter.mpr
      ⟨(Finset.mem_product.mp hz₁).2, (Finset.mem_product.mp hz₂).2⟩
  simp [hB] at hz

lemma quotient_rectangle_count {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (L : Finset ℕ) (hL : ∀ p ∈ L, p.Prime) :
    ∑ p ∈ L, (sinv A p).card * (sinv B p).card ≤
      (L.biUnion (sinv A)).card * (L.biUnion (sinv B)).card := by
  classical
  calc
    _ = (L.biUnion (fun p => sinv A p ×ˢ sinv B p)).card := by
      rw [Finset.card_biUnion]
      · simp only [Finset.card_product]
      · intro p hp q hq hpq
        exact quotient_rectangles_disjoint hAB (hL p hp) (hL q hq) hpq
    _ ≤ ((L.biUnion (sinv A)) ×ˢ (L.biUnion (sinv B))).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_product.mp hz).1⟩,
         Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_product.mp hz).2⟩⟩
    _ = _ := Finset.card_product _ _

lemma regular_rectangle_cross_bound (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 1 ≤ g k) {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B)
    (hA : WeightRegular (rectangleWeight m g) A)
    (hB : WeightRegular (rectangleWeight m g) B)
    (k : ℕ) (hk : m k < (L_common 2 k A B).card) :
    ((A.card : ℝ) * B.card) * (g k)^2 ≤
      (Y_val 2 k)^2 * M_layer 2 k *
        ((L_common 2 k A B).biUnion (sinv A)).card *
          ((L_common 2 k A B).biUnion (sinv B)).card := by
  let L := L_common 2 k A B
  let w := rectangleWeight m g k
  have hm : m k < N_layer 2 k := hk.trans_le (Finset.card_filter_le _ _)
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM : 0 < M_layer 2 k := M_layer_positive _ _
  have hgpos : 0 < g k := lt_of_lt_of_le zero_lt_one (hg k)
  have hw : 0 < w := by
    dsimp [w, rectangleWeight]
    rw [if_pos hm]
    positivity
  have hL (p : ℕ) (hp : p ∈ L) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hlocal (p : ℕ) (hp : p ∈ L) :
      w^2 * ((A.card : ℝ) * B.card) ≤ (sinv A p).card * (sinv B p).card := by
    have hp' := Finset.mem_filter.mp hp
    have ha := hA k p hp'.1 hw hp'.2.1
    have hb := hB k p hp'.1 hw hp'.2.2
    rw [← division_lemma A p (hL p hp)] at ha
    rw [← division_lemma B p (hL p hp)] at hb
    have h := mul_le_mul ha.le hb.le (by positivity) (by positivity)
    nlinarith
  have hsum : (L.card : ℝ) * (w^2 * ((A.card : ℝ) * B.card)) ≤
      ((L.biUnion (sinv A)).card : ℝ) * (L.biUnion (sinv B)).card := by
    calc
      _ = ∑ p ∈ L, w^2 * ((A.card : ℝ) * B.card) := by simp
      _ ≤ ∑ p ∈ L, ((sinv A p).card : ℝ) * (sinv B p).card := Finset.sum_le_sum hlocal
      _ ≤ _ := by exact_mod_cast quotient_rectangle_count hAB L hL
  have hcard : (m k : ℝ) + 1 ≤ L.card := by exact_mod_cast hk
  have hsum' : ((m k : ℝ) + 1) * w^2 * ((A.card : ℝ) * B.card) ≤
      ((L.biUnion (sinv A)).card : ℝ) * (L.biUnion (sinv B)).card := by
    have h := mul_le_mul_of_nonneg_right hcard
      (by positivity : 0 ≤ w^2 * ((A.card : ℝ) * B.card))
    nlinarith
  have hidentity : ((m k : ℝ) + 1) * w^2 = (g k)^2 / ((Y_val 2 k)^2 * M_layer 2 k) := by
    dsimp [w, rectangleWeight]
    rw [if_pos hm, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt hM.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m k + 1)]
    field_simp
  rw [hidentity, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hsum'
  dsimp [L] at hsum'
  nlinarith

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Counting.lean` -/

section


noncomputable section
open Finset BigOperators Nat Real Filter
open scoped Topology
set_option maxHeartbeats 1600000

lemma choose_rectangle_sieve_error (ε : ℝ) (hε : 0 < ε) : ∃ ε₁ > 0, ((111 / 100) * Real.exp γ + ε₁) ^ 2 * (Real.exp (-γ) + ε₁) < (111 / 100)^2 * Real.exp γ + ε := by
  have he : Real.exp γ ^ 2 * Real.exp (-γ) = Real.exp γ := by
    rw [pow_two, mul_assoc, ← Real.exp_add]
    simp
  have hlim : Filter.Tendsto
      (fun t : ℝ => ((111 / 100) * Real.exp γ + t)^2 * (Real.exp (-γ) + t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((111 / 100)^2 * Real.exp γ)) := by
    have hcont := (show Continuous (fun t : ℝ =>
      ((111 / 100) * Real.exp γ + t)^2 * (Real.exp (-γ) + t)) by continuity).tendsto 0
    have hvalue : ((111 / 100 : ℝ) * Real.exp γ + 0)^2 * (Real.exp (-γ) + 0) =
        (111 / 100)^2 * Real.exp γ := by
      simp only [add_zero, mul_pow, mul_assoc]
      rw [he]
    rw [hvalue] at hcont
    exact tendsto_nhdsWithin_of_tendsto_nhds hcont
  obtain ⟨t, ht, htpos⟩ :=
    ((hlim.eventually (gt_mem_nhds (by linarith :
      (111 / 100 : ℝ)^2 * Real.exp γ < (111 / 100)^2 * Real.exp γ + ε))).and
      self_mem_nhdsWithin).exists
  exact ⟨t, htpos, ht⟩

theorem small_interval_case (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (m : ℕ → ℕ)
    (hlam : 1 < lam)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k)))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (∀ k, (L_common lam k A B).card ≤ m k) →
        ((A.card : ℝ) * B.card ≤
          ((111 / 100)^2 * Real.exp γ + ε) * D_val lam m * n ^ 2 / Real.log n) := by
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := choose_rectangle_sieve_error ε hε
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ n) → ((Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    obtain ⟨ X₀, hX₀ ⟩ := sieve_bound hCheb ε₁ hε₁_pos;
    exact ⟨ ⌈X₀⌉₊, fun n hn P hP => by simpa using hX₀ n ( Nat.le_of_ceil_le hn ) P fun p hp => ⟨ hP p hp |>.1, mod_cast hP p hp |>.2 ⟩ ⟩;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → |∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ)) - Real.exp (-γ) / Real.log n| ≤ ε₁ / Real.log n := by
    have := mertens_product_estimate ε₁ hε₁_pos;
    exact ⟨ ⌈this.choose⌉₊ + 1, fun n hn => this.choose_spec n <| le_of_lt <| Nat.lt_of_ceil_lt hn ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn A B hadm hL
  have hA : (A.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.1 hx; simp_all +decide ;
      intro p hp₁ hp₂ hp₃ hp₄; simp_all +decide [ Finset.ext_iff, sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩
  have hB : (B.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.2.1 hx; simp_all +decide [ sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩;
  have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ := by
    have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (¬(sdiv A p).Nonempty ∨ ¬(sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))) := by
      convert prod_union_le_of_le_one _ _ using 1;
      · congr with p ; aesop;
      · aesop;
      · aesop;
    refine le_trans h_prod ?_;
    rw [ ← div_eq_mul_inv, le_div_iff₀ ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_subset ?_ ?_ <;> intro p hp <;> simp_all +decide [ primesUpTo ];
        grind;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop;
  have h_prod_bound : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ ≤ D_val lam m := by
    convert euler_common_product lam hlam m hsumm n A B hL using 1;
    rw [ Finset.prod_inv_distrib ];
  have h_prod_bound : (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε₁) / Real.log n := by
    grind;
  have h_final : (A.card : ℝ) * (B.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) ^ 2 * n ^ 2 * ((Real.exp (-γ) + ε₁) / Real.log n) * D_val lam m := by
    refine le_trans ( mul_le_mul hA hB ?_ ?_ ) ?_;
    · positivity;
    · exact mul_nonneg ( mul_nonneg ( add_nonneg (by positivity) hε₁_pos.le ) ( Nat.cast_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    · convert mul_le_mul_of_nonneg_left ( h_prod.trans ( mul_le_mul h_prod_bound ‹_› ( ?_ ) ( ?_ ) ) ) ( show 0 ≤ ( (111 / 100) * Real.exp γ + ε₁ ) ^ 2 * n ^ 2 by positivity ) using 1 <;> ring_nf;
      · exact inv_nonneg.mpr ( Finset.prod_nonneg fun x hx => sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop );
      · exact add_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) ) ( mul_nonneg hε₁_pos.le ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) );
  refine le_trans h_final ?_;
  convert mul_le_mul_of_nonneg_right hε₁.le ( show 0 ≤ ( n : ℝ ) ^ 2 * D_val lam m / Real.log n by exact div_nonneg ( mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) using 1
  focus
    ring
  ring


theorem large_rectangle_case (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : 0 < ε)
    (m : ℕ → ℕ) (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (hgtop : Tendsto g atTop atTop)
    (hsumm : Summable (fun k => Real.log (E_val 2 k (m k)))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        WeightRegular (rectangleWeight m g) A → WeightRegular (rectangleWeight m g) B →
        ∀ k, m k < (L_common 2 k A B).card →
          (∀ j, k < j → (L_common 2 j A B).card ≤ m j) →
          (A.card : ℝ) * B.card ≤
            ((111 / 100)^2 * Real.exp γ + ε) * D_val 2 m * n^2 / Real.log n := by
  obtain ⟨δ, hδ, hc⟩ := choose_rectangle_sieve_error ε hε
  obtain ⟨N₁, hN₁⟩ := sifted_bound_union hCheb δ hδ 2 (by norm_num)
  have hg2 : ∀ k, 1 ≤ (g k)^2 := fun k => by nlinarith [hg1 k]
  have hg2top : Tendsto (fun k => (g k)^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0) |>.comp hgtop
  obtain ⟨N₂, hN₂⟩ := weighted_interval_product δ hδ 2 (by norm_num)
    (fun k => (g k)^2) hg2 hg2top
  refine ⟨max N₁ N₂ + 2, ?_⟩
  intro n hn A B hAB hA hB k hk hhigher
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM := M_layer_positive 2 k
  have hg : 0 < g k := lt_of_lt_of_le zero_lt_one (hg1 k)
  have huA := hN₁ n hn1 k A hAB.1 (L_common 2 k A B)
    (by intro p hp; simp only [L_common, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩)
  have huB := hN₁ n hn1 k B hAB.2.1 (L_common 2 k A B)
    (by intro p hp; simp only [L_common, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩)
  have hrect := regular_rectangle_cross_bound m g hg1 hAB hA hB k hk
  have hprod := Pi_sieve_mul_le 2 (by norm_num) m hsumm n k A B hhigher
  let P := ∏ p ∈ ((Finset.Ioc ⌊Y_val 2 (k+1)⌋₊ ⌊(n : ℝ) / Y_val 2 k⌋₊).filter Nat.Prime),
    (1 - 1 / (p : ℝ))
  let c := (111 / 100 : ℝ) * Real.exp γ + δ
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hmul := mul_le_mul huA huB (by positivity) (le_trans (by positivity) huA)
  have hfirst : ((A.card : ℝ) * B.card) * (g k)^2 ≤
      c^2 * n^2 * M_layer 2 k * (Pi_sieve n 2 k A * Pi_sieve n 2 k B) := by
    have hm := mul_le_mul_of_nonneg_left hmul (show 0 ≤ (Y_val 2 k)^2 * M_layer 2 k by positivity)
    have heq : (Y_val 2 k)^2 * M_layer 2 k *
        ((c * n / Y_val 2 k * Pi_sieve n 2 k A) *
          (c * n / Y_val 2 k * Pi_sieve n 2 k B)) =
        c^2 * n^2 * M_layer 2 k * (Pi_sieve n 2 k A * Pi_sieve n 2 k B) := by
      field_simp
      <;> ring
    rw [heq] at hm
    exact hrect.trans (by simpa only [mul_assoc] using hm)
  have hsecond : ((A.card : ℝ) * B.card) * (g k)^2 ≤
      c^2 * n^2 * M_layer 2 k * (P * D_val 2 m) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hthird : (A.card : ℝ) * B.card ≤
      c^2 * (M_layer 2 k / (g k)^2 * P) * (D_val 2 m * n^2) := by
    calc
      _ ≤ (c^2 * n^2 * M_layer 2 k * (P * D_val 2 m)) / (g k)^2 :=
        (le_div_iff₀ (sq_pos_of_pos hg)).mpr hsecond
      _ = _ := by ring
  have hfourth : (A.card : ℝ) * B.card ≤
      c^2 * (Real.exp (-γ) + δ) * (D_val 2 m * n^2 / Real.log n) := by
    refine hthird.trans ?_
    convert mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hN₂ n hn2 k) (sq_nonneg c))
      (show 0 ≤ D_val 2 m * (n : ℝ)^2 by exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) using 1 <;> ring
  refine hfourth.trans ?_
  convert mul_le_mul_of_nonneg_right hc.le
    (show 0 ≤ D_val 2 m * (n : ℝ)^2 / Real.log n by
      exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) hlog.le) using 1 <;> ring

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Chebyshev.lean` -/

section


noncomputable section


open Finset BigOperators Nat Real Filter
open scoped Topology

set_option maxHeartbeats 800000

def factorialKernel (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

lemma factorialKernel_nonneg (n : ℕ) : 0 ≤ factorialKernel n := by
  unfold factorialKernel
  omega

lemma factorialKernel_eq_one {n : ℕ} (h₁ : 1 ≤ n) (h₆ : n < 6) :
    factorialKernel n = 1 := by
  interval_cases n <;> norm_num [factorialKernel]

def factorialCombination (n : ℕ) : ℝ :=
  Real.log (n.factorial) - Real.log ((n / 2).factorial) -
    Real.log ((n / 3).factorial) - Real.log ((n / 5).factorial) +
      Real.log ((n / 30).factorial)

lemma log_factorial_vonMangoldt (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (n / d : ℕ) =
      Real.log (n.factorial) := by
  have h_interchange :
      ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt d =
        ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt d * (if d ∣ m then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Finset.mem_Icc.mp hm).1,
        (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hd).trans (Finset.mem_Icc.mp hm).2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by have := (Finset.mem_Icc.mp hm).1; omega⟩
  have h_inner (d : ℕ) (hd : d ∈ Finset.Icc 1 n) :
      ∑ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (if d ∣ m then 1 else 0) =
        ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hset : (Finset.Icc 1 n).filter (d ∣ ·) =
        (Finset.Icc 1 (n / d)).image (d * ·) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hm1, hmn⟩, hdm⟩
        exact ⟨m / d, ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdm) hd0,
          Nat.div_le_div_right hmn⟩, Nat.mul_div_cancel' hdm⟩
      · rintro ⟨j, ⟨hj1, hjn⟩, rfl⟩
        exact ⟨⟨by nlinarith, (Nat.mul_le_mul_left d hjn).trans (Nat.mul_div_le n d)⟩,
          dvd_mul_right d j⟩
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const]
    rw [hset, Finset.card_image_of_injective _ (fun a b h => mul_left_cancel₀ hd0.ne' h)]
    simp [nsmul_eq_mul, mul_comm]
  rw [← Finset.sum_congr rfl h_inner, ← h_interchange]
  simp only [ArithmeticFunction.vonMangoldt_sum]
  clear h_inner h_interchange
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring

lemma log_factorial_vonMangoldt_of_le {m n : ℕ} (hmn : m ≤ n) :
    Real.log (m.factorial) =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (m / d : ℕ) := by
  rw [← log_factorial_vonMangoldt]
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hmn)
  intro d hd hdm
  have hmd : m < d := by
    simp only [Finset.mem_Icc] at hd hdm
    omega
  simp [Nat.div_eq_of_lt hmd]

lemma factorialCombination_eq_sum (n : ℕ) :
    factorialCombination n =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * factorialKernel (n / d) := by
  unfold factorialCombination
  rw [log_factorial_vonMangoldt_of_le (le_refl n),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 2),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 3),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 5),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 30)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [factorialKernel, Int.cast_add, Int.cast_sub, Int.cast_natCast,
    Nat.div_div_eq_div_mul]
  simp only [mul_comm d]
  ring

lemma chebyshevPsi_nat_eq_sum (n : ℕ) :
    chebyshevPsi n = ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d := by
  unfold chebyshevPsi
  erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num

lemma chebyshevPsi_factorial_step (n : ℕ) :
    chebyshevPsi n ≤ factorialCombination n + chebyshevPsi (n / 6 : ℕ) := by
  rw [chebyshevPsi_nat_eq_sum, factorialCombination_eq_sum, chebyshevPsi_nat_eq_sum]
  have hsmall : (∑ d ∈ Finset.Icc 1 (n / 6), ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ Finset.Icc 1 n, if d ≤ n / 6 then ArithmeticFunction.vonMangoldt d else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hle := Nat.div_le_self n 6
    omega
  rw [hsmall, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hkernel : (0 : ℝ) ≤ factorialKernel (n / d) := by
    exact_mod_cast factorialKernel_nonneg (n / d)
  split_ifs with hsmall
  · linarith [mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d)) hkernel]
  · have h₁ : 1 ≤ n / d := Nat.div_pos (Finset.mem_Icc.mp hd).2 hdpos
    have h₆ : n / d < 6 := (Nat.div_lt_iff_lt_mul hdpos).mpr (by omega)
    simp [factorialKernel_eq_one h₁ h₆]

lemma log_factorial_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n.factorial) := by
  induction hn <;> simp_all +decide [Nat.factorial]
  rw [Real.log_mul (by positivity) (by positivity)]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, Real.exp_log (by positivity)]
    nlinarith [Real.add_one_le_exp (1 / (m : ℝ)),
      one_div_mul_cancel (by positivity : (m : ℝ) ≠ 0)]
  have := h_log _ ‹_›
  norm_num at *
  nlinarith [inv_mul_cancel₀ (by positivity : ((Nat.cast : ℕ → ℝ) ‹_›) ≠ 0)]

def factorialEntropy : ℝ :=
  (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5

lemma factorialEntropy_lt : factorialEntropy < 922 / 1000 := by
  unfold factorialEntropy
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

lemma factorialCombination_mul30_bound (m : ℕ) (hm : 0 < m) :
    factorialCombination (30 * m) ≤
      (922 / 1000 : ℝ) * (30 * m) + 2 * Real.log (30 * m) := by
  have h2 : 30 * m / 2 = 15 * m := by omega
  have h3 : 30 * m / 3 = 10 * m := by omega
  have h5 : 30 * m / 5 = 6 * m := by omega
  have h30 : 30 * m / 30 = m := by omega
  unfold factorialCombination
  rw [h2, h3, h5, h30]
  have hu := _root_.log_factorial_le (30 * m) (by omega)
  have hu' := _root_.log_factorial_le m hm
  have hl2 := log_factorial_lower (15 * m) (by omega)
  have hl3 := log_factorial_lower (10 * m) (by omega)
  have hl5 := log_factorial_lower (6 * m) (by omega)
  push_cast at hu hu' hl2 hl3 hl5 ⊢
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlogm : Real.log (m : ℝ) ≤ Real.log (30 * (m : ℝ)) :=
    Real.log_le_log hmR (by linarith)
  have hlog30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hlog15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hmain :
      (30 * (m : ℝ)) * Real.log (30 * m) - (15 * m) * Real.log (15 * m) -
        (10 * m) * Real.log (10 * m) - (6 * m) * Real.log (6 * m) +
          m * Real.log m = factorialEntropy * (30 * m) := by
    simp only [Real.log_mul (by norm_num : (30 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (15 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hmR.ne',
      hlog30, hlog15, hlog10, hlog6, factorialEntropy]
    ring
  have hEntropy := mul_le_mul_of_nonneg_right factorialEntropy_lt.le (by positivity :
    (0 : ℝ) ≤ 30 * m)
  linarith

lemma chebyshevPsi_nat_le_two (n : ℕ) : chebyshevPsi n ≤ 2 * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [chebyshevPsi]
  have h := _root_.chebyshevPsi_le n hn
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound : (2 : ℝ) * n * Real.log 2 ≤ 2 * n := by nlinarith
  have h' : chebyshevPsi n ≤ 2 * n * Real.log 2 := by
    simpa [chebyshevPsi, chebyshevPsi'] using h
  exact h'.trans hbound

lemma chebyshevPsi_multiple_bound (m : ℕ) (hm : 0 < m) :
    chebyshevPsi (6480 * m : ℕ) ≤
      (358697 / 324000 : ℝ) * (6480 * m) + 8 * Real.log (6480 * m) := by
  have h₀ := chebyshevPsi_factorial_step (6480 * m)
  have h₁ := chebyshevPsi_factorial_step (1080 * m)
  have h₂ := chebyshevPsi_factorial_step (180 * m)
  have h₃ := chebyshevPsi_factorial_step (30 * m)
  have hd₀ : 6480 * m / 6 = 1080 * m := by omega
  have hd₁ : 1080 * m / 6 = 180 * m := by omega
  have hd₂ : 180 * m / 6 = 30 * m := by omega
  have hd₃ : 30 * m / 6 = 5 * m := by omega
  rw [hd₀] at h₀
  rw [hd₁] at h₁
  rw [hd₂] at h₂
  rw [hd₃] at h₃
  have ht₀ := factorialCombination_mul30_bound (216 * m) (by omega)
  have ht₁ := factorialCombination_mul30_bound (36 * m) (by omega)
  have ht₂ := factorialCombination_mul30_bound (6 * m) (by omega)
  have ht₃ := factorialCombination_mul30_bound m hm
  norm_num [← mul_assoc] at ht₀ ht₁ ht₂
  have ht₄ := chebyshevPsi_nat_le_two (5 * m)
  have hl₁ : Real.log (1080 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hl₂ : Real.log (180 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hl₃ : Real.log (30 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  push_cast at h₀ h₁ h₂ h₃ ht₄ ⊢
  linarith

lemma chebyshevPsi_mono : Monotone chebyshevPsi := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hxy)))
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- An elementary eventual Chebyshev upper bound, obtained solely from
factorial inequalities and a nonnegative periodic floor kernel. -/
theorem elementary_chebyshev_bound :
    ∃ T : ℝ, ∀ x : ℝ, T ≤ x → chebyshevPsi x ≤ (111 / 100) * x := by
  let c : ℝ := 358697 / 324000
  let δ : ℝ := 111 / 100 - c
  let K : ℝ := c * 6481 + 8 * Real.log 2
  have hδ : 0 < δ := by norm_num [δ, c]
  have hc : 0 ≤ c := by norm_num [c]
  have hlog := Real.isLittleO_log_id_atTop.def (by positivity : 0 < δ / 16)
  apply Filter.eventually_atTop.mp
  filter_upwards [hlog, eventually_ge_atTop (6481 : ℝ),
    eventually_ge_atTop (2 * K / δ)] with x hlog hx hK
  have hxpos : 0 < x := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hxpos.le,
    abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ x))] at hlog
  have hK' : 2 * K ≤ x * δ := (div_le_iff₀ hδ).mp hK
  let m : ℕ := ⌈x⌉₊ / 6480 + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hceilLower : ⌈x⌉₊ ≤ 6480 * m := by
    dsimp [m]
    have hmod := Nat.mod_lt ⌈x⌉₊ (by norm_num : 0 < 6480)
    have hdiv := Nat.div_add_mod ⌈x⌉₊ 6480
    omega
  have hceilUpper : 6480 * m ≤ ⌈x⌉₊ + 6480 := by
    dsimp [m]
    have hdiv := Nat.div_mul_le_self ⌈x⌉₊ 6480
    omega
  have hYlower : x ≤ (6480 * m : ℕ) :=
    (Nat.le_ceil x).trans (by exact_mod_cast hceilLower)
  have hYupper : ((6480 * m : ℕ) : ℝ) ≤ x + 6481 := by
    have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    have h := Nat.cast_le (α := ℝ).mpr hceilUpper
    push_cast at h
    push_cast
    linarith
  have hYpos : (0 : ℝ) < (6480 * m : ℕ) := by positivity
  have hlogY : Real.log ((6480 * m : ℕ) : ℝ) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
    apply Real.log_le_log hYpos
    linarith
  have hpsi := chebyshevPsi_multiple_bound m hm
  have hmono := chebyshevPsi_mono hYlower
  have hmain : c * ((6480 * m : ℕ) : ℝ) ≤ c * (x + 6481) :=
    mul_le_mul_of_nonneg_left hYupper hc
  dsimp [c, δ, K] at *
  push_cast at hmain hlogY hmono hpsi
  linarith

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Assembly.lean` -/

section


noncomputable section
open Finset BigOperators Filter
open scoped Topology
set_option maxHeartbeats 800000

lemma common_layer_index_le {n k : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (hne : (L_common 2 k A B).Nonempty) : k ≤ n := by
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨a, ha⟩ := hp'.2.1
  have ha' := Finset.mem_filter.mp ha
  have hab := Finset.mem_Icc.mp (hAB.1 ha'.1)
  have hpn : p ≤ n := (Nat.le_of_dvd (by omega) ha'.2).trans hab.2
  rw [I_layer_two] at hp'
  have hYp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp'.1).1).1
  have hkY : k < dyadicScale k := (Nat.lt_succ_self k).trans Nat.lt_two_pow_self
  omega

lemma largest_bad_layer (m : ℕ → ℕ) {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (hbad : ¬ ∀ k, (L_common 2 k A B).card ≤ m k) :
    ∃ k, m k < (L_common 2 k A B).card ∧
      ∀ j, k < j → (L_common 2 j A B).card ≤ m j := by
  classical
  let F := (Finset.range (n+1)).filter (fun k => m k < (L_common 2 k A B).card)
  have hmem (k : ℕ) (hk : m k < (L_common 2 k A B).card) : k ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := common_layer_index_le hAB (Finset.card_pos.mp (by omega : 0 < (L_common 2 k A B).card))
      omega), hk⟩
  obtain ⟨j, hj⟩ := not_forall.mp hbad
  have hF : F.Nonempty := ⟨j, hmem j (lt_of_not_ge hj)⟩
  refine ⟨F.max' hF, (Finset.mem_filter.mp (F.max'_mem hF)).2, ?_⟩
  intro j hj
  by_contra h
  exact (Finset.le_max' F j (hmem j (lt_of_not_ge h))).not_gt hj

theorem rectangle_layer_bound (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k) (hgtop : Tendsto g atTop atTop)
    (hsumm : Summable (fun k => Real.log (E_val 2 k (m k))))
    (hweights : Summable (fun k => rectangleWeight m g k * (N_layer 2 k : ℝ)))
    (hΩ : weightTotal (rectangleWeight m g) < 1) (C : ℝ)
    (hC : (111/100 : ℝ)^2 * Real.exp γ * D_val 2 m /
      (1-weightTotal (rectangleWeight m g))^2 < C) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (A.card : ℝ)*B.card < C*n^2/Real.log n := by
  let c := (111/100 : ℝ)^2 * Real.exp γ
  let d := (1-weightTotal (rectangleWeight m g))^2
  have hd : 0 < d := sq_pos_of_pos (sub_pos.mpr hΩ)
  have hD : 0 < D_val 2 m := Real.exp_pos _
  obtain ⟨ε, hε, hεC⟩ : ∃ ε : ℝ, 0 < ε ∧ (c+ε)*D_val 2 m/d < C := by
    have hlim : Tendsto (fun ε : ℝ => (c+ε)*D_val 2 m/d)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c*D_val 2 m/d)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds
        ((show Continuous (fun ε : ℝ => (c+ε)*D_val 2 m/d) by fun_prop).tendsto' _ _ (by simp))
    obtain ⟨ε, he, hp⟩ := ((hlim.eventually (gt_mem_nhds hC)).and self_mem_nhdsWithin).exists
    exact ⟨ε, hp, he⟩
  obtain ⟨N₁, hN₁⟩ := small_interval_case elementary_chebyshev_bound ε hε 2 m (by norm_num) hsumm
  obtain ⟨N₂, hN₂⟩ := large_rectangle_case elementary_chebyshev_bound ε hε m g hg1 hgtop hsumm
  refine ⟨max N₁ N₂+2, ?_⟩
  intro n hn A B hAB
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  obtain ⟨A', B', hAB', hA', hB', hretain⟩ := weighted_pair_subset (rectangleWeight m g)
    (rectangleWeight_nonneg m g (fun k => zero_le_one.trans (hg1 k))) hweights hΩ hAB
  have hregular : (A'.card : ℝ)*B'.card ≤ (c+ε)*D_val 2 m*n^2/Real.log n := by
    by_cases hsmall : ∀ k, (L_common 2 k A' B').card ≤ m k
    · exact hN₁ n hn1 A' B' hAB' hsmall
    · obtain ⟨k, hk, hhigh⟩ := largest_bad_layer m hAB' hsmall
      exact hN₂ n hn2 A' B' hAB' hA' hB' k hk hhigh
  calc
    _ ≤ ((A'.card : ℝ)*B'.card)/d := (le_div_iff₀ hd).mpr (by simpa [d, mul_comm] using hretain)
    _ ≤ ((c+ε)*D_val 2 m*n^2/Real.log n)/d := div_le_div_of_nonneg_right hregular hd.le
    _ = ((c+ε)*D_val 2 m/d) * ((n : ℝ)^2/Real.log n) := by ring
    _ < C * ((n : ℝ)^2/Real.log n) := mul_lt_mul_of_pos_right hεC (by positivity)
    _ = _ := by ring

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Series.lean` -/

section


noncomputable section
open Finset BigOperators Filter
open scoped Topology
set_option maxHeartbeats 800000

/-- A rational upper bound for the reciprocal cube root of two. -/
def geometricRatio : ℝ := 79371 / 100000

def rectangleGrowth (k : ℕ) : ℝ := 1 + ((k - 100 : ℕ) : ℝ)

lemma geometricRatio_pos : 0 < geometricRatio := by norm_num [geometricRatio]
lemma geometricRatio_lt_one : geometricRatio < 1 := by norm_num [geometricRatio]
lemma geometricRatio_cube : 1 ≤ 2 * geometricRatio^3 := by norm_num [geometricRatio]

lemma rectangleGrowth_ge_one (k : ℕ) : 1 ≤ rectangleGrowth k := by
  unfold rectangleGrowth
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma rectangleGrowth_tendsto : Tendsto rectangleGrowth atTop atTop := by
  apply tendsto_atTop_mono' atTop (show ∀ᶠ k : ℕ in atTop,
    (k : ℝ) - 100 ≤ rectangleGrowth k from ?_)
    (show Tendsto (fun k : ℕ => (k : ℝ)-100) atTop atTop from
      tendsto_atTop_add_const_right atTop (-100) tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 100] with k hk
  simp only [rectangleGrowth, Nat.cast_sub hk, Nat.cast_ofNat]
  linarith

lemma geometric_tail_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    HasSum (fun k : ℕ => if K ≤ k then q^(k+1) else 0) (q^(K+1) / (1-q)) := by
  let f := fun k : ℕ => if K ≤ k then q^(k+1) else 0
  have hshift : HasSum (fun k => f (k+K)) (q^(K+1)/(1-q)) := by
    have heq : (fun k => f (k+K)) = (fun k => q^(K+1)*q^k) := by
      funext k
      dsimp [f]
      rw [if_pos (by omega)]
      ring
    rw [heq, div_eq_mul_inv]
    exact HasSum.mul_left _ (hasSum_geometric_of_lt_one hq0 hq1)
  have hprefix : ∑ k ∈ range K, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, not_le.mpr (Finset.mem_range.mp hk)]
  simpa only [hprefix, zero_add] using hshift.sum_range_add

lemma geometric_slope_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => ((k-100 : ℕ) : ℝ) * q^(k+1)) (q^102/(1-q)^2) := by
  let f := fun k : ℕ => ((k-100 : ℕ) : ℝ) * q^(k+1)
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hone : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hsum : HasSum (fun k : ℕ => ((k : ℝ)+1)*q^k) (1/(1-q)^2) := by
    have heq : (1 : ℝ)/(1-q)^2 = q/(1-q)^2+(1-q)⁻¹ := by field_simp; ring
    simp only [add_mul, one_mul, heq]
    exact (hasSum_coe_mul_geometric_of_norm_lt_one hq).add
      (hasSum_geometric_of_lt_one hq0 hq1)
  have hshift : HasSum (fun k => f (k+101)) (q^102/(1-q)^2) := by
    have heq : (fun k => f (k+101)) = (fun k : ℕ => q^102*(((k : ℝ)+1)*q^k)) := by
      funext k
      dsimp [f]
      rw [show k+101-100=k+1 by omega]
      push_cast
      ring
    rw [heq, show q^102/(1-q)^2 = q^102*(1/(1-q)^2) by ring]
    exact HasSum.mul_left _ hsum
  have hprefix : ∑ k ∈ range 101, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, Nat.sub_eq_zero_of_le (show k ≤ 100 by have := Finset.mem_range.mp hk; omega)]
  simpa only [hprefix, zero_add] using hshift.sum_range_add

def weightedGeometricTail (k : ℕ) : ℝ :=
  if 16 ≤ k then rectangleGrowth k * geometricRatio^(k+1) else 0

lemma weightedGeometricTail_hasSum : HasSum weightedGeometricTail
    (geometricRatio^17/(1-geometricRatio) + geometricRatio^102/(1-geometricRatio)^2) := by
  have heq : weightedGeometricTail = fun k =>
      (if 16 ≤ k then geometricRatio^(k+1) else 0) +
      ((k-100 : ℕ) : ℝ)*geometricRatio^(k+1) := by
    funext k
    dsimp [weightedGeometricTail, rectangleGrowth]
    split_ifs with hk
    · ring
    · simp [Nat.sub_eq_zero_of_le (show k ≤ 100 by omega)]
  rw [heq]
  exact (geometric_tail_hasSum geometricRatio geometricRatio_pos.le geometricRatio_lt_one 16).add
    (geometric_slope_hasSum geometricRatio geometricRatio_pos.le geometricRatio_lt_one)

lemma weightedGeometricTail_nonneg (k : ℕ) : 0 ≤ weightedGeometricTail k := by
  unfold weightedGeometricTail
  split_ifs
  · exact mul_nonneg (zero_le_one.trans (rectangleGrowth_ge_one k))
      (pow_nonneg geometricRatio_pos.le _)
  · rfl

lemma weightedGeometricTail_sum_lt : ∑' k, weightedGeometricTail k < (191/2000 : ℝ) := by
  rw [weightedGeometricTail_hasSum.tsum_eq]
  norm_num [geometricRatio]

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/Parameters.lean` -/

section


noncomputable section
open Finset BigOperators
set_option maxHeartbeats 800000

def rectangleCap (k : ℕ) : ℝ := (4/5) / (geometricRatio^(k+1))^2

def rectangleMultiplicity (k : ℕ) : ℕ :=
  if k < 16 then N_layer 2 k else min (N_layer 2 k) ⌊rectangleCap k⌋₊

lemma rectangleMultiplicity_le (k : ℕ) : rectangleMultiplicity k ≤ N_layer 2 k := by
  unfold rectangleMultiplicity
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma rectangleMultiplicity_active (k : ℕ) (hk : rectangleMultiplicity k < N_layer 2 k) :
    16 ≤ k ∧ rectangleMultiplicity k = ⌊rectangleCap k⌋₊ := by
  have h16 : ¬ k < 16 := by intro h; simpa [rectangleMultiplicity, h] using hk
  refine ⟨by omega, ?_⟩
  simp only [rectangleMultiplicity, if_neg h16] at hk ⊢
  exact min_eq_right (by omega)

lemma floor_inverse_sqrt_bound (x : ℝ) (hx : 0 < x) :
    1 / Real.sqrt ((⌊(4/5 : ℝ)/x^2⌋₊ : ℝ)+1) ≤ (1119/1000 : ℝ)*x := by
  have hs : 0 < Real.sqrt ((⌊(4/5 : ℝ)/x^2⌋₊ : ℝ)+1) := by positivity
  apply (div_le_iff₀ hs).mpr
  apply (sq_le_sq₀ zero_le_one (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hf := Nat.lt_floor_add_one ((4/5 : ℝ)/x^2)
  have hh := mul_lt_mul_of_pos_right hf (sq_pos_of_pos hx)
  rw [div_mul_cancel₀ _ (sq_pos_of_pos hx).ne'] at hh
  nlinarith

lemma rectangle_weight_majorant (k : ℕ) :
    rectangleWeight rectangleMultiplicity rectangleGrowth k * (N_layer 2 k : ℝ) ≤
      ((72/100 : ℝ)*(1119/1000))*weightedGeometricTail k := by
  by_cases hk : rectangleMultiplicity k < N_layer 2 k
  · obtain ⟨h16, heq⟩ := rectangleMultiplicity_active k hk
    have hd := dyadic_density_bound k h16
    have hs := floor_inverse_sqrt_bound (geometricRatio^(k+1))
      (pow_pos geometricRatio_pos _)
    have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
    have hM : 0 < M_layer 2 k := M_layer_positive _ _
    have hg : 0 ≤ rectangleGrowth k := zero_le_one.trans (rectangleGrowth_ge_one k)
    calc
      _ = ((N_layer 2 k : ℝ)/(Y_val 2 k*Real.sqrt (M_layer 2 k))) *
          (1/Real.sqrt ((⌊rectangleCap k⌋₊ : ℝ)+1)) * rectangleGrowth k := by
        rw [rectangleWeight, if_pos hk, heq]
        ring
      _ ≤ (72/100 : ℝ)*((1119/1000)*geometricRatio^(k+1))*rectangleGrowth k := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hd hs (by positivity) (by norm_num)) hg
      _ = _ := by rw [weightedGeometricTail, if_pos h16]; ring
  · simp only [rectangleWeight, if_neg hk, zero_mul]
    exact mul_nonneg (by norm_num) (weightedGeometricTail_nonneg k)

lemma rectangle_weights_summable : Summable (fun k =>
    rectangleWeight rectangleMultiplicity rectangleGrowth k * (N_layer 2 k : ℝ)) := by
  apply (weightedGeometricTail_hasSum.summable.mul_left ((72/100 : ℝ)*(1119/1000))).of_nonneg_of_le
  · intro k
    exact mul_nonneg (rectangleWeight_nonneg _ _
      (fun k => zero_le_one.trans (rectangleGrowth_ge_one k)) k) (Nat.cast_nonneg _)
  · exact rectangle_weight_majorant

lemma rectangle_weightTotal_lt : weightTotal
    (rectangleWeight rectangleMultiplicity rectangleGrowth) < (77/1000 : ℝ) := by
  have h := Summable.tsum_le_tsum rectangle_weight_majorant rectangle_weights_summable
    (weightedGeometricTail_hasSum.summable.mul_left ((72/100 : ℝ)*(1119/1000)))
  rw [tsum_mul_left] at h
  have ht := mul_lt_mul_of_pos_left weightedGeometricTail_sum_lt
    (by norm_num : 0 < (72/100 : ℝ)*(1119/1000))
  dsimp [weightTotal]
  linarith

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductCertificate.lean` -/

section



open Finset

noncomputable def primeReciprocalFactor (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ) / (n - 1) else 1

/-- A zero entry retains the integer's Euler factor. A nonzero entry must
certify compositeness by a proper divisor. Rounded products are upper bounds. -/
def roundedProductCertificate (n b : ℕ) : List ℕ → Option ℕ
  | [] => some b
  | d :: ds =>
      if d = 0 then
        roundedProductCertificate (n + 1) ((b * n + n - 2) / (n - 1)) ds
      else if 1 < d ∧ d < n ∧ d ∣ n then
        roundedProductCertificate (n + 1) b ds
      else none

lemma primeReciprocalFactor_nonneg (n : ℕ) : 0 ≤ primeReciprocalFactor n := by
  unfold primeReciprocalFactor
  split_ifs with hp
  · have hn : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
    exact div_nonneg (Nat.cast_nonneg n) (by linarith)
  · norm_num

lemma primeReciprocalFactor_le {n : ℕ} (hn : 2 ≤ n) :
    primeReciprocalFactor n ≤ (n : ℝ) / (n - 1) := by
  unfold primeReciprocalFactor
  split_ifs
  · rfl
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < n - 1)]
    norm_num

lemma le_rounded_product {n b : ℕ} (hn : 2 ≤ n) :
    (b : ℝ) * primeReciprocalFactor n ≤ ((b * n + n - 2) / (n - 1) : ℕ) := by
  have hd : 0 < n - 1 := by omega
  have hdiv : b * n ≤ ((b * n + n - 2) / (n - 1)) * (n - 1) := by
    have h := Nat.div_add_mod (b * n + n - 2) (n - 1)
    have hm := Nat.mod_lt (b * n + n - 2) hd
    rw [Nat.mul_comm (n - 1)] at h
    omega
  have hnR : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    (b : ℝ) * primeReciprocalFactor n ≤ b * ((n : ℝ) / (n - 1)) :=
      mul_le_mul_of_nonneg_left (primeReciprocalFactor_le hn) (Nat.cast_nonneg b)
    _ ≤ ((b * n + n - 2) / (n - 1) : ℕ) := by
      rw [← mul_div_assoc, div_le_iff₀ hnR]
      have h := Nat.cast_le (α := ℝ).mpr hdiv
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h
      exact h

theorem roundedProductCertificate_sound {n b v : ℕ} {ds : List ℕ}
    (hn : 2 ≤ n) (h : roundedProductCertificate n b ds = some v) :
    (b : ℝ) * ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (n + i) ≤ v := by
  induction ds generalizing n b v with
  | nil =>
    simp only [roundedProductCertificate, Option.some.injEq] at h
    subst v
    simp
  | cons d ds ih =>
    simp only [roundedProductCertificate] at h
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [Nat.add_zero]
    have htail : 0 ≤ ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (n + (i + 1)) :=
      Finset.prod_nonneg fun i _ => primeReciprocalFactor_nonneg _
    split_ifs at h with hd hcomp
    · have hi := ih (by omega : 2 ≤ n + 1) h
      have hstep := mul_le_mul_of_nonneg_right (le_rounded_product (b := b) hn) htail
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at hi hstep ⊢
      simpa [mul_assoc, mul_comm, mul_left_comm, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hstep.trans hi
    · have hnp : ¬ n.Prime := by
        intro hp
        rcases (Nat.dvd_prime hp).mp hcomp.2.2 with h | h <;> omega
      simpa [primeReciprocalFactor, hnp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (by omega : 2 ≤ n + 1) h

noncomputable def reciprocalPrefix (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, primeReciprocalFactor (2 + i)

theorem certificate_prefix_step {scale : ℝ} {n b v : ℕ} {ds : List ℕ}
    (hprev : scale * reciprocalPrefix n ≤ b)
    (hcert : roundedProductCertificate (2 + n) b ds = some v) :
    scale * reciprocalPrefix (n + ds.length) ≤ v := by
  have hc := roundedProductCertificate_sound (by omega : 2 ≤ 2 + n) hcert
  unfold reciprocalPrefix at hprev ⊢
  rw [Finset.prod_range_add]
  have ht : 0 ≤ ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) :=
    Finset.prod_nonneg fun _ _ => primeReciprocalFactor_nonneg _
  calc
    _ = (scale * ∏ i ∈ Finset.range n, primeReciprocalFactor (2 + i)) *
        ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) := by ring
    _ ≤ (b : ℝ) * ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) :=
      mul_le_mul_of_nonneg_right hprev ht
    _ ≤ v := by simpa only [Nat.add_assoc] using hc

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block00.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData000 : List ℕ :=
  [0, 0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData000_checked :
    roundedProductCertificate 2 1000000000000 productData000 = some 11203742951367 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData000_length : productData000.length = 512 := by decide

def productData001 : List ℕ :=
  [2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 29, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData001_checked :
    roundedProductCertificate 514 11203742951367 productData001 = some 12399746588801 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData001_length : productData001.length = 512 := by decide

def productData002 : List ℕ :=
  [2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 29, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData002_checked :
    roundedProductCertificate 1026 12399746588801 productData002 = some 13108738941674 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData002_length : productData002.length = 512 := by decide

def productData003 : List ℕ :=
  [2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 17, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 43, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 17,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 37, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData003_checked :
    roundedProductCertificate 1538 13108738941674 productData003 = some 13614119445717 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData003_length : productData003.length = 512 := by decide

def productData004 : List ℕ :=
  [2, 7, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 29, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 41, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 47,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 41, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData004_checked :
    roundedProductCertificate 2050 13614119445717 productData004 = some 14011848726911 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData004_length : productData004.length = 512 := by decide

def productData005 : List ℕ :=
  [2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 37, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 43,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 23, 2, 37, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData005_checked :
    roundedProductCertificate 2562 14011848726911 productData005 = some 14335170298766 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData005_length : productData005.length = 512 := by decide

def productData006 : List ℕ :=
  [2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 31, 2, 13, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 19, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData006_checked :
    roundedProductCertificate 3074 14335170298766 productData006 = some 14608317423581 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData006_length : productData006.length = 512 := by decide

def productData007 : List ℕ :=
  [2, 17, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 41,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 29, 2, 3, 2, 41, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 37,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 17, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData007_checked :
    roundedProductCertificate 3586 14608317423581 productData007 = some 14846326480019 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData007_length : productData007.length = 512 := by decide

def productData008 : List ℕ :=
  [2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 47, 2, 3, 2, 53, 2, 59, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 59, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23,
    2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 17, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData008_checked :
    roundedProductCertificate 4098 14846326480019 productData008 = some 15049251388708 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData008_length : productData008.length = 512 := by decide

def productData009 : List ℕ :=
  [2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 47, 2, 29, 2, 3, 2, 37, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData009_checked :
    roundedProductCertificate 4610 15049251388708 productData009 = some 15242042490043 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData009_length : productData009.length = 512 := by decide

def productData010 : List ℕ :=
  [2, 47, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 37, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 17, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29,
    2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 23, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 43]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData010_checked :
    roundedProductCertificate 5122 15242042490043 productData010 = some 15395819608648 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData010_length : productData010.length = 512 := by decide

def productData011 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 41, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 29, 2, 23, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 43, 2, 71, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 61, 2, 3, 2, 31,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 7, 2, 59, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 31, 2, 3,
    2, 0, 2, 53, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 31, 2, 41, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData011_checked :
    roundedProductCertificate 5634 15395819608648 productData011 = some 15559272192512 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData011_length : productData011.length = 512 := by decide

def productData012 : List ℕ :=
  [2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 79,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 11, 2, 61, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37,
    2, 19, 2, 3, 2, 43, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 7,
    2, 3, 2, 41, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 43, 2, 3, 2, 73,
    2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 61, 2, 0,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 79, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 17, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData012_checked :
    roundedProductCertificate 6146 15559272192512 productData012 = some 15696355750714 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData012_length : productData012.length = 512 := by decide

def productData013 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 43, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 71, 2, 83, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 53, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 43,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 13, 2, 3, 2, 31, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 41, 2, 3, 2, 47, 2, 31, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 17, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 67]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData013_checked :
    roundedProductCertificate 6658 15696355750714 productData013 = some 15831281286877 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData013_length : productData013.length = 512 := by decide

def productData014 : List ℕ :=
  [2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 19,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 23, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17,
    2, 37, 2, 3, 2, 53, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 13, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 73, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47, 2, 79, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData014_checked :
    roundedProductCertificate 7170 15831281286877 productData014 = some 15955277652573 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData014_length : productData014.length = 512 := by decide

def productData015 : List ℕ :=
  [2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 31, 2, 43, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 73, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 0, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 71, 2, 3, 2, 23, 2, 7, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 83, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 47, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 29, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData015_checked :
    roundedProductCertificate 7682 15955277652573 productData015 = some 16064263523133 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData015_length : productData015.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block01.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData016 : List ℕ :=
  [2, 5, 2, 7, 2, 3, 2, 59, 2, 13, 2, 3, 2, 29, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 37, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53,
    2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 61, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 83, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 47, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 37, 2, 3, 2, 7, 2, 61, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 11, 2, 3, 2, 47, 2, 67, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 83, 2, 17, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 53, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 17, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData016_checked :
    roundedProductCertificate 8194 16064263523133 productData016 = some 16171070360976 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData016_length : productData016.length = 512 := by decide

def productData017 : List ℕ :=
  [2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 0, 2, 3, 2, 79, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 89, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 29, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 43, 2, 3, 2, 29, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 61,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 89, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData017_checked :
    roundedProductCertificate 8706 16171070360976 productData017 = some 16276188653242 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData017_length : productData017.length = 512 := by decide

def productData018 : List ℕ :=
  [2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 0, 2, 47, 2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 71, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 67,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 83, 2, 3, 2, 11, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 97,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 89, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 19, 2, 11, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 5, 2, 61, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 53, 2, 5, 2, 3, 2, 29, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 31, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 89, 2, 31, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData018_checked :
    roundedProductCertificate 9218 16276188653242 productData018 = some 16374523251979 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData018_length : productData018.length = 512 := by decide

def productData019 : List ℕ :=
  [2, 37, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43,
    2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 97, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 47, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 67, 2, 5,
    2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 13, 2, 3, 2, 73, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 43, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 79, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 19, 2, 3, 2, 5, 2, 89, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 29, 2, 53, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 73, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 61, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData019_checked :
    roundedProductCertificate 9730 16374523251979 productData019 = some 16465132845889 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData019_length : productData019.length = 512 := by decide

def productData020 : List ℕ :=
  [2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 43, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 43, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 19, 2, 3, 2, 37, 2, 0, 2, 3,
    2, 101, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 67, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 83, 2, 13, 2, 3, 2, 53, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 59,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 97, 2, 3, 2, 7, 2, 71, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 103, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 13, 2, 5, 2, 3, 2, 59, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71,
    2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData020_checked :
    roundedProductCertificate 10242 16465132845889 productData020 = some 16554857923270 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData020_length : productData020.length = 512 := by decide

def productData021 : List ℕ :=
  [2, 3, 2, 31, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 41, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3, 2, 19, 2, 11, 2, 3, 2, 29,
    2, 31, 2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 83, 2, 3, 2, 73, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 61, 2, 67, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 101,
    2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 103, 2, 73, 2, 3, 2, 0, 2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 61,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 71, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 67, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23,
    2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 103, 2, 3, 2, 11, 2, 47,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData021_checked :
    roundedProductCertificate 10754 16554857923270 productData021 = some 16631668344487 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData021_length : productData021.length = 512 := by decide

def productData022 : List ℕ :=
  [2, 19, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 47, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 37, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 31, 2, 3, 2, 19, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 101, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 107, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 41,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 83, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 31, 2, 3, 2, 43, 2, 23, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 59, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 61, 2, 43, 2, 3, 2, 0, 2, 89, 2, 3, 2, 107, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 59, 2, 0, 2, 3,
    2, 17, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79, 2, 61, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData022_checked :
    roundedProductCertificate 11266 16631668344487 productData022 = some 16701197414906 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData022_length : productData022.length = 512 := by decide

def productData023 : List ℕ :=
  [2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 7, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 73, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 19, 2, 3, 2, 67, 2, 5, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 61, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 53, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 47, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 53, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 23, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 73, 2, 89,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 17, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 11, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData023_checked :
    roundedProductCertificate 11778 16701197414906 productData023 = some 16784734264327 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData023_length : productData023.length = 512 := by decide

def productData024 : List ℕ :=
  [2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 7, 2, 3, 2, 109, 2, 97, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 17, 2, 47, 2, 3, 2, 5, 2, 83, 2, 3, 2, 89, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 79, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 59,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 41, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 97, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 47,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 113,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 67, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData024_checked :
    roundedProductCertificate 12290 16784734264327 productData024 = some 16859807852420 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData024_length : productData024.length = 512 := by decide

def productData025 : List ℕ :=
  [2, 7, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 101, 2, 0, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 71, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 17, 2, 61, 2, 3, 2, 5, 2, 79, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 67, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 29, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 73, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 103, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 79, 2, 5, 2, 3, 2, 67, 2, 43, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 73, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 101, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 53, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData025_checked :
    roundedProductCertificate 12802 16859807852420 productData025 = some 16930989739248 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData025_length : productData025.length = 512 := by decide

def productData026 : List ℕ :=
  [2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 29, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 89, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 97, 2, 3, 2, 0, 2, 7, 2, 3, 2, 103, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 11, 2, 29, 2, 3, 2, 19, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 17, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 61, 2, 3, 2, 11, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0,
    2, 3, 2, 13, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3,
    2, 79, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 41, 2, 13, 2, 3, 2, 23, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData026_checked :
    roundedProductCertificate 13314 16930989739248 productData026 = some 16995963942758 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData026_length : productData026.length = 512 := by decide

def productData027 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 0, 2, 109, 2, 3, 2, 61, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17,
    2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 73, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 89, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 107,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 101, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 73, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 103, 2, 11,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 71, 2, 13, 2, 3, 2, 5, 2, 67, 2, 3, 2, 79, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 43, 2, 3, 2, 23, 2, 29, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 13, 2, 17, 2, 3, 2, 11, 2, 19, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 109, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 17, 2, 79, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData027_checked :
    roundedProductCertificate 13826 16995963942758 productData027 = some 17054085181054 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData027_length : productData027.length = 512 := by decide

def productData028 : List ℕ :=
  [2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 31, 2, 3, 2, 7, 2, 83, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 73, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 29, 2, 41, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 89, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 97, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 107, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 53, 2, 0, 2, 3, 2, 19, 2, 37,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 113, 2, 3, 2, 13, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData028_checked :
    roundedProductCertificate 14338 17054085181054 productData028 = some 17121974261549 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData028_length : productData028.length = 512 := by decide

def productData029 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 89, 2, 3, 2, 0, 2, 0, 2, 3, 2, 107, 2, 5, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 71, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 41, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 59, 2, 3, 2, 29, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 13, 2, 3, 2, 0, 2, 97, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 101, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 67, 2, 3, 2, 103, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData029_checked :
    roundedProductCertificate 14850 17121974261549 productData029 = some 17185506565353 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData029_length : productData029.length = 512 := by decide

def productData030 : List ℕ :=
  [2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 89, 2, 3, 2, 0, 2, 73, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 113, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 0, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 103,
    2, 3, 2, 47, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 13, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 61, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 41, 2, 3, 2, 113, 2, 23, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 11, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 31, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 71, 2, 5, 2, 3, 2, 47, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 83, 2, 3, 2, 101, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData030_checked :
    roundedProductCertificate 15362 17185506565353 productData030 = some 17243948805667 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData030_length : productData030.length = 512 := by decide

def productData031 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 89, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 19, 2, 107, 2, 3, 2, 37, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 83, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 7, 2, 43, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 127,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 31, 2, 29, 2, 3, 2, 107, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 19, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 97, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 109, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 71, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 0, 2, 3, 2, 41, 2, 73, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 47, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData031_checked :
    roundedProductCertificate 15874 17243948805667 productData031 = some 17299682762857 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData031_length : productData031.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block02.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData032 : List ℕ :=
  [2, 7, 2, 3, 2, 37, 2, 13, 2, 3, 2, 19, 2, 23, 2, 3, 2, 47, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 109, 2, 3, 2, 101, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 53, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 83, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 71, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 0, 2, 3, 2, 11,
    2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 127, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 79, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 73, 2, 3, 2, 23, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41,
    2, 31, 2, 3, 2, 5, 2, 19, 2, 3, 2, 97, 2, 13, 2, 3, 2, 0, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 107, 2, 53,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 67, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 113, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5,
    2, 101, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 61]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData032_checked :
    roundedProductCertificate 16386 17299682762857 productData032 = some 17349670433605 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData032_length : productData032.length = 512 := by decide

def productData033 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 19, 2, 71, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 23, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 113, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 11, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71, 2, 109, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 0, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 89, 2, 41, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 103, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 67, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 47,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 61, 2, 3, 2, 31, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 37, 2, 11,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData033_checked :
    roundedProductCertificate 16898 17349670433605 productData033 = some 17404386755264 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData033_length : productData033.length = 512 := by decide

def productData034 : List ℕ :=
  [2, 23, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 107,
    2, 0, 2, 3, 2, 73, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 101,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 47, 2, 89, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 73, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 79, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 31, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 127, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 11, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 89, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 109, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 47, 2, 5, 2, 3, 2, 103, 2, 71, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 53, 2, 0, 2, 3, 2, 17, 2, 107, 2, 3, 2, 61, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData034_checked :
    roundedProductCertificate 17410 17404386755264 productData034 = some 17455715870899 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData034_length : productData034.length = 512 := by decide

def productData035 : List ℕ :=
  [2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 131, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 41, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43,
    2, 37, 2, 3, 2, 67, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 101, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 43, 2, 3, 2, 19, 2, 7, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 67, 2, 3, 2, 11, 2, 41, 2, 3, 2, 37, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 131,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 101, 2, 47, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 17, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 79, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData035_checked :
    roundedProductCertificate 17922 17455715870899 productData035 = some 17510549124232 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData035_length : productData035.length = 512 := by decide

def productData036 : List ℕ :=
  [2, 3, 2, 103, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3,
    2, 59, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 53,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 7,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 67, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 103, 2, 3, 2, 29, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 47, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 71, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 13, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 97,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 11, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 73, 2, 29, 2, 3, 2, 7, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 67, 2, 19, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 109, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 113, 2, 3, 2, 5, 2, 43, 2, 3, 2, 79,
    2, 23, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 127, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 19, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData036_checked :
    roundedProductCertificate 18434 17510549124232 productData036 = some 17550927752100 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData036_length : productData036.length = 512 := by decide

def productData037 : List ℕ :=
  [2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 13, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 31, 2, 3, 2, 83, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 79, 2, 3,
    2, 137, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 61, 2, 3, 2, 13, 2, 71, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 97, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 31, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 11, 2, 107, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29,
    2, 19, 2, 3, 2, 5, 2, 127, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 73, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 71, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 101, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 0, 2, 97, 2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 139, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 61, 2, 83, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19,
    2, 17, 2, 3, 2, 107, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData037_checked :
    roundedProductCertificate 18946 17550927752100 productData037 = some 17598473068027 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData037_length : productData037.length = 512 := by decide

def productData038 : List ℕ :=
  [2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 109, 2, 13, 2, 3, 2, 29, 2, 131, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 113, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 67, 2, 29, 2, 3, 2, 73, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7,
    2, 43, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 71, 2, 13, 2, 3, 2, 103, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 109, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 17, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 131, 2, 73, 2, 3, 2, 47, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 89, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 11, 2, 103, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 17, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 31, 2, 3, 2, 0,
    2, 127, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData038_checked :
    roundedProductCertificate 19458 17598473068027 productData038 = some 17644077998415 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData038_length : productData038.length = 512 := by decide

def productData039 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 83, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 31, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 43, 2, 7, 2, 3, 2, 53, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3,
    2, 101, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 41, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 61, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 0, 2, 89, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5,
    2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 37, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 103, 2, 7, 2, 3, 2, 0, 2, 53, 2, 3, 2, 79, 2, 5, 2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 89, 2, 11, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 137, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 113, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 97, 2, 3, 2, 11, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData039_checked :
    roundedProductCertificate 19970 17644077998415 productData039 = some 17692154016685 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData039_length : productData039.length = 512 := by decide

def productData040 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 103, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 29, 2, 0, 2, 3, 2, 131, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37,
    2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 17, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 107, 2, 19, 2, 3, 2, 7, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 137, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 127, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 139, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 89,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 79, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11,
    2, 71, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 109, 2, 47, 2, 3, 2, 5, 2, 59, 2, 3, 2, 37, 2, 83,
    2, 3, 2, 67, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 31, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 13, 2, 67, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 139, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData040_checked :
    roundedProductCertificate 20482 17692154016685 productData040 = some 17733141360984 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData040_length : productData040.length = 512 := by decide

def productData041 : List ℕ :=
  [2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 109, 2, 3, 2, 53, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 107, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 67, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 79, 2, 53, 2, 3, 2, 29, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 7, 2, 61, 2, 3, 2, 107, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 101, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 37, 2, 3, 2, 131, 2, 5, 2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 79,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 89, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 109,
    2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData041_checked :
    roundedProductCertificate 20994 17733141360984 productData041 = some 17777434714941 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData041_length : productData041.length = 512 := by decide

def productData042 : List ℕ :=
  [2, 3, 2, 137, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 97, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 13, 2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 109, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 31, 2, 103, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47,
    2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 71, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 139, 2, 3,
    2, 13, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 0, 2, 79, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 17, 2, 47, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 127, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData042_checked :
    roundedProductCertificate 21506 17777434714941 productData042 = some 17820812292081 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData042_length : productData042.length = 512 := by decide

def productData043 : List ℕ :=
  [2, 97, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 71,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 41, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 149, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 7, 2, 97, 2, 3, 2, 13, 2, 17, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 113, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 83, 2, 3, 2, 137, 2, 23, 2, 3, 2, 7,
    2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 59, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 17, 2, 3, 2, 41, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 37, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 113, 2, 43, 2, 3, 2, 83, 2, 5, 2, 3,
    2, 149, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 47, 2, 3, 2, 11, 2, 7, 2, 3, 2, 101, 2, 5, 2, 3, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData043_checked :
    roundedProductCertificate 22018 17820812292081 productData043 = some 17861712502297 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData043_length : productData043.length = 512 := by decide

def productData044 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 107, 2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 97, 2, 7, 2, 3, 2, 13, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 17, 2, 131, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 127, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 61,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 29, 2, 5, 2, 3, 2, 37, 2, 17, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 53, 2, 3, 2, 11, 2, 73,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 89, 2, 3, 2, 0, 2, 137, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 23, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 53, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 103, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 127, 2, 3, 2, 83, 2, 0, 2, 3, 2, 13, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData044_checked :
    roundedProductCertificate 22530 17861712502297 productData044 = some 17904875730967 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData044_length : productData044.length = 512 := by decide

def productData045 : List ℕ :=
  [2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 61, 2, 3, 2, 19, 2, 5, 2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 73, 2, 0, 2, 3, 2, 79, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 139, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 19, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 43, 2, 3,
    2, 53, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 83, 2, 3, 2, 0, 2, 41,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 61, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 103, 2, 67, 2, 3, 2, 7, 2, 19, 2, 3, 2, 149,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 89, 2, 3, 2, 41, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 131, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 53, 2, 3, 2, 23, 2, 5, 2, 3, 2, 83,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 43,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 101, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData045_checked :
    roundedProductCertificate 23042 17904875730967 productData045 = some 17940291941127 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData045_length : productData045.length = 512 := by decide

def productData046 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5,
    2, 103, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 67, 2, 7, 2, 3, 2, 41, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 137, 2, 3, 2, 5, 2, 151, 2, 3, 2, 131, 2, 23,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 113, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 47, 2, 3, 2, 71, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 37, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 17, 2, 3, 2, 0, 2, 13, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 29, 2, 0, 2, 3, 2, 139, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData046_checked :
    roundedProductCertificate 23554 17940291941127 productData046 = some 17984066362855 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData046_length : productData046.length = 512 := by decide

def productData047 : List ℕ :=
  [2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 59, 2, 0, 2, 3, 2, 0, 2, 101, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37,
    2, 73, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17, 2, 13,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 11, 2, 3, 2, 5, 2, 61, 2, 3, 2, 53, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 127,
    2, 17, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 149, 2, 107,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 109, 2, 3, 2, 7, 2, 41, 2, 3, 2, 0, 2, 83, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 101, 2, 11, 2, 3, 2, 97, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 53, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 61, 2, 17, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 19, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 107, 2, 5, 2, 3, 2, 0, 2, 127, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 137, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 13, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData047_checked :
    roundedProductCertificate 24066 17984066362855 productData047 = some 18020364305374 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData047_length : productData047.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block03.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData048 : List ℕ :=
  [2, 3, 2, 47, 2, 13, 2, 3, 2, 23, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 73, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 151, 2, 3, 2, 103, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 41,
    2, 19, 2, 3, 2, 7, 2, 157, 2, 3, 2, 89, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 59, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29,
    2, 11, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 137, 2, 0, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 103, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 139, 2, 149, 2, 3, 2, 41, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 97,
    2, 107, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 109,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 11, 2, 3, 2, 17, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 127, 2, 131, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 79, 2, 5, 2, 3, 2, 37, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 19, 2, 71, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData048_checked :
    roundedProductCertificate 24578 18020364305374 productData048 = some 18052307364230 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData048_length : productData048.length = 512 := by decide

def productData049 : List ℕ :=
  [2, 11, 2, 23, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 5, 2, 3, 2, 23, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 11, 2, 139, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 89, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 19, 2, 3, 2, 151,
    2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 37, 2, 127, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 131, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 73, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 101, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 41, 2, 17, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 67, 2, 3, 2, 109, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47, 2, 59, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 73, 2, 3, 2, 83, 2, 17, 2, 3, 2, 7, 2, 71, 2, 3, 2, 13, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 97, 2, 31, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 59, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 7, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData049_checked :
    roundedProductCertificate 25090 18052307364230 productData049 = some 18087963813665 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData049_length : productData049.length = 512 := by decide

def productData050 : List ℕ :=
  [2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 11, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7,
    2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 29, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 149, 2, 3, 2, 7, 2, 19, 2, 3, 2, 107, 2, 17, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 53, 2, 83, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3,
    2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 0, 2, 3, 2, 113, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 13, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 19, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 53, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 109, 2, 0, 2, 3, 2, 71, 2, 11, 2, 3, 2, 67, 2, 5, 2, 3, 2, 131, 2, 29, 2, 3, 2, 5, 2, 89, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData050_checked :
    roundedProductCertificate 25602 18087963813665 productData050 = some 18124380549853 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData050_length : productData050.length = 512 := by decide

def productData051 : List ℕ :=
  [2, 3, 2, 7, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 11, 2, 79, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 73, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 157, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 37, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 11, 2, 41, 2, 3, 2, 5, 2, 97, 2, 3, 2, 61, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 113, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 43, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 61, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 137, 2, 31, 2, 3, 2, 53, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 103, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 43, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 139, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 101, 2, 3, 2, 31, 2, 163, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 67, 2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 79, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData051_checked :
    roundedProductCertificate 26114 18124380549853 productData051 = some 18156737390679 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData051_length : productData051.length = 512 := by decide

def productData052 : List ℕ :=
  [2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 11, 2, 3, 2, 19,
    2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 149, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 47, 2, 3, 2, 7, 2, 23, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 41, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 127, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 139, 2, 3, 2, 7, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 67, 2, 97, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 17, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 149, 2, 7, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 41, 2, 3, 2, 61, 2, 5, 2, 3, 2, 151, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 103, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 47, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 43, 2, 3, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData052_checked :
    roundedProductCertificate 26626 18156737390679 productData052 = some 18195299746015 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData052_length : productData052.length = 512 := by decide

def productData053 : List ℕ :=
  [2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 157, 2, 23, 2, 3, 2, 7, 2, 101,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 59, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 163, 2, 7, 2, 3, 2, 19, 2, 73, 2, 3, 2, 113,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 97, 2, 0, 2, 3, 2, 137, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 11, 2, 3, 2, 59, 2, 17, 2, 3, 2, 89, 2, 5, 2, 3, 2, 0,
    2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 37, 2, 3, 2, 23, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 109, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 101, 2, 31, 2, 3, 2, 7, 2, 11, 2, 3, 2, 139, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 11, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 97, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 11, 2, 13, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 37, 2, 19, 2, 3, 2, 31, 2, 107, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 59,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 19, 2, 79, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0,
    2, 71, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 131, 2, 7, 2, 3, 2, 0, 2, 43]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData053_checked :
    roundedProductCertificate 27138 18195299746015 productData053 = some 18222546799596 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData053_length : productData053.length = 512 := by decide

def productData054 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 139, 2, 3, 2, 5, 2, 73, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 89, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 103, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 53, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 89, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 47, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3, 2, 79, 2, 167, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 13, 2, 103, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 83, 2, 11, 2, 3, 2, 101, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 41, 2, 3, 2, 7, 2, 37, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 61, 2, 0, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 107, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 37, 2, 29, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData054_checked :
    roundedProductCertificate 27650 18222546799596 productData054 = some 18257863299962 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData054_length : productData054.length = 512 := by decide

def productData055 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 89, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 61, 2, 3, 2, 47, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 7, 2, 59, 2, 3, 2, 5, 2, 23, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 127,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 41, 2, 29, 2, 3, 2, 43, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 79, 2, 113, 2, 3, 2, 19, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 101, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 73, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 157,
    2, 3, 2, 97, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 37, 2, 3, 2, 11, 2, 149, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 61, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 47, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 101, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 109, 2, 0, 2, 3, 2, 53]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData055_checked :
    roundedProductCertificate 28162 18257863299962 productData055 = some 18292548977727 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData055_length : productData055.length = 512 := by decide

def productData056 : List ℕ :=
  [2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 29, 2, 41, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 149, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 107, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 83,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 127, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 151, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 67, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 167, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 137, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 19, 2, 43, 2, 3, 2, 103, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 83, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 79,
    2, 3, 2, 107, 2, 47, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 113, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 17, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 127, 2, 3, 2, 17, 2, 19,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 43, 2, 7, 2, 3, 2, 11, 2, 37, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 151, 2, 3, 2, 0, 2, 103, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 163, 2, 0, 2, 3, 2, 7, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData056_checked :
    roundedProductCertificate 28674 18292548977727 productData056 = some 18322924621983 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData056_length : productData056.length = 512 := by decide

def productData057 : List ℕ :=
  [2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 131, 2, 5, 2, 3,
    2, 61, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 29, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 109, 2, 7, 2, 3, 2, 0, 2, 139, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 149, 2, 3, 2, 31, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 23, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 67, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59,
    2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 17, 2, 3, 2, 5, 2, 79, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 7, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 163, 2, 3,
    2, 19, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 109, 2, 3, 2, 31, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 127, 2, 101, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 149, 2, 13, 2, 3, 2, 47, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 67, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData057_checked :
    roundedProductCertificate 29186 18322924621983 productData057 = some 18353455368294 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData057_length : productData057.length = 512 := by decide

def productData058 : List ℕ :=
  [2, 17, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2, 11, 2, 43, 2, 3, 2, 0, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 131, 2, 3, 2, 0, 2, 7, 2, 3, 2, 151, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 19, 2, 3, 2, 11, 2, 97, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 17, 2, 0, 2, 3, 2, 41, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 73,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 71, 2, 167, 2, 3, 2, 7, 2, 29, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 0, 2, 173, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 7,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 157, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 131, 2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 151,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 17, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3, 2, 97, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 103, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 109, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData058_checked :
    roundedProductCertificate 29698 18353455368294 productData058 = some 18381643589969 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData058_length : productData058.length = 512 := by decide

def productData059 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 47, 2, 0, 2, 3, 2, 167, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 79, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 107, 2, 11, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 157, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 127, 2, 5, 2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 37, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 113, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 13, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 11, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 83, 2, 41, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 131, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 137, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 73, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 37, 2, 71, 2, 3, 2, 5, 2, 127, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 67, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 109, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 11, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0,
    2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 31]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData059_checked :
    roundedProductCertificate 30210 18381643589969 productData059 = some 18410017085562 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData059_length : productData059.length = 512 := by decide

def productData060 : List ℕ :=
  [2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 73, 2, 3, 2, 7, 2, 59, 2, 3, 2, 71, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 41, 2, 7, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 109, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 89, 2, 3, 2, 67, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 43, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 173, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 139, 2, 3, 2, 29, 2, 7, 2, 3, 2, 101, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 0, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 89, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 137, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 13, 2, 53, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 163, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 41,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData060_checked :
    roundedProductCertificate 30722 18410017085562 productData060 = some 18440339416710 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData060_length : productData060.length = 512 := by decide

def productData061 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 7, 2, 157, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 67, 2, 13, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 113, 2, 23, 2, 3, 2, 0, 2, 131, 2, 3, 2, 173, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 79, 2, 3, 2, 7, 2, 13, 2, 3, 2, 137, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 89, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 11, 2, 53, 2, 3, 2, 17, 2, 5, 2, 3, 2, 149, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 71, 2, 3, 2, 83,
    2, 163, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 139,
    2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 73, 2, 3, 2, 101, 2, 5, 2, 3,
    2, 7, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 7, 2, 3, 2, 17, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 79, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 41, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData061_checked :
    roundedProductCertificate 31234 18440339416710 productData061 = some 18469061110647 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData061_length : productData061.length = 512 := by decide

def productData062 : List ℕ :=
  [2, 53, 2, 3, 2, 0, 2, 113, 2, 3, 2, 11, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 61, 2, 37, 2, 3, 2, 7, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 13, 2, 29, 2, 3, 2, 0, 2, 47, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 139, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 151, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 127, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 167, 2, 3, 2, 19, 2, 61, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 137, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 11, 2, 3, 2, 109,
    2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 43, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3, 2, 11, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 103,
    2, 5, 2, 3, 2, 7, 2, 179, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3,
    2, 0, 2, 47, 2, 3, 2, 5, 2, 97, 2, 3, 2, 163, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 29,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 53, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 167, 2, 0, 2, 3, 2, 0, 2, 103, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData062_checked :
    roundedProductCertificate 31746 18469061110647 productData062 = some 18495608823667 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData062_length : productData062.length = 512 := by decide

def productData063 : List ℕ :=
  [2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 23, 2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 83, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 139, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 179, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 163, 2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 37,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 47, 2, 0, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 127, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 103, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 89, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 53, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 23, 2, 71, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 29, 2, 137, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 181, 2, 3, 2, 5, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData063_checked :
    roundedProductCertificate 32258 18495608823667 productData063 = some 18525232530353 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData063_length : productData063.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block04.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData064 : List ℕ :=
  [2, 0, 2, 13, 2, 3, 2, 73, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 107, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 59, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 7, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 67,
    2, 167, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 19, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 83, 2, 31, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 137, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 173, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 79, 2, 7, 2, 3, 2, 0, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 157, 2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 0, 2, 13, 2, 3, 2, 17, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 89, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 139, 2, 0, 2, 3, 2, 149, 2, 7, 2, 3, 2, 167, 2, 5, 2, 3, 2, 43, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 41, 2, 11, 2, 3, 2, 7, 2, 79, 2, 3, 2, 29, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 107, 2, 3, 2, 23]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData064_checked :
    roundedProductCertificate 32770 18525232530353 productData064 = some 18553323435807 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData064_length : productData064.length = 512 := by decide

def productData065 : List ℕ :=
  [2, 83, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 61, 2, 3, 2, 13, 2, 23, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 127, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 101, 2, 67, 2, 3, 2, 29, 2, 7, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 0, 2, 3, 2, 19, 2, 139, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 23, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3, 2, 97, 2, 41, 2, 3, 2, 5,
    2, 131, 2, 3, 2, 11, 2, 151, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 67, 2, 0, 2, 3, 2, 37, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 89, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 47]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData065_checked :
    roundedProductCertificate 33282 18553323435807 productData065 = some 18584888003203 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData065_length : productData065.length = 512 := by decide

def productData066 : List ℕ :=
  [2, 3, 2, 0, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 149, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 97, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17, 2, 31, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 107, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 83, 2, 17, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 61, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 41, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 37, 2, 3, 2, 31, 2, 71, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 101, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 79,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 53, 2, 173,
    2, 3, 2, 5, 2, 89, 2, 3, 2, 73, 2, 103, 2, 3, 2, 7, 2, 13, 2, 3, 2, 67, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 5, 2, 109, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 127, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 179, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 97,
    2, 11, 2, 3, 2, 23, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0,
    2, 3, 2, 151, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData066_checked :
    roundedProductCertificate 33794 18584888003203 productData066 = some 18610552426232 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData066_length : productData066.length = 512 := by decide

def productData067 : List ℕ :=
  [2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 163, 2, 3, 2, 11, 2, 41, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 127, 2, 3, 2, 0, 2, 29, 2, 3, 2, 173, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 131, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 179, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 181, 2, 7, 2, 3, 2, 71, 2, 151, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 89, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 0, 2, 59, 2, 3, 2, 19, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 113, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 103, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 23,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 43, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 37]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData067_checked :
    roundedProductCertificate 34306 18610552426232 productData067 = some 18637501214352 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData067_length : productData067.length = 512 := by decide

def productData068 : List ℕ :=
  [2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 29, 2, 61, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 139, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 67, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 53, 2, 3, 2, 13, 2, 181, 2, 3, 2, 7, 2, 0, 2, 3, 2, 83, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 11, 2, 7, 2, 3, 2, 79, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13,
    2, 157, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 53, 2, 5, 2, 3, 2, 37, 2, 67,
    2, 3, 2, 5, 2, 101, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 0, 2, 113, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 29, 2, 127, 2, 3, 2, 151, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 17, 2, 137, 2, 3, 2, 23, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 167, 2, 131, 2, 3, 2, 13, 2, 5, 2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 179, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 47,
    2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData068_checked :
    roundedProductCertificate 34818 18637501214352 productData068 = some 18663022201661 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData068_length : productData068.length = 512 := by decide

def productData069 : List ℕ :=
  [2, 3, 2, 89, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 113, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 41, 2, 3, 2, 11, 2, 43, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 107, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 71, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 59, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 79, 2, 19, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 131, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 73, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 43, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 149, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 179, 2, 7, 2, 3, 2, 23, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 157, 2, 29, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 7, 2, 101, 2, 3, 2, 181, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31,
    2, 17, 2, 3, 2, 127, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 71,
    2, 3, 2, 11, 2, 23, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 103, 2, 31, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 83, 2, 3, 2, 7,
    2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 0,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 7, 2, 113, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData069_checked :
    roundedProductCertificate 35330 18663022201661 productData069 = some 18686114639058 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData069_length : productData069.length = 512 := by decide

def productData070 : List ℕ :=
  [2, 73, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 17, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 149, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 37, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 83, 2, 127, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0, 2, 157, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 181, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 137, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 31, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 151, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 13, 2, 79, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 0, 2, 71, 2, 3, 2, 47, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 59, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 7, 2, 53, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13,
    2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 131, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 17, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 163, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData070_checked :
    roundedProductCertificate 35842 18686114639058 productData070 = some 18712014081120 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData070_length : productData070.length = 512 := by decide

def productData071 : List ℕ :=
  [2, 5, 2, 3, 2, 103, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 151, 2, 3, 2, 5, 2, 17, 2, 3, 2, 89, 2, 59, 2, 3, 2, 7, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 79, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 17, 2, 0, 2, 3, 2, 83, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 191,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 173, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 139, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 157, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 31, 2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 13, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 61, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 109, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 97, 2, 3, 2, 0, 2, 83,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 131, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 137, 2, 3, 2, 0, 2, 29, 2, 3, 2, 191, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData071_checked :
    roundedProductCertificate 36354 18712014081120 productData071 = some 18737576351623 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData071_length : productData071.length = 512 := by decide

def productData072 : List ℕ :=
  [2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 23,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 103, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 47, 2, 71, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 163, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 19, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 101, 2, 19, 2, 3, 2, 131, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 43, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 137, 2, 107, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 97, 2, 53,
    2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 41, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 127, 2, 11, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 31, 2, 3, 2, 5, 2, 23, 2, 3, 2, 167, 2, 0, 2, 3, 2, 7, 2, 193,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 83, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 163, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 107, 2, 5,
    2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData072_checked :
    roundedProductCertificate 36866 18737576351623 productData072 = some 18762837763046 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData072_length : productData072.length = 512 := by decide

def productData073 : List ℕ :=
  [2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 139, 2, 61, 2, 3, 2, 0, 2, 149, 2, 3, 2, 113, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 37, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 53, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19,
    2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 191, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 7, 2, 139, 2, 3, 2, 101, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 31, 2, 29,
    2, 3, 2, 97, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 61, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 179, 2, 107, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 23, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 59, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 157, 2, 3, 2, 79, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData073_checked :
    roundedProductCertificate 37378 18762837763046 productData073 = some 18787288844862 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData073_length : productData073.length = 512 := by decide

def productData074 : List ℕ :=
  [2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 151, 2, 29, 2, 3, 2, 0, 2, 167, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 83, 2, 7, 2, 3, 2, 59, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 137, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 13, 2, 5, 2, 3, 2, 163, 2, 19, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 191, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 193, 2, 47, 2, 3, 2, 11, 2, 17, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 113,
    2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 47, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 7, 2, 3,
    2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 59, 2, 3, 2, 0,
    2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 181, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 167, 2, 5, 2, 3, 2, 23, 2, 29, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 83, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 149, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 89, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 131, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData074_checked :
    roundedProductCertificate 37890 18787288844862 productData074 = some 18809455930603 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData074_length : productData074.length = 512 := by decide

def productData075 : List ℕ :=
  [2, 3, 2, 5, 2, 193, 2, 3, 2, 71, 2, 107, 2, 3, 2, 41, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 17, 2, 79, 2, 3, 2, 109, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 61, 2, 3, 2, 5, 2, 137,
    2, 3, 2, 0, 2, 139, 2, 3, 2, 7, 2, 97, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 53, 2, 11, 2, 3, 2, 89, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 173, 2, 41, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29,
    2, 67, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 101, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 137, 2, 7, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 151, 2, 197, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 0, 2, 3, 2, 71, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 59,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 19, 2, 3, 2, 97, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 167, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData075_checked :
    roundedProductCertificate 38402 18809455930603 productData075 = some 18831841186400 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData075_length : productData075.length = 512 := by decide

def productData076 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 163, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 13, 2, 127, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 43, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 23, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 139, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 89, 2, 41,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 109, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 53, 2, 13,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 197, 2, 5, 2, 3, 2, 0, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 61, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 37, 2, 11, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 107, 2, 173, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 163, 2, 3, 2, 17, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67,
    2, 37, 2, 3, 2, 5, 2, 139, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 157, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData076_checked :
    roundedProductCertificate 38914 18831841186400 productData076 = some 18856857798958 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData076_length : productData076.length = 512 := by decide

def productData077 : List ℕ :=
  [2, 89, 2, 3, 2, 7, 2, 47, 2, 3, 2, 113, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 61, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 17, 2, 73, 2, 3, 2, 127, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 37,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 31, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 199, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 173,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 29, 2, 3, 2, 41, 2, 31,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 97, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 79, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 127, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7,
    2, 41, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 113, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 107, 2, 167, 2, 3, 2, 179, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData077_checked :
    roundedProductCertificate 39426 18856857798958 productData077 = some 18879672082938 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData077_length : productData077.length = 512 := by decide

def productData078 : List ℕ :=
  [2, 3, 2, 11, 2, 59, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 89, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 71, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13,
    2, 109, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 103, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 149, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 101,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 67, 2, 5, 2, 3, 2, 11, 2, 137, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 79, 2, 0, 2, 3, 2, 131, 2, 37, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 167, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 127, 2, 13, 2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 5, 2, 59, 2, 3, 2, 191, 2, 41, 2, 3, 2, 17, 2, 173, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 61,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 53, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 181, 2, 3, 2, 37, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 149, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 31, 2, 3, 2, 7, 2, 71, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData078_checked :
    roundedProductCertificate 39938 18879672082938 productData078 = some 18899417669771 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData078_length : productData078.length = 512 := by decide

def productData079 : List ℕ :=
  [2, 19, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 101, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2, 0, 2, 3,
    2, 13, 2, 23, 2, 3, 2, 107, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 113, 2, 3, 2, 29, 2, 13, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 151, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 179, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 97, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 109, 2, 3, 2, 73, 2, 7, 2, 3, 2, 11, 2, 67, 2, 3, 2, 89,
    2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 43, 2, 193, 2, 3, 2, 139, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 131, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 83, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 97, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 103, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 11, 2, 3, 2, 163, 2, 5, 2, 3, 2, 17, 2, 151, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData079_checked :
    roundedProductCertificate 40450 18899417669771 productData079 = some 18922178487287 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData079_length : productData079.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block05.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData080 : List ℕ :=
  [2, 13, 2, 3, 2, 71, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 107, 2, 3, 2, 5, 2, 17, 2, 3, 2, 179, 2, 0,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 131, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 7, 2, 89, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 181, 2, 17,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 73, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 47, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 157, 2, 7, 2, 3, 2, 61, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3, 2, 101, 2, 109, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 7, 2, 31, 2, 3, 2, 11, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5,
    2, 173, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 83, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29,
    2, 0, 2, 3, 2, 7, 2, 181, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 67]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData080_checked :
    roundedProductCertificate 40962 18922178487287 productData080 = some 18944229086845 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData080_length : productData080.length = 512 := by decide

def productData081 : List ℕ :=
  [2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 47, 2, 7, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 7, 2, 41, 2, 3, 2, 73,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 89, 2, 3, 2, 197, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 107, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 61, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 73, 2, 3, 2, 0, 2, 47, 2, 3, 2, 173, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 179, 2, 3, 2, 53, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 109, 2, 83, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 97, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5,
    2, 151, 2, 3, 2, 59, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 41, 2, 0, 2, 3, 2, 7, 2, 149, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 163, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 167, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData081_checked :
    roundedProductCertificate 41474 18944229086845 productData081 = some 18968755667697 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData081_length : productData081.length = 512 := by decide

def productData082 : List ℕ :=
  [2, 11, 2, 199, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 97, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 127, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 137, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 71, 2, 3, 2, 13, 2, 17, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 113, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 149, 2, 0, 2, 3, 2, 181, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0, 2, 53,
    2, 3, 2, 5, 2, 83, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 43, 2, 41, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 29, 2, 17, 2, 3, 2, 11, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 109,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2, 151, 2, 0,
    2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 107, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData082_checked :
    roundedProductCertificate 41986 18968755667697 productData082 = some 18993457588126 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData082_length : productData082.length = 512 := by decide

def productData083 : List ℕ :=
  [2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 101, 2, 13, 2, 3, 2, 23, 2, 71,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 157, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 37, 2, 0, 2, 3, 2, 191,
    2, 5, 2, 3, 2, 41, 2, 13, 2, 3, 2, 5, 2, 137, 2, 3, 2, 0, 2, 43, 2, 3, 2, 19, 2, 17, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 47, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 29, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71, 2, 139, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 151, 2, 3, 2, 0, 2, 79, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 179, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 127, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 113, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 73, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 163, 2, 43, 2, 3, 2, 5, 2, 53, 2, 3, 2, 137,
    2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 7, 2, 167, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 67, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 41]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData083_checked :
    roundedProductCertificate 42498 18993457588126 productData083 = some 19015234522078 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData083_length : productData083.length = 512 := by decide

def productData084 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37, 2, 23, 2, 3, 2, 0, 2, 193, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 23, 2, 67, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 71, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 179, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 103, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 79, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 139, 2, 17, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 11, 2, 83, 2, 3, 2, 59, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 181, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 109, 2, 3, 2, 13, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 19, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 7, 2, 19, 2, 3, 2, 89, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 191, 2, 3, 2, 131,
    2, 103, 2, 3, 2, 17, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 173, 2, 3,
    2, 0, 2, 137, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 157,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 139, 2, 3, 2, 13, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData084_checked :
    roundedProductCertificate 43010 19015234522078 productData084 = some 19032824949410 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData084_length : productData084.length = 512 := by decide

def productData085 : List ℕ :=
  [2, 71, 2, 5, 2, 3, 2, 19, 2, 101, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 97,
    2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 53, 2, 181, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 47, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 37, 2, 89, 2, 3, 2, 11, 2, 5, 2, 3, 2, 109, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 73, 2, 7, 2, 3, 2, 101, 2, 5, 2, 3, 2, 191, 2, 17, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 67, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 107, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3,
    2, 193, 2, 7, 2, 3, 2, 43, 2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 41, 2, 53, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 163, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 73,
    2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 43, 2, 3,
    2, 23, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 167, 2, 3, 2, 5, 2, 13, 2, 3, 2, 197, 2, 0, 2, 3, 2, 53,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 79, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData085_checked :
    roundedProductCertificate 43522 19032824949410 productData085 = some 19053701153857 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData085_length : productData085.length = 512 := by decide

def productData086 : List ℕ :=
  [2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 139, 2, 5,
    2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 157, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 11, 2, 3, 2, 131, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 163, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 193, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 11, 2, 7, 2, 3, 2, 31, 2, 13, 2, 3, 2, 151, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 73, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23,
    2, 127, 2, 3, 2, 19, 2, 97, 2, 3, 2, 43, 2, 5, 2, 3, 2, 101, 2, 11, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 199, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 89, 2, 23, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 157, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 7, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 173, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 11, 2, 3, 2, 79, 2, 19, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 191, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 211, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData086_checked :
    roundedProductCertificate 44034 19053701153857 productData086 = some 19074364073081 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData086_length : productData086.length = 512 := by decide

def productData087 : List ℕ :=
  [2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 41, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 0, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 19, 2, 3, 2, 7, 2, 103, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 59, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 0, 2, 61, 2, 3, 2, 97, 2, 197, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 101, 2, 3, 2, 29, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 89, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71,
    2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 127, 2, 107,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 113, 2, 7, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17,
    2, 59, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 167, 2, 3, 2, 0, 2, 179,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 193, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 73, 2, 31, 2, 3, 2, 107, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData087_checked :
    roundedProductCertificate 44546 19074364073081 productData087 = some 19094389401924 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData087_length : productData087.length = 512 := by decide

def productData088 : List ℕ :=
  [2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 67, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 23, 2, 3, 2, 43, 2, 79, 2, 3, 2, 197, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 163, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 31, 2, 17, 2, 3, 2, 199, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 73, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 53, 2, 29, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 11, 2, 41, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 37, 2, 13, 2, 3, 2, 167, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 97, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 113,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 137, 2, 101, 2, 3, 2, 7, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 17, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 83, 2, 0, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 181, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 131, 2, 3, 2, 13, 2, 11, 2, 3, 2, 19, 2, 41, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 173, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 17, 2, 71, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData088_checked :
    roundedProductCertificate 45058 19094389401924 productData088 = some 19113782116341 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData088_length : productData088.length = 512 := by decide

def productData089 : List ℕ :=
  [2, 199, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 79, 2, 3, 2, 0, 2, 0, 2, 3, 2, 127, 2, 5, 2, 3, 2, 0, 2, 31,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 103, 2, 0, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 191, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 109, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 17, 2, 5, 2, 3, 2, 131, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 0, 2, 53, 2, 3, 2, 149, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67,
    2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 11,
    2, 3, 2, 41, 2, 13, 2, 3, 2, 163, 2, 5, 2, 3, 2, 19, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 109,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 197, 2, 3, 2, 5, 2, 29, 2, 3, 2, 31, 2, 7, 2, 3, 2, 17, 2, 47, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 31, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 157, 2, 179, 2, 3, 2, 13, 2, 139, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 191, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 73, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData089_checked :
    roundedProductCertificate 45570 19113782116341 productData089 = some 19131727629670 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData089_length : productData089.length = 512 := by decide

def productData090 : List ℕ :=
  [2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 107, 2, 3, 2, 17, 2, 7, 2, 3, 2, 193, 2, 163, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 101, 2, 31, 2, 3, 2, 13, 2, 5, 2, 3, 2, 137, 2, 0, 2, 3, 2, 5, 2, 61,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 37, 2, 3, 2, 113, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13,
    2, 131, 2, 3, 2, 103, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 167, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 7, 2, 3, 2, 0,
    2, 149, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 151, 2, 3, 2, 7, 2, 71, 2, 3, 2, 199, 2, 89,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 13, 2, 3, 2, 17, 2, 29, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 97, 2, 5,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 193, 2, 3, 2, 181, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 5, 2, 173, 2, 3, 2, 11, 2, 7, 2, 3, 2, 89, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 101,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 47, 2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData090_checked :
    roundedProductCertificate 46082 19131727629670 productData090 = some 19151555915102 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData090_length : productData090.length = 512 := by decide

def productData091 : List ℕ :=
  [2, 5, 2, 17, 2, 3, 2, 0, 2, 29, 2, 3, 2, 11, 2, 127, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 53, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 0, 2, 83, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 101, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 13, 2, 71, 2, 3, 2, 73, 2, 5, 2, 3, 2, 53, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 139, 2, 3, 2, 79, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 173, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 61, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 167, 2, 3, 2, 71, 2, 0, 2, 3, 2, 11, 2, 73, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 151, 2, 7, 2, 3, 2, 67, 2, 13, 2, 3, 2, 107, 2, 5, 2, 3,
    2, 109, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29,
    2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 59, 2, 3, 2, 31, 2, 131, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 211, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 103, 2, 3,
    2, 5, 2, 179, 2, 3, 2, 23, 2, 197, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData091_checked :
    roundedProductCertificate 46594 19151555915102 productData091 = some 19169151256671 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData091_length : productData091.length = 512 := by decide

def productData092 : List ℕ :=
  [2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 109, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 73, 2, 149,
    2, 3, 2, 0, 2, 97, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 167, 2, 151, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 37, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 127, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 83,
    2, 5, 2, 3, 2, 11, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 5,
    2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 29, 2, 3, 2, 197, 2, 79, 2, 3, 2, 103, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 199, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 113, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 181, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData092_checked :
    roundedProductCertificate 47106 19169151256671 productData092 = some 19189400408917 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData092_length : productData092.length = 512 := by decide

def productData093 : List ℕ :=
  [2, 3, 2, 7, 2, 0, 2, 3, 2, 97, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 41, 2, 3, 2, 43, 2, 103, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 163, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 137, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 59, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 151, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 83, 2, 47, 2, 3, 2, 211, 2, 19, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 173, 2, 17, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 191, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 7, 2, 199, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 47, 2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 107, 2, 3, 2, 23, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 53, 2, 0, 2, 3, 2, 131, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 103, 2, 11, 2, 3, 2, 73, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData093_checked :
    roundedProductCertificate 47618 19189400408917 productData093 = some 19208656065216 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData093_length : productData093.length = 512 := by decide

def productData094 : List ℕ :=
  [2, 0, 2, 127, 2, 3, 2, 37, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 89, 2, 179, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 157, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 29, 2, 17, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 73, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 53, 2, 3, 2, 109, 2, 43,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 211, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 37, 2, 137, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 101, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 97, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 5, 2, 79, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 193, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 179, 2, 139, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 47, 2, 23, 2, 3, 2, 59, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 173, 2, 3, 2, 61, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 127]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData094_checked :
    roundedProductCertificate 48130 19208656065216 productData094 = some 19226923321694 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData094_length : productData094.length = 512 := by decide

def productData095 : List ℕ :=
  [2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 181, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 113, 2, 3,
    2, 53, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 79, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 157, 2, 11, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 131, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 107, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 41, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113,
    2, 167, 2, 3, 2, 5, 2, 7, 2, 3, 2, 109, 2, 17, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 173, 2, 11,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 181, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 71, 2, 7, 2, 3, 2, 139, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 191, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 29, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 13, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData095_checked :
    roundedProductCertificate 48642 19226923321694 productData095 = some 19246201758300 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData095_length : productData095.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block06.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData096 : List ℕ :=
  [2, 3, 2, 0, 2, 11, 2, 3, 2, 211, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 137, 2, 3,
    2, 101, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7,
    2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 41, 2, 23, 2, 3, 2, 11, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 149, 2, 31, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 103, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 61, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 7, 2, 3, 2, 127, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 197, 2, 3, 2, 0, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 61, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 7, 2, 67, 2, 3, 2, 13, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 107, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 19, 2, 89, 2, 3, 2, 11, 2, 43, 2, 3, 2, 179, 2, 5, 2, 3, 2, 17, 2, 101, 2, 3, 2, 5, 2, 0, 2, 3, 2, 193,
    2, 0, 2, 3, 2, 113, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 131, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 53, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData096_checked :
    roundedProductCertificate 49154 19246201758300 productData096 = some 19265302375415 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData096_length : productData096.length = 512 := by decide

def productData097 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 223,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 157, 2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 79, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 73, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 31, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 139, 2, 7, 2, 3, 2, 11, 2, 29, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 199, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 47, 2, 17, 2, 3, 2, 29, 2, 107, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 151, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 43, 2, 13, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 163, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 113, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61,
    2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 89, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 181, 2, 3, 2, 7, 2, 41, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 103, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 131, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData097_checked :
    roundedProductCertificate 49666 19265302375415 productData097 = some 19285763146321 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData097_length : productData097.length = 512 := by decide

def productData098 : List ℕ :=
  [2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 61, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 149, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 191, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 109, 2, 31, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 137, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 179, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 71, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 43, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 101, 2, 13,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 127, 2, 3, 2, 0, 2, 5, 2, 3, 2, 211, 2, 29, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 0, 2, 73, 2, 3, 2, 61, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 109, 2, 3, 2, 41, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 97, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7,
    2, 59, 2, 3, 2, 11, 2, 61, 2, 3, 2, 103, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 223, 2, 23, 2, 3,
    2, 0, 2, 197, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 179,
    2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 173]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData098_checked :
    roundedProductCertificate 50178 19285763146321 productData098 = some 19302212209542 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData098_length : productData098.length = 512 := by decide

def productData099 : List ℕ :=
  [2, 3, 2, 163, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 41, 2, 67, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 19, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 193, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 79, 2, 3, 2, 37, 2, 101, 2, 3, 2, 23, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 89, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 211, 2, 3, 2, 5, 2, 0, 2, 3, 2, 181, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 17,
    2, 3, 2, 5, 2, 151, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 13, 2, 0, 2, 3, 2, 127, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 131, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 29, 2, 139, 2, 3, 2, 17, 2, 163, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43,
    2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 223, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 137, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 199, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 73, 2, 5, 2, 3, 2, 61, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData099_checked :
    roundedProductCertificate 50690 19302212209542 productData099 = some 19318506913125 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData099_length : productData099.length = 512 := by decide

def productData100 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 41, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 181, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 107, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 167, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 43, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 23, 2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 47, 2, 7, 2, 3, 2, 83, 2, 191, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 5, 2, 103, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 53, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 67, 2, 3, 2, 7, 2, 227, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 31,
    2, 3, 2, 11, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 79, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 71,
    2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 43, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 163, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 149, 2, 3, 2, 29, 2, 7, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData100_checked :
    roundedProductCertificate 51202 19318506913125 productData100 = some 19338413334628 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData100_length : productData100.length = 512 := by decide

def productData101 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 191, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 7, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103,
    2, 197, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 47,
    2, 3, 2, 5, 2, 139, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 29, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 193, 2, 7, 2, 3, 2, 137, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 167,
    2, 3, 2, 0, 2, 127, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 223, 2, 7, 2, 3, 2, 5, 2, 157, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 227, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 149,
    2, 7, 2, 3, 2, 131, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 61,
    2, 3, 2, 17, 2, 13, 2, 3, 2, 71, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 113, 2, 3, 2, 59,
    2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 107, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 43, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 109, 2, 7, 2, 3, 2, 11, 2, 79, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData101_checked :
    roundedProductCertificate 51714 19338413334628 productData101 = some 19355910744321 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData101_length : productData101.length = 512 := by decide

def productData102 : List ℕ :=
  [2, 3, 2, 29, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 89, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 167, 2, 13, 2, 3, 2, 61, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 193, 2, 3, 2, 19, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 59, 2, 3, 2, 199, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 151, 2, 61, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 103, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 229, 2, 3, 2, 5, 2, 179, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 71, 2, 137, 2, 3, 2, 5, 2, 97, 2, 3, 2, 11,
    2, 31, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 131, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 149, 2, 3, 2, 23, 2, 41, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 61, 2, 5, 2, 3, 2, 17, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 139, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 151, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData102_checked :
    roundedProductCertificate 52226 19355910744321 productData102 = some 19372510676008 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData102_length : productData102.length = 512 := by decide

def productData103 : List ℕ :=
  [2, 23, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 71, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0,
    2, 113, 2, 3, 2, 5, 2, 89, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 101, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 43, 2, 41, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 7, 2, 37, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 227, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 191, 2, 157, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 41, 2, 43, 2, 3, 2, 0, 2, 167, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 211,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 197,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 17, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 181, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17,
    2, 97, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 109, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 173, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 83, 2, 3, 2, 7, 2, 13, 2, 3, 2, 127, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 139, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData103_checked :
    roundedProductCertificate 52738 19372510676008 productData103 = some 19390062202188 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData103_length : productData103.length = 512 := by decide

def productData104 : List ℕ :=
  [2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 137, 2, 3, 2, 223, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 71, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 41, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 229, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 83, 2, 19, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 197, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 193, 2, 3, 2, 5, 2, 127, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 53, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 89, 2, 149, 2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 73, 2, 3, 2, 59, 2, 5, 2, 3, 2, 109, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 199, 2, 17, 2, 3, 2, 11,
    2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 131, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 103, 2, 5,
    2, 3, 2, 7, 2, 191, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 83, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 61, 2, 223, 2, 3, 2, 71, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData104_checked :
    roundedProductCertificate 53250 19390062202188 productData104 = some 19406375828479 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData104_length : productData104.length = 512 := by decide

def productData105 : List ℕ :=
  [2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 11, 2, 173, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 107, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 61, 2, 3, 2, 11, 2, 103, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 199, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 163,
    2, 3, 2, 79, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 37, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 97, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 191, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 139, 2, 23, 2, 3, 2, 17, 2, 41, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 61, 2, 11, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 113, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 173, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 0, 2, 3, 2, 11, 2, 83, 2, 3, 2, 67, 2, 5, 2, 3, 2, 151,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 13, 2, 3, 2, 211, 2, 7, 2, 3, 2, 193, 2, 5, 2, 3, 2, 73, 2, 11,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 227, 2, 3, 2, 7, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData105_checked :
    roundedProductCertificate 53762 19406375828479 productData105 = some 19421837887264 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData105_length : productData105.length = 512 := by decide

def productData106 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 17, 2, 19, 2, 3, 2, 0, 2, 233, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 137, 2, 109, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 13, 2, 29,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 107, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 157, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 31,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 89, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 197, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 79, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 97, 2, 13, 2, 3, 2, 0, 2, 193, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 101, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 11, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 83, 2, 3, 2, 19, 2, 11, 2, 3, 2, 227, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 229, 2, 7, 2, 3, 2, 127, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData106_checked :
    roundedProductCertificate 54274 19421837887264 productData106 = some 19440728421811 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData106_length : productData106.length = 512 := by decide

def productData107 : List ℕ :=
  [2, 0, 2, 3, 2, 11, 2, 157, 2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 59, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 73, 2, 3, 2, 109, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 173, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 71, 2, 3, 2, 7, 2, 131, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 89,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 163, 2, 3, 2, 5, 2, 137, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 179, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 127, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 13, 2, 3, 2, 67, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 113, 2, 11, 2, 3, 2, 47, 2, 23, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 53, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 31, 2, 3, 2, 89, 2, 37, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 199, 2, 3, 2, 0, 2, 29, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43,
    2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 139, 2, 3, 2, 11, 2, 229, 2, 3, 2, 97, 2, 5, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3, 2, 101, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 19, 2, 31, 2, 3, 2, 167, 2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData107_checked :
    roundedProductCertificate 54786 19440728421811 productData107 = some 19455921385752 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData107_length : productData107.length = 512 := by decide

def productData108 : List ℕ :=
  [2, 3, 2, 17, 2, 29, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 197, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 151, 2, 3, 2, 157, 2, 19, 2, 3,
    2, 43, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 109, 2, 113, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 211, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 59, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 13, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 181, 2, 3, 2, 61, 2, 7, 2, 3, 2, 149, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 179, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 5, 2, 233, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 103, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 139, 2, 7, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 197, 2, 127, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData108_checked :
    roundedProductCertificate 55298 19455921385752 productData108 = some 19472035522131 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData108_length : productData108.length = 512 := by decide

def productData109 : List ℕ :=
  [2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 59,
    2, 3, 2, 71, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 199, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 107, 2, 191, 2, 3, 2, 0, 2, 97,
    2, 3, 2, 223, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 179, 2, 43, 2, 3, 2, 137,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 23, 2, 0, 2, 3, 2, 29, 2, 61, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37,
    2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 31, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 233, 2, 5, 2, 3, 2, 89, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5,
    2, 59, 2, 3, 2, 7, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 101,
    2, 3, 2, 127, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 167, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 181, 2, 41, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 199, 2, 3, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData109_checked :
    roundedProductCertificate 55810 19472035522131 productData109 = some 19489068314758 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData109_length : productData109.length = 512 := by decide

def productData110 : List ℕ :=
  [2, 151, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 103, 2, 3, 2, 5, 2, 29, 2, 3, 2, 37, 2, 11,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 113, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 47, 2, 19,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 193, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 163, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 181, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 13, 2, 3, 2, 131, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 23, 2, 179, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 211, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 79,
    2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData110_checked :
    roundedProductCertificate 56322 19489068314758 productData110 = some 19506986500835 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData110_length : productData110.length = 512 := by decide

def productData111 : List ℕ :=
  [2, 3, 2, 11, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 139, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 101, 2, 3,
    2, 19, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 163, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2, 227, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 47, 2, 11, 2, 3, 2, 23, 2, 19, 2, 3, 2, 127, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 89, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 0, 2, 43, 2, 3, 2, 5, 2, 149, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 239,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 211, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 89, 2, 151, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 173, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 223, 2, 37,
    2, 3, 2, 13, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData111_checked :
    roundedProductCertificate 56834 19506986500835 productData111 = some 19524422395104 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData111_length : productData111.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block07.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData112 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 41, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 103, 2, 0, 2, 3, 2, 181,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 137, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 79, 2, 3, 2, 19, 2, 71, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 101, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 229, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 131, 2, 17, 2, 3, 2, 5, 2, 113, 2, 3, 2, 97, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 163, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 71, 2, 89, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 239, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 17, 2, 3, 2, 7, 2, 157, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 101, 2, 7, 2, 3, 2, 137, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 197, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11,
    2, 47, 2, 3, 2, 61, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 67, 2, 53, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 47]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData112_checked :
    roundedProductCertificate 57346 19524422395104 productData112 = some 19540694605020 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData112_length : productData112.length = 512 := by decide

def productData113 : List ℕ :=
  [2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 107, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 53, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 167, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 11, 2, 149, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 103, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 31, 2, 11, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 131, 2, 3, 2, 7, 2, 127, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 241,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 89, 2, 3, 2, 7, 2, 13, 2, 3, 2, 37, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 47, 2, 53, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 73, 2, 83, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 139,
    2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 101, 2, 13, 2, 3, 2, 167, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 97, 2, 3, 2, 173, 2, 7, 2, 3,
    2, 199, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0,
    2, 227, 2, 3, 2, 41, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData113_checked :
    roundedProductCertificate 57858 19540694605020 productData113 = some 19556503018750 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData113_length : productData113.length = 512 := by decide

def productData114 : List ℕ :=
  [2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 211, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 233, 2, 3, 2, 11, 2, 23, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 163, 2, 139, 2, 3, 2, 43, 2, 5, 2, 3, 2, 107,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 127, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 157,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 103, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 0, 2, 17, 2, 3, 2, 191, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 223, 2, 89, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 79, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 151, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 41,
    2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 43, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 127, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 103, 2, 3, 2, 11,
    2, 131, 2, 3, 2, 59, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 29, 2, 19, 2, 3, 2, 83, 2, 7,
    2, 3, 2, 229, 2, 5, 2, 3, 2, 71, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 17, 2, 113, 2, 3, 2, 7, 2, 97, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData114_checked :
    roundedProductCertificate 58370 19556503018750 productData114 = some 19569859439882 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData114_length : productData114.length = 512 := by decide

def productData115 : List ℕ :=
  [2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 167, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 43, 2, 17,
    2, 3, 2, 5, 2, 137, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 17, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53,
    2, 73, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 0,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 179, 2, 193, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 211, 2, 13, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 31, 2, 5, 2, 3, 2, 127, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 137, 2, 11, 2, 3, 2, 41, 2, 79,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 43, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData115_checked :
    roundedProductCertificate 58882 19569859439882 productData115 = some 19588073072996 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData115_length : productData115.length = 512 := by decide

def productData116 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 191, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 67, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 37, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19,
    2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 157, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 59, 2, 37, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 71, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 61, 2, 107, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 109, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 37,
    2, 13, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 227, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 211,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 0, 2, 149, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 191, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 79, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 41, 2, 163, 2, 3, 2, 5, 2, 29, 2, 3, 2, 19, 2, 0, 2, 3, 2, 53, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 97, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 131, 2, 19, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 233, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 101, 2, 3, 2, 89, 2, 7, 2, 3, 2, 37, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData116_checked :
    roundedProductCertificate 59394 19588073072996 productData116 = some 19603190910659 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData116_length : productData116.length = 512 := by decide

def productData117 : List ℕ :=
  [2, 3, 2, 139, 2, 181, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 151, 2, 3, 2, 0, 2, 167, 2, 3, 2, 0, 2, 17, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 223, 2, 239, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 29,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 193, 2, 5, 2, 3, 2, 0, 2, 173, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 97, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 79, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 157, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 137, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 139, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 17, 2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 229, 2, 13, 2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 107, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 89, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 23, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 47, 2, 3, 2, 5, 2, 13, 2, 3, 2, 41, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 179, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 73, 2, 0, 2, 3, 2, 173, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 29, 2, 193, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData117_checked :
    roundedProductCertificate 59906 19603190910659 productData117 = some 19617533694999 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData117_length : productData117.length = 512 := by decide

def productData118 : List ℕ :=
  [2, 31, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 223, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 103, 2, 13, 2, 3, 2, 11, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 197, 2, 31,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 241, 2, 0, 2, 3, 2, 0, 2, 101, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 73, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5,
    2, 191, 2, 3, 2, 151, 2, 19, 2, 3, 2, 7, 2, 23, 2, 3, 2, 71, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 29, 2, 47, 2, 3, 2, 43, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 131, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3, 2, 5, 2, 7, 2, 3, 2, 101, 2, 0, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 67,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 89, 2, 3, 2, 31, 2, 0, 2, 3, 2, 11, 2, 163, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 59, 2, 3, 2, 127,
    2, 5, 2, 3, 2, 83, 2, 11, 2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 13, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData118_checked :
    roundedProductCertificate 60418 19617533694999 productData118 = some 19632731161809 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData118_length : productData118.length = 512 := by decide

def productData119 : List ℕ :=
  [2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 149, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 19, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3,
    2, 5, 2, 181, 2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 139, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 227, 2, 3, 2, 79, 2, 173, 2, 3, 2, 157, 2, 5, 2, 3, 2, 103, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 199, 2, 3, 2, 107, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 113, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 131, 2, 3, 2, 193, 2, 17, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 97, 2, 3, 2, 0, 2, 41, 2, 3, 2, 13,
    2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 47, 2, 7, 2, 3, 2, 73, 2, 23,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 197, 2, 3, 2, 7, 2, 71, 2, 3, 2, 29, 2, 233, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 167, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 11, 2, 3, 2, 101, 2, 37, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 31, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 109, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 29, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 239, 2, 3, 2, 19, 2, 47, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData119_checked :
    roundedProductCertificate 60930 19632731161809 productData119 = some 19645247375029 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData119_length : productData119.length = 512 := by decide

def productData120 : List ℕ :=
  [2, 3, 2, 5, 2, 43, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 137, 2, 3, 2, 227, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 37, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 23, 2, 67, 2, 3, 2, 139, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 229,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 197, 2, 7, 2, 3,
    2, 0, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 103,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 107, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 151, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 19, 2, 223, 2, 3, 2, 5, 2, 163, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 7, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 29, 2, 23, 2, 3, 2, 5, 2, 19, 2, 3, 2, 113, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 211, 2, 5,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 127, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 199,
    2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 103, 2, 3, 2, 31, 2, 0, 2, 3, 2, 101, 2, 5, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 241, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData120_checked :
    roundedProductCertificate 61442 19645247375029 productData120 = some 19659905969248 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData120_length : productData120.length = 512 := by decide

def productData121 : List ℕ :=
  [2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 31, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 109, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 0, 2, 229, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 47, 2, 29, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 173, 2, 3, 2, 7, 2, 179,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 29, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 79, 2, 3, 2, 97,
    2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 109, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 19, 2, 3, 2, 71, 2, 73, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 61, 2, 3, 2, 5, 2, 199, 2, 3, 2, 167, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 157, 2, 3, 2, 83, 2, 5, 2, 3,
    2, 17, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 127, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47,
    2, 97, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 89, 2, 3, 2, 43, 2, 5, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 139, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 163, 2, 149, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 17, 2, 41, 2, 3, 2, 7, 2, 197, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData121_checked :
    roundedProductCertificate 61954 19659905969248 productData121 = some 19673824091578 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData121_length : productData121.length = 512 := by decide

def productData122 : List ℕ :=
  [2, 0, 2, 3, 2, 179, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 101, 2, 103, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 11, 2, 3, 2, 73,
    2, 0, 2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 53,
    2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 137, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 223, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 233, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 11, 2, 7, 2, 3, 2, 59, 2, 19, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 149, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 131, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 0, 2, 3, 2, 11, 2, 67, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 181, 2, 107, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 19, 2, 3, 2, 31, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 239, 2, 3, 2, 0, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 227, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 61, 2, 109, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 113, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 157, 2, 13, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 71]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData122_checked :
    roundedProductCertificate 62466 19673824091578 productData122 = some 19688261874243 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData122_length : productData122.length = 512 := by decide

def productData123 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 251, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 61, 2, 3, 2, 29, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 67, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 199, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 89, 2, 0, 2, 3,
    2, 11, 2, 223, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19,
    2, 103, 2, 3, 2, 233, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 83, 2, 3, 2, 13, 2, 181,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 179, 2, 3, 2, 29, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 191, 2, 17, 2, 3, 2, 23, 2, 53, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 43, 2, 3, 2, 17, 2, 7, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 151, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 167, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 127, 2, 3, 2, 0, 2, 61, 2, 3, 2, 241, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 163, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 137, 2, 229, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 107, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData123_checked :
    roundedProductCertificate 62978 19688261874243 productData123 = some 19702897572266 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData123_length : productData123.length = 512 := by decide

def productData124 : List ℕ :=
  [2, 173, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0,
    2, 139, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 103, 2, 7,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0,
    2, 113, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 31, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 37, 2, 7, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 101, 2, 17, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 5, 2, 227, 2, 3, 2, 7, 2, 0, 2, 3, 2, 131, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 0, 2, 3, 2, 83, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 127, 2, 193, 2, 3, 2, 29, 2, 7, 2, 3, 2, 181, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 79, 2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 43, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 167, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 0, 2, 137, 2, 3, 2, 109, 2, 5, 2, 3, 2, 61, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData124_checked :
    roundedProductCertificate 63490 19702897572266 productData124 = some 19718364522982 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData124_length : productData124.length = 512 := by decide

def productData125 : List ℕ :=
  [2, 29, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3,
    2, 0, 2, 79, 2, 3, 2, 17, 2, 5, 2, 3, 2, 139, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 107, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 97, 2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 83, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 43, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 157, 2, 3, 2, 0, 2, 149, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 227, 2, 17, 2, 3, 2, 41, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 179, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53,
    2, 239, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 107, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 131,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 229, 2, 7, 2, 3,
    2, 5, 2, 139, 2, 3, 2, 11, 2, 13, 2, 3, 2, 191, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 19, 2, 7, 2, 3, 2, 71, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 41, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 43, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 251, 2, 3, 2, 31, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData125_checked :
    roundedProductCertificate 64002 19718364522982 productData125 = some 19730951437293 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData125_length : productData125.length = 512 := by decide

def productData126 : List ℕ :=
  [2, 3, 2, 149, 2, 7, 2, 3, 2, 113, 2, 5, 2, 3, 2, 173, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 233, 2, 19, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 31, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 109, 2, 37, 2, 3,
    2, 127, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 31, 2, 23, 2, 3, 2, 89, 2, 5,
    2, 3, 2, 0, 2, 163, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 59, 2, 3, 2, 13, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 41, 2, 101, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 13, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 239,
    2, 7, 2, 3, 2, 5, 2, 211, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 229, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 5, 2, 3, 2, 241, 2, 13, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 7, 2, 61, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 37, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 41, 2, 3, 2, 47, 2, 13, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 101, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13,
    2, 167, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 181, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 103,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 11, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData126_checked :
    roundedProductCertificate 64514 19730951437293 productData126 = some 19743445225376 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData126_length : productData126.length = 512 := by decide

def productData127 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 193, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 67,
    2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 151, 2, 37, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 113, 2, 0, 2, 3, 2, 197, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 7, 2, 3, 2, 89, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 71,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 29, 2, 97,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 109, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 241, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 79, 2, 5, 2, 3, 2, 223, 2, 19, 2, 3, 2, 5,
    2, 101, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 163, 2, 5, 2, 3, 2, 131, 2, 0, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 151, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 149, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 67, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 233,
    2, 3, 2, 41, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 43, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 31, 2, 3,
    2, 13, 2, 109, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData127_checked :
    roundedProductCertificate 65026 19743445225376 productData127 = some 19757971897093 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData127_length : productData127.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block08.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData128 : List ℕ :=
  [2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 0, 2, 3, 2, 173, 2, 7,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 211, 2, 137, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 97, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 13, 2, 3, 2, 179, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 29, 2, 3, 2, 11, 2, 37, 2, 3, 2, 47, 2, 5, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 89, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 29, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 67, 2, 7, 2, 3, 2, 0, 2, 199, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 7, 2, 131, 2, 3, 2, 13, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 233, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 101,
    2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 37, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 13, 2, 3, 2, 5, 2, 149, 2, 3, 2, 11, 2, 251, 2, 3, 2, 7,
    2, 107, 2, 3, 2, 103, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 211, 2, 3, 2, 0, 2, 257]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData128_checked :
    roundedProductCertificate 65538 19757971897093 productData128 = some 19773598907900 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData128_length : productData128.length = 512 := by decide

def productData129 : List ℕ :=
  [2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 157, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 89, 2, 3, 2, 13, 2, 41, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 29, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 109, 2, 3, 2, 127, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 37, 2, 3, 2, 53, 2, 7, 2, 3, 2, 239, 2, 5, 2, 3, 2, 11,
    2, 73, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 103, 2, 3, 2, 107, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 97, 2, 11, 2, 3, 2, 59, 2, 173, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 191, 2, 3, 2, 79, 2, 7, 2, 3, 2, 13, 2, 151, 2, 3, 2, 0, 2, 5, 2, 3, 2, 167, 2, 0, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 19, 2, 113, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 197, 2, 13, 2, 3, 2, 5, 2, 67, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 127, 2, 3, 2, 5, 2, 181, 2, 3, 2, 0, 2, 31,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 0, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29,
    2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 227, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 71, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 61, 2, 0, 2, 3, 2, 19, 2, 101, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData129_checked :
    roundedProductCertificate 66050 19773598907900 productData129 = some 19785827243546 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData129_length : productData129.length = 512 := by decide

def productData130 : List ℕ :=
  [2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 139, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 59, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 37, 2, 3, 2, 103, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 191, 2, 7, 2, 3, 2, 5, 2, 163, 2, 3, 2, 11, 2, 61, 2, 3, 2, 13, 2, 131, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 137, 2, 0,
    2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 241, 2, 3, 2, 101, 2, 0, 2, 3, 2, 179, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 109,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 17, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47,
    2, 0, 2, 3, 2, 211, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 7, 2, 149, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 61, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 167, 2, 3, 2, 193, 2, 0, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 37, 2, 113,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 17, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 199, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData130_checked :
    roundedProductCertificate 66562 19785827243546 productData130 = some 19799747943752 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData130_length : productData130.length = 512 := by decide

def productData131 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 23, 2, 13, 2, 3, 2, 229, 2, 17, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 239, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 109, 2, 5, 2, 3, 2, 103, 2, 0, 2, 3, 2, 5,
    2, 137, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 173,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 193, 2, 3, 2, 7,
    2, 31, 2, 3, 2, 23, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5, 2, 79, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 191, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 181, 2, 3, 2, 107, 2, 251, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData131_checked :
    roundedProductCertificate 67074 19799747943752 productData131 = some 19814748564644 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData131_length : productData131.length = 512 := by decide

def productData132 : List ℕ :=
  [2, 3, 2, 0, 2, 257, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 239, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 61,
    2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 71, 2, 3, 2, 157, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 53,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 13, 2, 139, 2, 3, 2, 7, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 241, 2, 0, 2, 3, 2, 11, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 151, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 19, 2, 17, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 179,
    2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 13,
    2, 3, 2, 103, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 7, 2, 59, 2, 3, 2, 113, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 97, 2, 53, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 47, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 251, 2, 0, 2, 3, 2, 59, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 103, 2, 3, 2, 0, 2, 7, 2, 3, 2, 149, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData132_checked :
    roundedProductCertificate 67586 19814748564644 productData132 = some 19828188699853 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData132_length : productData132.length = 512 := by decide

def productData133 : List ℕ :=
  [2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 193,
    2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 83, 2, 3, 2, 0, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 79, 2, 29, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 7, 2, 241, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 31, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 139, 2, 131, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 19, 2, 233, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 47, 2, 31, 2, 3, 2, 163, 2, 7, 2, 3, 2, 167, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 29,
    2, 3, 2, 17, 2, 197, 2, 3, 2, 137, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 37, 2, 3, 2, 31,
    2, 13, 2, 3, 2, 53, 2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 89, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 223, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 131,
    2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 179, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 191, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 113, 2, 7, 2, 3, 2, 0, 2, 181, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData133_checked :
    roundedProductCertificate 68098 19828188699853 productData133 = some 19839794861677 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData133_length : productData133.length = 512 := by decide

def productData134 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 163, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 83,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 13, 2, 3, 2, 71, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 173, 2, 0, 2, 3, 2, 0, 2, 149, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5,
    2, 127, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 53, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 197, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 97, 2, 3, 2, 0, 2, 109, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 89, 2, 3, 2, 107,
    2, 7, 2, 3, 2, 83, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 19, 2, 23, 2, 3, 2, 43, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 37, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 17, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 157, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 53, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 101, 2, 3, 2, 149, 2, 19, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 151, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 29, 2, 3, 2, 199, 2, 5, 2, 3,
    2, 53, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 67, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 19, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData134_checked :
    roundedProductCertificate 68610 19839794861677 productData134 = some 19852477207689 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData134_length : productData134.length = 512 := by decide

def productData135 : List ℕ :=
  [2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 257, 2, 3, 2, 47, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 263, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 107, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 29,
    2, 79, 2, 3, 2, 193, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 103, 2, 3, 2, 181, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 223, 2, 5, 2, 3, 2, 43, 2, 139, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 173, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 31,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 37, 2, 199, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 127, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 37, 2, 3, 2, 251, 2, 23, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 0, 2, 197, 2, 3, 2, 5, 2, 17, 2, 3, 2, 157, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 73,
    2, 29, 2, 3, 2, 5, 2, 41, 2, 3, 2, 17, 2, 149, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 7,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 151, 2, 67, 2, 3, 2, 43, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 179, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData135_checked :
    roundedProductCertificate 69122 19852477207689 productData135 = some 19864503698964 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData135_length : productData135.length = 512 := by decide

def productData136 : List ℕ :=
  [2, 5, 2, 83, 2, 3, 2, 11, 2, 7, 2, 3, 2, 257, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 59, 2, 3, 2, 17, 2, 5, 2, 3, 2, 227, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 47, 2, 43, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 113, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 103, 2, 137, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 79, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 19, 2, 3, 2, 101, 2, 71,
    2, 3, 2, 7, 2, 223, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 211, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 109, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 47,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 151, 2, 3, 2, 139, 2, 29, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 113, 2, 11, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 167, 2, 3, 2, 19, 2, 7, 2, 3, 2, 47, 2, 5,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 239, 2, 3, 2, 13, 2, 59, 2, 3, 2, 11, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 41, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 109, 2, 3, 2, 7, 2, 29, 2, 3, 2, 191, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData136_checked :
    roundedProductCertificate 69634 19864503698964 productData136 = some 19877294519271 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData136_length : productData136.length = 512 := by decide

def productData137 : List ℕ :=
  [2, 7, 2, 3, 2, 29, 2, 31, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 61, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 199, 2, 0, 2, 3, 2, 163, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 31, 2, 11, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 229, 2, 3,
    2, 167, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 61, 2, 3, 2, 37,
    2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 103, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2, 17, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 43, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 181, 2, 11, 2, 3, 2, 5, 2, 67, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 157, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 107, 2, 3, 2, 151, 2, 97, 2, 3, 2, 109, 2, 5, 2, 3, 2, 0,
    2, 251, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 41,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 163, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3,
    2, 5, 2, 227, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 241, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData137_checked :
    roundedProductCertificate 70146 19877294519271 productData137 = some 19891135048902 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData137_length : productData137.length = 512 := by decide

def productData138 : List ℕ :=
  [2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 223, 2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 197, 2, 3, 2, 107, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 127, 2, 11, 2, 3, 2, 5, 2, 263, 2, 3, 2, 139, 2, 0,
    2, 3, 2, 173, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3,
    2, 71, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 101, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 19, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 193, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 23, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 89, 2, 3, 2, 0, 2, 11, 2, 3, 2, 61, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 251, 2, 5, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 227, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3, 2, 179, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 0, 2, 31, 2, 3, 2, 67, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 97, 2, 3, 2, 5,
    2, 211, 2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData138_checked :
    roundedProductCertificate 70658 19891135048902 productData138 = some 19904319781706 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData138_length : productData138.length = 512 := by decide

def productData139 : List ℕ :=
  [2, 0, 2, 103, 2, 3, 2, 109, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 257, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 31, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 229, 2, 67, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 191, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 263, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 83,
    2, 37, 2, 3, 2, 113, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 23, 2, 149, 2, 3, 2, 5, 2, 137, 2, 3, 2, 41, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 199, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 19, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 127, 2, 0, 2, 3, 2, 23, 2, 43, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 37,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 233, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 163, 2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 47, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 101, 2, 19, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 67, 2, 3, 2, 41, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 137, 2, 79, 2, 3, 2, 131, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 229, 2, 3, 2, 43]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData139_checked :
    roundedProductCertificate 71170 19904319781706 productData139 = some 19917703334550 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData139_length : productData139.length = 512 := by decide

def productData140 : List ℕ :=
  [2, 97, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 13, 2, 157, 2, 3, 2, 11, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0,
    2, 179, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 59, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 109, 2, 29, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 181, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 71, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 47, 2, 227, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79,
    2, 0, 2, 3, 2, 5, 2, 167, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 193, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 89,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 107, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 61, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 97, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 17, 2, 53, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData140_checked :
    roundedProductCertificate 71682 19917703334550 productData140 = some 19931552580809 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData140_length : productData140.length = 512 := by decide

def productData141 : List ℕ :=
  [2, 3, 2, 23, 2, 17, 2, 3, 2, 103, 2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 257, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19,
    2, 11, 2, 3, 2, 127, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 197, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 167, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 151, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 73, 2, 3, 2, 11, 2, 71, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 269, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 157, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 191, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 61, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 139, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 113, 2, 3, 2, 17, 2, 107, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13,
    2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 233, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 173, 2, 3, 2, 71, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 59, 2, 3,
    2, 5, 2, 127, 2, 3, 2, 47, 2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 37, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 181, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 229, 2, 5, 2, 3, 2, 19, 2, 79, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 139, 2, 3, 2, 0, 2, 23, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData141_checked :
    roundedProductCertificate 72194 19931552580809 productData141 = some 19943936018363 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData141_length : productData141.length = 512 := by decide

def productData142 : List ℕ :=
  [2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 257, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 53,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 11, 2, 3, 2, 83, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 67, 2, 3, 2, 173,
    2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 97, 2, 3, 2, 263, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 269, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 233,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 131, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 59, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5,
    2, 103, 2, 3, 2, 7, 2, 199, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 107, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 67, 2, 13, 2, 3, 2, 41, 2, 5, 2, 3, 2, 29, 2, 113, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 83, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 193, 2, 3, 2, 13, 2, 191,
    2, 3, 2, 7, 2, 149, 2, 3, 2, 23, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 163, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 19, 2, 3, 2, 179, 2, 7, 2, 3, 2, 211]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData142_checked :
    roundedProductCertificate 72706 19943936018363 productData142 = some 19955970060241 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData142_length : productData142.length = 512 := by decide

def productData143 : List ℕ :=
  [2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 13, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 89, 2, 11,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 41, 2, 3, 2, 11, 2, 47, 2, 3, 2, 0, 2, 127, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 167,
    2, 5, 2, 3, 2, 157, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 109, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 239, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 79, 2, 23, 2, 3, 2, 19, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 101, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 271,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 197, 2, 0, 2, 3, 2, 43, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 67, 2, 31, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 151,
    2, 3, 2, 13, 2, 251, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 89, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 17, 2, 3, 2, 29, 2, 7,
    2, 3, 2, 0, 2, 211, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 11, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 59, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData143_checked :
    roundedProductCertificate 73218 19955970060241 productData143 = some 19968735930123 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData143_length : productData143.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block09.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData144 : List ℕ :=
  [2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 37, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 131, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 89, 2, 0, 2, 3, 2, 7, 2, 113, 2, 3, 2, 109,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 31, 2, 223, 2, 3, 2, 97, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 47, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 0, 2, 233, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37,
    2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 263, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 193, 2, 29,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 107, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 0, 2, 37, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 167, 2, 3, 2, 5,
    2, 241, 2, 3, 2, 23, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 79, 2, 3, 2, 0, 2, 181, 2, 3, 2, 101, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 103, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 23, 2, 3, 2, 13, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 37, 2, 13,
    2, 3, 2, 137, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 151, 2, 0, 2, 3,
    2, 53, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 199, 2, 3, 2, 0, 2, 19, 2, 3, 2, 61, 2, 11, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData144_checked :
    roundedProductCertificate 73730 19968735930123 productData144 = some 19980610715381 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData144_length : productData144.length = 512 := by decide

def productData145 : List ℕ :=
  [2, 13, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 23, 2, 13, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 191, 2, 3, 2, 67, 2, 5,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 239, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 79, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 47,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 263, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 109, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5,
    2, 113, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 71, 2, 3, 2, 211, 2, 5, 2, 3, 2, 0, 2, 163, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 269, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 73, 2, 3, 2, 19, 2, 131, 2, 3, 2, 7, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 173, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 97,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 71, 2, 0, 2, 3,
    2, 7, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 101, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 197, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 53, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 113, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 41, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData145_checked :
    roundedProductCertificate 74242 19980610715381 productData145 = some 19992951317079 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData145_length : productData145.length = 512 := by decide

def productData146 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 37, 2, 0, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 19, 2, 3, 2, 239, 2, 7, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 103,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 173, 2, 23, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 137, 2, 0, 2, 3, 2, 5,
    2, 149, 2, 3, 2, 241, 2, 17, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61, 2, 13, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 97, 2, 167, 2, 3, 2, 11, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 37, 2, 179, 2, 3, 2, 5, 2, 107, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 101, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 271, 2, 3, 2, 41, 2, 37,
    2, 3, 2, 193, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 61, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 227,
    2, 29, 2, 3, 2, 163, 2, 5, 2, 3, 2, 0, 2, 223, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 29, 2, 139, 2, 3,
    2, 157, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 73, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData146_checked :
    roundedProductCertificate 74754 19992951317079 productData146 = some 20004950595011 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData146_length : productData146.length = 512 := by decide

def productData147 : List ℕ :=
  [2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 13, 2, 3, 2, 79, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 257, 2, 3, 2, 5, 2, 0, 2, 3, 2, 127, 2, 7, 2, 3, 2, 11, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 59, 2, 3, 2, 0, 2, 151, 2, 3, 2, 0, 2, 5, 2, 3, 2, 179, 2, 11,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 19, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 73, 2, 3, 2, 13, 2, 5, 2, 3, 2, 53, 2, 199, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 241, 2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 197, 2, 3, 2, 5, 2, 61,
    2, 3, 2, 59, 2, 17, 2, 3, 2, 7, 2, 163, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 17, 2, 103, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 131, 2, 269, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 83, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 67, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 31, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 53, 2, 23, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 211, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 239, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData147_checked :
    roundedProductCertificate 75266 20004950595011 productData147 = some 20017933856344 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData147_length : productData147.length = 512 := by decide

def productData148 : List ℕ :=
  [2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 229, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41,
    2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 191, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 181, 2, 149,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 101, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 89, 2, 31, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 173, 2, 53, 2, 3, 2, 151, 2, 5, 2, 3, 2, 13, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 17, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 139,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 113, 2, 59, 2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 13, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 127, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 103, 2, 3, 2, 163, 2, 0, 2, 3, 2, 269, 2, 0,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 271, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 59, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 29, 2, 3, 2, 47, 2, 61, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 23, 2, 181, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 199, 2, 11, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 53, 2, 3, 2, 13, 2, 89, 2, 3, 2, 83, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData148_checked :
    roundedProductCertificate 75778 20017933856344 productData148 = some 20029519948334 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData148_length : productData148.length = 512 := by decide

def productData149 : List ℕ :=
  [2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 7, 2, 137, 2, 3, 2, 17, 2, 5, 2, 3, 2, 167, 2, 7,
    2, 3, 2, 5, 2, 127, 2, 3, 2, 37, 2, 0, 2, 3, 2, 23, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 79, 2, 3, 2, 241, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 109, 2, 43, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 89, 2, 13, 2, 3, 2, 101, 2, 157, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 227, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 41, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 73,
    2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 191, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 193, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 197, 2, 3, 2, 11, 2, 173, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 31, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 53, 2, 271, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 79, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 73, 2, 3, 2, 7, 2, 277, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 17, 2, 3, 2, 41, 2, 5, 2, 3, 2, 61, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData149_checked :
    roundedProductCertificate 76290 20029519948334 productData149 = some 20040511442787 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData149_length : productData149.length = 512 := by decide

def productData150 : List ℕ :=
  [2, 3, 2, 5, 2, 89, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 43, 2, 13, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 151, 2, 101, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 131,
    2, 3, 2, 11, 2, 53, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 19, 2, 107, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 11, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 167, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 37, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 29, 2, 3, 2, 251,
    2, 263, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 157, 2, 127,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 29, 2, 59, 2, 3, 2, 67, 2, 7, 2, 3,
    2, 233, 2, 5, 2, 3, 2, 13, 2, 137, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 179, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 229, 2, 3, 2, 71, 2, 113, 2, 3, 2, 79, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 37, 2, 31, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 67, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 109,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 11, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3, 2, 97, 2, 13, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData150_checked :
    roundedProductCertificate 76802 20040511442787 productData150 = some 20051957051674 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData150_length : productData150.length = 512 := by decide

def productData151 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 167, 2, 0, 2, 3, 2, 53, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 103, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 223, 2, 0, 2, 3, 2, 19, 2, 13, 2, 3, 2, 193, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 199, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 139, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 211, 2, 3, 2, 7,
    2, 43, 2, 3, 2, 0, 2, 41, 2, 3, 2, 73, 2, 5, 2, 3, 2, 29, 2, 71, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 17, 2, 3,
    2, 179, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 23, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 13, 2, 73, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 149, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 79, 2, 0, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 101, 2, 11, 2, 3, 2, 5, 2, 173, 2, 3, 2, 0, 2, 131, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 83, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 107, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 29, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData151_checked :
    roundedProductCertificate 77314 20051957051674 productData151 = some 20065921040647 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData151_length : productData151.length = 512 := by decide

def productData152 : List ℕ :=
  [2, 223, 2, 3, 2, 13, 2, 7, 2, 3, 2, 277, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 127, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3, 2, 5, 2, 71, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67,
    2, 29, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 41, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 137,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3,
    2, 7, 2, 167, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 181, 2, 13, 2, 3, 2, 0,
    2, 61, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 89, 2, 5, 2, 3, 2, 0, 2, 251, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 101, 2, 3, 2, 163, 2, 0, 2, 3,
    2, 113, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 83, 2, 3, 2, 37, 2, 19, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 191, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 17, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 37, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 197,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 19, 2, 3, 2, 137, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 7, 2, 3, 2, 139, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 23, 2, 29, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 79, 2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3, 2, 5, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData152_checked :
    roundedProductCertificate 77826 20065921040647 productData152 = some 20076715875210 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData152_length : productData152.length = 512 := by decide

def productData153 : List ℕ :=
  [2, 3, 2, 0, 2, 157, 2, 3, 2, 0, 2, 47, 2, 3, 2, 11, 2, 5, 2, 3, 2, 127, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 109, 2, 181, 2, 3, 2, 13, 2, 7, 2, 3, 2, 103, 2, 5, 2, 3, 2, 43, 2, 277, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 7, 2, 89, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 41,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 67, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 0, 2, 131, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 233, 2, 17, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 251, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 179, 2, 0, 2, 3, 2, 89, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 53, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 127, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 97, 2, 3, 2, 151, 2, 7, 2, 3, 2, 29, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 211, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 223, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 131, 2, 43, 2, 3, 2, 0, 2, 71, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 61, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 79, 2, 3, 2, 13, 2, 227, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 269,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData153_checked :
    roundedProductCertificate 78338 20076715875210 productData153 = some 20087446204672 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData153_length : productData153.length = 512 := by decide

def productData154 : List ℕ :=
  [2, 29, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 257, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 53, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 193, 2, 3, 2, 0, 2, 89, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 281, 2, 3, 2, 5, 2, 7, 2, 3, 2, 157, 2, 151, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 197, 2, 3, 2, 13, 2, 199, 2, 3, 2, 41, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 137, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 173, 2, 0, 2, 3, 2, 17, 2, 37, 2, 3, 2, 107,
    2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 139, 2, 7, 2, 3, 2, 19, 2, 83, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 239, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 11, 2, 3, 2, 67, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0,
    2, 3, 2, 5, 2, 103, 2, 3, 2, 11, 2, 113, 2, 3, 2, 37, 2, 7, 2, 3, 2, 227, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 0, 2, 109, 2, 3, 2, 7, 2, 19, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 179,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 71, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData154_checked :
    roundedProductCertificate 78850 20087446204672 productData154 = some 20098620940906 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData154_length : productData154.length = 512 := by decide

def productData155 : List ℕ :=
  [2, 19, 2, 3, 2, 0, 2, 139, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 163, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 271, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 43, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7,
    2, 181, 2, 3, 2, 229, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 61, 2, 3, 2, 101, 2, 29,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 7, 2, 3, 2, 131, 2, 11, 2, 3,
    2, 281, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 251, 2, 3, 2, 47, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 103, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3, 2, 23,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 79, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 61, 2, 13, 2, 3, 2, 71, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 7, 2, 173, 2, 3, 2, 0, 2, 47, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 241, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 23, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 199, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 97, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData155_checked :
    roundedProductCertificate 79362 20098620940906 productData155 = some 20110739363141 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData155_length : productData155.length = 512 := by decide

def productData156 : List ℕ :=
  [2, 3, 2, 7, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 41, 2, 3, 2, 157, 2, 5, 2, 3, 2, 7, 2, 229, 2, 3, 2, 5, 2, 257, 2, 3, 2, 67, 2, 7, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 211,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 167, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 19, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 43, 2, 3, 2, 79, 2, 191, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 223, 2, 7, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 53, 2, 3, 2, 7, 2, 283, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 173, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 113, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7,
    2, 227, 2, 3, 2, 5, 2, 127, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 19,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 181, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 11, 2, 139, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 83, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 17, 2, 23, 2, 3, 2, 7, 2, 59, 2, 3, 2, 131, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31,
    2, 47, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 107, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 179, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData156_checked :
    roundedProductCertificate 79874 20110739363141 productData156 = some 20122035398234 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData156_length : productData156.length = 512 := by decide

def productData157 : List ℕ :=
  [2, 0, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 191, 2, 97, 2, 3, 2, 29,
    2, 137, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 257, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 61, 2, 17, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 79, 2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 73, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 43, 2, 3, 2, 239, 2, 5,
    2, 3, 2, 7, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 197, 2, 5, 2, 3,
    2, 19, 2, 61, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 83, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 149,
    2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 79, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 89, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 263, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 173, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 211, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 131, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 229, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 233, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 193, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31, 2, 29, 2, 3, 2, 5, 2, 47, 2, 3, 2, 23, 2, 41, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData157_checked :
    roundedProductCertificate 80386 20122035398234 productData157 = some 20133515231925 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData157_length : productData157.length = 512 := by decide

def productData158 : List ℕ :=
  [2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2, 13, 2, 0, 2, 3, 2, 73, 2, 19, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47, 2, 7, 2, 3, 2, 109, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 131,
    2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 41, 2, 3, 2, 53, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 277, 2, 0, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 241,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 43, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 31, 2, 193, 2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 181, 2, 67, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 29, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 31,
    2, 3, 2, 233, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 167, 2, 0, 2, 3, 2, 5, 2, 163, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19,
    2, 17, 2, 3, 2, 97, 2, 5, 2, 3, 2, 7, 2, 199, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 127, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData158_checked :
    roundedProductCertificate 80898 20133515231925 productData158 = some 20145925490494 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData158_length : productData158.length = 512 := by decide

def productData159 : List ℕ :=
  [2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 7, 2, 11, 2, 3, 2, 31, 2, 0, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 79, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 41, 2, 257, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 59, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 227, 2, 3, 2, 13, 2, 11, 2, 3, 2, 149, 2, 5,
    2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 67, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 23, 2, 17, 2, 3, 2, 11, 2, 83, 2, 3, 2, 139, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 79, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37, 2, 127, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 151, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 101, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 89, 2, 263,
    2, 3, 2, 157, 2, 0, 2, 3, 2, 179, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 47, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 223, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23,
    2, 109, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 41, 2, 3, 2, 37, 2, 0, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 101, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData159_checked :
    roundedProductCertificate 81410 20145925490494 productData159 = some 20156534947592 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData159_length : productData159.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block10.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData160 : List ℕ :=
  [2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 73, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 163, 2, 7, 2, 3, 2, 5, 2, 167, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 137, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 211, 2, 79,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 103, 2, 11, 2, 3, 2, 53, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 157, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 41, 2, 3, 2, 17, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 113, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 229, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 11, 2, 233, 2, 3, 2, 83, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 107, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 0, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 263, 2, 191, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 281, 2, 3, 2, 137,
    2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 11, 2, 3, 2, 139, 2, 31, 2, 3, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData160_checked :
    roundedProductCertificate 81922 20156534947592 productData160 = some 20168315362983 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData160_length : productData160.length = 512 := by decide

def productData161 : List ℕ :=
  [2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 29, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 109, 2, 3, 2, 19, 2, 179, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 197, 2, 3, 2, 23, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 11, 2, 7, 2, 3, 2, 269, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 5, 2, 151, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 19, 2, 0, 2, 3, 2, 17, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 131, 2, 7, 2, 3, 2, 13, 2, 19, 2, 3, 2, 47, 2, 5, 2, 3, 2, 29, 2, 89, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 191, 2, 5, 2, 3, 2, 11, 2, 107, 2, 3, 2, 5, 2, 181, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 97, 2, 3, 2, 5, 2, 7, 2, 3, 2, 83, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 113, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 37, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 173, 2, 3, 2, 79, 2, 7, 2, 3, 2, 179, 2, 67, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 283, 2, 101, 2, 3, 2, 5, 2, 13, 2, 3, 2, 127, 2, 239, 2, 3, 2, 197, 2, 0, 2, 3, 2, 7, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData161_checked :
    roundedProductCertificate 82434 20168315362983 productData161 = some 20179540490713 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData161_length : productData161.length = 512 := by decide

def productData162 : List ℕ :=
  [2, 3, 2, 109, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 163, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 37, 2, 149, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7, 2, 79, 2, 3, 2, 43, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 23, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 251, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 43, 2, 3, 2, 101, 2, 5, 2, 3, 2, 97, 2, 59, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 71, 2, 29, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 137, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 31, 2, 3, 2, 0, 2, 223, 2, 3, 2, 193, 2, 5, 2, 3, 2, 41, 2, 23, 2, 3, 2, 5, 2, 271, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 139, 2, 53, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 13, 2, 7, 2, 3, 2, 31,
    2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 227, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 97, 2, 3, 2, 103, 2, 23,
    2, 3, 2, 167, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 19, 2, 3, 2, 0, 2, 31, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 263, 2, 3, 2, 5, 2, 7, 2, 3, 2, 199, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3, 2, 89,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 239, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 181, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData162_checked :
    roundedProductCertificate 82946 20179540490713 productData162 = some 20190454800278 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData162_length : productData162.length = 512 := by decide

def productData163 : List ℕ :=
  [2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 113, 2, 37, 2, 3, 2, 23, 2, 5, 2, 3, 2, 47, 2, 17,
    2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 103, 2, 3, 2, 0, 2, 139, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 193, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 179, 2, 3, 2, 0, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 241, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 233, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 7, 2, 269, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13,
    2, 67, 2, 3, 2, 53, 2, 0, 2, 3, 2, 127, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 97, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 101, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 83, 2, 89, 2, 3, 2, 61, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 211, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0,
    2, 199, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 181, 2, 3, 2, 43, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 109, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 191, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 43, 2, 3, 2, 11, 2, 53, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 127, 2, 3, 2, 7, 2, 37, 2, 3, 2, 59, 2, 113, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData163_checked :
    roundedProductCertificate 83458 20190454800278 productData163 = some 20200104565121 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData163_length : productData163.length = 512 := by decide

def productData164 : List ℕ :=
  [2, 131, 2, 3, 2, 5, 2, 79, 2, 3, 2, 137, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 167,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 13, 2, 3, 2, 73, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 31, 2, 229, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 83, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 37, 2, 31, 2, 3, 2, 151, 2, 241, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 17, 2, 73, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 59,
    2, 3, 2, 269, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 131, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 173, 2, 13, 2, 3, 2, 109,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 71, 2, 3, 2, 271, 2, 89, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 239, 2, 3, 2, 7, 2, 139, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 29, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 79, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData164_checked :
    roundedProductCertificate 83970 20200104565121 productData164 = some 20211617057649 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData164_length : productData164.length = 512 := by decide

def productData165 : List ℕ :=
  [2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 223, 2, 3, 2, 0, 2, 0, 2, 3, 2, 181, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5,
    2, 59, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 83,
    2, 3, 2, 7, 2, 41, 2, 3, 2, 251, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 211, 2, 191, 2, 3, 2, 13, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53,
    2, 13, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 227, 2, 0,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 193, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0,
    2, 101, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 103,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 149, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 137, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 89, 2, 3, 2, 11, 2, 271, 2, 3, 2, 0, 2, 41, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 43, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 29, 2, 3, 2, 11, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 73, 2, 59, 2, 3, 2, 5, 2, 197, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 163, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 157, 2, 3, 2, 29, 2, 173, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData165_checked :
    roundedProductCertificate 84482 20211617057649 productData165 = some 20221398616541 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData165_length : productData165.length = 512 := by decide

def productData166 : List ℕ :=
  [2, 5, 2, 11, 2, 3, 2, 7, 2, 167, 2, 3, 2, 13, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 277, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 257, 2, 97, 2, 3, 2, 241, 2, 5, 2, 3, 2, 149, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 17,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 19, 2, 3, 2, 103, 2, 7, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 139, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11,
    2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 163,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2, 269, 2, 3, 2, 53, 2, 107, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 197, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 61, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 103, 2, 3, 2, 17, 2, 7, 2, 3, 2, 13, 2, 23, 2, 3, 2, 41, 2, 5, 2, 3, 2, 223,
    2, 0, 2, 3, 2, 5, 2, 229, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 43,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 127, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 73, 2, 3, 2, 0, 2, 53, 2, 3, 2, 17, 2, 5, 2, 3, 2, 193, 2, 13, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData166_checked :
    roundedProductCertificate 84994 20221398616541 productData166 = some 20231839265838 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData166_length : productData166.length = 512 := by decide

def productData167 : List ℕ :=
  [2, 37, 2, 3, 2, 233, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 113, 2, 131, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 0, 2, 83, 2, 3, 2, 0, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 97, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 67, 2, 3, 2, 17,
    2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 11, 2, 3, 2, 59, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 179, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 191, 2, 3,
    2, 139, 2, 5, 2, 3, 2, 199, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 109, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 239, 2, 3, 2, 5, 2, 53, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 293, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 23, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 43, 2, 79, 2, 3, 2, 11, 2, 157, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 271, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 151, 2, 11,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2, 23, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 67, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3, 2, 149, 2, 5, 2, 3, 2, 127, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 113, 2, 3, 2, 23, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData167_checked :
    roundedProductCertificate 85506 20231839265838 productData167 = some 20241988354718 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData167_length : productData167.length = 512 := by decide

def productData168 : List ℕ :=
  [2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 227, 2, 5, 2, 3, 2, 97, 2, 139, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 47, 2, 41, 2, 3, 2, 89, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59,
    2, 0, 2, 3, 2, 31, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 71, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 277, 2, 7, 2, 3, 2, 101, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 199, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 151, 2, 3, 2, 5, 2, 23, 2, 3, 2, 53, 2, 7, 2, 3, 2, 83, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 281, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 211, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 0, 2, 3, 2, 173, 2, 131, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 71, 2, 3, 2, 13, 2, 0, 2, 3, 2, 103, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 137, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 43, 2, 3, 2, 0, 2, 17, 2, 3, 2, 197, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 241, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData168_checked :
    roundedProductCertificate 86018 20241988354718 productData168 = some 20253487819516 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData168_length : productData168.length = 512 := by decide

def productData169 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 101, 2, 3, 2, 0,
    2, 107, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 13,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 257, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 73, 2, 7, 2, 3, 2, 193,
    2, 19, 2, 3, 2, 79, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 181, 2, 277, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 127, 2, 0, 2, 3, 2, 223, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 101, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 107, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 59, 2, 229, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 61, 2, 3, 2, 7, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 71, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 13, 2, 283,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 31, 2, 3, 2, 113, 2, 67, 2, 3, 2, 43, 2, 5, 2, 3, 2, 233, 2, 11, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 227, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 89, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 167, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 173, 2, 3, 2, 17, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData169_checked :
    roundedProductCertificate 86530 20253487819516 productData169 = some 20263057989453 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData169_length : productData169.length = 512 := by decide

def productData170 : List ℕ :=
  [2, 11, 2, 3, 2, 61, 2, 0, 2, 3, 2, 263, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 19, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2, 5, 2, 251, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 151, 2, 3, 2, 11, 2, 0, 2, 3, 2, 79,
    2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 101, 2, 3, 2, 67, 2, 61,
    2, 3, 2, 179, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 17, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 83,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 197, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 191, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 67, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 167, 2, 19, 2, 3, 2, 13, 2, 113, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 199,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 11, 2, 3, 2, 23, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 281, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 71, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 157, 2, 7, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 11, 2, 149, 2, 3, 2, 47, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 89, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 59, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData170_checked :
    roundedProductCertificate 87042 20263057989453 productData170 = some 20273736151278 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData170_length : productData170.length = 512 := by decide

def productData171 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 67, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 251, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 79, 2, 0, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 73, 2, 3, 2, 43, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 229, 2, 139, 2, 3, 2, 239,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 59, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 127, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 61, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 277,
    2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 53, 2, 31, 2, 3, 2, 71, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 13,
    2, 3, 2, 5, 2, 107, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 103, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 179, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 37, 2, 3, 2, 281, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 97, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 283, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 19, 2, 3, 2, 47, 2, 11,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 191, 2, 3, 2, 5, 2, 173, 2, 3, 2, 107, 2, 83, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData171_checked :
    roundedProductCertificate 87554 20273736151278 productData171 = some 20284824182528 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData171_length : productData171.length = 512 := by decide

def productData172 : List ℕ :=
  [2, 7, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2, 137, 2, 0, 2, 3, 2, 37,
    2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 53, 2, 19, 2, 3, 2, 5, 2, 181, 2, 3, 2, 7, 2, 13, 2, 3, 2, 199, 2, 23, 2, 3,
    2, 131, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 109, 2, 163, 2, 3, 2, 11, 2, 29, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 89, 2, 193, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 19, 2, 47, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 83, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 103, 2, 41, 2, 3, 2, 7, 2, 43, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 227, 2, 3, 2, 233, 2, 13, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 53, 2, 3,
    2, 5, 2, 149, 2, 3, 2, 7, 2, 11, 2, 3, 2, 97, 2, 19, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 157, 2, 37, 2, 3, 2, 0, 2, 109, 2, 3, 2, 7, 2, 5, 2, 3, 2, 211, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 191, 2, 5, 2, 3, 2, 13, 2, 59, 2, 3, 2, 5, 2, 241, 2, 3,
    2, 11, 2, 197, 2, 3, 2, 53, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 103, 2, 3, 2, 23,
    2, 19, 2, 3, 2, 7, 2, 107, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 67, 2, 3, 2, 61, 2, 0,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 223, 2, 3, 2, 5, 2, 29, 2, 3, 2, 37, 2, 7, 2, 3,
    2, 0, 2, 73, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 23, 2, 3, 2, 101]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData172_checked :
    roundedProductCertificate 88066 20284824182528 productData172 = some 20292175268110 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData172_length : productData172.length = 512 := by decide

def productData173 : List ℕ :=
  [2, 283, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 41, 2, 251, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 263, 2, 61, 2, 3, 2, 151, 2, 137, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 31, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 107, 2, 5,
    2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 0, 2, 17, 2, 3, 2, 83, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 29,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 47, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 211, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 73, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 181, 2, 0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 113, 2, 13, 2, 3, 2, 0, 2, 19, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 43, 2, 0, 2, 3, 2, 193, 2, 5, 2, 3, 2, 11, 2, 101, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 127, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 269, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 281, 2, 3, 2, 229, 2, 0, 2, 3, 2, 0, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData173_checked :
    roundedProductCertificate 88578 20292175268110 productData173 = some 20303598611878 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData173_length : productData173.length = 512 := by decide

def productData174 : List ℕ :=
  [2, 3, 2, 41, 2, 5, 2, 3, 2, 139, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 97, 2, 3, 2, 239, 2, 59, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 163, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 7, 2, 3, 2, 11, 2, 257, 2, 3, 2, 101, 2, 5,
    2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 191, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 233, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31,
    2, 149, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 19,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 179, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 157, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 199, 2, 11, 2, 3, 2, 19, 2, 193, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 223, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 131,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 109, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 37, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 151, 2, 5, 2, 3, 2, 149, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 43,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 101, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData174_checked :
    roundedProductCertificate 89090 20303598611878 productData174 = some 20314280560778 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData174_length : productData174.length = 512 := by decide

def productData175 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 157, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 257, 2, 5, 2, 3,
    2, 19, 2, 271, 2, 3, 2, 5, 2, 109, 2, 3, 2, 283, 2, 13, 2, 3, 2, 73, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 53,
    2, 61, 2, 3, 2, 5, 2, 19, 2, 3, 2, 43, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 107, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 89, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 23, 2, 73, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 241, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 11, 2, 3, 2, 293, 2, 23,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 29, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 197, 2, 0, 2, 3, 2, 5, 2, 179, 2, 3, 2, 7, 2, 127, 2, 3, 2, 53, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 251, 2, 3, 2, 97]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData175_checked :
    roundedProductCertificate 89602 20314280560778 productData175 = some 20325585831205 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData175_length : productData175.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block11.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData176 : List ℕ :=
  [2, 5, 2, 3, 2, 227, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 193, 2, 173, 2, 3, 2, 23, 2, 7, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 89, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 31,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 43, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 137, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 73, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 37, 2, 181, 2, 3, 2, 41, 2, 5, 2, 3, 2, 59, 2, 103, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 61, 2, 11, 2, 3, 2, 167, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 151, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 61, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 173, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 17, 2, 13, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 131, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 83, 2, 3, 2, 137, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 41, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 239, 2, 0, 2, 3, 2, 7, 2, 157, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData176_checked :
    roundedProductCertificate 90114 20325585831205 productData176 = some 20335485571385 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData176_length : productData176.length = 512 := by decide

def productData177 : List ℕ :=
  [2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 233, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 269, 2, 5, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 23,
    2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83, 2, 257,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 41, 2, 3, 2, 31, 2, 11, 2, 3, 2, 103, 2, 5, 2, 3, 2, 0, 2, 151, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 11, 2, 17, 2, 3, 2, 139, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 163, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3, 2, 5, 2, 197,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 47, 2, 7, 2, 3, 2, 13, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 0, 2, 97, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 229,
    2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 211, 2, 199, 2, 3,
    2, 0, 2, 103, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 227, 2, 3, 2, 29, 2, 0, 2, 3, 2, 59, 2, 13, 2, 3,
    2, 181, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 71, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 31, 2, 179, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 293, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData177_checked :
    roundedProductCertificate 90626 20335485571385 productData177 = some 20344661998788 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData177_length : productData177.length = 512 := by decide

def productData178 : List ℕ :=
  [2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 223, 2, 3, 2, 197, 2, 53, 2, 3, 2, 7, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 263, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 107, 2, 7, 2, 3, 2, 97, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 127, 2, 5, 2, 3, 2, 53, 2, 29, 2, 3, 2, 5, 2, 271, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 149, 2, 241, 2, 3, 2, 7, 2, 5, 2, 3, 2, 167, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 103,
    2, 211, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 113, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 109, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 191,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 71, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 239, 2, 3, 2, 0, 2, 31, 2, 3, 2, 43, 2, 83, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 139, 2, 47, 2, 3, 2, 101, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 113, 2, 5, 2, 3, 2, 37]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData178_checked :
    roundedProductCertificate 91138 20344661998788 productData178 = some 20355129316112 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData178_length : productData178.length = 512 := by decide

def productData179 : List ℕ :=
  [2, 7, 2, 3, 2, 5, 2, 151, 2, 3, 2, 71, 2, 11, 2, 3, 2, 31, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 277, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 107, 2, 3, 2, 0, 2, 5, 2, 3, 2, 293, 2, 0, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 7, 2, 37, 2, 3, 2, 29, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 199, 2, 13, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 263, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 229, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 29, 2, 3, 2, 7, 2, 53, 2, 3, 2, 31, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 79, 2, 139, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 29, 2, 7, 2, 3,
    2, 73, 2, 0, 2, 3, 2, 107, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 149, 2, 3, 2, 89,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 11, 2, 3, 2, 0, 2, 197, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 101, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 71, 2, 17, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 251, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 181,
    2, 13, 2, 3, 2, 5, 2, 199, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 157, 2, 23]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData179_checked :
    roundedProductCertificate 91650 20355129316112 productData179 = some 20363989817444 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData179_length : productData179.length = 512 := by decide

def productData180 : List ℕ :=
  [2, 3, 2, 5, 2, 37, 2, 3, 2, 61, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 137, 2, 0, 2, 3, 2, 19, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 149, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 13, 2, 257, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 41, 2, 17, 2, 3, 2, 0, 2, 23, 2, 3, 2, 241, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 17, 2, 127, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 97, 2, 13, 2, 3, 2, 193, 2, 7,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 89, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 233, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 67, 2, 3, 2, 17, 2, 7, 2, 3, 2, 37, 2, 29, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 151, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 43, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 0, 2, 3, 2, 29, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 211, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData180_checked :
    roundedProductCertificate 92162 20363989817444 productData180 = some 20375451919745 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData180_length : productData180.length = 512 := by decide

def productData181 : List ℕ :=
  [2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 83, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 163, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 113, 2, 3, 2, 19, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 17, 2, 263, 2, 3, 2, 227, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 131, 2, 293, 2, 3, 2, 5, 2, 29, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 19,
    2, 3, 2, 199, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 31, 2, 239, 2, 3, 2, 5, 2, 109, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 113, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 281, 2, 47, 2, 3, 2, 191, 2, 167, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 41, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 163, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 127, 2, 3, 2, 5, 2, 0, 2, 3, 2, 157, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 59, 2, 7, 2, 3, 2, 151, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData181_checked :
    roundedProductCertificate 92674 20375451919745 productData181 = some 20386199982347 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData181_length : productData181.length = 512 := by decide

def productData182 : List ℕ :=
  [2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 83, 2, 17, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 73, 2, 13, 2, 3, 2, 53, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 179, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 79, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 269, 2, 3,
    2, 17, 2, 277, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 61, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 29,
    2, 3, 2, 109, 2, 5, 2, 3, 2, 0, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 233, 2, 3, 2, 223, 2, 41, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 17, 2, 113, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11, 2, 151, 2, 3, 2, 211,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 41, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 89, 2, 7, 2, 3, 2, 5, 2, 139, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 137, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 31, 2, 3, 2, 173, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 179, 2, 17, 2, 3, 2, 251, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 29, 2, 11, 2, 3, 2, 37, 2, 71, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 229, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 47, 2, 283, 2, 3, 2, 113, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 43]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData182_checked :
    roundedProductCertificate 93186 20386199982347 productData182 = some 20395586122060 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData182_length : productData182.length = 512 := by decide

def productData183 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 83, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 11, 2, 67, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 241, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 41, 2, 13, 2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2, 191, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71, 2, 7,
    2, 3, 2, 11, 2, 97, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 0, 2, 101, 2, 3, 2, 103, 2, 5, 2, 3, 2, 107, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 127, 2, 3, 2, 17,
    2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 269, 2, 223, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 193, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 149, 2, 167, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 271, 2, 11, 2, 3, 2, 157, 2, 5, 2, 3, 2, 0,
    2, 163, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 109, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 23, 2, 3, 2, 73, 2, 0, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23, 2, 47, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 53, 2, 19, 2, 3, 2, 97, 2, 131, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData183_checked :
    roundedProductCertificate 93698 20395586122060 productData183 = some 20405139647074 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData183_length : productData183.length = 512 := by decide

def productData184 : List ℕ :=
  [2, 13, 2, 7, 2, 3, 2, 71, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7,
    2, 73, 2, 3, 2, 79, 2, 307, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 31, 2, 0,
    2, 3, 2, 23, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 181, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 257, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 157, 2, 3, 2, 127, 2, 197, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 263, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 89, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 11, 2, 59, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 0, 2, 3, 2, 19, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 53, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 47, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 271, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 89, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 173, 2, 7, 2, 3, 2, 101, 2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 7, 2, 181, 2, 3, 2, 137, 2, 41, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 73, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 281, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData184_checked :
    roundedProductCertificate 94210 20405139647074 productData184 = some 20414862943973 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData184_length : productData184.length = 512 := by decide

def productData185 : List ℕ :=
  [2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 61, 2, 5, 2, 3, 2, 211, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 19,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 193, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 59, 2, 3, 2, 53,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 79, 2, 3,
    2, 239, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 107, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 0, 2, 3, 2, 139, 2, 13, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 269, 2, 3, 2, 0, 2, 11, 2, 3, 2, 23, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 17, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 167, 2, 3, 2, 0, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 101,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 227, 2, 3, 2, 11, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 251, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 89, 2, 0, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 11, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 19, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 31,
    2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData185_checked :
    roundedProductCertificate 94722 20414862943973 productData185 = some 20425397233055 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData185_length : productData185.length = 512 := by decide

def productData186 : List ℕ :=
  [2, 3, 2, 131, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 233,
    2, 157, 2, 3, 2, 13, 2, 5, 2, 3, 2, 191, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 199, 2, 19, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 7, 2, 3, 2, 97, 2, 17, 2, 3, 2, 167, 2, 11, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 0, 2, 283, 2, 3, 2, 5, 2, 127, 2, 3, 2, 11, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 307, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 43, 2, 3, 2, 0, 2, 149, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 59,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 83, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 227, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 17, 2, 109, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 23, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 0, 2, 41, 2, 3, 2, 23, 2, 17, 2, 3, 2, 271, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 241, 2, 3, 2, 163,
    2, 7, 2, 3, 2, 103, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 67, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData186_checked :
    roundedProductCertificate 95234 20425397233055 productData186 = some 20435453299845 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData186_length : productData186.length = 512 := by decide

def productData187 : List ℕ :=
  [2, 0, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 149, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 79, 2, 3, 2, 61, 2, 47, 2, 3, 2, 7, 2, 239, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 257, 2, 17, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 41, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 197, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 229, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 5, 2, 3, 2, 17, 2, 0,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 67, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 131, 2, 5, 2, 3, 2, 109, 2, 13, 2, 3,
    2, 5, 2, 137, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 139, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 23, 2, 191, 2, 3, 2, 29, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 307, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 223, 2, 5, 2, 3, 2, 277, 2, 19, 2, 3, 2, 5, 2, 97, 2, 3,
    2, 7, 2, 251, 2, 3, 2, 0, 2, 127, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 29,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 157, 2, 3, 2, 5, 2, 109, 2, 3, 2, 29, 2, 101, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData187_checked :
    roundedProductCertificate 95746 20435453299845 productData187 = some 20444610132717 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData187_length : productData187.length = 512 := by decide

def productData188 : List ℕ :=
  [2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 11, 2, 3, 2, 73, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 193, 2, 3, 2, 19, 2, 7, 2, 3, 2, 13, 2, 61, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 167, 2, 173, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 113, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 149, 2, 3, 2, 17, 2, 229, 2, 3, 2, 67, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 211, 2, 3, 2, 0, 2, 73, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 103, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 263, 2, 7, 2, 3, 2, 0, 2, 83, 2, 3, 2, 37, 2, 5, 2, 3, 2, 19, 2, 29, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 223, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 269, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 79, 2, 53, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 71, 2, 3, 2, 5, 2, 41, 2, 3, 2, 241,
    2, 0, 2, 3, 2, 127, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 277,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 109, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 13, 2, 97, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 311, 2, 3, 2, 5, 2, 197, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData188_checked :
    roundedProductCertificate 96258 20444610132717 productData188 = some 20454145109022 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData188_length : productData188.length = 512 := by decide

def productData189 : List ℕ :=
  [2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 151, 2, 43, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 131, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 179, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 157, 2, 73, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 199, 2, 3, 2, 17, 2, 19, 2, 3, 2, 103, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 47,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 293, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2, 23, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 107, 2, 37, 2, 3, 2, 5, 2, 71,
    2, 3, 2, 31, 2, 29, 2, 3, 2, 113, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 193, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 79, 2, 151, 2, 3, 2, 7, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17,
    2, 13, 2, 3, 2, 0, 2, 23, 2, 3, 2, 137, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 157, 2, 3,
    2, 0, 2, 17, 2, 3, 2, 83, 2, 5, 2, 3, 2, 37, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 67,
    2, 191, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 31, 2, 79,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 23, 2, 3, 2, 211, 2, 11, 2, 3, 2, 89, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData189_checked :
    roundedProductCertificate 96770 20454145109022 productData189 = some 20462791768377 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData189_length : productData189.length = 512 := by decide

def productData190 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 271, 2, 17, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 307, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 131, 2, 3, 2, 19, 2, 11, 2, 3, 2, 311, 2, 5,
    2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 173, 2, 3, 2, 257, 2, 5, 2, 3, 2, 13,
    2, 29, 2, 3, 2, 5, 2, 61, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 139, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 5, 2, 107, 2, 3, 2, 43, 2, 71, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 281, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 103, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 41, 2, 3, 2, 5, 2, 233, 2, 3, 2, 17, 2, 89,
    2, 3, 2, 163, 2, 251, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 127, 2, 3,
    2, 101, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 211, 2, 3, 2, 151,
    2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 199, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 79, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 239, 2, 67, 2, 3, 2, 11, 2, 29, 2, 3,
    2, 59, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 277, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData190_checked :
    roundedProductCertificate 97282 20462791768377 productData190 = some 20471606013479 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData190_length : productData190.length = 512 := by decide

def productData191 : List ℕ :=
  [2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 23, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 227, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 97, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11,
    2, 53, 2, 3, 2, 5, 2, 223, 2, 3, 2, 47, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2, 179, 2, 5, 2, 3, 2, 0, 2, 181,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 0, 2, 163, 2, 3, 2, 0, 2, 313, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 43, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 83, 2, 3, 2, 61, 2, 167, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 71, 2, 31, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 281, 2, 101, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 11, 2, 47, 2, 3, 2, 233, 2, 5, 2, 3, 2, 263, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 41,
    2, 3, 2, 59, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 7, 2, 61, 2, 3, 2, 11, 2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 89, 2, 3, 2, 127, 2, 19, 2, 3, 2, 31,
    2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 149, 2, 3, 2, 5, 2, 11, 2, 3, 2, 283, 2, 7, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 193, 2, 31, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 23, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 227, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 197, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData191_checked :
    roundedProductCertificate 97794 20471606013479 productData191 = some 20479961061788 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData191_length : productData191.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block12.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData192 : List ℕ :=
  [2, 3, 2, 37, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3,
    2, 29, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 59, 2, 3, 2, 7, 2, 41, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 131, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 257, 2, 3,
    2, 5, 2, 173, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 149, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 137, 2, 3, 2, 0, 2, 23, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 37, 2, 0, 2, 3, 2, 211, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 139, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 241, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 311, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 0, 2, 43, 2, 3, 2, 151, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 47, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5, 2, 101, 2, 3, 2, 11, 2, 13, 2, 3, 2, 29, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 229, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 269, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 293, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 61, 2, 13, 2, 3, 2, 5, 2, 283, 2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 173, 2, 5,
    2, 3, 2, 223, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData192_checked :
    roundedProductCertificate 98306 20479961061788 productData192 = some 20489522672955 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData192_length : productData192.length = 512 := by decide

def productData193 : List ℕ :=
  [2, 7, 2, 17, 2, 3, 2, 5, 2, 37, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 97, 2, 5, 2, 3, 2, 0,
    2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 109, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 61,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 31, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 163, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 53, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 181, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 0, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 167, 2, 3, 2, 5, 2, 97, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 13, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2, 157, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 197, 2, 3, 2, 5, 2, 41, 2, 3, 2, 113, 2, 0, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 229, 2, 3, 2, 17, 2, 53, 2, 3, 2, 131, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 281, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 313, 2, 0, 2, 3, 2, 67, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 53, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 101, 2, 3, 2, 43, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 109, 2, 199, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 71]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData193_checked :
    roundedProductCertificate 98818 20489522672955 productData193 = some 20499453963177 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData193_length : productData193.length = 512 := by decide

def productData194 : List ℕ :=
  [2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 13, 2, 67,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 107, 2, 3, 2, 7, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 277, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 271,
    2, 3, 2, 79, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 37, 2, 3, 2, 0, 2, 29, 2, 3, 2, 19, 2, 5, 2, 3, 2, 151, 2, 191, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 113,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 53, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 137, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37, 2, 0, 2, 3, 2, 251, 2, 11,
    2, 3, 2, 227, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 263, 2, 0, 2, 3,
    2, 83, 2, 5, 2, 3, 2, 0, 2, 131, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 179, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 19, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 113, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 173, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData194_checked :
    roundedProductCertificate 99330 20499453963177 productData194 = some 20509129644922 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData194_length : productData194.length = 512 := by decide

def productData195 : List ℕ :=
  [2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 13, 2, 3, 2, 61, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 59, 2, 23, 2, 3, 2, 191, 2, 5, 2, 3, 2, 283, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 41, 2, 163, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 139, 2, 17, 2, 3, 2, 89, 2, 127, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 257, 2, 3, 2, 17, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 103, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 23, 2, 3, 2, 67, 2, 167,
    2, 3, 2, 7, 2, 71, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 47, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 13, 2, 3, 2, 101, 2, 7, 2, 3, 2, 199,
    2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 59, 2, 3, 2, 223, 2, 0,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 239, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 37, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 73, 2, 113, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 107, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 197, 2, 3, 2, 149, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 37, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 13,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3, 2, 269, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData195_checked :
    roundedProductCertificate 99842 20509129644922 productData195 = some 20516917005752 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData195_length : productData195.length = 512 := by decide

def productData196 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 167, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 137, 2, 233, 2, 3, 2, 29, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 89,
    2, 0, 2, 3, 2, 17, 2, 317, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 229, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 193, 2, 5, 2, 3, 2, 0, 2, 227, 2, 3, 2, 5, 2, 19, 2, 3, 2, 163, 2, 11, 2, 3, 2, 43,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 37, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 239, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 103, 2, 13, 2, 3, 2, 157, 2, 7, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 0, 2, 251, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 107, 2, 3, 2, 17, 2, 0, 2, 3, 2, 101, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 47, 2, 7, 2, 3, 2, 11, 2, 263, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 131, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 19, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 5, 2, 179, 2, 3, 2, 31, 2, 97, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 73, 2, 3, 2, 181, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 13, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData196_checked :
    roundedProductCertificate 100354 20516917005752 productData196 = some 20526097385121 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData196_length : productData196.length = 512 := by decide

def productData197 : List ℕ :=
  [2, 13, 2, 3, 2, 19, 2, 149, 2, 3, 2, 7, 2, 281, 2, 3, 2, 79, 2, 5, 2, 3, 2, 233, 2, 7, 2, 3, 2, 5, 2, 163,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 193, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 157, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 31, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 241, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 71, 2, 5, 2, 3, 2, 23, 2, 79, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 139, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 211, 2, 53, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 271, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 127, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 67, 2, 29, 2, 3, 2, 137, 2, 5, 2, 3, 2, 103,
    2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 109, 2, 131, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 199, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 11, 2, 0, 2, 3, 2, 19, 2, 107, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 79, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 167, 2, 17, 2, 3, 2, 5, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData197_checked :
    roundedProductCertificate 100866 20526097385121 productData197 = some 20535434999054 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData197_length : productData197.length = 512 := by decide

def productData198 : List ℕ :=
  [2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 53, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 37, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19,
    2, 61, 2, 3, 2, 229, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71, 2, 241, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 17,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 7, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 59, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 173, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 19, 2, 3, 2, 283, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 307, 2, 3, 2, 13, 2, 151, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 59, 2, 277, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 19, 2, 293, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 23, 2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 61, 2, 3, 2, 17, 2, 5, 2, 3, 2, 29, 2, 19, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 79, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 179, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 37, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 139, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData198_checked :
    roundedProductCertificate 101378 20535434999054 productData198 = some 20544933717875 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData198_length : productData198.length = 512 := by decide

def productData199 : List ℕ :=
  [2, 0, 2, 11, 2, 3, 2, 19, 2, 7, 2, 3, 2, 181, 2, 5, 2, 3, 2, 101, 2, 223, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 227, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 97, 2, 3, 2, 269, 2, 43,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 0, 2, 79, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 257, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 67, 2, 0, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 103, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 41, 2, 109, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 71, 2, 3, 2, 83, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 179,
    2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 151, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 293, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 29, 2, 3, 2, 233, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 263, 2, 3, 2, 11, 2, 101, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 29, 2, 53, 2, 3, 2, 7, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 167, 2, 23, 2, 3, 2, 11, 2, 37, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData199_checked :
    roundedProductCertificate 101890 20544933717875 productData199 = some 20554792972669 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData199_length : productData199.length = 512 := by decide

def productData200 : List ℕ :=
  [2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 89, 2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 79, 2, 3,
    2, 19, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 113, 2, 17, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2, 31, 2, 3, 2, 157, 2, 0, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5, 2, 67, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0, 2, 173, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 89, 2, 11, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 197, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 251, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29,
    2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 271, 2, 3, 2, 13, 2, 5, 2, 3, 2, 59, 2, 139,
    2, 3, 2, 5, 2, 43, 2, 3, 2, 17, 2, 19, 2, 3, 2, 71, 2, 7, 2, 3, 2, 127, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3,
    2, 5, 2, 211, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 223, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 229, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 163, 2, 3, 2, 73, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 137, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData200_checked :
    roundedProductCertificate 102402 20554792972669 productData200 = some 20563405501906 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData200_length : productData200.length = 512 := by decide

def productData201 : List ℕ :=
  [2, 3, 2, 97, 2, 101, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 311, 2, 113, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 149, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 181, 2, 7, 2, 3, 2, 5, 2, 127, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 239,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 269, 2, 3, 2, 197, 2, 7, 2, 3, 2, 11, 2, 167, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 257, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 131, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 23, 2, 97, 2, 3, 2, 5, 2, 7, 2, 3, 2, 101, 2, 0, 2, 3, 2, 281, 2, 13, 2, 3, 2, 151, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 29, 2, 3, 2, 43, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 37, 2, 5, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 29, 2, 11, 2, 3, 2, 0, 2, 233, 2, 3, 2, 109, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 23, 2, 223, 2, 3, 2, 79, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 7, 2, 61, 2, 3, 2, 139, 2, 11, 2, 3, 2, 179, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 277, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 191, 2, 0, 2, 3, 2, 13, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 181, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41,
    2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 167, 2, 5, 2, 3, 2, 19, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData201_checked :
    roundedProductCertificate 102914 20563405501906 productData201 = some 20570979913646 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData201_length : productData201.length = 512 := by decide

def productData202 : List ℕ :=
  [2, 59, 2, 293, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 307, 2, 3, 2, 157, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 239, 2, 37,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 89, 2, 3, 2, 0, 2, 17, 2, 3, 2, 61, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 211, 2, 313, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 173, 2, 3, 2, 11, 2, 31, 2, 3, 2, 37, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 83, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 199, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 137, 2, 37, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 13, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 227, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 13, 2, 3, 2, 31, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 157,
    2, 3, 2, 59, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 271, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 47, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 113, 2, 29, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 283, 2, 3, 2, 5, 2, 0, 2, 3, 2, 241, 2, 7,
    2, 3, 2, 109, 2, 73, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 107, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 29, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 103, 2, 3, 2, 43, 2, 37, 2, 3, 2, 23]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData202_checked :
    roundedProductCertificate 103426 20570979913646 productData202 = some 20578520951612 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData202_length : productData202.length = 512 := by decide

def productData203 : List ℕ :=
  [2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 173, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 199, 2, 3, 2, 29, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 41, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31,
    2, 101, 2, 3, 2, 5, 2, 11, 2, 3, 2, 223, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 73, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 31, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 79, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 89, 2, 13, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 137,
    2, 3, 2, 17, 2, 41, 2, 3, 2, 127, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 101, 2, 5, 2, 3, 2, 103, 2, 151, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 241,
    2, 3, 2, 11, 2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 47, 2, 139, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 131, 2, 3, 2, 263, 2, 193, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 181, 2, 3, 2, 71, 2, 19, 2, 3, 2, 7, 2, 149]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData203_checked :
    roundedProductCertificate 103938 20578520951612 productData203 = some 20587808536672 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData203_length : productData203.length = 512 := by decide

def productData204 : List ℕ :=
  [2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 191, 2, 0, 2, 3,
    2, 163, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 31, 2, 7, 2, 3, 2, 13, 2, 41, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 19, 2, 127, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 107, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 31, 2, 3, 2, 17, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 73,
    2, 13, 2, 3, 2, 5, 2, 233, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 269,
    2, 3, 2, 5, 2, 227, 2, 3, 2, 0, 2, 229, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 311, 2, 163, 2, 3, 2, 281, 2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 79,
    2, 3, 2, 41, 2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 29, 2, 3, 2, 13,
    2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 239, 2, 7, 2, 3, 2, 317, 2, 11,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 101, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 103, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData204_checked :
    roundedProductCertificate 104450 20587808536672 productData204 = some 20597642117137 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData204_length : productData204.length = 512 := by decide

def productData205 : List ℕ :=
  [2, 43, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 113, 2, 3, 2, 61, 2, 277, 2, 3, 2, 0, 2, 67, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 17, 2, 3, 2, 73, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 31, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 179, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 227, 2, 61, 2, 3, 2, 0, 2, 89, 2, 3, 2, 257, 2, 5, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 71, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 7, 2, 103, 2, 3, 2, 0, 2, 251, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 107, 2, 3, 2, 5,
    2, 293, 2, 3, 2, 37, 2, 11, 2, 3, 2, 59, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 43, 2, 139, 2, 3, 2, 0, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 67, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 127, 2, 3, 2, 7, 2, 211, 2, 3, 2, 71, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 53, 2, 13,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 137, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 167,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 109, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 271, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 59, 2, 3, 2, 0, 2, 97, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 163, 2, 263, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData205_checked :
    roundedProductCertificate 104962 20597642117137 productData205 = some 20605668323196 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData205_length : productData205.length = 512 := by decide

def productData206 : List ℕ :=
  [2, 5, 2, 3, 2, 11, 2, 313, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 59, 2, 7, 2, 3, 2, 0, 2, 283, 2, 3, 2, 0, 2, 5, 2, 3, 2, 229,
    2, 193, 2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 73, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 149, 2, 89, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 157, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 251, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 37, 2, 3, 2, 61, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 43, 2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 139, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 67,
    2, 3, 2, 47, 2, 241, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 23, 2, 3,
    2, 97, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 151, 2, 11, 2, 3, 2, 37,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 239, 2, 3, 2, 113, 2, 0, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 137, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 53, 2, 101, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 131, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData206_checked :
    roundedProductCertificate 105474 20605668323196 productData206 = some 20614050798385 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData206_length : productData206.length = 512 := by decide

def productData207 : List ℕ :=
  [2, 3, 2, 13, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 71, 2, 3, 2, 11, 2, 227, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 97, 2, 3, 2, 5, 2, 229, 2, 3, 2, 0, 2, 0, 2, 3, 2, 107, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 17, 2, 3, 2, 13, 2, 73, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37, 2, 43,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 277, 2, 13, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 211, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 179, 2, 3, 2, 101, 2, 19, 2, 3, 2, 83, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 89,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3, 2, 17, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 41, 2, 3, 2, 5, 2, 23, 2, 3, 2, 131,
    2, 0, 2, 3, 2, 181, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 113, 2, 3, 2, 7,
    2, 43, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 191, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 103, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 71, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 233, 2, 13, 2, 3, 2, 0, 2, 83, 2, 3, 2, 109, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData207_checked :
    roundedProductCertificate 105986 20614050798385 productData207 = some 20622976618057 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData207_length : productData207.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block13.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData208 : List ℕ :=
  [2, 281, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 43, 2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 307,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 47, 2, 3, 2, 127, 2, 5, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 19, 2, 17, 2, 3, 2, 197, 2, 11, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 13, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 107, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 173, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 241, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 23, 2, 3, 2, 269, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2, 7, 2, 3, 2, 223,
    2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 317, 2, 47, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 59,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 89, 2, 139, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 229, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 83, 2, 3, 2, 97, 2, 0, 2, 3, 2, 11, 2, 67, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData208_checked :
    roundedProductCertificate 106498 20622976618057 productData208 = some 20632057850289 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData208_length : productData208.length = 512 := by decide

def productData209 : List ℕ :=
  [2, 113, 2, 3, 2, 5, 2, 103, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 11,
    2, 3, 2, 5, 2, 167, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 151, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 17, 2, 3, 2, 173, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 23, 2, 43, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 149, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 19, 2, 307, 2, 3, 2, 109, 2, 7, 2, 3, 2, 83, 2, 5, 2, 3, 2, 13, 2, 101, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 23, 2, 3, 2, 47, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 179, 2, 3, 2, 5, 2, 0, 2, 3, 2, 157, 2, 7,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 283, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 67, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 17, 2, 3, 2, 31, 2, 19, 2, 3, 2, 41,
    2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 239, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 181, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 101, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 167, 2, 73, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 211, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 233, 2, 3, 2, 163, 2, 13, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 139, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 11, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2, 47,
    2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 193, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData209_checked :
    roundedProductCertificate 107010 20632057850289 productData209 = some 20639369827693 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData209_length : productData209.length = 512 := by decide

def productData210 : List ℕ :=
  [2, 3, 2, 5, 2, 7, 2, 3, 2, 293, 2, 191, 2, 3, 2, 53, 2, 31, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13, 2, 131, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 29, 2, 0, 2, 3, 2, 263, 2, 7, 2, 3, 2, 97, 2, 5, 2, 3, 2, 179, 2, 0, 2, 3, 2, 5,
    2, 271, 2, 3, 2, 11, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 0, 2, 281, 2, 3, 2, 13, 2, 43, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 83, 2, 7, 2, 3, 2, 11, 2, 199, 2, 3, 2, 23, 2, 5, 2, 3, 2, 67, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7,
    2, 257, 2, 3, 2, 0, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 163, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 277, 2, 5, 2, 3, 2, 197, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 67, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 131, 2, 5, 2, 3, 2, 137, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 269, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 233, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 29, 2, 31, 2, 3, 2, 5, 2, 311, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 41, 2, 3, 2, 89, 2, 47, 2, 3, 2, 107, 2, 5, 2, 3, 2, 101,
    2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 83, 2, 3, 2, 11, 2, 7, 2, 3, 2, 79, 2, 5, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData210_checked :
    roundedProductCertificate 107522 20639369827693 productData210 = some 20647412537257 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData210_length : productData210.length = 512 := by decide

def productData211 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 103, 2, 167, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 67, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 71, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 19, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 251, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 257, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 241, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 103, 2, 3, 2, 29,
    2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 89, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 149, 2, 5, 2, 3, 2, 13, 2, 127, 2, 3, 2, 5, 2, 131, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 97, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 307, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 283, 2, 107, 2, 3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 43, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 181, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 79, 2, 31, 2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 83,
    2, 3, 2, 5, 2, 157, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 47, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 311, 2, 0, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData211_checked :
    roundedProductCertificate 108034 20647412537257 productData211 = some 20656185160953 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData211_length : productData211.length = 512 := by decide

def productData212 : List ℕ :=
  [2, 19, 2, 3, 2, 73, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 151, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 31, 2, 5, 2, 3, 2, 131, 2, 223, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 313, 2, 17, 2, 3, 2, 47, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 179, 2, 5, 2, 3, 2, 193, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 271, 2, 109,
    2, 3, 2, 0, 2, 191, 2, 3, 2, 251, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 73, 2, 3, 2, 71, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 227, 2, 3, 2, 19,
    2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 61, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 181, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 53, 2, 233, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 127, 2, 31, 2, 3, 2, 5, 2, 89, 2, 3, 2, 17, 2, 199, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 97, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 59, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 61, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 13, 2, 107, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 167, 2, 3, 2, 5, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData212_checked :
    roundedProductCertificate 108546 20656185160953 productData212 = some 20664728486915 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData212_length : productData212.length = 512 := by decide

def productData213 : List ℕ :=
  [2, 3, 2, 191, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 43, 2, 127, 2, 3, 2, 0, 2, 79, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 29, 2, 61, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 173, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 41, 2, 3,
    2, 13, 2, 137, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 149,
    2, 11, 2, 3, 2, 239, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 313, 2, 3, 2, 11, 2, 29, 2, 3, 2, 107, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 293, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 281, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 53, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 43, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 0, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 139, 2, 3, 2, 0, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37,
    2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 73, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 103, 2, 3, 2, 223, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 41, 2, 97, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 71, 2, 5, 2, 3, 2, 89, 2, 331, 2, 3, 2, 5, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData213_checked :
    roundedProductCertificate 109058 20664728486915 productData213 = some 20673615216055 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData213_length : productData213.length = 512 := by decide

def productData214 : List ℕ :=
  [2, 7, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 127,
    2, 13, 2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 17,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 229, 2, 43, 2, 3, 2, 7,
    2, 163, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 113, 2, 3, 2, 179, 2, 197,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 13, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 151, 2, 3, 2, 7, 2, 311, 2, 3, 2, 101, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 59, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 193, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 0, 2, 61, 2, 3, 2, 5, 2, 181, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 131, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 211, 2, 47, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 277, 2, 3, 2, 17, 2, 5, 2, 3, 2, 71, 2, 109, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 29, 2, 317, 2, 3, 2, 41, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 269, 2, 0, 2, 3, 2, 47, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 167, 2, 3, 2, 157, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData214_checked :
    roundedProductCertificate 109570 20673615216055 productData214 = some 20681899554620 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData214_length : productData214.length = 512 := by decide

def productData215 : List ℕ :=
  [2, 0, 2, 3, 2, 283, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2, 103, 2, 3, 2, 149, 2, 29,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 241, 2, 3, 2, 83, 2, 11, 2, 3,
    2, 23, 2, 13, 2, 3, 2, 59, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 29, 2, 7, 2, 3, 2, 17,
    2, 239, 2, 3, 2, 0, 2, 5, 2, 3, 2, 251, 2, 101, 2, 3, 2, 5, 2, 263, 2, 3, 2, 7, 2, 193, 2, 3, 2, 191, 2, 11,
    2, 3, 2, 307, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 41, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 71, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 7, 2, 3, 2, 73, 2, 5,
    2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 163, 2, 211, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 5, 2, 23, 2, 3, 2, 17, 2, 7, 2, 3, 2, 167, 2, 59, 2, 3, 2, 101, 2, 5, 2, 3, 2, 53, 2, 113,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 41, 2, 3, 2, 109, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 179, 2, 3, 2, 19, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 61, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 313, 2, 0, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 29, 2, 79, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 107, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 227, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData215_checked :
    roundedProductCertificate 110082 20681899554620 productData215 = some 20689208214822 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData215_length : productData215.length = 512 := by decide

def productData216 : List ℕ :=
  [2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 317, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 239,
    2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 151, 2, 3, 2, 17, 2, 71,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 31, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 19, 2, 3, 2, 53, 2, 7, 2, 3,
    2, 263, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 37, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 257, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 47, 2, 3, 2, 139, 2, 5,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 101, 2, 3, 2, 179, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 137, 2, 3, 2, 23, 2, 271, 2, 3, 2, 199, 2, 5, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 59, 2, 0, 2, 3, 2, 29, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 173, 2, 3, 2, 43, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 197, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 181, 2, 3, 2, 7, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 13, 2, 29, 2, 3, 2, 41, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 19, 2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 293, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 109, 2, 31,
    2, 3, 2, 277, 2, 113, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 241, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData216_checked :
    roundedProductCertificate 110594 20689208214822 productData216 = some 20697422401032 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData216_length : productData216.length = 512 := by decide

def productData217 : List ℕ :=
  [2, 137, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 11, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 29, 2, 3, 2, 89, 2, 13, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 107, 2, 5, 2, 3, 2, 73, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 251, 2, 3, 2, 17, 2, 11, 2, 3,
    2, 61, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 173, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 0, 2, 3, 2, 71, 2, 31, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 223, 2, 3, 2, 257, 2, 19, 2, 3, 2, 11, 2, 109, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79, 2, 157, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 163,
    2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 193,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 127, 2, 3, 2, 31, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 17, 2, 101, 2, 3, 2, 37, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 59, 2, 3, 2, 5, 2, 227,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 19, 2, 5, 2, 3, 2, 41, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 229, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 71, 2, 3, 2, 5, 2, 331, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 281, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 241, 2, 3,
    2, 7, 2, 151, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 233, 2, 3, 2, 0, 2, 239, 2, 3, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData217_checked :
    roundedProductCertificate 111106 20697422401032 productData217 = some 20705230143294 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData217_length : productData217.length = 512 := by decide

def productData218 : List ℕ :=
  [2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 97, 2, 311,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 181, 2, 29, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 67, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 37, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 19, 2, 3, 2, 131, 2, 5,
    2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 73, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 97,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 53, 2, 3, 2, 127, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 149, 2, 317, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 17, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 173, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 23, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 103, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 41, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 113, 2, 5, 2, 3, 2, 53, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47,
    2, 31, 2, 3, 2, 7, 2, 101, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 199, 2, 181, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 197, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 0, 2, 3, 2, 5, 2, 191, 2, 3, 2, 0, 2, 11, 2, 3, 2, 31, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData218_checked :
    roundedProductCertificate 111618 20705230143294 productData218 = some 20713745385790 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData218_length : productData218.length = 512 := by decide

def productData219 : List ℕ :=
  [2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 127, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 19, 2, 59, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 223, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2, 43, 2, 7, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 293, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 107, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 131, 2, 3, 2, 19, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 11,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 283, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 313, 2, 37, 2, 3, 2, 103, 2, 5, 2, 3, 2, 109, 2, 41, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 167, 2, 71, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 17, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 229, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 139, 2, 11, 2, 3, 2, 107, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 137, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 197, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 59,
    2, 3, 2, 37, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 131, 2, 43, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 241, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0,
    2, 103, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 109, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 23, 2, 163, 2, 3, 2, 7, 2, 73, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData219_checked :
    roundedProductCertificate 112130 20713745385790 productData219 = some 20721673497474 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData219_length : productData219.length = 512 := by decide

def productData220 : List ℕ :=
  [2, 0, 2, 5, 2, 3, 2, 127, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 0, 2, 3, 2, 61, 2, 307, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 281, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 251, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 41, 2, 269, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 139, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 137, 2, 47, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 0, 2, 43, 2, 3, 2, 149, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 37, 2, 3, 2, 101, 2, 7, 2, 3, 2, 257, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3,
    2, 5, 2, 53, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 59, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 13, 2, 3, 2, 157, 2, 5, 2, 3, 2, 7, 2, 79, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 11, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 179, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 37,
    2, 83, 2, 3, 2, 0, 2, 173, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 103, 2, 19,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 131, 2, 3, 2, 7,
    2, 167, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData220_checked :
    roundedProductCertificate 112642 20721673497474 productData220 = some 20730482083692 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData220_length : productData220.length = 512 := by decide

def productData221 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 79, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 43, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 199, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 269,
    2, 109, 2, 3, 2, 5, 2, 37, 2, 3, 2, 53, 2, 191, 2, 3, 2, 7, 2, 13, 2, 3, 2, 227, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 193, 2, 277, 2, 3, 2, 19, 2, 137, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 7, 2, 263, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 71, 2, 149, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 151, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 19, 2, 23, 2, 3, 2, 0, 2, 29, 2, 3, 2, 101, 2, 5, 2, 3, 2, 31, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 41, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 83, 2, 3, 2, 5, 2, 0, 2, 3, 2, 233, 2, 53,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 283, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 223, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 61, 2, 3, 2, 5, 2, 107, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 271, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 337,
    2, 3, 2, 137, 2, 5, 2, 3, 2, 53, 2, 13, 2, 3, 2, 5, 2, 97, 2, 3, 2, 0, 2, 29, 2, 3, 2, 11, 2, 47, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 103, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 199, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 89, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData221_checked :
    roundedProductCertificate 113154 20730482083692 productData221 = some 20737613903188 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData221_length : productData221.length = 512 := by decide

def productData222 : List ℕ :=
  [2, 3, 2, 197, 2, 71, 2, 3, 2, 5, 2, 19, 2, 3, 2, 79, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 67, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 107, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 31, 2, 317, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 89, 2, 67, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 257, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 11, 2, 31, 2, 3, 2, 13, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 263, 2, 47, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 37, 2, 3, 2, 11, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 0, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 293, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 31, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 173, 2, 3, 2, 23, 2, 0, 2, 3, 2, 113,
    2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 59, 2, 13,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 167, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 271, 2, 3, 2, 5, 2, 71, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 53, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 139, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 61, 2, 19, 2, 3, 2, 311, 2, 157, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 211, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData222_checked :
    roundedProductCertificate 113666 20737613903188 productData222 = some 20745442604604 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData222_length : productData222.length = 512 := by decide

def productData223 : List ℕ :=
  [2, 13, 2, 227, 2, 3, 2, 5, 2, 89, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 181, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 103, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2, 23,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 61, 2, 3, 2, 11, 2, 0, 2, 3, 2, 163, 2, 5, 2, 3, 2, 0, 2, 229, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 23, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5,
    2, 151, 2, 3, 2, 0, 2, 79, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 109, 2, 0, 2, 3, 2, 29, 2, 41, 2, 3, 2, 173, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 0, 2, 23, 2, 3, 2, 107, 2, 5, 2, 3, 2, 11, 2, 73, 2, 3, 2, 5, 2, 139, 2, 3, 2, 7,
    2, 233, 2, 3, 2, 0, 2, 191, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 41, 2, 11,
    2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 193, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 29, 2, 3,
    2, 0, 2, 113, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 239, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 43, 2, 307, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 71, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 97, 2, 109, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 149, 2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 83, 2, 5,
    2, 3, 2, 79, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 73, 2, 5, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData223_checked :
    roundedProductCertificate 114178 20745442604604 productData223 = some 20753238731632 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData223_length : productData223.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block14.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData224 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 19, 2, 3, 2, 251, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 89,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 31, 2, 17, 2, 3, 2, 7, 2, 179, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 79, 2, 3, 2, 191, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 7, 2, 199, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 43, 2, 3, 2, 331, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 313, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 131, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 151, 2, 0,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 281, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 137, 2, 3,
    2, 7, 2, 71, 2, 3, 2, 139, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 23,
    2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 47,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 37, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 11, 2, 103, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2, 11, 2, 3, 2, 179, 2, 0, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 59, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 97, 2, 13, 2, 3, 2, 5, 2, 113, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 5, 2, 149, 2, 3, 2, 11, 2, 0, 2, 3, 2, 229, 2, 127, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData224_checked :
    roundedProductCertificate 114690 20753238731632 productData224 = some 20760823155171 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData224_length : productData224.length = 512 := by decide

def productData225 : List ℕ :=
  [2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 139, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 79, 2, 3, 2, 5,
    2, 73, 2, 3, 2, 13, 2, 19, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 29, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 43, 2, 3, 2, 113, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 257,
    2, 3, 2, 167, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 131, 2, 3, 2, 5, 2, 211, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 89, 2, 5, 2, 3, 2, 241, 2, 67, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 263,
    2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 17, 2, 23, 2, 3, 2, 53, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 71, 2, 331, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 31, 2, 3, 2, 43, 2, 227, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 163, 2, 3, 2, 0, 2, 47, 2, 3, 2, 7, 2, 41, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 193, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 197, 2, 3, 2, 11, 2, 5, 2, 3, 2, 109,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 103, 2, 3, 2, 131, 2, 5, 2, 3, 2, 0, 2, 29,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 127, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 251, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData225_checked :
    roundedProductCertificate 115202 20760823155171 productData225 = some 20768197341207 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData225_length : productData225.length = 512 := by decide

def productData226 : List ℕ :=
  [2, 5, 2, 7, 2, 3, 2, 97, 2, 31, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5,
    2, 283, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 89, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 179, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 109, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 11, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 191,
    2, 269, 2, 3, 2, 23, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 61, 2, 0, 2, 3, 2, 89, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 193, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 311, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 181, 2, 157, 2, 3, 2, 0, 2, 29, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 43, 2, 17, 2, 3, 2, 277, 2, 5,
    2, 3, 2, 37, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 83, 2, 151, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 19, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 17,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 223, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 79, 2, 3, 2, 251, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData226_checked :
    roundedProductCertificate 115714 20768197341207 productData226 = some 20777335428480 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData226_length : productData226.length = 512 := by decide

def productData227 : List ℕ :=
  [2, 71, 2, 3, 2, 47, 2, 13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 233, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 103, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 17, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 107, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 293,
    2, 89, 2, 3, 2, 61, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 317, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 307,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 181, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 239, 2, 5, 2, 3, 2, 17, 2, 43, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7,
    2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 173, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 23,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 269, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 7, 2, 113, 2, 3, 2, 0, 2, 263, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 13, 2, 109, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 229, 2, 41, 2, 3, 2, 11, 2, 17, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 0, 2, 73, 2, 3, 2, 5, 2, 23, 2, 3, 2, 31, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 29,
    2, 11, 2, 3, 2, 5, 2, 277, 2, 3, 2, 139, 2, 13, 2, 3, 2, 7, 2, 223, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 157, 2, 31, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 127, 2, 3, 2, 19, 2, 0, 2, 3, 2, 151, 2, 5, 2, 3, 2, 113, 2, 0, 2, 3, 2, 5, 2, 107]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData227_checked :
    roundedProductCertificate 116226 20777335428480 productData227 = some 20784472106868 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData227_length : productData227.length = 512 := by decide

def productData228 : List ℕ :=
  [2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 313, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 23, 2, 17, 2, 3, 2, 31, 2, 13, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 271,
    2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 199, 2, 5, 2, 3, 2, 0, 2, 197, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 331, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 137, 2, 23, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 179, 2, 3, 2, 41, 2, 7, 2, 3, 2, 11,
    2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 337, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 107, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 79, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 167, 2, 3, 2, 0, 2, 11, 2, 3, 2, 47, 2, 17, 2, 3, 2, 191, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 181, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 173,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 31, 2, 193, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 163, 2, 233, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 251,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData228_checked :
    roundedProductCertificate 116738 20784472106868 productData228 = some 20792467996602 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData228_length : productData228.length = 512 := by decide

def productData229 : List ℕ :=
  [2, 0, 2, 37, 2, 3, 2, 7, 2, 0, 2, 3, 2, 149, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0,
    2, 17, 2, 3, 2, 19, 2, 53, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 7,
    2, 3, 2, 17, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 271, 2, 3,
    2, 43, 2, 239, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 241, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13,
    2, 107, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 113, 2, 137,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 257, 2, 67, 2, 3, 2, 5, 2, 73, 2, 3, 2, 23, 2, 101, 2, 3, 2, 7, 2, 11, 2, 3, 2, 79,
    2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 293, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 7, 2, 3, 2, 211, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 19, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 89,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 307, 2, 31, 2, 3, 2, 59, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 337, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 79, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 47, 2, 0, 2, 3, 2, 71, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 97, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 137, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 23, 2, 281, 2, 3, 2, 19, 2, 5, 2, 3, 2, 73, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData229_checked :
    roundedProductCertificate 117250 20792467996602 productData229 = some 20800254785301 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData229_length : productData229.length = 512 := by decide

def productData230 : List ℕ :=
  [2, 0, 2, 3, 2, 13, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 13,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 59, 2, 3,
    2, 17, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 191, 2, 3, 2, 0, 2, 67, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 311, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 157, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 37, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 7, 2, 3, 2, 79, 2, 13, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 179, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 127, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 197, 2, 3, 2, 199, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 107, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 97,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 37, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 13, 2, 0,
    2, 3, 2, 5, 2, 263, 2, 3, 2, 269, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 89, 2, 5, 2, 3, 2, 83, 2, 7, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 41, 2, 19, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 173, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 73, 2, 0, 2, 3, 2, 181, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 191, 2, 137, 2, 3, 2, 5, 2, 7, 2, 3, 2, 317,
    2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 227, 2, 3, 2, 101, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData230_checked :
    roundedProductCertificate 117762 20800254785301 productData230 = some 20808540897630 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData230_length : productData230.length = 512 := by decide

def productData231 : List ℕ :=
  [2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 281, 2, 17, 2, 3,
    2, 7, 2, 193, 2, 3, 2, 13, 2, 5, 2, 3, 2, 179, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 241, 2, 73, 2, 3, 2, 17,
    2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 71, 2, 3, 2, 0, 2, 7, 2, 3, 2, 41, 2, 0,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 197, 2, 0, 2, 3,
    2, 167, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 79, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 17, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 257, 2, 3, 2, 11, 2, 109, 2, 3, 2, 47, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 71, 2, 163, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37, 2, 31, 2, 3, 2, 7, 2, 23, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 113, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 103, 2, 5, 2, 3, 2, 7, 2, 53,
    2, 3, 2, 5, 2, 139, 2, 3, 2, 0, 2, 7, 2, 3, 2, 283, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 5, 2, 233, 2, 3, 2, 7, 2, 0, 2, 3, 2, 83, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 313, 2, 3, 2, 97, 2, 0, 2, 3, 2, 31, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 107, 2, 3, 2, 53, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 227,
    2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 149,
    2, 3, 2, 0, 2, 103, 2, 3, 2, 113, 2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 7, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData231_checked :
    roundedProductCertificate 118274 20808540897630 productData231 = some 20815388017978 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData231_length : productData231.length = 512 := by decide

def productData232 : List ℕ :=
  [2, 0, 2, 11, 2, 3, 2, 211, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 131,
    2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 331, 2, 0, 2, 3, 2, 5, 2, 151, 2, 3, 2, 23, 2, 0, 2, 3, 2, 17, 2, 157,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 11, 2, 53, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 109, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 83, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 337, 2, 13, 2, 3, 2, 0, 2, 271, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 5, 2, 11, 2, 3, 2, 257, 2, 7, 2, 3, 2, 19, 2, 127, 2, 3, 2, 59, 2, 5, 2, 3, 2, 11,
    2, 61, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 41, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 193, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 19, 2, 311, 2, 3, 2, 23, 2, 7, 2, 3, 2, 139, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 109,
    2, 3, 2, 11, 2, 283, 2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 269, 2, 3,
    2, 13, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 199,
    2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 97, 2, 5, 2, 3, 2, 29, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 239, 2, 19, 2, 3,
    2, 0, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 181, 2, 101, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData232_checked :
    roundedProductCertificate 118786 20815388017978 productData232 = some 20823258132118 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData232_length : productData232.length = 512 := by decide

def productData233 : List ℕ :=
  [2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 229, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 11, 2, 131, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 11, 2, 3, 2, 277, 2, 0, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 139, 2, 3, 2, 5, 2, 97, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 307, 2, 5,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 17, 2, 67, 2, 3, 2, 5, 2, 193, 2, 3, 2, 11, 2, 37, 2, 3, 2, 157, 2, 163, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 73, 2, 0, 2, 3, 2, 127, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 107, 2, 47,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 173, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 197, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 0, 2, 59, 2, 3, 2, 41, 2, 199, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 37, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 181, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19,
    2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 11,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 13, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 229, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 47, 2, 3, 2, 23, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData233_checked :
    roundedProductCertificate 119298 20823258132118 productData233 = some 20830572771083 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData233_length : productData233.length = 512 := by decide

def productData234 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 293, 2, 0, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 67, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 313, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 0, 2, 113, 2, 3, 2, 47, 2, 13, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 31, 2, 277, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 0, 2, 3, 2, 139, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 43, 2, 3, 2, 0, 2, 257, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 271, 2, 5, 2, 3, 2, 211, 2, 19, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 167, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 83, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 19, 2, 17, 2, 3, 2, 317, 2, 5, 2, 3, 2, 137, 2, 53, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107,
    2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 263, 2, 0,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 239, 2, 3, 2, 23, 2, 0, 2, 3,
    2, 109, 2, 251, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 53,
    2, 241, 2, 3, 2, 11, 2, 5, 2, 3, 2, 127, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 13,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 23, 2, 3, 2, 79, 2, 0, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData234_checked :
    roundedProductCertificate 119810 20830572771083 productData234 = some 20838382113143 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData234_length : productData234.length = 512 := by decide

def productData235 : List ℕ :=
  [2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2, 151, 2, 0, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 23, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 131, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 347, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 83, 2, 3, 2, 29, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7,
    2, 23, 2, 3, 2, 5, 2, 163, 2, 3, 2, 11, 2, 7, 2, 3, 2, 179, 2, 53, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 211,
    2, 3, 2, 5, 2, 71, 2, 3, 2, 7, 2, 101, 2, 3, 2, 13, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 191, 2, 13, 2, 3, 2, 11, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 149, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 17, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 83, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 29, 2, 103, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 223, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 67, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 0, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 157, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 269, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 199, 2, 3, 2, 113, 2, 7, 2, 3,
    2, 107, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData235_checked :
    roundedProductCertificate 120322 20838382113143 productData235 = some 20845985925749 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData235_length : productData235.length = 512 := by decide

def productData236 : List ℕ :=
  [2, 5, 2, 3, 2, 149, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 11, 2, 19, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 109, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0,
    2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 73,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 137, 2, 19, 2, 3, 2, 0, 2, 311, 2, 3, 2, 337, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 127, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 83, 2, 11, 2, 3, 2, 347, 2, 5, 2, 3, 2, 163, 2, 281, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 59, 2, 89, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 97,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 179, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 61, 2, 3, 2, 53, 2, 47, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 241, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 41, 2, 3, 2, 31, 2, 263, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 173, 2, 3, 2, 13, 2, 23, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 101, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 67, 2, 71, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData236_checked :
    roundedProductCertificate 120834 20845985925749 productData236 = some 20854079467230 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData236_length : productData236.length = 512 := by decide

def productData237 : List ℕ :=
  [2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 157, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 233, 2, 3, 2, 17, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 167,
    2, 317, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 29, 2, 3, 2, 31, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 331, 2, 3, 2, 29, 2, 41, 2, 3, 2, 0, 2, 31, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 137, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 197, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 0, 2, 61, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17,
    2, 277, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 103, 2, 5, 2, 3, 2, 11, 2, 239, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 89, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 281, 2, 5, 2, 3, 2, 271, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 11, 2, 3, 2, 0,
    2, 131, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 41,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 53, 2, 3, 2, 5, 2, 211, 2, 3, 2, 7, 2, 109, 2, 3, 2, 313, 2, 11, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 263, 2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 193, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 31, 2, 349, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 181, 2, 3, 2, 61, 2, 43, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 29, 2, 23, 2, 3, 2, 5, 2, 73, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData237_checked :
    roundedProductCertificate 121346 20854079467230 productData237 = some 20861457397923 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData237_length : productData237.length = 512 := by decide

def productData238 : List ℕ :=
  [2, 233, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 17, 2, 3, 2, 7, 2, 307, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 13, 2, 139, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 61, 2, 3, 2, 197, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 283, 2, 5, 2, 3, 2, 11, 2, 223, 2, 3, 2, 5,
    2, 199, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 59, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 83, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 0, 2, 29, 2, 3, 2, 97, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 67, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 151, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 61, 2, 5, 2, 3, 2, 19, 2, 71, 2, 3, 2, 5, 2, 89, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 251, 2, 13, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 179, 2, 3, 2, 103, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 149, 2, 3, 2, 71, 2, 5, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 31, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData238_checked :
    roundedProductCertificate 121858 20861457397923 productData238 = some 20869659590004 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData238_length : productData238.length = 512 := by decide

def productData239 : List ℕ :=
  [2, 79, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 109, 2, 3, 2, 167, 2, 163, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 191, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 139, 2, 151, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 0, 2, 347, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 101, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 19, 2, 0, 2, 3, 2, 181, 2, 283, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 23, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 43,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 47, 2, 3,
    2, 149, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 173,
    2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 241, 2, 61, 2, 3, 2, 5, 2, 67, 2, 3, 2, 13, 2, 11, 2, 3, 2, 79, 2, 7,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 277, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 139, 2, 3, 2, 0, 2, 0, 2, 3, 2, 131, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 293, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 59, 2, 3, 2, 199, 2, 5,
    2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 37, 2, 3, 2, 227, 2, 127, 2, 3, 2, 191, 2, 5, 2, 3,
    2, 0, 2, 263, 2, 3, 2, 5, 2, 0, 2, 3, 2, 113, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0,
    2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 103, 2, 11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData239_checked :
    roundedProductCertificate 122370 20869659590004 productData239 = some 20877149595152 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData239_length : productData239.length = 512 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ProductData/Block15.lean` -/

section


/-! Generated proper-divisor data. Every certificate is kernel checked. -/



def productData240 : List ℕ :=
  [2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 59, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 89, 2, 19, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 0, 2, 83, 2, 3, 2, 7, 2, 0, 2, 3, 2, 269, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 37, 2, 0, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 61, 2, 3, 2, 41,
    2, 71, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 109, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 23,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 83, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 257, 2, 3,
    2, 307, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 59, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 107, 2, 3, 2, 79, 2, 29, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 199, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 349, 2, 17, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 149, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 0, 2, 251, 2, 3, 2, 5, 2, 37, 2, 3, 2, 59, 2, 13, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 0, 2, 131, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 113, 2, 3, 2, 31, 2, 0, 2, 3, 2, 139, 2, 5, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 317, 2, 3, 2, 127, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 293, 2, 5, 2, 3, 2, 281, 2, 7,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 107, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 163, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData240_checked :
    roundedProductCertificate 122882 20877149595152 productData240 = some 20883763349848 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData240_length : productData240.length = 512 := by decide

def productData241 : List ℕ :=
  [2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 167, 2, 5, 2, 3, 2, 0, 2, 83, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 13, 2, 331, 2, 3, 2, 311, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 113, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 149,
    2, 101, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 7, 2, 157, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 191, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 83, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 71, 2, 7, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 181, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 61, 2, 53,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 11, 2, 3, 2, 0, 2, 337, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 179, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 103, 2, 3, 2, 0, 2, 17, 2, 3, 2, 193,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 67, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 61, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 79, 2, 3, 2, 43, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 59,
    2, 3, 2, 5, 2, 271, 2, 3, 2, 7, 2, 0, 2, 3, 2, 211, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 97, 2, 11, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 73, 2, 43, 2, 3, 2, 0, 2, 229, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData241_checked :
    roundedProductCertificate 123394 20883763349848 productData241 = some 20891873543858 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData241_length : productData241.length = 512 := by decide

def productData242 : List ℕ :=
  [2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 29, 2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 41, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 113, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 151, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 13, 2, 269, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 73, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 71, 2, 23, 2, 3, 2, 163, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 131, 2, 3, 2, 7, 2, 97, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 53, 2, 5, 2, 3, 2, 127, 2, 167, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 0,
    2, 193, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 101,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 227, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 223, 2, 0, 2, 3, 2, 31, 2, 17, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 283, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 137, 2, 313, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 151, 2, 3, 2, 0, 2, 19, 2, 3, 2, 37, 2, 5, 2, 3, 2, 11,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 197, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 101, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 277, 2, 5, 2, 3, 2, 61, 2, 29, 2, 3, 2, 5,
    2, 173, 2, 3, 2, 53, 2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 83]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData242_checked :
    roundedProductCertificate 123906 20891873543858 productData242 = some 20899110420833 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData242_length : productData242.length = 512 := by decide

def productData243 : List ℕ :=
  [2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 97, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 281, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 89, 2, 0,
    2, 3, 2, 41, 2, 239, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 269, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 347, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 53, 2, 3, 2, 7, 2, 353,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 0, 2, 3, 2, 23, 2, 113, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 7, 2, 3, 2, 59, 2, 0, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 13, 2, 311, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 191, 2, 3, 2, 37, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 73, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37,
    2, 3, 2, 5, 2, 137, 2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 127, 2, 131, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 193, 2, 7, 2, 3, 2, 151, 2, 47, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71, 2, 13, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 11, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData243_checked :
    roundedProductCertificate 124418 20899110420833 productData243 = some 20906655505537 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData243_length : productData243.length = 512 := by decide

def productData244 : List ℕ :=
  [2, 271, 2, 17, 2, 3, 2, 101, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29,
    2, 19, 2, 3, 2, 17, 2, 13, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 239, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 149, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 31, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 97, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 0, 2, 3, 2, 79,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 181, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 43, 2, 67,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 211, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 257, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 41, 2, 3, 2, 13, 2, 151, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 5, 2, 97, 2, 3, 2, 0, 2, 61, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 251,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 229, 2, 3, 2, 19, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 349, 2, 7, 2, 3, 2, 107, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 0, 2, 3,
    2, 5, 2, 113, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5,
    2, 163, 2, 3, 2, 103, 2, 0, 2, 3, 2, 67, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 283, 2, 0, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 89, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 83, 2, 3, 2, 167, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData244_checked :
    roundedProductCertificate 124930 20906655505537 productData244 = some 20914004198676 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData244_length : productData244.length = 512 := by decide

def productData245 : List ℕ :=
  [2, 17, 2, 3, 2, 7, 2, 331, 2, 3, 2, 0, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 271,
    2, 3, 2, 11, 2, 179, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 0, 2, 0, 2, 3, 2, 313, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 47,
    2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 223, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 241, 2, 307, 2, 3, 2, 13, 2, 199,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 29, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 269, 2, 3, 2, 0, 2, 7, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 7, 2, 337, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 59,
    2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 41, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 19,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 173, 2, 29, 2, 3, 2, 0, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 97, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47, 2, 0, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 29, 2, 23, 2, 3, 2, 19, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 317, 2, 11, 2, 3, 2, 5, 2, 127,
    2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 191, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 31, 2, 67, 2, 3, 2, 0, 2, 0, 2, 3, 2, 137, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData245_checked :
    roundedProductCertificate 125442 20914004198676 productData245 = some 20921159258042 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData245_length : productData245.length = 512 := by decide

def productData246 : List ℕ :=
  [2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 103, 2, 23, 2, 3, 2, 5, 2, 263, 2, 3, 2, 53, 2, 11, 2, 3,
    2, 17, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 163, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23,
    2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 193, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 241, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 233, 2, 5, 2, 3, 2, 37, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 139, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 59, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 19, 2, 3, 2, 0, 2, 23, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 101, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 79, 2, 3, 2, 71, 2, 281, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 19, 2, 11, 2, 3, 2, 5, 2, 257, 2, 3, 2, 13, 2, 53, 2, 3, 2, 97, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61,
    2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 113, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 0,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 191, 2, 251, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3,
    2, 5, 2, 197, 2, 3, 2, 37, 2, 293, 2, 3, 2, 7, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 59, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 107, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 43, 2, 11, 2, 3, 2, 47, 2, 5, 2, 3, 2, 211, 2, 97, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11,
    2, 41, 2, 3, 2, 19, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 167, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0,
    2, 3, 2, 59, 2, 227, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData246_checked :
    roundedProductCertificate 125954 20921159258042 productData246 = some 20928288999829 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData246_length : productData246.length = 512 := by decide

def productData247 : List ℕ :=
  [2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 79, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 73, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 23, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 271, 2, 19, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 23, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 103, 2, 277, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 53, 2, 127, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 139, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 89, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 13, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 197, 2, 19, 2, 3, 2, 131, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 151,
    2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 353, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 109, 2, 17, 2, 3, 2, 331, 2, 5, 2, 3, 2, 97, 2, 0, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 7, 2, 103, 2, 3, 2, 11, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 173, 2, 211, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 47, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 293, 2, 17, 2, 3, 2, 5, 2, 71, 2, 3, 2, 181,
    2, 31, 2, 3, 2, 223, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 113, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 179, 2, 0,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 61, 2, 0, 2, 3,
    2, 37, 2, 0, 2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData247_checked :
    roundedProductCertificate 126466 20928288999829 productData247 = some 20935062246973 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData247_length : productData247.length = 512 := by decide

def productData248 : List ℕ :=
  [2, 43, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 89, 2, 3, 2, 17, 2, 107,
    2, 3, 2, 157, 2, 5, 2, 3, 2, 71, 2, 37, 2, 3, 2, 5, 2, 59, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 61, 2, 3, 2, 283, 2, 31, 2, 3, 2, 83,
    2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 167, 2, 3, 2, 19, 2, 73, 2, 3, 2, 149, 2, 7, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 17, 2, 79, 2, 3, 2, 5, 2, 317, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 0, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 43, 2, 13, 2, 3, 2, 0, 2, 101, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 89, 2, 7, 2, 3, 2, 193, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 311, 2, 131,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 47, 2, 13, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 137, 2, 3, 2, 0, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 61, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 157, 2, 3,
    2, 0, 2, 223, 2, 3, 2, 7, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 347, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13,
    2, 0, 2, 3, 2, 67, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 103, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 79, 2, 61, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 233, 2, 0, 2, 3, 2, 11,
    2, 197, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 23]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData248_checked :
    roundedProductCertificate 126978 20935062246973 productData248 = some 20941479834419 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData248_length : productData248.length = 512 := by decide

def productData249 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 47, 2, 29, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 89, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 229,
    2, 5, 2, 3, 2, 199, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 193, 2, 3, 2, 113, 2, 0, 2, 3, 2, 0, 2, 5,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 109, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 107, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 149, 2, 3, 2, 277, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 11, 2, 337, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 139, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 13, 2, 43, 2, 3, 2, 7, 2, 251, 2, 3, 2, 0, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 17, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 227, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 173, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 71, 2, 0,
    2, 3, 2, 0, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79, 2, 23, 2, 3,
    2, 13, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 13, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 97, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 199, 2, 3, 2, 41, 2, 11, 2, 3, 2, 7, 2, 73,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 131, 2, 3, 2, 149, 2, 17, 2, 3, 2, 0, 2, 31, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData249_checked :
    roundedProductCertificate 127490 20941479834419 productData249 = some 20949350805074 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData249_length : productData249.length = 512 := by decide

def productData250 : List ℕ :=
  [2, 19, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 313, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 61, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 79, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 83, 2, 89, 2, 3, 2, 5, 2, 211, 2, 3, 2, 263, 2, 349, 2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 0, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17,
    2, 37, 2, 3, 2, 5, 2, 97, 2, 3, 2, 13, 2, 127, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 67, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 257, 2, 5, 2, 3, 2, 11, 2, 277, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 29, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 163, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 0, 2, 181, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37,
    2, 3, 2, 47, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 137, 2, 31, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 0, 2, 0, 2, 3, 2, 281,
    2, 53, 2, 3, 2, 167, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3, 2, 11, 2, 0,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 17, 2, 3, 2, 107, 2, 0, 2, 3, 2, 7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData250_checked :
    roundedProductCertificate 128002 20949350805074 productData250 = some 20956863979515 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData250_length : productData250.length = 512 := by decide

def productData251 : List ℕ :=
  [2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 79, 2, 3, 2, 17, 2, 173, 2, 3, 2, 191, 2, 5,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 59, 2, 0, 2, 3, 2, 83, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 11, 2, 71, 2, 3, 2, 5, 2, 149, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 11, 2, 3, 2, 293, 2, 0, 2, 3, 2, 307, 2, 5, 2, 3, 2, 7, 2, 197,
    2, 3, 2, 5, 2, 103, 2, 3, 2, 127, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 223, 2, 3,
    2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 179, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 11, 2, 13, 2, 3, 2, 0, 2, 97, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2, 23, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 17, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 199, 2, 5, 2, 3, 2, 331, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 61, 2, 131, 2, 3, 2, 11, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19,
    2, 151, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 0, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 269, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3,
    2, 31, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 359, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 61, 2, 3, 2, 157,
    2, 83, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 137, 2, 3, 2, 13, 2, 0, 2, 3, 2, 229, 2, 31,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 43, 2, 0, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 101, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData251_checked :
    roundedProductCertificate 128514 20956863979515 productData251 = some 20964350549576 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData251_length : productData251.length = 512 := by decide

def productData252 : List ℕ :=
  [2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 43, 2, 3, 2, 17, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 337, 2, 7, 2, 3, 2, 13, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0,
    2, 167, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 139, 2, 263, 2, 3, 2, 29, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 53, 2, 227, 2, 3, 2, 37, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 101, 2, 13, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 157, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 307, 2, 3,
    2, 17, 2, 29, 2, 3, 2, 19, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 257, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 239, 2, 31, 2, 3, 2, 5, 2, 191, 2, 3, 2, 7, 2, 0,
    2, 3, 2, 89, 2, 17, 2, 3, 2, 79, 2, 5, 2, 3, 2, 23, 2, 283, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 211, 2, 3,
    2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 277, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 53, 2, 3, 2, 67,
    2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 13, 2, 47, 2, 3, 2, 5, 2, 83, 2, 3, 2, 0, 2, 0, 2, 3, 2, 151, 2, 7,
    2, 3, 2, 127, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 29, 2, 3, 2, 347, 2, 71, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2, 13, 2, 0, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData252_checked :
    roundedProductCertificate 129026 20964350549576 productData252 = some 20971809982430 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData252_length : productData252.length = 512 := by decide

def productData253 : List ℕ :=
  [2, 0, 2, 281, 2, 3, 2, 5, 2, 11, 2, 3, 2, 353, 2, 0, 2, 3, 2, 17, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 101, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 29,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 11, 2, 3, 2, 227, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 317, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 127, 2, 3, 2, 0, 2, 31, 2, 3, 2, 103, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 151, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 73, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 0, 2, 3, 2, 0, 2, 137, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17,
    2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 233, 2, 3, 2, 5, 2, 7, 2, 3, 2, 107, 2, 0,
    2, 3, 2, 31, 2, 293, 2, 3, 2, 0, 2, 5, 2, 3, 2, 271, 2, 11, 2, 3, 2, 5, 2, 43, 2, 3, 2, 131, 2, 197, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 157, 2, 0, 2, 3, 2, 5, 2, 41, 2, 3, 2, 89, 2, 0, 2, 3, 2, 7,
    2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 13, 2, 3, 2, 0, 2, 193,
    2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 163, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3,
    2, 173, 2, 5, 2, 3, 2, 41, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 199, 2, 29, 2, 3, 2, 0,
    2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 59, 2, 19, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 43, 2, 61, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2, 0, 2, 3, 2, 29, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 109, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 47]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData253_checked :
    roundedProductCertificate 129538 20971809982430 productData253 = some 20977951220434 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData253_length : productData253.length = 512 := by decide

def productData254 : List ℕ :=
  [2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 83, 2, 113, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7,
    2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 11, 2, 0, 2, 3, 2, 281, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 37, 2, 3, 2, 179, 2, 5, 2, 3, 2, 181, 2, 11, 2, 3, 2, 5,
    2, 0, 2, 3, 2, 7, 2, 157, 2, 3, 2, 23, 2, 73, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 349,
    2, 3, 2, 29, 2, 0, 2, 3, 2, 211, 2, 101, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 0, 2, 59, 2, 3, 2, 197, 2, 107, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0,
    2, 139, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11,
    2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 113, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 229, 2, 0, 2, 3,
    2, 0, 2, 311, 2, 3, 2, 151, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 53, 2, 3, 2, 47, 2, 7, 2, 3, 2, 0,
    2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 241, 2, 3, 2, 5, 2, 23, 2, 3, 2, 101, 2, 83, 2, 3, 2, 19, 2, 0, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 73, 2, 191, 2, 3, 2, 0, 2, 7, 2, 3, 2, 283, 2, 5,
    2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7,
    2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 137]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData254_checked :
    roundedProductCertificate 130050 20977951220434 productData254 = some 20985679984686 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData254_length : productData254.length = 512 := by decide

def productData255 : List ℕ :=
  [2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 37, 2, 3, 2, 17, 2, 0, 2, 3, 2, 67, 2, 5, 2, 3, 2, 0, 2, 43, 2, 3,
    2, 5, 2, 73, 2, 3, 2, 61, 2, 11, 2, 3, 2, 131, 2, 211, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0,
    2, 3, 2, 193, 2, 13, 2, 3, 2, 41, 2, 7, 2, 3, 2, 149, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3,
    2, 11, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 67, 2, 3, 2, 37,
    2, 61, 2, 3, 2, 31, 2, 0, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 53, 2, 7,
    2, 3, 2, 11, 2, 229, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 251, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3,
    2, 0, 2, 31, 2, 3, 2, 13, 2, 5, 2, 3, 2, 139, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 257, 2, 3, 2, 0,
    2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 17,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 107, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 29, 2, 7, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 223, 2, 79, 2, 3, 2, 7, 2, 109, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 89, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 311, 2, 11, 2, 3, 2, 127, 2, 23, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 173, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3,
    2, 227, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 29, 2, 3, 2, 101, 2, 11, 2, 3, 2, 269, 2, 5, 2, 3, 2, 0,
    2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 0, 2, 3, 2, 13, 2, 283, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 0,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 13, 2, 3, 2, 83, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 0, 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem productData255_checked :
    roundedProductCertificate 130562 20985679984686 productData255 = some 20992098037658 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem productData255_length : productData255.length = 511 := by decide

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/PrimeProductBound.lean` -/

section



theorem reciprocalPrefix_131071_lt : reciprocalPrefix 131071 < (211 / 10 : ℝ) := by
  have h0 : (1000000000000 : ℝ) * reciprocalPrefix 0 ≤ 1000000000000 := by
    norm_num [reciprocalPrefix]
  have h1 := certificate_prefix_step h0 productData000_checked
  simp only [productData000_length, Nat.reduceAdd] at h1
  have h2 := certificate_prefix_step h1 productData001_checked
  simp only [productData001_length, Nat.reduceAdd] at h2
  have h3 := certificate_prefix_step h2 productData002_checked
  simp only [productData002_length, Nat.reduceAdd] at h3
  have h4 := certificate_prefix_step h3 productData003_checked
  simp only [productData003_length, Nat.reduceAdd] at h4
  have h5 := certificate_prefix_step h4 productData004_checked
  simp only [productData004_length, Nat.reduceAdd] at h5
  have h6 := certificate_prefix_step h5 productData005_checked
  simp only [productData005_length, Nat.reduceAdd] at h6
  have h7 := certificate_prefix_step h6 productData006_checked
  simp only [productData006_length, Nat.reduceAdd] at h7
  have h8 := certificate_prefix_step h7 productData007_checked
  simp only [productData007_length, Nat.reduceAdd] at h8
  have h9 := certificate_prefix_step h8 productData008_checked
  simp only [productData008_length, Nat.reduceAdd] at h9
  have h10 := certificate_prefix_step h9 productData009_checked
  simp only [productData009_length, Nat.reduceAdd] at h10
  have h11 := certificate_prefix_step h10 productData010_checked
  simp only [productData010_length, Nat.reduceAdd] at h11
  have h12 := certificate_prefix_step h11 productData011_checked
  simp only [productData011_length, Nat.reduceAdd] at h12
  have h13 := certificate_prefix_step h12 productData012_checked
  simp only [productData012_length, Nat.reduceAdd] at h13
  have h14 := certificate_prefix_step h13 productData013_checked
  simp only [productData013_length, Nat.reduceAdd] at h14
  have h15 := certificate_prefix_step h14 productData014_checked
  simp only [productData014_length, Nat.reduceAdd] at h15
  have h16 := certificate_prefix_step h15 productData015_checked
  simp only [productData015_length, Nat.reduceAdd] at h16
  have h17 := certificate_prefix_step h16 productData016_checked
  simp only [productData016_length, Nat.reduceAdd] at h17
  have h18 := certificate_prefix_step h17 productData017_checked
  simp only [productData017_length, Nat.reduceAdd] at h18
  have h19 := certificate_prefix_step h18 productData018_checked
  simp only [productData018_length, Nat.reduceAdd] at h19
  have h20 := certificate_prefix_step h19 productData019_checked
  simp only [productData019_length, Nat.reduceAdd] at h20
  have h21 := certificate_prefix_step h20 productData020_checked
  simp only [productData020_length, Nat.reduceAdd] at h21
  have h22 := certificate_prefix_step h21 productData021_checked
  simp only [productData021_length, Nat.reduceAdd] at h22
  have h23 := certificate_prefix_step h22 productData022_checked
  simp only [productData022_length, Nat.reduceAdd] at h23
  have h24 := certificate_prefix_step h23 productData023_checked
  simp only [productData023_length, Nat.reduceAdd] at h24
  have h25 := certificate_prefix_step h24 productData024_checked
  simp only [productData024_length, Nat.reduceAdd] at h25
  have h26 := certificate_prefix_step h25 productData025_checked
  simp only [productData025_length, Nat.reduceAdd] at h26
  have h27 := certificate_prefix_step h26 productData026_checked
  simp only [productData026_length, Nat.reduceAdd] at h27
  have h28 := certificate_prefix_step h27 productData027_checked
  simp only [productData027_length, Nat.reduceAdd] at h28
  have h29 := certificate_prefix_step h28 productData028_checked
  simp only [productData028_length, Nat.reduceAdd] at h29
  have h30 := certificate_prefix_step h29 productData029_checked
  simp only [productData029_length, Nat.reduceAdd] at h30
  have h31 := certificate_prefix_step h30 productData030_checked
  simp only [productData030_length, Nat.reduceAdd] at h31
  have h32 := certificate_prefix_step h31 productData031_checked
  simp only [productData031_length, Nat.reduceAdd] at h32
  have h33 := certificate_prefix_step h32 productData032_checked
  simp only [productData032_length, Nat.reduceAdd] at h33
  have h34 := certificate_prefix_step h33 productData033_checked
  simp only [productData033_length, Nat.reduceAdd] at h34
  have h35 := certificate_prefix_step h34 productData034_checked
  simp only [productData034_length, Nat.reduceAdd] at h35
  have h36 := certificate_prefix_step h35 productData035_checked
  simp only [productData035_length, Nat.reduceAdd] at h36
  have h37 := certificate_prefix_step h36 productData036_checked
  simp only [productData036_length, Nat.reduceAdd] at h37
  have h38 := certificate_prefix_step h37 productData037_checked
  simp only [productData037_length, Nat.reduceAdd] at h38
  have h39 := certificate_prefix_step h38 productData038_checked
  simp only [productData038_length, Nat.reduceAdd] at h39
  have h40 := certificate_prefix_step h39 productData039_checked
  simp only [productData039_length, Nat.reduceAdd] at h40
  have h41 := certificate_prefix_step h40 productData040_checked
  simp only [productData040_length, Nat.reduceAdd] at h41
  have h42 := certificate_prefix_step h41 productData041_checked
  simp only [productData041_length, Nat.reduceAdd] at h42
  have h43 := certificate_prefix_step h42 productData042_checked
  simp only [productData042_length, Nat.reduceAdd] at h43
  have h44 := certificate_prefix_step h43 productData043_checked
  simp only [productData043_length, Nat.reduceAdd] at h44
  have h45 := certificate_prefix_step h44 productData044_checked
  simp only [productData044_length, Nat.reduceAdd] at h45
  have h46 := certificate_prefix_step h45 productData045_checked
  simp only [productData045_length, Nat.reduceAdd] at h46
  have h47 := certificate_prefix_step h46 productData046_checked
  simp only [productData046_length, Nat.reduceAdd] at h47
  have h48 := certificate_prefix_step h47 productData047_checked
  simp only [productData047_length, Nat.reduceAdd] at h48
  have h49 := certificate_prefix_step h48 productData048_checked
  simp only [productData048_length, Nat.reduceAdd] at h49
  have h50 := certificate_prefix_step h49 productData049_checked
  simp only [productData049_length, Nat.reduceAdd] at h50
  have h51 := certificate_prefix_step h50 productData050_checked
  simp only [productData050_length, Nat.reduceAdd] at h51
  have h52 := certificate_prefix_step h51 productData051_checked
  simp only [productData051_length, Nat.reduceAdd] at h52
  have h53 := certificate_prefix_step h52 productData052_checked
  simp only [productData052_length, Nat.reduceAdd] at h53
  have h54 := certificate_prefix_step h53 productData053_checked
  simp only [productData053_length, Nat.reduceAdd] at h54
  have h55 := certificate_prefix_step h54 productData054_checked
  simp only [productData054_length, Nat.reduceAdd] at h55
  have h56 := certificate_prefix_step h55 productData055_checked
  simp only [productData055_length, Nat.reduceAdd] at h56
  have h57 := certificate_prefix_step h56 productData056_checked
  simp only [productData056_length, Nat.reduceAdd] at h57
  have h58 := certificate_prefix_step h57 productData057_checked
  simp only [productData057_length, Nat.reduceAdd] at h58
  have h59 := certificate_prefix_step h58 productData058_checked
  simp only [productData058_length, Nat.reduceAdd] at h59
  have h60 := certificate_prefix_step h59 productData059_checked
  simp only [productData059_length, Nat.reduceAdd] at h60
  have h61 := certificate_prefix_step h60 productData060_checked
  simp only [productData060_length, Nat.reduceAdd] at h61
  have h62 := certificate_prefix_step h61 productData061_checked
  simp only [productData061_length, Nat.reduceAdd] at h62
  have h63 := certificate_prefix_step h62 productData062_checked
  simp only [productData062_length, Nat.reduceAdd] at h63
  have h64 := certificate_prefix_step h63 productData063_checked
  simp only [productData063_length, Nat.reduceAdd] at h64
  have h65 := certificate_prefix_step h64 productData064_checked
  simp only [productData064_length, Nat.reduceAdd] at h65
  have h66 := certificate_prefix_step h65 productData065_checked
  simp only [productData065_length, Nat.reduceAdd] at h66
  have h67 := certificate_prefix_step h66 productData066_checked
  simp only [productData066_length, Nat.reduceAdd] at h67
  have h68 := certificate_prefix_step h67 productData067_checked
  simp only [productData067_length, Nat.reduceAdd] at h68
  have h69 := certificate_prefix_step h68 productData068_checked
  simp only [productData068_length, Nat.reduceAdd] at h69
  have h70 := certificate_prefix_step h69 productData069_checked
  simp only [productData069_length, Nat.reduceAdd] at h70
  have h71 := certificate_prefix_step h70 productData070_checked
  simp only [productData070_length, Nat.reduceAdd] at h71
  have h72 := certificate_prefix_step h71 productData071_checked
  simp only [productData071_length, Nat.reduceAdd] at h72
  have h73 := certificate_prefix_step h72 productData072_checked
  simp only [productData072_length, Nat.reduceAdd] at h73
  have h74 := certificate_prefix_step h73 productData073_checked
  simp only [productData073_length, Nat.reduceAdd] at h74
  have h75 := certificate_prefix_step h74 productData074_checked
  simp only [productData074_length, Nat.reduceAdd] at h75
  have h76 := certificate_prefix_step h75 productData075_checked
  simp only [productData075_length, Nat.reduceAdd] at h76
  have h77 := certificate_prefix_step h76 productData076_checked
  simp only [productData076_length, Nat.reduceAdd] at h77
  have h78 := certificate_prefix_step h77 productData077_checked
  simp only [productData077_length, Nat.reduceAdd] at h78
  have h79 := certificate_prefix_step h78 productData078_checked
  simp only [productData078_length, Nat.reduceAdd] at h79
  have h80 := certificate_prefix_step h79 productData079_checked
  simp only [productData079_length, Nat.reduceAdd] at h80
  have h81 := certificate_prefix_step h80 productData080_checked
  simp only [productData080_length, Nat.reduceAdd] at h81
  have h82 := certificate_prefix_step h81 productData081_checked
  simp only [productData081_length, Nat.reduceAdd] at h82
  have h83 := certificate_prefix_step h82 productData082_checked
  simp only [productData082_length, Nat.reduceAdd] at h83
  have h84 := certificate_prefix_step h83 productData083_checked
  simp only [productData083_length, Nat.reduceAdd] at h84
  have h85 := certificate_prefix_step h84 productData084_checked
  simp only [productData084_length, Nat.reduceAdd] at h85
  have h86 := certificate_prefix_step h85 productData085_checked
  simp only [productData085_length, Nat.reduceAdd] at h86
  have h87 := certificate_prefix_step h86 productData086_checked
  simp only [productData086_length, Nat.reduceAdd] at h87
  have h88 := certificate_prefix_step h87 productData087_checked
  simp only [productData087_length, Nat.reduceAdd] at h88
  have h89 := certificate_prefix_step h88 productData088_checked
  simp only [productData088_length, Nat.reduceAdd] at h89
  have h90 := certificate_prefix_step h89 productData089_checked
  simp only [productData089_length, Nat.reduceAdd] at h90
  have h91 := certificate_prefix_step h90 productData090_checked
  simp only [productData090_length, Nat.reduceAdd] at h91
  have h92 := certificate_prefix_step h91 productData091_checked
  simp only [productData091_length, Nat.reduceAdd] at h92
  have h93 := certificate_prefix_step h92 productData092_checked
  simp only [productData092_length, Nat.reduceAdd] at h93
  have h94 := certificate_prefix_step h93 productData093_checked
  simp only [productData093_length, Nat.reduceAdd] at h94
  have h95 := certificate_prefix_step h94 productData094_checked
  simp only [productData094_length, Nat.reduceAdd] at h95
  have h96 := certificate_prefix_step h95 productData095_checked
  simp only [productData095_length, Nat.reduceAdd] at h96
  have h97 := certificate_prefix_step h96 productData096_checked
  simp only [productData096_length, Nat.reduceAdd] at h97
  have h98 := certificate_prefix_step h97 productData097_checked
  simp only [productData097_length, Nat.reduceAdd] at h98
  have h99 := certificate_prefix_step h98 productData098_checked
  simp only [productData098_length, Nat.reduceAdd] at h99
  have h100 := certificate_prefix_step h99 productData099_checked
  simp only [productData099_length, Nat.reduceAdd] at h100
  have h101 := certificate_prefix_step h100 productData100_checked
  simp only [productData100_length, Nat.reduceAdd] at h101
  have h102 := certificate_prefix_step h101 productData101_checked
  simp only [productData101_length, Nat.reduceAdd] at h102
  have h103 := certificate_prefix_step h102 productData102_checked
  simp only [productData102_length, Nat.reduceAdd] at h103
  have h104 := certificate_prefix_step h103 productData103_checked
  simp only [productData103_length, Nat.reduceAdd] at h104
  have h105 := certificate_prefix_step h104 productData104_checked
  simp only [productData104_length, Nat.reduceAdd] at h105
  have h106 := certificate_prefix_step h105 productData105_checked
  simp only [productData105_length, Nat.reduceAdd] at h106
  have h107 := certificate_prefix_step h106 productData106_checked
  simp only [productData106_length, Nat.reduceAdd] at h107
  have h108 := certificate_prefix_step h107 productData107_checked
  simp only [productData107_length, Nat.reduceAdd] at h108
  have h109 := certificate_prefix_step h108 productData108_checked
  simp only [productData108_length, Nat.reduceAdd] at h109
  have h110 := certificate_prefix_step h109 productData109_checked
  simp only [productData109_length, Nat.reduceAdd] at h110
  have h111 := certificate_prefix_step h110 productData110_checked
  simp only [productData110_length, Nat.reduceAdd] at h111
  have h112 := certificate_prefix_step h111 productData111_checked
  simp only [productData111_length, Nat.reduceAdd] at h112
  have h113 := certificate_prefix_step h112 productData112_checked
  simp only [productData112_length, Nat.reduceAdd] at h113
  have h114 := certificate_prefix_step h113 productData113_checked
  simp only [productData113_length, Nat.reduceAdd] at h114
  have h115 := certificate_prefix_step h114 productData114_checked
  simp only [productData114_length, Nat.reduceAdd] at h115
  have h116 := certificate_prefix_step h115 productData115_checked
  simp only [productData115_length, Nat.reduceAdd] at h116
  have h117 := certificate_prefix_step h116 productData116_checked
  simp only [productData116_length, Nat.reduceAdd] at h117
  have h118 := certificate_prefix_step h117 productData117_checked
  simp only [productData117_length, Nat.reduceAdd] at h118
  have h119 := certificate_prefix_step h118 productData118_checked
  simp only [productData118_length, Nat.reduceAdd] at h119
  have h120 := certificate_prefix_step h119 productData119_checked
  simp only [productData119_length, Nat.reduceAdd] at h120
  have h121 := certificate_prefix_step h120 productData120_checked
  simp only [productData120_length, Nat.reduceAdd] at h121
  have h122 := certificate_prefix_step h121 productData121_checked
  simp only [productData121_length, Nat.reduceAdd] at h122
  have h123 := certificate_prefix_step h122 productData122_checked
  simp only [productData122_length, Nat.reduceAdd] at h123
  have h124 := certificate_prefix_step h123 productData123_checked
  simp only [productData123_length, Nat.reduceAdd] at h124
  have h125 := certificate_prefix_step h124 productData124_checked
  simp only [productData124_length, Nat.reduceAdd] at h125
  have h126 := certificate_prefix_step h125 productData125_checked
  simp only [productData125_length, Nat.reduceAdd] at h126
  have h127 := certificate_prefix_step h126 productData126_checked
  simp only [productData126_length, Nat.reduceAdd] at h127
  have h128 := certificate_prefix_step h127 productData127_checked
  simp only [productData127_length, Nat.reduceAdd] at h128
  have h129 := certificate_prefix_step h128 productData128_checked
  simp only [productData128_length, Nat.reduceAdd] at h129
  have h130 := certificate_prefix_step h129 productData129_checked
  simp only [productData129_length, Nat.reduceAdd] at h130
  have h131 := certificate_prefix_step h130 productData130_checked
  simp only [productData130_length, Nat.reduceAdd] at h131
  have h132 := certificate_prefix_step h131 productData131_checked
  simp only [productData131_length, Nat.reduceAdd] at h132
  have h133 := certificate_prefix_step h132 productData132_checked
  simp only [productData132_length, Nat.reduceAdd] at h133
  have h134 := certificate_prefix_step h133 productData133_checked
  simp only [productData133_length, Nat.reduceAdd] at h134
  have h135 := certificate_prefix_step h134 productData134_checked
  simp only [productData134_length, Nat.reduceAdd] at h135
  have h136 := certificate_prefix_step h135 productData135_checked
  simp only [productData135_length, Nat.reduceAdd] at h136
  have h137 := certificate_prefix_step h136 productData136_checked
  simp only [productData136_length, Nat.reduceAdd] at h137
  have h138 := certificate_prefix_step h137 productData137_checked
  simp only [productData137_length, Nat.reduceAdd] at h138
  have h139 := certificate_prefix_step h138 productData138_checked
  simp only [productData138_length, Nat.reduceAdd] at h139
  have h140 := certificate_prefix_step h139 productData139_checked
  simp only [productData139_length, Nat.reduceAdd] at h140
  have h141 := certificate_prefix_step h140 productData140_checked
  simp only [productData140_length, Nat.reduceAdd] at h141
  have h142 := certificate_prefix_step h141 productData141_checked
  simp only [productData141_length, Nat.reduceAdd] at h142
  have h143 := certificate_prefix_step h142 productData142_checked
  simp only [productData142_length, Nat.reduceAdd] at h143
  have h144 := certificate_prefix_step h143 productData143_checked
  simp only [productData143_length, Nat.reduceAdd] at h144
  have h145 := certificate_prefix_step h144 productData144_checked
  simp only [productData144_length, Nat.reduceAdd] at h145
  have h146 := certificate_prefix_step h145 productData145_checked
  simp only [productData145_length, Nat.reduceAdd] at h146
  have h147 := certificate_prefix_step h146 productData146_checked
  simp only [productData146_length, Nat.reduceAdd] at h147
  have h148 := certificate_prefix_step h147 productData147_checked
  simp only [productData147_length, Nat.reduceAdd] at h148
  have h149 := certificate_prefix_step h148 productData148_checked
  simp only [productData148_length, Nat.reduceAdd] at h149
  have h150 := certificate_prefix_step h149 productData149_checked
  simp only [productData149_length, Nat.reduceAdd] at h150
  have h151 := certificate_prefix_step h150 productData150_checked
  simp only [productData150_length, Nat.reduceAdd] at h151
  have h152 := certificate_prefix_step h151 productData151_checked
  simp only [productData151_length, Nat.reduceAdd] at h152
  have h153 := certificate_prefix_step h152 productData152_checked
  simp only [productData152_length, Nat.reduceAdd] at h153
  have h154 := certificate_prefix_step h153 productData153_checked
  simp only [productData153_length, Nat.reduceAdd] at h154
  have h155 := certificate_prefix_step h154 productData154_checked
  simp only [productData154_length, Nat.reduceAdd] at h155
  have h156 := certificate_prefix_step h155 productData155_checked
  simp only [productData155_length, Nat.reduceAdd] at h156
  have h157 := certificate_prefix_step h156 productData156_checked
  simp only [productData156_length, Nat.reduceAdd] at h157
  have h158 := certificate_prefix_step h157 productData157_checked
  simp only [productData157_length, Nat.reduceAdd] at h158
  have h159 := certificate_prefix_step h158 productData158_checked
  simp only [productData158_length, Nat.reduceAdd] at h159
  have h160 := certificate_prefix_step h159 productData159_checked
  simp only [productData159_length, Nat.reduceAdd] at h160
  have h161 := certificate_prefix_step h160 productData160_checked
  simp only [productData160_length, Nat.reduceAdd] at h161
  have h162 := certificate_prefix_step h161 productData161_checked
  simp only [productData161_length, Nat.reduceAdd] at h162
  have h163 := certificate_prefix_step h162 productData162_checked
  simp only [productData162_length, Nat.reduceAdd] at h163
  have h164 := certificate_prefix_step h163 productData163_checked
  simp only [productData163_length, Nat.reduceAdd] at h164
  have h165 := certificate_prefix_step h164 productData164_checked
  simp only [productData164_length, Nat.reduceAdd] at h165
  have h166 := certificate_prefix_step h165 productData165_checked
  simp only [productData165_length, Nat.reduceAdd] at h166
  have h167 := certificate_prefix_step h166 productData166_checked
  simp only [productData166_length, Nat.reduceAdd] at h167
  have h168 := certificate_prefix_step h167 productData167_checked
  simp only [productData167_length, Nat.reduceAdd] at h168
  have h169 := certificate_prefix_step h168 productData168_checked
  simp only [productData168_length, Nat.reduceAdd] at h169
  have h170 := certificate_prefix_step h169 productData169_checked
  simp only [productData169_length, Nat.reduceAdd] at h170
  have h171 := certificate_prefix_step h170 productData170_checked
  simp only [productData170_length, Nat.reduceAdd] at h171
  have h172 := certificate_prefix_step h171 productData171_checked
  simp only [productData171_length, Nat.reduceAdd] at h172
  have h173 := certificate_prefix_step h172 productData172_checked
  simp only [productData172_length, Nat.reduceAdd] at h173
  have h174 := certificate_prefix_step h173 productData173_checked
  simp only [productData173_length, Nat.reduceAdd] at h174
  have h175 := certificate_prefix_step h174 productData174_checked
  simp only [productData174_length, Nat.reduceAdd] at h175
  have h176 := certificate_prefix_step h175 productData175_checked
  simp only [productData175_length, Nat.reduceAdd] at h176
  have h177 := certificate_prefix_step h176 productData176_checked
  simp only [productData176_length, Nat.reduceAdd] at h177
  have h178 := certificate_prefix_step h177 productData177_checked
  simp only [productData177_length, Nat.reduceAdd] at h178
  have h179 := certificate_prefix_step h178 productData178_checked
  simp only [productData178_length, Nat.reduceAdd] at h179
  have h180 := certificate_prefix_step h179 productData179_checked
  simp only [productData179_length, Nat.reduceAdd] at h180
  have h181 := certificate_prefix_step h180 productData180_checked
  simp only [productData180_length, Nat.reduceAdd] at h181
  have h182 := certificate_prefix_step h181 productData181_checked
  simp only [productData181_length, Nat.reduceAdd] at h182
  have h183 := certificate_prefix_step h182 productData182_checked
  simp only [productData182_length, Nat.reduceAdd] at h183
  have h184 := certificate_prefix_step h183 productData183_checked
  simp only [productData183_length, Nat.reduceAdd] at h184
  have h185 := certificate_prefix_step h184 productData184_checked
  simp only [productData184_length, Nat.reduceAdd] at h185
  have h186 := certificate_prefix_step h185 productData185_checked
  simp only [productData185_length, Nat.reduceAdd] at h186
  have h187 := certificate_prefix_step h186 productData186_checked
  simp only [productData186_length, Nat.reduceAdd] at h187
  have h188 := certificate_prefix_step h187 productData187_checked
  simp only [productData187_length, Nat.reduceAdd] at h188
  have h189 := certificate_prefix_step h188 productData188_checked
  simp only [productData188_length, Nat.reduceAdd] at h189
  have h190 := certificate_prefix_step h189 productData189_checked
  simp only [productData189_length, Nat.reduceAdd] at h190
  have h191 := certificate_prefix_step h190 productData190_checked
  simp only [productData190_length, Nat.reduceAdd] at h191
  have h192 := certificate_prefix_step h191 productData191_checked
  simp only [productData191_length, Nat.reduceAdd] at h192
  have h193 := certificate_prefix_step h192 productData192_checked
  simp only [productData192_length, Nat.reduceAdd] at h193
  have h194 := certificate_prefix_step h193 productData193_checked
  simp only [productData193_length, Nat.reduceAdd] at h194
  have h195 := certificate_prefix_step h194 productData194_checked
  simp only [productData194_length, Nat.reduceAdd] at h195
  have h196 := certificate_prefix_step h195 productData195_checked
  simp only [productData195_length, Nat.reduceAdd] at h196
  have h197 := certificate_prefix_step h196 productData196_checked
  simp only [productData196_length, Nat.reduceAdd] at h197
  have h198 := certificate_prefix_step h197 productData197_checked
  simp only [productData197_length, Nat.reduceAdd] at h198
  have h199 := certificate_prefix_step h198 productData198_checked
  simp only [productData198_length, Nat.reduceAdd] at h199
  have h200 := certificate_prefix_step h199 productData199_checked
  simp only [productData199_length, Nat.reduceAdd] at h200
  have h201 := certificate_prefix_step h200 productData200_checked
  simp only [productData200_length, Nat.reduceAdd] at h201
  have h202 := certificate_prefix_step h201 productData201_checked
  simp only [productData201_length, Nat.reduceAdd] at h202
  have h203 := certificate_prefix_step h202 productData202_checked
  simp only [productData202_length, Nat.reduceAdd] at h203
  have h204 := certificate_prefix_step h203 productData203_checked
  simp only [productData203_length, Nat.reduceAdd] at h204
  have h205 := certificate_prefix_step h204 productData204_checked
  simp only [productData204_length, Nat.reduceAdd] at h205
  have h206 := certificate_prefix_step h205 productData205_checked
  simp only [productData205_length, Nat.reduceAdd] at h206
  have h207 := certificate_prefix_step h206 productData206_checked
  simp only [productData206_length, Nat.reduceAdd] at h207
  have h208 := certificate_prefix_step h207 productData207_checked
  simp only [productData207_length, Nat.reduceAdd] at h208
  have h209 := certificate_prefix_step h208 productData208_checked
  simp only [productData208_length, Nat.reduceAdd] at h209
  have h210 := certificate_prefix_step h209 productData209_checked
  simp only [productData209_length, Nat.reduceAdd] at h210
  have h211 := certificate_prefix_step h210 productData210_checked
  simp only [productData210_length, Nat.reduceAdd] at h211
  have h212 := certificate_prefix_step h211 productData211_checked
  simp only [productData211_length, Nat.reduceAdd] at h212
  have h213 := certificate_prefix_step h212 productData212_checked
  simp only [productData212_length, Nat.reduceAdd] at h213
  have h214 := certificate_prefix_step h213 productData213_checked
  simp only [productData213_length, Nat.reduceAdd] at h214
  have h215 := certificate_prefix_step h214 productData214_checked
  simp only [productData214_length, Nat.reduceAdd] at h215
  have h216 := certificate_prefix_step h215 productData215_checked
  simp only [productData215_length, Nat.reduceAdd] at h216
  have h217 := certificate_prefix_step h216 productData216_checked
  simp only [productData216_length, Nat.reduceAdd] at h217
  have h218 := certificate_prefix_step h217 productData217_checked
  simp only [productData217_length, Nat.reduceAdd] at h218
  have h219 := certificate_prefix_step h218 productData218_checked
  simp only [productData218_length, Nat.reduceAdd] at h219
  have h220 := certificate_prefix_step h219 productData219_checked
  simp only [productData219_length, Nat.reduceAdd] at h220
  have h221 := certificate_prefix_step h220 productData220_checked
  simp only [productData220_length, Nat.reduceAdd] at h221
  have h222 := certificate_prefix_step h221 productData221_checked
  simp only [productData221_length, Nat.reduceAdd] at h222
  have h223 := certificate_prefix_step h222 productData222_checked
  simp only [productData222_length, Nat.reduceAdd] at h223
  have h224 := certificate_prefix_step h223 productData223_checked
  simp only [productData223_length, Nat.reduceAdd] at h224
  have h225 := certificate_prefix_step h224 productData224_checked
  simp only [productData224_length, Nat.reduceAdd] at h225
  have h226 := certificate_prefix_step h225 productData225_checked
  simp only [productData225_length, Nat.reduceAdd] at h226
  have h227 := certificate_prefix_step h226 productData226_checked
  simp only [productData226_length, Nat.reduceAdd] at h227
  have h228 := certificate_prefix_step h227 productData227_checked
  simp only [productData227_length, Nat.reduceAdd] at h228
  have h229 := certificate_prefix_step h228 productData228_checked
  simp only [productData228_length, Nat.reduceAdd] at h229
  have h230 := certificate_prefix_step h229 productData229_checked
  simp only [productData229_length, Nat.reduceAdd] at h230
  have h231 := certificate_prefix_step h230 productData230_checked
  simp only [productData230_length, Nat.reduceAdd] at h231
  have h232 := certificate_prefix_step h231 productData231_checked
  simp only [productData231_length, Nat.reduceAdd] at h232
  have h233 := certificate_prefix_step h232 productData232_checked
  simp only [productData232_length, Nat.reduceAdd] at h233
  have h234 := certificate_prefix_step h233 productData233_checked
  simp only [productData233_length, Nat.reduceAdd] at h234
  have h235 := certificate_prefix_step h234 productData234_checked
  simp only [productData234_length, Nat.reduceAdd] at h235
  have h236 := certificate_prefix_step h235 productData235_checked
  simp only [productData235_length, Nat.reduceAdd] at h236
  have h237 := certificate_prefix_step h236 productData236_checked
  simp only [productData236_length, Nat.reduceAdd] at h237
  have h238 := certificate_prefix_step h237 productData237_checked
  simp only [productData237_length, Nat.reduceAdd] at h238
  have h239 := certificate_prefix_step h238 productData238_checked
  simp only [productData238_length, Nat.reduceAdd] at h239
  have h240 := certificate_prefix_step h239 productData239_checked
  simp only [productData239_length, Nat.reduceAdd] at h240
  have h241 := certificate_prefix_step h240 productData240_checked
  simp only [productData240_length, Nat.reduceAdd] at h241
  have h242 := certificate_prefix_step h241 productData241_checked
  simp only [productData241_length, Nat.reduceAdd] at h242
  have h243 := certificate_prefix_step h242 productData242_checked
  simp only [productData242_length, Nat.reduceAdd] at h243
  have h244 := certificate_prefix_step h243 productData243_checked
  simp only [productData243_length, Nat.reduceAdd] at h244
  have h245 := certificate_prefix_step h244 productData244_checked
  simp only [productData244_length, Nat.reduceAdd] at h245
  have h246 := certificate_prefix_step h245 productData245_checked
  simp only [productData245_length, Nat.reduceAdd] at h246
  have h247 := certificate_prefix_step h246 productData246_checked
  simp only [productData246_length, Nat.reduceAdd] at h247
  have h248 := certificate_prefix_step h247 productData247_checked
  simp only [productData247_length, Nat.reduceAdd] at h248
  have h249 := certificate_prefix_step h248 productData248_checked
  simp only [productData248_length, Nat.reduceAdd] at h249
  have h250 := certificate_prefix_step h249 productData249_checked
  simp only [productData249_length, Nat.reduceAdd] at h250
  have h251 := certificate_prefix_step h250 productData250_checked
  simp only [productData250_length, Nat.reduceAdd] at h251
  have h252 := certificate_prefix_step h251 productData251_checked
  simp only [productData251_length, Nat.reduceAdd] at h252
  have h253 := certificate_prefix_step h252 productData252_checked
  simp only [productData252_length, Nat.reduceAdd] at h253
  have h254 := certificate_prefix_step h253 productData253_checked
  simp only [productData253_length, Nat.reduceAdd] at h254
  have h255 := certificate_prefix_step h254 productData254_checked
  simp only [productData254_length, Nat.reduceAdd] at h255
  have h256 := certificate_prefix_step h255 productData255_checked
  simp only [productData255_length, Nat.reduceAdd] at h256
  norm_num at h256
  linarith

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/EulerBounds.lean` -/

section


noncomputable section
open Finset BigOperators
set_option maxHeartbeats 800000

lemma inverse_euler_eq (p : ℕ) (hp : p.Prime) :
    (1 - 1/(p : ℝ))⁻¹ = (p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := by exact sub_ne_zero.mpr (Nat.cast_ne_one.mpr hp.ne_one)
  field_simp

lemma inverse_euler_ge_one (p : ℕ) (hp : p.Prime) : 1 ≤ (1-1/(p : ℝ))⁻¹ := by
  rw [inverse_euler_eq p hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

lemma E_val_le_full_product (lam : ℝ) (k r : ℕ) :
    E_val lam k r ≤ ∏ p ∈ I_layer lam k, (1-1/(p : ℝ))⁻¹ := by
  apply Finset.sup'_le
  intro T hT
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  rw [← Finset.prod_sdiff hsub]
  apply le_mul_of_one_le_left
  · exact Finset.prod_nonneg fun p hp =>
      zero_le_one.trans (inverse_euler_ge_one p (Finset.mem_filter.mp (hsub hp)).2)
  · exact Finset.one_le_prod fun p hp =>
      inverse_euler_ge_one p (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2

lemma log_E_val_le (lam : ℝ) (k r : ℕ) (hY : 1 < Y_val lam k) :
    Real.log (E_val lam k r) ≤ (r : ℝ)/(Y_val lam k-1) := by
  have hden : 0 < Y_val lam k-1 := by linarith
  have hterm (p : ℕ) (hp : p ∈ I_layer lam k) :
      Real.log ((1-1/(p : ℝ))⁻¹) ≤ 1/(Y_val lam k-1) := by
    have hpprime := (Finset.mem_filter.mp hp).2
    have hpY : Y_val lam k ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1)
    have hpden : 0 < (p : ℝ)-1 := by linarith
    rw [inverse_euler_eq p hpprime]
    calc
      _ ≤ (p : ℝ)/(p-1)-1 := Real.log_le_sub_one_of_pos
        (div_pos (Nat.cast_pos.mpr hpprime.pos) hpden)
      _ = 1/((p : ℝ)-1) := by field_simp; ring
      _ ≤ _ := one_div_le_one_div_of_le hden (by linarith)
  have hE : E_val lam k r ≤ Real.exp ((r : ℝ)/(Y_val lam k-1)) := by
    apply Finset.sup'_le
    intro T hT
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hcard := (Finset.mem_filter.mp hT).2
    have hpos (p : ℕ) (hp : p ∈ T) : 0 < (1-1/(p : ℝ))⁻¹ :=
      zero_lt_one.trans_le (inverse_euler_ge_one p (Finset.mem_filter.mp (hsub hp)).2)
    calc
      _ = Real.exp (∑ p ∈ T, Real.log ((1-1/(p : ℝ))⁻¹)) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl fun p hp => (Real.exp_log (hpos p hp)).symm
      _ ≤ Real.exp ((T.card : ℝ)/(Y_val lam k-1)) := by
        apply Real.exp_le_exp.mpr
        simpa [div_eq_mul_inv] using Finset.sum_le_sum (fun p hp => hterm p (hsub hp))
      _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) hden.le)
  have := Real.log_le_log (zero_lt_one.trans_le (E_val_ge_one lam k r)) hE
  simpa only [Real.log_exp] using this

lemma layer_product_eq_interval (k : ℕ) :
    (∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹) =
      ∏ p ∈ Finset.Ico (dyadicScale k) (dyadicScale (k+1)), primeReciprocalFactor p := by
  rw [I_layer_two, dyadicScale_succ, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [primeReciprocalFactor]
  split_ifs with hpprime
  · exact inverse_euler_eq p hpprime
  · rfl

lemma layer_products_telescope (K : ℕ) :
    (∏ k ∈ Finset.range K, ∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹) =
      ∏ p ∈ Finset.Ico 2 (dyadicScale K), primeReciprocalFactor p := by
  induction K with
  | zero => simp [dyadicScale]
  | succ K ih =>
    rw [Finset.prod_range_succ, ih, layer_product_eq_interval]
    exact Finset.prod_Ico_consecutive _
      (by unfold dyadicScale; exact Nat.le_self_pow (by omega) 2)
      (by rw [dyadicScale_succ]; omega)

lemma primeReciprocalFactor_ge_one (p : ℕ) : 1 ≤ primeReciprocalFactor p := by
  unfold primeReciprocalFactor
  split_ifs with hp
  · rw [← inverse_euler_eq p hp]
    exact inverse_euler_ge_one p hp
  · rfl

lemma reciprocalPrefix_mono : Monotone reciprocalPrefix := by
  apply monotone_nat_of_le_succ
  intro n
  unfold reciprocalPrefix
  rw [Finset.prod_range_succ]
  exact le_mul_of_one_le_right (Finset.prod_nonneg (fun i hi => primeReciprocalFactor_nonneg _))
    (primeReciprocalFactor_ge_one _)

lemma finite_E_product_lt (m : ℕ → ℕ) :
    (∏ k ∈ Finset.range 16, E_val 2 k (m k)) < (211/10 : ℝ) := by
  have hle : (∏ k ∈ Finset.range 16, E_val 2 k (m k)) ≤
      ∏ k ∈ Finset.range 16, ∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹ :=
    Finset.prod_le_prod (fun k hk => zero_le_one.trans (E_val_ge_one _ _ _))
      (fun k hk => E_val_le_full_product _ _ _)
  rw [layer_products_telescope] at hle
  have heq : (∏ p ∈ Finset.Ico 2 (dyadicScale 16), primeReciprocalFactor p) =
      reciprocalPrefix 131070 := by
    rw [Finset.prod_Ico_eq_prod_range]
    norm_num only [dyadicScale, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub]
    simp only [reciprocalPrefix, Nat.add_comm]
  rw [heq] at hle
  exact (hle.trans (reciprocalPrefix_mono (by norm_num : 131070 ≤ 131071))).trans_lt
    reciprocalPrefix_131071_lt

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490/ParameterProduct.lean` -/

section


noncomputable section
open Finset BigOperators
set_option maxHeartbeats 800000

lemma rectangleCap_ratio (k : ℕ) : rectangleCap k / Y_val 2 k ≤
    (4/5 : ℝ)*geometricRatio^(k+1) := by
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hq : 0 < geometricRatio^(k+1) := pow_pos geometricRatio_pos _
  have hpow := one_le_pow₀ geometricRatio_cube (n := k+1)
  have heq : (2*geometricRatio^3)^(k+1) =
      Y_val 2 k * (geometricRatio^(k+1))^2 * geometricRatio^(k+1) := by
    rw [Y_val_two]
    simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_mul]
    ring
  rw [heq] at hpow
  apply (div_le_iff₀ hY).mpr
  unfold rectangleCap
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  nlinarith

lemma dyadic_tail_scale (k : ℕ) (hk : 16 ≤ k) : (131072 : ℝ) ≤ Y_val 2 k := by
  rw [Y_val_two]
  have h : dyadicScale 16 ≤ dyadicScale k := by
    unfold dyadicScale
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h

lemma rectangle_log_tail_bound (k : ℕ) (hk : 16 ≤ k) :
    Real.log (E_val 2 k (rectangleMultiplicity k)) ≤
      ((4/5 : ℝ)*131072/131071)*geometricRatio^(k+1) := by
  have hY := dyadic_tail_scale k hk
  have hYpos : 0 < Y_val 2 k := by linarith
  have hden : 0 < Y_val 2 k-1 := by linarith
  have hcap : (rectangleMultiplicity k : ℝ) ≤ rectangleCap k := by
    have hm : rectangleMultiplicity k ≤ ⌊rectangleCap k⌋₊ := by
      simp only [rectangleMultiplicity, if_neg (by omega : ¬ k < 16)]
      exact min_le_right _ _
    exact (Nat.cast_le.mpr hm).trans (Nat.floor_le (by unfold rectangleCap; positivity [geometricRatio_pos]))
  have hratio : Y_val 2 k/(Y_val 2 k-1) ≤ (131072/131071 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    _ ≤ (rectangleMultiplicity k : ℝ)/(Y_val 2 k-1) :=
      log_E_val_le _ _ _ (by linarith)
    _ ≤ rectangleCap k/(Y_val 2 k-1) := div_le_div_of_nonneg_right hcap hden.le
    _ = (rectangleCap k/Y_val 2 k)*(Y_val 2 k/(Y_val 2 k-1)) := by field_simp
    _ ≤ ((4/5 : ℝ)*geometricRatio^(k+1))*(131072/131071) :=
      mul_le_mul (rectangleCap_ratio k) hratio (by positivity) (by positivity [geometricRatio_pos])
    _ = _ := by ring

lemma geometric_shift_hasSum (K : ℕ) :
    HasSum (fun k : ℕ => geometricRatio^(k+K)) (geometricRatio^K/(1-geometricRatio)) := by
  simpa [pow_add, mul_comm, div_eq_mul_inv] using
    HasSum.mul_left (geometricRatio^K)
      (hasSum_geometric_of_lt_one geometricRatio_pos.le geometricRatio_lt_one)

lemma rectangle_log_summable : Summable (fun k => Real.log (E_val 2 k (rectangleMultiplicity k))) := by
  apply (summable_nat_add_iff 16).mp
  apply ((geometric_shift_hasSum 17).summable.mul_left ((4/5 : ℝ)*131072/131071)).of_nonneg_of_le
  · intro k
    exact Real.log_nonneg (E_val_ge_one _ _ _)
  · intro k
    simpa only [Nat.add_assoc] using rectangle_log_tail_bound (k+16) (by omega)

lemma rectangle_log_tail_sum_lt :
    ∑' k, Real.log (E_val 2 (k+16) (rectangleMultiplicity (k+16))) < (77/1000 : ℝ) := by
  have hs := (summable_nat_add_iff 16).mpr rectangle_log_summable
  have h := Summable.tsum_le_tsum
    (fun k => by simpa only [Nat.add_assoc] using rectangle_log_tail_bound (k+16) (by omega)) hs
    ((geometric_shift_hasSum 17).summable.mul_left ((4/5 : ℝ)*131072/131071))
  rw [tsum_mul_left, (geometric_shift_hasSum 17).tsum_eq] at h
  refine h.trans_lt ?_
  norm_num [geometricRatio]

lemma exp_small_bound : Real.exp (77/1000 : ℝ) < (1081/1000 : ℝ) := by
  have h := Real.exp_bound (show |(77/1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 8 by norm_num)
  norm_num at h
  linarith [abs_le.mp h]

lemma rectangle_D_lt : D_val 2 rectangleMultiplicity < 23 := by
  have heq : D_val 2 rectangleMultiplicity =
      (∏ k ∈ range 16, E_val 2 k (rectangleMultiplicity k)) *
      Real.exp (∑' k, Real.log (E_val 2 (k+16) (rectangleMultiplicity (k+16)))) := by
    unfold D_val
    rw [← rectangle_log_summable.sum_add_tsum_nat_add 16, Real.exp_add, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact Real.exp_log (zero_lt_one.trans_le (E_val_ge_one _ _ _))
  rw [heq]
  have he := (Real.exp_lt_exp.mpr rectangle_log_tail_sum_lt).trans exp_small_bound
  have hp := finite_E_product_lt rectangleMultiplicity
  have h := mul_lt_mul hp he.le (Real.exp_pos _) (by norm_num : (0 : ℝ) ≤ 211/10)
  linarith

lemma exp_gamma_lt : Real.exp γ < 1785/1000 := by
  have h_exp_bound : Real.exp (579/1000 : ℝ) < 1785/1000 := by
    have h := Real.exp_bound (show |(579/1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 20 by norm_num)
    norm_num at h
    linarith [abs_le.mp h]
  exact (Real.exp_le_exp.mpr (le_of_lt gamma_lt_tight)).trans_lt h_exp_bound

lemma rectangle_constant_lt :
    (111/100 : ℝ)^2 * Real.exp γ * D_val 2 rectangleMultiplicity /
      (1-weightTotal (rectangleWeight rectangleMultiplicity rectangleGrowth))^2 < 60 := by
  have hΩ := rectangle_weightTotal_lt
  have hD := rectangle_D_lt
  have hγ := exp_gamma_lt
  have hden : (1-(77/1000 : ℝ))^2 ≤
      (1-weightTotal (rectangleWeight rectangleMultiplicity rectangleGrowth))^2 := by
    nlinarith
  calc
    _ ≤ (111/100 : ℝ)^2 * Real.exp γ * D_val 2 rectangleMultiplicity / (1-77/1000)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)) (by norm_num) hden
    _ < (111/100 : ℝ)^2 * (1785/1000) * 23 / (1-77/1000)^2 := by
      gcongr
      exact Real.exp_nonneg _
    _ < 60 := by norm_num

end

end


/-! ### Upstream module `src/latest/ErdosProblems/Erdos490.lean` -/

section

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 490.
https://www.erdosproblems.com/forum/thread/490

Informal authors of the original argument:
- Endre Szemerédi
- ChatGPT 5.5 Pro

Formal authors of the original formalization:
- Aristotle
- Wouter van Doorn

Axiom-free analytic replacement and rectangle-counting proof: Codex.

URLs for the original argument and formalization:
- https://www.erdosproblems.com/forum/thread/490#post-6497
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem490.lean
-/


/-!
# Erdős problem 490, with constant 60 and no additional axioms

The proof uses an elementary factorial estimate for the Chebyshev function,
the proved Mertens product theorem, a weighted deletion argument, and disjoint
quotient rectangles. Dyadic layers and a kernel-checked finite Euler-product
certificate give an asymptotic constant below 60. No explicit Dusart estimates
are assumed. See the submodules for the analytic and numerical details.
-/


/-- If n is large enough, then every n-admissible pair satisfies
    |A|·|B| < 60 · n²/log n. -/
theorem erdos_490 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
        (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
          a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
        A.card * B.card < 60 * n ^ 2 / Real.log n := by
  obtain ⟨N₀, hN₀⟩ := rectangle_layer_bound rectangleMultiplicity rectangleGrowth
    rectangleGrowth_ge_one rectangleGrowth_tendsto rectangle_log_summable
    rectangle_weights_summable (by linarith [rectangle_weightTotal_lt]) 60 rectangle_constant_lt
  exact ⟨N₀, fun n hn A B hA hB hinj => hN₀ n hn A B ⟨hA, hB, hinj⟩⟩

end


#print axioms erdos_490
-- 'Erdos490.erdos_490' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos490
