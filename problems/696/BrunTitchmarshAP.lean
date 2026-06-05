/-
# Brun–Titchmarsh inequality (AP form) for Erdős problem 696

Discharges the `brun_titchmarsh` axiom in `Erdos696.lean`.
Strategy: lean-pool's `SelbergSieve4` interval form + restricted Mertens
+ Solymosi-style choice of sieve level. See `PLAN-brun-titchmarsh.md`.
-/
import Mathlib
import Mertens
import SelbergSieve4
import Erdos696Common

namespace Erdos696BT

open scoped BigOperators Topology ArithmeticFunction.omega
open Filter Real Nat

/-! ## Restricted Mertens product

We need the asymptotic `∏_{p ≤ N, p ∤ q} (1 - 1/p) · log N → e^{-γ} · q / φ(q)`.
Reduce to `Mertens.mertens_equation_15` (the unrestricted form, already proved)
by splitting the product at primes dividing `q`.
-/

/-- Product of `(1 - 1/p)` over primes `p ≤ N` that do not divide `q`. -/
noncomputable def mertensRestrictedProd (q N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), (1 - 1 / (p : ℝ))

/-- Product of `(1 - 1/p)` over primes `p` dividing `q`. Equals `φ(q)/q` for `q ≥ 1`. -/
noncomputable def primeDivProd (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))

lemma primeDivProd_eq_phi_div (q : ℕ) (hq : q ≠ 0) :
    primeDivProd q = (q.totient : ℝ) / q := by
  have hQ : (Nat.totient q : ℚ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors q
  -- Cast ℚ → ℝ via Rat.cast.
  have hR : (Nat.totient q : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg ((↑) : ℚ → ℝ) hQ
    push_cast at this
    exact_mod_cast this
  unfold primeDivProd
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h_eq : (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) =
      ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [one_div]
  rw [h_eq, eq_div_iff hq', mul_comm, ← hR]

/-- For `N ≥ q`, every prime factor of `q` is at most `N`. -/
lemma primeFactors_subset_of_le {q N : ℕ} (hq : q ≠ 0) (h : q ≤ N) :
    q.primeFactors ⊆ (Finset.range (N + 1)).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range]
  rw [Nat.mem_primeFactors] at hp
  refine ⟨?_, hp.1⟩
  calc p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hp.2.1
    _ ≤ N := h
    _ < N + 1 := Nat.lt_succ_self _

/-- For `N ≥ q`, primes ≤ N split into those dividing q and those not.
This is the key factorization. -/
lemma mertensProd_eq_restricted_mul (q N : ℕ) (hq : q ≠ 0) (hN : q ≤ N) :
    Mertens.mertensProd N = primeDivProd q * mertensRestrictedProd q N := by
  classical
  unfold Mertens.mertensProd mertensRestrictedProd primeDivProd
  -- The set {p ≤ N : prime, p | q} equals q.primeFactors when q ≤ N.
  have h_subset_eq : ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p ∣ q) =
      q.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp_prime⟩, hp_dvd⟩
      exact ⟨hp_prime, hp_dvd, hq⟩
    · rintro ⟨hp_prime, hp_dvd, _⟩
      have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hp_dvd
      exact ⟨⟨by omega, hp_prime⟩, hp_dvd⟩
  -- Split (filter Prime) into (filter dvd) and (filter not dvd).
  have h_split : (Finset.range (N + 1)).filter Nat.Prime =
      ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p ∣ q) ∪
      ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ q) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  rw [h_split, Finset.prod_union (Finset.disjoint_filter.mpr (fun _ _ h h' => h' h))]
  congr 1
  · rw [h_subset_eq]
  · -- The "not dvd" filter equals filter (Prime ∧ ¬ p∣q) on the original range.
    apply Finset.prod_nbij' id id <;>
      simp +contextual [Finset.mem_filter, Finset.mem_range, and_assoc]

/-- The restricted Mertens product times log N tends to e^{-γ} · q / φ(q). -/
theorem mertens_restricted (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => mertensRestrictedProd q N * Real.log N) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * (q : ℝ) / (q.totient : ℝ))) := by
  have hq' : q ≠ 0 := by omega
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hφ_ne : (q.totient : ℝ) ≠ 0 := by exact_mod_cast hφ_pos.ne'
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq'
  -- Eventually equal to `mertensProd N · log N · q / φ(q)`.
  have h_eq : ∀ᶠ N in atTop, mertensRestrictedProd q N * Real.log N =
      (Mertens.mertensProd N * Real.log N) * ((q : ℝ) / (q.totient : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop q] with N hN
    have h := mertensProd_eq_restricted_mul q N hq' hN
    have hφ := primeDivProd_eq_phi_div q hq'
    rw [hφ] at h
    -- h : mertensProd N = (φ q / q) * mertensRestrictedProd q N
    have : mertensRestrictedProd q N = Mertens.mertensProd N * (q : ℝ) / (q.totient : ℝ) := by
      rw [h]; field_simp
    rw [this]; ring
  rw [Filter.tendsto_congr' h_eq]
  have h_const : Tendsto (fun _ : ℕ => (q : ℝ) / (q.totient : ℝ)) atTop
      (𝓝 ((q : ℝ) / (q.totient : ℝ))) := tendsto_const_nhds
  have h_target : Real.exp (-Real.eulerMascheroniConstant) * (q : ℝ) / (q.totient : ℝ) =
      Real.exp (-Real.eulerMascheroniConstant) * ((q : ℝ) / (q.totient : ℝ)) := by
    field_simp
  rw [h_target]
  exact Filter.Tendsto.mul Mertens.mertens_equation_15 h_const

/-! ## AP sieve setup -/

open scoped ArithmeticFunction.zeta

/-- The product of primes ≤ N that do not divide q. -/
noncomputable def primorialRestricted (q N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), p

lemma primorialRestricted_squarefree (q N : ℕ) : Squarefree (primorialRestricted q N) := by
  unfold primorialRestricted
  apply PrimeUpperBound.prodDistinctPrimes_squarefree
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.2.1

/-- Number of primes in `[a₀, b]` in residue class `a (mod q)`. -/
noncomputable def primesBetween_AP (a₀ b : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Icc (Nat.ceil a₀) (Nat.floor b)).filter
    (fun n => n.Prime ∧ n % q = a % q)).card

/-- Sieve restricted to integers in `(x, x+y]` lying in `a (mod q)`. -/
noncomputable def primeInterSieveAP
    (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) : LPSelbergSieve where
  support := (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun n => n % q = a % q)
  prodPrimes := primorialRestricted q (Nat.floor z)
  prodPrimes_squarefree := primorialRestricted_squarefree q _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz

/-! ## AP cardinality lemmas (CRT) -/

/-- For `d` coprime to `q`, the joint condition "d ∣ x" and "x ≡ a (mod q)" reduces
to "x ≡ k (mod dq)" where `k = chineseRemainder hdq 0 a`. -/
private lemma joint_iff_crt {d q a : ℕ} (hd : d ≠ 0) (hq : 1 ≤ q) (hdq : Nat.Coprime d q) :
    ∀ x : ℕ,
      (d ∣ x ∧ x ≡ a [MOD q]) ↔
      x ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)] := by
  intro x
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  have hk_props : k ≡ 0 [MOD d] ∧ k ≡ a [MOD q] := (Nat.chineseRemainder hdq 0 a).property
  constructor
  · rintro ⟨hdx, hxq⟩
    -- x ≡ 0 (mod d) and x ≡ a (mod q); k satisfies the same. So x ≡ k mod both.
    have hxd : x ≡ k [MOD d] := by
      have h1 : x ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).mpr hdx
      exact h1.trans hk_props.1.symm
    have hxq' : x ≡ k [MOD q] := hxq.trans hk_props.2.symm
    exact (Nat.modEq_and_modEq_iff_modEq_mul hdq).mp ⟨hxd, hxq'⟩
  · intro hcrt
    have hxd : x ≡ k [MOD d] := hcrt.of_mul_right q
    have hxq : x ≡ k [MOD q] := hcrt.of_mul_left d
    refine ⟨?_, hxq.trans hk_props.2⟩
    exact (Nat.modEq_zero_iff_dvd).mp (hxd.trans hk_props.1)

/-- multSum for the AP sieve at a divisor `d` coprime to `q`, expressed as a count. -/
theorem multSum_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).multSum d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card) := by
  unfold LPSieve.multSum
  simp only [primeInterSieveAP, Finset.sum_boole]
  -- Goal: (filter (d ∣ ·) ((Icc ⌈x⌉ ⌊x+y⌋).filter (· % q = a % q))).card = ...
  rw [Nat.cast_inj]
  -- Reduce Icc to Ioc (⌈x⌉-1)
  rw [show ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun n => n % q = a % q)).filter (fun n => d ∣ n) =
      (Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
      (fun n => d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])
    from ?_]
  · -- Now strip the `d ∣ n` part using joint_iff_crt
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hdx, hcrt⟩; exact hcrt
    · intro hcrt
      have : d ∣ x ∧ x ≡ a [MOD q] := (joint_iff_crt hd hq hdq x).mpr hcrt
      exact ⟨this.1, hcrt⟩
  · -- The set equality
    have h_icc_ioc : Finset.Icc (Nat.ceil x) (Nat.floor (x+y)) =
        Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) := by
      rw [← Finset.Icc_succ_left_eq_Ioc]
      congr
      simpa [Nat.pred_eq_sub_one] using
        (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
    rw [h_icc_ioc]
    -- Combine the two filters into one
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have hiff : (d ∣ n ∧ n % q = a % q) ↔
        (d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)]) := by
      constructor
      · rintro ⟨hdn, hnq⟩
        have : n ≡ a [MOD q] := hnq
        exact ⟨hdn, (joint_iff_crt hd hq hdq n).mp ⟨hdn, this⟩⟩
      · rintro ⟨hdn, hcrt⟩
        have : d ∣ n ∧ n ≡ a [MOD q] := (joint_iff_crt hd hq hdq n).mpr hcrt
        exact ⟨hdn, this.2⟩
    tauto

/-- The remainder term for the AP sieve at coprime `d`. -/
theorem rem_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).rem d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card)
      - (↑d)⁻¹ * (y / (q : ℝ)) := by
  unfold LPSieve.rem
  rw [multSum_AP_eq x y z hx q a hq hz hd hdq]
  simp [primeInterSieveAP, if_neg hd]

/-- `|⌊r⌋ - r| ≤ 1` for real `r`. -/
private lemma abs_floor_sub_le (r : ℝ) : |((⌊r⌋ : ℤ) : ℝ) - r| ≤ 1 := by
  have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
  have h2 : r < ⌊r⌋ + 1 := Int.lt_floor_add_one r
  rw [abs_le]
  constructor <;> linarith

/-- Pushing `Int.floor` through `ℚ → ℝ` cast. -/
private lemma floor_rat_cast_eq_floor_real (r : ℚ) :
    ((⌊r⌋ : ℤ) : ℝ) = ((⌊(r : ℝ)⌋ : ℤ) : ℝ) := by
  congr 1; exact (Rat.floor_cast r).symm

/-- The count of integers ≡ v mod m in `Ioc a b` is within 2 of `(b - a) / m`,
provided `a ≤ b`. -/
private lemma abs_count_modEq_sub_le (a b m v : ℕ) (hm : 0 < m) (hab : a ≤ b) :
    |(((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ)
        - ((b : ℝ) - a) / m| ≤ 2 := by
  have hcount : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℤ) =
      max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 :=
    Nat.Ioc_filter_modEq_card a b hm v
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm
  have h_q_to_R_b : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have h_q_to_R_a : ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have hN_eq : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ) =
      ((max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hN_eq]
  set FbR : ℝ := ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFbR_def
  set FaR : ℝ := ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFaR_def
  have hb_close : |FbR - (((b : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have ha_close : |FaR - (((a : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have h_FF_close : |(FbR - FaR) - (((b : ℝ) - a) / m)| ≤ 2 := by
    have heq : (FbR - FaR) - (((b : ℝ) - a) / m) =
        (FbR - ((b : ℝ) - v) / m) - (FaR - ((a : ℝ) - v) / m) := by field_simp; ring
    rw [heq]
    calc |(FbR - (((b : ℝ) - v) / m)) - (FaR - (((a : ℝ) - v) / m))|
        ≤ |FbR - (((b : ℝ) - v) / m)| + |FaR - (((a : ℝ) - v) / m)| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  by_cases h : (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋ : ℤ) ≤ 0
  · rw [max_eq_right h]
    push_cast
    have h_floor_le : FbR ≤ FaR := by
      have hZ : (⌊((b : ℚ) - v) / m⌋ : ℤ) ≤ ⌊((a : ℚ) - v) / m⌋ := by linarith
      have hZ_R : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) ≤ ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) := by
        exact_mod_cast hZ
      rw [h_q_to_R_b, h_q_to_R_a] at hZ_R; exact hZ_R
    have hbv : (((b : ℝ) - v) / m) ≤ FbR + 1 := by rw [abs_le] at hb_close; linarith
    have hav : FaR ≤ (((a : ℝ) - v) / m) + 1 := by rw [abs_le] at ha_close; linarith
    have hba_le : ((b : ℝ) - a) / m ≤ 2 := by
      have : (((b : ℝ) - v) / m) - (((a : ℝ) - v) / m) = ((b : ℝ) - a) / m := by
        field_simp; ring
      linarith
    have hba_nn : 0 ≤ ((b : ℝ) - a) / m := by
      apply div_nonneg
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      · linarith
    rw [abs_le]; constructor <;> linarith
  · push_neg at h
    rw [max_eq_left h.le]
    push_cast
    rw [h_q_to_R_b, h_q_to_R_a]
    show |FbR - FaR - ((b : ℝ) - a) / m| ≤ 2
    exact h_FF_close

/-- Bound the AP remainder by a fixed constant `5 = 2 + 3`. -/
theorem abs_rem_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ) (hq : 1 ≤ q)
    (hz : 1 ≤ z) {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    |(primeInterSieveAP x y z q a hq hz).rem d| ≤ 5 := by
  rw [rem_AP_eq x y z hx q a hq hz hd hdq]
  set b : ℕ := Nat.floor (x + y) with hb_def
  set a' : ℕ := Nat.ceil x - 1 with ha_def
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  set m : ℕ := d * q with hm_def
  have hm_pos : 0 < m := Nat.mul_pos (Nat.pos_of_ne_zero hd) hq
  have hd_R : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hab : a' ≤ b := by
    rw [ha_def, hb_def]
    have h_ceil_le : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
    have h_floor_le : Nat.floor x ≤ Nat.floor (x + y) := Nat.floor_mono (by linarith)
    omega
  have h_step1 := abs_count_modEq_sub_le a' b m k hm_pos hab
  set N : ℝ := (((Finset.Ioc a' b).filter (fun n => n ≡ k [MOD m])).card : ℝ) with hN_def
  have h_bx : |((b : ℝ) - (x + y))| ≤ 1 := by
    have h1 : (Nat.floor (x + y) : ℝ) ≤ x + y := Nat.floor_le (by linarith)
    have h2 : x + y < (Nat.floor (x + y) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hb_def]; rw [abs_le]; constructor <;> linarith
  have ha'_eq : (a' : ℝ) + 1 = (Nat.ceil x : ℝ) := by
    have h_ceil_ge_1 : 1 ≤ Nat.ceil x := Nat.ceil_pos.mpr hx
    rw [ha_def]
    push_cast [Nat.cast_sub h_ceil_ge_1]
    ring
  have h_ceil : |((Nat.ceil x : ℝ) - x)| ≤ 1 := by
    have h1 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx)
    rw [abs_le]; constructor <;> linarith
  have h_step2 : |((b : ℝ) - a') / m - y / m| ≤ 3 := by
    have h_num : |((b : ℝ) - a') - y| ≤ 3 := by
      have heq : (b : ℝ) - a' - y = ((b : ℝ) - (x + y)) - ((a' : ℝ) + 1 - x) + 1 := by ring
      rw [heq, ha'_eq]
      have h_abs_one : |(1 : ℝ)| = 1 := abs_one
      have h_sub_abs := abs_sub ((b : ℝ) - (x + y)) ((Nat.ceil x : ℝ) - x)
      calc |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x) + 1|
          ≤ |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x)| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ (|((b : ℝ) - (x + y))| + |((Nat.ceil x : ℝ) - x)|) + 1 := by linarith
        _ ≤ (1 + 1) + 1 := by linarith
        _ = 3 := by norm_num
    have hdiv : (((b : ℝ) - a') / m - y / m) = ((b : ℝ) - a' - y) / m := by rw [← sub_div]
    rw [hdiv, abs_div, abs_of_pos hm_R]
    have hm_ge_1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
    calc |((b : ℝ) - a' - y)| / m ≤ 3 / m := by gcongr
      _ ≤ 3 := by rw [div_le_iff₀ hm_R]; linarith
  have hyqm : ((d : ℝ))⁻¹ * (y / q) = y / m := by
    rw [hm_def]; push_cast; field_simp
  rw [hyqm]
  show |N - y / m| ≤ 5
  calc |N - y / m|
      = |(N - ((b : ℝ) - a') / m) + (((b : ℝ) - a') / m - y / m)| := by congr 1; ring
    _ ≤ |N - ((b : ℝ) - a') / m| + |((b : ℝ) - a') / m - y / m| := abs_add_le _ _
    _ ≤ 2 + 3 := by linarith
    _ = 5 := by norm_num

/-- Every divisor of `primorialRestricted q N` is coprime to `q`. -/
private lemma coprime_of_dvd_primorialRestricted (q N : ℕ) {d : ℕ} (hd_pos : 0 < d)
    (hd : d ∣ primorialRestricted q N) : Nat.Coprime d q := by
  rw [Nat.Coprime]
  by_contra h_ne
  have h_gcd_pos : 1 < Nat.gcd d q := by
    have h_gcd_ne_zero : Nat.gcd d q ≠ 0 := by
      intro h
      rw [Nat.gcd_eq_zero_iff] at h
      omega
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d q ≠ 1)
  have hpd : p ∣ d := hp_dvd.trans (Nat.gcd_dvd_left d q)
  have hpq : p ∣ q := hp_dvd.trans (Nat.gcd_dvd_right d q)
  have hp_in_prim : p ∣ primorialRestricted q N := hpd.trans hd
  unfold primorialRestricted at hp_in_prim
  obtain ⟨p', hp'_mem, hp_dvd_p'⟩ :=
    Prime.exists_mem_finset_dvd hp_prime.prime hp_in_prim
  rw [Finset.mem_filter] at hp'_mem
  have ⟨_, hp'_prime, hp'_ndvd⟩ := hp'_mem
  have hp_eq_p' : p = p' :=
    (Nat.prime_dvd_prime_iff_eq hp_prime hp'_prime).mp hp_dvd_p'
  rw [hp_eq_p'] at hpq
  exact hp'_ndvd hpq

/-- Variant of lean-pool's `rem_sum_le_of_const` where the bound only needs to hold
for divisors of `prodPrimes`. -/
private theorem rem_sum_le_of_const_dvd (s : LPSelbergSieve) (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ d, 0 < d → d ∣ s.prodPrimes → |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toLPSieve.prodPrimes.divisors), (3 : ℝ) ^ ω d * C)
  · apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_ne_zero
    have h_bound : |s.rem d| ≤ C := hrem d hd_pos hd.1.1
    have h_pow_nn : (0 : ℝ) ≤ (3 : ℝ) ^ ω d := pow_nonneg (by norm_num) _
    have h_abs_nn : (0 : ℝ) ≤ |s.rem d| := abs_nonneg _
    nlinarith
  rw [show C * s.level * (1 + Real.log s.level)^3 =
      C * (s.level * (1 + Real.log s.level)^3) from by ring]
  simp_rw [show ∀ i, (3 : ℝ) ^ ω i * C = C * (3 : ℝ) ^ ω i from fun i => by ring]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  rw [Finset.sum_filter]
  have := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (P := s.prodPrimes) (h := 3)
    s.level s.one_le_level s.prodPrimes_squarefree
  push_cast at this
  convert this using 2

/-- Sum of `3^ω(d) · |rem(d)|` over divisors of prodPrimes ≤ z bounded by `5z(1+log z)^3`. -/
theorem primeSieve_rem_sum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ∑ d ∈ (primeInterSieveAP x y z q a hq hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ (primeInterSieveAP x y z q a hq hz).level then
        (3 : ℝ) ^ ω d * |(primeInterSieveAP x y z q a hq hz).rem d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  apply rem_sum_le_of_const_dvd (primeInterSieveAP x y z q a hq hz) 5 (by norm_num)
  intro d hd_pos hd_dvd
  have hd_coprime : Nat.Coprime d q :=
    coprime_of_dvd_primorialRestricted q (Nat.floor z) hd_pos hd_dvd
  exact abs_rem_AP_le x y z hx hy q a hq hz hd_pos.ne' hd_coprime

/-! ## Lower bound on Selberg bounding sum (AP form)

We prove `selbergBoundingSum ≥ log(z) · φ(q) / (4q)` under the strong hypothesis
`16 q^4 ≤ z`. Strategy:
1. Lower-bound `selbergBoundingSum` by `∑_{m ∈ [1, ⌊√z⌋], gcd(m,q)=1} 1/m` (adapting
   the `selbergBoundingSum_ge_sum_div` proof from lean-pool).
2. Bound the coprime harmonic sum by a block-counting argument:
   `∑_{m ≤ Mq, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · log(M+1)`.
3. Choose `M = ⌊⌊√z⌋/q⌋`. With `16q^4 ≤ z`, get `M+1 ≥ 3 z^{1/4}/2 ≥ z^{1/4}`,
   so `log(M+1) ≥ log(z)/4`.
-/

/-- Helper: the radical of `m` (coprime to `q`, bounded by `z`) divides
`primorialRestricted q ⌊z⌋`. -/
private lemma rad_dvd_primorialRestricted
    (q : ℕ) (z : ℝ) (hz : 1 ≤ z) {m : ℕ} (hm_pos : 0 < m) (hm_le : (m : ℝ) ≤ z)
    (hmq : Nat.Coprime m q) :
    (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z) := by
  unfold primorialRestricted
  apply Finset.prod_dvd_prod_of_subset
  intro p hp_in
  rw [Nat.mem_primeFactors] at hp_in
  obtain ⟨hp_prime, hp_dvd, _⟩ := hp_in
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm_pos hp_dvd
  have hp_le_z : (p : ℝ) ≤ z := by
    calc (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hp_le_m
      _ ≤ z := hm_le
  have hp_le_floor : p ≤ Nat.floor z := Nat.le_floor hp_le_z
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hdvd_gcd : p ∣ Nat.gcd m q := Nat.dvd_gcd hp_dvd hpq
    rw [Nat.Coprime] at hmq
    rw [hmq] at hdvd_gcd
    exact hp_prime.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd_gcd)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp_prime, hp_not_dvd_q⟩

/-- Lower bound for the AP-sieve Selberg bounding sum by the coprime harmonic sum.
This is the AP-analogue of `boundingSum_ge_sum`, adapted from `selbergBoundingSum_ge_sum_div`
in lean-pool. The key change is that we restrict the inner sum to `m` coprime to `q`. -/
private lemma selbergBoundingSum_AP_ge_coprime_sum (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hnu_cm : PrimeUpperBound.CompletelyMultiplicative s.nu :=
    PrimeUpperBound.CompletelyMultiplicative.zeta.pdiv PrimeUpperBound.CompletelyMultiplicative.id
  have hnu_nonneg : ∀ n, 0 ≤ s.nu n := by
    intro n
    show 0 ≤ ((ζ : ArithmeticFunction ℝ).pdiv .id) n
    by_cases h : n = 0
    · simp [h]
    · apply div_nonneg
      · simp [h]
      · simp
  have hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1 := s.nu_lt_one_of_prime
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt z := Real.sqrt_nonneg z
  -- Chain of inequalities mirroring lean-pool's selbergBoundingSum_ge_sum_div.
  show s.selbergBoundingSum ≥ _
  dsimp only [LPSelbergSieve.selbergBoundingSum]
  calc ∑ l ∈ s.prodPrimes.divisors,
          (if ((l ^ 2 : ℕ) : ℝ) ≤ s.level then s.selbergTerms l else 0)
      ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => ((l ^ 2 : ℕ) : ℝ) ≤ s.level),
          ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
    _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt s.level))).filter
            (fun m => Nat.Coprime m q), s.nu m := ?_
    _ = ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
            (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := ?_
  · -- First leg: identical to the lean-pool proof.
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [PrimeUpperBound.prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu_cm
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]; exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply PrimeUpperBound.prod_factors_one_div_compMult_ge _ _ hnu_cm _ _ hlsq
      · intro p hpp hpl; exact hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  · -- Second leg: show the bi-union over l's contains every coprime m ≤ √z.
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hm_le⟩, hmq⟩ := hm
        have hm_pos : 0 < m := hm1
        have hm_ne_zero : m ≠ 0 := hm_pos.ne'
        have hm_le_R : (m : ℝ) ≤ Real.sqrt s.level := by
          calc (m : ℝ) ≤ (Nat.floor (Real.sqrt s.level) : ℝ) := by exact_mod_cast hm_le
            _ ≤ Real.sqrt s.level := Nat.floor_le hsqrt_nn
        have hm_le_z : (m : ℝ) ≤ s.level := by
          calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
            _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
        have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) :=
          Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
        have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
          pow_ne_zero _ hprod_pos.ne'
        rw [Finset.mem_biUnion]
        simp_rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨∏ p ∈ m.primeFactors, p, ?_, ?_⟩
        · refine ⟨⟨?_, s.prodPrimes_ne_zero⟩, ?_⟩
          · change (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z)
            exact rad_dvd_primorialRestricted q z hz hm_pos hm_le_z hmq
          · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]),
                Nat.cast_pow, Real.sqrt_sq]
            · trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_dvd hm_pos (Nat.prod_primeFactors_dvd m)
              · exact hm_le_R
            · norm_cast; omega
        · refine ⟨⟨?_, hprod_ne_zero⟩, Nat.prod_primeFactors_dvd m⟩
          rw [← Nat.factorization_le_iff_dvd hm_ne_zero hprod_ne_zero, Nat.factorization_pow]
          intro p
          have hy_mul_prod_nonneg :
              0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
            Nat.zero_le _
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
          swap
          · apply le_rfl
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
            exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
            exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
            apply Nat.le_floor
            calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
              _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
          · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hprod_pos.ne', pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
      · intro i _ _; apply hnu_nonneg
    · intro i hi j hj hij t hti htj n hn
      exfalso
      specialize hti hn
      specialize htj hn
      simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
      have hh : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ n → n ∣ j ^ ⌊s.level⌋₊ → i ∣ j := by
        intro i j n hiP hin hij
        apply PrimeUpperBound.nat_squarefree_dvd_pow i j _ (s.squarefree_of_dvd_prodPrimes hiP)
        exact Trans.trans hin hij
      have hidvdj : i ∣ j := hh i j hi.1.1 hti.2 htj.1.1
      have hjdvdi : j ∣ i := hh j i hj.1.1 htj.2 hti.1.1
      exact hij <| Nat.dvd_antisymm hidvdj hjdvdi
  · -- Final equality: ν(m) = 1/m for m ≥ 1, and s.level = z.
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm_ne : m ≠ 0 := by omega
    show ((ζ : ArithmeticFunction ℝ).pdiv .id) m = 1 / (m : ℝ)
    simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hm_ne, ArithmeticFunction.id_apply, one_div]

/-- For `q ≥ 1`, the number of integers in `(k·q, (k+1)·q]` coprime to `q` equals `φ(q)`. -/
private lemma card_block_coprime (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card
      = q.totient := by
  classical
  have hq_pos : 0 < q := hq
  -- Step 1: shift bijection — block of size q starting at k·q matches Ioc 0 q.
  have h_shift_card :
      ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card =
      ((Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q)).card := by
    apply Finset.card_bij (fun m _ => m - k * q)
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨h1, h2⟩, hmq⟩ := hm
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at h2
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq : m = (m - k * q) + k * q := by omega
      rw [Nat.Coprime, heq, Nat.gcd_add_mul_right_left] at hmq
      exact hmq
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Ioc] at ha hb
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at ha hb
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h1, h2⟩, hnq⟩ := hn
      refine ⟨n + k * q, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hexp : (k + 1) * q = k * q + q := by ring
        omega
      · rw [Nat.Coprime, Nat.gcd_add_mul_right_left]
        exact hnq
  rw [h_shift_card]
  -- Step 2: |{m ∈ Ioc 0 q : Coprime m q}| = φ(q).
  rw [Nat.totient_eq_card_coprime]
  -- target: #{m ∈ Ioc 0 q | m.Coprime q} = #{a ∈ range q | q.Coprime a}
  -- bijection: identity (within the range), using Coprime symmetric.
  by_cases hq1 : q = 1
  · subst hq1
    -- Both sides have card 1.
    have h_left : (Finset.Ioc 0 1).filter (fun m => Nat.Coprime m 1) = {1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨one_pos, le_refl _⟩, Nat.coprime_one_right _⟩
    have h_right : (Finset.range 1).filter (fun a => Nat.Coprime 1 a) = {0} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, _⟩; omega
      · rintro rfl; exact ⟨one_pos, Nat.coprime_one_left _⟩
    rw [h_left, h_right]
    simp
  · have hq2 : 2 ≤ q := by omega
    have h_q_not_co : ¬ Nat.Coprime q q := by
      rw [Nat.Coprime, Nat.gcd_self]; omega
    have h_0_not_co : ¬ Nat.Coprime 0 q := by
      rw [Nat.Coprime, Nat.gcd_zero_left]; omega
    have h_0_not_co' : ¬ Nat.Coprime q 0 := by
      rw [Nat.Coprime, Nat.gcd_zero_right]; omega
    -- Show both filtered sets equal {a ∈ Ico 1 q : Coprime a q}.
    have hA : (Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        refine ⟨⟨h1, ?_⟩, hmq⟩
        by_contra hc; push_neg at hc
        have : m = q := by omega
        rw [this] at hmq; exact h_q_not_co hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩; exact ⟨⟨h1, by omega⟩, hmq⟩
    have hB : (Finset.range q).filter (fun a => Nat.Coprime q a) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hm, hmq⟩
        refine ⟨⟨?_, hm⟩, Nat.coprime_comm.mp hmq⟩
        by_contra hc; push_neg at hc
        have : m = 0 := by omega
        rw [this] at hmq; exact h_0_not_co' hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        exact ⟨h2, Nat.coprime_comm.mp hmq⟩
    rw [hA, hB]

/-- Coprime harmonic block bound:
`∑_{m ≤ M·q, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · ∑_{k=1}^M 1/k`. -/
private lemma coprime_harmonic_block_lower_bound (q : ℕ) (hq : 1 ≤ q) (M : ℕ) :
    ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  -- Partition Ioc 0 (Mq) into blocks ((k-1)q, kq] for k = 1..M (when M ≥ 1).
  -- We use the disjoint union: Ioc 0 (Mq) = ⋃_{k=0}^{M-1} Ioc (k·q) ((k+1)·q).
  -- Then sum over each block contributes ≥ φ(q)/((k+1)q).
  set blocks : ℕ → Finset ℕ := fun k =>
    (Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q) with hblocks_def
  have h_block_sum :
      (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q) =
        (Finset.range M).biUnion blocks := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_biUnion, Finset.mem_range,
      hblocks_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmq⟩
      refine ⟨(m - 1) / q, ?_, ?_⟩
      · -- (m-1)/q < M, since m ≤ Mq so m-1 < Mq, so (m-1)/q < M.
        rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
      · refine ⟨⟨?_, ?_⟩, hmq⟩
        · -- (m-1)/q * q < m
          have h_mod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
        · -- m ≤ ((m-1)/q + 1) * q
          have hadd : ((m - 1) / q + 1) * q = (m - 1) / q * q + q := by ring
          have hmod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
    · rintro ⟨k, hkM, ⟨⟨h_lo, h_hi⟩, hmq⟩⟩
      refine ⟨⟨?_, ?_⟩, hmq⟩
      · -- 0 < m: m > k*q ≥ 0.
        have : k * q ≥ 0 := Nat.zero_le _
        omega
      · -- m ≤ M*q
        calc m ≤ (k + 1) * q := h_hi
          _ ≤ M * q := by
            apply Nat.mul_le_mul_right
            omega
  rw [h_block_sum]
  rw [Finset.sum_biUnion]
  · -- Now: ∑_{k=0}^{M-1} ∑_{m ∈ blocks k} 1/m ≥ (φ(q)/q) ∑_{k=1}^M 1/k
    -- Re-index: k' = k+1 so k=0 ↔ k'=1.
    have h_reindex :
        ∑ k ∈ Finset.range M, ∑ m ∈ blocks k, (1 : ℝ) / (m : ℝ) =
        ∑ k ∈ Finset.Icc 1 M, ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ) := by
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk
        rw [Finset.mem_Icc]; rw [Finset.mem_range] at hk; omega
      · intro k _ k' _ hk; omega
      · intro k hk
        rw [Finset.mem_Icc] at hk
        refine ⟨k - 1, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · intro k _; simp
    rw [h_reindex]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < k := hk.1
    have hk_R : (0 : ℝ) < k := by exact_mod_cast hk_pos
    have hkq_R : (0 : ℝ) < (k * q : ℕ) := by exact_mod_cast Nat.mul_pos hk_pos hq_pos
    -- block (k-1) has φ(q) elements, each m ≤ k*q, so 1/m ≥ 1/(k*q).
    have hk1 : k - 1 + 1 = k := by omega
    have h_card_block : (blocks (k - 1)).card = q.totient :=
      card_block_coprime q hq (k - 1)
    -- Each m in block (k-1) satisfies m ≤ k*q.
    have h_le_kq : ∀ m ∈ blocks (k - 1), (m : ℝ) ≤ (k * q : ℕ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have hbound := hm.1.2
      rw [hk1] at hbound
      exact_mod_cast hbound
    have h_pos_m : ∀ m ∈ blocks (k - 1), 0 < (m : ℝ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have : 0 < m := by
        have : (k - 1) * q ≥ 0 := Nat.zero_le _
        omega
      exact_mod_cast this
    -- ∑_{m ∈ blocks} 1/m ≥ ∑_{m ∈ blocks} 1/(k*q) = card * 1/(k*q) = φ(q)/(k*q).
    calc ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ)
        ≥ ∑ _ ∈ blocks (k - 1), (1 : ℝ) / ((k * q : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm_pos : 0 < (m : ℝ) := h_pos_m m hm
          have hm_le := h_le_kq m hm
          apply one_div_le_one_div_of_le hm_pos hm_le
      _ = (blocks (k - 1)).card * (1 / ((k * q : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) * (1 / ((k * q : ℕ) : ℝ)) := by rw [h_card_block]
      _ = (q.totient : ℝ) / q * (1 / (k : ℝ)) := by
          push_cast; field_simp
  · -- Pairwise disjoint blocks
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm hm'
    simp only [hblocks_def, Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    -- m ∈ (i*q, (i+1)*q] and m ∈ (j*q, (j+1)*q] with i ≠ j: contradiction.
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi1q : (i + 1) * q ≤ j * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm.1.2
      have h2 := hm'.1.1
      omega
    · have hj1q : (j + 1) * q ≤ i * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm'.1.2
      have h2 := hm.1.1
      omega

/-- The main bound on the AP-sieve Selberg bounding sum.

With the hypothesis `16 q^4 ≤ z`, we have
`selbergBoundingSum ≥ (φ(q)/q) · log(z) / 4`.

The constant `1/4` is explicit. The hypothesis ensures `√z/q ≥ 4q ≥ 4` and
`z^{1/4}/q ≥ 2`, which together give enough room for the `log(z)/4` lower bound
after the elementary block-counting argument. -/
theorem boundingSum_AP_ge (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      Real.log z * (q.totient : ℝ) / (4 * q) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_nn : (0 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Step 0: hypothesis implications.
  have hq4_nn : (0 : ℝ) ≤ (q : ℝ)^4 := by positivity
  have hq4_ge_1 : (1 : ℝ) ≤ (q : ℝ)^4 := by
    apply one_le_pow₀; exact_mod_cast hq
  have hz4 : (16 : ℝ) ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hsqrt_z_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz_pos
  have hsqrt_z_ge_4 : Real.sqrt z ≥ 4 := by
    have h1 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4^2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)
    linarith [Real.sqrt_le_sqrt hz4, h1]
  -- 4 q² ≤ √z
  have h_4q2_le_sqrtz : 4 * (q : ℝ)^2 ≤ Real.sqrt z := by
    have h_sq : (4 * (q : ℝ)^2)^2 ≤ z := by
      have heq : (4 * (q : ℝ)^2)^2 = 16 * (q : ℝ)^4 := by ring
      linarith
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ)^2)]
    exact Real.sqrt_le_sqrt h_sq
  have h_q_le_sqrtz4 : (q : ℝ) ≤ Real.sqrt z / 4 := by
    -- From 4q² ≤ √z and q ≥ 1: q ≤ q² ≤ √z/4.
    have hq_ge_1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq2_ge_q : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith
    nlinarith
  -- Step 1: lower-bound by coprime harmonic sum.
  apply le_trans (b := ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)) ?_
    (selbergBoundingSum_AP_ge_coprime_sum x y z hx hy q a hq hz)
  -- Step 2: choose N = ⌊√z⌋, M = N / q.
  set N : ℕ := Nat.floor (Real.sqrt z) with hN_def
  have hN_R_le : (N : ℝ) ≤ Real.sqrt z := Nat.floor_le (le_of_lt hsqrt_z_pos)
  have hN_R_ge : (N : ℝ) ≥ Real.sqrt z - 1 := by
    rw [hN_def]
    linarith [Nat.lt_floor_add_one (Real.sqrt z)]
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set M : ℕ := N / q with hM_def
  have hMq_le_N : M * q ≤ N := Nat.div_mul_le_self N q
  -- Step 3: subset sum: Ioc 0 (M*q) ⊆ Icc 1 N.
  have h_subset_sum :
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
        ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
            (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm.1.1, hm.1.2.trans hMq_le_N⟩, hm.2⟩
    · intro i _ _
      positivity
  -- Step 4: apply block bound.
  have h_block := coprime_harmonic_block_lower_bound q hq M
  -- Step 5: bound H_M ≥ log(M+1) ≥ log z / 4.
  -- First show M + 1 ≥ √z/(2q) ≥ z^{1/4}/√? ... actually z^{1/4} ≥ z^{1/4}.
  have hM_R_ge : ((M : ℝ) + 1) ≥ (N : ℝ) / q := by
    -- M = N/q (nat div), so M*q ≤ N, hence (M+1)*q > N, hence M+1 > N/q.
    have h_lt : N < (M + 1) * q := by
      rw [hM_def]
      have h_mod : N % q < q := Nat.mod_lt _ hq_pos
      have h_div := Nat.div_add_mod N q
      have h_div' : N / q * q + N % q = N := by
        rw [Nat.mul_comm] at h_div; omega
      have : (N / q + 1) * q = N / q * q + q := by ring
      omega
    have h_R : ((M + 1 : ℕ) : ℝ) > (N : ℝ) / q := by
      rw [gt_iff_lt, div_lt_iff₀ hq_R]
      exact_mod_cast h_lt
    push_cast at h_R
    linarith
  have hM_R_ge' : ((M : ℝ) + 1) ≥ Real.sqrt z / (2 * q) := by
    -- N ≥ √z - 1, and √z - 1 ≥ √z / 2 (since √z ≥ 2).
    have h_N_ge_half : (N : ℝ) ≥ Real.sqrt z / 2 := by linarith
    have hNq : (N : ℝ) / q ≥ Real.sqrt z / (2 * q) := by
      rw [ge_iff_le, div_le_div_iff₀ (by linarith) hq_R]
      have : Real.sqrt z * q ≤ N * (2 * q) := by nlinarith
      linarith
    linarith
  -- Strategy: work with z^{1/4} via Real.rpow.
  have hzq4_pos : 0 < z^((1:ℝ)/4) := Real.rpow_pos_of_pos hz_pos _
  have hzq4_nn : 0 ≤ z^((1:ℝ)/4) := le_of_lt hzq4_pos
  have h_2q_le_zq : 2 * (q : ℝ) ≤ z^((1:ℝ)/4) := by
    -- From 16 q^4 ≤ z, get (2q)^4 ≤ z, hence 2q ≤ z^{1/4}.
    have h_2q4 : (2 * (q : ℝ))^4 ≤ z := by nlinarith
    have h_2q_nn : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
    -- Use Real.rpow_le_rpow_iff_left or similar.
    have h_z_eq : z = (z^((1:ℝ)/4))^4 := by
      rw [← Real.rpow_natCast (z^((1:ℝ)/4)) 4]
      rw [← Real.rpow_mul (le_of_lt hz_pos)]
      norm_num
    rw [h_z_eq] at h_2q4
    have := pow_le_pow_iff_left₀ h_2q_nn hzq4_nn (by norm_num : 4 ≠ 0) |>.mp h_2q4
    exact this
  -- √z = z^{1/2} = (z^{1/4})^2.
  have h_sqrt_eq : Real.sqrt z = z^((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
  have h_z14_sq : z^((1:ℝ)/2) = (z^((1:ℝ)/4))^2 := by
    rw [show ((1:ℝ)/2) = (1:ℝ)/4 * 2 from by norm_num,
      Real.rpow_mul (le_of_lt hz_pos)]
    rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have hM_R_ge_zq : ((M : ℝ) + 1) ≥ z^((1:ℝ)/4) := by
    -- M+1 ≥ √z/(2q). √z = (z^{1/4})^2. 2q ≤ z^{1/4}.
    -- So √z/(2q) ≥ (z^{1/4})^2/(z^{1/4}) = z^{1/4}.
    have h_sqrt_z : Real.sqrt z = (z^((1:ℝ)/4))^2 := by rw [h_sqrt_eq, h_z14_sq]
    have h_2q_pos : 0 < 2 * (q : ℝ) := by linarith
    calc (M : ℝ) + 1 ≥ Real.sqrt z / (2 * q) := hM_R_ge'
      _ = (z^((1:ℝ)/4))^2 / (2 * q) := by rw [h_sqrt_z]
      _ ≥ (z^((1:ℝ)/4))^2 / (z^((1:ℝ)/4)) := by
          apply div_le_div_of_nonneg_left (by positivity) h_2q_pos h_2q_le_zq
      _ = z^((1:ℝ)/4) := by
          rw [sq, mul_div_assoc, div_self hzq4_pos.ne', mul_one]
  -- H_M ≥ log(M+1) ≥ log(z^{1/4}) = log(z)/4.
  have h_HM : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≥ Real.log z / 4 := by
    have h_inv : ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ ≥ Real.log (M + 1 : ℕ) :=
      Aux.log_add_one_le_sum_inv M
    have h_eq : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) =
        ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _; rw [one_div]
    rw [h_eq]
    refine le_trans ?_ h_inv
    have h_log_z14 : Real.log z / 4 = Real.log (z^((1:ℝ)/4)) := by
      rw [Real.log_rpow hz_pos]; ring
    rw [h_log_z14]
    apply Real.log_le_log (by positivity)
    have : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; rfl
    rw [this]
    exact hM_R_ge_zq
  -- Conclude.
  calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
          (1 : ℝ) / (m : ℝ) := h_subset_sum
    _ ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := h_block
    _ ≥ (q.totient : ℝ) / q * (Real.log z / 4) := by
        apply mul_le_mul_of_nonneg_left h_HM
        positivity
    _ = Real.log z * (q.totient : ℝ) / (4 * q) := by ring

/-! ## Final Brun–Titchmarsh AP bounds -/

/-- The Selberg sieve bound applied to the AP sieve. -/
theorem siftedSum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) (hz1 : 1 < z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hlog_pos : 0 < Real.log z := Real.log_pos hz1
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr hq_pos
  have hφ_R : (0 : ℝ) < q.totient := by exact_mod_cast hφ_pos
  have hS_pos : 0 < s.selbergBoundingSum := s.selbergBoundingSum_pos
  have hS_ge : s.selbergBoundingSum ≥ Real.log z * (q.totient : ℝ) / (4 * q) :=
    boundingSum_AP_ge x y z hx hy q a hq hz hzq
  have hbound_pos : 0 < Real.log z * (q.totient : ℝ) / (4 * q) := by positivity
  -- selberg_bound_simple gives siftedSum ≤ totalMass / S + remSum.
  apply le_trans (LPSelbergSieve.selberg_bound_simple s)
  -- totalMass = y/q, level = z.
  have htm : s.totalMass = y / q := rfl
  have hlev : s.level = z := rfl
  rw [htm]
  -- Bound y/q / S ≤ y/q / (lower bound on S).
  have hmain_bound : (y / q) / s.selbergBoundingSum ≤
      (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) := by
    apply div_le_div_of_nonneg_left _ hbound_pos hS_ge
    positivity
  have hmain_eq : (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) =
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) := by
    rw [div_div_eq_mul_div]
    rw [mul_comm (Real.log z) _]
    ring
  rw [hmain_eq] at hmain_bound
  have hrem_bound := primeSieve_rem_sum_AP_le x y z hx hy q a hq hz
  -- Now combine.
  linarith [hmain_bound, hrem_bound]

open Classical in
/-- Express the AP siftedSum as the cardinality of a filtered set. -/
theorem siftedSum_AP_eq_card (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum =
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have h_set_eq :
      (s.support.filter (fun d => Nat.Coprime s.prodPrimes d)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)) := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_supp, hd_cop⟩
      have hd_supp' : d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q) := hd_supp
      rw [Finset.mem_filter] at hd_supp'
      refine Finset.mem_filter.mpr ⟨hd_supp'.1, hd_supp'.2, ?_⟩
      intro p hpp hpz hpq hpd
      have hp_in : p ∈ ((Finset.range (Nat.floor z + 1)).filter
          (fun p => p.Prime ∧ ¬ p ∣ q)) := by
        refine Finset.mem_filter.mpr ⟨?_, hpp, hpq⟩
        rw [Finset.mem_range]
        have : p ≤ Nat.floor z := Nat.le_floor hpz
        omega
      have hp_dvd_prod : p ∣ s.prodPrimes :=
        Finset.dvd_prod_of_mem _ hp_in
      have h_one : p ∣ 1 := by
        have hgcd : p ∣ Nat.gcd s.prodPrimes d := Nat.dvd_gcd hp_dvd_prod hpd
        rwa [hd_cop] at hgcd
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_one h_one)
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_icc, hd_mod, h_pf⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · -- d ∈ support
        change d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q)
        exact Finset.mem_filter.mpr ⟨hd_icc, hd_mod⟩
      · -- Nat.Coprime s.prodPrimes d
        rw [Nat.Coprime]
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpprod : p ∣ s.prodPrimes := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hpd : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        have h_prod_eq : s.prodPrimes = primorialRestricted q (Nat.floor z) := rfl
        rw [h_prod_eq] at hpprod
        unfold primorialRestricted at hpprod
        rcases (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hpp) _).mp hpprod with ⟨r, hr, hpr⟩
        rcases Finset.mem_filter.mp hr with ⟨hr_range, hr_prime, hr_nq⟩
        have hpr_eq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hr_prime).mp hpr
        have hp_range_mem : p ∈ Finset.range (Nat.floor z + 1) := by
          rw [hpr_eq]; exact hr_range
        rw [Finset.mem_range] at hp_range_mem
        have hpz : (p : ℝ) ≤ z := by
          have : p ≤ Nat.floor z := by omega
          calc (p : ℝ) ≤ (Nat.floor z : ℝ) := by exact_mod_cast this
            _ ≤ z := Nat.floor_le (by linarith)
        have hp_nq : ¬ p ∣ q := by rw [hpr_eq]; exact hr_nq
        exact h_pf p hpp hpz hp_nq hpd
  -- Now unfold siftedSum and convert to filtered card.
  show s.siftedSum = _
  dsimp only [LPSieve.siftedSum]
  -- weights = 1, so siftedSum = ∑ d ∈ A, if Coprime then 1 else 0 = (A.filter Coprime).card
  have h_weights : ∀ d ∈ s.support, s.weights d = 1 := fun _ _ => rfl
  have : (∑ d ∈ s.support, if Nat.Coprime s.prodPrimes d then s.weights d else 0) =
      ((s.support.filter (fun d => Nat.Coprime s.prodPrimes d)).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [h_weights d hd.1, Nat.cast_one]
  rw [this, h_set_eq]

/-- Number of primes in an AP `≤ siftedSum + z`. -/
theorem primesBetween_AP_le_siftedSum_add (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      (primeInterSieveAP x y z q a hq hz).siftedSum + z := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  rw [siftedSum_AP_eq_card x y z q a hq hz]
  -- primesBetween_AP set ⊆ sifted set ∪ Icc 1 ⌊z⌋.
  have h_subset :
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n.Prime ∧ n % q = a % q)) ⊆
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
    intro p hp_mem
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
    rw [Finset.mem_union]
    rcases hp_mem with ⟨hp_range, hp_prime, hp_mod⟩
    by_cases hpz : (p : ℝ) ≤ z
    · right
      refine Finset.mem_Icc.mpr ⟨hp_prime.one_le, Nat.le_floor hpz⟩
    · left
      push_neg at hpz
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, hp_mod, ?_⟩
      intro p' hp'_prime hp'_le _ hp'_dvd
      rw [hp_prime.dvd_iff_eq hp'_prime.ne_one] at hp'_dvd
      rw [← hp'_dvd] at hp'_le
      linarith
  have h_card_le := Finset.card_le_card h_subset
  have h_card_union := Finset.card_union_le
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))
      (Finset.Icc 1 (Nat.floor z))
  have h_card_Icc : (Finset.Icc 1 (Nat.floor z)).card ≤ Nat.floor z := by
    rw [Nat.card_Icc]; omega
  have h_floor_le : (Nat.floor z : ℝ) ≤ z := Nat.floor_le (by linarith)
  -- Combine
  have h_chain : (primesBetween_AP x (x + y) q a : ℝ) ≤
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) +
      (Nat.floor z : ℝ) := by
    have h1 : (primesBetween_AP x (x + y) q a : ℝ) ≤
        ((((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q ∧
            ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))).card +
         (Finset.Icc 1 (Nat.floor z)).card : ℝ) := by
        unfold primesBetween_AP
        exact_mod_cast le_trans h_card_le h_card_union
    have h2 : ((Finset.Icc 1 (Nat.floor z)).card : ℝ) ≤ (Nat.floor z : ℝ) := by
      exact_mod_cast h_card_Icc
    linarith
  linarith

/-- Combined Brun–Titchmarsh AP bound: number of primes in an AP is
bounded by the sifted sum plus z. -/
theorem primesBetween_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hz1 : 1 < z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 + z := by
  have h1 := primesBetween_AP_le_siftedSum_add x y z hx hy q a hq hz
  have h2 := siftedSum_AP_le x y z hx hy q a hq hz hzq hz1
  linarith

/-- `piMod t q a` (from `Erdos696.lean`) is bounded by our `primesBetween_AP 1 t q a`. -/
theorem piMod_le_via_primesBetween_AP (t : ℝ) (q a : ℕ) (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (Erdos696.piMod t q a : ℝ) ≤ primesBetween_AP 1 t q a := by
  classical
  unfold Erdos696.piMod primesBetween_AP
  have h_ceil_one : Nat.ceil (1 : ℝ) = 1 := by simp
  rw [h_ceil_one]
  -- Show the Set equals coe of the filter Finset.
  have h_set :
      {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q} =
      ((Finset.Icc 1 ⌊t⌋₊).filter (fun n => n.Prime ∧ n % q = a % q) : Set ℕ) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_coe, Finset.mem_Icc,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp_le, hp_prime, hp_mod⟩
      exact ⟨⟨hp_prime.one_le, hp_le⟩, hp_prime, hp_mod⟩
    · rintro ⟨⟨_, hp_le⟩, hp_prime, hp_mod⟩
      exact ⟨hp_le, hp_prime, hp_mod⟩
  rw [h_set, Nat.card_coe_set_eq, Set.ncard_coe_finset]

set_option maxHeartbeats 1000000 in
/-- **Brun–Titchmarsh in arithmetic progressions** (strengthened-hypothesis form).

Discharges the original `axiom brun_titchmarsh` in `Erdos696.lean` for the
range `t ≥ 256 · q^9`, which is the range used by every downstream consumer.
The constant `CBT = 30000` is chosen large enough to absorb both the leading
sieve constant and the explicit error term `5 z (1 + log z)^3 + z` at level
`z = √(t/q)`. -/
theorem brun_titchmarsh_large :
    ∃ CBT : ℝ, 0 < CBT ∧
      ∀ q : ℕ, 1 ≤ q →
        ∀ a : ℕ, Nat.Coprime a q →
          ∀ t : ℝ, (256 * (q : ℝ)^9 : ℝ) ≤ t →
            ((Erdos696.piMod t q a : ℝ)) ≤
              CBT * t / ((q.totient : ℝ) * Real.log (t / q)) := by
  refine ⟨30000, by norm_num, ?_⟩
  intro q hq a _hcop t ht
  -- Basic positivity.
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < q := by linarith
  have hq4_ge_1 : (1 : ℝ) ≤ (q : ℝ)^4 := one_le_pow₀ hq1
  have hq8_ge_1 : (1 : ℝ) ≤ (q : ℝ)^8 := one_le_pow₀ hq1
  have hq9_ge_1 : (1 : ℝ) ≤ (q : ℝ)^9 := one_le_pow₀ hq1
  have h256q9 : (256 : ℝ) ≤ 256 * (q : ℝ)^9 := by nlinarith [hq9_ge_1]
  have ht256 : (256 : ℝ) ≤ t := le_trans h256q9 ht
  have ht_pos : (0 : ℝ) < t := by linarith
  have ht_gt1 : (1 : ℝ) < t := by linarith
  have htq_pos : 0 < t / q := div_pos ht_pos hq_pos
  -- z := √(t/q).
  set z : ℝ := Real.sqrt (t / q) with hz_def
  have hz_pos : 0 < z := Real.sqrt_pos.mpr htq_pos
  -- t/q ≥ 256 q^8.
  have htq_lb : 256 * (q : ℝ)^8 ≤ t / q := by
    rw [le_div_iff₀ hq_pos]
    have : 256 * (q : ℝ)^8 * q = 256 * (q : ℝ)^9 := by ring
    linarith [this ▸ ht]
  have htq_ge_256 : (256 : ℝ) ≤ t / q := by
    have : (256 : ℝ) ≤ 256 * (q : ℝ)^8 := by nlinarith [hq8_ge_1]
    linarith
  -- 16 q^4 ≤ z.
  have hzq : 16 * (q : ℝ)^4 ≤ z := by
    have hsq : (16 * (q : ℝ)^4)^2 ≤ t / q := by
      have heq : (16 * (q : ℝ)^4)^2 = 256 * (q : ℝ)^8 := by ring
      linarith
    have h16q4_nn : (0 : ℝ) ≤ 16 * (q : ℝ)^4 := by positivity
    rw [hz_def, ← Real.sqrt_sq h16q4_nn]
    exact Real.sqrt_le_sqrt hsq
  -- z ≥ 16 ≥ 1.
  have hz_ge_16 : (16 : ℝ) ≤ z := by
    have : (16 : ℝ) ≤ 16 * (q : ℝ)^4 := by nlinarith [hq4_ge_1]
    linarith
  have hz_ge_1 : (1 : ℝ) ≤ z := by linarith
  have hz_gt_1 : (1 : ℝ) < z := by linarith
  -- log z = (1/2) log (t/q).
  have hlog_z : Real.log z = (1/2) * Real.log (t / q) := by
    rw [hz_def, Real.log_sqrt htq_pos.le]
    ring
  have hlog_tq_pos : 0 < Real.log (t / q) :=
    Real.log_pos (by linarith)
  have hlog_z_pos : 0 < Real.log z := by rw [hlog_z]; linarith
  -- Apply piMod_le_via_primesBetween_AP and primesBetween_AP_le with x=1, y=t-1.
  have hpiMod_le : (Erdos696.piMod t q a : ℝ) ≤ primesBetween_AP 1 t q a :=
    piMod_le_via_primesBetween_AP t q a hq (by linarith)
  have hy_pos : (0 : ℝ) < t - 1 := by linarith
  have h_xy : (1 : ℝ) + (t - 1) = t := by ring
  have hpB : ((primesBetween_AP 1 ((1 : ℝ) + (t - 1)) q a : ℕ) : ℝ) ≤
      4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z :=
    primesBetween_AP_le 1 (t - 1) z (by norm_num) hy_pos q a hq hz_ge_1 hz_gt_1 hzq
  rw [h_xy] at hpB
  -- φ(q) facts.
  have hφ_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hφ_le_q : (q.totient : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  -- u = t/q.
  set u : ℝ := t / q with hu_def
  have hu_pos : 0 < u := htq_pos
  have hu_ge_256 : 256 ≤ u := htq_ge_256
  have hu_gt_1 : (1 : ℝ) < u := by linarith
  have hlog_u_pos : 0 < Real.log u := Real.log_pos hu_gt_1
  have h_sqrt_u_eq : z = Real.sqrt u := by rw [hz_def]
  -- log u ≥ log 256 > 5 (since e^5 < 256).
  have hlog256_ge : (5 : ℝ) ≤ Real.log 256 := by
    have he5_le : Real.exp 5 ≤ 256 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [h5]
      have h2 : Real.exp 1 ^ 5 ≤ 2.7182818286 ^ 5 := by
        apply pow_le_pow_left₀ (Real.exp_pos 1).le h1.le
      have h3 : (2.7182818286 : ℝ) ^ 5 ≤ 256 := by norm_num
      linarith
    have := Real.log_le_log (Real.exp_pos 5) he5_le
    rwa [Real.log_exp] at this
  have hlog_u_ge_5 : (5 : ℝ) ≤ Real.log u :=
    le_trans hlog256_ge (Real.log_le_log (by norm_num) hu_ge_256)
  -- (1 + (1/2) log u) ≤ log u  ⇐  (1/2) log u ≥ 1  ⇐  log u ≥ 2.
  have h1pluslog_le : 1 + (1/2) * Real.log u ≤ Real.log u := by linarith
  -- (1 + log z)^3 ≤ (log u)^3.
  have h_pow_le : (1 + Real.log z)^3 ≤ (Real.log u)^3 := by
    rw [hlog_z]
    have h_nn : 0 ≤ 1 + (1/2) * Real.log u := by linarith
    exact pow_le_pow_left₀ h_nn h1pluslog_le 3
  have hlog_u_ge_1 : (1 : ℝ) ≤ Real.log u := by linarith
  have hlog_u_pow3_ge_1 : (1 : ℝ) ≤ (Real.log u)^3 := by
    calc (1 : ℝ) = 1^3 := by ring
      _ ≤ (Real.log u)^3 := pow_le_pow_left₀ (by norm_num) hlog_u_ge_1 3
  -- Combine main + error and bound by 30000 · t / (φ(q) log u).
  -- Strategy: show entire RHS bound ≤ 30000 · u / log u (using φ(q) ≤ q, t = qu).
  -- Main term: 4q · (t-1)/q / (φ(q) (1/2) log u) ≤ 8 u q / (φ(q) log u).
  --   In particular ≤ 8 q² / (φ(q) log u) · u / q ≤ 8 u q / (φ(q) log u),
  --   and bounding by t/(φ(q) log(t/q)) factor: 8t/(φ(q) log u).
  -- Error term: 5 z (1+log z)^3 + z ≤ 6 √u (log u)^3.
  -- Goal: 8t/(φ(q) log u) + 6 √u (log u)^3 ≤ 30000 t/(φ(q) log u).
  -- I.e.,  6 √u (log u)^3 ≤ 29992 t/(φ(q) log u).
  -- Using φ(q) ≤ q and t = qu: t/(φ(q) log u) ≥ qu/(q log u) = u/log u.
  -- So need 6 √u (log u)^3 ≤ 29992 · u/log u, i.e., 6 (log u)^4 / √u ≤ 29992,
  -- i.e., (log u)^4 / √u ≤ 4999.
  -- Bound: log u ≤ 8 u^{1/8}, so (log u)^4 ≤ 4096 √u, so (log u)^4/√u ≤ 4096.
  have h_log_le : Real.log u ≤ u^((1 : ℝ)/8) / ((1 : ℝ)/8) :=
    Real.log_le_rpow_div hu_pos.le (by norm_num)
  have h_log_le' : Real.log u ≤ 8 * u^((1 : ℝ)/8) := by
    have heq : u^((1 : ℝ)/8) / ((1 : ℝ)/8) = 8 * u^((1 : ℝ)/8) := by
      field_simp
    linarith [heq ▸ h_log_le]
  have h_log_nn : 0 ≤ Real.log u := by linarith
  have h_pow4_le : (Real.log u)^4 ≤ (8 * u^((1 : ℝ)/8))^4 :=
    pow_le_pow_left₀ h_log_nn h_log_le' 4
  have hu18_nn : 0 ≤ u^((1 : ℝ)/8) := (Real.rpow_pos_of_pos hu_pos _).le
  have h_pow4_simp : (8 * u^((1 : ℝ)/8))^4 = 4096 * u^((1 : ℝ)/2) := by
    rw [mul_pow]
    have h1 : (8 : ℝ)^4 = 4096 := by norm_num
    have h2 : (u^((1 : ℝ)/8))^4 = u^((1 : ℝ)/2) := by
      rw [← Real.rpow_natCast (u^((1 : ℝ)/8)) 4, ← Real.rpow_mul hu_pos.le]
      norm_num
    rw [h1, h2]
  have h_sqrt_eq : Real.sqrt u = u^((1 : ℝ)/2) := Real.sqrt_eq_rpow u
  have hu12_pos : 0 < u^((1 : ℝ)/2) := Real.rpow_pos_of_pos hu_pos _
  have h_logu4_le : (Real.log u)^4 ≤ 4096 * Real.sqrt u := by
    rw [h_sqrt_eq]
    linarith [h_pow4_le, h_pow4_simp]
  -- φ(q) ≥ 1.
  have hφ_ge_1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  -- t = q · u.
  have ht_eq_qu : t = (q : ℝ) * u := by
    rw [hu_def]; field_simp
  -- piMod ≤ ... ≤ 30000 t/(φ(q) log(t/q)).
  -- Step 1: piMod ≤ RHS of hpB.
  have h_step1 : (Erdos696.piMod t q a : ℝ) ≤
      4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z :=
    le_trans hpiMod_le hpB
  -- Step 2: bound the entire RHS by 30000 t/(φ(q) log(t/q)).
  have h_target : 4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z ≤
      30000 * t / ((q.totient : ℝ) * Real.log (t / q)) := by
    -- Rewrite main term using log z = (1/2) log u and simplify.
    have h_simp_main : 4 * (q : ℝ) * ((t - 1) / (q : ℝ)) = 4 * (t - 1) := by
      field_simp
    rw [h_simp_main, hlog_z, ← hu_def]
    rw [show (q.totient : ℝ) * ((1 / 2) * Real.log u) =
        (1 / 2) * ((q.totient : ℝ) * Real.log u) from by ring]
    -- LHS = 4(t-1) / ((1/2) (φ(q) log u)) + 5z(1+log z)^3 + z
    --     = 8(t-1)/(φ(q) log u) + 5z(1+log z)^3 + z.
    have h_denom_pos : 0 < (q.totient : ℝ) * Real.log u := by positivity
    have h_main_simp : 4 * (t - 1) / ((1/2) * ((q.totient : ℝ) * Real.log u)) =
        8 * (t - 1) / ((q.totient : ℝ) * Real.log u) := by
      rw [show ((1 : ℝ)/2) * ((q.totient : ℝ) * Real.log u) =
        ((q.totient : ℝ) * Real.log u) / 2 from by ring]
      rw [div_div_eq_mul_div]
      congr 1
      ring
    rw [h_main_simp]
    -- Error bound: 5z(1+log z)^3 + z ≤ 6 √u (log u)^3.
    have h_err : 5 * z * (1 + Real.log z)^3 + z ≤ 6 * Real.sqrt u * (Real.log u)^3 := by
      rw [h_sqrt_u_eq]
      nlinarith [h_pow_le, hz_pos.le, hlog_u_pow3_ge_1,
        Real.sqrt_pos.mpr hu_pos, h_sqrt_u_eq]
    -- Combined: 8(t-1)/(φ(q) log u) + 5z(1+log z)^3 + z ≤
    --          8 t/(φ(q) log u) + 6 √u (log u)^3.
    have h_main_le_t : 8 * (t - 1) / ((q.totient : ℝ) * Real.log u) ≤
        8 * t / ((q.totient : ℝ) * Real.log u) := by
      apply div_le_div_of_nonneg_right _ h_denom_pos.le
      linarith
    -- Bound 6 √u (log u)^3 ≤ (29992 · t)/(φ(q) log u) using log u^4 ≤ 4096 √u.
    -- 6 √u (log u)^3 = 6 √u (log u)^3 · (log u)/(log u) = 6 (log u)^4 / log u · √u/√u · √u
    --                                                  ... let me just do it.
    -- We have (log u)^4 ≤ 4096 √u, so (log u)^4 ≤ 4096 √u.
    -- Then 6 √u (log u)^3 · log u ≤ 6 √u · 4096 √u = 24576 u.
    -- So 6 √u (log u)^3 ≤ 24576 u / log u ≤ 24576 q u / (φ(q) log u) (since φ(q) ≤ q)
    --                                     = 24576 t / (φ(q) log u).
    have h_err_le : 6 * Real.sqrt u * (Real.log u)^3 ≤
        24576 * t / ((q.totient : ℝ) * Real.log u) := by
      have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
      -- Multiply both sides of (log u)^4 ≤ 4096 √u by 6 √u / log u.
      -- I.e., 6 √u (log u)^3 = 6 √u (log u)^4 / log u ≤ 6 √u · 4096 √u / log u
      --                     = 6 · 4096 · u / log u = 24576 u / log u.
      have h_step : 6 * Real.sqrt u * (Real.log u)^3 ≤ 24576 * u / Real.log u := by
        rw [le_div_iff₀ hlog_u_pos]
        have h_lhs_eq : 6 * Real.sqrt u * (Real.log u)^3 * Real.log u =
            6 * Real.sqrt u * (Real.log u)^4 := by ring
        rw [h_lhs_eq]
        have hmul : 6 * Real.sqrt u * (Real.log u)^4 ≤
            6 * Real.sqrt u * (4096 * Real.sqrt u) := by
          apply mul_le_mul_of_nonneg_left h_logu4_le
          positivity
        have h_sq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
        nlinarith [hmul, h_sq, hu_pos.le]
      have h2 : 24576 * u / Real.log u ≤ 24576 * t / ((q.totient : ℝ) * Real.log u) := by
        rw [ht_eq_qu]
        rw [div_le_div_iff₀ hlog_u_pos h_denom_pos]
        have h1 : 24576 * u * ((q.totient : ℝ) * Real.log u) =
            24576 * u * Real.log u * (q.totient : ℝ) := by ring
        have h2 : 24576 * ((q : ℝ) * u) * Real.log u =
            24576 * u * Real.log u * (q : ℝ) := by ring
        rw [h1, h2]
        have h_factor_nn : 0 ≤ 24576 * u * Real.log u := by positivity
        exact mul_le_mul_of_nonneg_left hφ_le_q h_factor_nn
      linarith
    -- Combine.
    have h_combine : 8 * (t - 1) / ((q.totient : ℝ) * Real.log u) +
        5 * z * (1 + Real.log z)^3 + z ≤
        (8 + 24576) * t / ((q.totient : ℝ) * Real.log u) := by
      have h_sum :
          8 * t / ((q.totient : ℝ) * Real.log u) +
            24576 * t / ((q.totient : ℝ) * Real.log u) =
          (8 + 24576) * t / ((q.totient : ℝ) * Real.log u) := by
        rw [div_add_div_same]; ring_nf
      linarith [h_main_le_t, h_err, h_err_le, h_sum]
    have h_final : (8 + 24576 : ℝ) * t / ((q.totient : ℝ) * Real.log u) ≤
        30000 * t / ((q.totient : ℝ) * Real.log u) := by
      apply div_le_div_of_nonneg_right _ h_denom_pos.le
      nlinarith [ht_pos.le]
    -- Rewrite h_combine in terms of (1 + 1/2 * log u)^3 to match the goal.
    rw [hlog_z] at h_combine
    linarith [h_combine, h_final]
  exact le_trans h_step1 h_target

#print axioms brun_titchmarsh_large

end Erdos696BT
