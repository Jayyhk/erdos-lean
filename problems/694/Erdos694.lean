/-
STANDALONE VERSION of Erdős Problem #694 — TOTIENT FIBRE EXTREMES.

Trust boundary (verify with `#print axioms` at the bottom):
  Mathlib core (propext, Classical.choice, Quot.sound)
  + linnik_dvd            (Linnik's theorem, divisibility form, axiomatized)

Mertens' third theorem (`mertens_product`, equation 15 of Mertens 1874) is
fully proved inline (see the `Mertens` sub-namespace + the bridge below);
that proof was originally produced by Aristotle from Harmonic and verified by
Lean. Linnik 1944 (eq. 2) remains axiomatized — its proof in Mathlib is a
larger undertaking (Linnik's exceptional-zero machinery).
-/

import Mathlib

namespace Erdos694

open Classical Filter Asymptotics Topology
open scoped BigOperators Nat

/-! ## Scratch helpers (totient ratio bookkeeping) -/

lemma ratio_totient_eq_prod_primeFactors_q (m : ℕ) (hm : m ≠ 0) :
    (m : ℚ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
  have hφ : (Nat.totient m : ℚ) =
      (m : ℚ) * ∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors m
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hprod_nonzero :
      (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpne1 : (p : ℚ) ≠ 1 := by
      norm_num [hpprime.ne_one]
    have hpne0 : (p : ℚ) ≠ 0 := by
      norm_num [hpprime.ne_zero]
    have hrewrite : (1 - (p : ℚ)⁻¹) = ((p : ℚ) - 1) / p := by
      field_simp [hpne0]
    rw [hrewrite]
    exact div_ne_zero (sub_ne_zero.mpr hpne1) hpne0
  have hφne : (Nat.totient m : ℚ) ≠ 0 := by
    rw [hφ]
    exact mul_ne_zero hmQ hprod_nonzero
  calc
    (m : ℚ) / Nat.totient m
        = (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹))⁻¹ := by
          rw [hφ]
          field_simp [hmQ, hprod_nonzero]
    _ = ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpne0 : (p : ℚ) ≠ 0 := by
        norm_num [hpprime.ne_zero]
      have hpne1 : (p : ℚ) ≠ 1 := by
        norm_num [hpprime.ne_one]
      field_simp [hpne0, hpne1]

lemma ratio_totient_eq_prod_primeFactors_real (m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℝ) / (p - 1)) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (ratio_totient_eq_prod_primeFactors_q m hm)
  simpa [Rat.cast_prod] using hq

noncomputable def primeEulerProdNat (Y : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))

lemma one_le_prime_factor (p : ℕ) (hp : Nat.Prime p) :
    1 ≤ (p : ℝ) / (p - 1) := by
  have hden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  rw [one_le_div hden]
  norm_num

lemma prime_factor_le_succ_div_self {Y p : ℕ} (hY : 1 ≤ Y) (hp : Nat.Prime p) (hYp : Y < p) :
    (p : ℝ) / (p - 1) ≤ ((Y + 1 : ℕ) : ℝ) / Y := by
  have hpden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  rw [div_le_div_iff₀ hpden hYpos]
  have hle : (Y + 1 : ℝ) ≤ p := by exact_mod_cast hYp
  norm_num at hle ⊢
  nlinarith

lemma ratio_totient_le_split_bound (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y * (((Y + 1 : ℕ) : ℝ) / Y) ^
        (m.primeFactors.filter fun p => Y < p).card := by
  classical
  set S := m.primeFactors with hS
  set small := S.filter (fun p => p ≤ Y) with hsmall
  set large := S.filter (fun p => ¬ p ≤ Y) with hlarge
  have hsplit :
      (∏ p ∈ S, ((p : ℝ) / (p - 1))) =
        (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
          (∏ p ∈ large, ((p : ℝ) / (p - 1))) := by
    rw [hsmall, hlarge]
    exact (Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Y)
      (fun p => ((p : ℝ) / (p - 1)))).symm
  have hsmall_subset : small ⊆ (Finset.Icc 1 Y).filter Nat.Prime := by
    intro p hp
    rw [hsmall] at hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpY⟩
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpprime.one_le, hpY⟩, hpprime⟩
  have hsmall_le :
      (∏ p ∈ small, ((p : ℝ) / (p - 1))) ≤ primeEulerProdNat Y := by
    unfold primeEulerProdNat
    let all := (Finset.Icc 1 Y).filter Nat.Prime
    have hnonneg_small : 0 ≤ ∏ p ∈ small, ((p : ℝ) / (p - 1)) := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpS : p ∈ S := by
        rw [hsmall] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime)
    have hone_rest : 1 ≤ ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
      have aux : ∀ t : Finset ℕ, t ⊆ all \ small →
          1 ≤ ∏ p ∈ t, ((p : ℝ) / (p - 1)) := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            have ha_mem : a ∈ all \ small := ht (Finset.mem_insert_self a s)
            have hs_sub : s ⊆ all \ small := fun x hx => ht (Finset.mem_insert_of_mem hx)
            exact one_le_mul_of_one_le_of_one_le
              (one_le_prime_factor a (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha_mem).1).2)
              (ih hs_sub)
      exact aux (all \ small) (fun _ h => h)
    calc
      (∏ p ∈ small, ((p : ℝ) / (p - 1)))
          ≤ (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
              ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
            exact le_mul_of_one_le_right hnonneg_small hone_rest
      _ = ∏ p ∈ all, ((p : ℝ) / (p - 1)) := by
            rw [mul_comm, Finset.prod_sdiff hsmall_subset]
  have hlarge_le :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
    calc
      (∏ p ∈ large, ((p : ℝ) / (p - 1)))
          ≤ ∏ _p ∈ large, (((Y + 1 : ℕ) : ℝ) / Y) := by
            refine Finset.prod_le_prod ?nonneg ?le
            · intro p hp
              have hpS : p ∈ S := by
                rw [hlarge] at hp
                exact (Finset.mem_filter.mp hp).1
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact zero_le_one.trans (one_le_prime_factor p hpprime)
            · intro p hp
              rw [hlarge] at hp
              rcases Finset.mem_filter.mp hp with ⟨hpS, hpYp⟩
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact prime_factor_le_succ_div_self hY hpprime (Nat.lt_of_not_ge hpYp)
      _ = (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
        rw [Finset.prod_const]
  rw [ratio_totient_eq_prod_primeFactors_real m hm, hS, hsplit]
  have hlarge_le' :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card := by
    simpa [hlarge, hS, not_le] using hlarge_le
  exact mul_le_mul hsmall_le hlarge_le'
    (Finset.prod_nonneg fun p hp => by
      have hpS : p ∈ S := by
        rw [hlarge] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime))
    (by
      unfold primeEulerProdNat
      exact Finset.prod_nonneg fun p hp => by
        exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2))

lemma large_primeFactors_card_le_log (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    ((m.primeFactors.filter fun p => Y < p).card : ℝ) ≤
      Real.log m / Real.log (Y + 1) := by
  classical
  set L := m.primeFactors.filter fun p => Y < p with hL
  have hL_subset : L ⊆ m.primeFactors := by
    rw [hL]
    exact Finset.filter_subset _ _
  have hpow_le_prod : (Y + 1) ^ L.card ≤ ∏ p ∈ L, p := by
    calc
      (Y + 1) ^ L.card = ∏ _p ∈ L, (Y + 1) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ L, p := by
        refine Finset.prod_le_prod ?nonneg ?le
        · intro p hp
          exact Nat.zero_le (Y + 1)
        · intro p hp
          have hpY : Y < p := by
            rw [hL] at hp
            exact (Finset.mem_filter.mp hp).2
          exact Nat.succ_le_of_lt hpY
  have hprod_le_all : (∏ p ∈ L, p) ≤ ∏ p ∈ m.primeFactors, p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hL_subset ?_
    intro p hpall hpnot
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpall
    exact hpprime.one_le
  have hprod_all_le_m : (∏ p ∈ m.primeFactors, p) ≤ m := by
    exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hm) (Nat.prod_primeFactors_dvd m)
  have hpow_le_m : (Y + 1) ^ L.card ≤ m :=
    hpow_le_prod.trans (hprod_le_all.trans hprod_all_le_m)
  have hbase_gt_one : (1 : ℝ) < (Y + 1 : ℕ) := by
    norm_num
    exact Nat.succ_le_iff.mp hY
  have hlog_pos : 0 < Real.log ((Y + 1 : ℕ) : ℝ) := Real.log_pos hbase_gt_one
  have hpow_pos : 0 < (((Y + 1) ^ L.card : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.succ_pos Y) L.card
  have hm_pos_real : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hm
  have hlog_le :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log hpow_pos (by exact_mod_cast hpow_le_m)
  have hlog_pow :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) =
        (L.card : ℝ) * Real.log ((Y + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hL]
  rw [hlog_pow] at hlog_le
  simpa [Nat.cast_add, Nat.cast_one] using (le_div_iff₀ hlog_pos).mpr hlog_le

lemma ratio_totient_le_log_split_bound (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y *
        ((((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1))) := by
  have hsplit := ratio_totient_le_split_bound m Y hm hY
  have hcard := large_primeFactors_card_le_log m Y hm hY
  have hbase_ge_one : 1 ≤ (((Y + 1 : ℕ) : ℝ) / Y) := by
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
    rw [one_le_div hYpos]
    norm_num
  have hpow_le :
      (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one hcard
  exact hsplit.trans (mul_le_mul_of_nonneg_left hpow_le (by
    unfold primeEulerProdNat
    exact Finset.prod_nonneg fun p hp => by
      exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2)))

/-! ## Main proof body -/

/- ## Section 1 — Preliminaries -/

/-- **Fibre-finiteness inequality.** For every `m ≥ 1`, `m ≤ 2 · φ(m)²`.
This gives the bound `m ≤ 2 n²` whenever `φ(m) = n`, ensuring totient fibres are finite.

Proof strategy (PDF Section 1):
- Per prime power `p^k`: `φ(p^k)² = p^(2k-2)(p-1)² ≥ p^k` for odd `p`, and
  `φ(2^k)² = 2^(2k-2) ≥ 2^(k-1)` for `p = 2`.
- Multiplicatively (using `Nat.recOnPosPrimePosCoprime`): the global `2` accounts for
  the at-most-one-factor-of-2 in `m`. The coprime step uses the strengthened
  invariant `if Odd m then m ≤ φ(m)² else m ≤ 2 φ(m)²` — i.e., the factor-of-2
  appears only when `m` is even, and disappears under multiplication of two odd numbers. -/
private lemma totient_sq_ge_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp_odd : Odd p) (hk : 0 < k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  -- Now k = j + 1
  rw [Nat.totient_prime_pow_succ hp]
  have hp3 : 3 ≤ p := by
    rcases hp_odd with ⟨t, ht⟩
    have h2 := hp.two_le
    omega
  have hp_pos : 0 < p := hp.pos
  -- Goal: p ^ (j+1) ≤ (p ^ j * (p - 1)) ^ 2
  -- (p ^ j * (p - 1)) ^ 2 = p^(2j) * (p-1)^2
  -- We have (p-1)^2 ≥ p for p ≥ 3
  -- So p^j * (p-1)^2 ≥ p^j * p = p^(j+1). And p^(2j) ≥ p^j since j ≥ 0, p ≥ 1.
  have hp_minus_one_sq_ge : p ≤ (p - 1) ^ 2 := by
    -- p ≥ 3, so set q := p - 1 ≥ 2. Goal: q + 1 ≤ q^2.
    set q := p - 1 with hq
    have hq2 : 2 ≤ q := by omega
    have hpeq : p = q + 1 := by omega
    rw [hpeq]
    -- Goal: q + 1 ≤ q^2. q^2 = q*q ≥ 2*q = q + q ≥ q + 2 > q + 1
    have h1 : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq2
    have h2 : 2 * q ≥ q + q := by omega
    have h3 : q + q ≥ q + 1 := by omega
    calc q + 1 ≤ q + q := h3
      _ ≤ 2 * q := by omega
      _ ≤ q * q := h1
      _ = q ^ 2 := by ring
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos _
  calc p ^ (j + 1) = p ^ j * p := by ring
    _ ≤ p ^ j * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hp_minus_one_sq_ge
    _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) := Nat.le_mul_of_pos_left _ hpj_pos
    _ = (p ^ j * (p - 1)) ^ 2 := by ring

private lemma totient_sq_ge_half_pow_two (k : ℕ) (hk : 0 < k) :
    2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  -- Goal: 2 ^ (j+1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2 = 2 * (2^j)^2 = 2^(2j+1)
  show 2 ^ (j + 1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2
  have heq : 2 * (2 ^ j * (2 - 1 : ℕ)) ^ 2 = 2 ^ (2 * j + 1) := by
    have h21 : (2 - 1 : ℕ) = 1 := rfl
    rw [h21, mul_one]
    rw [show (2 : ℕ) * (2 ^ j) ^ 2 = 2 ^ (2 * j + 1) from by
      rw [pow_succ]; ring]
  rw [heq]
  apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
  omega

theorem totient_sq_ge_half (m : ℕ) (_hm : 1 ≤ m) : m ≤ 2 * (Nat.totient m) ^ 2 := by
  -- Strengthened invariant
  suffices h : ∀ n : ℕ, n ≤ 2 * (Nat.totient n) ^ 2 ∧ (Odd n → n ≤ (Nat.totient n) ^ 2) by
    exact (h m).1
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨totient_sq_ge_half_pow_two k hk, ?_⟩
      intro hodd
      exfalso
      have heven : Even (2 ^ k) := by
        rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
        exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
      exact (Nat.not_odd_iff_even.mpr heven) hodd
    · have hp_odd : Odd p := hp.odd_of_ne_two hp2
      have hge : p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 :=
        totient_sq_ge_odd_prime_pow p k hp hp_odd hk
      refine ⟨?_, fun _ => hge⟩
      have hle : (Nat.totient (p ^ k)) ^ 2 ≤ 2 * (Nat.totient (p ^ k)) ^ 2 := by
        have := Nat.zero_le ((Nat.totient (p ^ k)) ^ 2); omega
      exact hge.trans hle
  | zero =>
    refine ⟨?_, ?_⟩
    · exact Nat.zero_le _
    · intro hodd
      exfalso
      exact (Nat.not_odd_iff_even.mpr Even.zero) hodd
  | one =>
    refine ⟨?_, fun _ => ?_⟩
    · -- 1 ≤ 2 * φ(1)^2 = 2 * 1 = 2
      rw [Nat.totient_one]; norm_num
    · rw [Nat.totient_one]; norm_num
  | coprime a b ha hb hcop iha ihb =>
    obtain ⟨iha1, iha2⟩ := iha
    obtain ⟨ihb1, ihb2⟩ := ihb
    have hφmul : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul hcop
    have hsq : (Nat.totient a * Nat.totient b) ^ 2 =
        (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · -- First conjunct: a*b ≤ 2 * φ(a*b)^2
      by_cases ha_odd : Odd a
      · -- a odd: a ≤ φ(a)^2 and b ≤ 2*φ(b)^2
        have ha_le : a ≤ (Nat.totient a) ^ 2 := iha2 ha_odd
        rw [hφmul, hsq]
        calc a * b ≤ (Nat.totient a) ^ 2 * (2 * (Nat.totient b) ^ 2) :=
              Nat.mul_le_mul ha_le ihb1
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
      · -- a even: by coprimality b must be odd
        have ha_even : Even a := Nat.not_odd_iff_even.mp ha_odd
        have h2dvda : 2 ∣ a := ha_even.two_dvd
        have hb_odd : Odd b := by
          rw [Nat.odd_iff]
          by_contra hbe
          push_neg at hbe
          have : 2 ∣ b := by omega
          have h2dvd_gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2dvda this
          rw [hcop] at h2dvd_gcd
          omega
        have hb_le : b ≤ (Nat.totient b) ^ 2 := ihb2 hb_odd
        rw [hφmul, hsq]
        calc a * b ≤ (2 * (Nat.totient a) ^ 2) * (Nat.totient b) ^ 2 :=
              Nat.mul_le_mul iha1 hb_le
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
    · -- Second conjunct: Odd (a*b) → a*b ≤ φ(a*b)^2
      intro hab_odd
      have ha_odd : Odd a := (Nat.odd_mul.mp hab_odd).1
      have hb_odd : Odd b := (Nat.odd_mul.mp hab_odd).2
      rw [hφmul, hsq]
      exact Nat.mul_le_mul (iha2 ha_odd) (ihb2 hb_odd)

/-- Corollary: if `φ(m) = n`, then `m ≤ 2 n²`. -/
theorem totient_preimage_bound {m n : ℕ} (hm : 1 ≤ m) (h : Nat.totient m = n) :
    m ≤ 2 * n ^ 2 := by
  rw [← h]; exact totient_sq_ge_half m hm

/-! ### Axiomatized prerequisites

Mathlib v4.27 has neither:
  1. Linnik's theorem in the divisibility form used here
     (`linnik_dvd`); nor
  2. the Mertens product asymptotic `∏_{p ≤ y}(1 - 1/p)^{-1} ~ e^γ log y`
     (`mertens_product`).

We axiomatize exactly these two classical inputs. Both are well-known
unconditional results (Linnik 1944, Mertens 1874) for which Mathlib v4.27 has
the surrounding infrastructure (e.g., `Nat.Primes.not_summable_one_div`,
`Chebyshev.theta`, `Nat.forall_exists_prime_gt_and_modEq`) but not the named
quantitative theorems themselves. When they land in Mathlib these axioms can
be deleted and replaced with imports.

The original PDF additionally invokes the PNT in the form `ϑ(y) ~ y`. This
formalization avoids that dependency: the lower-bound size estimate uses the
cruder bound `A_Y ≤ P_Y ≤ 4^Y` (provable from `Nat.primorial_le_4_pow`,
already in Mathlib), which is enough for the final `log log x` asymptotic.

Both axioms below are transitively used by `totient_fibre_extremes`:
`mertens_product` is consumed by `landau_max_ratio` for the upper bound and
by the lower-bound construction; `linnik_dvd` is consumed by the lower-bound
construction at the height-to-`x` rescaling step. -/

/-! ## Mertens' third theorem (Aristotle's formalization, inlined) -/

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

/-! ### Bridge from Aristotle's `Mertens.mertens_equation_15` to 694's `mertens_product`

Aristotle's `Mertens.mertens_equation_15` proves Mertens' third theorem in the form
`∏(1-1/p) · log N → e^{-γ}` over `N : ℕ`. The form `mertens_product` below is the
floor-indexed reciprocal `(∏ p/(p-1)) / (e^γ · log y) → 1` over `y : ℝ`. The bridge
is elementary: take reciprocal, compose with `Nat.floor`, and correct `log ⌊y⌋ ~ log y`. -/

/-- The set of primes ≤ N indexed via `Finset.range (N+1)` (Aristotle's version)
equals the set indexed via `Finset.Icc 1 N` (694's version), since 0 and 1 are not prime. -/
private lemma primes_range_eq_Icc (N : ℕ) :
    (Finset.range (N + 1)).filter Nat.Prime = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  refine ⟨fun ⟨hlt, hp⟩ => ⟨⟨hp.one_lt.le, by omega⟩, hp⟩, fun ⟨⟨_, hle⟩, hp⟩ => ⟨by omega, hp⟩⟩

/-- Reciprocal identity: `∏ p/(p-1) = 1 / ∏(1-1/p)` (over the same primes). -/
private lemma prod_ratio_eq_inv_mertensProd (N : ℕ) :
    (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 N), ((p : ℝ) / (p - 1))) =
      (Mertens.mertensProd N)⁻¹ := by
  rw [Mertens.mertensProd, ← primes_range_eq_Icc, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp_pos : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  have hpm1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  field_simp

/-- log y / log ⌊y⌋₊ → 1 as y → ∞. -/
private lemma tendsto_log_div_log_floor :
    Tendsto (fun y : ℝ => Real.log y / Real.log ⌊y⌋₊) atTop (𝓝 1) := by
  have h_ratio : Tendsto (fun y : ℝ => y / ⌊y⌋₊) atTop (𝓝 1) := by
    have h1 : Tendsto (fun y : ℝ => (⌊y⌋₊ : ℝ) / y) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
    have h2 : Tendsto (fun y : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h3 : Tendsto (fun y : ℝ => 1 / ((⌊y⌋₊ : ℝ) / y)) atTop (𝓝 (1 / 1)) :=
      h2.div h1 one_ne_zero
    rw [div_one] at h3
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with y hy
    have hy_pos : 0 < y := by linarith
    have hfloor_pos : 0 < (⌊y⌋₊ : ℝ) := by
      have : (1 : ℕ) ≤ ⌊y⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hy.le).ne'
      exact_mod_cast this
    field_simp
  have h_log_diff : Tendsto (fun y : ℝ => Real.log (y / ⌊y⌋₊)) atTop (𝓝 0) := by
    have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    have := hcont.tendsto.comp h_ratio
    simpa [Real.log_one] using this
  have h_log_y : Tendsto (fun y : ℝ => Real.log y) atTop atTop := Real.tendsto_log_atTop
  have h_log_floor : Tendsto (fun y : ℝ => Real.log ⌊y⌋₊) atTop atTop := by
    have h_floor : Tendsto (fun y : ℝ => (⌊y⌋₊ : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
    exact Real.tendsto_log_atTop.comp h_floor
  have h_eq : (fun y : ℝ => Real.log y / Real.log ⌊y⌋₊) =ᶠ[atTop]
      (fun y => 1 + Real.log (y / ⌊y⌋₊) / Real.log ⌊y⌋₊) := by
    filter_upwards [Filter.eventually_gt_atTop (2 : ℝ),
        h_log_floor.eventually_gt_atTop (0 : ℝ)] with y hy hlog_floor_pos
    have hy_pos : 0 < y := by linarith
    have hfloor_ne : (⌊y⌋₊ : ℝ) ≠ 0 := by
      have : (1 : ℕ) ≤ ⌊y⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (by linarith)).ne'
      exact_mod_cast Nat.one_le_iff_ne_zero.mp this
    have hlog_floor_ne : Real.log ⌊y⌋₊ ≠ 0 := hlog_floor_pos.ne'
    show Real.log y / Real.log ⌊y⌋₊ = 1 + Real.log (y / ⌊y⌋₊) / Real.log ⌊y⌋₊
    rw [Real.log_div hy_pos.ne' hfloor_ne]
    field_simp
    ring
  have h_div_zero : Tendsto (fun y : ℝ => Real.log (y / ⌊y⌋₊) / Real.log ⌊y⌋₊) atTop (𝓝 0) :=
    h_log_diff.div_atTop h_log_floor
  have h_target : Tendsto (fun y : ℝ => 1 + Real.log (y / ⌊y⌋₊) / Real.log ⌊y⌋₊) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h_div_zero
  exact h_target.congr' h_eq.symm

/-- **Equation 15 of Mertens** (*Ein Beitrag zur analytischen Zahlentheorie*,
J. reine angew. Math. 78 (1874), 46–62; page 53). Mertens' third theorem:
`∏_{p ≤ y, p prime} (1 - 1/p)^{-1}` is asymptotic to `e^γ · log y` as `y → ∞`.
Derived from `Mertens.mertens_equation_15` (Aristotle's full Lean
formalization of Mertens' third theorem, see `Erdos694/Mertens.lean`). -/
theorem mertens_product :
    Tendsto
      (fun y : ℝ =>
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊y⌋₊), ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))
      atTop (𝓝 1) := by
  -- Aristotle: M(N) · log N → e^{-γ}
  have h_M : Tendsto (fun N : ℕ => Mertens.mertensProd N * Real.log N) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := Mertens.mertens_equation_15
  -- Multiply by e^γ: M(N) · log N · e^γ → 1
  have h_M_eγ : Tendsto (fun N : ℕ =>
      Mertens.mertensProd N * Real.log N * Real.exp Real.eulerMascheroniConstant)
        atTop (𝓝 1) := by
    have := h_M.mul_const (Real.exp Real.eulerMascheroniConstant)
    simpa [← Real.exp_add, neg_add_cancel, Real.exp_zero] using this
  -- Compose with floor: M(⌊y⌋) · log ⌊y⌋ · e^γ → 1
  have h_M_floor : Tendsto (fun y : ℝ =>
      Mertens.mertensProd ⌊y⌋₊ * Real.log ⌊y⌋₊ * Real.exp Real.eulerMascheroniConstant)
        atTop (𝓝 1) := h_M_eγ.comp tendsto_nat_floor_atTop
  -- Replace log ⌊y⌋ with log y (× log y / log ⌊y⌋ correction)
  have h_M_logy : Tendsto (fun y : ℝ =>
      Mertens.mertensProd ⌊y⌋₊ * Real.log y * Real.exp Real.eulerMascheroniConstant)
        atTop (𝓝 1) := by
    have := h_M_floor.mul tendsto_log_div_log_floor
    simp only [mul_one] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with y hy
    have hy_pos : 0 < y := by linarith
    have hfloor_pos : 0 < (⌊y⌋₊ : ℝ) := by
      have : (1 : ℕ) ≤ ⌊y⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (by linarith)).ne'
      exact_mod_cast this
    have hfloor_ge_2 : (2 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      have h2y : (2 : ℝ) ≤ y := by linarith
      have : (2 : ℕ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.le_floor h2y
      exact_mod_cast this
    have hlog_floor_ne : Real.log ⌊y⌋₊ ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp
  -- Take reciprocal: 1 / (M(⌊y⌋) · log y · e^γ) → 1
  have h_recip : Tendsto (fun y : ℝ =>
      1 / (Mertens.mertensProd ⌊y⌋₊ * Real.log y * Real.exp Real.eulerMascheroniConstant))
        atTop (𝓝 (1 / 1)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).div h_M_logy one_ne_zero
  rw [div_one] at h_recip
  -- Rewrite using P(N) = 1/M(N)
  refine h_recip.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with y hy
  rw [prod_ratio_eq_inv_mertensProd]
  have hy_pos : 0 < y := by linarith
  have hlog_y_ne : Real.log y ≠ 0 := (Real.log_pos (by linarith)).ne'
  have heγ_ne : Real.exp Real.eulerMascheroniConstant ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- **Equation 2 of Linnik** (*On the least prime in an arithmetic progression. I.
The basic theorem*, Mat. Sbornik N.S. 15 (57) (1944), 139–178; page 139),
specialized to the residue class `l = 1`.

There exist absolute constants `C, L ≥ 1` such that for every `M ≥ 1`,
there exists a prime `ℓ` with `M ∣ ℓ - 1` and `ℓ ≤ C · M^L`.

This is the divisibility-form version of Linnik 1944 (best `L = 5` due to
Xylouris 2011), in the form most convenient for the lower-bound construction. -/
axiom linnik_dvd :
  ∃ C : ℝ, ∃ L : ℕ, 1 ≤ C ∧ 1 ≤ L ∧
    ∀ M : ℕ, 1 ≤ M →
      ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L

/-! ## Lemma 1.1 — Landau's max-ratio asymptotic

`max_{1 ≤ m ≤ T} m/φ(m) = (e^γ + o(1)) log log T`

**Proof strategy used here** (different from PDF; analytic split-at-Y):

For any threshold `Y`, every `m ≥ 1` satisfies (see `Erdos694Scratch`):
```
  m / φ(m) ≤ ∏_{p ≤ Y, p prime} p/(p-1)  ·  ((Y+1)/Y) ^ (log m / log(Y+1)).
```
Choosing `Y = Y(T) → ∞` slowly enough that `((Y+1)/Y)^(log T/log(Y+1)) → 1` and
applying `mertens_product` to the first factor gives the asymptotic.
-/

/- ### Landau's lemma — proof

We choose `Y(T) := ⌊log T / log 4⌋`. Key properties:
- `Y(T) → ∞` as `T → ∞` (slowly).
- `primorial Y ≤ 4^Y ≤ T`, so `primorial Y ∈ [1, ⌊T⌋]`.
- `m/φ(m)` at `m = primorial Y` equals `primeEulerProdNat Y` (lower witness).
- For every `m ∈ [1, ⌊T⌋]`, `m/φ(m) ≤ primeEulerProdNat Y · ((Y+1)/Y)^(log T/log(Y+1))`.
- The extra factor `((Y+1)/Y)^(log T/log(Y+1)) → 1` and
  `primeEulerProdNat Y / (e^γ log Y) → 1` (Mertens), `log Y / log log T → 1`.
-/

private noncomputable def landauY (T : ℝ) : ℕ := ⌊Real.log T / Real.log 4⌋₊

private lemma landauY_log4_le (T : ℝ) (hT : 1 ≤ T) :
    (landauY T : ℝ) * Real.log 4 ≤ Real.log T := by
  unfold landauY
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg hT
  have h := Nat.floor_le (a := Real.log T / Real.log 4) (by positivity)
  have heq : (Real.log T / Real.log 4) * Real.log 4 = Real.log T := by
    field_simp
  calc (⌊Real.log T / Real.log 4⌋₊ : ℝ) * Real.log 4
      ≤ (Real.log T / Real.log 4) * Real.log 4 :=
        mul_le_mul_of_nonneg_right h hlog4_pos.le
    _ = Real.log T := heq

private lemma landauY_tendsto :
    Tendsto landauY atTop atTop := by
  unfold landauY
  -- log T / log 4 → ∞, then ⌊·⌋₊ → ∞.
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h1 : Tendsto (fun T : ℝ => Real.log T / Real.log 4) atTop atTop := by
    have := Real.tendsto_log_atTop
    exact this.atTop_div_const hlog4_pos
  exact tendsto_nat_floor_atTop.comp h1

private lemma landauY_ge_one_eventually :
    ∀ᶠ T : ℝ in atTop, 1 ≤ landauY T := landauY_tendsto.eventually_ge_atTop 1

private lemma landauY_ge_two_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ landauY T := landauY_tendsto.eventually_ge_atTop 2

private lemma four_pow_landauY_le (T : ℝ) (hT : 1 ≤ T) :
    ((4 : ℝ) ^ landauY T) ≤ T := by
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hT_pos : 0 < T := by linarith
  have hY_le : (landauY T : ℝ) * Real.log 4 ≤ Real.log T := landauY_log4_le T hT
  -- From Y * log 4 ≤ log T, deduce 4^Y ≤ T.
  have h1 : Real.log ((4 : ℝ) ^ landauY T) = (landauY T : ℝ) * Real.log 4 := by
    rw [Real.log_pow]
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ landauY T := by positivity
  have h2 : Real.log ((4 : ℝ) ^ landauY T) ≤ Real.log T := by
    rw [h1]; exact hY_le
  exact (Real.log_le_log_iff h4_pos hT_pos).mp h2

/-- Primorial Y has prime factors exactly {primes ≤ Y}, so its m/φ(m) ratio equals
`primeEulerProdNat Y`. -/
private lemma ratio_totient_primorial (Y : ℕ) (_hY : 1 ≤ Y) :
    (primorial Y : ℝ) / Nat.totient (primorial Y) =
      primeEulerProdNat Y := by
  classical
  set m := primorial Y
  have hm_pos : 0 < m := primorial_pos Y
  have hm_ne : m ≠ 0 := hm_pos.ne'
  -- primeFactors(m) = (Finset.range (Y+1)).filter Nat.Prime
  have hfacts : m.primeFactors = (Finset.range (Y + 1)).filter Nat.Prime := by
    show (∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, p).primeFactors =
        (Finset.range (Y + 1)).filter Nat.Prime
    apply Nat.primeFactors_prod
    intro p hp; exact (Finset.mem_filter.mp hp).2
  rw [ratio_totient_eq_prod_primeFactors_real m hm_ne]
  rw [hfacts]
  unfold primeEulerProdNat
  -- Need: ∏ p ∈ (range (Y+1)).filter Prime, ... = ∏ p ∈ (Icc 1 Y).filter Prime, ...
  -- These finsets are equal (primes p satisfy 1 ≤ p ≤ Y iff p ∈ range(Y+1) ∧ p prime, modulo
  -- the fact that primes are ≥ 2 ≥ 1).
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hpr, hppri⟩
    refine ⟨⟨hppri.one_le, ?_⟩, hppri⟩
    omega
  · rintro ⟨⟨_, hpY⟩, hppri⟩
    exact ⟨by omega, hppri⟩

/-- `log Y → ∞` as `Y → ∞` (over `ℕ`). -/
private lemma log_landauY_tendsto :
    Tendsto (fun T : ℝ => Real.log (landauY T : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop).comp landauY_tendsto)

/-- `log log T / log Y(T) → 1`, i.e., `log Y(T) / log log T → 1`. -/
private lemma log_landauY_div_loglog_tendsto :
    Tendsto (fun T : ℝ => Real.log (landauY T : ℝ) / Real.log (Real.log T)) atTop (𝓝 1) := by
  -- Y(T) = ⌊log T / log 4⌋, so log Y(T) = log(log T / log 4) + o(1)
  --       = log log T - log log 4 + o(1).
  -- So log Y(T) / log log T = 1 - log log 4 / log log T + o(1/log log T) → 1.
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- We squeeze: (log T / log 4 - 1) ≤ Y ≤ log T / log 4, so for large T,
  -- log Y is within o(1) of log log T - log log 4.
  -- Easier: log Y / log(log T / log 4) → 1 (since Y / (log T / log 4) → 1).
  -- Then log(log T / log 4) / log log T → 1.
  -- Step 1: log Y - log(log T / log 4) → 0.
  have h_step1 : Tendsto (fun T : ℝ => Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
      atTop (𝓝 0) := by
    -- = log (Y / (log T / log 4)). And Y / (log T / log 4) → 1 (since |x - ⌊x⌋| ≤ 1 and x → ∞).
    -- Use: log Y - log x = log (Y/x) → log 1 = 0.
    -- For T large enough, both Y ≥ 1 and log T / log 4 ≥ 1.
    have h_ratio : Tendsto
        (fun T : ℝ => (landauY T : ℝ) / (Real.log T / Real.log 4)) atTop (𝓝 1) := by
      -- |Y - log T / log 4| ≤ 1 ≤ small relative to log T / log 4.
      -- Use squeeze: Y / x ∈ [(x-1)/x, x/x] = [1 - 1/x, 1].
      have h_sandwich_lower : ∀ᶠ T : ℝ in atTop,
          1 - 1 / (Real.log T / Real.log 4) ≤ (landauY T : ℝ) / (Real.log T / Real.log 4) := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT_gt
        have hT1 : 1 ≤ T := le_of_lt hT_gt
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        have hx_pos : 0 < Real.log T / Real.log 4 := by positivity
        unfold landauY
        have h_floor_ge : Real.log T / Real.log 4 - 1 < ⌊Real.log T / Real.log 4⌋₊ + 1 := by
          have := Nat.lt_floor_add_one (a := Real.log T / Real.log 4)
          linarith
        have h_floor_ge' : Real.log T / Real.log 4 - 1 ≤ (⌊Real.log T / Real.log 4⌋₊ : ℝ) := by
          have h := Nat.sub_one_lt_floor (Real.log T / Real.log 4)
          linarith
        rw [le_div_iff₀ hx_pos]
        have h1 : (1 - 1 / (Real.log T / Real.log 4)) * (Real.log T / Real.log 4) =
            Real.log T / Real.log 4 - 1 := by
          field_simp
        rw [h1]
        exact h_floor_ge'
      have h_sandwich_upper : ∀ᶠ T : ℝ in atTop,
          (landauY T : ℝ) / (Real.log T / Real.log 4) ≤ 1 := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT_gt
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        have hx_pos : 0 < Real.log T / Real.log 4 := by positivity
        rw [div_le_one hx_pos]
        unfold landauY
        exact Nat.floor_le (by positivity)
      have h_lower_to_one :
          Tendsto (fun T : ℝ => 1 - 1 / (Real.log T / Real.log 4)) atTop (𝓝 1) := by
        have h_inner : Tendsto (fun T : ℝ => Real.log T / Real.log 4) atTop atTop :=
          Real.tendsto_log_atTop.atTop_div_const hlog4_pos
        have h_inv : Tendsto (fun T : ℝ => 1 / (Real.log T / Real.log 4)) atTop (𝓝 0) := by
          have hi := h_inner.inv_tendsto_atTop
          have : (fun T : ℝ => 1 / (Real.log T / Real.log 4)) =
              (fun T : ℝ => (Real.log T / Real.log 4)⁻¹) := by ext T; rw [one_div]
          rw [this]; exact hi
        have : Tendsto (fun T : ℝ => 1 - 1 / (Real.log T / Real.log 4)) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub h_inv
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_to_one tendsto_const_nhds
        h_sandwich_lower h_sandwich_upper
    -- Now log of ratio → log 1 = 0.
    have h_log_ratio : Tendsto
        (fun T : ℝ => Real.log ((landauY T : ℝ) / (Real.log T / Real.log 4))) atTop (𝓝 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h_ratio
      simpa [Real.log_one] using this
    -- log(Y / x) = log Y - log x for Y > 0, x > 0.
    have h_eventual : ∀ᶠ T : ℝ in atTop,
        Real.log ((landauY T : ℝ) / (Real.log T / Real.log 4)) =
          Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4) := by
      filter_upwards [landauY_ge_one_eventually, Filter.eventually_gt_atTop (1 : ℝ)] with T hY1 hT
      have hY_pos : (0 : ℝ) < (landauY T : ℝ) := by exact_mod_cast hY1
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT
      have hx_pos : (0 : ℝ) < Real.log T / Real.log 4 := by positivity
      rw [Real.log_div hY_pos.ne' hx_pos.ne']
    exact (Filter.Tendsto.congr' h_eventual h_log_ratio)
  -- Step 2: log(log T / log 4) / log log T → 1.
  have h_step2 : Tendsto (fun T : ℝ => Real.log (Real.log T / Real.log 4) / Real.log (Real.log T))
      atTop (𝓝 1) := by
    -- log(log T / log 4) = log log T - log log 4. Divide by log log T → 1.
    have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have h_eq : ∀ᶠ T : ℝ in atTop,
        Real.log (Real.log T / Real.log 4) / Real.log (Real.log T) =
          1 - Real.log (Real.log 4) / Real.log (Real.log T) := by
      filter_upwards [Filter.eventually_gt_atTop (Real.exp 2)] with T hT
      have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
      have hT_pos : 0 < T := lt_of_lt_of_le hexp2_pos hT.le
      have h_logT_gt : 2 < Real.log T := by
        have := Real.log_lt_log hexp2_pos hT
        simpa [Real.log_exp] using this
      have hlogT_pos : 0 < Real.log T := by linarith
      have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have h_loglogT_pos : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
      rw [Real.log_div hlogT_pos.ne' hlog4_pos.ne']
      field_simp
    have h_inner_tendsto : Tendsto
        (fun T : ℝ => 1 - Real.log (Real.log 4) / Real.log (Real.log T)) atTop (𝓝 1) := by
      have h_inv : Tendsto (fun T : ℝ => Real.log (Real.log 4) / Real.log (Real.log T))
          atTop (𝓝 0) := by
        have := h_loglog_inf.inv_tendsto_atTop
        have h2 := this.const_mul (Real.log (Real.log 4))
        simpa [div_eq_mul_inv] using h2
      have : Tendsto (fun T : ℝ => 1 - Real.log (Real.log 4) / Real.log (Real.log T)) atTop
          (𝓝 (1 - 0)) := tendsto_const_nhds.sub h_inv
      simpa using this
    exact h_inner_tendsto.congr' (h_eq.mono (fun _ => Eq.symm))
  -- Combine: (log Y - log(log T / log 4)) → 0, and log(log T / log 4) / log log T → 1.
  -- log Y / log log T = (log Y - log(log T / log 4)) / log log T + log(log T / log 4)/ log log T
  --                   → 0 + 1 = 1.
  have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_diff_div : Tendsto
      (fun T : ℝ => (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
        / Real.log (Real.log T)) atTop (𝓝 0) := by
    have := h_step1.div_atTop h_loglog_inf
    simpa using this
  have h_sum : Tendsto
      (fun T : ℝ => (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
        / Real.log (Real.log T)
        + Real.log (Real.log T / Real.log 4) / Real.log (Real.log T)) atTop (𝓝 (0 + 1)) :=
    h_diff_div.add h_step2
  have h_eq2 : ∀ᶠ T : ℝ in atTop,
      (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4)) / Real.log (Real.log T)
        + Real.log (Real.log T / Real.log 4) / Real.log (Real.log T)
        = Real.log (landauY T : ℝ) / Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 2)] with T hT
    have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    have h_logT_gt : 2 < Real.log T := by
      have := Real.log_lt_log hexp2_pos hT
      simpa [Real.log_exp] using this
    have hlogT_pos : 0 < Real.log T := by linarith
    have h_loglogT_pos : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
    have h := h_loglogT_pos.ne'
    field_simp
    ring
  have h_final : Tendsto (fun T : ℝ => Real.log (landauY T : ℝ) / Real.log (Real.log T))
      atTop (𝓝 1) := by
    have := Filter.Tendsto.congr' h_eq2 h_sum
    simpa using this
  exact h_final

theorem landau_max_ratio :
    Tendsto
      (fun T : ℝ => (⨆ m ∈ Set.Icc 1 ⌊T⌋₊,
        (m : ℝ) / Nat.totient m) / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log T)))
      atTop (𝓝 1) := by
  -- Notation
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  -- Y(T) := ⌊log T / log 4⌋. Y → ∞, primorial Y ≤ 4^Y ≤ T.
  set Y : ℝ → ℕ := landauY with hY_def
  -- denominator: γc * log log T.
  set D : ℝ → ℝ := fun T => γc * Real.log (Real.log T) with hD_def
  -- sup function S.
  set S : ℝ → ℝ := fun T => ⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m with hS_def
  -- "primeEulerProdNat Y(T)" — lower bound.
  set L : ℝ → ℝ := fun T => primeEulerProdNat (Y T) with hL_def
  -- Upper bound factor ((Y+1)/Y)^(log T / log(Y+1)).
  set F : ℝ → ℝ := fun T => (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
    (Real.log T / Real.log ((Y T : ℝ) + 1)) with hF_def
  -- Mertens applied to ℕ→ℝ via Y.
  have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_logT_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < Real.log T := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT
    exact Real.log_pos hT
  have h_loglog_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with T hT
    have h1 : 1 < Real.log T := by
      have := Real.log_lt_log (Real.exp_pos _) hT
      simpa [Real.log_exp] using this
    exact Real.log_pos h1
  -- Mertens for our Y: primeEulerProdNat(Y(T)) / (γc * log Y(T)) → 1.
  have h_mertens_Y :
      Tendsto (fun T : ℝ => L T / (γc * Real.log (Y T : ℝ))) atTop (𝓝 1) := by
    -- mertens_product: (∏_{p ∈ filter Prime (Icc 1 ⌊y⌋₊)} p/(p-1)) / (γc * log y) → 1 as y → ∞.
    -- Compose with y = (Y T : ℝ). Then ⌊(Y T : ℝ)⌋₊ = Y T (since Y T : ℕ).
    have h_yT_to_inf : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp landauY_tendsto
    have h := mertens_product.comp h_yT_to_inf
    -- This gives: (∏_{p ∈ filter Prime (Icc 1 ⌊(Y T : ℝ)⌋₊)} ...) / (γc * log (Y T : ℝ)) → 1.
    -- Need to convert to L T / (γc * log Y T).
    have h_eq : ∀ᶠ T : ℝ in atTop,
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊((Y T : ℕ) : ℝ)⌋₊), ((p : ℝ) / (p - 1))) /
            (Real.exp Real.eulerMascheroniConstant * Real.log ((Y T : ℕ) : ℝ)) =
          L T / (γc * Real.log (Y T : ℝ)) := by
      filter_upwards with T
      have hfloor : ⌊((Y T : ℕ) : ℝ)⌋₊ = Y T := Nat.floor_natCast (Y T)
      rw [hfloor]
      rfl
    exact h.congr' h_eq
  -- log Y(T) / log log T → 1.
  have h_logY_div : Tendsto (fun T : ℝ => Real.log (Y T : ℝ) / Real.log (Real.log T))
      atTop (𝓝 1) := log_landauY_div_loglog_tendsto
  -- L(T) / D(T) → 1.
  have h_LD : Tendsto (fun T => L T / D T) atTop (𝓝 1) := by
    -- L/D = (L / (γc log Y)) * (log Y / log log T) — provided log log T ≠ 0.
    have h_prod : Tendsto
        (fun T : ℝ => (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T))) atTop (𝓝 (1 * 1)) :=
      h_mertens_Y.mul h_logY_div
    have h_eq : ∀ᶠ T : ℝ in atTop,
        (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T)) = L T / D T := by
      filter_upwards [landauY_ge_two_eventually, h_loglog_pos_ev] with T hY2 hloglog_pos
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hY_gt_one : (1 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 1 < Y T)
      have h_logY_pos : 0 < Real.log (Y T : ℝ) := Real.log_pos hY_gt_one
      show (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T)) = L T / D T
      rw [hD_def]
      simp only
      field_simp
    have := h_prod.congr' h_eq
    simpa using this
  -- F(T) → 1.
  -- log F(T) = (log T / log(Y+1)) * log((Y+1)/Y).
  -- For Y ≥ 2: 0 ≤ log F T ≤ log T / (Y log(Y+1)) → 0.
  have hF_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < F T := by
    filter_upwards [landauY_ge_one_eventually] with T hY1
    have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
    have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
    exact Real.rpow_pos_of_pos hbase_pos _
  have hF_to_one : Tendsto F atTop (𝓝 1) := by
    -- F = exp(log F) and we'll show log F → 0.
    have h_logF_eq : ∀ᶠ T : ℝ in atTop,
        Real.log (F T) =
          Real.log T / Real.log ((Y T : ℝ) + 1) *
            Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) := by
      filter_upwards [landauY_ge_one_eventually] with T hY1
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
      show Real.log ((((Y T : ℝ) + 1) / (Y T : ℝ)) ^
        (Real.log T / Real.log ((Y T : ℝ) + 1))) = _
      rw [Real.log_rpow hbase_pos]
    -- Bound: 0 ≤ log F ≤ log T / (Y · log(Y+1)).
    have h_logF_nn_ev : ∀ᶠ T : ℝ in atTop, 0 ≤ Real.log (F T) := by
      filter_upwards [h_logF_eq, landauY_ge_two_eventually,
        Filter.eventually_gt_atTop (1 : ℝ)] with T heq hY2 hT_gt
      rw [heq]
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hY_gt_one : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
      -- log T / log(Y+1) ≥ 0; (Y+1)/Y ≥ 1, so log ≥ 0.
      have h_div_nn : 0 ≤ Real.log T / Real.log ((Y T : ℝ) + 1) :=
        div_nonneg hlogT_pos.le hlog_Yp1_pos.le
      have h_base_ge_one : 1 ≤ ((Y T : ℝ) + 1) / (Y T : ℝ) := by
        rw [le_div_iff₀ hY_pos]
        linarith
      have h_log_base_nn : 0 ≤ Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) := by
        exact Real.log_nonneg h_base_ge_one
      exact mul_nonneg h_div_nn h_log_base_nn
    have h_logF_le_ev : ∀ᶠ T : ℝ in atTop,
        Real.log (F T) ≤ Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
      filter_upwards [h_logF_eq, landauY_ge_two_eventually,
        Filter.eventually_gt_atTop (1 : ℝ)] with T heq hY2 hT_gt
      rw [heq]
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
      -- log((Y+1)/Y) = log(1 + 1/Y) ≤ 1/Y (since log(1+x) ≤ x for x ≥ 0).
      have h_one_plus : ((Y T : ℝ) + 1) / (Y T : ℝ) = 1 + 1 / (Y T : ℝ) := by
        field_simp
      have h_log_le : Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) ≤ 1 / (Y T : ℝ) := by
        rw [h_one_plus]
        have h_inv_nn : 0 ≤ 1 / (Y T : ℝ) := by positivity
        exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by
          have : 1 + 1 / (Y T : ℝ) - 1 = 1 / (Y T : ℝ) := by ring
          linarith)
      have h_div_nn : 0 ≤ Real.log T / Real.log ((Y T : ℝ) + 1) :=
        div_nonneg hlogT_pos.le hlog_Yp1_pos.le
      calc Real.log T / Real.log ((Y T : ℝ) + 1) *
            Real.log (((Y T : ℝ) + 1) / (Y T : ℝ))
          ≤ Real.log T / Real.log ((Y T : ℝ) + 1) * (1 / (Y T : ℝ)) :=
            mul_le_mul_of_nonneg_left h_log_le h_div_nn
        _ = Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
            field_simp
    -- Now show log T / (Y · log(Y+1)) → 0.
    -- We have Y ≥ log T / log 4 - 1, so Y · log(Y+1) ≥ (log T / log 4 - 1) · log(2).
    -- Actually for ε > 0, we want log T / (Y · log(Y+1)) ≤ ε eventually.
    -- For T large, Y ≥ log T / (2 log 4), and Y+1 ≥ 2, so log(Y+1) ≥ log 2.
    -- So Y · log(Y+1) ≥ (log T / (2 log 4)) · log 2.
    -- log T / (Y · log(Y+1)) ≤ log T / ((log T)·log 2/(2 log 4)) = 2 log 4 / log 2.
    -- Wait, that doesn't go to 0! We need a better lower bound on Y · log(Y+1).
    -- Since Y → ∞, log(Y+1) → ∞, so Y · log(Y+1) ≥ Y · log Y ≥ (log T)·(log log T) /(C),
    -- which dominates log T. So ratio → 0.
    have h_upper_to_zero : Tendsto
        (fun T : ℝ => Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1))) atTop (𝓝 0) := by
      -- Bound: For T large, Y ≥ log T / (2 log 4) and log(Y+1) ≥ log Y.
      -- Y · log(Y+1) ≥ Y · log Y.
      -- Actually use a cleaner approach: the limit
      -- log T / (Y log Y) — replace Y with a real-valued thing close to log T / log 4.
      -- Cleaner: log T / (Y · log(Y+1)) = (log 4) · (log T / log 4) / (Y · log(Y+1))
      --                                ≤ (log 4) · (Y+1) / (Y · log(Y+1))
      --                                = (log 4) · (1 + 1/Y) / log(Y+1)
      --                                → log 4 · 1 / ∞ = 0.
      -- Use: log T ≤ (Y+1) log 4 from Y ≥ log T/log 4 - 1.
      have h_logT_bound : ∀ᶠ T : ℝ in atTop,
          Real.log T ≤ ((Y T : ℝ) + 1) * Real.log 4 := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
        have h := landauY_log4_le T hT
        -- (Y) * log 4 ≤ log T, so log T ≤ (Y+1) log 4 needs Y+1 ≥ log T / log 4, true since
        -- Y = ⌊log T / log 4⌋ and ⌊x⌋ + 1 > x.
        have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
        have h2 : Real.log T / Real.log 4 < (landauY T : ℝ) + 1 := Nat.lt_floor_add_one _
        -- log T = (log T / log 4) * log 4 < ((Y T : ℝ) + 1) * log 4.
        have heq : Real.log T = (Real.log T / Real.log 4) * Real.log 4 := by
          field_simp
        rw [heq]
        exact (mul_le_mul_of_nonneg_right h2.le hlog4_pos.le)
      have h_main_bd : ∀ᶠ T : ℝ in atTop,
          Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) ≤
            Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)) := by
        filter_upwards [h_logT_bound, landauY_ge_two_eventually] with T hbd hY2
        have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
        have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
        have hdenom_pos : 0 < (Y T : ℝ) * Real.log ((Y T : ℝ) + 1) :=
          mul_pos hY_pos hlog_Yp1_pos
        rw [div_le_iff₀ hdenom_pos]
        have heq : Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)) *
              ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) =
            Real.log 4 * ((1 + 1 / (Y T : ℝ)) * (Y T : ℝ)) := by
          field_simp
        rw [heq]
        have : Real.log 4 * ((1 + 1 / (Y T : ℝ)) * (Y T : ℝ)) =
            Real.log 4 * ((Y T : ℝ) + 1) := by
          field_simp
        rw [this, mul_comm (Real.log 4) _]
        exact hbd
      -- Now show RHS → 0.
      have h_rhs_to_zero : Tendsto
          (fun T : ℝ => Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)))
          atTop (𝓝 (Real.log 4 * 0)) := by
        apply Tendsto.const_mul
        -- (1 + 1/Y) → 1, log(Y+1) → ∞, so (1+1/Y)/log(Y+1) → 0.
        have h_num : Tendsto (fun T : ℝ => 1 + 1 / (Y T : ℝ)) atTop (𝓝 (1 + 0)) := by
          apply Tendsto.const_add
          have h_inv : Tendsto (fun T : ℝ => 1 / (Y T : ℝ)) atTop (𝓝 0) := by
            have hYTend : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
              tendsto_natCast_atTop_atTop.comp landauY_tendsto
            have := hYTend.inv_tendsto_atTop
            have : (fun T : ℝ => 1 / (Y T : ℝ)) = fun T : ℝ => ((Y T : ℝ))⁻¹ := by
              ext T; rw [one_div]
            rw [this]
            exact hYTend.inv_tendsto_atTop
          exact h_inv
        have h_denom : Tendsto (fun T : ℝ => Real.log ((Y T : ℝ) + 1)) atTop atTop := by
          have hYTend : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp landauY_tendsto
          have hYp1 : Tendsto (fun T : ℝ => (Y T : ℝ) + 1) atTop atTop :=
            hYTend.atTop_add tendsto_const_nhds
          exact Real.tendsto_log_atTop.comp hYp1
        have := h_num.div_atTop h_denom
        simpa using this
      have h_zero_eq : Real.log 4 * 0 = 0 := by ring
      rw [h_zero_eq] at h_rhs_to_zero
      -- Squeeze: 0 ≤ log T / (Y log(Y+1)) ≤ RHS, with both ends → 0.
      have h_lhs_nn : ∀ᶠ T : ℝ in atTop,
          0 ≤ Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), landauY_ge_two_eventually] with
          T hT_gt hY2
        have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
        have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        positivity
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rhs_to_zero
        h_lhs_nn h_main_bd
    -- Squeeze log F: 0 ≤ log F ≤ ... → 0. So log F → 0.
    have h_logF_to_zero : Tendsto (fun T => Real.log (F T)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper_to_zero
        h_logF_nn_ev h_logF_le_ev
    -- F = exp(log F), so F → exp 0 = 1.
    have h_F_eq : ∀ᶠ T : ℝ in atTop, Real.exp (Real.log (F T)) = F T := by
      filter_upwards [hF_pos_ev] with T hF_pos
      exact Real.exp_log hF_pos
    have h_exp : Tendsto (fun T => Real.exp (Real.log (F T))) atTop (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.tendsto _ |>.comp h_logF_to_zero
    have : Tendsto F atTop (𝓝 (Real.exp 0)) := h_exp.congr' h_F_eq
    simpa using this
  -- U(T)/D(T) := L(T) * F(T) / D(T) = (L(T)/D(T)) * F(T) → 1 * 1 = 1.
  have h_UD : Tendsto (fun T => L T * F T / D T) atTop (𝓝 1) := by
    have h := h_LD.mul hF_to_one
    have h_eq : ∀ᶠ T : ℝ in atTop, L T / D T * F T = L T * F T / D T := by
      filter_upwards with T
      ring
    have := h.congr' h_eq
    simpa using this
  -- Now bounds: L T ≤ S T ≤ L T * F T eventually.
  -- S T is the sup; ratio_totient_le_log_split_bound gives upper, primorial gives lower.
  -- Need: BddAbove the sup family for ciSup_le.
  have h_bound_ev : ∀ᶠ T : ℝ in atTop,
      L T / D T ≤ S T / D T ∧ S T / D T ≤ L T * F T / D T := by
    filter_upwards [landauY_ge_one_eventually, h_loglog_pos_ev,
      Filter.eventually_ge_atTop (1 : ℝ)] with T hY1 hloglog_pos hT1
    -- Set up positivity facts.
    have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
    have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
    have hbase_ge_one : 1 ≤ ((Y T : ℝ) + 1) / (Y T : ℝ) := by
      rw [le_div_iff₀ hY_pos]; linarith
    have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
    have hT_pos : 0 < T := by linarith
    have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg hT1
    have h_floor_T_pos : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT1)
    -- L T ≥ 1 (it's a product of factors ≥ 1).
    have hL_ge_one : 1 ≤ L T := by
      show 1 ≤ primeEulerProdNat (Y T)
      unfold primeEulerProdNat
      -- Use a generic helper: prove for any finset of primes, product of p/(p-1) ≥ 1.
      have aux : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) →
          (1 : ℝ) ≤ ∏ p ∈ s, (p : ℝ) / (p - 1) := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; simp
        | insert p s' hps ih =>
            intro hpp
            rw [Finset.prod_insert hps]
            have hp_prime : Nat.Prime p := hpp p (Finset.mem_insert_self _ _)
            have hp1 : (1 : ℝ) ≤ (p : ℝ) / (p - 1) :=
              one_le_prime_factor p hp_prime
            have hs'_each : ∀ q ∈ s', Nat.Prime q := fun q hq =>
              hpp q (Finset.mem_insert_of_mem hq)
            have hs' : (1 : ℝ) ≤ ∏ q ∈ s', (q : ℝ) / (q - 1) := ih hs'_each
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ (p : ℝ) / (p - 1) * ∏ q ∈ s', (q : ℝ) / (q - 1) :=
                mul_le_mul hp1 hs' zero_le_one (zero_le_one.trans hp1)
      apply aux
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hL_pos : 0 < L T := by linarith
    -- BddAbove for the sup family.
    have hbdd_inner :
        BddAbove (Set.range (fun (m : ℕ) =>
          ⨆ (_ : m ∈ Set.Icc 1 ⌊T⌋₊), (m : ℝ) / Nat.totient m)) := by
      refine ⟨L T * F T, ?_⟩
      rintro _ ⟨m, rfl⟩
      simp only
      by_cases hm : m ∈ Set.Icc 1 ⌊T⌋₊
      · rw [ciSup_pos hm]
        -- bound m/φ(m) ≤ L T * F T using ratio_totient_le_log_split_bound.
        have hm_pos : 1 ≤ m := hm.1
        have hm_ne : m ≠ 0 := by omega
        have h_split := ratio_totient_le_log_split_bound m (Y T) hm_ne hY1
        -- h_split says: m/φ(m) ≤ L T * ((Y+1)/Y)^(log m / log(Y+1)).
        -- We want: m/φ(m) ≤ L T * F T = L T * ((Y+1)/Y)^(log T / log(Y+1)).
        -- Since base ≥ 1 and log m ≤ log T (m ≤ ⌊T⌋ ≤ T), the exponent is at most log T/log(Y+1).
        have hm_le_T : (m : ℝ) ≤ T := by
          have := hm.2
          have hm_le_floor_R : (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast this
          calc (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := hm_le_floor_R
            _ ≤ T := Nat.floor_le (by linarith : (0 : ℝ) ≤ T)
        have hlog_le : Real.log m ≤ Real.log T := by
          have hm_pos_R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
          exact Real.log_le_log hm_pos_R hm_le_T
        have hlogYp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := by
          apply Real.log_pos; linarith
        have hexp_le : Real.log m / Real.log ((Y T : ℝ) + 1) ≤
            Real.log T / Real.log ((Y T : ℝ) + 1) := by
          exact div_le_div_of_nonneg_right hlog_le hlogYp1_pos.le
        have h_pow_le :
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log m / Real.log ((Y T : ℝ) + 1)) ≤
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
        -- Combine.
        have h_split' : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log m / Real.log ((Y T : ℝ) + 1)) := by
          have hh := h_split
          push_cast at hh
          exact hh
        have h_chain : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log T / Real.log ((Y T : ℝ) + 1)) := by
          calc (m : ℝ) / Nat.totient m ≤ _ := h_split'
            _ ≤ L T * _ := mul_le_mul_of_nonneg_left h_pow_le hL_pos.le
        show (m : ℝ) / Nat.totient m ≤ L T * F T
        exact h_chain
      · rw [ciSup_neg hm, Real.sSup_empty]
        have : 0 ≤ L T * F T := by
          have hF_nn : 0 ≤ F T := by
            exact (Real.rpow_pos_of_pos hbase_pos _).le
          exact mul_nonneg hL_pos.le hF_nn
        exact this
    -- Now S T ≤ L T * F T.
    have hS_le_LF : S T ≤ L T * F T := by
      show (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤ L T * F T
      apply ciSup_le
      intro m
      by_cases hm : m ∈ Set.Icc 1 ⌊T⌋₊
      · rw [ciSup_pos hm]
        -- bound m/φ(m) ≤ L T * F T (re-prove).
        have hm_pos : 1 ≤ m := hm.1
        have hm_ne : m ≠ 0 := by omega
        have h_split := ratio_totient_le_log_split_bound m (Y T) hm_ne hY1
        have hm_le_T : (m : ℝ) ≤ T := by
          have := hm.2
          have hm_le_floor_R : (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast this
          calc (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := hm_le_floor_R
            _ ≤ T := Nat.floor_le (by linarith : (0 : ℝ) ≤ T)
        have hm_pos_R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
        have hlog_le : Real.log m ≤ Real.log T := Real.log_le_log hm_pos_R hm_le_T
        have hlogYp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := by
          apply Real.log_pos; linarith
        have hexp_le : Real.log m / Real.log ((Y T : ℝ) + 1) ≤
            Real.log T / Real.log ((Y T : ℝ) + 1) :=
          div_le_div_of_nonneg_right hlog_le hlogYp1_pos.le
        have h_pow_le :
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log m / Real.log ((Y T : ℝ) + 1)) ≤
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
        have h_split' : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log m / Real.log ((Y T : ℝ) + 1)) := by
          have hh := h_split
          push_cast at hh
          exact hh
        calc (m : ℝ) / Nat.totient m ≤ _ := h_split'
          _ ≤ L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left h_pow_le hL_pos.le
          _ = L T * F T := by rfl
      · rw [ciSup_neg hm, Real.sSup_empty]
        have hF_nn : 0 ≤ F T := by
          exact (Real.rpow_pos_of_pos hbase_pos _).le
        exact mul_nonneg hL_pos.le hF_nn
    -- Now S T ≥ L T (using m = primorial Y T as a witness).
    have hS_ge_L : L T ≤ S T := by
      have hY1_real : 1 ≤ Y T := hY1
      -- m_witness = primorial (Y T).
      set m := primorial (Y T) with hm_def
      have hm_pos : 1 ≤ m := primorial_pos (Y T)
      have hm_ratio_eq : (m : ℝ) / Nat.totient m = L T := by
        show (m : ℝ) / Nat.totient m = primeEulerProdNat (Y T)
        exact ratio_totient_primorial (Y T) hY1
      -- m ≤ 4^Y ≤ T.
      have hm_le_4Y : (m : ℝ) ≤ ((4 : ℝ) ^ (Y T)) := by
        exact_mod_cast primorial_le_4_pow (Y T)
      have h4Y_le_T : ((4 : ℝ) ^ (Y T)) ≤ T := four_pow_landauY_le T hT1
      have hm_le_T : (m : ℝ) ≤ T := le_trans hm_le_4Y h4Y_le_T
      have hm_le_floor : m ≤ ⌊T⌋₊ := Nat.le_floor hm_le_T
      have hm_in : m ∈ Set.Icc 1 ⌊T⌋₊ := ⟨hm_pos, hm_le_floor⟩
      have : (m : ℝ) / Nat.totient m ≤ S T := by
        show (m : ℝ) / Nat.totient m ≤ ⨆ m' ∈ Set.Icc 1 ⌊T⌋₊, (m' : ℝ) / Nat.totient m'
        have h_inner_eq :
            (⨆ (_ : m ∈ Set.Icc 1 ⌊T⌋₊),
                (m : ℝ) / Nat.totient m) = (m : ℝ) / Nat.totient m :=
          ciSup_pos hm_in
        rw [← h_inner_eq]
        exact le_ciSup hbdd_inner m
      linarith [hm_ratio_eq]
    have hD_pos : 0 < D T := mul_pos hγc_pos hloglog_pos
    refine ⟨?_, ?_⟩
    · exact div_le_div_of_nonneg_right hS_ge_L hD_pos.le
    · exact div_le_div_of_nonneg_right hS_le_LF hD_pos.le
  -- Apply squeeze.
  have h_lower : ∀ᶠ T : ℝ in atTop, L T / D T ≤ S T / D T :=
    h_bound_ev.mono (fun _ h => h.1)
  have h_upper : ∀ᶠ T : ℝ in atTop, S T / D T ≤ L T * F T / D T :=
    h_bound_ev.mono (fun _ h => h.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_LD h_UD h_lower h_upper

/- ## Section 2 — The asymptotic formula -/

/-- The maximal totient-fibre ratio at scale `x`. -/
noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin

/-- **Theorem 2.1 (upper bound).** `R(x) ≤ (e^γ + o(1)) log log x`.

Proof: for `n ≤ x` and `M = f_max(n)`, `m = f_min(n)`, the inequality
`M/m ≤ M/φ(M)` (since `m/φ(m) ≥ 1`) plus fibre-finiteness `M ≤ 2n² ≤ 2x²`
plus Lemma 1.1 give the bound.
-/
theorem R_upper_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log x) := by
  intro ε hε_pos
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  have hε2_pos : 0 < ε / 2 := by positivity
  have hδ_pos : 0 < ε / (2 * γc) := by positivity
  -- Step 1: Get eventually-for-real-T bound on S(T) := ⨆ m ∈ Icc 1 ⌊T⌋₊, m/φ(m).
  have h_evlt :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) /
          (γc * Real.log (Real.log T)) ≤ 1 + ε / (2 * γc) := by
    have hone_lt : (1 : ℝ) < 1 + ε / (2 * γc) := by linarith
    exact landau_max_ratio.eventually_le_const hone_lt
  have h_pos_log_log : ∀ᶠ T : ℝ in atTop, 0 < Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with T hT
    have hexp_pos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
    have hlogT : 1 < Real.log T := by
      have := Real.log_lt_log hexp_pos hT
      simpa [Real.log_exp] using this
    exact Real.log_pos hlogT
  have h_landau_bound :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log T) := by
    filter_upwards [h_evlt, h_pos_log_log] with T hT_le hT_llog_pos
    have hg_pos : 0 < γc * Real.log (Real.log T) := mul_pos hγc_pos hT_llog_pos
    have hf_le : (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
        (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) :=
      (div_le_iff₀ hg_pos).mp hT_le
    have heq : (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) =
        (γc + ε/2) * Real.log (Real.log T) := by
      field_simp
    rw [heq] at hf_le
    exact hf_le
  -- Step 2: precompose with T(x) = 2 * x^2.
  have htends_2xsq : Tendsto (fun x : ℕ => (2 : ℝ) * (x : ℝ)^2) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℕ => ((x : ℝ))^2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp h1
    exact Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) h2
  have h_landau_at_T :
      ∀ᶠ x : ℕ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) :=
    htends_2xsq.eventually h_landau_bound
  -- Step 3: For x ≥ 2, log log(2x²) ≤ log 4 + log log x.
  have h_loglog_bound :
      ∀ᶠ x : ℕ in atTop,
        Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) ≤ Real.log 4 + Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hx_ge_2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le_logx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx_ge_2
    have heq1 : Real.log ((2 : ℝ) * (x : ℝ)^2) = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have hlogargs : Real.log 2 + 2 * Real.log x ≤ 4 * Real.log x := by linarith
    have hlog_inner_pos : 0 < Real.log 2 + 2 * Real.log x := by linarith
    have h_le_log : Real.log (Real.log 2 + 2 * Real.log x) ≤ Real.log (4 * Real.log x) :=
      Real.log_le_log hlog_inner_pos hlogargs
    have heq2 : Real.log (4 * Real.log x) = Real.log 4 + Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) hlogx_pos.ne']
    rw [heq1]; linarith
  -- Step 4: log log x → ∞ as ℕ → ∞.
  have h_loglog_to_inf : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  -- Step 5: eventually log log x ≥ 2(γc + ε/2)log 4 / ε.
  have h_loglog_large :
      ∀ᶠ x : ℕ in atTop,
        (γc + ε/2) * Real.log 4 ≤ (ε / 2) * Real.log (Real.log x) := by
    -- want eventually log log x ≥ K where K = (γc+ε/2) log 4 * 2 / ε.
    set K : ℝ := (γc + ε/2) * Real.log 4 * 2 / ε
    have hK_eventually : ∀ᶠ x : ℕ in atTop, K ≤ Real.log (Real.log x) :=
      h_loglog_to_inf.eventually_ge_atTop K
    filter_upwards [hK_eventually] with x hxK
    have hε_pos' : (0 : ℝ) < ε := hε_pos
    have hKeq : (γc + ε/2) * Real.log 4 = (ε / 2) * K := by
      show (γc + ε/2) * Real.log 4 = (ε / 2) * ((γc + ε/2) * Real.log 4 * 2 / ε)
      field_simp
    rw [hKeq]
    have hε_half_pos : (0 : ℝ) < ε / 2 := hε2_pos
    exact (mul_le_mul_of_nonneg_left hxK hε_half_pos.le)
  -- Step 6: combine all bounds, plus R x ≤ S(2x²).
  -- R x ≤ S(2x²) — to be proved.
  have h_R_le_S :
      ∀ᶠ x : ℕ in atTop,
        R x ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx1
    -- Notation
    set S2x : ℝ := ⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m with hS2x_def
    -- Boundedness for the inner family
    have hfloor_pos : 1 ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := by
      apply Nat.le_floor
      have hx_pos : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
      have : (1 : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by nlinarith
      exact_mod_cast this
    -- BddAbove for the inner family (m/φ m ≤ m ≤ ⌊2x²⌋₊).
    have hbdd_inner :
        BddAbove (Set.range (fun (m : ℕ) =>
          ⨆ (_ : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊), (m : ℝ) / Nat.totient m)) := by
      refine ⟨((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ), ?_⟩
      rintro _ ⟨m, rfl⟩
      simp only
      by_cases hm : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊
      · rw [ciSup_pos hm]
        have hφ_pos : 0 < Nat.totient m := Nat.totient_pos.mpr hm.1
        have h_div_le : (m : ℝ) / Nat.totient m ≤ m := by
          rw [div_le_iff₀ (by exact_mod_cast hφ_pos)]
          have h1 : (1 : ℝ) ≤ (Nat.totient m : ℝ) := by exact_mod_cast hφ_pos
          have h2 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast m.zero_le
          nlinarith
        have h_le : (m : ℝ) ≤ ((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm.2
        linarith
      · rw [ciSup_neg hm, Real.sSup_empty]
        exact_mod_cast Nat.zero_le _
    -- S2x ≥ 0 (witness m=1).
    have hS2x_nonneg : 0 ≤ S2x := by
      have h1mem : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨le_refl _, hfloor_pos⟩
      have h1_term : (1 : ℝ) / Nat.totient 1 = 1 := by simp
      have h_ge : (1 : ℝ) ≤ S2x := by
        rw [hS2x_def]
        calc (1 : ℝ) = (1 : ℝ) / Nat.totient 1 := h1_term.symm
          _ ≤ ⨆ (_ : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
                ((1 : ℕ) : ℝ) / Nat.totient 1 := by
              rw [ciSup_pos h1mem]
              push_cast; rfl
          _ ≤ _ := le_ciSup hbdd_inner 1
      linarith
    -- Now R x = iSup over n of inner. Apply ciSup_le for outer (Nonempty ℕ).
    unfold R
    apply ciSup_le
    intro n
    -- Inner: ⨆ (_ : n ∈ S_x), (mmax:ℝ)/mmin where S_x is the predicate set.
    by_cases hmem : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hmem]
      -- Now compute mmax, mmin and bound mmax/mmin ≤ S2x.
      obtain ⟨hn_in_Icc, m_wit, hφm⟩ := hmem
      -- The set A = {m | φ m = n}.
      set A : Set ℕ := {m | Nat.totient m = n} with hA_def
      have hn_pos : 1 ≤ n := hn_in_Icc.1
      have hn_le_x : n ≤ x := hn_in_Icc.2
      -- m_wit ∈ A. m_wit ≥ 1 since φ m_wit = n ≥ 1 implies m_wit ≥ 1.
      have hm_wit_pos : 1 ≤ m_wit := by
        rcases Nat.eq_zero_or_pos m_wit with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm; omega
        · exact hpos
      -- A is nonempty.
      have hA_ne : A.Nonempty := ⟨m_wit, hφm⟩
      -- A is bounded above by 2n².
      have hA_bdd : BddAbove A := by
        refine ⟨2 * n ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have hm' : Nat.totient m = n := hm
            rw [h0, Nat.totient_zero] at hm'; omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      -- mmax := sSup A is in A by Nat.sSup_mem.
      set mmax : ℕ := sSup A with hmmax_def
      have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
      have hφmmax : Nat.totient mmax = n := hmmax_in
      have hmmax_pos : 1 ≤ mmax := by
        rcases Nat.eq_zero_or_pos mmax with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax; omega
        · exact hpos
      -- mmax ≤ 2n² ≤ 2x².
      have hmmax_le_2nsq : mmax ≤ 2 * n ^ 2 := totient_preimage_bound hmmax_pos hφmmax
      have hmmax_le_2xsq_R : (mmax : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
        have h1 : (mmax : ℝ) ≤ (2 * n^2 : ℕ) := by exact_mod_cast hmmax_le_2nsq
        have h2 : ((2 * n^2 : ℕ) : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
          push_cast
          have hn_le_x_R : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn_le_x
          have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
          nlinarith
        linarith
      have hmmax_le_floor : mmax ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := Nat.le_floor hmmax_le_2xsq_R
      have hmmax_in_Icc : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨hmmax_pos, hmmax_le_floor⟩
      -- mmin := sInf A in A.
      set mmin : ℕ := sInf A with hmmin_def
      have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
      have hφmmin : Nat.totient mmin = n := hmmin_in
      have hmmin_pos : 1 ≤ mmin := by
        rcases Nat.eq_zero_or_pos mmin with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin; omega
        · exact hpos
      -- mmin ≥ n (since n = φ mmin ≤ mmin).
      have hmmin_ge_n : n ≤ mmin := by
        have := Nat.totient_le mmin; rw [hφmmin] at this; exact this
      -- (mmax:ℝ)/mmin ≤ (mmax:ℝ)/n = (mmax:ℝ)/φ(mmax) ≤ S2x.
      show (mmax : ℝ) / mmin ≤ S2x
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
      have hmmax_nn_R : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
      have hmmin_ge_n_R : (n : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmmin_ge_n
      have h_div_le : (mmax : ℝ) / mmin ≤ (mmax : ℝ) / n := by
        apply div_le_div_of_nonneg_left hmmax_nn_R hn_pos_R hmmin_ge_n_R
      have h_n_eq : ((n : ℝ)) = (Nat.totient mmax : ℝ) := by exact_mod_cast hφmmax.symm
      rw [h_n_eq] at h_div_le
      have h_term_le_S : (mmax : ℝ) / Nat.totient mmax ≤ S2x := by
        have h_inner_eq :
            (⨆ (_ : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
                (mmax : ℝ) / Nat.totient mmax) = (mmax : ℝ) / Nat.totient mmax :=
          ciSup_pos hmmax_in_Icc
        rw [hS2x_def, ← h_inner_eq]
        exact le_ciSup hbdd_inner mmax
      linarith
    · rw [ciSup_neg hmem]
      rw [Real.sSup_empty]
      exact hS2x_nonneg
  -- Step 7: assemble.
  have hllog_pos_ev : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have hlog3_lt_logx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    have h1 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    have h2 : 1 ≤ Real.log x := by linarith
    exact (Real.log_nonneg h2)
  filter_upwards [h_landau_at_T, h_loglog_bound, h_loglog_large, h_R_le_S, hllog_pos_ev]
    with x h1 h2 h3 h4 h5
  -- have h1 : S(2x²) ≤ (γc + ε/2) * log log (2x²)
  -- have h2 : log log(2x²) ≤ log 4 + log log x
  -- have h3 : (γc + ε/2) * log 4 ≤ (ε/2) * log log x
  -- have h4 : R x ≤ S(2x²)
  -- have h5 : 0 ≤ log log x
  -- want: R x ≤ (γc + ε) * log log x.
  -- (γc + ε/2)(log 4 + log log x) = (γc + ε/2) log 4 + (γc + ε/2) log log x
  --   ≤ (ε/2) log log x + (γc + ε/2) log log x = (γc + ε) log log x.
  have hγε2_pos : 0 ≤ γc + ε / 2 := by linarith
  calc R x
      ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := h4
    _ ≤ (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) := h1
    _ ≤ (γc + ε/2) * (Real.log 4 + Real.log (Real.log x)) :=
        mul_le_mul_of_nonneg_left h2 hγε2_pos
    _ = (γc + ε/2) * Real.log 4 + (γc + ε/2) * Real.log (Real.log x) := by ring
    _ ≤ (ε/2) * Real.log (Real.log x) + (γc + ε/2) * Real.log (Real.log x) := by linarith
    _ = (γc + ε) * Real.log (Real.log x) := by ring

/- **Theorem 2.1 (lower bound).** `R(x) ≥ (e^γ + o(1)) log log x`.

The formal proof uses Linnik with modulus `A_Y * P_Y`, giving a prime `ℓ`
with `A_Y * P_Y ∣ ℓ - 1`. In particular `A_Y ∣ ℓ - 1`, so the construction
`U_Y = (ℓ - 1)/A_Y`, `Q_Y = ∏_{q | U_Y, Y < q} q`, `a_Y = ℓ Q_Y`,
`b_Y = P_Y U_Y Q_Y` works.

The deterministic part proves:
`φ(a_Y) = φ(b_Y)`,
`b_Y/a_Y = primeEulerProdNat Y · (ℓ - 1)/ℓ`, and
`n_Y ≤ A_Y · ℓ²`.

For height control, the proof avoids PNT/theta and uses
`A_Y ≤ P_Y ≤ 4^Y`, hence `n_Y ≤ exp(K·Y)` for a constant `K`.
Taking `Y = ⌊log x / (2K)⌋` gives `n_Y ≤ x` eventually and
`log Y = log log x + O(1)`.
-/
/- ## Lower-bound construction (Phase 1+2: foundations)

This namespace builds the deterministic ingredients for the totient-collision
construction, deferring all asymptotic content to later phases. The deterministic
phase (Phases 1-6) is independent of `mertens_product`, `linnik_dvd`, and any
axiom; it is pure prime-factor bookkeeping. The asymptotic wrapper at the end of
the namespace consumes both axioms.
-/

namespace LowerConstruction

open Classical Filter
open scoped BigOperators Nat

/-- Primes up to `Y`. -/
noncomputable def smallPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

/-- `P_Y = ∏_{p≤Y} p`. -/
noncomputable def P (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, p

/-- `A_Y = ∏_{p≤Y} (p - 1)`. -/
noncomputable def A (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, (p - 1)

/-- Large prime factors of `U`, namely those above `Y`. -/
noncomputable def largeFactors (Y U : ℕ) : Finset ℕ :=
  U.primeFactors.filter fun q => Y < q

/-- `Q_Y(U) = ∏_{q | U, q > Y} q`. -/
noncomputable def Q (Y U : ℕ) : ℕ :=
  ∏ q ∈ largeFactors Y U, q

lemma A_pos (Y : ℕ) : 0 < A Y := by
  unfold A
  refine Finset.prod_pos ?_
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h2 : 2 ≤ p := hpprime.two_le
  omega

lemma P_pos (Y : ℕ) : 0 < P Y := by
  unfold P
  refine Finset.prod_pos ?_
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  exact hpprime.pos

lemma Q_pos (Y U : ℕ) : 0 < Q Y U := by
  unfold Q
  refine Finset.prod_pos ?_
  intro q hq
  rw [largeFactors] at hq
  rcases Finset.mem_filter.mp hq with ⟨hqU, _⟩
  exact (Nat.prime_of_mem_primeFactors hqU).pos

lemma A_le_P (Y : ℕ) : A Y ≤ P Y := by
  unfold A P
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    rw [smallPrimes] at hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
    have h2 : 2 ≤ p := hpprime.two_le
    omega
  · intro p _
    omega

lemma P_eq_primorial (Y : ℕ) : P Y = primorial Y := by
  unfold P smallPrimes primorial
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpY⟩, hpprime⟩
      exact ⟨by omega, hpprime⟩
    · rintro ⟨hpY, hpprime⟩
      have h1 : 1 ≤ p := hpprime.one_le
      exact ⟨⟨h1, by omega⟩, hpprime⟩
  · intros; rfl

lemma P_le_four_pow (Y : ℕ) : P Y ≤ 4 ^ Y := by
  rw [P_eq_primorial]
  exact primorial_le_4_pow Y

lemma A_le_four_pow (Y : ℕ) : A Y ≤ 4 ^ Y :=
  (A_le_P Y).trans (P_le_four_pow Y)

/-- `Q Y U` divides `U`, since it is a product of distinct prime factors of `U`. -/
lemma Q_dvd_U (Y U : ℕ) (_hU : U ≠ 0) : Q Y U ∣ U := by
  unfold Q largeFactors
  -- Q = ∏ q ∈ U.primeFactors.filter (Y < ·), q.
  -- This divides ∏ q ∈ U.primeFactors, q, which divides U.
  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd U)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- If `0 < U < ℓ` and `ℓ` is prime, then `ℓ` is NOT a prime factor of `U`. -/
lemma ell_not_mem_largeFactors {Y U ℓ : ℕ} (_hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) : ℓ ∉ largeFactors Y U := by
  intro hmem
  have h1 : ℓ ∈ U.primeFactors := (Finset.mem_filter.mp hmem).1
  have h2 : ℓ ∣ U := Nat.dvd_of_mem_primeFactors h1
  have h3 : ℓ ≤ U := Nat.le_of_dvd hU_pos h2
  exact (lt_irrefl _) (h3.trans_lt hU_lt)

/-- The prime factors of `Q Y U` are exactly `largeFactors Y U`. -/
lemma primeFactors_Q (Y U : ℕ) (_hU : U ≠ 0) :
    (Q Y U).primeFactors = largeFactors Y U := by
  unfold Q
  apply Nat.primeFactors_prod
  intro q hq
  rw [largeFactors] at hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

/-- The prime factors of `P Y` are exactly `smallPrimes Y`. -/
lemma primeFactors_P (Y : ℕ) :
    (P Y).primeFactors = smallPrimes Y := by
  unfold P
  apply Nat.primeFactors_prod
  intro p hp
  rw [smallPrimes] at hp
  exact (Finset.mem_filter.mp hp).2

/-- The prime factors of `ℓ * Q Y U` (when `ℓ` is prime, `0 < U < ℓ`) are exactly
`{ℓ} ∪ largeFactors Y U`. -/
lemma primeFactors_a (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U) (_hU_lt : U < ℓ) :
    (ℓ * Q Y U).primeFactors = insert ℓ (largeFactors Y U) := by
  have hU_ne : U ≠ 0 := Nat.pos_iff_ne_zero.mp hU_pos
  have hQ_ne : Q Y U ≠ 0 := Nat.pos_iff_ne_zero.mp (Q_pos Y U)
  rw [Nat.primeFactors_mul hℓ.ne_zero hQ_ne, hℓ.primeFactors,
    primeFactors_Q Y U hU_ne]
  ext r
  simp [Finset.mem_insert]

/-- The prime factors of `P Y * U * Q Y U` are exactly `smallPrimes Y ∪ largeFactors Y U`,
provided `U > 0` and `Q Y U` divides `U`. -/
lemma primeFactors_b (Y U : ℕ) (hU_pos : 0 < U) (_hU_dvd : Q Y U ∣ U) :
    (P Y * U * Q Y U).primeFactors = smallPrimes Y ∪ largeFactors Y U := by
  have hU_ne : U ≠ 0 := Nat.pos_iff_ne_zero.mp hU_pos
  have hP_ne : P Y ≠ 0 := Nat.pos_iff_ne_zero.mp (P_pos Y)
  have hQ_ne : Q Y U ≠ 0 := Nat.pos_iff_ne_zero.mp (Q_pos Y U)
  have hPU_ne : P Y * U ≠ 0 := mul_ne_zero hP_ne hU_ne
  rw [Nat.primeFactors_mul hPU_ne hQ_ne, Nat.primeFactors_mul hP_ne hU_ne,
    primeFactors_P, primeFactors_Q Y U hU_ne]
  ext r
  simp only [Finset.mem_union]
  constructor
  · rintro ((hr | hr) | hr)
    · exact Or.inl hr
    · -- r ∈ U.primeFactors. Case on r ≤ Y or r > Y.
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrU : r ∣ U := Nat.dvd_of_mem_primeFactors hr
      by_cases hY : Y < r
      · refine Or.inr ?_
        rw [largeFactors]
        exact Finset.mem_filter.mpr ⟨hr, hY⟩
      · refine Or.inl ?_
        rw [smallPrimes]
        push_neg at hY
        have h1 : 1 ≤ r := hrp.one_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hY⟩, hrp⟩
    · exact Or.inr hr
  · rintro (hr | hr)
    · exact Or.inl (Or.inl hr)
    · exact Or.inr hr

/-- The bridge to `mertens_product`: `(P Y : ℝ) / A Y` equals the
`primeEulerProdNat Y` defined in `Erdos694Scratch`. -/
lemma P_div_A_eq_primeEulerProdNat (Y : ℕ) :
    (P Y : ℝ) / (A Y : ℝ) = primeEulerProdNat Y := by
  unfold P A primeEulerProdNat
  rw [show ((Finset.Icc 1 Y).filter Nat.Prime) = smallPrimes Y from rfl]
  rw [Nat.cast_prod, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h1 : 1 ≤ p := hpprime.one_le
  rw [Nat.cast_sub h1]
  push_cast
  rfl

/-! ### Phase 4: Totient equalities for the construction -/

/-- `smallPrimes Y` and `largeFactors Y U` are disjoint, since one consists of primes `≤ Y`
and the other of primes `> Y`. -/
lemma smallPrimes_disjoint_largeFactors (Y U : ℕ) :
    Disjoint (smallPrimes Y) (largeFactors Y U) := by
  rw [Finset.disjoint_left]
  intro p hp_small hp_large
  rw [smallPrimes, Finset.mem_filter, Finset.mem_Icc] at hp_small
  rw [largeFactors, Finset.mem_filter] at hp_large
  have h1 : p ≤ Y := hp_small.1.2
  have h2 : Y < p := hp_large.2
  omega

/-- The product of primes in `largeFactors Y U` equals `Q Y U`. -/
lemma prod_largeFactors_eq_Q (Y U : ℕ) :
    ∏ q ∈ largeFactors Y U, q = Q Y U := rfl

/-- The product of primes in `smallPrimes Y` equals `P Y`. -/
lemma prod_smallPrimes_eq_P (Y : ℕ) :
    ∏ p ∈ smallPrimes Y, p = P Y := rfl

/-- The product of `(p - 1)` over `smallPrimes Y` equals `A Y`. -/
lemma prod_smallPrimes_sub_one_eq_A (Y : ℕ) :
    ∏ p ∈ smallPrimes Y, (p - 1) = A Y := rfl

/-- `φ(ℓ · Q) = (ℓ - 1) · ∏_{q ∈ largeFactors Y U} (q - 1)`. -/
lemma totient_a_eq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U) (hU_lt : U < ℓ)
    (_hQ_dvd : Q Y U ∣ U) :
    (Nat.totient (ℓ * Q Y U) : ℕ) =
      (ℓ - 1) * ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hℓ_ne : ℓ ≠ 0 := hℓ.ne_zero
  have hQ_ne : Q Y U ≠ 0 := (Q_pos Y U).ne'
  have hN_ne : ℓ * Q Y U ≠ 0 := mul_ne_zero hℓ_ne hQ_ne
  -- Key formula: φ(N) * ∏ p = N * ∏ (p - 1).
  have hkey := Nat.totient_mul_prod_primeFactors (ℓ * Q Y U)
  rw [primeFactors_a Y U ℓ hℓ hU_pos hU_lt] at hkey
  have hℓ_notin : ℓ ∉ largeFactors Y U := ell_not_mem_largeFactors hℓ hU_pos hU_lt
  rw [Finset.prod_insert hℓ_notin, Finset.prod_insert hℓ_notin] at hkey
  -- ∏_{p ∈ insert ℓ S} p = ℓ * ∏ q = ℓ * Q
  -- Now: φ(ℓ Q) * (ℓ * ∏q) = (ℓ * Q) * ((ℓ - 1) * ∏ (q - 1))
  -- The left side product ∏ q over largeFactors equals Q.
  rw [prod_largeFactors_eq_Q] at hkey
  -- hkey : φ(ℓ Q) * (ℓ * Q) = (ℓ * Q) * ((ℓ - 1) * ∏ (q - 1))
  have hN_pos : 0 < ℓ * Q Y U := Nat.pos_of_ne_zero hN_ne
  have : (ℓ * Q Y U) * Nat.totient (ℓ * Q Y U) =
      (ℓ * Q Y U) * ((ℓ - 1) * ∏ q ∈ largeFactors Y U, (q - 1)) := by
    rw [mul_comm (ℓ * Q Y U) (Nat.totient (ℓ * Q Y U))]
    convert hkey using 1
  exact Nat.eq_of_mul_eq_mul_left hN_pos this

/-- For the construction, `φ(P_Y · U · Q_Y(U)) = A_Y · U · ∏_{q ∈ largeFactors} (q - 1)`. -/
lemma totient_b_eq_under_construction (Y U ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (hU_pos : 0 < U) (_hU_lt : U < ℓ)
    (_hAU : A Y * U = ℓ - 1) :
    (Nat.totient (P Y * U * Q Y U) : ℕ) =
      A Y * U * ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hP_ne : P Y ≠ 0 := (P_pos Y).ne'
  have hU_ne : U ≠ 0 := hU_pos.ne'
  have hQ_ne : Q Y U ≠ 0 := (Q_pos Y U).ne'
  have hQ_dvd : Q Y U ∣ U := Q_dvd_U Y U hU_ne
  have hPU_ne : P Y * U ≠ 0 := mul_ne_zero hP_ne hU_ne
  have hN_ne : P Y * U * Q Y U ≠ 0 := mul_ne_zero hPU_ne hQ_ne
  have hN_pos : 0 < P Y * U * Q Y U := Nat.pos_of_ne_zero hN_ne
  -- Key formula: φ(N) * ∏ p = N * ∏ (p - 1) where the products are over N.primeFactors.
  have hkey := Nat.totient_mul_prod_primeFactors (P Y * U * Q Y U)
  rw [primeFactors_b Y U hU_pos hQ_dvd] at hkey
  have hdisj : Disjoint (smallPrimes Y) (largeFactors Y U) :=
    smallPrimes_disjoint_largeFactors Y U
  rw [Finset.prod_union hdisj, Finset.prod_union hdisj] at hkey
  -- hkey : φ(N) * (P Y * Q Y U) = N * (A Y * ∏ (q-1))
  rw [prod_smallPrimes_eq_P, prod_largeFactors_eq_Q,
      prod_smallPrimes_sub_one_eq_A] at hkey
  -- hkey : φ(N) * (P Y * Q Y U) = (P Y * U * Q Y U) * (A Y * ∏ (q - 1))
  -- We want: φ(N) = A Y * U * ∏ (q - 1).
  -- Multiply target by (P Y * Q Y U): A Y * U * ∏ (q-1) * (P Y * Q Y U) =
  -- (P Y * U * Q Y U) * (A Y * ∏ (q-1)). Same as hkey RHS.
  have hPQ_pos : 0 < P Y * Q Y U := Nat.mul_pos (P_pos Y) (Q_pos Y U)
  have hcancel :
      Nat.totient (P Y * U * Q Y U) * (P Y * Q Y U) =
        (A Y * U * ∏ q ∈ largeFactors Y U, (q - 1)) * (P Y * Q Y U) := by
    rw [hkey]; ring
  exact Nat.eq_of_mul_eq_mul_right hPQ_pos hcancel

/-- The crucial collision: `φ(ℓ · Q) = φ(P_Y · U · Q)` for the construction. -/
lemma totient_a_eq_totient_b (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (hU_pos : 0 < U) (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) = Nat.totient (P Y * U * Q Y U) := by
  have hU_ne : U ≠ 0 := hU_pos.ne'
  rw [totient_a_eq Y U ℓ hℓ hU_pos hU_lt (Q_dvd_U Y U hU_ne),
      totient_b_eq_under_construction Y U ℓ hℓ hU_pos hU_lt hAU, ← hAU]

/-! ### Phase 5: Ratio identity -/

/-- `b/a = (P_Y/A_Y) · ((ℓ-1)/ℓ)` for the construction. -/
lemma collision_ratio (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (_hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    ((P Y * U * Q Y U : ℕ) : ℝ) / ((ℓ * Q Y U : ℕ) : ℝ) =
      primeEulerProdNat Y * ((ℓ - 1 : ℝ) / ℓ) := by
  have hℓ_pos : 0 < ℓ := hℓ.pos
  have hQ_pos : 0 < Q Y U := Q_pos Y U
  have hA_pos : 0 < A Y := A_pos Y
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ_pos.ne'
  have hQR : (Q Y U : ℝ) ≠ 0 := by exact_mod_cast hQ_pos.ne'
  have hAR : (A Y : ℝ) ≠ 0 := by exact_mod_cast hA_pos.ne'
  -- Cast (ℓ - 1) using the Nat subtraction-vs-ℝ bridge.
  have hℓ_one : 1 ≤ ℓ := hℓ.one_le
  have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub hℓ_one]; norm_num
  -- (P Y * U * Q Y U : ℝ) / (ℓ * Q Y U : ℝ) = (P Y * U) / ℓ.
  push_cast
  have step1 : ((P Y : ℝ) * U * Q Y U) / ((ℓ : ℝ) * Q Y U) =
      ((P Y : ℝ) * U) / (ℓ : ℝ) := by
    field_simp
  rw [step1]
  -- Use A Y * U = ℓ - 1 in ℝ: cast.
  have hAU_R : (A Y : ℝ) * (U : ℝ) = (ℓ : ℝ) - 1 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hAU
    simp at this
    rw [hℓm1_cast] at this
    exact this
  -- So U = (ℓ - 1) / A Y in ℝ.
  have hU_R : (U : ℝ) = ((ℓ : ℝ) - 1) / (A Y : ℝ) := by
    field_simp
    linarith [hAU_R]
  rw [hU_R]
  -- Now LHS = P Y * ((ℓ - 1) / A Y) / ℓ = (P Y / A Y) * ((ℓ - 1) / ℓ).
  rw [← P_div_A_eq_primeEulerProdNat]
  field_simp

/-! ### Phase 6: Crude size bound -/

/-- The constructed totient value is bounded: `φ(ℓ · Q) ≤ A_Y · U²`. -/
lemma collision_n_le_A_mul_U_sq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) ≤ A Y * U * U := by
  have hU_ne : U ≠ 0 := hU_pos.ne'
  have hQ_dvd : Q Y U ∣ U := Q_dvd_U Y U hU_ne
  rw [totient_a_eq Y U ℓ hℓ hU_pos hU_lt hQ_dvd, ← hAU]
  -- (A Y * U) * ∏ (q - 1) ≤ A Y * U * U
  -- Suffices: ∏ (q - 1) ≤ U.
  have hprod_le_Q : ∏ q ∈ largeFactors Y U, (q - 1) ≤ Q Y U := by
    unfold Q
    refine Finset.prod_le_prod (fun q _ => Nat.zero_le _) ?_
    intro q _
    omega
  have hQ_le_U : Q Y U ≤ U := Nat.le_of_dvd hU_pos hQ_dvd
  have hprod_le_U : ∏ q ∈ largeFactors Y U, (q - 1) ≤ U :=
    le_trans hprod_le_Q hQ_le_U
  calc A Y * U * ∏ q ∈ largeFactors Y U, (q - 1)
      ≤ A Y * U * U := Nat.mul_le_mul_left _ hprod_le_U

/-- The constructed totient value is bounded by `A_Y · ℓ²`. -/
lemma collision_n_le_A_mul_ell_sq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) ≤ A Y * (ℓ * ℓ) := by
  have h1 := collision_n_le_A_mul_U_sq Y U ℓ hℓ hU_pos hU_lt hAU
  have hU_le_ℓ : U ≤ ℓ := hU_lt.le
  calc Nat.totient (ℓ * Q Y U)
      ≤ A Y * U * U := h1
    _ ≤ A Y * ℓ * ℓ := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ hU_le_ℓ) hU_le_ℓ
    _ = A Y * (ℓ * ℓ) := by ring

end LowerConstruction

/-! ### Helper lemmas for `collision_at_height` -/

/-- Mertens product, lifted along `ℕ → ℝ` (in terms of `primeEulerProdNat`). -/
private lemma mertens_product_nat :
    Tendsto
      (fun Y : ℕ =>
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)))
      atTop (𝓝 1) := by
  have h_yT_to_inf : Tendsto (fun Y : ℕ => ((Y : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := mertens_product.comp h_yT_to_inf
  have h_eq : ∀ᶠ Y : ℕ in atTop,
      (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊((Y : ℕ) : ℝ)⌋₊),
            ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log ((Y : ℕ) : ℝ)) =
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
    filter_upwards with Y
    have hfloor : ⌊((Y : ℕ) : ℝ)⌋₊ = Y := Nat.floor_natCast Y
    rw [hfloor]
    rfl
  exact h.congr' h_eq

/-- `LowerConstruction.P` tends to infinity as `Y → ∞`. -/
private lemma lc_P_atTop : Tendsto (fun Y : ℕ => LowerConstruction.P Y) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  obtain ⟨p, hpM, hp_prime⟩ := Nat.exists_infinite_primes M
  refine ⟨p, fun Y hY => ?_⟩
  -- For Y ≥ p, P Y = primorial Y ≥ primorial p ≥ p ≥ M.
  rw [LowerConstruction.P_eq_primorial]
  -- primorial is monotone in Y.
  have h_mono : primorial p ≤ primorial Y := by
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨?_, hq.2⟩
      have hq_lt : q < p + 1 := Finset.mem_range.mp hq.1
      exact Finset.mem_range.mpr (by omega)
    · intros q hq _
      rw [Finset.mem_filter] at hq
      exact hq.2.one_le
  -- p ≤ primorial p (since p ∈ filter Prime (range (p+1))).
  have h_p_le : p ≤ primorial p := by
    unfold primorial
    have hp_mem : p ∈ Finset.filter Nat.Prime (Finset.range (p + 1)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp_prime⟩
    have h_prod_singleton : p = ∏ x ∈ ({p} : Finset ℕ), id x := by simp
    calc p = ∏ x ∈ ({p} : Finset ℕ), id x := h_prod_singleton
      _ ≤ ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), id x := by
          refine Finset.prod_le_prod_of_subset_of_one_le'
            (Finset.singleton_subset_iff.mpr hp_mem) ?_
          intros q hq _
          rw [Finset.mem_filter] at hq
          exact hq.2.one_le
      _ = ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), x := by
          simp
  linarith

/-- Size bound for the construction: `n ≤ exp((2 log C + (4L+1) log 4 + 1) · Y)`. -/
private lemma collision_size_bound (Y U ℓ : ℕ) (C : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hℓ_prime : Nat.Prime ℓ) (hU_pos : 0 < U) (hU_lt_ℓ : U < ℓ)
    (hAU : LowerConstruction.A Y * U = ℓ - 1)
    (hℓ_le : (ℓ : ℝ) ≤ C * ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ^ L)
    (hY1 : 1 ≤ Y) :
    (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
      Real.exp ((2 * Real.log C + (4 * L + 1) * Real.log 4 + 1) * Y) := by
  classical
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hℓ_pos : 0 < ℓ := hℓ_prime.pos
  have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
  have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
  -- Step 1: φ(ℓ Q) ≤ A Y · ℓ².
  have h_n_le : Nat.totient (ℓ * LowerConstruction.Q Y U) ≤
      LowerConstruction.A Y * (ℓ * ℓ) :=
    LowerConstruction.collision_n_le_A_mul_ell_sq Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
  have h_n_le_R :
      (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
        (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := by
    have h0 := (Nat.cast_le (α := ℝ)).mpr h_n_le
    push_cast at h0
    linarith [h0]
  -- Step 2: A Y ≤ 4^Y, P Y ≤ 4^Y, in ℝ.
  have hA_le4 : (LowerConstruction.A Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.A_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_le4 : (LowerConstruction.P Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.P_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_nn : (0 : ℝ) ≤ (LowerConstruction.P Y : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4_pow_pos : (0 : ℝ) < (4 : ℝ) ^ Y := by positivity
  -- A Y * P Y ≤ 4^(2Y).
  have hAP_le : ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (2 * Y) := by
    push_cast
    calc (LowerConstruction.A Y : ℝ) * (LowerConstruction.P Y : ℝ)
        ≤ (4 : ℝ) ^ Y * (4 : ℝ) ^ Y :=
          mul_le_mul hA_le4 hP_le4 hP_nn (by positivity)
      _ = (4 : ℝ) ^ (Y + Y) := by rw [pow_add]
      _ = (4 : ℝ) ^ (2 * Y) := by ring_nf
  have hAP_nn : (0 : ℝ) ≤ ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  -- ℓ ≤ C · 4^(2LY).
  have hℓ_le2 : (ℓ : ℝ) ≤ C * ((4 : ℝ) ^ (2 * Y)) ^ L := by
    apply hℓ_le.trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ C)
    exact pow_le_pow_left₀ hAP_nn hAP_le L
  have h4_pow_id : ((4 : ℝ) ^ (2 * Y)) ^ L = (4 : ℝ) ^ (2 * Y * L) := by
    rw [← pow_mul]
  rw [h4_pow_id] at hℓ_le2
  have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast Nat.zero_le _
  -- ℓ² ≤ C² · 4^(4YL).
  have hℓ_sq_le : (ℓ : ℝ) * (ℓ : ℝ) ≤ C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
    have h_step : (ℓ : ℝ) * (ℓ : ℝ) ≤
        (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) :=
      mul_le_mul hℓ_le2 hℓ_le2 hℓ_nn (by positivity)
    have h_eq : (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
      rw [show (4 * Y * L) = (2 * Y * L) + (2 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq ▸ h_step]
  -- A Y · ℓ² ≤ C² · 4^((4L+1)Y).
  have h_total : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
      C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
    have hsq_nn : (0 : ℝ) ≤ (ℓ : ℝ) * (ℓ : ℝ) := mul_nonneg hℓ_nn hℓ_nn
    have h_step1 : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
        (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) := by
      exact mul_le_mul hA_le4 hℓ_sq_le hsq_nn (by positivity)
    have h_eq2 : (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
      rw [show ((4 * L + 1) * Y) = Y + (4 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq2 ▸ h_step1]
  -- Now bound C² · 4^((4L+1)Y) ≤ exp(K·Y).
  have hC_pos : 0 < C := by linarith
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_C2_pos : 0 < C ^ 2 := pow_pos hC_pos 2
  have h_4pow_pos : (0 : ℝ) < (4 : ℝ) ^ ((4 * L + 1) * Y) := by positivity
  have h_lhs_pos : (0 : ℝ) < C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) :=
    mul_pos h_C2_pos h_4pow_pos
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hY_R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hY_nn : (0 : ℝ) ≤ (Y : ℝ) := by linarith
  have h_log_lhs : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) =
      2 * Real.log C + ((4 * L + 1) * Y : ℕ) * Real.log 4 := by
    rw [Real.log_mul h_C2_pos.ne' h_4pow_pos.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h_KY_ge_log : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) ≤ K * Y := by
    rw [h_log_lhs, hK_def]
    push_cast
    -- Want: 2 log C + (4L+1) Y log 4 ≤ (2 log C + (4L+1) log 4 + 1) * Y.
    nlinarith [hlogC_nn, hY_R, hlog4_pos, hL_pos_R,
      mul_nonneg hlogC_nn (by linarith : (0:ℝ) ≤ (Y:ℝ) - 1)]
  -- Combine.
  calc (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ)
      ≤ (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := h_n_le_R
    _ ≤ C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := h_total
    _ = Real.exp (Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y))) :=
        (Real.exp_log h_lhs_pos).symm
    _ ≤ Real.exp (K * Y) := Real.exp_le_exp.mpr h_KY_ge_log

/-- **Auxiliary height theorem — analytic combination of Mertens + a Linnik
hypothesis.**

This theorem is the height-form version of the lower-bound construction. It
takes a Linnik-style prime-existence hypothesis as an *explicit argument* (so
the closed theorem itself does not depend on the global `linnik_dvd` axiom —
that axiom enters only at `totient_collision_construction` below, where this
theorem is instantiated).

Concretely: given absolute constants `C, L ≥ 1` and a Linnik-form input
(existence of a prime `ℓ` with `M ∣ ℓ - 1` and polynomial bound `ℓ ≤ C · M^L`
for every `M ≥ 1`), there exists `K > 0` such that for every sufficiently large
`Y`, the explicit construction `a := ℓ · Q_Y(U)`, `b := P_Y · U · Q_Y(U)` (with
`U := (ℓ - 1) / A_Y` and `ℓ` the Linnik prime for `M = A_Y · P_Y`) yields a
totient collision with the right ratio and `n ≤ exp(K · Y)`.

The proof packages the analytic combination (Mertens product asymptotic on
`(P_Y / A_Y) · ((ℓ-1)/ℓ)`, plus the size bound `A_Y ≤ 4^Y` and
`ℓ ≤ C · (A_Y P_Y)^L ≤ C · 16^(LY)`) into a single height-level statement,
leaving the rescaling to `x` to be done in pure Lean below.

Trust boundary: depends on `mertens_product` only (the Linnik input is taken
as an explicit hypothesis rather than from the global axiom). -/
theorem collision_at_height :
    ∀ (C : ℝ) (L : ℕ), 1 ≤ C → 1 ≤ L →
      (∀ M : ℕ, 1 ≤ M →
        ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L) →
      ∀ ε : ℝ, 0 < ε →
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ Y : ℕ in atTop,
            ∃ a b n : ℕ,
              1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
              Nat.totient a = n ∧ Nat.totient b = n ∧
              (b : ℝ) / a ≥
                (Real.exp Real.eulerMascheroniConstant - ε) * Real.log Y ∧
              (n : ℝ) ≤ Real.exp (K * Y) := by
  intro C L hC hL hLinnik ε hε
  classical
  -- Set K := 2 log C + (4L+1) log 4 + 1.
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hK_pos : 0 < K := by
    have h2 : 0 < (4 * (L : ℝ) + 1) * Real.log 4 :=
      mul_pos (by linarith) hlog4_pos
    linarith
  refine ⟨K, hK_pos, ?_⟩
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  -- Helper: build the collision triple with size bound.
  -- The construction is the same in both cases; only the ratio bound differs.
  -- For each Y ≥ 1, given the Linnik input, we extract (ℓ, U) and pack the triple.
  -- We prove the conclusion in two cases on γc vs ε.
  by_cases hcase : γc ≤ ε
  · -- Easy case: (γc - ε) log Y ≤ 0, any nonneg ratio works.
    filter_upwards [Filter.eventually_ge_atTop 1] with Y hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]; exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]; exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- ratio nonneg ≥ (γc - ε) log Y (which is ≤ 0).
      have hℓQ_pos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      have hℓQR_pos : (0 : ℝ) < ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast hℓQ_pos
      have hPUQR_nn : (0 : ℝ) ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast Nat.zero_le _
      have h_ratio_nn :
          0 ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
              ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        div_nonneg hPUQR_nn hℓQR_pos.le
      have hYR_nn : (0 : ℝ) ≤ Real.log (Y : ℝ) := by
        have : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
        exact Real.log_nonneg this
      have h_rhs_nonpos : (γc - ε) * Real.log (Y : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hYR_nn
      linarith
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1
  · -- Main case: γc > ε. Use Mertens to get the ratio bound.
    push_neg at hcase
    have hγc_eps_pos : 0 < γc - ε := by linarith
    have hε2_pos : 0 < ε / 2 := by linarith
    have hγc_eps2_pos : 0 < γc - ε / 2 := by linarith
    -- From Mertens: primeEulerProdNat Y ≥ (γc - ε/2) log Y eventually.
    -- Strategy: ratio (ppN / γc·logY) → 1, so eventually ratio ≥ (γc - ε/2) / γc.
    have h_thresh1_lt : (γc - ε / 2) / γc < 1 := by
      rw [div_lt_one hγc_pos]; linarith
    have h_mertens_ge :
        ∀ᶠ Y : ℕ in atTop,
          (γc - ε / 2) / γc ≤
            (primeEulerProdNat Y) /
              (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
      -- ratio → 1 > (γc - ε/2) / γc, so eventually ratio ≥ (γc - ε/2)/γc.
      have h_lt : (γc - ε / 2) / γc < 1 := h_thresh1_lt
      exact mertens_product_nat.eventually_const_le h_lt
    have h_logY_pos : ∀ᶠ Y : ℕ in atTop, 0 < Real.log (Y : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with Y hY2
      have : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast hY2
      exact Real.log_pos this
    have h_prime_ge : ∀ᶠ Y : ℕ in atTop,
        (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
      filter_upwards [h_mertens_ge, h_logY_pos] with Y hmer hlogY
      have hγc_logY_pos : 0 < γc * Real.log (Y : ℝ) := mul_pos hγc_pos hlogY
      -- hmer: (γc - ε/2)/γc ≤ ppN/(γc·logY).
      -- Multiply both sides by γc·logY > 0.
      have h1 := mul_le_mul_of_nonneg_right hmer hγc_logY_pos.le
      have h_lhs_eq : (γc - ε / 2) / γc * (γc * Real.log (Y : ℝ)) =
          (γc - ε / 2) * Real.log (Y : ℝ) := by
        field_simp
      have h_rhs_eq :
          primeEulerProdNat Y / (γc * Real.log (Y : ℝ)) *
            (γc * Real.log (Y : ℝ)) = primeEulerProdNat Y := by
        field_simp
      -- combine
      have : (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
        rw [← h_lhs_eq, ← h_rhs_eq]
        exact h1
      exact this
    -- Now bound (ℓ-1)/ℓ ≥ rat := (γc - ε)/(γc - ε/2). For this we need ℓ ≥ M₀.
    set rat : ℝ := (γc - ε) / (γc - ε / 2) with hrat_def
    have hrat_lt_one : rat < 1 := by
      rw [hrat_def, div_lt_one hγc_eps2_pos]; linarith
    have hrat_pos : 0 < rat := div_pos hγc_eps_pos hγc_eps2_pos
    have h1mr_pos : 0 < 1 - rat := by linarith
    set M₀ : ℕ := ⌈(1 - rat)⁻¹⌉₊ + 1 with hM₀_def
    -- For ℓ ≥ M₀, (ℓ-1)/ℓ ≥ rat.
    have h_ratio_bound : ∀ ℓ : ℕ, M₀ ≤ ℓ →
        rat ≤ ((ℓ - 1 : ℕ) : ℝ) / (ℓ : ℝ) := by
      intro ℓ hℓM₀
      have hℓ_pos : 0 < ℓ := by
        rw [hM₀_def] at hℓM₀
        omega
      have hℓ_one : 1 ≤ ℓ := hℓ_pos
      have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]; push_cast; ring
      rw [hℓm1_cast, le_div_iff₀ hℓR_pos]
      -- Want rat * ℓ ≤ ℓ - 1, i.e., (1 - rat) * ℓ ≥ 1.
      have h_ge_inv : (1 - rat)⁻¹ ≤ (ℓ : ℝ) := by
        have h1 : ((⌈(1 - rat)⁻¹⌉₊ : ℕ) : ℝ) ≤ (ℓ : ℝ) := by
          have : ⌈(1 - rat)⁻¹⌉₊ ≤ ℓ := by rw [hM₀_def] at hℓM₀; omega
          exact_mod_cast this
        exact (Nat.le_ceil _).trans h1
      have h_one_le : 1 ≤ (1 - rat) * (ℓ : ℝ) := by
        have h1 : (1 - rat)⁻¹ * (1 - rat) = 1 := inv_mul_cancel₀ h1mr_pos.ne'
        have h2 : (1 - rat)⁻¹ * (1 - rat) ≤ (ℓ : ℝ) * (1 - rat) :=
          mul_le_mul_of_nonneg_right h_ge_inv h1mr_pos.le
        rw [h1] at h2
        linarith
      linarith
    -- For Y large, the Linnik prime ℓ ≥ A·P + 1 ≥ P + 1 ≥ M₀.
    -- Since P Y → ∞, we get P Y ≥ M₀ eventually.
    have h_P_ge_M₀ : ∀ᶠ Y : ℕ in atTop, M₀ ≤ LowerConstruction.P Y :=
      lc_P_atTop.eventually_ge_atTop M₀
    -- Combine all eventual conditions.
    filter_upwards [h_prime_ge, h_logY_pos, h_P_ge_M₀, Filter.eventually_ge_atTop 1]
      with Y hPrime hLogY hPM₀ hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    -- ℓ ≥ A·P + 1: from A·P ∣ ℓ - 1 and ℓ - 1 ≥ 1.
    have hAP_dvd_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ ℓ - 1 := hℓ_dvd
    have hℓm1_pos : 1 ≤ ℓ - 1 := by omega
    have hAP_le_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ≤ ℓ - 1 :=
      Nat.le_of_dvd (by omega) hAP_dvd_lm1
    have hP_le_lm1 : LowerConstruction.P Y ≤ ℓ - 1 := by
      have h1 : LowerConstruction.P Y ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
        Nat.le_mul_of_pos_left _ hA_pos
      linarith
    have hM₀_le_ℓ : M₀ ≤ ℓ := by
      have : M₀ ≤ LowerConstruction.P Y := hPM₀
      omega
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]; exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]; exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- The main ratio bound: b/a ≥ (γc - ε) log Y.
      -- b/a = primeEulerProdNat Y · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat = (γc - ε) log Y.
      have h_ratio_eq :
          ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
            ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) =
              primeEulerProdNat Y * ((ℓ - 1 : ℝ) / ℓ) :=
        LowerConstruction.collision_ratio Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
      rw [ge_iff_le, h_ratio_eq]
      -- Cast (ℓ - 1 : ℕ) = (ℓ : ℝ) - 1.
      have hℓ_one : 1 ≤ ℓ := hℓ_prime.one_le
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]; push_cast; ring
      have h_rat_le : rat ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        rw [← hℓm1_cast]
        exact h_ratio_bound ℓ hM₀_le_ℓ
      -- primeEulerProdNat Y ≥ (γc - ε/2) log Y > 0.
      have hPpN_pos : 0 ≤ primeEulerProdNat Y := by
        have h1 : (γc - ε / 2) * Real.log (Y : ℝ) ≥ 0 :=
          mul_nonneg hγc_eps2_pos.le hLogY.le
        linarith [hPrime]
      have h_prod_lb :
          (γc - ε) * Real.log (Y : ℝ) ≤
            ((γc - ε / 2) * Real.log (Y : ℝ)) * rat := by
        -- (γc - ε/2) * rat = γc - ε.
        have h_prod_eq : (γc - ε / 2) * rat = γc - ε := by
          rw [hrat_def, mul_div_assoc']
          rw [mul_div_cancel_left₀ _ hγc_eps2_pos.ne']
        rw [show ((γc - ε / 2) * Real.log (Y : ℝ)) * rat =
            ((γc - ε / 2) * rat) * Real.log (Y : ℝ) by ring]
        rw [h_prod_eq]
      -- Combine: ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat ≥ (γc - ε) log Y.
      have h_ratio_lb :
          (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        -- ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat:
        -- Use: ppN ≥ (γc - ε/2) log Y ≥ 0, (ℓ-1)/ℓ ≥ rat ≥ 0.
        have h1 : 0 ≤ ((γc - ε / 2) * Real.log (Y : ℝ)) := mul_nonneg hγc_eps2_pos.le hLogY.le
        have h2 : 0 ≤ rat := hrat_pos.le
        have h3 : 0 ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
          have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_one
          have h_lm1_nn : 0 ≤ (ℓ : ℝ) - 1 := by linarith
          exact div_nonneg h_lm1_nn hℓR_pos.le
        have h_first : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * rat :=
          mul_le_mul_of_nonneg_right hPrime h2
        have h_second : primeEulerProdNat Y * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_left h_rat_le hPpN_pos
        have : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          le_trans h_first h_second
        rw [show primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) by ring]
        exact this
      -- Goal currently: (γc - ε) * log Y ≤ ppN * ((ℓ - 1) / ℓ).
      -- ((ℓ : ℝ) - 1)/(ℓ : ℝ) is what shows up after the rewrite.
      have h_combined :
          (γc - ε) * Real.log (Y : ℝ) ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
        calc (γc - ε) * Real.log (Y : ℝ)
            ≤ (γc - ε / 2) * Real.log (Y : ℝ) * rat := h_prod_lb
          _ ≤ primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
              have : primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
                  primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by ring
              linarith [this ▸ h_ratio_lb]
      exact h_combined
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1

/-- **Totient-collision construction (Section 2 lower bound).**
Now a *theorem* (was previously a top-level axiom): derived from the
height-form `collision_at_height` together with `linnik_dvd`, by the
substitution `Y(x) := ⌊log x / (2K)⌋` (so that `n ≤ exp(K·Y) ≤ √x ≤ x`, while
`log Y(x) = log log x + O(1)`). -/
theorem totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro ε hε
  -- Extract Linnik constants.
  obtain ⟨C, L, hC, hL, hLinnik⟩ := linnik_dvd
  -- Apply the height-level theorem with halved tolerance ε/2.
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K, hK_pos, hY⟩ := collision_at_height C L hC hL hLinnik (ε / 2) hε2
  -- Substitute Y(x) := ⌊log x / (2K)⌋, x ≥ exp(2K) ensures Y(x) ≥ 1, and
  -- exp(K·Y(x)) ≤ exp(log x / 2) = √x ≤ x.
  -- log Y(x) = log log x - log (2K) + o(1), and (e^γ - ε/2) (log log x - C') ≥
  -- (e^γ - ε) log log x for x large.
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  have h2K_pos : 0 < 2 * K := by linarith
  -- Define the threshold map x ↦ Y(x). To translate `∀ᶠ Y, P Y` over ℕ into
  -- `∀ᶠ x, P (Y(x))`, use that Y(x) → ∞ as x → ∞ (it's monotone in x).
  -- Convert hY (eventually-in-Y) to eventually-in-x via composition.
  rw [Filter.eventually_atTop] at hY
  obtain ⟨Y₀, hY_main⟩ := hY
  -- Pick a base x-threshold large enough.
  -- We need: (a) Y(x) := ⌊log x / (2K)⌋ ≥ Y₀, (b) Y(x) ≥ 1, (c) exp(K·Y(x)) ≤ x,
  -- (d) log Y(x) ≥ 1 (so positive), and (e) the ratio bound (e^γ - ε/2) log Y(x) ≥
  --     (e^γ - ε) log log x. For (e), since log Y(x) ≤ log log x and we want
  --     (e^γ - ε/2) log Y(x) ≥ (e^γ - ε) log log x, equivalent to
  --     (e^γ - ε/2) (log log x - log(2K)) ≥ (e^γ - ε) log log x, i.e.,
  --     (ε/2) log log x ≥ (e^γ - ε/2) log(2K) + ... (eventually true).
  -- Define Yx as a Nat-valued function. Use Nat.floor of a real.
  let Yx : ℕ → ℕ := fun x => ⌊Real.log (x : ℝ) / (2 * K)⌋₊
  -- Step A: Yx tends to atTop.
  have hYx_tendsto : Tendsto Yx atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ) / (2 * K)) atTop atTop := by
      have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact hlog.atTop_div_const h2K_pos
    exact tendsto_nat_floor_atTop.comp h1
  -- Threshold to get Yx ≥ max(Y₀, 1).
  have h_Yx_ge_Y0 : ∀ᶠ x : ℕ in atTop, Y₀ ≤ Yx x := hYx_tendsto.eventually_ge_atTop Y₀
  have h_Yx_ge_1 : ∀ᶠ x : ℕ in atTop, 1 ≤ Yx x := hYx_tendsto.eventually_ge_atTop 1
  -- Compute the basic inequalities relating x and Yx.
  -- Key: for x ≥ 1 with log x ≥ 0, Yx x ≤ log x / (2K), hence 2K · Yx ≤ log x,
  -- so exp(K · Yx) ≤ exp(log x / 2) = √x ≤ x for x ≥ 1.
  have h_exp_K_Yx_le_x : ∀ᶠ x : ℕ in atTop, Real.exp (K * Yx x) ≤ (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx1
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hxR_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_nn : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hxR
    have h_floor_le : (Yx x : ℝ) ≤ Real.log (x : ℝ) / (2 * K) := by
      simpa [Yx] using Nat.floor_le (a := Real.log (x : ℝ) / (2 * K)) (by positivity)
    have h_2K_Yx : (2 * K) * (Yx x : ℝ) ≤ Real.log (x : ℝ) := by
      have := mul_le_mul_of_nonneg_left h_floor_le h2K_pos.le
      have hsimp : (2 * K) * (Real.log (x : ℝ) / (2 * K)) = Real.log (x : ℝ) := by
        field_simp
      linarith [hsimp ▸ this]
    have hK_Yx_le_half : K * (Yx x : ℝ) ≤ Real.log (x : ℝ) / 2 := by
      have h2 : 2 * (K * (Yx x : ℝ)) ≤ Real.log (x : ℝ) := by linarith
      linarith
    have h_exp_le : Real.exp (K * (Yx x : ℝ)) ≤ Real.exp (Real.log (x : ℝ) / 2) :=
      Real.exp_le_exp.mpr hK_Yx_le_half
    have h_sqrt_le : Real.exp (Real.log (x : ℝ) / 2) ≤ (x : ℝ) := by
      -- exp(log x / 2) = sqrt x ≤ x for x ≥ 1.
      have hexp_eq : Real.exp (Real.log (x : ℝ) / 2) =
          Real.exp (Real.log (x : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hexp_eq, Real.exp_log hxR_pos]
      -- x^(1/2) ≤ x for x ≥ 1: x^(1/2) = x^(1/2) and x = x^1, so use Real.rpow_le_rpow_left.
      have h_rpow_le : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hxR
        norm_num
      rw [Real.rpow_one] at h_rpow_le
      exact h_rpow_le
    calc Real.exp (K * (Yx x : ℝ)) ≤ Real.exp (Real.log (x : ℝ) / 2) := h_exp_le
      _ ≤ (x : ℝ) := h_sqrt_le
  -- Step B: For x large enough, log (Yx x) ≥ (1 - ε/(2*(e^γ - ε/2))) * log log x −
  -- (something involving log(2K)). We prove eventually:
  --   (e^γ - ε/2) * log (Yx x) ≥ (e^γ - ε) * log log x.
  -- Strategy: log (Yx x) ≥ log (log x / (2K) - 1) = log log x - log(2K) + o(1)
  -- (eventually), so the LHS is (e^γ - ε/2)(log log x - log(2K) - small).
  -- Difference RHS-LHS = (ε/2) log log x - (e^γ - ε/2)(log(2K) + small).
  -- Eventually positive for log log x → ∞.
  have h_loglog_tendsto : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp h1
  have hlogYx_tendsto : Tendsto (fun x : ℕ => Real.log (Yx x : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => (Yx x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hYx_tendsto
    exact Real.tendsto_log_atTop.comp h1
  -- Need: eventually `(e^γ - ε/2) log (Yx x) ≥ (e^γ - ε) log log x`.
  -- Use: Yx x ≥ log x / (2K) - 1, so log (Yx x) ≥ log (log x / (2K) - 1).
  -- For x large enough (log x ≥ 4K), log x / (2K) - 1 ≥ log x / (4K), so
  -- log (Yx x) ≥ log (log x / (4K)) = log log x - log (4K).
  -- Then (e^γ - ε/2)(log log x - log(4K)) ≥ (e^γ - ε) log log x ⇔
  -- (ε/2) log log x ≥ (e^γ - ε/2) log(4K), eventually true.
  have h_ratio_eventually : ∀ᶠ x : ℕ in atTop,
      (γc - ε / 2) * Real.log (Yx x : ℝ) ≥ (γc - ε) * Real.log (Real.log (x : ℝ)) := by
    -- Strategy:
    -- log (Yx x) ≥ log log x - log (4K)  (eventually, when log x ≥ 8K).
    -- Also log (Yx x) ≤ log log x      (eventually, when Yx x ≤ log x).
    -- We split on the sign of (γc - ε/2):
    --  • If γc - ε/2 ≥ 0: LHS ≥ (γc - ε/2)(log log x - log 4K) ≥ (γc - ε) log log x
    --                     ⇔ (ε/2) log log x ≥ (γc - ε/2) log(4K), true eventually.
    --  • If γc - ε/2 < 0: γc - ε < γc - ε/2 < 0. Use log Yx ≤ log log x:
    --                     LHS = (γc - ε/2) log Yx ≥ (γc - ε/2) log log x ≥ (γc - ε) log log x
    --                     (first ≥ since coefficient is negative; second since γc-ε/2 ≥ γc-ε).
    have h4K_pos : (0 : ℝ) < 4 * K := by linarith
    -- Magnitude bound for the threshold: |γc - ε/2| · |log(4K)| + 1 + γc·γc.
    -- We make log log x larger than (|γc - ε/2| · |log(4K)| + 1) · 2 / ε to ensure the
    -- needed inequality.
    set MUB : ℝ := (|γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) + 1) * 2 / ε + 1
      with hMUB_def
    have h_loglog_ge : ∀ᶠ x : ℕ in atTop, Real.log (Real.log (x : ℝ)) ≥ MUB :=
      h_loglog_tendsto.eventually_ge_atTop _
    have h_logx_ge_8K : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ 8 * K := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    have h_logx_ge_e : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ Real.exp 1 := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    -- For Yx x ≤ log x (eventually): Yx x = ⌊log x / (2K)⌋ ≤ log x / (2K). For 2K ≥ 1, Yx ≤ log x
    -- automatically; for 2K < 1, need log x / (2K) ≤ log x which holds only if 2K ≥ 1. So use
    -- the stronger threshold: pick x large enough that log x / (2K) ≤ log x is moot — we just
    -- want log(Yx x) ≤ log log x. Since Yx x ≤ log x / (2K), have log Yx ≤ log(log x / (2K)) =
    -- log log x - log(2K). If log(2K) ≥ 0 (i.e., 2K ≥ 1), log Yx ≤ log log x. If log(2K) < 0
    -- (i.e., 2K < 1), log Yx ≤ log log x + |log(2K)|.
    -- Cleaner: log (Yx x) ≤ log log x + |log(2K)| (eventually). We use this generic bound.
    have h_logx_ge_2K : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ 2 * K := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    filter_upwards [h_loglog_ge, h_logx_ge_8K, h_logx_ge_e, h_logx_ge_2K, h_Yx_ge_1]
      with x hx_loglog hx_logx hx_logx_e hx_logx_2K hx_Yx1
    -- Compute Yx x ≥ log x / (4K) and Yx x ≤ log x / (2K).
    have h_logx_pos : (0 : ℝ) < Real.log (x : ℝ) := by
      have : Real.exp 1 > 0 := Real.exp_pos _
      linarith
    have h_Yx_pos_R : (0 : ℝ) < (Yx x : ℝ) := by exact_mod_cast hx_Yx1
    have h_floor_lb : (Real.log (x : ℝ) / (2 * K) - 1 : ℝ) ≤ (Yx x : ℝ) := by
      have h := Nat.sub_one_lt_floor (a := Real.log (x : ℝ) / (2 * K))
      simp only [Yx]; linarith
    have h_floor_ub : ((Yx x : ℝ)) ≤ Real.log (x : ℝ) / (2 * K) := by
      simpa [Yx] using Nat.floor_le (a := Real.log (x : ℝ) / (2 * K)) (by positivity)
    -- log x / (2K) ≥ 4, so log x / (2K) - 1 ≥ log x / (4K) ≥ 2.
    have h_logx_div_2K_ge4 : Real.log (x : ℝ) / (2 * K) ≥ 4 := by
      rw [ge_iff_le, le_div_iff₀ h2K_pos]; linarith
    have h_logx_div_4K_pos : (0 : ℝ) < Real.log (x : ℝ) / (4 * K) := by
      positivity
    have h_subtraction_id : Real.log (x : ℝ) / (2 * K) - Real.log (x : ℝ) / (4 * K) =
        Real.log (x : ℝ) / (4 * K) := by field_simp; ring
    have h_logx_div_4K_ge2 : Real.log (x : ℝ) / (4 * K) ≥ 2 := by
      have : Real.log (x : ℝ) / (4 * K) = (Real.log (x : ℝ) / (2 * K)) / 2 := by
        field_simp; ring
      rw [this]; linarith
    have h_lower_lb : (Real.log (x : ℝ) / (4 * K)) ≤ Real.log (x : ℝ) / (2 * K) - 1 := by
      linarith
    have h_Yx_ge_4K : (Yx x : ℝ) ≥ Real.log (x : ℝ) / (4 * K) := by linarith
    -- log (Yx x) ≥ log (log x / (4K)) = log log x - log (4K).
    have h_log_Yx_ge : Real.log (Yx x : ℝ) ≥ Real.log (Real.log (x : ℝ) / (4 * K)) :=
      Real.log_le_log h_logx_div_4K_pos h_Yx_ge_4K
    have h_4K_pos' : (0 : ℝ) < 4 * K := by linarith
    have h_log_div_4K : Real.log (Real.log (x : ℝ) / (4 * K)) =
        Real.log (Real.log (x : ℝ)) - Real.log (4 * K) := by
      rw [Real.log_div h_logx_pos.ne' h_4K_pos'.ne']
    have h_log_Yx_lb : Real.log (Yx x : ℝ) ≥
        Real.log (Real.log (x : ℝ)) - Real.log (4 * K) := by
      rw [← h_log_div_4K]; exact h_log_Yx_ge
    -- log (Yx x) ≤ log (log x / (2K)) = log log x - log(2K).
    have h_logx_div_2K_pos : (0 : ℝ) < Real.log (x : ℝ) / (2 * K) := by positivity
    have h_log_Yx_ub : Real.log (Yx x : ℝ) ≤ Real.log (Real.log (x : ℝ) / (2 * K)) :=
      Real.log_le_log h_Yx_pos_R h_floor_ub
    have h_log_div_2K_id : Real.log (Real.log (x : ℝ) / (2 * K)) =
        Real.log (Real.log (x : ℝ)) - Real.log (2 * K) := by
      rw [Real.log_div h_logx_pos.ne' h2K_pos.ne']
    have h_log_Yx_ub2 : Real.log (Yx x : ℝ) ≤
        Real.log (Real.log (x : ℝ)) - Real.log (2 * K) := by
      rw [← h_log_div_2K_id]; exact h_log_Yx_ub
    -- Set abbreviations.
    set M : ℝ := Real.log (Real.log (x : ℝ)) with hM_def
    set N : ℝ := Real.log (Yx x : ℝ) with hN_def
    -- We have N ≥ M - log(4K) and N ≤ M - log(2K).
    -- Want: (γc - ε/2) N ≥ (γc - ε) M.
    -- Use: N ≥ M - log(4K). Then (γc - ε/2) N ≥ (γc - ε/2)(M - log(4K)) when γc-ε/2 ≥ 0,
    -- i.e., (γc - ε/2) M - (γc - ε/2) log(4K). Want this ≥ (γc - ε) M ⇔
    --   (ε/2) M ≥ (γc - ε/2) log(4K). Holds when M ≥ 2(γc - ε/2) log(4K) / ε, i.e., M ≥ MUB
    --   (chosen large enough).
    -- For γc - ε/2 < 0: use N ≤ M - log(2K) ≤ M + |log(2K)|, so (γc-ε/2) N ≥ (γc-ε/2)(M + |log(2K)|).
    -- Goal: (γc - ε/2) N ≥ (γc - ε) M.
    have h_abs_le : |γc - ε / 2| * |Real.log (4 * K)| ≤
        (|γc - ε / 2| * |Real.log (4 * K)| + 1) := by linarith
    have hMUB_M : M ≥ MUB := hx_loglog
    have h_M_pos : 0 < M := by
      rw [hM_def]; exact Real.log_pos (by linarith [Real.exp_one_gt_d9])
    -- nlinarith handles the bound with the right hints.
    -- Common bookkeeping for both cases:
    -- (γc - ε/2) · log(4K) ≤ |γc - ε/2| · (|log(4K)| + |log(2K)|).
    -- (γc - ε/2) · log(2K) ≤ |γc - ε/2| · (|log(4K)| + |log(2K)|) (for case 2; using
    -- |γc-ε/2|·|log(2K)| ≤ same RHS).
    have h_abs_nn : 0 ≤ |γc - ε / 2| := abs_nonneg _
    have h_abs_log4K : 0 ≤ |Real.log (4 * K)| := abs_nonneg _
    have h_abs_log2K : 0 ≤ |Real.log (2 * K)| := abs_nonneg _
    have h_bd_4K : (γc - ε / 2) * Real.log (4 * K) ≤
        |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
      calc (γc - ε / 2) * Real.log (4 * K)
          ≤ |(γc - ε / 2) * Real.log (4 * K)| := le_abs_self _
        _ = |γc - ε / 2| * |Real.log (4 * K)| := abs_mul _ _
        _ ≤ |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
            apply mul_le_mul_of_nonneg_left _ h_abs_nn
            linarith
    have h_bd_2K : (γc - ε / 2) * Real.log (2 * K) ≤
        |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
      calc (γc - ε / 2) * Real.log (2 * K)
          ≤ |(γc - ε / 2) * Real.log (2 * K)| := le_abs_self _
        _ = |γc - ε / 2| * |Real.log (2 * K)| := abs_mul _ _
        _ ≤ |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
            apply mul_le_mul_of_nonneg_left _ h_abs_nn
            linarith
    -- ε/2 · M ≥ |γc-ε/2| · (|log(4K)| + |log(2K)|) + 1 + ε/2.
    set BoundLog : ℝ := |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|)
      with hBoundLog_def
    have h_BoundLog_nn : 0 ≤ BoundLog := mul_nonneg h_abs_nn (by linarith)
    have h_bd_4K' : (γc - ε / 2) * Real.log (4 * K) ≤ BoundLog := h_bd_4K
    have h_bd_2K' : (γc - ε / 2) * Real.log (2 * K) ≤ BoundLog := h_bd_2K
    have h_eps_M_explicit : ε / 2 * M ≥ BoundLog + 1 + ε / 2 := by
      -- M ≥ MUB = (BoundLog + 1) * 2 / ε + 1.
      -- ⟹ ε/2 · M ≥ ε/2 · ((BoundLog + 1) * 2 / ε + 1) = (BoundLog + 1) + ε/2.
      have h_eps_pos : 0 < ε := hε
      have h_M_lb : M ≥ (BoundLog + 1) * 2 / ε + 1 := hMUB_M
      have hε_M : ε / 2 * M ≥ ε / 2 * ((BoundLog + 1) * 2 / ε + 1) :=
        mul_le_mul_of_nonneg_left h_M_lb (by linarith)
      have h_simp : ε / 2 * ((BoundLog + 1) * 2 / ε + 1) = (BoundLog + 1) + ε / 2 := by
        field_simp
      linarith [h_simp ▸ hε_M]
    by_cases hcoeff : 0 ≤ γc - ε / 2
    · -- Case 1: γc - ε/2 ≥ 0.
      have h_LHS_lb : (γc - ε / 2) * N ≥ (γc - ε / 2) * (M - Real.log (4 * K)) :=
        mul_le_mul_of_nonneg_left h_log_Yx_lb hcoeff
      -- (γc - ε/2)(M - log(4K)) - (γc - ε) M = (ε/2) M - (γc - ε/2) log(4K) ≥ 0.
      have h_arith : (γc - ε / 2) * (M - Real.log (4 * K)) ≥ (γc - ε) * M := by
        have hexpand : (γc - ε / 2) * (M - Real.log (4 * K)) - (γc - ε) * M =
            ε / 2 * M - (γc - ε / 2) * Real.log (4 * K) := by ring
        linarith [hexpand]
      linarith
    · -- Case 2: γc - ε/2 < 0. Use N ≤ M - log(2K), coefficient negative.
      push_neg at hcoeff
      have hcoeff_le : γc - ε / 2 ≤ 0 := le_of_lt hcoeff
      -- (γc - ε/2) N - (γc - ε/2)(M - log(2K)) = (γc - ε/2)(N - M + log(2K))
      -- N ≤ M - log(2K) ⟹ N - M + log(2K) ≤ 0. Multiply by negative: ≥ 0.
      have h_LHS_lb : (γc - ε / 2) * N ≥ (γc - ε / 2) * (M - Real.log (2 * K)) := by
        -- mul_le_mul_of_nonpos_left : c ≤ 0 → a ≤ b → c * b ≤ c * a.
        exact mul_le_mul_of_nonpos_left h_log_Yx_ub2 hcoeff_le
      -- (γc - ε/2)(M - log(2K)) - (γc - ε) M = ε/2 M - (γc - ε/2) log(2K) ≥ 0.
      have h_arith : (γc - ε / 2) * (M - Real.log (2 * K)) ≥ (γc - ε) * M := by
        have hexpand : (γc - ε / 2) * (M - Real.log (2 * K)) - (γc - ε) * M =
            ε / 2 * M - (γc - ε / 2) * Real.log (2 * K) := by ring
        linarith [hexpand]
      linarith
  -- Now combine: the main per-x consequence.
  -- We need: ∃ a b n, [props] ∧ n ≤ x ∧ b/a ≥ (e^γ - ε) log log x.
  filter_upwards [h_Yx_ge_Y0, h_Yx_ge_1, h_exp_K_Yx_le_x, h_ratio_eventually,
    Filter.eventually_ge_atTop 1] with x hxY0 hxYx1 hx_exp hx_ratio _hx1
  obtain ⟨a, b, n, ha, hb, hn, hφa, hφb, hba_height, hn_size⟩ := hY_main (Yx x) hxY0
  refine ⟨a, b, n, ha, hb, hn, ?_, hφa, hφb, ?_⟩
  · -- n ≤ x.
    have hn_le_R : (n : ℝ) ≤ Real.exp (K * Yx x) := hn_size
    have h_le_x_R : (n : ℝ) ≤ (x : ℝ) := le_trans hn_le_R hx_exp
    exact_mod_cast h_le_x_R
  · -- b/a ≥ (γc - ε) log log x.
    calc (b : ℝ) / a ≥ (γc - ε / 2) * Real.log (Yx x : ℝ) := hba_height
      _ ≥ (γc - ε) * Real.log (Real.log (x : ℝ)) := hx_ratio

private lemma R_ge_of_totient_collision {x a b n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n) (hnx : n ≤ x)
    (hφa : Nat.totient a = n) (hφb : Nat.totient b = n) :
    (b : ℝ) / a ≤ R x := by
  -- We show R x ≥ b/a by exhibiting n in the supremum index set.
  -- mmax := sSup {m | φ m = n} ≥ b (since b is in the set and the set is bounded)
  -- mmin := sInf {m | φ m = n} ≤ a (since a is in the set)
  -- so mmax/mmin ≥ b/a.
  set A : Set ℕ := {m | Nat.totient m = n} with hA_def
  have hb_in : b ∈ A := hφb
  have ha_in : a ∈ A := hφa
  have hA_ne : A.Nonempty := ⟨b, hb_in⟩
  -- A is bounded above by 2 n^2 (totient_preimage_bound).
  have hA_bdd : BddAbove A := by
    refine ⟨2 * n ^ 2, ?_⟩
    intro m hm
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · have hm' : Nat.totient m = n := hm
        rw [h0, Nat.totient_zero] at hm'; omega
      · exact hpos
    exact totient_preimage_bound hm_pos hm
  set mmax : ℕ := sSup A with hmmax_def
  set mmin : ℕ := sInf A with hmmin_def
  have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
  have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
  -- b ≤ mmax (since b ∈ A, mmax = sSup A).
  have hb_le_mmax : b ≤ mmax := le_csSup hA_bdd hb_in
  -- mmin ≤ a (since a ∈ A, mmin = sInf A).
  have hmmin_le_a : mmin ≤ a := Nat.sInf_le ha_in
  -- mmin ≥ 1.
  have hmmin_pos : 1 ≤ mmin := by
    rcases Nat.eq_zero_or_pos mmin with h0 | hpos
    · have : Nat.totient mmin = n := hmmin_in
      rw [h0, Nat.totient_zero] at this; omega
    · exact hpos
  have hmmax_pos : 1 ≤ mmax := le_trans hb hb_le_mmax
  -- (mmax : ℝ)/mmin ≥ b/a.
  have ha_pos_R : (0 : ℝ) < a := by exact_mod_cast ha
  have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
  have hb_le_mmax_R : (b : ℝ) ≤ mmax := by exact_mod_cast hb_le_mmax
  have hmmin_le_a_R : (mmin : ℝ) ≤ a := by exact_mod_cast hmmin_le_a
  have hratio_ge : (b : ℝ) / a ≤ (mmax : ℝ) / mmin := by
    -- b/a ≤ mmax/a ≤ mmax/mmin
    have h1 : (b : ℝ) / a ≤ (mmax : ℝ) / a :=
      div_le_div_of_nonneg_right hb_le_mmax_R (le_of_lt ha_pos_R)
    have hmmax_nn : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
    have h2 : (mmax : ℝ) / a ≤ (mmax : ℝ) / mmin :=
      div_le_div_of_nonneg_left hmmax_nn hmmin_pos_R hmmin_le_a_R
    linarith
  -- Now show R x ≥ mmax/mmin by inclusion in the supremum.
  -- n ∈ {n | n ∈ Icc 1 x ∧ ∃ m, φ m = n}
  have hn_in_idx : n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n} := by
    refine ⟨⟨hn, hnx⟩, b, hφb⟩
  -- Boundedness for the outer sup.
  -- The outer family ⨆ (n : ℕ), ⨆ (_ : n ∈ idx_set), (mmax_n : ℝ) / mmin_n is bounded
  -- by 2 * x^2 (since mmax ≤ 2 n² ≤ 2 x², and mmin ≥ 1).
  have hbdd_outer :
      BddAbove (Set.range (fun (n' : ℕ) =>
        ⨆ (_ : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
          let mmax' := sSup {m | Nat.totient m = n'}
          let mmin' := sInf {m | Nat.totient m = n'}
          (mmax' : ℝ) / mmin')) := by
    refine ⟨((2 * x ^ 2 : ℕ) : ℝ), ?_⟩
    rintro _ ⟨n', rfl⟩
    simp only
    by_cases hn'mem : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hn'mem]
      obtain ⟨⟨hn'_pos, hn'_le_x⟩, m_w, hφm_w⟩ := hn'mem
      have hm_w_pos : 1 ≤ m_w := by
        rcases Nat.eq_zero_or_pos m_w with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm_w; omega
        · exact hpos
      set A' : Set ℕ := {m | Nat.totient m = n'} with hA'_def
      have hA'_ne : A'.Nonempty := ⟨m_w, hφm_w⟩
      have hA'_bdd : BddAbove A' := by
        refine ⟨2 * n' ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have : Nat.totient m = n' := hm
            rw [h0, Nat.totient_zero] at this; omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      set mmax' : ℕ := sSup A' with hmmax'_def
      set mmin' : ℕ := sInf A' with hmmin'_def
      have hmmax'_in : mmax' ∈ A' := Nat.sSup_mem hA'_ne hA'_bdd
      have hmmin'_in : mmin' ∈ A' := Nat.sInf_mem hA'_ne
      have hφmmax' : Nat.totient mmax' = n' := hmmax'_in
      have hφmmin' : Nat.totient mmin' = n' := hmmin'_in
      have hmmax'_pos : 1 ≤ mmax' := by
        rcases Nat.eq_zero_or_pos mmax' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax'; omega
        · exact hpos
      have hmmin'_pos : 1 ≤ mmin' := by
        rcases Nat.eq_zero_or_pos mmin' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin'; omega
        · exact hpos
      have hmmax'_le : mmax' ≤ 2 * n' ^ 2 := totient_preimage_bound hmmax'_pos hφmmax'
      have hmmax'_le_2xsq : mmax' ≤ 2 * x ^ 2 := by
        have : 2 * n' ^ 2 ≤ 2 * x ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn'_le_x 2)
        omega
      -- (mmax' : ℝ) / mmin' ≤ mmax' (since mmin' ≥ 1)
      have hmmin'_pos_R : (0 : ℝ) < mmin' := by exact_mod_cast hmmin'_pos
      have hmmax'_nn_R : (0 : ℝ) ≤ mmax' := by exact_mod_cast Nat.zero_le _
      have h1' : (mmax' : ℝ) / mmin' ≤ mmax' := by
        rw [div_le_iff₀ hmmin'_pos_R]
        have : (1 : ℝ) ≤ (mmin' : ℝ) := by exact_mod_cast hmmin'_pos
        nlinarith
      have h2' : (mmax' : ℝ) ≤ ((2 * x ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmmax'_le_2xsq
      linarith
    · rw [ciSup_neg hn'mem]
      simp only [Real.sSup_empty]
      exact_mod_cast Nat.zero_le _
  -- R x ≥ inner term at n.
  have hR_ge : (mmax : ℝ) / mmin ≤ R x := by
    unfold R
    have h_inner_eq :
        (⨆ (_ : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
            let mmax' := sSup {m | Nat.totient m = n}
            let mmin' := sInf {m | Nat.totient m = n}
            (mmax' : ℝ) / mmin') = (mmax : ℝ) / mmin :=
      ciSup_pos hn_in_idx
    rw [← h_inner_eq]
    exact le_ciSup hbdd_outer n
  exact le_trans hratio_ge hR_ge

theorem R_lower_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro ε hε
  filter_upwards [totient_collision_construction ε hε, Filter.eventually_ge_atTop 1]
    with x hx hx1
  obtain ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, hba⟩ := hx
  have hR_ge : (b : ℝ) / a ≤ R x :=
    R_ge_of_totient_collision ha hb hn hnx hφa hφb
  linarith

/-- **Theorem 2.1.** Combined upper and lower bounds give the asymptotic.

Squeeze argument: given `R_upper_bound` and `R_lower_bound` (both `∀ ε > 0, ∀ᶠ x, …`),
choose `ε = δ · e^γ / 2` for target `δ > 0`. Eventually
`(R x - e^γ log log x) / log log x ∈ [-ε, ε]`, so `R x / (e^γ log log x) - 1 ∈
[-δ/2, δ/2]`, giving `dist < δ`. -/
theorem totient_fibre_extremes :
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  set ε : ℝ := δ * γc / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev := (R_upper_bound ε hε_pos).and
    ((R_lower_bound ε hε_pos).and (Filter.eventually_ge_atTop 3))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun x hxN => ?_⟩
  obtain ⟨hxu, hxl, hx3⟩ := hN x hxN
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlogx_gt_one : 1 < Real.log x := by
    have hle : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3R
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    linarith
  have hllogx_pos : 0 < Real.log (Real.log x) := Real.log_pos hlogx_gt_one
  set L : ℝ := Real.log (Real.log x) with hL_def
  have hdenom_pos : 0 < γc * L := mul_pos hγc_pos hllogx_pos
  rw [Real.dist_eq]
  have key : R x / (γc * L) - 1 = (R x - γc * L) / (γc * L) := by
    field_simp
  rw [key, abs_div, abs_of_pos hdenom_pos]
  have hub : R x - γc * L ≤ ε * L := by
    have h1 : (γc + ε) * L = γc * L + ε * L := by ring
    linarith
  have hlb : -(ε * L) ≤ R x - γc * L := by
    have h1 : (γc - ε) * L = γc * L - ε * L := by ring
    linarith
  have habs : |R x - γc * L| ≤ ε * L := abs_le.mpr ⟨hlb, hub⟩
  have hratio : |R x - γc * L| / (γc * L) ≤ ε * L / (γc * L) :=
    div_le_div_of_nonneg_right habs (le_of_lt hdenom_pos)
  have hsimp : ε * L / (γc * L) = ε / γc := by
    field_simp
  rw [hsimp] at hratio
  have hε_over_γc : ε / γc = δ / 2 := by
    rw [hε_def]
    field_simp
  rw [hε_over_γc] at hratio
  have hδ2_lt : δ / 2 < δ := by linarith
  exact lt_of_le_of_lt hratio hδ2_lt

/- ## Section 3 — Permanence observation

This section is **fully proved** — no sorries, no axioms beyond Mathlib.
-/

/-- **Proposition 3.1 (Permanence).** If `φ(a) = φ(b) = n` with `a > b ≥ 1`, then
for every prime `r` coprime to `a*b`, the totient value `N_r := (r - 1) · n` has
both `r·a` and `r·b` as preimages, with ratio `r·a / (r·b) = a/b`.

In particular, since there are infinitely many primes coprime to any given `a*b`,
infinitely many distinct totient values achieve at least the ratio `a/b`. -/
theorem permanence_step (a b r : ℕ)
    (hab : Nat.totient a = Nat.totient b) (hr : Nat.Prime r) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    Nat.totient (r * a) = Nat.totient (r * b) := by
  have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hr).mpr hra
  have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrb
  rw [Nat.totient_mul hcop_a, Nat.totient_mul hcop_b, hab]

/-- **Proposition 3.1 (corollary, faithful to the PDF).**
If `1 ≤ b < a` and `φ(a) = φ(b)`, then there are infinitely many distinct
totient values `N` admitting a pair of preimages `(x, y)` with `y < x` and
`b · x ≥ a · y` (equivalently, `x / y ≥ a / b` in `ℚ` — and hence
`f_max(N) / f_min(N) ≥ a / b` since `f_max(N) ≥ x` and `f_min(N) ≤ y`).

This is the strict form of PDF Proposition 3.1: any nontrivial totient
collision propagates to infinitely many collisions of at least the same ratio. -/
theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}.Infinite := by
  have ha : 1 ≤ a := lt_of_le_of_lt hb hgt |>.le
  -- Strategy: f r := (r - 1) * φ(a) is injective on primes ≥ 2, and for primes r
  -- coprime to a*b, the witnesses x = r*a, y = r*b satisfy (since r ≥ 2 and a > b)
  -- y = r*b < r*a = x and b*x = a*y. {primes not dividing a*b} is infinite.
  set S : Set ℕ := {N | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}
  -- The set of primes coprime to a*b is infinite (primes infinite, divisors finite).
  have h_inf_good : {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}.Infinite := by
    apply Set.Infinite.mono (s := {r | r.Prime} \ {r | r ∣ (a * b)})
    · intro r hr; exact ⟨hr.1, hr.2⟩
    · refine Set.Infinite.diff Nat.infinite_setOf_prime ?_
      exact Set.Finite.subset (Set.finite_Icc 0 (a * b)) (fun r hr =>
        Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_of_dvd (Nat.mul_pos ha hb) hr⟩)
  -- Each such prime maps into S.
  have hmap : ∀ r ∈ {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}, (r - 1) * Nat.totient a ∈ S := by
    rintro r ⟨hpr, hndvd⟩
    have hra : ¬ r ∣ a := fun h => hndvd (h.mul_right b)
    have hrb : ¬ r ∣ b := fun h => hndvd (Dvd.dvd.mul_left h a)
    have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hra
    have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hrb
    have hr2 : 2 ≤ r := hpr.two_le
    have hr_pos : 0 < r := by omega
    refine ⟨r * a, r * b, ?_, ?_, ?_, ?_⟩
    · rw [Nat.totient_mul hcop_a, Nat.totient_prime hpr]
    · rw [Nat.totient_mul hcop_b, Nat.totient_prime hpr, hab]
    · -- y = r*b < r*a = x because b < a and r > 0
      exact (Nat.mul_lt_mul_left hr_pos).mpr hgt
    · -- b * (r * a) = a * (r * b) — exact equality, hence ≥.
      ring_nf
      exact le_refl _
  -- f is injective on primes (since primes ≥ 2 and φ(a) > 0).
  have hφ_pos : 0 < Nat.totient a := Nat.totient_pos.mpr ha
  have hinj : Set.InjOn (fun r : ℕ => (r - 1) * Nat.totient a)
      {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)} := by
    rintro r ⟨hpr, _⟩ s ⟨hps, _⟩ heq
    simp only at heq
    have h2r : 2 ≤ r := hpr.two_le
    have h2s : 2 ≤ s := hps.two_le
    have : r - 1 = s - 1 := Nat.eq_of_mul_eq_mul_right hφ_pos heq
    omega
  exact (h_inf_good.image hinj).mono (Set.image_subset_iff.mpr hmap)

/- Sanity check: verify Proposition 3.1's permanence step relies only on Mathlib axioms,
not our local analytic axioms. Uncomment to inspect:
#print axioms permanence_step
-/


/-- **Asymptotic companion theorem (Section 4).**

PDF Theorem 2.1 in the natural `Tendsto` shape an asymptotic result requires.

Trust boundary: `Erdos694.mertens_product` + `Erdos694.linnik_dvd` plus
Mathlib core. There are no `sorry`s in this file. -/
theorem erdos_694 :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) :=
  totient_fibre_extremes

#print axioms erdos_694
-- 'Erdos694.erdos_694' depends on axioms: [propext, Classical.choice, Erdos694.linnik_dvd, Quot.sound]

end Erdos694
