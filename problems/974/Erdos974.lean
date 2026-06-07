import Mathlib

namespace Erdos974

/-- Data associated with the problem. -/
structure ProblemData (n : ℕ) [NeZero n] where
  /-- The tuple of complex numbers `z` -/
  z : Fin n → ℂ
  /-- The starting indices of the zero runs -/
  (a b : ℤ)
  /-- z 0 = 1 -/
  z0 : z 0 = 1
  /-- The zero runs are distinct -/
  hab : a < b
  /-- A run of `n - 1` zero power sums starts from `a` -/
  sums_a : ∀ k < n - 1, ∑ i, z i ^ (a + k) = 0
  /-- A run of `n - 1` zero power sums starts from `b` -/
  sums_b : ∀ k < n - 1, ∑ i, z i ^ (b + k) = 0

variable {n : ℕ} [NeZero n]

open Finset Matrix Complex Function

lemma zpow_add_int_natCast {z : ℂ} {m : ℤ} {k : ℕ} (hmk : m + (k : ℤ) ≠ 0) :
    z ^ (m + k) = z ^ k * z ^ m := by
  rw [add_comm, zpow_add' (by lia), zpow_natCast]

lemma sum_zpow_ne_zero_exponent {z : Fin n → ℂ} {m : ℤ} {k : ℕ} (hsum : ∑ i, z i ^ (m + k) = 0) :
    m + k ≠ 0 := by
  by_contra h
  simp_all

omit [NeZero n] in
lemma Complex.triangle_eq
    {f : Fin n → ℂ} (hf₁ : ∀ i, ‖f i‖ = 1) (hf₂ : ‖∑ i, f i‖ = n) {i j : Fin n} : f i = f j := by
  contrapose! hf₂
  apply ne_of_lt
  have hij : i ≠ j := by lia
  rw [← sum_add_sum_compl {i, j}, sum_pair hij]
  calc
    _ ≤ ‖f i + f j‖ + ‖∑ k ∈ {i,j}ᶜ, f k‖ := norm_add_le ..
    _ ≤ ‖f i + f j‖ + ∑ k ∈ {i,j}ᶜ, ‖f k‖ := add_le_add_right (norm_sum_le ..) _
    _ = ‖f i + f j‖ + (n - 2) := by
      congr 1
      simp_rw [hf₁, sum_const, nsmul_one, card_compl, Fintype.card_fin]
      rw [card_pair hij, Nat.cast_sub (by lia), Nat.cast_ofNat]
    _ < ‖f i‖ + ‖f j‖ + (n - 2) := by
      refine add_lt_add_left ((norm_add_le ..).lt_of_ne ?_) _
      have n0 (i) : f i ≠ 0 := norm_ne_zero_iff.mp (by simp [hf₁])
      simp_rw [Ne, norm_add_eq_iff, n0, false_or]
      contrapose hf₂
      rw [ext_norm_arg_iff]
      exact ⟨hf₁ j ▸ hf₁ i, hf₂⟩
    _ = _ := by grind

section Esymm

open ComplexConjugate

variable {ι : Type*} [Fintype ι] {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1)

include hz

open scoped Classical in
lemma prod_eq_prod_univ_mul_conj_compl {S : Finset ι} :
    ∏ i ∈ S, z i = (∏ i, z i) * conj (∏ i ∈ Sᶜ, z i) := by
  rw [← prod_mul_prod_compl S, mul_assoc, map_prod, ← prod_mul_distrib]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]

open MvPolynomial in
lemma MvPolynomial.esymm_sub_eq {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (esymm _ _ (Fintype.card ι - k)).eval z =
    (esymm _ _ (Fintype.card ι)).eval z * conj ((esymm _ _ k).eval z) := by
  simp_rw [esymm, map_sum, map_prod, eval_X, sum_mul]
  conv_lhs =>
    enter [2, i]
    rw [prod_eq_prod_univ_mul_conj_compl hz, map_prod]
  conv_rhs =>
    enter [1, 1]
    rw [← card_univ]
  rw [powersetCard_self, sum_singleton, ← mul_sum]
  congr 1
  classical let e : Finset ι ≃ Finset ι := ⟨_, _, compl_compl, compl_compl⟩
  refine sum_equiv e (fun s ↦ ?_) fun s ms ↦ ?_
  · simp_rw [mem_powersetCard_univ, e, Equiv.coe_fn_mk, card_compl]
    grind [s.card_le_univ]
  · simp_rw [e, Equiv.coe_fn_mk]

end Esymm

/-- `n - 1` consecutive zero power sums starting at `m`, combined with `z 0 = 1`,
force `z` to be injective.

**Proof sketch.** Let `S = univ.image z` and `r = #S`. Suppose `r < n` (toward
contradiction). For each `y ∈ S`, define the *compressed weight*
`c(y) := |{i | z i = y}| * y ^ m`. Then
`∑_{y ∈ S} c(y) * y ^ k = ∑_i z_i^{m+k} = 0` for `k = 0, …, n − 2`.
Because `r ≤ n − 1`, the first `r` of these equations (for `k = 0, …, r − 1`) form
a Vandermonde system on the `r` distinct values in `S`.
By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero` (Vandermonde invertibility), `c = 0`.
But `c(1) ≥ 1` since `z 0 = 1`, giving a contradiction. -/
lemma injective_of_power_sums {z : Fin n → ℂ} (hz0 : z 0 = 1) {m : ℤ}
    (hm : ∀ k < n - 1, ∑ i, z i ^ (m + k) = 0) : Injective z := by
  -- Let `S = univ.image z` and `r = #S`. Suppose `r < n` (toward contradiction).
  by_contra h_noninj
  obtain ⟨S, hS_card⟩ : ∃ S : Finset ℂ, #S < n ∧ ∀ i, z i ∈ S := by
    refine ⟨univ.image z, ?_, ?_⟩
    · refine (card_image_le.trans (by simp)).lt_of_ne fun h ↦ h_noninj ?_
      simpa using card_image_iff.mp (by simpa : #(univ.image z) = #univ)
    · simp
  -- For each `k < n - 1`, using `sum_fiberwise_of_maps_to`:
  have h_sum {k} (hk : k < n - 1) : ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = 0 := by
    convert hm k hk using 1; rw [← sum_congr rfl fun x hx ↦ by rw [card_filter]]
    simp only [Nat.cast_sum, sum_mul]
    simp_all [sum_comm]
  -- Choose an equiv `e : Fin r ≃ S` (via `equivFin S` or similar).
  let e : Fin #S ≃ S := Fintype.equivOfCardEq (by simp)
  -- Define `c : Fin r → ℂ` by `c t = #{i | z i = e t} * (e t).1 ^ m`.
  let c (t : Fin #S) := #{i | z i = e t} * (e t).1 ^ m
  have hc {k} (hk : k < #S) : ∑ t, c t * (e t).1 ^ k = 0 := by
    have h_sum_eq :
        ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = ∑ t, #{i | z i = e t} * (e t).1 ^ (m + k) := by
      rw [← sum_coe_sort]
      conv_lhs => rw [← e.sum_comp]
    replace h_sum_eq : ∑ y ∈ S, #{i | z i = y} * y ^ (m + k) = ∑ t, c t * (e t).1 ^ k := by
      convert h_sum_eq using 2
      rw [zpow_add'] <;> norm_num
      · ring
      · by_cases h : m + k = 0 <;> simp [h]
        specialize hm k (by lia)
        simp_all [add_eq_zero_iff_eq_neg]
    exact h_sum_eq ▸ h_sum (hk.trans_le (Nat.le_sub_one_of_lt hS_card.1))
  -- By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero`, `c = 0`.
  have hc_zero : c = 0 :=
    eq_zero_of_forall_pow_sum_mul_pow_eq_zero (fun i j hij ↦ by simpa using hij) fun i ↦ hc i.2
  -- But `1 ∈ S` (since `z 0 = 1`), so for some `t₀`, `e t₀ = 1`.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, (e t₀).1 = 1 :=
    ⟨e.symm ⟨1, hS_card.2 0 |> fun h ↦ by simp_all⟩, by simp⟩
  replace hc_zero := congr_fun hc_zero t₀; simp_all [c, e]

/-- Given `z` injective, `z 0 = 1`, and `n - 1` consecutive zero power sums at `m`,
every `z i` is nonzero.

**Proof sketch.** Suppose `z j = 0` for some `j`. Since `z 0 = 1 ≠ 0`, we have `j ≠ 0`.
By injectivity, `z i ≠ 0` for `i ≠ j`. Since `m + k ≠ 0` for all relevant `k`
(by `sum_zpow_ne_zero_exponent`), `0 ^ (m + k) = 0`, so the zero term drops from each sum:
`∑_{i ≠ j} z_i^{m+k} = 0`.
After reindexing via `Fin.succAbove j`, the remaining `n − 1` nonzero distinct values
satisfy an `(n−1) × (n−1)` Vandermonde system, forcing all weights `z_i^m = 0`.
But `z_0^m = 1 ≠ 0`, contradiction. -/
lemma ne_zero_of_power_sums {z : Fin n → ℂ} (hz0 : z 0 = 1) {m : ℤ}
    (hm : ∀ k < n - 1, ∑ i, z i ^ (m + k) = 0) : ∀ i, z i ≠ 0 := fun i hi ↦ by
  have hInj := injective_of_power_sums hz0 hm
  replace hm {k} (hk : k < n - 1) : ∑ j ∈ univ.erase i, z j ^ m * z j ^ k = 0 := by
    specialize hm k hk
    by_cases hmk : m + k = 0
    · simp_all
    · conv_lhs at hm => enter [2, i]; rw [zpow_add' (by tauto), zpow_natCast]
      rw [sum_erase_eq_sub (mem_univ _), hm, ← zpow_natCast, ← zpow_add' (by tauto), hi,
        _root_.zero_zpow _ hmk, sub_zero]
  have ceq : #(univ.erase i) = n - 1 := by simp
  let g : Fin (n - 1) ↪o Fin n := (univ.erase i).orderEmbOfFin ceq
  replace hm (k : Fin (n - 1)) : ∑ j, z (g j) ^ m * z (g j) ^ k.1 = 0 := by
    specialize hm k.2
    rwa [← map_orderEmbOfFin_univ _ ceq, sum_map] at hm
  replace hm := eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hInj.comp g.injective) hm
  replace hm (j) : z (g j) = 0 := eq_zero_of_zpow_eq_zero congr($hm j)
  rcases n with _ | _ | n
  · exact i.elim0
  · simp [i.fin_one_eq_zero, hz0] at hi
  · specialize hm ⟨0, by lia⟩
    rw [← hi, hInj.eq_iff] at hm
    have : g ⟨0, by lia⟩ ∈ univ.erase i := orderEmbOfFin_mem _ ceq _
    simp [← hm] at this

/-- Two kernel vectors of the `(n−1) × n` Vandermonde submatrix
`(z_i^k)_{k < n-1, i < n}` that agree at position `0` must be equal.

**Proof sketch.** Let `d = v − w`. Then `d 0 = 0` and
`∑_i z_i^k · d_i = 0` for every `k < n − 1`.
Split the sum using `Fin.cons`:
`z_0^k · d_0 + ∑_{j : Fin (n−1)} z_{j+1}^k · d_{j+1} = 0`.
Since `z_0^k · 0 = 0`, this gives
`∑_j (z ∘ Fin.succ) j ^ k · (d ∘ Fin.succ) j = 0` for `k < n − 1`.
The `(n−1) × (n−1)` Vandermonde matrix of `z ∘ Fin.succ` is invertible
(because `z` is injective implies `z ∘ Fin.succ` is injective).
By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero`, `d ∘ Fin.succ = 0`.
Combined with `d 0 = 0`, `d = 0`, so `v = w`. -/
lemma eq_of_vandermonde_ker {z v w : Fin n → ℂ} (hInj : Injective z)
    (hv : ∀ k < n - 1, ∑ i, z i ^ k * v i = 0)
    (hw : ∀ k < n - 1, ∑ i, z i ^ k * w i = 0)
    (h0 : v 0 = w 0) : v = w := by
  rcases n with _ | _ | n
  · exact (NeZero.ne 0 rfl).elim
  · ext i; simp [i.fin_one_eq_zero, h0]
  · simp only [Fin.sum_univ_succ, add_tsub_cancel_right, Order.lt_add_one_iff,
      Fin.succ_zero_eq_one] at hv hw
    let d : Fin (n + 2) → ℂ := v - w
    have hd0 : d 0 = 0 := by simp [d, h0]
    have hd_sum {k} (hk : k ≤ n) : ∑ i, z i ^ k * d i = 0 := by
      specialize hv k hk; specialize hw k hk; simp_all [d, mul_sub, Fin.sum_univ_succ]
    have hd_split {k} (hk : k ≤ n) : ∑ j : Fin (n + 1), z j.succ ^ k * d j.succ = 0 := by
      specialize hd_sum hk; rw [Fin.sum_univ_succ] at hd_sum; simp_all
    have h_inj_succ : (z ∘ Fin.succ).Injective := hInj.comp (Fin.succ_injective _)
    have h_eq_zero (i : Fin (n + 1)) : ∑ j : Fin (n + 1), d j.succ * z j.succ ^ i.1 = 0 := by
      simpa only [mul_comm] using hd_split i.is_le
    have h_d_succ_zero : d ∘ Fin.succ = 0 :=
      eq_zero_of_forall_pow_sum_mul_pow_eq_zero h_inj_succ h_eq_zero
    ext i; exact sub_eq_zero.mp (i.cases hd0 (congr_fun h_d_succ_zero))

namespace ProblemData

variable (PD : ProblemData n)

lemma z_inj : PD.z.Injective :=
  injective_of_power_sums PD.z0 PD.sums_a

lemma z_ne_zero : ∀ i, PD.z i ≠ 0 :=
  ne_zero_of_power_sums PD.z0 PD.sums_a

/-- All elements of `z` raised to this power must give 1. -/
def q : ℕ := (PD.b - PD.a).toNat

lemma q_pos : PD.q ≠ 0 := by grind [q, PD.hab]

/-- Proposition 1 in https://www.erdosproblems.com/forum/thread/974#post-640. -/
lemma z_qth_root (i : Fin n) : PD.z i ^ PD.q = 1 := by
  have hva (k) (hk : k < n - 1) : ∑ i, PD.z i ^ k * PD.z i ^ PD.a = 0 := by
    have h := PD.sums_a k hk
    simpa [zpow_add_int_natCast (sum_zpow_ne_zero_exponent h)] using h
  have hvb (k) (hk : k < n - 1) : ∑ i, PD.z i ^ k * PD.z i ^ PD.b = 0 := by
    have h := PD.sums_b k hk
    simpa [zpow_add_int_natCast (sum_zpow_ne_zero_exponent h)] using h
  have key := eq_of_vandermonde_ker PD.z_inj hva hvb (by simp [PD.z0])
  replace key : PD.z i ^ PD.a = PD.z i ^ PD.b := congr($key i)
  rw [q, ← zpow_natCast, Int.toNat_sub_of_le PD.hab.le,
    zpow_sub₀ (PD.z_ne_zero _), ← key, div_self (zpow_ne_zero _ (PD.z_ne_zero _))]

open scoped Classical in
/-- The least period of the power sum function applied to `PD.z`. -/
noncomputable def p : ℕ :=
  {p ∈ Icc 1 PD.q | (fun k ↦ ∑ i, PD.z i ^ k).Periodic p}.min'
    ⟨PD.q, mem_filter.mpr ⟨by grind [PD.q_pos], by simp [pow_add, PD.z_qth_root]⟩⟩

/-- The least positive index starting a run of `n - 1` zero power sums. -/
noncomputable def c : ℕ :=
  (PD.a % PD.p).toNat

section PProperties

open scoped Classical in
lemma p_mem_filter : PD.p ∈ {p ∈ Icc 1 PD.q | (fun k ↦ ∑ i, PD.z i ^ k).Periodic p} :=
  min'_mem _ _

lemma one_le_p : 1 ≤ PD.p := by
  have := PD.p_mem_filter
  classical rw [mem_filter, mem_Icc] at this
  exact this.1.1

lemma p_le_q : PD.p ≤ PD.q := by
  have := PD.p_mem_filter
  classical rw [mem_filter, mem_Icc] at this
  exact this.1.2

lemma p_pos : 0 < PD.p := Nat.one_le_iff_ne_zero.mp PD.one_le_p |>.bot_lt

/-- The power sum function is periodic with period `p`. -/
lemma p_periodic : (fun k ↦ ∑ i, PD.z i ^ k).Periodic PD.p := by
  have := PD.p_mem_filter
  classical rw [mem_filter] at this
  exact this.2

/-- `p` is minimal among periods in `Icc 1 q`. -/
lemma p_le_of_periodic {d : ℕ} (hd_mem : d ∈ Icc 1 PD.q)
    (hper : (fun k ↦ ∑ i, PD.z i ^ k).Periodic d) : PD.p ≤ d := by
  classical exact min'_le _ _ (mem_filter.mpr ⟨hd_mem, hper⟩)

/-- Each `z_i` is a `p`-th root of unity.

**Proof sketch.** The power sum function satisfies `S(k + p) = S(k)` for all `k`,
i.e. `∑_i z_i^k (z_i^p - 1) = 0` for all `k ∈ ℕ`. In particular for `k = 0, …, n − 1`.
By `eq_zero_of_forall_pow_sum_mul_pow_eq_zero` (Vandermonde invertibility, using injectivity
of `z`), we get `z_i^p - 1 = 0` for all `i`. -/
lemma z_pow_p (i : Fin n) : PD.z i ^ PD.p = 1 := by
  have h_vandermonde (k : Fin n) : ∑ i, PD.z i ^ k.1 * (PD.z i ^ PD.p - 1) = 0 := by
    have := PD.p_periodic k; simp_all [mul_sub, sub_eq_iff_eq_add]
    simpa only [← pow_add] using this
  have h_vandermonde_inv : (fun i ↦ PD.z i ^ PD.p - 1) = 0 := by
    refine eq_zero_of_forall_pow_sum_mul_pow_eq_zero PD.z_inj fun k ↦ ?_
    simpa only [mul_comm] using h_vandermonde k
  exact sub_eq_zero.mp <| congr_fun h_vandermonde_inv i

open Polynomial in
/-- The number of roots is at most `p`: there are only `p` distinct `p`-th roots of unity. -/
lemma n_le_p : n ≤ PD.p := by
  have h_card_le_p : #(univ.image PD.z) ≤ PD.p := by
    -- Tightly related to the definition of `p`,
    -- the `p` elements in `univ.image PD.z` are exactly the `p`-th roots of unity.
    have h_roots : univ.image PD.z ⊆ (X ^ PD.p - 1 : ℂ[X]).roots.toFinset := by
      suffices X ^ PD.p - 1 ≠ (0 : ℂ[X]) by simpa [subset_iff, PD.z_pow_p]
      exact X_pow_sub_C_ne_zero PD.p_pos _
    calc
      _ ≤ _ := card_le_card h_roots
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = _ := natDegree_X_pow_sub_C
  rwa [card_image_of_injective _ PD.z_inj, card_fin] at h_card_le_p

end PProperties

/-- `z_i ^ a = z_i ^ c` (reduction of integer zpow to natural pow modulo `p`).

Since `z_i^p = 1`, we have `z_i^a = z_i^(a mod p)`. And `c = (a mod p).toNat`,
so `z_i^a = z_i^c`. -/
lemma z_zpow_a_eq_pow_c (i : Fin n) : PD.z i ^ PD.a = PD.z i ^ PD.c := by
  rw [← Int.mul_ediv_add_emod PD.a PD.p, zpow_add₀ (PD.z_ne_zero i), _root_.zpow_mul, zpow_natCast,
    z_pow_p, _root_.one_zpow, one_mul]
  have h_mod : PD.a % PD.p = PD.c :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast PD.p_pos.ne'))).symm
  rw [h_mod, zpow_natCast]

/-- The power sum at position `c + k` is zero for `k < n − 1`. -/
lemma sum_pow_c_add_eq_zero {k : ℕ} (hk : k < n - 1) : ∑ i, PD.z i ^ (PD.c + k) = 0 := by
  rw [← PD.sums_a k hk]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [pow_add, ← PD.z_zpow_a_eq_pow_c, zpow_add₀ (PD.z_ne_zero i), zpow_natCast]

/-! ### Bounds on `c` -/

/-- The zero run starts at `c ≥ 1` when `n ≥ 2`. If `c = 0` then `S(c) = S(0) = n ≠ 0`,
contradicting `sum_pow_c_add_eq_zero` at `k = 0`. -/
lemma one_le_c (hn : 2 ≤ n) : 1 ≤ PD.c := by
  have key := PD.sum_pow_c_add_eq_zero (show 0 < n - 1 by lia)
  by_contra! h
  rw [Nat.lt_one_iff] at h
  simp_rw [h, add_zero, pow_zero, sum_const, nsmul_one, card_univ, Fintype.card_fin,
    Nat.cast_eq_zero] at key
  lia

/-- The zero run fits within `[1, p − 1]`: `c + n − 1 ≤ p`, i.e. `c + n ≤ p + 1`.
If `c + k ≥ p` for some `k < n − 1`, then `c + k ≡ 0 (mod p)` would give `S(0) = 0`,
contradicting `S(0) = n ≠ 0`. -/
lemma c_add_n_le_p_add_one (hn : 2 ≤ n) : PD.c + n ≤ PD.p + 1 := by
  contrapose! hn
  obtain ⟨k, hk⟩ : ∃ k ∈ range (n - 1), PD.c + k = PD.p := by
    use PD.p - PD.c
    have h_c_lt_p : PD.c < PD.p :=
      Int.toNat_lt (Int.emod_nonneg _ (mod_cast PD.p_pos.ne')) |>.2
        (Int.emod_lt_of_pos _ (mod_cast PD.p_pos))
    exact ⟨mem_range.mpr (by omega), add_tsub_cancel_of_le h_c_lt_p.le⟩
  have h_sum_zero : ∑ i, PD.z i ^ (PD.c + k) = 0 :=
    PD.sum_pow_c_add_eq_zero (mem_range.mp hk.1)
  simp_all [z_pow_p]

open ComplexConjugate in
/-- The power sum at the reflected position `p − c − j` equals `conj(S(c + j))`.
Since `z_i^p = 1` and `|z_i| = 1`, we have `z_i^(p − c − j) = conj(z_i^(c+j))`,
so `S(p − c − j) = conj(S(c + j)) = 0`.

In terms of an offset from the bottom of the reflected run:
let `m = p + 2 − c − n`. Then `S(m + k) = 0` for `k = 0, …, n − 2`. -/
lemma sum_pow_reflected_eq_zero (hn : 2 ≤ n) {k : ℕ} (hk : k < n - 1) :
    ∑ i, PD.z i ^ (PD.p + 2 - PD.c - n + k) = 0 := by
  have h_conj : ∑ i, PD.z i ^ (PD.p + 2 - PD.c - n + k) =
      ∑ i, (PD.z i)⁻¹ ^ (PD.c + (n - 2 - k)) := by
    refine sum_congr rfl fun i hi ↦ ?_
    have h_exp : PD.p + 2 - PD.c - n + k + (PD.c + (n - 2 - k)) = PD.p := by
      grind [PD.c_add_n_le_p_add_one hn]
    have h_exp : PD.z i ^ PD.p = 1 := PD.z_pow_p i
    rw [inv_pow]
    grind
  have h_inv_conj (i) : (PD.z i)⁻¹ = conj (PD.z i) :=
    inv_eq_conj <| norm_eq_one_of_pow_eq_one (PD.z_pow_p i) PD.p_pos.ne'
  have h_conj_sum :
      ∑ i, (PD.z i)⁻¹ ^ (PD.c + (n - 2 - k)) = conj (∑ i, PD.z i ^ (PD.c + (n - 2 - k))) := by
    simp [h_inv_conj, map_sum]
  have := PD.sum_pow_c_add_eq_zero (show n - 2 - k < n - 1 from by omega); aesop

/-- `z_i ^ c = z_i ^ (p + 2 − c − n)` for all `i`, by Vandermonde kernel uniqueness.

Both `v_i = z_i^c` and `w_i = z_i^(p+2−c−n)` satisfy the Vandermonde kernel
condition `∑_i z_i^k v_i = 0` for `k < n − 1`, and both equal `1` at `i = 0`. -/
lemma z_pow_c_eq_reflected (hn : 2 ≤ n) (i : Fin n) :
    PD.z i ^ PD.c = PD.z i ^ (PD.p + 2 - PD.c - n) := by
  have h_eq : (PD.z · ^ PD.c) = (PD.z · ^ (PD.p + 2 - PD.c - n)) := by
    refine eq_of_vandermonde_ker PD.z_inj (fun k hk ↦ ?_) (fun k hk ↦ ?_) ?_
    · simp_rw [← PD.sum_pow_c_add_eq_zero hk, ← pow_add, add_comm]
    · rw [← PD.sum_pow_reflected_eq_zero hn hk]
      exact sum_congr rfl fun _ _ ↦ by ring
    · rw [PD.z0, one_pow, one_pow]
  exact congr_fun h_eq i

/-- If `n ≠ 1`, `p + 2 = n + 2c`.

**Proof sketch.** By `z_pow_c_eq_reflected`, `z_i^c = z_i^m` where `m = p + 2 − c − n`.
If `c = m`, then `p + 2 = 2c + n` and we're done. Otherwise, `|c − m|` is a positive
integer less than `p`, and `z_i^{|c−m|} = 1` for all `i`. This makes `|c − m|` a period
of the power sum function smaller than `p`, contradicting the minimality of `p`. -/
theorem p_add_two_eq_n_add_two_mul_c (hn : 2 ≤ n) : PD.p + 2 = n + 2 * PD.c := by
  have h_pow_abs (i) : PD.z i ^ (Int.natAbs (PD.c - (PD.p + 2 - PD.c - n))) = 1 := by
    have h_pow_abs : PD.z i ^ (PD.c - (PD.p + 2 - PD.c - n) : ℤ) = 1 := by
      rw [zpow_sub₀ (PD.z_ne_zero i), zpow_natCast, PD.z_pow_c_eq_reflected hn i,
        show (PD.p + 2 - PD.c - n : ℤ) = (PD.p + 2 - PD.c - n : ℕ) by
          grind [PD.c_add_n_le_p_add_one hn], zpow_natCast]
      exact div_self (pow_ne_zero _ (PD.z_ne_zero i))
    obtain ⟨k, ek | ek⟩ := Int.eq_nat_or_neg (PD.c - (PD.p + 2 - PD.c - n)) <;> simp_all
  by_contra h_contra
  have h_period :
      (∑ i, PD.z i ^ ·).Periodic (Int.natAbs (PD.c - (PD.p + 2 - PD.c - n))) := fun k ↦ by
    simp_all [pow_add]
  have h_period_lt_p : Int.natAbs (PD.c - (PD.p + 2 - PD.c - n)) < PD.p := by
    grind [PD.one_le_c hn, PD.c_add_n_le_p_add_one hn]
  have h_period_in_Icc : Int.natAbs (PD.c - (PD.p + 2 - PD.c - n)) ∈ Icc 1 PD.q :=
    mem_Icc.mpr ⟨by lia, by grind [PD.p_le_q]⟩
  exact not_le_of_gt h_period_lt_p (PD.p_le_of_periodic h_period_in_Icc h_period)

lemma odd_iff_odd : Odd n ↔ Odd PD.p := by
  obtain rfl | hn : n = 1 ∨ 2 ≤ n := by grind [‹NeZero n›.ne]
  · suffices PD.p = 1 by lia
    simp_rw [p, min'_eq_iff, mem_filter, mem_Icc]
    exact ⟨⟨⟨le_rfl, by grind [PD.q_pos]⟩, by simp [PD.z0]⟩, fun m bm ↦ bm.1.1⟩
  · grind [PD.p_add_two_eq_n_add_two_mul_c hn]

section Odd

lemma exists_sqrt_of_odd (oddn : Odd n) (i : Fin n) : ∃ v, v ^ PD.p = 1 ∧ v ^ 2 = PD.z i := by
  refine ⟨PD.z i ^ ((PD.p + 1) / 2), ?_, ?_⟩
  · rw [pow_right_comm, z_pow_p, one_pow]
  · rw [← pow_mul, Nat.div_mul_cancel (by grind [PD.odd_iff_odd]), pow_succ, z_pow_p, one_mul]

variable (oddn : Odd n)

/-- The square roots of `PD.z`, only defined when `n` is odd. -/
noncomputable def v (i : Fin n) : ℂ :=
  (PD.exists_sqrt_of_odd oddn i).choose

lemma v_pow_p (i : Fin n) : PD.v oddn i ^ PD.p = 1 :=
  (PD.exists_sqrt_of_odd oddn i).choose_spec.1

lemma v_sq (i : Fin n) : PD.v oddn i ^ 2 = PD.z i :=
  (PD.exists_sqrt_of_odd oddn i).choose_spec.2

lemma norm_v_eq_one (i : Fin n) : ‖PD.v oddn i‖ = 1 :=
  norm_eq_one_of_pow_eq_one (PD.v_pow_p oddn i) PD.p_pos.ne'

lemma v_ne_zero (i : Fin n) : PD.v oddn i ≠ 0 := by
  simp [← norm_ne_zero_iff, norm_v_eq_one]

open ComplexConjugate in
lemma psum_odd_eq_zero {m : ℕ} (hm : Odd m ∧ m < n) :
    (MvPolynomial.psum _ _ m).eval (PD.v oddn) = 0 := by
  obtain rfl | hn : n = 1 ∨ 2 ≤ n := by grind [‹NeZero n›.ne]
  · grind -- m cannot exist in this case
  have key := PD.p_add_two_eq_n_add_two_mul_c hn
  simp_rw [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X]
  apply_fun conj
  simp_rw [map_sum, map_pow, map_zero]
  have mltp : m < PD.p := by grind [PD.n_le_p]
  obtain ⟨k, hk⟩ : Even (PD.p - m) := (Nat.even_sub' mltp.le).mpr (by simp_all [← odd_iff_odd])
  conv_lhs =>
    enter [2, i]
    rw [← inv_eq_conj (PD.norm_v_eq_one oddn i), inv_pow, ← one_mul _⁻¹, ← PD.v_pow_p oddn i,
      ← pow_sub₀ _ (PD.v_ne_zero oddn i) mltp.le, hk, ← two_mul, pow_mul, v_sq]
  have clek : PD.c ≤ k := by lia
  rw [le_iff_exists_add] at clek
  obtain ⟨l, rfl⟩ := clek
  exact PD.sum_pow_c_add_eq_zero (by lia)

lemma esymm_odd_eq_zero {m : ℕ} (hm : Odd m ∧ m < n) :
    (MvPolynomial.esymm _ _ m).eval (PD.v oddn) = 0 := by
  have newton := MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ m
  replace newton := congrArg (MvPolynomial.eval (PD.v oddn)) newton
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at newton
  have key (x) (hx : x ∈ {p ∈ antidiagonal m | p.1 < m}) :
      (-1) ^ x.1 * (MvPolynomial.esymm _ _ x.1).eval (PD.v oddn) *
      (MvPolynomial.psum _ _ x.2).eval (PD.v oddn) = 0 := by
    obtain ⟨i, j⟩ := x
    simp only [mem_filter, mem_antidiagonal, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero,
      one_ne_zero, ne_eq, false_and, false_or] at hx ⊢
    obtain ⟨hm₁, hm₂⟩ := hx
    have odd_or_odd : Odd i ∨ Odd j := by grind
    refine odd_or_odd.imp (fun oi ↦ ?_) fun oj ↦ ?_
    · exact esymm_odd_eq_zero ⟨oi, by lia⟩
    · exact PD.psum_odd_eq_zero oddn ⟨oj, by lia⟩
  rw [sum_eq_zero key, mul_zero, mul_eq_zero, Nat.cast_eq_zero] at newton
  exact newton.resolve_left hm.1.pos.ne'

lemma norm_sum_v_pow_n : ‖∑ i, PD.v oddn i ^ n‖ = n := by
  have newton := MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero (Fin n) ℂ
  replace newton := congrArg (MvPolynomial.eval (PD.v oddn)) newton
  have endsubset : {(0, n), (n, 0)} ⊆ antidiagonal n := fun p hp ↦ by
    rw [mem_antidiagonal]
    rw [mem_insert, mem_singleton] at hp
    cases hp <;> lia
  simp only [Fintype.card_fin, ← sum_sdiff endsubset, map_add, map_sum, map_mul, map_pow,
    map_neg, map_one, map_zero] at newton
  have key (x) (hx : x ∈ antidiagonal n \ {(0, n), (n, 0)}) :
      (-1) ^ x.1 * (MvPolynomial.esymm _ _ x.1).eval (PD.v oddn) *
      (MvPolynomial.psum _ _ x.2).eval (PD.v oddn) = 0 := by
    obtain ⟨i, j⟩ := x
    simp only [mem_sdiff, mem_antidiagonal, mem_insert, Prod.mk.injEq, mem_singleton] at hx ⊢
    obtain hi | hj : Odd i ∧ i < n ∨ Odd j ∧ j < n := by grind
    · simp [PD.esymm_odd_eq_zero _ hi]
    · simp [PD.psum_odd_eq_zero _ hj]
  rw [sum_eq_zero key, zero_add, sum_pair (by simp [oddn.pos.ne])] at newton
  simp only [pow_zero, MvPolynomial.esymm_zero, map_one, mul_one, MvPolynomial.psum, map_sum,
    map_pow, MvPolynomial.eval_X, one_mul, oddn.neg_one_pow, neg_mul, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_natCast, add_neg_eq_zero] at newton
  rw [newton, MvPolynomial.esymm_eq_sum_monomial]
  conv_lhs =>
    enter [1, 1, 2, 1, 1]
    rw [← card_fin n]
  rw [powersetCard_self, sum_singleton, MvPolynomial.eval_monomial]
  simp [norm_v_eq_one]

lemma v_pow_n_eq_one (i : Fin n) : PD.v oddn i ^ n = 1 := by
  rw [Complex.triangle_eq (j := 0) (by simp [PD.norm_v_eq_one]) (norm_sum_v_pow_n PD oddn)]
  have vsq : PD.v oddn 0 ^ 2 = 1 := by rw [PD.v_sq, PD.z0]
  rw [sq_eq_one_iff] at vsq
  obtain h | h := vsq
  · simp_all
  · have vp : PD.v oddn 0 ^ PD.p = 1 := PD.v_pow_p oddn 0
    rw [h, ((odd_iff_odd PD).mp oddn).neg_one_pow] at vp
    norm_cast at vp

include oddn in
lemma z_pow_n_eq_one (i : Fin n) : PD.z i ^ n = 1 := by
  rw [← PD.v_sq oddn, pow_right_comm, v_pow_n_eq_one, one_pow]

end Odd

/-- **Odd case of Erdős Problem 974.** -/
theorem erdos974_odd (oddn : Odd n) : univ.image PD.z = Polynomial.nthRootsFinset n 1 := by
  refine eq_of_subset_of_card_le (fun z mz ↦ ?_) ?_
  · simp_rw [mem_image, mem_univ, true_and] at mz
    obtain ⟨i, rfl⟩ := mz
    rw [Polynomial.mem_nthRootsFinset oddn.pos]
    exact PD.z_pow_n_eq_one oddn i
  · rw [card_image_of_injective _ PD.z_inj, card_fin, Polynomial.nthRootsFinset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots ..)

-- We now prove the even case, and re-type `PD : ProblemData (2 * n)`.
variable (PD : ProblemData (2 * n))

lemma z_pow_half_p (i : Fin (2 * n)) : PD.z i ^ (PD.p / 2) = 1 ∨ PD.z i ^ (PD.p / 2) = -1 := by
  rw [← sq_eq_one_iff, ← pow_mul, Nat.div_mul_cancel (by grind [PD.odd_iff_odd]), PD.z_pow_p]

/-- The indices `i` such that `z_i^(p/2) = 1`. -/
noncomputable def evenIndices : Finset (Fin (2 * n)) :=
  {i | PD.z i ^ (PD.p / 2) = 1}

/-- The indices `i` such that `z_i^(p/2) = -1`. -/
noncomputable def oddIndices : Finset (Fin (2 * n)) :=
  {i | PD.z i ^ (PD.p / 2) = -1}

lemma disjoint_evenIndices_oddIndices : Disjoint PD.evenIndices PD.oddIndices := by
  refine disjoint_left.mpr fun i mi ↦ ?_
  simp only [evenIndices, oddIndices, mem_filter_univ] at mi ⊢
  norm_num [mi]

lemma union_evenIndices_oddIndices : PD.evenIndices ∪ PD.oddIndices = univ := by
  simp_rw [evenIndices, oddIndices, ← filter_or, PD.z_pow_half_p, filter_true]

lemma zero_mem_evenIndices : 0 ∈ PD.evenIndices := by
  simp [evenIndices, PD.z0]

lemma zero_notMem_oddIndices : 0 ∉ PD.oddIndices := by
  apply PD.disjoint_evenIndices_oddIndices.notMem_of_mem_left_finset PD.zero_mem_evenIndices

lemma sum_evenIndices_oddIndices {m : ℕ} (hm : m < n) :
    ∑ i ∈ PD.evenIndices, PD.z i ^ m = ∑ i ∈ PD.oddIndices, PD.z i ^ m := by
  have key := PD.p_add_two_eq_n_add_two_mul_c (by lia)
  have := PD.sum_pow_c_add_eq_zero (show PD.p / 2 + m - PD.c < 2 * n - 1 by lia)
  conv_lhs at this =>
    enter [2, i]
    rw [Nat.add_sub_of_le (by lia), pow_add]
  rw [← PD.union_evenIndices_oddIndices, sum_union PD.disjoint_evenIndices_oddIndices,
    add_eq_zero_iff_eq_neg, ← sum_neg_distrib] at this
  convert this with i mi i mi
  · rw [evenIndices, mem_filter_univ] at mi
    rw [mi, one_mul]
  · rw [oddIndices, mem_filter_univ] at mi
    rw [mi, neg_one_mul, neg_neg]

lemma card_evenIndices_oddIndices : #PD.evenIndices = n ∧ #PD.oddIndices = n := by
  have key := PD.sum_evenIndices_oddIndices ‹NeZero n›.pos
  simp_rw [pow_zero, sum_const, nsmul_one, Nat.cast_inj] at key
  suffices #PD.evenIndices + #PD.oddIndices = 2 * n by lia
  rw [← card_union_of_disjoint PD.disjoint_evenIndices_oddIndices, PD.union_evenIndices_oddIndices,
    card_fin]

/-- A function that reproduces `z` for the `n` even indices. -/
def ze (i : PD.evenIndices) : ℂ := PD.z i.1

/-- A function that reproduces `z` for the `n` odd indices. -/
def zo (i : PD.oddIndices) : ℂ := PD.z i.1

lemma psum_ze_eq_psum_zo {m : ℕ} (hm : m < n) :
    (MvPolynomial.psum _ _ m).eval PD.ze = (MvPolynomial.psum _ _ m).eval PD.zo := by
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X, ze, zo,
    univ_eq_attach, sum_attach _ (PD.z · ^ m)]
  exact PD.sum_evenIndices_oddIndices hm

lemma esymm_ze_eq_esymm_zo {m : ℕ} (hm : m < n) :
    (MvPolynomial.esymm _ _ m).eval PD.ze = (MvPolynomial.esymm _ _ m).eval PD.zo := by
  obtain rfl | posm := m.eq_zero_or_pos
  · simp
  have zen := congrArg (MvPolynomial.eval PD.ze) (MvPolynomial.mul_esymm_eq_sum PD.evenIndices ℂ m)
  have zon := congrArg (MvPolynomial.eval PD.zo) (MvPolynomial.mul_esymm_eq_sum PD.oddIndices ℂ m)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at zen zon
  have key (x) (hx : x ∈ {p ∈ antidiagonal m | p.1 < m}) :
      (-1) ^ x.1 * (MvPolynomial.esymm _ _ x.1).eval PD.ze *
      (MvPolynomial.psum _ _ x.2).eval PD.ze =
      (-1) ^ x.1 * (MvPolynomial.esymm _ _ x.1).eval PD.zo *
      (MvPolynomial.psum _ _ x.2).eval PD.zo := by
    obtain ⟨i, j⟩ := x
    simp only [mem_filter, mem_antidiagonal] at hx ⊢
    obtain ⟨hm₁, hm₂⟩ := hx
    rw [PD.psum_ze_eq_psum_zo (by lia), esymm_ze_eq_esymm_zo (hm₂.trans hm)]
  rwa [sum_congr rfl key, ← zon, mul_right_inj' (by simpa using posm.ne')] at zen

lemma esymm_ze_ne_esymm_zo :
    (MvPolynomial.esymm _ _ n).eval PD.ze ≠ (MvPolynomial.esymm _ _ n).eval PD.zo := by
  by_contra! h
  have prodeven := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.evenIndices
  have prododd := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.oddIndices
  simp_rw [Fintype.card_coe, PD.card_evenIndices_oddIndices] at prodeven prododd
  replace prodeven := congrArg (Polynomial.eval (-1)) prodeven
  replace prododd := congrArg (Polynomial.eval (-1)) prododd
  simp_rw [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    univ_eq_attach] at prodeven prododd
  replace prodeven := congrArg (MvPolynomial.eval PD.ze) prodeven
  replace prododd := congrArg (MvPolynomial.eval PD.zo) prododd
  simp only [map_prod, map_sub, map_neg, map_one, MvPolynomial.eval_X, map_sum, map_mul,
    map_pow, ← sub_eq_neg_add] at prodeven prododd
  have key (m) (hx : m ∈ range (n + 1)) :
      (MvPolynomial.esymm PD.evenIndices ℂ m).eval PD.ze * (-1) ^ (n - m) =
      (MvPolynomial.esymm PD.oddIndices ℂ m).eval PD.zo * (-1) ^ (n - m) := by
    obtain rfl | hm : m = n ∨ m < n := by grind
    · rw [h]
    · rw [PD.esymm_ze_eq_esymm_zo hm]
  rw [sum_congr rfl key, ← prododd] at prodeven
  clear prododd key
  apply absurd prodeven
  let e0 : PD.evenIndices := ⟨0, PD.zero_mem_evenIndices⟩
  have me0 : e0 ∈ PD.evenIndices.attach := by simp
  rw [prod_eq_zero me0 (by simp [e0, ze, PD.z0])]
  refine (prod_ne_zero_iff.mpr fun i _ ↦ ?_).symm
  obtain ⟨i, mi⟩ := i
  simp_rw [zo, sub_ne_zero, ← PD.z0]
  exact PD.z_inj.ne (ne_of_mem_of_not_mem mi PD.zero_notMem_oddIndices)

lemma esymm_zo_eq_zero_of_mem_Ico {m : ℕ} (hm : m ∈ Ico 1 n) :
    (MvPolynomial.esymm _ _ m).eval PD.zo = 0 := by
  rw [mem_Ico] at hm
  have normeven (i) : ‖PD.ze i‖ = 1 := norm_eq_one_of_pow_eq_one (PD.z_pow_p i) PD.p_pos.ne'
  have normodd (i) : ‖PD.zo i‖ = 1 := norm_eq_one_of_pow_eq_one (PD.z_pow_p i) PD.p_pos.ne'
  have eseven :=
    MvPolynomial.esymm_sub_eq normeven (k := m) (by simp [PD.card_evenIndices_oddIndices, hm.2.le])
  have esodd :=
    MvPolynomial.esymm_sub_eq normodd (k := m) (by simp [PD.card_evenIndices_oddIndices, hm.2.le])
  simp only [Fintype.card_coe, PD.card_evenIndices_oddIndices] at eseven esodd
  rw [PD.esymm_ze_eq_esymm_zo (by lia), esodd, PD.esymm_ze_eq_esymm_zo hm.2, ← sub_eq_zero,
    ← sub_mul, mul_eq_zero, sub_eq_zero] at eseven
  simp_rw [PD.esymm_ze_ne_esymm_zo.symm] at eseven
  rwa [false_or, map_eq_zero] at eseven

lemma esymm_ze_eq_zero_of_mem_Ico {m : ℕ} (hm : m ∈ Ico 1 n) :
    (MvPolynomial.esymm _ _ m).eval PD.ze = 0 := by
  rw [← PD.esymm_zo_eq_zero_of_mem_Ico hm]
  exact PD.esymm_ze_eq_esymm_zo (by grind)

lemma esymm_ze_eq : (MvPolynomial.esymm _ _ n).eval PD.ze = -(-1) ^ n := by
  have prodeven := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.evenIndices
  simp_rw [Fintype.card_coe, PD.card_evenIndices_oddIndices] at prodeven
  replace prodeven := congrArg (Polynomial.eval (-1)) prodeven
  simp_rw [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    univ_eq_attach] at prodeven
  replace prodeven := congrArg (MvPolynomial.eval PD.ze) prodeven
  simp only [map_prod, map_add, map_neg, map_one, MvPolynomial.eval_X, map_sum, map_mul,
    map_pow] at prodeven
  have endsubset : {0, n} ⊆ range (n + 1) := by grind
  have key (x) (hx : x ∈ range (n + 1) \ {0, n}) :
      (MvPolynomial.esymm _ _ x).eval PD.ze * (-1) ^ (n - x) = 0 := by
    replace hx : x ∈ Ico 1 n := by grind
    simp [PD.esymm_ze_eq_zero_of_mem_Ico hx]
  rw [← sum_sdiff endsubset, sum_eq_zero key, zero_add, sum_pair ‹NeZero n›.ne',
    MvPolynomial.esymm_zero, map_one, one_mul, tsub_zero, tsub_self, pow_zero, mul_one] at prodeven
  let e0 : PD.evenIndices := ⟨0, PD.zero_mem_evenIndices⟩
  have me0 : e0 ∈ PD.evenIndices.attach := by simp
  rw [prod_eq_zero me0 (by simp [e0, ze, PD.z0])] at prodeven
  rw [eq_neg_iff_add_eq_zero, prodeven, add_comm]

lemma ze_pow_n (i : PD.evenIndices) : PD.ze i ^ n = 1 := by
  have prodeven := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.evenIndices
  simp_rw [Fintype.card_coe, PD.card_evenIndices_oddIndices] at prodeven
  replace prodeven := congrArg (Polynomial.eval (MvPolynomial.C (-PD.ze i))) prodeven
  simp_rw [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    univ_eq_attach] at prodeven
  replace prodeven := congrArg (MvPolynomial.eval PD.ze) prodeven
  simp only [map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, map_sum, map_mul,
    map_pow] at prodeven
  have endsubset : {0, n} ⊆ range (n + 1) := by grind
  have key (x) (hx : x ∈ range (n + 1) \ {0, n}) :
      (MvPolynomial.esymm _ _ x).eval PD.ze * (-PD.ze i) ^ (n - x) = 0 := by
    replace hx : x ∈ Ico 1 n := by grind
    simp [PD.esymm_ze_eq_zero_of_mem_Ico hx]
  rw [← sum_sdiff endsubset, sum_eq_zero key, zero_add, sum_pair ‹NeZero n›.ne',
    MvPolynomial.esymm_zero, map_one, one_mul, tsub_zero, tsub_self, pow_zero, mul_one,
    PD.esymm_ze_eq] at prodeven
  have me0 : i ∈ PD.evenIndices.attach := by simp
  rwa [prod_eq_zero me0 (by simp), eq_comm, add_neg_eq_zero, ← div_eq_one_iff_eq (by simp),
    ← div_pow, neg_div_neg_eq, div_one] at prodeven

theorem image_ze : univ.image PD.ze = Polynomial.nthRootsFinset n 1 := by
  refine eq_of_subset_of_card_le (fun z mz ↦ ?_) ?_
  · simp_rw [mem_image, mem_univ, true_and] at mz
    obtain ⟨i, rfl⟩ := mz
    rw [Polynomial.mem_nthRootsFinset ‹NeZero n›.pos]
    exact PD.ze_pow_n _
  · have ze_inj : Injective PD.ze := fun i j h ↦ by
      unfold ze at h
      rwa [PD.z_inj.eq_iff, SetLike.coe_eq_coe] at h
    rw [card_image_of_injective _ ze_inj, card_univ, Fintype.card_coe,
      PD.card_evenIndices_oddIndices.1, Polynomial.nthRootsFinset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots ..)

lemma esymm_zo_eq : (MvPolynomial.esymm _ _ n).eval PD.zo = ∏ i ∈ PD.oddIndices, PD.z i := by
  have prododd := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.oddIndices
  simp_rw [Fintype.card_coe, PD.card_evenIndices_oddIndices] at prododd
  replace prododd := congrArg (Polynomial.eval 0) prododd
  simp_rw [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    zero_add, univ_eq_attach] at prododd
  replace prododd := congrArg (MvPolynomial.eval PD.zo) prododd
  simp only [map_prod, MvPolynomial.eval_X, map_sum, map_mul, map_pow, map_zero] at prododd
  have endsubset : {0, n} ⊆ range (n + 1) := by grind
  have key (x) (hx : x ∈ range (n + 1) \ {0, n}) :
      (MvPolynomial.esymm _ _ x).eval PD.zo * 0 ^ (n - x) = 0 := by
    replace hx : x ∈ Ico 1 n := by grind
    simp [PD.esymm_zo_eq_zero_of_mem_Ico hx]
  rw [← sum_sdiff endsubset, sum_eq_zero key, zero_add, sum_pair ‹NeZero n›.ne',
    MvPolynomial.esymm_zero, map_one, one_mul, tsub_zero, tsub_self, pow_zero, mul_one,
    zero_pow ‹NeZero n›.ne, zero_add] at prododd
  simp_rw [zo, prod_attach] at prododd
  exact prododd.symm

lemma zo_pow_n (i : PD.oddIndices) : PD.zo i ^ n = -∏ i ∈ PD.oddIndices, -PD.z i := by
  have prododd := MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ PD.oddIndices
  simp_rw [Fintype.card_coe, PD.card_evenIndices_oddIndices] at prododd
  replace prododd := congrArg (Polynomial.eval (MvPolynomial.C (-PD.zo i))) prododd
  simp_rw [Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    univ_eq_attach] at prododd
  replace prododd := congrArg (MvPolynomial.eval PD.zo) prododd
  simp only [map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, map_sum, map_mul,
    map_pow] at prododd
  have endsubset : {0, n} ⊆ range (n + 1) := by grind
  have key (x) (hx : x ∈ range (n + 1) \ {0, n}) :
      (MvPolynomial.esymm _ _ x).eval PD.zo * (-PD.zo i) ^ (n - x) = 0 := by
    replace hx : x ∈ Ico 1 n := by grind
    simp [PD.esymm_zo_eq_zero_of_mem_Ico hx]
  rw [← sum_sdiff endsubset, sum_eq_zero key, zero_add, sum_pair ‹NeZero n›.ne',
    MvPolynomial.esymm_zero, map_one, one_mul, tsub_zero, tsub_self, pow_zero, mul_one,
    PD.esymm_zo_eq] at prododd
  have me0 : i ∈ PD.oddIndices.attach := by simp
  rw [prod_eq_zero me0 (by simp), ← neg_one_mul, mul_pow, ← one_mul (Finset.prod ..)] at prododd
  nth_rw 2 [show (1 : ℂ) = (-1) ^ n * (-1) ^ n by rw [← sq, pow_right_comm]; simp] at prododd
  rw [mul_assoc, ← mul_add, eq_comm, mul_eq_zero] at prododd
  simp_rw [show (-1 : ℂ) ^ n ≠ 0 by simp, false_or, ← eq_neg_iff_add_eq_zero] at prododd
  convert prododd
  conv_lhs =>
    enter [2, i]
    rw [← neg_one_mul]
  rw [prod_mul_distrib, prod_const, PD.card_evenIndices_oddIndices.2]

theorem image_zo :
    univ.image PD.zo = Polynomial.nthRootsFinset n (-∏ i ∈ PD.oddIndices, -PD.z i) := by
  refine eq_of_subset_of_card_le (fun z mz ↦ ?_) ?_
  · simp_rw [mem_image, mem_univ, true_and] at mz
    obtain ⟨i, rfl⟩ := mz
    rw [Polynomial.mem_nthRootsFinset ‹NeZero n›.pos]
    exact PD.zo_pow_n _
  · have zo_inj : Injective PD.zo := fun i j h ↦ by
      unfold zo at h
      rwa [PD.z_inj.eq_iff, SetLike.coe_eq_coe] at h
    rw [card_image_of_injective _ zo_inj, card_univ, Fintype.card_coe,
      PD.card_evenIndices_oddIndices.2, Polynomial.nthRootsFinset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots ..)

/-- **Even case of Erdős Problem 974.** -/
theorem erdos974_even : univ.image PD.z = Polynomial.nthRootsFinset n 1 ∪
    Polynomial.nthRootsFinset n (-∏ i ∈ PD.oddIndices, -PD.z i) := by
  rw [← PD.image_ze, ← PD.image_zo]
  ext z
  simp_rw [mem_union, mem_image, mem_univ, true_and, ze, zo, Subtype.exists, exists_prop,
    ← exists_or, ← or_and_right, ← mem_union, union_evenIndices_oddIndices, mem_univ, true_and]

end ProblemData

/-- **Erdős Problem 974** (Turán's conjecture, proved by Tijdeman 1966).
Given complex `z 0, …, z (n-1)` with `z 0 = 1` and two distinct runs of
`n - 1` consecutive zero power sums (encoded as `PD : ProblemData n`):
* if `n` is odd, the `z i` are exactly the `n`-th roots of unity;
* if `n = 2 m` is even, the `z i` form the union of the `m`-th roots of unity
  and the `m`-th roots of `-∏ i ∈ oddIndices, -z i` — the vertices of two
  regular `m`-gons sharing a circumscribed circle. -/
theorem erdos_974 {n : ℕ} [NeZero n] (PD : ProblemData n) :
    (Odd n → univ.image PD.z = Polynomial.nthRootsFinset n 1) ∧
    (∀ m, [NeZero m] → ∀ (PD' : ProblemData (2 * m)), univ.image PD'.z =
      Polynomial.nthRootsFinset m 1 ∪
      Polynomial.nthRootsFinset m (-∏ i ∈ PD'.oddIndices, -PD'.z i)) :=
  ⟨PD.erdos974_odd, fun _ _ PD' => PD'.erdos974_even⟩

#print axioms erdos_974
-- 'Erdos974.erdos_974' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos974
