import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos391

/-
# Problem Description

Erdős Problem 391. Let `t(n)` be maximal such that there is a representation
`n! = a₁ ⋯ aₙ` with `t(n) = a₁ ≤ ⋯ ≤ aₙ`. Two questions:

1. Is it true that `lim t(n)/n = 1/e`?
2. Is there a constant `c > 0` with `t(n)/n ≤ 1/e - c/log n` for infinitely many `n`?

`erdos_391` answers both affirmatively, as a single conjunction. Both were settled by
Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr and Ventullo. Erdős, Selfridge and Straus
had claimed the matching lower bound for the first, but the proof was lost when Straus died
and was never reconstructed, so it stood only as a conjecture.

`ratio n` is `(t n : ℝ) / n`, where `t n = Nat.findGreatest (Feasible n) n !` and
`Feasible n k` asks for a monotone `a : Fin n → ℕ` with `∏ i, a i = n !` and every `a i ≥ k`.
Since `a` is monotone, bounding every factor below by `k` is the same as bounding the first
one, so this is the `a₁` of the question — `exists_maximizing_representation` records that
the maximizing representation really does have `a ⟨0⟩ = t n`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/IntegralRPow.lean` -/

section
noncomputable section

open Filter MeasureTheory Set

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

theorem integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (Ioi a) :=
  integrableOn_Ioi_rpow_of_lt hr ha

theorem integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ r = -a ^ (r + 1) / (r + 1) :=
  integral_Ioi_rpow_of_lt hr ha

theorem integral_Ioi_rpow_tendsto_aux {a r : ℝ} (hr : r < -1) (ha : 0 < a)
    {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
    Tendsto (fun i ↦ ∫ x in a..b i, x ^ r) l (nhds (-a ^ (r + 1) / (r + 1))) := by
  have hEq :
      (fun i ↦ ∫ x in a..b i, x ^ r) =ᶠ[l]
        fun i ↦ b i ^ (r + 1) / (r + 1) - a ^ (r + 1) / (r + 1) := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_rpow]
    · rw [sub_div]
    · exact Or.inr ⟨hr.ne, Set.notMem_uIcc_of_lt ha (ha.trans_le hi)⟩
  refine Tendsto.congr' hEq.symm ?_
  have hpow : Tendsto (fun i ↦ b i ^ (r + 1)) l (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp hb
  simpa [neg_div] using hpow.div_const (r + 1) |>.sub_const (a ^ (r + 1) / (r + 1))

theorem integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ r)⁻¹) (Ioi a) := by
  refine (integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  change x ^ (-r) = (x ^ r)⁻¹
  rw [Real.rpow_neg (ha.trans hx).le]

theorem integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by
    rw [← Real.rpow_neg (ha.trans hx).le])]
  rw [integral_rpow_Ioi (neg_lt_neg hr) ha]
  rw [show -r + 1 = 1 - r by ring]
  rw [show 1 - r = -(r - 1) by ring, div_neg, neg_div, neg_neg]

theorem integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ n) (Ioi a) := by
  simpa using (integrable_on_rpow_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ n = -a ^ (n + 1) / (n + 1) := by
  exact_mod_cast (integral_rpow_Ioi (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa using (integrable_on_rpow_inv_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) := by
  exact_mod_cast (integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa only [← zpow_natCast] using
    (integrable_on_zpow_inv_Ioi (n := (n : ℤ)) (show 1 < (n : ℤ) by exact_mod_cast hn) ha)

theorem integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) := by
  have h :=
    integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha
  have hexp : 1 - (n : ℝ) = -((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  have hden : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  rw [hexp, hden, Real.rpow_neg ha.le, Real.rpow_natCast] at h
  simpa [Nat.cast_sub hn.le] using h

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/Misc.lean` -/

section
open scoped BigOperators

/-!
This file only reintroduces the pieces of `src/for_mathlib/misc.lean` that are not already
available in Mathlib4 under the same names.

In particular, Mathlib4 already provides results such as:
* `Rat.cast_sum`
* `Finset.filter_comm`
* `Finset.one_le_prod`
* `Real.finsetProd_rpow`
* `Real.self_le_rpow_of_one_le`
* `Real.self_le_rpow_of_le_one`
* the add-one interval lemmas in `Finset` and `Set`
-/

section
open Int

private lemma _root_.Int.Ico_succ_right {a b : ℤ} : Finset.Ico a (b + 1) = Finset.Icc a b := by
  simpa using (Finset.Ico_add_one_right_eq_Icc a b)

private lemma _root_.Int.Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
  simpa [eq_comm] using (Finset.insert_Ioc_right_eq_Ioc_add_one (a := a) (b := b) h)

private lemma _root_.Int.insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
    insert (a + 1) (Finset.Ioc (a + 1) b) = Finset.Ioc a b := by
  simpa using (Finset.insert_Ioc_add_one_left_eq_Ioc (a := a) (b := b) h)

private lemma _root_.Int.Ioc_succ_left {a b : ℤ} (h : a < b) :
    Finset.Ioc (a + 1) b = (Finset.Ioc a b).erase (a + 1) := by
  have hnot : a + 1 ∉ Finset.Ioc (a + 1) b := by simp
  rw [← insert_Ioc_succ_left h, Finset.erase_insert hnot]

private lemma _root_.Int.Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc (a + 1) (b + 1) = (insert (b + 1) (Finset.Ioc a b)).erase (a + 1) := by
  have hab : a < b + 1 := h.trans_lt (lt_add_of_pos_right b zero_lt_one)
  rw [Ioc_succ_left hab, Ioc_succ_right h]

end

section
open Finset

private lemma _root_.Finset.Icc_subset_range_add_one {x y : ℕ} :
    Finset.Icc x y ⊆ Finset.range (y + 1) := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  exact Finset.Icc_subset_Icc_left (b := y) (Nat.zero_le x)

private lemma _root_.Finset.Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Finset.Ico x y ∪ Finset.Icc y z = Finset.Icc x z := by
  rw [← Finset.coe_inj, Finset.coe_union, Finset.coe_Ico, Finset.coe_Icc, Finset.coe_Icc,
    Set.Ico_union_Icc_eq_Icc h₁ h₂]

private lemma _root_.Finset.Icc_sdiff_Icc_right {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Finset.Icc x z \ Finset.Icc y z = Finset.Ico x y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

private lemma _root_.Finset.Icc_sdiff_Icc_left {x y z : ℕ} (h₁ : z ≤ y) (h₂ : x ≤ z) :
    Finset.Icc x y \ Finset.Icc x z = Finset.Ioc z y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

private lemma _root_.Finset.prod_rpow {ι : Type*} {s : Finset ι} {f : ι → ℝ} (c : ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∏ i ∈ s, f i) ^ c = ∏ i ∈ s, (f i ^ c) := by
  simpa [eq_comm] using (Real.finsetProd_rpow s f hf c)

end

@[simp] theorem Ico_inter_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Finset.Ico a b ∩ Finset.Icc b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem Ico_disjoint_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Disjoint (Finset.Ico a b) (Finset.Icc b c) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem range_sdiff_Icc {x y : ℕ} (h : x ≤ y) :
    Finset.range (y + 1) \ Finset.Icc x y = Finset.Ico 0 x := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_sdiff_Icc_right (Nat.zero_le _) h]

theorem Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ici a \ Set.Icc a b = Set.Ioi b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · intro hx
    exact lt_of_not_ge fun hxb => hx.2 ⟨hx.1, hxb⟩
  · intro hbx
    exact ⟨hab.trans hbx.le, fun hx => (not_lt_of_ge hx.2) hbx⟩

theorem Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ioi a \ Set.Ioc a b = Set.Ioi b := by
  rw [Set.Ioi_sdiff_Ioc, max_eq_right hab]

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod (s := s) (f := f) h1)

section
open Real

private lemma _root_.Real.le_rpow_self_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    x ≤ x ^ r :=
  self_le_rpow_of_one_le hx hr

private lemma _root_.Real.le_rpow_self_of {x r : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (h_one_le : r ≤ 1) :
    x ≤ x ^ r :=
  self_le_rpow_of_le_one hx₀ hx₁ h_one_le

end

@[to_additive]
theorem prod_powerset_compl {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Finset α) (f : Finset α → β) :
    (∏ x ∈ s.powerset, f (s \ x)) = ∏ x ∈ s.powerset, f x := by
  refine Finset.prod_bij' (fun x _ ↦ s \ x) (fun x _ ↦ s \ x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    rfl

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/BasicEstimates.lean` -/

section
noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology

/-!
This file contains the Lean 4 statement port of the old Lean 3
`for_mathlib/basic_estimates` file.

When a result already exists upstream in Mathlib 4, this file prefers the
Mathlib version instead of reintroducing a duplicate local theorem.
-/

theorem tendsto_log_coe_at_top : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_coe_at_top : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_coe_at_top

section Summatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ n ≤ x, a n`.
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n

theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]

theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]

end Summatory

section PrimeSummatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ p ≤ x, a p`
where `p` ranges over primes.
-/
def prime_summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ (Finset.Icc k ⌊x⌋₊).filter Nat.Prime, a n

theorem prime_summatory_eq_summatory (a : ℕ → M) :
    prime_summatory a = summatory (fun n => if n.Prime then a n else 0) := by
  ext k x
  simp [prime_summatory, summatory, Finset.sum_filter]

end PrimeSummatory

def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, Int.fract t * (t ^ 2)⁻¹

section
open Nat

private theorem _root_.Nat.cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
  by nlinarith [log_le_sub_one_of_pos hx]

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

scoped[Chebyshev] notation "ϑ" => Erdos391.chebyshev_first
theorem chebyshev_first_pos {x : ℝ} (hx : 2 ≤ x) : 0 < chebyshev_first x :=
  Chebyshev.theta_pos hx

theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (x + 1)]
  congr 1
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, and_assoc]
  constructor
  · rintro ⟨hp1, hp2⟩
    exact ⟨hp2.one_le, hp1, hp2⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp2, hp3⟩

def partial_euler_product (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] theorem partial_euler_product_zero : partial_euler_product 0 = 1 := by
  simp [partial_euler_product]

theorem partial_euler_trivial_lower_bound {n : ℕ} : 1 ≤ partial_euler_product n := by
  refine Finset.one_le_prod ?_
  intro p hp
  simp only [mem_filter] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by nlinarith [inv_nonneg.2 (show 0 ≤ (p : ℝ) by positivity)])

theorem trivial_divisor_bound {n : ℕ} : (ArithmeticFunction.sigma 0 n : ℝ) ≤ n := by
  exact_mod_cast (show ArithmeticFunction.sigma 0 n ≤ n by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Nat.card_divisors_le_self n)

theorem my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n := by
  rw [summatory_eq_floor (a := a) (k := k) x, Nat.floor_eq_on_Ico n x hx]

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

lemma summatory_zero_eq_of_lt {x : ℝ} (hx : x < 1) :
  summatory a 0 x = a 0 := by
  rw [summatory_eq_floor (a := a) (k := 0) x, Nat.floor_eq_zero.mpr hx, summatory_nat]
  simp

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n+1) = a (n + 1) + summatory a k n := by
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by exact_mod_cast rfl]
  rw [summatory_nat, summatory_nat]
  have hIcc : Finset.Icc k (n + 1) = insert (n + 1) (Finset.Icc k n) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert]
  · intro hmem
    exact Nat.not_succ_le_self n (Finset.mem_Icc.mp hmem).2

lemma summatory_succ_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) (k : ℕ) (n : ℕ)
  (hk : k ≤ n + 1) :
  a (n + 1) = summatory a k (n + 1) - summatory a k n := by
  rw [summatory_succ (a := a) k n hk, add_sub_cancel_right]

lemma summatory_eq_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a 1 n - summatory a 1 (n - 1) := by
  intro n hn
  cases n with
  | zero =>
      cases hn rfl
  | succ n =>
      simpa using summatory_succ_sub (a := a) 1 n (by omega)

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

lemma summatory_nonneg' {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] {a : ℕ → M}
    (k : ℕ) (x : ℝ) (ha : ∀ (i : ℕ), k ≤ i → (i : ℝ) ≤ x → 0 ≤ a i)
    (hk : k ≠ 0) :
  0 ≤ summatory a k x := by
  rw [summatory]
  refine Finset.sum_nonneg ?_
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi0 : i ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_iff_ne_zero.mpr hk) hi.1)
  exact ha i hi.1 ((Nat.le_floor_iff' hi0).1 hi.2)

lemma summatory_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] (a : ℕ → M)
    (x : ℝ) (k : ℕ) (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x := by
  rw [summatory]
  exact Finset.sum_nonneg (fun i _ ↦ ha i)

lemma summatory_monotone_of_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (a : ℕ → M)
  (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  Monotone (summatory a k) := by
  intro i j hij
  rw [summatory, summatory]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hij)
  · intro n _ _; exact ha n

lemma abs_summatory_bound {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k z, ‖a i‖ := by
  exact (abs_summatory_le_sum a).trans <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hx))
      (by intro i _ _; exact norm_nonneg _)

@[fun_prop] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor

end SummatoryExtra

section
open ArithmeticFunction

private lemma _root_.ArithmeticFunction.sigma_zero_eq_zeta_mul_zeta :
  ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]

private lemma _root_.ArithmeticFunction.sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  ArithmeticFunction.sigma 0 i = ∑ _ ∈ i.divisors, 1 := by
  rw [ArithmeticFunction.sigma_apply, Finset.sum_congr rfl]
  intro _ _
  simp

end

section
open Finset

private lemma _root_.Finset.Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

private lemma _root_.Finset.prod_eq_prod_iff_of_le' {ι : Type*}
  {s : Finset ι} {f g : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro hf h
    constructor
    · intro _ i hi
      exact False.elim (Finset.notMem_empty i hi)
    · intro _
      simp
  · intro a s ha ih hf h
    constructor
    · intro hprod
      rw [Finset.prod_insert ha, Finset.prod_insert ha] at hprod
      have hs_le : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        Finset.prod_le_prod' (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hs_pos : 0 < ∏ i ∈ s, f i :=
        Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hfa : f a = g a := by
        rcases lt_or_eq_of_le (h a (Finset.mem_insert_self a s)) with hlt | hEq
        · have hlt' : f a * ∏ i ∈ s, f i < g a * ∏ i ∈ s, g i := by
            exact (Nat.mul_lt_mul_of_pos_right hlt hs_pos).trans_le (Nat.mul_le_mul_left _ hs_le)
          exact (False.elim (Nat.lt_irrefl _ (hprod ▸ hlt')))
        · exact hEq
      have hs_eq : ∏ i ∈ s, f i = ∏ i ∈ s, g i := by
        exact Nat.eq_of_mul_eq_mul_left (hf a (Finset.mem_insert_self a s)) (hfa ▸ hprod)
      have hs_all : ∀ i ∈ s, f i = g i :=
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))).1 hs_eq
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hfa
      · exact hs_all i hi
    · intro hall
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [hall a (Finset.mem_insert_self a s)]
      refine congrArg (g a * ·) ?_
      apply (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))).2
      intro i hi
      exact hall i (Finset.mem_insert_of_mem hi)

end

section
open Nat

@[simp] private lemma _root_.Nat.floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

private lemma _root_.Nat.divisors_nonempty_iff {n : ℕ} : n.divisors.Nonempty ↔ n ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty, Nat.divisors_eq_empty]

end

lemma tendsto_log_log_log_coe_at_top :
    Tendsto (fun x : ℕ ↦ log (log (log (x : ℝ)))) atTop atTop := by
  exact tendsto_log_atTop.comp tendsto_log_log_coe_at_top

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Icc x y) := Integrable.smul b hf'
  refine hsmul.integrable.mono ?_ ?_
  · exact measurable_summatory.aestronglyMeasurable.mul hf'.1
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_)
      (norm_nonneg _)
    · exact hz.2.trans (Nat.le_ceil y)
    · rw [Real.norm_eq_abs]
      exact le_abs_self b

theorem partial_summation_nat {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i) (hf' : IntegrableOn f' (Icc k N)) :
  ∑ n ∈ Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
  let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
  have hc_sum :
      ∑ n ∈ Finset.Icc k N, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k N, f n * c n := by
    rw [show Finset.Icc k N = (Finset.Ioc k N).cons k Finset.left_notMem_Ioc by
      simpa using (Finset.Icc_eq_cons_Ioc hN)]
    rw [Finset.sum_cons]
    have htail :
        ∑ n ∈ Finset.Ioc k N, a n * f n =
          ∑ n ∈ Finset.Ioc k N, if k ≤ n then a n * f n else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
      simp [hk]
    simp [c, mul_comm, htail]
  have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) N)] deriv f := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) N)), f' t = deriv f t
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact (hf t ht).deriv.symm
  have hc_abel := sum_mul_eq_sub_sub_integral_mul' (c := c) (f := f) hN
    (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
  have hc_partial : ∀ n, (∑ i ∈ Finset.Icc 0 n, c i) = summatory a k n := by
    intro n
    calc
      ∑ i ∈ Finset.Icc 0 n, c i = ∑ i ∈ Finset.Icc k n, c i := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi ⊢
          exact ⟨Nat.zero_le _, hi.2⟩
        · intro i hi0 hi
          have hi0' := Finset.mem_Icc.mp hi0
          have hki : ¬ k ≤ i := by
            intro hk
            exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
          simp [c, hki]
      _ = ∑ i ∈ Finset.Icc k n, a i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
        simp [c, hk]
      _ = summatory a k n := by rw [← summatory_nat]
  have hcongr :
      ∀ᵐ t ∂volume,
        t ∈ Set.Ioc (k : ℝ) N →
          deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, summatory_eq_floor (a := a) (k := k) t,
      mul_comm]
  have hIocIcc :
      (∫ t in Set.Ioc (k : ℝ) N, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
        ∫ t in Set.Icc (k : ℝ) N, summatory a k t * f' t := by
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
      setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hc_sum, hc_abel, hc_partial, hc_partial, summatory_self, hIocIcc]
  simp [c, mul_comm]
  ring

theorem partial_summation {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one (a := fun n ↦ a n * f n) hk h,
      summatory_eq_of_lt_one (a := a) hk h, zero_mul]
  · have hle : (k : ℝ) ≤ x := le_of_not_gt h
    have hx : k ≤ ⌊x⌋₊ := by rwa [Nat.le_floor_iff' hk]
    let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
    have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) x)] deriv f := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) x)), f' t = deriv f t
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact (hf t ht).deriv.symm
    have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f)
      (show 0 ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k) hle
      (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
    rw [Nat.floor_natCast] at habel
    have hc_partial : ∀ t : ℝ, (∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) = summatory a k t := by
      intro t
      calc
        ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = ∑ i ∈ Finset.Icc k ⌊t⌋₊, c i := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi0 hi
            have hi0' := Finset.mem_Icc.mp hi0
            have hki : ¬ k ≤ i := by
              intro hk
              exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
            simp [c, hki]
        _ = ∑ i ∈ Finset.Icc k ⌊t⌋₊, a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
          simp [c, hk]
        _ = summatory a k t := by rw [summatory]
    have hsum :
        ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k ⌊x⌋₊, f n * c n := by
      rw [show Finset.Icc k ⌊x⌋₊ = (Finset.Ioc k ⌊x⌋₊).cons k Finset.left_notMem_Ioc by
        simpa using (Finset.Icc_eq_cons_Ioc hx)]
      rw [Finset.sum_cons]
      have htail :
          ∑ n ∈ Finset.Ioc k ⌊x⌋₊, a n * f n =
            ∑ n ∈ Finset.Ioc k ⌊x⌋₊, if k ≤ n then a n * f n else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
        simp [hk]
      simp [c, mul_comm, htail]
    have hcongr :
        ∀ᵐ t ∂volume,
          t ∈ Set.Ioc (k : ℝ) x →
            deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, mul_comm]
    have hIocIcc :
        (∫ t in Set.Ioc (k : ℝ) x, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
          ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
        setIntegral_congr_set Ioc_ae_eq_Icc]
    have hc_k : ∑ i ∈ Finset.Icc 0 k, c i = summatory a k k := by
      simpa using hc_partial (k : ℝ)
    rw [summatory, hsum, habel, hc_partial x, hc_k, summatory_self, hIocIcc]
    simp [c, mul_comm]
    ring

theorem partial_summation_cont {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc

theorem partial_summation' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} (hk : k ≠ 0) (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ici k)) {x : ℝ} :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono_set Icc_subset_Ici_self)

theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Icc_subset_Ici_self)

lemma fract_mul_integrable {f : ℝ → ℝ} (s : Set ℝ)
  (hf' : IntegrableOn f s) :
  IntegrableOn (Int.fract * f) s := by
  refine Integrable.mono hf' ?_ (Filter.Eventually.of_forall ?_)
  · exact measurable_fract.aestronglyMeasurable.mul hf'.1
  · intro x
    simp only [norm_mul, Pi.mul_apply, norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

private lemma harmonic_series_aux_identity {x : ℝ} (hx : 1 ≤ x) :
    summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
      (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
        Int.fract x * x⁻¹ := by
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt (fun x ↦ x⁻¹) (-(i ^ 2)⁻¹) i := by
    intro i hi
    exact hasDerivAt_inv (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun i : ℝ ↦ (i ^ 2)⁻¹) (Ici 1) := by
    refine (ContinuousOn.inv₀ (f := fun i : ℝ ↦ i ^ 2) (s := Ici 1)
      (continuous_pow 2).continuousOn ?_)
    · intro i hi
      exact pow_ne_zero 2 (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont.neg) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_floor, sub_mul, Nat.cast_one]
  · have hEqOn :
        EqOn
          (fun a : ℝ ↦ Int.fract a * (a ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 a * -(a ^ 2)⁻¹)
          (fun y : ℝ ↦ y⁻¹) (Ioc 1 x) := by
      intro y hy
      dsimp
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      rw [hs, mul_neg, sub_neg_eq_add, ← add_mul, Int.fract_add_floor]
      have hycalc : y * (y⁻¹ * y⁻¹) = y⁻¹ := by
        field_simp [hy'.ne']
      simpa [sq, mul_inv, mul_assoc] using hycalc
    have hInt0 :
        ∫ t in Ioc 1 x,
            (Int.fract t * (t ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹) = log x := by
      rw [setIntegral_congr_fun measurableSet_Ioc hEqOn, ← intervalIntegral.integral_of_le hx,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    have hfloor : ((⌊x⌋ : ℝ)) = x - Int.fract x := by
      rw [Int.self_sub_fract]
    have hf :
        Integrable (fun t : ℝ ↦ Int.fract t * (t ^ 2)⁻¹) (volume.restrict (Ioc 1 x)) := by
      exact (fract_mul_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)).integrable
    have hgpos :
        Integrable (fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (volume.restrict (Ioc 1 x)) := by
      exact (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)
        |>.mono_set Ioc_subset_Icc_self).integrable
    have hxinv : x * x⁻¹ = (1 : ℝ) := by
      field_simp [(zero_lt_one.trans_le hx).ne']
    have hA : (x - Int.fract x) * x⁻¹ = 1 - Int.fract x * x⁻¹ := by
      rw [sub_mul, hxinv]
    rw [hfloor, hA] at *
    let I : ℝ := ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹
    let K : ℝ := ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹
    have hIK : I + K = log x := by
      calc
        I + K =
            ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ +
              summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹ := by
                symm
                simpa [I, K] using (integral_add hf hgpos)
        _ = log x := by
          simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using hInt0
    have hJneg :
        ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹ = -K := by
      simpa [K, mul_neg] using
        (integral_neg (f := fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (μ := volume.restrict (Ioc 1 x)))
    have hK : K = log x - I := by
      linarith
    rw [hJneg, hK]
    simp [I, sq, hxinv]
    ring_nf

lemma euler_mascheroni_convergence_rate :
  Asymptotics.IsBigOWith 1 atTop
    (fun x : ℝ ↦ 1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨1, ?_⟩
  intro x hx
  have h : IntegrableOn (fun x : ℝ ↦ Int.fract x * (x ^ 2)⁻¹) (Ioi 1) := by
    refine fract_mul_integrable _ ?_
    exact integrable_on_pow_inv_Ioi one_lt_two zero_lt_one
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ← setIntegral_sdiff measurableSet_Ioc h Ioc_subset_Ioi_self,
    Ioi_diff_Icc hx, norm_of_nonneg]
  · refine (setIntegral_mono_on (h.mono_set (Ioi_subset_Ioi hx))
      (integrable_on_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx))
      measurableSet_Ioi ?_).trans ?_
    · intro t ht
      exact mul_le_of_le_one_left (inv_nonneg.2 (sq_nonneg _)) (Int.fract_lt_one _).le
    · rw [integral_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx)]
      norm_num
  · exact
      setIntegral_nonneg measurableSet_Ioi
        (fun t ht ↦ div_nonneg (Int.fract_nonneg _) (sq_nonneg _))

lemma euler_mascheroni_integral_Ioc_convergence :
  Tendsto (fun x : ℝ ↦ 1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  simpa using
    (euler_mascheroni_convergence_rate.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  Tendsto (fun x : ℝ ↦ (1 : ℝ) - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  refine euler_mascheroni_integral_Ioc_convergence.congr' ?_
  change ∀ᶠ x : ℝ in atTop,
    1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ =
      1 - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹
  rw [eventually_atTop]
  exact ⟨1, fun x hx ↦ by rw [intervalIntegral.integral_of_le hx]⟩

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
      Int.fract x * x⁻¹ := by
  simpa using harmonic_series_aux_identity hx

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le

lemma harmonic_series_is_O_with :
  Asymptotics.IsBigOWith 2 atTop
    (fun x ↦ summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  have hfract :
      Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * x⁻¹) (fun x ↦ x⁻¹) :=
    is_O_with_one_fract_mul _
  refine (euler_mascheroni_convergence_rate.sub hfract).congr' ?_ ?_ Filter.EventuallyEq.rfl
  · norm_num
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (harmonic_series_is_O_aux hx).symm

theorem harmonic_series_real_limit :
    Tendsto (fun x ↦ (∑ i ∈ Finset.Icc 1 ⌊x⌋₊, (i : ℝ)⁻¹) - log x) atTop
      (𝓝 euler_mascheroni) := by
  simpa [summatory] using
    (harmonic_series_is_O_with.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

theorem harmonic_series_limit :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, (i : ℝ)⁻¹) - log n) atTop
      (𝓝 euler_mascheroni) := by
  exact (harmonic_series_real_limit.comp tendsto_natCast_atTop_atTop).congr (fun x ↦ by simp)

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, Int.fract t * t⁻¹) - Int.fract x * log x) := by
  rw [intervalIntegral.integral_of_le hx]
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Ici 1) continuousOn_id ?_
    intro x hx
    exact (zero_lt_one.trans_le hx).ne'
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  clear ps
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_fract, sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left,
    sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← add_assoc, sub_add_cancel, Nat.cast_one,
    ← integral_add]
  · have hEqOn :
        EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Ioc 1 x) := by
      intro y hy
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      dsimp
      rw [hs]
      have hyinv : y * y⁻¹ = (1 : ℝ) := by
        field_simp [hy'.ne']
      calc
        (1 : ℝ) = y * y⁻¹ := by simpa using hyinv.symm
        _ = (Int.fract y + (⌊y⌋ : ℝ)) * y⁻¹ := by
          rw [Int.fract_add_floor]
        _ = Int.fract y * y⁻¹ + (⌊y⌋ : ℝ) * y⁻¹ := by ring
    rw [← integral_one, intervalIntegral.integral_of_le hx,
      setIntegral_congr_fun measurableSet_Ioc hEqOn]
  · refine fract_mul_integrable _ ?_
    exact (cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Ioc_subset_Icc_self

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : Filter ℝ) (h : Tendsto f l atTop)
    (c : ℝ) :
  Asymptotics.IsLittleO l (fun _ : ℝ ↦ c) f := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in atTop, ‖c‖ ≤ ε * ‖x‖ := by
    filter_upwards [eventually_ge_atTop (‖c‖ * ε⁻¹), eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂
    rw [norm_of_nonneg hx₂]
    calc
      ‖c‖ = ε * (‖c‖ * ε⁻¹) := by
        field_simp [hε.ne']
      _ ≤ ε * x := mul_le_mul_of_nonneg_left hx₁ hε.le
  exact h.eventually hbound

lemma is_o_one_log (c : ℝ) : Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ c) log := by
  exact is_o_const_of_tendsto_at_top _ _ Real.tendsto_log_atTop _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  Asymptotics.IsBigOWith c atTop
    (fun x ↦ summatory (fun i ↦ log i) 1 x - (x * log x - x))
    (fun x ↦ log x) := by
  have f₁ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * log x) log :=
    is_O_with_one_fract_mul _
  have f₂ : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 : ℝ)) log := is_o_one_log _
  have f₃ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ ∫ t in 1..x, Int.fract t * t⁻¹) log := by
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        change IntegrableOn (Int.fract * fun y : ℝ ↦ y⁻¹) (Icc 1 x)
        exact fract_mul_integrable (s := Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
        intro y hy
        refine mul_le_of_le_one_left (inv_nonneg.2 (zero_le_one.trans hy.1)) (Int.fract_lt_one _).le
      exact intervalIntegral.integral_mono_on (μ := volume) hx hfract h₁ h₂
    · refine intervalIntegral.integral_nonneg hx ?_
      intro y hy
      exact mul_nonneg (Int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1))
  refine (f₂.add_isBigOWith (f₃.sub f₁) ?_).congr' rfl ?_ Filter.EventuallyEq.rfl
  · norm_num [hc]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa using (summatory_log_aux hx).symm

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (fun n ↦ f n * ⌊x / n⌋) 1 y =
    summatory (fun n ↦ ∑ i ∈ n.divisors, f i) 1 x := by
  simp_rw [summatory, ← Nat.cast_floor_eq_cast_int_floor (div_nonneg hy (Nat.cast_nonneg _)),
    ← summatory_const_one, summatory, Finset.mul_sum, mul_one]
  calc
    ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc 1 ⌊x / i⌋₊, f i
      = ∑ i ∈ Finset.Icc 1 ⌊y⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x / i⌋₊).image (fun j => i * j), f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_image ?_
            intro a ha b hb hab
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            exact Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp hi1) hab
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ i ∈ n.divisors, f i := by
          refine Finset.sum_comm'
            (t := fun i : ℕ => (Finset.Icc 1 ⌊x / i⌋₊).image fun j : ℕ => i * j)
            (t' := (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ)) (s' := fun n : ℕ => n.divisors)
            (f := fun i (_n : ℕ) => f i) ?_
          intro i n
          constructor
          · rintro ⟨hi, hn⟩
            rw [Finset.mem_image] at hn
            rcases hn with ⟨j, hj, rfl⟩
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).1
                  ((Finset.mem_Icc.mp hj).2)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := by
              have hmul : (i : ℝ) * j ≤ (i : ℝ) * (x / i) :=
                mul_le_mul_of_nonneg_left hjx (show 0 ≤ (i : ℝ) by positivity)
              have hdiv : (i : ℝ) * (x / i) = x := by
                field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hi1))]
              simpa [Nat.cast_mul, hdiv] using hmul
            have hi_ne : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
            have hj_ne : j ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hj1)
            have hij_ne : i * j ≠ 0 := Nat.mul_ne_zero hi_ne hj_ne
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_divisors]
              exact ⟨dvd_mul_right i j, hij_ne⟩
            · rw [Finset.mem_Icc]
              exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hij_ne),
                (Nat.le_floor_iff hy).2 hxij⟩
          · rintro ⟨hin, hn⟩
            rw [Nat.mem_divisors] at hin
            rcases hin with ⟨⟨j, rfl⟩, hij_ne⟩
            have hi_ne : i ≠ 0 := by
              intro hi0
              exact hij_ne (by simp [hi0])
            have hj_ne : j ≠ 0 := by
              intro hj0
              exact hij_ne (by simp [hj0])
            have hi1 : 1 ≤ i := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hi_ne)
            have hj1 : 1 ≤ j := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hj_ne)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hy).1 (Finset.mem_Icc.mp hn).2
            have hix : (i : ℝ) ≤ x := by
              exact
                le_trans
                  (by
                    exact_mod_cast Nat.le_mul_of_pos_right i
                      (Nat.pos_iff_ne_zero.mpr hj_ne))
                  hxij
            have hiy : (i : ℝ) ≤ y := le_trans hix xy
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (le_div_iff₀ (Nat.cast_pos.2 hi1)).2
                  (by simpa [Nat.cast_mul, mul_comm] using hxij)
            refine ⟨Finset.mem_Icc.mpr ⟨hi1, (Nat.le_floor_iff (hy.trans xy)).2 hiy⟩, ?_⟩
            rw [Finset.mem_image]
            exact ⟨j, Finset.mem_Icc.mpr ⟨hj1,
              (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).2 hjx⟩, rfl⟩

lemma exp_sub_mul {x c : ℝ} {hc : 0 ≤ c} : c - c * log c ≤ exp x - c * x := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp [(Real.exp_pos _).le]
  suffices hmain : Real.exp (Real.log c) - c * Real.log c ≤ Real.exp x - c * x by
    rwa [Real.exp_log hc] at hmain
  have h₁ : Differentiable ℝ (fun x ↦ Real.exp x - c * x) :=
    Real.differentiable_exp.sub (differentiable_id.const_mul _)
  have h₂ : ∀ t, deriv (fun y ↦ Real.exp y - c * y) t = Real.exp t - c := by
    intro t
    change deriv (Real.exp - fun y : ℝ ↦ c * y) t = Real.exp t - c
    simpa using ((Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul c)).deriv
  cases le_total (Real.log c) x with
  | inl hx =>
      have hmono : MonotoneOn (fun y ↦ Real.exp y - c * y) (Icc (Real.log c) x) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (Real.log c) x) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonneg, ← Real.log_le_iff_le_exp hc]
            exact hy.1.le
      exact hmono (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
  | inr hx =>
      have hanti : AntitoneOn (fun y ↦ Real.exp y - c * y) (Icc x (Real.log c)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x (Real.log c)) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonpos, ← Real.le_log_iff_exp_le hc]
            exact hy.2.le
      exact hanti (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx

lemma div_bound_aux1 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ^ K ≤ n) (h2 : 0 < K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) := by
  transitivity (2 : ℝ) ^ (r : ℝ)
  · have hpow : (1 + (1 : ℝ)) ^ r = (2 : ℝ) ^ (r : ℝ) := by
      norm_num
    rw [← hpow, add_comm]
    simpa using (one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num : -2 ≤ (1 : ℝ)) r)
  · have hnonneg : 0 ≤ (2 : ℝ) ^ K := by
      positivity
    refine le_trans ?_ (Real.rpow_le_rpow hnonneg h1 ?_)
    · rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_div_cancel₀ _ h2.ne']
    · exact div_nonneg (Nat.cast_nonneg _) h2.le

lemma bernoulli_aux (x : ℝ) : x + 1 / 2 ≤ 2 ^ x := by
  have h : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have h₁ :
      1 / Real.log 2 - 1 / Real.log 2 * Real.log (1 / Real.log 2) ≤
        Real.exp (Real.log 2 * x) - 1 / Real.log 2 * (Real.log 2 * x) := by
    apply exp_sub_mul
    simp only [one_div, inv_nonneg]
    exact h.le
  rw [Real.rpow_def_of_pos zero_lt_two, ← le_sub_iff_add_le']
  rw [← mul_assoc, div_mul_cancel₀ _ h.ne', one_mul] at h₁
  apply le_trans ?_ h₁
  rw [one_div (Real.log 2), Real.log_inv]
  simp only [one_div, mul_neg, sub_neg_eq_add]
  suffices h2 : Real.log 2 / 2 - 1 ≤ Real.log (Real.log 2) by
    field_simp [h]
    linarith
  transitivity (-1 / 2 : ℝ)
  · linarith [Real.log_two_lt_d9]
  · have hlog : (-1 : ℝ) ≤ 2 * Real.log (Real.log 2) := by
      simpa [Real.log_rpow h] using
        (Real.le_log_iff_exp_le (Real.rpow_pos_of_pos h _)).2 (by
          apply Real.exp_neg_one_lt_d9.le.trans
          apply le_trans _ (Real.rpow_le_rpow (by positivity) Real.log_two_gt_d9.le zero_le_two)
          · rw [Real.rpow_two]
            norm_num)
    nlinarith

lemma div_bound_aux2 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ≤ n) (h2 : 2 ≤ K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) * K := by
  have h4 : ((r : ℝ) + 1) / K ≤ 2 ^ ((r : ℝ) / K) := by
    transitivity (r : ℝ) / K + 1 / 2
    · rw [add_div]
      simp only [one_div, add_le_add_iff_left]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 h2
    · exact bernoulli_aux _
  have hK0 : 0 < K := by
    positivity
  transitivity (2 : ℝ) ^ ((r : ℝ) / K) * K
  · rwa [← div_le_iff₀ hK0]
  · apply mul_le_mul_of_nonneg_right _ hK0.le
    exact Real.rpow_le_rpow (by positivity) h1 (div_nonneg (Nat.cast_nonneg _) hK0.le)

lemma divisor_function_exact_prime_power (r : ℕ) {p : ℕ} (h : p.Prime) :
    ArithmeticFunction.sigma 0 (p ^ r) = r + 1 := by
  simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := r) h

lemma divisor_function_exact {n : ℕ} :
  n ≠ 0 → ArithmeticFunction.sigma 0 n = n.factorization.prod (fun _ k ↦ k + 1) := by
  intro hn
  change ArithmeticFunction.sigma 0 n = n.primeFactors.prod (fun p ↦ n.factorization p + 1)
  simpa [ArithmeticFunction.sigma_zero_apply] using (Nat.card_divisors hn)

lemma divisor_function_div_pow_eq {n : ℕ} (K : ℝ) (hn : n ≠ 0) :
  (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
    n.factorization.prod (fun p k ↦ (k + 1) / ((p : ℝ) ^ ((k : ℝ) / K))) := by
  change
      (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
        n.primeFactors.prod
          (fun p ↦ (n.factorization p + 1) / ((p : ℝ) ^ ((n.factorization p : ℝ) / K)))
  rw [div_eq_mul_inv]
  have hsigma : (ArithmeticFunction.sigma 0 n : ℝ) =
      n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) := by
    exact_mod_cast (divisor_function_exact (n := n) hn)
  rw [hsigma]
  have hpow : (n : ℝ) ^ K⁻¹ =
      n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
    calc
      (n : ℝ) ^ K⁻¹ = (((n.factorization.prod fun p k => p ^ k : ℕ) : ℕ) : ℝ) ^ K⁻¹ := by
        rw [Nat.prod_factorization_pow_eq_self hn]
      _ = (n.primeFactors.prod fun p ↦ ((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹ := by
        simp [Finsupp.prod]
      _ = n.primeFactors.prod (fun p ↦ (((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹) := by
        symm
        exact Real.finsetProd_rpow _ (fun p => ((p : ℕ) : ℝ) ^ (n.factorization p))
          (by intro p hp; positivity) _
      _ = n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
        congr with p
        rw [← Real.rpow_natCast, ← Real.rpow_mul, div_eq_mul_inv]
        positivity
  rw [hpow]
  simpa [div_eq_mul_inv] using (show
    n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) *
        n.primeFactors.prod (fun p ↦ ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) =
      n.primeFactors.prod
        (fun p ↦ (n.factorization p + 1 : ℝ) * ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) by
      rw [← Finset.prod_mul_distrib])

lemma prod_of_subset_le_prod_of_one_le {ι N : Type*} [CommSemiring N] [Preorder N]
    [ZeroLEOneClass N] [PosMulMono N]
    {s t : Finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i)
    (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  exact Finset.prod_le_prod_of_subset_of_one_le h hs hf

lemma anyk_divisor_bound (n : ℕ) {K : ℝ} (hK : 2 ≤ K) :
  (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ) ^ (1 / K) * K ^ ((2 : ℝ) ^ K) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [ArithmeticFunction.sigma_apply, Nat.divisors_zero, Nat.cast_zero, pow_zero]
    rw [zero_rpow]
    · simp
    · simpa [one_div] using inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_two hK))
  rw [show (n : ℝ) ^ (1 / K) = (n : ℝ) ^ K⁻¹ by rw [one_div], mul_comm]
  rw [← div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)]
  rw [divisor_function_div_pow_eq _ hn.ne']
  let s : Finset ℕ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ K)
  have hsubset : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine (Finset.prod_le_prod_of_subset_of_le_one hsubset ?_ ?_).trans ?_
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp hp'
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpbound : (2 : ℝ) ^ K ≤ p := by
      apply le_of_not_gt
      intro hlt
      exact hp' (by simp [s, hp, hlt])
    rw [div_le_iff₀]
    · simpa using div_bound_aux1 (p : ℝ) (n.factorization p) K hpbound (by linarith)
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  refine (Finset.prod_le_prod ?_ ?_).trans ((Finset.prod_const K).trans_le ?_)
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors (hsubset hp)
    rw [div_le_iff₀]
    · simpa [mul_comm] using
        div_bound_aux2 (p : ℝ) (n.factorization p) K
          (by exact_mod_cast hpprime.two_le) hK
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  · rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have hsIcc : s ⊆ Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊ := by
      intro p hp
      have hp' : p ∈ n.primeFactors ∧ (p : ℝ) < (2 : ℝ) ^ K := by
        simpa [s] using hp
      rw [Finset.mem_Icc]
      refine ⟨Nat.pos_of_mem_primeFactors hp'.1, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hp'.2.le
    have hsle : s.card ≤ ⌊((2 : ℝ) ^ K)⌋₊ := by
      calc
        s.card ≤ (Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊).card := Finset.card_le_card hsIcc
        _ = ⌊((2 : ℝ) ^ K)⌋₊ := by
          rw [Nat.card_Icc]
          omega
    exact le_trans (by exact_mod_cast hsle) (Nat.floor_le (by positivity))

lemma log_log_mul_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
  Tendsto (fun x : ℝ ↦ log (log x) * log x / x ^ ε) atTop (𝓝 0) := by
  refine IsLittleO.tendsto_div_nhds_zero ?_
  refine ((isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (isBigO_refl _ _)).trans ?_
  refine ((isLittleO_log_rpow_atTop (half_pos hε)).pow two_pos).congr' ?_ ?_
  · filter_upwards with x using by simp [sq]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_two, ← Real.rpow_mul hx, div_mul_cancel₀ ε two_ne_zero]

lemma divisor_bound₁ {ε : ℝ} (hε1 : 0 < ε) (hε2 : ε ≤ 1) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_coe_at_top
  have hx :
      Tendsto
        (fun n : ℕ =>
          2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3)))
        atTop (𝓝 0) := by
    simpa using
      ((log_log_mul_log_div_rpow (div_pos hε1 zero_lt_three)).comp hl).const_mul 2
  have hε : 0 < Real.log 2 * ε / 2 := by
    exact half_pos (mul_pos (Real.log_pos one_lt_two) hε1)
  filter_upwards
    [tendsto_log_log_coe_at_top (eventually_ge_atTop ((Real.log 2 * (1 + ε / 2))⁻¹)),
      tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ)),
      hl (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_log_coe_at_top (eventually_ge_atTop (2 * Real.log 2 * (1 + ε / 2))),
      h (eventually_gt_atTop (0 : ℝ)),
      hx (Metric.closedBall_mem_nhds 0 hε)] with
    n hlln' hlln hln hlln'' hn hx'
  dsimp at hlln hlln' hln hlln'' hn
  set K : ℝ := log (log (n : ℝ)) / (Real.log 2 * (1 + ε / 2)) with hK
  have hpowK_pos : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos zero_lt_two _
  have hε' : 0 < Real.log 2 * (1 + ε / 2) := by
    exact mul_pos (Real.log_pos one_lt_two) (by linarith)
  have hpowK : (2 : ℝ) ^ K ≤ Real.log n ^ (1 - ε / 3) := by
    refine (Real.log_le_log_iff hpowK_pos (Real.rpow_pos_of_pos hln _)).mp ?_
    rw [Real.log_rpow zero_lt_two,
      Real.log_rpow hln, hK, mul_comm (Real.log 2), ← div_div,
      div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne', div_le_iff₀]
    · have hfactor : 1 ≤ (1 - ε / 3) * (1 + ε / 2) := by
        nlinarith [hε1, hε2]
      have hmain :
          log (log (n : ℝ)) ≤
            ((1 - ε / 3) * (1 + ε / 2)) * log (log (n : ℝ)) :=
        le_mul_of_one_le_left hlln.le hfactor
      nlinarith [hmain]
    · linarith
  have hlogK : log K ≤ 2 * log (log (Real.log n)) := by
    have haux : log ((Real.log 2 * (1 + ε / 2))⁻¹) ≤ log (log (Real.log n)) := by
      exact log_le_log_of_le (inv_pos.2 hε') hlln'
    rw [hK, div_eq_mul_inv, Real.log_mul hlln.ne' (inv_ne_zero (ne_of_gt hε')), two_mul]
    linarith
  have hK₂ : 2 ≤ K := by
    rwa [le_div_iff₀ hε', ← mul_assoc]
  have hK₀ : 0 < K := zero_lt_two.trans_le hK₂
  have hK' : 0 < K ^ ((2 : ℝ) ^ K) := Real.rpow_pos_of_pos hK₀ _
  refine (anyk_divisor_bound n hK₂).trans ?_
  refine (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hn _) hK')
    (Real.rpow_pos_of_pos hn _)).mp ?_
  rw [
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' hK'.ne', Real.log_rpow hn, Real.log_rpow hK₀,
    Real.log_rpow hn]
  have hmul :
      (2 : ℝ) ^ K * log K ≤
        Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) :=
    mul_le_mul hpowK hlogK (Real.log_nonneg (one_le_two.trans hK₂)) (Real.rpow_nonneg hln.le _)
  have hsum :
      1 / K * log (n : ℝ) + (2 : ℝ) ^ K * log K ≤
        1 / K * log (n : ℝ) +
          Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hmul (1 / K * log (n : ℝ))
  refine hsum.trans ?_
  rw [hK, one_div_div, ← div_mul_eq_mul_div]
  suffices hs :
      Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) ≤
        Real.log 2 / log (log (n : ℝ)) * (ε / 2) * log (n : ℝ) by
    linarith
  suffices hs' :
      2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / (log (n : ℝ) ^ (ε / 3))) ≤
        Real.log 2 * ε / 2 by
    rw [Real.rpow_sub hln, div_eq_mul_one_div, Real.rpow_one, div_mul_eq_mul_div,
      mul_comm _ (log (n : ℝ)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hln.le
    rw [le_div_iff₀ hlln]
    field_simp at hs' ⊢
    simpa [mul_assoc] using hs'
  have hx'' :
      |2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3))| ≤
        Real.log 2 * ε / 2 := by
    simpa [mem_closedBall_zero_iff, norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hln _)] using hx'
  exact le_of_abs_le hx''

lemma divisor_bound {ε : ℝ} (hε1 : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  rcases le_total ε 1 with hε2 | hε2
  · exact divisor_bound₁ hε1 hε2
  · filter_upwards
      [divisor_bound₁ zero_lt_one le_rfl,
        tendsto_log_log_coe_at_top (eventually_ge_atTop (0 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with n hn hn' hn''
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn'') ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hn')

lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop, (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ)^ε := by
  rcases le_total (1 : ℝ) ε with hε1 | hε1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine trivial_divisor_bound.trans ?_
    exact Real.le_rpow_self_of_one_le (by exact_mod_cast hn) hε1
  · have hx : Tendsto (fun n : ℕ => Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹) atTop (𝓝 0) := by
      simpa [mul_assoc] using
        (tendsto_log_log_coe_at_top.inv_tendsto_atTop).const_mul (Real.log 2 * 2)
    filter_upwards
      [divisor_bound zero_lt_one,
        eventually_ge_atTop (1 : ℕ),
        hx (Metric.closedBall_mem_nhds 0 hε)] with n hn hn' hx'
    have hx'' : |Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹| ≤ ε := by
      simpa [mem_closedBall_zero_iff, norm_eq_abs] using hx'
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn') ?_)
    rw [div_mul_eq_mul_div, div_eq_mul_inv]
    simpa [one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using le_of_abs_le hx''

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]

lemma helpful_floor_identity {x : ℝ} :
  ⌊x⌋ - 2 * ⌊x/2⌋ ≤ 1 := by
  have h : (⌊x⌋ - 2 * ⌊x / 2⌋ : Int) < 2 := by
    exact_mod_cast (show ((⌊x⌋ : ℝ) - 2 * ⌊x / 2⌋) < 2 by
      linarith [Int.sub_one_lt_floor (x / 2), Int.floor_le x])
  linarith

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 := by
  have h₁ : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hx₁, by simpa [one_add_one_eq_two] using hx₂⟩
  have h₂ : ⌊x / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  rw [h₁, h₂]
  simp

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ := by
  have h₄ : (2 * ⌊x / 2⌋ : Int) - 1 < ⌊x⌋ := by
    exact_mod_cast (show (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ by
      linarith [Int.floor_le (x / 2), Int.sub_one_lt_floor x])
  exact Int.sub_one_lt_iff.mp h₄

def chebyshev_error (x : ℝ) : ℝ := by
  exact
    (summatory (fun i ↦ Real.log i) 1 x - (x * log x - x)) -
      2 * (summatory (fun i ↦ Real.log i) 1 (x / 2) - (x / 2 * log (x / 2) - x / 2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x =
    Real.log 2 * x + chebyshev_error x := by
  have hhalf :
      summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Real.log n) 1 (x / 2) := by
    rw [show summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Λ n * ⌊(x / 2) / n⌋) 1 x by
          rw [summatory]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_right_comm]]
    exact von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le)
  have hx2 : (2 : ℝ) * (x / 2) = x := by
    simpa using (mul_div_cancel₀ x two_ne_zero)
  calc
    summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x
      = summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 x -
          2 * summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x := by
            rw [summatory, summatory, summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = summatory (fun n ↦ Real.log n) 1 x - 2 * summatory (fun n ↦ Real.log n) 1 (x / 2) := by
          rw [von_mangoldt_summatory hx₀.le le_rfl, hhalf]
    _ = Real.log 2 * x + chebyshev_error x := by
          rw [chebyshev_error, mul_sub, Real.log_div hx₀.ne' two_ne_zero, mul_sub, hx2]
          ring

def chebyshev_first' (x : ℝ) : ℝ := by
  exact ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Real.log n

def chebyshev_second' (x : ℝ) : ℝ := by
  exact Finset.sum (Finset.range ⌊x⌋₊) fun n => Λ n

lemma chebyshev_first_eq {x : ℝ} :
  chebyshev_first x = ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n := by
  change Chebyshev.theta x =
    ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n
  rw [Chebyshev.theta_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first'_eq {x : ℝ} :
  chebyshev_first' x = ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Λ n := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first_le_chebyshev_second : chebyshev_first ≤ chebyshev_second := by
  intro x
  exact Chebyshev.theta_le_psi x

lemma chebyshev_first'_le_chebyshev_second' : chebyshev_first' ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_first'_eq, chebyshev_second']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma chebyshev_first_nonneg : 0 ≤ chebyshev_first := by
  intro x
  exact Chebyshev.theta_nonneg x

lemma chebyshev_first'_nonneg : 0 ≤ chebyshev_first' := by
  intro x
  rw [chebyshev_first'_eq]
  exact Finset.sum_nonneg' fun _ => ArithmeticFunction.vonMangoldt_nonneg

lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x

lemma chebyshev_second'_nonneg : 0 ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_second']
  exact Finset.sum_nonneg' fun _ => ArithmeticFunction.vonMangoldt_nonneg

lemma log_nat_nonneg : ∀ (n : ℕ), 0 ≤ log (n : ℝ) := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      exact log_nonneg (by simp)

lemma chebyshev_first_monotone : Monotone chebyshev_first := by
  exact Chebyshev.theta_mono

lemma is_O_chebyshev_first_chebyshev_second :
    Asymptotics.IsBigO atTop chebyshev_first chebyshev_second := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with x
  rw [one_mul, norm_of_nonneg (chebyshev_first_nonneg x),
    norm_of_nonneg (chebyshev_second_nonneg x)]
  exact chebyshev_first_le_chebyshev_second x

lemma chebyshev_second_eq_summatory : chebyshev_second = summatory Λ 1 := by
  ext x
  change Chebyshev.psi x = summatory (⇑Λ) 1 x
  rw [Chebyshev.psi_eq_sum_Icc, summatory]
  rw [Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · simp
  · simp

@[simp] lemma chebyshev_first_zero : chebyshev_first 0 = 0 := by
  exact Chebyshev.theta_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  exact Chebyshev.psi_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_first'_zero : chebyshev_first' 0 = 0 := by
  simp [chebyshev_first']

@[simp] lemma chebyshev_second'_zero : chebyshev_second' 0 = 0 := by
  simp [chebyshev_second']

lemma chebyshev_lower_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_error x ≤ chebyshev_second x - Real.log 2 * x := by
  rw [le_sub_iff_add_le', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hfloor : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) ≤ 1 := by
    exact_mod_cast helpful_floor_identity
  simpa using mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_second x - chebyshev_second (x / 2) - Real.log 2 * x ≤ chebyshev_error x := by
  rw [sub_le_iff_le_add', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  have hs : Finset.Icc 1 ⌊x / 2⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (half_le_self hx.le))
  rw [summatory, ← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  · simp_rw [Finset.mem_sdiff, Finset.mem_Icc, and_imp, not_and, not_le, Nat.le_floor_iff hx.le,
      Nat.floor_lt (div_nonneg hx.le zero_le_two), Nat.succ_le_iff]
    intro i hi₁ hi₂ hi₃
    replace hi₃ := hi₃ hi₁
    have hge1 : 1 ≤ x / i := by
      refine (one_le_div₀ ?_).2 hi₂
      exact_mod_cast hi₁
    have hlt2 : x / i < 2 := by
      have hi_pos : (0 : ℝ) < i := by
        exact_mod_cast hi₁
      have hmul : x < 2 * i := by
        linarith
      exact (div_lt_iff₀ hi_pos).2 (by simpa [mul_comm] using hmul)
    have hEq : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) = 1 := by
      exact_mod_cast (helpful_floor_identity2 (x := x / i) hge1 hlt2)
    rw [hEq, mul_one]
  · intro i _ _
    have hcoeff' : (2 : ℝ) * ↑⌊x / ↑i / 2⌋ ≤ ↑⌊x / ↑i⌋ := by
      exact_mod_cast (helpful_floor_identity3 (x := x / i))
    have hcoeff : 0 ≤ (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) := by
      linarith
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hcoeff)

lemma chebyshev_error_O :
  Asymptotics.IsBigO atTop chebyshev_error log := by
  have h23 : (2 : ℝ) < 3 := by norm_num
  refine (summatory_log h23).isBigO.sub ?_
  refine (((summatory_log h23).isBigO.comp_tendsto
    (tendsto_id.atTop_div_const zero_lt_two)).const_mul_left 2).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxhalf : 1 ≤ x / 2 := by linarith
  have hxlog : log (x / 2) ≤ log x := log_le_log_of_le (by linarith) (by linarith)
  simpa [Function.comp_apply, one_mul, norm_of_nonneg (log_nonneg hxhalf),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))] using hxlog

lemma chebyshev_lower_explicit {c : ℝ} (hc : c < Real.log 2) :
  ∀ᶠ x : ℝ in atTop, c * x ≤ chebyshev_second x := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h₁] with x hx₁ hx₂
  have hx₂' : ‖chebyshev_error x‖ ≤ (Real.log 2 - c) * x := by
    simpa [id, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx₁)] using hx₂
  have hmain := (neg_le_of_abs_le hx₂').trans (chebyshev_lower_aux (zero_lt_one.trans_le hx₁))
  linarith

lemma chebyshev_lower :
  Asymptotics.IsBigO atTop id chebyshev_second := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(Real.log 2 / 2)⁻¹, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    chebyshev_lower_explicit (half_lt_self (Real.log_pos one_lt_two))] with x hx₁ hx₂
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (half_pos (Real.log_pos one_lt_two))]
  simp [id, Real.norm_eq_abs, abs_of_nonneg hx₁, norm_of_nonneg (chebyshev_second_nonneg x)]
  simpa [mul_comm] using hx₂

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  chebyshev_second n ≤ n * Real.log n := by
  rw [chebyshev_second_eq_summatory, summatory_nat, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log n) ?_).trans ?_
  · intro i hi
    apply von_mangoldt_upper.trans
    simp only [Finset.mem_Icc] at hi
    exact log_le_log_of_le (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · simp

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  chebyshev_second x ≤ x * log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← chebyshev_second_eq_summatory]
  refine (chebyshev_trivial_upper_nat _).trans ?_
  refine mul_le_mul (Nat.floor_le hx₀.le)
    ?_ (log_nonneg (by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff x).2 hx
      exact this)) hx₀.le
  · exact log_le_log_of_le (by
      have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Nat.floor_pos.mpr hx)
      exact hfloorpos) (Nat.floor_le hx₀.le)

lemma chebyshev_upper_inductive {c : ℝ} (hc : Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, chebyshev_second x ≤ 2 * c * x + C * log C := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp h₁
  let C : ℝ := max 1 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : (n : ℝ) ≤ C
  · rw [chebyshev_second_eq_summatory]
    refine
      (summatory_monotone_of_nonneg _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) hn).trans
        ?_
    rw [← chebyshev_second_eq_summatory]
    refine (chebyshev_trivial_upper (le_max_left _ _)).trans ?_
    refine le_add_of_nonneg_left (mul_nonneg ?_ (Nat.cast_nonneg _))
    exact mul_nonneg zero_le_two ((Real.log_nonneg one_le_two).trans hc.le)
  · have hn : C < n := lt_of_not_ge hn
    have hn' : 0 < n := by
      refine Nat.succ_le_iff.mp ?_
      exact Nat.one_le_cast.mp ((le_max_left _ _).trans hn.le)
    have h₁ := chebyshev_upper_aux (Nat.cast_pos.mpr hn')
    rw [sub_sub, sub_le_iff_le_add] at h₁
    apply h₁.trans
    rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← Nat.cast_two,
      Nat.floor_div_eq_div, Nat.cast_two, ← add_assoc]
    have h₃ := hC₀ (n : ℝ) ((le_max_right _ _).trans hn.le)
    rw [Real.norm_eq_abs] at h₃
    replace h₃ := le_of_abs_le h₃
    have h₂ := ih (n / 2) (Nat.div_lt_self hn' one_lt_two)
    rw [← chebyshev_second_eq_summatory]
    have hsum :
        chebyshev_error (n : ℝ) + chebyshev_second (n / 2 : ℕ) + Real.log 2 * (n : ℝ) ≤
          (c - Real.log 2) * ‖(n : ℝ)‖ + (2 * c * (n / 2 : ℕ) + C * log C) +
            Real.log 2 * (n : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right (add_le_add h₃ h₂) (Real.log 2 * (n : ℝ))
    refine hsum.trans ?_
    have hc0 : 0 ≤ c := (Real.log_nonneg one_le_two).trans hc.le
    have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧
    Asymptotics.IsBigOWith 1 atTop chebyshev_second (fun x ↦ c * x + C * log C) := by
  have hc' : Real.log 2 < c / 2 := by
    nlinarith
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc'
  refine ⟨C, hC₁, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨0, ?_⟩
  intro x hx
  rw [Real.norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory,
    summatory_eq_floor, ← chebyshev_second_eq_summatory, one_mul]
  refine (hC ⌊x⌋₊).trans (le_trans ?_ (le_abs_self _))
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by nlinarith
  have hmul : c * (⌊x⌋₊ : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left hfloor hc0
  have hEq : 2 * (c / 2) * (⌊x⌋₊ : ℝ) = c * (⌊x⌋₊ : ℝ) := by ring
  simpa [hEq, add_assoc, add_left_comm, add_comm] using add_le_add_right hmul (C * log C)

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * Real.log 2 < c) :
  Asymptotics.IsBigOWith c atTop chebyshev_second id := by
  let c' : ℝ := Real.log 2 + c / 2
  have hc'₁ : c' < c := by
    dsimp [c']
    nlinarith
  have hc'₂ : 2 * Real.log 2 < c' := by
    dsimp [c']
    nlinarith
  have hc'₀ : 0 ≤ c' := by
    dsimp [c']
    nlinarith [Real.log_nonneg one_le_two, hc]
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂
  have hconst : (fun _ : ℝ ↦ C * log C) =o[atTop] id := by
    exact (isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop)
  have hmain : Asymptotics.IsBigOWith c atTop (fun x ↦ c' * x + C * log C) id := by
    have hc'₁' : ‖c'‖ < c := by
      simpa [Real.norm_of_nonneg hc'₀] using hc'₁
    simpa [c'] using
      (Asymptotics.isBigOWith_const_mul_self c' id atTop).add_isLittleO hconst hc'₁'
  exact (hC.trans hmain zero_le_one).congr_const (one_mul c)

lemma chebyshev_upper : Asymptotics.IsBigO atTop chebyshev_second id := by
  exact (chebyshev_upper_explicit (lt_add_one _)).isBigO

lemma chebyshev_first_upper : Asymptotics.IsBigO atTop chebyshev_first id := by
  exact is_O_chebyshev_first_chebyshev_second.trans chebyshev_upper

lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : Summable f) :
  Asymptotics.IsBigO atTop (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
    (fun _ ↦ (1 : ℝ)) := by
  simpa using hf.hasSum.tendsto_sum_nat.isBigO_one ℝ

lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) := by
  set f : ℝ → ℝ := log
  set g : ℝ → ℝ := fun x ↦ x^(1 / 2 : ℝ) - x^(-1 / 2 : ℝ)
  set f' : ℝ → ℝ := Inv.inv
  set g' : ℝ → ℝ := fun x ↦ 1 / 2 * x^(-3 / 2 : ℝ) + 1 / 2 * x^(-1 / 2 : ℝ)
  suffices h : ∀ y ∈ Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · have hpow : (2⁻¹ : ℝ) - 1 = -1 / 2 := by norm_num
      simpa [Set.Ici, id, one_mul, hpow] using
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (1 / 2 : ℝ)) (Or.inl hy'.ne'))
    · have hpow : (-1 / 2 : ℝ) - 1 = -3 / 2 := by norm_num
      have hpow' : (-2⁻¹ : ℝ) - 1 = -3 / 2 := by norm_num
      have hcoef : (-1 / 2 : ℝ) = -2⁻¹ := by norm_num
      have hderiv :=
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (-1 / 2 : ℝ)) (Or.inl hy'.ne'))
      simpa [Set.Ici, id, one_mul, hpow, hpow', hcoef, neg_mul, mul_assoc] using hderiv
  have hmain :=
    image_le_of_deriv_right_le_deriv_boundary
      (f := f) (f' := f') (a := 1) (b := x)
      (continuousOn_log.mono fun y hy ↦ (zero_lt_one.trans_le hy.1).ne')
      f_deriv
      (by simp [f])
      ((continuousOn_id.rpow_const (by simp)).sub
        (continuousOn_id.rpow_const fun y hy ↦ Or.inl (zero_lt_one.trans_le hy.1).ne'))
      g_deriv
      (by
        intro y hy
        dsimp [f', g']
        rw [← mul_add, mul_comm, ← div_eq_mul_one_div,
          le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), ← sub_nonneg, ← Real.rpow_neg_one]
        convert sq_nonneg (y^(-1 / 4 : ℝ) - y^(-3 / 4 : ℝ)) using 1
        have hy' : 0 < y := zero_lt_one.trans_le hy.1
        rw [sub_sq, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_two,
          ← Real.rpow_mul hy'.le, mul_assoc, ← Real.rpow_add hy', ← Real.rpow_mul hy'.le]
        norm_num
        ring)
  intro y hy
  exact hmain hy

lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx' : x ≠ 0 := hx0.ne'
  have hden : 0 < x * (x - 1) := by nlinarith
  have hrewrite : (x⁻¹)^2 / (1 - x⁻¹) = 1 / (x * (x - 1)) := by
    field_simp [hx']
  rw [hrewrite, ← div_eq_mul_one_div]
  rw [div_le_iff₀ hden]
  calc
    log x ≤ x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ) := log_le_thing hx.le
    _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by
      have hx1 : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
        calc
          x ^ (-3 / 2 : ℝ) * x = x ^ (-3 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-3 / 2 : ℝ) 1]; norm_num
      have hx2 : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
        calc
          x ^ (-1 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-1 / 2 : ℝ) 1]; norm_num
      calc
        x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ)
            = x ^ (-1 / 2 : ℝ) * x - x ^ (-1 / 2 : ℝ) := by rw [hx2]
        _ = x ^ (-1 / 2 : ℝ) * (x - 1) := by ring
        _ = (x ^ (-3 / 2 : ℝ) * x) * (x - 1) := by rw [hx1]
        _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by ring

@[to_additive]
lemma prod_prime_powers' {M : Type*} [CommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.prod_sigma', eq_comm]
  refine Finset.prod_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

@[to_additive]
lemma prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [prod_prime_powers']
  refine Finset.prod_congr rfl ?_
  intro p hp
  refine Finset.prod_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

lemma sum_prime_powers' {M : Type*} [AddCommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.sum_sigma', eq_comm]
  refine Finset.sum_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

lemma sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [sum_prime_powers']
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

@[to_additive]
lemma exact_prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine prod_prime_powers.trans (Finset.prod_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.prod_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

lemma exact_sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine sum_prime_powers.trans (Finset.sum_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

theorem geom_sum_Ico'_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (_hmn : m ≤ n) :
  ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx₀ hx₁

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n ∈ Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, sum_prime_powers, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  simp only [Finset.mem_Icc, Nat.cast_pow, and_imp]
  intro p hp₁ hp₂
  split_ifs with hp
  · have hp₃ : (p : ℝ) ≤ x := (Nat.le_floor_iff' hp.ne_zero).1 hp₂
    have hInsert :
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, if_pos]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow
          ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
    rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
    refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hp.one_lt))
    rw [show Finset.Icc 2 ⌊x⌋₊ = Finset.Ico 2 (⌊x⌋₊ + 1) by
      ext i
      simp]
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le ?_ ?_ ?_) ?_
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    · exact Nat.succ_le_succ (hp₁.trans hp₂)
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rw [abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n := by
    intro x hx
    rw [← summatory, ← von_mangoldt_summatory hx le_rfl, mul_sum, summatory,
      ← Finset.sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [mul_div_left_comm x, abs_sub_comm, ← mul_sub, abs_mul,
      ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg, Int.self_sub_floor, Int.fract_nonneg]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  refine Asymptotics.IsBigO.trans ?_ chebyshev_upper
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg))]
  exact hbound x hx

lemma is_O_von_mangoldt_div_self :
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
        (fun x ↦ x) by
    refine ((isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop).mul h).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← mul_sub, inv_mul_cancel_left₀ hx.ne']
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [inv_mul_cancel₀ hx.ne']
  refine summatory_log_sub.symm.triangle ?_
  have h₁ := (summatory_log (lt_add_one 2)).isBigO
  refine ((h₁.trans isLittleO_log_id_atTop.isBigO).sub (isBigO_refl _ _)).congr_left ?_
  intro x
  dsimp [summatory]
  ring

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  rw [prime_summatory, prime_summatory]
  refine (Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left one_le_two))
    (fun y hy => ?_) (fun _ _ => rfl)).symm
  rcases Finset.mem_sdiff.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_filter.mp hy1 with ⟨hyIcc, hyPrime⟩
  exact False.elim <| hy2 <|
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hyPrime.two_le, (Finset.mem_Icc.mp hyIcc).2⟩, hyPrime⟩

lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  exact is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self

lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have :
      (Finset.range (x + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 x := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2.pos, Nat.lt_succ_iff.mp hn.1⟩
  exact (Finset.card_le_card this).trans (by simp)

lemma chebyshev_first_eq_prime_summatory :
  chebyshev_first = prime_summatory (fun n ↦ Real.log n) 1 := by
  ext x
  change Chebyshev.theta x = prime_summatory (fun n ↦ Real.log n) 1 x
  rw [Chebyshev.theta_eq_sum_Icc, prime_summatory]
  congr 1

@[simp] lemma prime_counting'_zero : π' 0 = 0 := by
  rfl

@[simp] lemma prime_counting'_one : π' 1 = 0 := by
  rfl

@[simp] lemma prime_counting'_two : π' 2 = 0 := by
  rfl

lemma chebyshev_first_trivial_bound (x : ℝ) :
  chebyshev_first x ≤ π ⌊x⌋₊ * log x := by
  by_cases hx : x ≤ 0
  · rw [show chebyshev_first = Chebyshev.theta by rfl]
    rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_le_of_lt hx (by norm_num : (0 : ℝ) < 2))]
    simp [Nat.floor_eq_zero.2 (hx.trans_lt zero_lt_one)]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [chebyshev_first_eq_prime_summatory, prime_summatory, prime_counting_eq_card_primes,
      ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ (log x) ?_
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    have hyle : (y : ℝ) ≤ x := by
      exact le_trans (by exact_mod_cast hy.1.2) (Nat.floor_le hx0.le)
    exact log_le_log_of_le (show 0 < (y : ℝ) by exact_mod_cast hy.2.pos) hyle

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (fun _ ↦ 1) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (fun _ ↦ (1 : ℝ)) 1 x := by
  rw [prime_counting_eq_prime_summatory]
  simp [prime_summatory]

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - chebyshev_first x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
  have hmul :
      (fun n : ℕ ↦ ite (Nat.Prime n) (Real.log n : ℝ) 0) =
        fun n : ℕ ↦ ite (Nat.Prime n) (1 : ℝ) 0 * Real.log n := by
    funext n
    rw [boole_mul]
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory']
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', hmul,
    partial_summation_cont' (fun n ↦ ite (Nat.Prime n) (1 : ℝ) 0) Real.log (fun y ↦ y⁻¹)
      one_ne_zero (fun y hy ↦ hasDerivAt_log <| by
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        intro hzero
        rw [hzero] at hy'
        norm_num at hy')
      (by
        refine ContinuousOn.inv₀ continuousOn_id ?_
        intro y hy hzero
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        rw [hzero] at hy'
        norm_num at hy') x, Nat.cast_one]

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  Asymptotics.IsBigO atTop
    (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x - chebyshev_first x) id := by
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  change ‖∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Icc 1 x, (1 : ℝ) = x - 1 := by
      simp [hx.le]
    rw [hconst]
    linarith

lemma is_O_prime_counting_div_log :
  Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x) := by
  have h :
      Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) id := by
    refine (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left ?_
    intro x
    ring
  refine (Asymptotics.IsBigO.mul h (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_assoc, mul_inv_cancel₀ (Real.log_pos hx).ne', mul_one]
  · filter_upwards with x
    simp [div_eq_mul_inv]

lemma prime_counting_le_const_mul_div_log :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, (π (⌊x⌋₊) : ℝ) ≤ c * ‖x / Real.log x‖ := by
  obtain ⟨c₀, hc₀, hc₀'⟩ := is_O_prime_counting_div_log.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀'
  obtain ⟨c₁, hc₁⟩ := hc₀'
  refine ⟨max c₀ c₁, lt_max_of_lt_left hc₀, ?_⟩
  intro x
  have hmax : 0 < max c₀ c₁ := lt_max_of_lt_left hc₀
  have hc₁' :
      ∀ y : ℝ, c₁ ≤ y → ‖(π ⌊y⌋₊ : ℝ)‖ ≤ c₀ * ‖y / Real.log y‖ := by
    intro y hy
    exact hc₁ y hy
  simp only [Real.norm_natCast] at hc₁'
  rcases le_total c₁ x with hx₀ | hx₀
  · exact (hc₁' x hx₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rcases lt_trichotomy x 1 with hx₁ | rfl | hx₁
  · rw [Nat.floor_eq_zero.2 hx₁, Nat.primeCounting_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_of_le_left hc₀.le) (norm_nonneg _)
  · simp
  refine (Nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊)).trans ?_
  refine (((Nat.floor_le (zero_le_one.trans hx₁.le)).trans hx₀).trans (le_max_right c₀ c₁)).trans ?_
  rw [le_mul_iff_one_le_right hmax, norm_div, Real.norm_of_nonneg (Real.log_nonneg hx₁.le),
    Real.norm_of_nonneg (zero_le_one.trans hx₁.le), one_le_div (Real.log_pos hx₁)]
  exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hx₁)).trans (by simp)

lemma chebyshev_second_sub_chebyshev_first_eq {x : ℝ} (hx : 2 ≤ x) :
  chebyshev_second x - chebyshev_first x ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
  rw [show chebyshev_second = Chebyshev.psi by rfl, show chebyshev_first = Chebyshev.theta by rfl]
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx, add_tsub_cancel_left]
  refine (Finset.sum_le_card_nsmul _ _ ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * log x) ?_).trans ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hpow : x ^ (1 / k : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hx)
      refine one_div_le_one_div_of_le zero_lt_two hk'
    apply (chebyshev_first_monotone hpow).trans
    refine (chebyshev_first_le_chebyshev_second _).trans ?_
    refine (chebyshev_trivial_upper (one_le_rpow (one_le_two.trans hx) (by positivity))).trans ?_
    rw [Real.log_rpow (zero_lt_two.trans_le hx)]
    ring_nf
    exact le_rfl
  · have hcard :
        ((Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) ≤ Real.log x / Real.log 2 := by
      let m : ℕ := ⌊Real.log x / Real.log 2⌋₊
      refine le_trans ?_ (Nat.floor_le ?_)
      · have hsub : Finset.Icc 2 m ⊆ Finset.Icc 1 m := by
          intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          exact ⟨one_le_two.trans hn.1, hn.2⟩
        have hcard' : ((Finset.Icc 2 m).card : ℝ) ≤ ((Finset.Icc 1 m).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        simp [m, Nat.card_Icc] at hcard' ⊢
      · exact div_nonneg (Real.log_nonneg (one_le_two.trans hx)) (Real.log_pos one_lt_two).le
    rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_right hcard ?_).trans ?_
    · exact
        mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.log_nonneg (one_le_two.trans hx))
    have hconst : (1 / 2 : ℝ) / Real.log 2 ≤ 1 := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9]
    have hfac :
        (Real.log x / Real.log 2) * ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * Real.log x) =
          ((1 / 2 : ℝ) / Real.log 2) * (x ^ (1 / 2 : ℝ) * (Real.log x)^2) := by
      field_simp [(Real.log_pos one_lt_two).ne']
    rw [hfac]
    refine (mul_le_mul_of_nonneg_right hconst ?_).trans ?_
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · simp

lemma chebyshev_first_two : chebyshev_first 2 = Real.log 2 := by
  rw [chebyshev_first_eq_prime_summatory, prime_summatory]
  norm_num
  rw [show (Finset.Icc 1 2).filter Nat.Prime = ({2} : Finset ℕ) by decide]
  simp

lemma chebyshev_first_trivial_lower : ∀ x, 2 ≤ x → 0.5 ≤ chebyshev_first x := by
  intro x hx
  have hmono : chebyshev_first 2 ≤ chebyshev_first x := chebyshev_first_monotone hx
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  rw [chebyshev_first_two] at hmono
  linarith

lemma chebyshev_first_lower : Asymptotics.IsBigO atTop id chebyshev_first := by
  have hdiffO :
      Asymptotics.IsBigO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x)
        (fun x ↦ x ^ (1 / 2 : ℝ) * (log x)^2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hnonneg₁ : 0 ≤ chebyshev_second x - chebyshev_first x := by
      exact sub_nonneg_of_le (chebyshev_first_le_chebyshev_second x)
    have hnonneg₂ : 0 ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
      exact mul_nonneg (by positivity) (sq_nonneg _)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg₁, Real.norm_eq_abs, abs_of_nonneg hnonneg₂]
    exact chebyshev_second_sub_chebyshev_first_eq hx
  have hdiff :
      Asymptotics.IsLittleO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x) id := by
    refine hdiffO.trans_isLittleO ?_
    have ht : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)^2) (fun x ↦ x ^ (1 / 2 : ℝ)) := by
      refine ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).pow two_pos).congr' ?_ ?_
      · filter_upwards with x using by simp [sq]
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_two, ← Real.rpow_mul hx]
        congr 1
        ring
    refine ((isBigO_refl (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop).mul_isLittleO ht).congr' ?_ ?_
    · filter_upwards with x using by rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx, add_halves, Real.rpow_one]
      rfl
  have haux := hdiff.symm.trans_isBigO chebyshev_lower
  exact (chebyshev_lower.trans haux.right_isBigO_add).congr_right (fun x ↦ by ring)

lemma chebyshev_first_all :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * ‖x‖ ≤ ‖chebyshev_first x‖ := by
  obtain ⟨c₀, hc₀, h⟩ := chebyshev_first_lower.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.1 h.bound
  let c : ℝ := max c₀ (2 * X)
  have hc : 0 < c := lt_max_of_lt_left hc₀
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  intro x hx
  rw [inv_mul_le_iff₀ hc]
  rcases le_total X x with hx' | hx'
  · exact (hX x hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_of_nonneg (zero_le_two.trans hx)]
  have hhalf : (1 / 2 : ℝ) ≤ chebyshev_first x := by
    have hlow := chebyshev_first_trivial_lower x hx
    norm_num at hlow ⊢
    exact hlow
  refine hx'.trans ?_
  rw [show X = (2 * X) * (1 / 2 : ℝ) by ring]
  exact
    (mul_le_mul (le_max_right c₀ (2 * X)) hhalf (by norm_num) hc.le)


lemma is_O_div_log_prime_counting :
  Asymptotics.IsBigO atTop (fun x ↦ x / log x) (fun x ↦ (π ⌊x⌋₊ : ℝ)) := by
  have hθ :
      Asymptotics.IsBigO atTop chebyshev_first
        (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [one_mul, Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_eq_abs]
    exact (chebyshev_first_trivial_bound x).trans (le_abs_self _)
  refine ((chebyshev_first_lower.trans hθ).mul
    (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards with x using by simp [id, div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_inv_cancel_right₀ (Real.log_pos hx).ne']

def prime_log_div_sum_error (x : ℝ) : ℝ := by
  exact prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring

lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := by
  exact log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (pow_ne_zero 2 (Real.log_pos hx').ne')

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    have hrewrite : (y * log y ^ 2)⁻¹ = -((-y⁻¹) / (log y)^2) := by
      rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv]
    rw [hrewrite]
    exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hy1).ne').neg
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact my_func_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]

lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
  Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) := by
  suffices h :
      Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 ((log a)⁻¹ - 0)) by
    simpa using h
  have hEq :
      ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹ := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_inv_self_mul_log_sq ha (ha.trans_le hi)]
  rw [tendsto_congr' hEq]
  exact (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hb)).const_sub _

lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log a)⁻¹ a (fun x ↦ ?_) tendsto_id ?_
  · by_cases hx : a ≤ x
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact my_func_continuous_on.mono fun y hy ↦ ha.trans_le hy.1
    · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hx)]
  · refine (integral_Ioi_my_func_tendsto_aux ha tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop a] with x hx
    have hax : a ≤ x := le_of_lt hx
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using hy
    rw [Real.norm_of_nonneg]
    exact inv_nonneg.2 (mul_nonneg (le_trans (by linarith) hy'.1) (sq_nonneg _))

lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul (Real.continuousOn_log.mono ?_)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (Real.log_pos hx').ne'

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact my_func2_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]

lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) := by
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ ?_
    intro y hy
    have hy2 : 2 ≤ y := hy.1
    have hy0 : 0 < y := by linarith
    exact mul_ne_zero hy0.ne' (pow_ne_zero _ (Real.log_pos (by linarith)).ne')
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_set_ae Ico_ae_eq_Icc).2 ?_
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul]
    refine (partial_summation_integrable _ (ContinuousOn.integrableOn_Icc hlog')).sub ?_
    exact (hlog.mul hlog').integrableOn_Icc
  · have hbound :
        ∀ᵐ x : ℝ ∂volume.restrict (Ici k),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ ‖c * (x * log x ^ 2)⁻¹‖ := by
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ hx) (norm_nonneg _)).trans ?_
      have hcnorm : c * |(1 : ℝ)| ≤ ‖c‖ := by
        simp [Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Ici (2 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_inv₀.mono hne).neg
    · exact (Real.continuousOn_log.mono hne).pow _
    · intro y hy
      exact pow_ne_zero _ (Real.log_pos (one_lt_two.trans_le hy)).ne'
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  rw [sub_eq_iff_eq_add]
  convert hps using 1
  · rw [prime_summatory_eq_summatory]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hpy : y.Prime
    · have hy1 : (1 : ℝ) < y := by
        rw [Nat.one_lt_cast, ← Nat.succ_le_iff]
        exact (Finset.mem_Icc.mp hy).1
      simp [a, f, hpy]
      field_simp [(show (y : ℝ) ≠ 0 by positivity), (Real.log_pos hy1).ne']
    · simp [a, hpy]
  · rw [← prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq]
    rw [prime_reciprocal_integral]
    simp only [div_eq_mul_inv, Pi.add_apply, add_mul, f', f, neg_mul, mul_neg, integral_neg,
      sub_neg_eq_add, ← mul_inv]
    have h₁ :
        Integrable (fun a ↦ (a * Real.log a)⁻¹)
          (volume.restrict (Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (my_func2_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
        (setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          (integrable_on_prime_log_div_sum_error.mono_set
            (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self))
          (integrable_on_prime_log_div_sum_error.mono_set <| by
            intro y hy
            exact hx.trans hy.le) :
          ∫ t in Set.Ioc (2 : ℝ) x ∪ Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
            (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
              ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
    rw [mul_inv_cancel₀ (Real.log_pos (one_lt_two.trans_le hx)).ne', hEq,
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf

lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Ici y),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ c * (x * log x ^ 2)⁻¹ := by
      intro y hy
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans ?_
      rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg]
      exact zero_le_two.trans (hk₂.trans (hy.trans hx))
    have hI :
        Asymptotics.IsBigO atTop
          (fun y ↦ ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_my_func_Ioi hy]
    exact hI.trans_eventuallyEq hEq |>.trans (Asymptotics.isBigO_const_mul_self c _ _)

def meissel_mertens : ℝ := by
  exact 1 - log (Real.log 2) + prime_reciprocal_integral

lemma prime_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (fun x ↦ (log x)⁻¹) := by
  refine prime_reciprocal_error.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_summatory_one_eq_prime_summatory_two, meissel_mertens, ← prime_reciprocal_eq hx]

lemma is_o_log_inv_one {c : ℝ} (hc : c ≠ 0) :
    Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)⁻¹) (fun _ : ℝ ↦ (c : ℝ)) := by
  exact (Asymptotics.IsLittleO.inv_rev (is_o_one_log c⁻¹) (by simp [hc])).congr_right (by simp)

lemma is_o_const_log_log (c : ℝ) :
    Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ (c : ℝ)) (fun x : ℝ ↦ log (log x)) := by
  exact is_o_const_of_tendsto_at_top _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) _

lemma prime_reciprocal_upper :
  Asymptotics.IsBigO atTop (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x)
    (fun x ↦ log (log x)) := by
  refine ((prime_reciprocal.trans
      ((is_o_log_inv_one one_ne_zero).trans (is_o_const_log_log _)).isBigO).add
      ((isBigO_refl _ _).add_isLittleO (is_o_const_log_log meissel_mertens))).congr_left ?_
  intro x
  ring

lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ := by
  field_simp [hx₀, hx₁]
  ring

lemma sum_thing_has_sum (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) ((k + 1 : ℝ)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => inv_nonneg.2 (by positivity))]
  have htel :
      ∀ i : ℕ,
        ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ =
          (↑(i + (k + 1)) : ℝ)⁻¹ - (↑(i + 1 + (k + 1)) : ℝ)⁻¹ := by
    intro i
    simp only [Nat.cast_add_one, Nat.cast_add, add_right_comm (i : ℝ) 1, ← add_assoc]
    convert mul_add_one_inv (i + k + 1) ?_ ?_ using 2
    · norm_num [add_assoc]
    · exact_mod_cast Nat.succ_ne_zero (i + k)
    · exact_mod_cast Nat.succ_ne_zero (i + k + 1)
  simp only [htel, Finset.sum_range_sub', zero_add, Nat.cast_add_one]
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat (k + 1))).const_sub
      ((k + 1 : ℝ)⁻¹)

lemma sum_thing'_has_sum : HasSum (fun n : ℕ ↦ ((n - 1) * n : ℝ)⁻¹) 1 := by
  refine (hasSum_nat_add_iff' 2).1 ?_
  have hzero :
      (∑ i ∈ Finset.range 2, (((i : ℝ) - 1) * (i : ℝ))⁻¹) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hzero]
  norm_num
  have hbase :
      HasSum (fun n : ℕ ↦ ((↑n + ↑0 + 1) * (↑n + ↑0 + 2) : ℝ)⁻¹) 1 := by
    simpa using sum_thing_has_sum 0
  refine HasSum.congr_fun hbase ?_
  intro n
  have hn2 : (↑n + 2 : ℝ) ≠ 0 := by positivity
  have hn1 : (↑n + 2 - 1 : ℝ) ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  field_simp [hn1, hn2, Nat.cast_add]
  ring

lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum (fun n : ℕ ↦ ((n + k) * (n + k + 1) : ℝ)⁻¹) ((k : ℝ)⁻¹) := by
  convert sum_thing_has_sum (k - 1) using 1
  · ext n
    rw [add_assoc, add_assoc, Nat.cast_sub hk, Nat.cast_one, sub_add_cancel, add_sub, sub_add]
    norm_num [add_assoc]
  · simp [hk]

lemma sum_thing''_indicator_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum ({n | k < n}.indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹)) ((k : ℝ)⁻¹) := by
  have hrange : Set.range (fun i : ℕ => i + (k + 1)) = {n | k < n} := by
    ext n
    constructor
    · rintro ⟨i, rfl⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) i)
    · intro hn
      refine ⟨n - (k + 1), Nat.sub_add_cancel ?_⟩
      exact Nat.succ_le_of_lt hn
  rw [← hrange]
  have hinj : Function.Injective (fun i : ℕ => i + (k + 1)) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (Function.Injective.hasSum_iff hinj ?_).1
  · convert sum_thing'''_has_sum hk using 1
    ext n
    simp [Set.indicator_of_mem, ← add_assoc]
  · intro n hn
    simp [Set.indicator_of_notMem, hn]

lemma prime_sum_thing_summable' (s : Set ℕ) :
  Summable (s.indicator ((Set.ofPred Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) := by
  exact (sum_thing'_has_sum.summable.indicator _).indicator _

lemma indicator_mono {α β : Type*} [Zero β] [Preorder β] {s t : Set α} {f : α → β}
    (h : s ⊆ t) (hf : ∀ x, x ∉ s → x ∈ t → 0 ≤ f x) :
  indicator s f ≤ indicator t f := by
  intro x
  by_cases hs : x ∈ s
  · simp [Set.indicator_of_mem, hs, h hs]
  · by_cases ht : x ∈ t
    · simp [Set.indicator_of_notMem, hs, ht, hf x hs ht]
    · simp [Set.indicator_of_notMem, hs, ht]

lemma prime_sum_thing {k : ℕ} (hk : 1 ≤ k) :
  tsum
      ({n | k < n}.indicator ((Set.ofPred Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) ≤
    ((k : ℝ)⁻¹) := by
  refine hasSum_le ?_ (prime_sum_thing_summable' _).hasSum (sum_thing''_indicator_has_sum hk)
  intro n
  by_cases hkn : k < n
  · by_cases hpn : Nat.Prime n
    · have hpn' : n ∈ Set.ofPred Nat.Prime := hpn
      simp [Set.indicator_of_mem, hkn, hpn']
    · have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (lt_of_le_of_lt hk hkn)
      have hnonneg : 0 ≤ (n : ℝ)⁻¹ * ((n : ℝ) - 1)⁻¹ := by
        apply mul_nonneg
        · positivity
        · exact inv_nonneg.2 (sub_nonneg.mpr hn1.le)
      have hpn' : n ∉ Set.ofPred Nat.Prime := hpn
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hkn, hpn', hnonneg]
  · simp [Set.indicator_of_notMem, hkn]

lemma my_mul_thing' : ∀ {n : ℕ}, (0 : ℝ) ≤ (((n - 1) * n : ℝ)⁻¹) := by
  intro n
  exact inv_nonneg.2 my_mul_thing

lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ range (⌊x⌋₊ + 1), f i - c)
    (fun x ↦ x⁻¹) := by
  have hf'' : Summable f := (sum_thing'_has_sum.summable).of_nonneg_of_le hf' hf
  refine ⟨tsum f, (Asymptotics.IsBigO.of_bound 2 ?_).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ ⌊x⌋₊ := by
    rwa [Nat.le_floor_iff' one_ne_zero, Nat.cast_one]
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa
  rw [← Summable.sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg fun i ↦ hf' (i + _)), norm_of_nonneg (zero_le_one.trans hx)]
  transitivity (⌊x⌋₊ : ℝ)⁻¹
  · refine hasSum_le (fun n ↦ ?_) ((summable_nat_add_iff _).2 hf'').hasSum
      (sum_thing'''_has_sum hx')
    have hsub : (↑n : ℝ) + (↑⌊x⌋₊ + 1) - 1 = ↑n + ↑⌊x⌋₊ := by ring
    simpa [Nat.cast_add, Nat.cast_add_one, add_assoc, add_left_comm, add_comm, mul_comm,
      mul_left_comm, mul_assoc, hsub] using hf (n + (⌊x⌋₊ + 1))
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := zero_lt_one.trans_le hx''
  field_simp [hxpos.ne', hfloorpos.ne']
  nlinarith [Nat.lt_floor_add_one x]

lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Icc 1 ⌊x⌋₊, f i - c)
    (fun x ↦ x⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf'
  refine ⟨c, hc.congr_left ?_⟩
  intro x
  have hIco : Finset.Ico 0 (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    simpa using (Finset.Ico_succ_right_eq_Icc 0 ⌊x⌋₊)
  rw [Finset.range_eq_Ico, hIco, Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · have h0 : f 0 = 0 := ((hf' 0).antisymm (by simpa using hf 0)).symm
    simp [h0]
  · simp

lemma intermediate_bound :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ x⁻¹) := by
  simp only [prime_summatory, Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · rfl
    · exact my_mul_thing'
  · split_ifs with h
    · exact my_mul_thing'
    · simp

lemma prime_proper_powers {x : ℝ} {f : ℕ → ℝ} :
  (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f q) - prime_summatory f 1 x =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 2 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  rw [exact_sum_prime_powers, prime_summatory, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  have hk : 1 ≤ ⌊log x / Real.log p⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  rw [Finset.Icc_eq_insert_Icc_succ hk, Finset.sum_insert, pow_one, add_comm]
  · rw [Finset.mem_Icc]
    norm_num

lemma is_O_reciprocal_difference_aux {x : ℝ} :
  |(∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
      prime_summatory (fun p ↦ (((p - 1) * p : ℝ)⁻¹)) 1 x| ≤
    ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) := by
  rw [prime_proper_powers, prime_summatory, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by simpa using hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  let N : ℕ := ⌊log x / Real.log p⌋₊
  have hk : 1 ≤ N := by
    dsimp [N]
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  have hgeom :
      ∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹ =
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) := by
    simpa only [← Finset.Ico_succ_right_eq_Icc, inv_pow, Nat.succ_eq_add_one,
      Nat.succ_eq_succ] using
      (geom_sum_Ico' (x := (p : ℝ)⁻¹)
        (by simpa using (inv_ne_one.mpr hp1.ne'))
        (Nat.succ_le_succ hk))
  have hdiff :
      |(∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹) - (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    rw [hgeom]
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) -
            (((p - 1) * p : ℝ)⁻¹) =
          -(((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1)) := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      have haux : (p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N = p := by
        rw [inv_pow]
        field_simp [hp0'.ne', pow_ne_zero N hp0'.ne']
      have hrewrite :
          (1 - (p : ℝ) ^ 2 * (1 / (p : ℝ)) ^ (N + 1) - 1) * (p : ℝ) ^ N =
            -((p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N) := by
        ring_nf
      rw [hrewrite, haux]
    rw [hstep, abs_neg, abs_of_nonneg]
    exact div_nonneg (inv_nonneg.2 (pow_nonneg hp0'.le _)) (sub_nonneg.2 hp1.le)
  have hdiff' :
      |(∑ k ∈ Finset.Icc 2 ⌊log x / Real.log p⌋₊, (↑(p ^ k) : ℝ)⁻¹) -
          (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    simpa [N, Nat.cast_pow] using hdiff
  rw [hdiff']
  have hratio :
      ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) ≤ 2 * ((p : ℝ) ^ (N + 1))⁻¹ := by
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) =
          ((p : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) ^ (N + 1))⁻¹ := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      ring_nf
    rw [hstep]
    have hp_ratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
      have hp_sub : 0 < (p : ℝ) - 1 := sub_pos_of_lt hp1
      rw [div_le_iff₀ hp_sub]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      nlinarith
    exact mul_le_mul_of_nonneg_right hp_ratio (inv_nonneg.2 (pow_nonneg hp0'.le _))
  have hxp : x < (p : ℝ) ^ (N + 1) := by
    have hlogb : Real.logb p x < (N + 1 : ℝ) := by
      dsimp [N]
      simpa [Real.log_div_log] using Nat.lt_floor_add_one (log x / Real.log p)
    have hxpow : x < (p : ℝ) ^ ((N + 1 : ℕ) : ℝ) := by
      convert (Real.logb_lt_iff_lt_rpow hp1 hx).1 hlogb using 1
      norm_num
    rwa [Real.rpow_natCast] at hxpow
  have hinv : ((p : ℝ) ^ (N + 1))⁻¹ ≤ x⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hx hxp.le)
  exact hratio.trans (mul_le_mul_of_nonneg_left hinv (by positivity))

lemma is_O_reciprocal_difference : ∃ c,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := intermediate_bound
  refine ⟨c, ?_⟩
  have hc' : Asymptotics.IsBigO atTop
      (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
      (fun x ↦ (log x)⁻¹) := by
    refine hc.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine Asymptotics.IsBigO.triangle ?_ hc'
  have haux0 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ) * x⁻¹)
      (fun x ↦ (log x)⁻¹) := by
    refine (is_O_prime_counting_div_log.mul (isBigO_refl _ _)).congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hx.ne', one_mul]
  have haux : Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ))
      (fun x ↦ (log x)⁻¹) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (haux0.const_mul_left 2)
  have hbound :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦
          (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
            prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
            prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x)
        (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [one_mul, norm_eq_abs, norm_eq_abs]
    have hcard :
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
          (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
      have hcard' :
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := by
        rw [Finset.sum_const, prime_counting_eq_card_primes]
      calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := hcard'
        _ = (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
          exact nsmul_eq_mul (π ⌊x⌋₊) (2 * x⁻¹)
    exact (is_O_reciprocal_difference_aux).trans (le_trans (le_of_eq hcard) (le_abs_self _))
  exact hbound.trans haux

lemma prime_power_reciprocal : ∃ b,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) - (log (log x) + b))
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_reciprocal_difference
  refine ⟨meissel_mertens + c, ?_⟩
  exact (hc.add prime_reciprocal).congr_left fun x ↦ by ring_nf

lemma summable_indicator_iff_subtype {α β : Type*} [TopologicalSpace α] [AddCommMonoid α]
  {s : Set β} (f : β → α) :
  Summable (f ∘ Subtype.val : s → α) ↔ Summable (s.indicator f) := by
  simpa [Function.comp_def] using (summable_subtype_iff_indicator (s := s) (f := f))

lemma is_unit_of_is_unit_pow {α : Type*} [CommMonoid α] {a : α} :
  ∀ n, n ≠ 0 → (IsUnit (a ^ n) ↔ IsUnit a) := by
  intro n
  induction n with
  | zero =>
      intro h
      exact (h rfl).elim
  | succ n ih =>
      cases n with
      | zero =>
          intro _
          simp
      | succ n =>
          intro _
          rw [pow_succ, IsUnit.mul_iff, ih (Nat.succ_ne_zero _), and_self]

lemma is_prime_pow_and_not_prime_iff {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (x : α) :
  IsPrimePow x ∧ ¬ Prime x ↔ (∃ p k, Prime p ∧ 1 < k ∧ p ^ k = x) := by
  constructor
  · rintro ⟨⟨p, k, hp, hk, rfl⟩, hx⟩
    refine ⟨p, k, hp, ?_, rfl⟩
    rw [← Nat.succ_le_iff] at hk
    exact lt_of_le_of_ne hk fun h => hx (h ▸ by simpa using hp)
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hk0 : k ≠ 0 := by omega
    refine ⟨IsPrimePow.pow hp.isPrimePow hk0, fun hx => ?_⟩
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_add]
      simp [pow_one, mul_comm]
    have hu : IsUnit (p ^ (k - 1)) :=
      (hx.irreducible.isUnit_or_isUnit hpow).resolve_left hp.not_isUnit
    exact hp.not_isUnit <| (is_unit_of_is_unit_pow (a := p) (k - 1) (by omega)).mp hu

lemma log_one_sub_recip {p : ℕ} (hp : 1 < p) :
  |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ (((p - 1) * p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hpInv : |(p : ℝ)⁻¹| < 1 := by
    simpa [abs_of_nonneg hp0.le] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  have h := Real.abs_log_sub_add_sum_range_le hpInv 1
  have h' :
      |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) := by
    simpa [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, div_one, pow_one]
      using h
  have hrew : |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) = (((p - 1) * p : ℝ)⁻¹) := by
    rw [abs_inv, abs_of_nonneg hp0.le, pow_two, div_eq_mul_inv]
    field_simp [hp0.ne']
  exact h'.trans_eq hrew

lemma my_func_neg {p : ℕ} (hp : 1 < p) : (p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹) ≤ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hsub : 0 < 1 - (p : ℝ)⁻¹ := by
    exact sub_pos_of_lt <| by simpa [one_div] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  linarith [log_le_sub_one_of_pos hsub]

lemma mertens_third_log_error :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c)
    (fun x : ℝ ↦ x⁻¹) := by
  simp only [Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · exact neg_le_of_neg_le (neg_le_of_abs_le (log_one_sub_recip h.one_lt))
    · exact my_mul_thing'
  · split_ifs with h
    · rw [neg_nonneg]
      exact my_func_neg h.one_lt
    · rfl

lemma mertens_third_log :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        log (1 - (p : ℝ)⁻¹)⁻¹ - (log (log x) + c))
    (fun x : ℝ ↦ (log x)⁻¹) := by
  obtain ⟨c₂, hc₂⟩ := mertens_third_log_error
  have hc₂' : Asymptotics.IsBigO atTop
      (fun x : ℝ ↦
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c₂)
      (fun x ↦ (log x)⁻¹) := by
    refine hc₂.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine ⟨c₂ + meissel_mertens, (prime_reciprocal.add hc₂').congr_left ?_⟩
  intro x
  simp only [Real.log_inv, Finset.sum_neg_distrib, Finset.sum_add_distrib, neg_add,
    prime_summatory]
  ring

lemma partial_euler_trivial_upper_bound {n : ℕ} : partial_euler_product n ≤ 2 ^ π n := by
  rw [partial_euler_product, prime_counting_eq_card_primes, ← Finset.prod_const]
  have hpos : ∀ i : ℕ, i.Prime → 0 < (1 - (i : ℝ)⁻¹) := fun i hi =>
    sub_pos_of_lt <| by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.pos
      simpa using (one_div_lt_one_div hi0 zero_lt_one).2 (by exact_mod_cast hi.one_lt)
  refine Finset.prod_le_prod (fun i hi => (inv_pos.2 (hpos i (Finset.mem_filter.mp hi).2)).le)
    (fun i hi => ?_)
  rcases Finset.mem_filter.mp hi with ⟨_, hip⟩
  have hip0 : (0 : ℝ) < i := by exact_mod_cast hip.pos
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (i : ℝ)⁻¹ := by
    field_simp [hip0.ne']
    nlinarith [show (2 : ℝ) ≤ i by exact_mod_cast hip.two_le]
  have hinv : (1 - (i : ℝ)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (hpos _ hip) (by positivity)]
    exact hhalf
  norm_num at hinv ⊢
  exact hinv

lemma mertens_third :
  ∃ c, 0 < c ∧
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊ - c * Real.log x)
      (fun _ ↦ (1 : ℝ)) := by
  obtain ⟨c, hc⟩ := mertens_third_log
  obtain ⟨k, hk₀, hk⟩ := hc.exists_pos
  refine ⟨Real.exp c, Real.exp_pos _, Asymptotics.IsBigO.of_bound (2 * (k * Real.exp c)) ?_⟩
  filter_upwards [hk.bound, Real.tendsto_log_atTop.eventually (eventually_ge_atTop k)] with x hx hx'
  have hk' : k * (Real.log x)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (hk₀.trans_le hx')]
    simpa using hx'
  rw [norm_eq_abs, norm_inv, Real.norm_of_nonneg (hk₀.le.trans hx')] at hx
  have i := (Real.abs_exp_sub_one_le (hx.trans hk')).trans
    (mul_le_mul_of_nonneg_left hx zero_le_two)
  have hx'' : 0 < Real.log x := hk₀.trans_le hx'
  have hx''' : 0 < Real.exp c * Real.log x := mul_pos (Real.exp_pos _) hx''
  have hp : ∀ p, p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime → 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact inv_pos.2 (sub_pos_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.2.one_lt)))
  rw [Real.exp_sub, Real.exp_add, Real.exp_log hx'', ← Real.log_prod (fun p h ↦ (hp p h).ne'),
    Real.exp_log (Finset.prod_pos hp), mul_comm, div_sub_one hx'''.ne', abs_div,
    abs_of_nonneg hx'''.le, div_le_iff₀ hx''', mul_assoc, mul_mul_mul_comm,
    inv_mul_cancel₀ hx''.ne', mul_one] at i
  simpa [partial_euler_product, norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using i

lemma weak_mertens_third_upper :
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊) log := by
  let ⟨c, _, hc⟩ := mertens_third
  exact ((hc.trans (is_o_one_log 1).isBigO).add
    (Asymptotics.isBigO_const_mul_self c _ _)).congr_left (by simp)

lemma weak_mertens_third_lower :
    Asymptotics.IsBigO atTop log (fun x ↦ partial_euler_product ⌊x⌋₊) := by
  obtain ⟨c, hc₀, hc⟩ := mertens_third
  have h := Asymptotics.isBigO_self_const_mul hc₀.ne' log atTop
  have h' := hc.trans_isLittleO ((is_o_one_log 1).trans_isBigO h)
  exact (h.trans h'.right_isBigO_add).congr_right (by simp)

lemma weak_mertens_third_upper_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 2 ≤ x → ‖partial_euler_product (⌊x⌋₊)‖ ≤ c * ‖log x‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_upper.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  refine ⟨max c (2 ^ c₁ / Real.log 2), lt_max_of_lt_left hc₀, fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    norm_of_nonneg (Real.log_nonneg (one_le_two.trans hx))]
  have hpow : (2 : ℝ) ^ π ⌊x⌋₊ ≤ 2 ^ c₁ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have hpi : (π ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℕ) := by
      exact_mod_cast (prime_counting_le_self ⌊x⌋₊)
    exact le_trans hpi ((Nat.floor_le (zero_le_two.trans hx)).trans h)
  have hupper : 2 ^ c₁ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
    calc
      2 ^ c₁ = (2 ^ c₁ / Real.log 2) * Real.log 2 := by
        field_simp [(Real.log_pos one_lt_two).ne']
      _ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
        refine mul_le_mul (le_max_right _ _) (Real.log_le_log zero_lt_two hx)
          (Real.log_nonneg one_le_two) ?_
        exact le_trans (by positivity : 0 ≤ 2 ^ c₁ / Real.log 2) (le_max_right _ _)
  exact (partial_euler_trivial_upper_bound.trans hpow).trans hupper

lemma weak_mertens_third_lower_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 1 ≤ x → c * ‖log x‖ ≤ ‖partial_euler_product (⌊x⌋₊)‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_lower.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  let c' := max c (Real.log c₁)
  have hc' : 0 < c' := lt_max_of_lt_left hc₀
  refine ⟨c'⁻¹, inv_pos.2 hc', fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · rw [inv_mul_le_iff₀ hc']
    exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (Real.log_nonneg hx),
    norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound)]
  have hlog : Real.log x ≤ c' := by
    exact le_trans (Real.log_le_log (zero_lt_one.trans_le hx) h) (le_max_right _ _)
  have hone : c'⁻¹ * Real.log x ≤ 1 := by
    rw [inv_mul_le_iff₀ hc', mul_one]
    exact hlog
  exact hone.trans (partial_euler_trivial_lower_bound (n := ⌊x⌋₊))

lemma two_pow_card_distinct_divisors_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
  2 ^ ω n ≤ ArithmeticFunction.sigma 0 n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.pow_card_le_prod _ _ _ ?_
  intro p hp
  have hp0 : 0 < n.factorization p :=
    Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  omega

lemma mul_eq_mul_iff {a b c d : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d) :
  a * b = c * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases hac.eq_or_lt with rfl | hac'
    · exact ⟨rfl, Nat.mul_left_cancel ha (show a * b = a * d by simpa using h)⟩
    rcases hbd.eq_or_lt with rfl | hbd'
    · exact ⟨Nat.mul_right_cancel hb (show a * b = c * b by simpa using h), rfl⟩
    exact False.elim <| (mul_lt_mul'' hac' hbd' ha.le hb.le).ne h
  · rintro ⟨rfl, rfl⟩
    rfl

lemma divisor_count_eq_pow_iff_squarefree {n : ℕ} :
  ArithmeticFunction.sigma 0 n = 2 ^ ω n ↔ Squarefree n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization, ← Finset.prod_const,
    Nat.squarefree_iff_factorization_le_one hn, eq_comm]
  rw [Finset.prod_eq_prod_iff_of_le']
  · constructor
    · intro h p
      by_cases hp : p ∈ n.factorization.support
      · have hpEq : 2 = n.factorization p + 1 := h p hp
        omega
      · rw [Finsupp.notMem_support_iff.mp hp]
        exact Nat.zero_le 1
    · intro h p hp
      have hp0 : 0 < n.factorization p :=
        Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hp1 : n.factorization p ≤ 1 := h p
      omega
  · intro _ _
    exact zero_lt_two
  · intro p hp
    have hp0 : 0 < n.factorization p :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    omega

lemma tendsto_primorial_at_top :
  Tendsto primorial atTop atTop := by
  apply primorial_monotone.tendsto_atTop_atTop
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  refine ⟨p, hp₁.trans ?_⟩
  exact Nat.le_of_dvd (primorial_pos _) hp₂.dvd_primorial

lemma primorial_three : primorial 3 = 6 := by
  decide

lemma two_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ≤ primorial n := by
  rw [← primorial_two]
  exact primorial_monotone hn

lemma squarefree_prime_prod {ι : Type*} {s : Finset ι} (f : ι → ℕ)
    (hs : ∀ i ∈ s, (f i).Prime) (hf : Set.InjOn f (s : Set ι)) :
  Squarefree (s.prod f) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (hs i hi) (hs j hj)).2 fun hEq => hij (hf hi hj hEq)
  · intro i hi
    exact (hs i hi).squarefree

lemma divisor_lower_bound_aux (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ n : ℕ in atTop,
      1 / log (log (n : ℝ)) * (1 - ε) ≤ 1 / (log (log (n : ℝ)) - c) := by
  suffices hmain :
      ∀ᶠ x : ℝ in atTop, 1 / x * (1 - ε) ≤ 1 / (x - c) by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually hmain
  filter_upwards [eventually_ge_atTop (c + -c / ε), eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop c] with x hx hx' hx''
  have hx0 : 0 < x - c := sub_pos_of_lt hx''
  have haux : ε * c - c ≤ ε * x := by
    have := mul_le_mul_of_nonneg_left hx hε.le
    simpa [sub_eq_add_neg, mul_add, mul_div_cancel₀ _ hε.ne'] using this
  have hmul : (1 - ε) * (x - c) ≤ x := by
    nlinarith
  have hmid : 1 - ε ≤ x / (x - c) := (le_div_iff₀ hx0).2 hmul
  have hleft : 1 / x * (1 - ε) = (1 - ε) / x := by ring
  rw [hleft]
  exact (div_le_iff₀ hx').2 <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmid

lemma factors_primorial {n : ℕ} :
  (primorial n).primeFactorsList = (List.range (n + 1)).filter Nat.Prime := by
  have hrange : (List.range (n + 1)).Nodup := by
    simpa using (List.nodup_range : (List.range (n + 1)).Nodup)
  have hnodup : ((List.range (n + 1)).filter Nat.Prime).Nodup := hrange.filter _
  have htf :
      ((List.range (n + 1)).filter Nat.Prime).toFinset =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext x
    simp
  have hprod : ((List.range (n + 1)).filter Nat.Prime).prod = primorial n := by
    calc
      ((List.range (n + 1)).filter Nat.Prime).prod
          = ((List.range (n + 1)).filter Nat.Prime).toFinset.prod id := by
              simpa using (List.prod_toFinset id hnodup).symm
      _ = primorial n := by
            rw [htf, primorial]
            rfl
  refine
    ((Nat.primeFactorsList_unique hprod (fun p hp => by
        simpa using (List.mem_filter.mp hp).2)).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  have hpair : List.Pairwise (fun a b : ℕ => a ≤ b) (List.range (n + 1)) := by
    simpa using (List.sortedLT_range (n + 1)).pairwise.imp (@Nat.le_of_lt)
  exact hpair.sublist List.filter_sublist

@[simp] lemma to_finset_filter
  {α : Type*} {l : List α} (p : α → Prop) [DecidableEq α] [DecidablePred p] :
  (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp

@[simp] lemma to_finset_range {n : ℕ} : (List.range n).toFinset = Finset.range n := by
  simpa using List.toFinset_range n

lemma factors_to_finset_primorial {n : ℕ} :
  (primorial n).primeFactorsList.toFinset = (Finset.range (n + 1)).filter Nat.Prime := by
  rw [factors_primorial]
  simp

lemma card_distinct_factors_primorial {n : ℕ} : ω (primorial n) = π n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    factors_to_finset_primorial, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

lemma card_factors_primorial {n : ℕ} : Ω (primorial n) = π n := by
  rw [← card_distinct_factors_primorial, eq_comm,
    ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (primorial_pos _).ne']
  exact squarefree_primorial _

lemma le_log_sigma_zero_primorial :
  ∃ c : ℝ, ∀ p, 2 ≤ p →
    (log (primorial p : ℝ) * Real.log 2) / (log (log (primorial p : ℝ)) - c) ≤
      Real.log (ArithmeticFunction.sigma 0 (primorial p)) := by
  obtain ⟨c, hc₀, hc⟩ := chebyshev_first_all
  refine ⟨Real.log c, ?_⟩
  intro p hp
  have hp₁ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₂ : 0 < (p : ℝ) := zero_lt_two.trans_le hp₁
  have hp₃ : 0 < chebyshev_first p := chebyshev_first_pos hp₁
  have htheta : log (primorial p : ℝ) = chebyshev_first p := by
    simpa [chebyshev_first] using (Chebyshev.theta_eq_log_primorial (p : ℝ)).symm
  have hpow : ((2 : ℝ) ^ ω (primorial p)) = (2 : ℝ) ^ ((ω (primorial p) : ℝ)) := by
    rw [← Real.rpow_natCast]
  rw [divisor_count_eq_pow_iff_squarefree.2 (squarefree_primorial _), Nat.cast_pow, Nat.cast_two,
    hpow, Real.log_rpow (by positivity), card_distinct_factors_primorial, htheta]
  have h₁ : chebyshev_first p ≤ π p * log (p : ℝ) := by
    simpa using chebyshev_first_trivial_bound (p : ℝ)
  have hcp : c * (p : ℝ) ≤ chebyshev_first p := by
    simpa [Real.norm_of_nonneg hp₂.le, Real.norm_of_nonneg hp₃.le] using hc (p : ℝ) hp₁
  have h₂ : log (p : ℝ) ≤ log (chebyshev_first p) - Real.log c := by
    have hlog := log_le_log_of_le (mul_pos hc₀ hp₂) hcp
    rw [Real.log_mul hc₀.ne' hp₂.ne'] at hlog
    linarith
  have h₃ : 0 < log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp)
  have h₄ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg one_le_two
  have h₅ : (0 : ℝ) ≤ π p := Nat.cast_nonneg (π p)
  have hden : 0 < log (chebyshev_first p) - Real.log c := by
    linarith
  refine (div_le_iff₀ hden).2 ?_
  calc
    chebyshev_first p * Real.log 2 ≤ (π p * log (p : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h₁ h₄
    _ ≤ (π p * (log (chebyshev_first p) - Real.log c)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ h₅) h₄
    _ = π p * Real.log 2 * (log (chebyshev_first p) - Real.log c) := by ring

lemma one_le_sigma {k n : ℕ} (hn : n ≠ 0) : 1 ≤ ArithmeticFunction.sigma k n := by
  simpa [ArithmeticFunction.sigma_apply] using
    (Finset.single_le_sum
      (f := fun d : ℕ ↦ d ^ k)
      (fun d _ => Nat.zero_le _)
      (by simp [hn] : 1 ∈ n.divisors))

lemma divisor_lower_bound_log {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
  obtain ⟨c, hc⟩ := le_log_sigma_zero_primorial
  have hmain :
      ∃ᶠ n : ℕ in atTop,
        log (n : ℝ) * Real.log 2 / (log (log (n : ℝ)) - c) ≤
          log (ArithmeticFunction.sigma 0 n : ℝ) := by
    exact tendsto_primorial_at_top.frequently (eventually_atTop.2 ⟨2, hc⟩).frequently
  apply (hmain.and_eventually (divisor_lower_bound_aux c hε)).mp
  simp only [and_imp]
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁ hn₂
  apply hn₁.trans'
  rw [mul_div_assoc, mul_comm (log (n : ℝ))]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (Nat.one_le_cast.2 hn₀))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hn₂ (Real.log_nonneg one_le_two)

lemma divisor_lower_bound {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) ≤
        ArithmeticFunction.sigma 0 n := by
  apply (divisor_lower_bound_log hε).mp
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁
  have hn₀' : 0 < n := hn₀
  have hn₀'' : (0 : ℝ) < n := by exact_mod_cast hn₀'
  have hsigma : (0 : ℝ) < ArithmeticFunction.sigma 0 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀'.ne'
  have hlog :
      log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε))) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
    simpa [Real.log_rpow hn₀''] using hn₁
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hn₀'' _) hsigma).1 hlog

lemma cobounded_of_frequently {α : Type*} [ConditionallyCompleteLattice α]
  {f : Filter α} (c : α) (hc : ∃ᶠ x in f, c ≤ x) :
  Filter.IsCobounded (· ≤ ·) f := by
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨x, hxc, hxd⟩ := (hc.and_eventually hd).exists
  exact hxc.trans hxd

lemma Limsup_eq_of_eventually_of_frequently {f : Filter ℝ} (c : ℝ)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c + ε)
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c - ε ≤ x) :
  limsup id f = c := by
  have hb : f.IsBounded (· ≤ ·) := ⟨c + 1, upper 1 zero_lt_one⟩
  have hb' : f.IsBoundedUnder (· ≤ ·) id := by
    simpa [Filter.IsBoundedUnder]
      using hb
  have hc : f.IsCobounded (· ≤ ·) :=
    cobounded_of_frequently (c - 1) (by simpa using lower 1 zero_lt_one)
  have hc' : f.IsCoboundedUnder (· ≤ ·) id := by
    simpa [Filter.IsCoboundedUnder]
      using hc
  apply le_antisymm
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    simpa using (limsup_le_of_le (u := id) (f := f) (a := c + ε) hc' (upper ε hε))
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    rw [← sub_le_iff_le_add]
    simpa using (le_limsup_of_frequently_le (u := id) (f := f) (a := c - ε) (lower ε hε) hb')

lemma Limsup_eq_of_eventually_of_frequently_mul {f : Filter ℝ} {c : ℝ} (hc : 0 ≤ c)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c * (1 + ε))
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c * (1 - ε) ≤ x) :
  limsup id f = c := by
  rcases hc.eq_or_lt with rfl | hc'
  · refine Limsup_eq_of_eventually_of_frequently 0 (fun ε hε => ?_) (fun ε hε => ?_)
    · apply Filter.EventuallyLE.trans (upper 1 zero_lt_one)
        (Filter.Eventually.of_forall fun x => ?_)
      linarith [hε.le]
    · apply (lower 1 zero_lt_one).mono
      intro x hx
      linarith [hε.le]
  · apply Limsup_eq_of_eventually_of_frequently
    · intro ε hε
      refine (upper (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        x ≤ c * (1 + ε / c) := hx
        _ = c + ε := by
          field_simp [hc'.ne']
    · intro ε hε
      refine (lower (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        c - ε = c * (1 - ε / c) := by
          field_simp [hc'.ne']
        _ ≤ x := hx

lemma divisor_limsup :
  atTop.limsup
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)) =
    log (2 : ℝ) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have l := Real.tendsto_log_atTop
  refine Limsup_eq_of_eventually_of_frequently_mul
    (f := Filter.map
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ))
      atTop)
    (Real.log_nonneg one_le_two) ?_ ?_
  · intro ε hε
    change ∀ᶠ n : ℕ in atTop,
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ) ≤
        Real.log 2 * (1 + ε)
    filter_upwards [divisor_bound hε, eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    have hlog : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε))) := by
      exact log_le_log_of_le (by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀.ne') hn
    have hlog' : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ) := by
      simpa [Real.log_rpow hn₁] using hlog
    refine (div_le_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hlog' hn₃.le
    have hEq :
        ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) * log (log (n : ℝ)) =
          Real.log 2 * (1 + ε) * log (n : ℝ) := by
      field_simp [hn₃.ne']
    calc
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ))
          ≤ ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) *
              log (log (n : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Real.log 2 * (1 + ε) * log (n : ℝ) := hEq
  · intro ε hε
    change ∃ᶠ n : ℕ in atTop,
      Real.log 2 * (1 - ε) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)
    refine (divisor_lower_bound_log hε).mp ?_
    filter_upwards [eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    intro hn
    refine (le_div_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hn hn₃.le
    have hEq :
        Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := by
      field_simp [hn₃.ne']
    calc
      Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := hEq
      _ ≤ log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos391/Mertens.lean` -/

section
open Filter Real
open scoped BigOperators Topology

namespace Mertens

noncomputable def M : ℝ := meissel_mertens

noncomputable def E₂p (x : ℝ) : ℝ :=
  prime_summatory (fun p : ℕ ↦ (p : ℝ)⁻¹) 1 x -
    (Real.log (Real.log x) + M)

theorem sum_prime_div_eq (x : ℝ) :
    (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) =
      Real.log (Real.log x) + M + E₂p x := by
  rw [E₂p]
  have hsets : (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime =
      (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp, hpx⟩, hprime⟩
      exact ⟨⟨hp, hpx⟩, hprime⟩
    · rintro ⟨⟨hp, hpx⟩, hprime⟩
      exact ⟨⟨hp, hpx⟩, hprime⟩
  rw [prime_summatory, ← hsets]
  simp only [one_div]
  ring

theorem eventually_abs_E₂p_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |E₂p x| ≤ C / Real.log x := by
  obtain ⟨C, hC⟩ := prime_reciprocal.bound
  refine ⟨|C|, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hx hlarge
  have hlog : 0 < Real.log x := Real.log_pos hlarge
  change |prime_summatory (fun p : ℕ ↦ (p : ℝ)⁻¹) 1 x -
    (Real.log (Real.log x) + meissel_mertens)| ≤ |C| / Real.log x
  rw [Real.norm_eq_abs] at hx
  have hinv : ‖(Real.log x)⁻¹‖ = (Real.log x)⁻¹ :=
    norm_of_nonneg (inv_nonneg.mpr hlog.le)
  rw [hinv] at hx
  exact hx.trans (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hlog.le))

end Mertens

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos391.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 391.
https://www.erdosproblems.com/forum/thread/391

Informal authors:
- Boris Alexeev
- John H. Conway
- Michael Rosenfeld
- Andrew Sutherland
- Terence Tao
- Michael Uhr
- Kevin Ventullo

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos391.md
-/
/-
Erdős Problem 391: decomposing a factorial into large factors.

The mathematical reconstruction and the correspondence between the published
argument and this development are documented in `tex/391.tex`.
-/


open Filter Real
open scoped BigOperators Topology



noncomputable section

attribute [local instance] Classical.propDecidable

/-- A positive, nondecreasing `n`-tuple whose product is `n!`. -/
def IsFactorialRepresentation (n : ℕ) (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ Monotone a ∧ ∏ i, a i = n.factorial

/-- The threshold `k` can be attained by a representation of `n!` with `n`
factors.  Requiring every factor to be at least `k` is equivalent to requiring
the first factor of the sorted representation to be at least `k`. -/
def Feasible (n k : ℕ) : Prop :=
  0 < k ∧ ∃ a : Fin n → ℕ, IsFactorialRepresentation n a ∧ ∀ i, k ≤ a i

/-- The standard representation `n! = 1 * 2 * ... * n`. -/
def standardRepresentation (n : ℕ) (i : Fin n) : ℕ := i.1 + 1

lemma standardRepresentation_pos (n : ℕ) (i : Fin n) :
    0 < standardRepresentation n i := by
  simp [standardRepresentation]

lemma standardRepresentation_monotone (n : ℕ) :
    Monotone (standardRepresentation n) := by
  intro i j hij
  exact Nat.add_le_add_right hij 1

lemma standardRepresentation_prod (n : ℕ) :
    ∏ i, standardRepresentation n i = n.factorial := by
  calc
    ∏ i : Fin n, standardRepresentation n i =
        ∏ i ∈ Finset.range n, (i + 1) := by
          simpa [standardRepresentation] using
            (Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) n)
    _ = n.factorial := Finset.prod_range_add_one_eq_factorial n

lemma standardRepresentation_spec (n : ℕ) :
    IsFactorialRepresentation n (standardRepresentation n) := by
  exact ⟨standardRepresentation_pos n, standardRepresentation_monotone n,
    standardRepresentation_prod n⟩

/-- Sorting an arbitrary positive tuple preserves its product and lower bound,
so it yields a representation in the nondecreasing convention used here. -/
lemma feasible_of_unsorted {n k : ℕ} (hk : 0 < k) (a : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (ha_prod : ∏ i, a i = n.factorial)
    (ha_lower : ∀ i, k ≤ a i) : Feasible n k := by
  let b : Fin n → ℕ := a ∘ Tuple.sort a
  refine ⟨hk, b, ⟨?_, Tuple.monotone_sort a, ?_⟩, ?_⟩
  · intro i
    exact ha_pos (Tuple.sort a i)
  · simpa [b, Function.comp_def, ha_prod] using (Equiv.prod_comp (Tuple.sort a) a)
  · intro i
    exact ha_lower (Tuple.sort a i)

/-- A threshold-admissible subfactorization of `n!` with exactly `n` positive
factors can be upgraded to a factorization: multiply the unused quotient into
one factor, then sort. -/
lemma feasible_of_subfactorization {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (a : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_dvd : (∏ i, a i) ∣ n.factorial) (ha_lower : ∀ i, k ≤ a i) :
    Feasible n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let q : ℕ := (m + 1).factorial / ∏ i, a i
  let b : Fin (m + 1) → ℕ :=
    Fin.cases (a 0 * q) (fun i ↦ a i.succ)
  have hq_pos : 0 < q := by
    apply Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) ha_dvd)
    exact Finset.prod_pos fun i _ ↦ ha_pos i
  have hb_pos : ∀ i, 0 < b i := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact mul_pos (ha_pos 0) hq_pos
    · exact ha_pos j.succ
  have hb_lower : ∀ i, k ≤ b i := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (ha_lower 0).trans (Nat.le_mul_of_pos_right (a 0) hq_pos)
    · exact ha_lower j.succ
  have hb_prod : ∏ i, b i = (m + 1).factorial := by
    rw [Fin.prod_univ_succ]
    change a 0 * q * ∏ i : Fin m, a i.succ = (m + 1).factorial
    calc
      a 0 * q * ∏ i : Fin m, a i.succ =
          (a 0 * ∏ i : Fin m, a i.succ) * q := by ac_rfl
      _ = (∏ i, a i) * q := by rw [Fin.prod_univ_succ]
      _ = (m + 1).factorial := Nat.mul_div_cancel' ha_dvd
  exact feasible_of_unsorted hk b hb_pos hb_prod hb_lower

lemma feasible_one {n : ℕ} (hn : 0 < n) : Feasible n 1 := by
  refine ⟨by simp, standardRepresentation n, standardRepresentation_spec n, ?_⟩
  intro i
  simp [standardRepresentation]

lemma factor_le_product {n : ℕ} {a : Fin n → ℕ}
    (ha : ∀ i, 0 < a i) (i : Fin n) : a i ≤ ∏ j, a j := by
  have hdiv : a i ∣ ∏ j, a j := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  exact Nat.le_of_dvd (Finset.prod_pos fun j _ ↦ ha j) hdiv

lemma feasible_le_factorial {n k : ℕ} (hn : 0 < n) (hk : Feasible n k) :
    k ≤ n.factorial := by
  obtain ⟨_hkpos, a, ha, hka⟩ := hk
  let i : Fin n := ⟨0, hn⟩
  calc
    k ≤ a i := hka i
    _ ≤ ∏ j, a j := factor_le_product ha.1 i
    _ = n.factorial := ha.2.2

/-- The maximal attainable lower bound on all `n` factors.  The search bound
`n!` is exact by `feasible_le_factorial`. -/
def t (n : ℕ) : ℕ := Nat.findGreatest (Feasible n) n.factorial

lemma t_le_factorial (n : ℕ) : t n ≤ n.factorial :=
  Nat.findGreatest_le _

lemma t_feasible {n : ℕ} (hn : 0 < n) : Feasible n (t n) := by
  apply Nat.findGreatest_spec (P := Feasible n) (m := 1)
  · exact (Nat.factorial_pos n)
  · exact feasible_one hn

lemma feasible_le_t {n k : ℕ} (hn : 0 < n) (hk : Feasible n k) : k ≤ t n := by
  exact Nat.le_findGreatest (feasible_le_factorial hn hk) hk

lemma t_pos {n : ℕ} (hn : 0 < n) : 0 < t n :=
  (t_feasible hn).1

/-- The geometric-mean obstruction: every factor is at least `t n`. -/
lemma t_pow_le_factorial {n : ℕ} (hn : 0 < n) : t n ^ n ≤ n.factorial := by
  obtain ⟨_htpos, a, ha, hta⟩ := t_feasible hn
  calc
    t n ^ n = ∏ _i : Fin n, t n := by simp
    _ ≤ ∏ i, a i := Finset.prod_le_prod' (fun i _hi ↦ hta i)
    _ = n.factorial := ha.2.2

/-- A coarse bound used to keep all logarithms in their natural range. -/
lemma t_le_self {n : ℕ} (hn : 0 < n) : t n ≤ n := by
  rw [← Nat.pow_le_pow_iff_left hn.ne']
  exact (t_pow_le_factorial hn).trans n.factorial_le_pow

/-- The normalized extremal threshold appearing in Problem 391. -/
noncomputable def ratio (n : ℕ) : ℝ := (t n : ℝ) / n

lemma ratio_nonneg (n : ℕ) : 0 ≤ ratio n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma ratio_pos {n : ℕ} (hn : 0 < n) : 0 < ratio n := by
  exact div_pos (by exact_mod_cast t_pos hn) (by exact_mod_cast hn)

lemma ratio_le_one {n : ℕ} (hn : 0 < n) : ratio n ≤ 1 := by
  rw [ratio, div_le_one (by exact_mod_cast hn)]
  exact_mod_cast t_le_self hn

lemma n_mul_log_t_le_log_factorial {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log (t n) ≤ Real.log n.factorial := by
  have htpos : (0 : ℝ) < t n := by exact_mod_cast t_pos hn
  calc
    (n : ℝ) * Real.log (t n) = Real.log ((t n : ℝ) ^ n) := by
      rw [Real.log_pow]
    _ ≤ Real.log (n.factorial : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast t_pow_le_factorial hn

/-- A convenient effective upper half of Stirling's formula.  The constant is
deliberately loose; its error is `o(n / log n)`, which is what the prime
obstruction below needs. -/
lemma log_factorial_le (n : ℕ) (hn : 0 < n) :
    Real.log n.factorial ≤
      (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hseq := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  change Real.log (Stirling.stirlingSeq (m + 1)) ≤
    Real.log (Stirling.stirlingSeq (0 + 1)) at hseq
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity : (Real.sqrt 2) ≠ 0),
    Real.log_exp, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hseq
  have hlog_two_mul : Real.log (2 * (m + 1 : ℕ)) =
      Real.log 2 + Real.log (m + 1 : ℕ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
    positivity
  have hlog_div : Real.log ((m + 1 : ℕ) / Real.exp 1) =
      Real.log (m + 1 : ℕ) - 1 := by
    rw [Real.log_div (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)
      (Real.exp_pos 1).ne', Real.log_exp]
  rw [hlog_two_mul, hlog_div] at hseq
  linarith

/-- The matching lower half of the deliberately loose Stirling estimate. -/
lemma log_factorial_ge (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log n.factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hseq := Stirling.log_stirlingSeq_bounded_by_constant m
  have hconstant : 0 ≤
      1 - (12 : ℝ)⁻¹ - Real.log 2 / 2 := by
    nlinarith [Real.log_two_lt_d9]
  have hseqnonneg : 0 ≤ Real.log (Stirling.stirlingSeq (m + 1)) :=
    hconstant.trans hseq
  rw [Stirling.log_stirlingSeq_formula] at hseqnonneg
  have hlog_two_mul : Real.log (2 * (m + 1 : ℕ)) =
      Real.log 2 + Real.log (m + 1 : ℕ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
    positivity
  have hlog_div : Real.log ((m + 1 : ℕ) / Real.exp 1) =
      Real.log (m + 1 : ℕ) - 1 := by
    rw [Real.log_div (by positivity : (((m + 1 : ℕ) : ℝ)) ≠ 0)
      (Real.exp_pos 1).ne', Real.log_exp]
  rw [hlog_two_mul, hlog_div] at hseqnonneg
  have hlognonneg : 0 ≤ Real.log (2 * (m + 1 : ℕ)) := by
    apply Real.log_nonneg
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    linarith
  nlinarith

/-- Convert the discrete base-`p` logarithm used by Legendre's formula to a
uniform real logarithmic bound. -/
lemma natLog_add_one_real_le {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    (Nat.log p n + 1 : ℕ) ≤ (2 * Real.log (n : ℝ) + 1 : ℝ) := by
  have hbase : Nat.log p n ≤ Nat.log 2 n :=
    Nat.log_anti_left Nat.one_lt_two hp.two_le
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpowReal : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogpow : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤
      Real.log (n : ℝ) := Real.log_le_log (by positivity) hpowReal
  rw [Real.log_pow] at hlogpow
  have htwo : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hcastnonneg : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
    nlinarith
  have hbaseReal : (Nat.log p n : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast hbase
  push_cast
  linarith

lemma factorial_two_valuation_eq (n : ℕ) :
    n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  simpa using h

lemma binary_digit_sum_le (n : ℕ) :
    (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 := by
  have hdigit : ∀ x ∈ Nat.digits 2 n, x ≤ 1 := by
    intro x hx
    have hlt := Nat.digits_lt_base Nat.one_lt_two hx
    omega
  have haux : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 1) → l.sum ≤ l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons x xs ih =>
        have hx : x ≤ 1 := hl x (by simp)
        have hxs : ∀ y ∈ xs, y ≤ 1 := by
          intro y hy
          exact hl y (by simp [hy])
        have ih' := ih hxs
        simp only [List.sum_cons, List.length_cons]
        omega
  have hsum : (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length :=
    haux _ hdigit
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.length_digits 2 n Nat.one_lt_two hn] at hsum
    exact hsum

lemma factorial_two_valuation_lower (n : ℕ) :
    n - (Nat.log 2 n + 1) ≤ n.factorial.factorization 2 := by
  rw [factorial_two_valuation_eq]
  exact Nat.sub_le_sub_left (binary_digit_sum_le n) n

lemma eventually_log_ratio_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (ratio n) ≤ -1 + δ := by
  have hlog := Real.isLittleO_log_id_atTop.def (by positivity : (0 : ℝ) < δ / 4)
  filter_upwards [hlog.natCast_atTop,
    Filter.eventually_ge_atTop ⌈(2 / δ : ℝ)⌉₊,
    Filter.eventually_gt_atTop 1] with n hlogn hnlarge hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  simp only [id, norm_eq_abs] at hlogn
  rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn.le)),
    abs_of_nonneg hnreal.le] at hlogn
  have hlarge_real : (2 / δ : ℝ) ≤ n := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hnlarge)
  have hone : (1 : ℝ) ≤ (δ / 2) * n := by
    have htwo : (2 : ℝ) ≤ δ * n := by
      calc
        (2 : ℝ) = δ * (2 / δ) := by field_simp
        _ ≤ δ * n := mul_le_mul_of_nonneg_left hlarge_real hδ.le
    linarith
  have herr : Real.log (n : ℝ) / 2 + 1 ≤ δ * n := by
    calc
      Real.log (n : ℝ) / 2 + 1 ≤ (δ / 4 * n) / 2 + (δ / 2) * n :=
        add_le_add (div_le_div_of_nonneg_right hlogn (by norm_num)) hone
      _ ≤ δ * n := by nlinarith [mul_pos hδ hnreal]
  rw [ratio, Real.log_div (by exact_mod_cast (t_pos hnpos).ne') hnreal.ne']
  have htlog := n_mul_log_t_le_log_factorial hnpos
  have hfact := log_factorial_le n hnpos
  apply le_of_mul_le_mul_left (a := (n : ℝ)) ?_ hnreal
  nlinarith

lemma eventually_ratio_le_exp (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ratio n ≤ Real.exp (-1 + δ) := by
  filter_upwards [eventually_log_ratio_le δ hδ,
    Filter.eventually_gt_atTop 0] with n hn hnpos
  exact (Real.log_le_iff_le_exp (ratio_pos hnpos)).mp hn

lemma eventually_ratio_le_two_fifths :
    ∀ᶠ n : ℕ in Filter.atTop, ratio n ≤ (2 : ℝ) / 5 := by
  have hexp_neg : Real.exp (-1) < (2 : ℝ) / 5 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.exp_neg,
      inv_eq_one_div, div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_d9]
  have hlog : (-1 : ℝ) < Real.log ((2 : ℝ) / 5) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp_neg
  let δ : ℝ := (Real.log ((2 : ℝ) / 5) + 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have harg : -1 + δ < Real.log ((2 : ℝ) / 5) := by
    dsimp [δ]
    linarith
  have hexp : Real.exp (-1 + δ) < (2 : ℝ) / 5 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mp harg
  filter_upwards [eventually_ratio_le_exp δ hδ] with n hn
  exact hn.trans hexp.le

lemma log_nat_eq_sum_factorization {m : ℕ} (hm : m ≠ 0) :
    Real.log m = ∑ p ∈ m.primeFactors,
      (m.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm,
    Nat.prod_factorization_eq_prod_primeFactors]
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero (m.factorization p)
      (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma sum_factorization_log_le_log {m : ℕ} (hm : m ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (m.factorization p : ℝ) * Real.log p ≤ Real.log m := by
  rw [log_nat_eq_sum_factorization hm]
  have heq :
      (∑ p ∈ P, (m.factorization p : ℝ) * Real.log p) =
        ∑ p ∈ P ∩ m.primeFactors,
          (m.factorization p : ℝ) * Real.log p := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hpP hpnot
    have hpnotmem : p ∉ m.primeFactors := by
      intro hpmem
      exact hpnot (Finset.mem_inter.mpr ⟨hpP, hpmem⟩)
    have hpnotdvd : ¬p ∣ m := by
      intro hpdvd
      exact hpnotmem ((hP p hpP).mem_primeFactors hpdvd hm)
    rw [Nat.factorization_eq_zero_of_not_dvd hpnotdvd]
    simp
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro p hpprime _hpnot
  exact mul_nonneg (Nat.cast_nonneg _) <|
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpprime).one_lt.le)

lemma selected_prime_excess_le_factor_excess {m k : ℕ}
    (hm : m ≠ 0) (hk : 0 < k) (hkm : k ≤ m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (m.factorization p : ℝ) * (Real.log p - Real.log k) ≤
      Real.log m - Real.log k := by
  let s : ℕ := ∑ p ∈ P, m.factorization p
  by_cases hs : s = 0
  · have hz : ∀ p ∈ P, m.factorization p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hs
    have hsumzero :
        (∑ p ∈ P, (m.factorization p : ℝ) *
          (Real.log p - Real.log k)) = 0 := by
      exact Finset.sum_eq_zero fun p hp ↦ by simp [hz p hp]
    rw [hsumzero]
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkm))
  · have hsone : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
    have hlogk : 0 ≤ Real.log k :=
      Real.log_nonneg (by exact_mod_cast hk)
    have hprime := sum_factorization_log_le_log hm P hP
    calc
      (∑ p ∈ P, (m.factorization p : ℝ) * (Real.log p - Real.log k)) =
          (∑ p ∈ P, (m.factorization p : ℝ) * Real.log p) -
            (s : ℝ) * Real.log k := by
              simp_rw [mul_sub, Finset.sum_sub_distrib]
              simp [s, Finset.sum_mul]
      _ ≤ Real.log m - Real.log k := by nlinarith

lemma prime_excess_le_representation_excess {n k : ℕ} {a : Fin n → ℕ}
    (ha : IsFactorialRepresentation n a) (hk : 0 < k) (hka : ∀ i, k ≤ a i)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hval : ∀ p ∈ P, n.factorial.factorization p = 1) :
    ∑ p ∈ P, (Real.log p - Real.log k) ≤
      Real.log n.factorial - (n : ℝ) * Real.log k := by
  have hleft :
      (∑ p ∈ P, (Real.log p - Real.log k)) =
        ∑ i : Fin n, ∑ p ∈ P,
          (a i).factorization p * (Real.log p - Real.log k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hv : ∑ i : Fin n, (a i).factorization p = 1 := by
      rw [← Nat.factorization_prod_apply (fun i _hi ↦ (ha.1 i).ne')]
      rw [ha.2.2, hval p hp]
    rw [← Finset.sum_mul]
    norm_cast
    simp [hv]
  rw [hleft]
  calc
    (∑ i : Fin n, ∑ p ∈ P,
        (a i).factorization p * (Real.log p - Real.log k)) ≤
        ∑ i : Fin n, (Real.log (a i) - Real.log k) := by
          exact Finset.sum_le_sum fun i _hi ↦
            selected_prime_excess_le_factor_excess (ha.1 i).ne' hk (hka i) P hP
    _ = Real.log n.factorial - (n : ℝ) * Real.log k := by
      rw [Finset.sum_sub_distrib]
      have hlogprod :
          (∑ i : Fin n, Real.log (a i)) =
            Real.log (∏ i : Fin n, (a i : ℝ)) := by
        symm
        exact Real.log_prod fun i _hi ↦ by exact_mod_cast (ha.1 i).ne'
      rw [hlogprod]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_cast
      rw [ha.2.2]

lemma prime_excess_le_representation_excess_of_one_le {n k : ℕ}
    {a : Fin n → ℕ} (ha : IsFactorialRepresentation n a)
    (hk : 0 < k) (hka : ∀ i, k ≤ a i)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hval : ∀ p ∈ P, 1 ≤ n.factorial.factorization p)
    (hgap : ∀ p ∈ P, 0 ≤ Real.log p - Real.log k) :
    ∑ p ∈ P, (Real.log p - Real.log k) ≤
      Real.log n.factorial - (n : ℝ) * Real.log k := by
  have hleft :
      (∑ p ∈ P, (Real.log p - Real.log k)) ≤
        ∑ i : Fin n, ∑ p ∈ P,
          (a i).factorization p * (Real.log p - Real.log k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p hp
    have hv : ∑ i : Fin n, (a i).factorization p =
        n.factorial.factorization p := by
      rw [← Nat.factorization_prod_apply (fun i _hi ↦ (ha.1 i).ne'), ha.2.2]
    calc
      Real.log p - Real.log k =
          (1 : ℝ) * (Real.log p - Real.log k) := by ring
      _ ≤ (n.factorial.factorization p : ℝ) *
          (Real.log p - Real.log k) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hval p hp) (hgap p hp)
      _ = ∑ i : Fin n,
          (a i).factorization p * (Real.log p - Real.log k) := by
            rw [← Finset.sum_mul]
            norm_cast
            rw [hv]
  calc
    (∑ p ∈ P, (Real.log p - Real.log k)) ≤
        ∑ i : Fin n, ∑ p ∈ P,
          (a i).factorization p * (Real.log p - Real.log k) := hleft
    _ ≤ ∑ i : Fin n, (Real.log (a i) - Real.log k) := by
      exact Finset.sum_le_sum fun i _hi ↦
        selected_prime_excess_le_factor_excess (ha.1 i).ne' hk (hka i) P hP
    _ = Real.log n.factorial - (n : ℝ) * Real.log k := by
      rw [Finset.sum_sub_distrib]
      have hlogprod :
          (∑ i : Fin n, Real.log (a i)) =
            Real.log (∏ i : Fin n, (a i : ℝ)) := by
        symm
        exact Real.log_prod fun i _hi ↦ by exact_mod_cast (ha.1 i).ne'
      rw [hlogprod]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_cast
      rw [ha.2.2]

/-- The primes in the upper half of `[1,n]`.  Restricting to this very simple
subfamily already forces a loss of order `n / log n`. -/
def upperHalfPrimes (n : ℕ) : Finset ℕ :=
  (n + 1).primesBelow \ (n / 2 + 1).primesBelow

lemma mem_upperHalfPrimes {n p : ℕ} :
    p ∈ upperHalfPrimes n ↔ p.Prime ∧ n / 2 < p ∧ p ≤ n := by
  simp only [upperHalfPrimes, Finset.mem_sdiff, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpn, hpprime⟩, hpnot⟩
    have hnotlt : ¬p < n / 2 + 1 := fun h ↦ hpnot ⟨h, hpprime⟩
    exact ⟨hpprime, by omega, by omega⟩
  · rintro ⟨hpprime, hhalf, hpn⟩
    refine ⟨⟨by omega, hpprime⟩, ?_⟩
    rintro ⟨hplt, _⟩
    omega

lemma card_upperHalfPrimes (n : ℕ) :
    (upperHalfPrimes n).card =
      Nat.primeCounting n - Nat.primeCounting (n / 2) := by
  have hsub : (n / 2 + 1).primesBelow ⊆ (n + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr
      ⟨(Nat.mem_primesBelow.mp hp).1.trans_le (by omega), (Nat.mem_primesBelow.mp hp).2⟩
  rw [upperHalfPrimes, Finset.card_sdiff_of_subset hsub,
    Nat.primesBelow_card_eq_primeCounting',
    Nat.primesBelow_card_eq_primeCounting']
  rfl

lemma three_fourths_log_le_log_nat_div_two {n : ℕ} (hn : 81 ≤ n) :
    (3 / 4 : ℝ) * Real.log n ≤ Real.log (n / 2 : ℕ) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hmpos : (0 : ℝ) < (n / 2 : ℕ) := by exact_mod_cast (by omega : 0 < n / 2)
  have hmge : (n : ℝ) / 3 ≤ (n / 2 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    exact_mod_cast (by omega : n ≤ (n / 2) * 3)
  have hlogn : 4 * Real.log 3 ≤ Real.log n := by
    have hpow : ((3 : ℝ) ^ 4) ≤ n := by norm_num; exact_mod_cast hn
    have := Real.log_le_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ 4) hpow
    rw [Real.log_pow] at this
    norm_num at this ⊢
    exact this
  calc
    (3 / 4 : ℝ) * Real.log n ≤ Real.log n - Real.log 3 := by
      nlinarith
    _ = Real.log ((n : ℝ) / 3) := by
      rw [Real.log_div hnpos.ne' (by norm_num : (3 : ℝ) ≠ 0)]
    _ ≤ Real.log (n / 2 : ℕ) :=
      Real.log_le_log (div_pos hnpos (by norm_num)) hmge

lemma eventually_chebyshev_error_small :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n + 1 : ℕ) + 2 * Real.sqrt n * Real.log n ≤ (n : ℝ) / 100 := by
  have hsmall :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound
      (by norm_num : (0 : ℝ) < 1 / 400)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    Filter.eventually_ge_atTop 2] with n hlog hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hsqrtnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrpow : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt n := by
    exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  rw [Real.norm_of_nonneg hlognonneg, hrpow,
    Real.norm_of_nonneg hsqrtnonneg] at hlog
  have hlogsucc : Real.log (n + 1 : ℕ) ≤ 2 * Real.log n := by
    have hsquare : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (by nlinarith : n + 1 ≤ n ^ 2)
    calc
      Real.log (n + 1 : ℕ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hsquare
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hsqrtone : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnreal
  have hsqrtlog : Real.sqrt n * Real.log n ≤ (n : ℝ) / 400 := by
    calc
      Real.sqrt n * Real.log n ≤ Real.sqrt n * ((1 / 400 : ℝ) * Real.sqrt n) := by
        exact mul_le_mul_of_nonneg_left hlog hsqrtnonneg
      _ = (Real.sqrt n * Real.sqrt n) / 400 := by ring
      _ = (n : ℝ) / 400 := by
        rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ n)]
  calc
    Real.log (n + 1 : ℕ) + 2 * Real.sqrt n * Real.log n ≤
        2 * Real.log n + 2 * Real.sqrt n * Real.log n := by gcongr
    _ ≤ 4 * (Real.sqrt n * Real.log n) := by
      nlinarith [mul_le_mul_of_nonneg_right hsqrtone hlognonneg]
    _ ≤ (n : ℝ) / 100 := by nlinarith

lemma upperHalfPrime_factorization_factorial {n p : ℕ} (hn : 5 ≤ n)
    (hp : p ∈ upperHalfPrimes n) : n.factorial.factorization p = 1 := by
  have hdata := mem_upperHalfPrimes.mp hp
  have hpprime : p.Prime := hdata.1
  have hp3 : 3 ≤ p := by omega
  have hnpow : n < p ^ 2 := by
    rw [pow_two]
    have hn2p : n < 2 * p := by omega
    have h2psq : 2 * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hlog : Nat.log p n < 2 :=
    (Nat.log_lt_iff_lt_pow hpprime.one_lt (by omega)).mpr hnpow
  rw [Nat.factorization_factorial hpprime hlog]
  simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, pow_one]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

lemma log_five_four_le_upperHalfPrime_gap {n p : ℕ} (hn : 0 < n)
    (hratio : ratio n ≤ (2 : ℝ) / 5) (hp : p ∈ upperHalfPrimes n) :
    Real.log ((5 : ℝ) / 4) ≤ Real.log p - Real.log (t n) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : (0 : ℝ) < t n := by exact_mod_cast t_pos hn
  have htbound : (t n : ℝ) ≤ ((2 : ℝ) / 5) * n := by
    rw [ratio] at hratio
    exact (div_le_iff₀ hnreal).mp hratio
  have hpdata := mem_upperHalfPrimes.mp hp
  have hn2p_nat : n < 2 * p := by omega
  have hn2p : (n : ℝ) < 2 * p := by exact_mod_cast hn2p_nat
  have hfive : ((5 : ℝ) / 4) * t n ≤ p := by
    nlinarith
  calc
    Real.log ((5 : ℝ) / 4) =
        Real.log (((5 : ℝ) / 4) * t n) - Real.log (t n) := by
          rw [Real.log_mul (by norm_num : ((5 : ℝ) / 4) ≠ 0) htpos.ne']
          ring
    _ ≤ Real.log p - Real.log (t n) := by
      exact sub_le_sub_right
        (Real.log_le_log (mul_pos (by norm_num) htpos) hfive) _

lemma upperHalfPrimes_obstruction {n : ℕ} (hn : 5 ≤ n)
    (hratio : ratio n ≤ (2 : ℝ) / 5) :
    ((upperHalfPrimes n).card : ℝ) * Real.log ((5 : ℝ) / 4) ≤
      Real.log n.factorial - (n : ℝ) * Real.log (t n) := by
  obtain ⟨_htpos, a, ha, hta⟩ := t_feasible (by omega : 0 < n)
  have hP : ∀ p ∈ upperHalfPrimes n, p.Prime := fun p hp ↦
    (mem_upperHalfPrimes.mp hp).1
  have hbound := prime_excess_le_representation_excess ha (t_pos (by omega)) hta
    (upperHalfPrimes n) hP (fun p hp ↦ upperHalfPrime_factorization_factorial hn hp)
  calc
    ((upperHalfPrimes n).card : ℝ) * Real.log ((5 : ℝ) / 4) =
        ∑ _p ∈ upperHalfPrimes n, Real.log ((5 : ℝ) / 4) := by simp
    _ ≤ ∑ p ∈ upperHalfPrimes n, (Real.log p - Real.log (t n)) := by
      exact Finset.sum_le_sum fun p hp ↦
        log_five_four_le_upperHalfPrime_gap (by omega) hratio hp
    _ ≤ Real.log n.factorial - (n : ℝ) * Real.log (t n) := hbound

/-- A slightly wider interval than `upperHalfPrimes`.  The cutoff `9n/20`
is chosen so that elementary Chebyshev bounds already prove this set has
cardinality comparable to `n / log n`, while its primes still exceed the
eventual bound `2n/5` for `t(n)`. -/
def largePrimes (n : ℕ) : Finset ℕ :=
  (n + 1).primesBelow \ (9 * n / 20 + 1).primesBelow

lemma mem_largePrimes {n p : ℕ} :
    p ∈ largePrimes n ↔ p.Prime ∧ 9 * n / 20 < p ∧ p ≤ n := by
  simp only [largePrimes, Finset.mem_sdiff, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpn, hpprime⟩, hpnot⟩
    have hnotlt : ¬p < 9 * n / 20 + 1 := fun h ↦ hpnot ⟨h, hpprime⟩
    exact ⟨hpprime, by omega, by omega⟩
  · rintro ⟨hpprime, hcut, hpn⟩
    refine ⟨⟨by omega, hpprime⟩, ?_⟩
    rintro ⟨hplt, _⟩
    omega

lemma card_largePrimes (n : ℕ) :
    (largePrimes n).card =
      Nat.primeCounting n - Nat.primeCounting (9 * n / 20) := by
  have hsub : (9 * n / 20 + 1).primesBelow ⊆ (n + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr
      ⟨(Nat.mem_primesBelow.mp hp).1.trans_le (by omega), (Nat.mem_primesBelow.mp hp).2⟩
  rw [largePrimes, Finset.card_sdiff_of_subset hsub,
    Nat.primesBelow_card_eq_primeCounting',
    Nat.primesBelow_card_eq_primeCounting']
  rfl

lemma sum_largePrimes_log (n : ℕ) :
    (∑ p ∈ largePrimes n, Real.log p) =
      Chebyshev.theta n - Chebyshev.theta (9 * n / 20 : ℕ) := by
  have hsub : (9 * n / 20 + 1).primesBelow ⊆ (n + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr
      ⟨(Nat.mem_primesBelow.mp hp).1.trans_le (by omega), (Nat.mem_primesBelow.mp hp).2⟩
  have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ Real.log p)
  have htheta_n : Chebyshev.theta n =
      ∑ p ∈ (n + 1).primesBelow, Real.log p := by
    simpa [Nat.primesLE] using Chebyshev.theta_eq_sum_primesLE_log n
  have htheta_cut : Chebyshev.theta (9 * n / 20 : ℕ) =
      ∑ p ∈ (9 * n / 20 + 1).primesBelow, Real.log p := by
    simpa [Nat.primesLE] using
      Chebyshev.theta_eq_sum_primesLE_log (9 * n / 20)
  rw [largePrimes]
  linarith [hsum, htheta_n, htheta_cut]

lemma theta_sub_cutoff_lower {n : ℕ} (hn : 10 ≤ n)
    (herr : Real.log (n + 1 : ℕ) + 2 * Real.sqrt n * Real.log n ≤
      (n : ℝ) / 100) :
    (n : ℝ) / 20 ≤
      Chebyshev.theta n - Chebyshev.theta (9 * n / 20 : ℕ) := by
  have htheta_n := Chebyshev.theta_ge n
  have hmcast : ((9 * n / 20 : ℕ) : ℝ) ≤ (9 / 20 : ℝ) * n := by
    calc
      ((9 * n / 20 : ℕ) : ℝ) ≤ ((9 * n : ℕ) : ℝ) / 20 := Nat.cast_div_le
      _ = (9 / 20 : ℝ) * n := by norm_num; ring
  have hlog2 : (3 / 5 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htheta_cut : Chebyshev.theta (9 * n / 20 : ℕ) ≤
      (9 / 10 : ℝ) * n * Real.log 2 := by
    calc
      Chebyshev.theta (9 * n / 20 : ℕ) ≤
          Real.log 4 * (9 * n / 20 : ℕ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = 2 * Real.log 2 * (9 * n / 20 : ℕ) := by
        rw [Real.log_four_eq]
      _ ≤ (9 / 10 : ℝ) * n * Real.log 2 := by
        have hlognonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have herr' : Real.log ((n : ℝ) + 1) + 2 * Real.sqrt n * Real.log n ≤
      (n : ℝ) / 100 := by simpa using herr
  have htheta_n' :
      (n : ℝ) * Real.log 2 - (n : ℝ) / 100 ≤ Chebyshev.theta n := by
    linarith
  have hdiff :
      (1 / 10 : ℝ) * n * Real.log 2 - (n : ℝ) / 100 ≤
        Chebyshev.theta n - Chebyshev.theta (9 * n / 20 : ℕ) := by
    linarith
  have hmain : (3 / 50 : ℝ) * n ≤ (1 / 10 : ℝ) * n * Real.log 2 := by
    calc
      (3 / 50 : ℝ) * n = (n / 10) * (3 / 5) := by ring
      _ ≤ (n / 10) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = (1 / 10 : ℝ) * n * Real.log 2 := by ring
  linarith

lemma sum_largePrimes_log_le (n : ℕ) :
    (∑ p ∈ largePrimes n, Real.log p) ≤
      ((largePrimes n).card : ℝ) * Real.log n := by
  calc
    (∑ p ∈ largePrimes n, Real.log p) ≤
        ∑ _p ∈ largePrimes n, Real.log n := by
      exact Finset.sum_le_sum fun p hp ↦
        Real.log_le_log (by exact_mod_cast (mem_largePrimes.mp hp).1.pos)
          (by exact_mod_cast (mem_largePrimes.mp hp).2.2)
    _ = ((largePrimes n).card : ℝ) * Real.log n := by simp

lemma eventually_largePrimes_card_lower :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) / (20 * Real.log n) ≤ (largePrimes n).card := by
  filter_upwards [eventually_chebyshev_error_small,
    Filter.eventually_ge_atTop 10] with n herr hn
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have htheta := theta_sub_cutoff_lower hn herr
  rw [← sum_largePrimes_log n] at htheta
  have hsum := sum_largePrimes_log_le n
  rw [div_le_iff₀ (mul_pos (by norm_num) hlogpos)]
  nlinarith

lemma neg_log_one_sub_le_two_mul {z : ℝ} (hz0 : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    -Real.log (1 - z) ≤ 2 * z := by
  have hden : 0 < 1 - z := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hden
  have hfrac : z / (1 - z) ≤ 2 * z := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hzhalf)]
  have hinv : (1 - z)⁻¹ - 1 = z / (1 - z) := by
    field_simp
    ring
  rw [← hinv] at hfrac
  linarith

lemma eventually_stirling_error_le_large_prime_scale :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log n / 2 + 1 ≤
        Real.log ((9 : ℝ) / 8) * n / (80 * Real.log n) := by
  have hsq : (fun x : ℝ ↦ Real.log x ^ 2) =o[Filter.atTop] (fun x ↦ x) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 2 (by norm_num))
  have hsmall :
      (fun x : ℝ ↦ Real.log x ^ 2 / 2 + Real.log x) =o[Filter.atTop]
        (fun x ↦ x) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (hsq.const_mul_left ((2 : ℝ)⁻¹)).add Real.isLittleO_log_id_atTop
  have hloggap : 0 < Real.log ((9 : ℝ) / 8) := Real.log_pos (by norm_num)
  have hbound := hsmall.bound (div_pos hloggap (by norm_num : (0 : ℝ) < 80))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound,
    Filter.eventually_ge_atTop 3] with n hnsmall hn
  have hnreal : (0 : ℝ) ≤ n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hleftnonneg : 0 ≤ Real.log (n : ℝ) ^ 2 / 2 + Real.log n := by positivity
  rw [Real.norm_of_nonneg hleftnonneg, Real.norm_of_nonneg hnreal] at hnsmall
  rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 80) hlogpos)]
  nlinarith

lemma largePrime_factorization_factorial_pos {n p : ℕ} (_hn : 10 ≤ n)
    (hp : p ∈ largePrimes n) : 1 ≤ n.factorial.factorization p := by
  have hdata := mem_largePrimes.mp hp
  have hpprime : p.Prime := hdata.1
  exact hpprime.factorization_pos_of_dvd n.factorial_ne_zero
    (Nat.dvd_factorial hpprime.pos hdata.2.2)

lemma log_nine_eight_le_largePrime_gap {n p : ℕ} (hn : 0 < n)
    (hratio : ratio n ≤ (2 : ℝ) / 5) (hp : p ∈ largePrimes n) :
    Real.log ((9 : ℝ) / 8) ≤ Real.log p - Real.log (t n) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : (0 : ℝ) < t n := by exact_mod_cast t_pos hn
  have htbound : (t n : ℝ) ≤ ((2 : ℝ) / 5) * n := by
    rw [ratio] at hratio
    exact (div_le_iff₀ hnreal).mp hratio
  have hpdata := mem_largePrimes.mp hp
  have h9n20p_nat : 9 * n < 20 * p := by omega
  have h9n20p : (9 : ℝ) * n < 20 * p := by exact_mod_cast h9n20p_nat
  have hnine : ((9 : ℝ) / 8) * t n ≤ p := by
    nlinarith
  calc
    Real.log ((9 : ℝ) / 8) =
        Real.log (((9 : ℝ) / 8) * t n) - Real.log (t n) := by
          rw [Real.log_mul (by norm_num : ((9 : ℝ) / 8) ≠ 0) htpos.ne']
          ring
    _ ≤ Real.log p - Real.log (t n) := by
      exact sub_le_sub_right
        (Real.log_le_log (mul_pos (by norm_num) htpos) hnine) _

lemma largePrimes_obstruction {n : ℕ} (hn : 10 ≤ n)
    (hratio : ratio n ≤ (2 : ℝ) / 5) :
    ((largePrimes n).card : ℝ) * Real.log ((9 : ℝ) / 8) ≤
      Real.log n.factorial - (n : ℝ) * Real.log (t n) := by
  obtain ⟨_htpos, a, ha, hta⟩ := t_feasible (by omega : 0 < n)
  have hP : ∀ p ∈ largePrimes n, p.Prime := fun p hp ↦ (mem_largePrimes.mp hp).1
  have hbound := prime_excess_le_representation_excess_of_one_le ha (t_pos (by omega)) hta
    (largePrimes n) hP (fun p hp ↦ largePrime_factorization_factorial_pos hn hp)
    (fun p hp ↦ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9 / 8)).trans
      (log_nine_eight_le_largePrime_gap (by omega) hratio hp))
  calc
    ((largePrimes n).card : ℝ) * Real.log ((9 : ℝ) / 8) =
        ∑ _p ∈ largePrimes n, Real.log ((9 : ℝ) / 8) := by simp
    _ ≤ ∑ p ∈ largePrimes n, (Real.log p - Real.log (t n)) := by
      exact Finset.sum_le_sum fun p hp ↦
        log_nine_eight_le_largePrime_gap (by omega) hratio hp
    _ ≤ Real.log n.factorial - (n : ℝ) * Real.log (t n) := hbound

/-- An explicit positive constant for the second question in Problem 391.
It is intentionally far from optimal; the published coefficient is about
`0.3044`, whereas this proof only uses a fixed interval of large primes. -/
noncomputable def deficitConstant : ℝ :=
  Real.log ((9 : ℝ) / 8) / (80 * Real.exp 1)

lemma deficitConstant_pos : 0 < deficitConstant := by
  exact div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) (Real.exp_pos 1))

theorem eventually_ratio_le_sub_deficit :
    ∀ᶠ n : ℕ in Filter.atTop,
      ratio n ≤ 1 / Real.exp 1 - deficitConstant / Real.log n := by
  let L : ℝ := Real.log ((9 : ℝ) / 8)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hlogtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglarge : ∀ᶠ n : ℕ in Filter.atTop, L / 40 ≤ Real.log n :=
    hlogtop.eventually (Filter.eventually_ge_atTop (L / 40))
  filter_upwards [eventually_ratio_le_two_fifths,
    eventually_largePrimes_card_lower,
    eventually_stirling_error_le_large_prime_scale,
    hloglarge, Filter.eventually_ge_atTop 10] with n hratio hcard herr hloglarge hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  let z : ℝ := Real.exp 1 * deficitConstant / Real.log n
  have hzformula : z = L / (80 * Real.log n) := by
    dsimp [z, deficitConstant, L]
    field_simp
  have hz0 : 0 ≤ z := by rw [hzformula]; positivity
  have hzhalf : z ≤ 1 / 2 := by
    rw [hzformula, div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 80) hlogpos)]
    nlinarith
  have hzden : 0 < 1 - z := by linarith
  have htarget :
      1 / Real.exp 1 - deficitConstant / Real.log n =
        Real.exp (-1) * (1 - z) := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.exp_neg]
    dsimp [z, deficitConstant]
    field_simp
  by_contra hcontra
  have hy : Real.exp (-1) * (1 - z) < ratio n := by
    rw [← htarget]
    exact lt_of_not_ge hcontra
  have hbasepos : 0 < Real.exp (-1) * (1 - z) :=
    mul_pos (Real.exp_pos _) hzden
  have hlogratio :
      Real.log (Real.exp (-1) * (1 - z)) < Real.log (ratio n) :=
    (Real.log_lt_log_iff hbasepos (ratio_pos hnpos)).mpr hy
  have hlogbase :
      Real.log (Real.exp (-1) * (1 - z)) = -1 + Real.log (1 - z) := by
    rw [Real.log_mul (Real.exp_pos _).ne' hzden.ne', Real.log_exp]
  rw [hlogbase] at hlogratio
  have htaylor := neg_log_one_sub_le_two_mul hz0 hzhalf
  have hneglog : -1 - Real.log (ratio n) < 2 * z := by linarith
  have hlogratio_eq :
      Real.log (ratio n) = Real.log (t n) - Real.log n := by
    rw [ratio, Real.log_div (by exact_mod_cast (t_pos hnpos).ne')
      (by exact_mod_cast hnpos.ne')]
  have hfact := log_factorial_le n hnpos
  have hslack_upper :
      Real.log n.factorial - (n : ℝ) * Real.log (t n) ≤
        (n : ℝ) * (-1 - Real.log (ratio n)) +
          (Real.log n / 2 + 1) := by
    nlinarith
  have hobstruction := largePrimes_obstruction hn hratio
  have hlower :
      L * n / (20 * Real.log n) ≤
        Real.log n.factorial - (n : ℝ) * Real.log (t n) := by
    calc
      L * n / (20 * Real.log n) =
          ((n : ℝ) / (20 * Real.log n)) * L := by ring
      _ ≤ ((largePrimes n).card : ℝ) * L :=
        mul_le_mul_of_nonneg_right hcard hL.le
      _ ≤ Real.log n.factorial - (n : ℝ) * Real.log (t n) := by
        simpa [L] using hobstruction
  have hnz :
      (n : ℝ) * (2 * z) = L * n / (40 * Real.log n) := by
    rw [hzformula]
    field_simp
    ring
  have hupper :
      Real.log n.factorial - (n : ℝ) * Real.log (t n) <
        L * n / (20 * Real.log n) := by
    calc
      Real.log n.factorial - (n : ℝ) * Real.log (t n) ≤
          (n : ℝ) * (-1 - Real.log (ratio n)) +
            (Real.log n / 2 + 1) := hslack_upper
      _ < (n : ℝ) * (2 * z) + (Real.log n / 2 + 1) := by
        gcongr
      _ ≤ L * n / (40 * Real.log n) +
          L * n / (80 * Real.log n) := by
        rw [hnz]
        gcongr
      _ < L * n / (20 * Real.log n) := by
        have hscale : 0 < L * n / Real.log n := by positivity
        calc
          L * n / (40 * Real.log n) + L * n / (80 * Real.log n) =
              (3 / 80 : ℝ) * (L * n / Real.log n) := by ring
          _ < (4 / 80 : ℝ) * (L * n / Real.log n) := by gcongr <;> norm_num
          _ = L * n / (20 * Real.log n) := by ring
  exact (not_lt_of_ge hlower hupper)

/-- The second question has a positive answer, in the stronger form that the
logarithmic deficit holds for every sufficiently large `n`. -/
theorem infinitely_many_ratio_le_sub_deficit :
    ∃ c : ℝ, 0 < c ∧
      {n : ℕ | ratio n ≤ 1 / Real.exp 1 - c / Real.log n}.Infinite := by
  refine ⟨deficitConstant, deficitConstant_pos, ?_⟩
  have hevent := eventually_ratio_le_sub_deficit
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  apply Set.infinite_of_forall_exists_gt
  intro a
  let n := max N (a + 1)
  refine ⟨n, ?_, ?_⟩
  · exact hN n (le_max_left _ _)
  · dsimp [n]
    omega

/-! ## The qualitative lower bound

For the limit, a fixed positive logarithmic reserve is enough.  The following
parameters implement the simpler approximate factorization from the first
version of the ACRSTUV argument.  We take a short interval of odd integers just
above `n / exp (1 + δ)`, repeat every member `2 A` times, and later exchange its
large prime factors with those of `n!`.  Here `A = (log n)^3 + O(1)`; hence all
rounding and valuation discrepancies are `o(n)`.
-/

/-- The slowly growing auxiliary scale used in the lower-bound construction. -/
noncomputable def lowerScale (n : ℕ) : ℕ := ⌈Real.log (n : ℝ) ^ 3⌉₊ + 1

lemma lowerScale_pos (n : ℕ) : 0 < lowerScale n := by
  simp [lowerScale]

lemma lowerScale_cast_lower (n : ℕ) :
    Real.log (n : ℝ) ^ 3 + 1 ≤ (lowerScale n : ℝ) := by
  rw [lowerScale, Nat.cast_add, Nat.cast_one]
  exact add_le_add (Nat.le_ceil _) le_rfl

lemma lowerScale_cast_upper {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) :
    (lowerScale n : ℝ) ≤ 3 * Real.log (n : ℝ) ^ 3 := by
  have hnonneg : 0 ≤ Real.log (n : ℝ) ^ 3 := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hpow : 1 ≤ Real.log (n : ℝ) ^ 3 := one_le_pow₀ hlog
  rw [lowerScale, Nat.cast_add, Nat.cast_one]
  linarith

lemma lowerScale_isLittleO_id :
    (fun n : ℕ ↦ (lowerScale n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hlog :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 : ℝ)) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1)).natCast_atTop
  have hscale :
      (fun n : ℕ ↦ (lowerScale n : ℝ)) =O[Filter.atTop]
        (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ (3 : ℝ))]
    simpa [Real.rpow_natCast] using lowerScale_cast_upper hn
  have := hscale.trans_isLittleO hlog
  simpa [Real.rpow_one] using this

lemma tendsto_lowerScale_div :
    Tendsto (fun n : ℕ ↦ (lowerScale n : ℝ) / n) Filter.atTop (nhds 0) :=
  lowerScale_isLittleO_id.tendsto_div_nhds_zero

lemma lowerScale_mul_log_isLittleO_id :
    (fun n : ℕ ↦ (lowerScale n : ℝ) * Real.log (n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hlog :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (4 : ℕ)) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    have hr := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).natCast_atTop
    apply hr.congr'
    · exact Filter.Eventually.of_forall fun n ↦ Real.rpow_natCast (Real.log (n : ℝ)) 4
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hscale :
      (fun n : ℕ ↦ (lowerScale n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
        (fun n : ℕ ↦ Real.log (n : ℝ) ^ (4 : ℕ)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with n hn
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
      simpa [Function.comp_def] using (show (0 : ℝ) ≤ 1 from by norm_num).trans hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlognonneg),
      abs_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ (4 : ℕ))]
    have hs := lowerScale_cast_upper hn
    calc
      (lowerScale n : ℝ) * Real.log (n : ℝ) ≤
          (3 * Real.log (n : ℝ) ^ 3) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hs hlognonneg
      _ = 3 * Real.log (n : ℝ) ^ (4 : ℕ) := by ring
  have := hscale.trans_isLittleO hlog
  simpa [Real.rpow_one] using this

lemma tendsto_lowerScale_mul_log_div :
    Tendsto (fun n : ℕ ↦ (lowerScale n : ℝ) * Real.log (n : ℝ) / n)
      Filter.atTop (nhds 0) := lowerScale_mul_log_isLittleO_id.tendsto_div_nhds_zero

lemma lowerScale_mul_log_sq_isLittleO_id :
    (fun n : ℕ ↦ (lowerScale n : ℝ) * Real.log (n : ℝ) ^ 2)
      =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have hlog :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (5 : ℕ)) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    have hr := (isLittleO_log_rpow_rpow_atTop (5 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).natCast_atTop
    apply hr.congr'
    · exact Filter.Eventually.of_forall fun n ↦
        Real.rpow_natCast (Real.log (n : ℝ)) 5
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hscale :
      (fun n : ℕ ↦ (lowerScale n : ℝ) * Real.log (n : ℝ) ^ 2)
        =O[Filter.atTop] (fun n : ℕ ↦ Real.log (n : ℝ) ^ (5 : ℕ)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with n hn
    have hn' : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [Function.comp_def] using hn
    have hnonneg : 0 ≤ Real.log (n : ℝ) := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),
      abs_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ (5 : ℕ))]
    have hs := lowerScale_cast_upper hn
    calc
      (lowerScale n : ℝ) * Real.log (n : ℝ) ^ 2 ≤
          (3 * Real.log (n : ℝ) ^ 3) * Real.log (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = 3 * Real.log (n : ℝ) ^ (5 : ℕ) := by ring
  have := hscale.trans_isLittleO hlog
  simpa [Real.rpow_one] using this

lemma tendsto_lowerScale_mul_log_sq_div :
    Tendsto (fun n : ℕ ↦
      (lowerScale n : ℝ) * Real.log (n : ℝ) ^ 2 / n)
      Filter.atTop (nhds 0) :=
  lowerScale_mul_log_sq_isLittleO_id.tendsto_div_nhds_zero

lemma tendsto_lowerScale_atTop :
    Tendsto (fun n : ℕ ↦ (lowerScale n : ℝ)) Filter.atTop Filter.atTop := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hlogtop
  filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
    simpa [Function.comp_def] using (show (0 : ℝ) ≤ 1 from by norm_num).trans hn
  have hcube : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := one_le_pow₀ hn
    simpa [pow_succ'] using mul_le_mul_of_nonneg_left hpow hlognonneg
  calc
    Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 3 + 1 :=
      hcube.trans (le_add_of_nonneg_right (by norm_num))
    _ ≤ (lowerScale n : ℝ) := lowerScale_cast_lower n

lemma tendsto_inv_lowerScale :
    Tendsto (fun n : ℕ ↦ ((lowerScale n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_lowerScale_atTop

lemma tendsto_log_div_lowerScale :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / lowerScale n)
      Filter.atTop (nhds 0) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogtop).const_div_atTop 1
  have hnonneg : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ Real.log (n : ℝ) / lowerScale n := by
    filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 0)] with n hn
    exact div_nonneg hn (by exact_mod_cast (lowerScale_pos n).le)
  have hle : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n : ℝ) / lowerScale n ≤
        1 / Real.log (n : ℝ) ^ 2 := by
    filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hn
    have hn' : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [Function.comp_def] using hn
    have hA := lowerScale_cast_lower n
    have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hn'
    have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    rw [div_le_div_iff₀ hApos (sq_pos_of_pos hlogpos)]
    norm_num
    calc
      Real.log (n : ℝ) * Real.log (n : ℝ) ^ 2 =
          Real.log (n : ℝ) ^ 3 := by ring
      _ ≤ Real.log (n : ℝ) ^ 3 + 1 := le_add_of_nonneg_right (by norm_num)
      _ ≤ (lowerScale n : ℝ) := hA
  exact squeeze_zero' hnonneg hle hupper

lemma lowerScale_cube_isLittleO_id :
    (fun n : ℕ ↦ (lowerScale n : ℝ) ^ 3) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hlog :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (9 : ℕ)) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    have hr := (isLittleO_log_rpow_rpow_atTop (9 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).natCast_atTop
    apply hr.congr'
    · exact Filter.Eventually.of_forall fun n ↦ Real.rpow_natCast (Real.log (n : ℝ)) 9
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hcube :
      (fun n : ℕ ↦ (lowerScale n : ℝ) ^ 3) =O[Filter.atTop]
        (fun n : ℕ ↦ Real.log (n : ℝ) ^ (9 : ℕ)) := by
    apply Asymptotics.IsBigO.of_bound 27
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (lowerScale n : ℝ) ^ 3),
      abs_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ (9 : ℕ))]
    have hs := lowerScale_cast_upper hn
    calc
      (lowerScale n : ℝ) ^ 3 ≤ (3 * Real.log (n : ℝ) ^ 3) ^ 3 := by gcongr
      _ = 27 * Real.log (n : ℝ) ^ (9 : ℕ) := by ring
  have := hcube.trans_isLittleO hlog
  simpa [Real.rpow_one] using this

lemma lowerScale_six_isLittleO_id :
    (fun n : ℕ ↦ (lowerScale n : ℝ) ^ 6) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hlog :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (18 : ℕ)) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    have hr := (isLittleO_log_rpow_rpow_atTop (18 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).natCast_atTop
    apply hr.congr'
    · exact Filter.Eventually.of_forall fun n ↦
        Real.rpow_natCast (Real.log (n : ℝ)) 18
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hscale :
      (fun n : ℕ ↦ (lowerScale n : ℝ) ^ 6) =O[Filter.atTop]
        (fun n : ℕ ↦ Real.log (n : ℝ) ^ (18 : ℕ)) := by
    apply Asymptotics.IsBigO.of_bound (3 ^ 6)
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (lowerScale n : ℝ) ^ 6),
      abs_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ (18 : ℕ))]
    have hs := lowerScale_cast_upper hn
    calc
      (lowerScale n : ℝ) ^ 6 ≤ (3 * Real.log (n : ℝ) ^ 3) ^ 6 := by gcongr
      _ = (3 ^ 6 : ℝ) * Real.log (n : ℝ) ^ (18 : ℕ) := by ring
  have := hscale.trans_isLittleO hlog
  simpa [Real.rpow_one] using this

lemma eventually_four_lowerScale_six_le :
    ∀ᶠ n : ℕ in Filter.atTop, 4 * lowerScale n ^ 6 ≤ n := by
  have hsmall := lowerScale_six_isLittleO_id.def (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with n hn hnpos
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (lowerScale n : ℝ) ^ 6),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] at hn
  exact_mod_cast (show (4 : ℝ) * (lowerScale n : ℝ) ^ 6 ≤ n by nlinarith)

lemma tendsto_log_log_div_log_nat :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simpa [Function.comp_def, id] using h

lemma tendsto_log_lowerScale_div_log :
    Tendsto (fun n : ℕ ↦ Real.log (lowerScale n : ℝ) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 3 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := hlogtop.const_div_atTop (Real.log 3)
  have hupperlim : Tendsto
      (fun n : ℕ ↦ Real.log 3 / Real.log (n : ℝ) +
        3 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    convert hconst.add ((tendsto_log_log_div_log_nat.const_mul 3)) using 1 <;> norm_num
  have hbounds : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ Real.log (lowerScale n : ℝ) / Real.log (n : ℝ) ∧
      Real.log (lowerScale n : ℝ) / Real.log (n : ℝ) ≤
        Real.log 3 / Real.log (n : ℝ) +
          3 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
    filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hn
    have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
    have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    have hs := lowerScale_cast_upper hn
    have hlogA : Real.log (lowerScale n : ℝ) ≤
        Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) := by
      calc
        Real.log (lowerScale n : ℝ) ≤
            Real.log (3 * Real.log (n : ℝ) ^ 3) :=
          Real.log_le_log hApos hs
        _ = Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) := by
          rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
            (pow_ne_zero 3 hlogpos.ne'), Real.log_pow]
          norm_num
    constructor
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast lowerScale_pos n)) hlogpos.le
    · rw [div_le_iff₀ hlogpos]
      calc
        Real.log (lowerScale n : ℝ) ≤
            Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) := hlogA
        _ = (Real.log 3 / Real.log (n : ℝ) +
              3 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) *
              Real.log (n : ℝ) := by field_simp
  exact squeeze_zero' (hbounds.mono fun _ h ↦ h.1)
    (hbounds.mono fun _ h ↦ h.2) hupperlim

/-- The cutoff separates the small primes, whose valuation discrepancies are
summable trivially, from the large primes, which occur at most once in each
approximate factor. -/
noncomputable def lowerCutoff (n : ℕ) : ℕ := n / lowerScale n ^ 3

lemma eventually_two_lowerScale_cube_le :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * lowerScale n ^ 3 ≤ n := by
  have hsmall := lowerScale_cube_isLittleO_id.def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with n hn hnpos
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (lowerScale n : ℝ) ^ 3),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] at hn
  exact_mod_cast (show (2 : ℝ) * (lowerScale n : ℝ) ^ 3 ≤ n by nlinarith)

lemma lowerCutoff_lower {n : ℕ} (hlarge : 2 * lowerScale n ^ 3 ≤ n) :
    n ≤ 2 * lowerScale n ^ 3 * lowerCutoff n := by
  let D := lowerScale n ^ 3
  have hD : 0 < D := pow_pos (lowerScale_pos n) _
  have hLtwo : 2 ≤ n / D := (Nat.le_div_iff_mul_le hD).mpr (by
    dsimp [D]
    simpa [mul_comm] using hlarge)
  have hrem : n % D < D := Nat.mod_lt n hD
  have hnlt : n < D * (n / D + 1) := by
    calc
      n = D * (n / D) + n % D := by rw [Nat.div_add_mod]
      _ < D * (n / D) + D := by omega
      _ = D * (n / D + 1) := by ring
  calc
    n ≤ D * (n / D + 1) := hnlt.le
    _ ≤ 2 * D * (n / D) := by nlinarith
    _ = 2 * lowerScale n ^ 3 * lowerCutoff n := by rfl

lemma lowerCutoff_sq_ge {n : ℕ} (hn : 0 < n)
    (hsix : 4 * lowerScale n ^ 6 ≤ n) :
    n ≤ lowerCutoff n ^ 2 := by
  have hA : 1 ≤ lowerScale n := lowerScale_pos n
  have hlarge : 2 * lowerScale n ^ 3 ≤ n := by
    have hcube : lowerScale n ^ 3 ≤ lowerScale n ^ 6 := by
      calc
        lowerScale n ^ 3 ≤ lowerScale n ^ 3 * lowerScale n ^ 3 := by
          exact Nat.le_mul_of_pos_right _ (pow_pos (lowerScale_pos n) 3)
        _ = lowerScale n ^ 6 := by ring
    omega
  have hcutNat := lowerCutoff_lower hlarge
  have hcut : (n : ℝ) ≤
      2 * (lowerScale n : ℝ) ^ 3 * lowerCutoff n := by exact_mod_cast hcutNat
  have hsixReal : 4 * (lowerScale n : ℝ) ^ 6 ≤ (n : ℝ) := by
    exact_mod_cast hsix
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsquare : (n : ℝ) ^ 2 ≤
      (2 * (lowerScale n : ℝ) ^ 3 * lowerCutoff n) ^ 2 := by gcongr
  have hmul : (n : ℝ) ^ 2 ≤
      (n : ℝ) * (lowerCutoff n : ℝ) ^ 2 := by
    calc
      (n : ℝ) ^ 2 ≤
          (2 * (lowerScale n : ℝ) ^ 3 * lowerCutoff n) ^ 2 := hsquare
      _ = (4 * (lowerScale n : ℝ) ^ 6) *
          (lowerCutoff n : ℝ) ^ 2 := by ring
      _ ≤ (n : ℝ) * (lowerCutoff n : ℝ) ^ 2 := by gcongr
  have : (n : ℝ) ≤ (lowerCutoff n : ℝ) ^ 2 := by nlinarith
  exact_mod_cast this

lemma eventually_lowerCutoff_sq_ge :
    ∀ᶠ n : ℕ in Filter.atTop, n ≤ lowerCutoff n ^ 2 := by
  filter_upwards [eventually_four_lowerScale_six_le,
    Filter.eventually_gt_atTop 0] with n hsix hn
  exact lowerCutoff_sq_ge hn hsix

lemma tendsto_log_lowerCutoff_div_log :
    Tendsto (fun n : ℕ ↦ Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ))
      Filter.atTop (nhds 1) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := hlogtop.const_div_atTop (Real.log 2)
  have herr : Tendsto
      (fun n : ℕ ↦ Real.log 2 / Real.log (n : ℝ) +
        3 * (Real.log (lowerScale n : ℝ) / Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    convert hconst.add (tendsto_log_lowerScale_div_log.const_mul 3) using 1 <;> norm_num
  have hlowerlim : Tendsto
      (fun n : ℕ ↦ 1 - (Real.log 2 / Real.log (n : ℝ) +
        3 * (Real.log (lowerScale n : ℝ) / Real.log (n : ℝ))))
      Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.sub herr using 1 <;> norm_num
  have hbounds : ∀ᶠ n : ℕ in Filter.atTop,
      1 - (Real.log 2 / Real.log (n : ℝ) +
          3 * (Real.log (lowerScale n : ℝ) / Real.log (n : ℝ))) ≤
        Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ) ∧
      Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ) ≤ 1 := by
    filter_upwards [eventually_two_lowerScale_cube_le,
      hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hlarge hlog
    have hnpos : 0 < n := by
      have : 0 < 2 * lowerScale n ^ 3 :=
        mul_pos (by norm_num) (pow_pos (lowerScale_pos n) _)
      omega
    have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hlog
    have hLnat : 0 < lowerCutoff n := by
      have hcut := lowerCutoff_lower hlarge
      by_contra hz
      have hzero : lowerCutoff n = 0 := Nat.eq_zero_of_not_pos hz
      have hnzero : n = 0 := by simpa [hzero] using hcut
      exact hnpos.ne' hnzero
    have hLle : lowerCutoff n ≤ n := Nat.div_le_self _ _
    have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    have hDpos : (0 : ℝ) < (lowerScale n : ℝ) ^ 3 := pow_pos hApos _
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hdenpos : (0 : ℝ) < 2 * (lowerScale n : ℝ) ^ 3 :=
      mul_pos (by norm_num) hDpos
    have hquotpos : 0 < (n : ℝ) / (2 * (lowerScale n : ℝ) ^ 3) :=
      div_pos hnreal hdenpos
    have hquotle : (n : ℝ) / (2 * (lowerScale n : ℝ) ^ 3) ≤
        (lowerCutoff n : ℝ) := by
      rw [div_le_iff₀ hdenpos]
      exact_mod_cast (show n ≤ lowerCutoff n * (2 * lowerScale n ^ 3) by
        simpa [mul_comm, mul_left_comm, mul_assoc] using lowerCutoff_lower hlarge)
    have hloglower : Real.log (n : ℝ) - Real.log 2 -
        3 * Real.log (lowerScale n : ℝ) ≤ Real.log (lowerCutoff n : ℝ) := by
      calc
        Real.log (n : ℝ) - Real.log 2 - 3 * Real.log (lowerScale n : ℝ) =
            Real.log ((n : ℝ) / (2 * (lowerScale n : ℝ) ^ 3)) := by
          rw [Real.log_div hnreal.ne' (mul_ne_zero (by norm_num)
            hDpos.ne'),
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
              hDpos.ne', Real.log_pow]
          norm_num
          ring
        _ ≤ Real.log (lowerCutoff n : ℝ) :=
          Real.log_le_log hquotpos hquotle
    constructor
    · rw [le_div_iff₀ hlogpos]
      calc
        (1 - (Real.log 2 / Real.log (n : ℝ) +
            3 * (Real.log (lowerScale n : ℝ) / Real.log (n : ℝ)))) *
              Real.log (n : ℝ) =
            Real.log (n : ℝ) - Real.log 2 -
              3 * Real.log (lowerScale n : ℝ) := by field_simp; ring
        _ ≤ Real.log (lowerCutoff n : ℝ) := hloglower
    · rw [div_le_one hlogpos]
      exact Real.log_le_log (by exact_mod_cast hLnat) (by exact_mod_cast hLle)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim tendsto_const_nhds
    (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2)

lemma tendsto_log_lowerCutoff_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (lowerCutoff n : ℝ)) Filter.atTop Filter.atTop := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod := tendsto_log_lowerCutoff_div_log.pos_mul_atTop (by norm_num) hlogtop
  apply hprod.congr'
  filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hn
  have hn0 : Real.log (n : ℝ) ≠ 0 := (lt_of_lt_of_le (by norm_num) hn).ne'
  change Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ) *
    Real.log (n : ℝ) = Real.log (lowerCutoff n : ℝ)
  field_simp

lemma eventually_two_le_lowerCutoff :
    ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ lowerCutoff n := by
  filter_upwards [tendsto_log_lowerCutoff_atTop.eventually
    (Filter.eventually_ge_atTop 1)] with n hn
  by_contra h
  have hle : lowerCutoff n ≤ 1 := by omega
  interval_cases hL : lowerCutoff n <;> norm_num [hL] at hn

lemma tendsto_mertensError_comp (f : ℕ → ℝ)
    (hlog : Tendsto (fun n ↦ Real.log (f n)) Filter.atTop Filter.atTop)
    (hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ f n) :
    Tendsto (fun n ↦ Mertens.E₂p (f n)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCnonneg, hC⟩ := Mertens.eventually_abs_E₂p_le
  have htop : Tendsto f Filter.atTop Filter.atTop := by
    apply (Real.tendsto_exp_atTop.comp hlog).congr'
    filter_upwards [hlarge] with n hn
    exact Real.exp_log (by linarith)
  have hboundlim : Tendsto (fun n ↦ C / Real.log (f n))
      Filter.atTop (nhds 0) := hlog.const_div_atTop C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have habs : Tendsto (fun n ↦ |Mertens.E₂p (f n)|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ abs_nonneg _)
      _ hboundlim
    exact (htop.eventually hC)
  simpa [Real.norm_eq_abs] using habs

lemma tendsto_mertensError_nat :
    Tendsto (fun n : ℕ ↦ Mertens.E₂p (n : ℝ)) Filter.atTop (nhds 0) := by
  apply tendsto_mertensError_comp (fun n : ℕ ↦ (n : ℝ))
  · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact_mod_cast hn

lemma tendsto_mertensError_lowerCutoff :
    Tendsto (fun n : ℕ ↦ Mertens.E₂p (lowerCutoff n : ℝ))
      Filter.atTop (nhds 0) := by
  apply tendsto_mertensError_comp (fun n : ℕ ↦ (lowerCutoff n : ℝ))
  · exact tendsto_log_lowerCutoff_atTop
  · filter_upwards [eventually_two_le_lowerCutoff] with n hn
    exact_mod_cast hn

lemma tendsto_loglog_sub_lowerCutoff :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) -
      Real.log (Real.log (lowerCutoff n : ℝ))) Filter.atTop (nhds 0) := by
  have hratioLog := tendsto_log_lowerCutoff_div_log.log (by norm_num : (1 : ℝ) ≠ 0)
  have heq : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (Real.log (n : ℝ)) - Real.log (Real.log (lowerCutoff n : ℝ)) =
        -Real.log (Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ)) := by
    filter_upwards [tendsto_log_lowerCutoff_atTop.eventually
        (Filter.eventually_gt_atTop 0),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop 0)] with n hL hn
    have hn' : 0 < Real.log (n : ℝ) := by simpa [Function.comp_def] using hn
    rw [Real.log_div hL.ne' hn'.ne']
    ring
  have hneg : Tendsto
      (fun n : ℕ ↦ -Real.log (Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    convert hratioLog.neg using 1 <;> norm_num
  exact hneg.congr' (heq.mono fun _ h ↦ h.symm)

/-- Cumulative reciprocal prime sum, in the exact form used by Mertens' second
theorem. -/
noncomputable def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 N with p.Prime, 1 / (p : ℝ)

lemma primeReciprocalSum_eq (N : ℕ) :
    primeReciprocalSum N =
      Real.log (Real.log (N : ℝ)) + Mertens.M + Mertens.E₂p (N : ℝ) := by
  simpa [primeReciprocalSum] using Mertens.sum_prime_div_eq (N : ℝ)

lemma tendsto_largePrime_reciprocal_difference :
    Tendsto (fun n : ℕ ↦ primeReciprocalSum n - primeReciprocalSum (lowerCutoff n))
      Filter.atTop (nhds 0) := by
  have h := tendsto_loglog_sub_lowerCutoff.add
    (tendsto_mertensError_nat.sub tendsto_mertensError_lowerCutoff)
  convert h using 1
  · funext n
    rw [primeReciprocalSum_eq, primeReciprocalSum_eq]
    ring
  · ring

/-- Primes above the moving cutoff and at most `n`. -/
def lowerLargePrimes (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (lowerCutoff n) n).filter Nat.Prime

lemma sum_lowerLargePrimes_reciprocal (n : ℕ) :
    ∑ p ∈ lowerLargePrimes n, 1 / (p : ℝ) =
      primeReciprocalSum n - primeReciprocalSum (lowerCutoff n) := by
  have hsub : (Finset.Ioc 0 (lowerCutoff n)).filter Nat.Prime ⊆
      (Finset.Ioc 0 n).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.div_le_self _ _)⟩, hp.2⟩
  have hdiff :
      (Finset.Ioc 0 n).filter Nat.Prime \
          (Finset.Ioc 0 (lowerCutoff n)).filter Nat.Prime = lowerLargePrimes n := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc,
      lowerLargePrimes]
    aesop
    exact right.pos
  rw [← hdiff, primeReciprocalSum, primeReciprocalSum,
    ← Finset.sum_sdiff hsub]
  ring

/-- Number of occurrences of primes above the cutoff in `n!`. -/
def targetLargeCount (n : ℕ) : ℕ :=
  ∑ p ∈ lowerLargePrimes n, n.factorial.factorization p

lemma targetLargeCount_real_bound {n : ℕ} (hn : 0 < n) :
    (targetLargeCount n : ℝ) / n ≤
      2 * (primeReciprocalSum n - primeReciprocalSum (lowerCutoff n)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ p ∈ lowerLargePrimes n,
      (n.factorial.factorization p : ℝ) ≤ 2 * (n : ℝ) / p := by
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpge : 2 ≤ p := hpprime.two_le
    calc
      (n.factorial.factorization p : ℝ) ≤ (n / (p - 1) : ℕ) := by
        exact_mod_cast Nat.factorization_factorial_le_div_pred hpprime n
      _ ≤ (n : ℝ) / (p - 1 : ℕ) := Nat.cast_div_le
      _ ≤ 2 * (n : ℝ) / p := by
        have hpReal : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
        have hpredReal : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
        rw [div_le_div_iff₀ hpredReal hpReal]
        norm_num
        push_cast
        have hpineq : p ≤ 2 * (p - 1) := by omega
        have hpineqReal : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by exact_mod_cast hpineq
        nlinarith
  simp only [targetLargeCount, Nat.cast_sum]
  calc
    (∑ p ∈ lowerLargePrimes n, (n.factorial.factorization p : ℝ)) / n ≤
        (∑ p ∈ lowerLargePrimes n, 2 * (n : ℝ) / p) / n := by
      gcongr with p hp
      exact hterm p hp
    _ = 2 * (∑ p ∈ lowerLargePrimes n, 1 / (p : ℝ)) := by
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
      field_simp [hnreal.ne', (by exact_mod_cast hpprime.ne_zero : (p : ℝ) ≠ 0)]
    _ = 2 * (primeReciprocalSum n - primeReciprocalSum (lowerCutoff n)) := by
      rw [sum_lowerLargePrimes_reciprocal]

lemma tendsto_targetLargeCount_div :
    Tendsto (fun n : ℕ ↦ (targetLargeCount n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact targetLargeCount_real_bound hn
  · convert tendsto_largePrime_reciprocal_difference.const_mul 2 using 1 <;> norm_num

/-- The unique residue class `j` for which `u + 2*j` is divisible by an odd
modulus. -/
noncomputable def oddProgressionResidue (u m : ℕ) : ℕ :=
  ((-(u : ZMod m)) * (2 : ZMod m)⁻¹).val

lemma dvd_oddProgression_iff_modEq {u m j : ℕ} (hm : 0 < m) (hodd : Odd m) :
    m ∣ u + 2 * j ↔ j ≡ oddProgressionResidue u m [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff]
  change ((u + 2 * j : ℕ) : ZMod m) = 0 ↔
    (j : ZMod m) = (oddProgressionResidue u m : ZMod m)
  rw [Nat.cast_add, Nat.cast_mul, oddProgressionResidue, ZMod.natCast_zmod_val]
  change (u : ZMod m) + (2 : ZMod m) * j = 0 ↔
    (j : ZMod m) = -(u : ZMod m) * (2 : ZMod m)⁻¹
  have hunit : (2 : ZMod m) * (2 : ZMod m)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 (Nat.coprime_two_left.mpr hodd)
  have hunit' : (2 : ZMod m)⁻¹ * (2 : ZMod m) = 1 := by
    rw [mul_comm, hunit]
  constructor
  · intro h
    have hmul : (2 : ZMod m) * j = -(u : ZMod m) :=
      eq_neg_of_add_eq_zero_right h
    calc
      (j : ZMod m) = 1 * j := by simp
      _ = ((2 : ZMod m)⁻¹ * 2) * j := by rw [hunit']
      _ = (2 : ZMod m)⁻¹ * ((2 : ZMod m) * j) := by ring
      _ = (2 : ZMod m)⁻¹ * (-(u : ZMod m)) := by rw [hmul]
      _ = -(u : ZMod m) * (2 : ZMod m)⁻¹ := by ring
  · intro h
    rw [h]
    calc
      (u : ZMod m) + 2 * (-(u : ZMod m) * (2 : ZMod m)⁻¹) =
          (u : ZMod m) + -(u : ZMod m) * (2 * (2 : ZMod m)⁻¹) := by ring
      _ = 0 := by rw [hunit]; simp

/-- Number of members of the first `r` terms of an odd-step progression
which are divisible by `m`. -/
def oddProgressionDivisorCount (u r m : ℕ) : ℕ :=
  ({j ∈ Finset.range r | m ∣ u + 2 * j}).card

lemma oddProgressionDivisorCount_eq {u r m : ℕ} (hm : 0 < m) (hodd : Odd m) :
    oddProgressionDivisorCount u r m = r / m +
      if oddProgressionResidue u m % m < r % m then 1 else 0 := by
  rw [oddProgressionDivisorCount, ← Nat.count_eq_card_filter_range]
  simp_rw [dvd_oddProgression_iff_modEq hm hodd]
  exact Nat.count_modEq_card r hm (oddProgressionResidue u m)

lemma oddProgressionDivisorCount_bounds {u r m : ℕ} (hm : 0 < m)
    (hodd : Odd m) :
    r / m ≤ oddProgressionDivisorCount u r m ∧
      oddProgressionDivisorCount u r m ≤ r / m + 1 := by
  rw [oddProgressionDivisorCount_eq hm hodd]
  split_ifs <;> omega

/-- Sum a function over `r` consecutive blocks of length `q`. -/
lemma sum_repeated_blocks {M : Type} [AddCommMonoid M]
    (q r : ℕ) (hq : 0 < q) (f : ℕ → M) :
    (∑ i : Fin (q * r), f (i.1 / q)) = q • (∑ j : Fin r, f j.1) := by
  let e : Fin r × Fin q ≃ Fin (q * r) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm r q))
  rw [← Equiv.sum_comp e]
  rw [Fintype.sum_prod_type]
  have heapply : ∀ (j : Fin r) (s : Fin q), (e (j, s)).1 / q = j.1 := by
    intro j s
    simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv]
    change (s.1 + q * j.1) / q = j.1
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt s.2, zero_add]
  simp_rw [heapply]
  calc
    (∑ j : Fin r, ∑ _s : Fin q, f j.1) = ∑ j : Fin r, q • f j.1 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ = q • (∑ j : Fin r, f j.1) := Finset.sum_nsmul Finset.univ q _

lemma mul_div_block_le (q r m : ℕ) (hq : 0 < q) (hm : 0 < m) :
    q * r / m ≤ q * (r / m) + q := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hm]
  have hrem : r % m < m := Nat.mod_lt r hm
  have hmul : q * (r % m) < q * m := (Nat.mul_lt_mul_left hq).mpr hrem
  calc
    q * r = q * (m * (r / m) + r % m) := by rw [Nat.div_add_mod]
    _ < q * (r / m * m) + q * m := by
      rw [mul_add]
      convert Nat.add_lt_add_left hmul (q * (m * (r / m))) using 1 <;> ring
    _ = (q * (r / m) + q) * m := by ring
    _ < (q * (r / m) + q + 1) * m := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hm

lemma block_count_compare {q r n m C : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hnle : n ≤ q * r) (hlen : q * r < n + q)
    (hClow : r / m ≤ C) (hCup : C ≤ r / m + 1) :
    q * C ≤ n / m + 3 * q ∧ n / m ≤ q * C + q := by
  constructor
  · calc
      q * C ≤ q * (r / m + 1) := Nat.mul_le_mul_left q hCup
      _ = q * (r / m) + q := by ring
      _ ≤ q * r / m + q :=
        Nat.add_le_add_right (Nat.mul_div_le_mul_div_assoc q r m) q
      _ ≤ (n + q) / m + q :=
        Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_of_lt hlen)) q
      _ ≤ n / m + q / m + 1 + q :=
        Nat.add_le_add_right (Nat.add_div_le_div_add_div_add_one n q m) q
      _ ≤ n / m + 3 * q := by
        have hqdiv : q / m ≤ q := Nat.div_le_self q m
        omega
  · calc
      n / m ≤ (q * r) / m := Nat.div_le_div_right hnle
      _ ≤ q * (r / m) + q := mul_div_block_le q r m hq hm
      _ ≤ q * C + q := Nat.add_le_add_right (Nat.mul_le_mul_left q hClow) q

/-- The integer threshold just above `n / exp (1 + δ)`. -/
noncomputable def lowerTarget (δ : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / Real.exp (1 + δ)⌉₊

/-- The least odd integer not smaller than `k`. -/
def oddCeilNat (k : ℕ) : ℕ := if k % 2 = 1 then k else k + 1

lemma oddCeilNat_le_add_one (k : ℕ) : oddCeilNat k ≤ k + 1 := by
  by_cases h : k % 2 = 1 <;> simp [oddCeilNat, h]

lemma le_oddCeilNat (k : ℕ) : k ≤ oddCeilNat k := by
  by_cases h : k % 2 = 1 <;> simp [oddCeilNat, h]

lemma odd_oddCeilNat (k : ℕ) : Odd (oddCeilNat k) := by
  rw [Nat.odd_iff]
  simp only [oddCeilNat]
  split_ifs with h
  · exact h
  · omega

/-- Number of distinct odd values in the approximate factorization. -/
noncomputable def lowerBlocks (n : ℕ) : ℕ :=
  n ⌈/⌉ (2 * lowerScale n)

lemma lowerBlocks_le_div_add_one (n : ℕ) :
    lowerBlocks n ≤ n / lowerScale n + 1 := by
  rw [lowerBlocks, ceilDiv_le_iff_le_mul
    (mul_pos (by norm_num) (lowerScale_pos n))]
  have hmod : n % lowerScale n < lowerScale n :=
    Nat.mod_lt n (lowerScale_pos n)
  have hnlt : n < lowerScale n * (n / lowerScale n + 1) := by
    calc
      n = lowerScale n * (n / lowerScale n) + n % lowerScale n := by
        rw [Nat.div_add_mod]
      _ < lowerScale n * (n / lowerScale n) + lowerScale n := by omega
      _ = lowerScale n * (n / lowerScale n + 1) := by ring
  calc
    n ≤ lowerScale n * (n / lowerScale n + 1) := hnlt.le
    _ ≤ 2 * lowerScale n * (n / lowerScale n + 1) := by
      nlinarith [lowerScale_pos n]

/-- Number of entries before the cleanup step. -/
noncomputable def approximateLength (n : ℕ) : ℕ :=
  2 * lowerScale n * lowerBlocks n

lemma le_approximateLength (n : ℕ) : n ≤ approximateLength n := by
  simpa [approximateLength, lowerBlocks] using
    (le_smul_ceilDiv (b := n)
      (mul_pos (by norm_num) (lowerScale_pos n) : 0 < 2 * lowerScale n))

lemma approximateLength_lt (n : ℕ) :
    approximateLength n < n + 2 * lowerScale n := by
  rw [approximateLength, lowerBlocks, Nat.ceilDiv_eq_add_pred_div]
  have hpos : 0 < 2 * lowerScale n := mul_pos (by norm_num) (lowerScale_pos n)
  have hdiv : (n + 2 * lowerScale n - 1) / (2 * lowerScale n) *
      (2 * lowerScale n) ≤ n + 2 * lowerScale n - 1 :=
    Nat.div_mul_le_self _ _
  have hcomm : 2 * lowerScale n *
      ((n + 2 * lowerScale n - 1) / (2 * lowerScale n)) =
      ((n + 2 * lowerScale n - 1) / (2 * lowerScale n)) *
        (2 * lowerScale n) := by ac_rfl
  rw [hcomm]
  omega

lemma tendsto_approximateLength_div :
    Tendsto (fun n : ℕ ↦ (approximateLength n : ℝ) / n)
      Filter.atTop (nhds 1) := by
  have hlow : ∀ᶠ n : ℕ in Filter.atTop,
      (1 : ℝ) ≤ (approximateLength n : ℝ) / n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    have hcast : (n : ℝ) ≤ approximateLength n := by
      exact_mod_cast le_approximateLength n
    simpa using hcast
  have hupp : ∀ᶠ n : ℕ in Filter.atTop,
      (approximateLength n : ℝ) / n ≤ 1 + 2 * (lowerScale n : ℝ) / n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [div_le_iff₀ (by exact_mod_cast hn)]
    have h := (approximateLength_lt n).le
    have hcast : (approximateLength n : ℝ) ≤
        (n : ℝ) + 2 * lowerScale n := by
      exact_mod_cast h
    calc
      (approximateLength n : ℝ) ≤ (n : ℝ) + 2 * lowerScale n := hcast
      _ = (1 + 2 * (lowerScale n : ℝ) / n) * n := by
        field_simp
        <;> ring
  have hupperlim : Tendsto (fun n : ℕ ↦ 1 + 2 * (lowerScale n : ℝ) / n)
      Filter.atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    convert hone.add (tendsto_lowerScale_div.const_mul 2) using 1
    · funext n
      ring
    · norm_num
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hone hupperlim hlow hupp

/-- The repeated odd interval.  Division by `2 * lowerScale n` makes every
odd value occur exactly that many times. -/
noncomputable def approximateFactor (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : ℕ :=
  oddCeilNat (lowerTarget δ n) +
    2 * (i.1 / (2 * lowerScale n))

lemma approximateFactor_odd (δ : ℝ) (n : ℕ) (i : Fin (approximateLength n)) :
    Odd (approximateFactor δ n i) := by
  rw [Nat.odd_iff]
  simp [approximateFactor, Nat.add_mod]
  simpa [Nat.odd_iff] using odd_oddCeilNat (lowerTarget δ n)

lemma lowerTarget_le_approximateFactor (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) :
    lowerTarget δ n ≤ approximateFactor δ n i := by
  exact (le_oddCeilNat _).trans (Nat.le_add_right _ _)

lemma approximateFactor_pos {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (i : Fin (approximateLength n)) : 0 < approximateFactor δ n i := by
  apply lt_of_lt_of_le (Nat.ceil_pos.mpr ?_) (lowerTarget_le_approximateFactor δ n i)
  exact div_pos (by exact_mod_cast hn) (Real.exp_pos _)

lemma eventually_approximateFactor_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n := by
  let g : ℝ := 1 - 1 / Real.exp (1 + δ)
  have hexpone : 1 < Real.exp (1 + δ) := by
    rw [Real.one_lt_exp_iff]
    linarith
  have hg : 0 < g := by
    dsimp [g]
    rw [sub_pos, div_lt_one (Real.exp_pos _)]
    exact hexpone
  have hlogevent : ∀ᶠ n : ℕ in Filter.atTop,
      max 1 (4 / g) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max 1 (4 / g)))
  filter_upwards [hlogevent,
    Filter.eventually_ge_atTop ⌈(8 / g : ℝ)⌉₊] with n hlog hnlarge
  have hlogone : 1 ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) hlog
  have hloggap : 4 / g ≤ Real.log (n : ℝ) := le_trans (le_max_right _ _) hlog
  have hA : 4 / g ≤ (lowerScale n : ℝ) := by
    calc
      4 / g ≤ Real.log (n : ℝ) := hloggap
      _ ≤ Real.log (n : ℝ) ^ 3 + 1 := by
        nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
      _ ≤ (lowerScale n : ℝ) := lowerScale_cast_lower n
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
  have hdiv : (n : ℝ) / lowerScale n ≤ g * n / 4 := by
    rw [div_le_iff₀ hApos]
    have hgA : 4 ≤ g * (lowerScale n : ℝ) := by
      calc
        4 = g * (4 / g) := by field_simp
        _ ≤ g * lowerScale n := mul_le_mul_of_nonneg_left hA hg.le
    nlinarith
  have hr : (2 : ℝ) * lowerBlocks n ≤ g * n / 2 + 2 := by
    have hblocks := lowerBlocks_le_div_add_one n
    have hblocksReal : (lowerBlocks n : ℝ) ≤
        ((n / lowerScale n : ℕ) : ℝ) + 1 := by exact_mod_cast hblocks
    calc
      (2 : ℝ) * lowerBlocks n ≤
          2 * (((n / lowerScale n : ℕ) : ℝ) + 1) := by gcongr
      _ ≤ 2 * ((n : ℝ) / lowerScale n + 1) := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ g * n / 2 + 2 := by nlinarith
  have htarget_nonneg : 0 ≤ (n : ℝ) / Real.exp (1 + δ) := by positivity
  have htarget : (lowerTarget δ n : ℝ) <
      (n : ℝ) / Real.exp (1 + δ) + 1 := by
    exact Nat.ceil_lt_add_one htarget_nonneg
  have hu : (oddCeilNat (lowerTarget δ n) : ℝ) <
      (1 - g) * n + 2 := by
    have huNat := oddCeilNat_le_add_one (lowerTarget δ n)
    have huReal : (oddCeilNat (lowerTarget δ n) : ℝ) ≤
        (lowerTarget δ n : ℝ) + 1 := by exact_mod_cast huNat
    have hginv : 1 - g = 1 / Real.exp (1 + δ) := by simp [g]
    calc
      (oddCeilNat (lowerTarget δ n) : ℝ) ≤
          (lowerTarget δ n : ℝ) + 1 := huReal
      _ < (n : ℝ) / Real.exp (1 + δ) + 2 := by linarith
      _ = (1 - g) * n + 2 := by rw [hginv]; ring
  have hnlargeReal : 8 / g ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hnlarge)
  have hfour : 4 ≤ g * n / 2 := by
    have : 8 ≤ g * (n : ℝ) := by
      calc
        8 = g * (8 / g) := by field_simp
        _ ≤ g * n := mul_le_mul_of_nonneg_left hnlargeReal hg.le
    nlinarith
  exact_mod_cast (show (oddCeilNat (lowerTarget δ n) : ℝ) +
      2 * lowerBlocks n ≤ n by nlinarith)

lemma approximateFactor_le_interval_top (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) :
    approximateFactor δ n i ≤
      oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n := by
  have hq : 0 < 2 * lowerScale n := mul_pos (by norm_num) (lowerScale_pos n)
  have hi : i.1 / (2 * lowerScale n) < lowerBlocks n := by
    rw [Nat.div_lt_iff_lt_mul hq]
    simpa [approximateLength, mul_comm, mul_left_comm, mul_assoc] using i.2
  simp only [approximateFactor]
  omega

/-- Logarithm of the deliberately slightly-too-long odd interval. -/
noncomputable def approximateLog (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (approximateLength n), Real.log (approximateFactor δ n i : ℝ)

lemma log_lowerTarget_scale {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    Real.log ((n : ℝ) / Real.exp (1 + δ)) =
      Real.log (n : ℝ) - 1 - δ := by
  rw [Real.log_div (by exact_mod_cast hn.ne') (Real.exp_ne_zero _), Real.log_exp]
  ring

lemma approximateFactor_log_lower {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (i : Fin (approximateLength n)) :
    Real.log (n : ℝ) - 1 - δ ≤
      Real.log (approximateFactor δ n i : ℝ) := by
  have hxpos : 0 < (n : ℝ) / Real.exp (1 + δ) :=
    div_pos (by exact_mod_cast hn) (Real.exp_pos _)
  have hxle : (n : ℝ) / Real.exp (1 + δ) ≤
      (approximateFactor δ n i : ℝ) := by
    calc
      (n : ℝ) / Real.exp (1 + δ) ≤ (lowerTarget δ n : ℝ) :=
        Nat.le_ceil _
      _ ≤ (approximateFactor δ n i : ℝ) := by
        exact_mod_cast lowerTarget_le_approximateFactor δ n i
  rw [← log_lowerTarget_scale hn δ]
  exact Real.log_le_log hxpos hxle

lemma approximateFactor_real_upper {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (i : Fin (approximateLength n)) :
    (approximateFactor δ n i : ℝ) ≤
      (n : ℝ) / Real.exp (1 + δ) +
        2 * (n : ℝ) / lowerScale n + 4 := by
  have htarget_nonneg : 0 ≤ (n : ℝ) / Real.exp (1 + δ) := by positivity
  have htarget : (lowerTarget δ n : ℝ) <
      (n : ℝ) / Real.exp (1 + δ) + 1 :=
    Nat.ceil_lt_add_one htarget_nonneg
  have hoddNat := oddCeilNat_le_add_one (lowerTarget δ n)
  have hodd : (oddCeilNat (lowerTarget δ n) : ℝ) ≤
      (lowerTarget δ n : ℝ) + 1 := by exact_mod_cast hoddNat
  have hblocksNat := lowerBlocks_le_div_add_one n
  have hblocks : (lowerBlocks n : ℝ) ≤
      (n : ℝ) / lowerScale n + 1 := by
    calc
      (lowerBlocks n : ℝ) ≤ ((n / lowerScale n : ℕ) : ℝ) + 1 := by
        exact_mod_cast hblocksNat
      _ ≤ (n : ℝ) / lowerScale n + 1 := by
        gcongr
        exact Nat.cast_div_le
  have hfactor : (approximateFactor δ n i : ℝ) ≤
      oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n := by
    exact_mod_cast approximateFactor_le_interval_top δ n i
  have htarget' : (lowerTarget δ n : ℝ) + 1 ≤
      (n : ℝ) / Real.exp (1 + δ) + 2 := by
    linarith
  calc
    (approximateFactor δ n i : ℝ) ≤
        oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n := hfactor
    _ ≤ ((lowerTarget δ n : ℝ) + 1) +
        2 * ((n : ℝ) / lowerScale n + 1) := by gcongr
    _ ≤ ((n : ℝ) / Real.exp (1 + δ) + 2) +
        2 * ((n : ℝ) / lowerScale n + 1) := by gcongr
    _ = (n : ℝ) / Real.exp (1 + δ) +
        2 * (n : ℝ) / lowerScale n + 4 := by ring

lemma approximateFactor_log_upper {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (i : Fin (approximateLength n)) :
    Real.log (approximateFactor δ n i : ℝ) ≤
      Real.log (n : ℝ) - 1 - δ +
        (2 * Real.exp (1 + δ) / lowerScale n +
          4 * Real.exp (1 + δ) / n) := by
  let x : ℝ := (n : ℝ) / Real.exp (1 + δ)
  let c : ℝ := approximateFactor δ n i
  let err : ℝ := 2 * Real.exp (1 + δ) / lowerScale n +
    4 * Real.exp (1 + δ) / n
  have hx : 0 < x := div_pos (by exact_mod_cast hn) (Real.exp_pos _)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast approximateFactor_pos hn i
  have hratio : c / x ≤ 1 + err := by
    have hcup := approximateFactor_real_upper hn δ i
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hAreal : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    dsimp [c, x, err] at ⊢
    rw [div_le_iff₀ hx]
    calc
      (approximateFactor δ n i : ℝ) ≤
          (n : ℝ) / Real.exp (1 + δ) +
            2 * (n : ℝ) / lowerScale n + 4 := hcup
      _ = (1 + (2 * Real.exp (1 + δ) / lowerScale n +
            4 * Real.exp (1 + δ) / n)) *
          ((n : ℝ) / Real.exp (1 + δ)) := by
        field_simp [hnreal.ne', hAreal.ne', Real.exp_ne_zero]
        <;> ring
  have hlogratio : Real.log (c / x) ≤ err :=
    (Real.log_le_sub_one_of_pos (div_pos hc hx)).trans (by linarith)
  have hlogeq : Real.log c - Real.log x = Real.log (c / x) := by
    rw [Real.log_div hc.ne' hx.ne']
  have hxlog : Real.log x = Real.log (n : ℝ) - 1 - δ := by
    exact log_lowerTarget_scale hn δ
  dsimp [c, err] at *
  rw [hxlog] at hlogeq
  linarith

/-- A concrete error term for the logarithmic size of the approximate
factorization.  Every summand tends to zero after normalization. -/
noncomputable def approximateLogError (δ : ℝ) (n : ℕ) : ℝ :=
  2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n +
    (1 + 2 * (lowerScale n : ℝ) / n) *
      (2 * Real.exp (1 + δ) / lowerScale n +
        4 * Real.exp (1 + δ) / n)

lemma tendsto_approximateLogError (δ : ℝ) :
    Tendsto (approximateLogError δ) Filter.atTop (nhds 0) := by
  have hfirst : Tendsto
      (fun n : ℕ ↦ 2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n)
      Filter.atTop (nhds 0) := by
    convert tendsto_lowerScale_mul_log_div.const_mul 2 using 1
    · funext n
      ring
    · norm_num
  have hlen : Tendsto (fun n : ℕ ↦ 1 + 2 * (lowerScale n : ℝ) / n)
      Filter.atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    convert hone.add (tendsto_lowerScale_div.const_mul 2) using 1
    · funext n
      ring
    · norm_num
  have hA : Tendsto
      (fun n : ℕ ↦ 2 * Real.exp (1 + δ) / (lowerScale n : ℝ))
      Filter.atTop (nhds 0) := by
    convert tendsto_inv_lowerScale.const_mul (2 * Real.exp (1 + δ)) using 1
    · funext n
      rw [div_eq_mul_inv]
    · norm_num
  have hn : Tendsto (fun n : ℕ ↦ 4 * Real.exp (1 + δ) / (n : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have herr : Tendsto
      (fun n : ℕ ↦ 2 * Real.exp (1 + δ) / lowerScale n +
        4 * Real.exp (1 + δ) / n) Filter.atTop (nhds 0) := by
    convert hA.add hn using 1 <;> norm_num
  change Tendsto
    (fun n : ℕ ↦
      2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n +
        (1 + 2 * (lowerScale n : ℝ) / n) *
          (2 * Real.exp (1 + δ) / lowerScale n +
            4 * Real.exp (1 + δ) / n)) Filter.atTop (nhds 0)
  simpa only [zero_add, one_mul, mul_zero] using hfirst.add (hlen.mul herr)

lemma approximateLog_normalized_bounds (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ (approximateLog δ n -
          (n : ℝ) * (Real.log (n : ℝ) - 1 - δ)) / n ∧
      (approximateLog δ n -
          (n : ℝ) * (Real.log (n : ℝ) - 1 - δ)) / n ≤
        approximateLogError δ n := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hlogtop.eventually (Filter.eventually_ge_atTop (1 + δ))] with n hn hlog
  let b : ℝ := Real.log (n : ℝ) - 1 - δ
  let err : ℝ := 2 * Real.exp (1 + δ) / lowerScale n +
    4 * Real.exp (1 + δ) / n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hAreal : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
  have hlog' : 1 + δ ≤ Real.log (n : ℝ) := by
    simpa [Function.comp_def] using hlog
  have hbnonneg : 0 ≤ b := by dsimp [b]; linarith
  have hble : b ≤ Real.log (n : ℝ) := by dsimp [b]; linarith
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
    have : (0 : ℝ) < 1 + δ := by linarith
    linarith
  have herrnonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hNlow : (n : ℝ) ≤ approximateLength n := by
    exact_mod_cast le_approximateLength n
  have hNup : (approximateLength n : ℝ) ≤
      (n : ℝ) + 2 * lowerScale n := by
    exact_mod_cast (approximateLength_lt n).le
  have hsumlow : (n : ℝ) * b ≤ approximateLog δ n := by
    calc
      (n : ℝ) * b ≤ (approximateLength n : ℝ) * b :=
        mul_le_mul_of_nonneg_right hNlow hbnonneg
      _ = ∑ _i : Fin (approximateLength n), b := by simp
      _ ≤ approximateLog δ n := by
        rw [approximateLog]
        exact Finset.sum_le_sum fun i _ ↦ approximateFactor_log_lower hn δ i
  have hsumup : approximateLog δ n ≤
      (approximateLength n : ℝ) * (b + err) := by
    rw [approximateLog]
    calc
      (∑ i : Fin (approximateLength n),
          Real.log (approximateFactor δ n i : ℝ)) ≤
          ∑ _i : Fin (approximateLength n), (b + err) := by
        exact Finset.sum_le_sum fun i _ ↦ by
          simpa [b, err] using approximateFactor_log_upper hn δ i
      _ = (approximateLength n : ℝ) * (b + err) := by
        simp
        <;> ring
  have hraw : approximateLog δ n - (n : ℝ) * b ≤
      2 * (lowerScale n : ℝ) * Real.log (n : ℝ) +
        (approximateLength n : ℝ) * err := by
    nlinarith
  have hratio : (approximateLength n : ℝ) / n ≤
      1 + 2 * (lowerScale n : ℝ) / n := by
    rw [div_le_iff₀ hnreal]
    calc
      (approximateLength n : ℝ) ≤ (n : ℝ) + 2 * lowerScale n := hNup
      _ = (1 + 2 * (lowerScale n : ℝ) / n) * n := by
        field_simp [hnreal.ne']
        <;> ring
  constructor
  · exact div_nonneg (sub_nonneg.mpr hsumlow) hnreal.le
  · rw [show approximateLogError δ n =
        2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n +
          (1 + 2 * (lowerScale n : ℝ) / n) * err by
        rfl]
    calc
      (approximateLog δ n - (n : ℝ) * b) / n ≤
          (2 * (lowerScale n : ℝ) * Real.log (n : ℝ) +
            (approximateLength n : ℝ) * err) / n :=
        div_le_div_of_nonneg_right hraw hnreal.le
      _ = 2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n +
          ((approximateLength n : ℝ) / n) * err := by
        field_simp [hnreal.ne']
        <;> ring
      _ ≤ 2 * (lowerScale n : ℝ) * Real.log (n : ℝ) / n +
          (1 + 2 * (lowerScale n : ℝ) / n) * err := by
        gcongr

lemma tendsto_approximateLog_normalized (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦
      (approximateLog δ n -
        (n : ℝ) * (Real.log (n : ℝ) - 1 - δ)) / n)
      Filter.atTop (nhds 0) := by
  have hb := approximateLog_normalized_bounds δ hδ
  exact squeeze_zero' (hb.mono fun _ h ↦ h.1) (hb.mono fun _ h ↦ h.2)
    (tendsto_approximateLogError δ)

/-- Exact prime-adic valuation of the repeated odd interval. -/
lemma sum_approximateFactor_factorization {δ : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    (∑ i : Fin (approximateLength n), (approximateFactor δ n i).factorization p) =
      2 * lowerScale n *
        (∑ e ∈ Finset.Ico 1 (Nat.log p n + 1),
          oddProgressionDivisorCount (oddCeilNat (lowerTarget δ n))
            (lowerBlocks n) (p ^ e)) := by
  let q := 2 * lowerScale n
  let r := lowerBlocks n
  let u := oddCeilNat (lowerTarget δ n)
  have hq : 0 < q := mul_pos (by norm_num) (lowerScale_pos n)
  have hlen : approximateLength n = q * r := by rfl
  have hgroup :
      (∑ i : Fin (approximateLength n), (approximateFactor δ n i).factorization p) =
        q * (∑ j : Fin r, (u + 2 * j.1).factorization p) := by
    change (∑ i : Fin (q * r), (u + 2 * (i.1 / q)).factorization p) =
      q * (∑ j : Fin r, (u + 2 * j.1).factorization p)
    simpa [nsmul_eq_mul] using
      (sum_repeated_blocks q r hq (fun j ↦ (u + 2 * j).factorization p))
  rw [hgroup]
  congr 1
  have hpow : n < p ^ (Nat.log p n + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp.one_lt n
  have hu : 0 < u := by
    apply lt_of_lt_of_le (Nat.ceil_pos.mpr ?_) (le_oddCeilNat _)
    exact div_pos (by exact_mod_cast hn) (Real.exp_pos _)
  have hfactor : ∀ j : Fin r,
      (u + 2 * j.1).factorization p =
        ∑ e ∈ Finset.Ico 1 (Nat.log p n + 1),
          if p ^ e ∣ u + 2 * j.1 then 1 else 0 := by
    intro j
    have hjupper : u + 2 * j.1 ≤ n := by
      dsimp [u, r] at *
      omega
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
      (lt_of_le_of_lt hjupper hpow), Finset.card_filter]
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [oddProgressionDivisorCount, Finset.card_filter,
    Finset.sum_fin_eq_sum_range]
  dsimp [r, u]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Finset.mem_range.mp hx]

/-- For every odd prime, the valuation of the repeated interval and that of
`n!` differ by at most one block per relevant prime power. -/
lemma approximateFactor_factorization_discrepancy {δ : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    let S := ∑ i : Fin (approximateLength n),
      (approximateFactor δ n i).factorization p
    let T := n.factorial.factorization p
    let B := Nat.log p n + 1
    S ≤ T + 6 * lowerScale n * B ∧
      T ≤ S + 2 * lowerScale n * B := by
  let q := 2 * lowerScale n
  let r := lowerBlocks n
  let u := oddCeilNat (lowerTarget δ n)
  let B := Nat.log p n + 1
  let E := Finset.Ico 1 B
  let C : ℕ → ℕ := fun e ↦ oddProgressionDivisorCount u r (p ^ e)
  have hq : 0 < q := mul_pos (by norm_num) (lowerScale_pos n)
  have hnle : n ≤ q * r := by
    simpa [q, r, approximateLength] using le_approximateLength n
  have hlen : q * r < n + q := by
    simpa [q, r, approximateLength] using approximateLength_lt n
  have hterm : ∀ e ∈ E,
      q * C e ≤ n / p ^ e + 3 * q ∧ n / p ^ e ≤ q * C e + q := by
    intro e he
    have hm : 0 < p ^ e := pow_pos hp.pos _
    have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    have hb := oddProgressionDivisorCount_bounds (u := u) (r := r) hm hodd
    exact block_count_compare hq hm hnle hlen hb.1 hb.2
  have hsource :
      (∑ i : Fin (approximateLength n),
          (approximateFactor δ n i).factorization p) = q * ∑ e ∈ E, C e := by
    simpa [q, r, u, B, E, C] using
      sum_approximateFactor_factorization hn hp hupper
  have htarget : n.factorial.factorization p = ∑ e ∈ E, n / p ^ e := by
    have hlog : Nat.log p n < B := by simp [B]
    simpa [E] using Nat.factorization_factorial hp hlog
  have hcard : E.card ≤ B := by
    simp [E]
  dsimp only
  constructor
  · rw [hsource, htarget, Finset.mul_sum]
    calc
      (∑ e ∈ E, q * C e) ≤ ∑ e ∈ E, (n / p ^ e + 3 * q) := by
        exact Finset.sum_le_sum fun e he ↦ (hterm e he).1
      _ = (∑ e ∈ E, n / p ^ e) + E.card * (3 * q) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (∑ e ∈ E, n / p ^ e) + 6 * lowerScale n * B := by
        apply Nat.add_le_add_left
        calc
          E.card * (3 * q) ≤ B * (3 * q) := Nat.mul_le_mul_right _ hcard
          _ = 6 * lowerScale n * B := by dsimp [q]; ring
  · rw [hsource, htarget, Finset.mul_sum]
    calc
      (∑ e ∈ E, n / p ^ e) ≤ ∑ e ∈ E, (q * C e + q) := by
        exact Finset.sum_le_sum fun e he ↦ (hterm e he).2
      _ = (∑ e ∈ E, q * C e) + E.card * q := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (∑ e ∈ E, q * C e) + 2 * lowerScale n * B := by
        apply Nat.add_le_add_left
        calc
          E.card * q ≤ B * q := Nat.mul_le_mul_right _ hcard
          _ = 2 * lowerScale n * B := by dsimp [q]; ring

/-! ### Aggregating the small-prime discrepancy -/

def lowerSmallPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (lowerCutoff n + 1)).filter fun p ↦ p.Prime ∧ p ≠ 2

noncomputable def sourceValuation (δ : ℝ) (n p : ℕ) : ℕ :=
  ∑ i : Fin (approximateLength n), (approximateFactor δ n i).factorization p

noncomputable def sourceSmallLog (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lowerSmallPrimes n, (sourceValuation δ n p : ℝ) * Real.log p

noncomputable def targetSmallLog (n : ℕ) : ℝ :=
  ∑ p ∈ lowerSmallPrimes n,
    (n.factorial.factorization p : ℝ) * Real.log p

noncomputable def smallValuationLogError (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lowerSmallPrimes n,
    |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| * Real.log p

noncomputable def smallDiscrepancyUpper (n : ℕ) : ℝ :=
  6 * ((2 * Real.log (n : ℝ) + 1) * Real.log (n : ℝ) /
      (lowerScale n : ℝ) ^ 2 +
    (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
      Real.log (n : ℝ) / n)

lemma tendsto_smallDiscrepancyUpper :
    Tendsto smallDiscrepancyUpper Filter.atTop (nhds 0) := by
  have hfirst : Tendsto
      (fun n : ℕ ↦ (2 * Real.log (n : ℝ) + 1) * Real.log (n : ℝ) /
        (lowerScale n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have hsq := tendsto_log_div_lowerScale.mul tendsto_log_div_lowerScale
    have hmix := tendsto_log_div_lowerScale.mul tendsto_inv_lowerScale
    have h := (hsq.const_mul 2).add hmix
    convert h using 1
    · funext n
      field_simp
      <;> ring
    · norm_num
  have hsecond : Tendsto
      (fun n : ℕ ↦ (lowerScale n : ℝ) *
        (2 * Real.log (n : ℝ) + 1) * Real.log (n : ℝ) / n)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_lowerScale_mul_log_sq_div.const_mul 2).add
      tendsto_lowerScale_mul_log_div
    convert h using 1
    · funext n
      ring
    · norm_num
  change Tendsto (fun n : ℕ ↦ 6 *
    (((2 * Real.log (n : ℝ) + 1) * Real.log (n : ℝ) /
      (lowerScale n : ℝ) ^ 2) +
    ((lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
      Real.log (n : ℝ) / n))) Filter.atTop (nhds 0)
  simpa using (hfirst.add hsecond).const_mul 6

lemma smallValuationLogError_bound {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    smallValuationLogError δ n / n ≤ smallDiscrepancyUpper n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hterm : ∀ p ∈ lowerSmallPrimes n,
      |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| * Real.log p ≤
        6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
          Real.log (n : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp)
    have hprange := Finset.mem_range.mp hp'.1
    have hpprime := hp'.2.1
    have hpne := hp'.2.2
    have hpleCut : p ≤ lowerCutoff n := by omega
    have hple : p ≤ n := hpleCut.trans (Nat.div_le_self _ _)
    have hlogpnonneg : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
    have hlogple : Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hpprime.pos) (by exact_mod_cast hple)
    have hd := approximateFactor_factorization_discrepancy hn hpprime hpne hupper
    change sourceValuation δ n p ≤
        n.factorial.factorization p + 6 * lowerScale n * (Nat.log p n + 1) ∧
      n.factorial.factorization p ≤
        sourceValuation δ n p + 2 * lowerScale n * (Nat.log p n + 1) at hd
    have hB := natLog_add_one_real_le hn hpprime
    have hB0 : (Nat.log p n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      push_cast at hB
      linarith
    have hU : (0 : ℝ) ≤ 2 * Real.log (n : ℝ) + 1 := by positivity
    have habs : |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| ≤
        6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) := by
      rw [abs_le]
      constructor
      · have hcast : (n.factorial.factorization p : ℝ) ≤
            sourceValuation δ n p +
              2 * lowerScale n * (Nat.log p n + 1) := by exact_mod_cast hd.2
        have hnonnegB : (0 : ℝ) ≤ Nat.log p n + 1 := by positivity
        have hA : (0 : ℝ) ≤ lowerScale n := Nat.cast_nonneg _
        have herror : 2 * (lowerScale n : ℝ) * (Nat.log p n + 1) ≤
            6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) := by
          calc
            2 * (lowerScale n : ℝ) * (Nat.log p n + 1) ≤
                2 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) := by
              gcongr
            _ ≤ 6 * (lowerScale n : ℝ) *
                (2 * Real.log (n : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_right (by nlinarith) hU
        linarith
      · have hcast : (sourceValuation δ n p : ℝ) ≤
            n.factorial.factorization p +
              6 * lowerScale n * (Nat.log p n + 1) := by exact_mod_cast hd.1
        have hA : (0 : ℝ) ≤ lowerScale n := Nat.cast_nonneg _
        have herror : 6 * (lowerScale n : ℝ) * (Nat.log p n + 1) ≤
            6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) := by
          gcongr
        linarith
    calc
      |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| * Real.log p ≤
          (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1)) *
            Real.log p := mul_le_mul_of_nonneg_right habs hlogpnonneg
      _ ≤ 6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
          Real.log n := by gcongr
  have hsum : smallValuationLogError δ n ≤
      ((lowerCutoff n + 1 : ℕ) : ℝ) *
        (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
          Real.log (n : ℝ)) := by
    rw [smallValuationLogError]
    calc
      (∑ p ∈ lowerSmallPrimes n,
          |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| * Real.log p) ≤
          ∑ _p ∈ lowerSmallPrimes n,
            (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
              Real.log (n : ℝ)) := Finset.sum_le_sum hterm
      _ = ((lowerSmallPrimes n).card : ℝ) *
          (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
            Real.log (n : ℝ)) := by simp
      _ ≤ ((lowerCutoff n + 1 : ℕ) : ℝ) *
          (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
            Real.log (n : ℝ)) := by
        gcongr
        have hc := Finset.card_filter_le
          (Finset.range (lowerCutoff n + 1)) (fun p ↦ p.Prime ∧ p ≠ 2)
        have hc' : (lowerSmallPrimes n).card ≤ lowerCutoff n + 1 := by
          simpa [lowerSmallPrimes] using hc
        exact_mod_cast hc'
  have hL : (lowerCutoff n : ℝ) ≤
      (n : ℝ) / (lowerScale n : ℝ) ^ 3 := by
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := lowerScale n ^ 3)
    have hpow : ((lowerScale n ^ 3 : ℕ) : ℝ) =
        (lowerScale n : ℝ) ^ 3 := by norm_num
    rw [hpow] at h
    simpa [lowerCutoff] using h
  have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
  have hcore_nonneg : 0 ≤ (2 * Real.log (n : ℝ) + 1) * Real.log (n : ℝ) := by
    positivity
  rw [div_le_iff₀ hnreal]
  calc
    smallValuationLogError δ n ≤
        ((lowerCutoff n + 1 : ℕ) : ℝ) *
          (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
            Real.log (n : ℝ)) := hsum
    _ ≤ ((n : ℝ) / (lowerScale n : ℝ) ^ 3 + 1) *
          (6 * (lowerScale n : ℝ) * (2 * Real.log (n : ℝ) + 1) *
            Real.log (n : ℝ)) := by
      push_cast
      gcongr
    _ = smallDiscrepancyUpper n * n := by
      rw [smallDiscrepancyUpper]
      field_simp [hnreal.ne', hApos.ne']
      <;> ring

lemma tendsto_smallValuationLogError (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ smallValuationLogError δ n / n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦
      div_nonneg (Finset.sum_nonneg fun p _ ↦
        mul_nonneg (abs_nonneg _) (Real.log_nonneg (by
          have hp := (Finset.mem_filter.mp (show p ∈ lowerSmallPrimes n from ‹_›)).2.1
          exact_mod_cast hp.one_lt.le))) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_approximateFactor_upper δ hδ] with n hn hu
    exact smallValuationLogError_bound hn hu
  · exact tendsto_smallDiscrepancyUpper

noncomputable def sourceLargeLog (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lowerLargePrimes n, (sourceValuation δ n p : ℝ) * Real.log p

noncomputable def targetLargeLog (n : ℕ) : ℝ :=
  ∑ p ∈ lowerLargePrimes n,
    (n.factorial.factorization p : ℝ) * Real.log p

lemma log_nat_eq_sum_factorization_range {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    Real.log (a : ℝ) =
      ∑ p ∈ Finset.range (n + 1), (a.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    have hpFactors : p ∈ a.primeFactors := by simpa using hp
    have hpData := (Nat.mem_primeFactors.mp hpFactors)
    have hpa : p ≤ a := Nat.le_of_dvd ha hpData.2.1
    simp only [Finset.mem_range]
    omega
  · intro p hpRange hpNot
    have hz : a.factorization p = 0 := Finsupp.notMem_support_iff.mp hpNot
    simp [hz]

lemma approximateLog_eq_factorization_sum {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    approximateLog δ n =
      ∑ p ∈ Finset.range (n + 1), (sourceValuation δ n p : ℝ) * Real.log p := by
  rw [approximateLog]
  have hfactor : ∀ i : Fin (approximateLength n),
      Real.log (approximateFactor δ n i : ℝ) =
        ∑ p ∈ Finset.range (n + 1),
          ((approximateFactor δ n i).factorization p : ℝ) * Real.log p := by
    intro i
    apply log_nat_eq_sum_factorization_range (approximateFactor_pos hn i)
    exact (approximateFactor_le_interval_top δ n i).trans hupper
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [sourceValuation, Nat.cast_sum]
  rw [Finset.sum_mul]

lemma factorial_log_eq_factorization_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Finset.range (n + 1),
        (n.factorial.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    have hpne : n.factorial.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    have hpprime : p.Prime := by
      by_contra hnp
      exact hpne (Nat.factorization_eq_zero_of_not_prime _ hnp)
    have hpn : p ≤ n := by
      by_contra h
      have hz := Nat.factorization_factorial_eq_zero_of_lt (Nat.lt_of_not_ge h)
      exact hpne hz
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hpn)
  · intro p hpRange hpNot
    have hz : n.factorial.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNot
    simp [hz]

lemma sourceValuation_two_eq_zero (δ : ℝ) (n : ℕ) :
    sourceValuation δ n 2 = 0 := by
  rw [sourceValuation]
  apply Finset.sum_eq_zero
  intro i hi
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have hev : Even (approximateFactor δ n i) := even_iff_two_dvd.mpr hd
  exact (Nat.not_even_iff_odd.2 (approximateFactor_odd δ n i)) hev

lemma small_large_subset_range {n : ℕ} :
    lowerSmallPrimes n ∪ lowerLargePrimes n ⊆ Finset.range (n + 1) := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hprange := (Finset.mem_filter.mp hp).1
    have hple : p ≤ lowerCutoff n := by
      have := Finset.mem_range.mp hprange
      omega
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hple.trans (Nat.div_le_self _ _)))
  · have hpIoc := (Finset.mem_filter.mp hp).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hpIoc).2)

lemma disjoint_small_large (n : ℕ) :
    Disjoint (lowerSmallPrimes n) (lowerLargePrimes n) := by
  rw [Finset.disjoint_left]
  intro p hps hpl
  have hsrange := (Finset.mem_filter.mp hps).1
  have hlrange := (Finset.mem_filter.mp hpl).1
  have hs : p ≤ lowerCutoff n := by
    have := Finset.mem_range.mp hsrange
    omega
  have hl := (Finset.mem_Ioc.mp hlrange).1
  omega

lemma source_factorization_sum_split {δ : ℝ} {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ Finset.range (n + 1),
        (sourceValuation δ n p : ℝ) * Real.log p) =
      sourceSmallLog δ n + sourceLargeLog δ n := by
  rw [sourceSmallLog, sourceLargeLog, ← Finset.sum_union (disjoint_small_large n)]
  apply (Finset.sum_subset (small_large_subset_range (n := n)) ?_).symm
  intro p hpRange hpNot
  have hpNotUnion : p ∉ lowerSmallPrimes n ∪ lowerLargePrimes n := hpNot
  by_cases hpprime : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      simp [sourceValuation_two_eq_zero]
    · have hple : p ≤ n := by
        have := Finset.mem_range.mp hpRange
        omega
      by_cases hpL : p ≤ lowerCutoff n
      · have hps : p ∈ lowerSmallPrimes n := by
          simp [lowerSmallPrimes, hpprime, hp2, hpL]
        exact (hpNotUnion (Finset.mem_union_left _ hps)).elim
      · have hpl : p ∈ lowerLargePrimes n := by
          simp [lowerLargePrimes, hpprime, hple, Nat.lt_of_not_ge hpL]
        exact (hpNotUnion (Finset.mem_union_right _ hpl)).elim
  · have hz : sourceValuation δ n p = 0 := by
      rw [sourceValuation]
      exact Finset.sum_eq_zero fun i _ ↦
        Nat.factorization_eq_zero_of_not_prime _ hpprime
    simp [hz]

lemma target_factorization_sum_split (n : ℕ) (hL2 : 2 ≤ lowerCutoff n) :
    (∑ p ∈ Finset.range (n + 1),
        (n.factorial.factorization p : ℝ) * Real.log p) =
      (n.factorial.factorization 2 : ℝ) * Real.log 2 +
        targetSmallLog n + targetLargeLog n := by
  rw [targetSmallLog, targetLargeLog, add_assoc,
    ← Finset.sum_union (disjoint_small_large n)]
  have hsub := small_large_subset_range (n := n)
  have htwoMem : 2 ∈ Finset.range (n + 1) ↔ 2 ≤ n := by simp
  by_cases hn2 : 2 ≤ n
  · have htwo : 2 ∈ Finset.range (n + 1) := htwoMem.mpr hn2
    have htwoNot : 2 ∉ lowerSmallPrimes n ∪ lowerLargePrimes n := by
      simp [lowerSmallPrimes, lowerLargePrimes,
        show ¬ lowerCutoff n < 2 by omega]
    change (∑ p ∈ Finset.range (n + 1),
        (n.factorial.factorization p : ℝ) * Real.log p) =
      ((n.factorial.factorization 2 : ℝ) * Real.log 2) +
        ∑ p ∈ lowerSmallPrimes n ∪ lowerLargePrimes n,
          (n.factorial.factorization p : ℝ) * Real.log p
    have hsubInsert : insert 2 (lowerSmallPrimes n ∪ lowerLargePrimes n) ⊆
        Finset.range (n + 1) := by
      intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact htwo
      · exact hsub hp
    have hzero : ∀ p ∈ Finset.range (n + 1),
        p ∉ insert 2 (lowerSmallPrimes n ∪ lowerLargePrimes n) →
        (n.factorial.factorization p : ℝ) * Real.log p = 0 := by
      intro p hpRange hpNot
      by_cases hpprime : p.Prime
      · by_cases hp2 : p = 2
        · exact (hpNot (by simp [hp2])).elim
        · have hple : p ≤ n := by
            have := Finset.mem_range.mp hpRange
            omega
          by_cases hpL : p ≤ lowerCutoff n
          · have hps : p ∈ lowerSmallPrimes n := by
              simp [lowerSmallPrimes, hpprime, hp2, hpL]
            exact (hpNot (by simp [hps])).elim
          · have hpl : p ∈ lowerLargePrimes n := by
              simp [lowerLargePrimes, hpprime, hple, Nat.lt_of_not_ge hpL]
            exact (hpNot (by simp [hpl])).elim
      · simp [Nat.factorization_eq_zero_of_not_prime _ hpprime]
    calc
      (∑ p ∈ Finset.range (n + 1),
          (n.factorial.factorization p : ℝ) * Real.log p) =
          ∑ p ∈ insert 2 (lowerSmallPrimes n ∪ lowerLargePrimes n),
            (n.factorial.factorization p : ℝ) * Real.log p :=
        (Finset.sum_subset hsubInsert hzero).symm
      _ = (n.factorial.factorization 2 : ℝ) * Real.log 2 +
          ∑ p ∈ lowerSmallPrimes n ∪ lowerLargePrimes n,
            (n.factorial.factorization p : ℝ) * Real.log p := by
        rw [Finset.sum_insert htwoNot]
        norm_num
  · have hnlt : n < 2 := Nat.lt_of_not_ge hn2
    have hfact : n.factorial.factorization 2 = 0 :=
      Nat.factorization_factorial_eq_zero_of_lt hnlt
    rw [hfact]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    apply (Finset.sum_subset hsub ?_).symm
    intro p hpRange hpNot
    have hpLe : p ≤ n := by
      have := Finset.mem_range.mp hpRange
      omega
    have hpLt : p < 2 := hpLe.trans_lt hnlt
    have hpNotPrime : ¬ p.Prime := by
      intro hp
      exact (not_lt_of_ge hp.two_le) hpLt
    simp [Nat.factorization_eq_zero_of_not_prime _ hpNotPrime]

lemma largeLog_difference_identity {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    sourceLargeLog δ n - targetLargeLog n =
      approximateLog δ n - Real.log n.factorial +
        (n.factorial.factorization 2 : ℝ) * Real.log 2 -
        (sourceSmallLog δ n - targetSmallLog n) := by
  have hs := approximateLog_eq_factorization_sum hn hupper
  rw [source_factorization_sum_split hn] at hs
  have ht := factorial_log_eq_factorization_sum n
  rw [target_factorization_sum_split n hL2] at ht
  linarith

lemma sourceSmall_sub_targetSmall_le_error (δ : ℝ) (n : ℕ) :
    sourceSmallLog δ n - targetSmallLog n ≤ smallValuationLogError δ n := by
  rw [sourceSmallLog, targetSmallLog, smallValuationLogError,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlognonneg : 0 ≤ Real.log (p : ℝ) := by
    have hpprime := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
  rw [← sub_mul]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) hlognonneg

lemma factorial_two_valuation_real_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) - (2 * Real.log (n : ℝ) + 1) ≤
      (n.factorial.factorization 2 : ℝ) := by
  have hlogNat : Nat.log 2 n + 1 ≤ n := by
    have hlt := Nat.log_lt_self 2 (by omega : n ≠ 0)
    omega
  have hval := factorial_two_valuation_lower n
  have hcast : ((n - (Nat.log 2 n + 1) : ℕ) : ℝ) ≤
      n.factorial.factorization 2 := by exact_mod_cast hval
  rw [Nat.cast_sub hlogNat] at hcast
  have hB := natLog_add_one_real_le (by omega : 0 < n) Nat.prime_two
  push_cast at hB hcast
  linarith

lemma tendsto_log_div_nat :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, id] using h

noncomputable def largeSurplusError (δ : ℝ) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) / 2 + 1) +
    (2 * Real.log (n : ℝ) + 1) * Real.log 2 +
    smallValuationLogError δ n

lemma tendsto_largeSurplusError_div (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ largeSurplusError δ n / n)
      Filter.atTop (nhds 0) := by
  have hone : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
  have hfirst : Tendsto (fun n : ℕ ↦
      (Real.log (n : ℝ) / 2 + 1) / n) Filter.atTop (nhds 0) := by
    have h := (tendsto_log_div_nat.div_const 2).add hone
    convert h using 1
    · funext n
      ring
    · norm_num
  have hsecond : Tendsto (fun n : ℕ ↦
      ((2 * Real.log (n : ℝ) + 1) * Real.log 2) / n)
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_log_div_nat.const_mul 2).add hone).mul_const (Real.log 2)
    convert h using 1
    · funext n
      ring
    · norm_num
  change Tendsto (fun n : ℕ ↦
    ((Real.log (n : ℝ) / 2 + 1) +
      (2 * Real.log (n : ℝ) + 1) * Real.log 2 +
      smallValuationLogError δ n) / n) Filter.atTop (nhds 0)
  have h := hfirst.add (hsecond.add (tendsto_smallValuationLogError δ hδ))
  convert h using 1
  · funext n
    ring
  · norm_num

lemma approximateLog_lower_eventually (δ : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (Real.log (n : ℝ) - 1 - δ) ≤ approximateLog δ n := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hlogtop.eventually (Filter.eventually_ge_atTop (1 + δ))] with n hn hlog
  have hlog' : 1 + δ ≤ Real.log (n : ℝ) := by
    simpa [Function.comp_def] using hlog
  have hb : 0 ≤ Real.log (n : ℝ) - 1 - δ := by linarith
  have hN : (n : ℝ) ≤ approximateLength n := by
    exact_mod_cast le_approximateLength n
  calc
    (n : ℝ) * (Real.log (n : ℝ) - 1 - δ) ≤
        (approximateLength n : ℝ) * (Real.log (n : ℝ) - 1 - δ) :=
      mul_le_mul_of_nonneg_right hN hb
    _ = ∑ _i : Fin (approximateLength n),
        (Real.log (n : ℝ) - 1 - δ) := by
      simp
      <;> ring
    _ ≤ approximateLog δ n := by
      rw [approximateLog]
      exact Finset.sum_le_sum fun i _ ↦
        approximateFactor_log_lower hn δ i

lemma eventually_largeLog_surplus (δ : ℝ) (hδ : 0 < δ)
    (hδlog : δ < Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((Real.log 2 - δ) / 2) * n ≤
        sourceLargeLog δ n - targetLargeLog n := by
  let gap : ℝ := (Real.log 2 - δ) / 2
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have herr := (tendsto_largeSurplusError_div δ hδ).eventually
    (Metric.closedBall_mem_nhds 0 hgap)
  filter_upwards [Filter.eventually_ge_atTop 2,
    eventually_two_le_lowerCutoff,
    eventually_approximateFactor_upper δ hδ,
    approximateLog_lower_eventually δ, herr] with n hn hL2 hu hsource herr
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfact := log_factorial_le n hnpos
  have htwo := factorial_two_valuation_real_lower hn
  have hsmall := sourceSmall_sub_targetSmall_le_error δ n
  have hid := largeLog_difference_identity hnpos hL2 hu
  have herrnorm : largeSurplusError δ n / n ≤ gap := by
    rw [Real.dist_eq] at herr
    simp only [sub_zero] at herr
    exact (le_abs_self _).trans herr
  have herrraw : largeSurplusError δ n ≤ gap * n := by
    rw [div_le_iff₀ hnreal] at herrnorm
    simpa [mul_comm] using herrnorm
  dsimp [largeSurplusError, gap] at herrraw ⊢
  nlinarith

/-! The moving large-prime interval has logarithmic width only
`O(log log n)`.  The quantitative Mertens bound therefore upgrades the
already proved `targetLargeCount / n → 0` to the weighted estimate needed
for matching. -/

noncomputable def cutoffLogGap (n : ℕ) : ℝ :=
  Real.log (n : ℝ) - Real.log (lowerCutoff n : ℝ)

noncomputable def cutoffGapUpper (n : ℕ) : ℝ :=
  Real.log 2 + 3 * Real.log (lowerScale n : ℝ)

lemma eventually_cutoffLogGap_bounds :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ cutoffLogGap n ∧ cutoffLogGap n ≤ cutoffGapUpper n := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_two_lowerScale_cube_le,
    hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hlarge hnlog
  have hnpos : 0 < n := by
    have : 0 < 2 * lowerScale n ^ 3 :=
      mul_pos (by norm_num) (pow_pos (lowerScale_pos n) _)
    omega
  have hLpos : 0 < lowerCutoff n := by
    have hc := lowerCutoff_lower hlarge
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    simp [hz] at hc
    omega
  have hLle : lowerCutoff n ≤ n := Nat.div_le_self _ _
  have hlogle : Real.log (lowerCutoff n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hLpos) (by exact_mod_cast hLle)
  have hprod : (n : ℝ) ≤
      2 * (lowerScale n : ℝ) ^ 3 * lowerCutoff n := by
    exact_mod_cast lowerCutoff_lower hlarge
  have hlogprod := Real.log_le_log (by exact_mod_cast hnpos) hprod
  have hlogeq : Real.log
      (2 * (lowerScale n : ℝ) ^ 3 * lowerCutoff n) =
      Real.log 2 + 3 * Real.log (lowerScale n : ℝ) +
        Real.log (lowerCutoff n : ℝ) := by
    have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        (pow_ne_zero 3 hApos.ne'))
      (by exact_mod_cast hLpos.ne'),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (pow_ne_zero 3 hApos.ne'),
      Real.log_pow]
    ring
  rw [hlogeq] at hlogprod
  exact ⟨by simp [cutoffLogGap, hlogle], by
    dsimp [cutoffLogGap, cutoffGapUpper]
    linarith⟩

lemma tendsto_loglog_sq_div_log_nat :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) ^ 2 /
      Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
  have hreal := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hcomp := hreal.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply hcomp.congr'
  filter_upwards
    [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_gt_atTop 0)] with n hn
  simp only [Function.comp_apply, Real.rpow_one]
  rw [Real.rpow_two]

lemma tendsto_log_lowerScale_sq_div_log :
    Tendsto (fun n : ℕ ↦ Real.log (lowerScale n : ℝ) ^ 2 /
      Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ ↦ Real.log 3 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := hlogtop.const_div_atTop (Real.log 3)
  have hll := tendsto_log_log_div_log_nat
  have hll2 := tendsto_loglog_sq_div_log_nat
  have hu : Tendsto (fun n : ℕ ↦
      (Real.log 3 + 3 * Real.log (Real.log (n : ℝ))) ^ 2 /
        Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
    have h := ((hc.const_mul (Real.log 3)).add
      ((hll.const_mul (6 * Real.log 3)).add (hll2.const_mul 9)))
    convert h using 1
    · funext n
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [hlogtop.eventually (Filter.eventually_gt_atTop 0)] with n hn
    exact div_nonneg (sq_nonneg _) hn.le
  · filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop 1)] with n hn
    have hn' : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [Function.comp_def] using hn
    have hApos : (0 : ℝ) < lowerScale n := by exact_mod_cast lowerScale_pos n
    have hAone : (1 : ℝ) ≤ lowerScale n := by
      exact_mod_cast lowerScale_pos n
    have hlogA_nonneg := Real.log_nonneg hAone
    have hs := lowerScale_cast_upper hn'
    have hlogupper : Real.log (lowerScale n : ℝ) ≤
        Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) := by
      calc
        Real.log (lowerScale n : ℝ) ≤
            Real.log (3 * Real.log (n : ℝ) ^ 3) :=
          Real.log_le_log hApos hs
        _ = Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) := by
          rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
            (by positivity : Real.log (n : ℝ) ^ 3 ≠ 0), Real.log_pow]
          ring
    have hupperNonneg : 0 ≤
        Real.log 3 + 3 * Real.log (Real.log (n : ℝ)) :=
      hlogA_nonneg.trans hlogupper
    exact div_le_div_of_nonneg_right
      ((sq_le_sq₀ hlogA_nonneg hupperNonneg).mpr hlogupper) (by positivity)
  · exact hu

lemma tendsto_cutoffGapUpper_div_log :
    Tendsto (fun n : ℕ ↦ cutoffGapUpper n / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc := hlogtop.const_div_atTop (Real.log 2)
  have h := hc.add (tendsto_log_lowerScale_div_log.const_mul 3)
  convert h using 1
  · funext n
    simp [cutoffGapUpper]
    ring
  · norm_num

lemma tendsto_cutoffGapUpper_sq_div_log :
    Tendsto (fun n : ℕ ↦ cutoffGapUpper n ^ 2 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc := hlogtop.const_div_atTop ((Real.log 2) ^ 2)
  have hm := tendsto_log_lowerScale_div_log.const_mul (6 * Real.log 2)
  have hs := tendsto_log_lowerScale_sq_div_log.const_mul 9
  have h := hc.add (hm.add hs)
  convert h using 1
  · funext n
    simp [cutoffGapUpper]
    ring
  · norm_num

lemma tendsto_cutoffGapUpper_div_logCutoff :
    Tendsto (fun n : ℕ ↦ cutoffGapUpper n /
      Real.log (lowerCutoff n : ℝ)) Filter.atTop (nhds 0) := by
  have h := tendsto_cutoffGapUpper_div_log.div
    tendsto_log_lowerCutoff_div_log (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto
      ((fun n : ℕ ↦ cutoffGapUpper n / Real.log (n : ℝ)) /
        (fun n : ℕ ↦ Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by simpa using h
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply h'.congr'
  filter_upwards [hlogtop.eventually (Filter.eventually_gt_atTop 0),
    tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hL
  simp only [Pi.div_apply]
  have hn0 : Real.log (n : ℝ) ≠ 0 := hn.ne'
  have hL0 : Real.log (lowerCutoff n : ℝ) ≠ 0 := hL.ne'
  field_simp [hn0, hL0]
  <;> ring

lemma tendsto_cutoffGapUpper_sq_div_logCutoff :
    Tendsto (fun n : ℕ ↦ cutoffGapUpper n ^ 2 /
      Real.log (lowerCutoff n : ℝ)) Filter.atTop (nhds 0) := by
  have h := tendsto_cutoffGapUpper_sq_div_log.div
    tendsto_log_lowerCutoff_div_log (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto
      ((fun n : ℕ ↦ cutoffGapUpper n ^ 2 / Real.log (n : ℝ)) /
        (fun n : ℕ ↦ Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by simpa using h
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply h'.congr'
  filter_upwards [hlogtop.eventually (Filter.eventually_gt_atTop 0),
    tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hL
  simp only [Pi.div_apply]
  have hn0 : Real.log (n : ℝ) ≠ 0 := hn.ne'
  have hL0 : Real.log (lowerCutoff n : ℝ) ≠ 0 := hL.ne'
  field_simp [hn0, hL0]
  <;> ring

lemma tendsto_largeReciprocal_mul_cutoffLogGap :
    Tendsto (fun n : ℕ ↦
      (primeReciprocalSum n - primeReciprocalSum (lowerCutoff n)) *
        cutoffLogGap n) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCnonneg, hC⟩ := Mertens.eventually_abs_E₂p_le
  have hcutoffTop :
      Tendsto (fun n : ℕ ↦ (lowerCutoff n : ℝ)) Filter.atTop Filter.atTop := by
    apply (Real.tendsto_exp_atTop.comp tendsto_log_lowerCutoff_atTop).congr'
    filter_upwards [eventually_two_le_lowerCutoff] with n hn
    apply Real.exp_log
    exact_mod_cast (by omega : 0 < lowerCutoff n)
  have hu : Tendsto (fun n : ℕ ↦
      cutoffGapUpper n ^ 2 / Real.log (lowerCutoff n : ℝ) +
        C * (cutoffGapUpper n / Real.log (n : ℝ)) +
        C * (cutoffGapUpper n / Real.log (lowerCutoff n : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_cutoffGapUpper_sq_div_logCutoff.add
      ((tendsto_cutoffGapUpper_div_log.const_mul C).add
        (tendsto_cutoffGapUpper_div_logCutoff.const_mul C))
    convert h using 1
    · funext n
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [eventually_cutoffLogGap_bounds] with n hg
    have hD : 0 ≤ primeReciprocalSum n - primeReciprocalSum (lowerCutoff n) := by
      rw [← sum_lowerLargePrimes_reciprocal]
      exact Finset.sum_nonneg fun p _ ↦ by positivity
    exact mul_nonneg hD hg.1
  · filter_upwards [eventually_cutoffLogGap_bounds,
      eventually_two_le_lowerCutoff,
      Filter.eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop 0),
      tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0),
      tendsto_natCast_atTop_atTop.eventually hC,
      hcutoffTop.eventually hC] with
      n hg hL2 hn2 hnlog hLlog hEn hEL
    have hnlog' : 0 < Real.log (n : ℝ) := by
      simpa [Function.comp_def] using hnlog
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hLreal : (2 : ℝ) ≤ lowerCutoff n := by exact_mod_cast hL2
    have hgapnonneg := hg.1
    have hgaple := hg.2
    have hGnonneg : 0 ≤ cutoffGapUpper n := hgapnonneg.trans hgaple
    have hloglog : Real.log (Real.log (n : ℝ)) -
        Real.log (Real.log (lowerCutoff n : ℝ)) ≤
          cutoffLogGap n / Real.log (lowerCutoff n : ℝ) := by
      have hratioPos : 0 < Real.log (n : ℝ) /
          Real.log (lowerCutoff n : ℝ) := div_pos hnlog' hLlog
      have hbasic := Real.log_le_sub_one_of_pos hratioPos
      have heq : Real.log (Real.log (n : ℝ)) -
          Real.log (Real.log (lowerCutoff n : ℝ)) =
          Real.log (Real.log (n : ℝ) /
            Real.log (lowerCutoff n : ℝ)) := by
        rw [Real.log_div hnlog'.ne' hLlog.ne']
      rw [heq]
      calc
        Real.log (Real.log (n : ℝ) / Real.log (lowerCutoff n : ℝ)) ≤
            Real.log (n : ℝ) / Real.log (lowerCutoff n : ℝ) - 1 := hbasic
        _ = cutoffLogGap n / Real.log (lowerCutoff n : ℝ) := by
          dsimp [cutoffLogGap]
          field_simp [hLlog.ne']
          <;> ring
    have hDupper : primeReciprocalSum n - primeReciprocalSum (lowerCutoff n) ≤
        cutoffLogGap n / Real.log (lowerCutoff n : ℝ) +
          C / Real.log (n : ℝ) + C / Real.log (lowerCutoff n : ℝ) := by
      rw [primeReciprocalSum_eq, primeReciprocalSum_eq]
      have hEn' : Mertens.E₂p (n : ℝ) ≤
          C / Real.log (n : ℝ) :=
        (le_abs_self _).trans hEn
      have hEL' : -Mertens.E₂p (lowerCutoff n : ℝ) ≤
          C / Real.log (lowerCutoff n : ℝ) :=
        (neg_le_abs _).trans hEL
      linarith
    calc
      (primeReciprocalSum n - primeReciprocalSum (lowerCutoff n)) * cutoffLogGap n ≤
          (cutoffLogGap n / Real.log (lowerCutoff n : ℝ) +
            C / Real.log (n : ℝ) + C / Real.log (lowerCutoff n : ℝ)) *
              cutoffLogGap n := mul_le_mul_of_nonneg_right hDupper hgapnonneg
      _ ≤ (cutoffGapUpper n / Real.log (lowerCutoff n : ℝ) +
            C / Real.log (n : ℝ) + C / Real.log (lowerCutoff n : ℝ)) *
              cutoffGapUpper n := by
        have hdenL : 0 ≤ (Real.log (lowerCutoff n : ℝ))⁻¹ := by positivity
        have hdenN : 0 ≤ (Real.log (n : ℝ))⁻¹ := by positivity
        have hCdivN_nonneg : 0 ≤ C / Real.log (n : ℝ) := by
          have := hEn
          exact (abs_nonneg _).trans this
        have hCdivL_nonneg : 0 ≤ C / Real.log (lowerCutoff n : ℝ) := by
          have := hEL
          exact (abs_nonneg _).trans this
        gcongr
      _ = cutoffGapUpper n ^ 2 / Real.log (lowerCutoff n : ℝ) +
          C * (cutoffGapUpper n / Real.log (n : ℝ)) +
          C * (cutoffGapUpper n / Real.log (lowerCutoff n : ℝ)) := by ring
  · exact hu

lemma tendsto_targetLargeCount_mul_cutoffLogGap_div :
    Tendsto (fun n : ℕ ↦
      (targetLargeCount n : ℝ) * cutoffLogGap n / n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_cutoffLogGap_bounds] with n hg
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hg.1) (Nat.cast_nonneg _)
  · filter_upwards [eventually_cutoffLogGap_bounds,
      Filter.eventually_gt_atTop 0] with n hg hn
    have hc := targetLargeCount_real_bound hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (targetLargeCount n : ℝ) * cutoffLogGap n / n =
          ((targetLargeCount n : ℝ) / n) * cutoffLogGap n := by ring
      _ ≤ (2 * (primeReciprocalSum n - primeReciprocalSum (lowerCutoff n))) *
          cutoffLogGap n := mul_le_mul_of_nonneg_right hc hg.1
      _ = 2 * ((primeReciprocalSum n - primeReciprocalSum (lowerCutoff n)) *
          cutoffLogGap n) := by ring
  · simpa only [mul_zero] using
      tendsto_largeReciprocal_mul_cutoffLogGap.const_mul 2

noncomputable def sourceLargeCount (δ : ℝ) (n : ℕ) : ℕ :=
  ∑ p ∈ lowerLargePrimes n, sourceValuation δ n p

lemma sourceLargeLog_upper {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    sourceLargeLog δ n ≤ (sourceLargeCount δ n : ℝ) * Real.log n := by
  rw [sourceLargeLog]
  calc
    (∑ p ∈ lowerLargePrimes n,
        (sourceValuation δ n p : ℝ) * Real.log p) ≤
        ∑ p ∈ lowerLargePrimes n,
          (sourceValuation δ n p : ℝ) * Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hple := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hpprime := (Finset.mem_filter.mp hp).2
      have hpPosReal : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hpleReal : (p : ℝ) ≤ n := by exact_mod_cast hple
      gcongr
    _ = (sourceLargeCount δ n : ℝ) * Real.log n := by
      simp only [sourceLargeCount, Nat.cast_sum]
      rw [← Finset.sum_mul]

lemma targetLargeLog_lower {n : ℕ} (hLpos : 0 < lowerCutoff n) :
    (targetLargeCount n : ℝ) * Real.log (lowerCutoff n : ℝ) ≤
      targetLargeLog n := by
  rw [targetLargeLog]
  simp only [targetLargeCount, Nat.cast_sum]
  calc
    (∑ p ∈ lowerLargePrimes n, (n.factorial.factorization p : ℝ)) *
        Real.log (lowerCutoff n : ℝ) =
        ∑ p ∈ lowerLargePrimes n,
          (n.factorial.factorization p : ℝ) *
            Real.log (lowerCutoff n : ℝ) := by rw [Finset.sum_mul]
    _ ≤ ∑ p ∈ lowerLargePrimes n,
        (n.factorial.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      gcongr

lemma eventually_targetLargeCount_le_sourceLargeCount (δ : ℝ) (hδ : 0 < δ)
    (hδlog : δ < Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop, targetLargeCount n ≤ sourceLargeCount δ n := by
  let gap : ℝ := (Real.log 2 - δ) / 2
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hweighted := tendsto_targetLargeCount_mul_cutoffLogGap_div.eventually
    (Metric.ball_mem_nhds 0 hgap)
  filter_upwards [eventually_largeLog_surplus δ hδ hδlog,
    eventually_cutoffLogGap_bounds, eventually_two_le_lowerCutoff,
    Filter.eventually_gt_atTop 0, hweighted] with n hsurplus hgapbounds hL2 hn hw
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < lowerCutoff n := by omega
  have hw' : (targetLargeCount n : ℝ) * cutoffLogGap n / n < gap := by
    rw [Real.dist_eq] at hw
    simp only [sub_zero] at hw
    exact (le_abs_self _).trans_lt hw
  by_contra hnot
  have hcountNat : sourceLargeCount δ n ≤ targetLargeCount n := by omega
  have hcount : (sourceLargeCount δ n : ℝ) ≤ targetLargeCount n := by
    exact_mod_cast hcountNat
  have hsupper := sourceLargeLog_upper hn δ
  have htlower := targetLargeLog_lower hLpos
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hdiff : sourceLargeLog δ n - targetLargeLog n ≤
      (targetLargeCount n : ℝ) * cutoffLogGap n := by
    calc
      sourceLargeLog δ n - targetLargeLog n ≤
          (sourceLargeCount δ n : ℝ) * Real.log n -
            (targetLargeCount n : ℝ) * Real.log (lowerCutoff n : ℝ) :=
        sub_le_sub hsupper htlower
      _ ≤ (targetLargeCount n : ℝ) * Real.log n -
            (targetLargeCount n : ℝ) * Real.log (lowerCutoff n : ℝ) := by
        gcongr
      _ = (targetLargeCount n : ℝ) * cutoffLogGap n := by
        dsimp [cutoffLogGap]
        ring
  have hwraw : (targetLargeCount n : ℝ) * cutoffLogGap n < gap * n := by
    rw [div_lt_iff₀ hnreal] at hw'
    simpa [mul_comm] using hw'
  dsimp [gap] at hsurplus hwraw
  nlinarith

/-! ### Finitary large-prime matching -/

abbrev TargetLargeOccurrence (n : ℕ) :=
  Σ p : {p // p ∈ lowerLargePrimes n}, Fin (n.factorial.factorization p.1)

abbrev SourceLargeOccurrence (δ : ℝ) (n : ℕ) :=
  Σ p : {p // p ∈ lowerLargePrimes n},
    Σ i : Fin (approximateLength n),
      Fin ((approximateFactor δ n i).factorization p.1)

def targetOccurrencePrime {n : ℕ} (x : TargetLargeOccurrence n) : ℕ := x.1.1

def sourceOccurrencePrime {δ : ℝ} {n : ℕ} (x : SourceLargeOccurrence δ n) : ℕ :=
  x.1.1

def sourceOccurrenceIndex {δ : ℝ} {n : ℕ} (x : SourceLargeOccurrence δ n) :
    Fin (approximateLength n) := x.2.1

lemma card_targetLargeOccurrence (n : ℕ) :
    Fintype.card (TargetLargeOccurrence n) = targetLargeCount n := by
  simp only [TargetLargeOccurrence, Fintype.card_sigma, Fintype.card_fin,
    Finset.univ_eq_attach]
  rw [Finset.sum_attach]
  rfl

lemma card_sourceLargeOccurrence (δ : ℝ) (n : ℕ) :
    Fintype.card (SourceLargeOccurrence δ n) = sourceLargeCount δ n := by
  simp [SourceLargeOccurrence, sourceLargeCount, sourceValuation,
    Finset.sum_attach]
  exact Finset.sum_attach (lowerLargePrimes n)
    (fun p ↦ ∑ i : Fin (approximateLength n),
      (approximateFactor δ n i).factorization p)

lemma sourceOccurrence_data {δ : ℝ} {n : ℕ} (x : SourceLargeOccurrence δ n) :
    let p := sourceOccurrencePrime x
    let i := sourceOccurrenceIndex x
    p ∈ lowerLargePrimes n ∧
      p.Prime ∧ lowerCutoff n < p ∧
      p ∣ approximateFactor δ n i := by
  dsimp [sourceOccurrencePrime, sourceOccurrenceIndex]
  have hpMem := x.1.2
  have hpprime := (Finset.mem_filter.mp hpMem).2
  have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpMem).1).1
  have hvalpos : 0 < (approximateFactor δ n x.2.1).factorization x.1.1 :=
    lt_of_le_of_lt (Nat.zero_le _) x.2.2.2
  exact ⟨hpMem, hpprime, hpgt,
    Nat.dvd_of_factorization_pos hvalpos.ne'⟩

lemma sourceOccurrence_factorization_le_one {δ : ℝ} {n : ℕ}
    (hn : 0 < n) (hsq : n ≤ lowerCutoff n ^ 2)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (x : SourceLargeOccurrence δ n) :
    (approximateFactor δ n (sourceOccurrenceIndex x)).factorization
      (sourceOccurrencePrime x) ≤ 1 := by
  let p := sourceOccurrencePrime x
  let i := sourceOccurrenceIndex x
  change (approximateFactor δ n i).factorization p ≤ 1
  have hx := sourceOccurrence_data x
  have hfactorpos := approximateFactor_pos (δ := δ) hn i
  have hfactorle := (approximateFactor_le_interval_top δ n i).trans hupper
  by_contra hnot
  have htwo : 2 ≤ (approximateFactor δ n i).factorization p := by omega
  have hpdvd : p ^ 2 ∣ approximateFactor δ n i :=
    (hx.2.1.pow_dvd_iff_le_factorization hfactorpos.ne').mpr htwo
  have hple : p ^ 2 ≤ approximateFactor δ n i :=
    Nat.le_of_dvd hfactorpos hpdvd
  have hLlt : lowerCutoff n ^ 2 < p ^ 2 := by
    exact Nat.pow_lt_pow_left hx.2.2.1 (by norm_num)
  omega

lemma sourceOccurrenceIndex_injective {δ : ℝ} {n : ℕ}
    (hn : 0 < n) (hsq : n ≤ lowerCutoff n ^ 2)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    Function.Injective (sourceOccurrenceIndex :
      SourceLargeOccurrence δ n → Fin (approximateLength n)) := by
  intro x y hxy
  rcases x with ⟨⟨p, hpMem⟩, ⟨i, hi⟩⟩
  rcases y with ⟨⟨q, hqMem⟩, ⟨j, hj⟩⟩
  change i = j at hxy
  subst j
  have hpprime := (Finset.mem_filter.mp hpMem).2
  have hqprime := (Finset.mem_filter.mp hqMem).2
  have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpMem).1).1
  have hqgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqMem).1).1
  have hpval : 0 < (approximateFactor δ n i).factorization p :=
    lt_of_le_of_lt (Nat.zero_le _) hi.isLt
  have hqval : 0 < (approximateFactor δ n i).factorization q :=
    lt_of_le_of_lt (Nat.zero_le _) hj.isLt
  have hpdvd := Nat.dvd_of_factorization_pos hpval.ne'
  have hqdvd := Nat.dvd_of_factorization_pos hqval.ne'
  have hfactorpos := approximateFactor_pos (δ := δ) hn i
  have hfactorle := (approximateFactor_le_interval_top δ n i).trans hupper
  have hpq : p = q := by
    by_contra hpq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpprime hqprime).mpr hpq
    have hpqdvd : p * q ∣ approximateFactor δ n i :=
      hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
    have hpqle : p * q ≤ approximateFactor δ n i :=
      Nat.le_of_dvd hfactorpos hpqdvd
    have hLmul : lowerCutoff n ^ 2 < p * q := by
      simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt hpgt hqgt
    omega
  subst q
  have hone := sourceOccurrence_factorization_le_one hn hsq hupper
    (⟨⟨p, hpMem⟩, ⟨i, hi⟩⟩ : SourceLargeOccurrence δ n)
  change (approximateFactor δ n i).factorization p ≤ 1 at hone
  have hiLt := hi.isLt
  change hi.1 < (approximateFactor δ n i).factorization p at hiLt
  have hjLt := hj.isLt
  change hj.1 < (approximateFactor δ n i).factorization p at hjLt
  have hhi0 : hi.1 = 0 := by omega
  have hhj0 : hj.1 = 0 := by omega
  have hhij : hi = hj := Fin.ext (by omega)
  subst hj
  rfl

noncomputable def largeOccurrenceMatching {δ : ℝ} {n : ℕ}
    (hcount : targetLargeCount n ≤ sourceLargeCount δ n) :
    TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n := by
  apply (Function.Embedding.nonempty_of_card_le ?_).some
  rw [card_targetLargeOccurrence, card_sourceLargeOccurrence]
  exact hcount

/-! ### Replacing the large-prime part of the approximate factors -/

lemma targetOccurrence_data {n : ℕ} (x : TargetLargeOccurrence n) :
    targetOccurrencePrime x ∈ lowerLargePrimes n ∧
      (targetOccurrencePrime x).Prime := by
  exact ⟨x.1.2, (Finset.mem_filter.mp x.1.2).2⟩

/-- The prime exponents of an approximate factor after all primes in the
moving large interval have been removed. -/
noncomputable def sourceSmallExponent (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : ℕ →₀ ℕ :=
  (approximateFactor δ n i).factorization.filter
    (fun p ↦ p ∉ lowerLargePrimes n)

/-- Large target-prime occurrences assigned to the `i`th approximate factor
by an occurrence matching. -/
noncomputable def assignedTargetExponent {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : ℕ →₀ ℕ :=
  ∑ x : TargetLargeOccurrence n,
    if sourceOccurrenceIndex (e x) = i then
      Finsupp.single (targetOccurrencePrime x) 1 else 0

noncomputable def repairedExponent {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : ℕ →₀ ℕ :=
  sourceSmallExponent δ n i + assignedTargetExponent e i

noncomputable def repairedFactor {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : ℕ :=
  (repairedExponent e i).prod (fun p a ↦ p ^ a)

lemma assignedTargetExponent_eq_zero_of_not_prime {δ : ℝ} {n p : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) (hp : ¬p.Prime) :
    assignedTargetExponent e i p = 0 := by
  rw [assignedTargetExponent, Finsupp.finsetSum_apply]
  change (∑ x : TargetLargeOccurrence n,
    (if sourceOccurrenceIndex (e x) = i then
      Finsupp.single (targetOccurrencePrime x) 1 else 0) p) = 0
  apply Finset.sum_eq_zero
  intro x hx
  split_ifs with hidx
  · rw [Finsupp.single_apply]
    split_ifs with hprime
    · subst p
      exact (hp (targetOccurrence_data x).2).elim
    · rfl
  · rfl

lemma repairedExponent_support_prime {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) :
    ∀ p ∈ (repairedExponent e i).support, p.Prime := by
  intro p hp
  by_contra hprime
  have hsource : sourceSmallExponent δ n i p = 0 := by
    simp [sourceSmallExponent, Finsupp.filter_apply,
      Nat.factorization_eq_zero_of_not_prime _ hprime]
  have htarget := assignedTargetExponent_eq_zero_of_not_prime e i hprime
  rw [Finsupp.mem_support_iff, repairedExponent, Finsupp.add_apply,
    hsource, htarget, add_zero] at hp
  exact hp rfl

lemma repairedFactor_factorization {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) :
    (repairedFactor e i).factorization = repairedExponent e i := by
  exact Nat.prod_pow_factorization_eq_self (repairedExponent_support_prime e i)

lemma repairedFactor_pos {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : 0 < repairedFactor e i := by
  rw [repairedFactor]
  exact Nat.pos_of_ne_zero ((Finsupp.prod_ne_zero_iff).2 fun p hp ↦
    pow_ne_zero _ (repairedExponent_support_prime e i p hp).ne_zero)

lemma sum_assignedTargetExponent {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    ∑ i : Fin (approximateLength n), assignedTargetExponent e i =
      ∑ x : TargetLargeOccurrence n,
        Finsupp.single (targetOccurrencePrime x) 1 := by
  simp only [assignedTargetExponent]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simpa using Fintype.sum_ite_eq (sourceOccurrenceIndex (e x))
    (fun _ : Fin (approximateLength n) ↦
      Finsupp.single (targetOccurrencePrime x) 1)

lemma sum_targetOccurrence_single (n : ℕ) :
    ∑ x : TargetLargeOccurrence n,
        Finsupp.single (targetOccurrencePrime x) 1 =
      n.factorial.factorization.filter (fun p ↦ p ∈ lowerLargePrimes n) := by
  ext p
  simp only [Finsupp.finsetSum_apply, Finsupp.filter_apply]
  change (∑ x : TargetLargeOccurrence n,
      (Finsupp.single (targetOccurrencePrime x) 1) p) =
    if p ∈ lowerLargePrimes n then n.factorial.factorization p else 0
  by_cases hp : p ∈ lowerLargePrimes n
  · rw [if_pos hp, Fintype.sum_sigma]
    simp [TargetLargeOccurrence, targetOccurrencePrime,
      Finsupp.single_apply, hp]
    calc
      (∑ x ∈ (lowerLargePrimes n).attach,
          if (x : ℕ) = p then n.factorial.factorization x else 0) =
          ∑ q ∈ lowerLargePrimes n,
            if q = p then n.factorial.factorization q else 0 :=
        Finset.sum_attach (lowerLargePrimes n)
          (fun q ↦ if q = p then n.factorial.factorization q else 0)
      _ = n.factorial.factorization p := by simp [hp]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finsupp.single_apply]
    split_ifs with hxp
    · subst p
      exact (hp x.1.2).elim
    · rfl

lemma sum_repairedExponent {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    ∑ i : Fin (approximateLength n), repairedExponent e i =
      (∑ i : Fin (approximateLength n),
          (approximateFactor δ n i).factorization.filter
            (fun p ↦ p ∉ lowerLargePrimes n)) +
        n.factorial.factorization.filter (fun p ↦ p ∈ lowerLargePrimes n) := by
  rw [← sum_targetOccurrence_single n, ← sum_assignedTargetExponent e]
  simp [repairedExponent, sourceSmallExponent, Finset.sum_add_distrib]

noncomputable def repairedProduct {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) : ℕ :=
  ∏ i : Fin (approximateLength n), repairedFactor e i

lemma repairedProduct_pos {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    0 < repairedProduct e := by
  exact Finset.prod_pos fun i _ ↦ repairedFactor_pos e i

lemma repairedProduct_factorization {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    (repairedProduct e).factorization =
      ∑ i : Fin (approximateLength n), repairedExponent e i := by
  rw [repairedProduct, Nat.factorization_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    exact repairedFactor_factorization e i
  · intro i hi
    exact (repairedFactor_pos e i).ne'

lemma repairedProduct_factorization_of_mem {δ : ℝ} {n p : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∈ lowerLargePrimes n) :
    (repairedProduct e).factorization p = n.factorial.factorization p := by
  rw [repairedProduct_factorization e, sum_repairedExponent e,
    Finsupp.add_apply, Finsupp.filter_apply_pos _ _ hp,
    Finsupp.finsetSum_apply]
  have hz : ∀ i : Fin (approximateLength n),
      ((approximateFactor δ n i).factorization.filter
        (fun q ↦ q ∉ lowerLargePrimes n)) p = 0 := by
    intro i
    exact Finsupp.filter_apply_neg _ _ (not_not.mpr hp)
  simp [hz]

lemma repairedProduct_factorization_of_not_mem {δ : ℝ} {n p : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∉ lowerLargePrimes n) :
    (repairedProduct e).factorization p = sourceValuation δ n p := by
  rw [repairedProduct_factorization e, sum_repairedExponent e,
    Finsupp.add_apply, Finsupp.filter_apply_neg _ _ hp,
    Finsupp.finsetSum_apply]
  rw [add_zero, sourceValuation]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finsupp.filter_apply_pos _ _ hp

lemma repairedProduct_prime_le { δ : ℝ} {n p : ℕ} (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∈ (repairedProduct e).factorization.support) : p ≤ n := by
  have hpval : 0 < (repairedProduct e).factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  by_cases hplarge : p ∈ lowerLargePrimes n
  · exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hplarge).1).2
  · rw [repairedProduct_factorization_of_not_mem e hplarge,
      sourceValuation] at hpval
    obtain ⟨i, hiMem, hi⟩ := Finset.sum_pos_iff.mp hpval
    have hpdvd : p ∣ approximateFactor δ n i :=
      Nat.dvd_of_factorization_pos hi.ne'
    exact (Nat.le_of_dvd (approximateFactor_pos hn i) hpdvd).trans
      ((approximateFactor_le_interval_top δ n i).trans hupper)

lemma repairedProduct_log_eq_factorization_sum { δ : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    Real.log (repairedProduct e : ℝ) =
      ∑ p ∈ Finset.range (n + 1),
        ((repairedProduct e).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (repairedProduct_prime_le hn hupper e hp))
  · intro p hpRange hpNot
    have hz : (repairedProduct e).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNot
    simp [hz]

lemma repairedProduct_log_identity { δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    Real.log (repairedProduct e : ℝ) =
      approximateLog δ n - sourceLargeLog δ n + targetLargeLog n := by
  rw [repairedProduct_log_eq_factorization_sum hn hupper e]
  have hpoint : ∀ p ∈ Finset.range (n + 1),
      ((repairedProduct e).factorization p : ℝ) * Real.log p =
        (sourceValuation δ n p : ℝ) * Real.log p +
          (if p ∈ lowerLargePrimes n then
            ((n.factorial.factorization p : ℝ) - sourceValuation δ n p) *
              Real.log p else 0) := by
    intro p hpRange
    by_cases hp : p ∈ lowerLargePrimes n
    · rw [repairedProduct_factorization_of_mem e hp, if_pos hp]
      ring
    · rw [repairedProduct_factorization_of_not_mem e hp, if_neg hp]
      ring
  calc
    (∑ p ∈ Finset.range (n + 1),
        ((repairedProduct e).factorization p : ℝ) * Real.log p) =
        ∑ p ∈ Finset.range (n + 1),
          ((sourceValuation δ n p : ℝ) * Real.log p +
            if p ∈ lowerLargePrimes n then
              ((n.factorial.factorization p : ℝ) - sourceValuation δ n p) *
                Real.log p else 0) := by
      exact Finset.sum_congr rfl hpoint
    _ = (∑ p ∈ Finset.range (n + 1),
          (sourceValuation δ n p : ℝ) * Real.log p) +
        ∑ p ∈ Finset.range (n + 1),
          (if p ∈ lowerLargePrimes n then
            ((n.factorial.factorization p : ℝ) - sourceValuation δ n p) *
              Real.log p else 0) := by
      rw [Finset.sum_add_distrib]
    _ = approximateLog δ n +
        ∑ p ∈ lowerLargePrimes n,
          ((n.factorial.factorization p : ℝ) - sourceValuation δ n p) *
            Real.log p := by
      rw [← approximateLog_eq_factorization_sum hn hupper]
      congr 1
      let f : ℕ → ℝ := fun p ↦
        ((n.factorial.factorization p : ℝ) - sourceValuation δ n p) *
          Real.log p
      have hsubset : lowerLargePrimes n ⊆ Finset.range (n + 1) := by
        intro p hp
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
      calc
        (∑ p ∈ Finset.range (n + 1),
            if p ∈ lowerLargePrimes n then f p else 0) =
            ∑ p ∈ lowerLargePrimes n,
              (if p ∈ lowerLargePrimes n then f p else 0) := by
          apply (Finset.sum_subset hsubset ?_).symm
          intro p hpRange hpNot
          simp [hpNot]
        _ = ∑ p ∈ lowerLargePrimes n, f p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [hp]
    _ = approximateLog δ n - sourceLargeLog δ n + targetLargeLog n := by
      rw [targetLargeLog, sourceLargeLog]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring

lemma targetSmall_sub_sourceSmall_le_error (δ : ℝ) (n : ℕ) :
    targetSmallLog n - sourceSmallLog δ n ≤ smallValuationLogError δ n := by
  rw [sourceSmallLog, targetSmallLog, smallValuationLogError,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlognonneg : 0 ≤ Real.log (p : ℝ) := by
    have hpprime := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
  rw [← sub_mul]
  have hdiff : (n.factorial.factorization p : ℝ) - sourceValuation δ n p ≤
      |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| := by
    nlinarith [neg_le_abs ((sourceValuation δ n p : ℝ) -
      n.factorial.factorization p)]
  exact mul_le_mul_of_nonneg_right hdiff hlognonneg

lemma eventually_largeLog_surplus_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      sourceLargeLog δ n - targetLargeLog n ≤
        (Real.log 2 - δ / 2) * n := by
  have herrlim : Tendsto (fun n : ℕ ↦ approximateLogError δ n +
      smallValuationLogError δ n / n) Filter.atTop (nhds 0) :=
    by simpa using ((tendsto_approximateLogError δ).add
      (tendsto_smallValuationLogError δ hδ))
  have hr : (0 : ℝ) < δ / 2 := by linarith
  have herr := herrlim.eventually (Metric.closedBall_mem_nhds 0 hr)
  filter_upwards [Filter.eventually_ge_atTop 2, eventually_two_le_lowerCutoff,
    eventually_approximateFactor_upper δ hδ,
    approximateLog_normalized_bounds δ hδ, herr] with
      n hn hL2 hupper happrox herr
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have happroxRaw : approximateLog δ n ≤
      (n : ℝ) * (Real.log (n : ℝ) - 1 - δ) +
        n * approximateLogError δ n := by
    have h := happrox.2
    rw [div_le_iff₀ hnreal] at h
    nlinarith
  have hfact := log_factorial_ge n hnpos
  have hvalNat : n.factorial.factorization 2 ≤ n := by
    rw [factorial_two_valuation_eq]
    exact Nat.sub_le _ _
  have hval : (n.factorial.factorization 2 : ℝ) ≤ n := by
    exact_mod_cast hvalNat
  have hsmall := targetSmall_sub_sourceSmall_le_error δ n
  have hid := largeLog_difference_identity hnpos hL2 hupper
  have herrBound : approximateLogError δ n +
      smallValuationLogError δ n / n ≤ δ / 2 := by
    rw [Real.dist_eq, sub_zero] at herr
    exact (le_abs_self _).trans herr
  have herrRaw : n * approximateLogError δ n +
      smallValuationLogError δ n ≤ (δ / 2) * n := by
    rw [show smallValuationLogError δ n =
      (smallValuationLogError δ n / n) * n by field_simp] 
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hvalLog := mul_le_mul_of_nonneg_right hval hlog2
  nlinarith

lemma sourceLargeLog_lower {n : ℕ} (hLpos : 0 < lowerCutoff n) (δ : ℝ) :
    (sourceLargeCount δ n : ℝ) * Real.log (lowerCutoff n : ℝ) ≤
      sourceLargeLog δ n := by
  rw [sourceLargeLog]
  simp only [sourceLargeCount, Nat.cast_sum]
  calc
    (∑ p ∈ lowerLargePrimes n, (sourceValuation δ n p : ℝ)) *
        Real.log (lowerCutoff n : ℝ) =
        ∑ p ∈ lowerLargePrimes n,
          (sourceValuation δ n p : ℝ) * Real.log (lowerCutoff n : ℝ) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ p ∈ lowerLargePrimes n,
        (sourceValuation δ n p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      gcongr

lemma targetLargeLog_upper {n : ℕ} (hn : 0 < n) :
    targetLargeLog n ≤ (targetLargeCount n : ℝ) * Real.log n := by
  rw [targetLargeLog]
  simp only [targetLargeCount, Nat.cast_sum]
  calc
    (∑ p ∈ lowerLargePrimes n,
        (n.factorial.factorization p : ℝ) * Real.log p) ≤
        ∑ p ∈ lowerLargePrimes n,
          (n.factorial.factorization p : ℝ) * Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hple := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hpprime := (Finset.mem_filter.mp hp).2
      have hpPosReal : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hpleReal : (p : ℝ) ≤ n := by exact_mod_cast hple
      gcongr
    _ = (∑ p ∈ lowerLargePrimes n,
        (n.factorial.factorization p : ℝ)) * Real.log n := by
      rw [Finset.sum_mul]

lemma tendsto_sourceLargeCount_div (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ (sourceLargeCount δ n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have hhalf := tendsto_log_lowerCutoff_div_log.eventually
    (Metric.closedBall_mem_nhds 1 (by norm_num : (0 : ℝ) < 1 / 2))
  have hright : Tendsto (fun n : ℕ ↦
      2 * ((targetLargeCount n : ℝ) / n) +
        Real.log 2 / Real.log (lowerCutoff n : ℝ))
      Filter.atTop (nhds 0) := by
    have hfirst := tendsto_targetLargeCount_div.const_mul 2
    have hsecond := tendsto_log_lowerCutoff_atTop.const_div_atTop (Real.log 2)
    simpa using hfirst.add hsecond
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 1,
      tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop 0),
      eventually_largeLog_surplus_upper δ hδ, hhalf] with
      n hn hLlog hnlog hsurplus hhalf
    have hnpos : 0 < n := by omega
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnlog' : 0 < Real.log (n : ℝ) := by
      simpa [Function.comp_def] using hnlog
    have hLpos : 0 < lowerCutoff n := by
      by_contra h
      have hz := Nat.eq_zero_of_not_pos h
      simp [hz] at hLlog
    have hratioLower : (1 / 2 : ℝ) ≤
        Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ) := by
      rw [Real.dist_eq] at hhalf
      have := neg_le_of_abs_le hhalf
      linarith
    have hlogCompare : Real.log (n : ℝ) ≤
        2 * Real.log (lowerCutoff n : ℝ) := by
      rw [le_div_iff₀ hnlog'] at hratioLower
      linarith
    have hsLower := sourceLargeLog_lower hLpos δ
    have htUpper := targetLargeLog_upper hnpos
    have hsurplus' : sourceLargeLog δ n ≤
        targetLargeLog n + Real.log 2 * n := by
      nlinarith
    have hraw : (sourceLargeCount δ n : ℝ) *
        Real.log (lowerCutoff n : ℝ) ≤
          2 * (targetLargeCount n : ℝ) *
            Real.log (lowerCutoff n : ℝ) + Real.log 2 * n := by
      nlinarith
    rw [div_le_iff₀ hnreal]
    have hLne : Real.log (lowerCutoff n : ℝ) ≠ 0 := hLlog.ne'
    calc
      (sourceLargeCount δ n : ℝ) ≤
          (2 * (targetLargeCount n : ℝ) *
              Real.log (lowerCutoff n : ℝ) + Real.log 2 * n) /
            Real.log (lowerCutoff n : ℝ) :=
        (le_div_iff₀ hLlog).2 hraw
      _ =
          2 * (targetLargeCount n : ℝ) +
            Real.log 2 * n / Real.log (lowerCutoff n : ℝ) := by
        field_simp [hLne]
        <;> ring
      _ = (2 * ((targetLargeCount n : ℝ) / n) +
          Real.log 2 / Real.log (lowerCutoff n : ℝ)) * n := by
        field_simp [hnreal.ne', hLne]
        <;> ring
  · exact hright

/-- The proof of `tendsto_sourceLargeCount_div` actually supplies the
quantitative estimate needed below.  We record it separately because the
slowly growing logarithmic width of the large-prime interval must still be
multiplied into the source count. -/
lemma eventually_sourceLargeCount_div_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (sourceLargeCount δ n : ℝ) / n ≤
        2 * ((targetLargeCount n : ℝ) / n) +
          Real.log 2 / Real.log (lowerCutoff n : ℝ) := by
  have hhalf := tendsto_log_lowerCutoff_div_log.eventually
    (Metric.closedBall_mem_nhds 1 (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [Filter.eventually_gt_atTop 1,
      tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop 0),
      eventually_largeLog_surplus_upper δ hδ, hhalf] with
      n hn hLlog hnlog hsurplus hhalf
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnlog' : 0 < Real.log (n : ℝ) := by
    simpa [Function.comp_def] using hnlog
  have hLpos : 0 < lowerCutoff n := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    simp [hz] at hLlog
  have hratioLower : (1 / 2 : ℝ) ≤
      Real.log (lowerCutoff n : ℝ) / Real.log (n : ℝ) := by
    rw [Real.dist_eq] at hhalf
    have := neg_le_of_abs_le hhalf
    linarith
  have hlogCompare : Real.log (n : ℝ) ≤
      2 * Real.log (lowerCutoff n : ℝ) := by
    rw [le_div_iff₀ hnlog'] at hratioLower
    linarith
  have hsLower := sourceLargeLog_lower hLpos δ
  have htUpper := targetLargeLog_upper hnpos
  have hsurplus' : sourceLargeLog δ n ≤
      targetLargeLog n + Real.log 2 * n := by
    nlinarith
  have hraw : (sourceLargeCount δ n : ℝ) *
      Real.log (lowerCutoff n : ℝ) ≤
        2 * (targetLargeCount n : ℝ) *
          Real.log (lowerCutoff n : ℝ) + Real.log 2 * n := by
    nlinarith
  rw [div_le_iff₀ hnreal]
  have hLne : Real.log (lowerCutoff n : ℝ) ≠ 0 := hLlog.ne'
  calc
    (sourceLargeCount δ n : ℝ) ≤
        (2 * (targetLargeCount n : ℝ) *
            Real.log (lowerCutoff n : ℝ) + Real.log 2 * n) /
          Real.log (lowerCutoff n : ℝ) :=
      (le_div_iff₀ hLlog).2 hraw
    _ = 2 * (targetLargeCount n : ℝ) +
          Real.log 2 * n / Real.log (lowerCutoff n : ℝ) := by
      field_simp [hLne]
      <;> ring
    _ = (2 * ((targetLargeCount n : ℝ) / n) +
        Real.log 2 / Real.log (lowerCutoff n : ℝ)) * n := by
      field_simp [hnreal.ne', hLne]
      <;> ring

lemma tendsto_sourceLargeCount_mul_cutoffLogGap_div (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦
      (sourceLargeCount δ n : ℝ) * cutoffLogGap n / n)
      Filter.atTop (nhds 0) := by
  have hright : Tendsto (fun n : ℕ ↦
      2 * ((targetLargeCount n : ℝ) * cutoffLogGap n / n) +
        Real.log 2 * (cutoffGapUpper n /
          Real.log (lowerCutoff n : ℝ))) Filter.atTop (nhds 0) := by
    have hfirst := tendsto_targetLargeCount_mul_cutoffLogGap_div.const_mul 2
    have hsecond := tendsto_cutoffGapUpper_div_logCutoff.const_mul (Real.log 2)
    simpa using hfirst.add hsecond
  apply squeeze_zero'
  · filter_upwards [eventually_cutoffLogGap_bounds] with n hg
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hg.1) (Nat.cast_nonneg _)
  · filter_upwards [eventually_sourceLargeCount_div_le δ hδ,
      eventually_cutoffLogGap_bounds,
      tendsto_log_lowerCutoff_atTop.eventually (Filter.eventually_gt_atTop 0),
      Filter.eventually_gt_atTop 0] with n hs hg hL hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (sourceLargeCount δ n : ℝ) * cutoffLogGap n / n =
          ((sourceLargeCount δ n : ℝ) / n) * cutoffLogGap n := by ring
      _ ≤ (2 * ((targetLargeCount n : ℝ) / n) +
          Real.log 2 / Real.log (lowerCutoff n : ℝ)) * cutoffLogGap n :=
        mul_le_mul_of_nonneg_right hs hg.1
      _ = 2 * ((targetLargeCount n : ℝ) * cutoffLogGap n / n) +
          Real.log 2 * (cutoffLogGap n /
            Real.log (lowerCutoff n : ℝ)) := by
        have hLne := hL.ne'
        field_simp [hnreal.ne', hLne]
        <;> ring
      _ ≤ 2 * ((targetLargeCount n : ℝ) * cutoffLogGap n / n) +
          Real.log 2 * (cutoffGapUpper n /
            Real.log (lowerCutoff n : ℝ)) := by
        gcongr
        exact hg.2
  · exact hright

/-! ### Exact cleanup tools

The analytic part of the lower bound produces a large odd divisor of the
product of the approximate factors.  The next lemma distributes any divisor
of a finite product among the individual factors.  It is the finite,
constructive content of primality in `Nat`; importantly, it introduces no
choice principle beyond the ordinary classical choice already used for
finite tuples.
-/

lemma exists_pointwise_dvd_of_dvd_fin_prod {m P : ℕ} (b : Fin m → ℕ)
    (hP : P ∣ ∏ i, b i) :
    ∃ d : Fin m → ℕ, (∀ i, d i ∣ b i) ∧ ∏ i, d i = P := by
  induction m generalizing P with
  | zero =>
      have hP1 : P = 1 := Nat.dvd_one.mp (by simpa using hP)
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simpa [hP1]
  | succ m ih =>
      rw [Fin.prod_univ_succ] at hP
      obtain ⟨P₀, P₁, hP₀, hP₁, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hP
      obtain ⟨d, hd, hdprod⟩ := ih (fun i ↦ b i.succ) hP₁
      refine ⟨Fin.cons P₀ d, ?_, ?_⟩
      · intro i
        refine Fin.cases hP₀ (fun j ↦ ?_) i
        simpa using hd j
      · rw [Fin.prod_univ_succ]
        simpa [hdprod]

lemma nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k + 2 ^ k :=
          Nat.add_le_add_left (by have := Nat.two_pow_pos k; omega) _
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

lemma exists_power_two_ge {k d : ℕ} (hd : 0 < d) :
    ∃ e : ℕ, k ≤ d * 2 ^ e := by
  refine ⟨k, (nat_le_two_pow k).trans ?_⟩
  exact Nat.le_mul_of_pos_left _ hd

/-- The least exponent of two which raises `d` to at least `k`.  The zero
branch is irrelevant in the application but makes the definition total. -/
noncomputable def inflateExponent (k d : ℕ) : ℕ :=
  if hd : d = 0 then 0 else
    Nat.find (exists_power_two_ge (k := k) (Nat.pos_of_ne_zero hd))

lemma le_mul_pow_inflateExponent {k d : ℕ} (hd : 0 < d) :
    k ≤ d * 2 ^ inflateExponent k d := by
  rw [inflateExponent, dif_neg hd.ne']
  exact Nat.find_spec (exists_power_two_ge hd)

lemma inflateExponent_eq_zero_of_le {k d : ℕ} (hd : 0 < d) (hkd : k ≤ d) :
    inflateExponent k d = 0 := by
  rw [inflateExponent, dif_neg hd.ne']
  exact Nat.eq_zero_of_le_zero
    (Nat.find_min' (exists_power_two_ge hd) (by simpa using hkd))

/-- Minimality gives the one-bit overshoot bound used in the logarithmic
accounting: after restoring a positive damaged factor, it is strictly below
`2*k` unless no restoration was needed. -/
lemma mul_pow_inflateExponent_lt_two_mul {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hdk : d < k) :
    d * 2 ^ inflateExponent k d < 2 * k := by
  have hepos : 0 < inflateExponent k d := by
    by_contra he
    have he0 : inflateExponent k d = 0 := Nat.eq_zero_of_not_pos he
    have hle : k ≤ d := by
      simpa [he0] using (le_mul_pow_inflateExponent (k := k) hd)
    exact (not_le_of_gt hdk) hle
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hepos.ne'
  have hminimal : ¬ k ≤ d * 2 ^ e := by
    have hfind : inflateExponent k d =
        Nat.find (exists_power_two_ge (k := k) hd) := by
      simp [inflateExponent, hd.ne']
    exact Nat.find_min (exists_power_two_ge (k := k) hd) (by omega)
  rw [he, pow_succ]
  have hlt : d * 2 ^ e < k := Nat.lt_of_not_ge hminimal
  nlinarith

/-- Merge the excess entries of a long subfactorization into its first entry.
This is why harmless rounding to a length slightly larger than `n` causes no
problem in the approximate construction. -/
lemma feasible_of_long_subfactorization {n m k : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hk : 0 < k) (a : Fin m → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_dvd : (∏ i, a i) ∣ n.factorial) (ha_lower : ∀ i, k ≤ a i) :
    Feasible n k := by
  let l : List ℕ := List.ofFn a
  have hllen : l.length = m := by simp [l]
  have htake_len : (l.take n).length = n := by
    simp [List.length_take, hllen, Nat.min_eq_left hnm]
  have htake_ne : l.take n ≠ [] := by
    intro h
    have : (l.take n).length = 0 := by simp [h]
    omega
  obtain ⟨x, xs, htake⟩ := List.exists_cons_of_ne_nil htake_ne
  let merged : List ℕ := (x * (l.drop n).prod) :: xs
  have hmerged_len : merged.length = n := by
    have hcons_len : (x :: xs).length = n := htake ▸ htake_len
    simpa [merged] using hcons_len
  have hl_pos : ∀ y ∈ l, 0 < y := by
    intro y hy
    simp only [l, List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ha_pos i
  have hdrop_pos : 0 < (l.drop n).prod := by
    exact List.prod_pos fun y hy ↦ hl_pos y (List.mem_of_mem_drop hy)
  have hmerged_pos : ∀ y ∈ merged, 0 < y := by
    intro y hy
    change y ∈ (x * (l.drop n).prod) :: xs at hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · have hxmem : x ∈ l := by
        apply List.mem_of_mem_take (i := n)
        rw [htake]
        simp
      exact mul_pos (hl_pos x hxmem) hdrop_pos
    · have hymem : y ∈ l := by
        apply List.mem_of_mem_take (i := n)
        rw [htake]
        simp [hy]
      exact hl_pos y hymem
  have hmerged_lower : ∀ y ∈ merged, k ≤ y := by
    intro y hy
    change y ∈ (x * (l.drop n).prod) :: xs at hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · have hxmem : x ∈ l := by
        apply List.mem_of_mem_take (i := n)
        rw [htake]
        simp
      have hxlower : k ≤ x := by
        simp only [l, List.mem_ofFn] at hxmem
        obtain ⟨i, rfl⟩ := hxmem
        exact ha_lower i
      exact hxlower.trans (Nat.le_mul_of_pos_right x hdrop_pos)
    · have hymem : y ∈ l := by
        apply List.mem_of_mem_take (i := n)
        rw [htake]
        simp [hy]
      simp only [l, List.mem_ofFn] at hymem
      obtain ⟨i, rfl⟩ := hymem
      exact ha_lower i
  have hmerged_prod : merged.prod = ∏ i, a i := by
    calc
      merged.prod = (x * (l.drop n).prod) * xs.prod := by simp [merged]
      _ = (x * xs.prod) * (l.drop n).prod := by ac_rfl
      _ = (l.take n).prod * (l.drop n).prod := by simp [htake]
      _ = l.prod := List.prod_take_mul_prod_drop l n
      _ = ∏ i, a i := by simp [l, List.prod_ofFn]
  let e : Fin n ≃ Fin merged.length := finCongr hmerged_len.symm
  let b : Fin n → ℕ := fun i ↦ merged.get (e i)
  have hb_pos : ∀ i, 0 < b i := by
    intro i
    exact hmerged_pos _ (List.get_mem _ _)
  have hb_lower : ∀ i, k ≤ b i := by
    intro i
    exact hmerged_lower _ (List.get_mem _ _)
  have hb_prod : ∏ i, b i = ∏ i, a i := by
    calc
      ∏ i, b i = ∏ j : Fin merged.length, merged.get j := by
        apply Fintype.prod_equiv e
        intro i
        rfl
      _ = merged.prod := by rw [← List.prod_ofFn, List.ofFn_get]
      _ = ∏ i, a i := hmerged_prod
  exact feasible_of_subfactorization hn hk b hb_pos
    ((dvd_of_eq hb_prod).trans ha_dvd) hb_lower

/-- The part of an integer left after removing its complete power of two. -/
def twoFreePart (N : ℕ) : ℕ := N / ordProj[2] N

lemma twoFreePart_mul_ordProj (N : ℕ) :
    twoFreePart N * ordProj[2] N = N := by
  rw [twoFreePart, mul_comm]
  exact Nat.mul_div_cancel' (Nat.ordProj_dvd N 2)

lemma twoFreePart_pos {N : ℕ} (hN : 0 < N) : 0 < twoFreePart N := by
  apply Nat.div_pos (Nat.le_of_dvd hN (Nat.ordProj_dvd N 2))
  exact Nat.two_pow_pos _

/-- Exact two-adic cleanup.  Once positive divisors `d i` of the repaired odd
factors have been chosen, raise each one by its least necessary power of two.
If the sum of these exponents fits in the two-adic valuation of `n!`, the
result is an admissible subfactorization, and excess entries may be merged.
-/
lemma feasible_of_two_adic_cleanup {n m k : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hk : 0 < k) (d : Fin m → ℕ) (hd_pos : ∀ i, 0 < d i)
    (hd_odd : (∏ i, d i) ∣ twoFreePart n.factorial)
    (hexp : ∑ i, inflateExponent k (d i) ≤ n.factorial.factorization 2) :
    Feasible n k := by
  let a : Fin m → ℕ := fun i ↦ d i * 2 ^ inflateExponent k (d i)
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    exact mul_pos (hd_pos i) (Nat.two_pow_pos _)
  have ha_lower : ∀ i, k ≤ a i := by
    intro i
    exact le_mul_pow_inflateExponent (k := k) (hd_pos i)
  have hpow : 2 ^ (∑ i, inflateExponent k (d i)) ∣
      2 ^ n.factorial.factorization 2 := Nat.pow_dvd_pow 2 hexp
  have ha_prod : ∏ i, a i =
      (∏ i, d i) * 2 ^ (∑ i, inflateExponent k (d i)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    simpa using
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i : Fin m ↦ inflateExponent k (d i)) (2 : ℕ))
  have ha_dvd : (∏ i, a i) ∣ n.factorial := by
    rw [ha_prod]
    have hmul := Nat.mul_dvd_mul hd_odd hpow
    simpa [twoFreePart_mul_ordProj] using hmul
  exact feasible_of_long_subfactorization hn hnm hk a ha_pos ha_dvd ha_lower

/-! ### Completing the lower-bound construction -/

lemma twoFreePart_factorization (N : ℕ) :
    (twoFreePart N).factorization = N.factorization.erase 2 := by
  simpa [twoFreePart] using Nat.factorization_ordCompl N 2

noncomputable def cleanupProduct {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) : ℕ :=
  Nat.gcd (repairedProduct e) (twoFreePart n.factorial)

noncomputable def cleanupQuotient {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) : ℕ :=
  repairedProduct e / cleanupProduct e

lemma cleanupProduct_pos {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    0 < cleanupProduct e := by
  exact Nat.gcd_pos_of_pos_left _ (repairedProduct_pos e)

lemma cleanupProduct_dvd_repaired {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    cleanupProduct e ∣ repairedProduct e := by
  exact Nat.gcd_dvd_left _ _

lemma cleanupProduct_dvd_twoFree {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    cleanupProduct e ∣ twoFreePart n.factorial := by
  exact Nat.gcd_dvd_right _ _

lemma cleanupQuotient_pos {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    0 < cleanupQuotient e := by
  apply Nat.div_pos (Nat.le_of_dvd (repairedProduct_pos e)
    (cleanupProduct_dvd_repaired e))
  exact cleanupProduct_pos e

lemma cleanupQuotient_mul_cleanupProduct {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    cleanupQuotient e * cleanupProduct e = repairedProduct e := by
  exact Nat.div_mul_cancel (cleanupProduct_dvd_repaired e)

lemma cleanupQuotient_dvd_repaired {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    cleanupQuotient e ∣ repairedProduct e := by
  exact Nat.div_dvd_of_dvd (cleanupProduct_dvd_repaired e)

lemma cleanupQuotient_factorization {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    (cleanupQuotient e).factorization =
      (repairedProduct e).factorization - (cleanupProduct e).factorization := by
  exact Nat.factorization_div (cleanupProduct_dvd_repaired e)

lemma cleanupProduct_factorization {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    (cleanupProduct e).factorization =
      (repairedProduct e).factorization ⊓ n.factorial.factorization.erase 2 := by
  rw [cleanupProduct, Nat.factorization_gcd (repairedProduct_pos e).ne'
    (twoFreePart_pos (Nat.factorial_pos n)).ne', twoFreePart_factorization]

lemma cleanupQuotient_prime_le {δ : ℝ} {n p : ℕ} (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∈ (cleanupQuotient e).factorization.support) : p ≤ n := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvdQ : p ∣ cleanupQuotient e :=
    (Nat.mem_primeFactors.mp hp).2.1
  have hpdvdB : p ∣ repairedProduct e :=
    hpdvdQ.trans (cleanupQuotient_dvd_repaired e)
  have hpB : p ∈ (repairedProduct e).factorization.support := by
    rw [Finsupp.mem_support_iff]
    exact (hpprime.factorization_pos_of_dvd (repairedProduct_pos e).ne' hpdvdB).ne'
  exact repairedProduct_prime_le hn hupper e hpB

lemma cleanupQuotient_log_eq_factorization_sum {δ : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    Real.log (cleanupQuotient e : ℝ) =
      ∑ p ∈ Finset.range (n + 1),
        ((cleanupQuotient e).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (cleanupQuotient_prime_le hn hupper e hp))
  · intro p hpRange hpNot
    have hz : (cleanupQuotient e).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNot
    simp [hz]

lemma cleanupQuotient_factorization_ne_two {δ : ℝ} {n p : ℕ} (hn : 0 < n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) (hp2 : p ≠ 2) :
    (cleanupQuotient e).factorization p =
      (repairedProduct e).factorization p - n.factorial.factorization p := by
  rw [cleanupQuotient_factorization e, cleanupProduct_factorization hn e]
  simp [Finsupp.sub_apply, Finsupp.inf_apply, hp2]
  omega

lemma cleanupQuotient_factorization_two {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    (cleanupQuotient e).factorization 2 = 0 := by
  have h2not : 2 ∉ lowerLargePrimes n := by
    intro h
    have hgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).1
    omega
  rw [cleanupQuotient_factorization e, cleanupProduct_factorization hn e]
  simp [Finsupp.sub_apply, Finsupp.inf_apply,
    repairedProduct_factorization_of_not_mem e h2not,
    sourceValuation_two_eq_zero]

lemma cleanupQuotient_factorization_large {δ : ℝ} {n p : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∈ lowerLargePrimes n) :
    (cleanupQuotient e).factorization p = 0 := by
  have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hp2 : p ≠ 2 := by omega
  rw [cleanupQuotient_factorization_ne_two hn e hp2,
    repairedProduct_factorization_of_mem e hp]
  simp

lemma cleanupQuotient_factorization_small {δ : ℝ} {n p : ℕ} (hn : 0 < n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (hp : p ∈ lowerSmallPrimes n) :
    (cleanupQuotient e).factorization p =
      sourceValuation δ n p - n.factorial.factorization p := by
  have hp2 := (Finset.mem_filter.mp hp).2.2
  have hpLe : p ≤ lowerCutoff n := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  have hpNotLarge : p ∉ lowerLargePrimes n := by
    intro h
    have hgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).1
    omega
  rw [cleanupQuotient_factorization_ne_two hn e hp2,
    repairedProduct_factorization_of_not_mem e hpNotLarge]

lemma cleanupQuotient_log_le_smallError {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n) :
    Real.log (cleanupQuotient e : ℝ) ≤ smallValuationLogError δ n := by
  rw [cleanupQuotient_log_eq_factorization_sum hn hupper e,
    smallValuationLogError]
  have hpoint : ∀ p ∈ Finset.range (n + 1),
      ((cleanupQuotient e).factorization p : ℝ) * Real.log p ≤
        if p ∈ lowerSmallPrimes n then
          |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| *
            Real.log p else 0 := by
    intro p hpRange
    by_cases hpSmall : p ∈ lowerSmallPrimes n
    · rw [if_pos hpSmall, cleanupQuotient_factorization_small hn e hpSmall]
      have hpprime := (Finset.mem_filter.mp hpSmall).2.1
      have hlognonneg : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
      apply mul_le_mul_of_nonneg_right _ hlognonneg
      by_cases hle : n.factorial.factorization p ≤ sourceValuation δ n p
      · rw [Nat.cast_sub hle]
        exact le_abs_self _
      · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)]
        norm_num only [Nat.cast_zero]
        exact abs_nonneg _
    · rw [if_neg hpSmall]
      have hz : (cleanupQuotient e).factorization p = 0 := by
        by_cases hp2 : p = 2
        · subst p
          exact cleanupQuotient_factorization_two hn hL2 e
        · by_cases hpprime : p.Prime
          · have hple : p ≤ n := by
              have := Finset.mem_range.mp hpRange
              omega
            have hpgt : lowerCutoff n < p := by
              by_contra h
              have hpLe : p ≤ lowerCutoff n := Nat.le_of_not_gt h
              have hpS : p ∈ lowerSmallPrimes n := by
                simp [lowerSmallPrimes, hpprime, hp2, hpLe]
              exact hpSmall hpS
            have hpLarge : p ∈ lowerLargePrimes n := by
              simp [lowerLargePrimes, hpprime, hpgt, hple]
            exact cleanupQuotient_factorization_large hn hL2 e hpLarge
          · exact Nat.factorization_eq_zero_of_not_prime _ hpprime
      simp [hz]
  calc
    (∑ p ∈ Finset.range (n + 1),
        ((cleanupQuotient e).factorization p : ℝ) * Real.log p) ≤
        ∑ p ∈ Finset.range (n + 1),
          (if p ∈ lowerSmallPrimes n then
            |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| *
              Real.log p else 0) := Finset.sum_le_sum hpoint
    _ = ∑ p ∈ lowerSmallPrimes n,
        |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| *
          Real.log p := by
      let f : ℕ → ℝ := fun p ↦
        |(sourceValuation δ n p : ℝ) - n.factorial.factorization p| * Real.log p
      have hsubset : lowerSmallPrimes n ⊆ Finset.range (n + 1) := by
        exact fun p hp ↦ small_large_subset_range
          (Finset.mem_union_left _ hp)
      calc
        (∑ p ∈ Finset.range (n + 1),
            if p ∈ lowerSmallPrimes n then f p else 0) =
            ∑ p ∈ lowerSmallPrimes n,
              (if p ∈ lowerSmallPrimes n then f p else 0) := by
          apply (Finset.sum_subset hsubset ?_).symm
          intro p hpRange hpNot
          simp [hpNot]
        _ = ∑ p ∈ lowerSmallPrimes n, f p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [hp]

noncomputable def sourceLargeIndices (δ : ℝ) (n : ℕ) :
    Finset (Fin (approximateLength n)) :=
  Finset.univ.image (sourceOccurrenceIndex :
    SourceLargeOccurrence δ n → Fin (approximateLength n))

lemma card_sourceLargeIndices {δ : ℝ} {n : ℕ}
    (hn : 0 < n) (hsq : n ≤ lowerCutoff n ^ 2)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n) :
    (sourceLargeIndices δ n).card = sourceLargeCount δ n := by
  rw [sourceLargeIndices,
    Finset.card_image_of_injective Finset.univ
      (sourceOccurrenceIndex_injective hn hsq hupper),
    Finset.card_univ, card_sourceLargeOccurrence]

lemma repairedFactor_eq_approximateFactor_of_not_largeIndex {δ : ℝ} {n : ℕ}
    (hn : 0 < n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) (hi : i ∉ sourceLargeIndices δ n) :
    repairedFactor e i = approximateFactor δ n i := by
  have hno : ∀ x : SourceLargeOccurrence δ n,
      sourceOccurrenceIndex x ≠ i := by
    intro x hxi
    apply hi
    rw [sourceLargeIndices, Finset.mem_image]
    exact ⟨x, Finset.mem_univ x, hxi⟩
  have hfilter : sourceSmallExponent δ n i =
      (approximateFactor δ n i).factorization := by
    rw [sourceSmallExponent, Finsupp.filter_eq_self_iff]
    intro p hpval
    intro hpLarge
    have hvalpos : 0 < (approximateFactor δ n i).factorization p :=
      Nat.pos_of_ne_zero hpval
    let x : SourceLargeOccurrence δ n :=
      ⟨⟨p, hpLarge⟩, ⟨i, ⟨0, hvalpos⟩⟩⟩
    exact hno x rfl
  have hassigned : assignedTargetExponent e i = 0 := by
    rw [assignedTargetExponent]
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg (hno (e x))]
  rw [repairedFactor, repairedExponent, hfilter, hassigned, add_zero,
    Nat.prod_factorization_pow_eq_self (approximateFactor_pos hn i).ne']

def changedIndices {m : ℕ} (b d : Fin m → ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ d i ≠ b i

lemma changed_card_log_two_le_log_div {m : ℕ} (b d : Fin m → ℕ)
    (hbpos : ∀ i, 0 < b i) (hdpos : ∀ i, 0 < d i)
    (hdvd : ∀ i, d i ∣ b i) :
    ((changedIndices b d).card : ℝ) * Real.log 2 ≤
      Real.log (((∏ i, b i) / ∏ i, d i : ℕ) : ℝ) := by
  let q : Fin m → ℕ := fun i ↦ b i / d i
  have hqpos : ∀ i, 0 < q i := by
    intro i
    exact Nat.div_pos (Nat.le_of_dvd (hbpos i) (hdvd i)) (hdpos i)
  have hqchanged : ∀ i ∈ changedIndices b d, 2 ≤ q i := by
    intro i hi
    have hne : d i ≠ b i := (Finset.mem_filter.mp hi).2
    have hmul : d i * q i = b i := Nat.mul_div_cancel' (hdvd i)
    have hqne : q i ≠ 1 := by
      intro h
      rw [h, mul_one] at hmul
      exact hne hmul
    exact (Nat.two_le_iff (q i)).2 ⟨(hqpos i).ne', hqne⟩
  have hpow : 2 ^ (changedIndices b d).card ≤ ∏ i, q i := by
    calc
      2 ^ (changedIndices b d).card =
          ∏ _i ∈ changedIndices b d, 2 := by simp
      _ ≤ ∏ i ∈ changedIndices b d, q i := by
        exact Finset.prod_le_prod' hqchanged
      _ ≤ ∏ i, q i := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · exact Finset.filter_subset _ _
        · intro i hi
          omega
        · intro i hi hnot
          exact hqpos i
  have hprod : (∏ i, d i) * (∏ i, q i) = ∏ i, b i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact Nat.mul_div_cancel' (hdvd i)
  have hprodDpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ ↦ hdpos i
  have hqeq : (∏ i, q i) = (∏ i, b i) / ∏ i, d i :=
    Nat.eq_div_of_mul_eq_right hprodDpos.ne' hprod
  have hcast : ((2 ^ (changedIndices b d).card : ℕ) : ℝ) ≤
      ((∏ i, q i : ℕ) : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
      (2 ^ (changedIndices b d).card : ℕ)) hcast
  rw [Nat.cast_pow, Real.log_pow, hqeq] at hlog
  exact hlog

noncomputable def sourceLargeFactor (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : ℕ :=
  ((approximateFactor δ n i).factorization.filter
    (fun p ↦ p ∈ lowerLargePrimes n)).prod (fun p a ↦ p ^ a)

noncomputable def sourceSmallFactor (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : ℕ :=
  (sourceSmallExponent δ n i).prod (fun p a ↦ p ^ a)

noncomputable def assignedTargetFactor {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : ℕ :=
  (assignedTargetExponent e i).prod (fun p a ↦ p ^ a)

lemma repairedFactor_eq_parts {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) :
    repairedFactor e i = sourceSmallFactor δ n i * assignedTargetFactor e i := by
  rw [repairedFactor, repairedExponent, sourceSmallFactor, assignedTargetFactor,
    Finsupp.prod_add_index']
  · intro p
    simp
  · intro p a b
    rw [pow_add]

lemma approximateFactor_eq_parts {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (i : Fin (approximateLength n)) :
    approximateFactor δ n i = sourceSmallFactor δ n i * sourceLargeFactor δ n i := by
  rw [sourceSmallFactor, sourceSmallExponent, sourceLargeFactor]
  have hsplit := Finsupp.prod_filter_mul_prod_filter_not
    (fun p ↦ p ∉ lowerLargePrimes n)
    (approximateFactor δ n i).factorization (fun p a ↦ p ^ a)
  simp only [not_not] at hsplit
  exact (hsplit.trans (Nat.prod_factorization_pow_eq_self
    (approximateFactor_pos hn i).ne')).symm

lemma sourceLargeFactor_pos (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : 0 < sourceLargeFactor δ n i := by
  rw [sourceLargeFactor]
  exact Nat.pos_of_ne_zero ((Finsupp.prod_ne_zero_iff).2 fun p hp ↦ by
    have hpprime : p.Prime := by
      have hsupport := Finsupp.mem_support_iff.mp hp
      have hfac : (approximateFactor δ n i).factorization p ≠ 0 := by
        intro hz
        rw [Finsupp.filter_apply, hz] at hsupport
        simp at hsupport
      by_contra h
      exact hfac (Nat.factorization_eq_zero_of_not_prime _ h)
    exact pow_ne_zero _ hpprime.ne_zero)

lemma sourceSmallFactor_pos (δ : ℝ) (n : ℕ)
    (i : Fin (approximateLength n)) : 0 < sourceSmallFactor δ n i := by
  rw [sourceSmallFactor]
  exact Nat.pos_of_ne_zero ((Finsupp.prod_ne_zero_iff).2 fun p hp ↦ by
    have hpprime : p.Prime := by
      have hsupport := Finsupp.mem_support_iff.mp hp
      have hfac : (approximateFactor δ n i).factorization p ≠ 0 := by
        intro hz
        rw [sourceSmallExponent, Finsupp.filter_apply, hz] at hsupport
        simp at hsupport
      by_contra h
      exact hfac (Nat.factorization_eq_zero_of_not_prime _ h)
    exact pow_ne_zero _ hpprime.ne_zero)

lemma assignedTargetFactor_eq_prod {δ : ℝ} {n : ℕ}
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) :
    assignedTargetFactor e i = ∏ x : TargetLargeOccurrence n,
      if sourceOccurrenceIndex (e x) = i then targetOccurrencePrime x else 1 := by
  rw [assignedTargetFactor, assignedTargetExponent]
  let g : TargetLargeOccurrence n → ℕ →₀ ℕ := fun x ↦
    if sourceOccurrenceIndex (e x) = i then
      Finsupp.single (targetOccurrencePrime x) 1 else 0
  let h : TargetLargeOccurrence n → ℕ := fun x ↦
    if sourceOccurrenceIndex (e x) = i then targetOccurrencePrime x else 1
  have hprod : ∀ s : Finset (TargetLargeOccurrence n),
      (∑ x ∈ s, g x).prod (fun p a ↦ p ^ a) = ∏ x ∈ s, h x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx,
          Finsupp.prod_add_index'
            (h := fun p a : ℕ ↦ p ^ a) (fun _ ↦ by simp)
            (fun _ _ _ ↦ by rw [pow_add]), ih]
        dsimp [g, h]
        split_ifs with hidx
        · simp [Finsupp.prod_single_index, (targetOccurrence_data x).2.ne_zero]
        · simp
  simpa [g, h] using hprod Finset.univ

lemma assignedTargetFactor_le {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (sourceOccurrenceIndex :
      SourceLargeOccurrence δ n → Fin (approximateLength n)))
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) : assignedTargetFactor e i ≤ n := by
  rw [assignedTargetFactor_eq_prod]
  by_cases hex : ∃ x : TargetLargeOccurrence n,
      sourceOccurrenceIndex (e x) = i
  · obtain ⟨x, hx⟩ := hex
    calc
      (∏ y : TargetLargeOccurrence n,
          if sourceOccurrenceIndex (e y) = i then targetOccurrencePrime y else 1) =
          targetOccurrencePrime x := by
        have hsingle := Finset.prod_eq_single
          (s := (Finset.univ : Finset (TargetLargeOccurrence n)))
          (f := fun y ↦ if sourceOccurrenceIndex (e y) = i then
            targetOccurrencePrime y else 1) x
          (by
            intro y hy hyx
            have hne : sourceOccurrenceIndex (e y) ≠ i := by
              intro hyi
              have hey : e y = e x := hinj (hyi.trans hx.symm)
              exact hyx (e.injective hey)
            simp [hne])
          (by simp)
        simpa [hx] using hsingle
      _ ≤ n := (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (targetOccurrence_data x).1).1).2
  · have hall : ∀ x : TargetLargeOccurrence n,
        sourceOccurrenceIndex (e x) ≠ i := by
      intro x h
      exact hex ⟨x, h⟩
    rw [show (∏ x : TargetLargeOccurrence n,
      if sourceOccurrenceIndex (e x) = i then targetOccurrencePrime x else 1) = 1 by
      apply Finset.prod_eq_one
      intro x hx
      rw [if_neg (hall x)]]
    exact hn

lemma lowerCutoff_lt_sourceLargeFactor_of_mem {δ : ℝ} {n : ℕ}
    (i : Fin (approximateLength n)) (hi : i ∈ sourceLargeIndices δ n) :
    lowerCutoff n < sourceLargeFactor δ n i := by
  rw [sourceLargeIndices, Finset.mem_image] at hi
  obtain ⟨x, hx, hxi⟩ := hi
  have hxdata := sourceOccurrence_data x
  have hpMem := hxdata.1
  have hpgt := hxdata.2.2.1
  have hindex : sourceOccurrenceIndex x = i := hxi
  have hvalpos : 0 < (approximateFactor δ n i).factorization
      (sourceOccurrencePrime x) := by
    have hxval := x.2.2.isLt
    change x.2.2.1 < (approximateFactor δ n (sourceOccurrenceIndex x)).factorization
      (sourceOccurrencePrime x) at hxval
    rw [hindex] at hxval
    exact lt_of_le_of_lt (Nat.zero_le _) hxval
  have hsupportPrime : ∀ p ∈ ((approximateFactor δ n i).factorization.filter
      (fun p ↦ p ∈ lowerLargePrimes n)).support, p.Prime := by
    intro p hp
    have hfac : (approximateFactor δ n i).factorization p ≠ 0 := by
      have hs := Finsupp.mem_support_iff.mp hp
      intro hz
      rw [Finsupp.filter_apply, hz] at hs
      simp at hs
    by_contra h
    exact hfac (Nat.factorization_eq_zero_of_not_prime _ h)
  have hfactorization : (sourceLargeFactor δ n i).factorization =
      (approximateFactor δ n i).factorization.filter
        (fun p ↦ p ∈ lowerLargePrimes n) := by
    exact Nat.prod_pow_factorization_eq_self hsupportPrime
  have hpvalLarge : 0 < (sourceLargeFactor δ n i).factorization
      (sourceOccurrencePrime x) := by
    rw [hfactorization, Finsupp.filter_apply_pos _ _ hpMem]
    exact hvalpos
  have hpdvd : sourceOccurrencePrime x ∣ sourceLargeFactor δ n i :=
    Nat.dvd_of_factorization_pos hpvalLarge.ne'
  exact hpgt.trans_le (Nat.le_of_dvd (sourceLargeFactor_pos δ n i) hpdvd)

lemma repairedFactor_log_le_approximate_add_gap {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n)
    (hinj : Function.Injective (sourceOccurrenceIndex :
      SourceLargeOccurrence δ n → Fin (approximateLength n)))
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (i : Fin (approximateLength n)) :
    Real.log (repairedFactor e i : ℝ) ≤
      Real.log (approximateFactor δ n i : ℝ) + cutoffLogGap n := by
  have hLpos : 0 < lowerCutoff n := by omega
  have hLle : lowerCutoff n ≤ n := Nat.div_le_self _ _
  by_cases hi : i ∈ sourceLargeIndices δ n
  · have ha := assignedTargetFactor_le hn hinj e i
    have hl := (lowerCutoff_lt_sourceLargeFactor_of_mem i hi).le
    have hspos := sourceSmallFactor_pos δ n i
    have hmul : repairedFactor e i * lowerCutoff n ≤
        approximateFactor δ n i * n := by
      rw [repairedFactor_eq_parts, approximateFactor_eq_parts hn]
      calc
        sourceSmallFactor δ n i * assignedTargetFactor e i * lowerCutoff n =
            sourceSmallFactor δ n i *
              (assignedTargetFactor e i * lowerCutoff n) := by ac_rfl
        _ ≤ sourceSmallFactor δ n i *
              (n * sourceLargeFactor δ n i) := by
          gcongr
        _ = sourceSmallFactor δ n i * sourceLargeFactor δ n i * n := by
          ac_rfl
    have hmulReal : (repairedFactor e i : ℝ) * lowerCutoff n ≤
        (approximateFactor δ n i : ℝ) * n := by exact_mod_cast hmul
    have hleftpos : (0 : ℝ) < (repairedFactor e i : ℝ) * lowerCutoff n :=
      mul_pos (by exact_mod_cast repairedFactor_pos e i) (by exact_mod_cast hLpos)
    have hlog := Real.log_le_log hleftpos hmulReal
    rw [Real.log_mul (by exact_mod_cast (repairedFactor_pos e i).ne')
        (by exact_mod_cast hLpos.ne'),
      Real.log_mul (by exact_mod_cast (approximateFactor_pos hn i).ne')
        (by exact_mod_cast hn.ne')] at hlog
    dsimp [cutoffLogGap]
    linarith
  · rw [repairedFactor_eq_approximateFactor_of_not_largeIndex hn e i hi]
    have hlogle : Real.log (lowerCutoff n : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hLpos) (by exact_mod_cast hLle)
    dsimp [cutoffLogGap]
    linarith

lemma inflateExponent_log_bound {k d c : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hc : 0 < c) (hkc : k ≤ c) :
    (inflateExponent k d : ℝ) * Real.log 2 ≤
      if d < k then Real.log (c : ℝ) - Real.log (d : ℝ) + Real.log 2 else 0 := by
  by_cases hdk : d < k
  · rw [if_pos hdk]
    have hmul := mul_pow_inflateExponent_lt_two_mul hk hd hdk
    have hmulReal : (d : ℝ) * 2 ^ inflateExponent k d < 2 * k := by
      exact_mod_cast hmul
    have hleftpos : (0 : ℝ) < (d : ℝ) * 2 ^ inflateExponent k d :=
      mul_pos (by exact_mod_cast hd) (by positivity)
    have hrightpos : (0 : ℝ) < 2 * k :=
      mul_pos (by norm_num) (by exact_mod_cast hk)
    have hlog := Real.strictMonoOn_log hleftpos hrightpos hmulReal
    have hlogkc : Real.log (k : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkc)
    rw [Real.log_mul (by exact_mod_cast hd.ne') (by positivity :
        ((2 : ℝ) ^ inflateExponent k d) ≠ 0),
      Real.log_pow,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hk.ne')] at hlog
    linarith
  · have hkd : k ≤ d := Nat.le_of_not_gt hdk
    rw [if_neg hdk, inflateExponent_eq_zero_of_le hd hkd]
    simp

/-- Logarithmic accounting for the two-adic restoration.  The first term is
the total logarithmic loss caused by replacing the source large primes; the
next two terms pay only for indices which originally contained such a prime;
and the final two copies of the cleanup quotient pay for lost odd factors and
the one-bit rounding in the least power of two. -/
lemma sum_inflateExponent_log_bound {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hL2 : 2 ≤ lowerCutoff n) (hsq : n ≤ lowerCutoff n ^ 2)
    (hupper : oddCeilNat (lowerTarget δ n) + 2 * lowerBlocks n ≤ n)
    (e : TargetLargeOccurrence n ↪ SourceLargeOccurrence δ n)
    (d : Fin (approximateLength n) → ℕ) (hdpos : ∀ i, 0 < d i)
    (hdvd : ∀ i, d i ∣ repairedFactor e i)
    (hdprod : ∏ i, d i = cleanupProduct e) :
    ((∑ i, inflateExponent (lowerTarget δ n) (d i) : ℕ) : ℝ) *
        Real.log 2 ≤
      sourceLargeLog δ n - targetLargeLog n +
        (sourceLargeCount δ n : ℝ) * cutoffLogGap n +
        (sourceLargeCount δ n : ℝ) * Real.log 2 +
        2 * Real.log (cleanupQuotient e : ℝ) := by
  let S := sourceLargeIndices δ n
  let b : Fin (approximateLength n) → ℕ := fun i ↦ repairedFactor e i
  let c : Fin (approximateLength n) → ℕ := fun i ↦ approximateFactor δ n i
  let k := lowerTarget δ n
  have hk : 0 < k := by
    dsimp [k, lowerTarget]
    exact Nat.ceil_pos.mpr (div_pos (by exact_mod_cast hn) (Real.exp_pos _))
  have hbpos : ∀ i, 0 < b i := fun i ↦ repairedFactor_pos e i
  have hcpos : ∀ i, 0 < c i := fun i ↦ approximateFactor_pos hn i
  have hkc : ∀ i, k ≤ c i := fun i ↦ lowerTarget_le_approximateFactor δ n i
  have hinj := sourceOccurrenceIndex_injective (δ := δ) hn hsq hupper
  have hgap : 0 ≤ cutoffLogGap n := by
    dsimp [cutoffLogGap]
    have hLpos : (0 : ℝ) < lowerCutoff n := by exact_mod_cast (by omega : 0 < lowerCutoff n)
    have hLle : (lowerCutoff n : ℝ) ≤ n := by
      exact_mod_cast (show lowerCutoff n ≤ n by
        exact Nat.div_le_self n (lowerScale n ^ 3))
    exact sub_nonneg.mpr (Real.log_le_log hLpos hLle)
  have hlogB : Real.log (repairedProduct e : ℝ) =
      ∑ i, Real.log (b i : ℝ) := by
    rw [repairedProduct, Nat.cast_prod, Real.log_prod]
    intro i hi
    exact_mod_cast (hbpos i).ne'
  have hlogD : Real.log (cleanupProduct e : ℝ) =
      ∑ i, Real.log (d i : ℝ) := by
    rw [← hdprod, Nat.cast_prod, Real.log_prod]
    intro i hi
    exact_mod_cast (hdpos i).ne'
  have hlogQuotient :
      (∑ i, Real.log (b i : ℝ)) - (∑ i, Real.log (d i : ℝ)) =
        Real.log (cleanupQuotient e : ℝ) := by
    have hQpos : (0 : ℝ) < cleanupQuotient e := by
      exact_mod_cast cleanupQuotient_pos e
    have hPpos : (0 : ℝ) < cleanupProduct e := by
      exact_mod_cast cleanupProduct_pos e
    have hmul : Real.log (repairedProduct e : ℝ) =
        Real.log (cleanupQuotient e : ℝ) +
          Real.log (cleanupProduct e : ℝ) := by
      rw [← Real.log_mul hQpos.ne' hPpos.ne', ← Nat.cast_mul,
        cleanupQuotient_mul_cleanupProduct]
    rw [← hlogB, ← hlogD]
    linarith
  have hA :
      ∑ i, (if d i < k then
          Real.log (c i : ℝ) - Real.log (b i : ℝ) else 0) ≤
        sourceLargeLog δ n - targetLargeLog n +
          (sourceLargeCount δ n : ℝ) * cutoffLogGap n := by
    calc
      (∑ i, (if d i < k then
          Real.log (c i : ℝ) - Real.log (b i : ℝ) else 0)) ≤
          ∑ i, ((Real.log (c i : ℝ) - Real.log (b i : ℝ)) +
            if i ∈ S then cutoffLogGap n else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hlow : d i < k <;> by_cases hiS : i ∈ S
        · simp [hlow, hiS]
          exact hgap
        · simp [hlow, hiS]
        · simp only [if_neg hlow, if_pos hiS]
          have hrepair := repairedFactor_log_le_approximate_add_gap
            hn hL2 hinj e i
          dsimp [b, c]
          linarith
        · simp only [if_neg hlow, if_neg hiS]
          have heq := repairedFactor_eq_approximateFactor_of_not_largeIndex
            hn e i hiS
          dsimp [b, c]
          rw [heq]
          linarith
      _ = (∑ i, Real.log (c i : ℝ)) -
            (∑ i, Real.log (b i : ℝ)) +
          (S.card : ℝ) * cutoffLogGap n := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp
        <;> ring
      _ = sourceLargeLog δ n - targetLargeLog n +
          (sourceLargeCount δ n : ℝ) * cutoffLogGap n := by
        have hBident := repairedProduct_log_identity hn hupper e
        have hScard := card_sourceLargeIndices (δ := δ) hn hsq hupper
        dsimp [c, approximateLog] at hBident ⊢
        rw [← hlogB, hBident, show S.card = sourceLargeCount δ n by
          simpa [S] using hScard]
        ring
  have hB :
      ∑ i, (if d i < k then
          Real.log (b i : ℝ) - Real.log (d i : ℝ) else 0) ≤
        Real.log (cleanupQuotient e : ℝ) := by
    calc
      (∑ i, (if d i < k then
          Real.log (b i : ℝ) - Real.log (d i : ℝ) else 0)) ≤
          ∑ i, (Real.log (b i : ℝ) - Real.log (d i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hlow : d i < k
        · simp [hlow]
        · rw [if_neg hlow]
          have hdle : d i ≤ b i := Nat.le_of_dvd (hbpos i) (hdvd i)
          have hlogle : Real.log (d i : ℝ) ≤ Real.log (b i : ℝ) :=
            Real.log_le_log (by exact_mod_cast hdpos i) (by exact_mod_cast hdle)
          linarith
      _ = Real.log (cleanupQuotient e : ℝ) := by
        rw [Finset.sum_sub_distrib]
        exact hlogQuotient
  have hC :
      ∑ i, (if d i < k then Real.log 2 else 0) ≤
        (sourceLargeCount δ n : ℝ) * Real.log 2 +
          Real.log (cleanupQuotient e : ℝ) := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hpoint : ∀ i, (if d i < k then Real.log 2 else 0) ≤
        (if i ∈ S then Real.log 2 else 0) +
          (if d i ≠ b i then Real.log 2 else 0) := by
      intro i
      by_cases hlow : d i < k
      · by_cases hiS : i ∈ S
        · by_cases hchanged : d i ≠ b i <;>
            simp [hlow, hiS, hchanged, hlog2]
        · have heqB := repairedFactor_eq_approximateFactor_of_not_largeIndex
            hn e i hiS
          by_cases hchanged : d i ≠ b i
          · simp [hlow, hiS, hchanged]
          · exfalso
            have heqDB : d i = b i := not_not.mp hchanged
            have hdc : d i = c i := by
              exact heqDB.trans (by simpa [b, c] using heqB)
            have hck : c i < k := by simpa [hdc] using hlow
            exact (not_lt_of_ge (hkc i)) hck
      · by_cases hiS : i ∈ S <;> by_cases hchanged : d i ≠ b i <;>
          simp [hlow, hiS, hchanged, hlog2]
    calc
      (∑ i, (if d i < k then Real.log 2 else 0)) ≤
          ∑ i, ((if i ∈ S then Real.log 2 else 0) +
            (if d i ≠ b i then Real.log 2 else 0)) :=
        Finset.sum_le_sum fun i hi ↦ hpoint i
      _ = (S.card : ℝ) * Real.log 2 +
          ((changedIndices b d).card : ℝ) * Real.log 2 := by
        rw [Finset.sum_add_distrib]
        congr 1
        · change (∑ i ∈ Finset.univ, if i ∈ S then Real.log 2 else 0) = _
          rw [← Finset.sum_filter]
          simp
        · change (∑ i ∈ Finset.univ, if d i ≠ b i then Real.log 2 else 0) = _
          rw [← Finset.sum_filter]
          simp [changedIndices]
      _ ≤ (sourceLargeCount δ n : ℝ) * Real.log 2 +
          Real.log (cleanupQuotient e : ℝ) := by
        have hScard := card_sourceLargeIndices (δ := δ) hn hsq hupper
        have hchanged := changed_card_log_two_le_log_div b d hbpos hdpos hdvd
        have hquot : ((∏ i, b i) / ∏ i, d i : ℕ) = cleanupQuotient e := by
          dsimp [b, cleanupQuotient, repairedProduct]
          rw [hdprod]
        rw [hquot] at hchanged
        rw [show S.card = sourceLargeCount δ n by simpa [S] using hScard]
        linarith
  calc
    ((∑ i, inflateExponent k (d i) : ℕ) : ℝ) * Real.log 2 =
        ∑ i, (inflateExponent k (d i) : ℝ) * Real.log 2 := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ ∑ i, (if d i < k then
          Real.log (c i : ℝ) - Real.log (d i : ℝ) + Real.log 2 else 0) := by
      exact Finset.sum_le_sum fun i hi ↦
        inflateExponent_log_bound hk (hdpos i) (hcpos i) (hkc i)
    _ = (∑ i, (if d i < k then
          Real.log (c i : ℝ) - Real.log (b i : ℝ) else 0)) +
        (∑ i, (if d i < k then
          Real.log (b i : ℝ) - Real.log (d i : ℝ) else 0)) +
        ∑ i, (if d i < k then Real.log 2 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hlow : d i < k <;> simp [hlow]
    _ ≤ (sourceLargeLog δ n - targetLargeLog n +
          (sourceLargeCount δ n : ℝ) * cutoffLogGap n) +
        Real.log (cleanupQuotient e : ℝ) +
        ((sourceLargeCount δ n : ℝ) * Real.log 2 +
          Real.log (cleanupQuotient e : ℝ)) := by
      gcongr
    _ = sourceLargeLog δ n - targetLargeLog n +
        (sourceLargeCount δ n : ℝ) * cutoffLogGap n +
        (sourceLargeCount δ n : ℝ) * Real.log 2 +
        2 * Real.log (cleanupQuotient e : ℝ) := by ring

noncomputable def restorationError (δ : ℝ) (n : ℕ) : ℝ :=
  (sourceLargeCount δ n : ℝ) * cutoffLogGap n +
    (sourceLargeCount δ n : ℝ) * Real.log 2 +
    2 * smallValuationLogError δ n

lemma tendsto_restorationError_div (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ restorationError δ n / n)
      Filter.atTop (nhds 0) := by
  have hweighted := tendsto_sourceLargeCount_mul_cutoffLogGap_div δ hδ
  have hcount := (tendsto_sourceLargeCount_div δ hδ).mul_const (Real.log 2)
  have hsmall := (tendsto_smallValuationLogError δ hδ).const_mul 2
  have h := hweighted.add (hcount.add hsmall)
  convert h using 1
  · funext n
    dsimp [restorationError]
    ring
  · norm_num

lemma tendsto_twoValuationLoss_div :
    Tendsto (fun n : ℕ ↦
      ((2 * Real.log (n : ℝ) + 1) * Real.log 2) / n)
      Filter.atTop (nhds 0) := by
  have hone : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
  have h := ((tendsto_log_div_nat.const_mul 2).add hone).mul_const (Real.log 2)
  convert h using 1
  · funext n
    ring
  · norm_num

/-- For every fixed positive reserve `δ < log 2`, the ACRSTUV matching and
cleanup construction eventually gives an honest factorial representation
whose every entry is at least `ceil (n / exp (1 + δ))`. -/
lemma eventually_feasible_lowerTarget (δ : ℝ) (hδ : 0 < δ)
    (hδlog : δ < Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop, Feasible n (lowerTarget δ n) := by
  have hr := (tendsto_restorationError_div δ hδ).eventually
    (Metric.closedBall_mem_nhds 0 (by positivity : (0 : ℝ) < δ / 4))
  have hv := tendsto_twoValuationLoss_div.eventually
    (Metric.closedBall_mem_nhds 0 (by positivity : (0 : ℝ) < δ / 4))
  filter_upwards [Filter.eventually_ge_atTop 2,
      eventually_two_le_lowerCutoff, eventually_lowerCutoff_sq_ge,
      eventually_approximateFactor_upper δ hδ,
      eventually_targetLargeCount_le_sourceLargeCount δ hδ hδlog,
      eventually_largeLog_surplus_upper δ hδ, hr, hv] with
      n hn2 hL2 hsq hupper hcount hsurplus hr hv
  have hn : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < lowerTarget δ n := by
    dsimp [lowerTarget]
    exact Nat.ceil_pos.mpr (div_pos hnreal (Real.exp_pos _))
  let e := largeOccurrenceMatching hcount
  have hcleanupDvd : cleanupProduct e ∣
      ∏ i : Fin (approximateLength n), repairedFactor e i := by
    simpa [repairedProduct] using cleanupProduct_dvd_repaired e
  obtain ⟨d, hdvd, hdprod⟩ := exists_pointwise_dvd_of_dvd_fin_prod
    (fun i : Fin (approximateLength n) ↦ repairedFactor e i) hcleanupDvd
  have hdpos : ∀ i, 0 < d i := by
    intro i
    by_contra h
    have hdi : d i = 0 := Nat.eq_zero_of_not_pos h
    have hprodZero : ∏ j, d j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hdi
    rw [hdprod] at hprodZero
    exact (cleanupProduct_pos e).ne' hprodZero
  have hlogQ := cleanupQuotient_log_le_smallError hn hL2 hupper e
  have hsumLog := sum_inflateExponent_log_bound hn hL2 hsq hupper e
    d hdpos hdvd hdprod
  have hrnorm : restorationError δ n / n ≤ δ / 4 := by
    rw [Real.dist_eq, sub_zero] at hr
    exact (le_abs_self _).trans hr
  have hrraw : restorationError δ n ≤ (δ / 4) * n := by
    rw [div_le_iff₀ hnreal] at hrnorm
    simpa [mul_comm] using hrnorm
  have hvnorm : ((2 * Real.log (n : ℝ) + 1) * Real.log 2) / n ≤
      δ / 4 := by
    rw [Real.dist_eq, sub_zero] at hv
    exact (le_abs_self _).trans hv
  have hvraw : (2 * Real.log (n : ℝ) + 1) * Real.log 2 ≤
      (δ / 4) * n := by
    rw [div_le_iff₀ hnreal] at hvnorm
    simpa [mul_comm] using hvnorm
  have hsumUpper :
      ((∑ i, inflateExponent (lowerTarget δ n) (d i) : ℕ) : ℝ) *
          Real.log 2 ≤ (Real.log 2 - δ / 4) * n := by
    dsimp [restorationError] at hrraw
    nlinarith
  have hvalLower := factorial_two_valuation_real_lower hn2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvalMul :
      ((n : ℝ) - (2 * Real.log (n : ℝ) + 1)) * Real.log 2 ≤
        (n.factorial.factorization 2 : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hvalLower hlog2pos.le
  have hsumCast :
      ((∑ i, inflateExponent (lowerTarget δ n) (d i) : ℕ) : ℝ) ≤
        (n.factorial.factorization 2 : ℝ) := by
    have hsumMul :
        ((∑ i, inflateExponent (lowerTarget δ n) (d i) : ℕ) : ℝ) *
            Real.log 2 ≤
          (n.factorial.factorization 2 : ℝ) * Real.log 2 := by
      calc
      ((∑ i, inflateExponent (lowerTarget δ n) (d i) : ℕ) : ℝ) *
          Real.log 2 ≤ (Real.log 2 - δ / 4) * n := hsumUpper
      _ ≤ ((n : ℝ) - (2 * Real.log (n : ℝ) + 1)) * Real.log 2 := by
        nlinarith
      _ ≤ (n.factorial.factorization 2 : ℝ) * Real.log 2 := hvalMul
    nlinarith
  have hexp : ∑ i, inflateExponent (lowerTarget δ n) (d i) ≤
      n.factorial.factorization 2 := by exact_mod_cast hsumCast
  apply feasible_of_two_adic_cleanup hn (le_approximateLength n) hk d hdpos
  · rw [hdprod]
    exact cleanupProduct_dvd_twoFree e
  · exact hexp

lemma eventually_one_div_exp_le_ratio (δ : ℝ) (hδ : 0 < δ)
    (hδlog : δ < Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 / Real.exp (1 + δ) ≤ ratio n := by
  filter_upwards [eventually_feasible_lowerTarget δ hδ hδlog,
    Filter.eventually_gt_atTop 0] with n hfeasible hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : lowerTarget δ n ≤ t n := feasible_le_t hn hfeasible
  have hceil : (n : ℝ) / Real.exp (1 + δ) ≤ lowerTarget δ n := by
    exact Nat.le_ceil _
  rw [ratio]
  calc
    1 / Real.exp (1 + δ) =
        ((n : ℝ) / Real.exp (1 + δ)) / n := by field_simp
    _ ≤ (lowerTarget δ n : ℝ) / n := by
      exact div_le_div_of_nonneg_right hceil hnreal.le
    _ ≤ (t n : ℝ) / n := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast ht) hnreal.le

/-- The first question in Problem 391: the normalized maximal least factor
converges to `1/e`. -/
theorem tendsto_ratio :
    Tendsto ratio Filter.atTop (nhds (1 / Real.exp 1)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · by_cases ha0 : 0 < a
    · have haexp : a < Real.exp (-1) := by
        simpa [Real.exp_neg] using ha
      have hloga : Real.log a < -1 :=
        (Real.log_lt_iff_lt_exp ha0).2 haexp
      let δ : ℝ := min ((-1 - Real.log a) / 2) (Real.log 2 / 2)
      have hfirst : 0 < (-1 - Real.log a) / 2 := by linarith
      have hsecond : 0 < Real.log 2 / 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      have hδ : 0 < δ := by simp [δ, hfirst, hsecond]
      have hδa : δ < -1 - Real.log a := by
        have hle : δ ≤ (-1 - Real.log a) / 2 := min_le_left _ _
        linarith
      have hδlog : δ < Real.log 2 := by
        have hle : δ ≤ Real.log 2 / 2 := min_le_right _ _
        linarith
      have halower : a < 1 / Real.exp (1 + δ) := by
        have hlog : Real.log a < -(1 + δ) := by linarith
        have hexp : a < Real.exp (-(1 + δ)) :=
          (Real.log_lt_iff_lt_exp ha0).1 hlog
        simpa only [Real.exp_neg, one_div] using hexp
      filter_upwards [eventually_one_div_exp_le_ratio δ hδ hδlog] with n hn
      exact halower.trans_le hn
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hr := ratio_pos hn
      exact (not_lt.mp ha0).trans_lt hr
  · have hlimitPos : 0 < 1 / Real.exp 1 := by positivity
    have hbpos : 0 < b := hlimitPos.trans hb
    have hexp : Real.exp (-1) < b := by
      simpa [Real.exp_neg] using hb
    have hlogb : -1 < Real.log b :=
      (Real.lt_log_iff_exp_lt hbpos).2 hexp
    let δ : ℝ := (Real.log b + 1) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have harg : -1 + δ < Real.log b := by dsimp [δ]; linarith
    have hexpUpper : Real.exp (-1 + δ) < b :=
      (Real.lt_log_iff_exp_lt hbpos).1 harg
    filter_upwards [eventually_ratio_le_exp δ hδ] with n hn
    exact hn.trans_lt hexpUpper

/-- A maximizing representation exists, and its first (smallest) factor is
exactly `t n`, matching the indexing in the original problem. -/
theorem exists_maximizing_representation {n : ℕ} (hn : 0 < n) :
    ∃ a : Fin n → ℕ,
      IsFactorialRepresentation n a ∧ a ⟨0, hn⟩ = t n := by
  obtain ⟨_htpos, a, ha, hta⟩ := t_feasible hn
  refine ⟨a, ha, le_antisymm ?_ (hta ⟨0, hn⟩)⟩
  have hfirst : ∀ i, a ⟨0, hn⟩ ≤ a i := by
    intro i
    apply ha.2.1
    change 0 ≤ i.1
    omega
  have hfeas : Feasible n (a ⟨0, hn⟩) := by
    refine ⟨ha.1 ⟨0, hn⟩, a, ha, hfirst⟩
  exact feasible_le_t hn hfeas

/-- Complete resolution of the two questions in Erdős Problem 391.  The
second conjunct is stronger than requested: the logarithmic deficit used to
prove it holds for every sufficiently large integer. -/
theorem erdos_391 :
    Tendsto ratio Filter.atTop (nhds (1 / Real.exp 1)) ∧
      ∃ c : ℝ, 0 < c ∧
        {n : ℕ | ratio n ≤ 1 / Real.exp 1 - c / Real.log n}.Infinite := by
  exact ⟨tendsto_ratio, infinitely_many_ratio_le_sub_deficit⟩

end

end

#print axioms erdos_391
-- 'Erdos391.erdos_391' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos391
