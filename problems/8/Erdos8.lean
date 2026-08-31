import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos8

/-
# Problem Description

Erdős Problem 8, conjectured by Erdős and Graham. For any finite colouring of the integers,
is there a covering system all of whose moduli are monochromatic? `erdos_8` proves that the
answer is no.

The disproof rests on Hough's bound on the least modulus of a covering system, which is
Erdős Problem 2 — `hough_minimum_modulus_bound` below draws it directly from
`Erdos2.uniformMinimumBound`. Given a bound `B` on the least modulus, colour every integer
of absolute value at most `B` by that absolute value and everything else `0`; then no
covering system can have all its moduli one colour. This is the colouring the problem page
describes.

`Monochromatic colour D` is `∃ k, ∀ d ∈ D, colour d = k`, and `IsDistinctCoveringSystem D a`
is as in Problem 2: moduli distinct (they form a `Finset`), each at least `2`, and every
integer congruent to `a d` mod some `d ∈ D`.
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

scoped[Chebyshev] notation "ϑ" => Erdos8.chebyshev_first
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


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos448/MertensEulerProduct448.lean` -/

section
open Asymptotics Filter Finset Real
open scoped BigOperators Topology

namespace Erdos448

/-! A sharp-enough consequence of the formalized second Mertens theorem. -/

lemma eventually_prime_reciprocal_sum_le_loglog_add_one :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ≤
        Real.log (Real.log (N : ℝ)) + meissel_mertens + 1 := by
  obtain ⟨c, hc⟩ := prime_reciprocal.bound
  have hcnat := tendsto_natCast_atTop_atTop.eventually hc
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 |c| ≤ Real.log (N : ℝ) :=
    tendsto_log_coe_at_top.eventually_ge_atTop (max 1 |c|)
  filter_upwards [hcnat, hlarge] with N hN hlog
  have hlogpos : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans_le ((le_max_left 1 |c|).trans hlog)
  have hnorm_inv : ‖(Real.log (N : ℝ))⁻¹‖ = (Real.log (N : ℝ))⁻¹ :=
    norm_of_nonneg (inv_nonneg.mpr hlogpos.le)
  have hc_le_log : c ≤ Real.log (N : ℝ) :=
    (le_abs_self c).trans ((le_max_right 1 |c|).trans hlog)
  have hmul : c * ‖(Real.log (N : ℝ))⁻¹‖ ≤ 1 := by
    rw [hnorm_inv]
    change c / Real.log (N : ℝ) ≤ 1
    exact (div_le_one hlogpos).2 hc_le_log
  have herr :
      prime_summatory (fun p : ℕ => (p : ℝ)⁻¹) 1 (N : ℝ) -
          (Real.log (Real.log (N : ℝ)) + meissel_mertens) ≤ 1 :=
    (le_norm_self _).trans (hN.trans hmul)
  simpa [prime_summatory] using (sub_le_iff_le_add'.mp herr)

lemma sum_Icc_two_inv_mul_pred_eq {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
        (((n : ℝ) * ((n : ℝ) - 1))⁻¹)) = 1 - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hmem : n + 1 ∉ Finset.Icc 2 n := by simp
      have hIcc : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
        ext m
        simp
        omega
      rw [hIcc, Finset.sum_insert hmem, ih]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hspos : (0 : ℝ) < n + 1 := by positivity
      push_cast
      field_simp [hnpos.ne', hspos.ne']
      ring

lemma prime_correction_sum_le_one (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (((p : ℝ) * ((p : ℝ) - 1))⁻¹)) ≤ 1 := by
  classical
  by_cases hN : 2 ≤ N
  · have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.Icc 2 N := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, (Finset.mem_Icc.mp hp'.1).2⟩
    calc
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((p : ℝ) * ((p : ℝ) - 1))⁻¹))
          ≤ ∑ n ∈ Finset.Icc 2 N, (((n : ℝ) * ((n : ℝ) - 1))⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro n hn _
            have hn' := Finset.mem_Icc.mp hn
            have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn'.1
            exact inv_nonneg.mpr
              (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith)))
      _ = 1 - (N : ℝ)⁻¹ := sum_Icc_two_inv_mul_pred_eq hN
      _ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  · have hNle : N ≤ 1 := by omega
    have hempty : (Finset.Icc 1 N).filter Nat.Prime = ∅ := by
      ext p
      constructor
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        have hp2 := hp'.2.two_le
        have hpN := (Finset.mem_Icc.mp hp'.1).2
        omega
      · intro hp
        simp at hp
    simp [hempty]

lemma half_inv_pred_eq (p : ℕ) (hp : Nat.Prime p) :
    (2 * ((p : ℝ) - 1))⁻¹ =
      (1 / 2 : ℝ) * ((p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp [hp0, hp1]
  ring

lemma half_prime_pred_sum_le (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (2 * ((p : ℝ) - 1))⁻¹) ≤
      (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 := by
  calc
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (2 * ((p : ℝ) - 1))⁻¹)
        = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (1 / 2 : ℝ) *
              ((p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact half_inv_pred_eq p (Finset.mem_filter.mp hp).2
    _ = (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) +
        (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) +
        (1 / 2 : ℝ) * 1 := by
          gcongr
          exact prime_correction_sum_le_one N
    _ = (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 := by ring

lemma finite_product_one_add_le_exp_sum
    (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n ∈ s, 0 ≤ f n) :
    s.prod (fun n => 1 + f n) ≤ Real.exp (s.sum f) := by
  calc
    s.prod (fun n => 1 + f n) ≤ s.prod (fun n => Real.exp (f n)) := by
      exact Finset.prod_le_prod
        (fun n hn => add_nonneg zero_le_one (hf n hn))
        (fun n hn => by simpa [add_comm] using Real.add_one_le_exp (f n))
    _ = Real.exp (s.sum f) := by rw [← Real.exp_sum]

noncomputable def mertensHalfEulerConstant : ℝ :=
  Real.exp (meissel_mertens / 2 + 1)

lemma mertensHalfEulerConstant_pos : 0 < mertensHalfEulerConstant := by
  exact Real.exp_pos _

theorem eventually_prime_half_euler_product_le :
    ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter Nat.Prime).prod
          (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) ≤
        mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
  filter_upwards [eventually_prime_reciprocal_sum_le_loglog_add_one,
      tendsto_log_coe_at_top.eventually_gt_atTop 0] with N hrec hlogpos
  let S := (Finset.Icc 1 N).filter Nat.Prime
  let w : ℕ → ℝ := fun p => (2 * ((p : ℝ) - 1))⁻¹
  have hw : ∀ p ∈ S, 0 ≤ w p := by
    intro p hp
    have hp' : (1 : ℝ) < p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    dsimp [w]
    positivity
  have hsum : S.sum w ≤
      (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1) := by
    have hhalf := half_prime_pred_sum_le N
    dsimp [S, w]
    calc
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (2 * ((p : ℝ) - 1))⁻¹)
          ≤ (1 / 2 : ℝ) *
              (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 :=
            hhalf
      _ ≤ (1 / 2 : ℝ) *
              (Real.log (Real.log (N : ℝ)) + meissel_mertens + 1) + 1 / 2 := by
            gcongr
      _ = (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
            (meissel_mertens / 2 + 1) := by ring
  have hprod : S.prod (fun p => 1 + w p) ≤ Real.exp (S.sum w) :=
    finite_product_one_add_le_exp_sum S w hw
  have hexp : Real.exp (S.sum w) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1)) := Real.exp_le_exp.mpr hsum
  have hsqrt :
      Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ))) =
        Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlogpos]
    congr 1
    ring
  calc
    ((Finset.Icc 1 N).filter Nat.Prime).prod
        (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹)
        = S.prod (fun p => 1 + w p) := rfl
    _ ≤ Real.exp (S.sum w) := hprod
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1)) := hexp
    _ = mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
      rw [Real.exp_add, hsqrt]
      simp [mertensHalfEulerConstant, mul_comm]

theorem exists_prime_half_euler_product_threshold :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 N).filter Nat.Prime).prod
          (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) ≤
        mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
  exact eventually_atTop.1 eventually_prime_half_euler_product_le

end Erdos448

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos2.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 2.
https://www.erdosproblems.com/forum/thread/2

Informal authors:
- Paul Balister
- Béla Bollobás
- Robert Morris
- Julian Sahasrabudhe
- Marius Tiba

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos2.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 2

Erdős asked whether covering systems with distinct moduli can have arbitrarily
large least modulus.  Hough proved that they cannot.  Balister, Bollobás,
Morris, Sahasrabudhe and Tiba gave a distortion-sieve proof and the explicit
bound `616000`.

The mathematical reconstruction and the lemma-by-lemma formalization plan are
in `tex/2.tex`.
-/

open scoped BigOperators


namespace Erdos2

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact covering-system statement -/

/-- A covering system with one residue attached to each member of the finite
set `D` of moduli.  Since `D` is a `Finset`, the moduli are distinct by
construction.  The lower bound `2 ≤ d` excludes the trivial modulus `1`. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧ ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

/-- The positive answer to Erdős's original question.  The theorem below
proves the negation of this proposition. -/
def HasArbitrarilyLargeMinimum : Prop :=
  ∀ N : ℕ, ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
    IsDistinctCoveringSystem D a ∧ ∀ d ∈ D, N ≤ d

/-- The uniform-bound formulation of the negative answer. -/
def HasUniformMinimumBound : Prop :=
  ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
    IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M

lemma uniformBound_iff_not_arbitrarilyLarge :
    HasUniformMinimumBound ↔ ¬HasArbitrarilyLargeMinimum := by
  constructor
  · rintro ⟨M, hM⟩ hlarge
    obtain ⟨D, a, hcover, hmin⟩ := hlarge M
    obtain ⟨d, hdD, hdM⟩ := hM D a hcover
    exact (not_lt_of_ge (hmin d hdD)) hdM
  · intro hnot
    by_contra huniform
    apply hnot
    change ∀ N : ℕ, ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
      IsDistinctCoveringSystem D a ∧ ∀ d ∈ D, N ≤ d
    intro N
    by_contra hN
    push Not at hN
    apply huniform
    refine ⟨N, ?_⟩
    exact hN

/-! ## Finite probability distributions -/

/-- A probability distribution represented by its weights on a finite type. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  sum_weight : ∑ x, weight x = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The mass of a finite event. -/
def mass (P : FinProb Ω) (S : Finset Ω) : ℝ :=
  ∑ x ∈ S, P.weight x

@[simp]
lemma mass_empty (P : FinProb Ω) : P.mass ∅ = 0 := by
  simp [mass]

@[simp]
lemma mass_univ (P : FinProb Ω) : P.mass Finset.univ = 1 := by
  simpa [mass] using P.sum_weight

lemma mass_nonneg (P : FinProb Ω) (S : Finset Ω) : 0 ≤ P.mass S := by
  exact Finset.sum_nonneg fun x _ => P.weight_nonneg x

lemma mass_mono (P : FinProb Ω) {S T : Finset Ω} (hST : S ⊆ T) :
    P.mass S ≤ P.mass T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro x hxT hxS
  exact P.weight_nonneg x

lemma mass_union_le [DecidableEq Ω] (P : FinProb Ω) (S T : Finset Ω) :
    P.mass (S ∪ T) ≤ P.mass S + P.mass T := by
  rw [mass, mass, mass]
  calc
    ∑ x ∈ S ∪ T, P.weight x =
        (∑ x ∈ S, P.weight x) + ∑ x ∈ T \ S, P.weight x := by
          rw [show S ∪ T = S ∪ (T \ S) by ext x; simp]
          rw [Finset.sum_union]
          exact Finset.disjoint_sdiff
    _ ≤ (∑ x ∈ S, P.weight x) + ∑ x ∈ T, P.weight x := by
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset : T \ S ⊆ T)
          fun x hxT hxTS => P.weight_nonneg x) _

lemma mass_biUnion_le_sum [DecidableEq Ω] {ι : Type*} [DecidableEq ι]
    (P : FinProb Ω) (I : Finset ι) (E : ι → Finset Ω) :
    P.mass (I.biUnion E) ≤ ∑ i ∈ I, P.mass (E i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (P.mass_union_le (E i) (I.biUnion E)).trans
        (add_le_add_right ih _)

lemma exists_outside_of_sum_mass_lt_one [DecidableEq Ω]
    {ι : Type*} [DecidableEq ι] (P : FinProb Ω) (I : Finset ι)
    (E : ι → Finset Ω) (hsmall : (∑ i ∈ I, P.mass (E i)) < 1) :
    ∃ x : Ω, ∀ i ∈ I, x ∉ E i := by
  have hproper : I.biUnion E ≠ (Finset.univ : Finset Ω) := by
    intro hall
    have hunion : P.mass (I.biUnion E) = 1 := by rw [hall, P.mass_univ]
    have hle := P.mass_biUnion_le_sum I E
    linarith
  by_contra hnone
  push Not at hnone
  apply hproper
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact hnone x

lemma mass_le_of_pointwise [DecidableEq Ω] (P Q : FinProb Ω)
    (S : Finset Ω) {c : ℝ}
    (hpoint : ∀ x, P.weight x ≤ c * Q.weight x) :
    P.mass S ≤ c * Q.mass S := by
  rw [mass, mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => hpoint x

lemma mass_sdiff_ge [DecidableEq Ω] (P : FinProb Ω) (S T : Finset Ω) :
    P.mass S - P.mass T ≤ P.mass (S \ T) := by
  have hsub : S ⊆ (S \ T) ∪ T := by
    intro x hx
    by_cases hxt : x ∈ T
    · simp [hxt]
    · simp [hx, hxt]
  have hle := (P.mass_mono hsub).trans (P.mass_union_le (S \ T) T)
  linarith

end FinProb

/-! ## One distortion step on a finite fibre -/

namespace Distortion

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]

/-- The uniform proportion of the fibre `B x`. -/
def fibreDensity (B : X → Finset Y) (x : X) : ℝ :=
  ((B x).card : ℝ) / (Fintype.card Y : ℝ)

lemma card_pos_real : (0 : ℝ) < Fintype.card Y := by
  exact_mod_cast Fintype.card_pos

lemma fibreDensity_nonneg (B : X → Finset Y) (x : X) :
    0 ≤ fibreDensity B x := by
  exact div_nonneg (by positivity) (card_pos_real.le)

lemma fibreDensity_le_one (B : X → Finset Y) (x : X) :
    fibreDensity B x ≤ 1 := by
  rw [fibreDensity, div_le_one (card_pos_real)]
  exact_mod_cast Finset.card_le_univ (B x)

/-- BBMST's fibre multiplier.  The first branch deletes the bad part when
its fibre density is at most `δ`; the second branch removes exactly `δ` of
the original fibre mass. -/
def multiplier (B : X → Finset Y) (δ : ℝ) (x : X) (y : Y) : ℝ :=
  let α := fibreDensity B x
  if α ≤ δ then
    if y ∈ B x then 0 else (1 - α)⁻¹
  else if y ∈ B x then
    (α - δ) / (α * (1 - δ))
  else
    (1 - δ)⁻¹

/-- Extend `P` uniformly across `Y`, then apply the distortion multiplier. -/
def stepWeight (P : FinProb X) (B : X → Finset Y) (δ : ℝ) : X × Y → ℝ :=
  fun z => P.weight z.1 / (Fintype.card Y : ℝ) * multiplier B δ z.1 z.2

lemma sum_ite_mem (S : Finset Y) (a b : ℝ) :
    ∑ y : Y, (if y ∈ S then a else b) =
      (S.card : ℝ) * a + ((Fintype.card Y - S.card : ℕ) : ℝ) * b := by
  classical
  have hcard : ((Finset.univ.filter fun y : Y => y ∉ S).card) =
      Fintype.card Y - S.card := by
    rw [show (Finset.univ.filter fun y : Y => y ∉ S) = Finset.univ \ S by ext y; simp]
    rw [Finset.card_sdiff]
    simp
  rw [Finset.sum_ite]
  simp [hcard]

lemma one_sub_fibreDensity_pos_of_le
    (B : X → Finset Y) (x : X) {δ : ℝ} (hδ : δ < 1)
    (hα : fibreDensity B x ≤ δ) : 0 < 1 - fibreDensity B x := by
  linarith

lemma fibreDensity_pos_of_not_le
    (B : X → Finset Y) (x : X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hα : ¬fibreDensity B x ≤ δ) : 0 < fibreDensity B x := by
  exact lt_of_le_of_lt hδ (lt_of_not_ge hα)

lemma cast_card_sub (S : Finset Y) :
    ((Fintype.card Y - S.card : ℕ) : ℝ) =
      (Fintype.card Y : ℝ) - (S.card : ℝ) := by
  exact_mod_cast Nat.cast_sub (Finset.card_le_univ S)

/-- The multiplier has average one on every fibre. -/
lemma sum_multiplier (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) :
    ∑ y : Y, multiplier B δ x y = (Fintype.card Y : ℝ) := by
  classical
  let α := fibreDensity B x
  let N : ℝ := Fintype.card Y
  have hN : N ≠ 0 := ne_of_gt card_pos_real
  have hcard : ((B x).card : ℝ) = α * N := by
    dsimp only [α, N, fibreDensity]
    field_simp
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    rw [sum_ite_mem]
    change ((B x).card : ℝ) * 0 +
        ((Fintype.card Y - (B x).card : ℕ) : ℝ) * (1 - α)⁻¹ = N
    rw [mul_zero, zero_add, cast_card_sub]
    have hne : 1 - α ≠ 0 :=
      ne_of_gt (one_sub_fibreDensity_pos_of_le B x hδ1 hα)
    calc
      ((Fintype.card Y : ℝ) - (B x).card) * (1 - α)⁻¹ =
          (N * (1 - α)) * (1 - α)⁻¹ := by
            rw [hcard]
            change (N - α * N) * (1 - α)⁻¹ = (N * (1 - α)) * (1 - α)⁻¹
            ring
      _ = N := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hδne : 1 - δ ≠ 0 := by linarith
    simp only [multiplier, α, hα, if_false]
    rw [sum_ite_mem]
    change ((B x).card : ℝ) * ((α - δ) / (α * (1 - δ))) +
        ((Fintype.card Y - (B x).card : ℕ) : ℝ) * (1 - δ)⁻¹ = N
    rw [cast_card_sub, hcard]
    change α * N * ((α - δ) / (α * (1 - δ))) +
        (N - α * N) * (1 - δ)⁻¹ = N
    field_simp [hαne, hδne]
    ring

lemma multiplier_nonneg (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) (y : Y) :
    0 ≤ multiplier B δ x y := by
  let α := fibreDensity B x
  have hαnonneg : 0 ≤ α := fibreDensity_nonneg B x
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (by linarith [fibreDensity_le_one B x])
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hδpos : 0 < 1 - δ := by linarith
    simp only [multiplier, α, hα, if_false]
    split_ifs
    · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hα))
        (mul_nonneg hαpos.le hδpos.le)
    · exact inv_nonneg.mpr hδpos.le

lemma multiplier_le (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) (y : Y) :
    multiplier B δ x y ≤ (1 - δ)⁻¹ := by
  let α := fibreDensity B x
  have hδpos : 0 < 1 - δ := by linarith
  by_cases hα : α ≤ δ
  · simp only [multiplier, α, hα, if_pos]
    split_ifs
    · exact inv_nonneg.mpr hδpos.le
    · apply (inv_le_inv₀ (by linarith) hδpos).2
      linarith
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    simp only [multiplier, α, hα, if_false]
    split_ifs
    · rw [div_eq_mul_inv, mul_inv]
      calc
        (α - δ) * (α⁻¹ * (1 - δ)⁻¹) =
            ((α - δ) * α⁻¹) * (1 - δ)⁻¹ := by ring
        _ ≤ 1 * (1 - δ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hδpos.le)
          exact mul_inv_le_one_of_le₀ (by linarith) hαpos.le
        _ = (1 - δ)⁻¹ := one_mul _
    · exact le_rfl

/-- One normalized distortion step. -/
def step (P : FinProb X) (B : X → Finset Y) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : FinProb (X × Y) where
  weight := stepWeight P B δ
  weight_nonneg z := mul_nonneg
    (div_nonneg (P.weight_nonneg z.1) card_pos_real.le)
    (multiplier_nonneg B hδ0 hδ1 z.1 z.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : X, ∑ y : Y, stepWeight P B δ (x, y) = ∑ x : X, P.weight x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [stepWeight]
        rw [← Finset.mul_sum, sum_multiplier B hδ0 hδ1 x]
        field_simp [ne_of_gt (card_pos_real (Y := Y))]
      _ = 1 := P.sum_weight

/-- Expectation with respect to a finite probability distribution. -/
def expectation (P : FinProb X) (f : X → ℝ) : ℝ :=
  ∑ x : X, P.weight x * f x

lemma expectation_indicator (P : FinProb X) (A : Finset X) (c : ℝ) :
    expectation P (fun x => if x ∈ A then c else 0) = c * P.mass A := by
  rw [expectation, FinProb.mass]
  calc
    ∑ x : X, P.weight x * (if x ∈ A then c else 0) =
        ∑ x ∈ A, P.weight x * c := by
          simp_rw [mul_ite, mul_zero]
          rw [← Finset.sum_filter]
          simp
    _ = (∑ x ∈ A, P.weight x) * c := by rw [Finset.sum_mul]
    _ = c * (∑ x ∈ A, P.weight x) := by ring

lemma expectation_mul_indicators (P : FinProb X) (A B C : Finset X)
    (c d : ℝ) (hC : ∀ x, x ∈ C ↔ x ∈ A ∧ x ∈ B) :
    expectation P (fun x =>
      (if x ∈ A then c else 0) * (if x ∈ B then d else 0)) =
        (c * d) * P.mass C := by
  rw [show (fun x =>
      (if x ∈ A then c else 0) * (if x ∈ B then d else 0)) =
      (fun x => if x ∈ C then c * d else 0) by
    funext x
    by_cases hxC : x ∈ C
    · have hx := (hC x).mp hxC
      simp [hxC, hx.1, hx.2]
    · have hx := mt (hC x).mpr hxC
      simp only [not_and_or] at hx
      rcases hx with hxA | hxB
      · simp [hxC, hxA]
      · simp [hxC, hxB]]
  exact expectation_indicator P C (c * d)

/-- Fraction of the original fibre mass left on its bad part after
distortion. -/
def removedFraction (δ α : ℝ) : ℝ :=
  if α ≤ δ then 0 else (α - δ) / (1 - δ)

lemma cast_card_eq_density_mul (B : X → Finset Y) (x : X) :
    ((B x).card : ℝ) = fibreDensity B x * (Fintype.card Y : ℝ) := by
  rw [fibreDensity]
  field_simp [ne_of_gt (card_pos_real (Y := Y))]

lemma sum_stepWeight_bad (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (x : X) :
    ∑ y ∈ B x, stepWeight P B δ (x, y) =
      P.weight x * removedFraction δ (fibreDensity B x) := by
  classical
  let α := fibreDensity B x
  let N : ℝ := Fintype.card Y
  have hN : N ≠ 0 := ne_of_gt card_pos_real
  have hcard : ((B x).card : ℝ) = α * N := cast_card_eq_density_mul B x
  have hδne : 1 - δ ≠ 0 := by linarith
  by_cases hα : α ≤ δ
  · rw [removedFraction, if_pos hα, mul_zero]
    apply Finset.sum_eq_zero
    intro y hy
    simp [stepWeight, multiplier, α, hα, hy]
  · have hαpos : 0 < α := fibreDensity_pos_of_not_le B x hδ0 hα
    have hαne : α ≠ 0 := ne_of_gt hαpos
    simp only [stepWeight, multiplier, removedFraction, α, hα, if_false]
    apply Eq.trans (Finset.sum_congr rfl (fun y hy => by rw [if_pos hy]))
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    change α * N *
        (P.weight x / N * ((α - δ) / (α * (1 - δ)))) =
      P.weight x * ((α - δ) / (1 - δ))
    field_simp [hN, hαne, hδne]

/-- The bad subset of the extended space. -/
def badPairs (B : X → Finset Y) : Finset (X × Y) :=
  Finset.univ.filter fun z => z.2 ∈ B z.1

lemma step_mass_bad (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (step P B δ hδ0 hδ1).mass (badPairs B) =
      expectation P (fun x => removedFraction δ (fibreDensity B x)) := by
  classical
  rw [FinProb.mass]
  change ∑ z ∈ Finset.univ.filter (fun z : X × Y => z.2 ∈ B z.1),
      stepWeight P B δ z = _
  rw [Finset.sum_filter]
  change ∑ z : X × Y, (if z.2 ∈ B z.1 then stepWeight P B δ z else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter]
  change ∑ y ∈ (Finset.univ.filter fun y : Y => y ∈ B x),
      stepWeight P B δ (x, y) = _
  rw [show (Finset.univ.filter fun y : Y => y ∈ B x) = B x by ext y; simp]
  exact sum_stepWeight_bad P B hδ0 hδ1 x

lemma expectation_mono (P : FinProb X) {f g : X → ℝ}
    (hfg : ∀ x, f x ≤ g x) : expectation P f ≤ expectation P g := by
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hfg x) (P.weight_nonneg x)

/-- Linearity of finite expectation over a finite family. -/
lemma expectation_finset_sum {ι : Type*} (P : FinProb X) (I : Finset ι)
    (f : ι → X → ℝ) :
    expectation P (fun x => ∑ i ∈ I, f i x) =
      ∑ i ∈ I, expectation P (f i) := by
  classical
  rw [expectation]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The square of a finite sum expands into the double sum of the pairwise
expectations. -/
lemma expectation_sq_finset_sum {ι : Type*} (P : FinProb X) (I : Finset ι)
    (f : ι → X → ℝ) :
    expectation P (fun x => (∑ i ∈ I, f i x) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, expectation P (fun x => f i x * f j x) := by
  classical
  rw [expectation]
  calc
    (∑ x : X, P.weight x * (∑ i ∈ I, f i x) ^ 2) =
        ∑ x : X, ∑ i ∈ I, ∑ j ∈ I,
          P.weight x * (f i x * f j x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x : X,
          P.weight x * (f i x * f j x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I, expectation P (fun x => f i x * f j x) := by
      rfl

lemma removedFraction_nonneg {δ α : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) : 0 ≤ removedFraction δ α := by
  rw [removedFraction]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (by linarith)

lemma removedFraction_le_first {δ α : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    removedFraction δ α ≤ α := by
  rw [removedFraction]
  split_ifs with h
  · exact hα0
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hα1)]

lemma sub_le_sq_div_four {δ α : ℝ} (hδ : 0 < δ) :
    α - δ ≤ α ^ 2 / (4 * δ) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (α - 2 * δ)]

lemma removedFraction_le_second {δ α : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) :
    removedFraction δ α ≤ α ^ 2 / (4 * δ * (1 - δ)) := by
  rw [removedFraction]
  split_ifs with h
  · exact div_nonneg (sq_nonneg α) (mul_nonneg (by positivity) (by linarith))
  · rw [div_le_iff₀ (by linarith)]
    calc
      α - δ ≤ α ^ 2 / (4 * δ) := sub_le_sq_div_four hδ0
      _ = α ^ 2 / (4 * δ * (1 - δ)) * (1 - δ) := by
        field_simp [ne_of_gt hδ0, ne_of_gt (show 0 < 1 - δ by linarith)]

/-- First moment of the removed fibre proportions. -/
def firstMoment (P : FinProb X) (B : X → Finset Y) : ℝ :=
  expectation P (fibreDensity B)

/-- Second moment of the removed fibre proportions. -/
def secondMoment (P : FinProb X) (B : X → Finset Y) : ℝ :=
  expectation P (fun x => (fibreDensity B x) ^ 2)

lemma step_mass_bad_le_first (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (step P B δ hδ0 hδ1).mass (badPairs B) ≤ firstMoment P B := by
  rw [step_mass_bad P B hδ0 hδ1]
  exact expectation_mono P fun x =>
    removedFraction_le_first hδ0 hδ1 (fibreDensity_nonneg B x) (fibreDensity_le_one B x)

lemma step_mass_bad_le_second (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (step P B δ hδ0.le hδ1).mass (badPairs B) ≤
      secondMoment P B / (4 * δ * (1 - δ)) := by
  rw [step_mass_bad P B hδ0.le hδ1, secondMoment, expectation]
  calc
    expectation P (fun x => removedFraction δ (fibreDensity B x)) ≤
        expectation P (fun x => (fibreDensity B x) ^ 2 / (4 * δ * (1 - δ))) :=
      expectation_mono P fun x => removedFraction_le_second hδ0 hδ1
        (fibreDensity_nonneg B x)
    _ = (∑ x : X, P.weight x * (fibreDensity B x) ^ 2) /
        (4 * δ * (1 - δ)) := by
      rw [expectation]
      simp_rw [div_eq_mul_inv, mul_assoc]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Uniform extension of a distribution to one new coordinate. -/
def uniformExtension (P : FinProb X) : FinProb (X × Y) :=
  step P (fun _ => ∅) 0 le_rfl zero_lt_one

@[simp]
lemma uniformExtension_weight (P : FinProb X) (z : X × Y) :
    (uniformExtension P : FinProb (X × Y)).weight z =
      P.weight z.1 / (Fintype.card Y : ℝ) := by
  simp [uniformExtension, step, stepWeight, multiplier, fibreDensity]

lemma step_weight_le_uniform (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (z : X × Y) :
    (step P B δ hδ0 hδ1).weight z ≤
      (1 - δ)⁻¹ * (uniformExtension P).weight z := by
  rw [uniformExtension_weight]
  change P.weight z.1 / (Fintype.card Y : ℝ) * multiplier B δ z.1 z.2 ≤
    (1 - δ)⁻¹ * (P.weight z.1 / (Fintype.card Y : ℝ))
  rw [mul_comm (1 - δ)⁻¹]
  exact mul_le_mul_of_nonneg_left (multiplier_le B hδ0 hδ1 z.1 z.2)
    (div_nonneg (P.weight_nonneg z.1) card_pos_real.le)

lemma step_mass_le_uniform (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S : Finset (X × Y)) :
    (step P B δ hδ0 hδ1).mass S ≤
      (1 - δ)⁻¹ * (uniformExtension P).mass S := by
  exact FinProb.mass_le_of_pointwise _ _ S (step_weight_le_uniform P B hδ0 hδ1)

/-- Pull an event on the old coordinates back to the extended product. -/
def oldPairs (S : Finset X) : Finset (X × Y) :=
  S.product Finset.univ

lemma step_mass_oldPairs (P : FinProb X) (B : X → Finset Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S : Finset X) :
    (step P B δ hδ0 hδ1).mass (oldPairs S) = P.mass S := by
  classical
  rw [FinProb.mass, FinProb.mass]
  change ∑ z ∈ S.product (Finset.univ : Finset Y), stepWeight P B δ z =
    ∑ x ∈ S, P.weight x
  calc
    ∑ z ∈ S.product (Finset.univ : Finset Y), stepWeight P B δ z =
        ∑ x ∈ S, ∑ y ∈ (Finset.univ : Finset Y), stepWeight P B δ (x, y) := by
      exact Finset.sum_product S Finset.univ (stepWeight P B δ)
    _ = ∑ x ∈ S, P.weight x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [stepWeight]
      rw [← Finset.mul_sum, sum_multiplier B hδ0 hδ1 x]
      field_simp [ne_of_gt (card_pos_real (Y := Y))]

/-! ## Iterating the distortion -/

/-- A positive coordinate size. -/
abbrev PosNat := {n : ℕ // 0 < n}

/-- A finite coordinate of the specified positive size. -/
abbrev Coordinate (q : PosNat) := Fin (q : ℕ)

instance coordinateNonempty (q : PosNat) : Nonempty (Coordinate q) :=
  ⟨⟨0, q.property⟩⟩

/-- The first `n` coordinates, associated to the left.  This orientation
makes adjoining coordinate `n` definitionally a product. -/
@[reducible] def Prefix (q : ℕ → PosNat) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Prefix q n × Coordinate (q n)

instance prefixFintype (q : ℕ → PosNat) : (n : ℕ) → Fintype (Prefix q n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (Prefix q n) (Coordinate (q n))
      (prefixFintype q n) inferInstance

/-- The data needed at each stage of a finite distortion sieve. -/
structure Schedule (q : ℕ → PosNat) where
  bad : (n : ℕ) → Prefix q n → Finset (Coordinate (q n))
  delta : ℕ → ℝ
  delta_nonneg : ∀ n, 0 ≤ delta n
  delta_lt_one : ∀ n, delta n < 1

/-- Unit mass on the empty prefix. -/
def unitProb : FinProb PUnit where
  weight _ := 1
  weight_nonneg _ := zero_le_one
  sum_weight := by simp

/-- The probability distribution after `n` distortion steps. -/
def prefixProb {q : ℕ → PosNat} (S : Schedule q) :
    (n : ℕ) → FinProb (Prefix q n)
  | 0 => unitProb
  | n + 1 => step (prefixProb S n) (S.bad n) (S.delta n)
      (S.delta_nonneg n) (S.delta_lt_one n)

/-- Residues not removed in the first `n` stages. -/
def residual {q : ℕ → PosNat} (S : Schedule q) :
    (n : ℕ) → Finset (Prefix q n)
  | 0 => Finset.univ
  | n + 1 => oldPairs (residual S n) \ badPairs (S.bad n)

/-- Actual distorted mass of the bad set at stage `n`. -/
def stageCost {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) : ℝ :=
  (prefixProb S (n + 1)).mass (badPairs (S.bad n))

@[simp]
lemma prefixProb_succ {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) :
    prefixProb S (n + 1) = step (prefixProb S n) (S.bad n) (S.delta n)
      (S.delta_nonneg n) (S.delta_lt_one n) := rfl

@[simp]
lemma residual_zero {q : ℕ → PosNat} (S : Schedule q) :
    residual S 0 = Finset.univ := rfl

lemma residual_mass_lower {q : ℕ → PosNat} (S : Schedule q) (n : ℕ) :
    1 - ∑ i ∈ Finset.range n, stageCost S i ≤
      (prefixProb S n).mass (residual S n) := by
  induction n with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, residual_zero]
        using (prefixProb S 0).mass_univ.ge
  | succ n ih =>
      rw [Finset.sum_range_succ]
      let R : Finset (Prefix q (n + 1)) :=
        oldPairs (residual S n) \ badPairs (S.bad n)
      have hres : residual S (n + 1) = R := by
        rw [residual]
      rw [hres, prefixProb_succ]
      have hdiff := (prefixProb S (n + 1)).mass_sdiff_ge
        (oldPairs (residual S n)) (badPairs (S.bad n))
      have hold : (prefixProb S (n + 1)).mass (oldPairs (residual S n)) =
          (prefixProb S n).mass (residual S n) :=
        step_mass_oldPairs (prefixProb S n) (S.bad n)
          (S.delta_nonneg n) (S.delta_lt_one n) (residual S n)
      rw [hold] at hdiff
      rw [sub_add_eq_sub_sub]
      calc
        1 - ∑ i ∈ Finset.range n, stageCost S i - stageCost S n ≤
            (prefixProb S n).mass (residual S n) - stageCost S n :=
          sub_le_sub_right ih _
        _ ≤ (prefixProb S (n + 1)).mass R := by
          simpa only [stageCost, R] using hdiff

lemma residual_nonempty_of_sum_cost_lt_one {q : ℕ → PosNat}
    (S : Schedule q) (n : ℕ)
    (hsmall : (∑ i ∈ Finset.range n, stageCost S i) < 1) :
    (residual S n).Nonempty := by
  have hpos : 0 < (prefixProb S n).mass (residual S n) :=
    lt_of_lt_of_le (sub_pos.mpr hsmall) (residual_mass_lower S n)
  by_contra hempty
  have hz : residual S n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hz, FinProb.mass_empty] at hpos
  exact lt_irrefl 0 hpos

lemma residual_nonempty_of_stage_bounds {q : ℕ → PosNat}
    (S : Schedule q) (n : ℕ) (c : ℕ → ℝ)
    (hcost : ∀ i < n, stageCost S i ≤ c i)
    (hsmall : (∑ i ∈ Finset.range n, c i) < 1) :
    (residual S n).Nonempty := by
  apply residual_nonempty_of_sum_cost_lt_one S n
  exact (Finset.sum_le_sum fun i hi => hcost i (Finset.mem_range.mp hi)).trans_lt hsmall

/-! ## Product boxes under the iterated distortion -/

/-- A coordinatewise box in a finite prefix. -/
def box {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) :
    (n : ℕ) → Finset (Prefix q n)
  | 0 => Finset.univ
  | n + 1 => (box A n).product (A n)

@[simp]
lemma box_zero {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) :
    box A 0 = Finset.univ := rfl

@[simp]
lemma box_succ {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i))) (n : ℕ) :
    box A (n + 1) = (box A n).product (A n) := rfl

lemma mem_box_pair {q : ℕ → PosNat}
    (A B : (i : ℕ) → Finset (Coordinate (q i))) :
    ∀ (n : ℕ) (x : Prefix q n),
      x ∈ box (fun i => A i ∩ B i) n ↔ x ∈ box A n ∧ x ∈ box B n := by
  intro n
  induction n with
  | zero => intro x; simp [box]
  | succ n ih =>
      intro z
      rcases z with ⟨x, y⟩
      constructor
      · intro h
        have hp := Finset.mem_product.mp h
        have hx := (ih x).mp hp.1
        have hy := Finset.mem_inter.mp hp.2
        exact ⟨Finset.mem_product.mpr ⟨hx.1, hy.1⟩,
          Finset.mem_product.mpr ⟨hx.2, hy.2⟩⟩
      · rintro ⟨hA, hB⟩
        have hpA := Finset.mem_product.mp hA
        have hpB := Finset.mem_product.mp hB
        exact Finset.mem_product.mpr ⟨(ih x).mpr ⟨hpA.1, hpB.1⟩,
          Finset.mem_inter.mpr ⟨hpA.2, hpB.2⟩⟩

lemma uniformExtension_mass_product
    (P : FinProb X) (S : Finset X) (T : Finset Y) :
    (uniformExtension P : FinProb (X × Y)).mass (S.product T) =
      P.mass S * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
  classical
  rw [FinProb.mass, FinProb.mass]
  calc
    ∑ z ∈ S.product T, (uniformExtension P).weight z =
        ∑ x ∈ S, ∑ y ∈ T, (uniformExtension P).weight (x, y) := by
      exact Finset.sum_product S T (uniformExtension P).weight
    _ = ∑ x ∈ S, P.weight x * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [uniformExtension_weight]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (∑ x ∈ S, P.weight x) * ((T.card : ℝ) / (Fintype.card Y : ℝ)) := by
      rw [Finset.sum_mul]

/-- The factor paid by a box at one declared active coordinate.  Inactive
coordinates are required to be unrestricted and cost exactly one. -/
def boxFactor {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active] (i : ℕ) : ℝ :=
  if active i then
    (1 - S.delta i)⁻¹ *
      (((A i).card : ℝ) / (Fintype.card (Coordinate (q i)) : ℝ))
  else 1

lemma boxFactor_nonneg {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active] (i : ℕ) :
    0 ≤ boxFactor S A active i := by
  rw [boxFactor]
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one i]))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact zero_le_one

/-- A coordinate box has the uniform box mass, multiplied only by the
distortion factors at coordinates on which it is nontrivial. -/
lemma prefixProb_mass_box_le {q : ℕ → PosNat} (S : Schedule q)
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (active : ℕ → Prop) [DecidablePred active]
    (hinactive : ∀ i, ¬active i → A i = Finset.univ) (n : ℕ) :
    (prefixProb S n).mass (box A n) ≤
      ∏ i ∈ Finset.range n, boxFactor S A active i := by
  induction n with
  | zero =>
      rw [box_zero, FinProb.mass_univ]
      simp
  | succ n ih =>
      rw [Finset.prod_range_succ, box_succ]
      by_cases hactive : active n
      · have hstep :
            (prefixProb S (n + 1)).mass ((box A n).product (A n)) ≤
              (1 - S.delta n)⁻¹ *
                (uniformExtension (prefixProb S n)).mass
                  ((box A n).product (A n)) :=
          step_mass_le_uniform (prefixProb S n) (S.bad n)
            (S.delta_nonneg n) (S.delta_lt_one n) ((box A n).product (A n))
        rw [uniformExtension_mass_product] at hstep
        rw [boxFactor, if_pos hactive]
        calc
          (prefixProb S (n + 1)).mass ((box A n).product (A n)) ≤
              (1 - S.delta n)⁻¹ *
                ((prefixProb S n).mass (box A n) *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := hstep
          _ = (prefixProb S n).mass (box A n) *
                ((1 - S.delta n)⁻¹ *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := by ring
          _ ≤ (∏ i ∈ Finset.range n, boxFactor S A active i) *
                ((1 - S.delta n)⁻¹ *
                  (((A n).card : ℝ) /
                    (Fintype.card (Coordinate (q n)) : ℝ))) := by
              exact mul_le_mul_of_nonneg_right ih
                (mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one n]))
                  (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · have hfull := hinactive n hactive
        have hold :
            (prefixProb S (n + 1)).mass (oldPairs (box A n)) =
              (prefixProb S n).mass (box A n) :=
          step_mass_oldPairs (prefixProb S n) (S.bad n)
            (S.delta_nonneg n) (S.delta_lt_one n) (box A n)
        rw [hfull, show (box A n).product Finset.univ = oldPairs (box A n) from rfl,
          hold, boxFactor, if_neg hactive, mul_one]
        exact ih

/-- The recursively associated prefix is canonically the dependent product
of its coordinates. -/
def prefixEquivPi (q : ℕ → PosNat) :
    (n : ℕ) → Prefix q n ≃ ((i : Fin n) → Coordinate (q i))
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by intro x; cases x; rfl
        right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n + 1 =>
      ((prefixEquivPi q n).prodCongr (Equiv.refl (Coordinate (q n)))).trans
      ((Equiv.prodComm _ _).trans
          (Fin.snocEquiv (fun i : Fin (n + 1) => Coordinate (q i))))

/-- Membership in a recursively associated product box is equivalent to
coordinatewise membership after applying the canonical prefix equivalence. -/
lemma mem_box_iff_mem_coordinate {q : ℕ → PosNat}
    (A : (i : ℕ) → Finset (Coordinate (q i)))
    (n : ℕ) (x : Prefix q n) :
    x ∈ box A n ↔ ∀ i : Fin n, (prefixEquivPi q n x) i ∈ A i.1 := by
  induction n with
  | zero =>
      simp only [box_zero, Finset.mem_univ, true_iff]
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      rcases x with ⟨x, y⟩
      rw [box_succ]
      refine Finset.mem_product.trans ?_
      rw [ih]
      constructor
      · rintro ⟨hx, hy⟩ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [prefixEquivPi] using hy
        · simpa [prefixEquivPi] using hx j
      · intro h
        constructor
        · intro j
          simpa [prefixEquivPi] using h j.castSucc
        · simpa [prefixEquivPi] using h (Fin.last n)

@[simp]
lemma mem_badPairs_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (B : X → Finset Y) (x : X) (y : Y) :
    (x, y) ∈ badPairs B ↔ y ∈ B x := by
  simp [badPairs]

end Distortion

/-! ## Finite congruence fibres -/

namespace Arithmetic

/-- The fibre of reduction from `ZMod n` to `ZMod m`. -/
def zmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) : Finset (ZMod n) :=
  Finset.univ.filter fun x => ZMod.castHom h (ZMod m) x = a

@[simp]
lemma mem_zmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) (x : ZMod n) :
    x ∈ zmodFiber h a ↔ ZMod.castHom h (ZMod m) x = a := by
  simp only [zmodFiber, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every fibre of a surjective reduction map between finite residue rings
has the expected normalized cardinality. -/
lemma zmodFiber_card_div_card {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) :
    (((zmodFiber h a).card : ℝ) / (Fintype.card (ZMod n) : ℝ)) =
      1 / (m : ℝ) := by
  classical
  let f : ZMod n →+ ZMod m := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective f := ZMod.castHom_surjective h
  have hfiber (b : ZMod m) :
      ((Finset.univ.filter fun x : ZMod n => f x = b).card) =
        (zmodFiber h a).card := by
    rw [zmodFiber]
    change ((Finset.univ.filter fun x : ZMod n => f x = b).card) =
      (Finset.univ.filter fun x : ZMod n => f x = a).card
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj b) (hsurj a)
  have hmaps :
      ((Finset.univ : Finset (ZMod n)) : Set (ZMod n)).MapsTo f
        ((Finset.univ : Finset (ZMod m)) : Set (ZMod m)) := by
    intro x hx
    exact Finset.mem_univ _
  have hcount :
      Fintype.card (ZMod n) =
        ∑ b : ZMod m, (Finset.univ.filter fun x : ZMod n => f x = b).card := by
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise hmaps]
  rw [show (∑ b : ZMod m,
      (Finset.univ.filter fun x : ZMod n => f x = b).card) =
        Fintype.card (ZMod m) * (zmodFiber h a).card by
      simp_rw [hfiber]
      simp] at hcount
  simp only [ZMod.card] at hcount ⊢
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hcountR : (n : ℝ) = (m : ℝ) * ((zmodFiber h a).card : ℝ) := by
    exact_mod_cast hcount
  field_simp [hm, hn]
  nlinarith [hcountR]

/-- The same reduction fibre, transported to the canonical `Fin n`
coordinate used by the distortion recursion. -/
def finZmodFiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (a : ZMod m) : Finset (Fin n) :=
  (zmodFiber h a).map (ZMod.finEquiv n).symm.toEmbedding

lemma finZmodFiber_card_div_card {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) :
    (((finZmodFiber h a).card : ℝ) / (Fintype.card (Fin n) : ℝ)) =
      1 / (m : ℝ) := by
  rw [finZmodFiber, Finset.card_map, Fintype.card_fin]
  simpa only [ZMod.card] using zmodFiber_card_div_card h a

@[simp]
lemma mem_finZmodFiber {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod m) (x : Fin n) :
    x ∈ finZmodFiber h a ↔
      ZMod.castHom h (ZMod m) (ZMod.finEquiv n x) = a := by
  simp [finZmodFiber, mem_zmodFiber]

/-! ### Enumerating the prime-power coordinates of a period -/

abbrev PrimeIndex (Q : ℕ) := {p : ℕ // p ∈ Q.primeFactors}

def primeCount (Q : ℕ) : ℕ := Q.primeFactors.card

/-- The increasing enumeration of the distinct prime divisors of `Q`. -/
def primeEnum (Q : ℕ) : Fin (primeCount Q) ≃o PrimeIndex Q :=
  monoEquivOfFin (PrimeIndex Q) (by simp [primeCount])

def primeAt (Q : ℕ) (i : Fin (primeCount Q)) : ℕ :=
  primeEnum Q i

lemma primeAt_mem (Q : ℕ) (i : Fin (primeCount Q)) :
    primeAt Q i ∈ Q.primeFactors :=
  (primeEnum Q i).property

lemma primeAt_prime (Q : ℕ) (i : Fin (primeCount Q)) :
    (primeAt Q i).Prime :=
  Nat.prime_of_mem_primeFactors (primeAt_mem Q i)

lemma primeAt_strictMono (Q : ℕ) : StrictMono (primeAt Q) := by
  intro i j hij
  exact_mod_cast (primeEnum Q).lt_iff_lt.mpr hij

/-- Coordinate `i` is the full prime power of the `i`th prime in `Q`.
Outside the finite range it is the harmless one-point coordinate. -/
def primePowerSize (Q i : ℕ) : Distortion.PosNat :=
  if h : i < primeCount Q then
    let p := primeAt Q ⟨i, h⟩
    ⟨p ^ Q.factorization p, pow_pos (primeAt_prime Q ⟨i, h⟩).pos _⟩
  else
    ⟨1, zero_lt_one⟩

@[simp]
lemma primePowerSize_of_lt (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    ((primePowerSize Q i : Distortion.PosNat) : ℕ) =
      (primeAt Q ⟨i, hi⟩) ^ Q.factorization (primeAt Q ⟨i, hi⟩) := by
  simp [primePowerSize, hi]

/-- Product of the first `n` enumerated prime-power coordinates. -/
def partialModulus (Q n : ℕ) : ℕ :=
  ∏ i : Fin n, ((primePowerSize Q i : Distortion.PosNat) : ℕ)

lemma partialModulus_full {Q : ℕ} (hQ : Q ≠ 0) :
    partialModulus Q (primeCount Q) = Q := by
  rw [partialModulus]
  calc
    ∏ i : Fin (primeCount Q),
        ((primePowerSize Q i : Distortion.PosNat) : ℕ) =
      ∏ p : PrimeIndex Q, p.1 ^ Q.factorization p.1 := by
        apply Fintype.prod_equiv (primeEnum Q).toEquiv
        intro i
        simp [primePowerSize, primeAt]
    _ = Q := (Nat.prod_primeFactors_coe_pow_factorization hQ).symm

/-- One enumerated `Fin` coordinate, identified with its residue ring. -/
def finPrimePowerEquiv (Q : ℕ) (i : Fin (primeCount Q)) :
    Distortion.Coordinate (primePowerSize Q i) ≃
      ZMod ((primeAt Q i) ^ Q.factorization (primeAt Q i)) :=
  letI : NeZero ((primeAt Q i) ^ Q.factorization (primeAt Q i)) :=
    ⟨pow_ne_zero _ (primeAt_prime Q i).ne_zero⟩
  (Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt))).trans
    (ZMod.finEquiv ((primeAt Q i) ^ Q.factorization (primeAt Q i))).toEquiv

/-- The full recursively associated product is the usual CRT residue ring. -/
def prefixCRTEq (Q : ℕ) (hQ : Q ≠ 0) :
    Distortion.Prefix (primePowerSize Q) (primeCount Q) ≃ ZMod Q :=
  (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q)).trans <|
    (Equiv.piCongrRight fun i : Fin (primeCount Q) => finPrimePowerEquiv Q i).trans <|
      (Equiv.piCongrLeft
        (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
        (primeEnum Q).toEquiv).trans
          (ZMod.equivPi (n := Q) hQ).symm.toEquiv

/-! ### One-coordinate congruence restrictions -/

/-- In a `p^γ` coordinate, impose one residue modulo `p^e`; exponent zero
is represented by the full coordinate. -/
def primeRestriction (p γ e : ℕ) (hp : p.Prime) (he : e ≤ γ)
    (b : ℤ) : Finset (Fin (p ^ γ)) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ γ) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact if hzero : e = 0 then Finset.univ else
    finZmodFiber (pow_dvd_pow p he) (b : ZMod (p ^ e))

lemma primeRestriction_zero (p γ : ℕ) (hp : p.Prime) (b : ℤ) :
    primeRestriction p γ 0 hp (Nat.zero_le γ) b = Finset.univ := by
  simp [primeRestriction]

lemma primeRestriction_card_div (p γ e : ℕ) (hp : p.Prime) (he : e ≤ γ)
    (b : ℤ) :
    (((primeRestriction p γ e hp he b).card : ℝ) /
        (Fintype.card (Fin (p ^ γ)) : ℝ)) =
      1 / ((p ^ e : ℕ) : ℝ) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ γ) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hzero : e = 0
  · subst e
    rw [primeRestriction_zero]
    simp only [Finset.card_univ, Fintype.card_fin, pow_zero, Nat.cast_one, div_one]
    exact div_self (by exact_mod_cast pow_ne_zero γ hp.ne_zero)
  · simp only [primeRestriction, hzero, ↓reduceDIte]
    exact finZmodFiber_card_div_card (pow_dvd_pow p he) (b : ZMod (p ^ e))

/-- Coordinate restrictions for the congruence `z ≡ b (mod d)`, expressed
inside the prime-power coordinates of a multiple `Q` of `d`. -/
def classCoordinates (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (i : ℕ) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) := by
  by_cases hi : i < primeCount Q
  · let j : Fin (primeCount Q) := ⟨i, hi⟩
    let p := primeAt Q j
    let γ := Q.factorization p
    let e := d.factorization p
    have hp : p.Prime := primeAt_prime Q j
    have he : e ≤ γ := (Nat.factorization_le_iff_dvd hd hQ).mpr hdQ p
    let R : Finset (Fin (p ^ γ)) := primeRestriction p γ e hp he b
    let castE : Fin (p ^ γ) ≃ Distortion.Coordinate (primePowerSize Q i) :=
      Equiv.cast (congrArg Fin (primePowerSize_of_lt Q hi).symm)
    exact R.map castE.toEmbedding
  · exact Finset.univ

/-- A coordinate is active precisely when `d` contains its prime. -/
def classActive (Q d i : ℕ) : Prop :=
  if hi : i < primeCount Q then
    d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0
  else False

lemma classCoordinates_of_not_active (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) (b : ℤ) (i : ℕ) (hi : ¬classActive Q d i) :
    classCoordinates Q d hQ hd hdQ b i = Finset.univ := by
  rw [classActive] at hi
  by_cases hir : i < primeCount Q
  · simp only [hir, ↓reduceDIte, not_not] at hi
    rw [classCoordinates]
    simp only [hir, ↓reduceDIte]
    simp only [primeRestriction, hi, ↓reduceDIte]
    exact Finset.map_univ_equiv _
  · simp [classCoordinates, hir]

lemma classCoordinates_card_div (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) (b : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((classCoordinates Q d hQ hd hdQ b i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) =
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  rw [classCoordinates]
  simp only [hi, ↓reduceDIte]
  rw [Finset.card_map, Fintype.card_fin, primePowerSize_of_lt Q hi]
  simpa only [Fintype.card_fin] using
    (primeRestriction_card_div
      (primeAt Q ⟨i, hi⟩)
      (Q.factorization (primeAt Q ⟨i, hi⟩))
      (d.factorization (primeAt Q ⟨i, hi⟩))
      (primeAt_prime Q ⟨i, hi⟩)
      ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ _)
      b)

/-- The prefix event determined by one congruence class. -/
def classBox (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (n : ℕ) : Finset (Distortion.Prefix (primePowerSize Q) n) :=
  Distortion.box (classCoordinates Q d hQ hd hdQ b) n

/-- A congruence class is a coordinate box, so its distorted mass is bounded
by the product of its active coordinate factors. -/
lemma prefixProb_mass_classBox_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass (classBox Q d hQ hd hdQ b n) ≤
      ∏ i ∈ Finset.range n,
        Distortion.boxFactor S (classCoordinates Q d hQ hd hdQ b)
          (classActive Q d) i := by
  exact Distortion.prefixProb_mass_box_le S
    (classCoordinates Q d hQ hd hdQ b) (classActive Q d)
    (classCoordinates_of_not_active Q d hQ hd hdQ b) n

/-- The explicit factor contributed by a congruence class at one coordinate. -/
def classFactor (S : Distortion.Schedule (primePowerSize Q))
    (d i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    if d.factorization (primeAt Q ⟨i, hi⟩) = 0 then 1 else
      (1 - S.delta i)⁻¹ /
        (((primeAt Q ⟨i, hi⟩) ^
          d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
  else 1

lemma boxFactor_classCoordinates
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (i : ℕ) :
    Distortion.boxFactor S (classCoordinates Q d hQ hd hdQ b)
        (classActive Q d) i = classFactor S d i := by
  rw [Distortion.boxFactor, classActive, classFactor]
  by_cases hi : i < primeCount Q
  · simp only [hi, ↓reduceDIte]
    by_cases he : d.factorization (primeAt Q ⟨i, hi⟩) = 0
    · simp [he]
    · simp only [he, if_false]
      rw [classCoordinates_card_div Q d hQ hd hdQ b hi]
      split
      · ring
      · rename_i hzero
        have hz : d.factorization (primeAt Q ⟨i, hi⟩) = 0 := by
          simpa only using not_ne_iff.mp hzero
        exact (he hz).elim
  · simp [hi]

lemma prefixProb_mass_classBox_le_explicit
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) (b : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass (classBox Q d hQ hd hdQ b n) ≤
      ∏ i ∈ Finset.range n, classFactor S d i := by
  simpa only [boxFactor_classCoordinates S hQ hd hdQ b] using
    prefixProb_mass_classBox_le S hQ hd hdQ b n

/-! ### Intersections of two congruence-class boxes -/

def pairCoordinates (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (i : ℕ) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
    classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i

def pairActive (Q d₁ d₂ i : ℕ) : Prop :=
  classActive Q d₁ i ∨ classActive Q d₂ i

lemma pairCoordinates_of_not_active (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (i : ℕ) (hi : ¬pairActive Q d₁ d₂ i) :
    pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i =
      Finset.univ := by
  rw [pairActive, not_or] at hi
  rw [pairCoordinates,
    classCoordinates_of_not_active Q d₁ hQ hd₁ hd₁Q b₁ i hi.1,
    classCoordinates_of_not_active Q d₂ hQ hd₂ hd₂Q b₂ i hi.2]
  exact Finset.inter_self _

lemma pairCoordinates_card_div_le_left (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d₁.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  calc
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      (((classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left :
            classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
                classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i ⊆
              classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i)
    _ = _ := classCoordinates_card_div Q d₁ hQ hd₁ hd₁Q b₁ hi

lemma pairCoordinates_card_div_le_right (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d₂.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  calc
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      (((classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
            classCoordinates Q d₁ hQ hd₁ hd₁Q b₁ i ∩
                classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i ⊆
              classCoordinates Q d₂ hQ hd₂ hd₂Q b₂ i)
    _ = _ := classCoordinates_card_div Q d₂ hQ hd₂ hd₂Q b₂ hi

lemma pairCoordinates_card_div_le_max (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) {i : ℕ} (hi : i < primeCount Q) :
    (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
      1 / (((primeAt Q ⟨i, hi⟩) ^
        max (d₁.factorization (primeAt Q ⟨i, hi⟩))
          (d₂.factorization (primeAt Q ⟨i, hi⟩)) : ℕ) : ℝ) := by
  by_cases he : d₁.factorization (primeAt Q ⟨i, hi⟩) ≤
      d₂.factorization (primeAt Q ⟨i, hi⟩)
  · rw [max_eq_right he]
    exact pairCoordinates_card_div_le_right Q d₁ d₂ hQ hd₁ hd₂
      hd₁Q hd₂Q b₁ b₂ hi
  · rw [max_eq_left (le_of_not_ge he)]
    exact pairCoordinates_card_div_le_left Q d₁ d₂ hQ hd₁ hd₂
      hd₁Q hd₂Q b₁ b₂ hi

/-- Membership in both congruence-class boxes is coordinatewise membership in
their intersection box. -/
lemma mem_pairBox_iff (Q d₁ d₂ : ℕ) (hQ : Q ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    (b₁ b₂ : ℤ) (n : ℕ) (x : Distortion.Prefix (primePowerSize Q) n) :
    x ∈ Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n ↔
      x ∈ classBox Q d₁ hQ hd₁ hd₁Q b₁ n ∧
        x ∈ classBox Q d₂ hQ hd₂ hd₂Q b₂ n := by
  exact Distortion.mem_box_pair
    (classCoordinates Q d₁ hQ hd₁ hd₁Q b₁)
    (classCoordinates Q d₂ hQ hd₂ hd₂Q b₂) n x

/-- The explicit coordinate factor for an intersection of two congruence
classes; the larger of the two prime exponents controls its density. -/
def pairFactor (S : Distortion.Schedule (primePowerSize Q))
    (d₁ d₂ i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    let e := max (d₁.factorization (primeAt Q ⟨i, hi⟩))
      (d₂.factorization (primeAt Q ⟨i, hi⟩))
    if e = 0 then 1 else
      (1 - S.delta i)⁻¹ * (1 /
        (((primeAt Q ⟨i, hi⟩) ^ e : ℕ) : ℝ)
      )
  else 1

lemma boxFactor_pairCoordinates_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q) (b₁ b₂ : ℤ) (i : ℕ) :
    Distortion.boxFactor S
        (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂)
        (pairActive Q d₁ d₂) i ≤ pairFactor S d₁ d₂ i := by
  rw [Distortion.boxFactor, pairFactor]
  by_cases hi : i < primeCount Q
  · simp only [hi, ↓reduceDIte]
    let e₁ := d₁.factorization (primeAt Q ⟨i, hi⟩)
    let e₂ := d₂.factorization (primeAt Q ⟨i, hi⟩)
    change
      (if pairActive Q d₁ d₂ i then
          (1 - S.delta i)⁻¹ *
            (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
              (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ))
        else 1) ≤
        if max e₁ e₂ = 0 then 1 else
          (1 - S.delta i)⁻¹ *
            (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ))
    by_cases he : max e₁ e₂ = 0
    · have hz₁ : e₁ = 0 := by omega
      have hz₂ : e₂ = 0 := by omega
      have hnot : ¬pairActive Q d₁ d₂ i := by
        rw [pairActive, classActive, classActive]
        simp only [hi, ↓reduceDIte, not_or, not_not]
        exact ⟨by simpa only [e₁] using hz₁, by simpa only [e₂] using hz₂⟩
      rw [if_neg hnot, if_pos he]
    · have hactive : pairActive Q d₁ d₂ i := by
        rw [pairActive, classActive, classActive]
        simp only [hi, ↓reduceDIte]
        by_contra hz
        rw [not_or] at hz
        apply he
        have hz₁ : e₁ = 0 := by
          simpa only [e₁] using not_ne_iff.mp hz.1
        have hz₂ : e₂ = 0 := by
          simpa only [e₂] using not_ne_iff.mp hz.2
        simp [hz₁, hz₂]
      rw [if_pos hactive, if_neg he]
      have hinv : 0 ≤ (1 - S.delta i)⁻¹ :=
        inv_nonneg.mpr (by linarith [S.delta_lt_one i])
      calc
        (1 - S.delta i)⁻¹ *
              (((pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i).card : ℝ) /
                (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) ≤
            (1 - S.delta i)⁻¹ *
              (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (pairCoordinates_card_div_le_max Q d₁ d₂ hQ hd₁ hd₂
              hd₁Q hd₂Q b₁ b₂ hi) hinv
        _ = (1 - S.delta i)⁻¹ *
              (1 / (((primeAt Q ⟨i, hi⟩) ^ max e₁ e₂ : ℕ) : ℝ)) := rfl
  · have hnot : ¬pairActive Q d₁ d₂ i := by
      simp [pairActive, classActive, hi]
    simp [hi, hnot]

lemma prefixProb_mass_pairBox_le
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q) (b₁ b₂ : ℤ) (n : ℕ) :
    (Distortion.prefixProb S n).mass
        (Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n) ≤
      ∏ i ∈ Finset.range n, pairFactor S d₁ d₂ i := by
  calc
    (Distortion.prefixProb S n).mass
        (Distortion.box
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂) n) ≤
      ∏ i ∈ Finset.range n,
        Distortion.boxFactor S
          (pairCoordinates Q d₁ d₂ hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂)
          (pairActive Q d₁ d₂) i :=
        Distortion.prefixProb_mass_box_le S _ _
          (pairCoordinates_of_not_active Q d₁ d₂ hQ hd₁ hd₂
            hd₁Q hd₂Q b₁ b₂) n
    _ ≤ ∏ i ∈ Finset.range n, pairFactor S d₁ d₂ i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Distortion.boxFactor_nonneg S _ _ i
      · intro i hi
        exact boxFactor_pairCoordinates_le S hQ hd₁ hd₂ hd₁Q hd₂Q b₁ b₂ i

/-! ### The arithmetic distortion schedule -/

/-- The modulus `d` is assigned to coordinate `i` when `i` is the largest
prime-power coordinate occurring in `d`. -/
def assignedAt (Q d i : ℕ) : Prop :=
  if hi : i < primeCount Q then
    d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
    ∀ j, i < j → (hj : j < primeCount Q) →
      d.factorization (primeAt Q ⟨j, hj⟩) = 0
  else False

abbrev ModulusIndex (D : Finset ℕ) := {d : ℕ // d ∈ D}

def stageIndices (Q : ℕ) (D : Finset ℕ) (i : ℕ) :
    Finset (ModulusIndex D) :=
  Finset.univ.filter fun d => assignedAt Q d i

/-- The section of one congruence class in the new coordinate over an old
prefix. -/
def classSection (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (i : ℕ) (x : Distortion.Prefix (primePowerSize Q) i)
    (d : ModulusIndex D) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
    classCoordinates Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i
  else ∅

/-- At a prime-power stage, remove the union of the sections of precisely the
classes assigned to that stage. -/
def stageBad (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (i : ℕ) (x : Distortion.Prefix (primePowerSize Q) i) :
    Finset (Distortion.Coordinate (primePowerSize Q i)) :=
  (stageIndices Q D i).biUnion (classSection Q D a hQ hd hdQ i x)

def arithmeticSchedule (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) :
    Distortion.Schedule (primePowerSize Q) where
  bad := stageBad Q D a hQ hd hdQ
  delta := delta
  delta_nonneg := hdelta0
  delta_lt_one := hdelta1

lemma classSection_card_div (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) (d : ModulusIndex D) :
    (((classSection Q D a hQ hd hdQ i x d).card : ℝ) /
        (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) =
      if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
        1 / (((primeAt Q ⟨i, hi⟩) ^
          d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
      else 0 := by
  rw [classSection]
  split
  · rename_i hx
    rw [classCoordinates_card_div Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) hi]
  · rename_i hx
    simp

lemma fibreDensity_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) :
    Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ≤
      ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          1 / (((primeAt Q ⟨i, hi⟩) ^
            d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
        else 0 := by
  rw [Distortion.fibreDensity, stageBad]
  have hcard : ((stageIndices Q D i).biUnion
      (classSection Q D a hQ hd hdQ i x)).card ≤
      ∑ d ∈ stageIndices Q D i, (classSection Q D a hQ hd hdQ i x d).card :=
    Finset.card_biUnion_le
  calc
    (((stageIndices Q D i).biUnion
        (classSection Q D a hQ hd hdQ i x)).card : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ) ≤
      ((↑(∑ d ∈ stageIndices Q D i,
          (classSection Q D a hQ hd hdQ i x d).card) : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hcard
    _ = ∑ d ∈ stageIndices Q D i,
        (((classSection Q D a hQ hd hdQ i x d).card : ℝ) /
          (Fintype.card (Distortion.Coordinate (primePowerSize Q i)) : ℝ)) := by
        push_cast
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
    _ = ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          1 / (((primeAt Q ⟨i, hi⟩) ^
            d.1.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hdstage
          exact classSection_card_div Q D a hQ hd hdQ hi x d

/-- The proportion of the `i`-th prime-power coordinate fixed by modulus
`d`.  Outside the actual coordinate range it is set to zero. -/
def stageCoefficient (Q d i : ℕ) : ℝ :=
  if hi : i < primeCount Q then
    1 / (((primeAt Q ⟨i, hi⟩) ^
      d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ)
  else 0

lemma stageCoefficient_of_lt (Q d : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    stageCoefficient Q d i =
      1 / (((primeAt Q ⟨i, hi⟩) ^
        d.factorization (primeAt Q ⟨i, hi⟩) : ℕ) : ℝ) := by
  simp [stageCoefficient, hi]

lemma stageCoefficient_nonneg (Q d i : ℕ) : 0 ≤ stageCoefficient Q d i := by
  rw [stageCoefficient]
  split
  · positivity
  · exact le_rfl

lemma fibreDensity_stageBad_le' (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (x : Distortion.Prefix (primePowerSize Q) i) :
    Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ≤
      ∑ d ∈ stageIndices Q D i,
        if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
          stageCoefficient Q d.1 i
        else 0 := by
  simpa only [stageCoefficient_of_lt Q _ hi] using
    fibreDensity_stageBad_le Q D a hQ hd hdQ hi x

lemma firstMoment_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          (Distortion.prefixProb S i).mass
            (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  let P := Distortion.prefixProb S i
  let I := stageIndices Q D i
  let f := fun d : ModulusIndex D => fun x : Distortion.Prefix (primePowerSize Q) i =>
    if x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i then
      stageCoefficient Q d.1 i
    else 0
  change Distortion.firstMoment P (stageBad Q D a hQ hd hdQ i) ≤
    ∑ d ∈ I, stageCoefficient Q d.1 i *
      P.mass (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i)
  rw [Distortion.firstMoment]
  calc
    Distortion.expectation P
        (Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i)) ≤
      Distortion.expectation P (fun x => ∑ d ∈ I, f d x) :=
        Distortion.expectation_mono P fun x =>
          fibreDensity_stageBad_le' Q D a hQ hd hdQ hi x
    _ = ∑ d ∈ I, Distortion.expectation P (f d) :=
      Distortion.expectation_finset_sum P I f
    _ = ∑ d ∈ I, stageCoefficient Q d.1 i *
        P.mass (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) := by
      apply Finset.sum_congr rfl
      intro d hdI
      exact Distortion.expectation_indicator P
        (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i)
        (stageCoefficient Q d.1 i)

lemma secondMoment_stageBad_le (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          (Distortion.prefixProb S i).mass
            (Distortion.box
              (pairCoordinates Q d₁.1 d₂.1 hQ
                (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
                (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
                (a d₁.1) (a d₂.1)) i) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  let P := Distortion.prefixProb S i
  let I := stageIndices Q D i
  let A := fun d : ModulusIndex D =>
    classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i
  let f := fun d : ModulusIndex D => fun x : Distortion.Prefix (primePowerSize Q) i =>
    if x ∈ A d then stageCoefficient Q d.1 i else 0
  change Distortion.secondMoment P (stageBad Q D a hQ hd hdQ i) ≤
    ∑ d₁ ∈ I, ∑ d₂ ∈ I,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        P.mass (Distortion.box
          (pairCoordinates Q d₁.1 d₂.1 hQ
            (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
            (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
            (a d₁.1) (a d₂.1)) i)
  rw [Distortion.secondMoment]
  calc
    Distortion.expectation P
        (fun x => Distortion.fibreDensity (stageBad Q D a hQ hd hdQ i) x ^ 2) ≤
      Distortion.expectation P (fun x => (∑ d ∈ I, f d x) ^ 2) := by
        apply Distortion.expectation_mono P
        intro x
        have hle := fibreDensity_stageBad_le' Q D a hQ hd hdQ hi x
        have hleft := Distortion.fibreDensity_nonneg
          (stageBad Q D a hQ hd hdQ i) x
        have hright : 0 ≤ ∑ d ∈ I, f d x := by
          apply Finset.sum_nonneg
          intro d hdI
          dsimp only [f]
          split
          · exact stageCoefficient_nonneg Q d.1 i
          · exact le_rfl
        nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hright hleft)]
    _ = ∑ d₁ ∈ I, ∑ d₂ ∈ I,
        Distortion.expectation P (fun x => f d₁ x * f d₂ x) :=
      Distortion.expectation_sq_finset_sum P I f
    _ = ∑ d₁ ∈ I, ∑ d₂ ∈ I,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          P.mass (Distortion.box
            (pairCoordinates Q d₁.1 d₂.1 hQ
              (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
              (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
              (a d₁.1) (a d₂.1)) i) := by
      apply Finset.sum_congr rfl
      intro d₁ hd₁I
      apply Finset.sum_congr rfl
      intro d₂ hd₂I
      exact Distortion.expectation_mul_indicators P (A d₁) (A d₂)
        (Distortion.box
          (pairCoordinates Q d₁.1 d₂.1 hQ
            (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
            (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
            (a d₁.1) (a d₂.1)) i)
        (stageCoefficient Q d₁.1 i) (stageCoefficient Q d₂.1 i)
        (mem_pairBox_iff Q d₁.1 d₂.1 hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
          (a d₁.1) (a d₂.1) i)

lemma firstMoment_stageBad_le_products (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, classFactor S d.1 j := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          (Distortion.prefixProb S i).mass
            (classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) i) :=
        firstMoment_stageBad_le Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
    _ ≤ ∑ d ∈ stageIndices Q D i,
        stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, classFactor S d.1 j := by
      apply Finset.sum_le_sum
      intro d hdI
      exact mul_le_mul_of_nonneg_left
        (prefixProb_mass_classBox_le_explicit S hQ (hd d.1 d.2)
          (hdQ d.1 d.2) (a d.1) i)
        (stageCoefficient_nonneg Q d.1 i)

lemma secondMoment_stageBad_le_products (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          (Distortion.prefixProb S i).mass
            (Distortion.box
              (pairCoordinates Q d₁.1 d₂.1 hQ
                (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
                (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
                (a d₁.1) (a d₂.1)) i) :=
        secondMoment_stageBad_le Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
    _ ≤ ∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
        (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
          ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j := by
      apply Finset.sum_le_sum
      intro d₁ hd₁I
      apply Finset.sum_le_sum
      intro d₂ hd₂I
      apply mul_le_mul_of_nonneg_left
      · exact prefixProb_mass_pairBox_le S hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2)
          (a d₁.1) (a d₂.1) i
      · exact mul_nonneg (stageCoefficient_nonneg Q d₁.1 i)
          (stageCoefficient_nonneg Q d₂.1 i)

/-! ### Encoding stage moduli by their exponent vectors -/

def stageCoordinate (Q : ℕ) {i : ℕ} (hi : i < primeCount Q)
    (j : Fin (i + 1)) : Fin (primeCount Q) :=
  ⟨j.1, j.2.trans_le (Nat.succ_le_of_lt hi)⟩

abbrev StageExponentVector (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :=
  (j : Fin (i + 1)) →
    Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)

def stageExponentVector (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hdQ : d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    StageExponentVector Q hi :=
  fun j =>
    ⟨d.factorization (primeAt Q (stageCoordinate Q hi j)),
      Nat.lt_succ_of_le ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ _)⟩

lemma primeAt_primeEnum_symm (Q : ℕ) (p : PrimeIndex Q) :
    primeAt Q ((primeEnum Q).symm p) = p.1 := by
  exact congrArg Subtype.val ((primeEnum Q).apply_symm_apply p)

lemma stageExponentVector_injective (Q : ℕ) (D : Finset ℕ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) :
    Set.InjOn
      (fun d : ModulusIndex D =>
        stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi)
      (stageIndices Q D i) := by
  intro d₁ hd₁I d₂ hd₂I hvec
  apply Subtype.ext
  apply Nat.eq_of_factorization_eq (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
  intro p
  by_cases hpQ : p ∈ Q.primeFactors
  · let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
    have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
    by_cases hki : k.1 ≤ i
    · let j : Fin (i + 1) := ⟨k.1, Nat.lt_succ_iff.mpr hki⟩
      have hjk : stageCoordinate Q hi j = k := by
        apply Fin.ext
        rfl
      have hv := congrArg Fin.val (congrFun hvec j)
      change d₁.1.factorization (primeAt Q (stageCoordinate Q hi j)) =
        d₂.1.factorization (primeAt Q (stageCoordinate Q hi j)) at hv
      simpa only [hjk, hpk] using hv
    · have hik : i < k.1 := lt_of_not_ge hki
      have ha₁ : assignedAt Q d₁.1 i := (Finset.mem_filter.mp hd₁I).2
      have ha₂ : assignedAt Q d₂.1 i := (Finset.mem_filter.mp hd₂I).2
      have ha₁' : d₁.1.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
          ∀ j, i < j → (hj : j < primeCount Q) →
            d₁.1.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
        simpa only [assignedAt, hi, ↓reduceDIte] using ha₁
      have ha₂' : d₂.1.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
          ∀ j, i < j → (hj : j < primeCount Q) →
            d₂.1.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
        simpa only [assignedAt, hi, ↓reduceDIte] using ha₂
      have hz₁ := ha₁'.2 k.1 hik k.2
      have hz₂ := ha₂'.2 k.1 hik k.2
      simpa only [hpk] using hz₁.trans hz₂.symm
  · by_cases hp : p.Prime
    · have hpndQ : ¬p ∣ Q := by
        intro hpQdvd
        exact hpQ ((Nat.mem_primeFactors).mpr ⟨hp, hpQdvd, hQ⟩)
      have hpnd₁ : ¬p ∣ d₁.1 := fun hpd => hpndQ (hpd.trans (hdQ d₁.1 d₁.2))
      have hpnd₂ : ¬p ∣ d₂.1 := fun hpd => hpndQ (hpd.trans (hdQ d₂.1 d₂.2))
      rw [Nat.factorization_eq_zero_of_not_dvd hpnd₁,
        Nat.factorization_eq_zero_of_not_dvd hpnd₂]
    · rw [Nat.factorization_eq_zero_of_not_prime d₁.1 hp,
        Nat.factorization_eq_zero_of_not_prime d₂.1 hp]

lemma assignedAt_iff_of_lt (Q d : ℕ) {i : ℕ} (hi : i < primeCount Q) :
    assignedAt Q d i ↔
      d.factorization (primeAt Q ⟨i, hi⟩) ≠ 0 ∧
        ∀ j, i < j → (hj : j < primeCount Q) →
          d.factorization (primeAt Q ⟨j, hj⟩) = 0 := by
  simp [assignedAt, hi]

/-- Local first-moment weight of one exponent.  At the last coordinate zero
is excluded; at earlier coordinates exponent zero contributes one. -/
def firstLocalFactor (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1))
    (e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) : ℝ :=
  let p := primeAt Q (stageCoordinate Q hi j)
  if j.1 = i then
    if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))
  else if e.1 = 0 then 1 else
    (1 - S.delta j.1)⁻¹ / (((p ^ e.1 : ℕ) : ℝ))

/-- Local second-moment weight of a pair of exponents. -/
def secondLocalFactor (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1))
    (e₁ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) : ℝ :=
  let p := primeAt Q (stageCoordinate Q hi j)
  if j.1 = i then
    if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
      1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))
  else
    let e := max e₁.1 e₂.1
    if e = 0 then 1 else
      (1 - S.delta j.1)⁻¹ / (((p ^ e : ℕ) : ℝ))

lemma firstLocalFactor_nonneg
    (S : Distortion.Schedule (primePowerSize Q)) {i : ℕ}
    (hi : i < primeCount Q) (j : Fin (i + 1))
    (e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) :
    0 ≤ firstLocalFactor S hi j e := by
  rw [firstLocalFactor]
  split <;> split
  · exact le_rfl
  · positivity
  · exact zero_le_one
  · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])) (by positivity)

lemma secondLocalFactor_nonneg
    (S : Distortion.Schedule (primePowerSize Q)) {i : ℕ}
    (hi : i < primeCount Q) (j : Fin (i + 1))
    (e₁ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) :
    0 ≤ secondLocalFactor S hi j e₁ e₂ := by
  rw [secondLocalFactor]
  split
  · split
    · exact le_rfl
    · positivity
  · dsimp only
    split
    · exact zero_le_one
    · exact mul_nonneg (inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])) (by positivity)

lemma prod_firstLocal_stageExponent
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i) :
    (∏ j : Fin (i + 1),
      firstLocalFactor S hi j (stageExponentVector Q d hQ hd hdQ hi j)) =
      stageCoefficient Q d i *
        ∏ j ∈ Finset.range i, classFactor S d j := by
  rw [Fin.prod_univ_castSucc, Finset.prod_range]
  have hlast : (Fin.last i : Fin (i + 1)).1 = i := rfl
  have hapos := (assignedAt_iff_of_lt Q d hi).mp ha
  have hcurrent :
      (stageExponentVector Q d hQ hd hdQ hi (Fin.last i)).1 =
        d.factorization (primeAt Q ⟨i, hi⟩) := by
    rfl
  have hlastFactor :
      firstLocalFactor S hi (Fin.last i)
          (stageExponentVector Q d hQ hd hdQ hi (Fin.last i)) =
        stageCoefficient Q d i := by
    rw [firstLocalFactor, stageCoefficient_of_lt Q d hi]
    simp only [hlast, if_true, hcurrent, if_neg hapos.1]
    rfl
  rw [hlastFactor, mul_comm]
  congr 1
  apply Fintype.prod_congr
  intro j
  have hj : j.1 < primeCount Q := j.2.trans hi
  have hjne : (j.castSucc : Fin (i + 1)).1 ≠ i := Nat.ne_of_lt j.2
  rw [firstLocalFactor, classFactor]
  simp only [hj, ↓reduceDIte, hjne, if_false, stageExponentVector,
    stageCoordinate]
  by_cases he : d.factorization (primeAt Q ⟨j.1, hj⟩) = 0
  · simp [he]
  · simp [he]

lemma prod_secondLocal_stageExponent
    (S : Distortion.Schedule (primePowerSize Q))
    (hQ : Q ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hd₁Q : d₁ ∣ Q) (hd₂Q : d₂ ∣ Q)
    {i : ℕ} (hi : i < primeCount Q)
    (ha₁ : assignedAt Q d₁ i) (ha₂ : assignedAt Q d₂ i) :
    (∏ j : Fin (i + 1),
      secondLocalFactor S hi j
        (stageExponentVector Q d₁ hQ hd₁ hd₁Q hi j)
        (stageExponentVector Q d₂ hQ hd₂ hd₂Q hi j)) =
      (stageCoefficient Q d₁ i * stageCoefficient Q d₂ i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁ d₂ j := by
  rw [Fin.prod_univ_castSucc, Finset.prod_range]
  have hapos₁ := (assignedAt_iff_of_lt Q d₁ hi).mp ha₁
  have hapos₂ := (assignedAt_iff_of_lt Q d₂ hi).mp ha₂
  have hlastFactor :
      secondLocalFactor S hi (Fin.last i)
          (stageExponentVector Q d₁ hQ hd₁ hd₁Q hi (Fin.last i))
          (stageExponentVector Q d₂ hQ hd₂ hd₂Q hi (Fin.last i)) =
        stageCoefficient Q d₁ i * stageCoefficient Q d₂ i := by
    rw [secondLocalFactor, stageCoefficient_of_lt Q d₁ hi,
      stageCoefficient_of_lt Q d₂ hi]
    simp only [Fin.val_last, if_true, stageExponentVector, stageCoordinate,
      hapos₁.1, hapos₂.1, or_false, false_or, if_false]
    have hp : primeAt Q ⟨i, hi⟩ ≠ 0 := (primeAt_prime Q ⟨i, hi⟩).ne_zero
    push_cast
    rw [pow_add]
    field_simp
  rw [hlastFactor, mul_comm]
  congr 1
  apply Fintype.prod_congr
  intro j
  have hj : j.1 < primeCount Q := j.2.trans hi
  have hjne : (j.castSucc : Fin (i + 1)).1 ≠ i := Nat.ne_of_lt j.2
  rw [secondLocalFactor, pairFactor]
  simp only [hj, ↓reduceDIte, hjne, if_false, stageExponentVector,
    stageCoordinate]
  let e₁ := d₁.factorization (primeAt Q ⟨j.1, hj⟩)
  let e₂ := d₂.factorization (primeAt Q ⟨j.1, hj⟩)
  by_cases he : max e₁ e₂ = 0
  · simp [e₁, e₂, he]
  · simp [e₁, e₂, he, div_eq_mul_inv]

def firstVectorWeight (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (v : StageExponentVector Q hi) : ℝ :=
  ∏ j : Fin (i + 1), firstLocalFactor S hi j (v j)

lemma firstVectorWeight_nonneg (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (v : StageExponentVector Q hi) :
    0 ≤ firstVectorWeight S hi v := by
  exact Finset.prod_nonneg fun j hj => firstLocalFactor_nonneg S hi j (v j)

lemma sum_stage_first_products_le_euler
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e := by
  let I := stageIndices Q D i
  let g := fun d : ModulusIndex D =>
    stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
  let w := firstVectorWeight S hi
  have hinj : Set.InjOn g I := stageExponentVector_injective Q D hQ hd hdQ hi
  calc
    (∑ d ∈ I, stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) =
      ∑ d ∈ I, w (g d) := by
        apply Finset.sum_congr rfl
        intro d hdI
        dsimp only [w, g, firstVectorWeight]
        rw [prod_firstLocal_stageExponent S hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
          ((Finset.mem_filter.mp hdI).2)]
    _ = ∑ v ∈ I.image g, w v := by
      rw [Finset.sum_image]
      intro d₁ hd₁I d₂ hd₂I heq
      exact hinj hd₁I hd₂I heq
    _ ≤ ∑ v : StageExponentVector Q hi, w v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvuniv hvimage
      exact firstVectorWeight_nonneg S hi v
    _ = ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e := by
      dsimp only [w, firstVectorWeight]
      exact (Fintype.prod_sum (fun j e => firstLocalFactor S hi j e)).symm

def piPairEquiv {I : Type*} (E : I → Type*) :
    ((∀ i, E i) × (∀ i, E i)) ≃ (∀ i, E i × E i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv z := rfl
  right_inv z := rfl

lemma sum_pair_pi_prod {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, Fintype (E i)]
    (f : ∀ i, E i → E i → ℝ) :
    (∑ x : ∀ i, E i, ∑ y : ∀ i, E i, ∏ i, f i (x i) (y i)) =
      ∏ i, ∑ a : E i, ∑ b : E i, f i a b := by
  calc
    (∑ x : ∀ i, E i, ∑ y : ∀ i, E i, ∏ i, f i (x i) (y i)) =
        ∑ z : (∀ i, E i) × (∀ i, E i), ∏ i, f i (z.1 i) (z.2 i) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ z : ∀ i, E i × E i, ∏ i, f i (z i).1 (z i).2 := by
      exact Fintype.sum_equiv (piPairEquiv E)
        (fun z => ∏ i, f i (z.1 i) (z.2 i))
        (fun z => ∏ i, f i (z i).1 (z i).2) (fun z => rfl)
    _ = ∏ i, ∑ z : E i × E i, f i z.1 z.2 := by
      exact (Fintype.prod_sum (fun (i : I) (z : E i × E i) => f i z.1 z.2)).symm
    _ = ∏ i, ∑ a : E i, ∑ b : E i, f i a b := by
      apply Fintype.prod_congr
      intro i
      rw [Fintype.sum_prod_type]

abbrev StageExponentPair (Q : ℕ) {i : ℕ} (hi : i < primeCount Q) :=
  (j : Fin (i + 1)) →
    (Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1) ×
      Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1))

lemma sum_stage_second_products_le_euler
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ := by
  let I := stageIndices Q D i
  let g := fun d : ModulusIndex D =>
    stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi
  let gp : ModulusIndex D × ModulusIndex D → StageExponentPair Q hi :=
    fun z j => (g z.1 j, g z.2 j)
  let w : StageExponentPair Q hi → ℝ := fun v =>
    ∏ j : Fin (i + 1), secondLocalFactor S hi j (v j).1 (v j).2
  have hinj : Set.InjOn g I := stageExponentVector_injective Q D hQ hd hdQ hi
  have hinjp : Set.InjOn gp (I.product I) := by
    intro z₁ hz₁ z₂ hz₂ hgp
    have hz₁' := Finset.mem_product.mp hz₁
    have hz₂' := Finset.mem_product.mp hz₂
    apply Prod.ext
    · apply hinj hz₁'.1 hz₂'.1
      funext j
      exact congrArg Prod.fst (congrFun hgp j)
    · apply hinj hz₁'.2 hz₂'.2
      funext j
      exact congrArg Prod.snd (congrFun hgp j)
  have hw (v : StageExponentPair Q hi) : 0 ≤ w v := by
    exact Finset.prod_nonneg fun j hj =>
      secondLocalFactor_nonneg S hi j (v j).1 (v j).2
  calc
    (∑ d₁ ∈ I, ∑ d₂ ∈ I,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) =
      ∑ d₁ ∈ I, ∑ d₂ ∈ I, w (gp (d₁, d₂)) := by
        apply Finset.sum_congr rfl
        intro d₁ hd₁I
        apply Finset.sum_congr rfl
        intro d₂ hd₂I
        dsimp only [w, gp, g]
        exact (prod_secondLocal_stageExponent S hQ
          (hd d₁.1 d₁.2) (hd d₂.1 d₂.2)
          (hdQ d₁.1 d₁.2) (hdQ d₂.1 d₂.2) hi
          ((Finset.mem_filter.mp hd₁I).2)
          ((Finset.mem_filter.mp hd₂I).2)).symm
    _ = ∑ z ∈ I.product I, w (gp z) := by
      exact (Finset.sum_product I I (fun z => w (gp z))).symm
    _ = ∑ v ∈ (I.product I).image gp, w v := by
      rw [Finset.sum_image]
      intro z₁ hz₁ z₂ hz₂ heq
      exact hinjp hz₁ hz₂ heq
    _ ≤ ∑ v : StageExponentPair Q hi, w v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvuniv hvimage
      exact hw v
    _ = ∏ j : Fin (i + 1),
        ∑ e : (Fin (Q.factorization
            (primeAt Q (stageCoordinate Q hi j)) + 1) ×
          Fin (Q.factorization
            (primeAt Q (stageCoordinate Q hi j)) + 1)),
          secondLocalFactor S hi j e.1 e.2 := by
      dsimp only [w]
      exact (Fintype.prod_sum (fun j (e :
          Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1) ×
            Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1)) =>
        secondLocalFactor S hi j e.1 e.2)).symm
    _ = ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ := by
      apply Fintype.prod_congr
      intro j
      rw [Fintype.sum_prod_type]

/-! ### Elementary finite geometric estimates -/

lemma fin_inv_pow_sum_eq (p γ : ℕ) (hp : p ≠ 0) (hp1 : p ≠ 1) :
    (∑ e : Fin (γ + 1),
      if e.1 = 0 then (0 : ℝ) else 1 / (((p ^ e.1 : ℕ) : ℝ))) =
      (1 - ((p : ℝ)⁻¹) ^ γ) / ((p : ℝ) - 1) := by
  induction γ with
  | zero => simp
  | succ γ ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, ih, Fin.val_last, Nat.add_eq_zero, Nat.succ_ne_zero,
        and_false, if_false]
      push_cast
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      have hp1R : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp1)
      have hcancel : (p : ℝ) ^ γ * (1 / (p : ℝ)) ^ γ = 1 := by
        rw [← mul_pow]
        field_simp
        simp
      have hbase : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
        field_simp
      have hboth : ((p : ℝ) ^ γ * (1 / (p : ℝ)) ^ γ) *
          ((p : ℝ) * (1 / (p : ℝ))) = 1 := by
        rw [hcancel, hbase, one_mul]
      field_simp [hpR, hp1R]
      rw [pow_succ, pow_succ]
      nlinarith [hcancel, hboth]

lemma fin_inv_pow_sum_le (p γ : ℕ) (hp2 : 2 ≤ p) :
    (∑ e : Fin (γ + 1),
      if e.1 = 0 then (0 : ℝ) else 1 / (((p ^ e.1 : ℕ) : ℝ))) ≤
      1 / ((p : ℝ) - 1) := by
  rw [fin_inv_pow_sum_eq p γ (by omega) (by omega)]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hden : 0 < (p : ℝ) - 1 := by linarith
  rw [div_le_div_iff_of_pos_right hden]
  have hpow : 0 ≤ ((p : ℝ)⁻¹) ^ γ := by positivity
  linarith

/-- Group a finite double geometric sum according to the maximum exponent.
There are exactly `2 * t + 1` ordered pairs with maximum `t`. -/
lemma fin_double_max_sum_eq_shell (r : ℝ) (γ : ℕ) :
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else r ^ max e₁.1 e₂.1) =
      ∑ e : Fin (γ + 1),
        if e.1 = 0 then 0 else ((2 * e.1 + 1 : ℕ) : ℝ) * r ^ e.1 := by
  let splitTerm : Fin (γ + 1) → Fin (γ + 1) → ℝ := fun e₁ e₂ =>
    (if e₁.1 ≠ 0 ∧ e₂ ≤ e₁ then r ^ e₁.1 else 0) +
      (if e₁ < e₂ then r ^ e₂.1 else 0)
  calc
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else r ^ max e₁.1 e₂.1) =
        ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), splitTerm e₁ e₂ := by
      apply Finset.sum_congr rfl
      intro e₁ he₁
      apply Finset.sum_congr rfl
      intro e₂ he₂
      dsimp only [splitTerm]
      by_cases hle : e₂ ≤ e₁
      · rw [max_eq_left (by exact_mod_cast hle)]
        by_cases hz : e₁.1 = 0
        · have hz₂ : e₂.1 = 0 := by omega
          have heq : e₂ = e₁ := Fin.ext (hz₂.trans hz.symm)
          subst e₂
          simp [hz]
        · simp [hz, hle, not_lt_of_ge hle]
      · have hlt : e₁ < e₂ := lt_of_not_ge hle
        rw [max_eq_right (by exact_mod_cast hlt.le)]
        have hz : e₂.1 ≠ 0 := by omega
        simp [hz, hle, hlt]
    _ = (∑ e₁ : Fin (γ + 1),
          if e₁.1 = 0 then 0 else ((e₁.1 + 1 : ℕ) : ℝ) * r ^ e₁.1) +
        ∑ e₂ : Fin (γ + 1),
          if e₂.1 = 0 then 0 else (e₂.1 : ℝ) * r ^ e₂.1 := by
      simp_rw [splitTerm]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro e₁ he₁
        by_cases hz : e₁.1 = 0
        · simp [hz]
        · rw [if_neg hz]
          rw [← Finset.sum_filter]
          rw [show (Finset.univ.filter fun e₂ : Fin (γ + 1) =>
              e₁.1 ≠ 0 ∧ e₂ ≤ e₁) = Finset.Iic e₁ by
            ext e₂
            simp [hz]]
          simp [Fin.card_Iic]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e₂ he₂
        by_cases hz : e₂.1 = 0
        · have hleast : ∀ x : Fin (γ + 1), e₂ ≤ x := by
            intro x
            exact_mod_cast (show e₂.1 ≤ x.1 by omega)
          simp [hz, hleast]
        · rw [if_neg hz, ← Finset.sum_filter]
          rw [show (Finset.univ.filter fun e₁ : Fin (γ + 1) => e₁ < e₂) =
              Finset.Iio e₂ by ext e₁; simp]
          simp [Fin.card_Iio]
    _ = ∑ e : Fin (γ + 1),
        if e.1 = 0 then 0 else ((2 * e.1 + 1 : ℕ) : ℝ) * r ^ e.1 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hz : e.1 = 0
      · simp [hz]
      · simp only [hz, if_false]
        push_cast
        ring

/-- The finite double maximum sum is bounded by its infinite geometric
value.  This is the local `(3p-1)/(p-1)^2` term in BBMST. -/
lemma fin_double_max_sum_le (p γ : ℕ) (hp2 : 2 ≤ p) :
    (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
      if max e₁.1 e₂.1 = 0 then 0 else
        1 / ((((p ^ max e₁.1 e₂.1 : ℕ) : ℝ)))) ≤
      (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by positivity
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp2
  have hr0 : 0 ≤ r := inv_nonneg.mpr hpR.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hp1R
  have hrewrite (n : ℕ) : 1 / ((((p ^ n : ℕ) : ℝ))) = r ^ n := by
    simp only [r, one_div, Nat.cast_pow, inv_pow]
  simp_rw [hrewrite]
  rw [fin_double_max_sum_eq_shell]
  rw [Fin.sum_univ_eq_sum_range (fun e : ℕ =>
    if e = 0 then 0 else ((2 * e + 1 : ℕ) : ℝ) * r ^ e)]
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hw := hasSum_coe_mul_geometric_of_norm_lt_one (r := r) hrnorm
  have hweighted :
      (∑ e ∈ Finset.range (γ + 1), (e : ℝ) * r ^ e) ≤ r / (1 - r) ^ 2 := by
    simpa only [hw.tsum_eq] using
      (hw.summable.sum_le_tsum (Finset.range (γ + 1))
        (fun e he => mul_nonneg (by positivity) (pow_nonneg hr0 e)))
  have htail :
      (∑ e ∈ Finset.range (γ + 1), if e = 0 then 0 else r ^ e) ≤ r / (1 - r) := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hgeom := fin_inv_pow_sum_le p γ hp2
    have hleft :
        (∑ e : Fin (γ + 1), if e.1 = 0 then 0 else r ^ e.1) =
          ∑ e : Fin (γ + 1),
            if e.1 = 0 then 0 else 1 / ((((p ^ e.1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [hrewrite]
    rw [hleft]
    calc
      _ ≤ 1 / ((p : ℝ) - 1) := hgeom
      _ = r / (1 - r) := by
        dsimp only [r]
        field_simp [ne_of_gt hpR, ne_of_gt (sub_pos.mpr hp1R)]
  calc
    (∑ e ∈ Finset.range (γ + 1),
        if e = 0 then 0 else ((2 * e + 1 : ℕ) : ℝ) * r ^ e) =
      2 * (∑ e ∈ Finset.range (γ + 1), (e : ℝ) * r ^ e) +
        (∑ e ∈ Finset.range (γ + 1), if e = 0 then 0 else r ^ e) := by
          rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro e he
          by_cases hz : e = 0
          · simp [hz]
          · simp only [hz, if_false]
            push_cast
            ring
    _ ≤ 2 * (r / (1 - r) ^ 2) + r / (1 - r) :=
      add_le_add (mul_le_mul_of_nonneg_left hweighted (by norm_num)) htail
    _ = (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
      dsimp only [r]
      field_simp [ne_of_gt hpR, ne_of_gt (sub_pos.mpr hp1R)]
      ring

lemma sum_firstLocalFactor_le
    (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1)) :
    (∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
      firstLocalFactor S hi j e) ≤
      if j.1 = i then
        1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)
      else
        1 + (1 - S.delta j.1)⁻¹ *
          (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) := by
  let p := primeAt Q (stageCoordinate Q hi j)
  let γ := Q.factorization p
  have hp2 : 2 ≤ p := (primeAt_prime Q (stageCoordinate Q hi j)).two_le
  have hgeom := fin_inv_pow_sum_le p γ hp2
  by_cases hjlast : j.1 = i
  · simp only [firstLocalFactor, p, γ, hjlast, if_true]
    exact hgeom
  · rw [if_neg hjlast]
    simp only [firstLocalFactor, p, γ, hjlast, if_false]
    have hinv : 0 ≤ (1 - S.delta j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])
    calc
      (∑ e : Fin (γ + 1),
        if e.1 = 0 then 1 else
          (1 - S.delta j.1)⁻¹ / (((p ^ e.1 : ℕ) : ℝ))) =
        ∑ e : Fin (γ + 1), ((if e.1 = 0 then 1 else 0) +
            (1 - S.delta j.1)⁻¹ *
              (if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ)))) := by
                apply Finset.sum_congr rfl
                intro e he
                by_cases he0 : e.1 = 0
                · simp [he0]
                · simp [he0, div_eq_mul_inv]
      _ = 1 + (1 - S.delta j.1)⁻¹ *
          (∑ e : Fin (γ + 1),
            if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp
      _ ≤ 1 + (1 - S.delta j.1)⁻¹ *
          (1 / ((p : ℝ) - 1)) := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left hgeom hinv) 1

lemma sum_secondLocalFactor_le
    (S : Distortion.Schedule (primePowerSize Q))
    {i : ℕ} (hi : i < primeCount Q) (j : Fin (i + 1)) :
    (∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
      ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
        secondLocalFactor S hi j e₁ e₂) ≤
      if j.1 = i then
        (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) ^ 2
      else
        1 + (1 - S.delta j.1)⁻¹ *
          ((3 * (primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) /
            ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) ^ 2) := by
  let p := primeAt Q (stageCoordinate Q hi j)
  let γ := Q.factorization p
  have hp2 : 2 ≤ p := (primeAt_prime Q (stageCoordinate Q hi j)).two_le
  have hgeom := fin_inv_pow_sum_le p γ hp2
  have hdouble := fin_double_max_sum_le p γ hp2
  by_cases hjlast : j.1 = i
  · simp only [secondLocalFactor, p, γ, hjlast, if_true]
    let f : Fin (γ + 1) → ℝ := fun e =>
      if e.1 = 0 then 0 else 1 / (((p ^ e.1 : ℕ) : ℝ))
    have hrewrite (e₁ e₂ : Fin (γ + 1)) :
        (if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
          1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))) = f e₁ * f e₂ := by
      dsimp only [f]
      by_cases h₁ : e₁.1 = 0
      · simp [h₁]
      · by_cases h₂ : e₂.1 = 0
        · simp [h₂]
        · simp only [h₁, h₂, false_or, if_false]
          push_cast
          rw [pow_add]
          field_simp
    calc
      (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
          if e₁.1 = 0 ∨ e₂.1 = 0 then 0 else
            1 / (((p ^ (e₁.1 + e₂.1) : ℕ) : ℝ))) =
          ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), f e₁ * f e₂ := by
        apply Finset.sum_congr rfl
        intro e₁ he₁
        apply Finset.sum_congr rfl
        intro e₂ he₂
        exact hrewrite e₁ e₂
      _ = (∑ e : Fin (γ + 1), f e) * (∑ e : Fin (γ + 1), f e) := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_mul]
      _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 := by
        rw [pow_two]
        exact mul_self_le_mul_self (Finset.sum_nonneg fun e he => by
          dsimp only [f]
          positivity) hgeom
  · rw [if_neg hjlast]
    simp only [secondLocalFactor, p, γ, hjlast, if_false]
    have hinv : 0 ≤ (1 - S.delta j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [S.delta_lt_one j.1])
    let splitTerm : Fin (γ + 1) → Fin (γ + 1) → ℝ := fun e₁ e₂ =>
      (if max e₁.1 e₂.1 = 0 then 1 else 0) +
        (1 - S.delta j.1)⁻¹ *
          (if max e₁.1 e₂.1 = 0 then 0 else
            1 / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ)))
    have hone :
        (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
          if max e₁.1 e₂.1 = 0 then (1 : ℝ) else 0) = 1 := by
      simp [Fin.sum_univ_succ, max_eq_zero]
      rw [show (Finset.univ.filter fun x : Fin (γ + 1) => x = 0) = {0} by
        ext x
        simp]
      simp
    calc
      (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
        if max e₁.1 e₂.1 = 0 then 1 else
          (1 - S.delta j.1)⁻¹ / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ))) =
        ∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1), splitTerm e₁ e₂ := by
        apply Finset.sum_congr rfl
        intro e₁ he₁
        apply Finset.sum_congr rfl
        intro e₂ he₂
        dsimp only [splitTerm]
        by_cases hz : max e₁.1 e₂.1 = 0
        · simp [hz]
        · simp [hz, div_eq_mul_inv]
      _ = 1 + (1 - S.delta j.1)⁻¹ *
          (∑ e₁ : Fin (γ + 1), ∑ e₂ : Fin (γ + 1),
            if max e₁.1 e₂.1 = 0 then 0 else
              1 / (((p ^ max e₁.1 e₂.1 : ℕ) : ℝ))) := by
        simp_rw [splitTerm]
        simp_rw [Finset.sum_add_distrib]
        rw [hone]
        simp_rw [← Finset.mul_sum]
      _ ≤ 1 + (1 - S.delta j.1)⁻¹ *
          ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hdouble hinv) 1

lemma sum_stage_first_products_le_standard
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  calc
    (∑ d ∈ stageIndices Q D i,
      stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, classFactor S d.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          firstLocalFactor S hi j e :=
        sum_stage_first_products_le_euler S D hQ hd hdQ hi
    _ ≤ ∏ j : Fin (i + 1),
        if j.1 = i then
          1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)
        else
          1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact Finset.sum_nonneg fun e he => firstLocalFactor_nonneg S hi j e
      · intro j hj
        exact sum_firstLocalFactor_le S hi j
    _ = (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, if_true, stageCoordinate]
      rw [mul_comm]
      congr 1
      apply Fintype.prod_congr
      intro j
      simp only [Fin.val_castSucc, Nat.ne_of_lt j.2, if_false, stageCoordinate]

lemma sum_stage_second_products_le_standard
    (S : Distortion.Schedule (primePowerSize Q))
    (D : Finset ℕ) (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0)
    (hdQ : ∀ d ∈ D, d ∣ Q) {i : ℕ} (hi : i < primeCount Q) :
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
  calc
    (∑ d₁ ∈ stageIndices Q D i, ∑ d₂ ∈ stageIndices Q D i,
      (stageCoefficient Q d₁.1 i * stageCoefficient Q d₂.1 i) *
        ∏ j ∈ Finset.range i, pairFactor S d₁.1 d₂.1 j) ≤
      ∏ j : Fin (i + 1),
        ∑ e₁ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
          ∑ e₂ : Fin (Q.factorization (primeAt Q (stageCoordinate Q hi j)) + 1),
            secondLocalFactor S hi j e₁ e₂ :=
      sum_stage_second_products_le_euler S D hQ hd hdQ hi
    _ ≤ ∏ j : Fin (i + 1),
        if j.1 = i then
          (1 / ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1)) ^ 2
        else
          1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) /
              ((primeAt Q (stageCoordinate Q hi j) : ℝ) - 1) ^ 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact Finset.sum_nonneg fun e₁ he₁ =>
          Finset.sum_nonneg fun e₂ he₂ => secondLocalFactor_nonneg S hi j e₁ e₂
      · intro j hj
        exact sum_secondLocalFactor_le S hi j
    _ = (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, if_true, stageCoordinate]
      rw [mul_comm]
      congr 1
      apply Fintype.prod_congr
      intro j
      simp only [Fin.val_castSucc, Nat.ne_of_lt j.2, if_false, stageCoordinate]

lemma firstMoment_stageBad_le_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.firstMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  exact (firstMoment_stageBad_le_products Q D a hQ hd hdQ delta hdelta0 hdelta1 hi).trans
    (sum_stage_first_products_le_standard S D hQ hd hdQ hi)

lemma secondMoment_stageBad_le_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.secondMoment (Distortion.prefixProb S i)
        (stageBad Q D a hQ hd hdQ i) ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  exact (secondMoment_stageBad_le_products Q D a hQ hd hdQ delta hdelta0 hdelta1 hi).trans
    (sum_stage_second_products_le_standard S D hQ hd hdQ hi)

lemma stageCost_le_first_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.stageCost S i ≤
      (1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            (1 / ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1))) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.stageCost S i ≤
        Distortion.firstMoment (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        arithmeticSchedule] using
        (Distortion.step_mass_bad_le_first (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) (hdelta0 i) (hdelta1 i))
    _ ≤ _ := firstMoment_stageBad_le_standard Q D a hQ hd hdQ delta hdelta0 hdelta1 hi

lemma stageCost_le_second_standard
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) {i : ℕ} (hi : i < primeCount Q)
    (hdi : 0 < delta i) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    Distortion.stageCost S i ≤
      ((1 / ((primeAt Q ⟨i, hi⟩ : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * delta i * (1 - delta i)) := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  calc
    Distortion.stageCost S i ≤
        Distortion.secondMoment (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) / (4 * delta i * (1 - delta i)) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        arithmeticSchedule] using
        (Distortion.step_mass_bad_le_second (Distortion.prefixProb S i)
          (stageBad Q D a hQ hd hdQ i) hdi (hdelta1 i))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right
      · exact secondMoment_stageBad_le_standard Q D a hQ hd hdQ delta hdelta0 hdelta1 hi
      · exact mul_nonneg (mul_nonneg (by norm_num) hdi.le)
          (sub_nonneg.mpr (hdelta1 i).le)

/-- Reconstruct a divisor of `Q` from its exponents on the enumerated prime
coordinates of `Q`. -/
lemma prod_primeAt_pow_factorization_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q) :
    (∏ j : Fin (primeCount Q),
      primeAt Q j ^ d.factorization (primeAt Q j)) = d := by
  calc
    (∏ j : Fin (primeCount Q),
      primeAt Q j ^ d.factorization (primeAt Q j)) =
        ∏ p : PrimeIndex Q, p.1 ^ d.factorization p.1 := by
      apply Fintype.prod_equiv (primeEnum Q).toEquiv
      intro j
      rfl
    _ = ∏ p ∈ Q.primeFactors, p ^ d.factorization p := by
      simpa using
        (Finset.prod_attach Q.primeFactors
          (fun p : ℕ => p ^ d.factorization p))
    _ = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
      symm
      apply Finset.prod_subset (Nat.primeFactors_mono hdQ hQ)
      intro p hpQ hpd
      have hpprime := Nat.prime_of_mem_primeFactors hpQ
      have hpnd : ¬p ∣ d := by
        intro hpdvd
        exact hpd (hpprime.mem_primeFactors hpdvd hd)
      rw [Nat.factorization_eq_zero_of_not_dvd hpnd, pow_zero]
    _ = d := (Nat.prod_primeFactors_pow_factorization hd).symm

/-- If `d` is assigned to stage `i`, its prime factorization is already
contained in the prefix through the `i`-th prime coordinate. -/
lemma prod_stage_prime_powers_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i) :
    (∏ j : Fin (i + 1),
      primeAt Q (stageCoordinate Q hi j) ^
        d.factorization (primeAt Q (stageCoordinate Q hi j))) = d := by
  let e : Fin (i + 1) ↪ Fin (primeCount Q) :=
    Fin.castLEEmb (Nat.succ_le_of_lt hi)
  let s : Finset (Fin (primeCount Q)) := Finset.univ.map e
  have hprefix :
      (∏ j : Fin (i + 1),
        primeAt Q (stageCoordinate Q hi j) ^
          d.factorization (primeAt Q (stageCoordinate Q hi j))) =
        ∏ j ∈ s, primeAt Q j ^ d.factorization (primeAt Q j) := by
    change (∏ j : Fin (i + 1),
        primeAt Q (stageCoordinate Q hi j) ^
          d.factorization (primeAt Q (stageCoordinate Q hi j))) =
      ∏ j ∈ Finset.univ.map e, primeAt Q j ^ d.factorization (primeAt Q j)
    rw [Finset.prod_map]
    rfl
  rw [hprefix]
  calc
    (∏ j ∈ s, primeAt Q j ^ d.factorization (primeAt Q j)) =
        ∏ j : Fin (primeCount Q),
          primeAt Q j ^ d.factorization (primeAt Q j) := by
      apply Finset.prod_subset (Finset.subset_univ s)
      intro j hjuniv hjnot
      have hjgt : i < j.1 := by
        by_contra hnot
        have hjle : j.1 ≤ i := Nat.le_of_not_gt hnot
        let k : Fin (i + 1) := ⟨j.1, Nat.lt_succ_iff.mpr hjle⟩
        have heq : e k = j := Fin.ext rfl
        apply hjnot
        exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, heq⟩
      have hz := ((assignedAt_iff_of_lt Q d hi).mp ha).2 j.1 hjgt j.2
      rw [hz, pow_zero]
    _ = d := prod_primeAt_pow_factorization_eq Q d hQ hd hdQ

/-- A modulus assigned at a prime below `K` is `K`-smooth. -/
lemma mem_smoothNumbers_of_assignedAt
    (Q d K : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    {i : ℕ} (hi : i < primeCount Q) (ha : assignedAt Q d i)
    (hpK : primeAt Q ⟨i, hi⟩ < K) :
    d ∈ K.smoothNumbers := by
  rw [Nat.mem_smoothNumbers_iff_primeFactors_subset]
  refine ⟨hd, ?_⟩
  intro p hpd
  have hpQ : p ∈ Q.primeFactors := Nat.primeFactors_mono hdQ hQ hpd
  let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
  have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
  have hki : k.1 ≤ i := by
    by_contra hnot
    have hik : i < k.1 := Nat.lt_of_not_ge hnot
    have hz := ((assignedAt_iff_of_lt Q d hi).mp ha).2 k.1 hik k.2
    have hpos : d.factorization p ≠ 0 :=
      (Nat.prime_of_mem_primeFactors hpd).factorization_pos_of_dvd hd
        (Nat.dvd_of_mem_primeFactors hpd) |>.ne'
    exact hpos (by simpa only [hpk] using hz)
  have hple : p ≤ primeAt Q ⟨i, hi⟩ := by
    rw [← hpk]
    exact (primeAt_strictMono Q).monotone hki
  exact Nat.mem_primesBelow.mpr
    ⟨hple.trans_lt hpK, Nat.prime_of_mem_primeFactors hpd⟩

/-! ### From surviving prefixes back to congruence classes -/

lemma castHom_castHom {k m n : ℕ} (hkm : k ∣ m) (hmn : m ∣ n)
    (x : ZMod n) :
    ZMod.castHom hkm (ZMod k) (ZMod.castHom hmn (ZMod m) x) =
      ZMod.castHom (hkm.trans hmn) (ZMod k) x := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((ZMod.castHom hkm (ZMod k)).comp (ZMod.castHom hmn (ZMod m)))
    (ZMod.castHom (hkm.trans hmn) (ZMod k))) x

/-- Each component of the prime-power CRT equivalence is the canonical
reduction map. -/
lemma equivPi_apply_eq_castHom
    (Q : ℕ) (hQ : Q ≠ 0) (x : ZMod Q) (p : PrimeIndex Q) :
    ZMod.equivPi (n := Q) hQ x p =
      ZMod.castHom
        ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hQ |>.2 le_rfl)
        (ZMod (p.1 ^ Q.factorization p.1)) x := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1)) p).comp
        (ZMod.equivPi (n := Q) hQ).toRingHom)
    (ZMod.castHom
      ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hQ |>.2 le_rfl)
      (ZMod (p.1 ^ Q.factorization p.1)))) x

/-- Applying CRT to a full prefix recovers the corresponding transported
prime-power coordinate. -/
lemma equivPi_prefixCRTEq_apply
    (Q : ℕ) (hQ : Q ≠ 0)
    (x : Distortion.Prefix (primePowerSize Q) (primeCount Q))
    (i : Fin (primeCount Q)) :
    ZMod.equivPi (n := Q) hQ (prefixCRTEq Q hQ x) (primeEnum Q i) =
      finPrimePowerEquiv Q i
        (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x i) := by
  let v : (j : Fin (primeCount Q)) →
      ZMod (((primeEnum Q j).1) ^ Q.factorization (primeEnum Q j).1) :=
    fun j => by
      simpa only [primeAt] using finPrimePowerEquiv Q j
        (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x j)
  let w : (p : PrimeIndex Q) → ZMod (p.1 ^ Q.factorization p.1) :=
    Equiv.piCongrLeft
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
      (primeEnum Q).toEquiv v
  have hx : prefixCRTEq Q hQ x =
      (ZMod.equivPi (n := Q) hQ).symm w := rfl
  rw [hx, (ZMod.equivPi (n := Q) hQ).apply_symm_apply]
  dsimp only [w]
  change (Equiv.piCongrLeft
      (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
      (primeEnum Q).toEquiv v) (primeEnum Q i) = v i
  exact Equiv.piCongrLeft_apply_apply
    (fun p : PrimeIndex Q => ZMod (p.1 ^ Q.factorization p.1))
    (primeEnum Q).toEquiv v i

/-- One coordinate restriction means precisely reduction to `b` modulo the
corresponding prime power of `d`. -/
lemma mem_classCoordinates_iff_cast
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (i : Fin (primeCount Q))
    (x : Distortion.Coordinate (primePowerSize Q i.1)) :
    x ∈ classCoordinates Q d hQ hd hdQ b i.1 ↔
      ZMod.castHom
        (pow_dvd_pow (primeAt Q i)
          ((Nat.factorization_le_iff_dvd hd hQ).mpr hdQ (primeAt Q i)))
        (ZMod ((primeAt Q i) ^ d.factorization (primeAt Q i)))
        (finPrimePowerEquiv Q i x) =
      (b : ZMod ((primeAt Q i) ^ d.factorization (primeAt Q i))) := by
  by_cases he : d.factorization (primeAt Q i) = 0
  · simp [classCoordinates, primeRestriction, finPrimePowerEquiv, i.isLt, he]
    have hone : (primeAt Q i) ^ d.factorization (primeAt Q i) = 1 := by
      rw [he, pow_zero]
    rw [hone]
    exact Subsingleton.elim _ _
  · simp [classCoordinates, primeRestriction, finPrimePowerEquiv, i.isLt, he]
    have hcast :
        (Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt).symm)).symm x =
          Equiv.cast (congrArg Fin (primePowerSize_of_lt Q i.isLt)) x := by
      rfl
    rw [hcast]
    constructor <;> intro h <;> convert h using 1 <;> congr 2

/-- A full prefix belongs to a congruence-class box whenever its CRT residue
reduces to that class modulo `d`. -/
lemma mem_classBox_of_cast_eq
    (Q d : ℕ) (hQ : Q ≠ 0) (hd : d ≠ 0) (hdQ : d ∣ Q)
    (b : ℤ) (x : Distortion.Prefix (primePowerSize Q) (primeCount Q))
    (hx : ZMod.castHom hdQ (ZMod d) (prefixCRTEq Q hQ x) = (b : ZMod d)) :
    x ∈ classBox Q d hQ hd hdQ b (primeCount Q) := by
  rw [classBox, Distortion.mem_box_iff_mem_coordinate]
  intro i
  rw [mem_classCoordinates_iff_cast Q d hQ hd hdQ b i]
  let p := primeAt Q i
  let γ := Q.factorization p
  let e := d.factorization p
  have hp : p.Prime := primeAt_prime Q i
  have heγ : e ≤ γ := (Nat.factorization_le_iff_dvd hd hQ).mpr hdQ p
  have hpeD : p ^ e ∣ d := (hp.pow_dvd_iff_le_factorization hd).2 le_rfl
  have hpγQ : p ^ γ ∣ Q := (hp.pow_dvd_iff_le_factorization hQ).2 le_rfl
  have hpeQ : p ^ e ∣ Q := hpeD.trans hdQ
  have hcoord := equivPi_prefixCRTEq_apply Q hQ x i
  have hproj := equivPi_apply_eq_castHom Q hQ (prefixCRTEq Q hQ x) (primeEnum Q i)
  have hfrom := congrArg (fun y : ZMod d => ZMod.castHom hpeD (ZMod (p ^ e)) y) hx
  have hleft :
      ZMod.castHom (pow_dvd_pow p heγ) (ZMod (p ^ e))
          (finPrimePowerEquiv Q i
            (Distortion.prefixEquivPi (primePowerSize Q) (primeCount Q) x i)) =
        ZMod.castHom hpeQ (ZMod (p ^ e)) (prefixCRTEq Q hQ x) := by
    rw [← hcoord, hproj]
    exact castHom_castHom (pow_dvd_pow p heγ) hpγQ _
  rw [hleft]
  rw [← castHom_castHom hpeD hdQ (prefixCRTEq Q hQ x)]
  simpa using hfrom

/-- Every divisor `d > 1` of `Q` is assigned to the coordinate of its
largest prime factor. -/
lemma exists_assignedAt
    (Q d : ℕ) (hQ : Q ≠ 0) (hdQ : d ∣ Q) (hd2 : 2 ≤ d) :
    ∃ i < primeCount Q, assignedAt Q d i := by
  have hd0 : d ≠ 0 := by omega
  have hpf : d.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let p := d.primeFactors.max' hpf
  have hpD : p ∈ d.primeFactors := Finset.max'_mem d.primeFactors hpf
  have hpQ : p ∈ Q.primeFactors := Nat.primeFactors_mono hdQ hQ hpD
  let k : Fin (primeCount Q) := (primeEnum Q).symm ⟨p, hpQ⟩
  refine ⟨k.1, k.2, (assignedAt_iff_of_lt Q d k.2).mpr ?_⟩
  have hpk : primeAt Q k = p := primeAt_primeEnum_symm Q ⟨p, hpQ⟩
  constructor
  · rw [hpk]
    exact (Nat.prime_of_mem_primeFactors hpD).factorization_pos_of_dvd hd0
      (Nat.dvd_of_mem_primeFactors hpD) |>.ne'
  · intro j hkj hj
    by_contra hfac
    have hpj : (primeAt Q ⟨j, hj⟩).Prime := primeAt_prime Q ⟨j, hj⟩
    have hpjd : primeAt Q ⟨j, hj⟩ ∣ d := by
      exact (hpj.dvd_iff_one_le_factorization hd0).2
        (Nat.one_le_iff_ne_zero.mpr hfac)
    have hpjD : primeAt Q ⟨j, hj⟩ ∈ d.primeFactors :=
      hpj.mem_primeFactors hpjd hd0
    have hjle : primeAt Q ⟨j, hj⟩ ≤ p := Finset.le_max' d.primeFactors _ hpjD
    have hp_lt : p < primeAt Q ⟨j, hj⟩ := by
      rw [← hpk]
      exact primeAt_strictMono Q hkj
    omega

/-- A residue surviving through stage `n` lies outside every congruence box
assigned before that stage. -/
lemma residual_not_mem_assigned_classBox
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (delta : ℕ → ℝ) (hdelta0 : ∀ i, 0 ≤ delta i)
    (hdelta1 : ∀ i, delta i < 1) :
    let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
    ∀ (n : ℕ) (x : Distortion.Prefix (primePowerSize Q) n),
      x ∈ Distortion.residual S n →
      ∀ (d : ModulusIndex D) (i : ℕ), i < n → assignedAt Q d.1 i →
        x ∉ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) n := by
  dsimp only
  let S := arithmeticSchedule Q D a hQ hd hdQ delta hdelta0 hdelta1
  intro n
  induction n with
  | zero =>
      intro x hx d i hi
      omega
  | succ n ih =>
      intro z hz d i hi ha hclass
      rcases z with ⟨x, y⟩
      have hzparts :
          x ∈ Distortion.residual S n ∧ y ∉ S.bad n x := by
        change (x, y) ∈ Distortion.oldPairs (Distortion.residual S n) \
          Distortion.badPairs (S.bad n) at hz
        have hraw := Finset.mem_sdiff.mp hz
        have hold := Finset.mem_product.mp hraw.1
        refine ⟨hold.1, ?_⟩
        intro hy
        apply hraw.2
        exact (Distortion.mem_badPairs_iff (S.bad n) x y).mpr hy
      rw [classBox, Distortion.box_succ] at hclass
      have hclassparts := Finset.mem_product.mp hclass
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | heq
      · exact ih x hzparts.1 d i hin ha hclassparts.1
      · subst i
        apply hzparts.2
        change y ∈ stageBad Q D a hQ hd hdQ n x
        rw [stageBad]
        apply Finset.mem_biUnion.mpr
        refine ⟨d, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, ha⟩
        · have hxclass :
              x ∈ classBox Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) (a d.1) n :=
            hclassparts.1
          rw [classSection, if_pos hxclass]
          exact hclassparts.2

end Arithmetic

/-! ## Analytic bounds for the large-prime tail -/

namespace Analytic

open Filter Asymptotics

/-- The local second-moment Euler factor is bounded by a coarse exponential
majorant.  The constant `20` is chosen so that the estimate also covers the
small prime `2`. -/
lemma second_factor_le_exp (p : ℕ) (hp : 2 ≤ p) :
    1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
      Real.exp (20 / (p : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hrat :
      2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
        20 / (p : ℝ) := by
    rw [show 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) =
      (2 * (3 * (p : ℝ) - 1)) / ((p : ℝ) - 1) ^ 2 by ring]
    rw [div_le_div_iff₀ (sq_pos_of_pos hp1) hp0]
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  calc
    1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) ≤
        1 + 20 / (p : ℝ) := by linarith
    _ ≤ Real.exp (20 / (p : ℝ)) := by
      simpa [add_comm] using Real.add_one_le_exp (20 / (p : ℝ))

/-- The full prime Euler product which majorizes the earlier-coordinate
second-moment factors. -/
def secondEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y,
    (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2))

/-- The earlier prime divisors of `Q` form a subset of all primes up to the
current prime, so their local factors are bounded by the full Euler product. -/
lemma prior_second_factors_le_euler
    (Q : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    (∏ j : Fin i,
      (1 + 2 *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  let e : Fin i ↪ ℕ :=
    ⟨fun j => Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩,
      fun j k hjk => by
        have heq : (⟨j.1, j.2.trans hi⟩ : Fin (Arithmetic.primeCount Q)) =
            ⟨k.1, k.2.trans hi⟩ :=
          (Arithmetic.primeAt_strictMono Q).injective hjk
        have hval : j.1 = k.1 :=
          congrArg (fun x : Fin (Arithmetic.primeCount Q) => x.1) heq
        exact Fin.ext hval⟩
  let s : Finset ℕ := Finset.univ.map e
  have hprod :
      (∏ j : Fin i,
        (1 + 2 *
          ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
            ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) =
        ∏ p ∈ s, (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) := by
    change (∏ j : Fin i,
        (1 + 2 *
          ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
            ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) =
      ∏ p ∈ Finset.univ.map e,
        (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2))
    rw [Finset.prod_map]
    rfl
  rw [hprod]
  unfold secondEulerProduct
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hp' := Finset.mem_map.mp hp
    obtain ⟨j, hj, rfl⟩ := hp'
    exact Nat.mem_primesLE.mpr ⟨by
      have hlt : (⟨j.1, j.2.trans hi⟩ : Fin (Arithmetic.primeCount Q)) < ⟨i, hi⟩ :=
        j.2
      exact ((Arithmetic.primeAt_strictMono Q) hlt).le,
      Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hp
    have hp2 : (2 : ℝ) ≤ e j := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤ (3 * (e j : ℝ) - 1) / ((e j : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    linarith
  · intro p hp hpnot
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    have hrat : 0 ≤ (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    linarith

lemma secondEulerProduct_le_exp_primeSum (y : ℕ) :
    secondEulerProduct y ≤
      Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
  unfold secondEulerProduct
  calc
    ∏ p ∈ Nat.primesLE y,
        (1 + 2 * ((3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) ≤
      ∏ p ∈ Nat.primesLE y, Real.exp (20 / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by
            exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
          have hrat : 0 ≤ (3 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 :=
            div_nonneg (by linarith) (sq_nonneg _)
          linarith
        · intro p hp
          exact second_factor_le_exp p (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    _ = Real.exp (∑ p ∈ Nat.primesLE y, 20 / (p : ℝ)) := by
      rw [Real.exp_sum]
    _ = Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Mertens' estimate turns the local-factor product into a fixed power of
`log y`. -/
theorem exists_secondEulerProduct_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20 := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 Erdos448.eventually_prime_reciprocal_sum_le_loglog_add_one
  let S : ℝ := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  let C₀ : ℝ := |meissel_mertens| + 1 + S + |Real.log (Real.log 3)|
  refine ⟨Real.exp (20 * C₀), Real.exp_pos _, ?_⟩
  intro y hy
  have hsumUpper :
      (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.log (Real.log (y : ℝ)) + C₀ := by
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun p _ ↦ div_nonneg zero_le_one (Nat.cast_nonneg p)
    by_cases hNy : N ≤ y
    · have h := hN y hNy
      have hsumId :
          (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (p : ℝ)⁻¹) =
            ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p := by
        apply Finset.sum_congr
        · ext p
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
          constructor
          · rintro ⟨⟨_, hpy⟩, hp⟩
            exact ⟨hpy, hp⟩
          · rintro ⟨hpy, hp⟩
            exact ⟨⟨hp.pos, hpy⟩, hp⟩
        · intro p _
          exact (one_div (p : ℝ)).symm
      rw [hsumId] at h
      dsimp [C₀]
      linarith [le_abs_self meissel_mertens, abs_nonneg (Real.log (Real.log 3))]
    · have hyN : y ≤ N := (Nat.lt_of_not_ge hNy).le
      have hmono : (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤ S := by
        dsimp [S]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.mpr
            ⟨(Nat.mem_primesLE.mp hp).1.trans hyN, (Nat.mem_primesLE.mp hp).2⟩
        · intro p _ _
          exact div_nonneg zero_le_one (Nat.cast_nonneg p)
      have hlog : Real.log (Real.log (3 : ℝ)) ≤ Real.log (Real.log (y : ℝ)) := by
        apply Real.log_le_log
        · exact Real.log_pos (by norm_num)
        · apply Real.log_le_log (by norm_num)
          exact_mod_cast hy
      dsimp [C₀]
      linarith [abs_nonneg meissel_mertens,
        neg_le_of_abs_le (le_rfl : |Real.log (Real.log 3)| ≤ |Real.log (Real.log 3)|)]
  apply (secondEulerProduct_le_exp_primeSum y).trans
  calc
    Real.exp (20 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.exp (20 * (Real.log (Real.log (y : ℝ)) + C₀)) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsumUpper (by norm_num))
    _ = Real.exp (20 * C₀) * Real.log (y : ℝ) ^ 20 := by
      have hlog : 0 < Real.log (y : ℝ) := by
        exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      rw [show 20 * (Real.log (Real.log (y : ℝ)) + C₀) =
          20 * C₀ + Real.log (Real.log (y : ℝ)) * 20 by ring,
        Real.exp_add]
      congr 1
      calc
        Real.exp (Real.log (Real.log (y : ℝ)) * 20) =
            Real.exp ((20 : ℕ) * Real.log (Real.log (y : ℝ))) := by
          congr 1
          norm_num
          ring
        _ = Real.exp (Real.log (Real.log (y : ℝ))) ^ 20 :=
          Real.exp_nat_mul _ _
        _ = Real.log (y : ℝ) ^ 20 := by rw [Real.exp_log hlog]

/-- The integer majorant for the large-prime stage costs is summable. -/
lemma summable_log_pow_twenty_div_sq :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) := by
  have hlo :
      (fun x : ℝ => Real.log x ^ (20 : ℝ)) =o[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    exact isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (20 : ℝ) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2 ≤
        1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    have hbound := (hlo.comp_tendsto tendsto_natCast_atTop_atTop).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hbound, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn hn2
    have hn' : Real.log (n : ℝ) ^ (20 : ℝ) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        Real.log (n : ℝ) ^ (20 : ℝ) ≤
            |Real.log (n : ℝ) ^ (20 : ℝ)| := le_abs_self _
        _ ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := by
          simpa only [Function.comp_apply, one_mul, Real.norm_eq_abs] using hn
        _ = (n : ℝ) ^ (1 / 2 : ℝ) :=
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hnNat : Real.log (n : ℝ) ^ (20 : ℕ) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact hn'
    have hnpos : (0 : ℝ) < n := by positivity
    calc
      Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2 ≤
          (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnNat (sq_nonneg _)
      _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by
          norm_num [Real.rpow_two]]
        rw [← Real.rpow_sub hnpos]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hO :
      (fun n : ℕ => Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) =O[atTop]
        (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hevent, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn hn2
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hn
  exact summable_of_isBigO_nat
    (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3 / 2))
    hO

/-! ### A two-level distortion schedule and its large-stage bound -/

/-- The small-prime coordinates are left uniform, while all later coordinates
use distortion parameter `1/2`. -/
def tailDelta (k i : ℕ) : ℝ := if i < k then 0 else 1 / 2

lemma tailDelta_nonneg (k i : ℕ) : 0 ≤ tailDelta k i := by
  unfold tailDelta
  split_ifs <;> norm_num

lemma tailDelta_lt_one (k i : ℕ) : tailDelta k i < 1 := by
  unfold tailDelta
  split_ifs <;> norm_num

lemma tailDelta_eq_half {k i : ℕ} (hki : k ≤ i) :
    tailDelta k i = 1 / 2 := by
  simp [tailDelta, Nat.not_lt.mpr hki]

lemma prior_schedule_factors_le_euler
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (k : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
    (∏ j : Fin i,
      (1 + (1 - S.delta j.1)⁻¹ *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  dsimp only [Arithmetic.arithmeticSchedule]
  apply (Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)).trans
    (prior_second_factors_le_euler Q hi)
  · have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    have hinv : 0 ≤ (1 - tailDelta k j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [tailDelta_lt_one k j.1])
    positivity
  · have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
      exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
    have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    have hinv : (1 - tailDelta k j.1)⁻¹ ≤ 2 := by
      rw [tailDelta]
      split_ifs <;> norm_num
    have hmul := mul_le_mul_of_nonneg_right hinv hrat
    linarith

lemma reciprocal_sub_one_sq_le_four_div_sq (p : ℕ) (hp : 2 ≤ p) :
    (1 / ((p : ℝ) - 1)) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_pow, one_pow, div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)]
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

/-- Every stage at or above the cutoff is bounded by the common summable
majorant supplied by the Mertens Euler-product estimate. -/
lemma large_stage_cost_le
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {k i : ℕ} (hk : 1 ≤ k) (hki : k ≤ i) (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
    Distortion.stageCost S i ≤
      4 * C * Real.log (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 20 /
        (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (tailDelta k)
      (tailDelta_nonneg k) (tailDelta_lt_one k)
  let p := Arithmetic.primeAt Q ⟨i, hi⟩
  have hdi : 0 < tailDelta k i := by rw [tailDelta_eq_half hki]; norm_num
  have hpprime := Arithmetic.primeAt_prime Q ⟨i, hi⟩
  have hp3 : 3 ≤ p := by
    have hpc : 0 < Arithmetic.primeCount Q := by omega
    let z : Fin (Arithmetic.primeCount Q) := ⟨0, hpc⟩
    have hzero : z < ⟨i, hi⟩ := by
      exact (show 0 < i by omega)
    have hpgt := Arithmetic.primeAt_strictMono Q hzero
    have hp0 := (Arithmetic.primeAt_prime Q z).two_le
    omega
  calc
    Distortion.stageCost S i ≤
      ((1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * tailDelta k i * (1 - tailDelta k i)) := by
      exact Arithmetic.stageCost_le_second_standard Q D a hQ hd hdQ
        (tailDelta k) (tailDelta_nonneg k) (tailDelta_lt_one k) hi hdi
    _ = (1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [tailDelta_eq_half hki]
      norm_num
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 * secondEulerProduct p := by
      apply mul_le_mul_of_nonneg_left
      · exact prior_schedule_factors_le_euler Q D a hQ hd hdQ k hi
      · positivity
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 *
        (C * Real.log (p : ℝ) ^ 20) := by
      apply mul_le_mul_of_nonneg_left (hC p hp3)
      positivity
    _ ≤ (4 / (p : ℝ) ^ 2) * (C * Real.log (p : ℝ) ^ 20) := by
      apply mul_le_mul_of_nonneg_right
      · exact reciprocal_sub_one_sq_le_four_div_sq p hpprime.two_le
      · exact mul_nonneg hC0 (by positivity)
    _ = 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by ring

/-! A prime-value cutoff is more convenient for summing the large-prime tail
and identifying the complementary smooth moduli. -/

def primeTailDelta (Q K i : ℕ) : ℝ :=
  if hi : i < Arithmetic.primeCount Q then
    if Arithmetic.primeAt Q ⟨i, hi⟩ < K then 0 else 1 / 2
  else 0

lemma primeTailDelta_nonneg (Q K i : ℕ) : 0 ≤ primeTailDelta Q K i := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma primeTailDelta_lt_one (Q K i : ℕ) : primeTailDelta Q K i < 1 := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma primeTailDelta_eq_half (Q K : ℕ) {i : ℕ}
    (hi : i < Arithmetic.primeCount Q)
    (hK : K ≤ Arithmetic.primeAt Q ⟨i, hi⟩) :
    primeTailDelta Q K i = 1 / 2 := by
  simp [primeTailDelta, hi, Nat.not_lt.mpr hK]

lemma primeTailDelta_inv_le_two (Q K i : ℕ) :
    (1 - primeTailDelta Q K i)⁻¹ ≤ (2 : ℝ) := by
  unfold primeTailDelta
  split_ifs <;> norm_num

lemma prior_prime_schedule_factors_le_euler
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∏ j : Fin i,
      (1 + (1 - S.delta j.1)⁻¹ *
        ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) ≤
      secondEulerProduct (Arithmetic.primeAt Q ⟨i, hi⟩) := by
  dsimp only [Arithmetic.arithmeticSchedule]
  apply (Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)).trans
    (prior_second_factors_le_euler Q hi)
  · have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 := by
      have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
        exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
      exact div_nonneg (by linarith) (sq_nonneg _)
    have hinv : 0 ≤ (1 - primeTailDelta Q K j.1)⁻¹ :=
      inv_nonneg.mpr (by linarith [primeTailDelta_lt_one Q K j.1])
    positivity
  · have hrat : 0 ≤
        (3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
          ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2 := by
      have hp2 : (2 : ℝ) ≤ Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ := by
        exact_mod_cast (Arithmetic.primeAt_prime Q ⟨j.1, j.2.trans hi⟩).two_le
      exact div_nonneg (by linarith) (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right
      (primeTailDelta_inv_le_two Q K j.1) hrat
    linarith

/-- A stage whose current prime is at least the prime-value cutoff has a cost
bounded by the common summable integer majorant. -/
lemma large_prime_stage_cost_le
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    {K i : ℕ} (hK3 : 3 ≤ K) (hi : i < Arithmetic.primeCount Q)
    (hKp : K ≤ Arithmetic.primeAt Q ⟨i, hi⟩) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i ≤
      4 * C * Real.log (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 20 /
        (Arithmetic.primeAt Q ⟨i, hi⟩ : ℝ) ^ 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  let p := Arithmetic.primeAt Q ⟨i, hi⟩
  have hdi : 0 < primeTailDelta Q K i := by
    rw [primeTailDelta_eq_half Q K hi hKp]
    norm_num
  have hpprime := Arithmetic.primeAt_prime Q ⟨i, hi⟩
  have hp3 : 3 ≤ p := hK3.trans hKp
  calc
    Distortion.stageCost S i ≤
      ((1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2))) /
        (4 * primeTailDelta Q K i * (1 - primeTailDelta Q K i)) := by
      exact Arithmetic.stageCost_le_second_standard Q D a hQ hd hdQ
        (primeTailDelta Q K) (primeTailDelta_nonneg Q K)
        (primeTailDelta_lt_one Q K) hi hdi
    _ = (1 / ((p : ℝ) - 1)) ^ 2 *
        ∏ j : Fin i,
          (1 + (1 - S.delta j.1)⁻¹ *
            ((3 * (Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) /
              ((Arithmetic.primeAt Q ⟨j.1, j.2.trans hi⟩ : ℝ) - 1) ^ 2)) := by
      rw [primeTailDelta_eq_half Q K hi hKp]
      norm_num
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 * secondEulerProduct p := by
      exact mul_le_mul_of_nonneg_left
        (prior_prime_schedule_factors_le_euler Q D a hQ hd hdQ K hi) (by positivity)
    _ ≤ (1 / ((p : ℝ) - 1)) ^ 2 *
        (C * Real.log (p : ℝ) ^ 20) := by
      exact mul_le_mul_of_nonneg_left (hC p hp3) (by positivity)
    _ ≤ (4 / (p : ℝ) ^ 2) * (C * Real.log (p : ℝ) ^ 20) := by
      exact mul_le_mul_of_nonneg_right
        (reciprocal_sub_one_sq_le_four_div_sq p hpprime.two_le)
        (mul_nonneg hC0 (by positivity))
    _ = 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by ring

lemma summable_large_majorant (C : ℝ) :
    Summable (fun n : ℕ =>
      4 * C * Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2) := by
  simpa only [mul_div_assoc] using
    summable_log_pow_twenty_div_sq.mul_left (4 * C)

/-- There is a numerical prime cutoff above which the total majorant of any
finite collection of stages is less than `1/2`. -/
lemma exists_large_prime_cutoff (C : ℝ) (hC0 : 0 ≤ C) :
    ∃ K : ℕ, 3 ≤ K ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2 := by
  let f : ℕ → ℝ := fun n =>
    4 * C * Real.log (n : ℝ) ^ 20 / (n : ℝ) ^ 2
  have hf : Summable f := summable_large_majorant C
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hf) (1 / 2) (by norm_num)
  let K := max 3 (s.sup id + 1)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro P hP
  have hdisj : Disjoint P s := Finset.disjoint_left.mpr (by
    intro p hpP hps
    have hple : p ≤ s.sup id := Finset.le_sup (f := id) hps
    have hKle : s.sup id + 1 ≤ K := le_max_right _ _
    have hKp := hP p hpP
    omega)
  have hnorm := hs P hdisj
  have hnonneg : 0 ≤ ∑ p ∈ P, f p := by
    apply Finset.sum_nonneg
    intro p hp
    dsimp only [f]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) (by positivity))
      (sq_nonneg _)
  change (∑ p ∈ P, f p) < 1 / 2
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm

/-! ## Summing the small-prime and large-prime stages -/

/-- The completely multiplicative reciprocal map used in the Euler product
for smooth numbers. -/
def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    change (((a * b : ℕ) : ℝ))⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    rw [Nat.cast_mul, mul_inv]

/-- The reciprocals of the positive integers all of whose prime factors are
below a fixed cutoff form a summable family. -/
lemma summable_reciprocal_smoothNumbers (K : ℕ) :
    Summable (fun d : K.smoothNumbers => (d.1 : ℝ)⁻¹) := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (inv_nonneg.mpr (by exact_mod_cast hp.pos.le))]
    change (p : ℝ)⁻¹ < 1
    rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalHom) hprime K
  change Summable (fun d : K.smoothNumbers => reciprocalHom d.1)
  exact Summable.of_norm heuler.1

/-- A uniform finite-tail formulation of smooth reciprocal summability. -/
lemma exists_smooth_reciprocal_cutoff (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < ε := by
  let f : K.smoothNumbers → ℝ := fun d => (d.1 : ℝ)⁻¹
  have hf : Summable f := summable_reciprocal_smoothNumbers K
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hf) ε hε
  let M := s.sup (fun d => d.1) + 1
  refine ⟨M, ?_⟩
  intro T hT
  have hdisj : Disjoint T s := Finset.disjoint_left.mpr (by
    intro d hdT hds
    have hdle : d.1 ≤ s.sup (fun e => e.1) := Finset.le_sup hds
    have hMd := hT d hdT
    dsimp only [M] at hMd
    omega)
  have hnorm := hs T hdisj
  have hnonneg : 0 ≤ ∑ d ∈ T, f d :=
    Finset.sum_nonneg fun d hd => inv_nonneg.mpr (Nat.cast_nonneg d.1)
  change (∑ d ∈ T, f d) < ε
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm

lemma firstLocalFactor_primeTailDelta
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (d : Arithmetic.ModulusIndex D)
    (ha : Arithmetic.assignedAt Q d.1 i)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K)
    (j : Fin (i + 1)) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Arithmetic.firstLocalFactor S hi j
      (Arithmetic.stageExponentVector Q d.1 hQ (hd d.1 d.2) (hdQ d.1 d.2) hi j) =
      (1 : ℝ) / ((Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j) ^
        d.1.factorization (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) : ℕ) : ℝ) := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  have hapos := (Arithmetic.assignedAt_iff_of_lt Q d.1 hi).mp ha
  by_cases hlast : j.1 = i
  · have hcoord : Arithmetic.stageCoordinate Q hi j = ⟨i, hi⟩ := Fin.ext hlast
    rw [Arithmetic.firstLocalFactor]
    simp only [hlast, if_true, Arithmetic.stageExponentVector]
    have hne : d.1.factorization
        (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) ≠ 0 := by
      simpa only [hcoord] using hapos.1
    simp [hne]
  · have hjlt : j.1 < i := by omega
    have hjpc : j.1 < Arithmetic.primeCount Q := hjlt.trans hi
    have hprimeLt :
        Arithmetic.primeAt Q ⟨j.1, hjpc⟩ < Arithmetic.primeAt Q ⟨i, hi⟩ := by
      exact Arithmetic.primeAt_strictMono Q hjlt
    have hjK : Arithmetic.primeAt Q ⟨j.1, hjpc⟩ < K := hprimeLt.trans hpK
    have hdelta : primeTailDelta Q K j.1 = 0 := by
      simp [primeTailDelta, hjpc, hjK]
    rw [Arithmetic.firstLocalFactor]
    simp only [hlast, if_false, Arithmetic.stageExponentVector,
      Arithmetic.stageCoordinate]
    by_cases he : d.1.factorization (Arithmetic.primeAt Q ⟨j.1, hjpc⟩) = 0
    · simp [he]
    · simp [S, Arithmetic.arithmeticSchedule, hdelta, he]

/-- At a stage below the prime cutoff, the first-moment weight of an assigned
modulus is exactly its reciprocal. -/
lemma small_stage_weight_eq_inv
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (d : Arithmetic.ModulusIndex D)
    (ha : Arithmetic.assignedAt Q d.1 i)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Arithmetic.stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j =
      1 / (d.1 : ℝ) := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  calc
    Arithmetic.stageCoefficient Q d.1 i *
        ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j =
      ∏ j : Fin (i + 1),
        Arithmetic.firstLocalFactor S hi j
          (Arithmetic.stageExponentVector Q d.1 hQ
            (hd d.1 d.2) (hdQ d.1 d.2) hi j) := by
      symm
      exact Arithmetic.prod_firstLocal_stageExponent S hQ
        (hd d.1 d.2) (hdQ d.1 d.2) hi ha
    _ = ∏ j : Fin (i + 1),
        (1 : ℝ) / ((Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j) ^
          d.1.factorization (Arithmetic.primeAt Q (Arithmetic.stageCoordinate Q hi j)) : ℕ) : ℝ) := by
      apply Fintype.prod_congr
      intro j
      exact firstLocalFactor_primeTailDelta Q D a hQ hd hdQ K hi d ha hpK j
    _ = 1 / (d.1 : ℝ) := by
      simp_rw [div_eq_mul_inv, one_mul]
      rw [Finset.prod_inv_distrib]
      congr 1
      rw [← Nat.cast_prod]
      exact_mod_cast Arithmetic.prod_stage_prime_powers_eq Q d.1 hQ
        (hd d.1 d.2) (hdQ d.1 d.2) hi ha

lemma small_prime_stage_cost_le_sum
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K : ℕ) {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i ≤
      ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  calc
    Distortion.stageCost S i ≤
        Distortion.firstMoment (Distortion.prefixProb S i)
          (Arithmetic.stageBad Q D a hQ hd hdQ i) := by
      simpa only [Distortion.stageCost, Distortion.prefixProb_succ, S,
        Arithmetic.arithmeticSchedule] using
        (Distortion.step_mass_bad_le_first (Distortion.prefixProb S i)
          (Arithmetic.stageBad Q D a hQ hd hdQ i)
          (primeTailDelta_nonneg Q K i) (primeTailDelta_lt_one Q K i))
    _ ≤ ∑ d ∈ Arithmetic.stageIndices Q D i,
        Arithmetic.stageCoefficient Q d.1 i *
          ∏ j ∈ Finset.range i, Arithmetic.classFactor S d.1 j :=
      Arithmetic.firstMoment_stageBad_le_products Q D a hQ hd hdQ
        (primeTailDelta Q K) (primeTailDelta_nonneg Q K)
        (primeTailDelta_lt_one Q K) hi
    _ = ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hdI
      rw [← one_div]
      exact small_stage_weight_eq_inv Q D a hQ hd hdQ K hi d
        ((Finset.mem_filter.mp hdI).2) hpK

lemma small_prime_stage_cost_lt
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K M : ℕ) {ε : ℝ}
    (htail : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) → (∑ d ∈ T, (d.1 : ℝ)⁻¹) < ε)
    (hmin : ∀ d ∈ D, M ≤ d)
    {i : ℕ} (hi : i < Arithmetic.primeCount Q)
    (hpK : Arithmetic.primeAt Q ⟨i, hi⟩ < K) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    Distortion.stageCost S i < ε := by
  dsimp only
  let I := Arithmetic.stageIndices Q D i
  let e : {d // d ∈ I} ↪ K.smoothNumbers :=
    ⟨fun d => ⟨d.1.1, Arithmetic.mem_smoothNumbers_of_assignedAt Q d.1.1 K hQ
        (hd d.1.1 d.1.2) (hdQ d.1.1 d.1.2) hi
        ((Finset.mem_filter.mp d.2).2) hpK⟩,
      fun d₁ d₂ h => by
        have hval : d₁.1.1 = d₂.1.1 :=
          congrArg (fun z : K.smoothNumbers => z.1) h
        exact Subtype.ext (Subtype.ext hval)⟩
  let T : Finset K.smoothNumbers := I.attach.map e
  have hTmin : ∀ d ∈ T, M ≤ d.1 := by
    intro d hdT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hdT
    exact hmin x.1.1 x.1.2
  have hsum :
      (∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹) =
        ∑ d ∈ T, (d.1 : ℝ)⁻¹ := by
    change (∑ d ∈ I, (d.1 : ℝ)⁻¹) = _
    rw [← Finset.sum_attach, Finset.sum_map]
    rfl
  calc
    Distortion.stageCost
        (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
          (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i ≤
      ∑ d ∈ Arithmetic.stageIndices Q D i, (d.1 : ℝ)⁻¹ :=
        small_prime_stage_cost_le_sum Q D a hQ hd hdQ K hi hpK
    _ = ∑ d ∈ T, (d.1 : ℝ)⁻¹ := hsum
    _ < ε := htail T hTmin

/-- The distortion stages whose controlling prime is below `K`. -/
def smallStages (Q K : ℕ) : Finset ℕ :=
  (Finset.range (Arithmetic.primeCount Q)).filter fun i =>
    if hi : i < Arithmetic.primeCount Q then
      Arithmetic.primeAt Q ⟨i, hi⟩ < K
    else False

lemma mem_smallStages_iff (Q K : ℕ) {i : ℕ}
    (hi : i < Arithmetic.primeCount Q) :
    i ∈ smallStages Q K ↔ Arithmetic.primeAt Q ⟨i, hi⟩ < K := by
  simp [smallStages, hi]

lemma card_smallStages_le (Q K : ℕ) :
    (smallStages Q K).card ≤ K := by
  let e : {i // i ∈ smallStages Q K} ↪ Fin K :=
    ⟨fun i =>
      let hi : i.1 < Arithmetic.primeCount Q :=
        Finset.mem_range.mp (Finset.mem_filter.mp i.2).1
      ⟨Arithmetic.primeAt Q ⟨i.1, hi⟩,
        (mem_smallStages_iff Q K hi).mp i.2⟩,
      fun i j h => by
        have hp : Arithmetic.primeAt Q
              ⟨i.1, Finset.mem_range.mp (Finset.mem_filter.mp i.2).1⟩ =
            Arithmetic.primeAt Q
              ⟨j.1, Finset.mem_range.mp (Finset.mem_filter.mp j.2).1⟩ :=
          congrArg Fin.val h
        have hij := (Arithmetic.primeAt_strictMono Q).injective hp
        exact Subtype.ext (congrArg Fin.val hij)⟩
  have hcard := Fintype.card_le_of_injective e e.injective
  simpa using hcard

lemma sum_small_stage_cost_lt_half
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (K M : ℕ)
    (htail : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ smallStages Q K, Distortion.stageCost S i) < 1 / 2 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε0 : 0 ≤ ε := by dsimp only [ε]; positivity
  calc
    (∑ i ∈ smallStages Q K, Distortion.stageCost S i) ≤
        ∑ _i ∈ smallStages Q K, ε := by
      apply Finset.sum_le_sum
      intro i hiS
      have hi : i < Arithmetic.primeCount Q :=
        Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
      have hpK := (mem_smallStages_iff Q K hi).mp hiS
      exact (small_prime_stage_cost_lt Q D a hQ hd hdQ K M htail hmin hi hpK).le
    _ = ((smallStages Q K).card : ℝ) * ε := by simp
    _ ≤ (K : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_smallStages_le Q K) hε0
    _ < 1 / 2 := by
      dsimp only [ε]
      have hden : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
      rw [show (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) =
        (K : ℝ) / (2 * ((K : ℝ) + 1)) by ring]
      rw [div_lt_iff₀ hden]
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- The complementary set of stages whose controlling prime is at least
`K`. -/
def largeStages (Q K : ℕ) : Finset ℕ :=
  Finset.range (Arithmetic.primeCount Q) \ smallStages Q K

lemma mem_largeStages (Q K : ℕ) {i : ℕ} :
    i ∈ largeStages Q K ↔
      ∃ hi : i < Arithmetic.primeCount Q,
        K ≤ Arithmetic.primeAt Q ⟨i, hi⟩ := by
  rw [largeStages, Finset.mem_sdiff]
  constructor
  · rintro ⟨hirange, hismall⟩
    have hi := Finset.mem_range.mp hirange
    refine ⟨hi, ?_⟩
    exact Nat.le_of_not_gt (fun hpK =>
      hismall ((mem_smallStages_iff Q K hi).mpr hpK))
  · rintro ⟨hi, hKp⟩
    refine ⟨Finset.mem_range.mpr hi, ?_⟩
    intro hismall
    exact (Nat.not_lt_of_ge hKp) ((mem_smallStages_iff Q K hi).mp hismall)

lemma sum_large_stage_cost_lt_half
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (htail : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ largeStages Q K, Distortion.stageCost S i) < 1 / 2 := by
  dsimp only
  let I := largeStages Q K
  let e : {i // i ∈ I} ↪ ℕ :=
    ⟨fun i =>
      Arithmetic.primeAt Q
        ⟨i.1, (mem_largeStages Q K).mp i.2 |>.choose⟩,
      fun i j h => by
        have hij := (Arithmetic.primeAt_strictMono Q).injective h
        exact Subtype.ext (congrArg Fin.val hij)⟩
  let P : Finset ℕ := I.attach.map e
  have hP : ∀ p ∈ P, K ≤ p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hp
    exact (mem_largeStages Q K).mp i.2 |>.choose_spec
  have hsum :
      (∑ i ∈ I.attach,
        4 * C * Real.log (e i : ℝ) ^ 20 / (e i : ℝ) ^ 2) =
        ∑ p ∈ P, 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := by
    rw [Finset.sum_map]
  calc
    (∑ i ∈ largeStages Q K,
        Distortion.stageCost
          (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
            (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i) =
      ∑ i ∈ I.attach,
        Distortion.stageCost
          (Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
            (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)) i.1 := by
      change (∑ i ∈ I, _) = _
      rw [← Finset.sum_attach]
    _ ≤ ∑ i ∈ I.attach,
        4 * C * Real.log (e i : ℝ) ^ 20 / (e i : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hiAttach
      let hi : i.1 < Arithmetic.primeCount Q := (mem_largeStages Q K).mp i.2 |>.choose
      have hKp : K ≤ Arithmetic.primeAt Q ⟨i.1, hi⟩ :=
        (mem_largeStages Q K).mp i.2 |>.choose_spec
      have heq : e i = Arithmetic.primeAt Q ⟨i.1, hi⟩ := by
        dsimp only [e]
        congr 1
      rw [heq]
      exact large_prime_stage_cost_le C hC0 hC Q D a hQ hd hdQ hK3 hi hKp
    _ = ∑ p ∈ P, 4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2 := hsum
    _ < 1 / 2 := htail P hP

/-- The complete accumulated distortion cost is strictly below one. -/
lemma sum_all_stage_cost_lt_one
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (hlarge : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (M : ℕ)
    (hsmall : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (∑ i ∈ Finset.range (Arithmetic.primeCount Q),
      Distortion.stageCost S i) < 1 := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  have hs := sum_small_stage_cost_lt_half Q D a hQ hd hdQ K M hsmall hmin
  have hl := sum_large_stage_cost_lt_half C hC0 hC K hK3 hlarge
    Q D a hQ hd hdQ
  have hsubset :
      smallStages Q K ⊆ Finset.range (Arithmetic.primeCount Q) :=
    Finset.filter_subset _ _
  have hunion :
      smallStages Q K ∪ largeStages Q K =
        Finset.range (Arithmetic.primeCount Q) := by
    rw [largeStages, Finset.union_sdiff_of_subset hsubset]
  have hdisj : Disjoint (smallStages Q K) (largeStages Q K) := by
    rw [largeStages]
    exact Finset.disjoint_sdiff
  calc
    (∑ i ∈ Finset.range (Arithmetic.primeCount Q),
        Distortion.stageCost S i) =
      ∑ i ∈ smallStages Q K ∪ largeStages Q K,
        Distortion.stageCost S i := by rw [hunion]
    _ = (∑ i ∈ smallStages Q K, Distortion.stageCost S i) +
        ∑ i ∈ largeStages Q K, Distortion.stageCost S i := by
      rw [Finset.sum_union hdisj]
    _ < 1 := by linarith

/-- The arithmetic distortion process leaves at least one residue after every
stage whenever all moduli lie beyond the smooth-number cutoff. -/
lemma arithmetic_residual_nonempty
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ y : ℕ, 3 ≤ y →
      secondEulerProduct y ≤ C * Real.log (y : ℝ) ^ 20)
    (K : ℕ) (hK3 : 3 ≤ K)
    (hlarge : ∀ P : Finset ℕ, (∀ p ∈ P, K ≤ p) →
      (∑ p ∈ P,
        4 * C * Real.log (p : ℝ) ^ 20 / (p : ℝ) ^ 2) < 1 / 2)
    (M : ℕ)
    (hsmall : ∀ T : Finset K.smoothNumbers,
      (∀ d ∈ T, M ≤ d.1) →
      (∑ d ∈ T, (d.1 : ℝ)⁻¹) < 1 / (2 * ((K : ℝ) + 1)))
    (Q : ℕ) (D : Finset ℕ) (a : ℕ → ℤ)
    (hQ : Q ≠ 0) (hd : ∀ d ∈ D, d ≠ 0) (hdQ : ∀ d ∈ D, d ∣ Q)
    (hmin : ∀ d ∈ D, M ≤ d) :
    let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
    (Distortion.residual S (Arithmetic.primeCount Q)).Nonempty := by
  dsimp only
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ (primeTailDelta Q K)
      (primeTailDelta_nonneg Q K) (primeTailDelta_lt_one Q K)
  apply Distortion.residual_nonempty_of_sum_cost_lt_one
  exact sum_all_stage_cost_lt_one C hC0 hC K hK3 hlarge M hsmall
    Q D a hQ hd hdQ hmin

end Analytic

/-! ## The uniform minimum-modulus theorem -/

/-- The distortion sieve supplies a universal upper bound for the least
modulus of every distinct covering system. -/
theorem uniformMinimumBound : HasUniformMinimumBound := by
  obtain ⟨C, hCpos, hC⟩ := Analytic.exists_secondEulerProduct_log_bound
  obtain ⟨K, hK3, hlarge⟩ := Analytic.exists_large_prime_cutoff C hCpos.le
  have hε : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) := by positivity
  obtain ⟨M, hsmall⟩ := Analytic.exists_smooth_reciprocal_cutoff K hε
  refine ⟨M, ?_⟩
  intro D a hcover
  by_contra hnone
  have hmin : ∀ d ∈ D, M ≤ d := by
    intro d hdD
    exact Nat.le_of_not_gt fun hdM => hnone ⟨d, hdD, hdM⟩
  let Q : ℕ := D.prod id
  have hd : ∀ d ∈ D, d ≠ 0 := by
    intro d hdD
    exact Nat.ne_of_gt (Nat.zero_lt_two.trans_le (hcover.1 d hdD))
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact Finset.prod_ne_zero_iff.mpr hd
  have hdQ : ∀ d ∈ D, d ∣ Q := by
    intro d hdD
    dsimp only [Q]
    exact Finset.dvd_prod_of_mem id hdD
  let S := Arithmetic.arithmeticSchedule Q D a hQ hd hdQ
    (Analytic.primeTailDelta Q K)
    (Analytic.primeTailDelta_nonneg Q K)
    (Analytic.primeTailDelta_lt_one Q K)
  have hres :
      (Distortion.residual S (Arithmetic.primeCount Q)).Nonempty := by
    exact Analytic.arithmetic_residual_nonempty C hCpos.le hC K hK3 hlarge
      M hsmall Q D a hQ hd hdQ hmin
  obtain ⟨x, hx⟩ := hres
  letI : NeZero Q := ⟨hQ⟩
  let y : ZMod Q := Arithmetic.prefixCRTEq Q hQ x
  let z : ℤ := y.val
  obtain ⟨d, hdD, hz⟩ := hcover.2 z
  have hcast :
      ZMod.castHom (hdQ d hdD) (ZMod d) (Arithmetic.prefixCRTEq Q hQ x) =
        (a d : ZMod d) := by
    have hy : (z : ZMod Q) = y := by
      dsimp only [z]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val y
    change ZMod.castHom (hdQ d hdD) (ZMod d) y = (a d : ZMod d)
    rw [← hy]
    simpa using (ZMod.intCast_eq_intCast_iff z (a d) d).2 hz
  have hbox := Arithmetic.mem_classBox_of_cast_eq Q d hQ (hd d hdD)
    (hdQ d hdD) (a d) x hcast
  obtain ⟨i, hi, hai⟩ := Arithmetic.exists_assignedAt Q d hQ (hdQ d hdD)
    (hcover.1 d hdD)
  have houtside := Arithmetic.residual_not_mem_assigned_classBox
    Q D a hQ hd hdQ (Analytic.primeTailDelta Q K)
    (Analytic.primeTailDelta_nonneg Q K)
    (Analytic.primeTailDelta_lt_one Q K)
    (Arithmetic.primeCount Q) x hx ⟨d, hdD⟩ i hi hai
  exact houtside hbox

/-- Equivalent negative formulation: least moduli cannot be arbitrarily
large. -/
theorem not_hasArbitrarilyLargeMinimum : ¬HasArbitrarilyLargeMinimum :=
  uniformBound_iff_not_arbitrarilyLarge.mp uniformMinimumBound

/-- Erdős Problem 2: distinct covering systems have a uniform bound on their
least modulus. -/
theorem erdos_2 :
    ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
      IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M :=
  uniformMinimumBound


end

end Erdos2

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos8.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 8.
https://www.erdosproblems.com/forum/thread/8

Informal authors:
- Bob Hough

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos8.md
-/
/-
This is a Lean formalization of the negative solution to Erdős Problem 8.
https://www.erdosproblems.com/8

The mathematical proof and its source audit are in `tex/8.tex`.
-/




attribute [local instance] Classical.propDecidable

/-- A finite family of congruence classes with distinct nontrivial moduli.

The moduli form a `Finset`, so distinctness is built into the representation.
The function `a` chooses the single residue attached to each modulus. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧
    ∀ z : ℤ, ∃ d ∈ D, Int.ModEq d z (a d)

/-- All moduli of `D` receive one common colour. -/
def Monochromatic {κ : Type*} (colour : ℤ → κ) (D : Finset ℕ) : Prop :=
  ∃ k : κ, ∀ d ∈ D, colour (d : ℤ) = k

/-- The literal universal question in Problem 8, with a nonempty finite palette
represented by `Fin r`. -/
def EveryFiniteColoringHasMonochromaticCover : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ colour : ℤ → Fin r,
    ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
      IsDistinctCoveringSystem D a ∧ Monochromatic colour D

/-- `B` meets the minimum-modulus conclusion if every distinct covering
system contains a modulus at most `B`. -/
def IsMinimumModulusBound (B : ℕ) : Prop :=
  ∀ (D : Finset ℕ) (a : ℕ → ℤ), IsDistinctCoveringSystem D a →
    ∃ d ∈ D, d ≤ B

/-- The cutoff colouring: integers of absolute value at most `B` receive
their absolute value, and every other integer has colour zero.  In particular,
the positive moduli `d ≤ B` all receive distinct nonzero colours. -/
def cutoffColour (B : ℕ) (z : ℤ) : Fin (B + 1) :=
  if h : z.natAbs ≤ B then
    ⟨z.natAbs, by omega⟩
  else
    0

@[simp]
lemma cutoffColour_ofNat_of_le (B d : ℕ) (hd : d ≤ B) :
    cutoffColour B (d : ℤ) = ⟨d, by omega⟩ := by
  simp [cutoffColour, hd]

@[simp]
lemma cutoffColour_ofNat_of_lt (B d : ℕ) (hd : B < d) :
    cutoffColour B (d : ℤ) = 0 := by
  simp [cutoffColour, Nat.not_le.mpr hd]

/-- A small nontrivial modulus has a colour used by no other modulus. -/
lemma cutoffColour_eq_of_small
    {B d e : ℕ} (hd2 : 2 ≤ d) (hdB : d ≤ B)
    (hcolour : cutoffColour B (e : ℤ) = cutoffColour B (d : ℤ)) :
    e = d := by
  by_cases heB : e ≤ B
  · simpa [cutoffColour, hdB, heB] using congrArg Fin.val hcolour
  · have he : B < e := Nat.lt_of_not_ge heB
    have hzero : cutoffColour B (d : ℤ) = 0 := by
      rw [← hcolour, cutoffColour_ofNat_of_lt B e he]
    have := congrArg Fin.val hzero
    simp [cutoffColour, hdB] at this
    omega

/-- One congruence class with modulus greater than one cannot cover the
integers: it misses the successor of its residue. -/
lemma not_modEq_add_one (a : ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ¬ Int.ModEq d (a + 1) a := by
  intro h
  rw [Int.modEq_iff_dvd] at h
  have hd1 : (d : ℤ) ∣ 1 := by
    obtain ⟨k, hk⟩ := h
    refine ⟨-k, ?_⟩
    have hdiff : a - (a + 1) = -1 := by ring
    rw [hdiff] at hk
    calc
      (1 : ℤ) = -(-1) := by omega
      _ = -((d : ℤ) * k) := congrArg Neg.neg hk
      _ = (d : ℤ) * (-k) := by ring
  have : (d : ℤ) ≤ 1 := Int.le_of_dvd (by omega) hd1
  omega

/-- Hough's minimum-modulus conclusion implies the cutoff colouring is a
counterexample to Problem 8. -/
theorem cutoffColour_has_no_monochromatic_cover
    {B : ℕ} (hB : IsMinimumModulusBound B) :
    ∀ (D : Finset ℕ) (a : ℕ → ℤ),
      IsDistinctCoveringSystem D a → ¬ Monochromatic (cutoffColour B) D := by
  intro D a hcover hmono
  obtain ⟨d, hdD, hdB⟩ := hB D a hcover
  obtain ⟨k, hk⟩ := hmono
  have hd2 : 2 ≤ d := hcover.1 d hdD
  have hD : D = {d} := by
    ext e
    constructor
    · intro heD
      have hsame : cutoffColour B (e : ℤ) = cutoffColour B (d : ℤ) :=
        (hk e heD).trans (hk d hdD).symm
      exact Finset.mem_singleton.mpr (cutoffColour_eq_of_small hd2 hdB hsame)
    · intro hed
      have : e = d := by simpa only [Finset.mem_singleton] using hed
      subst e
      exact hdD
  obtain ⟨e, heD, hemod⟩ := hcover.2 (a d + 1)
  rw [hD] at heD
  have hed : e = d := by simpa using heD
  subst e
  exact not_modEq_add_one (a d) hd2 hemod

/-- The elementary reduction from the minimum-modulus theorem to the
negative answer to Erdős Problem 8. -/
theorem negative_answer_of_minimum_modulus_bound
    (hmin : ∃ B : ℕ, IsMinimumModulusBound B) :
    ¬ EveryFiniteColoringHasMonochromaticCover := by
  rintro hall
  obtain ⟨B, hB⟩ := hmin
  obtain ⟨D, a, hcover, hmono⟩ := hall (B + 1) (by omega) (cutoffColour B)
  exact cutoffColour_has_no_monochromatic_cover hB D a hcover hmono

/-- The minimum-modulus input, supplied by the fully proved formalization of
Erdős Problem 2. -/
theorem hough_minimum_modulus_bound :
    ∃ B : ℕ, IsMinimumModulusBound B := by
  obtain ⟨M, hM⟩ := Erdos2.uniformMinimumBound
  refine ⟨M, ?_⟩
  intro D a hcover
  have hcover' : Erdos2.IsDistinctCoveringSystem D a := by
    simpa [IsDistinctCoveringSystem, Erdos2.IsDistinctCoveringSystem] using hcover
  obtain ⟨d, hdD, hdM⟩ := hM D a hcover'
  exact ⟨d, hdD, hdM.le⟩

/-- **Erdős Problem 8.** The answer is no: there is a finite colouring of
the integers for which no distinct covering system has monochromatic
moduli. -/
theorem erdos_8 :
    ¬ (∀ (r : ℕ), 0 < r → ∀ colour : ℤ → Fin r,
      ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
        IsDistinctCoveringSystem D a ∧ Monochromatic colour D) :=
  negative_answer_of_minimum_modulus_bound hough_minimum_modulus_bound

end

#print axioms erdos_8
-- 'Erdos8.erdos_8' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos8
