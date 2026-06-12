import Mathlib

namespace Erdos45

set_option maxErrors 2000

/-!
Vendored single-file copy of the `plby/unit-fractions` Lean 4 formalization,
specialized to Erdős problem 45.

Source files (under `src4/` of `https://github.com/plby/unit-fractions`)
are concatenated in topological dependency order. Project-internal `import`
statements have been removed; Mathlib imports are deduplicated and lifted
above.

The headline theorem `erdos_45` (the original repo's `erdos45`): for every
`k ≥ 2` there is an `nₖ` such that every `k`-colouring of the proper divisors
of `nₖ` admits a monochromatic subset whose reciprocals sum to 1. It follows
from Erdős 46 (helper `erdos_46`) via a compactness argument, which in turn
follows from Erdős 298 (Bloom-Mehta, helper `erdos_298`).
-/

/-! ## From src4/Definitions.lean -/

open scoped BigOperators ArithmeticFunction.omega
open Filter Real Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N

def upper_density : ℝ := limsup (partial_density A) atTop

def lower_density : ℝ := liminf (partial_density A) atTop

def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d

variable {A}

lemma partial_density_sdiff_finset (N : ℕ) (S : Finset ℕ) :
    partial_density A N ≤ partial_density (A \ S) N + S.card / N := by
  classical
  rw [partial_density, partial_density, ← add_div]
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hN
  rw [div_le_div_iff₀ hNpos hNpos]
  have hcard :
      ((range N).filter fun n ↦ n ∈ A).card ≤
        (((range N).filter fun n ↦ n ∈ A \ S).card + S.card) := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro x hx
    rcases mem_filter.mp hx with ⟨hxN, hxA⟩
    rw [mem_union, mem_filter]
    by_cases h : x ∈ S
    · exact Or.inr h
    · exact Or.inl ⟨hxN, hxA, h⟩
  have hcard' : (((range N).filter fun n ↦ n ∈ A).card : ℝ) ≤
      (((range N).filter fun n ↦ n ∈ A \ S).card : ℝ) + (S.card : ℝ) := by
    exact_mod_cast hcard
  simpa using mul_le_mul_of_nonneg_right hcard' hNpos.le

lemma is_bounded_under_ge_partial_density :
    IsBoundedUnder (· ≥ ·) atTop (partial_density A) :=
  isBoundedUnder_of ⟨0, fun _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

lemma is_cobounded_under_le_partial_density :
    IsCoboundedUnder (· ≤ ·) atTop (partial_density A) :=
  is_bounded_under_ge_partial_density.isCoboundedUnder_le

lemma is_bounded_under_le_partial_density :
    IsBoundedUnder (· ≤ ·) atTop (partial_density A) :=
  isBoundedUnder_of
    ⟨1, fun x ↦ div_le_one_of_le₀
      (Nat.cast_le.2 ((card_le_card (filter_subset _ _)).trans (by simp)))
      (Nat.cast_nonneg _)⟩

lemma upper_density_preserved {S : Finset ℕ} :
    upper_density A = upper_density (A \ (S : Set ℕ)) := by
  apply ge_antisymm
  · refine limsup_le_limsup ?_ is_cobounded_under_le_partial_density
      is_bounded_under_le_partial_density
    refine Eventually.of_forall fun N ↦ ?_
    by_cases hN : N = 0
    · simp [partial_density, hN]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hN
    rw [partial_density, partial_density, div_le_div_iff₀ hNpos hNpos]
    have hsubset :
        ((range N).filter fun n ↦ n ∈ A \ S) ⊆ ((range N).filter fun n ↦ n ∈ A) := by
      intro n hn
      rcases mem_filter.mp hn with ⟨hnN, hnAS⟩
      exact mem_filter.mpr ⟨hnN, hnAS.1⟩
    have hcard : (((range N).filter fun n ↦ n ∈ A \ S).card : ℝ) ≤
        (((range N).filter fun n ↦ n ∈ A).card : ℝ) := by
      exact_mod_cast card_le_card hsubset
    simpa using mul_le_mul_of_nonneg_right hcard hNpos.le
  rw [le_iff_forall_pos_le_add]
  intro ε hε
  rw [← sub_le_iff_le_add]
  refine le_limsup_of_le
      (u := partial_density (A \ (S : Set ℕ)))
      (hf := is_bounded_under_le_partial_density (A := A \ (S : Set ℕ))) ?_
  intro a ha
  rw [sub_le_iff_le_add]
  apply limsup_le_of_le is_cobounded_under_le_partial_density
  change ∀ᶠ n in atTop, partial_density A n ≤ a + ε
  have hge := tendsto_natCast_atTop_atTop.eventually_ge_atTop (↑S.card / ε)
  filter_upwards [ha, hge, eventually_gt_atTop 0] with N hN hN' hN''
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN''
  rw [div_le_iff₀ hε] at hN'
  have hS : (S.card : ℝ) / N ≤ ε := by
    rw [div_le_iff₀ hNreal]
    simpa [mul_comm] using hN'
  exact (partial_density_sdiff_finset (A := A) N S).trans (add_le_add hN hS)

lemma frequently_nat_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ᶠ N in atTop, ε < ((range N).filter fun n ↦ n ∈ A).card / N :=
  frequently_lt_of_lt_limsup is_cobounded_under_le_partial_density hA

lemma exists_nat_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ N : ℕ, 0 < N ∧ ε < ((range N).filter fun n ↦ n ∈ A).card / N := by
  simpa using (frequently_atTop'.1 (frequently_nat_of hA) 0)

lemma exists_density_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ N : ℕ, 0 < N ∧ ε * N < ((range N).filter fun n ↦ n ∈ A).card := by
  obtain ⟨N, hN, hN'⟩ := exists_nat_of hA
  refine ⟨N, hN, ?_⟩
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  exact (lt_div_iff₀ hNreal).mp hN'

lemma upper_density_nonneg : 0 ≤ upper_density A := by
  refine le_limsup_of_frequently_le ?_ is_bounded_under_le_partial_density
  exact Frequently.of_forall fun x ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end

-- This is R(A) in the paper.
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

lemma rec_sum_bUnion_disjoint {A : Finset (Finset ℕ)}
    (hA : (A : Set (Finset ℕ)).PairwiseDisjoint id) :
    rec_sum (A.biUnion id) = A.sum rec_sum := by
  simpa [rec_sum] using
    (Finset.sum_biUnion (s := A) (t := id) (f := fun n : ℕ ↦ (1 : ℚ) / n) hA)

lemma rec_sum_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    rec_sum (A ∪ B) = rec_sum A + rec_sum B := by
  simpa [rec_sum] using (Finset.sum_union h (f := fun n : ℕ ↦ (1 : ℚ) / n))

@[simp] lemma rec_sum_empty : rec_sum ∅ = 0 := by simp [rec_sum]

lemma rec_sum_nonneg {A : Finset ℕ} : 0 ≤ rec_sum A :=
  by
    simpa [rec_sum] using
      (sum_nonneg fun i (_hi : i ∈ A) ↦
        div_nonneg zero_le_one (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

lemma rec_sum_mono {A₁ A₂ : Finset ℕ} (h : A₁ ⊆ A₂) : rec_sum A₁ ≤ rec_sum A₂ :=
  by
    simpa [rec_sum] using
      (sum_le_sum_of_subset_of_nonneg h
        (fun i _hi _hnot ↦
          div_nonneg zero_le_one (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i)))

-- can make this stronger without 0 ∉ A but we never care about that case
lemma rec_sum_eq_zero_iff {A : Finset ℕ} (hA : 0 ∉ A) : rec_sum A = 0 ↔ A = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hsum :
        ∀ y ∈ A, (1 : ℚ) / y = 0 := by
      have := (sum_eq_zero_iff_of_nonneg
        (fun y (_hy : y ∈ A) ↦
          div_nonneg zero_le_one (show 0 ≤ (y : ℚ) by exact_mod_cast Nat.zero_le y))).1
        (by simpa [rec_sum] using h)
      simpa using this
    have hx0 := hsum x hx
    have : x = 0 := by
      simpa [one_div] using hx0
    exact hA (this ▸ hx)
  · rintro rfl
    simp

lemma nonempty_of_rec_sum_recip {A : Finset ℕ} {d : ℕ} (hd : 1 ≤ d) :
    rec_sum A = 1 / d → A.Nonempty := by
  intro h
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp only [one_div, zero_eq_inv, rec_sum_empty] at h
  have : 0 < d := hd
  exact this.ne (by exact_mod_cast h)

/--
This is A_q in the paper.
-/
def local_part (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  A.filter fun n ↦ q ∣ n ∧ Nat.Coprime q (n / q)

lemma mem_local_part {A : Finset ℕ} {q : ℕ} (n : ℕ) :
    n ∈ local_part A q ↔ n ∈ A ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  rw [local_part, mem_filter]

lemma local_part_mono {A₁ A₂ : Finset ℕ} {q : ℕ} (h : A₁ ⊆ A₂) :
    local_part A₁ q ⊆ local_part A₂ q :=
  filter_subset_filter _ h

lemma local_part_subset {A : Finset ℕ} {q : ℕ} :
    local_part A q ⊆ A :=
  filter_subset _ _

lemma zero_mem_local_part_iff {A : Finset ℕ} {q : ℕ} (hA : 0 ∉ A) :
    0 ∉ local_part A q :=
  fun i ↦ hA (local_part_subset i)

/--
This is Q_A in the paper. The definition looks a bit different, but `mem_ppowers_in_set` shows
it's the same thing.
-/
def ppowers_in_set (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun n ↦ n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

@[simp] lemma ppowers_in_set_empty : ppowers_in_set ∅ = ∅ := Finset.biUnion_empty

lemma ppowers_in_set_insert_zero (A : Finset ℕ) :
    ppowers_in_set (insert 0 A) = ppowers_in_set A := by
  rw [ppowers_in_set, ppowers_in_set, Finset.biUnion_insert, Nat.divisors_zero, filter_empty,
    empty_union]

lemma ppowers_in_set_erase_zero (A : Finset ℕ) :
    ppowers_in_set (A.erase 0) = ppowers_in_set A := by
  by_cases h : 0 ∈ A
  · rw [← ppowers_in_set_insert_zero, insert_erase h]
  · rw [Finset.erase_eq_of_notMem h]

lemma mem_ppowers_in_set {A : Finset ℕ} {q : ℕ} :
    q ∈ ppowers_in_set A ↔ IsPrimePow q ∧ (local_part A q).Nonempty := by
  constructor
  · intro h
    rcases mem_biUnion.mp h with ⟨n, hnA, hq⟩
    rw [mem_filter, Nat.mem_divisors] at hq
    rcases hq with ⟨⟨hqdiv, _hn0⟩, hpp, hcop⟩
    exact ⟨hpp, ⟨n, by simpa [local_part, hnA, hqdiv, hcop]⟩⟩
  · rintro ⟨hpp, ⟨n, hnlocal⟩⟩
    rcases (mem_local_part (A := A) (q := q) n).mp hnlocal with ⟨hnA, hqdiv, hcop⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      have : q = 1 := by simpa [hn0] using hcop
      exact hpp.ne_one this
    refine mem_biUnion.mpr ⟨n, hnA, ?_⟩
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨hqdiv, hn0⟩, hpp, hcop⟩

lemma zero_not_mem_ppowers_in_set {A : Finset ℕ} : 0 ∉ ppowers_in_set A :=
  fun t ↦ not_isPrimePow_zero (mem_ppowers_in_set.1 t).1

namespace Nat

lemma pow_eq_one_iff {n k : ℕ} : n ^ k = 1 ↔ n = 1 ∨ k = 0 := by
  exact _root_.pow_eq_one_iff

end Nat

lemma factorization_disjoint_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Disjoint a.factorization.support b.factorization.support ↔ a.Coprime b := by
  simpa [Nat.support_factorization] using (Nat.disjoint_primeFactors ha hb)

lemma factorization_eq_iff {n p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∣ n ∧ (p ^ k).Coprime (n / p ^ k) ↔ n.factorization p = k := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_ne n 0 with rfl | hn
    · have hpow : p ^ k = 1 := by simpa using h₂
      exact (hk ((Nat.pow_eq_one_iff.mp hpow).resolve_left hp.ne_one)).elim
    have hp_mem : p ∈ (p ^ k).primeFactorsList := by
      rw [Nat.mem_primeFactorsList_iff_dvd (pow_ne_zero _ hp.ne_zero) hp]
      exact dvd_pow_self _ hk
    have hfac :=
      Nat.factorization_eq_of_coprime_left (a := p ^ k) (b := n / p ^ k) h₂ hp_mem
    rw [Nat.mul_div_cancel' h₁] at hfac
    rw [hfac, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  · intro hk'
    have hn : n ≠ 0 := by
      intro hn0
      simp [hn0] at hk'
      exact hk hk'.symm
    have hdvd : p ^ k ∣ n := by
      have hkle : k ≤ n.factorization p := hk'.ge
      exact (hp.pow_dvd_iff_le_factorization hn).2 hkle
    refine ⟨hdvd, ?_⟩
    have hdiv0 : n / p ^ k ≠ 0 := by
      exact Nat.ne_of_gt <| Nat.div_pos (Nat.le_of_dvd hn.bot_lt hdvd) (pow_pos hp.pos _)
    rw [← factorization_disjoint_iff (pow_ne_zero _ hp.ne_zero) hdiv0]
    rw [Nat.factorization_div hdvd, Nat.Prime.factorization_pow hp,
      Finsupp.support_single_ne_zero _ hk,
      disjoint_singleton_left, Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply, ne_eq,
      tsub_eq_zero_iff_le, not_not, Finsupp.single_eq_same, hk']

lemma coprime_div_iff {n p k : ℕ} (hp : p.Prime) (hn : p ^ k ∣ n) (hk : k ≠ 0) :
    Nat.Coprime (p ^ k) (n / p ^ k) → k = n.factorization p := by
  intro h
  exact (factorization_eq_iff hp hk).1 ⟨hn, h⟩ |>.symm

lemma mem_ppowers_in_set' {A : Finset ℕ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∈ ppowers_in_set A ↔ ∃ n ∈ A, n.factorization p = k := by
  rw [mem_ppowers_in_set, and_iff_right (hp.isPrimePow.pow hk)]
  constructor
  · rintro ⟨n, hnlocal⟩
    rcases (mem_local_part (A := A) (q := p ^ k) n).mp hnlocal with ⟨hnA, hdvd, hcop⟩
    exact ⟨n, hnA, (factorization_eq_iff hp hk).1 ⟨hdvd, hcop⟩⟩
  · rintro ⟨n, hnA, hfac⟩
    have hq := (factorization_eq_iff hp hk).2 hfac
    exact ⟨n, (mem_local_part (A := A) (q := p ^ k) n).2 ⟨hnA, hq.1, hq.2⟩⟩

lemma mem_ppowers_in_set'' {A : Finset ℕ} {n p : ℕ} (hn : n ∈ A) (hpk : n.factorization p ≠ 0) :
    p ^ n.factorization p ∈ ppowers_in_set A :=
  let hp_mem : p ∈ n.primeFactors := by
    simpa [Nat.support_factorization] using (Finsupp.mem_support_iff.2 hpk)
  (mem_ppowers_in_set' (Nat.prime_of_mem_primeFactors hp_mem) hpk).2 ⟨_, hn, rfl⟩

lemma ppowers_in_set_subset {A B : Finset ℕ} (hAB : A ⊆ B) :
    ppowers_in_set A ⊆ ppowers_in_set B :=
  biUnion_subset_biUnion_of_subset_left _ hAB

lemma ppowers_in_set_nonempty {A : Finset ℕ} (hA : ∃ n ∈ A, 2 ≤ n) :
    (ppowers_in_set A).Nonempty := by
  obtain ⟨n, hn, hn'⟩ := hA
  have hne : n ≠ 1 := by linarith
  have hn0 : n ≠ 0 := by linarith
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpk : n.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hn0 hpdvd).ne'
  exact ⟨p ^ n.factorization p, (mem_ppowers_in_set' hp hpk).2 ⟨n, hn, rfl⟩⟩

lemma ppowers_in_set_eq_empty {A : Finset ℕ} (hA : ppowers_in_set A = ∅) :
    ∀ n ∈ A, n < 2 := by
  intro n hn
  by_contra hn2
  exact (ppowers_in_set_nonempty ⟨n, hn, Nat.not_lt.mp hn2⟩).ne_empty hA

lemma ppowers_in_set_eq_empty' {A : Finset ℕ} (hA : ppowers_in_set A = ∅) (hA' : 0 ∉ A) :
    A.lcm id = 1 := by
  have hsubset : A ⊆ {1} := by
    intro n hn
    have hlt := ppowers_in_set_eq_empty hA n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hA' (hn0 ▸ hn)
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have : n = 1 := by omega
    rw [this]
    simp
  rw [Finset.subset_singleton_iff] at hsubset
  rcases hsubset with rfl | rfl <;> simp

-- This is R(A;q) in the paper.
def rec_sum_local (A : Finset ℕ) (q : ℕ) : ℚ :=
  (local_part A q).sum fun n ↦ (q : ℚ) / n

lemma rec_sum_local_disjoint {A B : Finset ℕ} {q : ℕ} (h : Disjoint A B) :
    rec_sum_local (A ∪ B) q = rec_sum_local A q + rec_sum_local B q := by
  simp [rec_sum_local, local_part, filter_union, Finset.sum_union, disjoint_filter_filter h]

lemma rec_sum_local_mono {A₁ A₂ : Finset ℕ} {q : ℕ} (h : A₁ ⊆ A₂) :
    rec_sum_local A₁ q ≤ rec_sum_local A₂ q :=
  by
    simpa [rec_sum_local] using
      (sum_le_sum_of_subset_of_nonneg (local_part_mono h) fun i _ _ ↦
        div_nonneg (show 0 ≤ (q : ℚ) by exact_mod_cast Nat.zero_le q)
          (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

def ppower_rec_sum (A : Finset ℕ) : ℚ :=
  (ppowers_in_set A).sum fun q ↦ (1 : ℚ) / q

lemma ppower_rec_sum_mono {A₁ A₂ : Finset ℕ} (h : A₁ ⊆ A₂) :
    ppower_rec_sum A₁ ≤ ppower_rec_sum A₂ :=
  by
    simpa [ppower_rec_sum] using
      (sum_le_sum_of_subset_of_nonneg (ppowers_in_set_subset h) fun q _ _ ↦
        div_nonneg zero_le_one (show 0 ≤ (q : ℚ) by exact_mod_cast Nat.zero_le q))

def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ y

def arith_regular (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)

lemma arith_regular.subset {N : ℕ} {A A' : Finset ℕ} (hA : arith_regular N A) (hA' : A' ⊆ A) :
    arith_regular N A' :=
  fun n hn ↦ hA n (hA' hn)

-- This is the set D_I
def interval_rare_ppowers (I : Finset ℤ) (A : Finset ℕ) (K : ℝ) : Finset ℕ :=
  (ppowers_in_set A).filter fun q ↦
    (((local_part A q).filter fun n ↦ ∀ x ∈ I, ¬ (n : ℤ) ∣ x).card : ℝ) < K / q

lemma interval_rare_ppowers_subset (I : Finset ℤ) {A : Finset ℕ} (K : ℝ) :
    interval_rare_ppowers I A K ⊆ ppowers_in_set A :=
  filter_subset _ _

-- This is the awkward condition that 'bridges' the hypothesis of the Fourier stuff
-- with the conclusion of the combinatorial bits
def good_condition (A : Finset ℕ) (K T L : ℝ) : Prop :=
  ∀ (t : ℝ) (I : Finset ℤ), I = Finset.Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
    T ≤ (A.filter fun n ↦ ∀ x ∈ I, ¬ (n : ℤ) ∣ x).card ∨
      ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, (q : ℤ) ∣ x


/-! ## From src4/ForMathlib/IntegralRPow.lean -/

noncomputable section

open Filter MeasureTheory

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

theorem integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (Set.Ioi a) :=
  integrableOn_Ioi_rpow_of_lt hr ha

theorem integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫ x in Set.Ioi a, x ^ r = -a ^ (r + 1) / (r + 1) :=
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
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp hb
  simpa [neg_div] using hpow.div_const (r + 1) |>.sub_const (a ^ (r + 1) / (r + 1))

theorem integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ r)⁻¹) (Set.Ioi a) := by
  refine (integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  change x ^ (-r) = (x ^ r)⁻¹
  rw [Real.rpow_neg (ha.trans hx).le]

theorem integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    ∫ x in Set.Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by
    rw [← Real.rpow_neg (ha.trans hx).le])]
  rw [integral_rpow_Ioi (neg_lt_neg hr) ha]
  rw [show -r + 1 = 1 - r by ring]
  rw [show 1 - r = -(r - 1) by ring, div_neg, neg_div, neg_neg]

theorem integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ n) (Set.Ioi a) := by
  simpa using (integrable_on_rpow_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    ∫ x in Set.Ioi a, x ^ n = -a ^ (n + 1) / (n + 1) := by
  exact_mod_cast (integral_rpow_Ioi (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Set.Ioi a) := by
  simpa using (integrable_on_rpow_inv_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Set.Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) := by
  exact_mod_cast (integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Set.Ioi a) := by
  simpa only [← zpow_natCast] using
    (integrable_on_zpow_inv_Ioi (n := (n : ℤ)) (show 1 < (n : ℤ) by exact_mod_cast hn) ha)

theorem integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Set.Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) := by
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


/-! ## From src4/ForMathlib/Misc.lean -/

open scoped BigOperators

/-!
This file only reintroduces the pieces of `src/for_mathlib/misc.lean` that are not already
available in Mathlib4 under the same names.

In particular, Mathlib4 already provides results such as:
* `Rat.cast_sum`
* `Finset.filter_comm`
* `Finset.one_le_prod`
* `Real.finset_prod_rpow`
* `Real.self_le_rpow_of_one_le`
* `Real.self_le_rpow_of_le_one`
* the add-one interval lemmas in `Finset` and `Set`
-/

namespace Int

lemma Ico_succ_right {a b : ℤ} : Finset.Ico a (b + 1) = Finset.Icc a b := by
  simpa using (Finset.Ico_add_one_right_eq_Icc a b)

lemma Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
  simpa [eq_comm] using (Finset.insert_Ioc_right_eq_Ioc_add_one (a := a) (b := b) h)

lemma insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
    insert (a + 1) (Finset.Ioc (a + 1) b) = Finset.Ioc a b := by
  simpa using (Finset.insert_Ioc_add_one_left_eq_Ioc (a := a) (b := b) h)

lemma Ioc_succ_left {a b : ℤ} (h : a < b) :
    Finset.Ioc (a + 1) b = (Finset.Ioc a b).erase (a + 1) := by
  have hnot : a + 1 ∉ Finset.Ioc (a + 1) b := by simp
  rw [← insert_Ioc_succ_left h, Finset.erase_insert hnot]

lemma Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc (a + 1) (b + 1) = (insert (b + 1) (Finset.Ioc a b)).erase (a + 1) := by
  have hab : a < b + 1 := h.trans_lt (lt_add_of_pos_right b zero_lt_one)
  rw [Ioc_succ_left hab, Ioc_succ_right h]

end Int

namespace Finset

lemma Icc_subset_range_add_one {x y : ℕ} : Icc x y ⊆ range (y + 1) := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  exact Finset.Icc_subset_Icc_left (b := y) (Nat.zero_le x)

lemma Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Ico x y ∪ Icc y z = Icc x z := by
  rw [← Finset.coe_inj, Finset.coe_union, Finset.coe_Ico, Finset.coe_Icc, Finset.coe_Icc,
    Set.Ico_union_Icc_eq_Icc h₁ h₂]

lemma Icc_sdiff_Icc_right {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Icc x z \ Icc y z = Ico x y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma Icc_sdiff_Icc_left {x y z : ℕ} (h₁ : z ≤ y) (h₂ : x ≤ z) :
    Icc x y \ Icc x z = Ioc z y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma prod_rpow {ι : Type*} {s : Finset ι} {f : ι → ℝ} (c : ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∏ i ∈ s, f i) ^ c = ∏ i ∈ s, (f i ^ c) := by
  simpa [eq_comm] using (Real.finset_prod_rpow s f hf c)

end Finset

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
  simp only [Set.mem_diff, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · intro hx
    exact lt_of_not_ge fun hxb => hx.2 ⟨hx.1, hxb⟩
  · intro hbx
    exact ⟨hab.trans hbx.le, fun hx => (not_lt_of_ge hx.2) hbx⟩

theorem Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ioi a \ Set.Ioc a b = Set.Ioi b := by
  rw [Set.Ioi_diff_Ioc, max_eq_right hab]

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod (s := s) (f := f) h1)

namespace Real

lemma le_rpow_self_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    x ≤ x ^ r :=
  self_le_rpow_of_one_le hx hr

lemma le_rpow_self_of {x r : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (h_one_le : r ≤ 1) :
    x ≤ x ^ r :=
  self_le_rpow_of_le_one hx₀ hx₁ h_one_le

end Real

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

/-! ## From src4/ForMathlib/BasicEstimates.lean -/

noncomputable section

open Asymptotics Filter Finset MeasureTheory Real
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

def euler_mascheroni : ℝ := 1 - ∫ t in Set.Ioi 1, Int.fract t * (t ^ 2)⁻¹

namespace Nat

theorem cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end Nat

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
  by nlinarith [log_le_sub_one_of_pos hx]

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

set_option quotPrecheck false in
scoped[Chebyshev] notation "ϑ" => chebyshev_first

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
  (hx : x ∈ Set.Ico (n : ℝ) (n + 1)) :
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

@[measurability] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor

end SummatoryExtra

namespace ArithmeticFunction

lemma sigma_zero_eq_zeta_mul_zeta :
  ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  ArithmeticFunction.sigma 0 i = ∑ _ ∈ i.divisors, 1 := by
  rw [ArithmeticFunction.sigma_apply, Finset.sum_congr rfl]
  intro _ _
  simp

end ArithmeticFunction

namespace Finset

lemma Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

lemma prod_eq_prod_iff_of_le' {ι : Type*}
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

end Finset

namespace Nat

@[simp] lemma floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

lemma divisors_nonempty_iff {n : ℕ} : n.divisors.Nonempty ↔ n ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty, Nat.divisors_eq_empty]

end Nat

lemma tendsto_log_log_log_coe_at_top :
    Tendsto (fun x : ℕ ↦ log (log (log (x : ℝ)))) atTop atTop := by
  exact tendsto_log_atTop.comp tendsto_log_log_coe_at_top

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Set.Icc x y)) :
  IntegrableOn (summatory a k * f) (Set.Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Set.Icc x y) := Integrable.smul b hf'
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
  (hf : ∀ i ∈ Set.Icc (k : ℝ) N, HasDerivAt f (f' i) i) (hf' : IntegrableOn f' (Set.Icc k N)) :
  ∑ n ∈ Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Set.Icc (k : ℝ) N, summatory a k t * f' t := by
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
    (hf : ∀ i ∈ Set.Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Set.Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Set.Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
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
    (hf : ∀ i ∈ Set.Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Set.Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc

theorem partial_summation' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} (hk : k ≠ 0) (hf : ∀ i ∈ Set.Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Set.Ici k)) {x : ℝ} :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono_set Set.Icc_subset_Ici_self)

theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Set.Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Set.Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Set.Icc_subset_Ici_self)

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
      (1 - (∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
        Int.fract x * x⁻¹ := by
  have diff : ∀ i ∈ Set.Ici (1 : ℝ), HasDerivAt (fun x ↦ x⁻¹) (-(i ^ 2)⁻¹) i := by
    intro i hi
    exact hasDerivAt_inv (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun i : ℝ ↦ (i ^ 2)⁻¹) (Set.Ici 1) := by
    refine (ContinuousOn.inv₀ (f := fun i : ℝ ↦ i ^ 2) (s := Set.Ici 1)
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
        Set.EqOn
          (fun a : ℝ ↦ Int.fract a * (a ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 a * -(a ^ 2)⁻¹)
          (fun y : ℝ ↦ y⁻¹) (Set.Ioc 1 x) := by
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
        ∫ t in Set.Ioc 1 x,
            (Int.fract t * (t ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹) = log x := by
      rw [setIntegral_congr_fun measurableSet_Ioc hEqOn, ← intervalIntegral.integral_of_le hx,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    have hfloor : ((⌊x⌋ : ℝ)) = x - Int.fract x := by
      rw [Int.self_sub_fract]
    have hf :
        Integrable (fun t : ℝ ↦ Int.fract t * (t ^ 2)⁻¹) (volume.restrict (Set.Ioc 1 x)) := by
      exact (fract_mul_integrable _ ((cont.mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self)).integrable
    have hgpos :
        Integrable (fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (volume.restrict (Set.Ioc 1 x)) := by
      exact (partial_summation_integrable _ ((cont.mono Set.Icc_subset_Ici_self).integrableOn_Icc)
        |>.mono_set Set.Ioc_subset_Icc_self).integrable
    have hxinv : x * x⁻¹ = (1 : ℝ) := by
      field_simp [(zero_lt_one.trans_le hx).ne']
    have hA : (x - Int.fract x) * x⁻¹ = 1 - Int.fract x * x⁻¹ := by
      rw [sub_mul, hxinv]
    rw [hfloor, hA] at *
    let I : ℝ := ∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹
    let K : ℝ := ∫ t in Set.Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹
    have hIK : I + K = log x := by
      calc
        I + K =
            ∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ +
              summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹ := by
                symm
                simpa [I, K] using (integral_add hf hgpos)
        _ = log x := by
          simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using hInt0
    have hJneg :
        ∫ t in Set.Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹ = -K := by
      simpa [K, mul_neg] using
        (integral_neg (f := fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (μ := volume.restrict (Set.Ioc 1 x)))
    have hK : K = log x - I := by
      linarith
    rw [hJneg, hK]
    simp [I, sq, hxinv]
    ring_nf

lemma euler_mascheroni_convergence_rate :
  Asymptotics.IsBigOWith 1 atTop
    (fun x : ℝ ↦ 1 - (∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨1, ?_⟩
  intro x hx
  have h : IntegrableOn (fun x : ℝ ↦ Int.fract x * (x ^ 2)⁻¹) (Set.Ioi 1) := by
    refine fract_mul_integrable _ ?_
    exact integrable_on_pow_inv_Ioi one_lt_two zero_lt_one
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ← setIntegral_diff measurableSet_Ioc h Set.Ioc_subset_Ioi_self,
    Ioi_diff_Icc hx, norm_of_nonneg]
  · refine (setIntegral_mono_on (h.mono_set (Set.Ioi_subset_Ioi hx))
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
  Tendsto (fun x : ℝ ↦ 1 - ∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  simpa using
    (euler_mascheroni_convergence_rate.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  Tendsto (fun x : ℝ ↦ (1 : ℝ) - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  refine euler_mascheroni_integral_Ioc_convergence.congr' ?_
  change ∀ᶠ x : ℝ in atTop,
    1 - ∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ =
      1 - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹
  rw [eventually_atTop]
  exact ⟨1, fun x hx ↦ by rw [intervalIntegral.integral_of_le hx]⟩

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
    (1 - (∫ t in Set.Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
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
  have diff : ∀ i ∈ Set.Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Set.Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Set.Ici 1) continuousOn_id ?_
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
        Set.EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Set.Ioc 1 x) := by
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
    exact (cont.mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Set.Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Set.Ioc_subset_Icc_self

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
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, ge_iff_le, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [Set.uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Set.Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        simpa [Pi.mul_apply] using fract_mul_integrable (s := Set.Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Set.Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
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
    simpa using ((Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul c)).deriv
  cases le_total (Real.log c) x with
  | inl hx =>
      have hmono : MonotoneOn (fun y ↦ Real.exp y - c * y) (Set.Icc (Real.log c) x) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (Real.log c) x) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonneg, ← Real.log_le_iff_le_exp hc]
            exact hy.1.le
      exact hmono (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx
  | inr hx =>
      have hanti : AntitoneOn (fun y ↦ Real.exp y - c * y) (Set.Icc x (Real.log c)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x (Real.log c)) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonpos, ← Real.le_log_iff_exp_le hc]
            exact hy.2.le
      exact hanti (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx

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
        exact Real.finset_prod_rpow _ (fun p => ((p : ℕ) : ℝ) ^ (n.factorization p))
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
  simpa using Chebyshev.theta_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  simpa using Chebyshev.psi_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

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
  suffices h : ∀ y ∈ Set.Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Set.Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Set.Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Set.Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Set.Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · convert (hasDerivWithinAt_id y (Set.Ici y)).rpow_const (Or.inl hy'.ne') using 1
      norm_num
    · convert (hasDerivWithinAt_id y (Set.Ici y)).rpow_const (Or.inl hy'.ne') using 1
      norm_num
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
  |∑ n ∈ Finset.Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Finset.Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Finset.Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Finset.Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      ∑ p ∈ filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
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
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Finset.Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Finset.Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, if_pos]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Finset.Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Finset.Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Finset.Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Finset.Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Finset.Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
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
      ∑ n ∈ Finset.Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Finset.Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Finset.Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Finset.Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Finset.Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
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
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
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
  (π ⌊x⌋₊ : ℝ) * log x - chebyshev_first x = ∫ t in Set.Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
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
  change ‖∫ t in Set.Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Set.Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Set.Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Set.Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Set.Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Set.Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Set.Icc 1 x, (1 : ℝ) = x - 1 := by
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

@[measurability] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Set.Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Ioi 1) := by
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
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Ioi a) := by
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
  ∫ x in Set.Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.Ioi 1) := by
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
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Set.Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Set.Ici (2 : ℝ) = Set.Ico 2 k ∪ Set.Ici k := by
    rw [Set.Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Set.Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Set.Icc 2 k) := by
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
        ∀ᵐ x : ℝ ∂volume.restrict (Set.Ici k),
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
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Set.Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Set.Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Set.Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Set.Ici (2 : ℝ)) := by
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
          (volume.restrict (Set.Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (my_func2_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Set.Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Set.Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Set.Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Set.Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Set.Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Set.Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Set.Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Set.Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Set.Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Set.Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Set.Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
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
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Set.Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf

lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Set.Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Set.Ici y),
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
          (fun y ↦ ∫ x in Set.Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Set.Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Set.Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
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
  convert sum_thing_has_sum 0 using 1
  · ext n
    norm_num [add_sub_assoc]
  · simp [Finset.sum_range_succ]

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
  Summable (s.indicator ((setOf Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) := by
  exact (sum_thing'_has_sum.summable.indicator _).indicator _

lemma indicator_mono {α β : Type*} [Zero β] [Preorder β] {s t : Set α} {f : α → β}
    (h : s ⊆ t) (hf : ∀ x, x ∉ s → x ∈ t → 0 ≤ f x) :
  Set.indicator s f ≤ Set.indicator t f := by
  intro x
  by_cases hs : x ∈ s
  · simp [Set.indicator_of_mem, hs, h hs]
  · by_cases ht : x ∈ t
    · simp [Set.indicator_of_notMem, hs, ht, hf x hs ht]
    · simp [Set.indicator_of_notMem, hs, ht]

lemma prime_sum_thing {k : ℕ} (hk : 1 ≤ k) :
  tsum
      ({n | k < n}.indicator ((setOf Nat.Prime).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) ≤
    ((k : ℝ)⁻¹) := by
  refine hasSum_le ?_ (prime_sum_thing_summable' _).hasSum (sum_thing''_indicator_has_sum hk)
  intro n
  by_cases hkn : k < n
  · by_cases hpn : Nat.Prime n
    · simp [Set.indicator_of_mem, hkn, hpn]
    · have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (lt_of_le_of_lt hk hkn)
      have hnonneg : 0 ≤ (n : ℝ)⁻¹ * ((n : ℝ) - 1)⁻¹ := by
        apply mul_nonneg
        · positivity
        · exact inv_nonneg.2 (sub_nonneg.mpr hn1.le)
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hkn, hpn, hnonneg]
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
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Finset.Icc 1 ⌊x⌋₊, f i - c)
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
    simpa only [← Finset.Ico_succ_right_eq_Icc, inv_pow] using
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
      (hx.irreducible.isUnit_or_isUnit hpow).resolve_left hp.not_unit
    exact hp.not_unit <| (is_unit_of_is_unit_pow (a := p) (k - 1) (by omega)).mp hu

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

lemma squarefree_primorial (n : ℕ) : Squarefree (primorial n) := by
  exact squarefree_prime_prod id (by simp) (fun _ _ _ _ h => h)

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


/-! ## From src4/AuxiliaryLemmas.lean -/

open Filter Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

noncomputable section

/-!
This file ports the statement surface of the old `src/aux_lemmas.lean`.

Several results from the Lean 3 file are now available directly in Mathlib 4, sometimes under
slightly different names. In particular, this file mainly re-exports or lightly repackages:

* `tendsto_mul_exp_add_div_pow_atTop`
* `tendsto_nat_ceil_atTop`
* `Nat.dvd_iff_prime_pow_dvd_dvd`
* `ArithmeticFunction.sigma_zero_apply`
* the harmonic-series asymptotics around `Real.eulerMascheroniConstant`

The remaining declarations below are included for API coverage.
-/

theorem tendsto_mul_add_div_pow_log_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (b * x + c) / log x ^ n) atTop atTop :=
  ((tendsto_mul_exp_add_div_pow_atTop b c n hb).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]

theorem tendsto_pow_rec_log_log_at_top {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ (c / Real.log (Real.log x))) atTop atTop := by
  have haux : Tendsto (fun x : ℝ => c * x / Real.log x) atTop atTop := by
    simpa [pow_one, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_mul_add_div_pow_log_at_top c 0 1 hc
  refine ((tendsto_exp_atTop.comp haux).comp tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem tendsto_nat_ceil_at_top {α : Type*} [Semiring α] [LinearOrder α]
    [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌈x⌉₊) atTop atTop := by
  simpa using (tendsto_nat_ceil_atTop : Tendsto (fun x : α => ⌈x⌉₊) atTop atTop)

theorem weird_floor_sq_tendsto_at_top :
    Tendsto (fun x : ℝ => ⌈Real.logb 2 x⌉₊ ^ 2) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
    tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide)
  simpa using hpow.comp (tendsto_nat_ceil_atTop.comp (Real.tendsto_logb_atTop one_lt_two))

theorem tendsto_pow_at_top_of {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto (fun x : ℝ => g x ^ f x) l atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log (g x)) l atTop := tendsto_log_atTop.comp hg
  have hf' : ∀ᶠ x in l, c / 2 ≤ f x := by
    exact (hf.eventually (Ioi_mem_nhds (show c / 2 < c by linarith))).mono fun _ hx => le_of_lt hx
  have hmul : Tendsto (fun x : ℝ => Real.log (g x) * f x) l atTop := by
    have hbase : Tendsto (fun x : ℝ => (c / 2) * Real.log (g x)) l atTop :=
      Tendsto.const_mul_atTop (show 0 < c / 2 by linarith) hlog
    refine tendsto_atTop_mono' _ ?_ hbase
    filter_upwards [hf', hg.eventually_gt_atTop (1 : ℝ)] with x hx hxg
    have hxlog : 0 ≤ Real.log (g x) := le_of_lt (Real.log_pos hxg)
    nlinarith
  refine (tendsto_exp_atTop.comp hmul).congr' ?_
  filter_upwards [hg.eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, mul_comm]

theorem tendsto_pow_rec_loglog_spec_at_top :
    Tendsto (fun x : ℝ => x ^ ((1 : ℝ) - 8 / Real.log (Real.log x))) atTop atTop := by
  refine tendsto_pow_at_top_of zero_lt_one ?_ tendsto_id
  have hzero : Tendsto (fun x : ℝ => (8 : ℝ) / Real.log (Real.log x)) atTop (𝓝 0) := by
    exact
      (show Tendsto (fun _ : ℝ => (8 : ℝ)) atTop (𝓝 8) from tendsto_const_nhds).div_atTop
        (tendsto_log_atTop.comp tendsto_log_atTop)
  simpa using tendsto_const_nhds.sub hzero

section

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

theorem sum_bUnion_le_sum_of_nonneg {f : ℕ → M} {s : Finset ℕ} {t : ℕ → Finset ℕ}
    (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    (s.biUnion t).sum f ≤ ∑ x ∈ s, ∑ i ∈ t x, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert n s hns hs =>
      have hunion :
          (insert n s).biUnion t = s.biUnion t ∪ (t n \ s.biUnion t) := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
          rcases Finset.mem_insert.mp hm with rfl | hm
          · by_cases hxs : x ∈ s.biUnion t
            · exact Finset.mem_union.mpr <| Or.inl hxs
            · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hxm, hxs⟩
          · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨m, hm, hxm⟩
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
            exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
          · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, (Finset.mem_sdiff.mp hx).1⟩
      have hf' : ∀ x ∈ s.biUnion t, 0 ≤ f x := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
        exact hf x <| Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
      rw [hunion, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_insert hns, add_comm]
      have htail :
          Finset.sum (t n \ s.biUnion t) f ≤ Finset.sum (t n) f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
        intro x hx _
        exact hf x <| Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, hx⟩
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add (hs hf') htail

end

theorem nat_cast_diff_issue {x y : ℤ} : (|x - y| : ℝ) = Int.natAbs (x - y) := by
  calc
    |(x : ℝ) - y| = |((x - y : ℤ) : ℝ)| := by norm_num
    _ = ((Int.natAbs (x - y) : ℕ) : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

theorem harmonic_sum_bound_two :
    ∀ᶠ N in (atTop : Filter ℕ), (Finset.sum (range (N + 1)) fun n => (1 : ℝ) / n) ≤
      2 * Real.log N := by
  filter_upwards [eventually_ge_atTop 6] with N hN
  have hN0 : N ≠ 0 := by omega
  have hsum : Finset.sum (range (N + 1)) (fun n => (1 : ℝ) / n) = ((harmonic N : ℚ) : ℝ) := by
    have h1N : 1 ≤ N + 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ h1N]
    rw [Finset.Ico_add_one_right_eq_Icc]
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hseq :
      (((harmonic N : ℚ) : ℝ) - Real.log N) = Real.eulerMascheroniSeq' N := by
    simp [Real.eulerMascheroniSeq', hN0]
  have hsmall : (((harmonic N : ℚ) : ℝ) - Real.log N) < 2 / 3 := by
    rw [hseq]
    exact (Real.strictAnti_eulerMascheroniSeq'.antitone (by omega)).trans_lt
      Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hlog : (2 / 3 : ℝ) ≤ Real.log N := by
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    have hlog2 : Real.log 2 ≤ Real.log N :=
      log_le_log_of_le (show 0 < (2 : ℝ) by norm_num) h2N
    linarith [Real.log_two_gt_d9]
  rw [hsum]
  have : (((harmonic N : ℚ) : ℝ)) ≤ Real.log N + 2 / 3 := by linarith
  refine this.trans ?_
  linarith

theorem sum_le_card_mul_real {A : Finset ℕ} {M : ℝ} {f : ℕ → ℝ}
    (h : ∀ n ∈ A, f n ≤ M) :
    A.sum f ≤ A.card * M := by
  simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul A f M h)

theorem two_in_Icc {a b x y : ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (|x - y| : ℝ) ≤ b - a := by
  rcases Finset.mem_Icc.mp hx with ⟨hax, hxb⟩
  rcases Finset.mem_Icc.mp hy with ⟨hay, hyb⟩
  have habs : |x - y| ≤ b - a := by
    refine abs_le.mpr ?_
    constructor <;> linarith
  exact_mod_cast habs

theorem two_in_Icc' {a b x y : ℤ} (I : Finset ℤ) (hI : I = Icc a b) (hx : x ∈ I) (hy : y ∈ I) :
    (|x - y| : ℝ) ≤ b - a := by
  rw [hI] at hx hy
  exact two_in_Icc hx hy

theorem dvd_iff_ppowers_dvd (d n : ℕ) :
    d ∣ n ↔ ∀ q, q ∣ d → IsPrimePow q → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpkd
    by_cases hk : k = 0
    · simp [hk]
    · exact h (p ^ k) hpkd (hp.isPrimePow.pow hk)

theorem dvd_iff_ppowers_dvd' (d n : ℕ) (hd : d ≠ 0) :
    d ∣ n ↔ ∀ q, q ∣ d → (IsPrimePow q ∧ Nat.Coprime q (d / q)) → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [dvd_iff_ppowers_dvd]
    intro q hqd hq
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    let r := p ^ d.factorization p
    have hk' : k ≤ d.factorization p := by
      exact (hp.pow_dvd_iff_le_factorization hd).1 hqd
    have hfac : d.factorization p ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le hk hk')
    have hrd : r ∣ d := by
      dsimp [r]
      simpa using (Nat.ordProj_dvd d p)
    have hqr : p ^ k ∣ r := by
      dsimp [r]
      exact pow_dvd_pow _ hk'
    have hrcond : IsPrimePow r ∧ Nat.Coprime r (d / r) := by
      dsimp [r]
      refine ⟨hp.isPrimePow.pow hfac, ?_⟩
      exact (factorization_eq_iff (n := d) hp hfac).2 rfl |>.2
    exact dvd_trans hqr (h r hrd hrcond)

theorem rec_sum_le_card_div {A : Finset ℕ} {M : ℝ} (hM : 0 < M) (h : ∀ n ∈ A, M ≤ (n : ℝ)) :
    (rec_sum A : ℝ) ≤ A.card / M := by
  have hsum : (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := by
    simp [rec_sum]
  calc
    (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := hsum
    _ ≤ A.card * (1 / M) := sum_le_card_mul_real fun n hn => by
      exact one_div_le_one_div_of_le hM (h n hn)
    _ = A.card / M := by simp [div_eq_mul_inv]

theorem divisor_function_eq_card_divisors {n : ℕ} :
    ArithmeticFunction.sigma 0 n = n.divisors.card := by
  simp [ArithmeticFunction.sigma_zero_apply]

theorem tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℕ => Real.log x ^ c) atTop atTop := by
  exact (tendsto_rpow_atTop hc).comp tendsto_log_coe_at_top

theorem one_lt_four : (1 : ℝ) < 4 := by norm_num

/-!
Compatibility declarations from the remainder of `src/aux_lemmas.lean`.

Theorems already available directly from Mathlib, such as `sum_pow`, `sum_pow'`, and
`sum_add_sum`, are not duplicated here.
-/

theorem prime_counting_lower_bound_explicit :
    ∀ᶠ N : ℕ in atTop, ⌊Real.sqrt (N : ℝ)⌋₊ ≤ ((Icc 1 N).filter Nat.Prime).card := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  obtain ⟨c, hc₀, hcheb⟩ := chebyshev_first_all
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((1 / c) ^ (4 : ℝ)))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlarge hlogN h2N hcN hloglogN
  have hlogN' : 0 < Real.log N := by simpa [Function.comp] using hlogN
  have hloglogN' : 0 < Real.log (Real.log N) := by simpa [Function.comp] using hloglogN
  have h0N : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_two h2N
  have hcheb' : c * (N : ℝ) ≤ chebyshev_first N := by
    have := hcheb (N : ℝ) h2N
    rw [Real.norm_of_nonneg (show 0 ≤ (N : ℝ) by positivity),
      Real.norm_of_nonneg (chebyshev_first_nonneg (N : ℝ))] at this
    simpa using this
  have htriv : chebyshev_first N ≤ (π N : ℝ) * Real.log N := by
    simpa using (chebyshev_first_trivial_bound (N : ℝ))
  rw [← prime_counting_eq_card_primes]
  refine Nat.floor_le_of_le ?_
  refine le_of_mul_le_mul_right ?_ hlogN'
  refine le_trans ?_ <| le_trans hcheb' htriv
  refine (Real.log_le_log_iff (mul_pos (Real.sqrt_pos.2 h0N) hlogN')
    (mul_pos hc₀ h0N)).mp ?_
  rw [Real.log_mul (Real.sqrt_pos.2 h0N).ne' hlogN'.ne', Real.sqrt_eq_rpow,
    Real.log_rpow h0N, Real.log_mul hc₀.ne' (show (N : ℝ) ≠ 0 by positivity)]
  have hlargeAbs : |Real.log (Real.log N)| ≤ (1 / 4 : ℝ) * |Real.log N| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge
  have hlarge' : Real.log (Real.log N) ≤ (1 / 4 : ℝ) * Real.log N := by
    rw [abs_of_pos hloglogN', abs_of_pos hlogN'] at hlargeAbs
    exact hlargeAbs
  have hcN' : Real.log (1 / c) ≤ (1 / 4 : ℝ) * Real.log N := by
    have hlog := Real.log_le_log (show 0 < (1 / c) ^ (4 : ℝ) by positivity) hcN
    rw [Real.log_rpow (one_div_pos.mpr hc₀)] at hlog
    nlinarith
  have hc' : Real.log c = -Real.log (1 / c) := by
    have hcinv : Real.log (1 / c) = -Real.log c := by
      rw [one_div]
      exact Real.log_inv c
    linarith
  rw [hc']
  have hleft : (1 / 2 : ℝ) * Real.log N + Real.log (Real.log N) ≤ (3 / 4 : ℝ) * Real.log N := by
    linarith
  have hright : (3 / 4 : ℝ) * Real.log N ≤ -Real.log (1 / c) + Real.log N := by
    linarith
  exact le_trans hleft hright

theorem something_like_this {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (A B : Finset ι)
    (hA : A.card = B.card) :
    (∑ g : B ≃ A, ∏ j : B, f (g j)) = B.card.factorial * A.prod f := by
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
    let e : B ≃ A := Fintype.equivOfCardEq (by simpa using hA.symm)
    simpa [e] using Fintype.card_equiv e
  · intro g _
    rw [← Finset.prod_coe_sort A]
    exact Fintype.prod_equiv g _ _ (fun x ↦ rfl)

theorem my_function_aux {n : ℕ} :
    (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  change Multiset.count x (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) :
    Multiset ℕ) ≤ 1
  rw [Finsupp.sum, Multiset.count_sum']
  simp only [Multiset.count_singleton]
  rw [← Finset.card_filter]
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter] at ha hb
  have hpa : Nat.Prime a := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using ha.1
  have hpb : Nat.Prime b := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using hb.1
  apply eq_of_prime_pow_eq (Nat.prime_iff.mp hpa) (Nat.prime_iff.mp hpb)
  · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha.1)
  · exact ha.2.symm.trans hb.2

def my_function (n : ℕ) : Finset ℕ :=
  ((((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).toFinset)

theorem card_my_function {n : ℕ} : (my_function n).card = ω n := by
  calc
    (my_function n).card =
        (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).card := by
          exact Multiset.toFinset_card_of_nodup my_function_aux
    _ = n.factorization.support.card := by
      rw [Finsupp.sum, Multiset.card_sum]
      simp
    _ = n.primeFactors.card := by rw [Nat.support_factorization]
    _ = ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      symm
      simpa using
        (Multiset.card_toFinset (m := (n.primeFactorsList : Multiset ℕ)))

theorem prod_my_function {n : ℕ} (hn : n ≠ 0) :
    (my_function n).prod id = n := by
  rw [← Finset.prod_val, my_function, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr my_function_aux,
    Finsupp.sum, Multiset.prod_sum]
  simp only [Multiset.prod_singleton]
  exact Nat.prod_factorization_pow_eq_self hn

theorem my_function_injective {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    my_function n = my_function m → n = m := by
  intro h
  rw [← prod_my_function hn, h, prod_my_function hm]

theorem rec_sum_le_prod_sum_aux {A : Finset ℕ} (t : ℕ) (hA : 0 ∉ A) :
    (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) ≤
      ((ppowers_in_set A).powersetCard t).sum fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n) := by
  have hsubset :
      (A.filter fun n : ℕ ↦ ω n = t).image my_function ⊆ (ppowers_in_set A).powersetCard t := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨n, hn, rfl⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro m hm
      simp only [my_function, Multiset.mem_toFinset, Finsupp.sum, Multiset.mem_sum,
        Multiset.mem_singleton] at hm
      rcases hm with ⟨a, ha, rfl⟩
      rw [mem_ppowers_in_set']
      · exact ⟨n, (Finset.mem_filter.mp hn).1, rfl⟩
      · exact Nat.prime_of_mem_primeFactors <| by simpa [Nat.support_factorization] using ha
      · exact Finsupp.mem_support_iff.mp ha
    · exact (card_my_function (n := n)).trans ((Finset.mem_filter.mp hn).2)
  have himage :
      (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) =
        ((A.filter fun n : ℕ ↦ ω n = t).image my_function).sum
          (fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n)) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro x hx
      simp only [one_div]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
      exact (congrArg (fun z : ℕ => ((z : ℝ) : ℝ)⁻¹)
        (prod_my_function (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA))).symm
    · intro x hx y hy hxy
      exact my_function_injective (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA)
        (ne_of_mem_of_not_mem (Finset.mem_filter.mp hy).1 hA) hxy
  rw [himage]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro i _ _
  refine Finset.prod_nonneg ?_
  intro j _
  rw [one_div]
  exact inv_nonneg.mpr (by positivity : 0 ≤ (j : ℝ))

theorem rec_sum_le_prod_sum {A : Finset ℕ} (hA₀ : 0 ∉ A) {I : Finset ℕ}
    (hI : ∀ n ∈ A, ω n ∈ I) :
    (rec_sum A : ℝ) ≤
      I.sum (fun t ↦ ((ppowers_in_set A).sum fun q ↦ (1 / q : ℝ)) ^ t / Nat.factorial t) := by
  classical
  let w : ℕ → ℝ := fun q ↦ (1 : ℝ) / q
  have hpowcard :
      ∀ s : Finset ℕ, ∀ t : ℕ,
        (s.powersetCard t).sum (fun x ↦ x.prod w) ≤ (s.sum w) ^ t / Nat.factorial t := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro t
      cases t with
      | zero =>
          simp [w, Finset.powersetCard_zero]
      | succ t =>
          rw [Finset.powersetCard_eq_empty.mpr (Nat.succ_pos t)]
          simp [w]
    · intro a s ha hs t
      cases t with
      | zero =>
          simp [w, ha, Finset.powersetCard_zero]
      | succ t =>
          have hdisj :
              Disjoint (s.powersetCard t.succ) ((s.powersetCard t).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx2 with ⟨y, hy, rfl⟩
            have hxsub : insert a y ⊆ s := (Finset.mem_powersetCard.mp hx1).1
            exact ha (hxsub (by simp))
          have hy_not : ∀ y ∈ s.powersetCard t, a ∉ y := by
            intro y hy hay
            exact ha ((Finset.mem_powersetCard.mp hy).1 hay)
          rw [Finset.powersetCard_succ_insert ha t, Finset.sum_union hdisj, Finset.sum_image]
          swap
          · intro y hy z hz h
            apply Finset.ext
            intro b
            by_cases hb : b = a
            · subst hb
              simp [hy_not y hy, hy_not z hz]
            · have hmem := congrArg (fun s : Finset ℕ => b ∈ s) h
              simpa [hb] using hmem
          have hins :
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                w a * ∑ y ∈ s.powersetCard t, y.prod w := by
            calc
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                  ∑ y ∈ s.powersetCard t, w a * y.prod w := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.prod_insert (hy_not y hy)]
              _ = w a * ∑ y ∈ s.powersetCard t, y.prod w := by
                    rw [← Finset.mul_sum]
          have hwa_nonneg : 0 ≤ w a := by
            dsimp [w]
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le a
          have hs_nonneg : 0 ≤ s.sum w := by
            refine Finset.sum_nonneg ?_
            intro i hi
            dsimp [w]
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le i
          rw [hins]
          have hmain :
              (s.powersetCard t.succ).sum (fun x ↦ x.prod w) +
                  w a * ∑ x ∈ s.powersetCard t, x.prod w ≤
                (s.sum w) ^ t.succ / Nat.factorial t.succ +
                  w a * ((s.sum w) ^ t / Nat.factorial t) := by
            exact add_le_add (hs t.succ) (mul_le_mul_of_nonneg_left (hs t) hwa_nonneg)
          refine le_trans hmain ?_
          have hbinom :
              (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t ≤
                (s.sum w + w a) ^ t.succ := by
            by_cases hsum : s.sum w = 0
            · rw [hsum]
              cases t with
              | zero => simp
              | succ t => simp [hwa_nonneg]
            · have hsum0 : 0 < s.sum w := lt_of_le_of_ne hs_nonneg (by simpa [eq_comm] using hsum)
              have hratio :
                  -2 ≤ w a / s.sum w := by
                have hratio0 : 0 ≤ w a / s.sum w := div_nonneg hwa_nonneg hs_nonneg
                linarith
              have hpow :
                  (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) ≤
                    (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := by
                exact
                  mul_le_mul_of_nonneg_left (one_add_mul_le_pow hratio t.succ)
                    (pow_nonneg hs_nonneg _)
              calc
                (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t =
                    (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) := by
                      rw [pow_succ']
                      field_simp [hsum]
                _ ≤ (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := hpow
                _ = (s.sum w * (1 + w a / s.sum w)) ^ t.succ := by rw [mul_pow]
                _ = (s.sum w + w a) ^ t.succ := by
                  congr 1
                  field_simp [hsum]
          have hfact :
              (s.sum w) ^ t.succ / Nat.factorial t.succ + w a * ((s.sum w) ^ t / Nat.factorial t) =
                ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) /
                  Nat.factorial t.succ := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp [show (Nat.factorial t : ℝ) ≠ 0 by positivity]
          rw [hfact]
          have hdiv :
              ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) / Nat.factorial t.succ ≤
                (s.sum w + w a) ^ t.succ / Nat.factorial t.succ :=
            div_le_div_of_nonneg_right hbinom (by positivity)
          refine hdiv.trans_eq ?_
          simp [Finset.sum_insert, ha, w, add_comm]
  rw [rec_sum]
  push_cast
  have hA : I.biUnion (fun t ↦ A.filter fun n : ℕ ↦ ω n = t) = A := by
    simpa using
      (Finset.biUnion_filter_eq_of_maps_to (s := A) (t := I) (f := fun n : ℕ ↦ ω n) hI)
  nth_rewrite 1 [← hA]
  refine le_trans (sum_bUnion_le_sum_of_nonneg ?_) ?_
  · intro n hn
    rw [one_div_nonneg]
    exact_mod_cast Nat.zero_le n
  refine Finset.sum_le_sum ?_
  intro t ht
  refine le_trans (rec_sum_le_prod_sum_aux t hA₀) ?_
  simpa [w] using hpowcard (ppowers_in_set A) t

theorem such_large_N_wow :
    ∀ᶠ N : ℕ in atTop, 2 * log (log (⌈Real.logb 2 N⌉₊ ^ 2)) < (1 / 500 : ℝ) * log (log N) := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 8000 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 / log 2 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (exp (exp (2 * log ((2 : ℕ) : ℝ))) * log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.sqrt 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (1500 * log 2 * 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux ] with
    N h1N h1logN hlogN' hlog2logN hcomplogN hsqrtlogN hloglogN hlarge1
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one h1logN
  have h0loglogN : 0 < log (log N) := by
    refine lt_trans ?_ hloglogN
    refine mul_pos ?_ zero_lt_two
    refine mul_pos ?_ (log_pos one_lt_two)
    norm_num1
  have h2000 : (0 : ℝ) < 1500 := by norm_num1
  have hhelper : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ 2 := by
    refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
    · exact Real.logb_nonneg one_lt_two h1N
    rw [← add_halves (log N ^ 2)]
    refine add_le_add ?_ ?_
    · rw [Real.logb]
      rw [div_eq_mul_inv]
      have htmp : (log 2)⁻¹ ≤ log N / 2 := by
        rw [le_div_iff₀ zero_lt_two]
        simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlogN'
      calc
        log N * (log 2)⁻¹ ≤ log N * (log N / 2) := by gcongr
        _ = log N ^ 2 / 2 := by ring
    · rw [le_div_iff₀, one_mul, ← Real.sqrt_le_left]
      · exact hsqrtlogN
      · exact le_of_lt h0logN
      · exact zero_lt_two
  have hhelper2 : (1 : ℝ) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, one_lt_div (log_pos one_lt_two)]
    · exact hlog2logN
  have hhelper3 : exp (exp (2 * log ↑2)) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, lt_div_iff₀ (log_pos one_lt_two)]
    exact hcomplogN
  have hloglogN' : 1500 * log 2 * 2 < log (log N) := by
    simpa [Function.comp] using hloglogN
  have hhelperR : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ (2 : ℝ) := by
    simpa [Real.rpow_natCast] using hhelper
  have hlogceil :
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log 2 + log (log (log N)) := by
    have hinner :
        log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := by
      refine Real.log_le_log (log_pos hhelper2) ?_
      exact Real.log_le_log (lt_trans zero_lt_one hhelper2) hhelperR
    calc
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := hinner
      _ = log 2 + log (log (log N)) := by
        rw [Real.log_rpow h0logN, Real.log_mul two_ne_zero h0loglogN.ne']
  have hlarge1' : |log (log (log N))| ≤ (1 / 8000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge1
  have hbigconst : (1 : ℝ) < 1500 * log 2 * 2 := by
    nlinarith [Real.log_two_gt_d9]
  have h0logloglogN : 0 < log (log (log N)) := by
    refine Real.log_pos ?_
    exact lt_trans hbigconst hloglogN'
  rw [← Real.rpow_natCast, Real.log_rpow (lt_trans zero_lt_one hhelper2)]
  have hmul :
      log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) =
        log 2 + log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    rw [Real.log_mul two_ne_zero (log_pos hhelper2).ne']
  change 2 * log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N)
  rw [hmul, mul_add]
  have hstep1 :
      2 * log 2 + 2 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) <
        (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    have haux' : 2 * log 2 < log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
      refine (lt_log_iff_exp_lt (log_pos hhelper2)).2 ?_
      refine (lt_log_iff_exp_lt (lt_trans zero_lt_one hhelper2)).2 ?_
      exact hhelper3
    linarith
  have hstep2 :
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N) := by
    have hconst : 3 * log 2 < (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hsmall :
        3 * log (log (log N)) ≤ (1 / 1000 : ℝ) * log (log N) := by
      rw [abs_of_pos h0logloglogN, abs_of_pos h0loglogN] at hlarge1'
      have : log (log (log N)) ≤ (1 / 8000 : ℝ) * log (log N) := hlarge1'
      linarith
    calc
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ))
          = 3 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by ring
      _ ≤ 3 * (log 2 + log (log (log N))) := by gcongr
      _ < (1 / 500 : ℝ) * log (log N) := by linarith
  exact lt_trans hstep1 hstep2

theorem explicit_mertens :
    ∀ᶠ N : ℕ in atTop,
      (((range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤ 2 * log (log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (c : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (b + 1))
    , tendsto_natCast_atTop_atTop.eventually hc.bound ] with N hN₁ hN₂ hN₃
  dsimp at hN₁ hN₂
  have hN₄ : 0 < log N := hc₀.trans_le hN₁
  simp_rw [norm_inv, ← div_eq_mul_inv, ← one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    Nat.floor_natCast]
    at hN₃
  have hdiv : c / log N ≤ 1 := by
    rw [div_le_iff₀ hN₄]
    linarith
  have hmain := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans hdiv))
  convert hmain.trans (show log (log N) + b + 1 ≤ 2 * log (log N) by linarith) using 2
  rw [range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  ext n
  simpa only
    [Finset.mem_filter, and_congr_left_iff, Finset.mem_Icc, zero_le', iff_and_self, true_and]
    using fun h _ => (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h.ne_zero, h.ne_one⟩).le

theorem card_factors_le_log {n : ℕ} : Ω n ≤ ⌊Real.logb 2 n⌋₊ := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hΩ : Ω n = 0
  · rw [hΩ]
    exact Nat.zero_le _
  have h0n : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : 2 ^ Ω n ≤ n := by
    rw [ArithmeticFunction.cardFactors_apply]
    calc
      2 ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
        exact List.pow_card_le_prod _ _ fun p hp =>
          (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn
  exact Nat.le_floor <| (Real.le_logb_iff_rpow_le one_lt_two h0n).2 <| by
    simpa [Real.rpow_natCast] using (show ((2 : ℕ) ^ Ω n : ℝ) ≤ n by exact_mod_cast hpow)

theorem this_condition_here {p : ℕ → Prop} [DecidablePred p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, p a) {N : ℕ} (hN : A.card ≤ ((range N).filter p).card)
    (h : ¬ (range N).filter p ⊆ A) :
    (∃ r < N, r ∉ A ∧ p r ∧ ∃ a ∈ A, r < a) ∨ A ⊂ (range N).filter p := by
  let _ := hN
  have h₁ : (((range N).filter p) \ A).Nonempty := by
    rwa [Finset.sdiff_nonempty]
  rw [or_iff_not_imp_right]
  intro h₂
  have h₂ : (A \ ((range N).filter p)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h'
    exact h₂ ⟨h', h⟩
  obtain ⟨r, hr⟩ := h₁
  obtain ⟨a, ha⟩ := h₂
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hr
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and', not_lt] at ha
  exact ⟨r, hr.1.1, hr.2, hr.1.2, a, ha.1, hr.1.1.trans_le (ha.2 (hA _ ha.1))⟩

theorem prime_power_recip_downward_bound (A : Finset ℕ) (ha : ∀ q ∈ A, IsPrimePow q)
    (N : ℕ) (hN : A.card ≤ ((range N).filter IsPrimePow).card) :
    A.sum (fun q ↦ (1 : ℝ) / q) ≤ ((range N).filter IsPrimePow).sum (fun q ↦ (1 : ℝ) / q) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.sum_empty]
    refine Finset.sum_nonneg ?_
    simp
  let a := A.max' hA
  let choices : Finset (Finset ℕ) :=
    (((range (a + 1)).filter IsPrimePow).powerset.filter fun B =>
      B.card ≤ ((range N).filter IsPrimePow).card)
  have hAc : A ∈ choices := by
    simp only [choices, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range,
      Nat.lt_add_one_iff]
    exact ⟨fun b hb ↦ ⟨Finset.le_max' _ _ hb, ha _ hb⟩, hN⟩
  by_cases haN : a < N
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun a' ha' => ?_) ?_
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(Finset.le_max' _ _ ha').trans_lt haN, ha _ ha'⟩
    · simp
  have haN : N ≤ a := Nat.le_of_not_gt haN
  have hchoices : choices.Nonempty := ⟨A, hAc⟩
  obtain ⟨B, hB, hB'⟩ := Finset.exists_max_image choices
    (fun B ↦ B.sum fun q ↦ (1 : ℝ) / q) hchoices
  simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hB
  suffices hEq : (range N).filter IsPrimePow = B by
    rw [hEq]
    exact hB' _ hAc
  suffices hsub : (range N).filter IsPrimePow ⊆ B by
    exact Finset.eq_of_subset_of_card_le hsub hB.2
  by_contra h
  have hBpp : ∀ a : ℕ, a ∈ B → IsPrimePow a := by
    intro x hx
    exact (Finset.mem_filter.mp (hB.1 hx)).2
  rcases this_condition_here hBpp hB.2 h with
    ⟨r, hr, hr', hr'', a', ha', hra'⟩ | hssub
  · have hr''' : r ∉ B.erase a' := fun hrB ↦ hr' (Finset.erase_subset _ _ hrB)
    let B' := (B.erase a').cons r hr'''
    have hra : r ≤ a := hra'.le.trans <| by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (hB.1 ha')).1)
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change (B.erase a').cons r hr''' ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
          exact ⟨hra, hr''⟩
        · exact (Finset.erase_subset _ _).trans hB.1
      · change ((B.erase a').cons r hr''').card ≤ ((range N).filter IsPrimePow).card
        have hcard :
            ((B.erase a').cons r hr''').card = B.card := by
          rw [Finset.card_cons, Finset.card_erase_of_mem ha',
            Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a', ha'⟩)]
        exact hcard.symm ▸ hB.2
    have hmax := hB' B' hB''
    rw [Finset.sum_cons, ← Finset.add_sum_erase _ _ ha', add_le_add_iff_right] at hmax
    exact (not_le_of_gt hra') <| Nat.cast_le.mp <|
      le_of_one_div_le_one_div (by exact_mod_cast hr''.pos) hmax
  · obtain ⟨b, hb, hb'⟩ := Finset.ssubset_iff_exists_cons_subset.mp hssub
    let B' := B.cons b hb
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change B.cons b hb ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · have hbmem := hb' (Finset.mem_cons_self b B)
          rw [Finset.mem_filter, Finset.mem_range] at hbmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hbmem.1.le.trans haN, hbmem.2⟩
        · intro x hx
          have hxmem := hb' (Finset.mem_cons_of_mem hx)
          rw [Finset.mem_filter, Finset.mem_range] at hxmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hxmem.1.le.trans haN, hxmem.2⟩
      · change (B.cons b hb).card ≤ ((range N).filter IsPrimePow).card
        exact Finset.card_le_card hb'
    have hmax := hB' _ hB''
    rw [Finset.sum_cons, add_le_iff_nonpos_left, one_div_nonpos, ← Nat.cast_zero, Nat.cast_le,
      le_zero_iff] at hmax
    have hbmem : b ∈ (range N).filter IsPrimePow := hb' (Finset.mem_cons_self b B)
    exact (Finset.mem_filter.mp hbmem).2.pos.ne' hmax

theorem Omega_eq_card_prime_pow_divisors {n : ℕ} (hn : n ≠ 0) :
    Ω n = (n.divisors.filter IsPrimePow).card := by
  revert hn
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp hk hpk
    rw [Nat.divisors_prime_pow hp, ArithmeticFunction.cardFactors_apply_prime_pow hp]
    have hfilter :
        (Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩
          (Finset.range (k + 1))).filter IsPrimePow =
          Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Finset.Ico 1 (k + 1)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hx, hxpp⟩
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := by
          intro hi0
          exact not_isPrimePow_one (by simpa [hi0] using hxpp)
        refine Finset.mem_map.mpr ⟨i, Finset.mem_Ico.mpr ?_, rfl⟩
        exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0), Finset.mem_range.mp hi⟩
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := by
          exact (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp hi).1).ne'
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2, rfl⟩
        · exact (isPrimePow_pow_iff hi0).2 hp.isPrimePow
    rw [hfilter, Finset.card_map]
    rw [Nat.card_Ico]
    omega
  · simp
  · simp [Finset.filter_singleton, not_isPrimePow_one]
  · intro a b ha hb hab haI hbI hab0
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
      ArithmeticFunction.cardFactors_mul ha0 hb0, haI ha0, hbI hb0,
      Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro d hdA hdB
    have hda : d ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdA).1
    have hdb : d ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdB).1
    have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes hab hda hdb
    exact (not_isPrimePow_one <| hd1 ▸ (Finset.mem_filter.mp hdA).2).elim

theorem rec_pp_sum_close :
    ∀ᶠ N : ℕ in atTop,
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
                (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N) := by
  filter_upwards
    [ eventually_gt_atTop 0
    , such_large_N_wow
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        prime_counting_lower_bound_explicit
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        explicit_mertens ] with N hlarge0 hlarge1 hprimes hmertens x y hxy hxyN
  let m := Int.natAbs (x - y)
  let M := Ω m
  let T := ⌈Real.logb 2 N⌉₊ ^ 2
  have hm : m ≠ 0 := by
    rwa [Int.natAbs_ne_zero, sub_ne_zero]
  have hMT : M ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
    calc
      M ≤ ⌊Real.logb 2 m⌋₊ := card_factors_le_log
      _ ≤ ⌊Real.sqrt T⌋₊ := by
        refine Nat.le_floor ?_
        have hlogm_nonneg : 0 ≤ Real.logb 2 m := by
          exact Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hm)
        refine le_trans (Nat.floor_le hlogm_nonneg) ?_
        calc
          Real.logb 2 m ≤ Real.logb 2 N := by
            rw [nat_cast_diff_issue] at hxyN
            exact Real.logb_le_logb_of_le one_lt_two
              (by exact_mod_cast Nat.pos_of_ne_zero hm) hxyN
          _ ≤ Real.sqrt T := by
            dsimp [T]
            push_cast
            rw [Real.sqrt_sq]
            · exact_mod_cast Nat.le_ceil (Real.logb 2 N)
            · positivity
      _ ≤ ((Finset.Icc 1 T).filter Nat.Prime).card := hprimes
      _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
        exact ⟨hp.1.2, hp.2.isPrimePow⟩
  calc
    ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) ≤
      ((Finset.range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro q hq
            rw [Finset.mem_filter] at hq
            rw [Finset.mem_filter]
            refine ⟨hq.1, hq.2.1, ?_⟩
            exact Int.natCast_dvd_natCast.mp <| by
              simpa [m] using Int.dvd_natAbs.mpr (dvd_sub hq.2.2.1 hq.2.2.2)
          · intro q _ _
            positivity
    _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).sum (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine prime_power_recip_downward_bound _ ?_ _ ?_
          · intro q hq
            exact (Finset.mem_filter.mp hq).2.1
          · have hcard :
                ((Finset.range (N + 1)).filter fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m).card ≤ Ω m := by
              rw [Omega_eq_card_prime_pow_divisors hm]
              refine Finset.card_le_card ?_
              intro x hx
              rcases Finset.mem_filter.mp hx with ⟨_, hxpp, hxdvd⟩
              refine Finset.mem_filter.mpr ?_
              constructor
              · rw [Nat.mem_divisors]
                exact ⟨hxdvd, hm⟩
              · exact hxpp
            exact hcard.trans hMT
    _ < ((1 : ℝ) / 500) * log (log N) := by
          refine lt_of_le_of_lt hmertens ?_
          dsimp [T]
          push_cast
          exact hlarge1

theorem ppowers_count_eq_prime_count {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card =
      (n.divisors.filter Nat.Prime).card := by
  let f : ℕ → ℕ := fun p ↦ p ^ n.factorization p
  have h₁ :
      n.divisors.filter (fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)) =
        (n.divisors.filter Nat.Prime).image f := by
    ext r
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro ha
      have hdivr : r ∣ n := Nat.dvd_of_mem_divisors ha.1
      rcases (isPrimePow_nat_iff r).1 ha.2.1 with ⟨p, k, hp, hk, hpk⟩
      have hdivpk : p ^ k ∣ n := by simpa [hpk] using hdivr
      have hcop : Nat.Coprime (p ^ k) (n / p ^ k) := by simpa [hpk] using ha.2.2
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨dvd_trans (dvd_pow_self _ hk.ne') hdivpk, hn⟩, hp⟩
      · dsimp [f]
        rw [← hpk, (coprime_div_iff hp hdivpk hk.ne' hcop).symm]
    · rintro ⟨p, hp, hpa⟩
      subst r
      rcases Finset.mem_filter.mp hp with ⟨hpDiv, hpPrime⟩
      have hpdvd : p ∣ n := Nat.dvd_of_mem_divisors hpDiv
      have h0fac : 0 < n.factorization p := hpPrime.factorization_pos_of_dvd hn hpdvd
      refine ⟨?_, hpPrime.isPrimePow.pow h0fac.ne', ?_⟩
      · rw [Nat.mem_divisors]
        exact ⟨Nat.ordProj_dvd n p, hn⟩
      · have : n.factorization p = n.factorization p := rfl
        rw [← factorization_eq_iff hpPrime h0fac.ne'] at this
        exact this.2
  rw [h₁]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hps
  rcases Finset.mem_filter.mp hp₁ with ⟨hp₁div, hp₁prime⟩
  rcases Finset.mem_filter.mp hp₂ with ⟨hp₂div, hp₂prime⟩
  exact eq_of_prime_pow_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hp₂prime)
    (hp₁prime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_divisors hp₁div)) hps

theorem omega_count_eq_ppowers {n : ℕ} :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card = ω n := by
  by_cases hn0 : n = 0
  · rw [hn0]
    simp
  · rw [ppowers_count_eq_prime_count hn0]
    have hEq : n.divisors.filter Nat.Prime = n.primeFactors := by
      ext q
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors_of_ne_zero hn0]
      constructor
      · intro h
        exact ⟨h.2, h.1.1⟩
      · intro h
        exact ⟨⟨h.2, hn0⟩, h.1⟩
    rw [hEq, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

theorem exp_pol_lbound (k : ℕ) (x : ℝ) (h : 0 < x) : x ^ k < k.factorial * exp x := by
  let f : ℕ → ℝ := fun i ↦ x ^ i / i.factorial
  have hsum_nonneg : 0 ≤ Finset.sum (Finset.range k) f := by
    exact Finset.sum_nonneg fun _ _ ↦ by
      change 0 ≤ x ^ _ / _
      positivity
  have hsum_eq :
      Finset.sum (Finset.range (k + 2)) f = Finset.sum (Finset.range k) f + f k + f (k + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum :
      f k + f (k + 1) ≤ Finset.sum (Finset.range (k + 2)) f := by
    rw [hsum_eq]
    nlinarith
  have hpos : 0 < f (k + 1) := by
    change 0 < x ^ (k + 1) / (k + 1).factorial
    positivity
  have hlt :
      f k < Finset.sum (Finset.range (k + 2)) f := by
    calc
      f k < f k + f (k + 1) := by
        exact lt_add_of_pos_right (f k) hpos
      _ ≤ Finset.sum (Finset.range (k + 2)) f := hsum
  have hexp : Finset.sum (Finset.range (k + 2)) f ≤ exp x :=
    by simpa [f] using Real.sum_le_exp_of_nonneg (le_of_lt h) (k + 2)
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hdiv : f k < exp x := lt_of_lt_of_le hlt hexp
  simp [f] at hdiv
  simpa [mul_comm] using (div_lt_iff₀ hfac).mp hdiv

theorem factorial_bound (t : ℕ) : ((t : ℝ) * exp (-1)) ^ t ≤ t.factorial := by
  by_cases h0 : t = 0
  · simp [h0]
  · have ht : 0 < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hlt : (t : ℝ) ^ t / exp t < t.factorial := by
      have hmain := exp_pol_lbound t t ht
      have hexp : 0 < exp (t : ℝ) := Real.exp_pos _
      rw [div_lt_iff₀ hexp]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    have hpoweq : ((t : ℝ) * exp (-1)) ^ t = (t : ℝ) ^ t / exp t := by
      calc
        ((t : ℝ) * exp (-1)) ^ t = (t : ℝ) ^ t * (exp (-1)) ^ t := by rw [mul_pow]
        _ = (t : ℝ) ^ t * exp ((t : ℝ) * (-1)) := by
          rw [← Real.exp_nat_mul (-1) t]
        _ = (t : ℝ) ^ t / exp t := by
          rw [show ((t : ℝ) * (-1)) = -(t : ℝ) by ring, Real.exp_neg, div_eq_mul_inv]
    exact le_of_lt (hpoweq ▸ hlt)

theorem helpful_decreasing_bound {x y : ℝ} {n : ℕ} (h0y : 0 < y) (hn : x ≤ n) (hy : y ≤ x) :
    (y / (n * exp (-1))) ^ n ≤ (y / (x * exp (-1))) ^ x := by
  have hx0 : 0 < x := lt_of_lt_of_le h0y hy
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le hx0 hn
  have hnexp : 0 < (n * exp (-1)) := mul_pos hn0 (exp_pos (-1))
  have hxexp : 0 < x * exp (-1) := mul_pos hx0 (exp_pos (-1))
  have hleft : 0 < y / (n * exp (-1)) := div_pos h0y hnexp
  have hright : 0 < y / (x * exp (-1)) := div_pos h0y hxexp
  let f : ℝ → ℝ := fun t ↦ (log y + 1) * t - t * log t
  have hderiv : ∀ t, t ≠ 0 → deriv f t = log y - log t := by
    intro t ht
    have hsub := deriv_fun_sub
      (f := fun s : ℝ ↦ (log y + 1) * s)
      (g := fun s : ℝ ↦ s * log s)
      (x := t)
      ((differentiableAt_const _).mul differentiableAt_id)
      (differentiableAt_id.mul (differentiableAt_log ht))
    have hlin : deriv (fun s : ℝ ↦ (log y + 1) * s) t = log y + 1 := by
      simpa using
        (deriv_const_mul (c := log y + 1) (d := fun s : ℝ ↦ s) (x := t) differentiableAt_id)
    calc
      deriv f t =
          deriv (fun s : ℝ ↦ (log y + 1) * s) t - deriv (fun s : ℝ ↦ s * log s) t := by
        simpa [f] using hsub
      _ = (log y + 1) - (log t + 1) := by rw [hlin, Real.deriv_mul_log ht]
      _ = log y - log t := by ring
  have hcont : ContinuousOn f (Set.Ici y) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · refine ContinuousOn.mul continuous_id.continuousOn ?_
      refine Real.continuousOn_log.mono ?_
      intro z hz
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le h0y hz)
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici y)) := by
    intro z hz
    rw [interior_Ici, Set.mem_Ioi] at hz
    dsimp [f]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ ?_
    · exact (differentiableAt_const _).mul differentiableAt_id
    · exact differentiableAt_id.mul (differentiableAt_log (ne_of_gt (lt_trans h0y hz)))
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici y) hcont hdiff
    (fun z hz ↦ by
      rw [interior_Ici, Set.mem_Ioi] at hz
      rw [hderiv z (ne_of_gt (lt_trans h0y hz)), sub_nonpos]
      exact Real.log_le_log h0y (le_of_lt hz))
  have hxIci : x ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact hy
  have hnIci : (n : ℝ) ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact le_trans hy hn
  specialize hanti hxIci hnIci hn
  have hleft' : (y / (n * exp (-1))) ^ n = Real.exp (f n) := by
    calc
      (y / (n * exp (-1))) ^ n = (Real.exp (Real.log (y / (n * exp (-1))))) ^ n := by
        rw [Real.exp_log hleft]
      _ = Real.exp ((n : ℝ) * Real.log (y / (n * exp (-1)))) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (f n) := by
        congr 1
        change (n : ℝ) * Real.log (y / (n * exp (-1))) = f n
        rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hnexp),
          Real.log_mul (ne_of_gt hn0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
        dsimp [f]
        ring
  have hright' : (y / (x * exp (-1))) ^ x = Real.exp (f x) := by
    rw [Real.rpow_def_of_pos hright]
    congr 1
    change Real.log (y / (x * exp (-1))) * x = f x
    rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hxexp),
      Real.log_mul (ne_of_gt hx0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
    dsimp [f]
    ring
  rw [hleft', hright']
  exact (Real.exp_le_exp).2 hanti

theorem sub_le_omega_div {a b : ℕ} (h : b ∣ a) : (ω a : ℝ) - ω b ≤ ω (a / b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by simpa using h
    simp
  have hnat : ω a ≤ ω b + ω (a / b) := by
    simp only [ArithmeticFunction.cardDistinctFactors_apply]
    obtain ⟨k, rfl⟩ := h
    have hk0 : k ≠ 0 := by
      intro hk0
      simp [hk0] at ha
    have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [Nat.mul_div_cancel_left _ hb, add_comm, ← List.length_append]
    apply List.Subperm.length_le
    refine (List.nodup_dedup _).subperm ?_
    intro x hx
    rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk.ne'] at hx
    simpa [or_comm] using hx
  rw [sub_le_iff_le_add, add_comm]
  exact_mod_cast hnat

theorem omega_div_le {a b : ℕ} (h : b ∣ a) : ω (a / b) ≤ ω a := by
  obtain ⟨k, rfl⟩ := h
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  simp only [ArithmeticFunction.cardDistinctFactors_apply, Nat.mul_div_cancel_left _ hb]
  refine (List.nodup_dedup _).subperm ?_ |>.length_le
  intro t ht
  rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk]
  exact Or.inr (List.mem_dedup.mp ht)

theorem div_bound_useful_version {ε : ℝ} (hε1 : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, n ≤ N ^ 2 → (ArithmeticFunction.sigma 0 n : ℝ) ≤
        N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε)) := by
  let c : ℝ := ε / 2
  have hc : 0 < c := half_pos hε1
  have hhelp0 : 1 ≤ 2 * Real.log 2 * (1 + ε) := by
    have hbase : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    calc
      1 ≤ 2 * Real.log 2 := hbase
      _ ≤ 2 * Real.log 2 * (1 + ε) := by
        have hpos : 0 ≤ 2 * Real.log 2 := le_of_lt (mul_pos zero_lt_two (Real.log_pos one_lt_two))
        nlinarith
  have hhelp : 0 < 2 * Real.log 2 * (1 + ε) := lt_of_lt_of_le zero_lt_one hhelp0
  have hhelp2 : 0 < (1 + ε) / (1 + c) := by
    refine div_pos (add_pos zero_lt_one hε1) (add_pos zero_lt_one hc)
  have hboundc : 0 < (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) := by
    refine div_pos ?_ hhelp2
    rw [sub_pos, one_lt_div]
    · simpa [c] using half_lt_self hε1
    · exact add_pos zero_lt_one hc
  have haux := (isLittleO_log_id_atTop).bound hboundc
  have hdiv := divisor_bound hc
  rw [Filter.eventually_atTop] at hdiv
  rcases hdiv with ⟨M, hdiv⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (M : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.exp 1))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with
    N h1N hN hN' hlarge h0logN h0loglogN h0logloglogN
  intro n hn
  let X : ℝ := N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε))
  have hXhelp : X = N ^ (2 * Real.log 2 * (1 + ε) / log (log (N : ℝ))) := by
    dsimp [X]
    rw [div_eq_mul_inv]
    ring_nf
  have hMX : (M : ℝ) ≤ X := by
    rw [hXhelp]
    exact hN
  have heX : Real.exp 1 ≤ X := by
    rw [hXhelp]
    exact hN'
  have h1X : 1 < X := by
    exact lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) heX
  have hlogX : 0 < log X := Real.log_pos h1X
  by_cases hnbig : (n : ℝ) ≤ X
  · exact (trivial_divisor_bound.trans hnbig)
  rw [not_le] at hnbig
  have hloglogn' : 0 < log (log n) := by
    refine Real.log_pos ?_
    rw [Real.lt_log_iff_exp_lt]
    · exact lt_of_le_of_lt heX hnbig
    · exact lt_trans (lt_trans zero_lt_one h1X) hnbig
  have hloglogn : 0 ≤ log (log n) := le_of_lt hloglogn'
  have hnM : (M : ℝ) ≤ n := le_trans hMX (le_of_lt hnbig)
  refine le_trans (hdiv n ?_) ?_
  · exact_mod_cast hnM
  transitivity ((N : ℝ) ^ 2) ^ (Real.log 2 / log (log ↑n) * (1 + c))
  · refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast hn
    · refine mul_nonneg ?_ ?_
      · exact div_nonneg (Real.log_nonneg one_le_two) hloglogn
      · exact add_nonneg zero_le_one (le_of_lt hc)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast Nat.zero_le N)]
    have hlarge' :
        log (log (log N)) ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * log (log N) := by
      have htmp : |log (log (log N))| ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * |log (log N)| := by
        simpa [Function.comp, Real.norm_eq_abs] using hlarge
      rw [show |log (log (log N))| = log (log (log N)) by exact abs_of_pos h0logloglogN] at htmp
      rw [show |log (log N)| = log (log N) by exact abs_of_pos h0loglogN] at htmp
      exact htmp
    have hcoef :
        (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) = 1 - (1 + c) / (1 + ε) := by
      field_simp [hhelp2.ne']
    have hconst : 0 ≤ log (2 * Real.log 2 * (1 + ε)) := Real.log_nonneg hhelp0
    have hlogXeq :
        log (log X) =
          log (2 * Real.log 2 * (1 + ε)) + log (log N) - log (log (log N)) := by
      rw [hXhelp, Real.log_rpow (lt_of_lt_of_le zero_lt_one h1N)]
      have hcalc :
          2 * Real.log 2 * (1 + ε) / log (log N) * log N =
            (2 * Real.log 2 * (1 + ε) * log N) / log (log N) := by
        ring
      rw [hcalc, Real.log_div, Real.log_mul]
      · exact ne_of_gt hhelp
      · exact ne_of_gt h0logN
      · exact ne_of_gt (mul_pos hhelp h0logN)
      · exact ne_of_gt h0loglogN
    have hXmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log X) := by
      rw [hlogXeq]
      rw [hcoef] at hlarge'
      nlinarith [hconst, hlarge']
    have hXlog : log (log X) ≤ log (log n) := by
      refine Real.log_le_log hlogX ?_
      exact Real.log_le_log (lt_trans zero_lt_one h1X) (le_of_lt hnbig)
    have hmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log n) :=
      le_trans hXmain hXlog
    have hfrac' : (1 + c) / log (log n) ≤ (1 + ε) / log (log N) := by
      have hεpos : 0 < 1 + ε := add_pos zero_lt_one hε1
      have hmain'' :
          ((1 + c) / (1 + ε)) * log (log N) * (1 + ε) ≤ log (log n) * (1 + ε) := by
        exact mul_le_mul_of_nonneg_right hmain (le_of_lt hεpos)
      have hmain' : (1 + c) * log (log N) ≤ (1 + ε) * log (log n) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hεpos.ne'] using hmain''
      exact (div_le_div_iff₀ hloglogn' h0loglogN).2 hmain'
    have hfrac :
        Real.log 2 / log (log ↑n) * (1 + c) ≤
          Real.log 2 / log (log ↑N) * (1 + ε) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hfrac' (le_of_lt (Real.log_pos one_lt_two))
    have hpowbound :
        (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑n) * (1 + c))) ≤
          (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑N) * (1 + ε))) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast h1N
      · exact mul_le_mul_of_nonneg_left hfrac zero_le_two
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpowbound

theorem another_large_N (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      1 / c / 2 ≤ log (log (log N)) ∧
        2 ^ ((100 : ℝ) / 99) ≤ log N ∧
        4 * log (log (log N)) ≤ log (log N) ∧
        log 2 < log (log (log N)) ∧
        log N ^ (-((2 : ℝ) / 99) / 2) ≤
          C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) /
            log N ^ ((2 : ℝ) / ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) ∧
        (1 - 2 / 99) * log (log N) +
            (1 + 5 / log (⌊(log (log N)) / (2 * log (log (log N)))⌋₊) * log (log N)) ≤
          (99 / 100 : ℝ) * log (log N) := by
  let _ := hc
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  have haux2 := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3960000 by norm_num))
  have haux3 := (Real.isLittleO_log_id_atTop.bound <| by
    have hden : 0 < ((Real.exp 10000 + 1) * 2 : ℝ) := by
      positivity
    exact one_div_pos.2 hden)
  have hhelp : 0 < (1 : ℝ) / 10000 := by
    norm_num
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux3
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 : ℝ) ^ ((100 : ℝ) / 99)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (1 / c / 2))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (1000 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((tendsto_rpow_atTop hhelp).comp
          (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((C / 2)⁻¹)) ] with
    N hlarge hlarge2 hlarge3 h0logN h1logN hlogN hlogloglogN' hlogloglogN h0loglogN hloglogN
      h0logloglogN hlargepow
  dsimp at hlargepow
  have h0logN_real : 0 < log N := by
    simpa [Function.comp] using h0logN
  have h1logN_real : 1 ≤ log N := by
    simpa [Function.comp] using h1logN
  have h0loglogN_real : 0 < log (log N) := by
    simpa [Function.comp] using h0loglogN
  have hloglogN_real : (1000 : ℝ) ≤ log (log N) := by
    simpa [Function.comp] using hloglogN
  have h0logloglogN_real : 0 < log (log (log N)) := by
    simpa [Function.comp] using h0logloglogN
  let x : ℝ := (log (log N)) / (2 * log (log (log N)))
  let F : ℝ := ⌊x⌋₊
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (le_of_lt h0loglogN_real)
      (mul_nonneg zero_le_two (le_of_lt h0logloglogN_real))
  have hlarge_abs : |log (log (log N))| ≤ (1 / 4 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge
  have hlarge2_abs : |log (log (log N))| ≤ (1 / 3960000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge2
  have hlarge3_abs :
      |log (log (log N))| ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge3
  have hlarge' : log (log (log N)) ≤ (1 / 4 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge_abs
    exact hlarge_abs
  have hlarge2' : log (log (log N)) ≤ (1 / 3960000 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge2_abs
    exact hlarge2_abs
  have hlarge3' : log (log (log N)) ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge3_abs
    exact hlarge3_abs
  have hx_exp : Real.exp 10000 + 1 ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul : log (log (log N)) * ((Real.exp 10000 + 1) * 2) ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge3'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hhelp2 : Real.exp 10000 ≤ F := by
    change Real.exp 10000 ≤ (⌊x⌋₊ : ℝ)
    rw [natCast_floor_eq_intCast_floor hx_nonneg]
    have hfloor : x - 1 < ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast (Int.sub_one_lt_floor x)
    linarith
  have hF_pos : 0 < F := lt_of_lt_of_le (Real.exp_pos 10000) hhelp2
  have hx_big : (1980000 : ℝ) ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul0 : log (log (log N)) * 3960000 ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge2'
    nlinarith
  have hF_big_nat : 1980000 ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff hx_nonneg]
    exact hx_big
  have hF_big : (1980000 : ℝ) ≤ F := by
    change (1980000 : ℝ) ≤ (⌊x⌋₊ : ℝ)
    exact_mod_cast hF_big_nat
  refine ⟨hlogloglogN', hlogN, ?_, hlogloglogN, ?_, ?_⟩
  · nlinarith
  · change log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ (2 / F)
    have htwo_div_F : 2 / F ≤ 2 / (1980000 : ℝ) := by
      have hone_div : 1 / F ≤ 1 / (1980000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (1980000 : ℝ) by positivity) hF_big
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (2 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hexp : -((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F ≤ -((1 : ℝ) / 10000) := by
      nlinarith
    have hpow_small : log N ^ (-((1 : ℝ) / 10000)) ≤ C / 2 := by
      rw [Real.rpow_neg (le_of_lt h0logN_real)]
      exact (inv_le_comm₀ (Real.rpow_pos_of_pos h0logN_real _) (div_pos hC zero_lt_two)).2 hlargepow
    have hpow_mid : log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) ≤ C / 2 := by
      exact (Real.rpow_le_rpow_of_exponent_le h1logN_real hexp).trans hpow_small
    have hmain : log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
        log N ^ (2 / F) ≤ C := by
      have hmul := mul_le_mul_of_nonneg_left hpow_mid (show 0 ≤ (2 : ℝ) by positivity)
      have hrewrite :
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
            log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
              log N ^ (2 / F) := by
        calc
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
              2 * (log N ^ (-((2 : ℝ) / 99) / 2) *
                (log N ^ ((1 : ℝ) / 100) * log N ^ (2 / F))) := by
                  rw [show (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
                      (-((2 : ℝ) / 99) / 2) + ((1 : ℝ) / 100 + 2 / F) by ring,
                    Real.rpow_add h0logN_real, Real.rpow_add h0logN_real]
          _ = log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
                log N ^ (2 / F) := by ring
      rw [hrewrite] at hmul
      linarith
    refine (_root_.le_div_iff₀ (Real.rpow_pos_of_pos h0logN_real _)).2 ?_
    have hmain' : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) *
        (2 * log N ^ ((1 : ℝ) / 100)) ≤ C := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    have hafter : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) ≤
        C * (2 * log N ^ ((1 : ℝ) / 100))⁻¹ := by
      exact (le_mul_inv_iff₀ (mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN_real _))).2 hmain'
    simpa [one_div] using hafter
  · change (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N)
    have hone : 1 ≤ (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hlogF : (10000 : ℝ) ≤ log F := by
      simpa using Real.log_le_log (Real.exp_pos 10000) hhelp2
    have hdiv : 5 / log F ≤ (5 : ℝ) / 10000 := by
      have hone_div : 1 / log F ≤ 1 / (10000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (10000 : ℝ) by positivity) hlogF
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (5 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
          ((97 : ℝ) / 99) * log (log N) + (1 / 1000) * log (log N) + (5 / 10000) * log (log N) := by
            rw [add_assoc]
            refine add_le_add ?_ ?_
            · norm_num
            · refine add_le_add hone ?_
              exact mul_le_mul_of_nonneg_right hdiv (le_of_lt h0loglogN)
      _ ≤ (99 / 100 : ℝ) * log (log N) := by
        have hcoef : ((97 : ℝ) / 99) + 1 / 1000 + 5 / 10000 ≤ 99 / 100 := by norm_num
        simpa [left_distrib, right_distrib, add_assoc, add_left_comm, add_comm, mul_add] using
          mul_le_mul_of_nonneg_right hcoef (le_of_lt h0loglogN_real)

theorem yet_another_large_N :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) * N ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) <
        log N ^ (-((1 : ℝ) / 101)) / 6 := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (log (6 * 2) / (1 - 1 / 101)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (-log (2 + -(2 * log 2) * (1 + 1 / 3))))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((Real.tendsto_exp_div_pow_atTop 3).comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (1 : ℝ)) ] with
    N h0N hlarge h0logN hloglogN hlogloglogN h0loglogN h0logloglogN hcube
  have hhelp : 0 < 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hlog2 : log 2 < (3 / 4 : ℝ) := by
      exact lt_trans Real.log_two_lt_d9 (by norm_num)
    nlinarith
  rw [_root_.lt_div_iff₀' (show (0 : ℝ) < 6 by norm_num), ← mul_assoc]
  apply (Real.log_lt_log_iff
    (mul_pos (mul_pos (by norm_num : 0 < (6 : ℝ)) zero_lt_two) (Real.rpow_pos_of_pos h0N _))
    (Real.rpow_pos_of_pos h0logN _)).1
  rw [Real.log_rpow h0logN,
    Real.log_mul (by norm_num : (6 : ℝ) * 2 ≠ 0) (Real.rpow_pos_of_pos h0N _).ne', neg_mul,
    lt_neg, neg_add, Real.log_rpow h0N, ← sub_eq_neg_add, lt_sub_iff_add_lt, ← neg_mul, neg_add,
    ← neg_div, neg_neg, ← neg_mul, ← neg_div]
  have hlog12 : log (6 * 2) < (1 - 1 / 101 : ℝ) * log (log N) := by
    have hcoef : 0 < (1 - 1 / 101 : ℝ) := by norm_num
    have := (_root_.div_lt_iff₀ hcoef).1 hloglogN
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hcinv : 1 / log (log N) ≤ 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hrecip : (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ ≤ log (log N) := by
      calc
        (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ = Real.exp (-log (2 + -(2 * log 2) * (1 + 1 / 3))) := by
          rw [Real.exp_neg, Real.exp_log hhelp]
        _ ≤ Real.exp (log (log (log N))) := Real.exp_le_exp.mpr hlogloglogN
        _ = log (log N) := by simpa [Function.comp] using (Real.exp_log h0loglogN)
    have hmul : 1 ≤ (2 + -(2 * log 2) * (1 + 1 / 3)) * log (log N) := by
      have := (inv_le_iff_one_le_mul₀ hhelp).1 hrecip
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have := (_root_.div_le_iff₀ h0loglogN).2 <|
      by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have hcube' : log (log N) < log N / (log (log N)) ^ 2 := by
    have hcube'' : (log (log N)) ^ 3 < log N := by
      have hcube0 : 1 < log N / (log (log N)) ^ 3 := by
        calc
          1 < Real.exp (log (log N)) / (log (log N)) ^ 3 := by simpa [Function.comp] using hcube
          _ = log N / (log (log N)) ^ 3 := by
            simpa [Function.comp] using
              congrArg (fun t => t / (log (log N)) ^ 3) (Real.exp_log h0logN)
      have := (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 3 by positivity)).1 hcube0
      simpa [pow_succ, pow_two, mul_assoc] using this
    refine (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 2 by positivity)).2 ?_
    simpa [pow_succ, pow_two, mul_assoc] using hcube''
  have hcoeff :
      2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3) =
        (2 + -(2 * log 2) * (1 + 1 / 3)) / log (log N) := by
    field_simp [h0loglogN.ne']
  have hrhs :
      log (log N) <
        (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := by
    rw [hcoeff, div_eq_mul_inv, mul_assoc]
    have hmul :
        log N / (log (log N)) ^ 2 ≤
          (2 + -(2 * log 2) * (1 + 1 / 3)) * (log N * (log (log N))⁻¹) := by
      have hrewrite :
          log N / (log (log N)) ^ 2 = (1 / log (log N)) * (log N * (log (log N))⁻¹) := by
        field_simp [h0loglogN.ne']
      rw [hrewrite]
      have htmp := mul_le_mul_of_nonneg_right hcinv (by positivity : 0 ≤ log N * (log (log N))⁻¹)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
    exact lt_of_lt_of_le hcube' <|
      by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) + log (6 * 2) <
        (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) +
          (1 - 1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) := by
      simpa [Function.comp] using add_lt_add_left hlog12 ((1 / 101 : ℝ) * log ((log ∘ Nat.cast) N))
    _ = log (log N) := by
      simp [Function.comp]
      ring
    _ < (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := hrhs

theorem yet_another_large_N' :
    ∀ᶠ N : ℕ in atTop,
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6 := by
  have haux :
      Asymptotics.IsLittleO atTop (fun x : ℝ ↦ log x) (fun x ↦ x ^ (1 / 10100 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10100)
  have hbound := haux.bound (show 0 < (1000 : ℝ) / 6012 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hbound
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (12 ^ ((101 : ℝ) / 100)))
    ] with N hsmall h0logN hlogN
  rw [← add_halves (log N ^ (-(1 / 101 : ℝ)) / 6)]
  refine add_le_add ?_ ?_
  · have hpow : (12 : ℝ) ≤ log N ^ (100 / 101 : ℝ) := by
      have h :=
        Real.rpow_le_rpow
          (show 0 ≤ (12 : ℝ) ^ ((101 : ℝ) / 100) by positivity)
          hlogN
          (by norm_num : 0 ≤ (100 : ℝ) / 101)
      calc
        (12 : ℝ) = ((12 : ℝ) ^ ((101 : ℝ) / 100)) ^ ((100 : ℝ) / 101) := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (12 : ℝ))]
          norm_num
        _ ≤ log N ^ (100 / 101 : ℝ) := h
    have hmain : 12 * (1 / log N) ≤ log N ^ (-(1 / 101 : ℝ)) := by
      calc
        12 * (1 / log N) ≤ log N ^ (100 / 101 : ℝ) * (1 / log N) := by
          gcongr
        _ = log N ^ (-(1 / 101 : ℝ)) := by
          have hInv : (1 / log N) = log N ^ (-1 : ℝ) := by
            calc
              1 / log N = (log N)⁻¹ := by ring
              _ = log N ^ (-1 : ℝ) := by
                have htmp : log N ^ (-(1 : ℝ)) = (log N ^ (1 : ℝ))⁻¹ :=
                  Real.rpow_neg h0logN.le (1 : ℝ)
                simpa [Real.rpow_one] using htmp.symm
          rw [hInv]
          have hrpow0 :
              log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) =
                log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) := by
            simpa [Function.comp] using
              (Real.rpow_add h0logN (100 / 101 : ℝ) (-1 : ℝ)).symm
          calc
            log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) = log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) :=
              hrpow0
            _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
    have h12 : (0 : ℝ) < 12 := by norm_num
    nlinarith
  · have hsmall' :
        log (log N) ≤ (1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)) := by
      have hnonnegLogLog : 0 ≤ log (log N) := by
        apply Real.log_nonneg
        have h12 : (1 : ℝ) ≤ 12 ^ ((101 : ℝ) / 100) := by
          have hbase : (1 : ℝ) ≤ 12 := by norm_num
          simpa using
            (Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ)) hbase
              (by norm_num : 0 ≤ ((101 : ℝ) / 100)))
        exact h12.trans hlogN
      have hnonnegPow : 0 ≤ log N ^ (1 / 10100 : ℝ) := by
        positivity
      have habs :
          |log (log N)| ≤ (1000 / 6012 : ℝ) * |log N ^ (1 / 10100 : ℝ)| := by
        simpa using hsmall
      rw [abs_of_nonneg hnonnegLogLog, abs_of_nonneg hnonnegPow] at habs
      exact habs
    calc
      (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N))
          = ((501 / 1000 : ℝ) * log (log N)) * (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              field_simp
              ring
      _ ≤ ((501 / 1000 : ℝ) * ((1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)))) *
            (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              gcongr
      _ = (1 / 12 : ℝ) * (log N ^ (1 / 10100 : ℝ) * (log N ^ ((1 : ℝ) / 100))⁻¹) := by
            ring
      _ = (1 / 12 : ℝ) * log N ^ (-(1 / 101 : ℝ)) := by
            have hInv : (log N ^ ((1 : ℝ) / 100))⁻¹ = log N ^ (-(1 / 100 : ℝ)) := by
              have htmp : log N ^ (-(1 / 100 : ℝ)) = (log N ^ ((1 : ℝ) / 100))⁻¹ :=
                Real.rpow_neg h0logN.le ((1 : ℝ) / 100)
              exact htmp.symm
            rw [hInv]
            congr 1
            have hrpow0 :
                log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := by
              simpa [Function.comp] using
                (Real.rpow_add h0logN (1 / 10100 : ℝ) (-(1 / 100 : ℝ))).symm
            calc
              log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := hrpow0
              _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
      _ = log N ^ (-(1 / 101 : ℝ)) / 12 := by ring
      _ = log N ^ (-(1 / 101 : ℝ)) / 6 / 2 := by ring

theorem and_another_large_N (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, 2 * log (log N) + 1 ≤ (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) := by
  let c : ℝ := (1 - ε) * log (1 + ε ^ 2)
  have hbase : 1 < 1 + ε ^ 2 := by
    rw [lt_add_iff_pos_right]
    exact sq_pos_of_pos h1
  have hεlt1 : ε < 1 := lt_trans h2 one_half_lt_one
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (sub_pos.mpr hεlt1) (Real.log_pos hbase)
  have haux := (isLittleO_log_rpow_atTop hc).bound (show 0 < (1 : ℝ) / 4 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , (tendsto_coe_log_pow_at_top c hc).eventually (eventually_ge_atTop (2 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N hlogN hpow hsmall
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one hlogN
  have h0loglogN : 0 < log (log N) := Real.log_pos hlogN
  have hsmall' : log (log N) ≤ (1 / 4 : ℝ) * (log N ^ c) := by
    have habs : |log (log N)| ≤ (1 / 4 : ℝ) * |log N ^ c| := by
      simpa [Function.comp, Real.norm_eq_abs] using hsmall
    rw [abs_of_pos h0loglogN, abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos h0logN _))] at habs
    exact habs
  have hconst : 1 ≤ (1 / 2 : ℝ) * (log N ^ c) := by
    have : (2 : ℝ) ≤ log N ^ c := hpow
    nlinarith
  have hmain : 2 * log (log N) + 1 ≤ log N ^ c := by
    have hlogpart : 2 * log (log N) ≤ (1 / 2 : ℝ) * (log N ^ c) := by
      nlinarith
    linarith
  have hrpow :
      (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) = log N ^ c := by
    rw [Real.rpow_def_of_pos (show 0 < 1 + ε ^ 2 by positivity), Real.rpow_def_of_pos h0logN]
    dsimp [c]
    ring_nf
  simpa [hrpow] using hmain

theorem prime_pow_not_coprime_prime_pow {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    ¬ Nat.Coprime a b →
      ∃ p k l : ℕ, Nat.Prime p ∧ (k ≠ 0 ∧ l ≠ 0) ∧ p ^ k = a ∧ p ^ l = b := by
  intro hab
  rcases (isPrimePow_nat_iff a).1 ha with ⟨q, k, hq, hk, hqa⟩
  rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
  refine ⟨q, k, l, hq, ⟨hk.ne', hl.ne'⟩, hqa, ?_⟩
  rw [← hrb]
  by_contra hqr
  apply hab
  rw [← hqa, ← hrb]
  refine Nat.coprime_pow_primes k l hq hr ?_
  intro hEq
  apply hqr
  simp [hEq]

theorem omega_mul_ppower {a q : ℕ} (hq : IsPrimePow q) : ω (q * a) ≤ 1 + ω a := by
  have hωq_nat : ω q = 1 := by
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    simpa using ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk.ne'
  have hωq : (ω q : ℝ) = 1 := by exact_mod_cast hωq_nat
  have hdivω : (ω ((q * a) / q) : ℝ) = ω a := by
    rw [Nat.mul_div_cancel_left _ hq.pos]
  have hsub : (ω (q * a) : ℝ) - ω q ≤ ω ((q * a) / q) := sub_le_omega_div (dvd_mul_right q a)
  have hreal : (ω (q * a) : ℝ) ≤ 1 + ω a := by
    calc
    (ω (q * a) : ℝ) ≤ ω q + ω ((q * a) / q) := by linarith
    _ = 1 + ω a := by rw [hωq, hdivω]
  exact_mod_cast hreal

theorem prime_dvd_prime_pow_then {a p : ℕ} (ha : IsPrimePow a) (hp : Nat.Prime p) (hpa : p ∣ a) :
    ∃ k : ℕ, k ≠ 0 ∧ p ^ k = a := by
  rcases (isPrimePow_nat_iff a).1 ha with ⟨r, k, hr, hk, hkr⟩
  refine ⟨k, hk.ne', ?_⟩
  rw [← hkr] at hpa
  have hpr : p ∣ r := hp.dvd_of_dvd_pow hpa
  have hEq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
  rw [hEq]
  exact hkr

theorem prime_pow_not_coprime_prod_iff {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD : ∀ d ∈ D, IsPrimePow d) :
    ¬ Nat.Coprime a (D.prod id) ↔
      ∃ p ka kd d : ℕ,
        d ∈ D ∧ Nat.Prime p ∧ ka ≠ 0 ∧ kd ≠ 0 ∧ p ^ ka = a ∧ p ^ kd = d := by
  constructor
  · intro h
    rw [Nat.Prime.not_coprime_iff_dvd] at h
    rcases h with ⟨p, hp, hpa, hpD⟩
    have hp' : Prime p := Nat.prime_iff.mp hp
    have hpD' : p ∣ D.toList.prod := by
      simpa using hpD
    rcases (Prime.dvd_prod_iff hp').mp hpD' with ⟨d, hdL, hd2⟩
    have hdD : d ∈ D := by simpa using hdL
    rcases prime_dvd_prime_pow_then ha hp hpa with ⟨ka, hka, hpka⟩
    rcases prime_dvd_prime_pow_then (hD d hdD) hp hd2 with ⟨kd, hkd, hpkd⟩
    exact ⟨p, ka, kd, d, hdD, hp, hka, hkd, hpka, hpkd⟩
  · rintro ⟨p, ka, kd, d, hd, hp, hka, hkd, hpka, hpkd⟩
    rw [Nat.Prime.not_coprime_iff_dvd]
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← hpka]
      exact dvd_pow_self _ hka
    · refine dvd_trans ?_ (Finset.dvd_prod_of_mem id hd)
      rw [← hpkd]
      exact dvd_pow_self _ hkd

theorem prime_pow_prods_coprime {A B : Finset ℕ} (hA : ∀ a ∈ A, IsPrimePow a)
    (hB : ∀ b ∈ B, IsPrimePow b) :
    Nat.Coprime (A.prod id) (B.prod id) ↔ ∀ a ∈ A, ∀ b ∈ B, Nat.Coprime a b := by
  let _ := hA
  let _ := hB
  constructor
  · intro h a ha b hb
    by_contra h'
    rw [Nat.Prime.not_coprime_iff_dvd] at h'
    rcases h' with ⟨r, hr, hra, hrb⟩
    have : ¬ ∃ p, Nat.Prime p ∧ p ∣ A.prod id ∧ p ∣ B.prod id := by
      intro hn
      exact (Nat.Prime.not_coprime_iff_dvd.mpr hn) h
    exact this ⟨r, hr, dvd_trans hra (Finset.dvd_prod_of_mem id ha),
      dvd_trans hrb (Finset.dvd_prod_of_mem id hb)⟩
  · intro h
    rw [Nat.coprime_prod_left_iff]
    intro a ha
    rw [Nat.coprime_prod_right_iff]
    intro b hb
    exact h a ha b hb

theorem weighted_ph {s : Finset ℕ} {f w : ℕ → ℚ} {b : ℚ} (h0b : 0 < b)
    (hw : ∀ a : ℕ, a ∈ s → 0 ≤ w a)
    (hb : b ≤ s.sum (fun x : ℕ ↦ w x * f x)) :
    ∃ (y : ℕ) (_ : y ∈ s), b ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    rw [hs, Finset.sum_empty] at hb
    exact (not_le_of_gt h0b) hb
  by_contra h
  push Not at h
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s f hsne
  have hylt : s.sum (fun x : ℕ ↦ w x) * f y < b := h y hys
  have hsumle : s.sum (fun x : ℕ ↦ w x * f x) ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hy n hn) (hw n hn)
  exact (not_lt_of_ge hb) (lt_of_le_of_lt hsumle hylt)

theorem prime_pow_not_coprime_iff {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    ¬ Nat.Coprime a b ↔
      ∃ p ka kb : ℕ, Nat.Prime p ∧ ka ≠ 0 ∧ kb ≠ 0 ∧ p ^ ka = a ∧ p ^ kb = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff a).1 ha with ⟨p, k, hp, hk, hpa⟩
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    by_cases hpr : p = r
    · refine ⟨p, k, l, hp, hk.ne', hl.ne', hpa, ?_⟩
      simpa [hpr] using hrb
    · exfalso
      apply hab
      rw [← hpa, ← hrb]
      exact Nat.coprime_pow_primes k l hp hr hpr
  · rintro ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    rw [Nat.Prime.not_coprime_iff_dvd]
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← hpa]
      exact dvd_pow_self _ hka
    · rw [← hpb]
      exact dvd_pow_self _ hkb

theorem eq_iff_ppowers_dvd (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔
      (∀ q, q ∣ a → IsPrimePow q → Nat.Coprime q (a / q) → q ∣ b) ∧
        ∀ q, q ∣ b → IsPrimePow q → Nat.Coprime q (b / q) → q ∣ a := by
  constructor
  · intro h
    subst h
    exact ⟨fun _ hq _ _ => hq, fun _ hq _ _ => hq⟩
  · rintro ⟨hab, hba⟩
    apply Nat.dvd_antisymm
    · exact (dvd_iff_ppowers_dvd' a b ha).2 fun q hq hq' => hab q hq hq'.1 hq'.2
    · exact (dvd_iff_ppowers_dvd' b a hb).2 fun q hq hq' => hba q hq hq'.1 hq'.2

theorem is_prime_pow_dvd_prod {n : ℕ} {D : Finset ℕ}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ D.prod id ↔ ∃ d, d ∈ D ∧ n ∣ d := by
  induction D using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Nat.dvd_one]
      constructor
      · intro h
        exact (hn.ne_one h).elim
      · rintro ⟨d, hd, _⟩
        simp at hd
  | @insert q D hqD hDind =>
      constructor
      · intro h
        rw [Finset.prod_insert hqD] at h
        have hnec : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b := by
          intro a ha b hb hab
          exact hD a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
        specialize hDind hnec
        have hcop : Nat.Coprime q (D.prod id) := by
          rw [Nat.coprime_prod_right_iff]
          intro d hd
          exact hD q (Finset.mem_insert_self q D) d (Finset.mem_insert_of_mem hd) <| by
            intro hEq
            exact hqD (hEq ▸ hd)
        rcases (hcop.isPrimePow_dvd_mul hn).mp h with hq | hD'
        · exact ⟨q, Finset.mem_insert_self q D, hq⟩
        · rw [hDind] at hD'
          rcases hD' with ⟨d, hd1, hd2⟩
          exact ⟨d, Finset.mem_insert_of_mem hd1, hd2⟩
      · rintro ⟨d, hd1, hd2⟩
        exact dvd_trans hd2 (Finset.dvd_prod_of_mem id hd1)

theorem prime_pow_dvd_prime_pow {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    a ∣ b ↔ ∃ p k l : ℕ, Nat.Prime p ∧ 0 < k ∧ k ≤ l ∧ p ^ k = a ∧ p ^ l = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    rw [← hrb] at hab
    rw [Nat.dvd_prime_pow hr] at hab
    rcases hab with ⟨k, hkl, h⟩
    refine ⟨r, k, l, hr, ?_, hkl, h.symm, hrb⟩
    refine Nat.pos_iff_ne_zero.mpr ?_
    intro hk
    rw [hk, pow_zero] at h
    exact ha.ne_one h
  · rintro ⟨p, k, l, hp, _hk, hkl, hpa, hpb⟩
    rw [← hpa, ← hpb]
    exact pow_dvd_pow _ hkl

theorem prime_pow_dvd_prod_prime_pow {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD1 : ∀ a₁ ∈ D, ∀ b ∈ D, a₁ ≠ b → Nat.Coprime a₁ b) (hD2 : ∀ d ∈ D, IsPrimePow d) :
    a ∣ D.prod id → Nat.Coprime a (D.prod id / a) → a ∈ D := by
  intro haD hacop
  by_cases hprod0 : D.prod id = 0
  · rw [hprod0, Nat.zero_div, Nat.coprime_zero_right] at hacop
    exact (ha.ne_one hacop).elim
  have haD' := haD
  rw [is_prime_pow_dvd_prod hD1 ha] at haD
  rcases haD with ⟨d, hd1, hd2⟩
  have hEq : a = d := by
    rw [prime_pow_dvd_prime_pow ha (hD2 d hd1)] at hd2
    rcases hd2 with ⟨p, k, l, hp, h0k, hkl, hpa, hpd⟩
    rw [← hpa, ← hpd]
    have hfac1 : k = (D.prod id).factorization p := by
      rw [← hpa] at haD'
      rw [← hpa] at hacop
      exact coprime_div_iff hp haD' (Nat.ne_zero_of_lt h0k) hacop
    have hfac2 : l ≤ (D.prod id).factorization p := by
      rw [← hp.pow_dvd_iff_le_factorization hprod0, hpd]
      exact Finset.dvd_prod_of_mem id hd1
    have hfac3 : k = l := le_antisymm hkl <| by
      rw [hfac1]
      exact hfac2
    rw [hfac3]
  rw [hEq]
  exact hd1

theorem prod_of_subset_le_prod_of_ge_one' {s : Finset ℕ} {f : ℕ → ℝ} :
    ∀ t : Finset ℕ,
      t ⊆ s →
        (∀ i ∈ s, 0 ≤ f i) →
          (∀ i ∈ s, i ∉ t → 1 ≤ f i) →
            t.prod f ≤ s.prod f := by
  induction s using Finset.induction_on with
  | empty =>
      intro t ht hs hf
      rw [Finset.subset_empty.mp ht]
  | @insert n s hns hsind =>
      intro t ht hs hf
      rw [Finset.prod_insert hns]
      by_cases htn : n ∈ t
      · let t' := t.erase n
        have htt' : insert n t' = t := Finset.insert_erase htn
        rw [← htt', Finset.prod_insert (Finset.notMem_erase _ _)]
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · refine hsind t' ?_ ?_ ?_
          · exact (Finset.erase_subset_erase _ ht).trans (Finset.erase_insert_subset _ _)
          · intro a ha
            exact hs a (Finset.mem_insert_of_mem ha)
          · intro a ha1 ha2
            refine hf a (Finset.mem_insert_of_mem ha1) ?_
            intro hat
            apply ha2
            rw [Finset.mem_erase]
            refine ⟨?_, hat⟩
            intro han
            apply hns
            simpa [han] using ha1
        · exact hs n (ht htn)
      · have ht' : t ⊆ s := by
          intro a ha
          rcases Finset.mem_insert.mp (ht ha) with rfl | ha'
          · exact False.elim (htn ha)
          · exact ha'
        refine le_trans (hsind t ht' ?_ ?_) ?_
        · intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
        · intro i hi1 hi2
          exact hf i (Finset.mem_insert_of_mem hi1) hi2
        refine le_mul_of_one_le_left ?_ ?_
        · refine Finset.prod_nonneg ?_
          intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
        · exact hf n (Finset.mem_insert_self n s) htn

theorem prod_of_subset_le_prod_of_ge_one {s t : Finset ℕ} {f : ℕ → ℝ} (h : t ⊆ s)
    (hs : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
    t.prod f ≤ s.prod f := by
  exact prod_of_subset_le_prod_of_ge_one' t h hs hf

theorem sum_le_sum_of_inj' {A : Finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) :
    ∀ B : Finset ℕ,
      (∀ b ∈ B, 0 ≤ f2 b) →
        (∀ a ∈ A, g a ∈ B) →
          (∀ a1 ∈ A, ∀ a2 ∈ A, g a1 = g a2 → a1 = a2) →
            (∀ a ∈ A, f2 (g a) = f1 a) → A.sum f1 ≤ B.sum f2 := by
  induction A using Finset.induction_on with
  | empty =>
      intro B hf2 hgB hginj hgf
      simp only [Finset.sum_empty]
      exact Finset.sum_nonneg hf2
  | @insert n A hnA hA =>
      intro B hf2 hgB hginj hgf
      rw [Finset.sum_insert hnA]
      let B' := B.erase (g n)
      have hBB' : insert (g n) B' = B := Finset.insert_erase (hgB n (Finset.mem_insert_self n A))
      rw [← hBB', Finset.sum_insert (Finset.notMem_erase _ _)]
      refine add_le_add ?_ ?_
      · simp [hgf n (Finset.mem_insert_self n A)]
      · refine hA B' ?_ ?_ ?_ ?_
        · intro b hb
          exact hf2 b (Finset.mem_of_mem_erase hb)
        · intro a ha
          rw [Finset.mem_erase]
          refine ⟨?_, hgB a (Finset.mem_insert_of_mem ha)⟩
          intro hEq
          have han : a = n :=
            hginj a (Finset.mem_insert_of_mem ha) n (Finset.mem_insert_self n A) hEq
          rw [han] at ha
          exact hnA ha
        · intro a1 ha1 a2 ha2 hgai
          exact hginj a1 (Finset.mem_insert_of_mem ha1) a2 (Finset.mem_insert_of_mem ha2) hgai
        · intro a ha
          exact hgf a (Finset.mem_insert_of_mem ha)

theorem sum_le_sum_of_inj {A B : Finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ)
    (hf2 : ∀ b ∈ B, 0 ≤ f2 b) (hgB : ∀ a ∈ A, g a ∈ B)
    (hginj : ∀ a1 ∈ A, ∀ a2 ∈ A, g a1 = g a2 → a1 = a2) (hgf : ∀ a ∈ A, f2 (g a) = f1 a) :
    A.sum f1 ≤ B.sum f2 := by
  exact sum_le_sum_of_inj' g B hf2 hgB hginj hgf

theorem card_bUnion_lt_card_mul_real {s : Finset ℤ} {f : ℤ → Finset ℕ} (m : ℝ)
    (h : ∀ a : ℤ, a ∈ s → ((f a).card : ℝ) < m) :
    s.Nonempty → ((s.biUnion f).card : ℝ) < s.card * m := by
  intro hs
  have hcard : (s.biUnion f).card ≤ Finset.sum s fun a => (f a).card := Finset.card_biUnion_le
  calc
    ((s.biUnion f).card : ℝ) ≤ Finset.sum s (fun a => ((f a).card : ℝ)) := by exact_mod_cast hcard
    _ < Finset.sum s (fun _ => m) := Finset.sum_lt_sum_of_nonempty hs h
    _ = s.card * m := by simp [nsmul_eq_mul]

theorem prod_le_max_size {ι N : Type*} [CommMonoidWithZero N] [Preorder N] [ZeroLEOneClass N]
    [PosMulMono N] {s : Finset ι} {f : ι → N} (hs : ∀ i ∈ s, 0 ≤ f i) (M : N)
    (hf : ∀ i ∈ s, f i ≤ M) : s.prod f ≤ M ^ s.card := by
  calc
    s.prod f ≤ s.prod fun _ => M := Finset.prod_le_prod hs hf
    _ = M ^ s.card := by simp

theorem sum_add_sum_add_sum {A B C : Finset ℕ} {f : ℕ → ℝ} :
    A.sum f + B.sum f + C.sum f =
      (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
  have hAB :
      A.sum f + B.sum f = (A ∪ B).sum f + (A ∩ B).sum f := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)).symm
  have hABC :
      (A ∪ B).sum f + C.sum f = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f := by
    simpa [add_comm, add_left_comm, add_assoc, Finset.union_assoc] using
      (Finset.sum_union_inter (s₁ := A ∪ B) (s₂ := C) (f := f)).symm
  have hInter :
      ((A ∪ B) ∩ C).sum f = (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
    have h' := Finset.sum_union_inter (s₁ := A ∩ C) (s₂ := B ∩ C) (f := f)
    have hUnion : A ∩ C ∪ B ∩ C = (A ∪ B) ∩ C := by
      ext x
      simp [or_and_right]
    rw [hUnion] at h'
    have hEq : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
      ext x
      simp [and_left_comm]
    rw [hEq] at h'
    linarith
  calc
    A.sum f + B.sum f + C.sum f = ((A ∪ B).sum f + (A ∩ B).sum f) + C.sum f := by rw [hAB]
    _ = (A ∪ B).sum f + C.sum f + (A ∩ B).sum f := by ring
    _ = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f + (A ∩ B).sum f := by rw [hABC]
    _ =
        (A ∪ B ∪ C).sum f +
          ((A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f) +
            (A ∩ B).sum f := by rw [hInter]
    _ = (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f -
          (A ∩ B ∩ C).sum f := by ring

theorem rec_sum_le_three {A B C : Finset ℕ} :
    rec_sum (A ∪ B ∪ C) ≤ rec_sum A + rec_sum B + rec_sum C := by
  let B' := B \ A
  let C' := C \ (A ∪ B')
  have hunion : A ∪ B ∪ C ⊆ A ∪ B' ∪ C' := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_union.mp hn with hn | hn
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hn
      · by_cases hna : n ∈ A
        · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hna
        · exact
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hn, hna⟩
    · by_cases hAB : n ∈ A ∪ B'
      · exact Finset.mem_union.mpr <| Or.inl hAB
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hn, hAB⟩
  refine le_trans (rec_sum_mono hunion) ?_
  rw [rec_sum_disjoint, rec_sum_disjoint]
  · refine add_le_add ?_ ?_
    · rw [add_le_add_iff_left]
      change rec_sum (B \ A) ≤ rec_sum B
      exact rec_sum_mono Finset.sdiff_subset
    · change rec_sum (C \ (A ∪ B')) ≤ rec_sum C
      exact rec_sum_mono Finset.sdiff_subset
  · exact Finset.disjoint_sdiff
  · exact Finset.disjoint_sdiff

theorem nat_gcd_prod_le_diff {a b c : ℤ} (hab : a ≠ b) (hac : a ≠ c) :
    Nat.gcd (Int.natAbs a) (Int.natAbs (b * c)) ≤ Int.natAbs (a - b) * Int.natAbs (a - c) := by
  refine Nat.le_of_dvd ?_ ?_
  · rw [Nat.pos_iff_ne_zero]
    intro hz
    rw [mul_eq_zero, Int.natAbs_eq_zero, Int.natAbs_eq_zero, sub_eq_zero, sub_eq_zero] at hz
    rcases hz with hz | hz
    · exact hab hz
    · exact hac hz
  · rw [Int.natAbs_mul]
    refine dvd_trans (gcd_mul_dvd_mul_gcd _ _ _) ?_
    refine mul_dvd_mul ?_ ?_
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)

theorem triv_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    1 - 2 * ε ≤ (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) := by
  let _ := hε2
  have hpos : 0 < 1 + ε ^ 2 := by positivity
  have hpos' : 1 + ε ^ 2 ≠ 0 := ne_of_gt hpos
  rw [div_eq_mul_inv, ← mul_assoc]
  field_simp [hpos']
  nlinarith [sq_nonneg ε, le_of_lt hε1]

theorem help_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    log (1 - ε) * (1 - ε) ≤ -ε / 2 := by
  have h1ε : 0 < 1 - ε := by linarith
  calc
    log (1 - ε) * (1 - ε) ≤ ((1 - ε) - 1) * (1 - ε) := by
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt h1ε)
      simpa using Real.log_le_sub_one_of_pos h1ε
    _ = -ε * (1 - ε) := by ring
    _ ≤ -ε / 2 := by nlinarith

theorem floor_sub_ceil {x y z : ℝ} : (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ x + y := by
  calc
    (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ z + x - ⌈z - y⌉ := by
      gcongr
      exact Int.floor_le (z + x)
    _ ≤ z + x - (z - y) := by
      gcongr
      exact Int.le_ceil (z - y)
    _ = x + y := by ring

theorem useful_identity (i : ℕ) (h : (1 : ℝ) < i) :
    (1 : ℝ) + 1 / (i - 1) = |(1 - (i : ℝ)⁻¹)⁻¹| := by
  have hi0 : (0 : ℝ) < i := lt_trans zero_lt_one h
  have hineq : 0 ≤ (1 - (i : ℝ)⁻¹)⁻¹ := by
    apply inv_nonneg.mpr
    have hrewrite : 1 - (i : ℝ)⁻¹ = ((i : ℝ) - 1) / i := by
      field_simp [show (i : ℝ) ≠ 0 by linarith]
    rw [hrewrite]
    exact div_nonneg (by linarith) (le_of_lt hi0)
  rw [abs_of_nonneg hineq]
  field_simp [show (i : ℝ) ≠ 0 by linarith, show (i : ℝ) - 1 ≠ 0 by linarith]
  ring

theorem useful_exp_estimate : ((35 : ℝ) / 100) ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) := by
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
  nlinarith [Real.exp_one_lt_d9]

theorem rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ,
        log N ^ (-ε / 2) ≤ rec_sum A →
          (∀ n ∈ A, (1 - ε) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
            (1 - 2 * ε) * Real.exp (-1) * log (log N) ≤
              (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ)) := by
  filter_upwards
    [ eventually_ge_atTop (0 : ℕ)
    , and_another_large_N ε hε1 hε2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)) ] with
    N _ hlarge0 hlarge1 hlarge2 A hrecA hreg
  let L : ℝ := log (log N)
  let x : ℝ := (1 - ε) * L
  have hεlt1 : ε < 1 := lt_trans hε2 one_half_lt_one
  have h1ε : 0 < 1 - ε := sub_pos.mpr hεlt1
  have hL : 0 < L := by
    simpa [L] using hlarge1
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos h1ε hL
  have hreg' : ∀ n ∈ A, x ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * L) := by
    intro n hn
    simpa [x, L] using hreg n hn
  have h0A : 0 ∉ A := by
    intro h0
    have h0reg := hreg' 0 h0
    rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
    exact (not_le_of_gt hx) (by simpa using h0reg.1)
  let S : ℝ := (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ))
  have hS : 0 < S := by
    have hAne : A.Nonempty := by
      by_contra hAne
      rw [Finset.not_nonempty_iff_eq_empty] at hAne
      rw [hAne, rec_sum_empty] at hrecA
      have hlogN : 0 < log N := lt_of_lt_of_le zero_lt_one hlarge2
      have hpow : 0 < log N ^ (-ε / 2) := Real.rpow_pos_of_pos hlogN (-ε / 2)
      linarith
    rcases hAne with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      have h0reg := hreg' 0 (ha0 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
      exact (not_le_of_gt hx) (by simpa using h0reg.1)
    have ha1 : a ≠ 1 := by
      intro ha1
      have h1reg := hreg' 1 (ha1 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_one] at h1reg
      exact (not_le_of_gt hx) (by simpa using h1reg.1)
    have ha2 : 2 ≤ a := by omega
    have hpp : (ppowers_in_set A).Nonempty := ppowers_in_set_nonempty ⟨a, ha, ha2⟩
    dsimp [S]
    refine Finset.sum_pos ?_ hpp
    intro q hq
    have hq0 : q ≠ 0 := by
      intro hq0
      rw [hq0] at hq
      exact zero_not_mem_ppowers_in_set hq
    rw [one_div_pos]
    exact_mod_cast Nat.pos_of_ne_zero hq0
  let D : ℝ := Real.exp (-1) * x
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.exp_pos (-1)) hx
  by_cases hdone : x < S
  · have hcoef : (1 - 2 * ε) * Real.exp (-1) ≤ 1 - ε := by
      have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
        exact (le_of_lt Real.exp_neg_one_lt_d9).trans (by norm_num)
      nlinarith
    have hmain := mul_le_mul_of_nonneg_right hcoef (le_of_lt hL)
    simpa [S, x, L, mul_assoc, mul_left_comm, mul_comm] using hmain.trans (le_of_lt hdone)
  · have hSle : S ≤ x := not_lt.mp hdone
    let I : Finset ℕ := (Finset.range (⌊2 * L⌋₊ + 1)).filter (fun n : ℕ ↦ x ≤ n)
    have hrec_upper :
        rec_sum A ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := by
      refine rec_sum_le_prod_sum h0A ?_
      intro n hn
      have hnreg := hreg' n hn
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hnreg.1⟩
      rw [Nat.lt_succ_iff]
      exact Nat.le_floor hnreg.2
    have hsum_upper :
        I.sum (fun t ↦ S ^ t / Nat.factorial t) ≤
          I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      rw [div_pow]
      have hpow_pos : 0 < S ^ t := pow_pos hS t
      have hfac_pos : 0 < (t.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos t
      have hden_pos : 0 < (((t : ℝ) * Real.exp (-1)) ^ t) := by
        cases t with
        | zero =>
            simp
        | succ t =>
            have hbase : 0 < (((Nat.succ t : ℕ) : ℝ) * Real.exp (-1)) := by positivity
            exact pow_pos hbase _
      exact (div_le_div_iff_of_pos_left hpow_pos hfac_pos hden_pos).2 (factorial_bound t)
    have hpointwise :
        ∀ t ∈ I, (S / (t * Real.exp (-1))) ^ t ≤ (S / D) ^ x := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      simpa [D, x, mul_assoc, mul_left_comm, mul_comm] using
        (helpful_decreasing_bound hS ht'.2 hSle)
    have hsum_card :
        I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) ≤ (I.card : ℝ) * (S / D) ^ x := by
      refine sum_le_card_mul_real ?_
      intro t ht
      exact hpointwise t ht
    have hIcard_nat : I.card ≤ (Finset.range (⌊2 * L⌋₊ + 1)).card := by
      simpa [I] using
        (Finset.card_filter_le (s := Finset.range (⌊2 * L⌋₊ + 1)) (p := fun n : ℕ ↦ x ≤ n))
    have hIcard :
        (I.card : ℝ) ≤ (1 + ε ^ 2) ^ x := by
      calc
        (I.card : ℝ) ≤ ((Finset.range (⌊2 * L⌋₊ + 1)).card : ℝ) := by
          exact_mod_cast hIcard_nat
        _ = (⌊2 * L⌋₊ : ℝ) + 1 := by simp
        _ ≤ 2 * L + 1 := by
          have hfloor : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by positivity)
          linarith
        _ ≤ (1 + ε ^ 2) ^ x := by
          simpa [x, L] using hlarge0
    have hrec_bound :
        log N ^ (-ε / 2) ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
      have hpow_nonneg : 0 ≤ (S / D) ^ x := by positivity
      calc
        log N ^ (-ε / 2) ≤ rec_sum A := hrecA
        _ ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := hrec_upper
        _ ≤ I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := hsum_upper
        _ ≤ (I.card : ℝ) * (S / D) ^ x := hsum_card
        _ ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
          exact mul_le_mul_of_nonneg_right hIcard hpow_nonneg
    have hleft :
        (1 - ε) ^ x ≤ log N ^ (-ε / 2) := by
      have hEq : (1 - ε) ^ x = log N ^ (log (1 - ε) * (1 - ε)) := by
        dsimp [x, L]
        nth_rewrite 1 [← Real.exp_log h1ε]
        rw [← Real.exp_mul, ← mul_assoc, mul_comm _ (log (log N)), Real.exp_mul,
          Real.exp_log]
        exact lt_of_lt_of_le zero_lt_one hlarge2
      rw [hEq]
      refine Real.rpow_le_rpow_of_exponent_le hlarge2 ?_
      exact help_ε_estimate ε hε1 hε2
    have hbase_nonneg : 0 ≤ (1 - ε) / (1 + ε ^ 2) := by
      exact div_nonneg (le_of_lt h1ε) (by positivity)
    have hright_nonneg : 0 ≤ S / D := by
      exact div_nonneg (le_of_lt hS) (le_of_lt hD)
    have hbase :
        (1 - ε) / (1 + ε ^ 2) ≤ S / D := by
      rw [← Real.rpow_le_rpow_iff hbase_nonneg hright_nonneg hx]
      have hfac_pos : 0 < (1 + ε ^ 2) ^ x := Real.rpow_pos_of_pos (by positivity) x
      calc
        ((1 - ε) / (1 + ε ^ 2)) ^ x = (1 - ε) ^ x / (1 + ε ^ 2) ^ x := by
          rw [Real.div_rpow (le_of_lt h1ε) (by positivity)]
        _ ≤ log N ^ (-ε / 2) / (1 + ε ^ 2) ^ x := by
          exact (div_le_div_iff_of_pos_right hfac_pos).2 hleft
        _ ≤ (S / D) ^ x := by
          rw [div_le_iff₀ hfac_pos]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hrec_bound
    have hmid : ((1 - ε) / (1 + ε ^ 2)) * D ≤ S := by
      exact (le_div_iff₀ hD).mp hbase
    have htriv :
        (1 - 2 * ε) * Real.exp (-1) * L ≤
          (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L := by
      have hcoef := triv_ε_estimate ε hε1 hε2
      have hEL_nonneg : 0 ≤ Real.exp (-1) * L := by
        exact mul_nonneg (le_of_lt (Real.exp_pos (-1))) (le_of_lt hL)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hEL_nonneg
    have hmid' :
        (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L ≤ S := by
      simpa [D, x, L, mul_assoc, mul_left_comm, mul_comm] using hmid
    simpa [S, L] using htriv.trans hmid'

theorem useful_rec_aux1 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ N k : ℕ,
          1 ≤ k →
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) ≤
              C ^ k := by
  have haux :
      ∃ C : ℝ,
        0 < C ∧
          ∀ N : ℕ,
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + 1 / (p * (p - 1)))) ≤ C := by
    have ht : ∀ n : ℕ,
        log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      intro n
      by_cases h0 : n = 0
      · subst h0
        simp [zero_pow]
      by_cases h1 : n = 1
      · subst h1
        simp
      have h2 : 2 ≤ n := by omega
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_trans zero_lt_one h2)
      have hn1_pos : 0 < (n : ℝ) - 1 := by
        have hn_gt : (1 : ℝ) < n := by
          exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
        linarith
      have hlog :
          log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤
            1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have hpos : 0 < 1 + 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 (mul_pos hn_pos hn1_pos))
        simpa using (Real.log_le_sub_one_of_pos hpos)
      have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast h2
        nlinarith
      have hhalf_pos : 0 < (n : ℝ) / 2 := by positivity
      have hdiv : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
        have h := one_div_le_one_div_of_le hhalf_pos hhalf
        have hEq : 1 / ((n : ℝ) / 2) = 2 / (n : ℝ) := by
          field_simp [hn_pos.ne']
        exact h.trans_eq hEq
      have h_inv :
          1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hdiv (one_div_nonneg.2 hn_pos.le)
        simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact hlog.trans h_inv
    have hsummable :
        Summable (fun n : ℕ => (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact (summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2)).mul_left 2
    refine ⟨Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))), Real.exp_pos _, ?_⟩
    intro N
    let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
    have hs_log :
        log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ≤
          ∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      rw [Real.log_prod]
      · refine le_trans (Finset.sum_le_sum fun i hi ↦ ht i) ?_
        exact hsummable.sum_le_tsum s (fun _ _ ↦ by positivity)
      · intro i hi
        have hip := (Finset.mem_filter.mp hi).2
        have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
          have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
          have hi1_pos : 0 < (i : ℝ) - 1 := by
            have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
            linarith
          exact mul_pos hi_pos hi1_pos
        have hpos : 0 < (1 : ℝ) + 1 / ((i : ℝ) * ((i : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 hden)
        exact hpos.ne'
    have hs_pos : 0 < s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      apply Finset.prod_pos
      intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
    have hexp :
        Real.exp (log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))) ≤
          Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact Real.exp_le_exp.mpr hs_log
    rw [Real.exp_log hs_pos] at hexp
    simpa [s] using hexp
  rcases haux with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro N k hk
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  change s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_lt hip.one_lt)
        linarith
      have hden_nonneg : 0 ≤ (i : ℝ) * ((i : ℝ) - 1) := by
        exact mul_nonneg (by exact_mod_cast Nat.zero_le i) hi1_nonneg
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hden_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden_pos : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)) := by
        exact one_div_nonneg.2 hden_pos.le
      have hstep :=
        one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
  have hN' : s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C := by
    simpa [s] using hN N
  have hpow : (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k ≤ C ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN' k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))
    _ ≤ C ^ k := hpow

theorem useful_rec_aux3 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N : ℕ,
            1 < y →
              y < N →
                ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                    (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) ≤
                  C * |log N| / |log y| := by
  rcases weak_mertens_third_upper_all with ⟨u, hu, hupp⟩
  rcases weak_mertens_third_lower_all with ⟨l, hl, hlow⟩
  refine ⟨u / l, div_pos hu hl, ?_⟩
  intro y N hy hyN
  let f : ℕ → ℝ := fun p ↦ (1 + 1 / (p - 1) : ℝ)
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  let t : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ (n : ℝ) ≤ y
  let u' : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ y < n
  let fy : Finset ℕ := (Icc 1 ⌊y⌋₊).filter Nat.Prime
  have hf_eq : ∀ p : ℕ, Nat.Prime p → f p = (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    calc
      f p = |(1 - (p : ℝ)⁻¹)⁻¹| := useful_identity p hp1
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := by
        refine abs_of_nonneg ?_
        exact (inv_pos.mpr (sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1))).le
  have hs_eq : s.prod f = partial_euler_product N := by
    rw [partial_euler_product]
    have hs' : s = (Icc 1 N).filter Nat.Prime := by
      ext n
      change n ∈ (range (N + 1)).filter Nat.Prime ↔ n ∈ (Icc 1 N).filter Nat.Prime
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hn, hp⟩
        exact ⟨⟨hp.one_lt.le, Nat.lt_succ_iff.mp hn⟩, hp⟩
      · rintro ⟨⟨_, hn⟩, hp⟩
        exact ⟨Nat.lt_succ_of_le hn, hp⟩
    rw [hs']
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have hfy_eq : fy.prod f = partial_euler_product ⌊y⌋₊ := by
    rw [partial_euler_product]
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have ht_subset : t ⊆ s := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnr, hnp⟩
    exact Finset.mem_filter.mpr ⟨hnr, hnp.1⟩
  have hsdiff : s \ t = u' := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_sdiff.mp hn with ⟨hsn, hnt⟩
      rcases Finset.mem_filter.mp hsn with ⟨hnr, hnp⟩
      refine Finset.mem_filter.mpr ⟨hnr, hnp, ?_⟩
      by_contra hny
      exact hnt <| Finset.mem_filter.mpr ⟨hnr, ⟨hnp, le_of_not_gt hny⟩⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnr, hnp, hny⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hnr, hnp⟩, ?_⟩
      intro hnt
      exact not_lt_of_ge (Finset.mem_filter.mp hnt).2.2 hny
  have hfy_subset : fy ⊆ t := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxprime⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    have hxy : (x : ℝ) ≤ y := by
      rw [← Nat.le_floor_iff]
      · exact hx2
      · exact le_trans zero_le_one (le_of_lt hy)
    have hxN : x ≤ N := by
      exact_mod_cast le_trans hxy (le_of_lt hyN)
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simpa [Finset.mem_range, Nat.lt_succ_iff] using hxN, ⟨hxprime, hxy⟩⟩
  have ht_nonneg : ∀ i ∈ t, 0 ≤ f i := by
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact add_nonneg zero_le_one (div_nonneg zero_le_one hsub)
  have ht_one : ∀ i ∈ t, i ∉ fy → 1 ≤ f i := by
    intro i hi hif
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact le_add_of_nonneg_right (div_nonneg zero_le_one hsub)
  have hlow_prod : partial_euler_product ⌊y⌋₊ ≤ t.prod f := by
    calc
      partial_euler_product ⌊y⌋₊ = fy.prod f := hfy_eq.symm
      _ ≤ t.prod f := prod_of_subset_le_prod_of_ge_one hfy_subset ht_nonneg ht_one
  have hNnat : 2 ≤ N := by
    have : 1 < N := by exact_mod_cast (lt_trans hy hyN)
    omega
  have hupp' : partial_euler_product N ≤ u * |log N| := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hupp (N : ℝ) (by exact_mod_cast hNnat)
  have hlow' : l * |log y| ≤ partial_euler_product ⌊y⌋₊ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hlow y (le_of_lt hy)
  have hden : l * |log y| ≤ t.prod f := hlow'.trans hlow_prod
  have hnum_nonneg : 0 ≤ s.prod f := by
    rw [hs_eq]
    exact le_trans zero_le_one partial_euler_trivial_lower_bound
  have ht_pos : 0 < t.prod f := by
    refine Finset.prod_pos ?_
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 < (i : ℝ) - 1 := sub_pos.mpr <| by exact_mod_cast hip.one_lt
    exact add_pos zero_lt_one (one_div_pos.mpr hsub)
  have hylog_pos : 0 < |log y| := by
    rw [abs_of_pos (Real.log_pos hy)]
    exact Real.log_pos hy
  have hmain :
      s.prod f / t.prod f ≤ (u * |log N|) / (l * |log y|) := by
    refine (div_le_div_of_nonneg_left hnum_nonneg (mul_pos hl hylog_pos) hden).trans ?_
    exact div_le_div_of_nonneg_right (hs_eq ▸ hupp') (mul_nonneg (le_of_lt hl) (abs_nonneg _))
  have hrewrite :
      (u * |log N|) / (l * |log y|) = (u / l) * |log N| / |log y| := by
    field_simp [hl.ne', abs_ne_zero.mpr (Real.log_pos hy).ne']
  calc
    ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))
        = u'.prod f := by simp [u', f]
    _ = s.prod f / t.prod f := by
          rw [← hsdiff]
          apply (eq_div_iff ht_pos.ne').2
          simpa using (Finset.prod_sdiff (f := f) ht_subset)
    _ ≤ (u * |log N|) / (l * |log y|) := hmain
    _ = (u / l) * |log N| / |log y| := hrewrite

theorem useful_rec_aux2 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N k : ℕ,
            1 ≤ k →
              1 < y →
                y < N →
                  ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                      (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
                    (C * |log N| / |log y|) ^ k := by
  rcases useful_rec_aux3 with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro y N k hk hy hyN
  specialize hN y N hy hyN
  let s : Finset ℕ := (range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)
  change s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤ (C * |log N| / |log y|) ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hi1_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) - 1) := by
        exact one_div_nonneg.2 hi1_nonneg
      have hstep := one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) - 1))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_pos : 0 < (i : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast hip.one_lt)
      exact add_pos zero_lt_one (one_div_pos.2 hi1_pos)
  have hpow :
      (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k ≤ (C * |log N| / |log y|) ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / (p - 1))))
    _ ≤ (C * |log N| / |log y|) ^ k := hpow

theorem Nat.coprime_symmetric : Symmetric Nat.Coprime := by
  exact Nat.Coprime.symmetric

theorem ArithmeticFunction.IsMultiplicative.prod {ι : Type*} (g : ι → ℕ) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Nat.Coprime (g i) (g j)) :
    s.prod (fun i ↦ f (g i)) = f (s.prod g) := by
  simpa using (hf.map_prod g s hs).symm

theorem my_sum_lemma {α β γ : Type*} [AddCommMonoid γ] [Preorder γ] [IsOrderedAddMonoid γ]
    {s : Finset α} {t : Finset β} (f : α → γ) (g : β → γ) (r : ∀ i ∈ s, β)
    (r_inj : ∀ a₁ a₂ ha₁ ha₂, r a₁ ha₁ = r a₂ ha₂ → a₁ = a₂)
    (hg : ∀ i ∈ t, 0 ≤ g i) (rt : ∀ a ha, r a ha ∈ t) (fr : ∀ a ha, g (r a ha) = f a) :
    s.sum f ≤ t.sum g := by
  classical
  have hEq :
      Finset.sum s.attach (fun i => f i) = Finset.sum s.attach (fun i => g (r i i.prop)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (fr i i.prop).symm
  rw [← Finset.sum_attach, hEq, ← Finset.sum_image]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ q _ ↦ hg _ q
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact rt a a.prop
  · intro a₁ _ a₂ _ h
    exact Subtype.ext (r_inj _ _ _ _ h)

theorem hcongr_thing {α β : Type*} (f g : α → β) :
    ∀ (p q : α → Prop),
      p = q →
        HEq (fun x (_ : p x) ↦ f x) (fun x (_ : q x) ↦ g x) →
          ∀ x, p x → f x = g x := by
  intro p q hpq h x hx
  subst hpq
  exact congrFun₂ (eq_of_heq h) x hx

theorem card_distinct_factors_apply' {m : ℕ} : ω m = m.primeFactorsList.toFinset.card := by
  simpa [ArithmeticFunction.cardDistinctFactors_apply] using
    (List.card_toFinset (l := m.primeFactorsList)).symm

theorem card_distinct_factors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    ω (m * n) = ω m + ω n := by
  exact ArithmeticFunction.cardDistinctFactors_mul hmn

theorem prod_one_add' {D : Finset ℕ} (hD : 0 ∉ D) (f : ArithmeticFunction ℝ)
    (hf' : f.IsMultiplicative) (hf'' : ∀ i, 0 ≤ f i) :
    D.sum f ≤
      (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
        (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum f) := by
  classical
  rw [Finset.prod_one_add]
  simp only [Finset.prod_sum]
  rw [Finset.sum_sigma']
  refine my_sum_lemma
      (f := f)
      (g := fun x : Σ x : Finset ℕ, ∀ a ∈ x, ℕ =>
        ∏ x_1 ∈ x.1.attach, f (x.2 x_1 x_1.prop))
      (r := fun d hd ↦ ⟨d.primeFactors, fun p hp ↦ p ^ d.factorization p⟩)
      ?_ ?_ ?_ ?_
  · intro d₁ d₂ hd₁ hd₂ h
    dsimp at h
    simp only [Sigma.mk.inj_iff] at h
    have hpow :
        ∀ p ∈ d₁.primeFactors, p ^ d₁.factorization p = p ^ d₂.factorization p := by
      intro p hp
      have hmem : (fun x ↦ x ∈ d₁.primeFactors) = fun x ↦ x ∈ d₂.primeFactors := by
        ext x
        rw [h.1]
      exact hcongr_thing _ _ _ _ hmem h.2 p hp
    apply Nat.eq_of_factorization_eq
    · exact ne_of_mem_of_not_mem hd₁ hD
    · exact ne_of_mem_of_not_mem hd₂ hD
    intro p
    by_cases hp : p ∈ d₁.primeFactors
    · apply Nat.pow_right_injective (Nat.prime_of_mem_primeFactors hp).two_le
      exact hpow p hp
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rwa [hp, eq_comm, ← Finsupp.notMem_support_iff, Nat.support_factorization, ← h.1,
        ← Nat.support_factorization, Finsupp.notMem_support_iff]
  · intro i hi
    apply Finset.prod_nonneg
    intro j hj
    exact hf'' _
  · intro d hd
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_pi, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨d, hd, hx⟩
    intro a had
    have hd₀ : d ≠ 0 := ne_of_mem_of_not_mem hd hD
    have hfac : d.factorization a ≠ 0 := by
      rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
    have had' : a.Prime ∧ a ∣ d := (Nat.mem_primeFactors_of_ne_zero hd₀).1 had
    rw [mem_ppowers_in_set' had'.1 hfac]
    exact ⟨⟨_, hd, rfl⟩, dvd_pow_self _ hfac⟩
  · intro d hd
    dsimp
    rw [Finset.prod_attach d.primeFactors (fun y ↦ f (y ^ d.factorization y))]
    rw [ArithmeticFunction.IsMultiplicative.prod _ hf']
    · congr 1
      rw [← Nat.support_factorization]
      change d.factorization.prod (· ^ ·) = d
      rw [Nat.prod_factorization_pow_eq_self]
      exact ne_of_mem_of_not_mem hd hD
    · intro p₁ hp₁ p₂ hp₂ hneq
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp₁)
        (Nat.prime_of_mem_primeFactors hp₂) hneq

@[simp] theorem card_distinct_factors_apply_is_prime_pow {q : ℕ} (hq : IsPrimePow q) : ω q = 1 := by
  exact ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hq

theorem Nat.le_pow_self {x y : ℕ} (hy : y ≠ 0) : x ≤ x ^ y := by
  exact Nat.le_self_pow hy x

theorem dvd_prime_powers {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 1 m) := by
  rcases S.eq_empty_or_nonempty with rfl | hS'
  · refine ⟨1, by simp⟩
  refine ⟨S.max' hS' + 1, ?_⟩
  intro x hx
  obtain ⟨p', k, hp', hk, rfl⟩ := (isPrimePow_nat_iff x).1 (hS x (Finset.filter_subset _ _ hx))
  simp only [Finset.mem_filter] at hx
  have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hx.2)
  subst p'
  refine Finset.mem_map.2 ⟨k, ?_, rfl⟩
  simp only [Finset.mem_Ico]
  constructor
  · exact hk
  · exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      ((Finset.le_max' _ _ hx.1).trans (Nat.le_succ _))

theorem dvd_prime_powers' {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x)
    (hSp : p ∉ S) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 2 m) := by
  obtain ⟨m, hm⟩ := dvd_prime_powers hp S hS
  refine ⟨m, ?_⟩
  intro x hx
  rcases Finset.mem_map.1 (hm hx) with ⟨n, hn, rfl⟩
  have hn1 : n ≠ 1 := by
    intro hn1
    apply hSp
    simpa [hn1] using hx
  refine Finset.mem_map.2 ⟨n, ?_, rfl⟩
  simp only [Finset.mem_Ico] at hn ⊢
  omega

theorem useful_rec_aux4' (y : ℝ) (k N : ℕ) (D : Finset ℕ) (hD' : 0 ∉ D)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  have h₁ :
      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q)) := by
    let f : ArithmeticFunction ℝ := ⟨fun d ↦ (k : ℝ) ^ ω d / d, by simp⟩
    have hf' : f.IsMultiplicative := by
      refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨by simp [f], ?_⟩
      intro m n hm hn hmn
      change (k : ℝ) ^ ω (m * n) / ((m * n : ℕ) : ℝ) =
        ((k : ℝ) ^ ω m / (m : ℝ)) * ((k : ℝ) ^ ω n / (n : ℝ))
      rw [card_distinct_factors_mul_of_coprime hmn, div_mul_div_comm, Nat.cast_mul, pow_add]
    have hf'' : ∀ i, 0 ≤ f i := by
      intro i
      exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    refine (prod_one_add' hD' f hf' hf'').trans_eq ?_
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [add_right_inj]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hωq : ω q = 1 := by
      rw [Finset.mem_filter] at hq
      rw [mem_ppowers_in_set] at hq
      exact card_distinct_factors_apply_is_prime_pow hq.1.1
    simp [f, hωq]
  have hsubset :
      D.biUnion (fun n ↦ n.primeFactorsList.toFinset) ⊆
        (Finset.range (N + 1)).filter Nat.Prime := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨d, hd, hxd⟩
    have hdx : x ∈ d.primeFactors := by
      simpa using hxd
    have hd'' : d.factorization x ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hdx
    have hxN : x ≤ N := by
      exact (Nat.le_pow_self hd'').trans <|
        (hD (x ^ d.factorization x) (mem_ppowers_in_set'' hd hd'')).2
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_of_mem_primeFactors hdx⟩
    show x ∈ Finset.range (N + 1)
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hxN
  have h₃ :
      ∀ i,
        (0 : ℝ) ≤ ((ppowers_in_set D).filter (fun q ↦ i ∣ q)).sum (fun q ↦ (k : ℝ) / q) := by
    intro i
    refine Finset.sum_nonneg ?_
    intro q hq
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply h₁.trans
  refine (prod_of_subset_le_prod_of_one_le hsubset ?_ ?_).trans ?_
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i _ _
    exact le_add_of_nonneg_right (h₃ i)
  rw [← Finset.prod_filter_mul_prod_filter_not ((range (N + 1)).filter Nat.Prime) (fun n ↦ y < n),
    mul_comm]
  have hleft₁ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, not_lt, and_imp, Finset.mem_range, Nat.lt_succ_iff,
        add_le_add_iff_left, div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers' hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
        (fun h ↦ not_lt_of_ge hpy (hD _ h).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [pow_two, hp0, hp1]
  have hleft₂ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    exact prod_of_subset_le_prod_of_one_le (Finset.filter_subset _ _)
      (fun i hi ↦ by
        rw [mul_comm]
        exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
      (fun i _ _ ↦ by
        rw [mul_comm]
        exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
  have hright :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter (fun n : ℕ ↦ Nat.Prime n ∧ y < (n : ℝ)))).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    rw [Finset.filter_filter]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, and_imp, Finset.mem_range, Nat.lt_succ_iff, add_le_add_iff_left,
        div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [hp0, hp1]
  refine mul_le_mul (hleft₁.trans hleft₂) hright (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i hi
    rw [mul_comm]
    exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing)

theorem useful_rec_aux4 (y : ℝ) (k N : ℕ) (D : Finset ℕ)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  by_cases h0 : 0 ∈ D
  · have hD' : 0 ∉ D.erase 0 := by simp
    rw [← Finset.sum_erase_add _ _ h0, Nat.cast_zero, div_zero, add_zero]
    apply useful_rec_aux4' y k N _ hD'
    rwa [ppowers_in_set_erase_zero]
  · exact useful_rec_aux4' y k N D h0 hD

theorem useful_rec_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ k N : ℕ,
            ∀ D : Finset ℕ,
              (1 < y →
                y < N →
                  1 ≤ k →
                    (∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) →
                      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C * |log N| / |log y|) ^ k) := by
  rcases useful_rec_aux1 with ⟨C₁, hC₁, haux₁⟩
  rcases useful_rec_aux2 with ⟨C₂, hC₂, haux₂⟩
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro y k N D hy hyN hk hD
  have hmain := useful_rec_aux4 y k N D hD
  have hleft :
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        C₁ ^ k := haux₁ N k hk
  have hright :
      ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        (C₂ * |log N| / |log y|) ^ k := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux₂ y N k hk hy hyN
  have hright_nonneg :
      0 ≤
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    have hp1_nonneg : 0 ≤ (p : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast hp'.one_lt.le)
    exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hp1_nonneg))
  have hCpow_nonneg : 0 ≤ C₁ ^ k := by
    exact pow_nonneg hC₁.le _
  have hmul :
      ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := by
    exact mul_le_mul hleft hright hright_nonneg hCpow_nonneg
  calc
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := hmain
    _ ≤ C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := hmul
    _ = ((C₁ * C₂) * |log N| / |log y|) ^ k := by
      rw [← mul_pow]
      congr 1
      ring

open Classical in
theorem find_good_d_aux1 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M u y : ℝ,
        ∀ q : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                0 ≤ u →
                  ∀ d ∈
                      (range (N + 1)).filter
                        (fun d : ℕ ↦
                          (∀ r : ℕ, IsPrimePow r → r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
                            M * u < (q * d : ℝ) ∧ q * d ≤ N),
                    ((((local_part A q).filter
                          (fun n ↦ (q * d) ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
                        (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤
                      2 * log N / d := by
  filter_upwards [eventually_ge_atTop 0, harmonic_sum_bound_two] with N hN hharmonic
  intro M u y q A hA hM hMN hu d hd
  let X :=
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hdlt : M * u < (q * d : ℝ) := (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : d ≠ 0 := by
    intro hzd
    subst hzd
    have hdlt' : M * u < 0 := by simpa using hdlt
    exact (not_lt_of_ge (mul_nonneg hM.le hu)) hdlt'
  have hqd_pos : 0 < (q * d : ℝ) := lt_of_le_of_lt (mul_nonneg hM.le hu) hdlt
  have hqd0 : (q * d : ℝ) ≠ 0 := ne_of_gt hqd_pos
  have hrectrivialaux :
      X.sum (fun n ↦ (q : ℚ) / n) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      exact ⟨hA (local_part_subset hx.1), hx.2.1⟩
    · intro i _ _
      exact div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg i)
  have hrectrivial' :
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
    calc
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
          ((((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) := by
        exact_mod_cast hrectrivialaux
      _ = ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
        rw [Rat.cast_sum]
        push_cast
        rfl
  have hrectrivial'' :
      ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) ≤
        (1 / d : ℝ) *
          (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) := by
    let g : ℕ → ℕ := fun n ↦ n / (q * d)
    rw [Finset.mul_sum]
    refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
    · intro n hn
      exact mul_nonneg (one_div_nonneg.2 (Nat.cast_nonneg d)) (one_div_nonneg.2 (Nat.cast_nonneg n))
    · intro n hn
      rw [Finset.mem_filter] at hn
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr <|
          lt_of_le_of_lt (Nat.div_le_self _ _) (Finset.mem_range.mp hn.1)
      · dsimp [g]
        simpa [Nat.mul_div_cancel' hn.2] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn.1)
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      calc
        a = (q * d) * g a := by simp [g, Nat.mul_div_cancel' ha.2]
        _ = (q * d) * g b := by rw [hab]
        _ = b := by simp [g, Nat.mul_div_cancel' hb.2]
    · intro n hn
      rw [Finset.mem_filter] at hn
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hDnotzero
      have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
        simpa [Nat.cast_mul] using hqd0
      have hcast : (g n : ℝ) = (n : ℝ) / (q * d : ℕ) := by
        dsimp [g]
        rw [Nat.cast_div hn.2 hqd0']
      rw [hcast, Nat.cast_mul, one_div_mul_one_div, mul_div, one_div_div, mul_comm (q : ℝ),
        mul_div_mul_left _ _ hd0]
  have hrectrivial''' :
      ((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum (fun m ↦ (1 : ℝ) / m) ≤
        (range (N + 1)).sum (fun n ↦ (1 : ℝ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
      one_div_nonneg.2 (Nat.cast_nonneg i)
  have hfinal :
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
        2 * log N / d := by
    have hstep1 :
        (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
          (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := by
      exact mul_le_mul_of_nonneg_left hrectrivial''' (one_div_nonneg.2 (Nat.cast_nonneg d))
    have hstep2 :
        (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) ≤ (1 / d : ℝ) * (2 * log N) := by
      exact mul_le_mul_of_nonneg_left hharmonic (one_div_nonneg.2 (Nat.cast_nonneg d))
    calc
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m)
          ≤ (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := hstep1
      _ ≤ (1 / d : ℝ) * (2 * log N) := hstep2
      _ = 2 * log N / d := by ring
  simpa [X] using hrectrivial'.trans (hrectrivial''.trans hfinal)

open Classical in
theorem find_good_d_aux2 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ k : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                1 ≤ k →
                  (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                    ∀ q ∈ ppowers_in_set A,
                      ∀ n ∈ local_part A q,
                        ∃ d ∈
                            (range (N + 1)).filter
                              (fun d : ℕ ↦
                                (∀ r : ℕ,
                                    IsPrimePow r →
                                      r ∣ d →
                                        Nat.Coprime r (d / r) →
                                          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r ∧ r ≤ N) ∧
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q * d : ℝ) ∧
                                    q * d ≤ N),
                          (q * d ∣ n) ∧ Nat.Coprime (q * d) (n / (q * d)) := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with
    N hlargeN M k A hA hM hMN hk hAreg q hq n hn
  have hqpp : IsPrimePow q := by
    rw [mem_ppowers_in_set] at hq
    exact hq.1
  have hN : 0 < N := by
    exact lt_trans zero_lt_one hlargeN
  let Q : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r
  let d : ℕ := Q.prod id
  have memQ {r : ℕ} :
      r ∈ Q ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r := by
    simp [Q]
  have hnz : n ≠ 0 := by
    intro hnz2
    rw [local_part, hnz2] at hn
    have htemp := hAreg 0 (Finset.mem_of_mem_filter 0 hn)
    exact (not_le_of_gt hM) (by exact_mod_cast htemp.1)
  have hnN : n ≤ N := by
    have hnA : n ∈ A := Finset.mem_of_mem_filter n hn
    have hnRange : n ∈ range (N + 1) := hA hnA
    exact Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hnRange)
  have hqdcop : Nat.Coprime q d := by
    by_contra h
    rw [prime_pow_not_coprime_prod_iff hqpp] at h
    · rcases h with ⟨p, kq, kd, d', hd, hp, hkq, hkd, hpq, hpd⟩
      rw [local_part, Finset.mem_filter] at hn
      have hd' : d' ∈ n.divisors ∧ IsPrimePow d' ∧ Nat.Coprime d' (n / d') ∧ d' ≠ q ∧
          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < d' := by
        simpa [memQ] using hd
      rcases hd' with ⟨hdDiv, hdProps⟩
      apply hdProps.2.2.1
      rw [← hpq, ← hpd]
      refine congrArg (fun t : ℕ => p ^ t) ?_
      calc
        kd = n.factorization p := by
          apply coprime_div_iff hp
          · rw [hpd]
            exact Nat.dvd_of_mem_divisors hdDiv
          · exact hkd
          · rw [hpd]
            exact hdProps.2.1
        _ = kq := by
          refine Eq.symm ?_
          apply coprime_div_iff hp
          · rw [hpq]
            exact hn.2.1
          · exact hkq
          · rw [hpq]
            exact hn.2.2
    · intro x hx
      exact (memQ.mp hx).2.1
  have hQcoprime :
      ∀ a ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
        ∀ b ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
          a ≠ b → Nat.Coprime a b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    by_contra h
    rw [prime_pow_not_coprime_iff ha.2.1 hb.2.1] at h
    rcases h with ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    apply hab
    rw [← hpa, ← hpb]
    refine congrArg (fun t : ℕ => p ^ t) ?_
    calc
      ka = n.factorization p := by
        apply coprime_div_iff hp
        · rw [hpa]
          exact Nat.dvd_of_mem_divisors ha.1
        · exact hka
        · rw [hpa]
          exact ha.2.2
      _ = kb := by
        refine Eq.symm ?_
        apply coprime_div_iff hp
        · rw [hpb]
          exact Nat.dvd_of_mem_divisors hb.1
        · exact hkb
        · rw [hpb]
          exact hb.2.2
  have hqd : q * d ∣ n := by
    rw [dvd_iff_ppowers_dvd]
    intro r hr1 hr2
    rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hr1 with hrq | hrd
    · rw [local_part, Finset.mem_filter] at hn
      exact dvd_trans hrq hn.2.1
    · rw [is_prime_pow_dvd_prod ?_ hr2] at hrd
      · rcases hrd with ⟨t, ht, hrt⟩
        exact dvd_trans hrt (Nat.dvd_of_mem_divisors (memQ.mp ht).1)
      · intro a ha b hb hab
        refine hQcoprime _ ?_ _ ?_ hab
        · exact Finset.mem_filter.mpr ⟨(memQ.mp ha).1, (memQ.mp ha).2.1, (memQ.mp ha).2.2.1⟩
        · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
  have hdupp : q * d ≤ N := by
    refine le_trans (Nat.le_of_dvd ?_ hqd) hnN
    have : (0 : ℝ) < n := by
      refine lt_of_lt_of_le hM ?_
      exact (hAreg n (Finset.mem_of_mem_filter n hn)).1
    exact_mod_cast this
  let Q' : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  have memQ' {r : ℕ} :
      r ∈ Q' ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
    simp [Q']
  have hQ'dcop : Nat.Coprime q (Q'.prod id) := by
    by_contra h
    rw [prime_pow_not_coprime_prod_iff hqpp] at h
    · rcases h with ⟨p, kq, kd, d', hd, hp, hkq, hkd, hpq, hpd⟩
      rw [local_part, Finset.mem_filter] at hn
      have hd' : d' ∈ n.divisors ∧ IsPrimePow d' ∧ Nat.Coprime d' (n / d') ∧ d' ≠ q ∧
          (d' : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
        simpa [memQ'] using hd
      rcases hd' with ⟨hdDiv, hdProps⟩
      apply hdProps.2.2.1
      rw [← hpq, ← hpd]
      refine congrArg (fun t : ℕ => p ^ t) ?_
      calc
        kd = n.factorization p := by
          apply coprime_div_iff hp
          · rw [hpd]
            exact Nat.dvd_of_mem_divisors hdDiv
          · exact hkd
          · rw [hpd]
            exact hdProps.2.1
        _ = kq := by
          refine Eq.symm ?_
          apply coprime_div_iff hp
          · rw [hpq]
            exact hn.2.1
          · exact hkq
          · rw [hpq]
            exact hn.2.2
    · intro x hx
      exact (memQ'.mp hx).2.1
  have hQ'qd : Nat.Coprime (q * d) (Q'.prod id) := by
    apply Nat.Coprime.symm
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.symm hQ'dcop
    · rw [prime_pow_prods_coprime]
      · intro a ha b hb
        refine hQcoprime _ ?_ _ ?_ ?_
        · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
        · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
        · intro hab
          have ha' := memQ'.mp ha
          have hb' := memQ.mp hb
          rw [hab] at ha'
          have hbnge : ¬ ((b : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))) := by
            exact (lt_iff_not_ge).mp hb'.2.2.2.2
          exact hbnge ha'.2.2.2.2
      · intro a ha
        exact (memQ'.mp ha).2.1
      · intro a ha
        exact (memQ.mp ha).2.1
  have hnqd : n = (Q'.prod id) * q * d := by
    rw [eq_iff_ppowers_dvd n ((Q'.prod id) * q * d) hnz ?_]
    · constructor
      · intro r hr1 hr2 hr3
        by_cases hrq : r = q
        · rw [mul_assoc, hrq]
          exact dvd_trans (dvd_mul_right q d) <|
            dvd_mul_of_dvd_right (dvd_refl (q * d)) (Q'.prod id)
        · by_cases hrsize : (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
          · have hrmem : r ∈ Q' := by
              exact memQ'.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            exact dvd_trans (Finset.dvd_prod_of_mem id hrmem) <|
              dvd_mul_of_dvd_left (dvd_mul_right (Q'.prod id) q) d
          · have hrmem : r ∈ Q := by
              rw [← lt_iff_not_ge] at hrsize
              exact memQ.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            have hrd' : r ∣ q * d := by
              have : r ∣ Q.prod id := Finset.dvd_prod_of_mem id hrmem
              simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                dvd_trans this (dvd_mul_right (Q.prod id) q)
            exact dvd_trans hrd' <| by
              simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                dvd_mul_right (q * d) (Q'.prod id)
      · intro r hr1 hr2 hr3
        have hr1' : r ∣ (Q'.prod id) * (q * d) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr1
        rcases (Nat.Coprime.symm hQ'qd).isPrimePow_dvd_mul hr2 |>.mp hr1' with hw1 | hw2
        · rw [is_prime_pow_dvd_prod ?_ hr2] at hw1
          · rcases hw1 with ⟨t, ht, hwt⟩
            exact dvd_trans hwt (Nat.dvd_of_mem_divisors (memQ'.mp ht).1)
          · intro a ha b hb hab
            refine hQcoprime _ ?_ _ ?_ hab
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp hb).1, (memQ'.mp hb).2.1, (memQ'.mp hb).2.2.1⟩
        · rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hw2 with hw3 | hw4
          · rw [local_part, Finset.mem_filter] at hn
            exact dvd_trans hw3 hn.2.1
          · exact dvd_trans hw4 (dvd_trans (dvd_mul_left _ _) hqd)
    · have hQ'ne : Q'.prod id ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro r hr
        exact Nat.ne_of_gt <| Nat.succ_le_iff.mp (memQ'.mp hr).2.1.pos
      have hqd0 : q * d ≠ 0 := by
        intro hbad
        apply hnz
        rw [hbad, zero_dvd_iff] at hqd
        exact hqd
      simpa [Nat.mul_assoc] using Nat.mul_ne_zero hQ'ne hqd0
  refine ⟨d, ?_, hqd, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      refine le_trans ?_ hdupp
      exact Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero <| by
        intro h
        rw [h] at hq
        exact zero_not_mem_ppowers_in_set hq)
    · refine ⟨?_, ?_, hdupp⟩
      · intro r hr1 hr2 hr3
        have hrQ : r ∈ Q := by
          refine prime_pow_dvd_prod_prime_pow hr1 ?_ ?_ hr2 hr3
          · intro a ha b hb hab
            by_contra h
            have ha' := memQ.mp ha
            have hb' := memQ.mp hb
            have h' := prime_pow_not_coprime_prime_pow ha'.2.1 hb'.2.1 h
            rcases h' with ⟨p, k, l, hp, hkl, hpa, hpb⟩
            have hafac : n.factorization p = k := by
              rw [← factorization_eq_iff hp hkl.1, hpa]
              exact ⟨Nat.dvd_of_mem_divisors ha'.1, ha'.2.2.1⟩
            have hbfac : n.factorization p = l := by
              rw [← factorization_eq_iff hp hkl.2, hpb]
              exact ⟨Nat.dvd_of_mem_divisors hb'.1, hb'.2.2.1⟩
            apply hab
            rw [← hpa, ← hpb, ← hafac, ← hbfac]
          · intro t ht
            exact (memQ.mp ht).2.1
        refine ⟨(memQ.mp hrQ).2.2.2.2, ?_⟩
        exact le_trans (Nat.divisor_le (memQ.mp hrQ).1) hnN
      · have hstep :
            M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) ≤
              (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
            exact mul_le_mul_of_nonneg_right
              ((hAreg n (Finset.mem_of_mem_filter n hn)).1) (le_of_lt (Real.exp_pos _))
        have hstep' : (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q : ℝ) * d := by
          rw [hnqd]
          push_cast
          rw [← Nat.cast_prod]
          have hmul :
              ((((Q'.prod id : ℕ) : ℝ) * (q : ℝ) * (d : ℝ)) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) =
                ((((Q'.prod id : ℕ) : ℝ) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) * ((q : ℝ) * d)) := by
            ring
          rw [hmul]
          have hqd0' : q * d ≠ 0 := by
            intro hzero
            rw [hzero, zero_dvd_iff] at hqd
            exact hnz hqd
          have hqdpos : 0 < (q : ℝ) * d := by
            exact_mod_cast Nat.pos_of_ne_zero hqd0'
          rw [mul_comm]
          apply mul_lt_of_lt_one_right hqdpos
          · rw [exp_neg, ← one_div, mul_one_div, div_lt_one]
            · calc
              (((Q'.prod id : ℕ) : ℝ)) = Q'.prod (fun i ↦ (i : ℝ)) := by
                simp
              _ ≤ (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ Q'.card := by
                refine prod_le_max_size ?_ _ ?_
                · intro i hi
                  exact Nat.cast_nonneg i
                · intro i hi
                  exact (memQ'.mp hi).2.2.2.2
              _ < (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ (log N ^ ((1 : ℝ) / k)) := by
                rw [← Real.rpow_natCast]
                apply Real.rpow_lt_rpow_of_exponent_lt
                · rw [one_lt_exp_iff]
                  apply Real.rpow_pos_of_pos
                  exact Real.log_pos (by exact_mod_cast hlargeN)
                · calc
                    (Q'.card : ℝ) ≤
                        (n.divisors.filter fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card := by
                          have hsubset : Q' ⊆ n.divisors.filter fun r ↦
                              IsPrimePow r ∧ Nat.Coprime r (n / r) := by
                            intro r hr
                            exact Finset.mem_filter.mpr
                              ⟨(memQ'.mp hr).1, (memQ'.mp hr).2.1, (memQ'.mp hr).2.2.1⟩
                          exact_mod_cast Finset.card_le_card hsubset
                    _ = (ω n : ℝ) := by
                      norm_num [omega_count_eq_ppowers]
                    _ < log N ^ ((1 : ℝ) / k) := by
                      rw [local_part] at hn
                      exact (hAreg n (Finset.mem_of_mem_filter n hn)).2
              _ = Real.exp (log N ^ ((1 : ℝ) - 1 / k)) := by
                rw [← Real.exp_mul, ← Real.rpow_add]
                · ring_nf
                exact Real.log_pos (by exact_mod_cast hlargeN)
            exact Real.exp_pos _
        exact lt_of_le_of_lt hstep hstep'
  · have hqd0 : q * d ≠ 0 := by
      intro hzero
      rw [hzero, zero_dvd_iff] at hqd
      exact hnz hqd
    have hquot : n / (q * d) = Q'.prod id := by
      rw [hnqd, Nat.mul_assoc]
      rw [Nat.mul_comm (Q'.prod id) (q * d)]
      exact Nat.mul_div_right (Q'.prod id) (Nat.pos_of_ne_zero hqd0)
    simpa [hquot] using hQ'qd

private theorem find_good_d_hc (C1 : ℝ) (_hC1 : 0 < C1) :
    0 < ((1 / 2 : ℝ) / Real.log (max C1 2)) := by
  refine div_pos (by norm_num) ?_
  apply Real.log_pos
  exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)

private theorem find_good_d_hC (C1 : ℝ) (hC1 : 0 < C1) :
    0 < (1 / (C1 * 2) : ℝ) := by
  rw [one_div_pos]
  exact mul_pos hC1 zero_lt_two

private theorem find_good_d_hC' (C1 : ℝ) (hC1 : 0 < C1) :
    C1 = 1 / (((1 / (C1 * 2) : ℝ)) * 2) := by
  have hC10 : C1 ≠ 0 := ne_of_gt hC1
  field_simp [hC10]

private theorem find_good_d_hC2 (C1 : ℝ) : 1 < max C1 2 := by
  exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)

private theorem find_good_d_hlarge1 {N : ℕ} (hlarge : 1 < log N) : 0 < log N := by
  exact lt_trans zero_lt_one hlarge

private theorem find_good_d_hlarge2 {N : ℕ} (hlarge1 : 0 < log N) (hlarge'' : (16 : ℝ) ≤ log N) :
    4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
  have hsqrt : (4 : ℝ) ≤ log N ^ ((1 : ℝ) / 2) := by
    have hsqrt' : Real.sqrt (16 : ℝ) ≤ Real.sqrt (log N) := Real.sqrt_le_sqrt hlarge''
    norm_num [Real.sqrt_eq_rpow] at hsqrt' ⊢
    exact hsqrt'
  have hpowpos : 0 < log N ^ ((1 : ℝ) / 2) := by
    positivity
  have hlog0 : 0 ≤ log N := le_of_lt hlarge1
  calc
    4 * log N ^ (-((3 : ℝ) / 2) + 1) = 4 / log N ^ ((1 : ℝ) / 2) := by
      rw [show -((3 : ℝ) / 2) + 1 = -((1 : ℝ) / 2) by ring]
      rw [Real.rpow_neg hlog0, ← one_div]
      ring
    _ ≤ 1 := by
      exact (div_le_iff₀ hpowpos).2 (by simpa using hsqrt)

private theorem find_good_d_h1y {N k : ℕ} (hlarge1 : 0 < log N) :
    1 < Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
  rw [Real.one_lt_exp_iff]
  exact Real.rpow_pos_of_pos hlarge1 _

private theorem find_good_d_hyN {N k : ℕ} (hlarge : 1 < log N) (hlarge' : 0 < N) (h1k : 1 < k) :
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < N := by
  have hexp : log N ^ ((1 : ℝ) - 2 / k) < log N ^ (1 : ℝ) := by
    refine Real.rpow_lt_rpow_of_exponent_lt hlarge ?_
    refine sub_lt_self 1 ?_
    refine div_pos zero_lt_two ?_
    exact_mod_cast (lt_trans zero_lt_one h1k)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hlarge'
  calc
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < Real.exp (log N) := by
      simpa using Real.exp_lt_exp.mpr hexp
    _ = N := by rw [Real.exp_log hNpos]

private theorem find_good_d_h0k {k : ℕ} (h1k : 1 < k) : (0 : ℝ) < k := by
  exact_mod_cast (lt_trans zero_lt_one h1k)

private theorem find_good_d_hlocal2 {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (haux2 : ∀ n ∈ local_part A q, ∃ d ∈ D, q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))) :
    local_part A q ⊆ D.biUnion newLocal := by
  subst newLocal
  intro n hn
  rw [Finset.mem_biUnion]
  rcases haux2 n hn with ⟨d, hd, hlocal⟩
  refine ⟨d, hd, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hn, hlocal⟩

private theorem find_good_d_hrecbound {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (hlocal2 : local_part A q ⊆ D.biUnion newLocal) :
    rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  subst newLocal
  rw [rec_sum_local]
  let s :=
    D.biUnion fun d ↦
      (local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))
  have h1 : (local_part A q).sum (fun n ↦ (q : ℚ) / n) ≤ s.sum (fun n ↦ (q : ℚ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlocal2 (by
      intro i _ _
      positivity)
  have h2 :
      s.sum (fun n ↦ (q : ℚ) / n) ≤
        D.sum (fun d ↦
          ((local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))).sum
            (fun n ↦ (q : ℚ) / n)) := by
    dsimp [s]
    refine sum_bUnion_le_sum_of_nonneg ?_
    intro i _
    positivity
  exact le_trans h1 h2

private theorem find_good_d_hDnotzero {M u : ℝ} {q : ℕ} {D : Finset ℕ}
    (hzM : 0 < M) (hu : 0 < u) (hDu : ∀ d ∈ D, M * u < q * d) :
    ∀ d ∈ D, d ≠ 0 := by
  intro d hd hd0
  have hd' := hDu d hd
  rw [hd0, Nat.cast_zero, mul_zero] at hd'
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hzM) (le_of_lt hu))) hd'

private theorem find_good_d_hbound1 {C1 c y ω0 : ℝ} {N q k : ℕ} {A D1 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hC1 : 0 < C1) (hc : c = (1 / 2 : ℝ) / Real.log (max C1 2))
    (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hkN : (k : ℝ) ≤ c * log (log N)) (hlarge1 : 0 < log N)
    (hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1) (h1k : 1 < k) (h0k : (0 : ℝ) < k)
    (hω0 : ω0 = (5 / log k) * log (log N)) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hωD1 : ∀ d ∈ D1, ω0 ≤ (ω d : ℝ))
    (haux1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d)
    (hrec1bound : D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k) :
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
      (rec_sum_local A q : ℝ) / 2 := by
  let C2 : ℝ := max C1 2
  have hC2 : 1 < C2 := lt_of_lt_of_le one_lt_two (le_max_right C1 2)
  have h1y : 1 < y := by
    rw [hy, Real.one_lt_exp_iff]
    exact Real.rpow_pos_of_pos hlarge1 _
  have hfac_nonneg : 0 ≤ 2 * log N := by positivity
  have hkpow_nonneg : 0 ≤ (k : ℝ) ^ (-ω0) := le_of_lt (Real.rpow_pos_of_pos h0k _)
  calc
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ)
        = D1.sum (fun d ↦ (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) := by
          rw [Rat.cast_sum]
    _ ≤ D1.sum (fun d ↦ 2 * log N / d) := by
          refine Finset.sum_le_sum ?_
          intro d hd
          exact haux1 d hd
    _ = 2 * log N * D1.sum (fun d ↦ (1 : ℝ) / d) := by
      rw [mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [div_eq_mul_one_div]
    _ ≤ 2 * log N * D1.sum (fun d ↦ (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d)) := by
      apply mul_le_mul_of_nonneg_left
      · refine Finset.sum_le_sum ?_
        intro d hd
        have hkge : 1 ≤ (k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d := by
          rw [← Real.rpow_natCast, ← Real.rpow_add]
          · apply one_le_rpow
            · exact_mod_cast (le_of_lt h1k)
            · linarith [hωD1 d hd]
          · exact h0k
        calc
          (1 : ℝ) / d = 1 * (1 / d) := by ring
          _ ≤ ((k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d) * (1 / d) := by
            exact mul_le_mul_of_nonneg_right hkge (by
              rw [one_div_nonneg]
              exact_mod_cast Nat.cast_nonneg d)
          _ = (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d) := by
            rw [div_eq_mul_one_div]
            ring
      · exact hfac_nonneg
    _ = 2 * log N * (k : ℝ) ^ (-ω0) * D1.sum (fun d ↦ ((k : ℝ) ^ ω d / d)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * log N * (k : ℝ) ^ (-ω0) * (C1 * |log N| / |log y|) ^ k := by
      exact mul_le_mul_of_nonneg_left hrec1bound (mul_nonneg hfac_nonneg hkpow_nonneg)
    _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by
      have hkpow :
          (k : ℝ) ^ (-ω0) = log N ^ (-5 : ℝ) := by
        have hlogk : 0 < Real.log k := by
          exact Real.log_pos (by exact_mod_cast h1k)
        calc
          (k : ℝ) ^ (-ω0) = Real.exp (Real.log k * (-ω0)) := by
            rw [Real.rpow_def_of_pos h0k]
          _ = Real.exp (-5 * log (log N)) := by
            rw [hω0]
            field_simp [ne_of_gt hlogk]
          _ = Real.exp (log (log N) * (-5 : ℝ)) := by ring_nf
          _ = (Real.exp (log (log N))) ^ (-5 : ℝ) := by rw [Real.exp_mul]
          _ = log N ^ (-5 : ℝ) := by rw [Real.exp_log hlarge1]
      have hyabs : |log y| = log N ^ ((1 : ℝ) - 2 / k) := by
        rw [hy, Real.log_exp, abs_eq_self.mpr]
        exact le_of_lt (Real.rpow_pos_of_pos hlarge1 _)
      have hquot : log N / log N ^ ((1 : ℝ) - (2 : ℝ) / k) = log N ^ ((2 : ℝ) / k) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_sub hlarge1 (1 : ℝ) ((1 : ℝ) - (2 : ℝ) / k)]
        have hEq : (1 : ℝ) - ((1 : ℝ) - (2 : ℝ) / k) = (2 : ℝ) / k := by
          field_simp [ne_of_gt h0k]
          ring
        rw [hEq]
      have hpowLog : (log N ^ (((2 : ℝ) / k))) ^ k = log N ^ (2 : ℝ) := by
        have hk2 : (((2 : ℝ) / k)) * k = 2 := by
          field_simp [ne_of_gt h0k]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlarge1.le, hk2]
      have hpowFinal : log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ) = log N ^ (-2 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_add hlarge1, ← Real.rpow_add hlarge1]
        norm_num
      rw [hkpow, abs_eq_self.mpr hlarge1.le, hyabs, mul_div_assoc, hquot, mul_pow]
      change
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * (log N ^ (((2 : ℝ) / k))) ^ k) =
          2 * log N ^ (-2 : ℝ) * C1 ^ k
      rw [hpowLog]
      calc
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * log N ^ (2 : ℝ))
            = 2 * (log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ)) * C1 ^ k := by
              ring
        _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by rw [hpowFinal]
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * C2 ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (le_of_lt hC1) (le_max_left C1 2) _
      · positivity
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * (log N ^ (Real.log C2 * c)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [← Real.rpow_natCast]
        refine (Real.le_rpow_iff_log_le
          (Real.rpow_pos_of_pos (show 0 < C2 by linarith) _) hlarge1).2 ?_
        rw [Real.log_rpow (show 0 < C2 by linarith), mul_comm (k : ℝ), mul_assoc]
        exact mul_le_mul_of_nonneg_left hkN (Real.log_pos hC2).le
      · positivity
    _ = 2 * (log N ^ (-(3 / 2 : ℝ))) := by
      rw [hc, show Real.log C2 = Real.log (max C1 2) by rfl]
      rw [mul_assoc, ← Real.rpow_add hlarge1]
      have hlogne : Real.log (max C1 2) ≠ 0 := ne_of_gt (Real.log_pos hC2)
      congr 1
      field_simp [hlogne]
      ring_nf
    _ ≤ (1 / log N) / 2 := by
      rw [le_div_iff₀ zero_lt_two, le_div_iff₀ hlarge1]
      calc
        2 * log N ^ (-(3 / 2 : ℝ)) * 2 * log N
            = 4 * log N ^ (-((3 : ℝ) / 2) + 1) := by
              rw [show (2 : ℝ) * log N ^ (-(3 / 2 : ℝ)) * 2 * log N =
                4 * (log N ^ (-(3 / 2 : ℝ)) * log N) by ring]
              nth_rewrite 2 [show (log N : ℝ) = log N ^ (1 : ℝ) by rw [Real.rpow_one]]
              rw [← Real.rpow_add hlarge1]
        _ ≤ 1 := hlarge2
    _ ≤ ((rec_sum_local A q : ℝ) / 2) := by
      have hhalf :
          (1 / log N) * (1 / 2 : ℝ) ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsumq (show (0 : ℝ) ≤ 1 / 2 by positivity)
      calc
        (1 / log N) / 2 = (1 / log N) * (1 / 2 : ℝ) := by ring
        _ ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) := hhalf
        _ = (rec_sum_local A q : ℝ) / 2 := by ring

private theorem find_good_d_hbound2 {ω0 : ℝ} {A : Finset ℕ} {q : ℕ} {D D1 D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hD1 : D1 = D.filter (fun d ↦ ω0 ≤ (ω d : ℝ)))
    (hD2 : D2 = D.filter (fun d ↦ (ω d : ℝ) < ω0))
    (hrecbound : rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  calc
    (rec_sum_local A q : ℚ) / 2 = rec_sum_local A q - (rec_sum_local A q : ℚ) / 2 := by
      exact Eq.symm (sub_self_div_two (rec_sum_local A q))
    _ ≤
        D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) -
          D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
      apply sub_le_sub
      · exact hrecbound
      · exact_mod_cast hbound1
    _ = D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
      have hDD : D = D1 ∪ D2 := by
        rw [hD1, hD2]
        ext d
        constructor
        · intro hd
          rw [Finset.mem_union]
          by_cases hdω : ω0 ≤ (ω d : ℝ)
          · exact Or.inl (Finset.mem_filter.mpr ⟨hd, hdω⟩)
          · exact Or.inr (Finset.mem_filter.mpr ⟨hd, lt_of_not_ge hdω⟩)
        · intro hd
          rcases Finset.mem_union.mp hd with hd | hd
          · exact Finset.mem_of_mem_filter d hd
          · exact Finset.mem_of_mem_filter d hd
      have hdisj : Disjoint D1 D2 := by
        rw [hD1, hD2, Finset.disjoint_left]
        intro x hx1 hx2
        exact not_lt_of_ge (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
      rw [hDD, Finset.sum_union hdisj]
      simp

private theorem find_good_d_hbound3 {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hDnotzero : ∀ d ∈ D2, d ≠ 0) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
  apply le_trans hbound2
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  apply le_of_eq
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast hDnotzero d hd
  field_simp [hd0]

private theorem find_good_d_hDsumpos {A : Finset ℕ} {q : ℕ} {N : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))))
    (hDnotzero : ∀ d ∈ D2, d ≠ 0) (hlarge1 : 0 < log N)
    (hsumq : 1 / log N ≤ rec_sum_local A q) :
    0 < D2.sum (fun d ↦ (1 / d : ℚ)) := by
  refine Finset.sum_pos ?_ ?_
  · intro i hi
    rw [one_div_pos]
    exact_mod_cast Nat.pos_of_ne_zero (hDnotzero i hi)
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hempty2 :
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) = 0 := by
      rw [hempty, Finset.sum_empty]
    rw [hempty2] at hbound3
    have hpos : (0 : ℚ) < rec_sum_local A q / 2 := by
      refine div_pos ?_ zero_lt_two
      have : (0 : ℝ) < rec_sum_local A q := by
        refine lt_of_lt_of_le ?_ hsumq
        exact one_div_pos.mpr hlarge1
      exact_mod_cast this
    exact (not_le_of_gt hpos) hbound3

private theorem find_good_d_hfound0 {A : Finset ℕ} {q : ℕ} {N : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))))
    (hlarge1 : 0 < log N) (hsumq : 1 / log N ≤ rec_sum_local A q) :
    ∃ x ∈ D2,
      (rec_sum_local A q : ℚ) / 2 ≤
        (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) := by
  have hpos : (0 : ℚ) < rec_sum_local A q / 2 := by
    refine div_pos ?_ zero_lt_two
    have : (0 : ℝ) < rec_sum_local A q := by
      refine lt_of_lt_of_le ?_ hsumq
      exact one_div_pos.mpr hlarge1
    exact_mod_cast this
  rcases weighted_ph hpos (by
      intro d hd
      positivity) hbound3 with ⟨x, hx, hineq⟩
  exact ⟨x, hx, hineq⟩

private theorem find_good_d_hfound {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hfound0 :
      ∃ x ∈ D2,
        (rec_sum_local A q : ℚ) / 2 ≤
          (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)))
    (hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ))) :
    ∃ d ∈ D2,
      (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) := by
  rcases hfound0 with ⟨x, hx1, hx2⟩
  refine ⟨x, hx1, ?_⟩
  have hpos : (0 : ℚ) < 2 * D2.sum (fun d ↦ (1 / d : ℚ)) := by positivity
  refine (div_le_iff₀ hpos).2 ?_
  calc
    (rec_sum_local A q : ℚ) = 2 * ((rec_sum_local A q : ℚ) / 2) := by ring
    _ ≤ 2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n))) := by
      gcongr
    _ = (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) * (2 * D2.sum (fun d ↦ (1 / d : ℚ))) := by
      ring

private theorem find_good_d_hfound1 {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hfound :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) :
    ∃ d ∈ D2,
      (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
  rcases hfound with ⟨d, hd1, hd2⟩
  refine ⟨d, hd1, ?_⟩
  calc
    (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) =
        ((((rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ)))) : ℚ) : ℝ) := by
      simp [Rat.cast_sum]
    _ ≤ (((newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) : ℚ) : ℝ) := by
      exact_mod_cast hd2
    _ = (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
      simp [Rat.cast_sum]

private theorem find_good_d_hbound4 {C1 C : ℝ} {N k : ℕ} {y : ℝ} {D2 : Finset ℕ}
    (hC' : C1 = 1 / (C * 2)) (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hlarge1 : 0 < log N)
    (hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1) :
    D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
  calc
    D2.sum (fun d ↦ (1 / d : ℝ)) = D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp
    _ ≤ (C1 * |log N| / |log y|) ^ 1 := hrec2bound
    _ = C1 * log N ^ ((2 : ℝ) / k) := by
      have hy1 : 1 < y := by
        rw [hy, Real.one_lt_exp_iff]
        exact Real.rpow_pos_of_pos hlarge1 _
      rw [pow_one, abs_eq_self.mpr (le_of_lt hlarge1),
        abs_eq_self.mpr (le_of_lt (Real.log_pos hy1)),
        hy, Real.log_exp]
      rw [mul_div_assoc]
      have hdiv :
          log N / log N ^ ((1 : ℝ) - 2 / k) = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
        calc
          log N / log N ^ ((1 : ℝ) - 2 / k)
              = log N ^ (1 : ℝ) / log N ^ ((1 : ℝ) - 2 / k) := by rw [Real.rpow_one]
          _ = log N ^ ((1 : ℝ) - ((1 : ℝ) - 2 / k)) := by rw [← Real.rpow_sub hlarge1]
          _ = log N ^ ((2 : ℝ) / k) := by ring_nf
          _ = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
            rw [← Real.rpow_mul (le_of_lt hlarge1)]
            ring_nf
      simpa [Real.rpow_one] using congrArg (fun t => C1 * t) hdiv
    _ = log N ^ ((2 : ℝ) / k) / (C * 2) := by
      rw [mul_comm C1, ← mul_one_div, hC']
      ring

private theorem find_good_d_hfinal {C : ℝ} {A : Finset ℕ} {q N k d : ℕ}
    {D2 : Finset ℕ} {newLocal : ℕ → Finset ℕ}
    (hC : 0 < C) (hlarge1 : 0 < log N) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ)))
    (hfound1 :
      (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)))
    (hbound4 : D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2)) :
    C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
      (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
  have hsumq' : (0 : ℝ) < rec_sum_local A q := by
    refine lt_of_lt_of_le ?_ hsumq
    exact one_div_pos.mpr hlarge1
  have haux :
      C / log N ^ ((2 : ℝ) / k) ≤
        1 / (2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ)) := by
    have hbound4' :
        (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
      simpa using hbound4
    have hbound4'' :
        (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) * (C * 2) ≤ log N ^ ((2 : ℝ) / k) := by
      exact (le_div_iff₀ (mul_pos hC zero_lt_two)).mp hbound4'
    have hmul : 2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) ≤ log N ^ ((2 : ℝ) / k) / C := by
      refine (le_div_iff₀ hC).2 ?_
      nlinarith
    have hrecip :=
      one_div_le_one_div_of_le
        (show 0 < 2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) by
          exact mul_pos zero_lt_two (by exact_mod_cast hDsumpos))
        hmul
    simpa [one_div_div] using hrecip
  have hmul :
      (rec_sum_local A q : ℝ) * (C / log N ^ ((2 : ℝ) / k)) ≤
        (rec_sum_local A q : ℝ) *
          (1 / (2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ))) :=
    mul_le_mul_of_nonneg_left haux (le_of_lt hsumq')
  refine le_trans ?_ hfound1
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem find_good_d :
    ∃ c C : ℝ,
      0 < c ∧
        0 < C ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ M : ℝ,
              ∀ k : ℕ,
                ∀ A ⊆ range (N + 1),
                  0 < M →
                    M ≤ N →
                      1 < k →
                        (k : ℝ) ≤ c * log (log N) →
                          (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                            ∀ q ∈ ppowers_in_set A,
                              1 / log N ≤ rec_sum_local A q →
                                ∃ d : ℕ,
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d ∧
                                    ((ω d : ℝ) < (5 / log k) * log (log N)) ∧
                                      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
                                        ((local_part A q).filter
                                            (fun n ↦ q * d ∣ n ∧
                                              Nat.Coprime (q * d) (n / (q * d)))).sum
                                          (fun n ↦ (q * d / n : ℝ)) := by
  classical
  rcases useful_rec_bound with ⟨C1, hC1, hrec1⟩
  let C2 := max C1 2
  let c : ℝ := (1 / 2) / Real.log C2
  have hc : 0 < c := by
    simpa [c, C2] using find_good_d_hc C1 hC1
  let C : ℝ := 1 / (C1 * 2)
  have hC : 0 < C := by
    simpa [C] using find_good_d_hC C1 hC1
  have hC' : C1 = 1 / (C * 2) := by
    simpa [C] using find_good_d_hC' C1 hC1
  have hC2 : 1 < C2 := by
    dsimp [C2]
    exact find_good_d_hC2 C1
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards
    [ find_good_d_aux1
    , find_good_d_aux2
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , eventually_gt_atTop (0 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (16 : ℝ)) ] with
    N haux1 haux2 hlarge hlarge' hlarge'' M k A hAN hzM hMN h1k hkN hAreg q hq hsumq
  dsimp at hlarge
  have hlarge1 : 0 < log N := by
    exact find_good_d_hlarge1 hlarge
  have hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
    exact find_good_d_hlarge2 hlarge1 hlarge''
  let y : ℝ := Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  let u : ℝ := Real.exp (-log N ^ ((1 : ℝ) - 1 / k))
  have h1y : 1 < y := by
    simpa [y] using find_good_d_h1y (N := N) (k := k) hlarge1
  have hyN : y < N := by
    simpa [y] using find_good_d_hyN (N := N) (k := k) hlarge hlarge' h1k
  have h0k : (0 : ℝ) < k := by
    exact find_good_d_h0k h1k
  let D : Finset ℕ :=
    (range (N + 1)).filter
      (fun d : ℕ ↦
        (∀ r : ℕ,
            IsPrimePow r →
              r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
          M * u < q * d ∧ q * d ≤ N)
  specialize haux2 M k A hAN hzM hMN (le_of_lt h1k) hAreg q hq
  specialize haux1 M u y q A hAN hzM hMN (le_of_lt (Real.exp_pos _))
  let newLocal : ℕ → Finset ℕ := fun d ↦
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hlocal2 : local_part A q ⊆ D.biUnion newLocal := by
    exact find_good_d_hlocal2 (A := A) (q := q) D newLocal rfl haux2
  have hrecbound :
      rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hrecbound (A := A) (q := q) D newLocal rfl hlocal2
  have hDu : ∀ d ∈ D, M * u < q * d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : ∀ d ∈ D, d ≠ 0 := by
    exact find_good_d_hDnotzero hzM (by simpa [u] using Real.exp_pos _) hDu
  set ω0 : ℝ := (5 / log k) * log (log N) with hω0
  let D1 := D.filter (fun d ↦ ω0 ≤ (ω d : ℝ))
  have hrec2 := hrec1
  specialize hrec1 y k N D1 h1y hyN (le_of_lt h1k)
  have haux1D1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d := by
    intro d hd
    exact haux1 d (Finset.mem_of_mem_filter d hd)
  have hrec1bound :
      D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k := by
    apply hrec1
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2 := by
    exact
      find_good_d_hbound1 (C1 := C1) (c := c) (y := y) (ω0 := ω0) (N := N) (q := q) (k := k)
        (A := A) (D1 := D1) (newLocal := newLocal) hC1 (by simp [c, C2]) rfl hkN hlarge1
        hlarge2 h1k h0k hω0 hsumq (by
          intro d hd
          exact (Finset.mem_filter.mp hd).2) haux1D1 hrec1bound
  let D2 := D.filter (fun d ↦ (ω d : ℝ) < ω0)
  specialize hrec2 y 1 N D2 h1y hyN (le_rfl : 1 ≤ 1)
  have hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1 := by
    apply hrec2
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hbound2 (A := A) (q := q) (D := D) (D1 := D1) (D2 := D2)
      (newLocal := newLocal) rfl rfl hrecbound hbound1
  have hD2notzero : ∀ d ∈ D2, d ≠ 0 := by
    intro d hd
    exact hDnotzero d (Finset.mem_of_mem_filter d hd)
  have hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
    exact find_good_d_hbound3 (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hbound2 hD2notzero
  have hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ)) := by
    exact find_good_d_hDsumpos (A := A) (q := q) (N := N) (D2 := D2) (newLocal := newLocal)
      hbound3 hD2notzero hlarge1 hsumq
  have hfound0 :
      ∃ x ∈ D2,
        (rec_sum_local A q : ℚ) / 2 ≤
          (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) := by
    exact find_good_d_hfound0 (A := A) (q := q) (N := N) (D2 := D2) (newLocal := newLocal)
      hbound3 hlarge1 hsumq
  have hfound :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) := by
    exact find_good_d_hfound (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hfound0 hDsumpos
  have hfound1 :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    exact find_good_d_hfound1 (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hfound
  have hbound4 :
      D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
    exact find_good_d_hbound4 (C1 := C1) (C := C) (N := N) (k := k) (y := y) (D2 := D2) hC'
      rfl hlarge1 hrec2bound
  rcases hfound1 with ⟨d, hd, hfound1⟩
  rcases Finset.mem_filter.mp hd with ⟨hdD, hdω⟩
  rcases Finset.mem_filter.mp hdD with ⟨_hdRange, hdProps⟩
  have hfinal :
      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    exact find_good_d_hfinal (C := C) (A := A) (q := q) (N := N) (k := k) (d := d) (D2 := D2)
      (newLocal := newLocal) hC hlarge1 hsumq hDsumpos hfound1 hbound4
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa [u] using hdProps.2.1
  · simpa [hω0] using hdω
  · simpa [newLocal] using hfinal

private theorem find_good_x_hlarge0 {N : ℕ} (hlarge7 : log 2 < log (log (log N))) :
    0 < log (log (log N)) := by
  exact lt_trans (Real.log_pos one_lt_two) hlarge7

private theorem find_good_x_hlarge1 {N : ℕ} (hlarge0 : 0 < log (log (log N)))
    (hlarge4 : 4 * log (log (log N)) ≤ log (log N)) :
    0 < log (log N) := by
  have hpos : 0 < 4 * log (log (log N)) := by positivity
  exact lt_of_lt_of_le hpos hlarge4

private theorem find_good_x_hlarge3 {N : ℕ} (hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N) :
    1 ≤ log N := by
  refine le_trans ?_ hlarge6
  refine one_le_rpow one_le_two ?_
  norm_num

private theorem find_good_x_hlarge2 {N : ℕ} (hlarge3 : 1 ≤ log N) : 0 < log N := by
  exact lt_of_lt_of_le zero_lt_one hlarge3

private theorem find_good_x_h1k {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊)
    (hlarge0 : 0 < log (log (log N))) (_hlarge1 : 0 < log (log N))
    (hlarge4 : 4 * log (log (log N)) ≤ log (log N)) :
    1 < k := by
  have htwo : (2 : ℝ) < (k : ℝ) + 1 := by
    calc
      (2 : ℝ) ≤ (log (log N)) / (2 * log (log (log N))) := by
        rw [_root_.le_div_iff₀ (show 0 < 2 * log (log (log N)) by positivity), ← mul_assoc]
        norm_num
        exact hlarge4
      _ < (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one ((log (log N)) / (2 * log (log (log N))))
      _ = (k : ℝ) + 1 := by rw [hk]
  have htwo_nat : 2 < k + 1 := by
    exact_mod_cast htwo
  exact Nat.lt_of_succ_lt_succ htwo_nat

private theorem find_good_x_hkc {N k : ℕ} {c : ℝ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (hc : 0 < c)
    (hlarge5 : 1 / c / 2 ≤ log (log (log N))) (hlarge0 : 0 < log (log (log N)))
    (hlarge1 : 0 < log (log N)) :
    (k : ℝ) ≤ c * log (log N) := by
  calc
    (k : ℝ) = (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) := by rw [hk]
    _ ≤ (log (log N)) / (2 * log (log (log N))) := by
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        positivity)
    _ ≤ c * log (log N) := by
      have haux : 1 / c ≤ 2 * log (log (log N)) := by
        have hmul := mul_le_mul_of_nonneg_left hlarge5 (show (0 : ℝ) ≤ 2 by positivity)
        calc
          1 / c = 2 * (1 / c / 2) := by ring
          _ ≤ 2 * log (log (log N)) := hmul
      have hinv : 1 / (2 * log (log (log N))) ≤ c := by
        exact (one_div_le (show 0 < 2 * log (log (log N)) by positivity) hc).2 haux
      rw [div_eq_mul_one_div, mul_comm c]
      exact mul_le_mul_of_nonneg_left hinv (le_of_lt hlarge1)

private theorem find_good_x_hlogNk {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (h1k : 1 < k)
    (hlarge7 : log 2 < log (log (log N))) (hlarge1 : 0 < log (log N))
    (hlarge2 : 0 < log N) (hlarge3 : 1 ≤ log N) :
    2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
  have hlarge0 : 0 < log (log (log N)) := by
    exact lt_trans (Real.log_pos one_lt_two) hlarge7
  let u : ℝ := log (log (log N)) / log (log N)
  have hpowpos : 0 < log N ^ u := by
    exact Real.rpow_pos_of_pos hlarge2 _
  have hmid : (2 : ℝ) < log N ^ u := by
    rw [← Real.log_lt_log_iff zero_lt_two hpowpos, Real.log_rpow hlarge2]
    dsimp [u]
    have hmul :
        log (log (log N)) / log (log N) * log (log N) = log (log (log N)) := by
      field_simp [ne_of_gt hlarge1]
    rw [hmul]
    exact hlarge7
  have hlt2 : 2 * log N ^ u < log N ^ (2 * u) := by
    calc
      2 * log N ^ u < log N ^ u * log N ^ u := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
          mul_lt_mul_of_pos_right hmid hpowpos
      _ = log N ^ (u + u) := by
        rw [← Real.rpow_add hlarge2]
      _ = log N ^ (2 * u) := by ring_nf
  have hexp_le : 2 * log (log (log N)) / log (log N) ≤ (1 : ℝ) / k := by
    rw [le_one_div (show 0 < 2 * log (log (log N)) / log (log N) by
      refine div_pos ?_ hlarge1
      exact mul_pos zero_lt_two hlarge0)]
    · rw [one_div_div]
      rw [hk]
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        exact mul_nonneg zero_le_two (le_of_lt hlarge0))
    · exact_mod_cast (lt_trans zero_lt_one h1k)
  have hu_eq : log N ^ u = log (log N) := by
    calc
      log N ^ u = Real.exp (Real.log (log N) * u) := by
        rw [Real.rpow_def_of_pos hlarge2]
      _ = Real.exp (log (log (log N))) := by
        dsimp [u]
        congr 1
        field_simp [ne_of_gt hlarge1]
      _ = log (log N) := by
        rw [Real.exp_log hlarge1]
  have hu2_eq : 2 * u = 2 * log (log (log N)) / log (log N) := by
    dsimp [u]
    field_simp [ne_of_gt hlarge1]
  calc
    2 * log (log N) = 2 * (log N ^ u) := by rw [hu_eq]
    _ < log N ^ (2 * u) := hlt2
    _ = log N ^ (2 * log (log (log N)) / log (log N)) := by rw [hu2_eq]
    _ ≤ log N ^ ((1 : ℝ) / k) := by
      exact Real.rpow_le_rpow_of_exponent_le hlarge3 hexp_le

private theorem find_good_x_hA_I {N : ℕ} {A : Finset ℕ} {I : Finset ℤ}
    (hA : A ⊆ range (N + 1)) :
    A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x) ⊆ range (N + 1) := by
  exact subset_trans (Finset.filter_subset _ _) hA

private theorem find_good_x_hA_I' {N k : ℕ} {M : ℝ} {A : Finset ℕ} {I : Finset ℤ}
    {A_I : Finset ℕ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ)) (hreg : arith_regular N A)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
  intro n hn
  rw [hA_I_def] at hn
  refine ⟨hMA n (Finset.mem_of_mem_filter n hn), ?_⟩
  rw [arith_regular] at hreg
  exact lt_of_le_of_lt (hreg n (Finset.mem_of_mem_filter n hn)).2 hlogNk

private theorem find_good_x_hqA_I {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hq : q ∈ ppowers_in_set A) (_h0A : 0 ∉ A)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge2 : 0 < log N) :
    q ∈ ppowers_in_set A_I := by
  rcases mem_ppowers_in_set.mp hq with ⟨hqpp, _⟩
  refine mem_ppowers_in_set.mpr ⟨hqpp, ?_⟩
  by_contra hlocalempty
  rw [Finset.not_nonempty_iff_eq_empty] at hlocalempty
  rw [rec_sum_local, hlocalempty, Finset.sum_empty, Rat.cast_zero] at hqlocal
  have hpos : 0 < (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) := by
    refine one_div_pos.mpr ?_
    positivity
  linarith

private theorem find_good_x_hqlocal2 {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N) (hlarge2 : 0 < log N)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q) :
    1 / log N ≤ rec_sum_local A_I q := by
  have hpow99 : (2 : ℝ) ≤ log N ^ ((99 : ℝ) / 100) := by
    have hpow99' : (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) ≤ log N ^ ((99 : ℝ) / 100) := by
      exact Real.rpow_le_rpow (by positivity) hlarge6 (by positivity)
    calc
      (2 : ℝ) = (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) := by
        rw [← Real.rpow_mul zero_le_two]
        norm_num
      _ ≤ log N ^ ((99 : ℝ) / 100) := hpow99'
  have hden : 2 * log N ^ ((1 : ℝ) / 100) ≤ log N := by
    calc
      2 * log N ^ ((1 : ℝ) / 100)
          ≤ log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100) := by
            exact mul_le_mul_of_nonneg_right hpow99 (by positivity)
      _ = log N := by
        calc
          log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100)
              = log N ^ (((99 : ℝ) / 100) + ((1 : ℝ) / 100)) := by
                  rw [← Real.rpow_add hlarge2]
          _ = log N := by
            norm_num [Real.rpow_one]
  have hdenpos : 0 < 2 * log N ^ ((1 : ℝ) / 100) := by positivity
  exact le_trans (one_div_le_one_div_of_le hdenpos hden) hqlocal

private theorem find_good_x_hsum {N q k d : ℕ} {M C : ℝ} {A A_I A_I' A_I'' : Finset ℕ}
    {I : Finset ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hA_I : A_I ⊆ range (N + 1)) (hA_I_subA : A_I ⊆ A) (hq : q ∈ ppowers_in_set A)
    (h0A : 0 ∉ A) (hC : 0 < C)
    (hreg : arith_regular N A)
    (hlargerecbound :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤ rec_sum A_I'' →
        (∀ n ∈ A_I'', (1 - 2 / 99) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
          (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
            (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k))
    (hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N))
    (hgood2 : (ω d : ℝ) < (5 / log k) * log (log N))
    (hgood3 :
      C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) ≤
        ((local_part A_I q).filter
            (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
          (fun n ↦ (q * d / n : ℝ)))
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N) :
    ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
  let _ := M
  let _ := I
  have hqpp : IsPrimePow q := (mem_ppowers_in_set.mp hq).1
  have hmain :
      (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
        (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    refine hlargerecbound ?_ ?_
    · calc
        log N ^ (-((2 : ℝ) / 99) / 2)
            ≤ C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := hlogNk2
        _ ≤ C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) := by
          have hmul : C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) ≤ C * rec_sum_local A_I q := by
            exact mul_le_mul_of_nonneg_left hqlocal (le_of_lt hC)
          exact div_le_div_of_nonneg_right hmul (by
            exact Real.rpow_nonneg (le_of_lt hlarge2) ((2 : ℝ) / k))
        _ ≤
            ((local_part A_I q).filter
                (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
              (fun n ↦ (q * d / n : ℝ)) := hgood3
        _ ≤ rec_sum A_I'' := by
          rw [rec_sum, Rat.cast_sum]
          push_cast
          let g : ℕ → ℕ := fun n ↦ n / (q * d)
          refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
          · intro b hb
            exact one_div_nonneg.2 (Nat.cast_nonneg b)
          · intro a ha
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            rw [hA_I''_def, Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_range]
              exact lt_of_le_of_lt (Nat.div_le_self a (q * d))
                (Finset.mem_range.mp (hA_I ha_local.1))
            · refine ⟨a, ?_, ?_, ?_⟩
              · rw [hA_I'_def, Finset.mem_filter]
                exact ⟨ha_local.1, ha'.2.1⟩
              · dsimp [g]
                exact Nat.div_mul_cancel ha'.2.1
              · simpa [g, Nat.coprime_comm] using ha'.2.2
          · intro a ha b hb hab
            have ha' := Finset.mem_filter.mp ha
            have hb' := Finset.mem_filter.mp hb
            calc
              a = (q * d) * g a := by
                simp [g, Nat.mul_div_cancel' ha'.2.1]
              _ = (q * d) * g b := by rw [hab]
              _ = b := by
                simp [g, Nat.mul_div_cancel' hb'.2.1]
          · intro a ha
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            have haA : a ∈ A := hA_I_subA ha_local.1
            have ha0 : a ≠ 0 := by
              intro hzero
              exact h0A (hzero ▸ haA)
            have hqd0 : q * d ≠ 0 := by
              intro hzero
              have : a = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ ha'.2.1)
              exact ha0 this
            have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast hqd0
            have hcast : (g a : ℝ) = (a : ℝ) / (q * d : ℕ) := by
              dsimp [g]
              rw [Nat.cast_div ha'.2.1 hqd0']
            rw [hcast, one_div_div, Nat.cast_mul]
    · intro n hn
      rw [hA_I''_def, Finset.mem_filter] at hn
      rcases hn.2 with ⟨m, hm1, hm2, hm3⟩
      rw [hA_I'_def, Finset.mem_filter] at hm1
      have hmA : m ∈ A := hA_I_subA hm1.1
      have hm0 : m ≠ 0 := by
        intro hzero
        exact h0A (hzero ▸ hmA)
      have hqdpos : 0 < q * d := by
        refine Nat.pos_iff_ne_zero.mpr ?_
        intro hzero
        have : m = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ hm1.2)
        exact hm0 this
      have hmdiv : m / (q * d) = n := by
        apply Nat.div_eq_of_eq_mul_right hqdpos
        simpa [mul_comm] using hm2.symm
      have hmreg := hreg m hmA
      refine ⟨?_, ?_⟩
      · calc
          (1 - 2 / 99) * log (log N) ≤ (ω m : ℝ) - (1 + 5 / log k * log (log N)) := by
            rw [le_sub_iff_add_le]
            exact le_trans hNlogk hmreg.1
          _ ≤ (ω m : ℝ) - ω (q * d) := by
            apply sub_le_sub_left
            calc
              (ω (q * d) : ℝ) ≤ 1 + (ω d : ℝ) := by
                exact_mod_cast omega_mul_ppower (a := d) hqpp
              _ ≤ 1 + (5 / log k) * log (log N) := by
                linarith [le_of_lt hgood2]
          _ ≤ ω (m / (q * d)) := sub_le_omega_div hm1.2
          _ = ω n := by rw [hmdiv]
      · calc
          (ω n : ℝ) = ω (m / (q * d)) := by rw [← hmdiv]
          _ ≤ ω m := by exact_mod_cast omega_div_le hm1.2
          _ ≤ 2 * log (log N) := hmreg.2
  calc
    ((35 : ℝ) / 100) * log (log N)
        ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) := by
          have hmul := mul_le_mul_of_nonneg_right useful_exp_estimate (le_of_lt hlarge1)
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := hmain

private theorem find_good_x_hI'ne {N q d : ℕ} {A_I' A_I'' : Finset ℕ} {I I' : Finset ℤ}
    (hA_I'_witness : ∀ n ∈ A_I', ∃ x ∈ I, (n : ℤ) ∣ x)
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x))
    (hsum : ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlarge1 : 0 < log (log N)) :
    I'.Nonempty := by
  rw [hI'_def, Finset.filter_nonempty_iff]
  have hA_I'_ne : A_I'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    rw [Finset.eq_empty_iff_forall_notMem] at hem
    have hA_I''_empty : A_I'' = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro h
      rw [hA_I''_def, Finset.filter_nonempty_iff] at h
      rcases h with ⟨a, ha1, n, hn1, hn2⟩
      exact hem n hn1
    have hpp_empty : ppowers_in_set A_I'' = ∅ := by
      rw [hA_I''_empty]
      exact ppowers_in_set_empty
    rw [hpp_empty, Finset.sum_empty, ← not_lt] at hsum
    have hpos : 0 < ((35 : ℝ) / 100) * log (log N) := by positivity
    exact (hsum hpos).elim
  obtain ⟨n, hn⟩ := hA_I'_ne
  rcases hA_I'_witness n hn with ⟨x, hxI, hnx⟩
  exact ⟨x, hxI, n, hn, hnx⟩

private theorem find_good_x_hI'single {N q k d : ℕ} {M t : ℝ} {A A_I A_I' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') (hI :
      I =
        Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (h0M : 0 < M) (hMN : M ≤ N) (_h0A : 0 ∉ A)
    (hgood1 : M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ y ∈ I', x = y := by
  intro y hy
  by_contra hxy
  have hx' := hx
  rw [hI'_def, Finset.mem_filter] at hx'
  rcases hx'.2 with ⟨mx, hmx, hmx'⟩
  have hmxqd : ((q * d : ℤ) ∣ (mx : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmx
    exact_mod_cast hmx.2
  have hdx : ((q * d : ℤ) ∣ x) := dvd_trans hmxqd hmx'
  have hy' := hy
  rw [hI'_def, Finset.mem_filter] at hy'
  rcases hy'.2 with ⟨my, hmy, hmy'⟩
  have hmyqd : ((q * d : ℤ) ∣ (my : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmy
    exact_mod_cast hmy.2
  have hdy : ((q * d : ℤ) ∣ y) := dvd_trans hmyqd hmy'
  let z : ℤ := |x - y|
  have hdz : ((q * d : ℤ) ∣ z) := by
    dsimp [z]
    rw [dvd_abs]
    exact dvd_sub hdx hdy
  have hzs :
      (z : ℝ) ≤ (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
    let w : ℝ := M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))
    let b : ℤ := ⌊t + w / 2⌋
    let a : ℤ := ⌈t - w / 2⌉
    have hIab : I = Icc a b := by
      simpa [a, b, w] using hI
    have hIx : x ∈ Icc a b := by
      simpa [hIab] using hx'.1
    have hIy : y ∈ Icc a b := by
      simpa [hIab] using hy'.1
    calc
      (z : ℝ) ≤ b - a := by
        simpa [z, Int.cast_abs] using (two_in_Icc hIx hIy)
      _ ≤ w / 2 + w / 2 := by
        simpa [a, b, w] using (floor_sub_ceil (z := t) (x := w / 2) (y := w / 2))
      _ = w := by ring
      _ = (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by rfl
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le h0M hMN
  have hpow_bound :
      (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    calc
      (N : ℝ) ^ (-(2 : ℝ) / log (log N))
          = Real.exp (log N * (-(2 : ℝ) / log (log N))) := by
              rw [Real.exp_mul, Real.exp_log hNpos]
      _ ≤ Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
        refine Real.exp_le_exp.mpr ?_
        have hloglog_bound : log (log N) ≤ 2 * log N ^ ((1 : ℝ) / k) := by
          have haux1 : log (log N) ≤ 2 * log (log N) := by linarith
          have haux2 : log (log N) ≤ log N ^ ((1 : ℝ) / k) := by
            exact le_trans haux1 (le_of_lt hlogNk)
          linarith
        have hdiv : 1 ≤ 2 * log N ^ ((1 : ℝ) / k) / log (log N) := by
          rw [le_div_iff₀ hlarge1]
          simpa using hloglog_bound
        have hsplit : log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k) = log N := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k)
                = log N ^ (((1 : ℝ) - 1 / k) + ((1 : ℝ) / k)) := by
                    rw [← Real.rpow_add hlarge2]
            _ = log N ^ (1 : ℝ) := by ring_nf
            _ = log N := by rw [Real.rpow_one]
        have hpow_main :
            log N ^ ((1 : ℝ) - 1 / k) ≤ 2 * log N / log (log N) := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) ≤
                log N ^ ((1 : ℝ) - 1 / k) * (2 * log N ^ ((1 : ℝ) / k) / log (log N)) := by
                  exact le_mul_of_one_le_right (by positivity) hdiv
            _ = (2 * (log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k))) / log (log N) := by ring
            _ = 2 * log N / log (log N) := by rw [hsplit]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using neg_le_neg hpow_main
  have hwidth_bound :
      M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    exact mul_le_mul_of_nonneg_left hpow_bound (le_of_lt h0M)
  have hzpos : 0 < z := by
    dsimp [z]
    exact abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hqdlez : ((q * d : ℤ)) ≤ z := by
    have hqdleabs : ((q * d : ℤ)) ≤ |z| := Int.le_abs_of_dvd (ne_of_gt hzpos) hdz
    simpa [abs_of_nonneg (le_of_lt hzpos)] using hqdleabs
  have hqdz : (q : ℝ) * d ≤ z := by
    exact_mod_cast hqdlez
  exact (not_le_of_gt hgood1) (le_trans hqdz (le_trans hzs hwidth_bound))

private theorem find_good_x_hxI {A_I' : Finset ℕ} {I I' : Finset ℤ} {x : ℤ}
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') :
    x ∈ I := by
  rw [hI'_def] at hx
  exact Finset.mem_of_mem_filter x hx

private theorem find_good_x_hqx {q d : ℕ} {A_I A_I' : Finset ℕ} {I I' : Finset ℤ} {x : ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') :
    (q : ℤ) ∣ x := by
  rw [hI'_def] at hx
  rcases (Finset.mem_filter.mp hx).2 with ⟨n, hn, hnx⟩
  rw [hA_I'_def] at hn
  have hqdvdqd : (q : ℤ) ∣ (q * d : ℤ) := ⟨d, by simp⟩
  have hqdvdn_nat : q * d ∣ n := (Finset.mem_filter.mp hn).2
  have hqdvdn : ((q * d : ℤ) ∣ (n : ℤ)) := by
    rcases hqdvdn_nat with ⟨m, rfl⟩
    refine ⟨m, by simp [mul_assoc, mul_left_comm, mul_comm]⟩
  exact dvd_trans hqdvdqd (dvd_trans hqdvdn hnx)

private theorem find_good_x_hpp {N q d : ℕ} {A A_I A_I' A_I'' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (_hx : x ∈ I') (h0A : 0 ∉ A) (hI'single : ∀ y ∈ I', x = y) :
    ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
  intro r hr
  rw [ppowers_in_set, Finset.mem_biUnion] at hr
  rcases hr with ⟨a, ha, hr⟩
  rw [Finset.mem_filter] at hr
  rw [hA_I''_def] at ha
  rw [Finset.mem_filter]
  rw [Finset.mem_filter] at ha
  rcases ha.2 with ⟨m, hm1, hm2⟩
  have hm1' := hm1
  rw [hA_I'_def, Finset.mem_filter] at hm1
  rw [hA_I_def, Finset.mem_filter] at hm1
  rcases hm1.1.2 with ⟨y, hy1, hy2⟩
  have hyI' : y ∈ I' := by
    rw [hI'_def, Finset.mem_filter]
    exact ⟨hy1, m, hm1', hy2⟩
  have hyx : x = y := hI'single y hyI'
  rw [hyx, ppowers_in_set, Finset.mem_biUnion]
  refine ⟨?_, ?_⟩
  · refine ⟨m, hm1.1.1, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hr.2.1, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [← hm2.1]
        exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
      · intro h0m
        rw [h0m] at hm1
        exact h0A hm1.1.1
    · rw [← hm2.1, mul_comm, Nat.mul_div_assoc]
      · refine Nat.Coprime.mul_right ?_ hr.2.2
        exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hr.1) hm2.2
      · exact Nat.dvd_of_mem_divisors hr.1
  · refine dvd_trans ?_ hy2
    have hrdvdm : r ∣ m := by
      rw [← hm2.1]
      exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
    exact_mod_cast hrdvdm

private theorem find_good_x_hfinal {N : ℕ} {A A_I'' : Finset ℕ} {x : ℤ}
    (hsum : ((35 : ℝ) / 100) * log (log N) ≤
      (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hpp : ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)) :
    ((35 : ℝ) / 100) * log (log N) ≤
      ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)).sum (fun r ↦ (1 / r : ℝ)) := by
  exact le_trans hsum <|
    Finset.sum_le_sum_of_subset_of_nonneg hpp (by
      intro i _ _
      positivity)

theorem find_good_x :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ A ⊆ range (N + 1),
          0 < M →
            M ≤ N →
              0 ∉ A →
                (∀ n ∈ A, M ≤ (n : ℝ)) →
                  arith_regular N A →
                    ∀ t : ℝ, ∀ I : Finset ℤ, ∀ q ∈ ppowers_in_set A,
                      I =
                          Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
                            ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ →
                        (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
                            rec_sum_local (A.filter (fun n ↦ ∃ x ∈ I, (n : ℤ) ∣ x)) q →
                          ∃ xq, xq ∈ I ∧ (q : ℤ) ∣ xq ∧
                              ((35 : ℝ) / 100) * log (log N) ≤
                                ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ xq)).sum
                                  (fun r : ℕ ↦ (1 / r : ℝ)) := by
  classical
  obtain ⟨c, C, hc, hC, hgoodd⟩ := find_good_d
  have heasy1 : 0 < ((2 : ℝ) / 99) := by
    norm_num
  have heasy2 : ((2 : ℝ) / 99) < 1 / 2 := by
    norm_num
  obtain hlargerecbound := rec_qsum_lower_bound ((2 : ℝ) / 99) heasy1 heasy2
  filter_upwards [hgoodd, hlargerecbound, another_large_N c C hc hC] with
    N hgooddN hlargerecbound hlargegroup M A hA h0M hMN h0A hMA hreg t I q hq hI hqlocal
  have hlarge4 : 4 * log (log (log N)) ≤ log (log N) := by
    exact hlargegroup.2.2.1
  have hlarge5 : 1 / c / 2 ≤ log (log (log N)) := by
    exact hlargegroup.1
  have hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N := by
    exact hlargegroup.2.1
  have hlarge7 : log 2 < log (log (log N)) := by
    exact hlargegroup.2.2.2.1
  have hlarge0 : 0 < log (log (log N)) := by
    exact find_good_x_hlarge0 hlarge7
  have hlarge1 : 0 < log (log N) := by
    exact find_good_x_hlarge1 hlarge0 hlarge4
  have hlarge3 : 1 ≤ log N := by
    exact find_good_x_hlarge3 hlarge6
  have hlarge2 : 0 < log N := by
    exact find_good_x_hlarge2 hlarge3
  set A_I : Finset ℕ := A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x) with hA_I_def
  set k : ℕ := ⌊(log (log N)) / (2 * log (log (log N)))⌋₊ with hk
  have h1k : 1 < k := by
    simpa [hk] using find_good_x_h1k (N := N) (k := k) hk hlarge0 hlarge1 hlarge4
  have hkc : (k : ℝ) ≤ c * log (log N) := by
    simpa [hk] using find_good_x_hkc (N := N) (k := k) (c := c) hk hc hlarge5 hlarge0 hlarge1
  have hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
    simpa [hk] using find_good_x_hlogNk (N := N) (k := k) hk h1k hlarge7 hlarge1 hlarge2 hlarge3
  have hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := by
    simpa [hk] using hlargegroup.2.2.2.2.1
  have hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N) := by
    simpa [hk] using hlargegroup.2.2.2.2.2
  have hA_I : A_I ⊆ range (N + 1) := by
    simpa [hA_I_def] using find_good_x_hA_I (N := N) (A := A) (I := I) hA
  have hA_I' : ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
    simpa [hA_I_def] using
      find_good_x_hA_I' (N := N) (k := k) (M := M) (A := A) (I := I) (A_I := A_I) hA_I_def
        hMA hreg hlogNk
  have hqA_I : q ∈ ppowers_in_set A_I := by
    simpa [hA_I_def] using
      find_good_x_hqA_I (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def hq h0A
        hqlocal hlarge2
  have hqlocal2 : 1 / log N ≤ rec_sum_local A_I q := by
    simpa [hA_I_def] using
      find_good_x_hqlocal2 (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def
        hlarge6 hlarge2 hqlocal
  specialize hgooddN M k A_I hA_I h0M hMN h1k hkc hA_I' q hqA_I hqlocal2
  rcases hgooddN with ⟨d, hgood1, hgood2, hgood3⟩
  set A_I' : Finset ℕ := A_I.filter (fun n : ℕ ↦ q * d ∣ n) with hA_I'_def
  set A_I'' : Finset ℕ :=
    (range (N + 1)).filter
      (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)) with hA_I''_def
  have hsum :
      ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    exact
      find_good_x_hsum (N := N) (q := q) (k := k) (d := d) (M := M) (C := C) (A := A)
        (A_I := A_I) (A_I' := A_I') (A_I'' := A_I'') (I := I) hA_I'_def hA_I''_def hA_I
        (by
          intro n hn
          rw [hA_I_def, Finset.mem_filter] at hn
          exact hn.1)
        hq
        h0A hC hreg
        (by
          intro hrec hreg'
          exact hlargerecbound A_I'' hrec hreg')
        hlogNk2 hNlogk hgood2 hgood3 hqlocal hlarge1 hlarge2
  set I' : Finset ℤ := I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x) with hI'_def
  have hI'ne : I'.Nonempty := by
    exact
      find_good_x_hI'ne (N := N) (q := q) (d := d) (A_I' := A_I') (A_I'' := A_I'')
        (I := I) (I' := I') (by
          intro n hn
          rw [hA_I'_def, Finset.mem_filter] at hn
          rcases (Finset.mem_filter.mp hn.1).2 with ⟨x, hxI, hnx⟩
          exact ⟨x, hxI, hnx⟩) hA_I''_def hI'_def hsum hlarge1
  obtain ⟨x, hx⟩ := hI'ne
  have hI'single : ∀ y ∈ I', x = y := by
    exact
      find_good_x_hI'single (N := N) (q := q) (k := k) (d := d) (M := M) (t := t) (A := A)
        (A_I := A_I) (A_I' := A_I') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hI'_def
        hx hI h0M hMN h0A hgood1 hlarge1 hlarge2 hlogNk
  have hxI : x ∈ I := by
    exact find_good_x_hxI (A_I' := A_I') (I := I) (I' := I') (x := x) hI'_def hx
  have hqx : (q : ℤ) ∣ x := by
    exact find_good_x_hqx (q := q) (d := d) (A_I := A_I) (A_I' := A_I') (I := I) (I' := I')
      (x := x) hA_I'_def hI'_def hx
  have hpp :
      ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
    exact
      find_good_x_hpp (N := N) (q := q) (d := d) (A := A) (A_I := A_I) (A_I' := A_I')
        (A_I'' := A_I'') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hA_I''_def hI'_def
        hx h0A hI'single
  have hfinal :
      ((35 : ℝ) / 100) * log (log N) ≤
        ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)).sum (fun r ↦ (1 / r : ℝ)) := by
    exact find_good_x_hfinal (N := N) (A := A) (A_I'' := A_I'') (x := x) hsum hpp
  exact ⟨x, hxI, hqx, hfinal⟩


/-! ## From src4/Fourier.lean -/

open scoped BigOperators
open Real Finset

noncomputable section
attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/fourier.lean`.

Mathlib 4 already provides much of the analytic API used here, especially the complex
exponential/trigonometric identities around:

* `Complex.exp_int_mul_two_pi_mul_I`
* `Complex.exp_ofReal_mul_I_re`
* `Complex.norm_exp_ofReal_mul_I`
* `Complex.two_cos`
-/

/-- Lean 3 used a local notation `[A]` for `A.lcm id`; we use an explicit alias in Lean 4. -/
abbrev lcmA (A : Finset ℕ) : ℕ := A.lcm id

/-- Def 4.1 -/
def integer_count (A : Finset ℕ) (k : ℕ) : ℕ := by
  classical
  exact (A.powerset.filter fun S => ∃ d : ℤ, rec_sum S * k = d).card

/-- Useful for def 4.2 and in other statements. -/
def valid_sum_range (t : ℕ) : Finset ℤ :=
  Finset.Ioc ((-(t : ℤ)) / 2) ((t : ℤ) / 2)

/-- Implementation lemma. -/
lemma dumb_subtraction_thing (t : ℕ) : ((t : ℤ) / 2 - -(t : ℤ) / 2) = t := by
  omega

lemma card_valid_sum_range (t : ℕ) : (valid_sum_range t).card = t := by
  rw [valid_sum_range, Int.card_Ioc, dumb_subtraction_thing]
  simp

lemma mem_valid_sum_range (t : ℕ) (h : ℤ) :
    h ∈ valid_sum_range t ↔ (-(t : ℤ)) / 2 < h ∧ h ≤ (t : ℤ) / 2 := by
  simp [valid_sum_range]

lemma of_mem_valid_sum_range {t : ℕ} {h : ℤ} :
    h ∈ valid_sum_range t → |(h : ℝ)| ≤ (t : ℝ) / 2 := by
  rw [mem_valid_sum_range, and_imp, Int.ediv_lt_iff_lt_mul zero_lt_two,
    Int.le_ediv_iff_mul_le zero_lt_two]
  intro h₁ h₂
  have h₁r : (-(t : ℝ)) < (h : ℝ) * 2 := by
    exact_mod_cast h₁
  have h₂r : (h : ℝ) * 2 ≤ (t : ℝ) := by
    exact_mod_cast h₂
  refine abs_le.mpr ?_
  constructor <;> linarith

lemma zero_mem_valid_sum_range {t : ℕ} (ht : t ≠ 0) : (0 : ℤ) ∈ valid_sum_range t := by
  rw [mem_valid_sum_range]
  have ht' : (0 : ℤ) < t := by
    exact_mod_cast Nat.pos_of_ne_zero ht
  constructor
  · omega
  · positivity

lemma lcm_ne_zero_of_zero_not_mem {A : Finset ℕ} (hA : 0 ∉ A) : A.lcm id ≠ 0 := by
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  rcases h with ⟨x, hx, hx0⟩
  subst hx0
  exact hA hx

/-- Def 4.2. -/
def j (A : Finset ℕ) : Finset ℤ :=
  (valid_sum_range (A.lcm id)).erase 0

lemma mem_j (A : Finset ℕ) (h : ℤ) :
    h ∈ j A ↔
      h ≠ 0 ∧
        (-((A.lcm id : ℕ) : ℤ)) / 2 < h ∧ h ≤ ((A.lcm id : ℕ) : ℤ) / 2 := by
  simp [j, mem_valid_sum_range]

lemma bound_of_mem_j (A : Finset ℕ) (h : ℤ) (h' : h ∈ j A) :
    |(h : ℝ)| ≤ ((A.lcm id : ℕ) : ℝ) / 2 := by
  rw [j, Finset.mem_erase] at h'
  simpa using of_mem_valid_sum_range h'.2

/-- Def 4.3. -/
def cos_prod (B : Finset ℕ) (t : ℤ) : ℝ :=
  B.prod fun n => |Real.cos (Real.pi * t / n)|

lemma cos_prod_nonneg {B : Finset ℕ} {t : ℤ} : 0 ≤ cos_prod B t := by
  exact Finset.prod_nonneg fun _ _ => abs_nonneg _

lemma cos_prod_le_one {B : Finset ℕ} {t : ℤ} : cos_prod B t ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_
  · intro _ _
    exact abs_nonneg _
  · intro _ _
    exact abs_cos_le_one _

/-- Def 4.4 part one. -/
def major_arc_at (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℤ) : Finset ℤ :=
  (j A).filter fun h => |(h : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k)

lemma mem_major_arc_at {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (i : ℤ) :
    i ∈ major_arc_at A k K t ↔
      i ∈ j A ∧ |(i : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k) := by
  simp [major_arc_at]

lemma major_arc_at_of_neg {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hk : k ≠ 0) (hK : K < 0) (t : ℤ) :
    major_arc_at A k K t = ∅ := by
  ext i
  constructor
  · intro hi
    have hden : 0 < 2 * (k : ℝ) := by
      positivity
    have hneg : K / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos hK hden
    rw [mem_major_arc_at] at hi
    exfalso
    have habs : 0 ≤ |(i : ℝ) - t * (A.lcm id) / k| := abs_nonneg _
    linarith
  · intro hi
    exact False.elim (Finset.notMem_empty i hi)

/-- Def 4.4 part two. -/
def major_arc (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ := by
  classical
  exact (j A).filter fun h => ∃ t : ℤ, h ∈ major_arc_at A k K t

def e (x : ℝ) : ℂ :=
  Complex.exp (x * (2 * Real.pi * Complex.I))

lemma e_add {x y : ℝ} : e (x + y) = e x * e y := by
  simp [e, add_mul, Complex.exp_add, mul_add, mul_left_comm, mul_comm]

lemma e_int (z : ℤ) : e z = 1 := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I z

@[simp] lemma e_nat (n : ℕ) : e n = 1 := by
  simpa using e_int (n : ℤ)

@[simp] lemma e_zero : e 0 = 1 := by
  simpa using e_nat 0

lemma e_sum {ι : Type*} {s : Finset ι} (f : ι → ℝ) :
    e (s.sum f) = s.prod fun i => e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [e]
  | @insert a s ha hs =>
      simp [ha, e_add, hs]

lemma e_half_re {x : ℝ} : (e (x / 2)).re = Real.cos (x * Real.pi) := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm, two_mul] using
    Complex.exp_ofReal_mul_I_re (x * Real.pi)

lemma norm_e {x : ℝ} : ‖e x‖ = 1 := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using
    Complex.norm_exp_ofReal_mul_I (x * (2 * Real.pi))

lemma mem_major_arc_at' {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (hk : k ≠ 0) (i : ℤ) :
    i ∈ major_arc_at A k K t ↔ i ∈ j A ∧ (|i * k - t * lcmA A| : ℝ) ≤ K / 2 := by
  rw [mem_major_arc_at]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have habs :
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ) = (|i * k - t * lcmA A| : ℝ) := by
    calc
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ)
          = |(i : ℝ) - t * (lcmA A : ℝ) / k| * |(k : ℝ)| := by
              rw [abs_of_pos hkpos]
      _ = |((i : ℝ) - t * (lcmA A : ℝ) / k) * k| := by
            rw [← abs_mul]
      _ = |((i * (k : ℤ) - t * (lcmA A : ℤ) : ℤ) : ℝ)| := by
            congr 1
            field_simp [hk0]
            push_cast
            ring
      _ = (|i * (k : ℤ) - t * (lcmA A : ℤ)| : ℝ) := by
            simp
  have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
    field_simp [hk0]
  have hmuldiv : (K / (2 * (k : ℝ))) * (k : ℝ) = K / 2 := by
    field_simp [hk0]
  constructor
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hK hkpos.le
    rwa [habs, hmuldiv] at hmul
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    rw [hdiv]
    apply (le_div_iff₀ hkpos).2
    rwa [habs]

lemma j_sdiff_major_arc {A k K} :
    j A \ major_arc A k K = (j A).filter (fun h => ∀ t, h ∉ major_arc_at A k K t) := by
  classical
  ext h
  constructor
  · intro hh
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rw [Finset.mem_filter]
    refine ⟨hj, ?_⟩
    intro t ht
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, ht⟩⟩
  · intro hh
    rcases Finset.mem_filter.mp hh with ⟨hj, hmajor⟩
    refine Finset.mem_sdiff.mpr ⟨hj, ?_⟩
    intro hm
    rw [major_arc, Finset.mem_filter] at hm
    rcases hm with ⟨_, ⟨t, ht⟩⟩
    exact hmajor t ht

/-- Centred at `x`, width `2 * y`. -/
def integer_range (x y : ℝ) : Finset ℤ := Finset.Icc ⌈x - y⌉ ⌊x + y⌋

lemma mem_integer_range_iff {x y : ℝ} {z : ℤ} :
    z ∈ integer_range x y ↔ |x - z| ≤ y := by
  rw [integer_range, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hz1, hz2⟩
    constructor
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
  · rintro ⟨hz1, hz2⟩
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)

lemma card_integer_range_le {x y : ℝ} (hy : 0 ≤ y) :
    ↑(integer_range x y).card ≤ 2 * y + 1 := by
  have hnonneg : 0 ≤ ⌊x + y⌋ + 1 - ⌈x - y⌉ := by
    refine sub_nonneg.mpr ?_
    rw [Int.ceil_le]
    have hlt : x - y < ↑(⌊x + y⌋ + 1 : ℤ) := by
      calc
        x - y ≤ x + y := by linarith
        _ < (⌊x + y⌋ : ℝ) + 1 := Int.lt_floor_add_one (x + y)
        _ = ↑(⌊x + y⌋ + 1 : ℤ) := by norm_num
    exact le_of_lt hlt
  calc
    ↑(integer_range x y).card = ((⌊x + y⌋ + 1 - ⌈x - y⌉ : ℤ) : ℝ) := by
      rw [integer_range, Int.card_Icc]
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    _ = (⌊x + y⌋ : ℝ) + 1 - ⌈x - y⌉ := by norm_num
    _ ≤ 2 * y + 1 := by
      have hfc : (⌊x + y⌋ : ℝ) - ⌈x - y⌉ ≤ y + y := by
        simpa using (floor_sub_ceil (z := x) (x := y) (y := y))
      linarith

def my_range (x : ℝ) : Finset ℤ := integer_range 0 x

lemma mem_my_range_iff {x : ℝ} {y : ℤ} :
    y ∈ my_range x ↔ |(y : ℝ)| ≤ x := by
  simpa [my_range] using (mem_integer_range_iff (x := 0) (y := x) (z := y))

def my_range' (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ :=
  my_range ((K / (2 * (k : ℝ)) + (lcmA A : ℝ) / 2) / |(lcmA A : ℝ) / k|)

def I (h : ℤ) (K : ℝ) (k : ℕ) : Finset ℤ := integer_range (h * k) (K / 2)

lemma mem_I' {h : ℤ} {K : ℝ} {k : ℕ} {z : ℤ} :
    z ∈ I h K k ↔ |(h * k : ℝ) - z| ≤ K / 2 := by
  simpa [I] using
    (mem_integer_range_iff (x := (h * k : ℝ)) (y := K / 2) (z := z))

lemma card_I_le {h K k} (hK : (0 : ℝ) ≤ K) : ↑(I h K k).card ≤ K + 1 := by
  calc
    ↑(I h K k).card ≤ 2 * (K / 2) + 1 := by
      simpa [I] using
        (card_integer_range_le (x := (h * k : ℝ)) (y := K / 2)
          (by exact div_nonneg hK (by positivity)))
    _ = K + 1 := by ring

/-- Def 4.5. -/
def minor_arc₁ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K).filter fun h =>
    δ ≤ (A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card

def minor_arc₂ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K) \ minor_arc₁ A k K δ

lemma major_arc_eq_union {A k K} (hA : 0 ∉ A) (hk : k ≠ 0) :
    major_arc A k K = (my_range' A k K).biUnion (major_arc_at A k K) := by
  classical
  ext h
  constructor
  · intro hh
    rw [major_arc, Finset.mem_filter] at hh
    rcases hh with ⟨hj, t, ht⟩
    rw [Finset.mem_biUnion]
    refine ⟨t, ?_, ht⟩
    rw [my_range', mem_my_range_iff]
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hden : 0 < |(lcmA A : ℝ) / k| := by
      exact abs_pos.mpr (div_ne_zero hlcm0 hk0)
    have hvalid : |(h : ℝ)| ≤ (lcmA A : ℝ) / 2 := bound_of_mem_j A h hj
    have harc : |(h : ℝ) - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) :=
      (mem_major_arc_at h).mp ht |>.2
    have harc' : |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| ≤ K / (2 * k) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using harc
    apply (le_div_iff₀ hden).2
    calc
      |(t : ℝ)| * |(lcmA A : ℝ) / k| = |(t : ℝ) * ((lcmA A : ℝ) / k)| := by
        rw [abs_mul]
      _ = |((t : ℝ) * ((lcmA A : ℝ) / k) - h) + h| := by
        congr 1
        ring
      _ ≤ |(t : ℝ) * ((lcmA A : ℝ) / k) - h| + |(h : ℝ)| := abs_add_le _ _
      _ = |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| + |(h : ℝ)| := by
        rw [abs_sub_comm]
      _ ≤ K / (2 * k) + (lcmA A : ℝ) / 2 := add_le_add harc' hvalid
  · intro hh
    rw [Finset.mem_biUnion] at hh
    rcases hh with ⟨t, -, ht⟩
    rw [major_arc, Finset.mem_filter]
    exact ⟨(mem_major_arc_at h).mp ht |>.1, ⟨t, ht⟩⟩

lemma minor_arc₂_eq {A k K δ} :
    minor_arc₂ A k K δ =
      ((j A \ major_arc A k K).filter fun h =>
        ↑(A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card < δ) := by
  ext h
  constructor
  · intro hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hs, hnot⟩
    rw [Finset.mem_filter]
    refine ⟨hs, ?_⟩
    by_contra hge
    apply hnot
    rw [minor_arc₁, Finset.mem_filter]
    exact ⟨hs, le_of_not_gt hge⟩
  · intro hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hs, hlt⟩
    rw [minor_arc₂, Finset.mem_sdiff]
    refine ⟨hs, ?_⟩
    intro hm
    rw [minor_arc₁, Finset.mem_filter] at hm
    exact (not_le.mpr hlt) hm.2

lemma e_eq_one_iff (x : ℝ) :
    e x = 1 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro hx
    rw [e] at hx
    obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp hx
    refine ⟨z, ?_⟩
    have hdiv := congrArg (fun w : ℂ => w / (2 * Real.pi * Complex.I)) hz
    have hxz : (x : ℂ) = z := by
      simpa [div_eq_mul_inv, mul_assoc, Complex.two_pi_I_ne_zero] using hdiv
    simpa using congrArg Complex.re hxz
  · rintro ⟨z, rfl⟩
    simpa using e_int z

lemma abs_e {x : ℝ} : ‖e x‖ = 1 := by
  simpa using norm_e (x := x)

lemma one_add_e (x : ℝ) : 1 + e x = 2 * e (x / 2) * cos (Real.pi * x) := by
  have hzero : e (-x / 2) * e (x / 2) = 1 := by
    simpa [show -x / 2 + x / 2 = 0 by ring] using
      (e_add (x := -x / 2) (y := x / 2)).symm
  have hsplit : e x = e (x / 2) * e (x / 2) := by
    simpa [show x / 2 + x / 2 = x by ring] using
      (e_add (x := x / 2) (y := x / 2))
  have hhalf : e (x / 2) = Complex.exp ((x * Real.pi) * Complex.I) := by
    simp [e, mul_left_comm, mul_comm, two_mul]
  have hnegHalf : e (-x / 2) = Complex.exp (-(x * Real.pi) * Complex.I) := by
    simp [e, mul_left_comm, mul_comm, two_mul]
  calc
    1 + e x = e (-x / 2) * e (x / 2) + e (x / 2) * e (x / 2) := by
      rw [hzero, hsplit]
    _ = e (x / 2) * (e (-x / 2) + e (x / 2)) := by ring
    _ = e (x / 2) *
        (Complex.exp (-(x * Real.pi) * Complex.I) + Complex.exp ((x * Real.pi) * Complex.I)) := by
      congr 1
      rw [hnegHalf, hhalf]
    _ = e (x / 2) * (2 * cos (Real.pi * x)) := by
      congr 1
      simpa [Complex.ofReal_cos, mul_comm, add_comm] using
        (Complex.two_cos (x * Real.pi : ℂ)).symm
    _ = 2 * e (x / 2) * cos (Real.pi * x) := by ring

lemma abs_one_add_e (x : ℝ) :
    ‖1 + e x‖ = 2 * |cos (Real.pi * x)| := by
  rw [one_add_e]
  rw [norm_mul, norm_mul, abs_e]
  norm_num
  simpa [Complex.ofReal_cos] using
    (RCLike.norm_ofReal (K := ℂ) (r := Real.cos (Real.pi * x)))

/-- Lemma 4.6. Note `r` in this statement is different to the `r` in the written proof. -/
lemma orthogonality {n m : ℕ} {r s : ℤ} (hm : m ≠ 0) {I : Finset ℤ}
    (hI : I = Finset.Ioc r s) (hrs₁ : r < s) (hrs₂ : I.card = m) :
    I.sum (fun h => e (h * n / m)) * (1 / m) = if m ∣ n then (1 : ℂ) else 0 := by
  classical
  have _ : r < s := hrs₁
  have hmℝ : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm
  have hmℂ : (m : ℂ) ≠ 0 := by
    exact_mod_cast hm
  have hcardI : I.card = (s - r).toNat := by
    rw [hI, Int.card_Ioc]
  have hcard : (s - r).toNat = m := hcardI.symm.trans hrs₂
  by_cases hmn : m ∣ n
  · obtain ⟨k, rfl⟩ := hmn
    rw [if_pos (dvd_mul_right m k)]
    have hterm : ∀ h : ℤ, e (h * (((m * k : ℕ) : ℝ)) / m) = 1 := by
      intro h
      calc
        e (h * (((m * k : ℕ) : ℝ)) / m) = e ((h : ℝ) * k) := by
          congr 1
          field_simp [hmℝ]
          rw [Nat.cast_mul]
          ring
        _ = e (h * k : ℤ) := by
          congr 1
          push_cast
          rfl
        _ = 1 := e_int (h * k)
    have hsum : I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = m := by
      calc
        I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = I.sum (fun _ => (1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact hterm h
        _ = m := by simp [hrs₂]
    calc
      I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) * (1 / m) = (m : ℂ) * (1 / m) := by
        rw [hsum]
      _ = 1 := by simp [one_div, hmℂ]
  · rw [if_neg hmn]
    let x : ℝ := (n : ℝ) / m
    let ξ : ℂ := e x
    have hpow : ∀ i : ℕ, e ((i : ℝ) * x) = ξ ^ i := by
      intro i
      induction i with
      | zero =>
          simp [ξ]
      | succ i ih =>
          calc
            e (((i + 1 : ℕ) : ℝ) * x) = e (x + (i : ℝ) * x) := by
              congr 1
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
            _ = e x * e ((i : ℝ) * x) := e_add
            _ = ξ * ξ ^ i := by simp [ξ, ih]
            _ = ξ ^ (i + 1) := by rw [pow_succ, mul_comm]
    have hξm : ξ ^ m = 1 := by
      rw [← hpow m]
      dsimp [x]
      rw [show (m : ℝ) * ((n : ℝ) / m) = n by
        field_simp [hmℝ]]
      exact e_nat n
    have hξ_ne : ξ ≠ 1 := by
      intro hξ
      apply hmn
      obtain ⟨z, hz⟩ := (e_eq_one_iff x).mp (by simpa [ξ] using hξ)
      have hnz : (n : ℝ) = z * m := by
        calc
          (n : ℝ) = x * m := by
            dsimp [x]
            field_simp [hmℝ]
          _ = z * m := by rw [hz]
      have hnz' : (n : ℤ) = z * m := by
        exact_mod_cast hnz
      exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hnz'⟩
    have hsum :
        I.sum (fun h => e (h * n / m)) =
          e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i := by
      rw [hI, Int.Ioc_eq_finset_map, Finset.sum_map]
      simp_rw [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
      rw [hcard]
      have hsplit :
          ∑ i ∈ range m, e (((r + 1 + (i : ℤ) : ℤ) * n / m)) =
            ∑ i ∈ range m, e ((((r + 1 : ℤ) : ℝ) * n / m)) * ξ ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have harg :
            (((r + 1 + (i : ℤ) : ℤ) : ℝ) * n / m) =
              (((r + 1 : ℤ) : ℝ) * n / m) + (i : ℝ) * x := by
          dsimp [x]
          push_cast
          ring
        rw [harg, e_add, hpow i]
      rw [hsplit, ← Finset.mul_sum]
    have hgeom0 : ∑ i ∈ range m, ξ ^ i = 0 := by
      have hmul : (∑ i ∈ range m, ξ ^ i) * (ξ - 1) = 0 := by
        simpa [hξm] using (geom_sum_mul ξ m)
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hξ_ne)
    calc
      I.sum (fun h => e (h * n / m)) * (1 / m) =
          (e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i) * (1 / m) := by
            rw [hsum]
      _ = 0 := by simp [hgeom0]

theorem Nat.lcm_smallest {a b d : ℕ} (hda : a ∣ d) (hdb : b ∣ d)
    (hd : ∀ e : ℕ, a ∣ e → b ∣ e → d ∣ e) : d = a.lcm b := by
  apply Nat.dvd_antisymm
  · exact hd _ (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b)
  · exact Nat.lcm_dvd hda hdb

lemma factorization_lcm {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x.lcm y).factorization = x.factorization ⊔ y.factorization := by
  exact Nat.factorization_lcm hx hy

/-- Lemma 4.7. -/
lemma lcm_desc {A : Finset ℕ} (hA : 0 ∉ A) :
    (lcmA A).factorization = A.sup Nat.factorization := by
  classical
  revert hA
  refine Finset.induction_on A ?_ ?_
  · intro hA
    simp [lcmA]
    rfl
  · intro a s ha ih hA
    have ha0 : a ≠ 0 := by
      intro h0
      apply hA
      simp [h0]
    have hs0 : 0 ∉ s := by
      intro hs
      apply hA
      simp [hs]
    rw [lcmA, Finset.lcm_insert, Finset.sup_insert]
    change (Nat.lcm a (s.lcm id)).factorization = a.factorization ⊔ s.sup Nat.factorization
    rw [factorization_lcm ha0 (lcm_ne_zero_of_zero_not_mem hs0), ih hs0]

lemma Finset.support_sup {α β : Type*} {f : α → β →₀ ℕ} (s : Finset α) :
    (s.sup f).support = s.biUnion (fun a => (f a).support) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sup_empty, Finset.biUnion_empty, Finsupp.bot_eq_zero]
    simp
  · intro a s _ ih
    rw [Finset.sup_insert, Finsupp.support_sup, ih, Finset.biUnion_insert]

lemma Finset.sup_eq_mem {α β : Type*} {s : Finset α} (f : α → β)
    [LinearOrder β] [OrderBot β] (hs : s.Nonempty) :
    ∃ x ∈ s, s.sup f = f x := by
  classical
  refine Finset.induction_on s ?_ ?_ hs
  · intro hs
    cases hs.ne_empty rfl
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨x, hx, hsup⟩
      by_cases hax : f a ≤ f x
      · refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_right.2 hax]
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_left.2 (le_of_not_ge hax)]
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      rw [hs0]
      refine ⟨a, by simp, ?_⟩
      simp

lemma Finset.finsupp_sup_apply {α β : Type*} {f : α → β →₀ ℕ} (s : Finset α) (x : β) :
    s.sup f x = s.sup (fun a => f a x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rfl
  · intro a s _ ih
    simp [Finset.sup_insert, Finsupp.sup_apply, ih]

lemma smooth_lcm_aux {X : ℕ} {A : Finset ℕ} (hX₀ : X ≠ 0)
    (hX : ∀ q ∈ ppowers_in_set A, q ≤ X) (hA : 0 ∉ A) :
    lcmA A ≤ X ^ Nat.primeCounting X := by
  have hlcm0 : lcmA A ≠ 0 := lcm_ne_zero_of_zero_not_mem hA
  have hprimecount : ((Finset.Icc 1 X).filter Nat.Prime).card = Nat.primeCounting X := by
    simpa [Nat.primeCounting] using (prime_counting_eq_card_primes (x := X)).symm
  have hpow_mem :
      ∀ p ∈ (lcmA A).primeFactors, p ^ (lcmA A).factorization p ∈ ppowers_in_set A := by
    intro p hp
    have hp' : p ∈ (lcmA A).factorization.support := by
      simpa [Nat.support_factorization] using hp
    have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac :
        (lcmA A).factorization p = A.sup (fun a => a.factorization p) := by
      rw [lcm_desc hA, Finset.finsupp_sup_apply]
    have hAne : A.Nonempty := by
      by_contra hAempty
      rw [Finset.not_nonempty_iff_eq_empty] at hAempty
      simp [hAempty] at hp
    rcases Finset.sup_eq_mem (s := A) (f := fun a => a.factorization p) hAne with ⟨a, haA, hsup⟩
    refine (mem_ppowers_in_set' hpprime hfac0).2 ⟨a, haA, ?_⟩
    rw [← hsup, ← hfac]
  have hcard :
      (lcmA A).primeFactors.card ≤ Nat.primeCounting X := by
    have hsubset : (lcmA A).primeFactors ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp' : p ∈ (lcmA A).factorization.support := by
        simpa [Nat.support_factorization] using hp
      have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
      have hpow_le : p ^ (lcmA A).factorization p ≤ X := hX _ (hpow_mem p hp)
      have hp_le : p ≤ X := (Nat.le_self_pow hfac0 p).trans hpow_le
      exact Finset.mem_filter.mpr ⟨by simp [hpprime.one_le, hp_le], hpprime⟩
    rw [← hprimecount]
    exact Finset.card_le_card hsubset
  calc
    lcmA A = (lcmA A).primeFactors.prod (fun p => p ^ (lcmA A).factorization p) := by
      symm
      exact Nat.prod_factorization_pow_eq_self hlcm0
    _ ≤ (lcmA A).primeFactors.prod (fun _ => X) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact hX (p ^ (lcmA A).factorization p) (hpow_mem p hp)
    _ = X ^ (lcmA A).primeFactors.card := by simp
    _ ≤ X ^ Nat.primeCounting X := by
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hX₀) hcard

/-- Lemma 4.8. -/
lemma smooth_lcm :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 ≤ X →
      ∀ A : Finset ℕ, 0 ∉ A → (∀ q ∈ ppowers_in_set A, ↑q ≤ X) →
        ↑(lcmA A) ≤ exp (C * X) := by
  obtain ⟨c, hc, hprime⟩ := prime_counting_le_const_mul_div_log
  refine ⟨c, hc, ?_⟩
  intro X hX₀ A hA hAX
  by_cases hX : X ≤ 1
  · have hppow : ppowers_in_set A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqX : (q : ℝ) ≤ 1 := (hAX q hq).trans hX
      rw [mem_ppowers_in_set] at hq
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.1.one_lt
      exact not_le_of_gt hq1 hqX
    have hlcm : lcmA A = 1 := by
      simpa [lcmA] using ppowers_in_set_eq_empty' hppow hA
    rw [hlcm, Nat.cast_one]
    simpa using Real.one_le_exp (mul_nonneg hc.le hX₀)
  · have hX' : 1 < X := lt_of_not_ge hX
    have hfloor0 : ⌊X⌋₊ ≠ 0 := by
      simp [Nat.floor_eq_zero, not_lt, hX'.le]
    refine
      (Nat.cast_le.2
        (smooth_lcm_aux hfloor0 (fun q hq ↦ Nat.le_floor (hAX q hq)) hA)).trans ?_
    simp only [Nat.cast_pow]
    refine (pow_le_pow_left₀ (by positivity) (Nat.floor_le hX₀) _).trans ?_
    have hdiv_nonneg : 0 ≤ X / Real.log X := by
      exact div_nonneg hX₀ (Real.log_nonneg hX'.le)
    have hX₁ : (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ c * (X / Real.log X) := by
      simpa [Real.norm_of_nonneg hdiv_nonneg] using hprime X
    have hpowpos : 0 < X ^ Nat.primeCounting ⌊X⌋₊ := by
      exact pow_pos (zero_lt_one.trans hX') _
    rwa [← Real.log_le_iff_le_exp hpowpos, ← Real.rpow_natCast,
      Real.log_rpow (zero_lt_one.trans hX'), ← _root_.le_div_iff₀ (Real.log_pos hX'),
      mul_div_assoc]

lemma jordan_apply {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 * x ≤ sin (Real.pi * x) := by
  have hπx_nonneg : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx
  have hπx_le : Real.pi * x ≤ Real.pi / 2 := by
    nlinarith [hx', Real.pi_pos]
  simpa [div_eq_mul_inv, mul_assoc, Real.pi_ne_zero] using
    (Real.mul_le_sin (x := Real.pi * x) hπx_nonneg hπx_le)

/-- Lemma 4.9. -/
lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |cos (Real.pi * x)| ≤ exp (-(2 * x ^ 2)) := by
  have hcos_nonneg : 0 ≤ cos (Real.pi * x) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [hx', Real.pi_pos]
  rw [abs_of_nonneg hcos_nonneg]
  have hπx : |Real.pi * x| ≤ Real.pi := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx)]
    nlinarith [hx', Real.pi_pos]
  have hcos :
      cos (Real.pi * x) ≤ 1 - 2 * x ^ 2 := by
    calc
      cos (Real.pi * x) ≤ 1 - 2 / Real.pi ^ 2 * (Real.pi * x) ^ 2 := Real.cos_le_one_sub_mul_cos_sq hπx
      _ = 1 - 2 * x ^ 2 := by
        field_simp [pow_two, Real.pi_ne_zero]
  have hexp : 1 - 2 * x ^ 2 ≤ exp (-(2 * x ^ 2)) := by
    simpa using Real.one_sub_le_exp_neg (2 * x ^ 2)
  exact hcos.trans hexp

lemma cos_bound_abs {x : ℝ} (hx' : |x| ≤ 1 / 2) :
    |cos (Real.pi * x)| ≤ exp (-(2 * x ^ 2)) := by
  rcases le_or_gt 0 x with hx | hx
  · exact cos_bound hx (by simpa [abs_of_nonneg hx] using hx')
  · have hxneg : 0 ≤ -x := by linarith
    have hxneg' : -x ≤ 1 / 2 := by
      have hxabs : |-x| ≤ 1 / 2 := by simpa [abs_neg] using hx'
      simpa [abs_of_nonneg hxneg] using hxabs
    have h := cos_bound hxneg hxneg'
    simpa [neg_mul, Real.cos_neg, pow_two] using h

lemma Nat.coprime_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n : ℕ) :
    Nat.Coprime n (s.prod f) ↔ ∀ i ∈ s, Nat.Coprime n (f i) := by
  simpa [Nat.coprime_iff_isRelPrime] using
    (IsRelPrime.prod_right_iff (t := s) (s := f) (x := n))

lemma prod_dvd_of_dvd_of_pairwise_disjoint {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hn : ∀ i ∈ s, f i ∣ n) (h : (s : Set ι).Pairwise fun i j => Nat.Coprime (f i) (f j)) :
    s.prod f ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a r har ihr =>
      rw [Finset.prod_insert har]
      have hcop : Nat.Coprime (f a) (r.prod f) := by
        rw [Nat.coprime_prod]
        intro i hi
        exact h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi har).symm
      refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact hn a (by simp)
      · refine ihr ?_ ?_
        · intro i hi
          exact hn i (by simp [hi])
        · intro i hi j hj hij
          exact h (by simp [hi]) (by simp [hj]) hij

/-- Lemma 4.10. -/
lemma triv_q_bound {A : Finset ℕ} (hA : 0 ∉ A) (n : ℕ) :
    ↑((ppowers_in_set A).filter fun q => n ∈ local_part A q).card ≤ log n / log 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [zero_mem_local_part_iff, hA, Real.log_zero]
  · have hsubset :
        (ppowers_in_set A).filter (fun q => n ∈ local_part A q) ⊆
          n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q)) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqppow, hqn⟩
      rcases (mem_ppowers_in_set.mp hqppow).1 with hqprime
      rcases (mem_local_part (A := A) (q := q) n).mp hqn with ⟨_, hqdvd, hqcop⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨hqdvd, hn0⟩
      · exact ⟨hqprime, hqcop⟩
    have hcard :
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
          ArithmeticFunction.cardDistinctFactors n := by
      calc
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
            (n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q))).card := by
              exact Finset.card_le_card hsubset
        _ = ArithmeticFunction.cardDistinctFactors n := omega_count_eq_ppowers
    have hpow_nat : 2 ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      calc
        2 ^ ArithmeticFunction.cardDistinctFactors n ≤ ArithmeticFunction.sigma 0 n :=
          two_pow_card_distinct_divisors_le_divisor_count hn0
        _ ≤ n := by
          rw [ArithmeticFunction.sigma_zero_apply]
          exact Nat.card_divisors_le_self n
    have hpow : (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      simpa [Real.rpow_natCast] using
        (show ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) ≤ n by
          exact_mod_cast hpow_nat)
    have hcardR :
        (((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card : ℝ) ≤
          ArithmeticFunction.cardDistinctFactors n := by
      exact_mod_cast hcard
    have hlog :
        (ArithmeticFunction.cardDistinctFactors n : ℝ) * log 2 ≤ log n := by
      have hlog_aux := Real.log_le_log
        (show 0 < (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n by positivity) hpow
      simpa [Real.log_rpow, mul_comm] using hlog_aux
    have hlog2 : 0 < log 2 := Real.log_pos one_lt_two
    exact le_trans hcardR ((le_div_iff₀ hlog2).2 <| by simpa [mul_comm] using hlog)

lemma sum_powerset_prod {ι : Type*} (I : Finset ι) (x : ι → ℂ) :
    I.powerset.sum (fun J => J.prod x) = I.prod (fun i => 1 + x i) := by
  simpa using (Finset.prod_one_add (s := I) (f := x)).symm

/-- Lemma 4.11. -/
lemma orthog_rat {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0) :
    (integer_count A k : ℂ) =
      1 / (lcmA A) *
        (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) := by
  have hA' : ((lcmA A : ℕ) : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA)
  have hk' : (k : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 hk
  have hdiv :
      ∀ S : Finset ℕ, S ⊆ A →
        ((∃ z : ℤ, rec_sum S * (k : ℚ) = z) ↔
          lcmA A ∣ (k * S.sum (fun n => lcmA A / n))) := by
    intro S hS
    have hsum :
        S.sum (fun x => ((lcmA A / x : ℕ) : ℚ)) = rec_sum S * (lcmA A : ℚ) := by
      rw [rec_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hA
        exact hS (hx0 ▸ hx)
      calc
        (((lcmA A / x : ℕ) : ℚ)) = (lcmA A : ℚ) / x := by
          rw [Nat.cast_div (K := ℚ)]
          · exact Finset.dvd_lcm (hS hx)
          · exact Nat.cast_ne_zero.2 hx0
        _ = ((1 : ℚ) / x) * (lcmA A : ℚ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    rw [← Int.natCast_dvd_natCast, dvd_iff_exists_eq_mul_left]
    apply exists_congr
    intro z
    constructor
    · intro hz
      have hzQ :
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        calc
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by
            rw [hsum]
          _ = (rec_sum S * (k : ℚ)) * (lcmA A : ℚ) := by ring
          _ = (z : ℚ) * (lcmA A : ℚ) := by rw [hz]
      apply (Int.cast_inj (α := ℚ)).mp
      rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_sum]
      simpa [Rat.cast_natCast] using hzQ
    · intro hz
      have hzQ : (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        simpa [Int.cast_natCast, Int.cast_mul, Nat.cast_mul, Nat.cast_sum, Rat.cast_natCast] using
          congrArg (fun t : ℤ => (t : ℚ)) hz
      have hmul' :
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ)) = (lcmA A : ℚ) * z := by
        calc
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by ring
          _ = (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) := by rw [hsum]
          _ = (z : ℚ) * (lcmA A : ℚ) := hzQ
          _ = (lcmA A : ℚ) * z := by ring
      exact (mul_right_inj' hA').mp hmul'
  have horth :
      ∀ S : Finset ℕ, S ∈ A.powerset →
        (if (∃ z : ℤ, rec_sum S * (k : ℚ) = z) then (1 : ℕ) else 0 : ℂ) =
          1 / (lcmA A) * (valid_sum_range (lcmA A)).sum (fun h => e (k * h * rec_sum S)) := by
    intro S hS
    have ht : (-((lcmA A : ℕ) : ℤ) / 2 : ℤ) < (lcmA A : ℤ) / 2 := by
      apply Int.ediv_lt_of_lt_mul zero_lt_two
      apply lt_of_lt_of_le
      · rw [Right.neg_neg_iff, Int.natCast_pos]
        exact Nat.pos_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA)
      · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
    rw [Finset.mem_powerset] at hS
    rw [Nat.cast_one, if_congr (hdiv S hS) rfl rfl, mul_comm (_ : ℂ)]
    rw [← orthogonality (lcm_ne_zero_of_zero_not_mem hA) rfl ht (card_valid_sum_range _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_mul, mul_div_assoc, mul_div_assoc, ← mul_assoc, mul_comm (i : ℝ)]
    congr 2
    rw [rec_sum, Nat.cast_sum, Finset.sum_div, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hA
      exact hS (hn0 ▸ hn)
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_one]
    calc
      (((lcmA A / n : ℕ) : ℝ) / (lcmA A : ℝ))
          = (((lcmA A : ℕ) : ℝ) / n) / (lcmA A : ℝ) := by
              rw [Nat.cast_div (K := ℝ)]
              · exact Finset.dvd_lcm (hS hn)
              · exact Nat.cast_ne_zero.2 hn0
      _ = (1 : ℝ) / n := by
        field_simp [hlcm0, show (n : ℝ) ≠ 0 by exact_mod_cast hn0]
  rw [integer_count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_congr rfl horth, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← sum_powerset_prod, ← e_sum, rec_sum, Rat.cast_sum, mul_sum,
    Rat.cast_div, Rat.cast_one, ← div_eq_mul_one_div, Rat.cast_natCast]

lemma integer_bound_thing {d : ℤ} (hd₀ : 0 ≤ d) (hd₁ : d ≠ 1) (hd₂ : d < 2) :
    d = 0 := by
  omega

lemma orthog_simp_aux {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) = lcmA A := by
  have hcount : integer_count A k = 1 := by
    have hfilter :
        A.powerset.filter (fun S => ∃ d : ℤ, rec_sum S * k = d) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hSA, d, hd⟩
        have hkQ : (k : ℚ) ≠ 0 := by
          exact_mod_cast hk
        have hkQ_pos : (0 : ℚ) < k := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        have hd0Q : (0 : ℚ) ≤ (d : ℚ) := by
          calc
            (0 : ℚ) ≤ rec_sum S * k := by
              exact mul_nonneg rec_sum_nonneg (show (0 : ℚ) ≤ k by exact_mod_cast Nat.zero_le k)
            _ = d := hd
        have hd0 : 0 ≤ d := by
          exact_mod_cast hd0Q
        have hdlt2Q : (d : ℚ) < 2 := by
          have hrec_lt : rec_sum S < 2 / k := (rec_sum_mono hSA).trans_lt hA'
          exact (by
            simpa [hd] using (_root_.lt_div_iff₀ hkQ_pos).mp hrec_lt : (d : ℚ) < 2)
        have hdlt2 : d < 2 := by
          exact_mod_cast hdlt2Q
        have hdne1 : d ≠ 1 := by
          intro hd1
          apply hS S hSA
          apply (eq_div_iff hkQ).2
          simpa [hd1] using hd
        have hdzero : d = 0 := integer_bound_thing hd0 hdne1 hdlt2
        have hrec0 : rec_sum S = 0 := by
          have hmul0 : rec_sum S * (k : ℚ) = 0 := by
            simpa [hdzero] using hd
          exact (mul_eq_zero.mp hmul0).resolve_right hkQ
        have hS0 : 0 ∉ S := by
          intro h0S
          exact hA (hSA h0S)
        exact (rec_sum_eq_zero_iff hS0).1 hrec0
      · intro hSe
        subst hSe
        exact ⟨by simp, 0, by simp⟩
    simp [integer_count, hfilter]
  have hlcm0 : ((lcmA A : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
  apply (div_eq_one_iff_eq hlcm0).mp
  rw [div_eq_mul_one_div, mul_comm, ← orthog_rat hA hk, hcount]
  norm_num

/-- Lemma 4.12. -/
lemma orthog_simp {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum
        (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) =
      lcmA A := by
  simpa using congrArg Complex.re (orthog_simp_aux hA hk hS hA')

/-- Lemma 4.13. -/
lemma orthog_simp2 {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k)
    (hA'' : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    (j A).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) ≤ -2 ^ (A.card - 1 : ℤ) := by
  have hlcm0 := lcm_ne_zero_of_zero_not_mem hA
  rw [j, Finset.sum_erase_eq_sub (zero_mem_valid_sum_range hlcm0), orthog_simp hA hk hS hA']
  simp only [Int.cast_zero, zero_div, mul_zero, e_zero, Finset.prod_const]
  rw [sub_le_iff_le_add, neg_add_eq_sub]
  refine hA''.trans ?_
  rw [le_sub_iff_add_le]
  have hpow :
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ) =
        ((1 + 1 : ℂ) ^ A.card).re := by
    calc
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ)
          = (2 : ℝ) ^ (A.card - 1 : ℤ) * 2 := by ring
      _ = (2 : ℝ) ^ ((A.card - 1 : ℤ) + 1) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]
      _ = (2 : ℝ) ^ (A.card : ℤ) := by simp
      _ = (2 : ℝ) ^ A.card := by rw [zpow_natCast]
      _ = ((2 : ℂ) ^ A.card).re := by
        simpa [Complex.ofReal_pow] using (Complex.ofReal_re ((2 : ℝ) ^ A.card)).symm
      _ = ((1 + 1 : ℂ) ^ A.card).re := by norm_num
  exact le_of_eq hpow

/-- Lemma 4.14. -/
lemma majorarcs_disjoint {A : Finset ℕ} {k : ℕ} {K : ℝ} (hk : k ≠ 0) (hA : K < lcmA A) :
    (Set.univ : Set ℤ).PairwiseDisjoint (major_arc_at A k K) := by
  intro t₁ _ t₂ _ ht
  change Disjoint (major_arc_at A k K t₁) (major_arc_at A k K t₂)
  rw [Finset.disjoint_left]
  by_cases hK : K < 0
  · intro h hh _
    rw [major_arc_at_of_neg hk hK] at hh
    simp at hh
  · intro h hh₁ hh₂
    have hK' : 0 ≤ K := le_of_not_gt hK
    have hh : h ∈ major_arc_at A k K t₁ ∧ h ∈ major_arc_at A k K t₂ := ⟨hh₁, hh₂⟩
    simp only [mem_major_arc_at' hk, and_and_and_comm, and_self] at hh
    have hbound : |((t₁ : ℝ) - t₂) * (lcmA A : ℝ)| ≤ K := by
      rw [sub_mul]
      refine le_trans (abs_sub_le _ ((h : ℝ) * k) _) ?_
      rw [abs_sub_comm]
      refine le_trans (add_le_add hh.2.1 hh.2.2) ?_
      nlinarith
    have hLnonneg : 0 ≤ (lcmA A : ℝ) := by positivity
    have hbound' : (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) ≤ K := by
      simpa [Int.cast_sub, Int.cast_abs, abs_mul, abs_of_nonneg hLnonneg] using hbound
    have ht' : 1 ≤ |t₁ - t₂| := by
      rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
    have ht'' : (1 : ℝ) ≤ (|t₁ - t₂| : ℝ) := by
      exact_mod_cast ht'
    have hge : (lcmA A : ℝ) ≤ (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) := by
      nlinarith
    exact (not_lt.mpr hbound') (lt_of_lt_of_le hA hge)

/-- Lemma 4.15. -/
lemma useful_rewrite {A : Finset ℕ} {theta : ℝ} :
    (A.prod (fun n => 1 + e (theta / n))).re =
      2 ^ A.card * cos (Real.pi * theta * rec_sum A) * A.prod (fun n => cos (Real.pi * theta / n)) := by
  simp only [one_add_e, Finset.prod_mul_distrib, ← mul_div_assoc]
  rw [Finset.prod_const, ← Nat.cast_two, ← Nat.cast_pow, ← Complex.ofReal_prod]
  have houter :
      ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2)) *
          ↑(∏ i ∈ A, cos (Real.pi * theta / ↑i))).re =
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2)).re *
          ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
    simpa using
      (Complex.re_mul_ofReal
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2))
        (∏ i ∈ A, cos (Real.pi * theta / ↑i)))
  have hinner :
      (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2)).re =
        (2 ^ A.card : ℝ) * (∏ x ∈ A, e (theta / ↑x / 2)).re := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.re_mul_ofReal
        (∏ x ∈ A, e (theta / ↑x / 2))
        (2 ^ A.card : ℝ))
  have hsum : A.sum (fun n => theta / (n : ℝ)) = theta * rec_sum A := by
    rw [rec_sum, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [Rat.cast_natCast, div_eq_mul_inv, mul_comm]
  calc
    ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2)) *
        ↑(∏ i ∈ A, cos (Real.pi * theta / ↑i))).re
        = (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (theta / ↑x / 2)).re *
            ∏ i ∈ A, cos (Real.pi * theta / ↑i) := houter
    _ = ((2 ^ A.card : ℝ) * (∏ x ∈ A, e (theta / ↑x / 2)).re) *
          ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
      rw [hinner]
    _ = ((2 ^ A.card : ℝ) * (e (∑ x ∈ A, theta / ↑x / 2)).re) *
          ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
      rw [← e_sum]
    _ = ((2 ^ A.card : ℝ) * cos ((∑ x ∈ A, theta / ↑x) * Real.pi)) *
          ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
      rw [← Finset.sum_div, e_half_re]
    _ = ((2 ^ A.card : ℝ) * cos (Real.pi * theta * rec_sum A)) *
          ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
      rw [hsum]
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card * cos (Real.pi * theta * rec_sum A) * ∏ i ∈ A, cos (Real.pi * theta / ↑i) := by
      ring

lemma prod_major_arc_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hA : 0 ∉ A) (hk : k ≠ 0) (hA' : K < lcmA A) {f : ℤ → α} :
    (major_arc A k K).prod f = (my_range' A k K).prod (fun t => (major_arc_at A k K t).prod f) := by
  rw [major_arc_eq_union hA hk]
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hA') (by simp)
  simpa using
    (Finset.prod_biUnion (s := my_range' A k K) (t := major_arc_at A k K) (f := f) hdisj)

def jt (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℝ) : Finset ℤ :=
  (my_range (K / (2 * (k : ℝ)))).filter fun h => ∃ i ∈ j A, (i : ℝ) - t * (lcmA A) / k = h

lemma prod_major_arc_at_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ} {t}
    {f : ℤ → α} (hk : k ∣ lcmA A) :
    (major_arc_at A k K t).prod f = (jt A k K t).prod (fun r => f (t * lcmA A / k + r)) := by
  by_cases hk0 : k = 0
  · have hlcm : lcmA A = 0 := Nat.zero_dvd.mp (by simpa [hk0] using hk)
    simp [major_arc_at, jt, j, valid_sum_range, hk0, hlcm]
  have hdiv : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk) t
  let c : ℤ := t * lcmA A / k
  have hc : ((c : ℤ) : ℝ) = t * (lcmA A : ℝ) / k := by
    calc
      ((c : ℤ) : ℝ) = (((t * lcmA A) / k : ℤ) : ℝ) := by rfl
      _ = (((t * lcmA A : ℤ) : ℝ) / ((k : ℤ) : ℝ)) := by
        rw [Int.cast_div hdiv (by exact_mod_cast hk0)]
      _ = (((t * lcmA A : ℤ) : ℝ) / (k : ℝ)) := by simp
      _ = ((((t : ℤ) : ℝ) * (lcmA A : ℝ)) / (k : ℝ)) := by simp
      _ = t * (lcmA A : ℝ) / k := by simp
  apply Eq.symm
  refine Finset.prod_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
  · intro a ha
    rw [jt, Finset.mem_filter] at ha
    rw [mem_major_arc_at]
    rcases ha with ⟨ha, i, hi, hia⟩
    have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
    have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
      calc
        (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
        _ = (c : ℝ) + a := by rw [hc]
        _ = ((c + a : ℤ) : ℝ) := by norm_num
    have hica : i = c + a := by
      exact Int.cast_inj.mp hicast
    constructor
    · simpa [hica] using hi
    · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
        rw [hc]
        simpa using hbounda
      simpa [Int.cast_add] using hbound
  · intro a₁ h₁ a₂ h₂ h
    exact add_left_cancel h
  · intro b hb
    refine ⟨b - c, ?_, ?_⟩
    · rw [mem_major_arc_at] at hb
      rw [jt, Finset.mem_filter]
      rcases hb with ⟨hbj, hbbound⟩
      constructor
      · refine (mem_my_range_iff).2 ?_
        have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
          calc
            (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
            _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by rw [hc]
        simpa [hbc] using hbbound
      · refine ⟨b, hbj, ?_⟩
        calc
          (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by rw [hc]
          _ = (b - c : ℤ) := by norm_num
    · simp [c]
  · intro a ha
    rfl

lemma majorarcs_at {K : ℝ} {A : Finset ℕ} {k : ℕ}
    (hk : k ≠ 0) (hk' : k ∣ lcmA A) {t : ℤ} :
    (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
      2 ^ A.card *
        (jt A k K t).sum
          (fun r => cos (Real.pi * k * r * rec_sum A) * A.prod (fun n => cos (Real.pi * (k * r) / n))) := by
  have hdivk : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk') t
  have hsum :
      (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
        (jt A k K t).sum
          (fun r => (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re) := by
    let c : ℤ := t * lcmA A / k
    have hc : c = t * lcmA A / k := rfl
    refine Eq.symm <| Finset.sum_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
    · intro a ha
      rw [jt, Finset.mem_filter] at ha
      rw [mem_major_arc_at]
      rcases ha with ⟨ha, i, hi, hia⟩
      have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
      have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
        calc
          (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
          _ = (c : ℝ) + a := by
            rw [hc]
            rw [Int.cast_div hdivk (by exact_mod_cast hk)]
            simp
          _ = ((c + a : ℤ) : ℝ) := by norm_num
      have hica : i = c + a := Int.cast_inj.mp hicast
      constructor
      · simpa [hica] using hi
      · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
          rw [hc]
          rw [Int.cast_div hdivk (by exact_mod_cast hk)]
          simpa using hbounda
        simpa [Int.cast_add] using hbound
    · intro a₁ h₁ a₂ h₂ h
      exact add_left_cancel h
    · intro b hb
      refine ⟨b - c, ?_, ?_⟩
      · rw [mem_major_arc_at] at hb
        rw [jt, Finset.mem_filter]
        rcases hb with ⟨hbj, hbbound⟩
        constructor
        · refine (mem_my_range_iff).2 ?_
          have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
            calc
              (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
              _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by
                rw [hc]
                rw [Int.cast_div hdivk (by exact_mod_cast hk)]
                simp
          simpa [hbc] using hbbound
        · refine ⟨b, hbj, ?_⟩
          calc
            (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by
              rw [hc]
              rw [Int.cast_div hdivk (by exact_mod_cast hk)]
              simp
            _ = (b - c : ℤ) := by norm_num
      · simp [hc]
    · intro a ha
      simp [hc]
  rw [hsum]
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  calc
    ∑ r ∈ jt A k K t, (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
        =
          ∑ r ∈ jt A k K t,
            2 ^ A.card *
              (cos (Real.pi * k * r * rec_sum A) * A.prod (fun n => cos (Real.pi * (k * r) / n))) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hprod :
                A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)) =
                  A.prod (fun n => 1 + e (↑k * ↑r / ↑n)) := by
              refine Finset.prod_congr rfl ?_
              intro n hn
              by_cases hn0 : n = 0
              · subst hn0
                simp
              · have hdivn : (n : ℤ) ∣ t * lcmA A := by
                  exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr <| Finset.dvd_lcm hn) t
                have hnZ : (n : ℤ) ≠ 0 := by
                  exact_mod_cast hn0
                have hnR : (n : ℝ) ≠ 0 := by
                  exact_mod_cast hn0
                have harg :
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n =
                      (((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n) := by
                  calc
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n
                        = ((↑k : ℝ) * ↑(t * lcmA A / k) + ↑k * ↑r) / ↑n := by
                            rw [Int.cast_add, mul_add]
                    _ = (↑k : ℝ) * ↑(t * lcmA A / k) / ↑n + ↑k * ↑r / ↑n := by
                          rw [add_div]
                    _ = ((((t * lcmA A : ℤ) : ℝ) / ↑n)) + ↑k * ↑r / ↑n := by
                          congr 1
                          rw [Int.cast_div_charZero hdivk]
                          field_simp [hkR, hnR]
                          simp [mul_comm, mul_left_comm]
                    _ = ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) + ↑k * ↑r / ↑n := by
                          rw [Int.cast_div_charZero hdivn]
                          simp
                calc
                  1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)
                      = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n)) := by
                          rw [harg]
                  _ = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) * e (↑k * ↑r / ↑n) := by
                        rw [e_add]
                  _ = 1 + e (↑k * ↑r / ↑n) := by
                        rw [e_int, one_mul]
            calc
              (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
                  = (A.prod (fun n => 1 + e (↑k * ↑r / ↑n))).re := by rw [hprod]
              _ = 2 ^ A.card * cos (Real.pi * ((k : ℝ) * r) * rec_sum A) *
                    A.prod (fun n => cos (Real.pi * ((k : ℝ) * r) / n)) := by
                    simpa using (useful_rewrite (A := A) (theta := (k : ℝ) * r))
              _ = 2 ^ A.card *
                    (cos (Real.pi * k * r * rec_sum A) * A.prod (fun n => cos (Real.pi * (k * r) / n))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card *
          (jt A k K t).sum
            (fun r => cos (Real.pi * k * r * rec_sum A) * A.prod (fun n => cos (Real.pi * (k * r) / n))) := by
          rw [Finset.mul_sum]

lemma cos_nonneg_of_abs_le {x : ℝ} (hx : |x| ≤ Real.pi / 2) : 0 ≤ cos x := by
  refine Real.cos_nonneg_of_mem_Icc ?_
  rw [Set.mem_Icc]
  exact abs_le.mp hx

/-- Lemma 4.16. -/
lemma majorarcs {M K : ℝ} {A : Finset ℕ} (hM : ∀ n : ℕ, n ∈ A → M ≤ n) (hK : 0 < K)
    (hKM : K < M) {k : ℕ} (hk' : k ∣ lcmA A) (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A)
    (hA₂ : (k : ℝ) * rec_sum A ≤ 2) (hA₃ : A.Nonempty) :
    (0 : ℝ) ≤ (major_arc A k K).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hKlcm : K < lcmA A := by
    apply hKM.trans_le
    obtain ⟨n, hn⟩ := hA₃
    refine (hM n hn).trans ?_
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA)) (Finset.dvd_lcm hn)
  have hk : k ≠ 0 := ne_zero_of_dvd_ne_zero (lcm_ne_zero_of_zero_not_mem hA) hk'
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hKlcm) (by simp)
  rw [major_arc_eq_union hA hk, Finset.sum_biUnion hdisj]
  simp only [majorarcs_at hk hk', ← Finset.mul_sum, jt, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_nonneg (pow_nonneg zero_le_two _) (Finset.sum_nonneg ?_)
  intro r hr
  rw [mem_my_range_iff] at hr
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ ?_)
  · have hcos :
      cos (Real.pi * k * r * rec_sum A) = cos (Real.pi * r * (2 - k * rec_sum A)) := by
        calc
          cos (Real.pi * k * r * rec_sum A)
              = cos (Real.pi * r * (k * rec_sum A - 2)) := by
                  rw [mul_sub, mul_mul_mul_comm, ← mul_assoc, mul_comm Real.pi r, mul_assoc ↑r Real.pi,
                    mul_comm Real.pi 2, Real.cos_sub_int_mul_two_pi]
          _ = cos (-(Real.pi * r * (k * rec_sum A - 2))) := by rw [Real.cos_neg]
          _ = cos (Real.pi * r * (2 - k * rec_sum A)) := by ring_nf
    rw [hcos]
    apply cos_nonneg_of_abs_le
    have hA₂' : 0 ≤ 2 - (k : ℝ) * (rec_sum A : ℝ) := sub_nonneg.mpr hA₂
    have hA₁' : 2 - (k : ℝ) * (rec_sum A : ℝ) ≤ (k : ℝ) / M := by linarith
    rw [abs_mul, abs_mul, abs_of_nonneg pi_pos.le, abs_of_nonneg hA₂']
    refine (mul_le_mul_of_nonneg_left hA₁' (mul_nonneg pi_pos.le (abs_nonneg _))).trans ?_
    have hM' : 0 < M := hK.trans hKM
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hrk : |(r : ℝ)| * (k : ℝ) ≤ K / 2 := by
      calc
        |(r : ℝ)| * (k : ℝ) ≤ (K / (2 * (k : ℝ))) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hr hkpos.le
        _ = K / 2 := by
          field_simp [hkpos.ne']
    have hratio : |(r : ℝ)| * (k : ℝ) / M ≤ 1 / 2 := by
      apply (div_le_iff₀ hM').2
      linarith [hrk, hKM]
    calc
      Real.pi * |(r : ℝ)| * (k / M) = Real.pi * ((|(r : ℝ)| * (k : ℝ)) / M) := by ring
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hratio pi_pos.le
      _ = Real.pi / 2 := by ring
  · apply Finset.prod_nonneg
    intro n hn
    apply cos_nonneg_of_abs_le
    have h2k : 0 < 2 * (k : ℝ) := by
      exact mul_pos zero_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hk)
    replace hr := ((le_div_iff₀ h2k).1 hr).trans (hKM.le.trans (hM n hn))
    have hnpos : 0 < |(n : ℝ)| := by
      apply abs_pos_of_pos
      exact hK.trans (hKM.trans_le (hM n hn))
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg pi_pos.le, div_le_div_iff₀ hnpos zero_lt_two,
      Nat.abs_cast k, Nat.abs_cast n, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    convert hr using 1
    ring_nf

lemma prod_sdiff' {α M : Type*} [DecidableEq α] [CommGroup M]
    (f : α → M) (s₁ s₂ : Finset α) (h : s₁ ⊆ s₂) :
    (s₂ \ s₁).prod f = (s₂.prod f) / s₁.prod f := by
  rw [eq_div_iff_mul_eq', Finset.prod_sdiff h]

lemma minor_lbound {M : ℝ} {A : Finset ℕ} {K : ℝ} {k : ℕ}
    (hM : ∀ n ∈ A, M ≤ ↑n) (hK : 0 < K) (hKM : K < M) (hkA : k ∣ lcmA A) (hk : k ≠ 0)
    (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A) (hA₂ : (k : ℝ) * rec_sum A < 2)
    (hA₃ : A.Nonempty) (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k)
    (hA₄ : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    1 / 2 ≤ (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hkQ : (0 : ℚ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hA₂' : rec_sum A < 2 / k := by
    have hA₂'' : (k : ℚ) * rec_sum A < 2 := by
      exact_mod_cast hA₂
    exact (_root_.lt_div_iff₀ hkQ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA₂'')
  let f : ℤ → ℝ := fun h => (A.prod (fun n => 1 + e (k * h / n))).re
  have hmajor : 0 ≤ (major_arc A k K).sum f := by
    simpa [f] using
      (majorarcs (M := M) (K := K) (A := A) hM hK hKM hkA hA₁ hA₂.le hA₃)
  have hsubset : major_arc A k K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hsplit :
      (j A \ major_arc A k K).sum f + (major_arc A k K).sum f = (j A).sum f := by
    simpa [f] using (Finset.sum_sdiff hsubset (f := f))
  have hminor_re :
      (j A \ major_arc A k K).sum f ≤ -2 ^ (A.card - 1 : ℤ) := by
    have htotal : (j A).sum f ≤ -2 ^ (A.card - 1 : ℤ) :=
      orthog_simp2 hA hk hS hA₂' hA₄
    rw [← hsplit] at htotal
    linarith
  have hpoint :
      ∀ h ∈ j A \ major_arc A k K, -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ f h := by
    intro h hh
    let z : ℂ := A.prod (fun n => 1 + e (k * h / n))
    have hzre : |z.re| ≤ ‖z‖ := by
      simpa using Complex.abs_re_le_norm z
    have hznorm : ‖z‖ = (2 : ℝ) ^ A.card * cos_prod A (h * k) := by
      dsimp [z]
      rw [norm_prod]
      simp_rw [abs_one_add_e]
      rw [Finset.prod_mul_distrib]
      simp [cos_prod, Int.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm]
    have hbound : -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ z.re := by
      rw [← hznorm]
      exact (abs_le.mp hzre).1
    simpa [f, z] using hbound
  have hminor_cp :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        (j A \ major_arc A k K).sum f := by
    calc
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)))
          = (j A \ major_arc A k K).sum (fun h => -((2 : ℝ) ^ A.card * cos_prod A (h * k))) := by
              rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ ≤ (j A \ major_arc A k K).sum (fun h => f h) := by
            exact Finset.sum_le_sum hpoint
      _ = (j A \ major_arc A k K).sum f := rfl
  have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₃
  have hpow : (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ A.card / 2 := by
    rw [zpow_sub₀ two_ne_zero]
    simp
  have hfinal :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        -(2 : ℝ) ^ (A.card - 1 : ℤ) := by
    exact le_trans hminor_cp hminor_re
  rw [hpow] at hfinal
  have hpowpos : 0 < (2 : ℝ) ^ A.card := pow_pos zero_lt_two _
  nlinarith

lemma Function.Antiperiodic.abs_periodic {f : ℝ → ℝ} {c : ℝ}
    (h : Function.Antiperiodic f c) :
    Function.Periodic (abs ∘ f) c := by
  intro x
  simp [Function.comp, h x, abs_neg]

lemma abs_cos_periodic : Function.Periodic (fun i => |cos i|) Real.pi := by
  intro x
  show |cos (x + Real.pi)| = |cos x|
  rw [Real.cos_add_pi]
  exact abs_neg _

lemma abs_cos_period {x y n : ℤ} (h : x % n = y % n) :
    |cos (Real.pi * (x / n))| = |cos (Real.pi * (y / n))| := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at h
    simp [h]
  have hdiv : n ∣ x - y := by
    rwa [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  obtain ⟨k, hk⟩ := hdiv
  rw [sub_eq_iff_eq_add'] at hk
  rw [hk, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_left₀]
  · rw [mul_add, mul_comm Real.pi k]
    exact abs_cos_periodic.int_mul k _
  · exact_mod_cast hn

lemma cos_prod_bound {A : Finset ℕ} {N : ℕ} (t : ℤ) (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) (h' : ℕ → ℤ) (hh'₁ : ∀ n ∈ A, h' n % n = t % n)
    (hh'₂ : ∀ n ∈ A, (|h' n| : ℝ) ≤ n / 2) :
    cos_prod A t ≤ exp (- (2 / N ^ 2) * A.sum (fun n => h' n ^ 2)) := by
  rw [cos_prod]
  have hrhs :
      exp (- (2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2)) =
        A.prod (fun n => exp (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) := by
    rw [show -(2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2) =
        A.sum (fun n => (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) by
          rw [Int.cast_sum]
          rw [Finset.mul_sum]
          congr with n
          rw [Int.cast_pow]]
    rw [Real.exp_sum]
  rw [hrhs]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
  intro n hn
  have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
  rw [neg_mul, div_mul_comm, ← div_pow, ← mul_comm (2 : ℝ), mul_div_assoc,
    ← Int.cast_natCast n, abs_cos_period (hh'₁ _ hn).symm, Int.cast_natCast]
  apply (cos_bound_abs _).trans
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    have hNn : (n : ℝ) ≤ N := by
      exact_mod_cast hA _ hn
    have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hn0 hNn
    apply Real.exp_le_exp.mpr
    have hcmp : 2 * ((h' n : ℝ) / N) ^ 2 ≤ 2 * ((h' n : ℝ) / n) ^ 2 := by
      have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith
      field_simp [hn0.ne', hN0.ne']
      nlinarith [sq_nonneg ((h' n : ℝ)), hsq]
    linarith
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh'₂ _ hn

lemma minor1_bound_aux :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} {A : Finset ℕ},
      8 ≤ M → 0 ∉ A → 0 < T →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        ↑(lcmA A) ≤ exp ((T * K ^ 2) / (4 * N ^ 2)) := by
  obtain ⟨C, hC₀, hC⟩ := smooth_lcm
  filter_upwards
    [ Filter.eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop (4 * C)) ] with N hN₁ hN' K M T A hM hA hT hA₄
  change 4 * C ≤ log N at hN'
  have hN₁' : (1 : ℝ) < N := by
    exact_mod_cast hN₁
  have h₁ : (0 : ℝ) < N ^ 2 := by
    exact pow_pos (zero_lt_one.trans hN₁') 2
  have hden : 0 < (N : ℝ) ^ 2 * log N := by
    exact mul_pos h₁ (Real.log_pos hN₁')
  refine (hC _ (div_nonneg ?_ hden.le) _ hA hA₄).trans ?_
  · exact mul_nonneg hT.le (sq_nonneg K)
  rw [exp_le_exp, mul_div_assoc',
    div_le_div_iff₀ hden (mul_pos (show (0 : ℝ) < 4 by norm_num) h₁), mul_right_comm,
    mul_comm (T * K ^ 2), mul_comm _ (log N), ← mul_assoc C, mul_assoc, mul_assoc (log N),
    mul_comm C]
  exact mul_le_mul_of_nonneg_right hN' (mul_nonneg h₁.le (mul_nonneg hT.le (sq_nonneg K)))

lemma exists_representative (t : ℤ) {n : ℕ} (hn : n ≠ 0) :
    ∃ tn : ℤ, tn % n = t % n ∧ |tn| ≤ n / 2 := by
  refine ⟨Int.bmod t n, ?_, ?_⟩
  · exact
      (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
        (Int.emod_eq_zero_of_dvd Int.dvd_bmod_sub_self)
  · refine abs_le.mpr ?_
    constructor
    · simpa using Int.le_bmod (x := t) (m := n) (Nat.pos_of_ne_zero hn)
    · have hlt : Int.bmod t n < (n + 1) / 2 :=
        Int.bmod_lt (x := t) (m := n) (Nat.pos_of_ne_zero hn)
      omega

lemma missing_bridge_sum {A : Finset ℕ} {t : ℤ} {K M : ℝ} {I : Finset ℤ} {tn : ℕ → ℤ}
    (hK : 0 < K) (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (htn₁ : ∀ n : ℕ, n ∈ A → tn n % ↑n = t % ↑n)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) := by
  let A' := A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)
  have hsubset : A' ⊆ A := Finset.filter_subset _ _
  refine
    le_trans ?_
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => sq_nonneg _)
  have hcard : M * (K ^ 2 / 4) ≤ (A'.card : ℝ) * (K ^ 2 / 4) := by
    exact mul_le_mul_of_nonneg_right hI' (by positivity)
  refine hcard.trans ?_
  calc
    (A'.card : ℝ) * (K ^ 2 / 4) = A'.sum (fun _ : ℕ => K ^ 2 / 4) := by
      simp [nsmul_eq_mul]
    _ ≤ A'.sum (fun n => (tn n : ℝ) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
      have hnodvd : ∀ x ∈ I, ¬ ((n : ℤ) ∣ x) := (Finset.mem_filter.mp hn).2
      have hnotlt : ¬ |(tn n : ℝ)| < K / 2 := by
        intro hi
        have hi' := abs_lt.mp hi
        have hx : t - tn n ∈ I := by
          rw [hI, Finset.mem_Icc]
          constructor
          · refine Int.ceil_le.mpr ?_
            have hleft : (t : ℝ) - K / 2 < (t : ℝ) - (tn n : ℝ) := by
              linarith
            exact le_of_lt (by simpa using hleft)
          · refine Int.le_floor.mpr ?_
            have hright : (t : ℝ) - (tn n : ℝ) < (t : ℝ) + K / 2 := by
              linarith
            exact le_of_lt (by simpa using hright)
        have hcontra := hnodvd _ hx
        rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, eq_comm] at hcontra
        exact hcontra (htn₁ _ hnA)
      have habs : K / 2 ≤ |(tn n : ℝ)| := not_lt.mp hnotlt
      have hk2 : 0 ≤ K / 2 := by linarith
      calc
        K ^ 2 / 4 = (K / 2) ^ 2 := by ring
        _ ≤ |(tn n : ℝ)| ^ 2 := by
          nlinarith [habs, abs_nonneg (tn n : ℝ)]
        _ = (tn n : ℝ) ^ 2 := by rw [sq_abs]

lemma missing_bridge (A : Finset ℕ) {N : ℕ} {t : ℤ} {K M : ℝ} (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) {I : Finset ℤ} (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    cos_prod A t ≤ exp (- (M * K ^ 2 / (2 * N ^ 2))) := by
  have hrepr : ∀ n : ℕ, ∃ tn : ℤ, n ∈ A → tn % n = t % n ∧ |tn| ≤ n / 2 := by
    intro n
    by_cases hn : n ∈ A
    · have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
      obtain ⟨tn, htn₁, htn₂⟩ := exists_representative t hn'
      exact ⟨tn, fun _ => ⟨htn₁, htn₂⟩⟩
    · refine ⟨0, ?_⟩
      simp [hn]
  choose tn htn₁ htn₂ using hrepr
  refine (cos_prod_bound (A := A) (N := N) t hA' hA tn htn₁ ?_).trans ?_
  · intro n hn
    have hz : |tn n| ≤ n / 2 := htn₂ n hn
    have hzInt : (((tn n).natAbs : ℕ) : ℤ) ≤ (n / 2 : ℕ) := by
      have hz' := hz
      rw [Int.abs_eq_natAbs] at hz'
      exact hz'
    have hzReal : (((tn n).natAbs : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hzInt
    have hzReal' : |((tn n : ℤ) : ℝ)| ≤ ((n / 2 : ℕ) : ℝ) := by
      simpa [Int.cast_abs] using hzReal
    exact hzReal'.trans Nat.cast_div_le
  · have hsum : M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) :=
      missing_bridge_sum hK hI htn₁ hI'
    have hsum' : M * (K ^ 2 / 4) ≤ ↑(A.sum fun n => tn n ^ 2) := by
      simpa [Int.cast_sum, Int.cast_pow] using hsum
    have hmul :
        -((2 : ℝ) / N ^ 2) * ↑(A.sum fun n => tn n ^ 2) ≤
          -((2 : ℝ) / N ^ 2) * (M * (K ^ 2 / 4)) := by
      exact mul_le_mul_of_nonpos_left hsum'
        (neg_nonpos.2 (div_nonneg zero_le_two (sq_nonneg (N : ℝ))))
    refine (Real.exp_le_exp.mpr hmul).trans_eq ?_
    congr 1
    ring

lemma minor1_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} (k : ℕ) {A : Finset ℕ},
      8 ≤ M → A.Nonempty → (∀ n ∈ A, M ≤ ↑n) → 0 < K → 0 < T →
      (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [minor1_bound_aux] with N hNaux K M T k A hM hAne hLower hK hT hUpper hSmooth
  have hA0 : 0 ∉ A := by
    intro h0
    have : M ≤ 0 := by simpa using hLower 0 h0
    linarith
  suffices hpoint :
      ∀ h ∈ minor_arc₁ A k K T, cos_prod A (h * k) ≤ ((lcmA A : ℝ) ^ 2)⁻¹ by
    have hsum :
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤
          ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (minor_arc₁ A k K T) (fun h => cos_prod A (h * k))
          (((lcmA A : ℝ) ^ 2)⁻¹) hpoint)
    refine hsum.trans ?_
    have hjsubset : j A ⊆ valid_sum_range (lcmA A) := by
      intro x hx
      rw [j, Finset.mem_erase] at hx
      exact hx.2
    have hcard : ((minor_arc₁ A k K T).card : ℝ) ≤ lcmA A := by
      exact_mod_cast
        (Finset.card_le_card ((Finset.filter_subset _ _).trans Finset.sdiff_subset)).trans
          ((Finset.card_le_card hjsubset).trans_eq (card_valid_sum_range _))
    have hlcmge : (8 : ℝ) ≤ lcmA A := by
      obtain ⟨n, hn⟩ := hAne
      have hnle : (8 : ℝ) ≤ n := hM.trans (hLower n hn)
      exact hnle.trans (by
        exact_mod_cast Nat.le_of_dvd
          (Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0))
          (Finset.dvd_lcm hn))
    have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
    calc
      ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹)
          = ((minor_arc₁ A k K T).card : ℝ) / (lcmA A : ℝ) ^ 2 := by
              rw [div_eq_mul_inv]
      _ ≤ (lcmA A : ℝ) / (lcmA A : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
      _ = 1 / (lcmA A : ℝ) := by
        field_simp [hlcm0]
      _ ≤ 1 / 8 := by
        exact one_div_le_one_div_of_le (by norm_num) hlcmge
      _ = (8 : ℝ)⁻¹ := by norm_num
  intro h hh
  rw [minor_arc₁, Finset.mem_filter] at hh
  have hI : I h K k =
      Finset.Icc ⌈((h * k : ℤ) : ℝ) - K / 2⌉ ⌊((h * k : ℤ) : ℝ) + K / 2⌋ := by
    simp [I, integer_range]
  refine (missing_bridge (A := A) (N := N) (t := h * k) hA0 hUpper hK hI hh.2).trans ?_
  have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
  have hlcmpos : 0 < (lcmA A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0)
  rw [Real.exp_neg]
  refine (inv_le_inv₀ (Real.exp_pos _) (sq_pos_iff.2 hlcm0)).2 ?_
  refine (pow_le_pow_left₀ hlcmpos.le (hNaux hM hA0 hT hSmooth) 2).trans ?_
  refine le_of_eq ?_
  rw [sq, ← Real.exp_add]
  congr 1
  ring_nf

lemma prod_swapping {A : Finset ℕ} (x : ℕ → ℝ) :
    A.prod
        (fun n => ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).prod (fun _ => x n)) =
      (ppowers_in_set A).prod (fun q => (local_part A q).prod x) := by
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  simp only [← Finset.prod_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr local_part_subset]

lemma minor2_ind_bound_part_one {N : ℕ} {A : Finset ℕ} {t : ℤ}
    (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N) :
    cos_prod A t ≤
      (ppowers_in_set A).prod (fun q => (cos_prod (local_part A q) t) ^ (2 * log N)⁻¹) := by
  let Q_ : ℕ → Finset ℕ :=
    fun n ↦ (ppowers_in_set A).filter (fun q => n ∈ local_part A q)
  have hq : ∀ n ∈ A, ((Q_ n).card : ℝ) ≤ 2 * log N := by
    intro n hn
    have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlogn_nonneg : 0 ≤ log n := by
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
    have htriv : ((Q_ n).card : ℝ) ≤ log n / log 2 := by
      simpa [Q_] using (triv_q_bound hA n)
    refine htriv.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul ?_ (Real.log_le_log hnpos (by exact_mod_cast hA' n hn)) hlogn_nonneg
      zero_le_two
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
    simpa [one_div] using ((one_div_le (Real.log_pos one_lt_two) zero_lt_two).2 hhalf)
  simp only [cos_prod]
  have hrewrite :
      (ppowers_in_set A).prod
          (fun q => (∏ n ∈ local_part A q, |cos (Real.pi * t / n)|) ^ (2 * log N)⁻¹) =
        (ppowers_in_set A).prod
          (fun q => ∏ n ∈ local_part A q, |cos (Real.pi * t / n)| ^ (2 * log N)⁻¹) := by
    refine Finset.prod_congr rfl ?_
    intro q hq'
    symm
    exact Real.finset_prod_rpow _ _ (fun n hn ↦ abs_nonneg _) _
  rw [hrewrite, ← prod_swapping]
  change ∏ n ∈ A, |cos (Real.pi * t / n)| ≤
    ∏ n ∈ A, ∏ _x ∈ Q_ n, |cos (Real.pi * t / n)| ^ (2 * log N)⁻¹
  simp_rw [Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) ?_
  intro n hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  refine Real.self_le_rpow_of_le_one (abs_nonneg _) (abs_cos_le_one _) ?_
  rw [← div_eq_inv_mul]
  refine (div_le_one ?_).2 (hq n hn)
  exact mul_pos zero_lt_two (Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN))

lemma minor2_ind_bound {N : ℕ} {A : Finset ℕ} {t : ℤ} {K L : ℝ} (I : Finset ℤ)
    (hA : 0 ∉ A) (hK : 0 < K) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) :
    cos_prod A t ≤ N ^ (-4 * (ppowers_in_set A \ interval_rare_ppowers I A L).card : ℝ) := by
  refine (minor2_ind_bound_part_one hA hA' hN).trans ?_
  rw [← Finset.prod_sdiff (interval_rare_ppowers_subset I L)]
  suffices hq' :
      ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
        cos_prod (local_part A q) t ≤ (N : ℝ) ^ (-8 * log N) by
    have hq'' :
        ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ (N : ℝ) ^ (-4 : ℝ) := by
      intro q hq
      have hlogpos : 0 < log (N : ℝ) := by
        exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
      calc
        cos_prod (local_part A q) t ^ (2 * log N)⁻¹
            ≤ ((N : ℝ) ^ (-8 * log N)) ^ (2 * log N)⁻¹ :=
              Real.rpow_le_rpow cos_prod_nonneg (hq' q hq)
                (inv_nonneg.2 <| mul_nonneg zero_le_two <|
                  Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hN)))
        _ = (N : ℝ) ^ (-4 : ℝ) := by
            rw [← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
            congr 2
            field_simp [hlogpos.ne']
            ring
    have hq''' :
        ∀ q ∈ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ 1 := by
      intro q hq
      apply Real.rpow_le_one cos_prod_nonneg cos_prod_le_one
      rw [inv_nonneg]
      exact mul_nonneg zero_le_two <| Real.log_nonneg <| by
        rw [Nat.one_le_cast]
        exact one_le_two.trans hN
    have hprod₁ :
        ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
            cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L, (N : ℝ) ^ (-4 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg cos_prod_nonneg _
      · intro q hq
        exact hq'' q hq
    have hprod₂ :
        ∏ q ∈ interval_rare_ppowers I A L, cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ interval_rare_ppowers I A L, (1 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg cos_prod_nonneg _
      · intro q hq
        exact hq''' q hq
    refine (mul_le_mul hprod₁ hprod₂ ?_ ?_).trans ?_
    · exact Finset.prod_nonneg fun i hi ↦ Real.rpow_nonneg cos_prod_nonneg _
    · exact
        Finset.prod_nonneg fun i hi ↦
          Real.rpow_nonneg (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N) _
    · rw [Finset.prod_const, Finset.prod_const_one, mul_one, ← Real.rpow_natCast,
        ← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
  intro q hq'
  have hqmem : q ∈ ppowers_in_set A := (Finset.mem_sdiff.mp hq').1
  have hqnot : q ∉ interval_rare_ppowers I A L := (Finset.mem_sdiff.mp hq').2
  have hqcount :
      L / q ≤
        (((local_part A q).filter
            fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := (local_part A q).image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) =
          (((local_part A q).filter
              fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    by_contra hlt
    apply hqnot
    rw [interval_rare_ppowers, Finset.mem_filter]
    have hlt' :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q := by
      rw [hcardeq]
      exact not_le.mp hlt
    simpa [sZ, Finset.bind_def, Finset.pure_def, Finset.biUnion_singleton] using
      (show q ∈ ppowers_in_set A ∧
          (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q from
        ⟨hqmem, hlt'⟩)
  refine (missing_bridge (A := local_part A q) (M := L / q) (zero_mem_local_part_iff hA)
    (fun _ hn ↦ hA' _ (filter_subset _ _ hn)) hK hI hqcount).trans ?_
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast zero_lt_two.trans_le hN
  have hlogpos : 0 < log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  rw [← Real.le_log_iff_exp_le (Real.rpow_pos_of_pos hN0 _), Real.log_rpow hN0]
  have hqpos : 0 < (q : ℝ) := by
    rw [Nat.cast_pos]
    rw [mem_ppowers_in_set] at hqmem
    exact hqmem.1.pos
  have hqbound : (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := hq q hqmem
  have hqbound' : 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 * q ≤ L * K ^ 2 := by
    have hden' : 0 < 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 := by positivity
    have hmul : q * (16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2) ≤ L * K ^ 2 := by
      exact (_root_.le_div_iff₀ hden').1 hqbound
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmain : 8 * log (N : ℝ) * log (N : ℝ) ≤ L * K ^ 2 / (2 * N ^ 2 * q) := by
    have hden : 0 < 2 * (N : ℝ) ^ 2 * q := by positivity
    refine (_root_.le_div_iff₀ hden).2 ?_
    nlinarith [hqbound', sq_nonneg (log (N : ℝ))]
  have hdiv : L / q * K ^ 2 / (2 * N ^ 2) = L * K ^ 2 / (2 * N ^ 2 * q) := by
    field_simp [hqpos.ne']
  rw [hdiv]
  nlinarith [hmain]

lemma powerset_sum_pow {α : Type*} {s : Finset α} {x : ℝ} :
    s.powerset.sum (fun t => x ^ t.card) = (1 + x) ^ s.card := by
  simpa using (Finset.prod_one_add (s := s) (f := fun _ : α => x)).symm

lemma powerset_sum_pow' {α : Type*} [DecidableEq α] {s : Finset α} {x : ℝ} :
    s.powerset.sum (fun t => x ^ (s \ t).card) = (1 + x) ^ s.card := by
  calc
    s.powerset.sum (fun t => x ^ (s \ t).card) = s.powerset.sum (fun t => x ^ t.card) := by
      refine Finset.sum_bij' (i := fun t _ => s \ t) (j := fun t _ => s \ t) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        rfl
    _ = (1 + x) ^ s.card := powerset_sum_pow

lemma lcm_Q {A : Finset ℕ} (hA : 0 ∉ A) : lcmA (ppowers_in_set A) = lcmA A := by
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd_iff.2 ?_
    intro i hi
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff i).1 (mem_ppowers_in_set.1 hi).1
    rw [mem_ppowers_in_set' hp hk.ne'] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    exact (Nat.ordProj_dvd _ _).trans (Finset.dvd_lcm hn)
  · refine Finset.lcm_dvd_iff.2 ?_
    intro n hn
    have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hpow : p ^ n.factorization p ∣ lcmA (ppowers_in_set A) := by
      by_cases hnp : n.factorization p = 0
      · simp [hnp]
      · apply Finset.dvd_lcm
        rw [mem_ppowers_in_set' hp hnp]
        exact ⟨n, hn, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · exact (pow_dvd_pow _ ((hp.pow_dvd_iff_le_factorization hn').1 hpk)).trans hpow

lemma d_strict_subset {K L δ : ℝ} {k : ℕ} {A : Finset ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (z : ∀ h ∈ minor_arc₂ A k K δ,
      ∃ x ∈ I h K k, ↑(lcmA (interval_rare_ppowers (I h K k) A L)) ∣ x) :
    (minor_arc₂ A k K δ).filter
        (fun h => interval_rare_ppowers (I h K k) A L ⊂ ppowers_in_set A) =
      minor_arc₂ A k K δ := by
  ext h
  constructor
  · intro hh
    exact (Finset.mem_filter.mp hh).1
  · intro hh
    rw [Finset.mem_filter]
    refine ⟨hh, (Finset.ssubset_iff_subset_ne.2 ?_)⟩
    refine ⟨interval_rare_ppowers_subset (I h K k) L, ?_⟩
    intro hEq
    have hhminor : h ∈ minor_arc₂ A k K δ := hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hh, _⟩
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rcases z h hhminor with ⟨x, hxI, hdivx⟩
    rw [hEq, lcm_Q hA] at hdivx
    rcases hdivx with ⟨t, rfl⟩
    have hxI' : (|h * k - t * lcmA A| : ℝ) ≤ K / 2 := by
      have hxI'' := (mem_I' (h := h) (K := K) (k := k) (z := (lcmA A : ℤ) * t)).1 hxI
      simpa [Int.cast_mul, mul_comm, mul_left_comm, mul_assoc, abs_sub_comm] using hxI''
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, (mem_major_arc_at' hk h).2 ⟨hj, hxI'⟩⟩⟩

lemma cast_lcm {x y : ℕ} : (lcm x y : ℤ) = lcm (x : ℤ) y := by
  rw [← Int.coe_lcm]

lemma Finset.cast_lcm {x : Finset ℕ} : ((x.lcm id : ℕ) : ℤ) = x.lcm (fun n => (n : ℤ)) := by
  classical
  refine Finset.induction_on x ?_ ?_
  · simp
  · intro a s ha hs
    simpa only [Finset.lcm_insert, id_eq] using
      hs ▸ (Erdos45.cast_lcm (x := a) (y := s.lcm id))

lemma cast_lcm_dvd {x : Finset ℕ} {z : ℤ} (h : ∀ i ∈ x, ↑i ∣ z) :
    ↑(lcmA x) ∣ z := by
  rw [Finset.cast_lcm]
  exact Finset.lcm_dvd h

lemma ssubsets_subset_powerset {α : Type*} [DecidableEq α] {s : Finset α} :
    s.ssubsets ⊆ s.powerset := by
  intro t ht
  exact Finset.mem_powerset.2 (Finset.mem_ssubsets.1 ht).1

lemma thing_le_four {N : ℕ} : ((N : ℝ)⁻¹ + 1) ^ N ≤ 4 := by
  rcases eq_or_ne N 0 with rfl | hN
  · norm_num
  · refine le_trans ?_ (Real.exp_one_lt_d9.le.trans (by norm_num))
    refine (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp ((N : ℝ)⁻¹)) N).trans ?_
    rw [← Real.exp_nat_mul ((N : ℝ)⁻¹) N]
    simp [hN]

lemma ppowers_in_set_le {N : ℕ} {A : Finset ℕ} (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    ∀ q ∈ ppowers_in_set A, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨n, hnA, hq⟩
  rw [Finset.mem_filter, Nat.mem_divisors] at hq
  rcases hq with ⟨⟨hqdiv, hn0⟩, hpp, _⟩
  constructor
  · exact hpp.one_lt.le
  · exact (Nat.le_of_dvd hn0.bot_lt hqdiv).trans (hA' n hnA)

lemma minor2_bound_end {k : ℕ} {A : Finset ℕ} (N : ℕ) (hN : 2 ≤ N) (hkN : k ≤ N / 192)
    (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) ≤
      8⁻¹ := by
  have hcard : (ppowers_in_set A).card ≤ N := by
    suffices hsubset : ppowers_in_set A ⊆ Finset.Icc 1 N by
      calc
        (ppowers_in_set A).card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsubset
        _ = N := by
          rw [Nat.card_Icc]
          omega
    intro x hx
    simpa [Finset.mem_Icc] using ppowers_in_set_le hA' x hx
  calc
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card)
        ≤
      6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).powerset.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (ssubsets_subset_powerset (s := ppowers_in_set A))
              (fun _ _ _ ↦ pow_nonneg (by positivity) _)
          · positivity
    _ = 6 * (k : ℝ) * (N : ℝ)⁻¹ * (1 + (N : ℝ)⁻¹) ^ (ppowers_in_set A).card := by
          rw [powerset_sum_pow' (s := ppowers_in_set A) (x := (N : ℝ)⁻¹), add_comm]
    _ ≤ 6 * (k : ℝ) * (N : ℝ)⁻¹ * 4 := by
          have hbase : (1 : ℝ) ≤ 1 + (N : ℝ)⁻¹ := by
            nlinarith [show 0 ≤ (N : ℝ)⁻¹ by positivity]
          have hfour : (1 + (N : ℝ)⁻¹) ^ N ≤ 4 := by
            simpa [add_comm] using (thing_le_four (N := N))
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact (pow_le_pow_right₀ hbase hcard).trans hfour
          · positivity
    _ ≤ 8⁻¹ := by
          have hkN' : (k : ℝ) ≤ (N : ℝ) / 192 := by
            calc
              (k : ℝ) ≤ ((N / 192 : ℕ) : ℝ) := by exact_mod_cast hkN
              _ ≤ (N : ℝ) / 192 := Nat.cast_div_le
          have hN' : 0 < (N : ℝ) := by
            exact_mod_cast zero_lt_two.trans_le hN
          calc
            6 * (k : ℝ) * (N : ℝ)⁻¹ * 4
                ≤ 6 * ((N : ℝ) / 192) * (N : ℝ)⁻¹ * 4 := by
                  gcongr
            _ = 8⁻¹ := by
                field_simp [hN'.ne']
                norm_num

lemma count_multiples {m n : ℕ} (hm : 1 ≤ m) :
    ((Finset.Icc 1 n).filter fun k => m ∣ k).card = n / m := by
  have hcard : (Finset.Icc 1 (n / m)).card = n / m := by
    simp [Nat.card_Icc]
  rw [← hcard]
  refine (Finset.card_bij (fun i _ => i * m) ?_ ?_ ?_).symm
  · intro i hi
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ?_, dvd_mul_left _ _⟩
    constructor
    · exact one_le_mul (Finset.mem_Icc.1 hi).1 hm
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).1
        (Finset.mem_Icc.1 hi).2
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_right (lt_of_lt_of_le Nat.zero_lt_one hm)
      (by simpa [Nat.mul_comm] using hij)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxdiv⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    rcases hxdiv with ⟨z, rfl⟩
    refine ⟨z, Finset.mem_Icc.2 ?_, by simp [Nat.mul_comm]⟩
    constructor
    · exact Nat.succ_le_of_lt <|
        Nat.pos_of_mul_pos_left (lt_of_lt_of_le Nat.zero_lt_one hx1)
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).2
        (by simpa [Nat.mul_comm] using hx2)

lemma count_multiples' {m : ℕ} {n : ℝ} (hm : 1 ≤ m) (hn : 0 ≤ n) :
    ↑((Finset.Icc 1 ⌊n⌋₊).filter fun k => m ∣ k).card ≤ n / m := by
  rw [count_multiples hm]
  refine (Nat.cast_div_le).trans ?_
  exact div_le_div_of_nonneg_right (Nat.floor_le hn) (by positivity)

lemma count_real_multiples' {m : ℕ} {x y : ℝ} (hxy : x ≤ y) (hm : 1 ≤ m) :
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ (y - x) / m + 1 := by
  let s : Finset ℤ := integer_range ((x + y) / (2 * (m : ℝ))) ((y - x) / (2 * (m : ℝ)))
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hsub :
      (Finset.Icc ⌈x⌉ ⌊y⌋).filter (fun k => (m : ℤ) ∣ k) ⊆
        s.image fun z : ℤ => (m : ℤ) * z := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkdiv⟩
    rcases Finset.mem_Icc.mp hkIcc with ⟨hkx, hky⟩
    rcases hkdiv with ⟨z, rfl⟩
    refine Finset.mem_image.mpr ⟨z, ?_, by simp⟩
    rw [mem_integer_range_iff, abs_le]
    have hx' : x ≤ (m : ℝ) * z := by
      have hx'' : x ≤ (((m : ℤ) * z : ℤ) : ℝ) := Int.ceil_le.mp hkx
      simpa using hx''
    have hy' : (m : ℝ) * z ≤ y := by
      have hy'' : ((((m : ℤ) * z : ℤ) : ℝ)) ≤ y := Int.le_floor.mp hky
      simpa using hy''
    constructor
    · field_simp [hm0']
      linarith
    · field_simp [hm0']
      linarith
  have hcard1 :
      ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤
        (s.image fun z : ℤ => (m : ℤ) * z).card :=
    Finset.card_le_card hsub
  have hcard2 : (s.image fun z : ℤ => (m : ℤ) * z).card ≤ s.card := Finset.card_image_le
  have hcard : ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ s.card :=
    Nat.le_trans hcard1 hcard2
  calc
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ ↑s.card := by
      exact_mod_cast hcard
    _ ≤ 2 * ((y - x) / (2 * (m : ℝ))) + 1 := by
      simpa [s] using
        (card_integer_range_le (x := (x + y) / (2 * (m : ℝ)))
          (y := (y - x) / (2 * (m : ℝ)))
          (by exact div_nonneg (sub_nonneg.mpr hxy) (by positivity)))
    _ = (y - x) / m + 1 := by ring_nf

lemma count_real_multiples {m : ℕ} {K : ℝ} {t : ℤ} (hK : 0 < K) (hm : 1 ≤ m) :
    ↑((integer_range t K).filter fun k => (m : ℤ) ∣ k).card ≤ (2 * K) / m + 1 := by
  simpa [integer_range, two_mul] using
    (count_real_multiples' (x := (t : ℝ) - K) (y := (t : ℝ) + K)
      (show (t : ℝ) - K ≤ (t : ℝ) + K by linarith) hm)

lemma candidate_count_one {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (_hN : 2 ≤ N) (_hA : 0 ∉ A) (hK : 1 ≤ K) (_hL : 0 < L) (hk : k ≠ 0)
    (_hKN : K ≤ ↑N)
    (_hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by
  classical
  let R : ℝ := ((k : ℝ) * lcmA A + K) / 2
  let s : Finset ℤ := (integer_range 0 R).filter fun x => (lcmA D : ℤ) ∣ x
  let f : ℤ → Finset ℤ := fun x => (j A).filter fun h => x ∈ I h K k
  have hDsub : D ⊆ ppowers_in_set A := (Finset.mem_ssubsets.1 hD).1
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hDsub h0)
  have hlcmD : 1 ≤ lcmA D := Nat.one_le_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hsubset :
      (minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D) ⊆
        s.biUnion f := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hhminor, hrare⟩
    rcases z h hhminor with ⟨x, hxI, hxdiv⟩
    have hhj : h ∈ j A := by
      rw [minor_arc₂, Finset.mem_sdiff] at hhminor
      exact (Finset.mem_sdiff.mp hhminor.1).1
    have hxdiv' : (lcmA D : ℤ) ∣ x := by
      simpa [hrare] using hxdiv
    have hxI' : (|(h * k : ℝ) - x|) ≤ K / 2 := by
      exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hxI
    have hhbound : |(h * k : ℝ)| ≤ (k : ℝ) * lcmA A / 2 := by
      calc
        |(h * k : ℝ)| = |(h : ℝ)| * (k : ℝ) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ k by positivity)]
        _ ≤ ((lcmA A : ℝ) / 2) * (k : ℝ) := by
          gcongr
          exact bound_of_mem_j A h hhj
        _ = (k : ℝ) * lcmA A / 2 := by ring
    have hxbound : |(x : ℝ)| ≤ R := by
      dsimp [R]
      calc
        |(x : ℝ)| = |((x : ℝ) - h * k) + h * k| := by ring_nf
        _ ≤ |(x : ℝ) - h * k| + |(h * k : ℝ)| := abs_add_le _ _
        _ ≤ K / 2 + (k : ℝ) * lcmA A / 2 := by
          exact add_le_add (by simpa [abs_sub_comm] using hxI') hhbound
        _ = ((k : ℝ) * lcmA A + K) / 2 := by ring
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact
        ⟨(mem_integer_range_iff (x := 0) (y := R) (z := x)).2 (by simpa [R] using hxbound),
          hxdiv'⟩
    · rw [Finset.mem_filter]
      exact ⟨hhj, hxI⟩
  have hfiber :
      ∀ x ∈ s, (((f x).card : ℝ)) ≤ K + 1 := by
    intro x hx
    have hsubx : f x ⊆ integer_range ((x : ℝ) / k) (K / (2 * k)) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [mem_integer_range_iff]
      have hxI : |(h * k : ℝ) - x| ≤ K / 2 := by
        exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hh.2
      have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
        field_simp [hk0]
      rw [hdiv]
      apply (le_div_iff₀ hkpos).2
      calc
        |(x : ℝ) / k - h| * (k : ℝ) = |(x : ℝ) / k - h| * |(k : ℝ)| := by
          rw [abs_of_pos hkpos]
        _ = |((x : ℝ) / k - h) * k| := by rw [← abs_mul]
        _ = |(x : ℝ) - h * k| := by
          congr 1
          field_simp [hk0]
        _ = |(h * k : ℝ) - x| := by rw [abs_sub_comm]
        _ ≤ K / 2 := hxI
    calc
      (((f x).card : ℝ)) ≤ ((integer_range ((x : ℝ) / k) (K / (2 * k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubx
      _ ≤ 2 * (K / (2 * k)) + 1 := by
        apply card_integer_range_le
        positivity
      _ = K / k + 1 := by
        field_simp [hk0]
      _ ≤ K + 1 := by
        have hdivle : K / k ≤ K := by
          apply (div_le_iff₀ (show (0 : ℝ) < k by exact_mod_cast Nat.pos_of_ne_zero hk)).2
          have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        linarith
  have hs : ((s.card : ℝ)) ≤ ((k : ℝ) * lcmA A + K) / lcmA D + 1 := by
    simpa [s, R, two_mul] using
      (count_real_multiples (m := lcmA D) (K := R) (t := 0) hRpos hlcmD)
  calc
    ((((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℕ) : ℝ)
        ≤ ((s.biUnion f).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ x ∈ s, (((f x).card : ℝ)) := by
          exact_mod_cast (Finset.card_biUnion_le (s := s) (t := f))
    _ ≤ ∑ x ∈ s, (K + 1) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hfiber x hx
    _ = (s.card : ℝ) * (K + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((((k : ℝ) * lcmA A + K) / lcmA D + 1) : ℝ) * (K + 1) := by
          exact mul_le_mul_of_nonneg_right hs (by linarith)
    _ = (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by ring

lemma candidate_count {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (hN : 2 ≤ N) (hA : 0 ∉ A) (hK : 1 ≤ K) (hL : 0 < L) (hk : k ≠ 0) (hKN : K ≤ ↑N)
    (hA' : ∀ n ∈ A, n ≤ N)
    (hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
  refine (candidate_count_one hN hA hK hL hk hKN hq z hD).trans ?_
  rw [Finset.mem_ssubsets] at hD
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hD.1 h0)
  have hlcmDpos_nat : 0 < lcmA D := Nat.pos_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have h₁ :
      (lcmA A : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by
    have hprod :
        Finset.prod (ppowers_in_set A \ D) (fun q => q) ≤ N ^ (ppowers_in_set A \ D).card := by
      simpa using
        (Finset.prod_le_pow_card (s := ppowers_in_set A \ D) (f := fun q => q) (n := N)
          (fun q hq => (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).2))
    have hdiv :
        lcmA A ∣ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      rw [← lcm_Q hA]
      refine Finset.lcm_dvd_iff.2 ?_
      intro q hq
      by_cases hqD : q ∈ D
      · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
      · exact dvd_mul_of_dvd_left (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _
    have hnat :
        lcmA A ≤ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      refine Nat.le_of_dvd ?_ hdiv
      refine Nat.mul_pos (Finset.prod_pos ?_) hlcmDpos_nat
      intro q hq
      exact (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).1
    exact_mod_cast hnat.trans (Nat.mul_le_mul_right _ hprod)
  have h₂ : K + 1 ≤ 2 * N := by
    linarith
  have h₃ : (1 : ℝ) ≤ lcmA D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have h₄ : (1 : ℝ) ≤ k := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hdiff_nonempty : (ppowers_in_set A \ D).Nonempty := by
    refine Finset.sdiff_nonempty.2 ?_
    intro hsub
    exact hD.2 hsub
  have h₅ : (N : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N by omega)
    have hcard1 : 1 ≤ (ppowers_in_set A \ D).card := by
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr hdiff_nonempty)
    simpa [pow_one] using (pow_le_pow_right₀ hN1 hcard1)
  have hlcmDpos : 0 < (lcmA D : ℝ) := by
    exact_mod_cast hlcmDpos_nat
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by positivity
  have hterm_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by positivity
  have hmul₁ :
      (k : ℝ) * lcmA A ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    exact mul_le_mul_of_nonneg_left h₁ hk_nonneg
  have hmul₂ : K ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    refine (hKN.trans h₅).trans ?_
    refine (le_mul_of_one_le_right hpow_nonneg h₃).trans ?_
    exact le_mul_of_one_le_left hterm_nonneg h₄
  have hdivbound :
      (((k : ℝ) * lcmA A + K) / lcmA D) ≤
        2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) := by
    apply (_root_.div_le_iff₀ hlcmDpos).2
    have hsum :
        (k : ℝ) * lcmA A + K ≤
          2 * ((k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D)) := by
      linarith
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  have hmain :
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
        4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
    have hinner :
        (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
          2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1 := by
      linarith
    calc
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1)
          ≤ (2 * N) * (2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1) := by
            refine mul_le_mul h₂ hinner ?_ ?_
            · positivity
            · linarith
      _ = 4 * (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * N) + 2 * N := by
            ring
      _ = 4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
            congr 2
            rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ]
  refine hmain.trans ?_
  have hNle :
      (N : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card := by
      refine one_le_mul_of_one_le_of_one_le h₄ ?_
      exact (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)).trans h₅
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ, ← mul_assoc]
    simpa [mul_assoc, mul_left_comm, mul_comm] using (le_mul_of_one_le_right hNnonneg hN1)
  linarith

lemma minor2_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K L T : ℝ} {k : ℕ} {A : Finset ℕ},
      0 ∉ A → 1 ≤ K → 0 < L → k ≠ 0 → k ≤ N / 192 → K ≤ N →
        (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) →
      (∀ (t : ℝ) (I : Finset ℤ), I = Finset.Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
        T ≤ (A.filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card ∨
          ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, (q : ℤ) ∣ x) →
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with
    N hN K L T k A hA hK hL hk hkN hKN hA' hq hI
  have hgood :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ∀ q ∈ interval_rare_ppowers (I h K k) A L, (q : ℤ) ∣ x := by
    intro h hh
    refine (hI (t := (h * k : ℝ)) (I := I h K k) (by simp [I, integer_range])).resolve_left ?_
    rw [minor_arc₂_eq, Finset.mem_filter] at hh
    letI : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) =
          (((A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card : ℝ)) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    have hh' : (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) < T := by
      rw [hcardeq]
      exact hh.2
    simpa [sZ] using (not_le.mpr hh')
  have hz :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x := by
    intro h hh
    rcases hgood h hh with ⟨x, hx, hx'⟩
    exact ⟨x, hx, cast_lcm_dvd hx'⟩
  have hcard :
      ∀ D ∈ (ppowers_in_set A).ssubsets,
        (((minor_arc₂ A k K T).filter
            fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
          6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    intro D hD
    exact candidate_count hN hA hK hL hk hKN hA' hq hz hD
  have hsumD :
      ∀ D,
        D ∈ (ppowers_in_set A).ssubsets →
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)) ≤
            6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card := by
    intro D hD
    refine
      (Finset.sum_le_card_nsmul
        _ _ ((N : ℝ) ^ (-4 * (ppowers_in_set A \ D).card : ℝ)) ?_).trans ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      rw [← hh.2]
      refine minor2_ind_bound (I h K k) hA (by linarith) hA' hN ?_ hq
      simp [I, integer_range]
    · rw [nsmul_eq_mul]
      refine (mul_le_mul_of_nonneg_right (hcard D hD)
        (Real.rpow_nonneg (show 0 ≤ (N : ℝ) by positivity) _)).trans ?_
      have hNpos : 0 < (N : ℝ) := by
        exact_mod_cast zero_lt_two.trans_le hN
      rw [mul_assoc, ← Real.rpow_add hNpos, mul_assoc (6 * (k : ℝ)), ← Real.rpow_neg_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (by positivity))
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast one_le_two.trans hN
      · have hcard1 : (1 : ℝ) ≤ (ppowers_in_set A \ D).card := by
          rw [Nat.one_le_cast, Nat.succ_le_iff, Finset.card_pos, Finset.sdiff_nonempty]
          rw [Finset.mem_ssubsets] at hD
          exact hD.2
        linarith
  have hsum :
      Finset.sum (ppowers_in_set A).ssubsets
          (fun D =>
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)))
        ≤
          Finset.sum (ppowers_in_set A).ssubsets
            (fun D =>
              6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card) := by
    refine Finset.sum_le_sum ?_
    intro D hD
    exact hsumD D hD
  simp only [Finset.sum_filter] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_ssubsets] at hsum
  rw [← Finset.sum_filter, d_strict_subset hA hk hz, ← Finset.mul_sum] at hsum
  exact hsum.trans (minor2_bound_end N hN hkN hA')

theorem circle_method_prop2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ {K L M T : ℝ} {k : ℕ} {A : Finset ℕ},
        0 < T → 0 < L → 8 ≤ K → K < M → M ≤ N → k ≠ 0 → (k : ℝ) ≤ M / 192 →
        (∀ n ∈ A, M ≤ ↑n) → (∀ n ∈ A, n ≤ N) → rec_sum A < 2 / k →
        (2 : ℝ) / k - 1 / M ≤ rec_sum A → k ∣ (A.lcm id : ℕ) →
        (∀ q ∈ ppowers_in_set A,
          ↑q ≤
            min (L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2))
              (min (c * M / k) (T * K ^ 2 / (N ^ 2 * log N)))) →
        good_condition A K T L → ∃ S ⊆ A, rec_sum S = 1 / k := by
  obtain ⟨C, hC₀, hClcm⟩ := smooth_lcm
  let C' : ℝ := max C 1
  let c : ℝ := log 2 / C'
  have hC'ge : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hC'one : (1 : ℝ) ≤ C' := by
    dsimp [C']
    exact le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one hC'one
  have hc₀ : 0 < c := by
    dsimp [c]
    exact div_pos (Real.log_pos one_lt_two) hC'pos
  refine ⟨c, hc₀, ?_⟩
  filter_upwards [minor1_bound, minor2_bound] with
    N hm1 hm2 K L M T k A hT hL hK hKM hMN hk hkM hA₁ hA₂ hA₃ hA₄ hkA hq hI
  have hM₀ : 0 < M := by
    linarith
  have hk₀ : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hk₀ne : (k : ℝ) ≠ 0 := hk₀.ne'
  have hcCkM : C * (c * M / k) / log 2 / M + 1 / M + 1 / M ≤ 2 / k := by
    have hterm1 : C * (c * M / k) / log 2 / M ≤ (1 : ℝ) / k := by
      have hEq : C * (c * M / k) / log 2 / M = (C / C') / k := by
        dsimp [c]
        field_simp [hk₀ne, hM₀.ne', hC'pos.ne', (Real.log_pos one_lt_two).ne']
      calc
        C * (c * M / k) / log 2 / M = (C / C') / k := hEq
        _ ≤ 1 / k := by
          have hdiv : C / C' ≤ 1 := by
            rw [div_le_iff₀ hC'pos]
            simpa using hC'ge
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hdiv (inv_nonneg.2 hk₀.le)
    have hterm2 : 1 / M + 1 / M ≤ (1 : ℝ) / k := by
      have hkM2 : (2 : ℝ) * k ≤ M := by
        nlinarith
      have hdiv : (2 : ℝ) / M ≤ (1 : ℝ) / k := by
        exact (div_le_div_iff₀ hM₀ hk₀).2 (by simpa [mul_comm] using hkM2)
      simpa [two_mul, div_eq_mul_inv] using hdiv
    have hsum : C * (c * M / k) / log 2 / M + (1 / M + 1 / M) ≤ 1 / k + 1 / k := by
      exact add_le_add hterm1 hterm2
    calc
      C * (c * M / k) / log 2 / M + 1 / M + 1 / M
          = C * (c * M / k) / log 2 / M + (1 / M + 1 / M) := by ring
      _ ≤ 1 / k + 1 / k := hsum
      _ = 2 / k := by ring
  have hA₅ : A.Nonempty := by
    by_contra hA₅
    rw [Finset.not_nonempty_iff_eq_empty] at hA₅
    subst hA₅
    have hA₄' : (2 : ℝ) / k - 1 / M ≤ 0 := by
      simpa using hA₄
    have hbad'' : (2 : ℝ) / k ≤ 1 / M := by
      linarith
    have hbad' : (2 : ℝ) * M ≤ k := by
      simpa using (div_le_div_iff₀ hk₀ hM₀).mp hbad''
    nlinarith
  have hq' :
      ∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) ∧
          (q : ℝ) ≤ c * M / k ∧ (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    simpa [le_min_iff, and_assoc] using hq
  have hq₁ :
      ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := by
    intro q hqpp
    exact (hq' q hqpp).1
  have hq₂ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
    intro q hqpp
    exact (hq' q hqpp).2.1
  have hq₃ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    intro q hqpp
    exact (hq' q hqpp).2.2
  have hm1' :
      (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm1 (K := K) (M := M) (T := T) (k := k) (A := A) (hK.trans hKM.le) hA₅ hA₁
      (by linarith) hT hA₂ hq₃
  have hA₆ : 0 ∉ A := by
    intro ht
    have : M ≤ 0 := by simpa using hA₁ 0 ht
    linarith
  have hkN : k ≤ N / 192 := by
    have hkN' : 192 * k ≤ N := by
      exact_mod_cast (show (192 : ℝ) * k ≤ N by nlinarith)
    omega
  have h0K : 0 < K := by
    linarith
  have hA₄' : (2 : ℝ) - k / M ≤ k * rec_sum A := by
    have hmul := mul_le_mul_of_nonneg_left hA₄ hk₀.le
    simpa [div_eq_mul_inv, mul_sub, hk₀ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hA₃' : (k : ℝ) * rec_sum A < 2 := by
    have hkQ : (0 : ℚ) < k := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hA₃Q : (k : ℚ) * rec_sum A < 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (_root_.lt_div_iff₀ hkQ).1 hA₃
    exact_mod_cast hA₃Q
  have hAlcm : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ) := by
    have hClcm_nonneg : 0 ≤ c * M / k := by
      refine div_nonneg ?_ (Nat.cast_nonneg k)
      exact mul_nonneg hc₀.le hM₀.le
    have hClcm_bound : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
      intro q hqpp
      exact hq₂ q hqpp
    have hClcmA := hClcm (c * M / k) hClcm_nonneg A hA₆ hClcm_bound
    refine hClcmA.trans ?_
    have hpowpos : 0 < (2 : ℝ) ^ (A.card - 1 : ℤ) := by
      rw [← Real.rpow_intCast]
      exact Real.rpow_pos_of_pos zero_lt_two _
    have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₅
    rw [← Real.log_le_log_iff (Real.exp_pos _) hpowpos, Real.log_exp]
    rw [show (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ (((A.card - 1 : ℤ) : ℝ)) by
      rw [← Real.rpow_intCast]]
    rw [Real.log_rpow zero_lt_two]
    rw [← div_le_iff₀ (Real.log_pos one_lt_two)]
    push_cast
    have hscaled : C * (c * M / k) / log 2 / M + 1 / M ≤ A.card / M := by
      refine le_trans ?_ (rec_sum_le_card_div hM₀ hA₁)
      refine le_trans ?_ hA₄
      linarith
    have hscaled' : C * (c * M / k) / log 2 + 1 ≤ A.card := by
      have hscaled2 : (C * (c * M / k) / log 2 + 1) / M ≤ A.card / M := by
        simpa [add_div] using hscaled
      have hmul := mul_le_mul_of_nonneg_right hscaled2 hM₀.le
      simpa [div_eq_mul_inv, hM₀.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  have hm2' :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm2 (K := K) (L := L) (T := T) (k := k) (A := A) hA₆
      ((by norm_num : (1 : ℝ) ≤ 8).trans hK) hL hk hkN (hKM.le.trans hMN) hA₂ hq₁ hI
  by_contra hS
  have hS' : ∀ S ⊆ A, rec_sum S ≠ 1 / k := by
    intro S hSA hrec
    exact hS ⟨S, hSA, hrec⟩
  have hminorl := minor_lbound hA₁ h0K hKM hkA hk hA₄' hA₃' hA₅ hS' hAlcm
  have hminors : minor_arc₂ A k K T ∪ minor_arc₁ A k K T = j A \ major_arc A k K := by
    rw [minor_arc₂]
    exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hminorl' :
      1 / 2 ≤
        (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) := by
    have htmp := hminorl
    rw [← hminors] at htmp
    rw [minor_arc₂] at htmp
    have hdisj : Disjoint ((j A \ major_arc A k K) \ minor_arc₁ A k K T) (minor_arc₁ A k K T) :=
      (Finset.disjoint_sdiff : Disjoint (minor_arc₁ A k K T)
        ((j A \ major_arc A k K) \ minor_arc₁ A k K T)).symm
    rw [Finset.sum_union hdisj] at htmp
    simpa [add_comm, add_left_comm, add_assoc] using htmp
  have hupper :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) < 1 / 2 := by
    calc
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k))
          ≤ 8⁻¹ + 8⁻¹ := add_le_add hm2' hm1'
      _ < 1 / 2 := by norm_num
  exact (not_lt_of_ge hminorl') hupper


/-! ## From src4/MainResults.lean -/

open scoped ArithmeticFunction.omega BigOperators
open Filter Finset Real

noncomputable section

/-!
This file ports the front compatibility surface of `src/main_results.lean`.

There is not much in Mathlib 4 corresponding directly to the project-specific statements in this
file. The main reusable Mathlib-backed ingredients come indirectly from the earlier local ports:

* `Definitions` for `rec_sum_local`, `interval_rare_ppowers`, `good_condition`, ...
* `AuxiliaryLemmas` for finset summation bounds and interval lemmas
* `ForMathlib.BasicEstimates` for the Chebyshev and prime-power infrastructure already upstream

The full declaration surface from the Lean 3 file is mirrored here. A couple of lemmas below have
already been ported with proofs; for the remaining declarations, the Lean 4 statements are present
so downstream files can target the right API shape while the proof transport continues.
-/

lemma good_d (N : ℕ) (M δ : ℝ) (A : Finset ℕ) (_hA₁ : A ⊆ Finset.range (N + 1)) (hM : 0 < M)
    (hAM : ∀ n ∈ A, M ≤ (n : ℝ))
    (hAq : ∀ q ∈ ppowers_in_set A, (2 : ℝ) * δ ≤ rec_sum_local A q)
    (I : Finset ℤ) (q : ℕ) (hq : q ∈ interval_rare_ppowers I A (M * δ)) :
    δ ≤ rec_sum_local (A.filter fun n => ∃ x ∈ I, ((n : ℤ) ∣ x)) q := by
  classical
  rw [interval_rare_ppowers, Finset.mem_filter] at hq
  let nA : Finset ℕ := A.filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)
  have hnA : nA = A.filter fun n : ℕ => ¬ ∃ x ∈ I, ((n : ℤ) ∣ x) := by
    apply Finset.filter_congr
    intro n hn
    simp
  have hqpp : IsPrimePow q := (mem_ppowers_in_set.mp hq.1).1
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hqpp.ne_zero
  have hqrare :
      (((local_part A q).filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) <
        (M * δ) / q := by
    simpa [Finset.fmap_def, Finset.filter_image,
      Finset.card_image_of_injective _ Nat.cast_injective] using hq.2
  have h1 : (rec_sum_local nA q : ℝ) ≤ δ := by
    rw [rec_sum_local, local_part, Finset.filter_comm, ← local_part, Rat.cast_sum]
    simp_rw [Rat.cast_div, Rat.cast_natCast]
    refine
      (sum_le_card_mul_real
        (A := (local_part A q).filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x))
        (M := (q : ℝ) / M)
        (f := fun i => (q : ℝ) / i) ?_).trans ?_
    · intro i hi
      simp only [Finset.mem_filter, mem_local_part, and_assoc] at hi
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg q) hM (hAM _ hi.1)
    · refine (mul_le_mul_of_nonneg_right hqrare.le ?_).trans ?_
      · exact div_nonneg (Nat.cast_nonneg q) hM.le
      · have hEq : ((M * δ) / q) * ((q : ℝ) / M) = δ := by
          field_simp [hq0, hM.ne']
        exact hEq.le
  have h2 :
      rec_sum_local A q =
        rec_sum_local (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q + rec_sum_local nA q := by
    rw [hnA, ← rec_sum_local_disjoint (Finset.disjoint_filter_filter_not _ _ _),
      Finset.filter_union_filter_not_eq]
  have h2' :
      (rec_sum_local A q : ℝ) =
        rec_sum_local (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q + rec_sum_local nA q := by
    exact_mod_cast h2
  have h4 :
      2 * δ ≤
        (rec_sum_local
          (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q : ℝ) + rec_sum_local nA q := by
    rw [← h2']
    exact hAq _ hq.1
  linarith

lemma explicit_mertens2 :
    ∀ᶠ N : ℕ in atTop,
      (((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤
        (501 / 500 : ℝ) * log (log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (c : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (500 * (b + 1)))
    , tendsto_natCast_atTop_atTop.eventually hc.bound ] with N hN₁ hN₂ hN₃
  dsimp at hN₁ hN₂
  have hN₄ : 0 < log N := hc₀.trans_le hN₁
  simp_rw [norm_inv, ← div_eq_mul_inv, ← one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    Nat.floor_natCast]
    at hN₃
  have hdiv : c / log N ≤ 1 := by
    rw [div_le_iff₀ hN₄]
    linarith
  have hmain := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans hdiv))
  convert
    hmain.trans
      (show log (log N) + b + 1 ≤ (501 / 500 : ℝ) * log (log N) by
        linarith) using 2
  rw [range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  ext n
  simpa only
    [Finset.mem_filter, and_congr_left_iff, Finset.mem_Icc, zero_le', iff_and_self, true_and]
    using fun h _ => (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h.ne_zero, h.ne_one⟩).le

lemma rec_sum_split (A B C E : Finset ℕ) (h : 0 ∉ B)
    (hC :
      C =
        A.filter fun n : ℕ => n ∈ B ∧ ∀ q ∈ ppowers_in_set A, n ∈ local_part B q → q ∈ E) :
    rec_sum ((A \ C) ∩ B) ≤ (((ppowers_in_set A) \ E).sum fun q => (rec_sum_local B q) / q) := by
  classical
  simp_rw [rec_sum, rec_sum_local, Finset.sum_div]
  calc
    (((A \ C) ∩ B).sum fun n => (1 : ℚ) / n) ≤
        ((((ppowers_in_set A) \ E).biUnion fun x => local_part B x).sum fun n => (1 : ℚ) / n) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n hn
        rw [hC] at hn
        rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, not_and, not_and] at hn
        have hn' := hn.1.2 hn.1.1 hn.2
        rw [not_forall] at hn'
        rcases hn' with ⟨q, hq⟩
        rw [Classical.not_imp, Classical.not_imp] at hq
        rw [Finset.mem_biUnion]
        refine ⟨q, ?_, hq.2.1⟩
        rw [Finset.mem_sdiff]
        exact ⟨hq.1, hq.2.2⟩
      · intro i hi₁ hi₂
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    _ ≤ (((ppowers_in_set A) \ E).sum fun x => (local_part B x).sum fun x₁ => (1 : ℚ) / x₁) := by
      exact sum_bUnion_le_sum_of_nonneg fun i hi => by
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    _ ≤ (((ppowers_in_set A) \ E).sum fun q => (local_part B q).sum fun i => (q : ℚ) / i / q) := by
      have hlast :
          (((ppowers_in_set A) \ E).sum fun x => (local_part B x).sum fun x₁ => (1 : ℚ) / x₁) =
            (((ppowers_in_set A) \ E).sum fun q =>
              (local_part B q).sum fun i => (q : ℚ) / i / q) := by
        rw [sum_congr rfl]
        intro x hx
        rw [sum_congr rfl]
        intro x₁ hx₁
        rw [local_part, Finset.mem_filter] at hx₁
        have hx0 : (x : ℚ) ≠ 0 := by
          exact_mod_cast (mem_ppowers_in_set.mp (Finset.mem_sdiff.mp hx).1).1.ne_zero
        have hx₁0 : (x₁ : ℚ) ≠ 0 := by
          intro hz
          apply h
          exact (by exact_mod_cast hz : x₁ = 0) ▸ hx₁.1
        field_simp [hx0, hx₁0]
      exact hlast.le

private lemma force_good_properties_hIcard0
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (h0M : 0 < M) :
    (I.card : ℤ) =
      ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
  rw [hI, Int.card_Icc]
  have hnonneg :
      0 ≤
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
    refine sub_nonneg.mpr ?_
    rw [Int.ceil_le]
    have hwidth_nonneg : 0 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
      exact mul_nonneg h0M.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have hlt :
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 <
          ↑(⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 : ℤ) := by
      calc
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 ≤
            t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 := by
          linarith
        _ < (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℝ) + 1 := by
          exact Int.lt_floor_add_one _
        _ = ↑(⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 : ℤ) := by
          norm_num
    exact le_of_lt hlt
  exact_mod_cast Int.toNat_of_nonneg hnonneg

private lemma force_good_properties_hIcardn0
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (hlarge1 : 1 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) :
    I.card ≠ 0 := by
  have hIne : I.Nonempty := by
    rw [hI, Finset.nonempty_Icc]
    rw [Int.ceil_le]
    have hfloor :
        t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 - 1 <
          (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℤ) := by
      exact Int.sub_one_lt_floor _
    have hgap :
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 ≤
          t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 - 1 := by
      nlinarith
    exact le_trans hgap (le_of_lt hfloor)
  exact Finset.card_ne_zero.mpr hIne

private lemma force_good_properties_hIcard'
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hIcard0 :
      (I.card : ℤ) =
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉) :
    (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
  rw [show (I.card : ℝ) = ((I.card : ℤ) : ℝ) by norm_num, hIcard0]
  push_cast
  calc
    (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℝ) + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
      rw [sub_le_sub_iff_right, add_le_add_iff_right]
      exact Int.floor_le _
    _ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 + 1 -
        (t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2) := by
      rw [sub_le_sub_iff_left]
      exact Int.le_ceil _
    _ = M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
      ring

private lemma force_good_properties_hIcard''
    (N : ℕ) (M : ℝ) (I : Finset ℤ)
    (hIcard' : (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1)
    (hlarge1 : 1 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) :
    (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
  nlinarith

private lemma force_good_properties_hlarge9
    (N : ℕ) (M : ℝ) (I : Finset ℤ)
    (hlarge : 1 < N)
    (h0M : 0 < M)
    (hlargeNs :
      (2 : ℝ) * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) <
        log N ^ (-((1 : ℝ) / 101)) / 6)
    (hIcard'' : (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)))
    (hIcardn0 : I.card ≠ 0) :
    (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
      M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_trans zero_lt_one hlarge)
  have hcardpos : 0 < (I.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hIcardn0
  have hpowpos : 0 < (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) := by
    exact Real.rpow_pos_of_pos hNpos _
  refine (_root_.lt_div_iff₀ hcardpos).2 ?_
  calc
    (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) * (I.card : ℝ) ≤
        (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
          (2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
      exact mul_le_mul_of_nonneg_left hIcard'' (le_of_lt hpowpos)
    _ = M * (2 * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3))) := by
      calc
        (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
            (2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) =
            2 * M *
              ((N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
                (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
              ring
        _ = 2 * M * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) := by
          rw [show (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
              (N : ℝ) ^ (-(2 : ℝ) / log (log N)) =
              (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) by
                rw [mul_comm, ← Real.rpow_add hNpos]
              ]
        _ = M * (2 * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3))) := by
          ring
    _ < M * (log N ^ (-(1 / 101 : ℝ)) / 6) := by
      exact mul_lt_mul_of_pos_left hlargeNs h0M

private lemma force_good_properties_hIclose'
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (hlarge2 : M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤ N) :
    ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N := by
  intro x hx y hy
  refine le_trans (two_in_Icc' I hI hx hy) ?_
  calc
    (((⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℤ) : ℝ) -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉) ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
      rw [sub_le_sub_iff_right]
      exact Int.floor_le _
    _ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 -
        (t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2) := by
      rw [sub_le_sub_iff_left]
      exact Int.le_ceil _
    _ = M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
      ring
    _ ≤ N := hlarge2

private lemma force_good_properties_hIclose
    (N : ℕ) (I : Finset ℤ)
    (hIclose' : ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N) :
    ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N := by
  intro x hx y hy
  have hxy := hIclose' x hx y hy
  rw [nat_cast_diff_issue] at hxy
  exact_mod_cast hxy

private lemma force_good_properties_two_values_case
    (N : ℕ) (M c : ℝ) (A A_I E : Finset ℕ) (I : Finset ℤ) (x1 x2 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (h0A : 0 ∉ A)
    (h0M : 0 < M)
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ))
    (hrecA : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A)
    (hlarge0 : 0 < log N)
    (hlarge5 :
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6)
    (hlarge3 : 0 < log (log N))
    (hnum : (502 / 500 : ℝ) - c ≤ 2 / 3)
    (hzI : ¬ (0 : ℤ) ∈ I)
    (hP :
      ↑(((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
          fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card) <
        M / log N)
    (hnoB :
      ¬ ∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))
    (hdiv :
      ∀ n : ℕ,
        n ≤ N ^ 2 →
          (ArithmeticFunction.sigma 0 n : ℝ) ≤
            N ^ (2 * log 2 / log (log (N : ℝ)) * (1 + 1 / 3)))
    (hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N)
    (hA_I : A_I = A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x)
    (hE :
      E =
        (ppowers_in_set A).filter
          (fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q))
    (hf :
      ∀ q ∈ E,
        f q ∈ I ∧
          ((q : ℤ) ∣ f q) ∧
            c * log (log N) ≤
              ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f q).sum
                (fun r : ℕ => (1 / r : ℝ)))
    (hx1E : x1 ∈ E)
    (hx2E : x2 ∈ E)
    (hclose12 : |(f x2 : ℝ) - f x1| ≤ N)
    (htwoxs : f x2 ≠ f x1)
    (hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2) :
    (x2 : ℤ) ∣ f x1 := by
  classical
  exfalso
  let A1 := A.filter fun n : ℕ => (n : ℤ) ∣ f x1
  let A2 := A.filter fun n : ℕ => (n : ℤ) ∣ f x2
  let A0 := A \ (A1 ∪ A2)
  have hf1 := hf x1 hx1E
  have hf2 := hf x2 hx2E
  have h3rec : rec_sum A ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
    refine le_trans ?_ rec_sum_le_three
    refine rec_sum_mono ?_
    intro n hn
    rw [Finset.mem_union]
    by_cases htemp : n ∈ A1 ∪ A2
    · exact Or.inl htemp
    · exact Or.inr <| Finset.mem_sdiff.mpr ⟨hn, htemp⟩
  by_cases hAlarge : rec_sum A ≤ 3 * rec_sum A1 ∨ rec_sum A ≤ 3 * rec_sum A2
  · apply hnoB
    let P1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
    let P2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
    let P12 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1 ∧ (n : ℤ) ∣ f x2
    have hrecAs :
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) ≤
          (502 / 500 : ℝ) * log (log N) := by
      have hunion :
          P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
        dsimp [P1, P2, P12]
        have h :=
          (Finset.sum_union_inter
            (s₁ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1)
            (s₂ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2)
            (f := fun q : ℕ => (1 : ℝ) / q)).symm
        simpa [Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
          and_left_comm, and_right_comm, and_assoc, add_comm, add_left_comm, add_assoc] using h
      have hunion_subset : P1 ∪ P2 ⊆ ppowers_in_set A := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq | hq <;> exact (Finset.mem_of_mem_filter _ hq)
      calc
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := hunion
        _ ≤ (ppower_rec_sum A : ℝ) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
              rw [add_le_add_iff_right, ppower_rec_sum]
              push_cast
              exact Finset.sum_le_sum_of_subset_of_nonneg hunion_subset fun i _ _ => by
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (ppower_rec_sum A : ℝ) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_left]
              refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) htwoxs hclose12))
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro r hr
                rw [Finset.mem_filter] at hr
                rw [Finset.mem_filter]
                rw [ppowers_in_set, Finset.mem_biUnion] at hr
                rcases hr.1 with ⟨m, hmA, hmq⟩
                rw [Finset.mem_filter, Nat.mem_divisors] at hmq
                refine ⟨?_, hmq.2.1, hr.2.2, hr.2.1⟩
                rw [Finset.mem_range]
                exact lt_of_le_of_lt
                  (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
                  (by rw [← Finset.mem_range]; exact hA hmA)
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (501 / 500 : ℝ) * log (log N) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_right]
              exact hsum4
        _ = (502 / 500 : ℝ) * log (log N) := by
              ring_nf
    rcases hAlarge with hA1large | hA2large
    · refine ⟨A1, Finset.filter_subset _ _, hA1large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A1).sum fun q : ℕ => (1 : ℝ) / q) ≤ P1.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A1) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A1]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf2.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
    · refine ⟨A2, Finset.filter_subset _ _, hA2large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A2).sum fun q : ℕ => (1 : ℝ) / q) ≤ P2.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A2) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A2]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le, add_comm]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf1.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
  · let A' := A0.filter fun n : ℕ => n ∈ A_I ∧ ∀ q ∈ ppowers_in_set A0, n ∈ local_part A_I q → q ∈ E
    have hP' : ((A \ A_I).card : ℝ) < M / log N := by
      let F : Finset ℤ := (A.image fun n : ℕ => (n : ℤ)).filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x
      have hsubset : (A \ A_I).image (fun n : ℕ => (n : ℤ)) ⊆ F := by
        intro z hz
        rw [Finset.mem_image] at hz
        rcases hz with ⟨n, hn, rfl⟩
        rw [Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨n, (Finset.mem_sdiff.mp hn).1, rfl⟩, ?_⟩
        intro x hx hnx
        apply (Finset.mem_sdiff.mp hn).2
        rw [hA_I, Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.mp hn).1, ⟨x, hx, hnx⟩⟩
      have hcardle : (((A \ A_I).image (fun n : ℕ => (n : ℤ))).card : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hcardeq : ((A \ A_I).image (fun n : ℕ => (n : ℤ))).card = (A \ A_I).card := by
        exact Finset.card_image_of_injective _ Nat.cast_injective
      have hF :
          F =
            ((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
              fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x) := by
        ext z
        simp [F, Finset.mem_image]
      have hPstd : (F.card : ℝ) < M / log N := by
        rw [hF]
        exact hP
      exact lt_of_le_of_lt (by simpa [hcardeq] using hcardle) hPstd
    have hrecaux' : 1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤
            1 / log N + (((ppowers_in_set A0) \ E).sum fun q => (rec_sum_local A_I q) / q) := by
              rw [add_le_add_iff_left]
              norm_cast
              refine rec_sum_split A0 A_I A' E ?_ ?_
              · intro hzA
                apply h0A
                rw [hA_I] at hzA
                exact Finset.mem_of_mem_filter 0 hzA
              · rfl
        _ ≤
            1 / log N +
              (1 / (2 * log N ^ ((1 : ℝ) / 100))) *
                (((ppowers_in_set A0) \ E).sum fun q => (1 : ℝ) / q) := by
              norm_cast
              rw [add_le_add_iff_left, Rat.cast_sum, Finset.mul_sum]
              simp_rw [Rat.cast_div, Rat.cast_natCast]
              refine Finset.sum_le_sum ?_
              intro q hq
              have hle : (rec_sum_local A_I q : ℝ) ≤ 1 / (2 * log N ^ ((1 : ℝ) / 100)) := by
                rw [← not_lt]
                intro nlt
                rw [Finset.mem_sdiff] at hq
                apply hq.2
                rw [hE, Finset.mem_filter]
                refine ⟨(ppowers_in_set_subset Finset.sdiff_subset) hq.1, le_of_lt nlt⟩
              exact
                (by
                  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                    (mul_le_mul_of_nonneg_right hle
                      (inv_nonneg.mpr (Nat.cast_nonneg q))))
        _ ≤ 1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) := by
              rw [add_le_add_iff_left]
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · refine le_trans ?_ hsum4
                rw [ppower_rec_sum]
                push_cast
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
                · exact Finset.sdiff_subset.trans (ppowers_in_set_subset Finset.sdiff_subset)
                · intro i _ _
                  rw [one_div_nonneg]
                  exact Nat.cast_nonneg i
              · positivity
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hlarge5
    have hrecA0 : (log N) ^ (-(1 / 101 : ℝ)) / 3 ≤ rec_sum A0 := by
      have hAlarge1 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A1) := by
        intro h
        apply hAlarge
        exact Or.inl (by exact_mod_cast h)
      have hAlarge2 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A2) := by
        intro h
        apply hAlarge
        exact Or.inr (by exact_mod_cast h)
      have hA1small : (rec_sum A1 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA1small
        apply hAlarge1
        nlinarith
      have hA2small : (rec_sum A2 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA2small
        apply hAlarge2
        nlinarith
      have hA0big : (rec_sum A : ℝ) / 3 ≤ rec_sum A0 := by
        have h3rec' : (rec_sum A : ℝ) ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
          exact_mod_cast h3rec
        by_contra hA0big
        have hA0small : (rec_sum A0 : ℝ) < rec_sum A / 3 := lt_of_not_ge hA0big
        nlinarith [h3rec', hA1small, hA2small, hA0small]
      nlinarith [hrecA, hA0big]
    have hrecaux : (rec_sum (A0 \ A') : ℝ) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        (rec_sum (A0 \ A') : ℝ) = rec_sum ((A0 \ A') \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          norm_cast
          rw [← rec_sum_disjoint, Finset.sdiff_union_inter]
          exact Finset.disjoint_sdiff_inter _ _
        _ ≤ rec_sum (A \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          norm_cast
          refine rec_sum_mono ?_
          intro n hn
          rw [Finset.mem_sdiff] at hn ⊢
          have hnA0 : n ∈ A0 := (Finset.mem_sdiff.mp hn.1).1
          have hnA : n ∈ A := by
            dsimp [A0] at hnA0
            exact (Finset.mem_sdiff.mp hnA0).1
          exact ⟨hnA, hn.2⟩
        _ ≤ ((A \ A_I).card : ℝ) / M + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          exact rec_sum_le_card_div h0M fun n hn => hMA n (Finset.mem_sdiff.mp hn).1
        _ ≤ 1 / log N + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          have htmp : ((A \ A_I).card : ℝ) / M < 1 / log N := by
            rw [_root_.div_lt_iff₀ h0M]
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hP'
          exact le_of_lt htmp
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hrecaux'
    have hrecA' : (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤ rec_sum A' := by
      calc
        (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤
            (log N) ^ (-(1 / 101 : ℝ)) / 3 - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          nlinarith
        _ ≤ (rec_sum A0 : ℝ) - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          rw [sub_le_sub_iff_right]
          exact hrecA0
        _ ≤ (rec_sum A0 : ℝ) - rec_sum (A0 \ A') := by
          rw [sub_le_sub_iff_left]
          exact hrecaux
        _ = rec_sum A' := by
          rw [sub_eq_iff_eq_add]
          norm_cast
          rw [← rec_sum_disjoint, Finset.union_sdiff_of_subset]
          · exact Finset.filter_subset _ _
          · exact Finset.disjoint_sdiff
    have hA'size : M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) ≤ A'.card := by
      have htmp : (rec_sum A' : ℝ) ≤ A'.card / M := by
        refine rec_sum_le_card_div h0M ?_
        intro n hn
        have hnA0 : n ∈ A0 := (Finset.mem_filter.mp hn).1
        have hnA : n ∈ A := by
          dsimp [A0] at hnA0
          exact (Finset.mem_sdiff.mp hnA0).1
        exact hMA n hnA
      have htmp' : ((log N) ^ (-(1 / 101 : ℝ)) / 6) * M ≤ (A'.card : ℝ) := by
        exact (_root_.le_div_iff₀ h0M).mp (hrecA'.trans htmp)
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp'
    have hIne : I.Nonempty := ⟨f x1, hf1.1⟩
    have hbadx :
        ∃ x ∈ I,
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
            (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card := by
      by_contra h
      rw [← not_lt] at hA'size
      apply hA'size
      have hA'union : A' = I.biUnion fun x : ℤ => A'.filter fun n : ℕ => (n : ℤ) ∣ x := by
        ext a
        constructor
        · intro hn
          have hn' := hn
          rw [Finset.mem_filter, hA_I, Finset.mem_filter] at hn
          rcases hn.2.1.2 with ⟨x, hx1, hx2⟩
          rw [Finset.mem_biUnion]
          exact ⟨x, hx1, by rw [Finset.mem_filter]; exact ⟨hn', hx2⟩⟩
        · intro hn
          rw [Finset.mem_biUnion] at hn
          rcases hn with ⟨x, hx1, hx2⟩
          exact Finset.mem_of_mem_filter a hx2
      rw [hA'union]
      refine
        lt_of_lt_of_le
          (card_bUnion_lt_card_mul_real
            (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ)) ?_ hIne)
          ?_
      · intro x hx
        rw [← not_le]
        intro hnle
        apply h
        exact ⟨x, hx, hnle⟩
      · rw [show ((I.card : ℝ) * (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))) =
            M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) by
            field_simp [show (I.card : ℝ) ≠ 0 by
              exact_mod_cast (Finset.card_ne_zero.mpr hIne)]]
    rcases hbadx with ⟨x, hx1, hx2⟩
    let m := Nat.gcd (Int.natAbs x) (Int.natAbs (f x1 * f x2))
    have hmsmall : m ≤ N ^ 2 := by
      have hbadx' : ∃ n ∈ A', (n : ℤ) ∣ x := by
        have hA'temp : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).Nonempty := by
          rw [← Finset.card_pos, Nat.pos_iff_ne_zero]
          intro hz
          rw [hz] at hx2
          have hpos : 0 < M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
            refine div_pos ?_ ?_
            · refine mul_pos h0M ?_
              refine div_pos ?_ ?_
              · exact Real.rpow_pos_of_pos hlarge0 _
              · norm_num1
            · exact_mod_cast (Finset.card_pos.mpr hIne)
          linarith
        rcases hA'temp with ⟨n, hn⟩
        rw [Finset.mem_filter] at hn
        exact ⟨n, hn.1, hn.2⟩
      rcases hbadx' with ⟨ns, hns1, hns2⟩
      rw [Finset.mem_filter] at hns1
      have hns3 := hns1.1
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hns3
      rw [not_or] at hns3
      refine le_trans (nat_gcd_prod_le_diff ?_ ?_) ?_
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.1 ⟨hns3.1, hns2⟩
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.2 ⟨hns3.1, hns2⟩
      · rw [sq]
        refine Nat.mul_le_mul ?_ ?_
        · exact hIclose x hx1 (f x1) hf1.1
        · exact hIclose x hx1 (f x2) hf2.1
    have hdivm : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card ≤ ArithmeticFunction.sigma 0 m := by
      rw [divisor_function_eq_card_divisors]
      refine Finset.card_le_card ?_
      intro n hn
      rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [dvd_iff_ppowers_dvd' n m]
        · intro q hq1 hq2
          rw [Nat.dvd_gcd_iff]
          rcases Finset.mem_filter.mp hn with ⟨hnA', hnx⟩
          rcases Finset.mem_filter.mp hnA' with ⟨hnA0, hnAI, hprop⟩
          refine ⟨?_, ?_⟩
          · have hqx : (q : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.mpr hq1) hnx
            exact Int.natCast_dvd.mp <| by
              simpa using Int.dvd_natAbs.mpr hqx
          · have hqE : q ∈ E := by
              have hnA : n ∈ A := by
                dsimp [A0] at hnA0
                exact (Finset.mem_sdiff.mp hnA0).1
              have hn0 : n ≠ 0 := by
                intro hnz
                apply h0A
                simpa [hnz] using hnA
              exact hprop q (by
                rw [ppowers_in_set, Finset.mem_biUnion]
                refine ⟨n, hnA0, ?_⟩
                rw [Finset.mem_filter, Nat.mem_divisors]
                exact ⟨⟨hq1, hn0⟩, hq2.1, hq2.2⟩) (by
                rw [local_part, Finset.mem_filter]
                exact ⟨hnAI, hq1, hq2.2⟩)
            have hfq := hf q hqE
            rcases hthreexs q hqE with hqfx1 | hqfx2
            · have hqx1 : (q : ℤ) ∣ f x1 := by simpa [hqfx1] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x1) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx1
              simpa [Int.natAbs_mul] using dvd_mul_of_dvd_left hqabs (Int.natAbs (f x2))
            · have hqx2 : (q : ℤ) ∣ f x2 := by simpa [hqfx2] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x2) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx2
              simpa [Int.natAbs_mul, Nat.mul_comm] using
                dvd_mul_of_dvd_right hqabs (Int.natAbs (f x1))
        · intro hnz
          apply h0A
          have hbah : A'.filter fun n : ℕ => (n : ℤ) ∣ x ⊆ A := by
            intro k hk
            have hkA' : k ∈ A' := (Finset.mem_filter.mp hk).1
            have hkA0 : k ∈ A0 := (Finset.mem_filter.mp hkA').1
            dsimp [A0] at hkA0
            exact (Finset.mem_sdiff.mp hkA0).1
          rw [hnz] at hn
          exact hbah hn
      · intro hmz
        rw [Nat.gcd_eq_zero_iff] at hmz
        have hmz' : x = 0 := by simpa using hmz.1
        rw [hmz'] at hx1
        exact hzI hx1
    specialize hdiv m hmsmall
    have hsigma_lt :
        (ArithmeticFunction.sigma 0 m : ℝ) <
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) :=
      lt_of_le_of_lt hdiv hlarge9
    have hsigma_ge :
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
          ArithmeticFunction.sigma 0 m := by
      exact le_trans hx2 (by exact_mod_cast hdivm)
    exact (not_lt_of_ge hsigma_ge) hsigma_lt

private lemma force_good_properties_three_values_case
    (N : ℕ) (c : ℝ) (A : Finset ℕ) (x1 x2 x3 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (hlarge3 : 0 < log (log N))
    (hnum : (102 / 100 : ℝ) ≤ 3 * c - ((1 : ℝ) / 500 + (1 : ℝ) / 500 + (1 : ℝ) / 500))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hS1 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS2 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS3 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (h21 : f x2 ≠ f x1)
    (h32 : f x3 ≠ f x2)
    (h31 : f x3 ≠ f x1)
    (hclose21 : |(f x2 : ℝ) - f x1| ≤ N)
    (hclose32 : |(f x3 : ℝ) - f x2| ≤ N)
    (hclose31 : |(f x3 : ℝ) - f x1| ≤ N) :
    False := by
  let F1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
  let F2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
  let F3 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3
  let S1 := F1.sum fun r : ℕ => (1 : ℝ) / r
  let S2 := F2.sum fun r : ℕ => (1 : ℝ) / r
  let S3 := F3.sum fun r : ℕ => (1 : ℝ) / r
  let S12 := (F1 ∩ F2).sum fun r : ℕ => (1 : ℝ) / r
  let S23 := (F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S13 := (F1 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S123 := (F1 ∩ F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  have hsum1 : 3 * c * log (log N) ≤ S1 + S2 + S3 := by
    have hS1' : c * log (log N) ≤ S1 := by simpa [S1, F1] using hS1
    have hS2' : c * log (log N) ≤ S2 := by simpa [S2, F2] using hS2
    have hS3' : c * log (log N) ≤ S3 := by simpa [S3, F3] using hS3
    nlinarith
  have hunion :
      S1 + S2 + S3 =
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123 := by
    dsimp [S1, S2, S3, S12, S13, S23, S123]
    simpa [F1, F2, F3, Finset.union_assoc, Finset.inter_assoc, Finset.inter_left_comm,
      Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
      and_assoc, and_left_comm, and_right_comm, add_comm, add_left_comm, add_assoc] using
      (sum_add_sum_add_sum (A := F1) (B := F2) (C := F3) (f := fun r : ℕ => (1 : ℝ) / r))
  have hsum2 : (S1 + S2 + S3) - (S12 + S13 + S23) ≤ ppower_rec_sum A := by
    have h123nonneg : 0 ≤ S123 := by
      dsimp [S123]
      refine Finset.sum_nonneg ?_
      intro i hi
      rw [one_div_nonneg]
      exact Nat.cast_nonneg i
    have hunion_le :
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) ≤ ppower_rec_sum A := by
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro q hq
        rw [Finset.mem_union, Finset.mem_union] at hq
        rcases hq with hq | hq
        · rcases hq with hq | hq
          · exact Finset.mem_of_mem_filter q hq
          · exact Finset.mem_of_mem_filter q hq
        · exact Finset.mem_of_mem_filter q hq
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    calc
      (S1 + S2 + S3) - (S12 + S13 + S23) =
          ((F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123) -
            (S12 + S13 + S23) := by rw [hunion]
      _ ≤ (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) := by
          nlinarith
      _ ≤ ppower_rec_sum A := hunion_le
  have hsum3 :
      S12 + S23 + S13 ≤
        (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N) := by
    have h12 :
        S12 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S12, F1, F2]
      refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) h21 hclose21))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
          rw [Finset.mem_range]
          exact lt_of_le_of_lt
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
            (by rw [← Finset.mem_range]; exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h23 :
        S23 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S23, F2, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x2) h32 hclose32))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
          rw [Finset.mem_range]
          exact lt_of_le_of_lt
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
            (by rw [← Finset.mem_range]; exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h13 :
        S13 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S13, F1, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x1) h31 hclose31))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
          rw [Finset.mem_range]
          exact lt_of_le_of_lt
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
            (by rw [← Finset.mem_range]; exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    nlinarith
  have hsum5 : ¬ ((501 / 500 : ℝ) * log (log N) < ((102 : ℝ) / 100) * log (log N)) := by
    rw [not_lt]
    calc
      (((102 : ℝ) / 100) * log (log N)) ≤
          (3 * c - (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500))) *
            log (log N) := by
              exact mul_le_mul_of_nonneg_right hnum (le_of_lt hlarge3)
      _ = 3 * c * log (log N) -
            ((((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N)) := by
              ring
      _ ≤ (S1 + S2 + S3) - (S12 + S13 + S23) := by
              nlinarith [hsum1, hsum3]
      _ ≤ ppower_rec_sum A := hsum2
      _ ≤ (501 / 500 : ℝ) * log (log N) := hsum4
  apply hsum5
  exact mul_lt_mul_of_pos_right (by norm_num) hlarge3

theorem force_good_properties :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      ((∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)) ∨
        good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
          (M / (2 * (log N) ^ (1 / 100 : ℝ)))) := by
  classical
  let c := (35 : ℝ) / 100
  have hthirdpos : (0 : ℝ) < 1 / 3 := by
    norm_num1
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , yet_another_large_N
    , yet_another_large_N'
    , rec_pp_sum_close
    , find_good_x
    , explicit_mertens2
    , div_bound_useful_version hthirdpos ] with
    N hlarge hlarge0 hlarge4 hlargeNs hlarge5 hrecN hgoodx hmertens hdiv
    M A hA h0M hMN hNM h0A hMA hreg hrecA hreclocal
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow : (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  refine or_iff_not_imp_left.2 ?_
  intro hnoB
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  by_cases hzI : (0 : ℤ) ∈ I
  · refine ⟨0, hzI, ?_⟩
    intro q hq
    exact dvd_zero (q : ℤ)
  have hIcard0 :
      (I.card : ℤ) =
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
    exact force_good_properties_hIcard0 N M t I hI h0M
  have hIcardn0 : I.card ≠ 0 := by
    exact force_good_properties_hIcardn0 N M t I hI hlarge1
  have hIcard' : (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
    exact force_good_properties_hIcard' N M t I hIcard0
  have hIcard'' : (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
    exact force_good_properties_hIcard'' N M I hIcard' hlarge1
  have hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
    exact force_good_properties_hlarge9 N M I hlarge h0M hlargeNs hIcard'' hIcardn0
  have hIclose' : ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N := by
    exact force_good_properties_hIclose' N M t I hI hlarge2
  have hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N := by
    exact force_good_properties_hIclose N I hIclose'
  let A_I := A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let E := (ppowers_in_set A).filter
    fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hDE : D ⊆ E := by
      intro q hq
      rw [Finset.mem_filter]
      refine ⟨interval_rare_ppowers_subset I K hq, ?_⟩
      refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
      · intro q hq'
        rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
        · exact hreclocal q hq'
        · exact le_of_lt hlarge0
      · rw [← div_eq_mul_one_div]
        exact hq
    have hlocal :
        ∀ q ∈ E, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
          c * log (log N) ≤
            ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              (fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (Finset.mem_of_mem_filter q hq) hI
      apply hgoodx
      rw [Finset.mem_filter] at hq
      exact hq.2
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    have hfcopy2 := hf
    have hfcopy3 := hf
    specialize hf x1 (hDE hx1)
    refine ⟨hf.1, ?_⟩
    intro x2 hx2
    specialize hfcopy2 x2 (hDE hx2)
    have hclose : ∀ x ∈ E, ∀ y ∈ E, |(f x : ℝ) - f y| ≤ N := by
      intro q hq r hr
      have hfcopy' := hfcopy
      specialize hfcopy q hq
      specialize hfcopy' r hr
      apply @le_trans _ _ _
        (((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
          ⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉) N
      · apply two_in_Icc
        · rw [← hI]
          exact hfcopy.1
        · rw [← hI]
          exact hfcopy'.1
      · have hfloor :
            ((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
              t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 := by
          exact Int.floor_le _
        have hceil :
            t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 ≤
              (⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
          exact Int.le_ceil _
        nlinarith
    have hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N) := by
      refine le_trans ?_ hmertens
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hr with ⟨a, ha, hr⟩
        rw [Finset.mem_filter] at hr
        refine ⟨?_, hr.2.1⟩
        exact lt_of_le_of_lt (Nat.divisor_le hr.1) (by rw [← Finset.mem_range]; exact hA ha)
      · intro i _ _
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    by_cases htwoxs : f x2 = f x1
    · obtain hf' := hfcopy2.2.1
      rw [htwoxs] at hf'
      exact hf'
    · by_cases hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2
      · exact
          force_good_properties_two_values_case
            N M c A A_I E I x1 x2 f hA h0A h0M hMA hrecA hlarge0 hlarge5 hlarge3
            (by norm_num1) hzI (by simpa using hP) hnoB hrecN hsum4 hlarge9 hdiv hIclose rfl rfl
            hfcopy (hDE hx1) (hDE hx2) (hclose x2 (hDE hx2) x1 (hDE hx1)) htwoxs hthreexs
      · rw [not_forall] at hthreexs
        rcases hthreexs with ⟨x3, hx3⟩
        rw [Classical.not_imp, not_or] at hx3
        specialize hfcopy3 x3 hx3.1
        exfalso
        let S1 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1).sum (fun r => (1 : ℝ) / r)
        let S2 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x2).sum (fun r => (1 : ℝ) / r)
        let S3 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x3).sum (fun r => (1 : ℝ) / r)
        exact
          force_good_properties_three_values_case
            N c A x1 x2 x3 f hA hlarge3 (by dsimp [c]; norm_num1) hrecN hsum4 hf.2.2
            hfcopy2.2.2 hfcopy3.2.2 htwoxs hx3.2.2 hx3.2.1
            (hclose x2 (hDE hx2) x1 (hDE hx1)) (hclose x3 hx3.1 x2 (hDE hx2))
            (hclose x3 hx3.1 x1 (hDE hx1))
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

theorem force_good_properties2 :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      (ppower_rec_sum A : ℝ) ≤ (2 / 3) * log (log N) →
      good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
        (M / (2 * (log N) ^ (1 / 100 : ℝ))) := by
  classical
  let c := (35 : ℝ) / 100
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , rec_pp_sum_close
    , find_good_x ] with
    N hlarge hlarge0 hlarge4 hrecN hgoodx M A hA h0M hMN hNM h0A hMA hreg hreclocal hpprecA
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow :
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hlocal :
        ∀ q ∈ D, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
            ((35 : ℝ) / 100) * log (log N) ≤
            (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (interval_rare_ppowers_subset I K hq) hI
      have hgoodq :
          (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
            rec_sum_local (A.filter fun n => ∃ x ∈ I, (n : ℤ) ∣ x) q := by
        refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
        · intro q hq'
          rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
          · exact hreclocal q hq'
          · exact le_of_lt hlarge0
        · rw [← div_eq_mul_one_div]
          exact hq
      exact hgoodx hgoodq
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    specialize hf x1 hx1
    refine ⟨hf.1, ?_⟩
    intro q hq
    specialize hfcopy q hq
    by_cases htwoxs : f q = f x1
    · obtain hf' := hfcopy.2.1
      rw [htwoxs] at hf'
      exact hf'
    · exfalso
      let S1 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1
      let S2 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q
      let S12 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q ∧ (n : ℤ) ∣ f x1
      have hfS1 : c * log (log N) ≤ S1.sum (fun r => (1 / r : ℝ)) := by
        simpa [S1, c] using hf.2.2
      have hfcopyS2 : c * log (log N) ≤ S2.sum (fun r => (1 / r : ℝ)) := by
        simpa [S2, c] using hfcopy.2.2
      have hsum1 :
          2 * c * log (log N) ≤
            S1.sum (fun r => (1 / r : ℝ)) + S2.sum (fun r => (1 / r : ℝ)) := by
        rw [two_mul, add_mul]
        exact add_le_add hfS1 hfcopyS2
      have hsum2 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
              S12.sum (fun r => (1 : ℝ) / r) ≤
            ppower_rec_sum A := by
        have hS12 : S1 ∩ S2 = S12 := by
          ext r
          simp [S1, S2, S12, and_left_comm, and_assoc, and_comm]
        have hEq :
            S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
                S12.sum (fun r => (1 : ℝ) / r) =
              (S1 ∪ S2).sum (fun r => (1 : ℝ) / r) := by
          rw [← hS12]
          linarith [Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := fun r => (1 : ℝ) / r)]
        rw [ppower_rec_sum]
        push_cast
        rw [hEq]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rw [Finset.mem_union] at hr
          cases hr with
          | inl hr1 =>
              exact (Finset.mem_filter.mp hr1).1
          | inr hr2 =>
              exact (Finset.mem_filter.mp hr2).1
        · intro i _ _
          rw [one_div_nonneg]
          exact Nat.cast_nonneg i
      have hsum3 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) - ppower_rec_sum A ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        linarith
      have hsum4 :
          ((1 : ℝ) / 500) * log (log N) ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        have hsilly : c = 35 / 100 := by
          rfl
        nlinarith
      have hqx1close : |(f q : ℝ) - f x1| ≤ N := by
        apply @le_trans _ _ _
          (((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
            ⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉) N
        · apply two_in_Icc
          · rw [← hI]
            exact hfcopy.1
          · rw [← hI]
            exact hf.1
        · have hfloor :
              ((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
                t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 := by
            exact Int.floor_le _
          have hceil :
              t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
                (⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
            exact Int.le_ceil _
          nlinarith
      specialize hrecN (f q) (f x1) htwoxs hqx1close
      rw [lt_iff_not_ge] at hrecN
      apply hrecN
      refine le_trans hsum4 ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        simp only [S12, Finset.mem_filter] at hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1 with ⟨m, hm1, hm2⟩
        rw [Finset.mem_filter] at hm2
        rw [Finset.mem_filter]
        refine ⟨?_, hm2.2.1, hr.2⟩
        rw [Finset.mem_range]
        exact lt_of_le_of_lt (Nat.divisor_le hm2.1) (by rw [← Finset.mem_range]; exact hA hm1)
      · intro i _ _
        exact div_nonneg zero_le_one (Nat.cast_nonneg i)
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

lemma pruning_lemma_one_prec (A : Finset ℕ) (ε : ℝ) (i : ℕ) :
    ∃ A_i ⊆ A, ∃ Q_i ⊆ ppowers_in_set A,
      Disjoint Q_i (ppowers_in_set A_i) ∧
      ((rec_sum A : ℝ) - ε * rec_sum Q_i ≤ rec_sum A_i) ∧
      (i ≤ (A \ A_i).card ∨ ∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) := by
  induction i with
  | zero =>
      exact ⟨A, Finset.Subset.rfl, ∅, by simp⟩
  | succ i ih =>
      obtain ⟨A', hA', Q', hQ', hQA', hr, hi⟩ := ih
      by_cases hq : ∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q
      · exact ⟨A', hA', Q', hQ', hQA', hr, Or.inr hq⟩
      · have hq_neg := hq
        push Not at hq
        obtain ⟨q', hq', h4⟩ := hq
        have hq'zero : q' ≠ 0 := ne_of_mem_of_not_mem hq' zero_not_mem_ppowers_in_set
        have hq'zero' : (q' : ℚ) ≠ 0 := by
          exact_mod_cast hq'zero
        let A'' := A'.filter fun n ↦ ¬ (q' ∣ n ∧ Nat.Coprime q' (n / q'))
        let Q'' := insert q' Q'
        have hq'' : q' ∉ Q' := by
          rw [Finset.disjoint_left] at hQA'
          exact fun hmem ↦ hQA' hmem hq'
        refine ⟨A'', (Finset.filter_subset _ _).trans hA', Q'', ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (ppowers_in_set_subset hA' hq') hQ'
        · refine Finset.disjoint_insert_left.2 ⟨?_, ?_⟩
          · intro hmem
            rcases (mem_ppowers_in_set.mp hmem).2 with ⟨x, hx⟩
            rcases (mem_local_part (A := A'') (q := q') x).mp hx with ⟨hxA'', hxdvd, hxcop⟩
            exact (Finset.mem_filter.mp hxA'').2 ⟨hxdvd, hxcop⟩
          · exact hQA'.mono_right (ppowers_in_set_subset (Finset.filter_subset _ _))
        · have hrs : (rec_sum Q'' : ℝ) = rec_sum Q' + 1 / (q' : ℝ) := by
            have hrsQ : rec_sum Q'' = rec_sum Q' + (1 : ℚ) / q' := by
              simp [Q'', rec_sum, hq'', add_comm]
            simpa [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
              congrArg (fun x : ℚ ↦ (x : ℝ)) hrsQ
          have hsplit : Disjoint (local_part A' q') A'' := by
            rw [Finset.disjoint_left]
            intro n hnlocal hnA''
            rcases (mem_local_part (A := A') (q := q') n).mp hnlocal with ⟨_, hndvd, hncop⟩
            exact (Finset.mem_filter.mp hnA'').2 ⟨hndvd, hncop⟩
          have hunion : local_part A' q' ∪ A'' = A' := by
            ext n
            constructor
            · intro hn
              rcases Finset.mem_union.mp hn with hn | hn
              · exact (mem_local_part (A := A') (q := q') n).mp hn |>.1
              · exact (Finset.mem_filter.mp hn).1
            · intro hnA
              by_cases hp : q' ∣ n ∧ Nat.Coprime q' (n / q')
              · exact Finset.mem_union.mpr <| Or.inl <|
                  (mem_local_part (A := A') (q := q') n).2 ⟨hnA, hp.1, hp.2⟩
              · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hnA, hp⟩
          have hlocaleq : rec_sum_local A' q' / q' = rec_sum (local_part A' q') := by
            rw [rec_sum_local, rec_sum, Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hn0 : n = 0
            · simp [hn0]
            · field_simp [hn0, hq'zero']
          have hrs2a : rec_sum A'' + rec_sum_local A' q' / q' = rec_sum A' := by
            calc
              rec_sum A'' + rec_sum_local A' q' / q' =
                  rec_sum A'' + rec_sum (local_part A' q') := by
                rw [hlocaleq]
              _ = rec_sum (local_part A' q' ∪ A'') := by
                rw [add_comm, ← rec_sum_disjoint hsplit]
              _ = rec_sum A' := by
                rw [hunion]
          have hrs2a_real : (rec_sum A'' : ℝ) + rec_sum_local A' q' / (q' : ℝ) = rec_sum A' := by
            exact_mod_cast hrs2a
          have hrs3 : (rec_sum A' : ℝ) ≤ rec_sum A'' + ε * (1 / (q' : ℝ)) := by
            rw [← hrs2a_real, div_eq_mul_one_div]
            have hqnonneg : 0 ≤ (q' : ℝ) := by
              exact_mod_cast Nat.zero_le q'
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_right h4 <| one_div_nonneg.mpr hqnonneg) (rec_sum A'' : ℝ)
          have hmain : (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) ≤ rec_sum A'' := by
            linarith [hr, hrs3]
          have hrewrite :
              (rec_sum A : ℝ) - ε * rec_sum Q'' =
                (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) := by
            rw [hrs]
            ring
          rw [hrewrite]
          exact hmain
        · left
          rw [Nat.succ_le_iff]
          refine (hi.resolve_right hq_neg).trans_lt ?_
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset
            (Finset.sdiff_subset_sdiff Finset.Subset.rfl (Finset.filter_subset _ _))]
          simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors,
            and_assoc] at hq'
          obtain ⟨x, hx₁, hx₂, hx₃, -, hx₅⟩ := hq'
          refine ⟨x, ?_⟩
          simp [hx₁, hx₂, hx₅, hA' hx₁]

lemma pruning_lemma_one :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ ε : ℝ, 0 < ε →
      ∃ B ⊆ A,
        ((rec_sum A : ℝ) - ε * 2 * log (log N) ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [explicit_mertens] with N hN A hA ε hε
  obtain ⟨B, hB, Q, hQ, haux, h_recsums, h_local⟩ := pruning_lemma_one_prec A ε (A.card + 1)
  refine ⟨B, hB, ?_, ?_⟩
  · have hQu : Q ⊆ (Finset.range (N + 1)).filter IsPrimePow := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_range]
      have hqA : q ∈ ppowers_in_set A := hQ hq
      simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter] at hqA
      obtain ⟨a, ha, hqa, hq', hq''⟩ := hqA
      exact ⟨(Nat.divisor_le hqa).trans_lt (Finset.mem_range.mp (hA ha)), hq'⟩
    have hQt :
        (rec_sum Q : ℝ) ≤
          ((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) := by
      simp only [rec_sum, Rat.cast_sum, one_div, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hQu (by simp)
    nlinarith
  · rcases h_local with hcard | hlocal
    · exfalso
      rw [Nat.succ_le_iff] at hcard
      exact not_lt_of_ge (Finset.card_le_card Finset.sdiff_subset) hcard
    · exact hlocal

lemma pruning_lemma_two_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 4 * ε * log (log N) < α → (∀ n ∈ A, M ≤ ↑n) →
      α ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A q) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A,
          (α - 1 / M ≤ rec_sum A_i) ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (i ≤ (A \ A_i).card ∨ (rec_sum A_i : ℝ) < α) := by
  filter_upwards [pruning_lemma_one] with N hN M α ε A hA hM hMN hε hεα hMA hrec hsmooth i
  induction i with
  | zero =>
      refine ⟨A, Finset.Subset.rfl, ?_, ?_, Or.inl zero_le'⟩
      · exact (sub_le_self _ (by simp only [hM.le, one_div, inv_nonneg])).trans hrec
      · intro q hq
        exact (hsmooth _ hq).2
  | succ i ih =>
      obtain ⟨A_i, hA_i, ih1, ih2, ih3⟩ := ih
      by_cases hr : (rec_sum A_i : ℝ) < α
      · exact ⟨A_i, hA_i, ih1, ih2, Or.inr hr⟩
      · have hA_ir : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        let ε' := 2 * ε
        obtain ⟨B, hB, hN1, hN2⟩ := hN A_i hA_ir ε' (mul_pos zero_lt_two hε)
        have ht0 : α ≤ rec_sum A_i := not_lt.mp hr
        have hBexists : B.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          simp only [rec_sum_empty, Rat.cast_zero, sub_nonpos] at hN1
          have ht1 : 4 * ε * log (log N) < ε' * 2 * log (log N) := by
            exact hεα.trans_le (ht0.trans hN1)
          rw [mul_right_comm 2 ε] at ht1
          linarith only [ht1]
        rcases hBexists with ⟨x, hx⟩
        have hxA1 : x ∈ A_i := hB hx
        have hxA2 : x ∈ A := hA_i hxA1
        let A_i' := A_i.erase x
        have h3 : A_i' ⊆ A_i := Finset.erase_subset _ _
        refine ⟨A_i', h3.trans hA_i, ?_, ?_, ?_⟩
        · have hrs2 : (rec_sum A_i : ℝ) - 1 / x = rec_sum A_i' := by
            simp only [A_i', rec_sum, sub_eq_iff_eq_add, Rat.cast_sum, one_div, Rat.cast_inv,
              Rat.cast_natCast, Finset.sum_erase_add _ _ hxA1]
          linarith only [ht0, one_div_le_one_div_of_le hM (hMA x (hA_i (hB hx))), hrs2]
        · intro q hq
          by_cases hxq : q ∣ x ∧ Nat.Coprime q (x / q)
          · have hlocalpart : local_part A_i' q = (local_part A_i q).erase x := by
              exact filter_erase _ _ _
            have hlocal : rec_sum_local A_i q = rec_sum_local A_i' q + q / x := by
              rw [rec_sum_local, rec_sum_local, hlocalpart, Finset.sum_erase_add]
              rw [local_part, Finset.mem_filter]
              exact ⟨hB hx, hxq⟩
            have hlocal2 : rec_sum_local A_i q - q / x = rec_sum_local A_i' q := by
              rwa [sub_eq_iff_eq_add]
            rw [← hlocal2]
            push_cast
            have hppB : q ∈ ppowers_in_set B := by
              rw [ppowers_in_set, Finset.mem_biUnion]
              refine ⟨x, hx, Finset.mem_filter.2 ?_⟩
              refine ⟨Nat.mem_divisors.2 ⟨hxq.1, ?_⟩, (mem_ppowers_in_set.1 hq).1, hxq.2⟩
              rintro rfl
              exact not_le_of_gt hM (by simpa only [Nat.cast_zero] using hMA _ hxA2)
            have hlocal3 : (rec_sum_local B q : ℝ) ≤ rec_sum_local A_i q :=
              Rat.cast_le.2 (rec_sum_local_mono hB)
            have hll : ε + ε < rec_sum_local A_i q := by
              rw [← two_mul ε]
              exact (hN2 q hppB).trans_le hlocal3
            have hll2 : (q : ℝ) / x ≤ ε := by
              rw [div_le_iff₀ (hM.trans_le (hMA x hxA2))]
              have hppA : ppowers_in_set A_i' ⊆ ppowers_in_set A :=
                ppowers_in_set_subset (h3.trans hA_i)
              exact (hsmooth q (hppA hq)).1.trans (mul_le_mul_of_nonneg_left (hMA x hxA2) hε.le)
            rw [lt_sub_iff_add_lt]
            linarith
          · have hrecl : rec_sum_local A_i q = rec_sum_local A_i' q := by
              have hlocalaux : local_part A_i q = local_part A_i' q := by
                ext n
                by_cases hnx : n = x
                · subst hnx
                  simp [A_i', local_part, hxA1, hxq]
                · simp [A_i', local_part, hnx]
              rw [rec_sum_local, rec_sum_local, hlocalaux]
            rw [← hrecl]
            exact ih2 q (ppowers_in_set_subset h3 hq)
        · left
          have hcard : (A \ A_i).card < (A \ A_i').card := by
            rw [Finset.card_sdiff_of_subset hA_i, Finset.card_sdiff_of_subset (h3.trans hA_i),
              tsub_lt_tsub_iff_left_of_le (Finset.card_le_card hA_i)]
            exact Finset.card_erase_lt_of_mem hxA1
          have hcard' : (A \ A_i).card + 1 ≤ (A \ A_i').card := Nat.succ_le_iff.2 hcard
          cases ih3 with
          | inl hf1 =>
              linarith
          | inr hf2 =>
              exfalso
              linarith

lemma pruning_lemma_two :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → ε > 0 → 4 * ε * log (log N) < α →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      α + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      ∃ B ⊆ A,
        ((rec_sum B : ℝ) < α) ∧
        (α - 1 / M ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [pruning_lemma_one, pruning_lemma_two_ind] with
    N h₁ h₂ M α ε A hA hM hMN hε hεα hMA hrec hsmooth
  obtain ⟨A', hA', hA'₁, hA'₃⟩ := h₁ A hA ε hε
  have hA'range : A' ⊆ Finset.range (N + 1) := hA'.trans hA
  have hMA' : ∀ n ∈ A', M ≤ (n : ℝ) := fun n hn => hMA n (hA' hn)
  have hrecA' : α ≤ rec_sum A' := by
    have hA'₁' : ((rec_sum A : ℝ) - 2 * ε * log (log N) ≤ rec_sum A') := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hA'₁
    nlinarith
  have hsmooth' : ∀ q ∈ ppowers_in_set A', (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A' q := by
    intro q hq
    exact ⟨hsmooth q ((ppowers_in_set_subset hA') hq), hA'₃ q hq⟩
  let i := A'.card + 1
  obtain ⟨B, hB, hB₁, hB₂, hB₃⟩ := h₂ M α ε A' hA'range hM hMN hε hεα hMA' hrecA' hsmooth' i
  refine ⟨B, hB.trans hA', ?_, hB₁, hB₂⟩
  refine hB₃.resolve_left ?_
  dsimp [i]
  intro hcard
  exact not_le_of_gt (Nat.lt_succ_self A'.card)
    (hcard.trans (Finset.card_le_card Finset.sdiff_subset))

lemma main_tech_lemma_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → w < 2 * M → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / w ^ 2 →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ (d : ℝ) ≤ w ∧ d ∣ n) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A, ∃ d_i : ℕ,
          y ≤ d_i ∧ d_i ≤ ⌈y⌉₊ + i ∧ d_i ≤ ⌊w⌋₊ ∧
          rec_sum A_i < 2 / d_i ∧ (2 : ℝ) / d_i - 1 / M ≤ rec_sum A_i ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (∀ n ∈ A_i, ∀ k, k ∣ n → k < d_i → (k : ℝ) < y) ∧
          ((∃ n ∈ A_i, d_i ∣ n) ∨
            (∀ n ∈ A_i, ∀ k, k ∣ n → k ≤ ⌈y⌉₊ + i → k ≤ ⌊w⌋₊ → (k : ℝ) < y)) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [pruning_lemma_two, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw2 hNw hMA hrec hsmooth hdiv i
  have hy01 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hy12 : 2 ≤ y + 1 := by linarith
  have hceil_lt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy01.le
  have hwzero : 0 < w := lt_of_lt_of_le zero_lt_two h2w
  have hfloor_le : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
  have hεNaux : 4 * ε * log (log N) < 2 * (3 * ε * log (log N)) := by
    nlinarith [hε, hloglog_pos]
  have hεNaux2 : 2 * (3 * ε * log (log N)) ≤ 2 * (2 / w ^ 2) := by
    nlinarith [hNw]
  have hwaux : 2 * w ≤ w ^ 2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right h2w hwzero.le
  induction i with
  | zero =>
      let α : ℚ := 2 / ⌈y⌉₊
      have hαaux : (α : ℝ) = 2 / ⌈y⌉₊ := by
        simp [α]
      have hceil_le_w : (⌈y⌉₊ : ℝ) ≤ w := (Nat.cast_le.mpr hyw2).trans hfloor_le
      have hceil_pos : 0 < (⌈y⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_pos.mpr hy01
      have hα : 4 * ε * log (log N) < α := by
        have hα1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / ⌈y⌉₊ := by
          have hα1' : (4 : ℝ) / w ^ 2 ≤ 2 / ⌈y⌉₊ := by
            refine (div_le_div_iff₀ (by positivity) hceil_pos).2 ?_
            nlinarith [hceil_le_w, hwaux]
          simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hα1'
        rw [hαaux]
        exact hεNaux.trans_le (hεNaux2.trans hα1)
      have hrec2 : (α : ℝ) + 2 * ε * log (log N) ≤ rec_sum A := by
        rw [hαaux]
        have hdivaux : (2 : ℝ) / ⌈y⌉₊ ≤ 2 / y :=
          div_le_div_of_nonneg_left zero_le_two hy01 (Nat.le_ceil y)
        linarith
      obtain ⟨B, hB, hB', hB'', hN'⟩ := hN M α ε A hA hM hMN hε hα hMA hrec2 hsmooth
      refine ⟨B, hB, ⌈y⌉₊, ?_, Nat.le_refl _, hyw2, ?_, ?_, hN', ?_, ?_⟩
      · exact Nat.le_ceil y
      · exact_mod_cast hB'
      · simpa [hαaux] using hB''
      · intro n hn k hk1 hk2
        exact Nat.lt_ceil.mp hk2
      · refine or_iff_not_imp_left.2 ?_
        intro hp n hn k hk1 hk2 hk3
        have hklt : k < ⌈y⌉₊ := by
          refine lt_of_le_of_ne hk2 ?_
          intro hk
          apply hp
          exact ⟨n, hn, hk ▸ hk1⟩
        exact Nat.lt_ceil.mp hklt
  | succ i ih =>
      rcases ih with ⟨A_i, hA_i, d_i, hyi, hdiy, hdiw, hrec_lt, hrec_ge, hsmooth_i, hsmall, hfinal⟩
      by_cases hdiv2 : ∃ n ∈ A_i, d_i ∣ n
      · exact ⟨A_i, hA_i, d_i, hyi, hdiy.trans (Nat.le_succ _), hdiw, hrec_lt, hrec_ge,
          hsmooth_i, hsmall, Or.inl hdiv2⟩
      · let dNext := min (⌈y⌉₊ + i + 1) ⌊w⌋₊
        have hdNext : d_i + 1 ≤ dNext := by
          change d_i + 1 ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
          rw [le_min_iff]
          refine ⟨Nat.succ_le_succ hdiy, ?_⟩
          refine lt_of_le_of_ne hdiw ?_
          intro hdEq
          have hA_in : A_i.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hAi
            have hrec_nonpos : (rec_sum A_i : ℝ) ≤ 0 := by
              simp [hAi]
            have hlower : (2 : ℝ) / d_i - 1 / M ≤ 0 := le_trans hrec_ge hrec_nonpos
            have hdipos : 0 < (d_i : ℝ) := hy01.trans_le hyi
            have hdi_le_w : (d_i : ℝ) ≤ w := (Nat.cast_le.mpr hdiw).trans hfloor_le
            have hMw' : 2 * M ≤ w := by
              have hMd : 2 * M ≤ (d_i : ℝ) := by
                have hlower' := hlower
                field_simp [hdipos.ne', hM.ne'] at hlower'
                nlinarith
              linarith
            exact (not_lt_of_ge hMw') hMw
          obtain ⟨x, hx⟩ := hA_in
          obtain ⟨d, hd1, hd2, hd3⟩ := hdiv x (hA_i hx)
          have hdle : d ≤ ⌊w⌋₊ := Nat.le_floor hd2
          have hdle' : d ≤ d_i := by simpa [hdEq] using hdle
          have hlt : d < d_i := by
            refine lt_of_le_of_ne hdle' ?_
            intro hdEq'
            apply hdiv2
            exact ⟨x, hx, hdEq' ▸ hd3⟩
          exact (not_le_of_gt (hsmall x hx d hd3 hlt)) hd1
        let αNext : ℚ := 2 / dNext
        have hαNextaux : (αNext : ℝ) = 2 / (dNext : ℝ) := by
          simp [αNext]
        have hdNext_le_floor : dNext ≤ ⌊w⌋₊ := by
          simp [dNext]
        have hdNext_le_w : (dNext : ℝ) ≤ w := (Nat.cast_le.mpr hdNext_le_floor).trans hfloor_le
        have hdipos_real : 0 < (d_i : ℝ) := hy01.trans_le hyi
        have hdipos_nat : 0 < d_i := Nat.cast_pos.mp hdipos_real
        have hOneLt_dNext : (1 : ℝ) < dNext := by
          exact_mod_cast lt_of_lt_of_le (Nat.succ_lt_succ hdipos_nat) hdNext
        have hαNext : 4 * ε * log (log N) < αNext := by
          have hαNext1' : (4 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) := by
            refine (div_le_div_iff₀ (by positivity) (zero_lt_one.trans hOneLt_dNext)).2 ?_
            nlinarith [hdNext_le_w, hwaux]
          have hαNext1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / (dNext : ℝ) := by
            simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hαNext1'
          rw [hαNextaux]
          exact hεNaux.trans_le (hεNaux2.trans hαNext1)
        have hrec2 : (αNext : ℝ) + 2 * ε * log (log N) ≤ rec_sum A_i := by
          rw [hαNextaux]
          have hrec3p : (d_i : ℝ) ≤ (dNext : ℝ) - 1 := by
            have hdNext' : (d_i : ℝ) + 1 ≤ dNext := by exact_mod_cast hdNext
            linarith
          have hrec3 : (2 : ℝ) / ((dNext : ℝ) - 1) - 1 / M ≤ rec_sum A_i := by
            have hrec3' : (2 : ℝ) / ((dNext : ℝ) - 1) ≤ 2 / d_i :=
              div_le_div_of_nonneg_left zero_le_two hdipos_real hrec3p
            exact le_trans (sub_le_sub_right hrec3' _) hrec_ge
          have hrec5 : (2 : ℝ) / (dNext : ℝ) ^ 2 ≤ 2 / ((dNext : ℝ) - 1) - 2 / (dNext : ℝ) := by
            have hdNext_pos : 0 < (dNext : ℝ) := zero_lt_one.trans hOneLt_dNext
            have hsubpos : 0 < (dNext : ℝ) - 1 := sub_pos.mpr hOneLt_dNext
            field_simp [hdNext_pos.ne', hsubpos.ne']
            nlinarith
          have hrec6 : (2 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_left zero_le_two (by positivity) ?_
            nlinarith [hdNext_le_w, hwzero]
          linarith [hMN2, hNw, hrec3, hrec5, hrec6]
        have hA_i' : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        have hMA' : ∀ n ∈ A_i, M ≤ (n : ℝ) := fun n hn => hMA n (hA_i hn)
        have hsmooth' : ∀ q ∈ ppowers_in_set A_i, (q : ℝ) ≤ ε * M := by
          intro q hq
          exact hsmooth q ((ppowers_in_set_subset hA_i) hq)
        obtain ⟨B, hB, hBlt, hBge, hBsm⟩ :=
          hN M αNext ε A_i hA_i' hM hMN hε hαNext hMA' hrec2 hsmooth'
        refine ⟨B, hB.trans hA_i, dNext, ?_, ?_, hdNext_le_floor, ?_, ?_, hBsm, ?_, ?_⟩
        · exact hyi.trans (Nat.cast_le.mpr <| (Nat.le_succ _).trans hdNext)
        · simp [dNext]
        · exact_mod_cast hBlt
        · simpa [hαNextaux] using hBge
        · intro n hn k hk1 hk2
          have hn2 : n ∈ A_i := hB hn
          cases hfinal with
          | inl h =>
              exfalso
              exact hdiv2 h
          | inr hnew2 =>
              have hk2' : k ≤ ⌈y⌉₊ + i := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact Nat.le_of_lt_succ hk2.1
              have hk2'' : k ≤ ⌊w⌋₊ := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact le_of_lt hk2.2
              exact hnew2 n hn2 k hk1 hk2' hk2''
        · by_cases hdNextDiv : ∃ n ∈ B, dNext ∣ n
          · exact Or.inl hdNextDiv
          · right
            intro n hn k hk1 hk2 hk3
            have hn2 : n ∈ A_i := hB hn
            cases hfinal with
            | inl h =>
                exfalso
                exact hdiv2 h
            | inr hnew2 =>
                have hk2' : k ≤ dNext := by
                  change k ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
                  rw [le_min_iff]
                  exact ⟨hk2, hk3⟩
                have hk2'' : k < dNext := by
                  refine lt_of_le_of_ne hk2' ?_
                  intro hkEq
                  apply hdNextDiv
                  exact ⟨n, hn, hkEq ▸ hk1⟩
                have hk2''' : k ≤ ⌈y⌉₊ + i := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact Nat.le_of_lt_succ hk2''.1
                have hk2'''' : k ≤ ⌊w⌋₊ := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact le_of_lt hk2''.2
                exact hnew2 n hn2 k hk1 hk2''' hk2''''

lemma main_tech_lemma :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 2 * M > w → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / (w ^ 2) →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ w) ∧ d ∣ n) →
      ∃ A' ⊆ A, ∃ d : ℕ,
        A' ≠ ∅ ∧ y ≤ d ∧ ((d : ℝ) ≤ w) ∧ rec_sum A' < 2 / d ∧
        (2 : ℝ) / d - 1 / M ≤ rec_sum A' ∧
        (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q) ∧
        (∃ n ∈ A', d ∣ n) ∧
        (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k : ℝ) < y) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [main_tech_lemma_ind, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv
  have hy01 : 0 < y := by
    exact lt_of_lt_of_le zero_lt_one hy
  have hwzero : 0 < w := by
    exact lt_of_lt_of_le zero_lt_two h2w
  let i := ⌊w⌋₊ - ⌈y⌉₊
  specialize hN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv i
  rcases hN with ⟨A', hA', d, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  refine ⟨A', hA', d, ?_⟩
  have hdw : (d : ℝ) ≤ w := by
    have hfloorw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
    have hdfloor : (d : ℝ) ≤ (⌊w⌋₊ : ℝ) := by
      exact_mod_cast hd3
    exact hdfloor.trans hfloorw
  have hA'ne : A' ≠ ∅ := by
    intro hA'em
    have hreczero : rec_sum A' = 0 := by
      rw [hA'em, rec_sum_empty]
    have hlow : (2 : ℝ) / d - 1 / M ≤ 0 := by
      rw [hreczero] at hd5
      simpa using hd5
    have haux1 : (2 : ℝ) / d ≤ 1 / M := by
      exact sub_nonpos.mp hlow
    have haux2 : (2 : ℝ) / w ≤ 2 / d := by
      refine div_le_div_of_nonneg_left zero_le_two ?_ ?_
      · exact hy01.trans_le hd1
      · exact hdw
    have haux3 : (2 : ℝ) / w ^ 2 ≤ 2 / w := by
      field_simp [hwzero.ne']
      nlinarith [h2w, hwzero]
    have haux4 : 3 * ε * log (log N) < ε * log (log N) := by
      exact lt_of_le_of_lt hNw <| lt_of_le_of_lt haux3 <| lt_of_le_of_lt haux2 <|
        lt_of_le_of_lt haux1 hMN2
    have hthree_lt_one : (3 : ℝ) < 1 := by
      nlinarith [haux4, hε, hloglog_pos]
    linarith
  refine ⟨hA'ne, hd1, hdw, hd4, hd5, hd6, ?_, hd7⟩
  · cases hd8 with
    | inl h =>
        exact h
    | inr h =>
        exfalso
        have hAexists : ∃ x : ℕ, x ∈ A' := by
          by_contra h
          apply hA'ne
          apply Finset.not_nonempty_iff_eq_empty.mp
          simpa [Finset.Nonempty] using h
        rcases hAexists with ⟨x, hx⟩
        have hxA : x ∈ A := hA' hx
        rcases hdiv x hxA with ⟨m, hm1, hm2, hm3⟩
        have htempw : m ≤ ⌊w⌋₊ := Nat.le_floor hm2
        have htemp : m ≤ ⌈y⌉₊ + i := by
          have hobvious : ⌈y⌉₊ + i = ⌊w⌋₊ := by
            dsimp [i]
            exact Nat.add_sub_of_le hyw
          rw [hobvious]
          exact htempw
        have := h x hx m hm3 htemp htempw
        linarith

private lemma large_enough_Naux1_hreduce
    (N : ℕ) (hN6 : 0 < (N : ℝ)) (hN7 : 0 < log (log N)) (hN8 : 0 < log N) :
    (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
      ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
  have hAiff :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
            (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) by positivity)
      (show 0 <
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) by
            positivity)]
    have hsq :
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) =
          (N : ℝ) ^ ((1 - (3 : ℝ) / log (log N)) * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      ring_nf
    rw [Real.log_mul
        (show (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by
          positivity)
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ≠ 0 by
          positivity)]
    rw [Real.log_div
        (Real.rpow_pos_of_pos hN6 _).ne'
        (show (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by positivity)]
    rw [Real.log_div
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) ≠ 0 by positivity)
        (show (16 * N ^ 2 * log N ^ 2 : ℝ) ≠ 0 by positivity)]
    have hlogDen1 :
        Real.log (16 * N ^ 2 * log N ^ 2 : ℝ) =
          Real.log 16 + 2 * Real.log N + 2 * Real.log (Real.log N) := by
      rw [show (16 * N ^ 2 * log N ^ 2 : ℝ) = 16 * ((N : ℝ) ^ 2 * log N ^ 2) by
        ring_nf]
      rw [Real.log_mul (show (16 : ℝ) ≠ 0 by norm_num)
        (show (N : ℝ) ^ 2 * log N ^ 2 ≠ 0 by positivity)]
      rw [Real.log_mul
        (show (N : ℝ) ^ 2 ≠ 0 by positivity)
        (show log N ^ 2 ≠ 0 by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, Real.log_rpow hN6, Real.log_rpow hN8]
      ring_nf
    have hlogDen2 :
        Real.log (2 * log N ^ (1 / 100 : ℝ)) =
          Real.log 2 + (1 / 100 : ℝ) * Real.log (Real.log N) := by
      rw [Real.log_mul
        (show (2 : ℝ) ≠ 0 by norm_num)
        (show log N ^ (1 / 100 : ℝ) ≠ 0 by positivity)]
      rw [Real.log_rpow hN8]
    rw [Real.log_rpow hN6, hsq, hlogDen1, hlogDen2]
    simp_rw [Real.log_rpow hN6]
    have hlog32 : Real.log (2 * 16 : ℝ) = Real.log 2 + Real.log 16 := by
      rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (16 : ℝ) ≠ 0 by norm_num)]
    constructor <;> intro h <;> rw [hlog32] at * <;>
      field_simp [hN7.ne'] at h ⊢ <;> ring_nf at h ⊢ <;> linarith
  have hBiff :
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
      (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
    rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num)
      (Real.rpow_pos_of_pos hN8 _).ne']
    rw [Real.log_rpow hN8, Real.log_rpow hN6]
    constructor <;> intro h <;>
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  exact hAiff.trans hBiff.symm

lemma large_enough_Naux1 :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) := by
  let C : ℝ := (((2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ))) ^ ((1 : ℝ) / 2))
  have haux4 :=
    (isLittleO_log_id_atTop.bound <| by
      rw [one_div_pos]
      exact mul_pos zero_lt_two (Real.log_pos (show (1 : ℝ) < 2 * 16 by norm_num)))
  have haux5 :
      ∀ᶠ x : ℝ in atTop,
        ‖log x‖ ≤ (1 / C) * ‖x ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound <| by
      rw [one_div_pos]
      dsimp [C]
      exact Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) by norm_num)
        _
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , tendsto_log_coe_at_top.eventually haux4
    , tendsto_log_coe_at_top.eventually haux5 ] with
    N hN1 hN2 hN3 hN3new4 hN3new5
  dsimp at hN1 hN2 hN3new4
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    exact lt_of_lt_of_le hpowpos hN2
  have hN12 : 2 * log (2 * 16) * log (log N) ≤ log N := by
    have habs : |log (log N)| ≤ (1 / (2 * log (2 * 16))) * |log N| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new4
    rw [abs_of_nonneg hN7.le, abs_of_nonneg hN8.le] at habs
    have hconst : 0 < 2 * log (2 * 16) := by
      exact mul_pos zero_lt_two (Real.log_pos (by norm_num))
    have hdiv : log (log N) ≤ log N / (2 * log (2 * 16)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * (2 * log (2 * 16)) ≤ log N := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hN13 :
      C * log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs :
        |log (log N)| ≤ (1 / C) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new5
    rw [abs_of_nonneg hN7.le, abs_of_nonneg (by positivity)] at habs
    have hconst : 0 < C := by
      dsimp [C]
      positivity
    have hdiv :
        log (log N) ≤ log N ^ ((1 : ℝ) / 2) / C := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * C ≤ log N ^ ((1 : ℝ) / 2) := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hC_sq : C * C = 2 * (2 + (1 / 100 : ℝ)) := by
    dsimp [C]
    have hbase : 0 < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) := by positivity
    rw [← Real.rpow_add hbase]
    norm_num
  have hreduce :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
    exact large_enough_Naux1_hreduce N hN6 hN7 hN8
  rw [hreduce]
  rw [← Real.log_le_log_iff
    (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
    (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
  rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num) (Real.rpow_pos_of_pos hN8 _).ne',
    Real.log_rpow hN8, Real.log_rpow hN6]
  have hfirst :
      log (2 * 16) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have htmp : 2 * log (2 * 16) * log (log N) ≤ log N := hN12
    have hpos : 0 < log (log N) := hN7
    have htmp' : 2 * log (2 * 16) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hpos).2 <| by simpa [mul_assoc] using htmp
    nlinarith
  have hsecond :
      (2 + 1 / 100 : ℝ) * log (log N) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have hsq : 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 ≤ log N := by
      have hmul :=
        mul_le_mul hN13 hN13
          (show 0 ≤ C * log (log N) by positivity)
          (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
      have hsimp :
          (C * log (log N)) * (C * log (log N)) =
            2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
        calc
          (C * log (log N)) * (C * log (log N)) =
              (C * C) * (log (log N) * log (log N)) := by ring
          _ = 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
              rw [hC_sq]
              ring_nf
      have hsimp' : (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) = log N := by
        rw [← Real.rpow_add hN8]
        norm_num
      calc
        2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 = (C * log (log N)) * (C * log (log N)) := by
          symm
          exact hsimp
        _ ≤ (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) := hmul
        _ = log N := hsimp'
    have htmp' : 2 * (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hN7).2 <| by
        simpa [mul_assoc, pow_two] using hsq
    nlinarith
  calc
    log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤
        (1 / 2 : ℝ) * (log N / log (log N)) + (1 / 2 : ℝ) * (log N / log (log N)) := by
          exact add_le_add hfirst hsecond
    _ = log N / log (log N) := by ring
    _ = (1 / log (log N)) * log N := by ring

lemma large_enough_Naux2 :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤
          (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) -
            1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  intro c hc
  have haux :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound (show 0 < (1 : ℝ) by norm_num)
  have haux2 := (isLittleO_log_rpow_atTop zero_lt_one).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (6 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , eventually_ge_atTop (64 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , tendsto_natCast_atTop_atTop.eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (-log c / (7 - 1 / 500))) ] with
    N hN1 hN2 hN3 hNnew hNnew2 hNnew3
  dsimp at hN1 hN2 hNnew3
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    linarith
  have hN9 : log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs : |log (log N)| ≤ (1 : ℝ) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew
    rw [abs_of_nonneg (le_of_lt hN7), abs_of_nonneg (by positivity), one_mul] at habs
    exact habs
  have hN10 : log N ≤ N := by
    have habs : |log N| ≤ (1 : ℝ) * |(N : ℝ) ^ (1 : ℝ)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew2
    rw [abs_of_nonneg (le_of_lt hN8), abs_of_nonneg (by positivity), one_mul, Real.rpow_one] at habs
    exact habs
  constructor
  · have hmain :
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) * (log N) ^ (1 / 500 : ℝ) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
      rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) *
          (log N) ^ (1 / 500 : ℝ) by positivity)
        (show 0 < c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
      rw [Real.log_mul (Real.rpow_pos_of_pos hN6 _).ne' (Real.rpow_pos_of_pos hN8 _).ne',
        Real.log_mul hc.ne' (Real.rpow_pos_of_pos hN6 _).ne', Real.log_rpow hN6,
        Real.log_rpow hN8, Real.log_rpow hN6]
      have hcN : -(7 - (1 : ℝ) / 500) * log (log N) ≤ log c := by
        have ha : 0 < (7 - (1 : ℝ) / 500) := by norm_num
        have htmp : -log c ≤ log (log N) * (7 - (1 : ℝ) / 500) := by
          exact (_root_.div_le_iff₀ ha).mp hNnew3
        nlinarith
      have hsqmul : log (log N) * log (log N) ≤ log N := by
        have hsq' :=
          mul_le_mul hN9 hN9
            (show 0 ≤ log (log N) by linarith)
            (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
        have hlog : log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) = log N := by
          rw [← Real.rpow_add hN8]
          norm_num
        calc
          log (log N) * log (log N) ≤ log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) := by
            simpa [pow_two] using hsq'
          _ = log N := hlog
      have hdiv : log (log N) ≤ log N / log (log N) := by
        exact (_root_.le_div_iff₀ hN7).2 hsqmul
      have hfrac : -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤ log c := by
        have hstep :
            -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤
              -(7 : ℝ) * log (log N) + (1 / 500 : ℝ) * log (log N) := by
          nlinarith
        linarith
      have hadd := add_le_add_right hfrac ((1 - (1 : ℝ) / log (log N)) * log N)
      have hrew :
          (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) +
              ((1 - (1 : ℝ) / log (log N)) * log N) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        field_simp [hN7.ne']
        ring
      have hrew' :
          ((1 - (1 : ℝ) / log (log N)) * log N) +
              (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        simpa [add_assoc, add_left_comm, add_comm] using hrew
      rw [hrew'] at hadd
      simpa [add_assoc, add_left_comm, add_comm] using hadd
    exact (le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).mpr hmain
  · refine le_trans (b := (7 : ℝ) / (log N ^ ((1 : ℝ) / 500))) ?_ ?_
    · refine (_root_.le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).2 ?_
      rw [← Real.rpow_add hN8]
      have hpow : log N ^ (-(1 / 101 : ℝ) + (1 / 500 : ℝ)) ≤ (1 : ℝ) := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hN2
        · norm_num
      linarith
    · rw [le_sub_iff_add_le]
      have hlogpow : log N ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ ((1 : ℝ) / 500) := by
        exact Real.rpow_le_rpow (le_of_lt hN8) hN10 (by norm_num : 0 ≤ (1 : ℝ) / 500)
      have hNexp : (N : ℝ) ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
        apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5)
        have hrec : 1 / log (log N) ≤ (1 : ℝ) / 6 := by
          exact one_div_le_one_div_of_le (by norm_num : 0 < (6 : ℝ)) hN1
        nlinarith
      have hInv :
          1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            1 / (log N ^ ((1 : ℝ) / 500)) := by
        exact one_div_le_one_div_of_le (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)
          (le_trans hlogpow hNexp)
      have hDne : log N ^ ((1 : ℝ) / 500) ≠ 0 := by positivity
      calc
        (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (log N ^ ((1 : ℝ) / 500)) := by
              exact add_le_add le_rfl hInv
        _ = (2 : ℝ) / (log N ^ ((1 : ℝ) / 500) / 4) := by
              field_simp [hDne]
              norm_num

lemma large_enough_Naux :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux1 := large_enough_Naux1
  have hlargeaux2 := large_enough_Naux2 c hc
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , hlargeaux2
    , hlargeaux1 ] with
    N hN1 hN2 hN3 hotheraux hnec
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    refine lt_of_lt_of_le ?_ hN1
    norm_num1
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num1 : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  dsimp
  intro hT3
  constructor
  · rw [← div_le_iff₀ (show 0 < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
    rw [← Real.rpow_sub hN6]
    have hexp :
        (1 - (8 : ℝ) / log (log N)) - (1 - (1 : ℝ) / log (log N)) =
          (-7 : ℝ) / log (log N) := by
      field_simp [hN7.ne']
      ring
    rw [hexp]
    refine le_trans ?_ hT3
    refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
    exact (div_le_div_iff_of_pos_right hN7).2 (by norm_num)
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
  constructor
  · refine le_trans
        (b :=
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) *
            ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 /
              (16 * (N : ℝ) ^ 2 * log N ^ 2)) ?_ ?_
    · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
    · have hstep :
          (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            (16 * (N : ℝ) ^ 2 * log N ^ 2) ≤
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / log N) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            ((N : ℝ) ^ 2 * log N) := by
        rw [div_le_div_iff₀
          (show 0 < 16 * (N : ℝ) ^ 2 * log N ^ 2 by positivity)
          (show 0 < (N : ℝ) ^ 2 * log N by positivity)]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hEq1 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) *
                (2 * log N ^ (1 / 100 : ℝ))⁻¹ *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                ((N : ℝ) ^ 2 * log N) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N) := by
          ring_nf
        have hEq2 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) / log N *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (16 * (N : ℝ) ^ 2 * log N ^ 2) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((log N)⁻¹ * 16 * log N ^ 2) := by
          rw [div_eq_mul_inv]
          ring_nf
        rw [hEq1, hEq2]
        have hcommon_nonneg :
            0 ≤
              ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                  (N : ℝ) ^ 2 := by
          positivity
        have hscalar :
            (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N ≤ (log N)⁻¹ * 16 * log N ^ 2 := by
          have h128 : (1 : ℝ) ≤ (128 : ℝ) ^ (500 : ℝ) := by
            apply one_le_rpow
            · norm_num
            · norm_num
          have hlogpow_ge_one : 1 ≤ log N ^ (1 / 100 : ℝ) := by
            apply one_le_rpow
            · exact le_trans h128 hN2
            · norm_num
          have hfac : 1 ≤ 2 * log N ^ (1 / 100 : ℝ) := by
            nlinarith
          have hleft :
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
            calc
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N =
                  log N * (2 * log N ^ (1 / 100 : ℝ))⁻¹ := by ac_rfl
              _ = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
                  symm
                  rw [div_eq_mul_inv]
          have hright :
              (log N)⁻¹ * 16 * log N ^ 2 = (16 * log N ^ 2) / log N := by
            calc
              (log N)⁻¹ * 16 * log N ^ 2 = 16 * log N ^ 2 * (log N)⁻¹ := by ac_rfl
              _ = (16 * log N ^ 2) / log N := by rw [div_eq_mul_inv]
          rw [hleft, hright]
          refine (div_le_div_iff₀ (show 0 < 2 * log N ^ (1 / 100 : ℝ) by positivity) hN8).2 ?_
          calc
            log N * log N = log N ^ 2 := by ring
            _ ≤ 16 * log N ^ 2 := by
              simpa [one_mul] using
                mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 16 by norm_num)
                  (show 0 ≤ log N ^ 2 by positivity)
            _ ≤ (16 * log N ^ 2) * (2 * log N ^ (1 / 100 : ℝ)) := by
              simpa [mul_one] using
                mul_le_mul_of_nonneg_left hfac (show 0 ≤ 16 * log N ^ 2 by positivity)
        exact mul_le_mul_of_nonneg_left hscalar hcommon_nonneg
      simpa using hstep
  · exact hotheraux

private lemma large_enough_N_hTp
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (_hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    192 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  have h500 : (0 : ℝ) < 500 := by norm_num
  have h5002 : (0 : ℝ) < 500 / 2 := by norm_num
  have hlog_nonneg : 0 ≤ log N := le_of_lt hN8
  have haux :
      192 * (log N) ^ (1 / 500 : ℝ) ≤
        (log N) ^ (1 / 500 : ℝ) * (log N) ^ (1 / 500 : ℝ) := by
    have h192 : (192 : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) := by
      rw [← Real.rpow_le_rpow_iff (show 0 ≤ (192 : ℝ) by norm_num)
        (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity) h500]
      rw [← Real.rpow_mul hlog_nonneg, one_div_mul_cancel (show (500 : ℝ) ≠ 0 by norm_num),
        Real.rpow_one]
      exact hN2
    exact mul_le_mul_of_nonneg_right h192 (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity)
  refine lt_of_le_of_lt haux ?_
  rw [← Real.rpow_add hN8]
  refine (Real.rpow_lt_rpow_iff
    (show 0 ≤ (log N) ^ (1 / 500 + 1 / 500 : ℝ) by positivity)
    (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h5002).1 ?_
  rw [← Real.rpow_mul hlog_nonneg]
  norm_num
  refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
  refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
  have hrightEq :
      ((N : ℝ) ^ (1 - (log (log N))⁻¹)) ^ (250 : ℕ) =
        (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
    norm_num
  have hdiv : (log (log N))⁻¹ ≤ 1 / 6 := by
    have h6 : (0 : ℝ) < 6 := by linarith
    simpa [one_div] using
      (one_div_le_one_div_of_le h6 hN1)
  have hpow :
      (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    have hpow' : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
      nlinarith
    simpa using hpow'
  exact le_trans hpow hrightEq.ge

private lemma large_enough_N_hT1
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
  have hstep :
      3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by
    gcongr
  calc
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := hstep
    _ = 2 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (3 / 500 : ℝ)) := by ring
    _ = 2 * (log N) ^ ((-(1 / 100 : ℝ)) + 3 / 500) := by
      rw [← Real.rpow_add hN8]
    _ = 2 * (log N) ^ (-(1 / 250 : ℝ)) := by congr 2; norm_num
    _ = 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
      rw [div_eq_mul_inv]
      congr 1
      calc
        (log N) ^ (-(1 / 250 : ℝ)) = ((log N) ^ (1 / 250 : ℝ))⁻¹ := by
          exact Real.rpow_neg hN8.le (1 / 250 : ℝ)
        _ = (((log N) ^ (1 / 500 : ℝ)) ^ 2)⁻¹ := by
          congr 1
          calc
            (log N) ^ (1 / 250 : ℝ) = (log N) ^ ((1 / 500 : ℝ) + 1 / 500) := by
              congr 2
              norm_num
            _ = ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
              rw [pow_two, ← Real.rpow_add hN8]

private lemma large_enough_N_hT2
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ)) :
    2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
  have hpow_nonneg : 0 ≤ (log N) ^ (-(1 / 100 : ℝ)) := by positivity
  have hstep :
      2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        (log N) ^ (1 / 200 : ℝ) * (log N) ^ (-(1 / 100 : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hN11 hpow_nonneg
  refine hstep.trans ?_
  rw [← Real.rpow_add hN8]
  norm_num

private lemma large_enough_N_hT3
    (N : ℕ)
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    (N : ℝ) ^ (-(5 : ℝ) / log (log N)) ≤ (log N) ^ (-(1 / 100 : ℝ)) := by
  have hlog_ge_one : (1 : ℝ) ≤ log N := by
    refine le_trans ?_ hN2
    apply one_le_rpow
    · norm_num
    · norm_num
  have hsq :
      log (log N) ^ (2 : ℕ) ≤ 500 * log N := by
    calc
      log (log N) ^ (2 : ℕ) ≤ (((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) ^ (2 : ℕ)) := by
        nlinarith [hN10]
      _ = (4 / 9 : ℝ) * ((log N) ^ (3 / 500 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by ring
      _ = (4 / 9 : ℝ) * (log N) ^ ((3 / 500 : ℝ) + 3 / 500) := by
        rw [← Real.rpow_add hN8]
      _ = (4 / 9 : ℝ) * (log N) ^ (3 / 250 : ℝ) := by congr 2; norm_num
      _ ≤ (4 / 9 : ℝ) * log N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hexp : (3 / 250 : ℝ) ≤ 1 := by norm_num
        simpa using Real.rpow_le_rpow_of_exponent_le hlog_ge_one hexp
      _ ≤ 500 * log N := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (4 / 9 : ℝ) ≤ 500) (le_of_lt hN8)
  have hlogineq : (1 / 100 : ℝ) * log (log N) ≤ 5 * log N / log (log N) := by
    rw [le_div_iff₀ hN7]
    nlinarith [hsq]
  rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (-(5 : ℝ) / log (log N)) by positivity)
    (show 0 < (log N) ^ (-(1 / 100 : ℝ)) by positivity)]
  rw [Real.log_rpow hN6, Real.log_rpow hN8]
  have hlogineq' : (1 / 100 : ℝ) * log (log N) ≤ (5 / log (log N)) * log N := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlogineq
  have hneg :
      -((5 / log (log N)) * log N) ≤ -((1 / 100 : ℝ) * log (log N)) := by
    linarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hneg

private lemma large_enough_N_hMε
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (N : ℝ) ^ (-(5 : ℝ) / log (log N)) * log (log N) := by
  have hN4 : 1 < log (log N) := by
    linarith
  have hexp_nonneg : 0 ≤ (1 : ℝ) - (6 : ℝ) / log (log N) := by
    rw [sub_nonneg, div_le_one hN7]
    simpa using hN1
  have hpow_ge_one : 1 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    refine one_le_rpow (le_of_lt hN5) hexp_nonneg
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    positivity
  have hmain : 1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    nlinarith
  have hexp :
      (-(5 : ℝ) / log (log N)) + (1 - (1 : ℝ) / log (log N)) =
        (1 : ℝ) - (6 : ℝ) / log (log N) := by
    ring
  rw [one_div, inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  rw [mul_assoc]
  rw [mul_left_comm ((N : ℝ) ^ (-(5 : ℝ) / log (log N))) (log (log N))
    ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)))]
  rw [← mul_assoc]
  calc
    1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := hmain
    _ = log (log N) *
          ((N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) := by
          rw [← Real.rpow_add hN6, hexp]
    _ = log (log N) * (N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          rw [mul_assoc]

private lemma large_enough_N_hKlower
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN3 : 64 ≤ N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    8 ≤ (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) := by
  have _ : 0 < log N := hN8
  have hhalf : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_le_rpow_iff (show 0 ≤ (8 : ℝ) by norm_num)
      (Real.rpow_nonneg (le_of_lt hN6) ((1 : ℝ) / 2)) (show (0 : ℝ) < 2 by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hN6)]
    norm_num
    exact_mod_cast hN3
  have hexp : (1 : ℝ) / 2 ≤ 1 - (3 : ℝ) / log (log N) := by
    have hdiv : (3 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hN7]
      nlinarith
    nlinarith
  exact hhalf.trans <| Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp

private lemma large_enough_N_hKM
    (N : ℕ)
    (hN5 : (1 : ℝ) < N)
    (hN7 : 0 < log (log N)) :
    (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  apply Real.rpow_lt_rpow_of_exponent_lt hN5
  have hdiv : (1 : ℝ) / log (log N) < (3 : ℝ) / log (log N) := by
    rw [div_lt_div_iff₀ hN7 hN7]
    nlinarith
  nlinarith

private lemma large_enough_N_hsum
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ))
    (hT : 4 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) :
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
  have hquarter_pos : 0 < 4 * (log N) ^ (1 / 500 : ℝ) := by positivity
  have hfirst :
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    rw [_root_.le_div_iff₀ hquarter_pos]
    calc
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) *
          (4 * (log N) ^ (1 / 500 : ℝ)) =
        24 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (1 / 500 : ℝ)) * log (log N) := by
          ring
      _ = 24 * (log N) ^ ((-(1 / 100 : ℝ)) + 1 / 500) * log (log N) := by
        rw [← Real.rpow_add hN8]
      _ = 24 * (log N) ^ (-(1 / 125 : ℝ)) * log (log N) := by
        congr 2
        norm_num
      _ = (24 * log (log N)) / (log N) ^ (1 / 125 : ℝ) := by
        rw [div_eq_mul_inv, Real.rpow_neg hN8.le]
        ring
      _ ≤ 1 := by
        rw [div_le_iff₀ (show 0 < (log N) ^ (1 / 125 : ℝ) by positivity)]
        simpa [one_mul] using hN9
  have hsecond :
      1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    exact one_div_le_one_div_of_le hquarter_pos hT.le
  calc
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (4 * (log N) ^ (1 / 500 : ℝ)) + 1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
        exact add_le_add hfirst hsecond
    _ = 1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
      have hPne : (log N) ^ (1 / 500 : ℝ) ≠ 0 := by positivity
      field_simp [hPne]
      norm_num

private lemma large_enough_N_honeOverM
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN8 : 0 < log N)
    (_hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (log N) ^ (-(1 / 100 : ℝ)) * log (log N) := by
  have hN6 : 0 < (N : ℝ) := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN4 : 1 < log (log N) := by
    linarith
  have hTq :
      (log N) ^ (1 / 100 : ℝ) <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
    have h100 : (0 : ℝ) < 100 := by
      norm_num
    refine (Real.rpow_lt_rpow_iff
      (show 0 ≤ (log N) ^ (1 / 100 : ℝ) by positivity)
      (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h100).1 ?_
    rw [← Real.rpow_mul hN8.le]
    norm_num
    refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
    refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
    have hdiv : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 6 := by
      have h6 : (0 : ℝ) < 6 := by
        norm_num
      exact one_div_le_one_div_of_le h6 hN1
    have hbound : (log (log N))⁻¹ ≤ (99 : ℝ) / 100 := by
      have haux : (1 : ℝ) / 6 ≤ (99 : ℝ) / 100 := by
        norm_num
      have hdiv' : (log (log N))⁻¹ ≤ (1 : ℝ) / 6 := by
        simpa [one_div] using hdiv
      exact hdiv'.trans haux
    have hexp : (1 : ℝ) ≤ (1 - (log (log N))⁻¹) * (100 : ℝ) := by
      nlinarith
    have hpow :
        (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
      have hpow' :
          (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      simpa using hpow'
    exact le_trans hpow <| by
      apply le_of_eq
      symm
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      congr 2
  have hratio :
      1 <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ) := by
    exact (one_lt_div_iff).2 <| Or.inl ⟨show 0 < (log N) ^ (1 / 100 : ℝ) by positivity, hTq⟩
  rw [Real.rpow_neg hN8.le, one_div]
  rw [inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  calc
    1 <
        log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ)) :=
      one_lt_mul_of_lt_of_le hN4 hratio.le
    _ = log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) *
            ((log N) ^ (1 / 100 : ℝ))⁻¹) := by
          rw [div_eq_mul_inv]
    _ = ((log N) ^ (1 / 100 : ℝ))⁻¹ * log (log N) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          ac_rfl

lemma large_enough_N :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
        (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ (log N) ^ (1 / 500 : ℝ) < 2 * M ∧
        2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        3 * ε * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * (log N) ^ (1 / 500 : ℝ)) ∧
        (log N) ^ (1 / 500 : ℝ) ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
        3 * ε' * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux := large_enough_Naux c hc
  have haux4 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 24 : ℝ) * ‖x ^ (1 / 125 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 125 : ℝ) by norm_num)).bound
      (show 0 < (1 / 24 : ℝ) by norm_num)
  have haux5 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (2 / 3 : ℝ) * ‖x ^ (3 / 500 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (3 / 500 : ℝ) by norm_num)).bound
      (show 0 < (2 / 3 : ℝ) by norm_num)
  have haux6 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 2 : ℝ) * ‖x ^ (1 / 200 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((192 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , tendsto_log_coe_at_top.eventually haux4
    , tendsto_log_coe_at_top.eventually haux5
    , tendsto_log_coe_at_top.eventually haux6
    , hlargeaux ] with
    N hN1 hN2 hN3 hN3new hN3new2 hN3new3 hotheraux
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (192 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  have hbound1 :
      log (log N) ≤ (1 / 24 : ℝ) * (log N) ^ (1 / 125 : ℝ) := by
    have habs :
        log (log N) ≤ (1 / 24 : ℝ) * |(log N) ^ (1 / 125 : ℝ)| := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new
    rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 125 : ℝ) by positivity)] at habs
    exact habs
  have hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ) := by
    nlinarith
  have hN10 :
      log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le,
      abs_of_nonneg (show 0 ≤ (log N) ^ (3 / 500 : ℝ) by positivity)] using hN3new2
  have hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ) := by
    have hbound3 :
        log (log N) ≤ (1 / 2 : ℝ) * (log N) ^ (1 / 200 : ℝ) := by
      have habs :
          log (log N) ≤ (1 / 2 : ℝ) * |(log N) ^ (1 / 200 : ℝ)| := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new3
      rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 200 : ℝ) by positivity)] at habs
      exact habs
    nlinarith
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ (1 / 100 : ℝ))
  let T : ℝ := M / log N
  let ε : ℝ := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let P : ℝ := (log N) ^ (1 / 500 : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε'pos : 0 < ε' := by
    dsimp [ε']
    positivity
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hotheraux' :
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M := by
    simpa [M, L, T, ε, ε', K, P] using hotheraux
  have hTp : 192 * P < M := by
    simpa [M, P] using large_enough_N_hTp N hN1 hN2 hN5 hN6 hN7 hN8
  have hT : 4 * P < M := by
    have hstep : 4 * P ≤ 192 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hTp
  have hT' : P < M := by
    have hstep : P ≤ 4 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hT
  have hT1 : 3 * ε' * log (log N) ≤ 2 / P ^ 2 := by
    simpa [ε', P] using large_enough_N_hT1 N hN8 hN10
  have hT2 : 2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
    simpa [ε'] using large_enough_N_hT2 N hN8 hN11
  have hT3 : ε ≤ ε' := by
    simpa [ε, ε'] using large_enough_N_hT3 N hN2 hN6 hN7 hN8 hN10
  have hKlower : 8 ≤ K := by
    simpa [K] using large_enough_N_hKlower N hN1 hN3 hN5 hN6 hN7 hN8
  have hsum :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) := by
    simpa [M, ε', P] using large_enough_N_hsum N hN8 hN9 (by simpa [M, P] using hT)
  have honeOverM : 1 / M < ε' * log (log N) := by
    simpa [M, ε'] using large_enough_N_honeOverM N hN1 hN5 hN8 hN9
  change
    1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
      (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ P < 2 * M ∧
      2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      3 * ε * log (log N) ≤ 2 / P ^ 2 ∧
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) ∧
      P ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
      3 * ε' * log (log N) ≤ 2 / P ^ 2 ∧
      2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
      (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M
  constructor
  · simpa [M, ε] using large_enough_N_hMε N hN1 hN5 hN6 hN7
  constructor
  · exact hεpos
  constructor
  · have hrec : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      exact
        one_div_le_one_div_of_le
          (by norm_num : 0 < (2 : ℝ))
          (by linarith : (2 : ℝ) ≤ log (log N))
    have hexp : (1 : ℝ) ≤ (1 - (1 : ℝ) / log (log N)) * (2 : ℝ) := by
      nlinarith
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (N : ℝ) ^ ((1 - (1 : ℝ) / log (log N)) * (2 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      _ = M ^ (2 : ℝ) := by
        dsimp [M]
        rw [← Real.rpow_mul (le_of_lt hN6)]
  constructor
  · calc
      M = (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by rfl
      _ < (N : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN5
        have hdivpos : 0 < (1 : ℝ) / log (log N) := by positivity
        nlinarith
      _ = N := by rw [Real.rpow_one]
  constructor
  · exact hMpos
  constructor
  · exact hN8
  constructor
  · exact hKlower
  constructor
  · simpa [M, K] using large_enough_N_hKM N hN5 hN7
  constructor
  · have hstep : M ≤ 2 * M := by
      nlinarith [hMpos]
    exact lt_of_lt_of_le hT' hstep
  constructor
  · have hmul1 : 2 * ε ≤ 2 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (2 : ℝ) by norm_num)
    have hmul2 : (2 * ε) * log (log N) ≤ (2 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT2
    simpa [mul_assoc] using hmul2
  constructor
  · have hmul1 : 3 * ε ≤ 3 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (3 : ℝ) by norm_num)
    have hmul2 : (3 * ε) * log (log N) ≤ (3 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT1
    simpa [mul_assoc] using hmul2
  constructor
  · exact hsum
  constructor
  · exact le_of_lt <| (_root_.lt_div_iff₀ (show 0 < (192 : ℝ) by norm_num)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hTp
  constructor
  · exact honeOverM
  constructor
  · exact hT1
  constructor
  · exact hT2
  · exact hotheraux' hT3

private lemma technical_prop_hdiv_aux
    (y z : ℝ) (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∣ n)
    (hyd₁ : y ≤ d₁)
    (hd₁₂ : 4 * d₁ ≤ d₂)
    (hd₂z : (d₂ : ℝ) ≤ z) :
    ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
  refine ⟨d₁, hyd₁, ?_, hd₁⟩
  have hd₁₂' : (4 : ℝ) * d₁ ≤ d₂ := by
    exact_mod_cast hd₁₂
  nlinarith

private lemma technical_prop_hrecB
    (N : ℕ) (M ε' y z : ℝ) (A' B : Finset ℕ) (d : ℕ)
    (h1y : 1 ≤ y)
    (hz_pos : 0 < z)
    (hzN : z ≤ (log N) ^ (1 / 500 : ℝ))
    (hε'M :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * ((log N) ^ (1 / 500 : ℝ))))
    (hrecB : rec_sum A' ≤ 3 * rec_sum B)
    (hdy : y ≤ d)
    (hdz : (d : ℝ) ≤ z / 4)
    (htechrec : (2 : ℝ) / d - 1 / M ≤ rec_sum A') :
    2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
  have hd_pos : 0 < (d : ℝ) := by
    linarith
  have hdz' : (d : ℝ) ≤ z := by
    nlinarith [hdz, hz_pos]
  have hsmall : 3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * d) := by
    calc
      3 * (2 * ε' * log (log N)) + 1 / M ≤
          1 / (2 * ((log N) ^ (1 / 500 : ℝ))) := hε'M
      _ ≤ 1 / (2 * z) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith [hzN]
      _ ≤ 1 / (2 * d) := by
        apply one_div_le_one_div_of_le
        · nlinarith [hd_pos]
        · nlinarith [hdz']
  have hhalfEq : (1 / (2 * d) : ℝ) = ((1 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
  have hadd :
      (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) = (2 : ℝ) / d := by
    field_simp [hd_pos.ne']
    ring
  have hsmall' :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ ((1 / 2 : ℝ) / d) := by
    rw [← hhalfEq]
    exact hsmall
  have hbound :
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤ (2 : ℝ) / d := by
    calc
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤
          (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hsmall' ((3 / 2 : ℝ) / d)
      _ = (2 : ℝ) / d := hadd
  have hpre :
      (3 / 2 : ℝ) / d + 3 * (2 * ε' * log (log N)) ≤ rec_sum A' := by
    linarith
  have haux : (3 : ℝ) * (2 / ((4 : ℝ) * d)) = ((3 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
    ring
  have hrecB' : (rec_sum A' : ℝ) ≤ 3 * (rec_sum B : ℝ) := by
    exact_mod_cast hrecB
  have hmulA : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ rec_sum A' := by
    rw [mul_add, haux]
    exact hpre
  have hmulB : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ 3 * rec_sum B := by
    exact le_trans hmulA hrecB'
  exact le_of_mul_le_mul_left hmulB (show 0 < (3 : ℝ) by norm_num)

set_option maxHeartbeats 0 in
-- The translated Lean 4 proof is long enough that it needs more heartbeats to elaborate.
theorem technical_prop :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ y z : ℝ,
      1 ≤ y → 4 * y + 4 ≤ z → z ≤ (log N) ^ (1 / 500 : ℝ) → 0 ∉ A →
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) →
      2 / y + (log N) ^ (-(1 / 200 : ℝ)) ≤ rec_sum A →
      (∀ n ∈ A, ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
  obtain ⟨c, hc, circle_method⟩ := circle_method_prop2
  obtain hlargeN := large_enough_N
  specialize hlargeN c hc
  filter_upwards
    [ main_tech_lemma
    , force_good_properties
    , force_good_properties2
    , circle_method
    , hlargeN ] with
    N htechlemma hforce1 hforce2 hcircle hlargeN
  clear circle_method
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ ((1 : ℝ) / 100))
  let T : ℝ := M / log N
  rcases hlargeN with
    ⟨hMε, hε, hM3, hM2, hM1, hlogN3, heK, hKM, hlogN4, hlogN5, hlogN6, hlargeNnew,
      hlargenew2, hε'M, hlarge3, hlarge4, hεε'M, hUhelper, hUhelper2, hUhelper3, hlarge7⟩
  have hNMcast : (N : ℝ) ≤ M ^ 2 := by
    rw [← Real.rpow_natCast]
    exact hM3
  have hM2aux : M ≤ N := by
    exact le_of_lt hM2
  intro A hA y z h1y hyz hzN h0A hA2 hrec hdiv hsmooth hreg
  have htemp6 :
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) = K := by
    have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hM1 hM2aux
    rw [← Real.rpow_add hNpos]
    have hEq :
        1 - (1 : ℝ) / log (log N) + (-(2 : ℝ) / log (log N)) =
          1 - (3 : ℝ) / log (log N) := by
      ring_nf
    rw [hEq]
  have hzT : 0 < T := by
    exact div_pos hM1 hlogN3
  have hzL : 0 < L := by
    apply div_pos hM1
    apply mul_pos
    · exact zero_lt_two
    · exact Real.rpow_pos_of_pos hlogN3 _
  have hyzaux : y ≤ z := by
    apply le_trans (b := 4 * y)
    · exact le_mul_of_one_le_left (le_trans zero_le_one h1y) (by norm_num : (1 : ℝ) ≤ 4)
    · apply le_trans (b := 4 * y + 4)
      · exact le_add_of_nonneg_right (show 0 ≤ (4 : ℝ) by norm_num)
      · exact hyz
  have hz_pos : 0 < z := by
    exact lt_of_lt_of_le zero_lt_one (le_trans h1y hyzaux)
  have hwM : z / 4 < 2 * M := by
    apply lt_of_lt_of_le (b := z)
    · rw [div_lt_iff₀ zero_lt_four]
      exact lt_mul_of_one_lt_right hz_pos one_lt_four
    · exact le_trans hzN (le_of_lt hlogN4)
  have h8z : 8 ≤ z := by
    apply le_trans (b := 4 * y + 4)
    · have h4y : 4 ≤ 4 * y := by
        exact le_mul_of_one_le_right (show 0 ≤ (4 : ℝ) by norm_num) h1y
      linarith
    · exact hyz
  have h2z : 2 ≤ z / 4 := by
    rw [le_div_iff₀ zero_lt_four]
    norm_num1
    exact h8z
  have hyz' : ⌈y⌉₊ ≤ ⌊z / 4⌋₊ := by
    rw [Nat.ceil_le]
    apply le_trans (b := z / 4 - 1)
    · apply le_sub_right_of_add_le
      rw [le_div_iff₀ zero_lt_four, add_mul, one_mul, mul_comm]
      exact hyz
    · rw [sub_le_iff_le_add]
      refine le_trans le_rfl ?_
      have hfloor : z / 4 < (⌊z / 4⌋₊ : ℝ) + 1 := by
        exact Nat.lt_floor_add_one (z / 4)
      exact le_of_lt hfloor
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  have h0ε' : 0 < ε' := by
    exact Real.rpow_pos_of_pos hlogN3 _
  have hε'w2 : 3 * ε' * log (log N) ≤ 2 / (z ^ 2) := by
    have hsq : z ^ 2 ≤ ((log N) ^ ((1 / 500 : ℝ))) ^ 2 := by
      nlinarith [hzN, hz_pos, show 0 ≤ (log N) ^ ((1 / 500 : ℝ)) by positivity]
    have hInv : 1 / (((log N) ^ ((1 / 500 : ℝ))) ^ 2) ≤ 1 / (z ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hz_pos) hsq
    refine hlarge3.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hε'z : 3 * ε' * log (log N) ≤ 2 / ((z / 4) ^ 2) := by
    have hεzaux : (z / 4) ^ 2 ≤ z ^ 2 := by
      nlinarith [hz_pos]
    have hInv : 1 / (z ^ 2) ≤ 1 / ((z / 4) ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hz_pos zero_lt_four)) hεzaux
    refine hε'w2.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hrec' : 2 / y + 2 * ε' * log (log N) ≤ rec_sum A := by
    apply le_trans ?_ hrec
    exact add_le_add le_rfl hlarge4
  have hsmooth' : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε' * M := by
    intro q hq
    rw [ppowers_in_set, Finset.mem_biUnion] at hq
    rcases hq with ⟨a, ha, hq⟩
    rw [Finset.mem_filter] at hq
    simp_rw [is_smooth] at hsmooth
    specialize hsmooth a ha q hq.2.1
    apply le_trans _ hεε'M
    exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
  have hdiv' : ∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
    intro n hn
    specialize hdiv n hn
    rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
    exact technical_prop_hdiv_aux y z n d₁ d₂ hd₁ hyd₁ hd₁₂ hd₂z
  have htech2 := htechlemma
  specialize htechlemma M ε' y (z / 4) A hA hM1 hM2 h0ε' hwM hε'M h1y h2z hyz' hε'z hA2 hrec'
    hsmooth' hdiv'
  rcases htechlemma with ⟨A', hA', d, htech⟩
  have hzd : d ≠ 0 := by
    have hd1 : 1 ≤ d := by
      exact_mod_cast le_trans h1y htech.2.1
    exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
  by_cases
    hgoodsubset :
      ∃ B ⊆ A',
        rec_sum A' ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)
  · clear hforce1
    rcases hgoodsubset with ⟨B, hB, hrecB, hppB⟩
    have hB2 : B ⊆ Finset.range (N + 1) := by
      exact (hB.trans hA').trans hA
    have hzM : z < 2 * M := by
      exact lt_of_le_of_lt hzN hlogN4
    have h14d : 1 ≤ (4 : ℝ) * d := by
      have hd1 : (1 : ℝ) ≤ d := by
        exact le_trans h1y htech.2.1
      nlinarith
    have h2z' : 2 ≤ z := by
      exact le_trans (by norm_num1 : (2 : ℝ) ≤ 8) h8z
    have hdz : ⌈(4 : ℝ) * d⌉₊ ≤ ⌊z⌋₊ := by
      have h4dz : (4 : ℝ) * d ≤ z := by
        nlinarith [htech.2.2.1]
      have h4dz_nat : 4 * d ≤ ⌊z⌋₊ := by
        exact (Nat.le_floor_iff (le_of_lt hz_pos)).mpr <| by
          simpa [Nat.cast_mul] using h4dz
      rw [show ((4 : ℝ) * d) = ((4 * d : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
      exact h4dz_nat
    have hB3 : ∀ n : ℕ, n ∈ B → M ≤ n := by
      intro n hn
      exact hA2 n ((hB.trans hA') hn)
    have hrecB' : 2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
      exact technical_prop_hrecB N M ε' y z A' B d h1y hz_pos hzN hlargeNnew hrecB htech.2.1
        htech.2.2.1 htech.2.2.2.2.1
    have hsmoothB : ∀ q ∈ ppowers_in_set B, (q : ℝ) ≤ ε' * M := by
      intro q hq
      exact hsmooth' q ((ppowers_in_set_subset ((hB.trans hA')) hq))
    have hdivB :
        ∀ n : ℕ, n ∈ B → ∃ d₁ : ℕ, (4 : ℝ) * d ≤ d₁ ∧ (d₁ : ℝ) ≤ z ∧ d₁ ∣ n := by
      intro n hn
      specialize hdiv n ((hB.trans hA') hn)
      rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
      have hdle : d ≤ d₁ := by
        obtain htech' := htech.2.2.2.2.2.2.2
        specialize htech' n (hB hn) d₁ hd₁
        apply le_of_not_gt
        intro hfoo
        specialize htech' hfoo
        exact (not_le.mpr htech') hyd₁
      refine ⟨d₂, ?_, hd₂z, hd₂⟩
      norm_cast
      apply le_trans (b := 4 * d₁)
      · have hdle' : (d : ℝ) ≤ d₁ := by
          exact_mod_cast hdle
        nlinarith
      · exact hd₁₂
    specialize htech2 M ε' ((4 : ℝ) * d) z B hB2 hM1 hM2 h0ε' hzM hε'M h14d h2z' hdz hε'w2 hB3
      hrecB' hsmoothB hdivB
    rcases htech2 with ⟨B', hB', d', htech2⟩
    have hB'2 : B' ⊆ Finset.range (N + 1) := by
      exact hB'.trans hB2
    have hB'reg : arith_regular N B' := by
      exact hreg.subset (hB'.trans (hB.trans hA'))
    have hB'3 : ∀ q ∈ ppowers_in_set B', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local B' q := by
      obtain htech2' := htech2.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech2' q hq)
    have hB'4 : (ppower_rec_sum B' : ℝ) ≤ (2 / 3) * log (log N) := by
      apply le_trans _ hppB
      norm_cast
      exact ppower_rec_sum_mono hB'
    have hB'5 : ∀ n : ℕ, n ∈ B' → M ≤ n := by
      intro n hn
      exact hA2 n ((hA' <| hB <| hB' hn))
    have hB'n0 : 0 ∉ B' := by
      intro hz
      exact h0A (hA' (hB (hB' hz)))
    specialize hforce2 M B' hB'2 hM1 (le_of_lt hM2) hNMcast hB'n0 hB'5 hB'reg hB'3 hB'4
    have hzd' : d' ≠ 0 := by
      have hd1 : 1 ≤ d' := by
        exact_mod_cast le_trans h14d htech2.2.1
      exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
    have hd'M : (d' : ℝ) ≤ M / 192 := by
      exact le_trans htech2.2.2.1 (le_trans hzN hlargenew2)
    have hB'6 : ∀ n : ℕ, n ∈ B' → n ≤ N := by
      intro n hn
      rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
      exact hB'2 hn
    have hdB' : d' ∣ B'.lcm id := by
      rcases htech2.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
      exact dvd_trans hnew (Finset.dvd_lcm hn)
    let U' :=
      min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d') (T * K ^ 2 / (N ^ 2 * log N)))
    have hU'M : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U' := by
      rw [le_min_iff]
      constructor
      · exact hUhelper
      · rw [le_min_iff]
        constructor
        · apply le_trans (b := c * M / z)
          · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
            · exact hUhelper3
            · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                exact one_div_le_one_div_of_le hz_pos hzN
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · have hd'pos : 0 < (d' : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero hzd'
            have hInv : 1 / z ≤ 1 / d' := by
              exact one_div_le_one_div_of_le hd'pos htech2.2.2.1
            simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
              (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
        · exact hUhelper2
    have hppB' : ∀ q : ℕ, q ∈ ppowers_in_set B' → (q : ℝ) ≤ U' := by
      intro q hq
      rw [ppowers_in_set, Finset.mem_biUnion] at hq
      rcases hq with ⟨a, ha, hq⟩
      rw [Finset.mem_filter] at hq
      simp_rw [is_smooth] at hsmooth
      specialize hsmooth a (hA' (hB (hB' ha))) q hq.2.1
      apply le_trans _ hU'M
      exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
    have hgoodB' : good_condition B' K T L := by
      rw [htemp6] at hforce2
      exact hforce2
    specialize
      @hcircle K L M T d' B' hzT hzL heK hKM hM2aux hzd' hd'M hB'5 hB'6 htech2.2.2.2.1
        htech2.2.2.2.2.1 hdB' hppB' hgoodB'
    rcases hcircle with ⟨S, hS, hcirc⟩
    refine ⟨S, hS.trans (hB'.trans (hB.trans hA')), d', ?_, htech2.2.2.1, hcirc⟩
    apply le_trans htech.2.1
    apply le_trans (b := (4 : ℝ) * d)
    · exact le_mul_of_one_le_left (Nat.cast_nonneg d) (by norm_num : (1 : ℝ) ≤ 4)
    · exact htech2.2.1
  · clear hforce2 htech2
    have hrangeA' : A' ⊆ Finset.range (N + 1) := by
      exact hA'.trans hA
    have hregA' : arith_regular N A' := by
      exact hreg.subset hA'
    have hNA' : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A' := by
      have hdP : (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) / 4 := by
        nlinarith [htech.2.2.1, hzN]
      have htwoDiv : (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 2 / d := by
        have hdpos : 0 < (d : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hzd
        have hInv : 1 / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 1 / d := by
          exact one_div_le_one_div_of_le hdpos hdP
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
      exact hlarge7.trans <| (sub_le_sub_right htwoDiv _).trans htech.2.2.2.2.1
    have hppA' : ∀ q ∈ ppowers_in_set A', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A' q := by
      obtain htech' := htech.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech' q hq)
    have hA'5 : ∀ n : ℕ, n ∈ A' → M ≤ n := by
      intro n hn
      exact hA2 n (hA' hn)
    have hA'n0 : 0 ∉ A' := by
      intro hz
      exact h0A (hA' hz)
    specialize hforce1 M A' hrangeA' hM1 (le_of_lt hM2) hNMcast hA'n0 hA'5 hregA' hNA' hppA'
    rcases hforce1 with htemp1 | htemp2
    · exfalso
      exact hgoodsubset htemp1
    · have hgoodA' : good_condition A' K T L := by
        rw [htemp6] at htemp2
        exact htemp2
      have hdM : (d : ℝ) ≤ M / 192 := by
        apply le_trans htech.2.2.1
        apply le_trans (b := z / 4)
        · exact le_rfl
        · apply le_trans ?_ (le_trans hzN hlargenew2)
          exact div_le_self (le_of_lt hz_pos) (by norm_num : (1 : ℝ) ≤ 4)
      have hA'6 : ∀ n : ℕ, n ∈ A' → n ≤ N := by
        intro n hn
        rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
        exact hrangeA' hn
      have hdA' : d ∣ A'.lcm id := by
        rcases htech.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
        exact dvd_trans hnew (Finset.dvd_lcm hn)
      let U :=
        min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d) (T * K ^ 2 / (N ^ 2 * log N)))
      have hUM : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U := by
        rw [le_min_iff]
        constructor
        · exact hUhelper
        · rw [le_min_iff]
          constructor
          · apply le_trans (b := c * M / z)
            · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
              · exact hUhelper3
              · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                  exact one_div_le_one_div_of_le hz_pos hzN
                simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                  (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
            · have hdpos : 0 < (d : ℝ) := by
                exact_mod_cast Nat.pos_of_ne_zero hzd
              have hdz' : (d : ℝ) ≤ z := by
                have : (d : ℝ) ≤ z / 4 := htech.2.2.1
                nlinarith
              have hInv : 1 / z ≤ 1 / d := by
                exact one_div_le_one_div_of_le hdpos hdz'
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · exact hUhelper2
      have hppA' : ∀ q : ℕ, q ∈ ppowers_in_set A' → (q : ℝ) ≤ U := by
        intro q hq
        rw [ppowers_in_set, Finset.mem_biUnion] at hq
        rcases hq with ⟨a, ha, hq⟩
        rw [Finset.mem_filter] at hq
        simp_rw [is_smooth] at hsmooth
        specialize hsmooth a (hA' ha) q hq.2.1
        apply le_trans _ hUM
        exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
      specialize
        @hcircle K L M T d A' hzT hzL heK hKM hM2aux hzd hdM hA'5 hA'6 htech.2.2.2.1
          htech.2.2.2.2.1 hdA' hppA' hgoodA'
      rcases hcircle with ⟨S, hS, hcirc⟩
      refine ⟨S, hS.trans hA', d, htech.2.1, ?_, hcirc⟩
      apply le_trans htech.2.2.1
      apply div_le_self
      · exact le_trans zero_le_one (le_trans h1y hyzaux)
      · norm_num

lemma prop_one_specialise :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1),
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) → 0 ∉ A →
      (log N) ^ (1 / 500 : ℝ) ≤ (rec_sum A : ℝ) →
      (∀ n ∈ A, ∃ d₂ : ℕ, d₂ ∣ n ∧ 4 ≤ d₂ ∧ (d₂ : ℝ) ≤ (log N) ^ (1 / 500 : ℝ)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) ∧ rec_sum S = 1 / d := by
  have hf : Tendsto (fun x : ℕ => log x ^ (1 / 500 : ℝ)) atTop atTop :=
    tendsto_coe_log_pow_at_top _ (by norm_num1)
  have hf' : Tendsto (fun x : ℕ => log x ^ (1 / 200 : ℝ)) atTop atTop :=
    tendsto_coe_log_pow_at_top _ (by norm_num1)
  filter_upwards
    [ technical_prop
    , hf.eventually (eventually_ge_atTop (8 : ℝ))
    , hf'.eventually (eventually_ge_atTop (1 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (0 : ℝ)) ] with
    N hN hN' hN'' hN''' A A_upper_bound A_lower_bound h0A hA₁ hA₂ hA₃ hA₄
  dsimp at hN' hN'' hN'''
  obtain ⟨S, hS, d, hd1, hd2, hrec⟩ :=
    hN A A_upper_bound 1 ((log N) ^ (1 / 500 : ℝ)) le_rfl
      (show 4 * (1 : ℝ) + 4 ≤ (log N) ^ (1 / 500 : ℝ) by
        exact le_trans (by norm_num1) hN')
      le_rfl h0A A_lower_bound
      (show 2 / (1 : ℝ) + (log N) ^ (-(1 / 200 : ℝ)) ≤ rec_sum A by
        apply (le_trans _ hN').trans hA₁
        rw [← le_sub_iff_add_le', Real.rpow_neg]
        · norm_num1
          have hpow_inv :
              ((log N) ^ (1 / 200 : ℝ))⁻¹ ≤ 1 := by
            simpa [one_div] using
              (one_div_le_one_div_of_le (show 0 < (1 : ℝ) by norm_num) hN'')
          exact le_trans hpow_inv (by norm_num1)
        · exact hN''')
      (by
        intro n hn
        obtain ⟨d₂, hd₂, hd₂', hd₂''⟩ := hA₂ n hn
        exact ⟨1, d₂, one_dvd _, hd₂, by simp, by simpa, hd₂''⟩)
      hA₃ hA₄
  refine ⟨S, hS, d, ?_, hd2, hrec⟩
  exact_mod_cast hd1

theorem corollary_one :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1),
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) →
      2 * (log N) ^ (1 / 500 : ℝ) ≤ rec_sum A →
      (∀ n ∈ A, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ (log N) ^ (1 / 500 : ℝ)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  classical
  filter_upwards [prop_one_specialise, eventually_ge_atTop (1 : ℕ)] with
    N p1 hN₁ A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄
  let good_set : Finset (Finset ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ⊆ A) ∧ (S : Set (Finset ℕ)).PairwiseDisjoint id ∧
      ∀ s, ∃ d : ℕ, s ∈ S → 1 ≤ d ∧ (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) ∧ rec_sum s = 1 / d
  let P : ℕ → Prop := fun k => ∃ S : Finset (Finset ℕ), S.card = k ∧ good_set S
  let k : ℕ := Nat.findGreatest P (A.card + 1)
  have P0 : P 0 := by
    refine ⟨∅, ?_⟩
    simp [good_set]
  have Pk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk
  choose d' hd'₁ hd'₂ hd'₃ using hS₃
  let t : ℕ → ℕ := fun d => (S.filter fun s => d' s = d).card
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d
  · obtain ⟨d, d_pos, ht⟩ := h
    obtain ⟨T', hT', hd₂⟩ :=
      Finset.exists_subset_card_eq (s := S.filter fun s => d' s = d) ht
    have hT'S : T' ⊆ S := hT'.trans (Finset.filter_subset _ _)
    refine ⟨T'.biUnion id, ?_, ?_⟩
    · refine (Finset.biUnion_subset_biUnion_of_subset_left _ hT'S).trans ?_
      rwa [Finset.biUnion_subset]
    · rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S)]
      have hsumT : T'.sum rec_sum = T'.sum (fun _ : Finset ℕ => (1 : ℚ) / d) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [(Finset.mem_filter.mp (hT' hi)).2] using (hd'₃ i (hT'S hi))
      rw [hsumT, Finset.sum_const, hd₂, nsmul_eq_mul]
      field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast d_pos.ne']
  · exfalso
    have hcount : ∀ d : ℕ, 0 < d → t d < d := by
      intro d hd
      by_contra hdt
      exact h ⟨d, hd, le_of_not_gt hdt⟩
    let A' := A \ S.biUnion id
    have hS : ((S.sum rec_sum : ℚ) : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) := by
      have hmaps : ∀ s ∈ S, d' s ∈ Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊ := by
        intro s hs
        simp only [Finset.mem_Icc, hd'₁ s hs, Nat.le_floor (hd'₂ s hs), and_self]
      have hS1 :
          ((S.sum rec_sum : ℚ) : ℝ) ≤
            (Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊).sum (fun d => (t d : ℝ) / d) := by
        rw [Rat.cast_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_le_sum ?_
        intro d hd
        rw [div_eq_mul_one_div, ← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ ?_
        intro s hs
        rcases Finset.mem_filter.mp hs with ⟨hsS, hsEq⟩
        have hrec_cast : (rec_sum s : ℝ) = (1 : ℝ) / d := by
          have hcast := congrArg (fun x : ℚ => (x : ℝ)) (hd'₃ s hsS)
          simpa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, hsEq] using hcast
        simpa [one_div] using hrec_cast.le
      have hS2 :
          (Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊).sum (fun d => (t d : ℝ) / d) ≤
            (log N) ^ (1 / 500 : ℝ) := by
        refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
        · simp only [one_div, Finset.mem_Icc, and_imp]
          intro d hd₁ _hd₂
          exact div_le_one_of_le₀ (Nat.cast_le.mpr (hcount d hd₁).le) (Nat.cast_nonneg _)
        · simpa [Nat.card_Icc, nsmul_eq_mul] using
            (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN₁)) _))
      exact le_trans hS1 hS2
    have hAS : Disjoint A' (S.biUnion id) := Finset.sdiff_disjoint
    have RA'_ineq : (log N) ^ (1 / 500 : ℝ) ≤ rec_sum A' := by
      have hsum : rec_sum A = rec_sum A' + rec_sum (S.biUnion id) := by
        rw [← rec_sum_disjoint hAS, Finset.sdiff_union_of_subset]
        rwa [Finset.biUnion_subset]
      rw [hsum] at hA₁
      simp only [Rat.cast_add] at hA₁
      rw [rec_sum_bUnion_disjoint hS₂, Rat.cast_sum] at hA₁
      rw [Rat.cast_sum] at hS
      linarith
    have hA' : A' ⊆ A := by
      intro n hn
      exact (Finset.mem_sdiff.mp hn).1
    have h0A' : 0 ∉ A' := by
      intro hz
      specialize A_lower_bound 0 (hA' hz)
      rw [← not_lt] at A_lower_bound
      apply A_lower_bound
      have hNpos : (0 : ℝ) < N := by
        exact_mod_cast lt_of_lt_of_le zero_lt_one hN₁
      simpa using (Real.rpow_pos_of_pos hNpos (1 - (1 : ℝ) / log (log N)))
    obtain ⟨S', hS', d, hd, hd', hS'₂⟩ :=
      p1 A' (hA'.trans A_upper_bound) (fun n hn => A_lower_bound n (hA' hn)) h0A' RA'_ineq
        (fun n hn => hA₂ n (hA' hn)) (fun n hn => hA₃ n (hA' hn)) (hA₄.subset hA')
    have hS'' : ∀ s ∈ S, Disjoint S' s := fun s hs =>
      Disjoint.mono hS' (Finset.subset_biUnion_of_mem id hs) hAS
    have hS''' : S' ∉ S := by
      intro hs
      exact (nonempty_of_rec_sum_recip hd hS'₂).ne_empty (disjoint_self.mp (hS'' _ hs))
    have hPk1 : P (k + 1) := by
      refine ⟨insert S' S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hS''', hk]
      · refine ⟨?_, ?_, ?_⟩
        · simpa [hS'.trans hA'] using hS₁
        · simpa [Set.pairwiseDisjoint_insert_of_notMem hS''', hS₂] using fun s hs =>
            hS'' _ hs
        · intro s
          rcases eq_or_ne s S' with rfl | hs
          · exact ⟨d, fun _ => ⟨hd, hd', hS'₂⟩⟩
          · refine ⟨d' s, fun hs' => ?_⟩
            have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs' hs
            exact ⟨hd'₁ _ hsS, hd'₂ _ hsS, hd'₃ _ hsS⟩
    have hk_bound : k + 1 ≤ A.card + 1 := by
      rw [← hk, add_le_add_iff_right]
      refine le_trans ?_ (Finset.card_le_card (Finset.biUnion_subset.2 hS₁))
      refine Finset.card_le_card_biUnion hS₂ ?_
      intro s hs
      exact nonempty_of_rec_sum_recip (hd'₁ s hs) (hd'₃ s hs)
    have : k + 1 ≤ k := Nat.le_findGreatest hk_bound hPk1
    exact Nat.not_succ_le_self _ this


/-! ## From src4/FinalResults.lean -/

open scoped ArithmeticFunction.omega BigOperators
open Filter Finset Real

noncomputable section
attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/final_results.lean`.

The main goal here is API coverage: every lemma/theorem from the Lean 3 file has a Lean 4 analog
with a translated statement.
-/

lemma another_weird_tendsto_at_top_aux (c : ℝ) (hc : 1 < c) :
    Tendsto (fun x : ℝ => c ^ x / log x) atTop atTop :=
  ((tendsto_exp_mul_div_rpow_atTop 1 _ (log_pos hc)).atTop_mul_atTop₀
      (tendsto_mul_add_div_pow_log_at_top 1 0 1 zero_lt_one)).congr' <| by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by positivity
    have hlogx : log x ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hx) hx.ne'
    simp [Real.rpow_def_of_pos (lt_trans zero_lt_one hc)]
    field_simp [hx0, hlogx]

lemma the_thing : 1 < exp 2 / 2 := by
  rw [one_lt_div zero_lt_two]
  rw [← Real.log_lt_iff_lt_exp zero_lt_two]
  exact Real.log_two_lt_d9.trans_le (by norm_num)

lemma another_weird_tendsto_at_top :
    Tendsto (fun x : ℝ => x / (2 ^ (1 / 2 * log x + 1) * log (1 / 2 * log x))) atTop atTop := by
  refine (Tendsto.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    ((another_weird_tendsto_at_top_aux (exp 2 / 2) the_thing).comp
      (tendsto_log_atTop.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  rw [Real.div_rpow (show 0 ≤ exp 2 by positivity) zero_le_two, div_div, div_mul_div_comm, one_mul,
    Real.rpow_add_one (show (2 : ℝ) ≠ 0 by norm_num), Real.rpow_def_of_pos (exp_pos 2),
    Real.log_exp, ← mul_assoc, mul_one_div_cancel (show (2 : ℝ) ≠ 0 by norm_num), one_mul,
    Real.exp_log hx, ← mul_assoc, mul_comm (2 : ℝ)]

lemma omega_eq_sum (N : ℕ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    ω n = (((Icc 1 N).filter Nat.Prime).filter fun p => p ∣ n).sum (fun _ => 1) := by
  rw [card_distinct_factors_apply', ← Finset.card_eq_sum_ones]
  have hnIcc := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1)
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, and_assoc]
  constructor
  · intro hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpdvd : p ∣ n := (Nat.mem_primeFactorsList_iff_dvd hn0 hpprime).mp hp
    refine ⟨hpprime.one_lt.le, ?_, hpprime, hpdvd⟩
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd).trans hnIcc.2
  · rintro ⟨_, _, hpprime, hpdvd⟩
    exact (Nat.mem_primeFactorsList_iff_dvd hn0 hpprime).mpr hpdvd

lemma count_multiples'' {m n : ℕ} (hm : 1 ≤ m) :
    (((Icc 1 n).filter fun k => m ∣ k).card : ℝ) = (n / m : ℝ) - Int.fract (n / m : ℝ) := by
  rw [count_multiples hm, Int.self_sub_fract, ← natCast_floor_eq_intCast_floor,
    Nat.floor_div_eq_div]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma count_multiples''' {m n : ℕ} (hm : 1 ≤ m) :
    (((Icc 1 n).filter fun k => m ∣ k).card : ℝ) ≤ (n / m : ℝ) := by
  rw [count_multiples'' hm, sub_le_self_iff]
  exact Int.fract_nonneg _

lemma sum_prime_counting :
    ∃ C : ℝ,
      Filter.Eventually
        (fun N : ℕ =>
          (N : ℝ) * log (log (N : ℝ)) - C * (N : ℝ) ≤
            (Icc (1 : ℕ) N).sum (fun x => (ω x : ℝ)))
        atTop := by
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).isBigO).bound
  refine ⟨-meissel_mertens + c + 1, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hc] with N hN
  simp only [prime_summatory, Nat.floor_natCast, abs_one, mul_one, norm_eq_abs] at hN
  have hω :
      ∀ x ∈ Icc 1 N, (ω x : ℝ) =
        ((Icc 1 N).filter Nat.Prime).sum (fun p => ite (p ∣ x) (1 : ℝ) 0) := by
    intro x hx
    rw [omega_eq_sum _ hx, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_congr rfl hω, Finset.sum_comm]
  simp only [← Finset.sum_filter]
  have hcount :
      ∀ x ∈ (Icc 1 N).filter Nat.Prime,
        ((Icc 1 N).filter fun a => x ∣ a).sum (fun _ => (1 : ℝ)) =
          (N / x : ℝ) - Int.fract (N / x : ℝ) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [← count_multiples'' hx.1.1, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_congr rfl hcount, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, ← Finset.mul_sum]
  have h₁ :
      (N : ℝ) * (log (log (N : ℝ)) + meissel_mertens - c) ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact sub_le_of_abs_sub_le_left hN
  have h₂ :
      (((Icc 1 N).filter Nat.Prime).sum fun x => Int.fract ((N : ℝ) * (x : ℝ)⁻¹)) ≤ N := by
    refine (sum_le_card_mul_real (A := (Icc 1 N).filter Nat.Prime) (M := 1) ?_).trans ?_
    · intro x hx
      exact (Int.fract_lt_one _).le
    · have hcard : (((Icc 1 N).filter Nat.Prime).card : ℝ) ≤ N := by
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      simpa using hcard
  have hmain :
      (N : ℝ) * (log (log (N : ℝ)) + meissel_mertens - c) - N ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) -
          (((Icc 1 N).filter Nat.Prime).sum fun x => Int.fract ((N : ℝ) * (x : ℝ)⁻¹)) :=
    sub_le_sub h₁ h₂
  convert hmain using 1
  ring

lemma range_eq_insert_Icc {n : ℕ} (hn : 1 ≤ n) : range n = insert 0 (Icc 1 (n - 1)) := by
  ext x
  simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

lemma prime_recip_lazy :
    ∃ c,
      Filter.Eventually
        (fun N : ℕ =>
          ((Icc (1 : ℕ) N).filter Nat.Prime).sum (fun p => (p : ℝ)⁻¹) ≤
            log (log (N : ℝ)) + c)
        atTop := by
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).isBigO).bound
  refine ⟨meissel_mertens + c, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hc] with N hN
  dsimp at hN
  simp only [prime_summatory, Nat.floor_natCast, abs_one, mul_one, abs_sub_le_iff,
    sub_le_iff_le_add', add_assoc] at hN
  exact hN.1

lemma sum_prime_counting_sq :
    ∃ C : ℝ,
      Filter.Eventually
        (fun N : ℕ =>
          (Icc (1 : ℕ) N).sum (fun x => (ω x : ℝ) ^ 2) ≤
            (N : ℝ) * log (log (N : ℝ)) ^ 2 + C * (N : ℝ) * log (log (N : ℝ)))
        atTop := by
  obtain ⟨c, hc⟩ := prime_recip_lazy
  refine ⟨(2 * c + 1) + 1, ?_⟩
  filter_upwards [hc, tendsto_log_log_coe_at_top (eventually_ge_atTop (c ^ 2 + c))] with N hN hN'
  dsimp at hN'
  have hω :
      ∀ x ∈ Icc 1 N, (ω x : ℝ) ^ 2 =
        (((Icc 1 N).filter Nat.Prime).sum (fun p => ite (p ∣ x) (1 : ℝ) 0)) ^ 2 := by
    intro x hx
    rw [omega_eq_sum _ hx, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_congr rfl hω]
  simp_rw [sq, Finset.sum_mul, mul_sum, boole_mul, ← ite_and, @Finset.sum_comm _ _ _ _ (Icc _ _),
    ← sq]
  have hsplit :
      ∀ p ∈ (Icc 1 N).filter Nat.Prime,
        ((Icc 1 N).filter Nat.Prime).sum
            (fun q =>
              (Icc 1 N).sum (fun n => ite (p ∣ n ∧ q ∣ n) (1 : ℝ) 0)) ≤
          (Icc 1 N).sum (fun n => ite (p ∣ n) (1 : ℝ) 0) +
            ((Icc 1 N).filter Nat.Prime).sum
              (fun q => (Icc 1 N).sum (fun n => ite (p * q ∣ n) (1 : ℝ) 0)) := by
    intro p hp
    rw [← Finset.sum_filter_add_sum_filter_not ((Icc 1 N).filter Nat.Prime) (fun q => p = q),
      Finset.sum_filter, Finset.sum_ite_eq, if_pos hp]
    simp only [and_self, add_le_add_iff_left]
    refine (Finset.sum_le_sum ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp hq
      refine Finset.sum_le_sum fun n hn => ?_
      by_cases h : p ∣ n ∧ q ∣ n
      · rw [if_pos h]
        have hpqcop : Nat.Coprime p q := by
          by_contra hcop
          rw [Nat.Prime.not_coprime_iff_dvd] at hcop
          rcases hcop with ⟨r, hr, hrp, hrq⟩
          have hrp' : r = p := (Nat.prime_dvd_prime_iff_eq hr hp.2).mp hrp
          have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr hq.1.2).mp hrq
          exact hq.2 (hrp'.symm.trans hrq')
        rw [if_pos (hpqcop.mul_dvd_of_dvd_of_dvd h.1 h.2)]
      · rw [if_neg h]
        split_ifs
        · exact zero_le_one
        · rfl
    · intro i hi hif
      simp only [Finset.sum_boole, Nat.cast_nonneg]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole]
  have h₁ :
      (((Icc 1 N).filter Nat.Prime).sum fun x => (((Icc 1 N).filter fun a => x ∣ a).card : ℝ)) ≤
        (N : ℝ) * (((Icc 1 N).filter Nat.Prime).sum fun x => (x : ℝ)⁻¹) := by
    simp only [mul_sum, ← div_eq_mul_inv]
    refine Finset.sum_le_sum fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    exact count_multiples''' hx.1.1
  have h₂ :
      (((Icc 1 N).filter Nat.Prime).sum fun p =>
          (((Icc 1 N).filter Nat.Prime).sum fun q =>
            (((Icc 1 N).filter fun a => p * q ∣ a).card : ℝ))) ≤
        (N : ℝ) * ((((Icc 1 N).filter Nat.Prime).sum fun p => (p : ℝ)⁻¹) ^ 2) := by
    simp only [sq, mul_sum, Finset.sum_mul, ← mul_inv, ← div_eq_mul_inv (N : ℝ), ← Nat.cast_mul]
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp hq
    simpa [Nat.mul_comm] using (count_multiples''' <| Nat.succ_le_of_lt <|
      Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hp.1.1) (lt_of_lt_of_le Nat.zero_lt_one hq.1.1)
    )
  refine (add_le_add h₁ h₂).trans ?_
  set S : ℝ := ((Icc 1 N).filter Nat.Prime).sum fun p => (p : ℝ)⁻¹
  set L : ℝ := log (log (N : ℝ))
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
  have hsq : S ^ 2 ≤ (L + c) ^ 2 := by
    have hSc : S ≤ L + c := by simpa [S, L] using hN
    exact pow_le_pow_left₀ hS0 hSc 2
  have hmain : S + S ^ 2 ≤ L ^ 2 + (((2 * c + 1) + 1) * L) := by
    have hSc : S ≤ L + c := by simpa [S, L] using hN
    nlinarith [hSc, hsq, hN']
  have hmainN := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg N)
  simpa [S, L, left_distrib, right_distrib, mul_assoc, mul_left_comm, mul_comm] using hmainN

lemma count_divisors {x N : ℕ} (hx : x ≠ 0) :
    (((Icc 1 N).filter fun i => x ∣ i).card : ℝ) = (N / x : ℝ) - Int.fract (N / x : ℝ) := by
  simpa using count_multiples'' (m := x) (n := N) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx))

lemma count_divisors' {x N : ℕ} (hx : x ≠ 0) (hN : N ≠ 0) :
    (((range N).filter fun i => x ∣ i).card : ℝ) =
      (N / x : ℝ) - (1 / x - 1 + Int.fract ((N - 1) / x : ℝ)) := by
  have hN' : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
  rw [range_eq_insert_Icc hN', Finset.filter_insert, if_pos (dvd_zero x), card_insert_of_notMem,
    Nat.cast_add_one, count_divisors hx, Nat.cast_sub hN', Nat.cast_one, sub_div]
  · ring
  · simp

lemma is_multiplicative_one {R : Type*} [Ring R] :
    (1 : ArithmeticFunction R).IsMultiplicative := by
  simp only [ArithmeticFunction.isMultiplicative_one]

-- `ite_div` is already available from imported dependencies.

lemma moebius_rec_sum {N : ℕ} (hN : N ≠ 0) :
    N.divisors.sum (fun x => (ArithmeticFunction.moebius x : ℝ) / x) =
      (N.divisors.filter Nat.Prime).prod (fun p => 1 - (p : ℝ)⁻¹) := by
  let f' : ArithmeticFunction ℝ := ⟨fun x => (ArithmeticFunction.moebius x : ℝ) / x, by simp⟩
  have hf' : f'.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f']
    · intro m n hmn
      simp [f', ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
        mul_div_mul_comm, Nat.cast_mul, Int.cast_mul]
  let f : ArithmeticFunction ℝ := f' * ArithmeticFunction.zeta
  have hf : f.IsMultiplicative := hf'.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  change ∑ x ∈ N.divisors, f' x = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  change f N = _
  rw [← Nat.primeFactors_eq_to_filter_divisors_prime]
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
        Finset.sum_range_succ', Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
      simp [f', ArithmeticFunction.moebius_apply_prime_pow, hp, hk, ite_div]
      ring
  | zero =>
      cases hN rfl
  | one =>
      simp [hf.map_one]
  | coprime a b ha hb hab aih bih =>
      have ha0 : a ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ha)
      have hb0 : b ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb)
      rw [hf.map_mul_of_coprime hab, Nat.primeFactors_mul ha0 hb0, Finset.prod_union]
      · rw [aih ha0, bih hb0]
      · exact hab.disjoint_primeFactors

lemma prod_sdiff'' {ι α : Type*} [DecidableEq ι] [CommGroupWithZero α] (f : ι → α)
    (s t : Finset ι)
    (h : t ⊆ s) (ht : ∀ i ∈ t, f i ≠ 0) :
    (s \ t).prod f = s.prod f / t.prod f := by
  rw [eq_div_iff_mul_eq]
  · rw [Finset.prod_sdiff h]
  · exact Finset.prod_ne_zero_iff.mpr fun i hi => ht i hi

lemma filter_sdiff {ι : Type*} (p : ι → Prop) [DecidableEq ι] [DecidablePred p]
    (s t : Finset ι) :
    (s \ t).filter p = s.filter p \ t.filter p := by
  ext x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> by_cases hp : p x <;>
    simp [hs, ht, hp, Finset.mem_sdiff, Finset.mem_filter]

lemma product_of_primes_factors {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    (s.prod id).primeFactorsList = s.sort (fun a b => a ≤ b) := by
  refine
    ((Nat.primeFactorsList_unique (n := s.prod id)
        (l := s.sort (fun a b => a ≤ b)) ?_ ?_).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  · calc
      (s.sort (fun a b => a ≤ b)).prod = (s.sort (fun a b => a ≤ b)).toFinset.prod id := by
          simpa using (List.prod_toFinset id (s.sort_nodup (fun a b => a ≤ b))).symm
      _ = s.prod id := by rw [Finset.sort_toFinset]
  · intro p hp
    exact hs p ((Finset.mem_sort (fun a b => a ≤ b)).mp hp)
  · exact pairwise_sort _ _

lemma product_of_primes_factors_to_finset {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    (s.prod id).primeFactorsList.toFinset = s := by
  rw [product_of_primes_factors hs, Finset.sort_toFinset]

lemma mem_factors_prod {A : Finset ℕ} (h : ∀ n ∈ A, n ≠ 0) {p : ℕ} :
    p ∈ (A.prod id).primeFactorsList ↔ ∃ a ∈ A, p ∈ (a : ℕ).primeFactorsList := by
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert n A hnA ih =>
      have hn0 : n ≠ 0 := h n (Finset.mem_insert_self _ _)
      have hA : ∀ m ∈ A, m ≠ 0 := by
        intro m hm
        exact h m (Finset.mem_insert_of_mem hm)
      have hprod0 : A.prod id ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro m hm
        exact hA m hm
      rw [Finset.prod_insert hnA]
      change p ∈ (n * A.prod id).primeFactorsList ↔ ∃ a ∈ insert n A, p ∈ (a : ℕ).primeFactorsList
      rw [Nat.mem_primeFactorsList_mul hn0 hprod0]
      constructor
      · intro hp
        rcases hp with hp | hp
        · exact ⟨n, Finset.mem_insert_self _ _, hp⟩
        · rw [ih hA] at hp
          rcases hp with ⟨a, ha, hpa⟩
          exact ⟨a, Finset.mem_insert_of_mem ha, hpa⟩
      · rintro ⟨a, ha, hpa⟩
        rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact Or.inl hpa
        · exact Or.inr ((ih hA).2 ⟨a, ha, hpa⟩)

lemma prod_primes_squarefree {A : Finset ℕ} (h : ∀ n ∈ A, Nat.Prime n) :
    Squarefree (A.prod id) := by
  exact squarefree_prime_prod id h (fun _ _ _ _ hEq => hEq)

lemma sieve_lemma_prec (N : ℕ) (y z : ℝ) (hy : 1 ≤ y) (hzN : z < N) :
    ((((range N).filter
          fun n =>
            ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ)) ≤
      (partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊) * N + 2 ^ (z + 1) := by
  by_cases hN0 : N = 0
  · rw [hN0, Finset.range_zero, Finset.filter_empty]
    norm_num
    exact Real.rpow_nonneg zero_le_two _
  rcases lt_or_ge z y with h | h
  · calc
      (((range N).filter
            fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ) ≤ (N : ℝ) := by
          have hcard :
              ((range N).filter
                    fun n =>
                      ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card ≤
                (range N).card :=
            Finset.card_filter_le _ _
          simpa using hcard
      _ ≤ (partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊) * N + 2 ^ (z + 1) := by
          rw [← add_zero (N : ℝ)]
          refine add_le_add ?_ ?_
          · rw [add_zero]
            refine le_mul_of_one_le_left (Nat.cast_nonneg N) ?_
            rw [one_le_div]
            · rw [partial_euler_product, partial_euler_product]
              refine prod_of_subset_le_prod_of_one_le ?_ ?_ ?_
              · intro p hp
                rw [Finset.mem_filter, Finset.mem_Icc]
                rw [Finset.mem_filter, Finset.mem_Icc] at hp
                refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
                exact le_trans hp.1.2 (Nat.floor_mono h.le)
              · intro p hp
                rw [inv_nonneg]
                rw [Finset.mem_filter] at hp
                have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
                exact sub_nonneg.mpr (le_of_lt (inv_lt_one_of_one_lt₀ hp1))
              · intro p hp1 hp2
                rw [Finset.mem_filter] at hp1
                have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1.2.one_lt
                have hpos : 0 < 1 - (p : ℝ)⁻¹ :=
                  sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1')
                refine (one_le_inv₀ hpos).2 ?_
                exact sub_le_self _ (inv_nonneg.2 (Nat.cast_nonneg p))
            · exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
          · exact Real.rpow_nonneg zero_le_two _
  · let P :=
      ((range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z).prod id
    have hP : P ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      exact hx.2.1.pos.ne'
    have h₁ :
        ((range N).filter fun n =>
            ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card =
          ((range N).filter fun n => Nat.Coprime n P).card := by
      congr 1
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn, hn'⟩
        refine ⟨hn, ?_⟩
        rw [Nat.coprime_prod]
        intro p hpP
        have hp : Nat.Prime p := (Finset.mem_filter.mp hpP).2.1
        have hy' : y ≤ p := (Finset.mem_filter.mp hpP).2.2.1
        have hz' : (p : ℝ) ≤ z := (Finset.mem_filter.mp hpP).2.2.2
        change Nat.Coprime n p
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro hdiv
        cases hn' p hp hdiv with
        | inl hlt => exact (not_lt_of_ge hy') hlt
        | inr hgt => exact (not_lt_of_ge hz') hgt
      · rintro ⟨hn, hn'⟩
        refine ⟨hn, ?_⟩
        intro p hp hpdvd
        by_contra hbad
        push Not at hbad
        have hpRange : p ∈ range N := by
          rw [Finset.mem_range]
          exact_mod_cast (lt_of_le_of_lt hbad.2 hzN)
        have hpP : p ∈ (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z := by
          simp [hpRange, hp, hbad.1, hbad.2]
        have hnotcop : ¬ Nat.Coprime n p := by
          have hnotcop' : ¬ Nat.Coprime p n := by
            rw [hp.coprime_iff_not_dvd]
            exact not_not_intro hpdvd
          simpa [Nat.coprime_comm] using hnotcop'
        rw [Nat.coprime_prod] at hn'
        exact hnotcop (hn' p hpP)
    have hmu :
        ∀ n, ∑ i ∈ (Nat.gcd n P).divisors, (ArithmeticFunction.moebius i : ℝ) =
          ite (Nat.gcd n P = 1) 1 0 := by
      intro n
      rw [← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.moebius_mul_coe_zeta]
      change ((ite ((Nat.gcd n P) = 1) 1 0 : ℤ) : ℝ) = _
      split_ifs <;> simp
    rw [h₁, ← Finset.sum_boole]
    simp only [Nat.Coprime]
    simp_rw [← hmu]
    have hgcddiv : ∀ x : ℕ, (Nat.gcd x P).divisors = P.divisors.filter fun d => d ∣ x := by
      intro x
      ext m
      constructor
      · intro hm
        rw [Nat.mem_divisors] at hm
        rcases (Nat.dvd_gcd_iff.mp hm.1) with ⟨hmx, hmP⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hmP, hP⟩, hmx⟩
      · intro hm
        rw [Finset.mem_filter, Nat.mem_divisors] at hm
        rcases hm with ⟨⟨hmP, hP'⟩, hmx⟩
        rw [Nat.mem_divisors]
        refine ⟨Nat.dvd_gcd hmx hmP, ?_⟩
        intro hgcd0
        have h0dvd : 0 ∣ P := by
          simpa [hgcd0] using (Nat.gcd_dvd_right x P)
        exact hP' (by simpa using h0dvd)
    simp_rw [hgcddiv, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [← mul_boole _ (ArithmeticFunction.moebius _ : ℝ), ← Finset.mul_sum]
    simp_rw [Finset.sum_boole]
    have hcount :
        ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) *
            ((((range N).filter fun i => x ∣ i).card : ℝ)) =
          ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) *
            ((N / x : ℝ) - (1 / x - 1 + Int.fract ((N - 1) / x : ℝ))) := by
      rw [Finset.sum_congr rfl]
      intro x hx
      rw [count_divisors']
      · rw [Nat.mem_divisors] at hx
        exact ne_zero_of_dvd_ne_zero hx.2 hx.1
      · exact hN0
    simp_rw [hcount, mul_sub]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_div_assoc', mul_comm _ (N : ℝ), mul_div_assoc]
    rw [← Finset.mul_sum]
    have hP_divisors :
        P.divisors.filter Nat.Prime =
          (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z := by
      rw [← Nat.primeFactors_eq_to_filter_divisors_prime]
      change (((range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z).prod id).primeFactors =
        (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z
      rw [Nat.primeFactors]
      exact
        product_of_primes_factors_to_finset
          (s := (range N).filter fun p => Nat.Prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z)
          (by
            intro p hp
            exact (Finset.mem_filter.mp hp).2.1)
    have hP_divisors' :
        (Icc 1 ⌊z⌋₊ \ Icc 1 ⌊y⌋₊).filter Nat.Prime ⊆ P.divisors.filter Nat.Prime := by
      have h_one_le_yfloor : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).2 hy
      have h_sdiff_eq : (Icc 1 ⌊z⌋₊ \ Icc 1 ⌊y⌋₊ : Finset ℕ) = Ioc ⌊y⌋₊ ⌊z⌋₊ := by
        ext n
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hP_divisors, h_sdiff_eq]
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hprime : Nat.Prime n := hn.2
      have hylt : y < n := (Nat.floor_lt' hprime.ne_zero).1 hn.1.1
      have hz0 : 0 ≤ z := zero_le_one.trans (le_trans hy h)
      have hnz : (n : ℝ) ≤ z := (Nat.le_floor_iff hz0).1 hn.1.2
      have hnN : n < N := by
        exact_mod_cast (lt_of_le_of_lt hnz hzN)
      simpa [Finset.mem_filter] using ⟨hnN, hprime, hylt.le, hnz⟩
    have hPsum :
        ∑ x ∈ P.divisors, (ArithmeticFunction.moebius x : ℝ) / x ≤
          partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ := by
      rw [moebius_rec_sum hP, partial_euler_product, partial_euler_product, Finset.prod_inv_distrib,
        Finset.prod_inv_distrib, inv_div_inv, ← prod_sdiff'', ← filter_sdiff]
      · refine Finset.prod_le_prod_of_subset_of_le_one ?_ ?_ ?_
        · convert hP_divisors'
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
          exact sub_nonneg.mpr (le_of_lt (inv_lt_one_of_one_lt₀ hp1))
        · intro p hp1 hp2
          refine sub_le_self _ ?_
          rw [inv_nonneg]
          exact Nat.cast_nonneg p
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
        exact le_trans hp.1.2 (Nat.floor_mono h)
      · intro p hp
        refine ne_of_gt ?_
        rw [Finset.mem_filter] at hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
        exact sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
    rw [sub_eq_add_neg]
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left hPsum (Nat.cast_nonneg N)
    · refine le_trans (le_abs_self _) ?_
      rw [abs_neg]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc
        ∑ x ∈ P.divisors,
            |(ArithmeticFunction.moebius x : ℝ) *
              (1 / x - 1 + Int.fract ((N - 1) / x : ℝ))| ≤
            (2 : ℝ) * (ArithmeticFunction.sigma 0 P : ℝ) := by
              rw [ArithmeticFunction.sigma_zero_apply]
              refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans ?_
              · intro d hd
                rw [abs_mul, ← one_mul (2 : ℝ)]
                refine mul_le_mul ?_ ?_ ?_ ?_
                · by_cases hdsq : Squarefree d
                  · rw [ArithmeticFunction.moebius_apply_of_squarefree hdsq]
                    norm_num
                  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
                    norm_num
                · rw [← add_sub_right_comm, ← add_sub]
                  refine le_trans (abs_add_le _ _) ?_
                  transitivity (1 : ℝ) + 1
                  · refine add_le_add ?_ ?_
                    · rw [abs_of_nonneg]
                      · have hd1 : (1 : ℝ) ≤ d := by
                          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hd)
                        simpa [one_div] using
                          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hd1)
                      · rw [one_div_nonneg]
                        exact Nat.cast_nonneg d
                    · rw [abs_of_nonpos, neg_sub]
                      · exact sub_le_self _ (Int.fract_nonneg _)
                      · rw [sub_nonpos]
                        exact le_of_lt (Int.fract_lt_one _)
                  · norm_num
                · exact abs_nonneg _
                · exact zero_le_one
              · simp only [nsmul_eq_mul]
                rw [mul_comm]
        _ ≤ 2 ^ (z + 1) := by
          have hPsq : Squarefree P := by
            refine prod_primes_squarefree ?_
            intro p hp
            rw [Finset.mem_filter] at hp
            exact hp.2.1
          rw [divisor_count_eq_pow_iff_squarefree.2 hPsq, Nat.cast_pow]
          norm_num
          rw [← Real.rpow_natCast, mul_comm, ← Real.rpow_add_one]
          · refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
            rw [card_distinct_factors_apply']
            transitivity (((insert 0 P.primeFactorsList.toFinset).card : ℕ) : ℝ)
            · rw [Finset.card_insert_of_notMem]
              · norm_num
              · rw [List.mem_toFinset]
                intro hbad
                exact Nat.not_prime_zero (Nat.prime_of_mem_primeFactorsList hbad)
            · transitivity (((Icc 0 ⌊z⌋₊).card : ℕ) : ℝ)
              · have hsubset : insert 0 P.primeFactorsList.toFinset ⊆ Icc 0 ⌊z⌋₊ := by
                  intro p hp
                  rw [Finset.mem_insert] at hp
                  rcases hp with rfl | hp
                  · simp only [Finset.left_mem_Icc, Nat.zero_le]
                  · rw [List.mem_toFinset,
                      mem_factors_prod
                        (h := by
                          intro n hn
                          exact Nat.Prime.ne_zero (Finset.mem_filter.mp hn).2.1)] at hp
                    rcases hp with ⟨q, hq1, hq2⟩
                    rw [Finset.mem_filter] at hq1
                    rw [Nat.primeFactorsList_prime hq1.2.1, List.mem_singleton] at hq2
                    rw [hq2, Finset.mem_Icc]
                    refine ⟨Nat.zero_le q, ?_⟩
                    exact (Nat.le_floor_iff (zero_le_one.trans (le_trans hy h))).2 hq1.2.2.2
                exact_mod_cast (Finset.card_le_card hsubset)
              · rw [Nat.card_Icc, Nat.cast_sub]
                · push_cast
                  rw [sub_zero]
                  nlinarith [Nat.floor_le (zero_le_one.trans (le_trans hy h))]
                · exact zero_le (⌊z⌋₊ + 1)
          · norm_num

lemma sieve_lemma_prec' :
    ∃ C c : ℝ,
      0 < C ∧
        0 < c ∧
          Filter.Eventually
            (fun N : ℕ =>
              ∀ y z : ℝ,
                2 ≤ y →
                  1 < z →
                    z ≤ c * log (N : ℝ) →
                      ((((range N).filter fun n =>
                              ∀ p : ℕ,
                                Nat.Prime p →
                                  p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ)) ≤
                        C * (log y / log z) * N)
            atTop := by
  rcases weak_mertens_third_lower_all with ⟨C₁, hC₁, hml⟩
  rcases weak_mertens_third_upper_all with ⟨C₂, hC₂, hmu⟩
  let C := 1 / C₁ * C₂ * 2
  let c : ℝ := 1 / 2
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos ?_ zero_lt_two
    refine mul_pos ?_ hC₂
    exact one_div_pos.mpr hC₁
  refine ⟨C, c, h0C, by norm_num, ?_⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (2 : ℝ))
    , (another_weird_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 / (C / 2 * log 2))) ] with
      N h0N hlogN hweirdN
  dsimp at hlogN hweirdN
  intro y z h2y h1z hzN
  have h0logN : 0 < log (N : ℝ) := by
    linarith
  have hzNhalf : z ≤ 1 / 2 * log (N : ℝ) := by
    simpa [c] using hzN
  have hzN' : z < N := by
    have hcLog : c * log (N : ℝ) ≤ log (N : ℝ) := by
      dsimp [c]
      refine mul_le_of_le_one_left h0logN.le ?_
      change (1 : ℝ) / 2 ≤ 1
      exact half_le_self zero_le_one
    exact hzN.trans_lt (lt_of_le_of_lt hcLog (log_lt_self h0N))
  refine le_trans (sieve_lemma_prec N y z (le_trans (by norm_num) h2y) hzN') ?_
  rw [← add_halves C, add_mul, add_mul]
  refine add_le_add ?_ ?_
  · have hlogz : 0 < log z := Real.log_pos h1z
    have hpepz_pos : 0 < partial_euler_product ⌊z⌋₊ := by
      exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
    have hmu' : partial_euler_product ⌊y⌋₊ ≤ C₂ * log y := by
      have hmu0 := hmu y h2y
      have hpepy_pos : 0 < partial_euler_product ⌊y⌋₊ := by
        exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
      simpa [Real.norm_eq_abs, abs_of_pos hpepy_pos,
        abs_of_pos (Real.log_pos (lt_of_lt_of_le one_lt_two h2y))] using hmu0
    have hml' : C₁ * log z ≤ partial_euler_product ⌊z⌋₊ := by
      have hml0 := hml z (le_of_lt h1z)
      simpa [Real.norm_eq_abs, abs_of_pos hlogz,
        abs_of_pos hpepz_pos] using hml0
    have hC : C / 2 = (1 / C₁) * C₂ := by
      dsimp [C]
      ring
    have hbase' :
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
          (((1 / C₁) * C₂) * log y) / log z := by
      refine (div_le_div_iff₀ hpepz_pos hlogz).2 ?_
      transitivity C₂ * log y * log z
      · exact mul_le_mul_of_nonneg_right hmu' hlogz.le
      · have hylog_nonneg : 0 ≤ log y := Real.log_nonneg (le_trans one_le_two h2y)
        have hcoeff_nonneg : 0 ≤ C₂ * log y / C₁ := by
          rw [div_eq_mul_inv]
          exact mul_nonneg (mul_nonneg hC₂.le hylog_nonneg) (inv_nonneg.2 hC₁.le)
        have hstep :
            (C₂ * log y / C₁) * (C₁ * log z) ≤
              (C₂ * log y / C₁) * partial_euler_product ⌊z⌋₊ := by
          exact mul_le_mul_of_nonneg_left hml' hcoeff_nonneg
        calc
          C₂ * log y * log z = (C₂ * log y / C₁) * (C₁ * log z) := by
            field_simp [hC₁.ne']
          _ ≤ (C₂ * log y / C₁) * partial_euler_product ⌊z⌋₊ := hstep
          _ = (((1 / C₁) * C₂) * log y) * partial_euler_product ⌊z⌋₊ := by
            ring
    have hbase :
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
          (C / 2) * (log y / log z) := by
      calc
        partial_euler_product ⌊y⌋₊ / partial_euler_product ⌊z⌋₊ ≤
            (((1 / C₁) * C₂) * log y) / log z := hbase'
        _ = (C / 2) * (log y / log z) := by rw [hC]; ring
    exact mul_le_mul_of_nonneg_right hbase h0N.le
  · have hlogz : 0 < log z := Real.log_pos h1z
    have hmainpow :
        2 ^ (z + 1) ≤ (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) := by
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      linarith
    have hloghalf :
        log z ≤ log (1 / 2 * log (N : ℝ)) := by
      refine Real.log_le_log (lt_trans zero_lt_one h1z) hzNhalf
    have hhalfpos : 0 < log (1 / 2 * log (N : ℝ)) := by
      have hhalfgt1 : 1 < 1 / 2 * log (N : ℝ) := by
        linarith
      refine Real.log_pos ?_
      exact hhalfgt1
    have hweird' :
        (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ)) ≤
          (C / 2 * log 2) * N := by
      have hApos : 0 < C / 2 * log 2 := by
        refine mul_pos ?_ (Real.log_pos one_lt_two)
        exact div_pos h0C zero_lt_two
      have hBpos :
          0 < (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ)) := by
        refine mul_pos (Real.rpow_pos_of_pos zero_lt_two _) hhalfpos
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (div_le_div_iff₀ hApos hBpos).1 hweirdN
    transitivity (2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1)
    · exact hmainpow
    transitivity
      ((2 : ℝ) ^ (1 / 2 * log (N : ℝ) + 1) * log (1 / 2 * log (N : ℝ))) / log z
    · rw [le_div_iff₀ hlogz]
      exact mul_le_mul_of_nonneg_left hloghalf
        (Real.rpow_nonneg (by positivity) _)
    · transitivity ((C / 2 * log 2) * N) / log z
      · exact div_le_div_of_nonneg_right hweird' hlogz.le
      · have hylog2 : log 2 ≤ log y := Real.log_le_log zero_lt_two h2y
        have hnum :
            (C / 2 * log 2) * N ≤ (C / 2 * log y) * N := by
          gcongr
        exact (div_le_div_of_nonneg_right hnum hlogz.le).trans_eq (by ring)

lemma plogp_tail_bound (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ N in (atTop : Filter ℕ),
          ∀ z : ℝ,
            0 ≤ log (log ⌊z⌋₊) →
              ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
                c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
  obtain ⟨c₁, hmertens⟩ := Filter.eventually_atTop.mp explicit_mertens
  let c : ℝ := a * 2
  refine ⟨c, mul_pos ha zero_lt_two, ?_⟩
  filter_upwards [eventually_gt_atTop 4, eventually_ge_atTop c₁] with N h4N hcN
  have h0Nnat : 0 < N := by omega
  have h0N : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h0Nnat
  have hlogN : 0 < log ((N : ℝ) / 4) := by
    refine Real.log_pos ?_
    rw [one_lt_div zero_lt_four]
    exact_mod_cast h4N
  intro z hz'
  by_cases hz : (N : ℝ) ≤ z
  · have hNz : N ≤ ⌊z⌋₊ := by
      rw [Nat.le_floor_iff' (Nat.ne_of_gt h0Nnat)]
      exact hz
    calc
      ((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => a / (log (x / 4) * x)) ≤
          ((Icc N ⌊z⌋₊).filter Nat.Prime).sum
            (fun x => (a / log ((N : ℝ) / 4)) * (1 / x : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
        rcases Finset.mem_Icc.mp hpIcc with ⟨hpN, hpz⟩
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpN
        have hlogp : 0 < log ((p : ℝ) / 4) := by
          refine Real.log_pos ?_
          rw [one_lt_div zero_lt_four]
          exact_mod_cast lt_of_lt_of_le h4N hpN
        have hlogNp : log ((N : ℝ) / 4) ≤ log ((p : ℝ) / 4) := by
          refine Real.log_le_log (div_pos h0N zero_lt_four) ?_
          exact div_le_div_of_nonneg_right hNp zero_lt_four.le
        have hrecip :
            1 / log ((p : ℝ) / 4) ≤ 1 / log ((N : ℝ) / 4) :=
          one_div_le_one_div_of_le hlogN hlogNp
        have hdiv :=
          mul_le_mul_of_nonneg_left hrecip (div_nonneg ha.le hp0.le)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = (a / log ((N : ℝ) / 4)) *
            (((Icc N ⌊z⌋₊).filter Nat.Prime).sum (fun x => (1 / x : ℝ))) := by
        rw [← Finset.mul_sum]
      _ ≤ (a / log ((N : ℝ) / 4)) *
            ((((range (⌊z⌋₊ + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqPrime⟩
          rcases Finset.mem_Icc.mp hqIcc with ⟨_, hqz⟩
          exact
            Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqz), hqPrime.isPrimePow⟩
        · intro n _ _
          exact one_div_nonneg.2 (Nat.cast_nonneg n)
      _ ≤ (a / log ((N : ℝ) / 4)) * (2 * log (log ⌊z⌋₊)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ha.le hlogN.le)
        exact hmertens ⌊z⌋₊ (le_trans hcN hNz)
      _ = c * log (log ⌊z⌋₊) / log ((N : ℝ) / 4) := by
        dsimp [c]
        ring
  · have hIcc : Icc N ⌊z⌋₊ = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact (Nat.floor_lt' (Nat.ne_of_gt h0Nnat)).2 (lt_of_not_ge hz)
    rw [hIcc, Finset.filter_empty, Finset.sum_empty]
    refine div_nonneg ?_ hlogN.le
    exact mul_nonneg (by dsimp [c]; positivity) hz'

lemma filter_div_aux (a b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∃ y z w : ℝ,
      2 ≤ y ∧
        16 ≤ w ∧
          0 < z ∧
            1 < z ∧
              4 * y + 4 ≤ z ∧
                a ≤ y ∧
                  d ≤ y ∧
                    log w / log z ≤ b ∧
                      ((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
                          (fun x => log y / (log (x / 4) * x)) ≤
                        c := by
  let y : ℝ := max 2 (max a d)
  have hlogy : 0 < log y := by
    refine Real.log_pos ?_
    exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
  obtain ⟨C₁, h0C₁, htail⟩ := plogp_tail_bound (log y) hlogy
  rw [Filter.eventually_atTop] at htail
  obtain ⟨C₂', htail'⟩ := htail
  let C₂ : ℝ := max 1 C₂'
  let ε : ℝ := c * b / (2 * C₁)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have haux := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound hε
  have haux' := Real.tendsto_log_atTop.eventually haux
  rw [Filter.eventually_atTop] at haux'
  obtain ⟨C₃, haux'⟩ := haux'
  let z : ℝ :=
    max (exp (log 4 * 2 / b))
      (max C₃
        (max 3
          (max (4 * y + 4)
            (max (exp (exp (log (16 / 4) * c / C₁)) + 1)
              (exp (exp (log (C₂ / 4) * c / C₁)) + 1)))))
  let w : ℝ := 4 * exp (C₁ * log (log ⌊z⌋₊) / c)
  have hz₁ : exp (log 4 * 2 / b) ≤ z := by
    exact le_max_left _ _
  have hz₂ : C₃ ≤ z := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hz₄' : 3 ≤ z := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hz₄ : 2 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    norm_num
  have hz₅ : exp 1 < z := by
    refine lt_of_lt_of_le ?_ hz₄'
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hz₆ : 4 * y + 4 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hzfloor : z - 1 ≤ ⌊z⌋₊ := by
    rw [sub_le_iff_le_add]
    exact le_of_lt (Nat.lt_floor_add_one _)
  have hz₃ : 1 ≤ z := le_trans one_le_two (le_of_lt hz₄)
  have hz₀ : 0 < z := lt_of_lt_of_le zero_lt_one hz₃
  have hz₈' : exp (exp (log (16 / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₉' : exp (exp (log (C₂ / 4) * c / C₁)) + 1 ≤ z := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hz₈ : log (16 / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₈'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₉ : log (C₂ / 4) * c / C₁ ≤ log (log ⌊z⌋₊) := by
    rw [← exp_le_exp, Real.exp_log, ← exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hzfloor
      rw [le_sub_iff_add_le]
      exact hz₉'
    · exact_mod_cast Nat.floor_pos.mpr hz₃
    · refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      rw [lt_sub_iff_add_lt]
      linarith
  have hz₇ : 0 ≤ log (log ⌊z⌋₊) := by
    refine le_trans ?_ hz₈
    refine div_nonneg ?_ h0C₁.le
    refine mul_nonneg ?_ hc.le
    exact Real.log_nonneg (by norm_num)
  have hzw : exp (log w / b) ≤ z := by
    have hlogz : 0 < log z := Real.log_pos (lt_trans one_lt_two hz₄)
    have hloglogz : log (log z) ≤ ε * log z := by
      specialize haux' z hz₂
      have hloglogz_pos : 0 < log (log z) := by
        refine Real.log_pos ?_
        rw [← Real.exp_lt_exp, Real.exp_log hz₀]
        exact hz₅
      rw [Real.norm_eq_abs, abs_of_pos hloglogz_pos, Real.rpow_one, Real.norm_eq_abs,
        abs_of_pos hlogz] at haux'
      exact haux'
    have hlogfloor_pos : 0 < log ⌊z⌋₊ := by
      refine Real.log_pos ?_
      refine lt_of_lt_of_le ?_ hzfloor
      linarith
    have hloglogfloor_le : log (log ⌊z⌋₊) ≤ log (log z) := by
      refine Real.log_le_log hlogfloor_pos ?_
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.floor_pos.mpr hz₃
      · exact_mod_cast Nat.floor_le hz₀.le
    have hfirst' : log 4 * 2 / b ≤ log z := by
      rw [← Real.exp_le_exp, Real.exp_log hz₀]
      exact hz₁
    have hfirst : log 4 / b ≤ log z / 2 := by
      have hfirst'' : (log 4 * 2 / b) / 2 ≤ log z / 2 := by
        exact div_le_div_of_nonneg_right hfirst' zero_le_two
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfirst''
    have hsecond' : log (log ⌊z⌋₊) ≤ ε * log z := by
      exact le_trans hloglogfloor_le hloglogz
    have hsecond :
        C₁ * log (log ⌊z⌋₊) / c / b ≤ log z / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hsecond' (show 0 ≤ C₁ / c / b by positivity)
      calc
        C₁ * log (log ⌊z⌋₊) / c / b = (C₁ / c / b) * log (log ⌊z⌋₊) := by ring
        _ ≤ (C₁ / c / b) * (ε * log z) := by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = log z / 2 := by
          dsimp [ε]
          field_simp [h0C₁.ne', hc.ne', hb.ne']
    have hlogw :
        log w / b ≤ log z := by
      rw [show log w = log 4 + C₁ * log (log ⌊z⌋₊) / c by
          rw [show w = 4 * exp (C₁ * log (log ⌊z⌋₊) / c) by rfl,
            Real.log_mul zero_lt_four.ne' (Real.exp_ne_zero _), Real.log_exp],
        add_div]
      have hsum : log 4 / b + (C₁ * log (log ⌊z⌋₊) / c) / b ≤ log z / 2 + log z / 2 := by
        exact add_le_add hfirst hsecond
      simpa [add_halves] using hsum
    rw [← Real.exp_log hz₀]
    exact Real.exp_le_exp.mpr hlogw
  have h16w : 16 ≤ w := by
    have hmain : log (16 / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₈ (show 0 ≤ C₁ / c by positivity)
      calc
        log (16 / 4) = (C₁ / c) * (log (16 / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : (16 : ℝ) / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (by norm_num : 0 < (16 : ℝ) / 4)] using Real.exp_le_exp.mpr hmain
    calc
      (16 : ℝ) = 4 * ((16 : ℝ) / 4) := by norm_num
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have hC₂w : C₂ ≤ w := by
    have hC₂ : (0 : ℝ) < C₂ := by
      dsimp [C₂]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hmain : log (C₂ / 4) ≤ C₁ * log (log ⌊z⌋₊) / c := by
      have hmul := mul_le_mul_of_nonneg_left hz₉ (show 0 ≤ C₁ / c by positivity)
      calc
        log (C₂ / 4) = (C₁ / c) * (log (C₂ / 4) * c / C₁) := by
          field_simp [h0C₁.ne', hc.ne']
        _ ≤ (C₁ / c) * log (log ⌊z⌋₊) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = C₁ * log (log ⌊z⌋₊) / c := by ring
    have hexp : C₂ / 4 ≤ exp (C₁ * log (log ⌊z⌋₊) / c) := by
      simpa [Real.exp_log (div_pos hC₂ zero_lt_four)] using Real.exp_le_exp.mpr hmain
    calc
      C₂ = 4 * (C₂ / 4) := by field_simp [zero_lt_four.ne']
      _ ≤ 4 * exp (C₁ * log (log ⌊z⌋₊) / c) := by
        exact mul_le_mul_of_nonneg_left hexp zero_le_four
      _ = w := by rfl
  have h0w' : (1 : ℝ) < ⌈w⌉₊ / 4 := by
    rw [lt_div_iff₀ zero_lt_four]
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    refine lt_of_lt_of_le ?_ h16w
    norm_num
  refine ⟨y, z, w, le_max_left _ _, h16w, hz₀, lt_trans one_lt_two hz₄, hz₆,
    le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_, ?_⟩
  · have hlogwz : log w / b ≤ log z := by
      have htmp : exp (log w / b) ≤ exp (log z) := by
        simpa [Real.exp_log hz₀] using hzw
      exact Real.exp_le_exp.mp htmp
    refine (div_le_iff₀ (Real.log_pos (lt_trans one_lt_two hz₄))).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hb).mp hlogwz
  · have h₁ : C₂' ≤ ⌈w⌉₊ := by
      have h₁r : (C₂' : ℝ) ≤ ⌈w⌉₊ := by
        exact le_trans (le_max_right _ _) (le_trans hC₂w (Nat.le_ceil w))
      exact_mod_cast h₁r
    refine le_trans (htail' ⌈w⌉₊ h₁ z hz₇) ?_
    have hlogceil : C₁ * log (log ⌊z⌋₊) / c ≤ log (⌈w⌉₊ / 4) := by
      rw [← Real.exp_le_exp, Real.exp_log (lt_trans zero_lt_one h0w')]
      calc
        exp (C₁ * log (log ⌊z⌋₊) / c) = w / 4 := by
          dsimp [w]
          field_simp
        _ ≤ ⌈w⌉₊ / 4 := by
          exact div_le_div_of_nonneg_right (Nat.le_ceil w) zero_le_four
    have hnum : C₁ * log (log ⌊z⌋₊) / log (⌈w⌉₊ / 4) ≤ c := by
      refine (div_le_iff₀ (Real.log_pos h0w')).2 ?_
      have hmul := mul_le_mul_of_nonneg_left hlogceil hc.le
      calc
        C₁ * log (log ⌊z⌋₊) = c * (C₁ * log (log ⌊z⌋₊) / c) := by
          field_simp [hc.ne']
        _ ≤ c * log (⌈w⌉₊ / 4) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hnum

lemma filter_div (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            2 / (1 / (5 * D * 2) * D) ≤ y ∧
              2 / (1 / (5 * D * 2)) ≤ y ∧
                ∀ᶠ N in (atTop : Filter ℕ),
                  ∀ A ⊆ range N,
                    ((A.filter fun n =>
                          ¬ ∃ d₁ d₂ : ℕ,
                              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                      ℝ) ≤
                      (N : ℝ) / (5 * D) := by
  rcases sieve_lemma_prec' with ⟨C, c, h0C, h0c, hsieve⟩
  have haux1 : 0 < (1 / (10 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  have haux2 : 0 < (1 / (20 * D)) / C := by
    refine div_pos ?_ h0C
    rw [one_div_pos]
    refine mul_pos ?_ hD
    norm_num
  rw [Filter.eventually_atTop] at hsieve
  rcases hsieve with ⟨T, hsieve⟩
  rcases
      (filter_div_aux (2 / (1 / (5 * D * 2) * D)) ((1 / (10 * D)) / C) ((1 / (20 * D)) / C)
          (2 / (1 / (5 * D * 2))) haux1 haux2) with
    ⟨y, z, w, h2y, h16w, h0z, h1z, hyz, hDy, hDy', hwzD', hzsum⟩
  have hwzD : C * (log w / log z) ≤ 1 / (10 * D) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_div_iff₀ h0C).mp hwzD'
  have h2w : 2 ≤ w := by
    refine le_trans ?_ h16w
    norm_num
  have h1y : 1 ≤ y := le_trans one_le_two h2y
  have h0zc : (0 : ℝ) < ⌊z⌋₊ := by
    exact_mod_cast Nat.floor_pos.mpr (le_of_lt h1z)
  refine ⟨y, z, h1y, hyz, h0z, hDy, hDy', ?_⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((T : ℝ) * ⌊z⌋₊))
    , tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop
          ((((Icc ⌈w⌉₊ ⌊z⌋₊).filter Nat.Prime).sum
              (fun x => C * (log y / log (x / 4) * 1))) *
            (20 * D)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((4 : ℝ) * ⌊z⌋₊ / c + log ⌊z⌋₊))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (z / c))
    , eventually_ge_atTop T ] with N h0N hTzN hweirdN hlogN1 hlogN2 hlarge
  intro A hA
  have hAcard :
      ((A.filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ) ≤
        (((range N).filter fun n =>
              ¬ ∃ d₁ d₂ : ℕ,
                  d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
          ℝ) := by
    norm_num
    exact Finset.card_le_card (Finset.filter_subset_filter _ hA)
  refine le_trans hAcard ?_
  have hz' : z ≤ c * log (N : ℝ) := by
    rw [div_le_iff₀ h0c] at hlogN2
    simpa [mul_comm] using hlogN2
  let X :=
    (range N).filter fun n =>
      ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p
  let Y :=
    fun m =>
      (range N).filter fun n =>
        m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p
  have hXbound : (X.card : ℝ) ≤ C * (log w / log z) * N := by
    exact hsieve N hlarge w z h2w h1z hz'
  have hYlocbound :
      ∀ m : ℕ,
        16 ≤ m →
          (m : ℝ) / 4 ≤ c * log ⌈(N : ℝ) / m⌉₊ →
            T ≤ ⌈(N : ℝ) / m⌉₊ →
              ((Y m).card : ℝ) ≤ C * (log y / log ((m : ℝ) / 4)) * (N / m + 1) := by
    intro m h16m hm hTm
    have h0m : 0 < m := by
      refine lt_of_lt_of_le ?_ h16m
      norm_num
    have h0m' : (0 : ℝ) < m := by exact_mod_cast h0m
    have h1m' : 1 < (m : ℝ) / 4 := by
      have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast h16m
      nlinarith
    have hcoeff_nonneg : 0 ≤ C * (log y / log ((m : ℝ) / 4)) := by
      refine mul_nonneg h0C.le ?_
      refine div_nonneg ?_ (Real.log_pos h1m').le
      exact Real.log_nonneg (le_trans one_le_two h2y)
    have hcard :
        (Y m).card ≤
          ((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card := by
      refine
        Finset.card_le_card_of_injOn
          (fun i => i / m)
          ?_
          ?_
      · intro n hn
        change n ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hn
        change
          n / m ∈
            (range ⌈(N : ℝ) / m⌉₊).filter
              (fun n => ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p)
        rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
        refine ⟨?_, ?_⟩
        · rw [Nat.lt_ceil, Nat.cast_div hn.2.1 (by exact_mod_cast h0m.ne')]
          exact div_lt_div_of_pos_right (by exact_mod_cast hn.1) h0m'
        · intro p hp hpnm
          rcases hn.2.2 p hp (dvd_trans hpnm (Nat.div_dvd_of_dvd hn.2.1)) with hpy | hmp
          · exact Or.inl hpy
          · right
            rw [div_lt_iff₀ zero_lt_four]
            simpa [mul_comm] using hmp
      · intro a ha b hb hab
        change a ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at ha
        change b ∈ (range N).filter
          (fun n => m ∣ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) < 4 * p) at hb
        rw [Finset.mem_filter] at ha hb
        have ha' : a = (a / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m ha.2.1).1 rfl
        have hb' : b = (b / m) * m := by
          exact (Nat.div_eq_iff_eq_mul_left h0m hb.2.1).1 rfl
        rw [ha', hb']
        exact congrArg (fun t => t * m) hab
    have hsieve' :
        (((range ⌈(N : ℝ) / m⌉₊).filter fun n =>
              ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ (m : ℝ) / 4 < p).card :
          ℝ) ≤
          C * (log y / log ((m : ℝ) / 4)) * ⌈(N : ℝ) / m⌉₊ := by
      exact hsieve ⌈(N : ℝ) / m⌉₊ hTm y ((m : ℝ) / 4) h2y h1m' hm
    refine (Nat.cast_le.2 hcard).trans ?_
    have hceil : (⌈(N : ℝ) / m⌉₊ : ℝ) ≤ N / m + 1 := by
      exact le_of_lt (Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) / m by positivity))
    exact hsieve'.trans (mul_le_mul_of_nonneg_left hceil hcoeff_nonneg)
  let Y' := ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r).biUnion fun p => Y p
  have hcover :
      ((range N).filter fun n =>
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z) ⊆ X ∪ Y' := by
    intro n hn
    by_cases hXin : n ∈ X
    · exact Finset.mem_union.mpr (Or.inl hXin)
    · have hn_range : n ∈ range N := (Finset.mem_filter.mp hn).1
      have hn_forbid :
          ¬ ∃ d₁ d₂ : ℕ,
              d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z :=
        (Finset.mem_filter.mp hn).2
      have hnotX :
          ¬ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < w ∨ z < p := by
        intro hprop
        exact hXin (Finset.mem_filter.mpr ⟨hn_range, hprop⟩)
      rw [Finset.mem_union, Finset.mem_biUnion]
      right
      rw [not_forall] at hnotX
      rcases hnotX with ⟨p, hp⟩
      rw [Classical.not_imp, Classical.not_imp, not_or, not_lt, not_lt] at hp
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, hp.1⟩
        · exact Nat.ceil_le.mpr hp.2.2.1
        · exact (Nat.le_floor_iff' hp.1.ne_zero).mpr hp.2.2.2
      · rw [Finset.mem_filter]
        refine ⟨hn_range, hp.2.1, ?_⟩
        intro q hq hqn
        by_cases hqy : y ≤ q
        · right
          have hp4q : (p : ℝ) < 4 * q := by
            by_contra hp4q
            have h4qp : 4 * q ≤ p := by exact_mod_cast not_lt.mp hp4q
            exact hn_forbid ⟨q, p, hqn, hp.2.1, hqy, h4qp, hp.2.2.2⟩
          exact hp4q
        · left
          exact lt_of_not_ge hqy
  calc
    ((((range N).filter fun n =>
            ¬ ∃ d₁ d₂ : ℕ,
                d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
        ℝ)) ≤ ((X ∪ Y').card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
    _ ≤ (X.card : ℝ) + (Y'.card : ℝ) := by
      exact_mod_cast Finset.card_union_le X Y'
    _ ≤ C * (log w / log z) * N + (Y'.card : ℝ) := by
      rw [add_le_add_iff_right]
      exact hXbound
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => ((Y p).card : ℝ))) := by
      rw [add_le_add_iff_left]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤
        (C * (log w / log z) * N +
          Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
            (fun p => C * (log y / log (p / 4)) * (N / p + 1))) := by
      rw [add_le_add_iff_left]
      refine Finset.sum_le_sum ?_
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have h16p : 16 ≤ p := by
        have h16ceil : 16 ≤ ⌈w⌉₊ := by
          have h16ceilR : (16 : ℝ) ≤ ⌈w⌉₊ := le_trans h16w (Nat.le_ceil w)
          exact_mod_cast h16ceilR
        exact le_trans h16ceil hp.1.1
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos hp.2
      refine hYlocbound p h16p ?_ ?_
      · have hp_le_floor : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hp.1.2
        have hfloorlog_div : (4 : ℝ) * ⌊z⌋₊ / c ≤ log ((N : ℝ) / ⌊z⌋₊) := by
          rw [Real.log_div h0N.ne' h0zc.ne', le_sub_iff_add_le]
          exact hlogN1
        have hfloorlog : (4 : ℝ) * ⌊z⌋₊ ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          rw [div_le_iff₀ h0c] at hfloorlog_div
          simpa [mul_comm, mul_left_comm, mul_assoc] using hfloorlog_div
        have hfloor_le : (⌊z⌋₊ : ℝ) ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hfloor_nonneg : (0 : ℝ) ≤ ⌊z⌋₊ := by positivity
          nlinarith
        have hp4_le : (p : ℝ) / 4 ≤ c * log ((N : ℝ) / ⌊z⌋₊) := by
          have hp4_le_floor : (p : ℝ) / 4 ≤ ⌊z⌋₊ := by
            nlinarith
          exact le_trans hp4_le_floor hfloor_le
        have hquot : (N : ℝ) / ⌊z⌋₊ ≤ (N : ℝ) / p := by
          exact div_le_div_of_nonneg_left h0N.le hp_pos hp_le_floor
        have hlogquot : log ((N : ℝ) / ⌊z⌋₊) ≤ log ((N : ℝ) / p) := by
          exact Real.log_le_log (div_pos h0N h0zc) hquot
        have hlogceil : log ((N : ℝ) / p) ≤ log ⌈(N : ℝ) / p⌉₊ := by
          refine Real.log_le_log (div_pos h0N hp_pos) ?_
          exact Nat.le_ceil _
        exact le_trans hp4_le (mul_le_mul_of_nonneg_left (le_trans hlogquot hlogceil) h0c.le)
      · rw [← Nat.cast_le (α := ℝ)]
        refine le_trans ?_ (Nat.le_ceil _)
        by_cases h0T : (0 : ℝ) < T
        · rw [le_div_iff₀ hp_pos]
          refine le_trans ?_ hTzN
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hp.1.2) h0T.le
        · exact (le_of_not_gt h0T).trans (by positivity)
    _ ≤ (N : ℝ) / (10 * D) + (N : ℝ) / (10 * D) := by
      refine add_le_add ?_ ?_
      · have htmp := mul_le_mul_of_nonneg_right hwzD h0N.le
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      · simp_rw [mul_assoc, mul_add]
        rw [Finset.sum_add_distrib]
        have hsum20 :
            Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * (N / p)) +
              Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                (fun p => C * (log y / log (p / 4)) * 1) ≤
              (N : ℝ) / (20 * D) + (N : ℝ) / (20 * D) := by
          refine add_le_add ?_ ?_
          · have hzsumC :
                C *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => log y / (log (p / 4) * p)) ≤
                  1 / (20 * D) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using (le_div_iff₀ h0C).mp hzsum
            have hEq :
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
              calc
                Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => C * (log y / log (p / 4)) * (N / p)) =
                  Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                    (fun p => (N : ℝ) * (C * (log y / (log (p / 4) * p)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      have hp0 : p ≠ 0 := (Nat.Prime.pos (Finset.mem_filter.mp hp).2).ne'
                      field_simp [hp0]
                _ = (N : ℝ) *
                    Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                      (fun p => C * (log y / (log (p / 4) * p))) := by
                      rw [Finset.mul_sum]
                _ = (N : ℝ) *
                    (C *
                      Finset.sum ((Icc ⌈w⌉₊ ⌊z⌋₊).filter fun r : ℕ => Nat.Prime r)
                        (fun p => log y / (log (p / 4) * p))) := by
                      rw [← Finset.mul_sum]
            rw [hEq]
            have htmp := mul_le_mul_of_nonneg_left hzsumC h0N.le
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
          · refine (le_div_iff₀ ?_).2 ?_
            · refine mul_pos ?_ hD
              norm_num
            · simpa [mul_assoc] using hweirdN
        have hsum10 : (N : ℝ) / (D * 20) + (N : ℝ) / (D * 20) = (N : ℝ) / (D * 10) := by
          field_simp [hD.ne']
          ring
        simpa [mul_assoc, mul_left_comm, mul_comm, hsum10] using hsum20
    _ = (N : ℝ) / (5 * D) := by
      field_simp [hD.ne']
      ring

lemma turan_primes_estimate :
    ∃ C : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - log (log (N : ℝ))) ^ 2) ≤
          C * (N : ℝ) * log (log (N : ℝ)) := by
  rcases sum_prime_counting with ⟨C1, hsum⟩
  rcases sum_prime_counting_sq with ⟨C2, hsumsq⟩
  let C : ℝ := C2 + 2 * C1
  refine ⟨C, ?_⟩
  filter_upwards
    [ hsum
    , hsumsq
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlargeSum hlargeSumSq hlargeN
  have hcardIcc : (Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  let L : ℝ := log (log (N : ℝ))
  let S1 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ)
  let S2 : ℝ := (Icc 1 N).sum fun x => (ω x : ℝ) ^ 2
  have hsum' : (N : ℝ) * L - C1 * N ≤ S1 := by
    simpa [L, S1, mul_assoc, mul_left_comm, mul_comm] using hlargeSum
  have hsumsq' : S2 ≤ (N : ℝ) * L ^ 2 + C2 * N * L := by
    simpa [L, S2, mul_assoc, mul_left_comm, mul_comm] using hlargeSumSq
  have hmul :
      (2 * L) * ((N : ℝ) * L - C1 * N) ≤ (2 * L) * S1 := by
    refine mul_le_mul_of_nonneg_left hsum' ?_
    positivity
  have hexpand :
      (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) =
        S2 - 2 * L * S1 + (N : ℝ) * L ^ 2 := by
    simp_rw [sub_sq, S1, S2]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcardIcc]
    ring
  rw [hexpand]
  dsimp [C]
  nlinarith

lemma filter_regular (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun n : ℕ =>
              n ≠ 0 ∧
                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
          ℝ) ≤
          (N : ℝ) / D := by
  rcases turan_primes_estimate with ⟨C, hturan⟩
  have h100 : (0 : ℝ) < 1 / 100 := by norm_num
  filter_upwards
    [ hturan
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (C / (1 / 100) / (1 / D * (1 / 100))))
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)) ] with
      N hNturan hlargeN hlargeN2 hlargeN3
  intro A hA
  by_contra h
  rw [not_le] at h
  let A' :=
    A.filter fun n : ℕ =>
      n ≠ 0 ∧
        ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
            (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  let L : ℝ := log (log (N : ℝ))
  let ε : ℝ := (1 / 100 : ℝ) * L
  have hcontr : C * (N : ℝ) * L < (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
    have hstep1 : C * (N : ℝ) * L ≤ ((N : ℝ) / D) * ε ^ 2 := by
      have htmp := hlargeN2
      dsimp [L] at htmp
      have hpos1 : 0 < (1 / D * (1 / 100 : ℝ)) := by positivity
      have hpos2 : 0 < (1 / 100 : ℝ) := by norm_num
      rw [div_le_iff₀ hpos1, div_le_iff₀ hpos2] at htmp
      have hNL_nonneg : 0 ≤ (N : ℝ) * L := mul_nonneg hlargeN3.le hlargeN.le
      calc
        C * (N : ℝ) * L = C * ((N : ℝ) * L) := by ring
        _ ≤ (L * (1 / D * (1 / 100 : ℝ)) * (1 / 100 : ℝ)) * ((N : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_right htmp hNL_nonneg
        _ = ((N : ℝ) / D) * ε ^ 2 := by
          dsimp [ε]
          ring
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos <| by
      dsimp [ε]
      refine mul_pos ?_ hlargeN
      norm_num
    have hstep2 : ((N : ℝ) / D) * ε ^ 2 < (A'.card : ℝ) * ε ^ 2 :=
      mul_lt_mul_of_pos_right h hεsq
    have hstep3 : (A'.card : ℝ) * ε ^ 2 ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      calc
        (A'.card : ℝ) * ε ^ 2 = A'.sum (fun _ => ε ^ 2) := by simp [nsmul_eq_mul]
        _ ≤ A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rw [Finset.mem_filter] at hn
          by_cases hlow : ((99 : ℝ) / 100) * L ≤ ω n
          · have hhigh : 2 * L < (ω n : ℝ) := by
              apply lt_of_not_ge
              intro hupper
              exact hn.2.2 ⟨by simpa using hlow, by simpa using hupper⟩
            have hεle : ε ≤ (ω n : ℝ) - L := by
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ (ω n : ℝ) - L := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ ((ω n : ℝ) - L) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            simpa using hsquare
          · have hεle : ε ≤ L - ω n := by
              have hlow' : (ω n : ℝ) < (99 : ℝ) / 100 * L := lt_of_not_ge hlow
              dsimp [ε]
              nlinarith
            have hε0 : 0 ≤ ε := by
              dsimp [ε]
              positivity
            have hdiff0 : 0 ≤ L - ω n := le_trans hε0 hεle
            have hsquare : ε ^ 2 ≤ (L - ω n) ^ 2 := by
              nlinarith [hεle, hε0, hdiff0]
            have hsame : (L - ω n) ^ 2 = ((ω n : ℝ) - L) ^ 2 := by ring
            exact hsame ▸ hsquare
    have hstep4 : A'.sum (fun n => ((ω n : ℝ) - L) ^ 2) ≤
        (Icc 1 N).sum (fun n => ((ω n : ℝ) - L) ^ 2) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
          intro hbad
          rw [hbad, Finset.mem_filter] at hm
          exact hm.2.1 rfl
        · have htempy := hA ((Finset.filter_subset _ _) hm)
          rw [Finset.mem_range] at htempy
          exact le_of_lt htempy
      · intro n _ _
        exact sq_nonneg _
    exact lt_of_lt_of_le (lt_of_le_of_lt hstep1 hstep2) (le_trans hstep3 hstep4)
  exact (not_lt_of_ge (by simpa [L] using hNturan)) hcontr

lemma log_helper (y : ℝ) (h : 0 < y) (h'' : y ≤ 1 / 2) : -2 * y ≤ log (1 - y) := by
  have hy1 : y < 1 := lt_of_le_of_lt h'' one_half_lt_one
  have hloginv : log ((1 - y)⁻¹) ≤ 2 * y := by
    refine le_trans (Real.log_le_sub_one_of_pos (inv_pos.2 (sub_pos.2 hy1))) ?_
    have hyinv_le : (1 - y)⁻¹ ≤ 2 := by
      have htwo : 2 ≤ 1 / y := by
        rw [le_div_iff₀ h]
        linarith
      simpa [one_div, inv_inv, h.ne'] using sub_one_div_inv_le_two (a := 1 / y) htwo
    have hy_nonneg : 0 ≤ y := h.le
    have hy1_ne : 1 - y ≠ 0 := sub_ne_zero.mpr (ne_of_lt hy1).symm
    calc
      (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by
        field_simp [hy1_ne]
        ring_nf
      _ ≤ y * 2 := mul_le_mul_of_nonneg_left hyinv_le hy_nonneg
      _ = 2 * y := by ring
  have hneglog : -log (1 - y) ≤ 2 * y := by
    simpa [Real.log_inv] using hloginv
  linarith

lemma nat_floor_real_le_floor {M : ℝ} {N : ℕ} (h : M ≤ N) :
    ⌊M⌋₊ ≤ ⌊(N : ℝ)⌋₊ := by
  simpa using (Nat.floor_le_of_le h)

lemma diff_mertens_sum_hlarge4 {N : ℕ}
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (hlarge5 : ‖log ((log ∘ Nat.cast) N)‖ ≤ (1 / 8 : ℝ) * ‖((log ∘ Nat.cast) N) ^ (1 : ℝ)‖) :
    log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
  have hmain : log (log (N : ℝ)) ≤ (1 / 8 : ℝ) * log (N : ℝ) := by
    simpa [Function.comp, Real.norm_eq_abs, abs_of_pos hloglogN, abs_of_nonneg hlogN.le,
      Real.rpow_one] using hlarge5
  nlinarith

lemma diff_mertens_sum_hsumM {N : ℕ} {b c M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (hlogN : 0 < log (N : ℝ))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹) :
    log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
        c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
      (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro hN
      subst hN
      norm_num at hlogN)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hfactor_pos : 0 < (1 : ℝ) - 8 / log (log (N : ℝ)) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  have hlogM :
      log M = (1 - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    rw [hM, Real.log_rpow h0N]
  have hloglogM :
      log (log M) = log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) := by
    rw [hlogM, Real.log_mul hfactor_pos.ne' hlogN.ne']
  have hlower := sub_le_of_abs_sub_le_left hlarge2'
  rw [hloglogM, hlogM] at hlower
  exact hlower

lemma diff_mertens_sum_hstep1 {N : ℕ} {M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h8loglogN : 8 < log (log (N : ℝ))) :
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) ≤
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
  let A : Finset ℕ := (Finset.Icc 1 N).filter IsPrimePow
  let B : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow
  let S : Finset ℕ :=
    (range N).filter fun r : ℕ =>
      IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)
  have hN0 : N ≠ 0 := by
    intro hN
    subst hN
    norm_num at h8loglogN
  have h1leN : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hMleN : M ≤ (N : ℝ) := by
    rw [hM]
    calc
      (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ (N : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le h1leN ?_
        have hnonneg : 0 ≤ 8 / log (log (N : ℝ)) := by positivity
        linarith
      _ = (N : ℝ) := by simp
  have hfloorMleN : ⌊M⌋₊ ≤ N := by
    simpa [Nat.floor_natCast] using nat_floor_real_le_floor (M := M) (N := N) hMleN
  have hBsubA : B ⊆ A := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqpp⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqM⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans hqM hfloorMleN⟩, hqpp⟩
  have hSsub : S ⊆ A \ B := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqrange, hqprop⟩
    rcases hqprop with ⟨hqpp, hMq⟩
    have hqA : q ∈ A := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨
        Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt hqpp.pos, le_of_lt (Finset.mem_range.mp hqrange)⟩,
        hqpp
      ⟩
    have hqnotB : q ∉ B := by
      intro hqB
      rcases Finset.mem_filter.mp hqB with ⟨hqIcc, _hqpp⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hq1, hqM⟩
      have hfloorMltq : ⌊M⌋₊ < q := by
        exact (Nat.floor_lt' (Nat.ne_of_gt hqpp.pos)).2 (by simpa [hM] using hMq)
      exact not_lt_of_ge hqM hfloorMltq
    exact Finset.mem_sdiff.mpr ⟨hqA, hqnotB⟩
  have hsum_le : S.sum (fun q => (q : ℝ)⁻¹) ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub ?_
    intro q _hq _hnot
    have hq_nonneg : 0 ≤ (q : ℝ) := by
      exact_mod_cast Nat.zero_le q
    exact inv_nonneg.2 hq_nonneg
  calc
    ((range N).filter fun (r : ℕ) =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
        (fun q => (q : ℝ)⁻¹) = S.sum (fun q => (q : ℝ)⁻¹) := by
          rfl
    _ ≤ (A \ B).sum (fun q => (q : ℝ)⁻¹) := hsum_le
    _ = A.sum (fun q => (q : ℝ)⁻¹) - B.sum (fun q => (q : ℝ)⁻¹) := by
      exact Finset.sum_sdiff_eq_sub hBsubA
    _ = (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
      rfl

lemma diff_mertens_sum_hstep4 {N : ℕ} {b c C : ℝ}
    (hC : C = c / 2 + 16)
    (h0c : 0 < c)
    (hlogN : 0 < log (N : ℝ))
    (hloglogN : 0 < log (log (N : ℝ)))
    (h8loglogN : 8 < log (log (N : ℝ)))
    (h16loglogN : 16 ≤ log (log (N : ℝ)))
    (hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ)) :
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
      C / log (log (N : ℝ)) := by
  let L : ℝ := log (log (N : ℝ))
  let X : ℝ := log (N : ℝ)
  have hL : 0 < L := hloglogN
  have hX : 0 < X := hlogN
  have hy_pos : 0 < 8 / L := by
    positivity
  have hy_le : 8 / L ≤ (1 / 2 : ℝ) := by
    field_simp [hL.ne']
    nlinarith
  have hone_sub_pos : 0 < 1 - 8 / L := by
    rw [sub_pos]
    exact (div_lt_one hL).2 h8loglogN
  have hlog_term : -log (1 - 8 / L) ≤ 16 / L := by
    have htmp := log_helper (y := 8 / L) hy_pos hy_le
    have htmp' : -log (1 - 8 / L) ≤ 2 * (8 / L) := by
      linarith
    convert htmp' using 1
    ring_nf
  have hX_ge : 8 * L ≤ X := by
    nlinarith
  have hterm1 : c * X⁻¹ ≤ c / (8 * L) := by
    rw [div_eq_mul_inv]
    have h_inv : X⁻¹ ≤ (8 * L)⁻¹ := by
      have h8L_pos : 0 < 8 * L := by positivity
      simpa [one_div] using one_div_le_one_div_of_le h8L_pos hX_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hprod_ge : 4 * L ≤ (1 - 8 / L) * X := by
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 8 / L := by
      nlinarith
    have hhalfX : 4 * L ≤ (1 / 2 : ℝ) * X := by
      nlinarith
    have hhalfX_le : (1 / 2 : ℝ) * X ≤ (1 - 8 / L) * X := by
      exact mul_le_mul_of_nonneg_right hhalf_le hX.le
    exact le_trans hhalfX hhalfX_le
  have hterm2 : c * (((1 - 8 / L) * X)⁻¹) ≤ c / (4 * L) := by
    rw [div_eq_mul_inv]
    have hprod_pos : 0 < (1 - 8 / L) * X := mul_pos hone_sub_pos hX
    have h4L_pos : 0 < 4 * L := by positivity
    have h_inv : ((1 - 8 / L) * X)⁻¹ ≤ (4 * L)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le h4L_pos hprod_ge
    refine mul_le_mul_of_nonneg_left ?_ h0c.le
    exact h_inv
  have hsum_c : c * X⁻¹ + c * (((1 - 8 / L) * X)⁻¹) ≤ c / (2 * L) := by
    have hsum' := add_le_add hterm1 hterm2
    refine hsum'.trans ?_
    field_simp [hL.ne']
    nlinarith
  have hleft :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
        c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := by
    simp [L, X, abs_of_pos hX, abs_of_pos (mul_pos hone_sub_pos hX)]
    ring
  have hright : c / (2 * L) + 16 / L = C / log (log (N : ℝ)) := by
    change c / (2 * L) + 16 / L = C / L
    rw [hC]
    field_simp [hL.ne']
  calc
    c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
        (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) =
      c * X⁻¹ - log (1 - 8 / L) + c * (((1 - 8 / L) * X)⁻¹) := hleft
    _ ≤ c / (2 * L) + 16 / L := by
      nlinarith [hsum_c, hlog_term]
    _ = C / log (log (N : ℝ)) := hright

lemma diff_mertens_sum :
    ∃ c : ℝ,
      ∀ᶠ N in (atTop : Filter ℕ),
        ((range N).filter fun (r : ℕ) =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (q : ℝ)⁻¹) ≤
          c / log (log (N : ℝ)) := by
  obtain ⟨b, hppr'⟩ := prime_power_reciprocal
  obtain ⟨c, h0c, hppr⟩ := hppr'.exists_pos
  let C : ℝ := c / 2 + 16
  refine ⟨C, ?_⟩
  have haux :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
      (show 0 < (1 : ℝ) / 8 by norm_num)
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually hppr.bound
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually hppr.bound
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (8 : ℝ))
    , (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (16 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N h0N hlarge1 hlarge2 hlogN hloglogN h8loglogN h16loglogN hlarge5
  let M : ℝ := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  have hlarge4 : log (log (N : ℝ)) * 4 ≤ (1 / 2 : ℝ) * log (N : ℝ) := by
    exact diff_mertens_sum_hlarge4 hlogN hloglogN hlarge5
  have hlarge1' :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹ := by
    simpa [Nat.floor_natCast, norm_inv, norm_eq_abs] using hlarge1
  have hlarge2' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹ := by
    simpa [M, norm_inv, norm_eq_abs] using hlarge2
  have hsumN :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) := by
    have htmp := sub_le_of_abs_sub_le_right hlarge1'
    linarith
  have hsumM :
      log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
          c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹ ≤
        (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hsumM (N := N) (b := b) (c := c) (M := M) rfl hlogN h8loglogN hlarge2'
  have hstep1 :
      ((range N).filter fun (r : ℕ) =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
          (fun q => (q : ℝ)⁻¹) ≤
        (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact diff_mertens_sum_hstep1 (N := N) (M := M) rfl h8loglogN
  have hstep2 :
      (((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) := by
    exact sub_le_sub_right hsumN _
  have hstep3 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) ≤
        c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) := by
    exact sub_le_sub_left hsumM _
  have hstep4 :
      c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
          (log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) + b -
            c * |(1 - 8 / log (log (N : ℝ))) * log (N : ℝ)|⁻¹) ≤
        C / log (log (N : ℝ)) := by
    exact
      diff_mertens_sum_hstep4 (N := N) (b := b) (c := c) (C := C) rfl h0c hlogN hloglogN
        h8loglogN h16loglogN hlarge4
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

lemma filter_smooth (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∀ A ⊆ range N,
        ((A.filter fun (n : ℕ) =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) ≤
          (N : ℝ) / D := by
  obtain ⟨c, hdiff⟩ := diff_mertens_sum
  filter_upwards [hdiff,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (D * 2)),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (0 : ℝ)),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (c / (1 / (2 * D)))),
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_gt_atTop (0 : ℝ))] with
    N hdiff' hlarge1 hlarge2 hlarge3 hlarge4 hlarge5
  intro A hA
  let A' := A.erase 0
  have hlocal : ∀ q ∈ range N, 1 ≤ q → (A'.filter fun n => q ∣ n).card ≤ N / q := by
    intro q hq h1q
    calc
      (A'.filter fun n => q ∣ n).card ≤ ((Icc 1 N).filter fun n => q ∣ n).card := by
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        refine ⟨?_, hn.2⟩
        have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
        have hnN := hA hnA
        rw [Finset.mem_range] at hnN
        rw [Finset.mem_Icc]
        refine ⟨?_, le_of_lt hnN⟩
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1)
      _ = N / q := count_multiples h1q
  have hlocal' : ∀ q ∈ range N, 1 ≤ q → ((A'.filter fun n => q ∣ n).card : ℝ) ≤ (N : ℝ) / q := by
    intro q hq h1q
    exact le_trans (by exact_mod_cast hlocal q hq h1q) Nat.cast_div_le
  calc
    ((A.filter fun n =>
        ∃ q : ℕ,
          IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
        ℝ) ≤
        (((A'.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card :
          ℝ) + 1) := by
      exact_mod_cast (show
        (A.filter fun n =>
            ∃ q : ℕ,
              IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n).card ≤
          (A'.filter fun n =>
              ∃ q : ℕ,
                IsPrimePow q ∧
                  (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                  q ∣ n).card + 1 by
        rw [show A' = A.erase 0 by rfl, filter_erase]
        refine le_trans (Finset.card_le_card (Finset.insert_erase_subset 0 _)) ?_
        exact Finset.card_insert_le _ _)
    _ ≤
        (((range N).filter fun r : ℕ =>
              IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => ((A'.filter fun n => q ∣ n).card : ℝ))) + 1 := by
      rw [add_le_add_iff_right]
      have hdecomp :
          A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n) ⊆
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).biUnion
              (fun q => A'.filter fun n => q ∣ n) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_biUnion]
        rcases hn.2 with ⟨q, hqpp, hqlarge, hqdiv⟩
        refine ⟨q, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, hqpp, hqlarge⟩
          rw [Finset.mem_range]
          have hnA : n ∈ A := (Finset.mem_erase.mp hn.1).2
          have hnN := hA hnA
          rw [Finset.mem_range] at hnN
          refine lt_of_le_of_lt ?_ hnN
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn.1).1) hqdiv
        · rw [Finset.mem_filter]
          exact ⟨hn.1, hqdiv⟩
      have hcard :
          (A'.filter
              (fun n =>
                ∃ q : ℕ,
                  IsPrimePow q ∧
                    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                    q ∣ n)).card ≤
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (A'.filter fun n => q ∣ n).card)) := by
        refine (Finset.card_le_card hdecomp).trans ?_
        simpa using (Finset.card_biUnion_le (s := (range N).filter fun r : ℕ =>
          IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ))
          (t := fun q => A'.filter fun n => q ∣ n))
      exact_mod_cast hcard
    _ ≤
        (N : ℝ) *
            (((range N).filter fun r : ℕ =>
                  IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (1 : ℝ) / q)) +
          1 := by
      rw [add_le_add_iff_right, mul_sum]
      refine Finset.sum_le_sum ?_
      intro q hq
      rw [← div_eq_mul_one_div]
      rw [Finset.mem_filter] at hq
      exact hlocal' q hq.1 (le_of_lt (IsPrimePow.one_lt hq.2.1))
    _ ≤ (N : ℝ) / (2 * D) + 1 := by
      rw [add_le_add_iff_right, div_eq_mul_one_div (N : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc
        ((range N).filter fun r : ℕ =>
            IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
            (fun q => (1 : ℝ) / q) =
            ((range N).filter fun r : ℕ =>
                IsPrimePow r ∧ (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (r : ℝ)).sum
              (fun q => (q : ℝ)⁻¹) := by
          simp_rw [one_div]
        _ ≤ c / log (log (N : ℝ)) := hdiff'
        _ ≤ 1 / (2 * D) := by
          simp_rw [one_div]
          have htmp := (div_le_iff₀ (by
            rw [one_div_pos]
            exact mul_pos zero_lt_two hD)).mp hlarge4
          have htmp' : c ≤ (1 / (2 * D)) * log (log (N : ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
          simpa [Function.comp, one_div, mul_comm, mul_left_comm, mul_assoc] using
            (div_le_iff₀ hlarge5).2 htmp'
    _ ≤ (N : ℝ) / D := by
      have hhalf : 1 ≤ (N : ℝ) / (2 * D) := by
        rw [one_le_div (by positivity)]
        simpa [mul_comm] using hlarge2
      calc
        (N : ℝ) / (2 * D) + 1 ≤ (N : ℝ) / (2 * D) + (N : ℝ) / (2 * D) := by
          simpa [add_comm] using add_le_add_left hhalf ((N : ℝ) / (2 * D))
        _ = (N : ℝ) / D := by
          field_simp [hD.ne']
          ring

lemma nat_le_cast_real_sub {m n : ℕ} : (n : ℝ) - (m : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
  by_cases h : m < n
  · rw [Nat.cast_sub (le_of_lt h)]
  · have h' : n ≤ m := le_of_not_gt h
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast h')

lemma final_large_N (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        4 * y + 4 ≤ z ∧
          0 < z ∧
            Filter.Eventually
              (fun N : ℕ =>
                (0 : ℝ) < N ∧
                  (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 < (N : ℝ) / (5 * D) ∧
                    (∀ A ⊆ range N,
                      ((A.filter fun (n : ℕ) =>
                            ∃ q : ℕ,
                              IsPrimePow q ∧
                                (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧
                                  q ∣ n).card :
                        ℝ) ≤
                        (N : ℝ) / (5 * D)) ∧
                      (∀ A ⊆ range N,
                        ((A.filter fun n : ℕ =>
                              n ≠ 0 ∧
                                ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                                    (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))).card :
                          ℝ) ≤
                          (N : ℝ) / (5 * D)) ∧
                        (∀ A ⊆ range N,
                          ((A.filter fun n =>
                                ¬ ∃ d₁ d₂ : ℕ,
                                    d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
                                      4 * d₁ ≤ d₂ ∧ (d₂ : ℝ) ≤ z).card :
                            ℝ) ≤
                            (N : ℝ) / (5 * D)) ∧
                          z ≤ log (N : ℝ) ^ ((1 : ℝ) / 500) ∧
                            (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤
                              (N : ℝ) / (5 * D))
              atTop := by
  rcases filter_div D hD with ⟨y, z, h1y, hyz, h0z, hChelp, hChelp', hfilterdiv⟩
  refine ⟨y, z, h1y, hyz, h0z, ?_⟩
  have h5D : 0 < 5 * D := by
    refine mul_pos ?_ hD
    norm_num
  have h1pos : (0 : ℝ) < 1 := by norm_num
  filter_upwards
    [ eventually_gt_atTop 0
    , filter_smooth (5 * D) h5D
    , filter_regular (5 * D) h5D
    , hfilterdiv
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * (5 * D)))
    , ((tendsto_pow_rec_log_log_at_top h1pos).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (5 * D * 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (z ^ (500 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((1 / (1 / (5 * D) / 2)) ^ (200 : ℝ))) ] with
      N hlarge hsmooth hregular hdiv hlarge2 hlarge3 hlarge4 hlarge5 hlarge6
  dsimp at hlarge3 hlarge4 hlarge5 hlarge6
  refine ⟨by exact_mod_cast hlarge, ?_, hsmooth, hregular, hdiv, ?_, ?_⟩
  · calc
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + 1 <
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 := by
            have hlt : 1 < ((N : ℝ) / (5 * D)) / 2 := by
              refine (_root_.lt_div_iff₀ zero_lt_two).2 ?_
              refine (_root_.lt_div_iff₀ h5D).2 ?_
              simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge2
            nlinarith
      _ ≤ (N : ℝ) / (5 * D) := by
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
        have hpow :
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) ≤ ((N : ℝ) / (5 * D)) / 2 := by
          have hfacpos : 0 < 5 * D * 2 := by positivity
          have hrecip :
              (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) ≤ 1 / (5 * D * 2) := by
            rw [Real.rpow_neg hNpos.le, ← one_div]
            exact one_div_le_one_div_of_le hfacpos hlarge3
          calc
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) =
                (N : ℝ) ^ (-(1 / log (log (N : ℝ)))) * (N : ℝ) := by
                  rw [sub_eq_add_neg, add_comm, Real.rpow_add_one hNpos.ne']
            _ ≤ (1 / (5 * D * 2)) * (N : ℝ) := by
              exact mul_le_mul_of_nonneg_right hrecip (show 0 ≤ (N : ℝ) by exact hNpos.le)
            _ = ((N : ℝ) / (5 * D)) / 2 := by
              field_simp [hD.ne']
        calc
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ))) + ((N : ℝ) / (5 * D)) / 2 ≤
              ((N : ℝ) / (5 * D)) / 2 + ((N : ℝ) / (5 * D)) / 2 := by
                exact add_le_add hpow le_rfl
          _ = (N : ℝ) / (5 * D) := by ring
  · have h500 : (0 : ℝ) < 500 := by norm_num
    rw [← Real.rpow_le_rpow_iff _ _ h500, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
    · exact hlarge4
    · norm_num
    · exact le_of_lt hlarge5
    · exact le_of_lt h0z
    · exact Real.rpow_nonneg (le_of_lt hlarge5) _
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast hlarge
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one h1y
    have hterm1 : 2 / y ≤ (1 / (5 * D)) / 2 := by
      have hterm1' : 2 / y ≤ 1 / (5 * D * 2) := by
        refine (_root_.div_le_iff₀ hypos).2 ?_
        have hc : 2 ≤ y * (1 / (5 * D * 2)) := by
          exact (_root_.div_le_iff₀ (show 0 < 1 / (5 * D * 2) by positivity)).1 hChelp'
        simpa [mul_comm] using hc
      calc
        2 / y ≤ 1 / (5 * D * 2) := hterm1'
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hterm2 : log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (1 / (5 * D)) / 2 := by
      rw [Real.rpow_neg hlarge5.le, ← one_div]
      have hroot :
          1 / (1 / (5 * D) / 2) ≤ log (N : ℝ) ^ ((1 : ℝ) / 200) := by
        have h200 : (0 : ℝ) < 200 := by norm_num
        rw [← Real.rpow_le_rpow_iff _ _ h200, ← Real.rpow_mul, one_div_mul_cancel, Real.rpow_one]
        · exact hlarge6
        · norm_num
        · exact le_of_lt hlarge5
        · rw [one_div_nonneg]
          refine div_nonneg ?_ zero_le_two
          rw [one_div_nonneg]
          refine mul_nonneg ?_ hD.le
          norm_num
        · exact Real.rpow_nonneg hlarge5.le _
      have hrootpos : 0 < 1 / (1 / (5 * D) / 2) := by positivity
      calc
        1 / (log (N : ℝ) ^ ((1 : ℝ) / 200)) ≤ 1 / (1 / (1 / (5 * D) / 2)) :=
            one_div_le_one_div_of_le hrootpos hroot
        _ = (1 / (5 * D)) / 2 := by
          field_simp [hD.ne']
    have hsum : 2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ 1 / (5 * D) := by
      calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤
            (1 / (5 * D)) / 2 + (1 / (5 * D)) / 2 := by
              exact add_le_add hterm1 hterm2
        _ = 1 / (5 * D) := by rw [add_halves]
    calc
      (2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200))) * (N : ℝ) ≤ (1 / (5 * D)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsum hNpos.le
      _ = (N : ℝ) / (5 * D) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]

theorem unit_fractions_upper_density' (D : ℝ) (hD : 0 < D) :
    ∃ y z : ℝ,
      1 ≤ y ∧
        0 ≤ z ∧
          ∀ A : Set ℕ,
            upper_density A > 1 / D →
              ∃ d ∈ Icc ⌈y⌉₊ ⌊z⌋₊,
                ∃ S : Finset ℕ,
                  (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 / d := by
  rcases final_large_N D hD with ⟨y, z, h1y, hyz, h0z, hfinal⟩
  refine ⟨y, z, h1y, le_of_lt h0z, ?_⟩
  intro A hA
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hfinal.and technical_prop)
  obtain ⟨N, hNN0, hAcard⟩ := frequently_atTop'.1 (frequently_nat_of hA) N0
  have hlargeN := (hN0 N (le_of_lt hNN0)).1
  have htech := (hN0 N (le_of_lt hNN0)).2
  dsimp at hlargeN
  have hzN := hlargeN.2.2.2.2.2.1
  have hyN := hlargeN.2.2.2.2.2.2
  let A' := (range N).filter fun n : ℕ => n ∈ A
  have hA'card : (N : ℝ) / D < A'.card := by
    have hNpos : 0 < (N : ℝ) := hlargeN.1
    have hAcard' : 1 / D < A'.card / N := by
      simpa [A'] using hAcard
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (lt_div_iff₀ hNpos).1 hAcard'
  let M := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  let A0 := A'.filter fun n : ℕ => (n : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))
  have hA0card : (A0.card : ℝ) < (N : ℝ) / (5 * D) := by
    calc
      (A0.card : ℝ) ≤ ((range ⌈(N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))⌉₊).card : ℝ) := by
        norm_cast
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_range, Nat.lt_ceil]
        exact hn.2
      _ < (N : ℝ) / (5 * D) := by
        rw [Finset.card_range]
        refine lt_trans (Nat.ceil_lt_add_one ?_) hlargeN.2.1
        exact Real.rpow_nonneg (le_of_lt hlargeN.1) _
  let A1 := A'.filter fun n ↦ ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  have hA1card : (A1.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A2 := A'.filter fun n ↦
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  have hA2card : (A2.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A3 := A'.filter fun n ↦
    ¬ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)
  have hA3card : (A3.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.2.1 A' ?_
    exact Finset.filter_subset _ _
  let A'' := A' \ (A0 ∪ A1 ∪ A2 ∪ A3)
  have hUnionSub : A0 ∪ A1 ∪ A2 ∪ A3 ⊆ A' := by
    intro n hn
    rcases Finset.mem_union.mp hn with h012 | h3
    · rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · exact (Finset.mem_filter.mp h0).1
        · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · exact (Finset.mem_filter.mp h3).1
  have hA''card : (N : ℝ) / (5 * D) ≤ A''.card := by
    let x : ℝ := (N : ℝ) / (5 * D)
    have hA'card5 : 5 * x < A'.card := by
      dsimp [x]
      have hx : 5 * ((N : ℝ) / (5 * D)) = (N : ℝ) / D := by
        field_simp [hD.ne']
      rw [hx]
      exact hA'card
    have hsum4 : ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ 4 * x := by
      calc
        ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ (A0.card + A1.card + A2.card + A3.card : ℕ) := by
          norm_cast
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          exact Finset.card_union_le _ _
        _ ≤ 4 * x := by
          have hA0le : (A0.card : ℝ) ≤ x := le_of_lt hA0card
          dsimp [x] at hA0le hA1card hA2card hA3card ⊢
          push_cast
          nlinarith
    calc
      x ≤ (A'.card : ℝ) - (x + x + (x + x)) := by
        have hx4 : x + x + (x + x) = 4 * x := by ring
        rw [hx4]
        nlinarith
      _ ≤ (A'.card : ℝ) - (A0 ∪ A1 ∪ A2 ∪ A3).card := by
        dsimp [x] at hsum4 ⊢
        linarith
      _ ≤ A''.card := by
        dsimp [A'']
        rw [Finset.card_sdiff_of_subset hUnionSub]
        exact nat_le_cast_real_sub
  clear hA'card hA0card hA1card hA2card hA3card
  have hnotA0 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A0 := by
    intro n hn hn0
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl hn0
  have hnotA1 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A1 := by
    intro n hn hn1
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr hn1
  have hnotA2 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A2 := by
    intro n hn hn2
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hn2
  have hnotA3 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A3 := by
    intro n hn hn3
    exact (Finset.mem_sdiff.mp hn).2 <| Finset.mem_union.mpr <| Or.inr hn3
  have h0A'' : 0 ∉ A'' := by
    intro hz
    exact hnotA0 hz <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, by
      simpa using (Real.rpow_pos_of_pos hlargeN.1 (1 - (1 : ℝ) / log (log (N : ℝ))))⟩
  have hA''N : ∀ n ∈ A'', n < N := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1.1
  have hstep : ∃ S ⊆ A'', ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
    refine htech A'' ?_ y z h1y hyz hzN h0A'' ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range]
      exact lt_of_lt_of_le (hA''N n hn) (Nat.le_succ N)
    · intro n hn
      rw [← not_lt]
      intro hbad
      exact hnotA0 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (A''.card : ℝ) / N := by
          rw [le_div_iff₀ hlargeN.1]
          refine le_trans hyN hA''card
        _ ≤ rec_sum A'' := by
          rw [Finset.card_eq_sum_ones, rec_sum]
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnle : (n : ℝ) ≤ N := by
            exact_mod_cast Nat.le_of_lt (hA''N n hn)
          have hn0 : n ≠ 0 := by
            intro hzn
            exact h0A'' (hzn ▸ hn)
          have hnpos : 0 < (n : ℝ) := by
            exact Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
          exact one_div_le_one_div_of_le hnpos hnle
    · intro n hn
      by_contra hbad
      exact hnotA3 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · intro n hn
      rw [is_smooth]
      intro q hq hqn
      rw [← not_lt]
      intro hbad
      exact hnotA1 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, ⟨q, hq, hbad, hqn⟩⟩
    · rw [arith_regular]
      intro n hn
      by_contra hbad
      have hn0 : n ≠ 0 := by
        intro hz
        exact h0A'' (hz ▸ hn)
      exact hnotA2 hn <| Finset.mem_filter.mpr ⟨by
        rw [Finset.mem_sdiff] at hn
        exact hn.1, ⟨hn0, hbad⟩⟩
  clear htech
  rcases hstep with ⟨S, hS, d, hyd, hdz, hrecd⟩
  refine ⟨d, ?_, S, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact Nat.ceil_le.mpr hyd
    · exact (Nat.le_floor_iff (le_of_lt h0z)).mpr hdz
  · intro s hs
    have hs' := hS hs
    rw [Finset.mem_sdiff, Finset.mem_filter] at hs'
    exact hs'.1.2
  · rw [rec_sum] at hrecd
    exact hrecd

theorem unit_fractions_upper_density (A : Set ℕ) (hA : upper_density A > 0) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 := by
  classical
  let D := 2 / upper_density A
  have hD : 0 < D := div_pos zero_lt_two hA
  have hDA : 1 / D < upper_density A := by
    rw [show D = 2 / upper_density A by rfl, one_div_div]
    exact half_lt_self hA
  rcases unit_fractions_upper_density' D hD with ⟨y, z, h1y, h0z, hupp⟩
  let M := (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).sum fun d => d
  let good_set : Finset (Finset ℕ) → Prop := fun S =>
    (∀ s ∈ S, (s : Set ℕ) ⊆ A) ∧
      (S : Set (Finset ℕ)).PairwiseDisjoint id ∧
        ∀ s, ∃ d : ℕ, s ∈ S → y ≤ d ∧ (d : ℝ) ≤ z ∧ rec_sum s = 1 / d
  let P : ℕ → Prop := fun k => ∃ S : Finset (Finset ℕ), S.card = k ∧ good_set S
  let k : ℕ := Nat.findGreatest P (M + 1)
  have P0 : P 0 := by
    refine ⟨∅, ?_⟩
    simp [good_set]
  have Pk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk
  choose d' hd'₁ hd'₂ hd'₃ using hS₃
  let t : ℕ → ℕ := fun d => (S.filter fun s => d' s = d).card
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d
  · obtain ⟨d, d_pos, ht⟩ := h
    obtain ⟨T', hT', hd₂⟩ := Finset.exists_subset_card_eq (s := S.filter fun s => d' s = d) ht
    have hT'S : T' ⊆ S := hT'.trans (Finset.filter_subset _ _)
    refine ⟨T'.biUnion id, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_biUnion.mp hn with ⟨s, hsT, hns⟩
      exact hS₁ s (hT'S hsT) hns
    · change rec_sum (T'.biUnion id) = 1
      rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S)]
      have hsumT : T'.sum rec_sum = T'.sum (fun _ : Finset ℕ => (1 : ℚ) / d) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [(Finset.mem_filter.mp (hT' hi)).2] using (hd'₃ i (hT'S hi))
      rw [hsumT, Finset.sum_const, hd₂, nsmul_eq_mul]
      field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast d_pos.ne']
  · exfalso
    have hcount : ∀ d : ℕ, 0 < d → t d < d := by
      intro d hd
      by_contra hdt
      exact h ⟨d, hd, le_of_not_gt hdt⟩
    let A' : Set ℕ := A \ (S.biUnion id : Set ℕ)
    have hDA' : 1 / D < upper_density A' := by
      have hpres : upper_density A = upper_density A' := by
        dsimp [A']
        simpa using (upper_density_preserved (A := A) (S := S.biUnion id))
      rw [← hpres]
      exact hDA
    specialize hupp A' hDA'
    rcases hupp with ⟨d, hd, S', hS'₁, hS'₂⟩
    have hd' : y ≤ d ∧ (d : ℝ) ≤ z := by
      rw [Finset.mem_Icc] at hd
      refine ⟨?_, ?_⟩
      · exact le_trans (Nat.le_ceil y) (by exact_mod_cast hd.1)
      · exact le_trans (by exact_mod_cast hd.2) (Nat.floor_le h0z)
    have h1d : 1 ≤ d := by
      have : (1 : ℝ) ≤ d := le_trans h1y hd'.1
      exact_mod_cast this
    have hAS : Disjoint A' (S.biUnion id : Set ℕ) := by
      dsimp [A']
      simpa using (disjoint_sdiff_self_left : Disjoint (A \ (S.biUnion id : Set ℕ))
        (S.biUnion id : Set ℕ))
    have hS'A : (S' : Set ℕ) ⊆ A := by
      intro n hn
      exact (hS'₁ hn).1
    have hS'' : ∀ s ∈ S, Disjoint S' s := by
      intro s hs
      rw [← Finset.disjoint_coe]
      exact Disjoint.mono hS'₁ (Finset.subset_biUnion_of_mem id hs) hAS
    have hS''' : S' ∉ S := by
      intro hs
      exact (nonempty_of_rec_sum_recip h1d hS'₂).ne_empty (disjoint_self.mp (hS'' _ hs))
    have hPk1 : P (k + 1) := by
      refine ⟨insert S' S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hS''', hk]
      · refine ⟨?_, ?_, ?_⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hS'A
          · exact hS₁ s hs
        · simpa [Set.pairwiseDisjoint_insert_of_notMem hS''', hS₂] using fun s hs =>
            hS'' _ hs
        · intro s
          rcases eq_or_ne s S' with rfl | hs
          · exact ⟨d, fun _ => ⟨hd'.1, hd'.2, hS'₂⟩⟩
          · refine ⟨d' s, fun hs' => ?_⟩
            have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs' hs
            exact ⟨hd'₁ _ hsS, hd'₂ _ hsS, hd'₃ _ hsS⟩
    have hk_bound : k + 1 ≤ M + 1 := by
      rw [← hk, add_le_add_iff_right]
      have hSdecomp :
          (Finset.Icc ⌈y⌉₊ ⌊z⌋₊).biUnion (fun d => S.filter fun s => d' s = d) = S := by
        refine Finset.biUnion_filter_eq_of_maps_to ?_
        intro n hn
        rw [Finset.mem_Icc]
        refine ⟨Nat.ceil_le.mpr (hd'₁ n hn), (Nat.le_floor_iff h0z).mpr (hd'₂ n hn)⟩
      rw [← hSdecomp]
      refine le_trans Finset.card_biUnion_le ?_
      refine Finset.sum_le_sum ?_
      intro d hd
      have hd' : d ∈ Finset.Icc ⌈y⌉₊ ⌊z⌋₊ := hd
      rw [Finset.mem_Icc, Nat.ceil_le] at hd'
      exact
        le_of_lt
          (hcount d (by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1y hd'.1))))
    have : k + 1 ≤ k := Nat.le_findGreatest hk_bound hPk1
    exact Nat.not_succ_le_self _ this

lemma rec_sum_union {A B : Finset ℕ} :
    (rec_sum (A ∪ B) : ℝ) ≤ rec_sum A + rec_sum B := by
  rw [← Rat.cast_add, Rat.cast_le, rec_sum, rec_sum, rec_sum, ← Finset.sum_union_inter,
    le_add_iff_nonneg_right, ← rec_sum]
  exact rec_sum_nonneg

lemma rec_sum_sdiff {A B : Finset ℕ} :
    (rec_sum A : ℝ) - rec_sum B ≤ rec_sum (A \ B) := by
  rw [← Rat.cast_sub, Rat.cast_le, tsub_le_iff_right,
    ← rec_sum_disjoint disjoint_sdiff_self_left]
  refine rec_sum_mono ?_
  rw [Finset.sdiff_union_self_eq_union]
  exact Finset.subset_union_left

lemma rec_sum_bUnion {I : Finset ℕ} (f : ℕ → Finset ℕ) :
    (rec_sum (I.biUnion f) : ℝ) ≤ I.sum (fun i => rec_sum (f i)) := by
  have hrat : rec_sum (I.biUnion f) ≤ I.sum (fun i => rec_sum (f i)) := by
    rw [rec_sum]
    exact sum_bUnion_le_sum_of_nonneg fun x hx => by
      exact div_nonneg zero_le_one (show 0 ≤ (x : ℚ) by exact_mod_cast Nat.zero_le x)
  exact_mod_cast hrat

lemma this_particular_tends_to :
    Tendsto (fun x : ℝ => x ^ (log (log (log x)) / log (log x))) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_pow_rec_log_log_at_top zero_lt_one)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop 0,
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)).eventually_ge_atTop 1]
      with x hx hx' hx''
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  have hmul := mul_le_mul_of_nonneg_right hx'' (one_div_nonneg.mpr hx')
  simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma Ioc_subset_Ioc_union_Ioc {a b c : ℕ} :
    Ioc a c ⊆ Ioc a b ∪ Ioc b c := by
  rw [← Finset.coe_subset, Finset.coe_union, Finset.coe_Ioc, Finset.coe_Ioc, Finset.coe_Ioc]
  exact Set.Ioc_subset_Ioc_union_Ioc

lemma bUnion_range_Ioc (N : ℕ) (f : ℕ → ℕ) :
    Ioc (f N) (f 0) ⊆ (range N).biUnion (fun i : ℕ => Ioc (f (i + 1)) (f i)) := by
  induction N with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert]
      have hsubset :
          Ioc (f (n + 1)) (f 0) ⊆ Ioc (f (n + 1)) (f n) ∪ Ioc (f n) (f 0) := by
        exact Ioc_subset_Ioc_union_Ioc
      exact subset_trans hsubset (Finset.union_subset_union Subset.rfl ih)

lemma this_fun_increasing_aux : StrictMonoOn (fun x : ℝ => exp x / x ^ 2) (Set.Ici 2) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 2) ?_ ?_
  · refine Real.continuous_exp.continuousOn.div (continuous_id.pow 2).continuousOn ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_two hx
    exact pow_ne_zero 2 hx0.ne'
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := lt_trans zero_lt_two hx
    change 0 < deriv (exp / fun x : ℝ => x ^ 2) x
    rw [deriv_div differentiableAt_exp (differentiableAt_pow 2) (pow_ne_zero 2 hx0.ne')]
    have hexp : deriv exp x = exp x := by
      exact congrFun Real.deriv_exp x
    have hpow : deriv (fun x : ℝ => x ^ 2) x = 2 * x := by
      calc
        deriv (fun x : ℝ => x ^ 2) x = (2 : ℝ) * x ^ (2 - 1) := by
          exact deriv_pow_field (𝕜 := ℝ) (x := x) 2
        _ = 2 * x := by simp
    rw [hexp, hpow, sq, ← mul_sub, ← sub_mul]
    exact div_pos (mul_pos (exp_pos _) (mul_pos (sub_pos_of_lt hx) hx0))
      (pow_pos (mul_pos hx0 hx0) 2)

lemma this_fun_increasing' :
    ∀ᶠ N in (atTop : Filter ℝ),
      ∀ M, N ≤ M → log N / log (log N) ^ 2 ≤ log M / log (log M) ^ 2 := by
  filter_upwards
      [ (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop 2
      , tendsto_log_atTop.eventually_gt_atTop 0
      , eventually_gt_atTop (0 : ℝ) ] with N hN hNl0 hN0 M hNM
  have hl : log N ≤ log M := log_le_log_of_le hN0 hNM
  have hll : log (log N) ≤ log (log M) := log_le_log_of_le hNl0 hl
  simpa [Function.comp, Real.exp_log hNl0, Real.exp_log (hNl0.trans_le hl)] using
    this_fun_increasing_aux.monotoneOn hN (le_trans hN hll) hll

lemma this_fun_increasing :
    ∃ C : ℝ,
      ∀ N M : ℕ,
        C ≤ N ∧ N ≤ M →
          log (N : ℝ) / (log (log (N : ℝ))) ^ 2 ≤
            log (M : ℝ) / (log (log (M : ℝ))) ^ 2 := by
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp this_fun_increasing'
  refine ⟨C, ?_⟩
  intro N M h
  exact hC N h.1 M (by exact_mod_cast h.2)

lemma harmonic_sum_bound_two' :
    ∀ᶠ N in (atTop : Filter ℝ),
      (range ⌈N⌉₊).sum (fun n => (1 : ℝ) / n) ≤ 2 * log N := by
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp harmonic_sum_bound_two
  filter_upwards [eventually_ge_atTop ((C : ℝ) + 1), eventually_gt_atTop (1 : ℝ)] with N hN h1N
  have hN' : (C : ℝ) ≤ N - 1 := by
    linarith
  have hCceil : C ≤ ⌈N - 1⌉₊ := by
    have haux : (C : ℝ) ≤ (⌈N - 1⌉₊ : ℝ) := le_trans hN' (Nat.le_ceil _)
    exact_mod_cast haux
  specialize hC ⌈N - 1⌉₊ hCceil
  calc
    (range ⌈N⌉₊).sum (fun n => (1 : ℝ) / n)
        ≤ (range (⌈N - 1⌉₊ + 1)).sum (fun n => (1 : ℝ) / n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            rw [Finset.mem_range] at hn ⊢
            exact lt_of_lt_of_le hn <| by
              refine Nat.ceil_le.mpr ?_
              calc
                N = (N - 1) + 1 := by ring
                _ ≤ (⌈N - 1⌉₊ : ℝ) + 1 := by
                  gcongr
                  exact Nat.le_ceil (N - 1)
                _ = ↑(⌈N - 1⌉₊ + 1) := by norm_num
          · intro n _ _
            exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    _ ≤ 2 * log (⌈N - 1⌉₊ : ℝ) := hC
    _ ≤ 2 * log N := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          refine log_le_log_of_le ?_ ?_
          · exact_mod_cast Nat.ceil_pos.mpr (sub_pos.mpr h1N)
          · have hceil_lt : (⌈N - 1⌉₊ : ℝ) < N := by
              linarith [Nat.ceil_lt_add_one (show 0 ≤ N - 1 by linarith)]
            exact hceil_lt.le

lemma harmonic_sum_bound' :
    ∃ C : ℝ,
      0 < C ∧
        ∀ N : ℝ,
          1 ≤ N → (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n) ≤ C * log (2 * N) := by
  obtain ⟨C₁, hharmonic⟩ := Filter.eventually_atTop.mp harmonic_sum_bound_two
  let C₁' : ℕ := max C₁ 2
  let I : Finset ℕ := Ico 1 C₁'
  let f : ℕ → ℝ := fun M => (Icc 1 M).sum (fun n => (1 : ℝ) / n)
  have hIne : I.Nonempty := by
    simpa [I] using
      (Finset.nonempty_Ico.mpr (lt_of_lt_of_le one_lt_two (le_max_right C₁ 2)) :
        (Ico 1 C₁').Nonempty)
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image I f hIne
  let C : ℝ := max 2 (f y / log 2)
  have h0C : 0 < C := lt_of_lt_of_le zero_lt_two (le_max_left _ _)
  refine ⟨C, h0C, ?_⟩
  intro N h1N
  have h0N : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have h1f : 1 ≤ ⌊N⌋₊ := by
    refine Nat.le_floor ?_
    exact_mod_cast h1N
  by_cases hcases : ⌊N⌋₊ < C₁
  · have hmem : ⌊N⌋₊ ∈ I := by
      simpa [I] using
        (show ⌊N⌋₊ ∈ Ico 1 C₁' from by
          rw [Finset.mem_Ico]
          exact ⟨h1f, lt_of_lt_of_le hcases (le_max_left C₁ 2)⟩)
    calc
      (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n)
          = f ⌊N⌋₊ := rfl
      _ ≤ f y := hmax _ hmem
      _ = (f y / log 2) * log 2 := by
            rw [div_mul_cancel₀ _]
            exact Real.log_ne_zero_of_pos_of_ne_one zero_lt_two (by norm_num)
      _ ≤ C * log 2 := by
            refine mul_le_mul_of_nonneg_right (le_max_right 2 (f y / log 2)) ?_
            exact (Real.log_pos one_lt_two).le
      _ ≤ C * (log 2 + log N) := by
            have hlogN : 0 ≤ log N := Real.log_nonneg h1N
            nlinarith [le_of_lt h0C, hlogN]
      _ = C * log (2 * N) := by
            rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) h0N.ne', mul_add]
  · have hcases' : C₁ ≤ ⌊N⌋₊ := Nat.le_of_not_gt hcases
    specialize hharmonic ⌊N⌋₊ hcases'
    calc
      (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n)
          ≤ (range (⌊N⌋₊ + 1)).sum (fun n => (1 : ℝ) / n) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro n hn
              rw [Finset.mem_Icc] at hn
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le hn.2
            · intro n _ _
              exact one_div_nonneg.mpr (Nat.cast_nonneg n)
      _ ≤ 2 * log ⌊N⌋₊ := by
            simpa using hharmonic
      _ ≤ C * log N := by
            have h2C : (2 : ℝ) ≤ C := le_max_left _ _
            have hfloor_le : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le h0N.le
            have hfloor_pos : 0 < (⌊N⌋₊ : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le zero_lt_one h1f)
            have hlogfloor_le : log ⌊N⌋₊ ≤ log N := log_le_log_of_le hfloor_pos hfloor_le
            have hlogfloor_nonneg : 0 ≤ log ⌊N⌋₊ := by
              exact Real.log_nonneg (by exact_mod_cast h1f)
            exact mul_le_mul h2C hlogfloor_le hlogfloor_nonneg (le_of_lt h0C)
      _ ≤ C * log (2 * N) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h0C)
            exact log_le_log_of_le h0N (by nlinarith)

lemma another_this_particular_tends_to :
    Tendsto (fun x : ℝ => log x / log (log x)) atTop atTop := by
  have h : Tendsto (fun x : ℝ => x / log x) atTop atTop := by
    simpa using tendsto_mul_add_div_pow_log_at_top (1 : ℝ) 0 1 zero_lt_one
  simpa using h.comp tendsto_log_atTop

lemma this_function_big_tends_to :
    Tendsto (fun x : ℝ => x ^ (log (log (log x)) / log (log x))) atTop atTop := by
  simpa using this_particular_tends_to

lemma now_last_large_N :
    Filter.Eventually
      (fun N : ℕ =>
        (198 : ℝ) / 199 * log (log (N : ℝ)) ≤
          log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ)))
      atTop := by
  filter_upwards
      [ ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (199 : ℝ))
      , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (0 : ℝ))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (0 : ℝ)) ] with
    N hlarge h0log h0log2 h0log3 h0log4
  have h0log2' : 0 < log (log (N : ℝ)) := by
    simpa using h0log2
  have hlarge' : (199 : ℝ) * log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) := by
    exact (_root_.le_div_iff₀ h0log3).mp hlarge
  have hsmall :
      log (log (log (N : ℝ))) ≤ (1 / 199 : ℝ) * log (log (N : ℝ)) := by
    nlinarith
  have hsub :
      log (log (log (N : ℝ))) - log (log (log (log (N : ℝ)))) ≤
        (1 / 199 : ℝ) * log (log (N : ℝ)) := by
    exact (sub_le_self _ (le_of_lt h0log4)).trans hsmall
  have hrewrite :
      log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ)) =
        log (log (N : ℝ)) -
          (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
    have hmul :
        log ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) =
          log (log (log (log (N : ℝ))) / log (log (N : ℝ))) + log (log (N : ℝ)) := by
      have hquot_ne : log (log (log (N : ℝ))) / log (log (N : ℝ)) ≠ 0 := by
        exact div_ne_zero (ne_of_gt h0log3) (ne_of_gt h0log2')
      simpa using Real.log_mul hquot_ne (ne_of_gt h0log)
    have hdiv :
        log (log (log (log (N : ℝ))) / log (log (N : ℝ))) =
          log (log (log (log (N : ℝ)))) - log (log (log (N : ℝ))) := by
      simpa using Real.log_div (ne_of_gt h0log3) (ne_of_gt h0log2')
    calc
      log (log (log (log (N : ℝ))) / log (log (N : ℝ)) * log (N : ℝ))
          = log (log (log (log (N : ℝ))) / log (log (N : ℝ))) + log (log (N : ℝ)) := by
              simpa using hmul
      _ = (log (log (log (log (N : ℝ)))) - log (log (log (N : ℝ)))) + log (log (N : ℝ)) := by
            rw [hdiv]
      _ = log (log (N : ℝ)) -
            (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
            ring
  have hfinal :
      (198 : ℝ) / 199 * log (log (N : ℝ)) ≤
        log (log (N : ℝ)) -
          (log (log (log (N : ℝ))) - log (log (log (log (N : ℝ))))) := by
    nlinarith
  rw [hrewrite]
  exact hfinal

lemma large_helper (c C : ℝ) (hc1 : c < 1) (h0C : 0 < C) :
    ∀ᶠ N in (atTop : Filter ℝ),
      log N ^ c < (log (log (log N)) / log (log N) * log N) * C := by
  have hc : 0 < -c + 1 := by
    rw [add_comm, ← sub_eq_add_neg]
    exact sub_pos.mpr hc1
  filter_upwards
      [ tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (0 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (log C⁻¹ / ((-c + 1) / 2)))
      , (another_this_particular_tends_to.comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (1 / ((-c + 1) / 2)))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (0 : ℝ))
      , ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_log_atTop).eventually
          (eventually_gt_atTop (1 : ℝ)) ] with
    N hN hN₁ hN₂ hN₃ hN₄ hN₅
  rw [← _root_.div_lt_iff₀ h0C, div_eq_mul_one_div, ← _root_.lt_div_iff₀' (show 0 < log N ^ c by
      exact Real.rpow_pos_of_pos hN _), div_eq_mul_one_div _ (log N ^ c), one_div, one_div,
    ← Real.rpow_neg hN.le c, mul_assoc, mul_comm (log N), ← Real.rpow_add_one hN.ne' (-c),
    div_eq_mul_one_div]
  transitivity (1 / log (log N)) * log N ^ (-c + 1)
  · rw [mul_comm, ← div_eq_mul_one_div]
    refine (_root_.lt_div_iff₀ hN₁).2 ?_
    refine (Real.log_lt_log_iff ?_ ?_).mp ?_
    · refine mul_pos ?_ hN₁
      rw [inv_pos]
      exact h0C
    · exact Real.rpow_pos_of_pos hN _
    rw [Real.log_rpow hN, Real.log_mul (inv_ne_zero h0C.ne') (ne_of_gt hN₁),
      ← add_halves (-c + 1), add_mul]
    refine add_lt_add ?_ ?_
    · exact (_root_.div_lt_iff₀' (show 0 < (-c + 1) / 2 by
          exact div_pos hc zero_lt_two)).mp hN₂
    · have haux : 1 < (((-c + 1) / 2) * log (log N)) / log (log (log N)) := by
        have : 1 < ((-c + 1) / 2) * (log (log N) / log (log (log N))) := by
          exact (_root_.div_lt_iff₀' (show 0 < (-c + 1) / 2 by
            exact div_pos hc zero_lt_two)).mp hN₃
        simpa [mul_div_assoc] using this
      exact (_root_.one_lt_div hN₄).mp haux
  · rw [mul_assoc]
    refine lt_mul_of_one_lt_left ?_ hN₅
    refine mul_pos ?_ ?_
    · rw [one_div_pos]
      exact hN₁
    · exact Real.rpow_pos_of_pos hN _

lemma the_last_large_N : ∀ C : ℝ, 0 < C →
    Filter.Eventually
      (fun N : ℕ =>
        log (N : ℝ) ^ ((3 : ℝ) / 4) ≤
            log (N : ℝ) * (log (log (log (N : ℝ))) / log (log (N : ℝ))) ∧
          ((⌈log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                (2 * log (log (N : ℝ)))⌉₊ : ℝ) *
              (2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
                C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) <
            (2 + 2 * C) * (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)))
      atTop := by
  intro C h0C
  have htemp' : ((3 : ℝ) / 4) < 1 := by norm_num
  have htemp₂ : ((251 : ℝ) / 500) < 1 := by norm_num
  have htemp₃ : ((1 : ℝ) / 500) < 1 := by norm_num
  have htemp₄ : (0 : ℝ) < 1 / 4 := by norm_num
  filter_upwards
      [ tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((3 : ℝ) / 4) (1 : ℝ) htemp' zero_lt_one)
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((1 : ℝ) / 500) ((1 : ℝ) / 4) htemp₃ htemp₄)
      , tendsto_natCast_atTop_atTop.eventually
          (large_helper ((251 : ℝ) / 500) ((1 : ℝ) / 2) htemp₂ one_half_pos)
      , ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (2 * (C * 1)))
      , tendsto_log_log_coe_at_top (eventually_ge_atTop (log 2 / (1 / 4 / 2)))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_gt_atTop (1 : ℝ))
      , (another_this_particular_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop (1 : ℝ))
      , ((another_this_particular_tends_to.comp tendsto_log_atTop).comp
            tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (8 : ℝ)) ] with
    N h1logN hlarge1 hlarge2 hlarge3 hweird h0loglogN hloglogN' hloglogN'' h1log3 hbig hbig₂
  have h0log3 : 0 < log (log (log (N : ℝ))) := lt_trans zero_lt_one h1log3
  have h0logN : 0 < log (N : ℝ) := lt_trans zero_lt_one h1logN
  have h0loglogNr : 0 < log (log (N : ℝ)) := by
    simpa using h0loglogN
  have hloglogN'_ineq : 2 * C < log (log (N : ℝ)) := by
    simpa using hloglogN'
  have hlarge₃ : 2 * log (log (N : ℝ)) ≤ log (N : ℝ) ^ ((1 : ℝ) / 4) := by
    refine
      (Real.log_le_log_iff (mul_pos zero_lt_two h0loglogNr) (Real.rpow_pos_of_pos h0logN _)).mp
        ?_
    rw [Real.log_rpow h0logN, Real.log_mul two_ne_zero h0loglogNr.ne', ← add_halves ((1 : ℝ) / 4),
      add_mul]
    have hpart1 : log 2 ≤ log (log (N : ℝ)) * ((1 : ℝ) / 8) := by
      have htmp : (8 : ℝ) * log 2 ≤ log (log (N : ℝ)) := by
        have hloglogN''_ineq : log 2 / ((1 / 4 : ℝ) / 2) ≤ log (log (N : ℝ)) := by
          simpa using hloglogN''
        nlinarith [hloglogN''_ineq]
      nlinarith
    have hpart2 : log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) * ((1 : ℝ) / 8) := by
      have htmp : (8 : ℝ) * log (log (log (N : ℝ))) ≤ log (log (N : ℝ)) := by
        exact (_root_.le_div_iff₀ h0log3).mp hbig₂
      nlinarith
    nlinarith
  refine ⟨?_, ?_⟩
  · simpa [mul_comm, mul_left_comm, mul_assoc] using le_of_lt hlarge1
  · transitivity
      (log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) + 1) *
        (2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
          C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ))
    · refine mul_lt_mul_of_pos_right ?_ ?_
      · exact Nat.ceil_lt_add_one <| by
          refine mul_nonneg ?_ ?_
          · refine Real.log_nonneg ?_
            exact hweird
          · exact mul_nonneg zero_le_two (le_of_lt h0loglogNr)
      · refine add_pos ?_ ?_
        · exact mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN _)
        · refine mul_pos ?_ h0logN
          refine mul_pos h0C ?_
          rw [one_div_pos]
          exact sq_pos_of_pos h0loglogN
    · rw [add_mul, mul_add, add_rotate, add_rotate, add_mul, add_mul]
      refine add_lt_add_of_lt_of_le ?_ ?_
      · have hsum5 :
            2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) +
                C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
          rw [← add_halves ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ))]
          refine add_lt_add ?_ ?_
          · rw [_root_.lt_div_iff₀ zero_lt_two, mul_comm, ← mul_assoc]
            norm_num
            rw [← _root_.lt_div_iff₀' zero_lt_four, div_eq_mul_one_div _ (4 : ℝ)]
            exact hlarge2
          · refine (_root_.lt_div_iff₀' zero_lt_two).2 ?_
            have hmain :
                2 * C < log (log (log (N : ℝ))) * log (log (N : ℝ)) := by
              exact lt_trans hloglogN'_ineq (lt_mul_of_one_lt_left h0loglogNr h1log3)
            have hscaled := mul_lt_mul_of_pos_right hmain (div_pos h0logN (sq_pos_of_pos h0loglogN))
            convert hscaled using 1 <;> field_simp [h0loglogNr.ne']
        have hsum6 :
            log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                (2 * log (log (N : ℝ)) *
                  (log (N : ℝ) ^ ((1 : ℝ) / 500) + log (N : ℝ) ^ ((1 : ℝ) / 500))) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
          transitivity
              log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                (2 * log (N : ℝ) ^ ((1 : ℝ) / 500))
          · have hfac :
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) <
                  log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) := by
              refine mul_lt_mul ?_ ?_ ?_ ?_
              · transitivity log (log (log (N : ℝ)))
                · refine Real.log_lt_log ?_ ?_
                  · exact div_pos h0loglogNr h0log3
                  · exact div_lt_self h0loglogNr h1log3
                · have hmid : log (log (log (N : ℝ))) < 2 * log (log (N : ℝ)) := by
                    transitivity log (log (N : ℝ))
                    · refine Real.log_lt_log h0loglogNr ?_
                      rw [← _root_.one_lt_div]
                      · exact hbig
                      · exact h0loglogNr
                    · exact lt_mul_of_one_lt_left h0loglogNr one_lt_two
                  exact lt_of_lt_of_le hmid hlarge₃
              · exact hlarge₃
              · exact mul_pos zero_lt_two h0loglogNr
              · exact Real.rpow_nonneg (le_of_lt h0logN) ((1 : ℝ) / 4)
            have hmul :
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) * (2 * log (log (N : ℝ))) *
                    (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) <
                  (log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4)) *
                    (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) :=
              mul_lt_mul_of_pos_right hfac
                (mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN ((1 : ℝ) / 500)))
            simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
          · have hlarge3' :
                2 * log (N : ℝ) ^ ((251 : ℝ) / 500) <
                  (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
              nlinarith [hlarge3]
            calc
              log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                  (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) =
                2 * log (N : ℝ) ^ ((251 : ℝ) / 500) := by
                  calc
                    log (N : ℝ) ^ ((1 : ℝ) / 4) * log (N : ℝ) ^ ((1 : ℝ) / 4) *
                        (2 * log (N : ℝ) ^ ((1 : ℝ) / 500)) =
                      2 *
                        (log (N : ℝ) ^ (((1 : ℝ) / 4) + (1 / 4)) *
                          log (N : ℝ) ^ ((1 : ℝ) / 500)) := by
                        rw [← Real.rpow_add h0logN]
                        ring
                    _ = 2 * log (N : ℝ) ^ ((((1 : ℝ) / 4) + (1 / 4)) + (1 / 500)) := by
                        rw [← Real.rpow_add h0logN]
                    _ = 2 * log (N : ℝ) ^ ((251 : ℝ) / 500) := by norm_num
              _ < (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := hlarge3'
        have hsum :
            2 * (log (N : ℝ) ^ ((1 : ℝ) / 500)) + C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) +
                log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
                  (2 * log (log (N : ℝ)) *
                    (log (N : ℝ) ^ ((1 : ℝ) / 500) + log (N : ℝ) ^ ((1 : ℝ) / 500))) <
              (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) +
                (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
              exact add_lt_add hsum5 hsum6
        convert hsum using 1 <;> ring_nf
      · have hy_nonneg :
            0 ≤ C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ) := by
          positivity
        have hlog_le :
            log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) ≤ log (log (log (N : ℝ))) := by
          refine Real.log_le_log ?_ ?_
          · exact div_pos h0loglogN h0log3
          · exact div_le_self (le_of_lt h0loglogN) (le_of_lt h1log3)
        calc
          log (log (log (N : ℝ)) / log (log (log (N : ℝ)))) *
              (2 * log (log (N : ℝ))) * (C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) ≤
            log (log (log (N : ℝ))) *
              (2 * log (log (N : ℝ))) * (C * (1 / log (log (N : ℝ)) ^ 2) * log (N : ℝ)) := by
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hlog_le
                  (mul_nonneg (mul_nonneg zero_le_two (le_of_lt h0loglogNr)) hy_nonneg)
          _ = 2 * C * (log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ) := by
            field_simp [h0loglogNr.ne']

lemma how_large_can_we_go (C : ℝ) (h0C : 0 < C) :
    ∀ᶠ N in (atTop : Filter ℝ),
      log N ^ ((1 : ℝ) / 1000) ≤ (log (log (log N)) / log (log N) * log N) * C := by
  have hsmall : ((1 : ℝ) / 1000) < 1 := by norm_num
  filter_upwards [large_helper ((1 : ℝ) / 1000) C hsmall h0C] with N hN
  exact le_of_lt hN

lemma crude_ps (p : ℕ → Prop) [DecidablePred p] (δ : ℝ) (Y : ℝ) (h0δ : 0 < δ)
    (h1Y : 1 ≤ Y) (N : ℕ)
    (h : ∀ X : ℝ, Y ≤ X ∧ X ≤ N →
      (((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p).card : ℝ) ≤ δ * X)
    (h2N : 2 ≤ N) :
    ((Icc ⌈Y⌉₊ N).filter p).sum (fun n => (1 : ℝ) / n) ≤
      (2 / log 2) * δ * log (N : ℝ) := by
  have h0Y : 0 < Y := lt_of_lt_of_le zero_lt_one h1Y
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_two h2N
  by_cases hYN : Y ≤ N
  · let f : ℕ → Finset ℕ := fun i =>
      (Ico ⌈2 ^ (i : ℝ) * Y⌉₊ ⌈2 * (2 ^ (i : ℝ) * Y)⌉₊).filter p
    let I : Finset ℕ := range (⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ + 1)
    have hcont : ((Icc ⌈Y⌉₊ N).filter p) ⊆ I.biUnion f := by
      intro n hn
      rw [Finset.mem_biUnion]
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : 0 < (n : ℝ) := by
        have hceilY : 0 < (⌈Y⌉₊ : ℝ) := by
          exact_mod_cast Nat.ceil_pos.mpr h0Y
        exact hceilY.trans_le (by exact_mod_cast hn.1.1)
      have haux : 0 < (n : ℝ) / Y := div_pos hn0 h0Y
      have haux' : 0 ≤ Real.logb 2 ((n : ℝ) / Y) := by
        refine Real.logb_nonneg one_lt_two ?_
        rw [one_le_div h0Y]
        exact le_trans (Nat.le_ceil Y) (by exact_mod_cast hn.1.1)
      let i : ℕ := ⌊Real.logb 2 ((n : ℝ) / Y)⌋₊
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        refine Nat.le_floor ?_
        refine le_trans (Nat.floor_le haux') ?_
        exact (Real.logb_le_logb one_lt_two haux (div_pos h0N h0Y)).2 <|
          div_le_div_of_nonneg_right (by exact_mod_cast hn.1.2) h0Y.le
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Ico]
          refine ⟨?_, ?_⟩
          · rw [Nat.ceil_le]
            have hi_le : (i : ℝ) ≤ Real.logb 2 ((n : ℝ) / Y) := Nat.floor_le haux'
            have hpow_le : (2 : ℝ) ^ (i : ℝ) ≤ (n : ℝ) / Y :=
              (Real.le_logb_iff_rpow_le one_lt_two haux).1 hi_le
            exact (_root_.le_div_iff₀ h0Y).mp hpow_le
          · refine Nat.lt_ceil.mpr ?_
            have hlogb_lt : Real.logb 2 ((n : ℝ) / Y) < ((i + 1 : ℕ) : ℝ) := by
              simpa [i] using Nat.lt_floor_add_one (Real.logb 2 ((n : ℝ) / Y))
            have hpow_lt : (n : ℝ) / Y < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) :=
              (Real.logb_lt_iff_lt_rpow one_lt_two haux).1 hlogb_lt
            have hupper' : (n : ℝ) < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y :=
              (_root_.div_lt_iff₀ h0Y).mp hpow_lt
            have heq : (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y = 2 * ((2 : ℝ) ^ (i : ℝ) * Y) := by
              rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ']
              ring
            calc
              (n : ℝ) < (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ)) * Y := hupper'
              _ = 2 * ((2 : ℝ) ^ (i : ℝ) * Y) := heq
        · exact hn.2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcont ?_) ?_
    · intro n _ _
      exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    refine le_trans (sum_bUnion_le_sum_of_nonneg ?_) ?_
    · intro n hn
      exact one_div_nonneg.mpr (Nat.cast_nonneg n)
    have hbound : ∀ i ∈ I, Finset.sum (f i) (fun n => (1 : ℝ) / n) ≤ δ := by
      intro x hx
      have hxy_pos : 0 < 2 ^ (x : ℝ) * Y := by
        exact mul_pos (Real.rpow_pos_of_pos zero_lt_two _) h0Y
      calc
        Finset.sum (f x) (fun n => (1 : ℝ) / n) ≤ ((f x).card : ℝ) * (1 / (2 ^ (x : ℝ) * Y)) := by
          refine sum_le_card_mul_real ?_
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Ico] at hn
          have hxy_le_n : 2 ^ (x : ℝ) * Y ≤ n := by
            exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn.1.1)
          exact one_div_le_one_div_of_le hxy_pos hxy_le_n
        _ ≤ (δ * (2 ^ (x : ℝ) * Y)) * (1 / (2 ^ (x : ℝ) * Y)) := by
          refine mul_le_mul_of_nonneg_right (h (2 ^ (x : ℝ) * Y) ?_) ?_
          · constructor
            · have hpow1 : (1 : ℝ) ≤ 2 ^ (x : ℝ) := by
                refine one_le_rpow one_le_two ?_
                exact_mod_cast Nat.zero_le x
              exact le_mul_of_one_le_left h0Y.le hpow1
            · rw [Finset.mem_range, Nat.lt_succ_iff] at hx
              have hxlog : (x : ℝ) ≤ Real.logb 2 ((N : ℝ) / Y) := by
                have hx' : (x : ℝ) ≤ ⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ := by
                  exact_mod_cast hx
                refine le_trans hx' ?_
                refine Nat.floor_le ?_
                refine Real.logb_nonneg one_lt_two ?_
                rw [one_le_div h0Y]
                exact hYN
              have hpow_le : (2 : ℝ) ^ (x : ℝ) ≤ (N : ℝ) / Y :=
                (Real.le_logb_iff_rpow_le one_lt_two (div_pos h0N h0Y)).1 hxlog
              exact (_root_.le_div_iff₀ h0Y).mp hpow_le
          · positivity
        _ = δ := by
          have hpow_ne : (2 : ℝ) ^ (x : ℝ) ≠ 0 := by positivity
          have hY_ne : Y ≠ 0 := ne_of_gt h0Y
          field_simp [hpow_ne, hY_ne]
    calc
      Finset.sum I (fun x => Finset.sum (f x) (fun n => (1 : ℝ) / n)) ≤
        Finset.sum I (fun _ => δ) := by
        exact Finset.sum_le_sum fun x hx => hbound x hx
      _ = I.card * δ := by simp [nsmul_eq_mul]
      _ ≤ ((2 / log 2) * log (N : ℝ)) * δ := by
        refine mul_le_mul_of_nonneg_right ?_ h0δ.le
        dsimp [I]
        rw [Finset.card_range]
        push_cast
        have hlogb_nonneg : 0 ≤ Real.logb 2 ((N : ℝ) / Y) := by
          refine Real.logb_nonneg one_lt_two ?_
          rw [one_le_div h0Y]
          exact hYN
        have hlogb_le : Real.logb 2 ((N : ℝ) / Y) ≤ Real.logb 2 (N : ℝ) := by
          exact Real.logb_le_logb_of_le one_lt_two (div_pos h0N h0Y) (div_le_self h0N.le h1Y)
        have hone_le : 1 ≤ Real.logb 2 (N : ℝ) := by
          rw [Real.logb, one_le_div (Real.log_pos one_lt_two)]
          exact log_le_log_of_le zero_lt_two (by exact_mod_cast h2N)
        calc
          (⌊Real.logb 2 ((N : ℝ) / Y)⌋₊ : ℝ) + 1 ≤ Real.logb 2 (N : ℝ) + 1 := by
            simpa [add_comm] using add_le_add_right ((Nat.floor_le hlogb_nonneg).trans hlogb_le) 1
          _ ≤ Real.logb 2 (N : ℝ) + Real.logb 2 (N : ℝ) := by linarith
          _ = (2 / log 2) * log (N : ℝ) := by
            rw [Real.logb, div_eq_mul_inv]
            ring
      _ = (2 / log 2) * δ * log (N : ℝ) := by ring
  · have hempty : Icc ⌈Y⌉₊ N = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact Nat.not_le.mp fun hceil => hYN (Nat.ceil_le.mp hceil)
    suffices hnonneg : (0 : ℝ) ≤ (2 / log 2) * δ * log (N : ℝ) by
      simpa [hempty] using hnonneg
    have hlogNnonneg : 0 ≤ log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (le_trans (show 1 ≤ 2 by norm_num) h2N))
    refine mul_nonneg ?_ hlogNnonneg
    refine mul_nonneg ?_ h0δ.le
    exact div_nonneg zero_le_two (le_of_lt (Real.log_pos one_lt_two))

set_option maxHeartbeats 800000 in
-- This proof needs a larger heartbeat budget because the eventuality/telescoping inequalities
-- trigger expensive normalization and `linarith` search near the end.
lemma harmonic_filter_reg :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n =>
                    n ≠ 0 ∧
                      ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
                          (ω n : ℝ) ≤ (3 : ℝ) / 2 * log (log (N : ℝ))))).sum
                (fun n => (1 : ℝ) / n) ≤
              C * log (N : ℝ) / log (log (N : ℝ)))
          atTop := by
  rcases turan_primes_estimate with ⟨C₁, hturan⟩
  rw [Filter.eventually_atTop] at hturan
  rcases hturan with ⟨C₂, hturan⟩
  let C₃ := max C₁ 1
  have h0C₃ : 0 < C₃ := by
    refine lt_of_lt_of_le zero_lt_one ?_
    exact le_max_right _ _
  let c₁ := C₃ * (4 / (1 / 200 : ℝ) ^ 2)
  have h0c₁ : 0 < c₁ := by
    dsimp [c₁]
    refine mul_pos h0C₃ ?_
    refine div_pos zero_lt_four ?_
    positivity
  let C := (c₁ / (198 / 199 : ℝ)) * (2 / log 2)
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos ?_ ?_
    · refine div_pos h0c₁ ?_
      norm_num
    · exact div_pos zero_lt_two (Real.log_pos one_lt_two)
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ eventually_ge_atTop 2
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((C₂ : ℝ) / 2))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop (log 4))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((2 : ℝ) ^ (100 : ℝ)))
    , now_last_large_N ] with
      N h2N hYlarge h1Y h0loglogN h4logN hbiglogN hweird
  let p := fun n : ℕ =>
    n ≠ 0 ∧
      ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
          (ω n : ℝ) ≤ (3 : ℝ) / 2 * log (log (N : ℝ)))
  let Y := (N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))
  let δ := c₁ / ((198 / 199 : ℝ) * log (log (N : ℝ)))
  have h0loglogN' : 0 < log (log (N : ℝ)) := by
    simpa using h0loglogN
  have h0N : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two h2N
  have h0logN : 0 < log (N : ℝ) := by
    refine lt_of_lt_of_le (Real.log_pos one_lt_four) h4logN
  have h0δ : 0 < δ := by
    dsimp [δ]
    refine div_pos h0c₁ ?_
    refine mul_pos ?_ h0loglogN'
    norm_num
  refine le_trans (crude_ps p δ Y h0δ (le_of_lt h1Y) N ?_ h2N) ?_
  · intro X hX
    have h1X : 1 ≤ X := le_trans (le_of_lt h1Y) hX.1
    let M := ⌈2 * X⌉₊
    have h0M : (0 : ℝ) < (M : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr <| by nlinarith [h1X]
    have hM' : (198 / 199 : ℝ) * log (log (N : ℝ)) ≤ log (log (M : ℝ)) := by
      transitivity log (log Y)
      · dsimp [Y]
        rw [Real.log_rpow h0N]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hweird
      · refine log_le_log_of_le ?_ ?_
        · refine Real.log_pos h1Y
        · refine log_le_log_of_le ?_ ?_
          · dsimp [Y]
            exact Real.rpow_pos_of_pos h0N _
          · refine le_trans hX.1 ?_
            dsimp [M]
            refine le_trans ?_ (Nat.le_ceil _)
            refine le_mul_of_one_le_left ?_ ?_
            · linarith
            · norm_num
    have h0loglogM : 0 < log (log (M : ℝ)) := by
      refine lt_of_lt_of_le ?_ hM'
      refine mul_pos ?_ h0loglogN'
      norm_num
    have hMX : (M : ℝ) ≤ 4 * X := by
      dsimp [M]
      refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
      · positivity
      · nlinarith
    have hM'' : log (log (M : ℝ)) ≤ (101 / 100 : ℝ) * log (log (N : ℝ)) := by
      have haux1 : 0 < log (4 * X) := by
        refine Real.log_pos ?_
        refine lt_of_lt_of_le one_lt_four ?_
        refine le_mul_of_one_le_right (show 0 ≤ (4 : ℝ) by positivity) h1X
      have haux2 : 0 < log (4 * (N : ℝ)) := by
        refine lt_of_lt_of_le haux1 ?_
        refine log_le_log_of_le ?_ ?_
        · refine mul_pos zero_lt_four ?_
          linarith
        · nlinarith [hX.2]
      transitivity log (log (4 * X))
      · refine log_le_log_of_le ?_ ?_
        · refine Real.log_pos ?_
          refine lt_of_lt_of_le one_lt_two ?_
          refine le_trans ?_ (Nat.le_ceil _)
          nlinarith
        · refine log_le_log_of_le h0M hMX
      transitivity log (log (4 * (N : ℝ)))
      · refine log_le_log_of_le haux1 ?_
        refine log_le_log_of_le ?_ ?_
        · refine mul_pos zero_lt_four ?_
          linarith
        · nlinarith [hX.2]
      · rw [← Real.log_rpow h0logN]
        refine log_le_log_of_le haux2 ?_
        transitivity (2 : ℝ) * log (N : ℝ)
        · rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h0N), two_mul]
          linarith
        · have hpow : (2 : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) := by
            have h100 : (0 : ℝ) < 100 := by norm_num
            rw [← Real.rpow_le_rpow_iff zero_le_two
                (show 0 ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) by positivity) h100]
            · rw [← Real.rpow_mul h0logN.le]
              rw [show ((1 : ℝ) / 100) * 100 = (1 : ℝ) by norm_num, Real.rpow_one]
              simpa using hbiglogN
          have hmul : 2 * log (N : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) := by
            exact mul_le_mul_of_nonneg_right hpow h0logN.le
          exact
            calc
              2 * log (N : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) := hmul
              _ = log (N : ℝ) ^ ((1 : ℝ) / 100) * log (N : ℝ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
              _ = log (N : ℝ) ^ (((1 : ℝ) / 100) + 1) := by
                rw [← Real.rpow_add h0logN]
              _ = log (N : ℝ) ^ ((101 : ℝ) / 100) := by
                rw [show ((1 : ℝ) / 100) + 1 = (101 : ℝ) / 100 by norm_num]
    have hlarge : C₂ ≤ M := by
      dsimp [M]
      rw [← Nat.cast_le (α := ℝ)]
      have hYlarge' : (C₂ : ℝ) / 2 ≤ Y := by
        simpa [Y] using hYlarge
      refine le_trans ?_ (Nat.le_ceil _)
      nlinarith [hYlarge', hX.1]
    have hδM : C₃ * 4 / (1 / 200 : ℝ) ^ 2 ≤ δ * log (log (M : ℝ)) := by
      dsimp [δ, c₁]
      rw [div_mul_eq_mul_div, ← mul_div, mul_div_assoc]
      refine le_mul_of_one_le_right h0c₁.le ?_
      rw [one_le_div]
      · exact hM'
      · refine mul_pos ?_ h0loglogN'
        norm_num
    have hsubset :
        ((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p) ⊆ ((Icc 1 M).filter p) := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnIco, hnp⟩
      rcases Finset.mem_Ico.mp hnIco with ⟨hnl, hnu⟩
      refine Finset.mem_filter.mpr ⟨?_, hnp⟩
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · exact le_trans (by exact_mod_cast (le_trans h1X (Nat.le_ceil X))) hnl
      · dsimp [M]
        exact le_of_lt hnu
    specialize hturan M hlarge
    by_contra h
    rw [not_le] at h
    have h' : δ * X < (((Icc 1 M).filter p).card : ℝ) := by
      exact lt_of_lt_of_le h (by exact_mod_cast Finset.card_le_card hsubset)
    rw [← not_lt] at hturan
    refine hturan ?_
    calc
      C₁ * (M : ℝ) * log (log (M : ℝ)) ≤ C₃ * (M : ℝ) * log (log (M : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h0loglogM.le
        exact mul_le_mul_of_nonneg_right (le_max_left C₁ (1 : ℝ)) h0M.le
      _ ≤ (δ * X) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
        let a : ℝ := 1 / 200
        have ha_nonneg : 0 ≤ a ^ 2 := by positivity
        have hδM' : C₃ * 4 ≤ (δ * log (log (M : ℝ))) * a ^ 2 := by
          have hmult := mul_le_mul_of_nonneg_right hδM ha_nonneg
          have ha_ne : a ^ 2 ≠ 0 := by positivity
          simpa [a, sq, div_eq_mul_inv, ha_ne, mul_assoc, mul_left_comm, mul_comm] using hmult
        have hdesired :
            C₃ * (4 * X) * log (log (M : ℝ)) ≤
              (δ * X) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
          have hmult := mul_le_mul_of_nonneg_right hδM'
            (show 0 ≤ X * log (log (M : ℝ)) by positivity)
          simpa [a, sq, mul_assoc, mul_left_comm, mul_comm] using hmult
        refine le_trans ?_ hdesired
        gcongr
      _ < ((((Icc 1 M).filter p).card : ℝ)) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) := by
        refine mul_lt_mul_of_pos_right h' ?_
        positivity
      _ ≤ ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
        have hconst :
            ((Icc 1 M).filter p).sum (fun _ => (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2)) ≤
              ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨_, hnP⟩
          dsimp [p] at hnP
          rw [not_and_or] at hnP
          rw [sq_le_sq, le_abs, abs_of_pos]
          · rcases hnP.2 with hn1 | hn2
            · right
              rw [neg_sub, le_sub_iff_add_le]
              rw [not_le] at hn1
              have hbound :
                  (99 / 100 : ℝ) * log (log (N : ℝ)) ≤
                    (199 / 200 : ℝ) * log (log (M : ℝ)) := by
                have htmp := mul_le_mul_of_nonneg_left hM' (show 0 ≤ (199 / 200 : ℝ) by norm_num)
                nlinarith
              have homega :
                  (ω n : ℝ) ≤ (199 / 200 : ℝ) * log (log (M : ℝ)) := by
                exact le_trans (le_of_lt hn1) hbound
              nlinarith
            · left
              rw [le_sub_iff_add_le, add_comm, ← one_add_mul]
              rw [not_le] at hn2
              refine le_trans ?_ (le_of_lt hn2)
              have hstep :
                  ((1 : ℝ) + 1 / 200) * log (log (M : ℝ)) ≤
                    ((1 : ℝ) + 1 / 200) * ((101 / 100 : ℝ) * log (log (N : ℝ))) := by
                gcongr
              have hcoef : ((1 : ℝ) + 1 / 200) * (101 / 100 : ℝ) ≤ (3 : ℝ) / 2 := by
                norm_num
              refine hstep.trans ?_
              exact (show
                  ((1 : ℝ) + 1 / 200) * ((101 / 100 : ℝ) * log (log (N : ℝ))) ≤
                    (3 : ℝ) / 2 * log (log (N : ℝ)) by
                  nlinarith)
          · positivity
        calc
          ((((Icc 1 M).filter p).card : ℝ)) * (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2) =
              ((Icc 1 M).filter p).sum (fun _ => (((1 / 200 : ℝ) * log (log (M : ℝ))) ^ 2)) := by
                simp [nsmul_eq_mul]
          _ ≤ ((Icc 1 M).filter p).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := hconst
      _ ≤ (Icc 1 M).sum (fun n => ((ω n : ℝ) - log (log (M : ℝ))) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset _ _
        · intro n _ _
          exact sq_nonneg _
  · have hEq :
        (2 / log 2) * δ * log (N : ℝ) = C * log (N : ℝ) / log (log (N : ℝ)) := by
      dsimp [C, δ]
      field_simp [h0loglogN'.ne', (Real.log_pos one_lt_two).ne']
    rw [hEq]

lemma harmonic_filter_div :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n =>
                    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧
                        (d : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 1000))).sum
                (fun n => (1 : ℝ) / n) ≤
              C * log (N : ℝ) / log (log (N : ℝ)))
          atTop := by
  rcases sieve_lemma_prec' with ⟨C₁, c₁, h0C₁, h0c₁, hsieve⟩
  rw [Filter.eventually_atTop] at hsieve
  rcases hsieve with ⟨C₂, hsieve⟩
  let c₂ := C₁ * (4 * (log 4 / ((1 : ℝ) / 1000)))
  have h0c₂ : 0 < c₂ := by
    dsimp [c₂]
    refine mul_pos h0C₁ ?_
    refine mul_pos zero_lt_four ?_
    exact div_pos (Real.log_pos one_lt_four) (by norm_num)
  let C := c₂ * (2 / log 2)
  have h0C : 0 < C := by
    dsimp [C]
    refine mul_pos h0c₂ ?_
    exact div_pos zero_lt_two (Real.log_pos one_lt_two)
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ eventually_ge_atTop 2
    , tendsto_natCast_atTop_atTop.eventually (how_large_can_we_go c₁ h0c₁)
    , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((C₂ : ℝ) / 2))
    , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)) ] with
      N h2N hNlarge h1logN hYlarge h1Y
  have h0N : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two h2N
  have h0loglogN : 0 < log (log (N : ℝ)) := Real.log_pos h1logN
  have h0logN : 0 < log (N : ℝ) := lt_trans zero_lt_one h1logN
  let Y := (N : ℝ) ^ (log (log (log (N : ℝ))) / log (log (N : ℝ)))
  let δ := c₂ / log (log (N : ℝ))
  have h0δ : 0 < δ := by
    dsimp [δ]
    exact div_pos h0c₂ h0loglogN
  let p := fun n =>
    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ log (N : ℝ) ^ ((1 : ℝ) / 1000)
  refine le_trans (crude_ps p δ Y h0δ h1Y N ?_ h2N) ?_
  · intro X hX
    have h1X : 1 ≤ X := le_trans h1Y hX.1
    let M := ⌈2 * X⌉₊
    have hlarge : C₂ ≤ ⌈2 * X⌉₊ := by
      rw [← Nat.cast_le (α := ℝ)]
      refine le_trans ?_ (Nat.le_ceil _)
      rw [mul_comm, ← div_le_iff₀ zero_lt_two]
      exact le_trans hYlarge hX.1
    let y : ℝ := 4
    let z := log (N : ℝ) ^ ((1 : ℝ) / 1000)
    have h2y : (2 : ℝ) ≤ y := by
      norm_num [y]
    have h1z : 1 < z := by
      dsimp [z]
      refine one_lt_rpow h1logN ?_
      norm_num
    have hzM : z ≤ c₁ * log (M : ℝ) := by
      have hzY : z ≤ c₁ * log Y := by
        dsimp [z, Y]
        rw [Real.log_rpow h0N]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hNlarge
      have h0Y : 0 < Y := by
        dsimp [Y]
        exact Real.rpow_pos_of_pos h0N _
      have hX_le_M : X ≤ (M : ℝ) := by
        dsimp [M]
        refine le_trans ?_ (Nat.le_ceil _)
        nlinarith [h1X]
      have hY_le_M : Y ≤ (M : ℝ) := le_trans hX.1 hX_le_M
      have hlogY_le : log Y ≤ log (M : ℝ) := Real.log_le_log h0Y hY_le_M
      exact le_trans hzY (mul_le_mul_of_nonneg_left hlogY_le h0c₁.le)
    have hMX : (M : ℝ) ≤ 4 * X := by
      dsimp [M]
      refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
      · positivity
      · linarith
    have hsubset :
        ((Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter p) ⊆
          (range M).filter fun n =>
            ∀ q : ℕ, Nat.Prime q → q ∣ n → (q : ℝ) < y ∨ z < q := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range]
      rw [Finset.mem_filter, Finset.mem_Ico] at hn
      refine ⟨hn.1.2, ?_⟩
      intro q hq₁ hq₂
      have hpred : ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ z := hn.2
      rw [not_exists] at hpred
      by_cases hq4 : 4 ≤ q
      · right
        have hqz : ¬ (q : ℝ) ≤ z := by
          exact fun hqz => hpred q ⟨hq₂, hq4, hqz⟩
        exact lt_of_not_ge hqz
      · left
        have hq' : (q : ℝ) < 4 := by
          exact_mod_cast lt_of_not_ge hq4
        simpa [y] using hq'
    specialize hsieve M hlarge y z h2y h1z hzM
    transitivity ((((range M).filter fun n =>
        ∀ p : ℕ, Nat.Prime p → p ∣ n → (p : ℝ) < y ∨ z < p).card : ℝ))
    · exact_mod_cast Finset.card_le_card hsubset
    · refine le_trans hsieve ?_
      have hcoeff_nonneg : 0 ≤ C₁ * (log y / log z) := by
        refine mul_nonneg h0C₁.le ?_
        refine div_nonneg ?_ (le_of_lt (Real.log_pos h1z))
        exact Real.log_nonneg (le_trans one_le_two h2y)
      have hcoeff_eq : C₁ * (log y / log z) * 4 = δ := by
        dsimp [δ, c₂, z, y]
        have h1000 : ((1 : ℝ) / 1000) ≠ 0 := by norm_num
        rw [Real.log_rpow h0logN]
        field_simp [h0loglogN.ne', h1000]
      calc
        C₁ * (log y / log z) * (M : ℝ) ≤ C₁ * (log y / log z) * (4 * X) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hMX hcoeff_nonneg
        _ = (C₁ * (log y / log z) * 4) * X := by ring
        _ = δ * X := by rw [hcoeff_eq]
  · have hEq : (2 / log 2) * δ * log (N : ℝ) = C * log (N : ℝ) / log (log (N : ℝ)) := by
      dsimp [C, δ]
      field_simp [h0loglogN.ne', (Real.log_pos one_lt_two).ne']
    rw [hEq]

lemma harmonic_filter_smooth_h1M {N : ℕ}
    (hN₁ : (1 : ℝ) < N) :
    1 ≤ ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊ := by
  refine Nat.succ_le_of_lt (Nat.ceil_pos.mpr ?_)
  exact Real.rpow_pos_of_pos (lt_trans zero_lt_one hN₁) _

lemma harmonic_filter_smooth_hMN {N : ℕ}
    (hN₁ : (1 : ℝ) < N)
    (h0loglogN : 0 < log (log (N : ℝ))) :
    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ N := by
  have h1N : (1 : ℝ) ≤ N := le_of_lt hN₁
  calc
    (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) ≤ (N : ℝ) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le h1N ?_
      have hnonneg : 0 ≤ 8 / log (log (N : ℝ)) := by
        positivity
      linarith
    _ = N := by simp

lemma harmonic_filter_smooth_hcomp {N : ℕ}
    (hN₁ : (1 : ℝ) < N)
    (h16loglogN : 16 ≤ log (log (N : ℝ))) :
    log (log (N : ℝ)) ≤ log ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))) := by
  have h0N : 0 < (N : ℝ) := by
    exact lt_trans zero_lt_one hN₁
  have h0logN : 0 < log (N : ℝ) := Real.log_pos hN₁
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  rw [Real.log_rpow h0N]
  have hlogN_ge4 : (4 : ℝ) ≤ log (N : ℝ) := by
    have htmp : Real.exp 4 ≤ Real.exp (log (log (N : ℝ))) := by
      exact Real.exp_le_exp.mpr (le_trans (by norm_num) h16loglogN)
    have h4le : (4 : ℝ) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp 4]
    exact le_trans h4le (by simpa [Real.exp_log h0logN] using htmp)
  have h1logN : (1 : ℝ) ≤ log (N : ℝ) := by
    linarith
  have hloglog_le_sqrt :
      log (log (N : ℝ)) ≤ (log (N : ℝ)) ^ (1 / 2 : ℝ) := by
    refine le_trans (log_le_thing (x := log (N : ℝ)) h1logN) ?_
    exact sub_le_self _ (by positivity)
  have hsqrt_sq : ((log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = log (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0logN.le]
    norm_num
  have hsqrt_le_halflog : (log (N : ℝ)) ^ (1 / 2 : ℝ) ≤ log (N : ℝ) / 2 := by
    have hsq_nonneg : 0 ≤ (((log (N : ℝ)) ^ (1 / 2 : ℝ)) - 2) ^ 2 := sq_nonneg _
    nlinarith
  have hloglog_le_halflog : log (log (N : ℝ)) ≤ log (N : ℝ) / 2 := by
    exact le_trans hloglog_le_sqrt hsqrt_le_halflog
  have h8div_le_half : 8 / log (log (N : ℝ)) ≤ (1 / 2 : ℝ) := by
    field_simp [h0loglogN.ne']
    linarith
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 8 / log (log (N : ℝ)) := by
    linarith
  have hhalflog_le :
      log (N : ℝ) / 2 ≤ ((1 : ℝ) - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hhalf_le h0logN.le
  exact le_trans hloglog_le_halflog hhalflog_le

lemma harmonic_filter_smooth_hNqrec {N q : ℕ} {C₂ : ℝ}
    (hharmonic :
      ∀ N : ℝ, 1 ≤ N → (Icc 1 ⌊N⌋₊).sum (fun n => (1 : ℝ) / n) ≤ C₂ * log (2 * N))
    (hq0 : 0 < q)
    (hqN : q ≤ N) :
    (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹) := by
  let g : ℕ → ℕ := fun m => m / q
  transitivity (Finset.sum (Icc 1 ⌊(N : ℝ) / q⌋₊) (fun m => (1 : ℝ) / (m * q)))
  · refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
    · intro m hm
      rw [one_div_nonneg]
      positivity
    · intro n hn
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Nat.succ_le_iff]
      refine ⟨Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn.1.1) hn.2) hq0, ?_⟩
      refine Nat.le_floor ?_
      rw [Nat.cast_div hn.2]
      · refine (div_le_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq0)).2 ?_
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
        simpa [div_mul_cancel₀ _ hqR] using (show (n : ℝ) ≤ N by exact_mod_cast hn.1.2)
      · exact_mod_cast hq0.ne'
    · intro a₁ ha₁ a₂ ha₂ ha
      rw [Finset.mem_filter] at ha₁ ha₂
      exact (Nat.div_left_inj ha₁.2 ha₂.2).1 ha
    · intro n hn
      rw [Finset.mem_filter] at hn
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      rw [Nat.cast_div hn.2 hqR]
      rw [div_mul_cancel₀ _ hqR]
  · transitivity ((1 : ℝ) / q * Finset.sum (Icc 1 ⌊(N : ℝ) / q⌋₊) (fun m => (1 : ℝ) / m))
    · rw [Finset.mul_sum]
      refine le_of_eq ?_
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [one_div, mul_comm]
    · have h :=
        mul_le_mul_of_nonneg_left
          (hharmonic ((N : ℝ) / q) ?_)
          (by positivity : 0 ≤ (1 : ℝ) / q)
      · simpa [one_div, mul_comm] using h
      · rw [le_div_iff₀]
        · simpa [one_mul] using (show (q : ℝ) ≤ N by exact_mod_cast hqN)
        · exact_mod_cast hq0

lemma harmonic_filter_smooth_hNqrec' {N : ℕ} {M C₂ : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h0C₂ : 0 < C₂)
    (hweird : C₂ * log 2 ≤ log (N : ℝ) / log (log (N : ℝ)))
    (hNqrec :
      ∀ q : ℕ,
        0 < q →
          q ≤ N →
            (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
              C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹)) :
    ∀ q ∈ ((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q),
      (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
        (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹) := by
  intro q hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  have hq0 : 0 < q := hq.2.1.pos
  have h0N : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le hq0 hq.1.2
  have h0M : 0 < M := by
    rw [hM]
    exact Real.rpow_pos_of_pos h0N _
  refine le_trans (hNqrec q hq0 hq.1.2) ?_
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr <| Nat.cast_nonneg q)
  transitivity C₂ * log (2 * ((N : ℝ) / M))
  · refine mul_le_mul_of_nonneg_left ?_ h0C₂.le
    refine Real.log_le_log ?_ ?_
    · refine mul_pos zero_lt_two (div_pos h0N ?_)
      exact_mod_cast hq0
    · refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ h0N.le
      simpa [one_div] using one_div_le_one_div_of_le h0M (by exact_mod_cast le_of_lt hq.2.2)
  · rw [hM, Real.log_mul (by norm_num) (by positivity), mul_add, add_mul, add_comm]
    refine add_le_add ?_ ?_
    · refine le_of_eq ?_
      rw [div_eq_mul_inv, ← Real.rpow_neg h0N.le, mul_comm (N : ℝ), ← Real.rpow_add_one h0N.ne' _,
        neg_sub, sub_add, sub_self, sub_zero, Real.log_rpow h0N]
      ring_nf
    · rw [one_mul]
      exact hweird

lemma harmonic_filter_smooth_htail {N : ℕ} {M b c C C₂ : ℝ}
    (hC : 2 * c ≤ C / (8 * C₂ + 1) - 2 * 8)
    (h0c : 0 < c)
    (h0C₂ : 0 < C₂)
    (h8loglogN : 8 < log (log (N : ℝ)))
    (h16loglogN : 16 ≤ log (log (N : ℝ)))
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h0logN : 0 < log (N : ℝ))
    (h0logM : 0 < log M)
    (hcomp : log (log (N : ℝ)) ≤ log M)
    (hmertensN :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹)
    (hmertensM :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹) :
    Finset.sum ((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q)
        (fun q => (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹)) ≤
      C * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
  let Q : Finset ℕ := (Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q
  let A : Finset ℕ := (Finset.Icc 1 N).filter IsPrimePow
  let B : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow
  have h0loglogN : 0 < log (log (N : ℝ)) := by
    linarith
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst hN0
    norm_num at h0logN
  have h0N : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have h1N : (1 : ℝ) < N := by
    by_contra hN
    have hexp : Real.exp (0 : ℝ) < Real.exp (log (N : ℝ)) := by
      exact Real.exp_lt_exp.mpr h0logN
    have hNgt : (1 : ℝ) < N := by
      simpa [Real.exp_zero, Real.exp_log h0N] using hexp
    exact hN hNgt
  have hloglogN' : 0 < 1 - 8 / log (log (N : ℝ)) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  have h0M : 0 < M := by
    rw [hM]
    exact Real.rpow_pos_of_pos h0N _
  have hMN : M ≤ N := by
    rw [hM]
    exact harmonic_filter_smooth_hMN (N := N) h1N h0loglogN
  have hfloorMN : ⌊M⌋₊ ≤ N := by
    simpa [Nat.floor_natCast] using nat_floor_real_le_floor (N := N) hMN
  have hQaux : Q ⊆ A \ B := by
    intro q hq
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, not_and, Finset.mem_Icc]
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    refine ⟨⟨⟨?_, hq.1.2⟩, hq.2.1⟩, ?_⟩
    · exact le_trans one_le_two (IsPrimePow.two_le hq.2.1)
    · intro hqB hqpp
      rw [Finset.mem_Icc] at hqB
      have hfloorMltq : ⌊M⌋₊ < q := by
        exact (Nat.floor_lt' (Nat.ne_of_gt hqpp.pos)).2 (by simpa using hq.2.2)
      exact not_lt_of_ge hqB.2 hfloorMltq
  have hBsubA : B ⊆ A := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hqpp⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hq2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, le_trans hq2 hfloorMN⟩, hqpp⟩
  have hsum_subset :
      Finset.sum Q (fun q => (q : ℝ)⁻¹) ≤ Finset.sum (A \ B) (fun q => (q : ℝ)⁻¹) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hQaux ?_
    intro q _hq _hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg q)
  have hsumN :
      Finset.sum A (fun q => (q : ℝ)⁻¹) ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) := by
    have htmp := sub_le_of_abs_sub_le_right hmertensN
    simpa [A, add_assoc, add_left_comm, add_comm] using htmp
  have hsumM :
      -(c * |log M|⁻¹) + (log (log M) + b) ≤ Finset.sum B (fun q => (q : ℝ)⁻¹) := by
    have htmp := sub_le_of_abs_sub_le_left hmertensM
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, B] using htmp
  have hlogM_eq : log M = (1 - 8 / log (log (N : ℝ))) * log (N : ℝ) := by
    rw [hM, Real.log_rpow h0N]
  have hloglogM_eq :
      log (log M) = log (1 - 8 / log (log (N : ℝ))) + log (log (N : ℝ)) := by
    rw [hlogM_eq, Real.log_mul hloglogN'.ne' h0logN.ne']
  have hInvN_le_logM : (log (N : ℝ))⁻¹ ≤ (log M)⁻¹ := by
    have hlogM_le_logN : log M ≤ log (N : ℝ) := log_le_log_of_le h0M hMN
    simpa [one_div] using one_div_le_one_div_of_le h0logM hlogM_le_logN
  have hInvM_le_loglogN : (log M)⁻¹ ≤ (log (log (N : ℝ)))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le h0loglogN hcomp
  have hInvN_le_loglogN : (log (N : ℝ))⁻¹ ≤ (log (log (N : ℝ)))⁻¹ := by
    exact le_trans hInvN_le_logM hInvM_le_loglogN
  have hbound_inv :
      c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ ≤ 2 * c / log (log (N : ℝ)) := by
    rw [abs_of_pos h0logN, abs_of_pos h0logM]
    have h1 : c * (log (N : ℝ))⁻¹ ≤ c * (log (log (N : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hInvN_le_loglogN h0c.le
    have h2 : c * (log M)⁻¹ ≤ c * (log (log (N : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hInvM_le_loglogN h0c.le
    calc
      c * (log (N : ℝ))⁻¹ + c * (log M)⁻¹
          ≤ c * (log (log (N : ℝ)))⁻¹ + c * (log (log (N : ℝ)))⁻¹ := by
            exact add_le_add h1 h2
      _ = 2 * c / log (log (N : ℝ)) := by
            field_simp [h0loglogN.ne']
            norm_num
  have hy_half : 8 / log (log (N : ℝ)) ≤ (1 / 2 : ℝ) := by
    field_simp [h0loglogN.ne']
    linarith
  have hloghelper :
      -(2 * (8 / log (log (N : ℝ)))) ≤ log (1 - 8 / log (log (N : ℝ))) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using log_helper (8 / log (log (N : ℝ))) (by positivity) hy_half
  have hbound_log :
      log (log (N : ℝ)) - log (log M) ≤ 16 / log (log (N : ℝ)) := by
    rw [hloglogM_eq]
    ring_nf
    have hneg' := neg_le_neg hloghelper
    ring_nf at hneg'
    exact hneg'
  have hdenpos : 0 < 8 * C₂ + 1 := by
    nlinarith
  have hC' : (2 * c + 16) * (8 * C₂ + 1) ≤ C := by
    have hCtemp := hC
    rw [le_sub_iff_add_le, _root_.le_div_iff₀ hdenpos] at hCtemp
    norm_num at hCtemp ⊢
    exact hCtemp
  have htail_inv :
      Finset.sum Q (fun q => (q : ℝ)⁻¹) ≤ (2 * c + 16) / log (log (N : ℝ)) := by
    refine le_trans hsum_subset ?_
    calc
      Finset.sum (A \ B) (fun q => (q : ℝ)⁻¹)
          = Finset.sum A (fun q => (q : ℝ)⁻¹) - Finset.sum B (fun q => (q : ℝ)⁻¹) := by
            exact Finset.sum_sdiff_eq_sub hBsubA
      _ ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) - Finset.sum B (fun q => (q : ℝ)⁻¹) := by
            exact sub_le_sub_right hsumN _
      _ ≤ c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
            (-(c * |log M|⁻¹) + (log (log M) + b)) := by
            exact sub_le_sub_left hsumM _
      _ ≤ (2 * c + 16) / log (log (N : ℝ)) := by
            have hmain :
                c * |log (N : ℝ)|⁻¹ + (log (log (N : ℝ)) + b) -
                    (-(c * |log M|⁻¹) + (log (log M) + b)) =
                  c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ +
                    (log (log (N : ℝ)) - log (log M)) := by
              ring
            rw [hmain]
            calc
              c * |log (N : ℝ)|⁻¹ + c * |log M|⁻¹ + (log (log (N : ℝ)) - log (log M))
                  ≤ 2 * c / log (log (N : ℝ)) + 16 / log (log (N : ℝ)) := by
                    exact add_le_add hbound_inv hbound_log
              _ = (2 * c + 16) / log (log (N : ℝ)) := by
                    field_simp [h0loglogN.ne']
  have hcoeff_nonneg : 0 ≤ (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) := by
    refine mul_nonneg ?_ ?_
    · linarith
    · exact div_nonneg h0logN.le h0loglogN.le
  calc
    Finset.sum Q (fun q => (8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ))) * ((q : ℝ)⁻¹))
        = ((8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ)))) *
            Finset.sum Q (fun q => (q : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
    _ ≤ ((8 * C₂ + 1) * (log (N : ℝ) / log (log (N : ℝ)))) *
          ((2 * c + 16) / log (log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left htail_inv hcoeff_nonneg
    _ = ((2 * c + 16) * (8 * C₂ + 1)) * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
          field_simp [h0loglogN.ne']
    _ ≤ C * log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by
          have hnonneg : 0 ≤ log (N : ℝ) / log (log (N : ℝ)) ^ 2 := by positivity
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hC' hnonneg

lemma harmonic_filter_smooth_hstep1 {N : ℕ} {M : ℝ}
    (hM : M = (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))))
    (h1M : 1 ≤ ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊) :
    ((Finset.Icc ⌈(N : ℝ) ^ ((1 : ℝ) - 1 / log (log (N : ℝ)))⌉₊ N).filter
          (fun n : ℕ =>
            ∃ q : ℕ,
              IsPrimePow q ∧
                ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n))).sum
        (fun m => (1 : ℝ) / m) ≤
      ((((Finset.Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q).biUnion
            fun q => (Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum
          fun n => (1 : ℝ) / n) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn.2 with ⟨q, hqpp, hMq, hqdiv⟩
    have hn1 : 1 ≤ n := le_trans h1M hn.1.1
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨q, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le q, ?_⟩, ⟨hqpp, ?_⟩⟩
      · exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqdiv) hn.1.2
      · simpa [hM] using hMq
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨le_trans h1M hn.1.1, hn.1.2⟩, hqdiv⟩
  · intro m hm₁ hm₂
    exact one_div_nonneg.mpr (Nat.cast_nonneg m)

lemma harmonic_filter_smooth :
    ∃ C : ℝ,
      0 < C ∧
        Filter.Eventually
          (fun N : ℕ =>
            ((Icc ⌈(N : ℝ) ^ (1 - 1 / log (log (N : ℝ)))⌉₊ N).filter
                  (fun n : ℕ =>
                    ∃ q : ℕ,
                      IsPrimePow q ∧
                        ((N : ℝ) ^ (1 - 8 / log (log (N : ℝ))) < (q : ℝ) ∧ q ∣ n))).sum
                (fun m => (1 : ℝ) / m) ≤
              C * log (N : ℝ) / log (log (N : ℝ)) ^ 2)
          atTop := by
  have hlogpow :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound (show 0 < (1 : ℝ) by norm_num)
  obtain ⟨b, hmertens₀⟩ := prime_power_reciprocal
  obtain ⟨c, h0c, hmertens⟩ := hmertens₀.exists_pos
  obtain ⟨C₂, h0C₂, hharmonic⟩ := harmonic_sum_bound'
  let C : ℝ := max ((2 * c + 2 * 8) * (8 * C₂ + 1)) 1
  have h0C : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 2 * c ≤ C / (8 * C₂ + 1) - 2 * 8 := by
    have hden : 0 < 8 * C₂ + 1 := by
      refine add_pos ?_ zero_lt_one
      refine mul_pos ?_ h0C₂
      norm_num
    rw [le_sub_iff_add_le, _root_.le_div_iff₀ hden]
    exact le_max_left _ _
  refine ⟨C, h0C, ?_⟩
  filter_upwards
    [ (another_this_particular_tends_to.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (C₂ * log 2))
    , tendsto_natCast_atTop_atTop.eventually hlogpow
    , tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , tendsto_log_log_coe_at_top (eventually_ge_atTop (16 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually hmertens.bound
    , (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_natCast_atTop_atTop).eventually
        hmertens.bound ] with
    N hweird hNlogpow hN₁ hM₁ h16loglogN hmertensN hmertensM
  have h1N : (1 : ℝ) ≤ N := le_of_lt hN₁
  have h0N : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one h1N
  have h0logN : 0 < log N := Real.log_pos hN₁
  have h8loglogN : 8 < log (log N) := lt_of_lt_of_le (by norm_num) h16loglogN
  have h0loglogN : 0 < log (log N) := lt_of_lt_of_le (by norm_num) h16loglogN
  have hloglogN' : 0 < 1 - 8 / log (log N) := by
    rw [sub_pos, div_lt_one h0loglogN]
    exact h8loglogN
  let M : ℝ := N ^ (1 - 8 / log (log N))
  have h1M : 1 ≤ ⌈(N : ℝ) ^ (1 - 1 / log (log N))⌉₊ := by
    exact harmonic_filter_smooth_h1M (N := N) hN₁
  have h0logM : 0 < log M := Real.log_pos hM₁
  have h0M : 0 < M := by
    dsimp [M]
    exact Real.rpow_pos_of_pos h0N _
  have hMN : M ≤ N := by
    change (N : ℝ) ^ ((1 : ℝ) - 8 / log (log N)) ≤ N
    exact harmonic_filter_smooth_hMN (N := N) hN₁ h0loglogN
  have hcomp : log (log N) ≤ log M := by
    change log (log N) ≤ log ((N : ℝ) ^ ((1 : ℝ) - 8 / log (log N)))
    exact harmonic_filter_smooth_hcomp (N := N) hN₁ h16loglogN
  have hmertensN' :
      |(((Finset.Icc 1 N).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log (N : ℝ)) + b)| ≤
        c * |log (N : ℝ)|⁻¹ := by
    simpa [Nat.floor_natCast, norm_inv, norm_eq_abs] using hmertensN
  have hmertensM' :
      |(((Finset.Icc 1 ⌊M⌋₊).filter IsPrimePow).sum fun q => (q : ℝ)⁻¹) -
          (log (log M) + b)| ≤
        c * |log M|⁻¹ := by
    simpa [M, norm_inv, norm_eq_abs] using hmertensM
  let Q : Finset ℕ := (Icc 0 N).filter fun q : ℕ => IsPrimePow q ∧ M < q
  let Nq : ℕ → Finset ℕ := fun q => (Icc 1 N).filter fun n : ℕ => q ∣ n
  have hNqrec :
      ∀ q : ℕ,
        0 < q →
          q ≤ N →
            (Nq q).sum (fun n => (1 : ℝ) / n) ≤
              C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹) := by
    intro q hq0 hqN
    change (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      C₂ * log (2 * ((N : ℝ) / q)) * ((q : ℝ)⁻¹)
    exact harmonic_filter_smooth_hNqrec (N := N) (q := q) (C₂ := C₂) hharmonic hq0 hqN
  have hNqrec' :
      ∀ q ∈ Q,
        (Nq q).sum (fun n => (1 : ℝ) / n) ≤
          (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹) := by
    intro q hq
    change (((Finset.Icc 1 N).filter fun n : ℕ => q ∣ n).sum (fun n => (1 : ℝ) / n)) ≤
      (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)
    exact
      harmonic_filter_smooth_hNqrec' (N := N) (M := M) (C₂ := C₂) rfl h0C₂ hweird hNqrec q
        (by simpa [Q] using hq)
  have htail :
      Finset.sum Q (fun q => (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)) ≤
        C * log N / log (log N) ^ 2 := by
    simpa [Q] using
      harmonic_filter_smooth_htail (N := N) (M := M) (b := b) (c := c) (C := C) (C₂ := C₂)
        hC h0c h0C₂ h8loglogN h16loglogN rfl h0logN h0logM hcomp hmertensN' hmertensM'
  calc
    ((Icc ⌈(N : ℝ) ^ (1 - 1 / log (log N))⌉₊ N).filter
          (fun n : ℕ =>
            ∃ q : ℕ, IsPrimePow q ∧ ((N : ℝ) ^ (1 - 8 / log (log N)) < (q : ℝ) ∧ q ∣ n))).sum
        (fun m => (1 : ℝ) / m)
        ≤ (Q.biUnion fun q => Nq q).sum (fun n => (1 : ℝ) / n) := by
          simpa [Q, Nq, M] using harmonic_filter_smooth_hstep1 (N := N) (M := M) rfl h1M
    _ ≤ Finset.sum Q (fun q => Finset.sum (Nq q) (fun n => (1 : ℝ) / n)) := by
          exact sum_bUnion_le_sum_of_nonneg (by
            intro n hn
            exact one_div_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ Finset.sum Q (fun q => (8 * C₂ + 1) * (log N / log (log N)) * ((q : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact hNqrec' q hq
    _ ≤ C * log N / log (log N) ^ 2 := htail


/-! ## From src4/ErdosProblems.lean -/

open Filter Finset Real
open scoped ArithmeticFunction.omega BigOperators

theorem unit_fractions_upper_log_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
      C * ((log (log (log N)) / log (log N)) * log N) ≤ rec_sum A →
        ∃ S ⊆ A, rec_sum S = 1 := by
  classical
  obtain ⟨C₁, h0C₁, hdiv⟩ := harmonic_filter_div
  obtain ⟨C₂, h0C₂, hreg⟩ := harmonic_filter_reg
  obtain ⟨C₃, h0C₃, hsmooth⟩ := harmonic_filter_smooth
  obtain ⟨C₁', hdivth⟩ := Filter.eventually_atTop.mp hdiv
  obtain ⟨C₂', hregth⟩ := Filter.eventually_atTop.mp hreg
  obtain ⟨C₃', hsmoothth⟩ := Filter.eventually_atTop.mp hsmooth
  let C : ℝ := 2 + 2 * C₃ + C₁ + C₂ + 2
  have h0C : 0 < C := by positivity
  obtain ⟨C₀, hcor⟩ := Filter.eventually_atTop.mp corollary_one
  obtain ⟨Cinc, hinc⟩ := this_fun_increasing
  refine ⟨C, h0C, ?_⟩
  filter_upwards
      [ eventually_gt_atTop 1
      , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (1 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_ge_atTop (1 : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (C₀ : ℝ))
      , eventually_ge_atTop C₁'
      , eventually_ge_atTop C₂'
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (C₃' : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (Cinc : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop (1 : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (exp (exp (1 : ℝ))))
      , the_last_large_N C₃ h0C₃
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          harmonic_sum_bound_two' ] with
    N hN h0logN h0loglogN_ev h1loglogN_ev h1log3N_ev hlargeN hdivth' hregth' hsmoothth' hincth
      hlargeN₂ hlargeN₃ hlargeN₄ hharmonic
  have h0loglogN : 0 < log (log N) := by
    simpa using h0loglogN_ev
  have h1loglogN : 1 < log (log N) := by
    simpa using h1loglogN_ev
  have h1log3N : 1 ≤ log (log (log N)) := by
    simpa [Function.comp] using h1log3N_ev
  let ε : ℝ := log (log (log N)) / log (log N)
  let ε' : ℝ := 1 / log (log N)
  have h0ε : 0 < ε := by
    refine div_pos ?_ h0loglogN
    exact Real.log_pos h1loglogN
  have h01ε : 0 < 1 / ε := by
    exact one_div_pos.mpr h0ε
  have hε1 : ε < 1 := by
    rw [div_lt_one h0loglogN]
    exact log_lt_self h0loglogN
  intro A hAN hrecA
  let A' := A.filter fun n : ℕ => (N : ℝ) ^ ε ≤ n
  have hrecA' : (2 + 2 * C₃ + C₁ + C₂) * ε * log N ≤ rec_sum A' := by
    have hAtemp : A' ∪ (A \ A') = A := by
      exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    by_contra h
    rw [not_le] at h
    have hotherrec : (rec_sum (A \ A') : ℝ) ≤ 2 * ε * log N := by
      rw [rec_sum]
      push_cast
      calc
        Finset.sum (A \ A') (fun n => (1 : ℝ) / n)
            ≤ Finset.sum (range (⌈(N : ℝ) ^ ε⌉₊)) (fun n => (1 : ℝ) / n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            rw [mem_range]
            rw [Finset.mem_sdiff, Finset.mem_filter, not_and, not_le] at hn
            rw [Nat.lt_ceil]
            exact hn.2 hn.1
          · intro n hn1 hn2
            exact one_div_nonneg.mpr (Nat.cast_nonneg n)
        _ ≤ 2 * ε * log N := by
          rw [mul_assoc, ← Real.log_rpow]
          · exact hharmonic
          · exact_mod_cast lt_trans zero_lt_one hN
    have hbad : (rec_sum A : ℝ) < C * (ε * log N) := by
      have hsum : (rec_sum A : ℝ) ≤ rec_sum A' + rec_sum (A \ A') := by
        simpa [hAtemp] using (rec_sum_union (A := A') (B := A \ A'))
      have hsumlt : rec_sum A' + rec_sum (A \ A') < C * (ε * log N) := by
        have hsumlt' := add_lt_add_of_lt_of_le h hotherrec
        dsimp [C] at hsumlt' ⊢
        nlinarith
      exact lt_of_le_of_lt hsum hsumlt
    exact not_lt_of_ge hrecA hbad
  clear hharmonic
  let Y := A'.filter fun n =>
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ (3 / 2) * log (log N))
  let X := A'.filter fun n =>
    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ ((d : ℝ) ≤ log N ^ ((1 : ℝ) / 1000))
  have hA'Icc : A' ⊆ Icc ⌈(N : ℝ) ^ ε⌉₊ N := by
    intro n hn
    rw [mem_Icc]
    rw [mem_filter] at hn
    have hn' := hAN hn.1
    rw [mem_Icc] at hn'
    refine ⟨?_, hn'.2⟩
    rw [Nat.ceil_le]
    exact hn.2
  have hrecX : (rec_sum X : ℝ) ≤ C₁ * ε' * log N := by
    rw [rec_sum]
    push_cast
    rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div, ← mul_div_assoc]
    refine le_trans ?_ (hdivth N hdivth')
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.filter_subset_filter _ hA'Icc
      · intro n hn1 hn2
        exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hε₁ : ε' ≤ ε := by
    have hmul := mul_le_mul_of_nonneg_right h1log3N (inv_nonneg.mpr h0loglogN.le)
    simpa [ε', ε, div_eq_mul_inv, one_mul] using hmul
  have hrecX' : (rec_sum X : ℝ) ≤ C₁ * ε * log N := by
    refine le_trans hrecX ?_
    have hmulε : ε' * log N ≤ ε * log N := mul_le_mul_of_nonneg_right hε₁ h0logN.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hmulε h0C₁.le
  have hrecY : (rec_sum Y : ℝ) ≤ C₂ * ε' * log N := by
    rw [rec_sum]
    push_cast
    rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div, ← mul_div_assoc]
    refine le_trans ?_ (hregth N hregth')
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.filter_subset_filter _ hA'Icc
      · intro n hn1 hn2
        exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hrecY' : (rec_sum Y : ℝ) ≤ C₂ * ε * log N := by
    refine le_trans hrecY ?_
    have hmulε : ε' * log N ≤ ε * log N := mul_le_mul_of_nonneg_right hε₁ h0logN.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hmulε h0C₂.le
  let A'' := A' \ (X ∪ Y)
  have hrecA'' : (2 + 2 * C₃) * ε * log N ≤ rec_sum A'' := by
    refine le_trans ?_ rec_sum_sdiff
    rw [le_sub_iff_add_le]
    have hXY : (rec_sum (X ∪ Y) : ℝ) ≤ (C₁ + C₂) * ε * log N := by
      refine le_trans rec_sum_union ?_
      linarith
    linarith
  let δ : ℝ := 1 - 1 / log (log N)
  have h0δ : 0 < δ := by
    have htmp : 1 / log (log N) < 1 := by
      simpa [one_div] using (one_div_lt_one_div h0loglogN zero_lt_one).2 h1loglogN
    linarith
  have hδ1 : δ ≤ 1 := by
    refine sub_le_self _ ?_
    rw [one_div_nonneg]
    exact le_of_lt h0loglogN
  let Nf := fun i : ℕ => (N : ℝ) ^ (δ ^ i)
  let Af := fun i : ℕ => Ioc ⌊Nf (i + 1)⌋₊ ⌊Nf i⌋₊ ∩ A''
  let Nf' := fun i : ℕ => ⌊Nf i⌋₊
  let ε'' : ℝ := 1 / (log (log N)) ^ 2
  have hgoodi : ∃ i : ℕ, 2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N ≤ rec_sum (Af i) := by
    by_contra h
    let I := range (⌈log (1 / ε) * (2 * log (log N))⌉₊)
    have hIA : A'' = I.biUnion (fun i => Af i) := by
      rw [← Finset.biUnion_inter]
      refine Eq.symm ?_
      rw [Finset.inter_eq_right]
      intro n hn
      have hcover := bUnion_range_Ioc ⌈log (1 / ε) * (2 * log (log N))⌉₊ Nf'
      refine hcover ?_
      rw [mem_Ioc]
      rw [Finset.mem_sdiff, Finset.mem_filter] at hn
      refine ⟨?_, ?_⟩
      · rw [Nat.floor_lt]
        · refine lt_of_lt_of_le ?_ hn.1.2
          refine Real.rpow_lt_rpow_of_exponent_lt ?_ ?_
          · exact_mod_cast hN
          · have hceil :
                δ ^ ⌈log (1 / ε) * (2 * log (log N))⌉₊ ≤
                  δ ^ (log (1 / ε) * (2 * log (log N))) := by
              rw [← Real.rpow_natCast]
              refine Real.rpow_le_rpow_of_exponent_ge h0δ hδ1 ?_
              exact Nat.le_ceil _
            refine lt_of_le_of_lt hceil ?_
            have h1divε : 1 < 1 / ε := by
              rw [lt_div_iff₀ h0ε]
              simpa using hε1
            have hlogδ : log δ ≤ -(1 / log (log N)) := by
              have htmp := Real.log_le_sub_one_of_pos h0δ
              simpa [δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            have hmul :
                (log (1 / ε) * (2 * log (log N))) * log δ ≤ -2 * log (1 / ε) := by
              have hfac_nonneg : 0 ≤ log (1 / ε) * (2 * log (log N)) := by
                exact mul_nonneg (le_of_lt (Real.log_pos h1divε)) (by positivity)
              calc
                (log (1 / ε) * (2 * log (log N))) * log δ
                    ≤ (log (1 / ε) * (2 * log (log N))) * (-(1 / log (log N))) := by
                      exact mul_le_mul_of_nonneg_left hlogδ hfac_nonneg
                _ = -2 * log (1 / ε) := by
                  have hL : log (log N) ≠ 0 := h0loglogN.ne'
                  field_simp [hL]
            calc
              δ ^ (log (1 / ε) * (2 * log (log N)))
                  = Real.exp ((log (1 / ε) * (2 * log (log N))) * log δ) := by
                    rw [Real.rpow_def_of_pos h0δ, mul_comm]
              _ ≤ Real.exp (-2 * log (1 / ε)) := by
                    gcongr
              _ < Real.exp (-(log (1 / ε))) := by
                    refine Real.exp_lt_exp.mpr ?_
                    have hpos : 0 < log (1 / ε) := Real.log_pos h1divε
                    linarith
              _ = ε := by
                    rw [show -(log (1 / ε)) = log ε by
                      rw [← Real.log_inv, one_div, inv_inv]]
                    rw [Real.exp_log h0ε]
        · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
      · have hnntemp := hAN hn.1.1
        rw [mem_Icc] at hnntemp
        have htemp : Nf' 0 = N := by
          dsimp [Nf', Nf]
          rw [pow_zero, Real.rpow_one, Nat.floor_natCast]
        rw [htemp]
        exact hnntemp.2
    rw [not_exists] at h
    rw [← not_lt] at hrecA''
    refine hrecA'' ?_
    rw [hIA]
    have hUnion :
        (rec_sum (I.biUnion fun i => Af i) : ℝ) ≤
          Finset.sum I (fun i => (rec_sum (Af i) : ℝ)) := by
      simpa using (rec_sum_bUnion (I := I) (f := Af))
    refine lt_of_le_of_lt hUnion ?_
    have hsum_card :
        Finset.sum I (fun i => (rec_sum (Af i) : ℝ)) ≤
          I.card • (2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N) := by
      refine Finset.sum_le_card_nsmul I (fun i => (rec_sum (Af i) : ℝ))
        (2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N) ?_
      intro x hx
      specialize h x
      rw [not_le] at h
      exact le_of_lt h
    refine lt_of_le_of_lt hsum_card ?_
    rw [Finset.card_range, one_div_div, nsmul_eq_mul]
    exact hlargeN₄.2
  rcases hgoodi with ⟨i, hi⟩
  let A₀ := Af i
  let N₀ := ⌊Nf i⌋₊
  have hNN₀ : (N : ℝ) ^ ε ≤ N₀ := by
    by_contra h
    have hA0empty : Af i = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro n hn
      rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn_le : (n : ℝ) ≤ N₀ := by exact_mod_cast hn.1.2
      exact h (le_trans hn.2.1.2 hn_le)
    rw [hA0empty, ← not_lt, rec_sum_empty] at hi
    have : 0 < 2 * log N ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N := by
      refine add_pos ?_ ?_
      · refine mul_pos ?_ ?_
        · norm_num
        · exact Real.rpow_pos_of_pos h0logN _
      · refine mul_pos ?_ h0logN
        refine mul_pos h0C₃ ?_
        rw [one_div_pos]
        exact sq_pos_of_pos h0loglogN
    linarith
  have h1N₀' : 1 ≤ Nf i := by
    refine one_le_rpow ?_ ?_
    · exact_mod_cast le_of_lt hN
    · exact pow_nonneg h0δ.le _
  have h1N₀ : 1 ≤ N₀ := by
    rw [← Nat.cast_le (α := ℝ)]
    refine le_trans ?_ hNN₀
    exact_mod_cast le_of_lt hlargeN₂
  have hN₀large₂ : 0 < log N₀ := by
    refine Real.log_pos ?_
    refine lt_of_lt_of_le ?_ hNN₀
    exact hlargeN₂
  have hN₀large : 1 ≤ log (log N₀) := by
    rw [← Real.exp_le_exp, Real.exp_log, ← Real.exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hNN₀
      exact hlargeN₃
    · exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀
    · exact hN₀large₂
  have hN₀N : (N₀ : ℝ) ≤ N := by
    rw [← Real.rpow_one N]
    refine le_trans (Nat.floor_le (by positivity)) ?_
    refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
    · exact_mod_cast le_of_lt hN
    · exact pow_le_one₀ h0δ.le hδ1
  have hlogNN₀' : (3 / 2 : ℝ) * log (log N) ≤ 2 * log (log N₀) := by
    have hstep : (log N) ^ (3 / 4 : ℝ) ≤ log N₀ := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_trans zero_lt_one hN
      have hpow_pos : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      have hlogpow_le : log ((N : ℝ) ^ ε) ≤ log N₀ := Real.log_le_log hpow_pos hNN₀
      have hlogpow_eq : log ((N : ℝ) ^ ε) = ε * log N := by
        rw [Real.log_rpow hNpos]
      calc
        (log N) ^ (3 / 4 : ℝ) ≤ log N * ε := by
          simpa [ε, mul_comm, mul_left_comm, mul_assoc] using hlargeN₄.1
        _ = log ((N : ℝ) ^ ε) := by rw [hlogpow_eq, mul_comm]
        _ ≤ log N₀ := hlogpow_le
    have haux : (3 / 4 : ℝ) * log (log N) ≤ log (log N₀) := by
      have hlog_step : log ((log N) ^ (3 / 4 : ℝ)) ≤ log (log N₀) := by
        exact Real.log_le_log (Real.rpow_pos_of_pos h0logN _) hstep
      simpa [Real.log_rpow h0logN, mul_comm] using hlog_step
    nlinarith
  have hlogNN₀ : log N ≤ (log N₀) ^ (2 : ℝ) := by
    have htmp : log (log N) ≤ (3 / 2 : ℝ) * log (log N) := by
      have hmul := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 / 2 by norm_num) h0loglogN.le
      simpa using hmul
    have hlog_eq : log ((log N₀) ^ (2 : ℝ)) = 2 * log (log N₀) := by
      rw [Real.log_rpow hN₀large₂]
    have hlog : log (log N) ≤ log ((log N₀) ^ (2 : ℝ)) := by
      rw [hlog_eq]
      exact le_trans htmp hlogNN₀'
    have hpow_pos : 0 < (log N₀) ^ (2 : ℝ) := by positivity
    exact (Real.log_le_log_iff h0logN hpow_pos).mp hlog
  let M := (N₀ : ℝ) ^ ((1 : ℝ) - 8 / log (log N₀))
  let Z := A₀.filter fun n => ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  let A₁ := A₀ \ Z
  have hloc : log N₀ / (log (log N₀)) ^ 2 ≤ ε'' * log N := by
    rw [mul_comm, ← div_eq_mul_one_div]
    refine hinc N₀ N ⟨?_, ?_⟩
    · exact le_trans hincth hNN₀
    · exact_mod_cast hN₀N
  have hA₀large : ∀ n ∈ A₀, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n := by
    intro n hn
    have hmem : n ∈ Ioc ⌊Nf (i + 1)⌋₊ ⌊Nf i⌋₊ := (Finset.mem_inter.mp hn).1
    have hmem' := Finset.mem_Ioc.mp hmem
    have hmem_lt : Nf (i + 1) < n := by
      exact (Nat.floor_lt (by positivity)).1 hmem'.1
    refine le_trans ?_ (le_of_lt hmem_lt)
    transitivity (Nf i) ^ (1 - (1 : ℝ) / log (log N₀))
    · refine Real.rpow_le_rpow ?_ ?_ ?_
      · exact_mod_cast le_trans zero_le_one h1N₀
      · exact Nat.floor_le (by positivity)
      · have hdiv : (1 : ℝ) / log (log N₀) ≤ 1 := by
          have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hN₀large
          simpa using this
        exact sub_nonneg.mpr hdiv
    · have hNfsucc : Nf (i + 1) = (Nf i) ^ δ := by
        dsimp [Nf]
        rw [pow_succ', ← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
        rw [mul_comm]
      rw [hNfsucc]
      refine Real.rpow_le_rpow_of_exponent_le h1N₀' ?_
      rw [sub_le_sub_iff_left]
      have hll : log (log N₀) ≤ log (log N) := by
        exact Real.log_le_log hN₀large₂
          (Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N)
      exact one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hN₀large) hll
  have hA₁large : ∀ n ∈ A₁, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n := by
    intro n hn
    exact hA₀large n (Finset.mem_sdiff.mp hn).1
  have hA₀' : A₀ ⊆ Icc ⌈(N₀ : ℝ) ^ (1 - 1 / log (log N₀))⌉₊ N₀ := by
    intro n hn
    rw [mem_Icc]
    have hn' := hn
    rw [mem_inter, mem_Ioc] at hn
    refine ⟨?_, hn.1.2⟩
    rw [Nat.ceil_le]
    exact hA₀large n hn'
  have hrecZ : (rec_sum Z : ℝ) ≤ C₃ * ε'' * log N := by
    rw [rec_sum]
    push_cast
    transitivity C₃ * log N₀ / (log (log N₀)) ^ 2
    · refine le_trans ?_ (hsmoothth N₀ ?_)
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset_filter _ hA₀'
        · intro n hn1 hn2
          exact one_div_nonneg.mpr (Nat.cast_nonneg n)
      · have hC₃' : C₃' ≤ N₀ := by
          rw [← Nat.cast_le (α := ℝ)]
          exact le_trans hsmoothth' hNN₀
        exact hC₃'
    · rw [mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hloc h0C₃.le
  have hrecA₁ : 2 * (log N₀) ^ ((1 : ℝ) / 500) ≤ rec_sum A₁ := by
    transitivity 2 * (log N) ^ ((1 : ℝ) / 500)
    · have hpow : (log N₀) ^ ((1 : ℝ) / 500) ≤ (log N) ^ ((1 : ℝ) / 500) := by
        refine Real.rpow_le_rpow ?_ ?_ ?_
        · exact Real.log_nonneg (by exact_mod_cast h1N₀)
        · exact Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N
        · norm_num1
      have hmul := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 2 by norm_num)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    · refine le_trans ?_ rec_sum_sdiff
      rw [le_sub_iff_add_le]
      refine le_trans ?_ hi
      rw [add_le_add_iff_left]
      exact hrecZ
  have hN₀ : C₀ ≤ N₀ := by
    rw [← Nat.cast_le (α := ℝ)]
    exact le_trans hlargeN hNN₀
  have hA₁N₀ : A₁ ⊆ range (N₀ + 1) := by
    intro n hn
    rw [mem_range, Nat.lt_succ_iff]
    have hn' : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    exact (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn').1).2
  have hA₁div : ∀ n ∈ A₁, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ log N₀ ^ (1 / 500 : ℝ) := by
    intro n hn
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
    have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
    have hn_not_union : n ∉ X ∪ Y := (Finset.mem_sdiff.mp hnA'').2
    have hn_notX : n ∉ X := fun hx => hn_not_union (Finset.mem_union.mpr (Or.inl hx))
    have hxdiv : ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ log N ^ ((1 : ℝ) / 1000) := by
      by_contra hxdiv
      exact hn_notX (by
        rw [mem_filter]
        exact ⟨hnA', hxdiv⟩)
    rcases hxdiv with ⟨d, hd₁, hd₂, hd₃⟩
    refine ⟨d, hd₁, hd₂, le_trans hd₃ ?_⟩
    calc
      log N ^ ((1 : ℝ) / 1000) ≤ ((log N₀) ^ (2 : ℝ)) ^ ((1 : ℝ) / 1000) := by
        exact Real.rpow_le_rpow h0logN.le hlogNN₀ (by norm_num)
      _ = log N₀ ^ ((1 : ℝ) / 500) := by
        rw [← Real.rpow_mul hN₀large₂.le]
        norm_num
  have hA₁smooth : ∀ n ∈ A₁, is_smooth M n := by
    intro n hn
    rw [is_smooth]
    intro q hq₁ hq₂
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hn_notZ : n ∉ Z := (Finset.mem_sdiff.mp hn).2
    rw [← not_lt]
    intro hbad
    exact hn_notZ (by
      rw [mem_filter]
      exact ⟨hnA₀, ⟨q, hq₁, hbad, hq₂⟩⟩)
  have hA₁reg : arith_regular N₀ A₁ := by
    rw [arith_regular]
    intro n hn
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
    have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
    have hn_not_union : n ∉ X ∪ Y := (Finset.mem_sdiff.mp hnA'').2
    have hn_notY : n ∉ Y := fun hy => hn_not_union (Finset.mem_union.mpr (Or.inr hy))
    have hn_nonzero : n ≠ 0 := by
      have htemp' := hAN (Finset.mem_filter.mp hnA').1
      rw [mem_Icc] at htemp'
      exact Nat.ne_of_gt htemp'.1
    have hn_regN :
        ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ (3 / 2) * log (log N) := by
      by_contra hbad
      exact hn_notY (by
        rw [mem_filter]
        exact ⟨hnA', hn_nonzero, hbad⟩)
    refine ⟨?_, ?_⟩
    · have hll : log (log N₀) ≤ log (log N) := by
        exact Real.log_le_log hN₀large₂
          (Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N)
      exact le_trans (mul_le_mul_of_nonneg_left hll (by norm_num)) hn_regN.1
    · exact le_trans hn_regN.2 hlogNN₀'
  specialize hcor N₀ hN₀ A₁ hA₁N₀ hA₁large hrecA₁ hA₁div hA₁smooth hA₁reg
  rcases hcor with ⟨S, hS₁, hS₂⟩
  refine ⟨S, ?_, hS₂⟩
  intro n hn
  have hnA₁ : n ∈ A₁ := hS₁ hn
  have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hnA₁).1
  have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
  have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
  exact (Finset.mem_filter.mp hnA').1

theorem erdos_298 (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  simpa [rec_sum] using unit_fractions_upper_density A hA

/-- **Erdős 46.** For any finite colouring `c` of the integers, there is a
monochromatic finite set `S` of integers `≥ 2` with `∑_{n ∈ S} 1/n = 1`.
Follows from Erdős 298 (Bloom-Mehta) applied to the densest colour class. -/
theorem erdos_46 :
    ∀ {α : Type*} [Finite α] (c : ℤ → α),
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ rec_sum S = 1 ∧ ∃ a : α, ∀ n ∈ S, c (n : ℤ) = a := by
  intro α _ c
  classical
  letI := Fintype.ofFinite α
  have hcard : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨c 0⟩
  letI : Nonempty α := ⟨c 0⟩
  let m : ℕ := Fintype.card α
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (by simpa [m] using hcard : 0 < m)
  let Acol : α → Set ℕ := fun a => {n : ℕ | c (n : ℤ) = a}
  have hblock :
      ∀ k : ℕ, ∃ a : α,
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card := by
    intro k
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := Finset.range (m * k)) (t := (Finset.univ : Finset α))
        (f := fun n : ℕ => c (n : ℤ)) (n := k)
        (fun _ _ => by simp) Finset.univ_nonempty (by simp [m])
    refine ⟨a, ?_⟩
    simpa [Acol] using ha
  let g : ℕ → α := fun k => Classical.choose (hblock k)
  have hg :
      ∀ k : ℕ,
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol (g k)).card := by
    intro k
    exact Classical.choose_spec (hblock k)
  obtain ⟨a, haInf⟩ := Finite.exists_infinite_fiber g
  have haInf' : (g ⁻¹' {a}).Infinite := by
    exact Set.infinite_coe_iff.mp haInf
  let K' : Set ℕ := (g ⁻¹' {a}) \ {0}
  have hK' : K'.Infinite := Set.Infinite.diff haInf' (Set.finite_singleton 0)
  let T : Set ℕ := {N : ℕ | (1 / (m : ℝ)) ≤ partial_density (Acol a) N}
  have himage : (fun k : ℕ => m * k) '' K' ⊆ T := by
    intro N hN
    rcases hN with ⟨k, hk, rfl⟩
    have hk0 : 0 < k := Nat.pos_iff_ne_zero.mpr (by simpa using hk.2)
    have hka : g k = a := by simpa using hk.1
    have hkcount :
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card := by
      simpa [g, hka] using hg k
    have hmkpos : 0 < (((m * k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (by simpa [m] using hcard) hk0
    have hkcount' :
        (k : ℝ) ≤ (((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card : ℝ) := by
      exact_mod_cast hkcount
    have hmne : (m : ℝ) ≠ 0 := by
      exact hmpos.ne'
    have hkne : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk0.ne'
    dsimp [T]
    rw [partial_density]
    have hfrac : (1 / (m : ℝ)) = (k : ℝ) / (((m * k : ℕ) : ℝ)) := by
      rw [Nat.cast_mul]
      field_simp [hmne, hkne]
    rw [hfrac]
    exact (div_le_div_iff_of_pos_right hmkpos).2 hkcount'
  have hinj : Set.InjOn (fun k : ℕ => m * k) K' := by
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by simpa [m] using hcard) hxy
  have hTinf : T.Infinite := (hK'.image hinj).mono himage
  have hfreq : ∃ᶠ N : ℕ in atTop, (1 / (m : ℝ)) ≤ partial_density (Acol a) N := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hTinf
  have hupper :
      (1 / (m : ℝ)) ≤ upper_density (Acol a) := by
    exact le_limsup_of_frequently_le hfreq (is_bounded_under_le_partial_density (A := Acol a))
  have hAcol : 0 < upper_density (Acol a) := by
    exact lt_of_lt_of_le (one_div_pos.mpr hmpos) hupper
  let B : Set ℕ := Acol a \ ({0, 1} : Set ℕ)
  have hpres : upper_density (Acol a) = upper_density B := by
    simpa [B] using (upper_density_preserved (A := Acol a) (S := ({0, 1} : Finset ℕ)))
  have hB : 0 < upper_density B := by
    rwa [← hpres]
  rcases erdos_298 B hB with ⟨S, hS, hrecS⟩
  refine ⟨S, ?_, hrecS, a, ?_⟩
  · intro n hn
    have hnB : n ∈ B := hS hn
    have hnB' : c (n : ℤ) = a ∧ n ≠ 0 ∧ n ≠ 1 := by
      simpa [B, Acol, Set.mem_insert_iff] using hnB
    omega
  · intro n hn
    have hnB : n ∈ B := hS hn
    simpa [B, Acol, Set.mem_insert_iff] using hnB.1

/-- **Erdős 45.** For every `k ≥ 2` there is an `nₖ` such that for any `k`-colouring
of the proper divisors `1 < d < nₖ` of `nₖ`, some monochromatic subset has reciprocals
summing to 1. Follows from Erdős 46 (compactness + the colouring version). -/
theorem erdos_45 :
    ∀ k : ℕ, 2 ≤ k → ∃ nₖ : ℕ, ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ ((nₖ.divisors.erase 1).erase nₖ) ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
  intro k hk
  classical
  let a0 : Fin k := ⟨0, lt_of_lt_of_le zero_lt_two hk⟩
  let GoodBound : ℕ → Prop := fun N =>
    ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ Finset.Icc 2 N ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a
  have hinterval : ∃ N : ℕ, GoodBound N := by
    by_contra hinterval
    have hbadN : ∀ N : ℕ, ∃ c : ℕ → Fin k,
        ¬ ∃ D' : Finset ℕ, D' ⊆ Finset.Icc 2 N ∧
          rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
      intro N
      have hN : ¬ GoodBound N := by
        intro hgood
        exact hinterval ⟨N, hgood⟩
      dsimp [GoodBound] at hN
      exact not_forall.mp hN
    let M : Finset ℕ → ℕ := fun s => s.sum id + 2
    let g : Finset ℕ → ℕ → Fin k := fun s => Classical.choose (hbadN (M s))
    obtain ⟨χ, hχ⟩ := Finset.rado_selection (β := fun _ : ℕ => Fin k) g
    let cInt : ℤ → Fin k := fun z => if hz : 0 ≤ z then χ z.toNat else a0
    rcases erdos_46 cInt with ⟨S, hSge2, hrecS, ⟨a, hmonoS⟩⟩
    obtain ⟨t, hSt, hχt⟩ := hχ S
    have hSM : S ⊆ Finset.Icc 2 (M t) := by
      intro n hn
      rw [Finset.mem_Icc]
      refine ⟨hSge2 n hn, ?_⟩
      dsimp [M]
      have hnt : n ∈ t := hSt hn
      have hle : n ≤ t.sum id := by
        simpa using
          (Finset.single_le_sum (f := fun m : ℕ => m) (fun m _ => Nat.zero_le m) hnt)
      exact le_trans hle (Nat.le_add_right _ _)
    have hmonoGt : ∃ b : Fin k, ∀ n ∈ S, g t n = b := by
      refine ⟨a, ?_⟩
      intro n hn
      have hχa : χ n = a := by
        simpa [cInt, a0] using hmonoS n hn
      calc
        g t n = χ n := by symm; exact hχt n hn
        _ = a := hχa
    rcases hmonoGt with ⟨b, hbmono⟩
    have hbad_t :
        ∀ D' : Finset ℕ, D' ⊆ Finset.Icc 2 (M t) → rec_sum D' = 1 →
          ∀ b : Fin k, ∃ d ∈ D', g t d ≠ b := by
      intro D' hD' hrec b
      by_contra hDbad
      push_neg at hDbad
      exact (Classical.choose_spec (hbadN (M t))) ⟨D', hD', hrec, b, hDbad⟩
    obtain ⟨d, hdS, hdne⟩ := hbad_t S hSM hrecS b
    exact hdne (hbmono d hdS)
  rcases hinterval with ⟨N, hN⟩
  refine ⟨Nat.factorial (N + 2), ?_⟩
  intro c
  rcases hN c with ⟨D', hD', hrecD', a, hmonoD'⟩
  refine ⟨D', ?_, hrecD', a, hmonoD'⟩
  intro d hd
  have hdIcc := hD' hd
  rw [Finset.mem_Icc] at hdIcc
  simp only [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, ?_, ?_⟩
  · have hfact : N < Nat.factorial (N + 2) := by
      exact lt_of_lt_of_le (by omega) (Nat.self_le_factorial _)
    exact ne_of_lt (lt_of_le_of_lt hdIcc.2 hfact)
  · exact ne_of_gt (lt_of_lt_of_le one_lt_two hdIcc.1)
  · exact ⟨Nat.dvd_factorial (lt_of_lt_of_le zero_lt_two hdIcc.1)
      (le_trans hdIcc.2 (Nat.le_add_right N 2)), Nat.factorial_ne_zero _⟩

end
end
end
end
end
end
end

#print axioms erdos_45
-- 'Erdos45.erdos_45' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos45
