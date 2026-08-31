import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos220

/-
# Problem Description

Erdős Problem 220 ($500). Let `n ≥ 1` and `A = {a₁ < ⋯ < a_φ(n)} = {1 ≤ m < n : (m, n) = 1}`.
Is it true that

  `∑_{1 ≤ k < φ(n)} (a_{k+1} - aₖ)² ≪ n² / φ(n)`?

`erdos_220` proves that it is. The answer is yes, by Montgomery and Vaughan, who in fact
proved the `γ`-th power version `∑ (a_{k+1} - aₖ)^γ ≪ n^γ / φ(n)^(γ-1)` for every `γ ≥ 1`.

`sortedTotatives n` is `((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)`, i.e.
literally the increasing list `A` of the statement, and `sumSquaredGaps` sums the squares of
its consecutive differences. The `≪` is rendered by a single positive real constant `C`
quantified before `n`, so it is independent of the modulus. At `n = 1` the list is empty and
both sides are trivial; the content is at `n ≥ 2`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/Basic.lean` -/

section
/-!
# Erdős Problem 220: elementary finite infrastructure

This file fixes the canonical increasing enumeration of the reduced residue
classes in `[0,n)`, the internal consecutive-gap square sum, and the finite
interval/window counts used by the analytic part of the proof.
-/

open scoped BigOperators

/-- The canonical representatives in `[0,n)` of the units modulo `n`. -/
def reducedResidueFinset (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun a => n.Coprime a

@[simp] lemma mem_reducedResidueFinset {n a : ℕ} :
    a ∈ reducedResidueFinset n ↔ a < n ∧ n.Coprime a := by
  simp [reducedResidueFinset]

@[simp] lemma card_reducedResidueFinset (n : ℕ) :
    (reducedResidueFinset n).card = n.totient := by
  simpa [reducedResidueFinset] using (Nat.totient_eq_card_coprime n).symm

@[simp] lemma reducedResidueFinset_zero : reducedResidueFinset 0 = ∅ := by
  simp [reducedResidueFinset]

@[simp] lemma reducedResidueFinset_one : reducedResidueFinset 1 = {0} := by
  ext a
  simp [mem_reducedResidueFinset]

/-- The reduced residues, in strictly increasing order. -/
noncomputable def reducedResidue (n : ℕ) : Fin n.totient ↪o ℕ :=
  (reducedResidueFinset n).orderEmbOfFin (card_reducedResidueFinset n)

@[simp] lemma reducedResidue_mem (n : ℕ) (i : Fin n.totient) :
    reducedResidue n i ∈ reducedResidueFinset n := by
  exact Finset.orderEmbOfFin_mem _ _ _

lemma reducedResidue_lt (n : ℕ) (i : Fin n.totient) :
    reducedResidue n i < n :=
  (mem_reducedResidueFinset.mp (reducedResidue_mem n i)).1

@[simp] lemma image_reducedResidue_univ (n : ℕ) :
    Finset.image (reducedResidue n) Finset.univ = reducedResidueFinset n := by
  exact Finset.image_orderEmbOfFin_univ _ _

@[simp] lemma map_reducedResidue_univ (n : ℕ) :
    Finset.map (reducedResidue n).toEmbedding Finset.univ = reducedResidueFinset n := by
  exact Finset.map_orderEmbOfFin_univ _ _

@[simp] lemma reducedResidue_one_apply (i : Fin (Nat.totient 1)) :
    reducedResidue 1 i = 0 := by
  have hlt := reducedResidue_lt 1 i
  omega

/-- The index of the left endpoint of the internal gap numbered by `k`. -/
def gapLeftIndex (n : ℕ) (k : Fin (n.totient - 1)) : Fin n.totient :=
  ⟨k.1, by omega⟩

/-- The index of the right endpoint of the internal gap numbered by `k`. -/
def gapRightIndex (n : ℕ) (k : Fin (n.totient - 1)) : Fin n.totient :=
  ⟨k.1 + 1, by omega⟩

@[simp] lemma gapLeftIndex_val (n : ℕ) (k : Fin (n.totient - 1)) :
    (gapLeftIndex n k).val = k.val := rfl

@[simp] lemma gapRightIndex_val (n : ℕ) (k : Fin (n.totient - 1)) :
    (gapRightIndex n k).val = k.val + 1 := rfl

lemma gapLeftIndex_lt_gapRightIndex (n : ℕ) (k : Fin (n.totient - 1)) :
    gapLeftIndex n k < gapRightIndex n k := by
  simp [gapLeftIndex, gapRightIndex]

lemma reducedResidue_gap_lt (n : ℕ) (k : Fin (n.totient - 1)) :
    reducedResidue n (gapLeftIndex n k) < reducedResidue n (gapRightIndex n k) :=
  (reducedResidue n).strictMono (gapLeftIndex_lt_gapRightIndex n k)

/-- The positive natural-number length of the `k`-th internal gap. -/
noncomputable def internalGap (n : ℕ) (k : Fin (n.totient - 1)) : ℕ :=
  reducedResidue n (gapRightIndex n k) - reducedResidue n (gapLeftIndex n k)

lemma internalGap_le_n (n : ℕ) (k : Fin (n.totient - 1)) :
    internalGap n k ≤ n := by
  dsimp [internalGap]
  exact (Nat.sub_le _ _).trans (Nat.le_of_lt (reducedResidue_lt n _))

/-- The sum of the squares of the gaps between consecutive reduced residues.

There is deliberately no wrap-around term here: this is exactly the sum in
Erdős Problem 220.
-/
noncomputable def gapSquareSum (n : ℕ) : ℝ :=
  ∑ k : Fin (n.totient - 1),
    (((reducedResidue n (gapRightIndex n k) : ℕ) : ℝ) -
      ((reducedResidue n (gapLeftIndex n k) : ℕ) : ℝ)) ^ 2

lemma gapSquareSum_eq_sum_internalGap (n : ℕ) :
    gapSquareSum n = ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _
  rw [internalGap, Nat.cast_sub (Nat.le_of_lt (reducedResidue_gap_lt n k))]

lemma gapSquareSum_eq_zero_of_totient_le_one {n : ℕ} (hφ : n.totient ≤ 1) :
    gapSquareSum n = 0 := by
  rw [gapSquareSum]
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  omega

@[simp] lemma gapSquareSum_zero : gapSquareSum 0 = 0 := by
  apply gapSquareSum_eq_zero_of_totient_le_one
  simp

@[simp] lemma gapSquareSum_one : gapSquareSum 1 = 0 := by
  apply gapSquareSum_eq_zero_of_totient_le_one
  simp

/-! ## Literal list formulation of the problem -/

/-- Sum of squared differences of adjacent entries of a natural-number list. -/
def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

@[simp] lemma sumSquaredGaps_nil : sumSquaredGaps [] = 0 := rfl

@[simp] lemma sumSquaredGaps_singleton (a : ℕ) : sumSquaredGaps [a] = 0 := rfl

@[simp] lemma sumSquaredGaps_cons_cons (a b : ℕ) (rest : List ℕ) :
    sumSquaredGaps (a :: b :: rest) =
      (b - a) ^ 2 + sumSquaredGaps (b :: rest) := rfl

/-- The list in the statement of Erdős Problem 220: all `m` with
`1 ≤ m < n` and `(m,n)=1`, in increasing order. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

@[simp] lemma mem_sortedTotatives {n m : ℕ} :
    m ∈ sortedTotatives n ↔ 1 ≤ m ∧ m < n ∧ m.Coprime n := by
  simp [sortedTotatives, and_assoc]

@[simp] lemma sortedTotatives_zero : sortedTotatives 0 = [] := by
  simp [sortedTotatives]

@[simp] lemma sortedTotatives_one : sortedTotatives 1 = [] := by
  simp [sortedTotatives]

lemma literalTotativeFinset_eq_reducedResidueFinset {n : ℕ} (hn : 2 ≤ n) :
    (Finset.Ico 1 n).filter (fun m => m.Coprime n) = reducedResidueFinset n := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico, mem_reducedResidueFinset]
  constructor
  · rintro ⟨⟨_, hmn⟩, hcop⟩
    exact ⟨hmn, hcop.symm⟩
  · rintro ⟨hmn, hcop⟩
    have hm0 : m ≠ 0 := by
      intro hm
      have hn1 : n = 1 := (Nat.coprime_zero_right n).mp (hm ▸ hcop)
      omega
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hm0, hmn⟩, hcop.symm⟩

lemma sortedTotatives_eq_reducedResidueSort {n : ℕ} (hn : 2 ≤ n) :
    sortedTotatives n = (reducedResidueFinset n).sort (· ≤ ·) := by
  rw [sortedTotatives, literalTotativeFinset_eq_reducedResidueFinset hn]

lemma sortedTotatives_eq_ofFn_reducedResidue {n : ℕ} (hn : 2 ≤ n) :
    sortedTotatives n = List.ofFn (reducedResidue n) := by
  rw [sortedTotatives_eq_reducedResidueSort hn, List.ofFn_eq_map]
  exact (Finset.listMap_orderEmbOfFin_finRange
    (reducedResidueFinset n) (card_reducedResidueFinset n)).symm

/-- Adjacent differences of a finite tuple are precisely the sum over its
consecutive `Fin` indices. -/
lemma sumSquaredGaps_ofFn (n : ℕ) (f : Fin n → ℕ) :
    sumSquaredGaps (List.ofFn f) =
      ∑ k : Fin (n - 1),
        (f ⟨k.val + 1, by omega⟩ - f ⟨k.val, by omega⟩) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp [List.ofFn_succ]
      | succ m =>
          let f' : Fin (m + 1) → ℕ := fun i => f i.succ
          rw [List.ofFn_succ (f := f)]
          rw [List.ofFn_succ (f := f')]
          simp only [sumSquaredGaps]
          rw [← List.ofFn_succ (f := f')]
          rw [ih f']
          change _ = ∑ k : Fin (m + 1),
            (f ⟨k.val + 1, by omega⟩ - f ⟨k.val, by omega⟩) ^ 2
          rw [Fin.sum_univ_succ]
          congr 1

/-- For `n ≥ 2`, the literal natural-number list sum in the problem is
exactly the canonical real-valued `gapSquareSum`. -/
theorem cast_sumSquaredGaps_sortedTotatives {n : ℕ} (hn : 2 ≤ n) :
    (sumSquaredGaps (sortedTotatives n) : ℝ) = gapSquareSum n := by
  rw [sortedTotatives_eq_ofFn_reducedResidue hn]
  rw [sumSquaredGaps_ofFn]
  rw [gapSquareSum_eq_sum_internalGap]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- Number of integers `t` with `1 ≤ t ≤ h` for which `x+t` is a unit
modulo `n`.  Coprimality is already periodic, so no explicit `% n` is needed.
-/
def unitCount (n h x : ℕ) : ℕ :=
  ((Finset.Icc 1 h).filter fun t => n.Coprime (x + t)).card

@[simp] lemma unitCount_zero (n x : ℕ) : unitCount n 0 x = 0 := by
  simp [unitCount]

lemma unitCount_eq_zero_iff {n h x : ℕ} :
    unitCount n h x = 0 ↔
      ∀ t : ℕ, 1 ≤ t → t ≤ h → ¬n.Coprime (x + t) := by
  simp only [unitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_Icc]
  constructor
  · intro H t ht1 hth hcop
    exact H ⟨ht1, hth⟩ hcop
  · intro H t ht hcop
    exact H t ht.1 ht.2 hcop

/-- Starting points `x ∈ [0,n)` whose following interval of length `h`
contains no unit modulo `n`. -/
def emptyWindows (n h : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun x => unitCount n h x = 0

@[simp] lemma mem_emptyWindows {n h x : ℕ} :
    x ∈ emptyWindows n h ↔ x < n ∧ unitCount n h x = 0 := by
  simp [emptyWindows]

lemma mem_emptyWindows_iff_forall {n h x : ℕ} :
    x ∈ emptyWindows n h ↔
      x < n ∧ ∀ t : ℕ, 1 ≤ t → t ≤ h → ¬n.Coprime (x + t) := by
  rw [mem_emptyWindows, unitCount_eq_zero_iff]

lemma emptyWindows_subset_range (n h : ℕ) :
    emptyWindows n h ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (mem_emptyWindows.mp hx).1

lemma card_emptyWindows_le (n h : ℕ) : (emptyWindows n h).card ≤ n := by
  exact (Finset.card_le_card (emptyWindows_subset_range n h)).trans_eq (Finset.card_range n)

@[simp] lemma emptyWindows_zero_left (h : ℕ) : emptyWindows 0 h = ∅ := by
  simp [emptyWindows]

@[simp] lemma emptyWindows_zero_right (n : ℕ) : emptyWindows n 0 = Finset.range n := by
  simp [emptyWindows]

@[simp] lemma card_emptyWindows_zero_right (n : ℕ) : (emptyWindows n 0).card = n := by
  simp

/-- The proportion of residue classes modulo `n` which are units. -/
noncomputable def density (n : ℕ) : ℝ :=
  (n.totient : ℝ) / (n : ℝ)

@[simp] lemma density_zero : density 0 = 0 := by
  simp [density]

@[simp] lemma density_one : density 1 = 1 := by
  simp [density]

lemma density_nonneg (n : ℕ) : 0 ≤ density n := by
  rw [density]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma density_pos {n : ℕ} (hn : 0 < n) : 0 < density n := by
  rw [density]
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hn) (by exact_mod_cast hn)

lemma density_le_one (n : ℕ) : density n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [density, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n)]
  exact_mod_cast Nat.totient_le n

lemma totient_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < n.totient :=
  Nat.totient_pos.mpr hn

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/ConcreteGaps.lean` -/

section
open scoped BigOperators

open Finset

/-- Starting positions lying in an internal reduced-residue gap and leaving at
least `h` steps before its right endpoint. -/
abbrev InternalGapStart (n h : ℕ) :=
  Σ k : Fin (n.totient - 1), Fin (internalGap n k - h)

/-- The integer represented by an internal gap start. -/
noncomputable def internalGapStartValue {n h : ℕ} (z : InternalGapStart n h) : ℕ :=
  reducedResidue n (gapLeftIndex n z.1) + z.2.val

lemma reducedResidue_add_internalGap (n : ℕ) (k : Fin (n.totient - 1)) :
    reducedResidue n (gapLeftIndex n k) + internalGap n k =
      reducedResidue n (gapRightIndex n k) := by
  rw [internalGap, Nat.add_sub_of_le (Nat.le_of_lt (reducedResidue_gap_lt n k))]

lemma not_coprime_strictly_between_reducedResidues
    {n y : ℕ} (k : Fin (n.totient - 1))
    (hleft : reducedResidue n (gapLeftIndex n k) < y)
    (hright : y < reducedResidue n (gapRightIndex n k)) :
    ¬ n.Coprime y := by
  intro hycop
  have hylt : y < n := hright.trans (reducedResidue_lt n _)
  have hymem : y ∈ reducedResidueFinset n :=
    mem_reducedResidueFinset.mpr ⟨hylt, hycop⟩
  rw [← image_reducedResidue_univ] at hymem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hymem
  have hki : gapLeftIndex n k < i := by
    apply (reducedResidue n).lt_iff_lt.mp
    simpa [hi] using hleft
  have hik : i < gapRightIndex n k := by
    apply (reducedResidue n).lt_iff_lt.mp
    simpa [hi] using hright
  change k.val < i.val at hki
  change i.val < k.val + 1 at hik
  omega

lemma internalGapStartValue_lt_right {n h : ℕ} (z : InternalGapStart n h) :
    internalGapStartValue z < reducedResidue n (gapRightIndex n z.1) := by
  have hj : z.2.val < internalGap n z.1 := by
    omega
  rw [← reducedResidue_add_internalGap]
  exact Nat.add_lt_add_left hj _

lemma internalGapStartValue_mem_emptyWindows {n h : ℕ} (z : InternalGapStart n h) :
    internalGapStartValue z ∈ emptyWindows n h := by
  rw [mem_emptyWindows_iff_forall]
  constructor
  · exact (internalGapStartValue_lt_right z).trans (reducedResidue_lt n _)
  · intro t ht1 hth htCoprime
    have hjt : z.2.val + t < internalGap n z.1 := by
      have hj := z.2.isLt
      omega
    have hleft : reducedResidue n (gapLeftIndex n z.1) <
        internalGapStartValue z + t := by
      dsimp [internalGapStartValue]
      omega
    have hright : internalGapStartValue z + t <
        reducedResidue n (gapRightIndex n z.1) := by
      rw [← reducedResidue_add_internalGap]
      dsimp [internalGapStartValue]
      omega
    exact not_coprime_strictly_between_reducedResidues z.1 hleft hright htCoprime

lemma internalGapStartValue_injective (n h : ℕ) :
    Function.Injective
      (internalGapStartValue : InternalGapStart n h → ℕ) := by
  rintro ⟨k, j⟩ ⟨l, m⟩ heq
  have hkl : k = l := by
    apply le_antisymm
    · by_contra hnle
      have hlk : l < k := lt_of_not_ge hnle
      have hidx : gapRightIndex n l ≤ gapLeftIndex n k := by
        simp only [gapRightIndex, gapLeftIndex, Fin.mk_le_mk]
        omega
      have hres : reducedResidue n (gapRightIndex n l) ≤
          reducedResidue n (gapLeftIndex n k) :=
        (reducedResidue n).monotone hidx
      have hmright : internalGapStartValue (⟨l, m⟩ : InternalGapStart n h) <
          reducedResidue n (gapRightIndex n l) :=
        internalGapStartValue_lt_right _
      have hkj : reducedResidue n (gapLeftIndex n k) ≤
          internalGapStartValue (⟨k, j⟩ : InternalGapStart n h) := by
        simp [internalGapStartValue]
      omega
    · by_contra hnle
      have hkl' : k < l := lt_of_not_ge hnle
      have hidx : gapRightIndex n k ≤ gapLeftIndex n l := by
        simp only [gapRightIndex, gapLeftIndex, Fin.mk_le_mk]
        omega
      have hres : reducedResidue n (gapRightIndex n k) ≤
          reducedResidue n (gapLeftIndex n l) :=
        (reducedResidue n).monotone hidx
      have hjright : internalGapStartValue (⟨k, j⟩ : InternalGapStart n h) <
          reducedResidue n (gapRightIndex n k) :=
        internalGapStartValue_lt_right _
      have hlm : reducedResidue n (gapLeftIndex n l) ≤
          internalGapStartValue (⟨l, m⟩ : InternalGapStart n h) := by
        simp [internalGapStartValue]
      omega
  subst l
  have hjm : j = m := by
    apply Fin.ext
    dsimp [internalGapStartValue] at heq
    omega
  subst m
  rfl

/-- Every internal gap contributes all of its possible empty-window starts,
and starts arising from distinct gaps are distinct. -/
lemma sum_internalGap_sub_le_card_emptyWindows (n h : ℕ) :
    ∑ k : Fin (n.totient - 1), (internalGap n k - h) ≤
      (emptyWindows n h).card := by
  let f : InternalGapStart n h → {x // x ∈ emptyWindows n h} :=
    fun z ↦ ⟨internalGapStartValue z, internalGapStartValue_mem_emptyWindows z⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply internalGapStartValue_injective n h
    exact congrArg Subtype.val hzw
  have hcard := Fintype.card_le_of_injective f hf
  simpa [InternalGapStart] using hcard

/-- One-dimensional layer cake for a natural square, with all levels above
`d` harmlessly included. -/
lemma nat_square_layer_cake_self (d : ℕ) :
    d ^ 2 = d + 2 * ∑ h ∈ Ioc 0 d, (d - h) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le d)]
      simp only [Nat.sub_self, add_zero]
      have hsum : ∑ x ∈ Ioc 0 d, (d + 1 - x) =
          (∑ x ∈ Ioc 0 d, (d - x)) + d := by
        calc
          ∑ x ∈ Ioc 0 d, (d + 1 - x) =
              ∑ x ∈ Ioc 0 d, ((d - x) + 1) := by
                apply sum_congr rfl
                intro x hx
                have hxd : x ≤ d := (mem_Ioc.mp hx).2
                omega
          _ = (∑ x ∈ Ioc 0 d, (d - x)) + d := by
            rw [sum_add_distrib]
            simp
      rw [hsum]
      nlinarith

lemma nat_square_layer_cake (d N : ℕ) (hdN : d ≤ N) :
    d ^ 2 = d + 2 * ∑ h ∈ Ioc 0 N, (d - h) := by
  rw [nat_square_layer_cake_self d]
  congr 2
  apply sum_subset
  · intro x hx
    rw [mem_Ioc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hdN⟩
  · intro x hxN hxd
    rw [mem_Ioc] at hxN
    have hdx : d < x := by
      by_contra hnot
      exact hxd (mem_Ioc.mpr ⟨hxN.1, Nat.le_of_not_gt hnot⟩)
    simp [Nat.sub_eq_zero_of_le hdx.le]

/-- The excess-mass function of the internal gaps. -/
noncomputable def internalGapExcess (n h : ℕ) : ℝ :=
  ∑ k : Fin (n.totient - 1), ((internalGap n k - h : ℕ) : ℝ)

lemma internalGapExcess_le_card_emptyWindows (n h : ℕ) :
    internalGapExcess n h ≤ ((emptyWindows n h).card : ℝ) := by
  rw [internalGapExcess]
  exact_mod_cast sum_internalGap_sub_le_card_emptyWindows n h

lemma sum_internalGap_cast_le (n : ℕ) :
    ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ≤ (n : ℝ) := by
  by_cases hsmall : n.totient ≤ 1
  · have hempty : ∀ k : Fin (n.totient - 1), False := by
      intro k
      have := k.isLt
      omega
    have hsum : ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact (hempty k).elim
    rw [hsum]
    positivity
  · have htwo : 2 ≤ n.totient := by omega
    let a : ℕ → ℝ := fun i ↦
      if hi : i < n.totient then ((reducedResidue n ⟨i, hi⟩ : ℕ) : ℝ) else 0
    let b : ℕ → ℝ := fun i ↦
      if hi : i < n.totient - 1 then (internalGap n ⟨i, hi⟩ : ℝ) else 0
    have heq :
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
          ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := by
      calc
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
            ∑ k : Fin (n.totient - 1), b k := by
              apply sum_congr rfl
              intro k hk
              simp [b, k.isLt]
        _ = ∑ k ∈ range (n.totient - 1), b k := by
              rw [Fin.sum_univ_eq_sum_range]
        _ = ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := by
              apply sum_congr rfl
              intro k hk
              have hklt : k < n.totient - 1 := mem_range.mp hk
              have hk0 : k < n.totient := by omega
              have hk1 : k + 1 < n.totient := by omega
              simp only [b, dif_pos hklt, internalGap, gapRightIndex, gapLeftIndex]
              have hgap : reducedResidue n ⟨k, hk0⟩ ≤
                  reducedResidue n ⟨k + 1, hk1⟩ := by
                apply Nat.le_of_lt
                apply (reducedResidue n).strictMono
                simp
              rw [Nat.cast_sub hgap]
              simp [a, hk0, hk1]
    calc
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
          ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := heq
      _ = a (n.totient - 1) - a 0 := by
            have hs := Finset.sum_range_sub' a (n.totient - 1)
            calc
              ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) =
                  - ∑ k ∈ range (n.totient - 1), (a k - a (k + 1)) := by
                    rw [← sum_neg_distrib]
                    apply sum_congr rfl
                    intro k hk
                    ring
              _ = a (n.totient - 1) - a 0 := by rw [hs]; ring
      _ ≤ (n : ℝ) := by
            have hlast : n.totient - 1 < n.totient := by omega
            have hzero : 0 < n.totient := by omega
            have hlt : reducedResidue n ⟨n.totient - 1, hlast⟩ < n :=
              reducedResidue_lt n _
            simp only [a, dif_pos hlast, dif_pos hzero]
            have hlast_le :
                ((reducedResidue n ⟨n.totient - 1, hlast⟩ : ℕ) : ℝ) ≤ n := by
              exact_mod_cast Nat.le_of_lt hlt
            have hfirst_nonneg :
                0 ≤ ((reducedResidue n ⟨0, hzero⟩ : ℕ) : ℝ) := by positivity
            linarith

/-- The internal gap squares are bounded by the first moment plus the finite
sum of their excess masses. -/
lemma gapSquareSum_le_internalGapExcess (n : ℕ) :
    gapSquareSum n ≤ (n : ℝ) +
      2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
  rw [gapSquareSum_eq_sum_internalGap]
  have hlayer :
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2) =
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) +
          2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
    calc
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2) =
          ∑ k : Fin (n.totient - 1),
            (((internalGap n k) ^ 2 : ℕ) : ℝ) := by
              apply sum_congr rfl
              intro k hk
              norm_num
      _ = ∑ k : Fin (n.totient - 1),
            (((internalGap n k) +
              2 * ∑ h ∈ Ioc 0 n, (internalGap n k - h) : ℕ) : ℝ) := by
              apply sum_congr rfl
              intro k hk
              rw [nat_square_layer_cake (internalGap n k) n (internalGap_le_n n k)]
      _ = (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) +
          2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
            push_cast
            simp only [sum_add_distrib, internalGapExcess]
            rw [← mul_sum, sum_comm]
  rw [hlayer]
  gcongr
  exact sum_internalGap_cast_le n

lemma gapSquareSum_le_emptyWindows_layer (n : ℕ) :
    gapSquareSum n ≤ (n : ℝ) +
      2 * ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) := by
  calc
    gapSquareSum n ≤ (n : ℝ) +
        2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h :=
      gapSquareSum_le_internalGapExcess n
    _ ≤ (n : ℝ) +
        2 * ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) := by
      gcongr with h hh
      exact internalGapExcess_le_card_emptyWindows n h

private theorem concrete_emptyWindow_tail_deduction
    (E : ℕ → ℝ) (N K : ℕ) (q phi B secondMoment : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hphi_le_q : phi ≤ q) (hB : 0 ≤ B)
    (hK_pos : 0 < K) (hK_le_N : K ≤ N)
    (hK_lower : q / phi ≤ (K : ℝ))
    (hK_upper : (K : ℝ) ≤ 2 * q / phi)
    (hE_trivial : ∀ h ∈ Ioc 0 N, E h ≤ q)
    (hE_analytic : ∀ h ∈ Ioc K N,
      E h * (h : ℝ) ^ 2 * phi ^ 2 ≤ B * q ^ 3)
    (hlayer : secondMoment = q + 2 * ∑ h ∈ Ioc 0 N, E h) :
    secondMoment ≤ (5 + 2 * B) * q ^ 2 / phi := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hphi0 : phi ≠ 0 := ne_of_gt hphi
  have hK_real_pos : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hcoeff_nonneg : 0 ≤ B * q ^ 3 / phi ^ 2 := by positivity
  have hsplit :
      ∑ h ∈ Ioc 0 N, E h =
        (∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h := by
    rw [← sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [Ioc_union_Ioc_eq_Ioc (Nat.zero_le K) hK_le_N]
  have hsmall : ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ ∑ _h ∈ Ioc 0 K, q := by
        apply sum_le_sum
        intro h hh
        exact hE_trivial h (by
          rw [mem_Ioc] at hh ⊢
          exact ⟨hh.1, hh.2.trans hK_le_N⟩)
      _ = (K : ℝ) * q := by simp
  have hlarge_pointwise : ∀ h ∈ Ioc K N,
      E h ≤ (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
    intro h hh
    have hh_nat_pos : 0 < h := lt_of_lt_of_le hK_pos (mem_Ioc.mp hh).1.le
    have hh_real_pos : 0 < (h : ℝ) := by exact_mod_cast hh_nat_pos
    have hden_pos : 0 < (h : ℝ) ^ 2 * phi ^ 2 := by positivity
    have hdiv : E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := by
      apply (le_div_iff₀ hden_pos).2
      simpa only [mul_assoc] using hE_analytic h hh
    calc
      E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := hdiv
      _ = (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        field_simp [ne_of_gt hh_real_pos, hphi0]
  have hinv_tail :
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹)) ≤ ((K : ℝ)⁻¹) := by
    calc
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹))
          ≤ ((K : ℝ)⁻¹) - ((N : ℝ)⁻¹) :=
        sum_Ioc_inv_sq_le_sub (by omega) hK_le_N
      _ ≤ ((K : ℝ)⁻¹) := sub_le_self _ (inv_nonneg.mpr (by positivity))
  have hlarge :
      ∑ h ∈ Ioc K N, E h ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ ∑ h ∈ Ioc K N,
              (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        exact sum_le_sum hlarge_pointwise
      _ = (B * q ^ 3 / phi ^ 2) *
            ∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹) := by
        rw [mul_sum]
      _ ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_tail hcoeff_nonneg
  have hq_le_Kphi : q ≤ (K : ℝ) * phi := (div_le_iff₀ hphi).mp hK_lower
  have hinvK_le : ((K : ℝ)⁻¹) ≤ phi / q := by
    apply (le_div_iff₀ hq).2
    have hq_div_K : q / (K : ℝ) ≤ phi := by
      apply (div_le_iff₀ hK_real_pos).2
      simpa [mul_comm] using hq_le_Kphi
    simpa [div_eq_mul_inv, mul_comm] using hq_div_K
  have hlarge_final : ∑ h ∈ Ioc K N, E h ≤ B * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := hlarge
      _ ≤ (B * q ^ 3 / phi ^ 2) * (phi / q) :=
        mul_le_mul_of_nonneg_left hinvK_le hcoeff_nonneg
      _ = B * q ^ 2 / phi := by
        field_simp [hq0, hphi0]
  have hsmall_final : ∑ h ∈ Ioc 0 K, E h ≤ 2 * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := hsmall
      _ ≤ (2 * q / phi) * q := mul_le_mul_of_nonneg_right hK_upper hq.le
      _ = 2 * q ^ 2 / phi := by ring
  have hfirst_moment : q ≤ q ^ 2 / phi := by
    apply (le_div_iff₀ hphi).2
    nlinarith
  rw [hlayer, hsplit]
  calc
    q + 2 * ((∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h)
        ≤ q + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by gcongr
    _ ≤ q ^ 2 / phi + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by gcongr
    _ = (5 + 2 * B) * q ^ 2 / phi := by ring

/-- Concrete finite deduction used by Erdős Problem 220.  The sole analytic
hypothesis is the division-free empty-window estimate supplied by the
Montgomery--Vaughan moment argument. -/
theorem gapSquareSum_le_of_emptyWindows_bound
    (n : ℕ) (hn : 0 < n) (B : ℝ) (hB : 0 ≤ B)
    (hEmpty : ∀ h : ℕ, 1 ≤ h → h ≤ n →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 *
          (n.totient : ℝ) ^ 2 ≤ B * (n : ℝ) ^ 3) :
    gapSquareSum n ≤ (5 + 2 * B) * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  let K : ℕ := ⌈(n : ℝ) / (n.totient : ℝ)⌉₊
  have hphiNat : 0 < n.totient := totient_pos_of_pos hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hphiR : 0 < (n.totient : ℝ) := by exact_mod_cast hphiNat
  have hphi_le_nR : (n.totient : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.totient_le n
  have hratio_one : (1 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
    rw [le_div_iff₀ hphiR]
    simpa using hphi_le_nR
  have hK_pos : 0 < K := by
    dsimp [K]
    exact Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hratio_one)
  have hK_lower : (n : ℝ) / (n.totient : ℝ) ≤ (K : ℝ) := by
    simpa [K] using Nat.le_ceil ((n : ℝ) / (n.totient : ℝ))
  have hK_upper : (K : ℝ) ≤ 2 * (n : ℝ) / (n.totient : ℝ) := by
    have hceil : (⌈(n : ℝ) / (n.totient : ℝ)⌉₊ : ℝ) ≤
        2 * ((n : ℝ) / (n.totient : ℝ)) := by
      exact Nat.ceil_le_two_mul (by linarith [hratio_one])
    simpa [K, mul_div_assoc] using hceil
  have hK_le_n : K ≤ n := by
    dsimp [K]
    rw [Nat.ceil_le]
    apply (div_le_iff₀ hphiR).2
    have hphi_one : (1 : ℝ) ≤ (n.totient : ℝ) := by exact_mod_cast hphiNat
    nlinarith
  have htail :
      (n : ℝ) + 2 *
          ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) ≤
        (5 + 2 * B) * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
    apply concrete_emptyWindow_tail_deduction
        (fun h ↦ ((emptyWindows n h).card : ℝ)) n K
        (n : ℝ) (n.totient : ℝ) B
        ((n : ℝ) + 2 *
          ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ))
        hnR hphiR hphi_le_nR hB hK_pos hK_le_n hK_lower hK_upper
    · intro h hh
      exact_mod_cast card_emptyWindows_le n h
    · intro h hh
      have hKh : K < h := (mem_Ioc.mp hh).1
      exact hEmpty h (by omega) (mem_Ioc.mp hh).2
    · rfl
  exact (gapSquareSum_le_emptyWindows_layer n).trans htail

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/Fourier.lean` -/

section
/-!
# Finite Fourier lemmas for Erdős 220

This file contains the elementary finite Fourier input used in the
Montgomery--Vaughan moment calculation.  We use the grid
`exp (2 * pi * I / q)` and intervals `0, ..., h - 1`; translating the
interval to `1, ..., h` only multiplies its Fourier transform by a unit.
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## Roots of unity and orthogonality -/

/-- The standard primitive `q`-th root of unity. -/
def fourierRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * (↑Real.pi : ℂ) * Complex.I / q)

@[simp] theorem fourierRoot_ne_zero (q : ℕ) : fourierRoot q ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- A complete nontrivial geometric sum on a root-of-unity grid vanishes. -/
theorem fourierRoot_sum_zero (q : ℕ) (hq : 2 ≤ q) (k : ℕ)
    (hk0 : 0 < k) (hkq : k < q) :
    ∑ a ∈ range q, fourierRoot q ^ (k * a) = 0 := by
  norm_num [pow_mul]
  rw [geom_sum_eq] <;> norm_num [fourierRoot]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm,
      div_mul_cancel₀] <;>
      norm_num [show q ≠ 0 by positivity]
  · rw [← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff]
    norm_num [Complex.ext_iff, div_mul_eq_mul_div]
    intro x hx
    rw [div_eq_iff (by positivity)] at hx
    exact False.elim <|
      absurd hx <| by
        exact fun hx' => by
          exact absurd
            (Int.le_of_dvd (by positivity) <|
              show (q : ℤ) ∣ k from
                ⟨x, by
                  rw [← @Int.cast_inj ℝ]
                  push_cast
                  nlinarith [Real.pi_pos]⟩)
            (by
              norm_cast
              linarith)

/-- Orthogonality of additive characters on `Z/qZ`, in divisibility form. -/
theorem fourierRoot_orthogonality (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ a ∈ range q, fourierRoot q ^ (k * ↑a) =
      if (q : ℤ) ∣ k then q else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    norm_num [zpow_mul, fourierRoot]
    norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hq.ne']
  · obtain ⟨u, r, hr⟩ : ∃ u r : ℤ, 0 < r ∧ r < q ∧ k = q * u + r := by
      exact
        ⟨k / q, k % q,
          lt_of_le_of_ne (Int.emod_nonneg _ (by positivity)) (Ne.symm (by aesop)),
          Int.emod_lt_of_pos _ (by positivity),
          by rw [Int.mul_ediv_add_emod]⟩
    have h_exp : ∀ a : ℕ,
        fourierRoot q ^ (k * a) = fourierRoot q ^ (r * a) := by
      intro a
      simp [hr, fourierRoot]
      norm_num [zpow_add₀ (Complex.exp_ne_zero _), zpow_mul]
      norm_num [← Complex.exp_nat_mul, mul_div_cancel₀, hq.ne']
    convert fourierRoot_sum_zero q (by omega) r.natAbs (by omega) (by omega) using 1
    cases r <;> aesop
    all_goals exact Nat.cast_zero

/-! ## The Fourier transform of an interval -/

/-! ## Ramanujan sums -/

/-- The exponential definition of the Ramanujan sum `c_q(m)`. -/
def ramanujanSum (q m : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter fun a => a.Coprime q, fourierRoot q ^ (a * m)

/-- Evaluation of a Ramanujan sum at a prime modulus. -/
theorem ramanujanSum_prime (p m : ℕ) (hp : p.Prime) :
    ramanujanSum p m = if p ∣ m then ((p - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hfilter : (range p).filter (fun a => a.Coprime p) = (range p).erase 0 := by
    ext a
    simp only [mem_filter, mem_range, mem_erase, ne_eq]
    constructor
    · rintro ⟨ha, hcop⟩
      exact ⟨by
        intro ha0
        subst a
        have hp1 : p = 1 := by simpa using hcop
        exact hp.ne_one hp1, ha⟩
    · rintro ⟨ha0, ha⟩
      exact ⟨ha, (hp.coprime_iff_not_dvd.mpr fun hpa => by
        exact ha0 (Nat.eq_zero_of_dvd_of_lt hpa ha)).symm⟩
  rw [ramanujanSum, hfilter]
  have herase :
      (∑ a ∈ (range p).erase 0, fourierRoot p ^ (a * m)) =
        (∑ a ∈ range p, fourierRoot p ^ (a * m)) - 1 := by
    rw [eq_sub_iff_add_eq]
    simpa only [zero_mul, pow_zero] using
      (Finset.sum_erase_add (s := range p)
        (f := fun a => fourierRoot p ^ (a * m)) (mem_range.mpr hp0))
  rw [herase]
  have hortho := fourierRoot_orthogonality p hp0 (m : ℤ)
  norm_cast at hortho
  simp only [Nat.cast_ite, Nat.cast_zero] at hortho
  have hortho' :
      (∑ a ∈ range p, fourierRoot p ^ (a * m)) =
        if p ∣ m then (p : ℂ) else 0 := by
    simpa only [Nat.mul_comm] using hortho
  by_cases hpm : p ∣ m
  · simp only [if_pos hpm] at hortho' ⊢
    rw [hortho', Nat.cast_sub hp.one_le]
    ring
  · simp only [if_neg hpm] at hortho' ⊢
    rw [hortho']
    ring

/-- The prime factor occurring in the squarefree Ramanujan expansion. -/
def primeRamanujanFactor (p m : ℕ) : ℂ :=
  ((p - 1 : ℕ) : ℂ) / p * (1 - ramanujanSum p m / (p - 1 : ℕ))

/-- At a prime, the Ramanujan factor is exactly the coprimality indicator. -/
theorem primeRamanujanFactor_eq_indicator (p m : ℕ) (hp : p.Prime) :
    primeRamanujanFactor p m = if m.Coprime p then 1 else 0 := by
  have hp1 : (p - 1 : ℕ) ≠ 0 := by have := hp.two_le; omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1c : ((p - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp1
  rw [primeRamanujanFactor, ramanujanSum_prime p m hp]
  by_cases hpm : p ∣ m
  · have hnc : ¬ m.Coprime p := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hpm
    rw [if_pos hpm, if_neg hnc]
    simp only [div_self hp1c, sub_self, mul_zero]
  · have hc : m.Coprime p := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hpm
    rw [if_neg hpm, if_pos hc]
    field_simp [hp0, hp1c]
    rw [Nat.cast_sub hp.one_le]
    ring

/-- Product form of the squarefree Ramanujan expansion. -/
def squarefreeRamanujanExpansion (s m : ℕ) : ℂ :=
  ∏ p ∈ s.primeFactors, primeRamanujanFactor p m

/-- The squarefree Ramanujan product is the coprimality indicator. -/
theorem squarefreeRamanujanExpansion_eq_indicator (s m : ℕ) (hs : Squarefree s) :
    squarefreeRamanujanExpansion s m = if m.Coprime s then 1 else 0 := by
  rw [squarefreeRamanujanExpansion]
  rw [Finset.prod_congr rfl fun p hp =>
    primeRamanujanFactor_eq_indicator p m (Nat.prime_of_mem_primeFactors hp)]
  rw [Finset.prod_boole]
  congr 1
  rw [← Nat.coprime_prod_right_iff, Nat.prod_primeFactors_of_squarefree hs]

/-! ## The subset (squarefree-divisor) expansion -/

/-- The product of the prime densities. -/
def fourierDensity (s : ℕ) : ℂ :=
  ∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)

/-- The nonconstant part of the prime Ramanujan factor. -/
def ramanujanCorrection (p m : ℕ) : ℂ :=
  -ramanujanSum p m / (p - 1 : ℕ)

/-- The term indexed by a squarefree divisor, represented by its set of primes. -/
def ramanujanSubsetTerm (T : Finset ℕ) (m : ℕ) : ℂ :=
  ∏ p ∈ T, ramanujanCorrection p m

/-- Prime products give the usual density `φ(s)/s`. -/
theorem fourierDensity_eq_density (s : ℕ) (hs : 0 < s) :
    fourierDensity s = (density s : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hPnat : ∏ p ∈ s.primeFactors, p ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hPC : ((∏ p ∈ s.primeFactors, p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hPnat
  have htot := Nat.totient_mul_prod_primeFactors s
  rw [fourierDensity, density]
  push_cast
  change (∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)) =
    (s.totient : ℂ) / s
  rw [Finset.prod_div_distrib]
  have hPC' : (∏ p ∈ s.primeFactors, (p : ℂ)) ≠ 0 := by
    simpa only [Nat.cast_prod] using hPC
  apply (div_eq_div_iff hPC' hsC).2
  convert congrArg (fun n : ℕ => (n : ℂ)) htot.symm using 1 <;>
    push_cast <;> ring

/-- Expanding the product over primes gives the sum over squarefree divisors. -/
theorem squarefreeRamanujanExpansion_eq_subsetSum (s m : ℕ) :
    squarefreeRamanujanExpansion s m =
      fourierDensity s *
        ∑ T ∈ s.primeFactors.powerset, ramanujanSubsetTerm T m := by
  simp only [squarefreeRamanujanExpansion, fourierDensity, ramanujanSubsetTerm]
  calc
    ∏ p ∈ s.primeFactors, primeRamanujanFactor p m =
        ∏ p ∈ s.primeFactors,
          ((((p - 1 : ℕ) : ℂ) / p) * (1 + ramanujanCorrection p m)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [primeRamanujanFactor, ramanujanCorrection]
      ring
    _ = (∏ p ∈ s.primeFactors, (((p - 1 : ℕ) : ℂ) / p)) *
        ∏ p ∈ s.primeFactors, (1 + ramanujanCorrection p m) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Finset.prod_one_add]

/-! ## Translated interval counts -/

/-- The natural unit count is the sum of the squarefree Fourier indicator. -/
theorem unitCount_cast_eq_squarefreeRamanujanExpansion
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) =
      ∑ t ∈ Finset.Icc 1 h, squarefreeRamanujanExpansion s (u + t) := by
  rw [unitCount]
  simp_rw [squarefreeRamanujanExpansion_eq_indicator _ _ hs]
  simp [Nat.coprime_comm, Finset.sum_boole]

/-- Exact divisor-sum expansion of a translated interval count. -/
theorem unitCount_cast_eq_ramanujanSubsetSum
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) =
      fourierDensity s * ∑ t ∈ Finset.Icc 1 h,
        ∑ T ∈ s.primeFactors.powerset, ramanujanSubsetTerm T (u + t) := by
  rw [unitCount_cast_eq_squarefreeRamanujanExpansion s h u hs]
  simp_rw [squarefreeRamanujanExpansion_eq_subsetSum]
  rw [Finset.mul_sum]

/-- Nonempty subsets are precisely the nonconstant terms in the expansion. -/
def nonconstantRamanujanSubsets (s : ℕ) : Finset (Finset ℕ) :=
  s.primeFactors.powerset.erase ∅

/-- The centered interval count is exactly the sum of the nonconstant
squarefree-divisor terms. -/
theorem unitCount_centered_eq_ramanujanSubsetSum
    (s h u : ℕ) (hs : Squarefree s) :
    (unitCount s h u : ℂ) - h * fourierDensity s =
      fourierDensity s *
        ∑ T ∈ nonconstantRamanujanSubsets s,
          ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) := by
  rw [unitCount_cast_eq_ramanujanSubsetSum s h u hs]
  rw [Finset.sum_comm]
  have hempty : ∅ ∈ s.primeFactors.powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hempty]
  simp only [ramanujanSubsetTerm, Finset.prod_empty, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul,
    nonconstantRamanujanSubsets]
  simp only [Nat.add_sub_cancel]
  ring

/-! ## Expansion into prime-frequency tuples -/

/-- A primitive frequency modulo `p`, represented by its least natural residue. -/
def PrimitiveFrequency (p : ℕ) :=
  {a : ℕ // a ∈ (Finset.range p).filter fun a => a.Coprime p}

instance primitiveFrequencyFintype (p : ℕ) : Fintype (PrimitiveFrequency p) :=
  Fintype.ofFinset ((Finset.range p).filter fun a => a.Coprime p) (fun _ => Iff.rfl)

/-- One primitive frequency for every prime in `T`. -/
abbrev PrimitiveFrequencyTuple (T : Finset ℕ) :=
  ∀ p : T, PrimitiveFrequency p.1

/-- The product character attached to a tuple of prime frequencies. -/
def primitiveTupleCharacter {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (m : ℕ) : ℂ :=
  ∏ p : T, fourierRoot p.1 ^ ((a p).1 * m)

/-- The exponential Ramanujan product is a sum over primitive frequency tuples. -/
theorem ramanujanSubsetTerm_eq_frequencySum (T : Finset ℕ) (m : ℕ) :
    ramanujanSubsetTerm T m =
      (∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))) *
        ∑ a : PrimitiveFrequencyTuple T, primitiveTupleCharacter a m := by
  classical
  rw [ramanujanSubsetTerm]
  have hprime (p : ℕ) :
      ramanujanCorrection p m =
        (-(1 : ℂ) / (p - 1 : ℕ)) *
          ∑ a : PrimitiveFrequency p, fourierRoot p ^ (a.1 * m) := by
    rw [ramanujanCorrection, ramanujanSum]
    rw [Finset.sum_subtype (F := primitiveFrequencyFintype p)
      ((Finset.range p).filter fun a => a.Coprime p)
      (fun _ => Iff.rfl) (fun a => fourierRoot p ^ (a * m))]
    simp only [Nat.mul_comm]
    simp only [div_eq_mul_inv, neg_mul, one_mul]
    congr 1
    exact mul_comm _ _
  simp_rw [hprime]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_attach T]
  have hatt : T.attach = (Finset.univ : Finset T) := by ext p; simp
  rw [hatt]
  simpa only [primitiveTupleCharacter] using
    (Fintype.prod_sum (R := ℂ)
      (f := fun p : T => fun a : PrimitiveFrequency p.1 =>
        fourierRoot p.1 ^ (a.1 * m)))

/-- Summing a squarefree-divisor term over a translated interval exposes
the combined interval character estimated by product Parseval. -/
theorem sum_ramanujanSubsetTerm_eq_frequencySum (T : Finset ℕ) (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) =
      (∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))) *
        ∑ a : PrimitiveFrequencyTuple T,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) := by
  simp_rw [ramanujanSubsetTerm_eq_frequencySum]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ t ∈ Finset.Icc 1 h,
      ∑ a ∈ (Finset.univ : Finset (PrimitiveFrequencyTuple T)),
        primitiveTupleCharacter a (u + t)) =
    ∑ a ∈ (Finset.univ : Finset (PrimitiveFrequencyTuple T)),
      ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)
  exact Finset.sum_comm

end

/-! ### Complete-period orthogonality for six frequency tuples -/

private theorem complex_exp_pow_nat (z : ℂ) (n : ℕ) :
    Complex.exp z ^ n = Complex.exp ((n : ℂ) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Complex.exp_add]

theorem fourierRoot_pow_of_dvd {p s k : ℕ} (hs : 0 < s) (hp : 0 < p) (hps : p ∣ s) :
    fourierRoot p ^ k = fourierRoot s ^ (k * (s / p)) := by
  have hsp : 0 < s / p := Nat.div_pos (Nat.le_of_dvd hs hps) hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hspC : ((s / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hsp)
  have hfactor : (s : ℂ) = (p : ℂ) * (s / p : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hps).symm
  simp only [fourierRoot, complex_exp_pow_nat, Nat.cast_mul]
  congr 1
  rw [hfactor]
  field_simp [hpC, hspC]

private theorem finset_prod_pow_eq_pow_sum {α : Type*} (S : Finset α)
    (f : α → ℕ) (z : ℂ) :
    ∏ x ∈ S, z ^ f x = z ^ (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih => simp [hx, ih, pow_add]

def sixFrequencyNumerator (s : ℕ) (U : Fin 6 → Finset ℕ)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : ℕ :=
  ∑ i : Fin 6, ∑ p : U i, (a i p).1 * (s / p.1)

def sixLocalFrequencyNat {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) : ℕ :=
  ∑ i : Fin 6, if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0

def sixLocalFrequency {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) : ZMod p :=
  (sixLocalFrequencyNat a p : ZMod p)

def sixPrimeCompatible (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : Prop :=
  ∀ p ∈ s.primeFactors, sixLocalFrequency a p = 0

noncomputable instance instDecidableSixPrimeCompatible
    (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    Decidable (sixPrimeCompatible s a) :=
  Classical.propDecidable _

theorem sixLocalFrequency_eq_zero_iff {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (p : ℕ) :
    sixLocalFrequency a p = 0 ↔ p ∣ sixLocalFrequencyNat a p := by
  simp [sixLocalFrequency, ZMod.natCast_eq_zero_iff]

def sixPrimeWeightedNumerator (s : ℕ) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) : ℕ :=
  ∑ p ∈ s.primeFactors, sixLocalFrequencyNat a p * (s / p)

theorem sixFrequencyNumerator_eq_primeWeighted
    (s : ℕ) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    sixFrequencyNumerator s U a = sixPrimeWeightedNumerator s a := by
  classical
  unfold sixFrequencyNumerator sixPrimeWeightedNumerator sixLocalFrequencyNat
  calc
    ∑ i : Fin 6, ∑ p : U i, (a i p).1 * (s / p.1) =
        ∑ i : Fin 6, ∑ p ∈ s.primeFactors,
          if hp : p ∈ U i then (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ p : U i, (a i p).1 * (s / p.1) =
            ∑ p : U i, if hp : p.1 ∈ U i then
              (a i ⟨p.1, hp⟩).1 * (s / p.1) else 0 := by simp
        _ = ∑ p ∈ U i, if hp : p ∈ U i then
              (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
          symm
          apply Finset.sum_subtype (U i)
          intro p
          rfl
        _ = ∑ p ∈ s.primeFactors, if hp : p ∈ U i then
              (a i ⟨p, hp⟩).1 * (s / p) else 0 := by
          apply Finset.sum_subset (hU i)
          intro p hp hpn
          simp [hpn]
    _ = ∑ p ∈ s.primeFactors, ∑ i : Fin 6,
          (if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0) * (s / p) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      split <;> simp_all
    _ = ∑ p ∈ s.primeFactors,
          (∑ i : Fin 6, if hp : p ∈ U i then (a i ⟨p, hp⟩).1 else 0) *
            (s / p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]

theorem sixPrimeWeightedNumerator_dvd_iff
    {s : ℕ} (hsq : Squarefree s) {U : Fin 6 → Finset ℕ}
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    s ∣ sixPrimeWeightedNumerator s a ↔ sixPrimeCompatible s a := by
  classical
  constructor
  · intro htotal p hp
    apply (sixLocalFrequency_eq_zero_iff a p).2
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hpTotal : p ∣ sixPrimeWeightedNumerator s a := hps.trans htotal
    have hrest : p ∣ ∑ q ∈ s.primeFactors.erase p,
        sixLocalFrequencyNat a q * (s / q) := by
      apply Finset.dvd_sum
      intro q hq
      have hq' := Finset.mem_erase.mp hq
      have hqPrime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq'.2
      have hqs : q ∣ s := Nat.dvd_of_mem_primeFactors hq'.2
      have hpProd : p ∣ q * (s / q) := by
        simpa [Nat.mul_div_cancel' hqs] using hps
      have hpQuot : p ∣ s / q := by
        rcases hpPrime.dvd_mul.mp hpProd with hpq | hpQuot
        · have hpqeq : q = p := (hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq
          exact (hq'.1 hpqeq).elim
        · exact hpQuot
      exact dvd_mul_of_dvd_right hpQuot _
    have hpTerm : p ∣ sixLocalFrequencyNat a p * (s / p) := by
      apply (Nat.dvd_add_iff_right hrest).mpr
      rw [Finset.sum_erase_add s.primeFactors
        (fun q ↦ sixLocalFrequencyNat a q * (s / q)) hp]
      exact hpTotal
    rcases hpPrime.dvd_mul.mp hpTerm with hpLocal | hpQuot
    · exact hpLocal
    · have hcop : p.Coprime (s / p) := by
        apply Nat.coprime_of_squarefree_mul
        simpa [Nat.mul_div_cancel' hps] using hsq
      exact ((hpPrime.coprime_iff_not_dvd).mp hcop hpQuot).elim
  · intro hcompat
    unfold sixPrimeWeightedNumerator
    apply Finset.dvd_sum
    intro p hp
    have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hpLocal : p ∣ sixLocalFrequencyNat a p :=
      (sixLocalFrequency_eq_zero_iff a p).1 (hcompat p hp)
    rcases hpLocal with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    calc
      p * k * (s / p) = p * (s / p) * k := by ac_rfl
      _ = s * k := by rw [Nat.mul_div_cancel' hps]

theorem sixFrequencyNumerator_dvd_iff_primeCompatible
    {s : ℕ} (hsq : Squarefree s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    s ∣ sixFrequencyNumerator s U a ↔ sixPrimeCompatible s a := by
  rw [sixFrequencyNumerator_eq_primeWeighted s hU a]
  exact sixPrimeWeightedNumerator_dvd_iff hsq a

theorem primitiveTupleCharacter_eq_fourierRoot_pow
    {s : ℕ} (hs : 0 < s) {T : Finset ℕ} (hT : T ⊆ s.primeFactors)
    (a : PrimitiveFrequencyTuple T) (u : ℕ) :
    primitiveTupleCharacter a u =
      fourierRoot s ^ ((∑ p : T, (a p).1 * (s / p.1)) * u) := by
  classical
  unfold primitiveTupleCharacter
  have hterm (p : T) :
      fourierRoot p.1 ^ ((a p).1 * u) =
        fourierRoot s ^ (((a p).1 * (s / p.1)) * u) := by
    have hp_mem : p.1 ∈ s.primeFactors := hT p.2
    have hp_prime : Nat.Prime p.1 := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd : p.1 ∣ s := Nat.dvd_of_mem_primeFactors hp_mem
    convert fourierRoot_pow_of_dvd hs hp_prime.pos hp_dvd (k := (a p).1 * u) using 1
    all_goals ring
  simp_rw [hterm]
  rw [finset_prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_mul]

theorem six_primitiveTupleCharacter_eq_fourierRoot_pow
    {s : ℕ} (hs : 0 < s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (u : ℕ) :
    ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      fourierRoot s ^ (sixFrequencyNumerator s U a * u) := by
  classical
  simp_rw [primitiveTupleCharacter_eq_fourierRoot_pow hs (hU _)]
  rw [finset_prod_pow_eq_pow_sum]
  congr 1
  unfold sixFrequencyNumerator
  rw [Finset.sum_mul]

theorem six_primitiveTupleCharacter_orthogonality_global
    {s : ℕ} (hs : 0 < s) {U : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ∑ u ∈ Finset.range s, ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      if s ∣ sixFrequencyNumerator s U a then (s : ℂ) else 0 := by
  classical
  simp_rw [six_primitiveTupleCharacter_eq_fourierRoot_pow hs hU a]
  simpa only [← Int.natCast_mul, zpow_natCast, Int.natCast_dvd_natCast,
    Nat.cast_ite, Nat.cast_zero] using
    fourierRoot_orthogonality s hs (sixFrequencyNumerator s U a : ℤ)

theorem six_primitiveTupleCharacter_orthogonality
    {s : ℕ} (hs : 0 < s) (hsq : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ∑ u ∈ Finset.range s, ∏ i : Fin 6, primitiveTupleCharacter (a i) u =
      if sixPrimeCompatible s a then (s : ℂ) else 0 := by
  classical
  rw [six_primitiveTupleCharacter_orthogonality_global hs hU a]
  by_cases h : sixPrimeCompatible s a
  · rw [if_pos h, if_pos ((sixFrequencyNumerator_dvd_iff_primeCompatible hsq hU a).2 h)]
  · rw [if_neg h, if_neg]
    intro hd
    exact h ((sixFrequencyNumerator_dvd_iff_primeCompatible hsq hU a).1 hd)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/Fundamental.lean` -/

section
/-!
# The finite Cauchy inequality used in the Montgomery--Vaughan argument

This file contains a division-free formulation of the prime-local
Cauchy--Schwarz estimate which is iterated, through the Chinese remainder
theorem, in the Montgomery--Vaughan fundamental lemma.  The squared form is
particularly convenient for moment calculations: for six functions on
`ZMod p`, a single linear congruence costs exactly `p ^ 4`.
-/

open scoped BigOperators

section FiniteCauchy

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

end FiniteCauchy

section OnePrime

variable {p : ℕ} [NeZero p]

/-- The solutions of a two-variable affine equation modulo `p`. -/
def affineSolution (u v : (ZMod p)ˣ) (c : ZMod p) :=
  {z : ZMod p × ZMod p // u.1 * z.1 + v.1 * z.2 = c}

noncomputable instance (u v : (ZMod p)ˣ) (c : ZMod p) :
    Fintype (affineSolution u v c) := by
  classical
  unfold affineSolution
  infer_instance

/-! ## Convolution form -/

/-- Unnormalised `L²` norm on a finite residue ring. -/
noncomputable def finiteL2 (f : ZMod p → ℂ) : ℝ :=
  Real.sqrt (∑ x : ZMod p, ‖f x‖ ^ 2)

/-- Unnormalised `L¹` norm on a finite residue ring. -/
noncomputable def finiteL1 (f : ZMod p → ℂ) : ℝ :=
  ∑ x : ZMod p, ‖f x‖

/-- Additive convolution on `ZMod p`. -/
def finiteConv (f g : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  ∑ y : ZMod p, f y * g (x - y)

theorem finiteL2_nonneg (f : ZMod p → ℂ) : 0 ≤ finiteL2 f :=
  Real.sqrt_nonneg _

theorem norm_le_finiteL2 (f : ZMod p → ℂ) (x : ZMod p) : ‖f x‖ ≤ finiteL2 f := by
  rw [finiteL2, ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun y _ ↦ sq_nonneg ‖f y‖) (Finset.mem_univ x))

/-- The endpoint `L² * L² → L∞` convolution inequality. -/
theorem norm_finiteConv_le (f g : ZMod p → ℂ) (x : ZMod p) :
    ‖finiteConv f g x‖ ≤ finiteL2 f * finiteL2 g := by
  calc
    ‖finiteConv f g x‖ ≤ ∑ y : ZMod p, ‖f y * g (x - y)‖ := norm_sum_le _ _
    _ = ∑ y : ZMod p, ‖f y‖ * ‖g (x - y)‖ := by simp_rw [norm_mul]
    _ ≤ Real.sqrt ((∑ y : ZMod p, ‖f y‖ ^ 2) *
        ∑ y : ZMod p, ‖g (x - y)‖ ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = finiteL2 f * finiteL2 g := by
      rw [Real.sqrt_mul (by positivity), finiteL2, finiteL2]
      congr 2
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ ↦ rfl)

/-- Convolution with an `L¹` function preserves a pointwise bound. -/
theorem norm_finiteConv_le_of_bound (f g : ZMod p → ℂ) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : ZMod p) :
    ‖finiteConv f g x‖ ≤ C * finiteL1 g := by
  calc
    ‖finiteConv f g x‖ ≤ ∑ y : ZMod p, ‖f y * g (x - y)‖ := norm_sum_le _ _
    _ = ∑ y : ZMod p, ‖f y‖ * ‖g (x - y)‖ := by simp_rw [norm_mul]
    _ ≤ ∑ y : ZMod p, C * ‖g (x - y)‖ := by
      gcongr with y
      exact hC y
    _ = C * finiteL1 g := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ ↦ rfl)

/-- Cauchy--Schwarz in the form `L¹ ≤ sqrt(card) * L²`. -/
theorem finiteL1_le (f : ZMod p → ℂ) :
    finiteL1 f ≤ Real.sqrt p * finiteL2 f := by
  calc
    finiteL1 f ≤ Real.sqrt ((∑ _x : ZMod p, (1 : ℝ) ^ 2) *
        ∑ x : ZMod p, ‖f x‖ ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      simpa [finiteL1] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ZMod p ↦ (1 : ℝ))
          (fun x ↦ ‖f x‖))
    _ = Real.sqrt p * finiteL2 f := by
      rw [Real.sqrt_mul (by positivity)]
      simp [finiteL2]

/-- Iterated convolution, with the first function as initial value. -/
def iterConv : (ZMod p → ℂ) → List (ZMod p → ℂ) → ZMod p → ℂ
  | f, [] => f
  | f, g :: gs => iterConv (finiteConv f g) gs

theorem norm_iterConv_le_of_bound (f : ZMod p → ℂ)
    (gs : List (ZMod p → ℂ)) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (x : ZMod p) :
    ‖iterConv f gs x‖ ≤ C * (gs.map finiteL1).prod := by
  induction gs generalizing f C with
  | nil => simpa [iterConv] using hC x
  | cons g gs ih =>
      simp only [iterConv, List.map_cons, List.prod_cons]
      calc
        ‖iterConv (finiteConv f g) gs x‖ ≤
            (C * finiteL1 g) * (gs.map finiteL1).prod :=
          ih _ _ (norm_finiteConv_le_of_bound f g C hC)
        _ = C * (finiteL1 g * (gs.map finiteL1).prod) := by ring

private theorem prod_finiteL1_nonneg (gs : List (ZMod p → ℂ)) :
    0 ≤ (gs.map finiteL1).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) ih

private theorem prod_finiteL1_le (gs : List (ZMod p → ℂ)) :
    (gs.map finiteL1).prod ≤
      (gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        finiteL1 g * (gs.map finiteL1).prod ≤
            (Real.sqrt p * finiteL2 g) *
              ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
          exact mul_le_mul (finiteL1_le g) ih (prod_finiteL1_nonneg gs)
            (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg g))
        _ = (Real.sqrt p * (gs.map fun _ ↦ Real.sqrt p).prod) *
              (finiteL2 g * (gs.map finiteL2).prod) := by ring

/-- The local Montgomery--Vaughan estimate for any number (at least two)
of functions.  For six functions the leading factor is `(sqrt p)^4`. -/
theorem norm_iterConv_le (f g : ZMod p → ℂ) (gs : List (ZMod p → ℂ))
    (x : ZMod p) :
    ‖iterConv f (g :: gs) x‖ ≤
      finiteL2 f * finiteL2 g *
        ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
  simp only [iterConv]
  calc
    ‖iterConv (finiteConv f g) gs x‖ ≤
        (finiteL2 f * finiteL2 g) * (gs.map finiteL1).prod :=
      norm_iterConv_le_of_bound _ _ _ (norm_finiteConv_le f g) x
    _ ≤ finiteL2 f * finiteL2 g *
        ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
      exact mul_le_mul_of_nonneg_left (prod_finiteL1_le gs)
        (mul_nonneg (finiteL2_nonneg f) (finiteL2_nonneg g))

end OnePrime

/-! ## Tensor-product / CRT iteration

`FundamentalCoordinate` packages one CRT coordinate together with its
prime-local Cauchy estimate.  `FundamentalSystem` forms finite products of
such coordinates.  Unlike a hypothesis asserting the desired global
estimate, the only analytic datum in a coordinate is the one-coordinate
operator bound proved above; the theorem below proves that these local
bounds tensorise even when each of the six functions couples all of its CRT
coordinates.
-/

structure FundamentalCoordinate where
  State : Type
  stateFintype : Fintype State
  Value : Fin 6 → Type
  valueFintype : ∀ i, Fintype (Value i)
  project : ∀ i, State → Value i
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  localBound : ∀ (f : ∀ i, Value i → ℂ),
    ‖stateFintype.elems.sum (fun s ↦ ∏ i, f i (project i s))‖ ≤
      scale * ∏ i, Real.sqrt ((valueFintype i).elems.sum (fun x ↦ ‖f i x‖ ^ 2))

/-- The local estimate after replacing the stored enumerations by specified
extensionally equal finite enumerations. -/
theorem FundamentalCoordinate.localBound_with (c : FundamentalCoordinate)
    (stateFintype : Fintype c.State)
    (valueFintype : ∀ i, Fintype (c.Value i))
    (f : ∀ i, c.Value i → ℂ) :
    letI : Fintype c.State := stateFintype
    letI (i : Fin 6) : Fintype (c.Value i) := valueFintype i
    ‖∑ s : c.State, ∏ i, f i (c.project i s)‖ ≤
      c.scale * ∏ i, Real.sqrt (∑ x : c.Value i, ‖f i x‖ ^ 2) := by
  letI : Fintype c.State := stateFintype
  letI (i : Fin 6) : Fintype (c.Value i) := valueFintype i
  have h := c.localBound f
  rw [show c.stateFintype.elems = stateFintype.elems by
    ext x
    constructor
    · intro hx
      exact stateFintype.complete x
    · intro hx
      exact c.stateFintype.complete x] at h
  simp_rw [show ∀ i, (c.valueFintype i).elems = (valueFintype i).elems by
    intro i
    ext x
    constructor
    · intro hx
      exact (valueFintype i).complete x
    · intro hx
      exact (c.valueFintype i).complete x] at h
  exact h

inductive FundamentalSystem
  | nil
  | cons (head : FundamentalCoordinate) (tail : FundamentalSystem)

namespace FundamentalSystem

@[reducible] def State : FundamentalSystem → Type
  | nil => Unit
  | cons c t => c.State × State t

@[reducible] def Value : FundamentalSystem → Fin 6 → Type
  | nil, _ => Unit
  | cons c t, i => c.Value i × Value t i

@[reducible] noncomputable def stateElements : (t : FundamentalSystem) → Finset t.State
  | nil => {()}
  | cons c t => c.stateFintype.elems ×ˢ t.stateElements

@[reducible] noncomputable def valueElements : (t : FundamentalSystem) → ∀ i,
    Finset (t.Value i)
  | nil, _ => {()}
  | cons c t, i => (c.valueFintype i).elems ×ˢ t.valueElements i

@[reducible] def project : (t : FundamentalSystem) → ∀ i, t.State → t.Value i
  | nil, _, _ => ()
  | cons c t, i, s => (c.project i s.1, t.project i s.2)

noncomputable def contraction (t : FundamentalSystem) (f : ∀ i, t.Value i → ℂ) : ℂ :=
  t.stateElements.sum fun s ↦ ∏ i, f i (t.project i s)

noncomputable def energy (t : FundamentalSystem) (i : Fin 6)
    (f : t.Value i → ℂ) : ℝ :=
  (t.valueElements i).sum fun x ↦ ‖f x‖ ^ 2

def scale : FundamentalSystem → ℝ
  | nil => 1
  | cons c t => c.scale * t.scale

theorem scale_nonneg : ∀ t : FundamentalSystem, 0 ≤ t.scale
  | nil => by simp [scale]
  | cons c t => mul_nonneg c.scale_nonneg t.scale_nonneg

/-- Montgomery--Vaughan's fundamental Cauchy/CRT inequality in tensor
form.  This is the full six-function result: functions may couple all CRT
coordinates, and the bound is the product of the prime-local scales. -/
theorem fundamental_le (t : FundamentalSystem) (f : ∀ i, t.Value i → ℂ) :
    ‖t.contraction f‖ ≤ t.scale * ∏ i, Real.sqrt (t.energy i (f i)) := by
  induction t with
  | nil =>
      change (∀ i, Unit → ℂ) at f
      unfold contraction scale energy stateElements valueElements project
      simp only [Finset.sum_singleton, one_mul]
      rw [norm_prod]
      simp only [Real.sqrt_sq_eq_abs, abs_norm]
      exact le_rfl
  | cons c t ih =>
      change (∀ i, c.Value i × t.Value i → ℂ) at f
      let hfun : ∀ i, t.Value i → ℂ := fun i y ↦
        (Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦ ‖f i (x, y)‖ ^ 2)) : ℂ)
      have hlocal (s : t.State) :
          ‖c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s))‖ ≤
            c.scale * ∏ i, Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2)) := by
        change ‖c.stateFintype.elems.sum (fun x ↦
            ∏ i, f i (c.project i x, t.project i s))‖ ≤
          c.scale * ∏ i, Real.sqrt ((c.valueFintype i).elems.sum
            (fun x ↦ ‖f i (x, t.project i s)‖ ^ 2))
        exact c.localBound (fun i x ↦ f i (x, t.project i s))
      have hnonneg (s : t.State) :
          0 ≤ ∏ i, Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
            ‖f i (x, t.project i s)‖ ^ 2)) := by positivity
      have htail_eq : t.contraction hfun =
          ((t.stateElements.sum (fun s ↦ ∏ i, Real.sqrt
            ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2))) : ℝ) : ℂ) := by
        simp [contraction, hfun]
      have htail_norm :
          ‖t.contraction hfun‖ = t.stateElements.sum (fun s ↦ ∏ i,
            Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2))) := by
        rw [htail_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact Finset.sum_nonneg fun s _ ↦ hnonneg s
      calc
        ‖(FundamentalSystem.cons c t).contraction f‖ =
            ‖t.stateElements.sum (fun s ↦ c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s)))‖ := by
                unfold contraction
                change ‖(c.stateFintype.elems ×ˢ t.stateElements).sum (fun s ↦
                  ∏ i, f i (c.project i s.1, t.project i s.2))‖ = _
                rw [Finset.sum_product_right]
        _ ≤ t.stateElements.sum (fun s ↦ ‖c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s))‖) := norm_sum_le _ _
        _ ≤ t.stateElements.sum (fun s ↦ c.scale * ∏ i,
              Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
                ‖f i (x, t.project i s)‖ ^ 2))) := by
                exact Finset.sum_le_sum fun s _ ↦ hlocal s
        _ = c.scale * ‖t.contraction hfun‖ := by
              rw [htail_norm, Finset.mul_sum]
        _ ≤ c.scale * (t.scale * ∏ i, Real.sqrt (t.energy i (hfun i))) := by
              exact mul_le_mul_of_nonneg_left (ih hfun) c.scale_nonneg
        _ = (FundamentalSystem.cons c t).scale *
              ∏ i, Real.sqrt ((FundamentalSystem.cons c t).energy i (f i)) := by
              simp only [scale]
              rw [mul_assoc]
              congr 1
              congr 1
              apply Finset.prod_congr rfl
              intro i _
              congr 1
              simp only [energy, hfun, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _),
                Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
              change (t.valueElements i).sum (fun y ↦
                (c.valueFintype i).elems.sum (fun x ↦ ‖f i (x, y)‖ ^ 2)) =
                ((c.valueFintype i).elems ×ˢ t.valueElements i).sum
                  (fun z ↦ ‖f i z‖ ^ 2)
              rw [Finset.sum_product_right]

end FundamentalSystem

/-! ## A concrete six-active prime coordinate

This constructor is the maximal-support local CRT coordinate.  The state
variables are the successive partial sums in a fivefold convolution; this
makes the identification with `iterConv` definitional after expanding the
finite products.
-/

section PrimeCoordinate

variable (p : ℕ) [NeZero p]

abbrev SixConvolutionState :=
  ZMod p × ZMod p × ZMod p × ZMod p × ZMod p

def sixConvolutionProject (i : Fin 6) (s : SixConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2.2.2
  | 1 => s.2.2.2.1 - s.2.2.2.2
  | 2 => s.2.2.1 - s.2.2.2.1
  | 3 => s.2.1 - s.2.2.1
  | 4 => s.1 - s.2.1
  | _ => -s.1

private theorem sixConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3, f 4, f 5] 0 := by
  simp only [iterConv, finiteConv]
  rw [show (∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s)) =
      ∑ e : ZMod p, ∑ d : ZMod p, ∑ c : ZMod p, ∑ b : ZMod p, ∑ a : ZMod p,
        f 0 a * f 1 (b - a) * f 2 (c - b) * f 3 (d - c) * f 4 (e - d) * f 5 (-e) by
    simp only [Fintype.sum_prod_type]
    congr 1 with e
    congr 1 with d
    congr 1 with c
    congr 1 with b
    congr 1 with a
    simp [Fin.prod_univ_succ, sixConvolutionProject]
    ring]
  simp_rw [Finset.sum_mul]
  ring

/-- Concrete local coordinate for a prime occurring in all six
denominators.  Its exact scale is `p²`. -/
noncomputable def primeCoordinateSix : FundamentalCoordinate where
  State := SixConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := sixConvolutionProject p
  scale := (p : ℝ) ^ 2
  scale_nonneg := sq_nonneg _
  localBound := by
    intro f
    change ‖∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s)‖ ≤ _
    rw [sixConvolution_sum_eq]
    have h := norm_iterConv_le (f 0) (f 1) [f 2, f 3, f 4, f 5] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    calc
      _ ≤ finiteL2 (f 0) * finiteL2 (f 1) *
          (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * Real.sqrt p)) *
            (finiteL2 (f 2) * (finiteL2 (f 3) * (finiteL2 (f 4) * finiteL2 (f 5))))) := h
      _ = (p : ℝ) ^ 2 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        have hs : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt (by positivity)
        have hscale : Real.sqrt (p : ℝ) * (Real.sqrt p * p) = (p : ℝ) ^ 2 := by
          rw [← mul_assoc, hs]
          ring
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        rw [hscale]
        ring

def twoConvolutionProject (i : Fin 6) (a : ZMod p) : ZMod p :=
  match i.1 with
  | 0 => a
  | 1 => -a
  | _ => 0

/-- Concrete coordinate for a prime occurring in the first two factors.
The remaining four coordinates are forced to zero. -/
noncomputable def primeCoordinateTwo : FundamentalCoordinate where
  State := ZMod p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := twoConvolutionProject p
  scale := 1
  scale_nonneg := zero_le_one
  localBound := by
    intro f
    change ‖∑ a : ZMod p, ∏ i, f i (twoConvolutionProject p i a)‖ ≤ _
    have heq : (∑ a : ZMod p, ∏ i, f i (twoConvolutionProject p i a)) =
        finiteConv (f 0) (f 1) 0 * (f 2 0 * f 3 0 * f 4 0 * f 5 0) := by
      simp [finiteConv, Fin.prod_univ_succ, twoConvolutionProject]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [heq, one_mul, norm_mul]
    calc
      ‖finiteConv (f 0) (f 1) 0‖ * ‖f 2 0 * f 3 0 * f 4 0 * f 5 0‖ ≤
          (finiteL2 (f 0) * finiteL2 (f 1)) *
            (finiteL2 (f 2) * finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5)) := by
        have hconst : ‖f 2 0 * f 3 0 * f 4 0 * f 5 0‖ ≤
            finiteL2 (f 2) * finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5) := by
          have h2 := norm_le_finiteL2 (f 2) 0
          have h3 := norm_le_finiteL2 (f 3) 0
          have h4 := norm_le_finiteL2 (f 4) 0
          have h5 := norm_le_finiteL2 (f 5) 0
          simp only [norm_mul]
          exact mul_le_mul
            (mul_le_mul
              (mul_le_mul h2 h3 (norm_nonneg _) (finiteL2_nonneg _))
              h4
              (norm_nonneg _)
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _)))
            h5
            (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
              (finiteL2_nonneg _))
        exact mul_le_mul (norm_finiteConv_le _ _ _) hconst (norm_nonneg _)
          (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
      _ = ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

/-- Reindex a prime-local coordinate by a permutation of the six factors. -/
noncomputable def permutePrimeCoordinate
    (S : Type) [Fintype S] (baseProject : Fin 6 → S → ZMod p)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (baseProject i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2))
    (σ : Equiv.Perm (Fin 6)) : FundamentalCoordinate where
  State := S
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fun i s ↦ baseProject (σ.symm i) s
  scale := scale
  scale_nonneg := hscale
  localBound := by
    intro f
    change ‖∑ s : S, ∏ i, f i (baseProject (σ.symm i) s)‖ ≤ _
    have h := hbound (fun i ↦ f (σ i))
    calc
      ‖∑ s : S, ∏ i, f i (baseProject (σ.symm i) s)‖ =
          ‖∑ s : S, ∏ i, f (σ i) (baseProject i s)‖ := by
        congr 2
        funext s
        symm
        exact Fintype.prod_equiv σ _ _ (by simp)
      _ ≤ scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f (σ i) x‖ ^ 2) := h
      _ = scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        congr 1
        exact Fintype.prod_equiv σ _ _ (by simp)

abbrev ThreeConvolutionState := ZMod p × ZMod p

def threeConvolutionProject (i : Fin 6) (s : ThreeConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2
  | 1 => s.1 - s.2
  | 2 => -s.1
  | _ => 0

private theorem threeConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : ThreeConvolutionState p, ∏ i, f i (threeConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2] 0 * (f 3 0 * f 4 0 * f 5 0) := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, threeConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first three factors. -/
noncomputable def primeCoordinateThree : FundamentalCoordinate where
  State := ThreeConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := threeConvolutionProject p
  scale := Real.sqrt p
  scale_nonneg := Real.sqrt_nonneg _
  localBound := by
    intro f
    change ‖∑ s : ThreeConvolutionState p, ∏ i, f i (threeConvolutionProject p i s)‖ ≤ _
    rw [threeConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    have hconst : ‖f 3 0 * f 4 0 * f 5 0‖ ≤
        finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5) := by
      have h3 := norm_le_finiteL2 (f 3) 0
      have h4 := norm_le_finiteL2 (f 4) 0
      have h5 := norm_le_finiteL2 (f 5) 0
      simp only [norm_mul]
      exact mul_le_mul (mul_le_mul h3 h4 (norm_nonneg _) (finiteL2_nonneg _)) h5
        (norm_nonneg _) (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          (Real.sqrt p * finiteL2 (f 2))) *
          (finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5)) :=
        mul_le_mul hactive hconst (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg _)))
      _ = Real.sqrt p * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

abbrev FourConvolutionState := ZMod p × ZMod p × ZMod p

def fourConvolutionProject (i : Fin 6) (s : FourConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2
  | 1 => s.2.1 - s.2.2
  | 2 => s.1 - s.2.1
  | 3 => -s.1
  | _ => 0

private theorem fourConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : FourConvolutionState p, ∏ i, f i (fourConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3] 0 * (f 4 0 * f 5 0) := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, fourConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first four factors. -/
noncomputable def primeCoordinateFour : FundamentalCoordinate where
  State := FourConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fourConvolutionProject p
  scale := Real.sqrt p ^ 2
  scale_nonneg := sq_nonneg _
  localBound := by
    intro f
    change ‖∑ s : FourConvolutionState p, ∏ i, f i (fourConvolutionProject p i s)‖ ≤ _
    rw [fourConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    have hconst : ‖f 4 0 * f 5 0‖ ≤ finiteL2 (f 4) * finiteL2 (f 5) := by
      simp only [norm_mul]
      exact mul_le_mul (norm_le_finiteL2 _ _) (norm_le_finiteL2 _ _)
        (norm_nonneg _) (finiteL2_nonneg _)
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          ((Real.sqrt p * Real.sqrt p) * (finiteL2 (f 2) * finiteL2 (f 3)))) *
          (finiteL2 (f 4) * finiteL2 (f 5)) :=
        mul_le_mul hactive hconst (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))))
      _ = Real.sqrt p ^ 2 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

abbrev FiveConvolutionState := ZMod p × ZMod p × ZMod p × ZMod p

def fiveConvolutionProject (i : Fin 6) (s : FiveConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2.2
  | 1 => s.2.2.1 - s.2.2.2
  | 2 => s.2.1 - s.2.2.1
  | 3 => s.1 - s.2.1
  | 4 => -s.1
  | _ => 0

private theorem fiveConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : FiveConvolutionState p, ∏ i, f i (fiveConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3, f 4] 0 * f 5 0 := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, fiveConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first five factors. -/
noncomputable def primeCoordinateFive : FundamentalCoordinate where
  State := FiveConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fiveConvolutionProject p
  scale := Real.sqrt p ^ 3
  scale_nonneg := pow_nonneg (Real.sqrt_nonneg _) _
  localBound := by
    intro f
    change ‖∑ s : FiveConvolutionState p, ∏ i, f i (fiveConvolutionProject p i s)‖ ≤ _
    rw [fiveConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3, f 4] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          ((Real.sqrt p * (Real.sqrt p * Real.sqrt p)) *
            (finiteL2 (f 2) * (finiteL2 (f 3) * finiteL2 (f 4))))) *
          finiteL2 (f 5) :=
        mul_le_mul hactive (norm_le_finiteL2 _ _) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _)
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
              (mul_nonneg (finiteL2_nonneg _)
                (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _)))))
      _ = Real.sqrt p ^ 3 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        have hs : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        rw [show Real.sqrt (p : ℝ) ^ 3 = Real.sqrt p * p by
          rw [pow_succ, hs, mul_comm]]
        ring

private noncomputable def finsetSupportPerm (s t : Finset (Fin 6))
    (h : s.card = t.card) : Equiv.Perm (Fin 6) :=
  Classical.choose (Equiv.Perm.exists_map_finset_eq s t h)

/-- The prime-local Montgomery--Vaughan coordinate for an arbitrary support
of cardinality at least two.  All six value types are `ZMod p`; coordinates
outside `J` are forced to zero.  The scale is exactly
`(sqrt p) ^ (J.card - 2)`. -/
noncomputable def primeCoordinateForSupport (J : Finset (Fin 6))
    (hJ : 2 ≤ J.card) : FundamentalCoordinate :=
  if h2 : J.card = 2 then
    permutePrimeCoordinate p (ZMod p) (twoConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h2, primeCoordinateTwo] using
          (primeCoordinateTwo p).localBound_with
            (by change Fintype (ZMod p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1} : Finset (Fin 6)) J (by simp [h2]))
  else if h3 : J.card = 3 then
    permutePrimeCoordinate p (ThreeConvolutionState p) (threeConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h3, primeCoordinateThree] using
          (primeCoordinateThree p).localBound_with
            (by change Fintype (ThreeConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2} : Finset (Fin 6)) J (by simp [h3]))
  else if h4 : J.card = 4 then
    permutePrimeCoordinate p (FourConvolutionState p) (fourConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        rw [h4]
        change ‖∑ s : FourConvolutionState p,
          ∏ i, f i (fourConvolutionProject p i s)‖ ≤ _
        rw [fourConvolution_sum_eq, norm_mul]
        have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3] 0
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one] at hactive
        have hconst : ‖f 4 0 * f 5 0‖ ≤ finiteL2 (f 4) * finiteL2 (f 5) := by
          simp only [norm_mul]
          exact mul_le_mul (norm_le_finiteL2 _ _) (norm_le_finiteL2 _ _)
            (norm_nonneg _) (finiteL2_nonneg _)
        calc
          _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
              ((Real.sqrt p * Real.sqrt p) *
                (finiteL2 (f 2) * finiteL2 (f 3)))) *
              (finiteL2 (f 4) * finiteL2 (f 5)) :=
            mul_le_mul hactive hconst (norm_nonneg _)
              (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
                (mul_nonneg
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
                  (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))))
          _ = Real.sqrt p ^ (4 - 2) *
              ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
            simp only [finiteL2]
            norm_num
            simp [Fin.prod_univ_succ]
            ring)
      (finsetSupportPerm ({0, 1, 2, 3} : Finset (Fin 6)) J (by simp [h4]))
  else if h5 : J.card = 5 then
    permutePrimeCoordinate p (FiveConvolutionState p) (fiveConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h5, primeCoordinateFive] using
          (primeCoordinateFive p).localBound_with
            (by change Fintype (FiveConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2, 3, 4} : Finset (Fin 6)) J (by simp [h5]))
  else
    have h6 : J.card = 6 := by
      have hle : J.card ≤ 6 := by simpa using J.card_le_univ
      omega
    permutePrimeCoordinate p (SixConvolutionState p) (sixConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        have hs : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
        simpa [h6, primeCoordinateSix, pow_succ, hs, mul_comm, mul_left_comm,
          mul_assoc] using
          (primeCoordinateSix p).localBound_with
            (by change Fintype (SixConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) J (by simp [h6]))

@[simp] theorem primeCoordinateForSupport_scale (J : Finset (Fin 6))
    (hJ : 2 ≤ J.card) :
    (primeCoordinateForSupport p J hJ).scale = Real.sqrt p ^ (J.card - 2) := by
  unfold primeCoordinateForSupport
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

end PrimeCoordinate

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/CompatibleFundamental.lean` -/

section
/-!
# The compatible-frequency / fundamental-lemma bridge

The Fourier expansion uses six families of primitive frequencies and retains
only tuples satisfying `sixPrimeCompatible`.  `FundamentalSystem`, on the
other hand, is phrased as a contraction over a finite tensor system.  This
file gives the exact, reusable bridge between those two presentations.

The data in `CompatibleFundamentalModel` is entirely finite and structural:
it identifies the primitive value domains and the compatible state domain
inside a `FundamentalSystem`.  The analytic estimate is then a direct
consequence of `FundamentalSystem.fundamental_le`; no estimate is stored in
the model.
-/

open scoped BigOperators

noncomputable section

/-- Six labelled primitive-frequency tuples for a fixed support family. -/
abbrev SixPrimitiveFrequencyTuple (U : Fin 6 → Finset ℕ) :=
  ∀ i, PrimitiveFrequencyTuple (U i)

/-- The finite subtype of globally compatible primitive tuples. -/
abbrev CompatiblePrimitiveTuple (s : ℕ) (U : Fin 6 → Finset ℕ) :=
  {a : SixPrimitiveFrequencyTuple U // sixPrimeCompatible s a}

/-- The compatible contraction attached to six functions on primitive
frequency tuples. -/
noncomputable def compatibleFrequencyContraction (s : ℕ) (U : Fin 6 → Finset ℕ)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) : ℂ := by
  classical
  exact ∑ a : SixPrimitiveFrequencyTuple U,
    if sixPrimeCompatible s a then ∏ i, f i (a i) else 0

/-- The interval Fourier transform on a primitive prime-frequency tuple. -/
def primitiveIntervalFourier {T : Finset ℕ} (h : ℕ)
    (a : PrimitiveFrequencyTuple T) : ℂ :=
  ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t

/-- The compatible sixfold interval contraction occurring after complete
period orthogonality. -/
def compatibleIntervalContraction (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℂ :=
  compatibleFrequencyContraction s U
    (fun _ a ↦ primitiveIntervalFourier h a)

/-- A finite structural realization of compatible primitive tuples inside a
`FundamentalSystem`.

The system is allowed to contain zero/nonprimitive values and states.  The
finsets `valueDomain` select precisely the primitive values.  Consequently
the selected state domain consists of those system states all of whose six
projections are primitive. -/
structure CompatibleFundamentalModel (s : ℕ)
    (U : Fin 6 → Finset ℕ) where
  system : FundamentalSystem
  valueDomain : ∀ i, Finset (FundamentalSystem.Value system i)
  valueDomain_subset : ∀ i, valueDomain i ⊆ FundamentalSystem.valueElements system i
  valueEquiv : ∀ i,
    PrimitiveFrequencyTuple (U i) ≃
      {x : FundamentalSystem.Value system i // x ∈ valueDomain i}
  stateEquiv : CompatiblePrimitiveTuple s U ≃
    {x : FundamentalSystem.State system //
      x ∈ FundamentalSystem.stateElements system ∧
        ∀ i, FundamentalSystem.project system i x ∈ valueDomain i}
  project_encode : ∀ (a : CompatiblePrimitiveTuple s U) (i : Fin 6),
    ((valueEquiv i) (a.1 i)).1 =
      FundamentalSystem.project system i ((stateEquiv a).1)

namespace CompatibleFundamentalModel

variable {s : ℕ} {U : Fin 6 → Finset ℕ}

/-- Extend a function on primitive values by zero to the whole value space
of the tensor system. -/
noncomputable def extend (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) (x : M.system.Value i) : ℂ := by
  classical
  exact if hx : x ∈ M.valueDomain i then
      f i ((M.valueEquiv i).symm ⟨x, hx⟩)
    else 0

@[simp] theorem extend_valueEquiv (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    M.extend f i ((M.valueEquiv i a).1) = f i a := by
  simp [extend]

theorem extend_eq_zero_of_not_mem (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ)
    (i : Fin 6) {x : M.system.Value i} (hx : x ∉ M.valueDomain i) :
    M.extend f i x = 0 := by
  simp [extend, hx]

/-- The tensor energy of the zero extension is exactly the primitive `L²`
energy, with no inactive-coordinate cardinality loss. -/
theorem energy_extend_eq (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) (i : Fin 6) :
    M.system.energy i (M.extend f i) =
      ∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2 := by
  classical
  rw [FundamentalSystem.energy]
  calc
    (M.system.valueElements i).sum (fun x ↦ ‖M.extend f i x‖ ^ 2) =
        (M.valueDomain i).sum (fun x ↦ ‖M.extend f i x‖ ^ 2) := by
      symm
      apply Finset.sum_subset (M.valueDomain_subset i)
      intro x hxall hxdomain
      rw [M.extend_eq_zero_of_not_mem f i hxdomain]
      simp
    _ = ∑ x : {x : M.system.Value i // x ∈ M.valueDomain i},
          ‖M.extend f i x.1‖ ^ 2 := by
      apply Finset.sum_subtype
      intro x
      rfl
    _ = ∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2 := by
      symm
      apply Fintype.sum_equiv (M.valueEquiv i)
      intro a
      simp

/-- After zero extension, the full system contraction is exactly the sum
over compatible primitive tuples. -/
theorem contraction_extend_eq (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) :
    M.system.contraction (M.extend f) = compatibleFrequencyContraction s U f := by
  classical
  let good : M.system.State → Prop := fun x ↦
    ∀ i, M.system.project i x ∈ M.valueDomain i
  have hzero {x : M.system.State} (hx : ¬ good x) :
      ∏ i, M.extend f i (M.system.project i x) = 0 := by
    have hex : ∃ i, M.system.project i x ∉ M.valueDomain i := by
      simpa [good] using hx
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact M.extend_eq_zero_of_not_mem f i hi
  have hfull_filter :
      M.system.stateElements.sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) =
        (M.system.stateElements.filter good).sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hgood : good x
    · rw [if_pos hgood]
    · rw [if_neg hgood, hzero hgood]
  have hstate_subtype :
      (M.system.stateElements.filter good).sum
          (fun x ↦ ∏ i, M.extend f i (M.system.project i x)) =
        ∑ x : {x : M.system.State // x ∈ M.system.stateElements.filter good},
          ∏ i, M.extend f i (M.system.project i x.1) := by
    apply Finset.sum_subtype
    intro x
    rfl
  have hcompatible_subtype :
      (∑ a : CompatiblePrimitiveTuple s U, ∏ i, f i (a.1 i)) =
        ∑ x : {x : M.system.State // x ∈ M.system.stateElements.filter good},
          ∏ i, M.extend f i (M.system.project i x.1) := by
    let e : CompatiblePrimitiveTuple s U ≃
        {x : M.system.State // x ∈ M.system.stateElements.filter good} :=
      M.stateEquiv.trans
        { toFun := fun x ↦ ⟨x.1, Finset.mem_filter.mpr ⟨x.2.1, x.2.2⟩⟩
          invFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).1,
            (Finset.mem_filter.mp x.2).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    apply Fintype.sum_equiv e
    intro a
    apply Finset.prod_congr rfl
    intro i hi
    change f i (a.1 i) =
      M.extend f i (M.system.project i (M.stateEquiv a).1)
    rw [← M.project_encode a i, M.extend_valueEquiv]
  have hite_subtype : compatibleFrequencyContraction s U f =
      ∑ a : CompatiblePrimitiveTuple s U, ∏ i, f i (a.1 i) := by
    unfold compatibleFrequencyContraction
    rw [show (∑ a : SixPrimitiveFrequencyTuple U,
        if sixPrimeCompatible s a then ∏ i, f i (a i) else 0) =
        ∑ a ∈ (Finset.univ : Finset (SixPrimitiveFrequencyTuple U)).filter
            (sixPrimeCompatible s), ∏ i, f i (a i) by
      rw [Finset.sum_filter]]
    apply Finset.sum_subtype
    intro a
    simp
  rw [FundamentalSystem.contraction, hfull_filter, hstate_subtype,
    ← hcompatible_subtype, ← hite_subtype]

/-- The arbitrary-support compatible-frequency contraction estimate.  Once
a finite CRT model is supplied, the conclusion follows solely from the
proved tensorized fundamental inequality. -/
theorem compatibleFrequencyContraction_le
    (M : CompatibleFundamentalModel s U)
    (f : ∀ i, PrimitiveFrequencyTuple (U i) → ℂ) :
    ‖compatibleFrequencyContraction s U f‖ ≤
      M.system.scale *
        ∏ i, Real.sqrt (∑ a : PrimitiveFrequencyTuple (U i), ‖f i a‖ ^ 2) := by
  rw [← M.contraction_extend_eq f]
  simpa only [M.energy_extend_eq f] using
    M.system.fundamental_le (M.extend f)

/-- Specialization to the six interval Fourier transforms used in the
moment expansion. -/
theorem compatibleIntervalContraction_le
    (M : CompatibleFundamentalModel s U) (h : ℕ) :
    ‖compatibleIntervalContraction s h U‖ ≤
      M.system.scale *
        ∏ i, Real.sqrt
          (∑ a : PrimitiveFrequencyTuple (U i),
            ‖primitiveIntervalFourier h a‖ ^ 2) := by
  exact M.compatibleFrequencyContraction_le
    (fun _ a ↦ primitiveIntervalFourier h a)

end CompatibleFundamentalModel

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/CompatibleStateEquiv.lean` -/

section
/-!
# Compatible prime states on a six-element support

For a nonempty support `J : Finset (Fin 6)`, a vector over `ZMod p` which is
zero off `J` and whose coordinates sum to zero is freely determined by all
but one of its coordinates.  This file gives the explicit equivalence and
the resulting cardinality `p ^ (J.card - 1)` (for prime `p`).
-/

open scoped BigOperators

/-- A prime-local compatible state: it is supported on `J` and its six
coordinates have sum zero. -/
def CompatiblePrimeState (p : ℕ) (J : Finset (Fin 6)) :=
  {a : Fin 6 → ZMod p //
    (∀ i, i ∉ J → a i = 0) ∧ ∑ i, a i = 0}

namespace CompatiblePrimeState

variable {p : ℕ} {J : Finset (Fin 6)}

@[simp] lemma zero_outside (a : CompatiblePrimeState p J) {i : Fin 6}
    (hi : i ∉ J) : a.1 i = 0 :=
  a.2.1 i hi

@[simp] lemma sum_eq_zero (a : CompatiblePrimeState p J) :
    ∑ i, a.1 i = 0 :=
  a.2.2

/-- Sum of a function over the subtype associated with `J.erase j0`, written
using `attach` so no choice of membership proofs enters later formulas. -/
def eraseSum (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) : ZMod p :=
  ∑ k ∈ (J.erase j0).attach, f k

/-- Extend freely chosen values on `J.erase j0` to a compatible vector by
putting at `j0` the negative of their sum and putting zero off `J`. -/
def extendErase (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) : Fin 6 → ZMod p :=
  fun i ↦ if hij : i = j0 then
      -eraseSum J j0 f
    else if hiJ : i ∈ J then
      f ⟨i, Finset.mem_erase.mpr ⟨hij, hiJ⟩⟩
    else 0

@[simp] lemma extendErase_apply_j0 (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p) :
    extendErase J j0 f j0 = -eraseSum J j0 f := by
  simp [extendErase]

@[simp] lemma extendErase_apply_of_mem_erase (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hi : i ∈ J.erase j0) :
    extendErase J j0 f i = f ⟨i, hi⟩ := by
  have hij : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hiJ : i ∈ J := (Finset.mem_erase.mp hi).2
  simp [extendErase, hij, hiJ]

@[simp] lemma extendErase_apply_of_not_mem (J : Finset (Fin 6)) (j0 : Fin 6)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hi : i ∉ J) (hij : i ≠ j0) :
    extendErase J j0 f i = 0 := by
  simp [extendErase, hij, hi]

private lemma sum_extendErase (J : Finset (Fin 6)) (j0 : Fin 6)
    (hj0 : j0 ∈ J) (f : ↑(J.erase j0) → ZMod p) :
    ∑ i, extendErase J j0 f i = 0 := by
  classical
  let g : Fin 6 → ZMod p := extendErase J j0 f
  have hsupport :
      (∑ i ∈ J, g i) = ∑ i : Fin 6, g i := by
    apply Finset.sum_subset (Finset.subset_univ J)
    intro i _ hiJ
    have hij : i ≠ j0 := by
      intro h
      subst i
      exact hiJ hj0
    exact extendErase_apply_of_not_mem J j0 f hiJ hij
  have herase :
      (∑ i ∈ J.erase j0, g i) =
        eraseSum J j0 f := by
    calc
      (∑ i ∈ J.erase j0, g i) =
          ∑ k ∈ (J.erase j0).attach, g k := by
            rw [Finset.sum_attach]
      _ = ∑ k ∈ (J.erase j0).attach, f k := by
        apply Finset.sum_congr rfl
        intro k _
        exact extendErase_apply_of_mem_erase J j0 f k.2
      _ = eraseSum J j0 f := rfl
  rw [← hsupport, ← Finset.sum_erase_add J g hj0, herase]
  simp [g]

/-- The explicit equivalence obtained by deleting one chosen support
coordinate. -/
def compatiblePrimeStateEquivErase (p : ℕ) (J : Finset (Fin 6))
    (j0 : Fin 6) (hj0 : j0 ∈ J) :
    CompatiblePrimeState p J ≃ (↑(J.erase j0) → ZMod p) where
  toFun a := fun i ↦ a.1 i
  invFun f := ⟨extendErase J j0 f, by
    constructor
    · intro i hiJ
      have hij : i ≠ j0 := by
        intro h
        subst i
        exact hiJ hj0
      exact extendErase_apply_of_not_mem J j0 f hiJ hij
    · exact sum_extendErase J j0 hj0 f⟩
  left_inv a := by
    apply Subtype.ext
    change extendErase J j0 (fun i : ↑(J.erase j0) ↦ a.1 i) = a.1
    funext i
    by_cases hij : i = j0
    · subst i
      have hsmall :
          eraseSum J j0 (fun k ↦ a.1 k) =
            ∑ i ∈ J.erase j0, a.1 i := by
        unfold eraseSum
        rw [Finset.sum_attach]
      have hsupport :
          (∑ i ∈ J, a.1 i) = ∑ i : Fin 6, a.1 i := by
        apply Finset.sum_subset (Finset.subset_univ J)
        intro i _ hiJ
        exact a.2.1 i hiJ
      have hsplit : (∑ i ∈ J.erase j0, a.1 i) + a.1 j0 = 0 := by
        rw [Finset.sum_erase_add J a.1 hj0, hsupport]
        exact a.2.2
      have hjvalue : a.1 j0 = -(∑ i ∈ J.erase j0, a.1 i) := by
        exact eq_neg_of_add_eq_zero_right hsplit
      simp only [extendErase_apply_j0]
      rw [hsmall, hjvalue]
    · by_cases hiJ : i ∈ J
      · have hi : i ∈ J.erase j0 := Finset.mem_erase.mpr ⟨hij, hiJ⟩
        exact extendErase_apply_of_mem_erase J j0 _ hi
      · rw [extendErase_apply_of_not_mem J j0 _ hiJ hij, a.2.1 i hiJ]
  right_inv f := by
    change (fun i : ↑(J.erase j0) ↦ extendErase J j0 f i) = f
    funext i
    exact extendErase_apply_of_mem_erase J j0 f i.2

@[simp] lemma compatiblePrimeStateEquivErase_apply
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (a : CompatiblePrimeState p J) (i : ↑(J.erase j0)) :
    compatiblePrimeStateEquivErase p J j0 hj0 a i = a.1 i :=
  rfl

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_mem
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p)
    (i : ↑(J.erase j0)) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 i = f i := by
  exact extendErase_apply_of_mem_erase J j0 f i.2

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_j0
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 j0 = -eraseSum J j0 f := by
  exact extendErase_apply_j0 J j0 f

@[simp] lemma compatiblePrimeStateEquivErase_symm_apply_outside
    (J : Finset (Fin 6)) (j0 : Fin 6) (hj0 : j0 ∈ J)
    (f : ↑(J.erase j0) → ZMod p)
    {i : Fin 6} (hiJ : i ∉ J) :
    ((compatiblePrimeStateEquivErase p J j0 hj0).symm f).1 i = 0 := by
  have hij : i ≠ j0 := fun h ↦ hiJ (h ▸ hj0)
  exact extendErase_apply_of_not_mem J j0 f hiJ hij

end CompatiblePrimeState

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/CompatiblePrimeCoordinate.lean` -/

section
/-!
# Compatible prime coordinates

This file transports the arbitrary-support prime coordinate to the concrete
subtype of supported zero-sum vectors used by the compatible model.
-/

open scoped BigOperators

noncomputable section

@[instance_reducible] private noncomputable def compatiblePrimeStateFintype
    (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : J.Nonempty) : Fintype (CompatiblePrimeState p J) := by
  let j0 := J.min' hJ
  exact Fintype.ofEquiv (↑(J.erase j0) → ZMod p)
    (CompatiblePrimeState.compatiblePrimeStateEquivErase
      p J j0 (Finset.min'_mem J hJ)).symm

private noncomputable def compatibleSupportPerm (K J : Finset (Fin 6))
    (h : K.card = J.card) : Equiv.Perm (Fin 6) :=
  Classical.choose (Equiv.Perm.exists_map_finset_eq K J h)

private theorem compatibleSupportPerm_map (K J : Finset (Fin 6))
    (h : K.card = J.card) :
    K.map (compatibleSupportPerm K J h).toEmbedding = J :=
  Classical.choose_spec (Equiv.Perm.exists_map_finset_eq K J h)

private theorem permutedProject_zero_outside
    {p : ℕ} [NeZero p] (K J : Finset (Fin 6)) (hcard : K.card = J.card)
    {S : Type} (project : Fin 6 → S → ZMod p)
    (hzero : ∀ s i, i ∉ K → project i s = 0)
    (s : S) (i : Fin 6) (hi : i ∉ J) :
    project ((compatibleSupportPerm K J hcard).symm i) s = 0 := by
  apply hzero
  intro hmem
  apply hi
  rw [← compatibleSupportPerm_map K J hcard]
  exact Finset.mem_map.mpr
    ⟨_, hmem, (compatibleSupportPerm K J hcard).apply_symm_apply i⟩

private theorem sum_permutedProject
    {p : ℕ} [NeZero p] {S : Type} (project : Fin 6 → S → ZMod p)
    (σ : Equiv.Perm (Fin 6)) (s : S) (hsum : ∑ i, project i s = 0) :
    ∑ i, project (σ.symm i) s = 0 := by
  rw [Fintype.sum_equiv σ.symm (fun i ↦ project (σ.symm i) s)
    (fun i ↦ project i s) (fun _ ↦ rfl)]
  exact hsum

private theorem twoProject_zero {p : ℕ} [NeZero p] (s : ZMod p) (i : Fin 6)
    (hi : i ∉ ({0, 1} : Finset (Fin 6))) :
    twoConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [twoConvolutionProject]

private theorem threeProject_zero {p : ℕ} [NeZero p]
    (s : ThreeConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2} : Finset (Fin 6))) :
    threeConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [threeConvolutionProject]

private theorem fourProject_zero {p : ℕ} [NeZero p]
    (s : FourConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3} : Finset (Fin 6))) :
    fourConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [fourConvolutionProject]

private theorem fiveProject_zero {p : ℕ} [NeZero p]
    (s : FiveConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3, 4} : Finset (Fin 6))) :
    fiveConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [fiveConvolutionProject]

private theorem sixProject_zero {p : ℕ} [NeZero p]
    (s : SixConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 6))) :
    sixConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all

private theorem twoProject_sum {p : ℕ} [NeZero p] (s : ZMod p) :
    ∑ i, twoConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, twoConvolutionProject]

private theorem threeProject_sum {p : ℕ} [NeZero p] (s : ThreeConvolutionState p) :
    ∑ i, threeConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, threeConvolutionProject]
  ring

private theorem fourProject_sum {p : ℕ} [NeZero p] (s : FourConvolutionState p) :
    ∑ i, fourConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, fourConvolutionProject]
  ring

private theorem fiveProject_sum {p : ℕ} [NeZero p] (s : FiveConvolutionState p) :
    ∑ i, fiveConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, fiveConvolutionProject]
  ring

private theorem sixProject_sum {p : ℕ} [NeZero p] (s : SixConvolutionState p) :
    ∑ i, sixConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, sixConvolutionProject]
  ring

private theorem twoProject_injective {p : ℕ} [NeZero p] :
    Function.Injective (fun s : ZMod p ↦ fun i ↦ twoConvolutionProject p i s) := by
  intro s t h
  simpa [twoConvolutionProject] using congrFun h 0

private theorem threeProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : ThreeConvolutionState p ↦ fun i ↦ threeConvolutionProject p i s) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [threeConvolutionProject] at h0 h2
  ext <;> simp_all

private theorem fourProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : FourConvolutionState p ↦ fun i ↦ fourConvolutionProject p i s) := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [fourConvolutionProject] at h0 h2 h3
  ext <;> simp_all

private theorem fiveProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : FiveConvolutionState p ↦ fun i ↦ fiveConvolutionProject p i s) := by
  rintro ⟨a, b, c, d⟩ ⟨e, f, g, h⟩ hv
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  simp only [fiveConvolutionProject] at h0 h2 h3 h4
  ext <;> simp_all

private theorem sixProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : SixConvolutionState p ↦ fun i ↦ sixConvolutionProject p i s) := by
  rintro ⟨a, b, c, d, e⟩ ⟨f, g, h, k, l⟩ hv
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  have h5 := congrFun hv 5
  simp only [sixConvolutionProject] at h0 h2 h3 h4 h5
  ext <;> simp_all

private theorem permutedProject_injective
    {p : ℕ} [NeZero p] {S : Type} (project : Fin 6 → S → ZMod p)
    (σ : Equiv.Perm (Fin 6))
    (hinj : Function.Injective (fun s ↦ fun i ↦ project i s)) :
    Function.Injective (fun s ↦ fun i ↦ project (σ.symm i) s) := by
  intro s t h
  apply hinj
  funext i
  simpa using congrFun h (σ i)

private theorem permutedLocalBound
    {p : ℕ} [NeZero p] {S : Type} [Fintype S]
    (project : Fin 6 → S → ZMod p) (σ : Equiv.Perm (Fin 6)) (scale : ℝ)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2)) :
    ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project (σ.symm i) s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  intro f
  have h := hbound (fun i ↦ f (σ i))
  calc
    ‖∑ s : S, ∏ i, f i (project (σ.symm i) s)‖ =
        ‖∑ s : S, ∏ i, f (σ i) (project i s)‖ := by
      congr 2
      funext s
      symm
      exact Fintype.prod_equiv σ _ _ (by simp)
    _ ≤ scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f (σ i) x‖ ^ 2) := h
    _ = scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
      congr 1
      exact Fintype.prod_equiv σ _ _ (by simp)

private theorem compatiblePrimeState_card [NeZero p]
    (J : Finset (Fin 6)) [Fintype (CompatiblePrimeState p J)] (hJ : J.Nonempty) :
    Fintype.card (CompatiblePrimeState p J) = p ^ (J.card - 1) := by
  let j0 := J.min' hJ
  rw [Fintype.card_congr (CompatiblePrimeState.compatiblePrimeStateEquivErase
    p J j0 (Finset.min'_mem J hJ))]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe]
  rw [Finset.card_erase_of_mem (Finset.min'_mem J hJ)]

private theorem fintypeElems_eq_univ {α : Type} (A : Fintype α) :
    A.elems = Finset.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact A.complete x

private noncomputable def compatibleStateEquivOfProject
    {p : ℕ} [NeZero p] {S : Type} [Fintype S] (J : Finset (Fin 6))
    [Fintype (CompatiblePrimeState p J)]
    (project : Fin 6 → S → ZMod p)
    (hzero : ∀ s i, i ∉ J → project i s = 0)
    (hsum : ∀ s, ∑ i, project i s = 0)
    (hinj : Function.Injective (fun s ↦ fun i ↦ project i s))
    (hcard : Fintype.card S = Fintype.card (CompatiblePrimeState p J)) :
    S ≃ CompatiblePrimeState p J := by
  let f : S → CompatiblePrimeState p J := fun s ↦
    ⟨fun i ↦ project i s, hzero s, hsum s⟩
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨fun s t h ↦ hinj (congrArg Subtype.val h), hcard⟩)

private theorem compatibleLocalBoundOfEquiv
    {p : ℕ} [NeZero p] {S : Type} [Fintype S] (J : Finset (Fin 6))
    [Fintype (CompatiblePrimeState p J)]
    (project : Fin 6 → S → ZMod p) (scale : ℝ)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2))
    (e : S ≃ CompatiblePrimeState p J)
    (he : ∀ s i, (e s).1 i = project i s)
    (f : Fin 6 → ZMod p → ℂ) :
    ‖∑ a : CompatiblePrimeState p J, ∏ i, f i (a.1 i)‖ ≤
      scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  calc
    _ = ‖∑ s : S, ∏ i, f i (project i s)‖ := by
      congr 1
      symm
      apply Fintype.sum_equiv e
      intro s
      simp only [he]
    _ ≤ _ := hbound f

private theorem compatiblePrimeCoordinate_localBound (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card)
    [Fintype (CompatiblePrimeState p J)]
    (f : Fin 6 → ZMod p → ℂ) :
    ‖∑ a : CompatiblePrimeState p J, ∏ i, f i (a.1 i)‖ ≤
      Real.sqrt p ^ (J.card - 2) *
        ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  classical
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  by_cases h2 : J.card = 2
  · let K : Finset (Fin 6) := {0, 1}
    have hcard : K.card = J.card := by simp [K, h2]
    let σ := compatibleSupportPerm K J hcard
    let project : Fin 6 → ZMod p → ZMod p :=
      fun i s ↦ twoConvolutionProject p (σ.symm i) s
    have hz : ∀ s i, i ∉ J → project i s = 0 := by
      intro s i hi
      exact permutedProject_zero_outside K J hcard (twoConvolutionProject p)
        twoProject_zero s i hi
    have hs : ∀ s, ∑ i, project i s = 0 := by
      intro s
      exact sum_permutedProject (twoConvolutionProject p) σ s (twoProject_sum s)
    have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
      permutedProject_injective (twoConvolutionProject p) σ twoProject_injective
    have hc : Fintype.card (ZMod p) = Fintype.card (CompatiblePrimeState p J) := by
      rw [compatiblePrimeState_card (p := p) J hJne, ZMod.card, h2]
      norm_num
    let e := compatibleStateEquivOfProject J project hz hs hinj hc
    refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
      ?_ e ?_ f
    · intro f
      apply permutedLocalBound (twoConvolutionProject p) σ _ _ f
      intro g
      simpa [h2, primeCoordinateTwo] using
        (primeCoordinateTwo p).localBound_with
          (by change Fintype (ZMod p); infer_instance)
          (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
    · intro s i
      rfl
  · by_cases h3 : J.card = 3
    · let K : Finset (Fin 6) := {0, 1, 2}
      have hcard : K.card = J.card := by simp [K, h3]
      let σ := compatibleSupportPerm K J hcard
      let project : Fin 6 → ThreeConvolutionState p → ZMod p :=
        fun i s ↦ threeConvolutionProject p (σ.symm i) s
      have hz : ∀ s i, i ∉ J → project i s = 0 := by
        intro s i hi
        exact permutedProject_zero_outside K J hcard (threeConvolutionProject p)
          threeProject_zero s i hi
      have hs : ∀ s, ∑ i, project i s = 0 := by
        intro s
        exact sum_permutedProject (threeConvolutionProject p) σ s (threeProject_sum s)
      have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
        permutedProject_injective (threeConvolutionProject p) σ threeProject_injective
      have hc : Fintype.card (ThreeConvolutionState p) =
          Fintype.card (CompatiblePrimeState p J) := by
        rw [compatiblePrimeState_card (p := p) J hJne, h3]
        simp [ThreeConvolutionState, ZMod.card]
        ring
      let e := compatibleStateEquivOfProject J project hz hs hinj hc
      refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
        ?_ e ?_ f
      · intro f
        apply permutedLocalBound (threeConvolutionProject p) σ _ _ f
        intro g
        simpa [h3, primeCoordinateThree] using
          (primeCoordinateThree p).localBound_with
            (by change Fintype (ThreeConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
      · intro s i
        rfl
    · by_cases h4 : J.card = 4
      · let K : Finset (Fin 6) := {0, 1, 2, 3}
        have hcard : K.card = J.card := by simp [K, h4]
        let σ := compatibleSupportPerm K J hcard
        let project : Fin 6 → FourConvolutionState p → ZMod p :=
          fun i s ↦ fourConvolutionProject p (σ.symm i) s
        have hz : ∀ s i, i ∉ J → project i s = 0 := by
          intro s i hi
          exact permutedProject_zero_outside K J hcard (fourConvolutionProject p)
            fourProject_zero s i hi
        have hs : ∀ s, ∑ i, project i s = 0 := by
          intro s
          exact sum_permutedProject (fourConvolutionProject p) σ s (fourProject_sum s)
        have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
          permutedProject_injective (fourConvolutionProject p) σ fourProject_injective
        have hc : Fintype.card (FourConvolutionState p) =
            Fintype.card (CompatiblePrimeState p J) := by
          rw [compatiblePrimeState_card (p := p) J hJne, h4]
          simp [FourConvolutionState, ZMod.card]
          ring
        let e := compatibleStateEquivOfProject J project hz hs hinj hc
        refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
          ?_ e ?_ f
        · intro f
          apply permutedLocalBound (fourConvolutionProject p) σ _ _ f
          intro g
          simpa [h4, primeCoordinateFour] using
            (primeCoordinateFour p).localBound_with
              (by change Fintype (FourConvolutionState p); infer_instance)
              (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
        · intro s i
          rfl
      · by_cases h5 : J.card = 5
        · let K : Finset (Fin 6) := {0, 1, 2, 3, 4}
          have hcard : K.card = J.card := by simp [K, h5]
          let σ := compatibleSupportPerm K J hcard
          let project : Fin 6 → FiveConvolutionState p → ZMod p :=
            fun i s ↦ fiveConvolutionProject p (σ.symm i) s
          have hz : ∀ s i, i ∉ J → project i s = 0 := by
            intro s i hi
            exact permutedProject_zero_outside K J hcard (fiveConvolutionProject p)
              fiveProject_zero s i hi
          have hs : ∀ s, ∑ i, project i s = 0 := by
            intro s
            exact sum_permutedProject (fiveConvolutionProject p) σ s (fiveProject_sum s)
          have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
            permutedProject_injective (fiveConvolutionProject p) σ fiveProject_injective
          have hc : Fintype.card (FiveConvolutionState p) =
              Fintype.card (CompatiblePrimeState p J) := by
            rw [compatiblePrimeState_card (p := p) J hJne, h5]
            simp [FiveConvolutionState, ZMod.card]
            ring
          let e := compatibleStateEquivOfProject J project hz hs hinj hc
          refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
            ?_ e ?_ f
          · intro f
            apply permutedLocalBound (fiveConvolutionProject p) σ _ _ f
            intro g
            simpa [h5, primeCoordinateFive] using
              (primeCoordinateFive p).localBound_with
                (by change Fintype (FiveConvolutionState p); infer_instance)
                (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
          · intro s i
            rfl
        · have h6 : J.card = 6 := by
            have hle : J.card ≤ 6 := by simpa using J.card_le_univ
            omega
          let K : Finset (Fin 6) := {0, 1, 2, 3, 4, 5}
          have hcard : K.card = J.card := by simp [K, h6]
          let σ := compatibleSupportPerm K J hcard
          let project : Fin 6 → SixConvolutionState p → ZMod p :=
            fun i s ↦ sixConvolutionProject p (σ.symm i) s
          have hz : ∀ s i, i ∉ J → project i s = 0 := by
            intro s i hi
            exact permutedProject_zero_outside K J hcard (sixConvolutionProject p)
              sixProject_zero s i hi
          have hs : ∀ s, ∑ i, project i s = 0 := by
            intro s
            exact sum_permutedProject (sixConvolutionProject p) σ s (sixProject_sum s)
          have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
            permutedProject_injective (sixConvolutionProject p) σ sixProject_injective
          have hc : Fintype.card (SixConvolutionState p) =
              Fintype.card (CompatiblePrimeState p J) := by
            rw [compatiblePrimeState_card (p := p) J hJne, h6]
            simp [SixConvolutionState, ZMod.card]
            ring
          let e := compatibleStateEquivOfProject J project hz hs hinj hc
          refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
            ?_ e ?_ f
          · intro f
            apply permutedLocalBound (sixConvolutionProject p) σ _ _ f
            intro g
            have hsqrt : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
            simpa [h6, primeCoordinateSix, pow_succ, hsqrt, mul_comm, mul_left_comm,
              mul_assoc] using
              (primeCoordinateSix p).localBound_with
                (by change Fintype (SixConvolutionState p); infer_instance)
                (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
          · intro s i
            rfl

/-- The arbitrary-support prime coordinate with its state type replaced by
the concrete supported zero-sum vector subtype.  Its data fields are a
single record literal; only the proof of `localBound` performs support-card
case analysis. -/
@[reducible] noncomputable def compatiblePrimeCoordinate (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card) : FundamentalCoordinate where
  State := CompatiblePrimeState p J
  stateFintype := compatiblePrimeStateFintype p J
    (Finset.card_pos.mp (by omega))
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fun i a ↦ a.1 i
  scale := Real.sqrt p ^ (J.card - 2)
  scale_nonneg := pow_nonneg (Real.sqrt_nonneg _) _
  localBound := by
    intro f
    simp_rw [fintypeElems_eq_univ]
    exact @compatiblePrimeCoordinate_localBound p _ J hJ
      (compatiblePrimeStateFintype p J (Finset.card_pos.mp (by omega))) f

@[simp] theorem compatiblePrimeCoordinate_scale (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card) :
    (compatiblePrimeCoordinate p J hJ).scale =
      Real.sqrt p ^ (J.card - 2) := by
  rfl

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/CompatibleModel.lean` -/

section
/-!
# The prime-by-prime compatible fundamental model

This file realizes the abstract `CompatibleFundamentalModel` by iterating the
prime-local compatible coordinates over exactly the primes used by one of the
six supports.  Omitting unused prime factors is essential: their local
compatibility equation is identically zero, and introducing them into the
tensor product would create a spurious cardinality loss.
-/

open scoped BigOperators

noncomputable section

/-- The set of the six factors in whose frequency support `p` occurs. -/
def primeSupport (U : Fin 6 → Finset ℕ) (p : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ p ∈ U i

@[simp] lemma mem_primeSupport {U : Fin 6 → Finset ℕ} {p : ℕ} {i : Fin 6} :
    i ∈ primeSupport U p ↔ p ∈ U i := by
  simp [primeSupport]

/-- The union of the six frequency supports. -/
def usedPrimes (U : Fin 6 → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion U

lemma mem_usedPrimes {U : Fin 6 → Finset ℕ} {p : ℕ} :
    p ∈ usedPrimes U ↔ ∃ i : Fin 6, p ∈ U i := by
  simp [usedPrimes]

abbrev UsedPrimeIndex (U : Fin 6 → Finset ℕ) := {p : ℕ // p ∈ usedPrimes U}

/-- The ordered list of used primes.  Its order only fixes nested product
types and has no mathematical significance. -/
def usedPrimeIndexList (U : Fin 6 → Finset ℕ) : List (UsedPrimeIndex U) :=
  (usedPrimes U).attach.toList

@[simp] lemma mem_usedPrimeIndexList {U : Fin 6 → Finset ℕ}
    (p : UsedPrimeIndex U) : p ∈ usedPrimeIndexList U := by
  simp [usedPrimeIndexList]

/-- Iteration of the compatible prime coordinate over a list of used primes. -/
noncomputable def compatibleSystemList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    List (UsedPrimeIndex U) → FundamentalSystem
  | [] => .nil
  | p :: ps => by
      letI : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      exact .cons
        (compatiblePrimeCoordinate p.1 (primeSupport U p.1) (hmult p.1 p.2))
        (compatibleSystemList s U hsub hmult ps)

/-- The full tensor system over the used primes. -/
noncomputable def compatibleSystem (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    FundamentalSystem :=
  compatibleSystemList s U hsub hmult (usedPrimeIndexList U)

/-- The residue in the `p`-coordinate belonging to a primitive-frequency
tuple, with zero inserted outside its support. -/
def primitiveResidue {T : Finset ℕ} (a : PrimitiveFrequencyTuple T) (p : ℕ) :
    ZMod p :=
  if hp : p ∈ T then ((a ⟨p, hp⟩).1 : ZMod p) else 0

@[simp] lemma primitiveResidue_of_mem {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) {p : ℕ} (hp : p ∈ T) :
    primitiveResidue a p = ((a ⟨p, hp⟩).1 : ZMod p) := by
  simp [primitiveResidue, hp]

@[simp] lemma primitiveResidue_of_not_mem {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) {p : ℕ} (hp : p ∉ T) :
    primitiveResidue a p = 0 := by
  simp [primitiveResidue, hp]

/-- Encode one primitive-frequency tuple into a nested value product. -/
def compatibleValueEncodeList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (L : List (UsedPrimeIndex U)) → (i : Fin 6) →
      PrimitiveFrequencyTuple (U i) →
        (compatibleSystemList s U hsub hmult L).Value i
  | [], _, _ => ()
  | p :: ps, i, a =>
      (primitiveResidue a p.1,
        compatibleValueEncodeList s U hsub hmult ps i a)

def compatibleValueEncode (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    (compatibleSystem s U hsub hmult).Value i :=
  compatibleValueEncodeList s U hsub hmult (usedPrimeIndexList U) i a

private lemma natCast_injective_below {p a b : ℕ} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h

private lemma compatibleValueEncodeList_component
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (i : Fin 6) (q : U i)
    (hmem : ∃ p ∈ L, p.1 = q.1)
    {a b : PrimitiveFrequencyTuple (U i)}
    (hab : compatibleValueEncodeList s U hsub hmult L i a =
      compatibleValueEncodeList s U hsub hmult L i b) : a q = b q := by
  induction L with
  | nil =>
      obtain ⟨p, hp, _⟩ := hmem
      simp at hp
  | cons p ps ih =>
      letI : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      by_cases hqp : q.1 = p.1
      · have hpU : p.1 ∈ U i := by simpa [hqp] using q.2
        have hqeq : q = ⟨p.1, hpU⟩ := Subtype.ext hqp
        have hfst := congrArg Prod.fst hab
        simp only [compatibleValueEncodeList] at hfst
        have hcast : ((a ⟨p.1, hpU⟩).1 : ZMod p.1) =
            ((b ⟨p.1, hpU⟩).1 : ZMod p.1) := by
          rw [primitiveResidue_of_mem a hpU, primitiveResidue_of_mem b hpU] at hfst
          exact hfst
        apply Subtype.ext
        rw [hqeq]
        apply natCast_injective_below (p := p.1) _ _ hcast
        · exact Finset.mem_range.mp (Finset.mem_filter.mp (a ⟨p.1, hpU⟩).2).1
        · exact Finset.mem_range.mp (Finset.mem_filter.mp (b ⟨p.1, hpU⟩).2).1
      · apply ih
        · obtain ⟨t, htL, htr⟩ := hmem
          simp only [List.mem_cons] at htL
          rcases htL with rfl | ht
          · exact (hqp htr.symm).elim
          · exact ⟨t, ht, htr⟩
        · exact congrArg Prod.snd hab

lemma compatibleValueEncodeList_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (i : Fin 6)
    (hcover : ∀ q ∈ U i, ∃ p ∈ L, p.1 = q) :
    Function.Injective (compatibleValueEncodeList s U hsub hmult L i) := by
  intro a b hab
  funext q
  exact compatibleValueEncodeList_component s U hsub hmult L i q
    (hcover q.1 q.2) hab

lemma compatibleValueEncode_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) : Function.Injective (compatibleValueEncode s U hsub hmult i) := by
  apply compatibleValueEncodeList_injective
  intro q hq
  let p : UsedPrimeIndex U := ⟨q, mem_usedPrimes.mpr ⟨i, hq⟩⟩
  exact ⟨p, mem_usedPrimeIndexList p, rfl⟩

lemma sixLocalFrequency_eq_sum_primitiveResidue
    {U : Fin 6 → Finset ℕ} (a : SixPrimitiveFrequencyTuple U) (p : ℕ) :
    sixLocalFrequency a p = ∑ i, primitiveResidue (a i) p := by
  unfold sixLocalFrequency sixLocalFrequencyNat primitiveResidue
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p ∈ U i <;> simp [hpi]

/-- The local compatible residue vector supplied by a globally compatible
primitive tuple. -/
def compatibleLocalState (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (a : CompatiblePrimitiveTuple s U) (p : UsedPrimeIndex U) :
    CompatiblePrimeState p.1 (primeSupport U p.1) := by
  refine ⟨fun i ↦ primitiveResidue (a.1 i) p.1, ?_, ?_⟩
  · intro i hi
    exact primitiveResidue_of_not_mem _ (by simpa using hi)
  · have hp : p.1 ∈ s.primeFactors := hsub p.2
    rw [← sixLocalFrequency_eq_sum_primitiveResidue]
    exact a.2 p.1 hp

/-- Encode a compatible primitive tuple in the nested state product. -/
def compatibleStateEncodeList (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (L : List (UsedPrimeIndex U)) → CompatiblePrimitiveTuple s U →
      (compatibleSystemList s U hsub hmult L).State
  | [], _ => ()
  | p :: ps, a =>
      (compatibleLocalState s U hsub a p,
        compatibleStateEncodeList s U hsub hmult ps a)

def compatibleStateEncode (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) :
    (compatibleSystem s U hsub hmult).State :=
  compatibleStateEncodeList s U hsub hmult (usedPrimeIndexList U) a

lemma project_compatibleStateEncodeList
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (a : CompatiblePrimitiveTuple s U) (i : Fin 6) :
    (compatibleSystemList s U hsub hmult L).project i
        (compatibleStateEncodeList s U hsub hmult L a) =
      compatibleValueEncodeList s U hsub hmult L i (a.1 i) := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
      apply Prod.ext
      · rfl
      · exact ih

lemma project_compatibleStateEncode
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) (i : Fin 6) :
    (compatibleSystem s U hsub hmult).project i
        (compatibleStateEncode s U hsub hmult a) =
      compatibleValueEncode s U hsub hmult i (a.1 i) :=
  project_compatibleStateEncodeList s U hsub hmult _ a i

/-- Every element of a system's explicit value finset is present. -/
lemma mem_valueElements (t : FundamentalSystem) (i : Fin 6) (x : t.Value i) :
    x ∈ t.valueElements i := by
  induction t with
  | nil => simp [FundamentalSystem.valueElements]
  | cons c t ih =>
      exact Finset.mem_product.mpr ⟨(c.valueFintype i).complete x.1, ih x.2⟩

/-- Every state is present in a system's explicit state finset. -/
lemma mem_stateElements (t : FundamentalSystem) (x : t.State) :
    x ∈ t.stateElements := by
  induction t with
  | nil => simp [FundamentalSystem.stateElements]
  | cons c t ih =>
      exact Finset.mem_product.mpr ⟨c.stateFintype.complete x.1, ih x.2⟩

/-- Jointly, the six projections of the compatible prime system determine
its state. -/
lemma compatibleSystemList_project_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) :
    Function.Injective
      (fun x : (compatibleSystemList s U hsub hmult L).State ↦
        fun i ↦ (compatibleSystemList s U hsub hmult L).project i x) := by
  induction L with
  | nil =>
      intro x y h
      cases x
      cases y
      rfl
  | cons p ps ih =>
      intro x y h
      apply Prod.ext
      · apply Subtype.ext
        funext i
        exact congrArg Prod.fst (congrFun h i)
      · apply ih
        funext i
        exact congrArg Prod.snd (congrFun h i)

lemma compatibleStateEncode_injective
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    Function.Injective (compatibleStateEncode s U hsub hmult) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply compatibleValueEncode_injective s U hsub hmult i
  rw [← project_compatibleStateEncode s U hsub hmult a i,
    ← project_compatibleStateEncode s U hsub hmult b i, hab]

/-- The selected value domain is precisely the image of primitive
frequencies. -/
def compatibleValueDomain (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) : Finset ((compatibleSystem s U hsub hmult).Value i) := by
  classical
  exact Finset.univ.image (compatibleValueEncode s U hsub hmult i)

noncomputable def compatibleValueEquiv
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) :
    PrimitiveFrequencyTuple (U i) ≃
      {x : (compatibleSystem s U hsub hmult).Value i //
        x ∈ compatibleValueDomain s U hsub hmult i} :=
  (Equiv.ofInjective _ (compatibleValueEncode_injective s U hsub hmult i)).trans
    (Equiv.setCongr (by
      ext x
      simp [compatibleValueDomain]))

@[simp] lemma compatibleValueEquiv_apply_val
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (i : Fin 6) (a : PrimitiveFrequencyTuple (U i)) :
    ((compatibleValueEquiv s U hsub hmult i) a).1 =
      compatibleValueEncode s U hsub hmult i a := rfl

/-- Local sum-zero states imply all compatibility equations belonging to
coordinates present in the list. -/
lemma compatible_of_project_eq_list
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) (a : SixPrimitiveFrequencyTuple U)
    (x : (compatibleSystemList s U hsub hmult L).State)
    (hproject : ∀ i,
      (compatibleSystemList s U hsub hmult L).project i x =
        compatibleValueEncodeList s U hsub hmult L i (a i)) :
    ∀ p ∈ L, sixLocalFrequency a p.1 = 0 := by
  induction L with
  | nil => simp
  | cons head tail ih =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with hpEq | hp
      · have peq : p = head := by exact hpEq
        subst p
        rw [sixLocalFrequency_eq_sum_primitiveResidue]
        calc
          ∑ i, primitiveResidue (a i) head.1 = ∑ i, x.1.1 i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (congrArg Prod.fst (hproject i)).symm
          _ = 0 := x.1.2.2
      · apply ih x.2 (fun i ↦ congrArg Prod.snd (hproject i)) p hp

/-- Decode a good system state into primitive tuples and prove all the
prime-compatibility equations, including the tautological equations at
unused prime factors. -/
lemma decoded_is_compatible
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (x : (compatibleSystem s U hsub hmult).State)
    (hx : ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
      compatibleValueDomain s U hsub hmult i) :
    sixPrimeCompatible s (fun i ↦
      (compatibleValueEquiv s U hsub hmult i).symm
        ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩) := by
  let a : SixPrimitiveFrequencyTuple U := fun i ↦
    (compatibleValueEquiv s U hsub hmult i).symm
      ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩
  have hencode (i : Fin 6) :
      compatibleValueEncode s U hsub hmult i (a i) =
        (compatibleSystem s U hsub hmult).project i x := by
    exact congrArg Subtype.val
      ((compatibleValueEquiv s U hsub hmult i).apply_symm_apply
        ⟨(compatibleSystem s U hsub hmult).project i x, hx i⟩)
  intro p hp
  by_cases hpused : p ∈ usedPrimes U
  · let q : UsedPrimeIndex U := ⟨p, hpused⟩
    exact compatible_of_project_eq_list s U hsub hmult
      (usedPrimeIndexList U) a x (fun i ↦ (hencode i).symm)
      q (mem_usedPrimeIndexList q)
  · rw [sixLocalFrequency_eq_sum_primitiveResidue]
    apply Finset.sum_eq_zero
    intro i hi
    apply primitiveResidue_of_not_mem
    intro hpi
    exact hpused (mem_usedPrimes.mpr ⟨i, hpi⟩)

/-- The range of the state encoding is exactly the filtered state domain
selected by the primitive value finsets. -/
lemma range_compatibleStateEncode
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    Set.range (compatibleStateEncode s U hsub hmult) =
      {x | x ∈ (compatibleSystem s U hsub hmult).stateElements ∧
        ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
          compatibleValueDomain s U hsub hmult i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨mem_stateElements _ _, ?_⟩
    intro i
    simp [compatibleValueDomain, project_compatibleStateEncode]
  · intro hx
    let a : SixPrimitiveFrequencyTuple U := fun i ↦
      (compatibleValueEquiv s U hsub hmult i).symm
        ⟨(compatibleSystem s U hsub hmult).project i x, hx.2 i⟩
    have ha : sixPrimeCompatible s a :=
      decoded_is_compatible s U hsub hmult x hx.2
    let A : CompatiblePrimitiveTuple s U := ⟨a, ha⟩
    refine ⟨A, ?_⟩
    apply compatibleSystemList_project_injective s U hsub hmult
      (usedPrimeIndexList U)
    funext i
    change (compatibleSystemList s U hsub hmult (usedPrimeIndexList U)).project i
        (compatibleStateEncodeList s U hsub hmult (usedPrimeIndexList U) A) = _
    rw [project_compatibleStateEncodeList]
    exact congrArg Subtype.val
      ((compatibleValueEquiv s U hsub hmult i).apply_symm_apply
        ⟨(compatibleSystem s U hsub hmult).project i x, hx.2 i⟩)

noncomputable def compatibleStateEquiv
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    CompatiblePrimitiveTuple s U ≃
      {x : (compatibleSystem s U hsub hmult).State //
        x ∈ (compatibleSystem s U hsub hmult).stateElements ∧
          ∀ i, (compatibleSystem s U hsub hmult).project i x ∈
            compatibleValueDomain s U hsub hmult i} :=
  (Equiv.ofInjective _ (compatibleStateEncode_injective s U hsub hmult)).trans
    (Equiv.setCongr (range_compatibleStateEncode s U hsub hmult))

@[simp] lemma compatibleStateEquiv_apply_val
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (a : CompatiblePrimitiveTuple s U) :
    ((compatibleStateEquiv s U hsub hmult) a).1 =
      compatibleStateEncode s U hsub hmult a := rfl

/-- The actual finite compatible-frequency model. -/
noncomputable def compatibleFundamentalModel
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    CompatibleFundamentalModel s U where
  system := compatibleSystem s U hsub hmult
  valueDomain := compatibleValueDomain s U hsub hmult
  valueDomain_subset := fun i x hx ↦ mem_valueElements _ _ x
  valueEquiv := compatibleValueEquiv s U hsub hmult
  stateEquiv := compatibleStateEquiv s U hsub hmult
  project_encode := by
    intro a i
    rw [compatibleValueEquiv_apply_val, compatibleStateEquiv_apply_val,
      project_compatibleStateEncode]

/-- The no-singleton formulation used after support-factor bookkeeping. -/
noncomputable def compatibleFundamentalModelOfNoSingleton
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    CompatibleFundamentalModel s U :=
  compatibleFundamentalModel s U hsub (by
    intro p hp
    have hpos : 0 < (primeSupport U p).card := by
      obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
      exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩
    have hne0 : (primeSupport U p).card ≠ 0 := Nat.ne_of_gt hpos
    have hne1 : (primeSupport U p).card ≠ 1 := hnoone p hp
    omega)

@[simp] theorem compatibleSystemList_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card)
    (L : List (UsedPrimeIndex U)) :
    (compatibleSystemList s U hsub hmult L).scale =
      (L.map fun p ↦ Real.sqrt p.1 ^ ((primeSupport U p.1).card - 2)).prod := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
      letI : NeZero p.1 :=
        ⟨(Nat.prime_of_mem_primeFactors (hsub p.2)).ne_zero⟩
      simp only [compatibleSystemList, FundamentalSystem.scale,
        List.map_cons, List.prod_cons, compatiblePrimeCoordinate_scale, ih]

@[simp] theorem compatibleSystem_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (compatibleSystem s U hsub hmult).scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) := by
  rw [compatibleSystem, compatibleSystemList_scale, usedPrimeIndexList,
    Finset.prod_map_toList]
  exact Finset.prod_attach (usedPrimes U)
    (fun p ↦ Real.sqrt p ^ ((primeSupport U p).card - 2))

@[simp] theorem compatibleFundamentalModel_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card) :
    (compatibleFundamentalModel s U hsub hmult).system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) :=
  compatibleSystem_scale s U hsub hmult

@[simp] theorem compatibleFundamentalModelOfNoSingleton_scale
    (s : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    (compatibleFundamentalModelOfNoSingleton s U hsub hnoone).system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) := by
  unfold compatibleFundamentalModelOfNoSingleton
  apply compatibleFundamentalModel_scale

/-- The concrete arbitrary-support compatible-frequency estimate in the
exact form needed by the sixth-moment expansion. -/
theorem compatibleIntervalContraction_le_of_noSingleton
    (s h : ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : usedPrimes U ⊆ s.primeFactors)
    (hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1) :
    ‖compatibleIntervalContraction s h U‖ ≤
      (∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2)) *
        ∏ i, Real.sqrt
          (∑ a : PrimitiveFrequencyTuple (U i),
            ‖primitiveIntervalFourier h a‖ ^ 2) := by
  let M := compatibleFundamentalModelOfNoSingleton s U hsub hnoone
  have hbound := M.compatibleIntervalContraction_le h
  rw [show M.system.scale =
      ∏ p ∈ usedPrimes U,
        Real.sqrt p ^ ((primeSupport U p).card - 2) by
    simpa [M] using compatibleFundamentalModelOfNoSingleton_scale
      s U hsub hnoone] at hbound
  exact hbound

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/ProductParseval.lean` -/

section
/-!
# Product Parseval lemmas for Erdős 220

This file packages the elementary Fourier calculation on a product of
prime cyclic groups.  Frequencies and points both live in
`\prod p : T, ZMod p`; the diagonal interval is inserted by the Chinese
remainder equivalence.  The final bound is deliberately stated without
normalising factors, which is the form needed by the moment expansion.
-/

open scoped BigOperators
open Finset Function

noncomputable section

/-- The product of the primes in `T`, indexed by the subtype `T`. -/
def primeProduct (T : Finset ℕ) : ℕ :=
  ∏ p : T, (p : ℕ)

/-- The product of the residue rings at the primes in `T`. -/
abbrev PrimeResidueSpace (T : Finset ℕ) :=
  ∀ p : T, ZMod (p : ℕ)

/-- Distinct members of a finite set of primes are pairwise coprime. -/
theorem primeProduct_pairwiseCoprime (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    Pairwise (Nat.Coprime on fun p : T ↦ (p : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (hT p p.property) (hT q q.property)).2
  intro hpqval
  exact hpq (Subtype.ext hpqval)

/-- A prime product is positive (also when `T` is empty). -/
theorem primeProduct_pos (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    0 < primeProduct T := by
  apply Finset.prod_pos
  intro p hp
  exact (hT p p.property).pos

/-- The Chinese-remainder identification used for the diagonal interval. -/
def primeProductCRTEq (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ZMod (primeProduct T) ≃+* PrimeResidueSpace T :=
  ZMod.prodEquivPi (fun p : T ↦ (p : ℕ))
    (primeProduct_pairwiseCoprime T hT)

/-- The combined additive character with frequency `a`, evaluated at `x`. -/
def productAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) : ℂ :=
  ∏ p, ZMod.stdAddChar (a p * x p)

/-- The sum of one standard character over a prime residue ring. -/
theorem zmod_stdAddChar_sum (p : ℕ) [NeZero p] (x : ZMod p) :
    ∑ a : ZMod p, ZMod.stdAddChar (a * x) =
      if x = 0 then (p : ℂ) else 0 := by
  split_ifs with hx
  · subst x
    simp
  · simpa only [AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hx))

/-- Orthogonality of the full family of product characters. -/
theorem productAddChar_orthogonality (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)] (x : PrimeResidueSpace T) :
    ∑ a : PrimeResidueSpace T, productAddChar T a x =
      if x = 0 then (primeProduct T : ℂ) else 0 := by
  classical
  simp only [productAddChar]
  have hfactor :
      (∑ a : PrimeResidueSpace T,
          ∏ p : T, ZMod.stdAddChar (a p * x p)) =
        ∏ p : T, ∑ a : ZMod (p : ℕ), ZMod.stdAddChar (a * x p) := by
    symm
    simpa using
      (Finset.prod_univ_sum (R := ℂ)
        (fun p : T ↦ (Finset.univ : Finset (ZMod (p : ℕ))))
        (fun p a ↦ ZMod.stdAddChar (a * x p)))
  rw [hfactor]
  simp_rw [zmod_stdAddChar_sum]
  by_cases hx : x = 0
  · subst x
    simp [primeProduct]
  · have hcoordinate : ∃ p : T, x p ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    obtain ⟨p, hp⟩ := hcoordinate
    rw [Finset.prod_eq_zero (Finset.mem_univ p)]
    · simp [hx]
    · simp [hp]

/-- Every value of a product character has norm one. -/
theorem norm_productAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) : ‖productAddChar T a x‖ = 1 := by
  rw [productAddChar, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Multiplying by the conjugate gives the character at a difference. -/
theorem productAddChar_mul_conj (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x y : PrimeResidueSpace T) :
    productAddChar T a x * starRingEnd ℂ (productAddChar T a y) =
      productAddChar T a (x - y) := by
  simp only [productAddChar, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Pi.sub_apply, mul_sub]
  calc
    ZMod.stdAddChar (a p * x p) *
          starRingEnd ℂ (ZMod.stdAddChar (a p * y p)) =
        ZMod.stdAddChar (a p * x p) /
          ZMod.stdAddChar (a p * y p) := by
      rw [div_eq_mul_inv, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
        ← Circle.coe_inv_eq_conj]
      rfl
    _ = ZMod.stdAddChar (a p * x p - a p * y p) :=
      (AddChar.map_sub_eq_div
        (ZMod.stdAddChar (N := (p : ℕ)))
        (a p * x p) (a p * y p)).symm

/-- The combined character is symmetric in its frequency and point. -/
theorem productAddChar_comm (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) :
    productAddChar T a x = productAddChar T x a := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [mul_comm]

/-- A complete product block has zero sum at every nonzero frequency. -/
theorem productAddChar_completeBlock_vanishes (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a : PrimeResidueSpace T) (ha : a ≠ 0) :
    ∑ x : PrimeResidueSpace T, productAddChar T a x = 0 := by
  calc
    ∑ x : PrimeResidueSpace T, productAddChar T a x =
        ∑ x : PrimeResidueSpace T, productAddChar T x a := by
      apply Finset.sum_congr rfl
      intro x hx
      exact productAddChar_comm T a x
    _ = 0 := by rw [productAddChar_orthogonality T, if_neg ha]

/-- The unnormalised transform of a finite injective family of product points. -/
def productFourierSum {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A : Type*} [Fintype A]
    (point : A → PrimeResidueSpace T) (a : PrimeResidueSpace T) : ℂ :=
  ∑ t, productAddChar T a (point t)

/-- Parseval for an injectively enumerated subset of the product group. -/
theorem productFourierSum_parseval {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A : Type*} [Fintype A]
    (point : A → PrimeResidueSpace T) (hpoint : Injective point) :
    ∑ a : PrimeResidueSpace T, ‖productFourierSum point a‖ ^ 2 =
      (primeProduct T : ℝ) * Fintype.card A := by
  classical
  have norm_sq_expand : ∀ a : PrimeResidueSpace T,
      (‖productFourierSum point a‖ ^ 2 : ℂ) =
        ∑ x : A, ∑ y : A, productAddChar T a (point x - point y) := by
    intro a
    have norm_sq_mul_conj : ∀ z : ℂ,
        (‖z‖ ^ 2 : ℂ) = z * starRingEnd ℂ z := by
      intro z
      norm_num [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_sq_mul_conj, productFourierSum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    exact productAddChar_mul_conj T a (point x) (point y)
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ a : PrimeResidueSpace T,
        (‖productFourierSum point a‖ ^ 2 : ℂ)) =
        ∑ x : A, ∑ y : A,
          ∑ a : PrimeResidueSpace T,
            productAddChar T a (point x - point y) := by
      simp_rw [norm_sq_expand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x : A, ∑ y : A,
          if x = y then (primeProduct T : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [productAddChar_orthogonality]
      simp only [sub_eq_zero]
      by_cases hxy : x = y
      · subst y
        simp
      · have hpneq : point x ≠ point y := fun h ↦ hxy (hpoint h)
        simp [hxy, hpneq]
    _ = (primeProduct T : ℂ) * Fintype.card A := by
      simp [mul_comm]

/-- Parseval restricted to any injectively indexed family of frequencies. -/
theorem productFourierSum_subset_parseval_le {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A B : Type*} [Fintype A] [Fintype B]
    (point : A → PrimeResidueSpace T) (hpoint : Injective point)
    (frequency : B → PrimeResidueSpace T) (hfrequency : Injective frequency) :
    ∑ b : B, ‖productFourierSum point (frequency b)‖ ^ 2 ≤
      (primeProduct T : ℝ) * Fintype.card A := by
  classical
  calc
    ∑ b : B, ‖productFourierSum point (frequency b)‖ ^ 2 =
        ∑ a ∈ (Finset.univ : Finset B).image frequency,
          ‖productFourierSum point a‖ ^ 2 := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact hfrequency hxy
    _ ≤ ∑ a : PrimeResidueSpace T,
          ‖productFourierSum point a‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = (primeProduct T : ℝ) * Fintype.card A :=
      productFourierSum_parseval point hpoint

/-- The residual interval, inserted in the product group through CRT. -/
def residualIntervalPoint (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (h : ℕ) (t : Fin (h % primeProduct T)) : PrimeResidueSpace T :=
  primeProductCRTEq T hT (t : ZMod (primeProduct T))

/-- The residual interval is injective in the product residue space. -/
theorem residualIntervalPoint_injective (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ) :
    Injective (residualIntervalPoint T hT h) := by
  intro x y hxy
  have hcast : (x.val : ZMod (primeProduct T)) =
      (y.val : ZMod (primeProduct T)) :=
    (primeProductCRTEq T hT).injective hxy
  have hmod := (ZMod.natCast_eq_natCast_iff' x.val y.val
    (primeProduct T)).1 hcast
  have hQ : 0 < primeProduct T := primeProduct_pos T hT
  have hxQ : x.val < primeProduct T :=
    lt_trans x.isLt (Nat.mod_lt h hQ)
  have hyQ : y.val < primeProduct T :=
    lt_trans y.isLt (Nat.mod_lt h hQ)
  apply Fin.ext
  simpa [Nat.mod_eq_of_lt hxQ, Nat.mod_eq_of_lt hyQ] using hmod

/-- The residual interval transform attached to a prime-frequency tuple. -/
def productResidualIntervalSum (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ)
    (a : PrimeResidueSpace T) : ℂ :=
  productFourierSum (residualIntervalPoint T hT h) a

/-! ## Compatibility with the primitive-frequency expansion in `Fourier` -/

/-- A primitive natural frequency, viewed in the corresponding residue ring. -/
def primitiveTupleToProductResidue (T : Finset ℕ)
    (a : PrimitiveFrequencyTuple T) : PrimeResidueSpace T :=
  fun p ↦ ((a p).1 : ZMod (p : ℕ))

/-- The natural-to-residue map on primitive tuples is injective. -/
theorem primitiveTupleToProductResidue_injective (T : Finset ℕ) :
    Injective (primitiveTupleToProductResidue T) := by
  intro a b hab
  funext p
  apply Subtype.ext
  have hp := congrFun hab p
  have hmod := (ZMod.natCast_eq_natCast_iff' (a p).1 (b p).1 (p : ℕ)).1 hp
  have ha_lt : (a p).1 < (p : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp (a p).2).1
  have hb_lt : (b p).1 < (p : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp (b p).2).1
  simpa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] using hmod

/-- Product characters are multiplicative under addition of product-group points. -/
theorem productAddChar_add (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x y : PrimeResidueSpace T) :
    productAddChar T a (x + y) =
      productAddChar T a x * productAddChar T a y := by
  simp only [productAddChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

/-- The product character evaluated on the diagonal natural residue. -/
def naturalProductAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (m : ℕ) : ℂ :=
  productAddChar T a (primeProductCRTEq T hT (m : ZMod (primeProduct T)))

/-- Diagonal product characters turn addition into multiplication. -/
theorem naturalProductAddChar_add (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (m n : ℕ) :
    naturalProductAddChar T hT a (m + n) =
      naturalProductAddChar T hT a m * naturalProductAddChar T hT a n := by
  rw [naturalProductAddChar, naturalProductAddChar, naturalProductAddChar,
    Nat.cast_add, map_add, productAddChar_add]

/-- Removing complete zero-sum blocks from a multiplicative sequence. -/
theorem sum_range_mul_add_of_multiplicative_block_zero
    (Q : ℕ) (f : ℕ → ℂ)
    (hadd : ∀ m n, f (m + n) = f m * f n)
    (hblock : ∑ m ∈ Finset.range Q, f m = 0) (k r : ℕ) :
    ∑ m ∈ Finset.range (Q * k + r), f m =
      ∑ m ∈ Finset.range r, f m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ]
      have hsplit : Q * k + Q + r = (Q * k + r) + Q := by omega
      rw [hsplit, Finset.sum_range_add, ih]
      have htail : ∑ x ∈ Finset.range Q, f (Q * k + r + x) = 0 := by
        calc
          ∑ x ∈ Finset.range Q, f (Q * k + r + x) =
              f (Q * k + r) * ∑ x ∈ Finset.range Q, f x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            exact hadd _ _
          _ = 0 := by rw [hblock, mul_zero]
      rw [htail, add_zero]

/-- The explicit equivalence enumerating `ZMod n` by its least natural
representatives. -/
def finNatCastEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun x := (x.val : ZMod n)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv x := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt x.isLt
  right_inv x := ZMod.natCast_zmod_val x

/-- A nontrivial diagonal product character has zero sum on one complete
prime-product block. -/
theorem naturalProductAddChar_completeBlock_vanishes (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (ha : a ≠ 0) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ m ∈ Finset.range (primeProduct T), naturalProductAddChar T hT a m = 0 := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  letI : NeZero (primeProduct T) := ⟨(primeProduct_pos T hT).ne'⟩
  calc
    ∑ m ∈ Finset.range (primeProduct T), naturalProductAddChar T hT a m =
        ∑ m : Fin (primeProduct T), naturalProductAddChar T hT a m := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp [Finset.mem_range.mp hm]
    _ =
        ∑ x : PrimeResidueSpace T, productAddChar T a x := by
      apply Fintype.sum_equiv
        ((finNatCastEquiv (primeProduct T)).trans
          (primeProductCRTEq T hT).toEquiv)
      intro m
      rfl
    _ = 0 := productAddChar_completeBlock_vanishes T a ha

/-- The standard `ZMod` character agrees with the root-of-unity convention
used by `primitiveTupleCharacter`. -/
theorem stdAddChar_natCast_eq_fourierRoot_pow (p n : ℕ) [NeZero p] :
    ZMod.stdAddChar (n : ZMod p) = fourierRoot p ^ n := by
  calc
    ZMod.stdAddChar (n : ZMod p) =
        ZMod.stdAddChar (n • (1 : ZMod p)) := by simp
    _ = ZMod.stdAddChar (1 : ZMod p) ^ n := by
      rw [AddChar.map_nsmul_eq_pow]
    _ = fourierRoot p ^ n := by
      congr 1
      simpa [fourierRoot] using (ZMod.stdAddChar_coe (N := p) (1 : ℤ))

/-- Compatibility of the natural primitive-tuple character with the CRT
product character. -/
theorem naturalProductAddChar_primitiveTuple (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimitiveFrequencyTuple T) (m : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    naturalProductAddChar T hT (primitiveTupleToProductResidue T a) m =
      primitiveTupleCharacter a m := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  rw [naturalProductAddChar, productAddChar, primitiveTupleCharacter]
  apply Finset.prod_congr rfl
  intro p hp
  have hcrt :
      primeProductCRTEq T hT (m : ZMod (primeProduct T)) p =
        (m : ZMod (p : ℕ)) := by
    unfold primeProductCRTEq primeProduct
    rw [ZMod.prodEquivPi_apply]
    exact map_natCast (ZMod.castHom
      (Finset.dvd_prod_of_mem (fun p : T ↦ (p : ℕ)) (Finset.mem_univ p))
      (ZMod (p : ℕ))) m
  rw [hcrt]
  simp only [primitiveTupleToProductResidue]
  rw [← Nat.cast_mul, stdAddChar_natCast_eq_fourierRoot_pow]

/-- A tuple of primitive frequencies on a nonempty prime set is nonzero in
the product residue space. -/
theorem primitiveTupleToProductResidue_ne_zero (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty)
    (a : PrimitiveFrequencyTuple T) :
    primitiveTupleToProductResidue T a ≠ 0 := by
  obtain ⟨p, hpT⟩ := hT0
  intro ha
  have hcoord := congrFun ha (⟨p, hpT⟩ : T)
  have hdiv : p ∣ (a ⟨p, hpT⟩).1 :=
    (ZMod.natCast_eq_zero_iff (a ⟨p, hpT⟩).1 p).1 hcoord
  have hlt : (a ⟨p, hpT⟩).1 < p :=
    Finset.mem_range.mp (Finset.mem_filter.mp (a ⟨p, hpT⟩).2).1
  have hz : (a ⟨p, hpT⟩).1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
  have hcop := (Finset.mem_filter.mp (a ⟨p, hpT⟩).2).2
  rw [hz] at hcop
  have hp1 : p = 1 := by simpa using hcop
  exact (hT p hpT).ne_one hp1

/-- Removing all complete prime-product blocks leaves precisely the residual
interval transform. -/
theorem naturalProductAddChar_sum_range_eq_residual (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (ha : a ≠ 0)
    (h : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ m ∈ Finset.range h, naturalProductAddChar T hT a m =
      productResidualIntervalSum T hT h a := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  have hdecomp : primeProduct T * (h / primeProduct T) + h % primeProduct T = h := by
    exact Nat.div_add_mod h (primeProduct T)
  calc
    ∑ m ∈ Finset.range h, naturalProductAddChar T hT a m =
        ∑ m ∈ Finset.range
          (primeProduct T * (h / primeProduct T) + h % primeProduct T),
          naturalProductAddChar T hT a m := by rw [hdecomp]
    _ = ∑ m ∈ Finset.range (h % primeProduct T),
          naturalProductAddChar T hT a m :=
      sum_range_mul_add_of_multiplicative_block_zero (primeProduct T)
        (naturalProductAddChar T hT a)
        (naturalProductAddChar_add T hT a)
        (naturalProductAddChar_completeBlock_vanishes T hT a ha)
        (h / primeProduct T) (h % primeProduct T)
    _ = productResidualIntervalSum T hT h a := by
      rw [productResidualIntervalSum, productFourierSum,
        Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp [Finset.mem_range.mp hm, naturalProductAddChar, residualIntervalPoint]

/-- Translation changes a primitive interval transform only by a unit phase;
complete blocks may therefore be discarded inside its norm. -/
theorem norm_primitiveTuple_intervalSum_eq_residual (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty)
    (a : PrimitiveFrequencyTuple T) (h u : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ =
      ‖productResidualIntervalSum T hT h
        (primitiveTupleToProductResidue T a)‖ := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  let freq := primitiveTupleToProductResidue T a
  have hfreq : freq ≠ 0 := primitiveTupleToProductResidue_ne_zero T hT hT0 a
  have hIcc : Finset.Icc 1 h =
      (Finset.range h).image (fun k ↦ k + 1) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨ht1, hth⟩
      refine ⟨t - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have himage : Set.InjOn (fun k : ℕ ↦ k + 1) (Finset.range h) := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have hsum :
      ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) =
        naturalProductAddChar T hT freq (u + 1) *
          productResidualIntervalSum T hT h freq := by
    rw [hIcc, Finset.sum_image himage]
    simp_rw [← naturalProductAddChar_primitiveTuple T hT a]
    calc
      ∑ k ∈ Finset.range h, naturalProductAddChar T hT freq (u + (k + 1)) =
          ∑ k ∈ Finset.range h,
            naturalProductAddChar T hT freq (u + 1) *
              naturalProductAddChar T hT freq k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show u + (k + 1) = (u + 1) + k by omega,
          naturalProductAddChar_add]
      _ = naturalProductAddChar T hT freq (u + 1) *
          ∑ k ∈ Finset.range h, naturalProductAddChar T hT freq k := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [naturalProductAddChar_sum_range_eq_residual T hT freq hfreq h]
  rw [hsum, norm_mul]
  have hphase : ‖naturalProductAddChar T hT freq (u + 1)‖ = 1 := by
    exact norm_productAddChar T _ _
  rw [hphase, one_mul]

/-- The directly usable primitive-frequency energy estimate.  Nonemptiness is
necessary: for `T = ∅` the sole frequency is the constant character and the
left side is `h²`. -/
theorem primitiveTuple_intervalEnergy_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty) (h u : ℕ) :
    ∑ a : PrimitiveFrequencyTuple T,
        ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ ^ 2 ≤
      (primeProduct T : ℝ) * h := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  calc
    ∑ a : PrimitiveFrequencyTuple T,
        ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ ^ 2 =
        ∑ a : PrimitiveFrequencyTuple T,
          ‖productFourierSum (residualIntervalPoint T hT h)
            (primitiveTupleToProductResidue T a)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← productResidualIntervalSum,
        norm_primitiveTuple_intervalSum_eq_residual T hT hT0 a h u]
    _ ≤ (primeProduct T : ℝ) * ((h % primeProduct T : ℕ) : ℝ) := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        (productFourierSum_subset_parseval_le
          (residualIntervalPoint T hT h)
          (residualIntervalPoint_injective T hT h)
          (primitiveTupleToProductResidue T)
          (primitiveTupleToProductResidue_injective T))
    _ ≤ (primeProduct T : ℝ) * h := by
      gcongr
      exact_mod_cast Nat.mod_le h (primeProduct T)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/IntegralRPow.lean` -/

section
noncomputable section

open Filter MeasureTheory Set

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

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

end

section
open Finset

end

@[simp] theorem Ico_inter_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Finset.Ico a b ∩ Finset.Icc b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod (s := s) (f := f) h1)

section
open Real

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

section
open Nat

private theorem _root_.Nat.cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

scoped[Chebyshev] notation "ϑ" => Erdos220.chebyshev_first

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

theorem my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

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

end

section
open Finset

private lemma _root_.Finset.Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

end

section
open Nat

@[simp] private lemma _root_.Nat.floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

end

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

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le

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

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]

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

lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x

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

@[simp] lemma prime_counting'_zero : π' 0 = 0 := by
  rfl

@[simp] lemma prime_counting'_one : π' 1 = 0 := by
  rfl

@[simp] lemma prime_counting'_two : π' 2 = 0 := by
  rfl

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

@[simp] lemma to_finset_filter
  {α : Type*} {l : List α} (p : α → Prop) [DecidableEq α] [DecidablePred p] :
  (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp

@[simp] lemma to_finset_range {n : ℕ} : (List.range n).toFinset = Finset.range n := by
  simpa using List.toFinset_range n

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/Mertens.lean` -/

section
/-!
# Weak Mertens bounds used for Erdős Problem 220

This file packages `weak_mertens_third_upper_all` at natural endpoints and
records the consequence for a product over any collection of primes bounded
by the endpoint.  The separate `h = 1` argument is needed because the source
theorem is stated only for real endpoints at least `2`.
-/

open scoped BigOperators

@[simp] lemma partial_euler_product_one : partial_euler_product 1 = 1 := by
  rw [partial_euler_product]
  have hempty : (Finset.Icc 1 1).filter Nat.Prime = ∅ := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpBounds := Finset.mem_Icc.mp hp'.1
      have hpeq : p = 1 := by omega
      subst p
      exact (Nat.not_prime_one hp'.2).elim
    · simp
  rw [hempty]
  simp

/-- The same natural-endpoint bound in the `log (2h)` form used in the
small-prime/large-prime split. -/
theorem partial_euler_product_le_log_two_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h →
      partial_euler_product h ≤ C * Real.log (2 * (h : ℝ)) := by
  obtain ⟨c, hc, hupper⟩ := weak_mertens_third_upper_all
  let C : ℝ := max c (Real.log 2)⁻¹
  have hC : 0 < C := hc.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro h hh
  by_cases hh2 : 2 ≤ h
  · have hh2R : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh2
    have hprod : 0 ≤ partial_euler_product h :=
      (by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound
    have hlog : 0 ≤ Real.log (h : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
    have hsource :
        partial_euler_product h ≤ c * Real.log (h : ℝ) := by
      simpa [Real.norm_of_nonneg hprod, Real.norm_of_nonneg hlog] using
        hupper (h : ℝ) hh2R
    have hlog_mono : Real.log (h : ℝ) ≤ Real.log (2 * (h : ℝ)) := by
      apply Real.log_le_log
      · positivity
      · nlinarith
    calc
      partial_euler_product h ≤ c * Real.log (h : ℝ) := hsource
      _ ≤ C * Real.log (h : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
      _ ≤ C * Real.log (2 * (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_mono hC.le
  · have heq : h = 1 := by omega
    subst h
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hsmall : (Real.log 2)⁻¹ ≤ C := le_max_right _ _
    have hfinal : partial_euler_product 1 ≤ C * Real.log 2 := calc
      partial_euler_product 1 = 1 := by
        exact partial_euler_product_one
      _ = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ C * Real.log 2 := mul_le_mul_of_nonneg_right hsmall hlog2.le
    simpa using hfinal

/-- Each Euler factor belonging to a prime is at least one. -/
lemma one_le_inverse_prime_factor {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ :=
    sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by
    nlinarith [inv_nonneg.2 (show (0 : ℝ) ≤ p by positivity)])

/-- The inverse product over the prime factors of a smooth integer is at
most the complete inverse prime product at the same endpoint. -/
theorem primeFactors_inverse_product_le_partial_euler_product
    {s h : ℕ} (hsmooth : ∀ p ∈ s.primeFactors, p ≤ h) :
    (∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      partial_euler_product h := by
  classical
  rw [partial_euler_product]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hsmooth p hp⟩, hpPrime⟩
  · intro p hp
    exact (one_le_inverse_prime_factor
      (Nat.prime_of_mem_primeFactors hp)).trans' (by norm_num)
  · intro p hp _
    exact one_le_inverse_prime_factor (Finset.mem_filter.mp hp).2

/-- Smoothness bounds the reciprocal totient density.  This is the
division-free form useful in moment arguments: it says
`s / φ(s) ≪ log (2h)` after multiplying through by `φ(s)`.

Squarefreeness is not needed for this consequence, because the totient
density depends only on the prime factors. -/
theorem exists_smooth_le_log_mul_totient :
    ∃ C : ℝ, 0 < C ∧ ∀ {s h : ℕ}, 0 < s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (s : ℝ) ≤ C * Real.log (2 * (h : ℝ)) * (s.totient : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := partial_euler_product_le_log_two_mul
  refine ⟨C, hC, ?_⟩
  intro s h hs hh hsmooth
  let D : ℝ := ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)
  have hDpos : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun p hp ↦ by
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
      exact sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  have hinv : D⁻¹ ≤ C * Real.log (2 * (h : ℝ)) := by
    have hsub := primeFactors_inverse_product_le_partial_euler_product hsmooth
    have hcomplete := hbound h hh
    change (∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      C * Real.log (2 * (h : ℝ))
    rw [← Finset.prod_inv_distrib]
    exact hsub.trans hcomplete
  have hphi : (s.totient : ℝ) = (s : ℝ) * D := by
    have hphiQ := congrArg (fun q : ℚ ↦ (q : ℝ))
      (Nat.totient_eq_mul_prod_factors s)
    simpa [D, Rat.cast_prod] using hphiQ
  calc
    (s : ℝ) = D⁻¹ * (s.totient : ℝ) := by
      rw [hphi]
      field_simp [hDpos.ne']
    _ ≤ (C * Real.log (2 * (h : ℝ))) * (s.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg _)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/SmallMoment.lean` -/

section
/-!
# The smooth-modulus sixth moment

This file contains the elementary algebraic parts of the small-prime
sixth-moment argument used for Erdős problem 220.  The genuinely analytic
input is the constrained-fraction estimate; the lemmas below isolate the
finite Markov step, the local factor `716`, and the absorption of a fixed
power of a logarithm by one power of the interval length.
-/

open scoped BigOperators

/-- An even power of the norm of a real-valued complex number can be kept
as a complex sixth power until after character orthogonality is used. -/
lemma norm_pow_six_eq_re_pow_six_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    ‖z‖ ^ 6 = z.re ^ 6 := by
  have hz' : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz]
  calc
    ‖z‖ ^ 6 = ‖(z.re : ℂ)‖ ^ 6 :=
      congrArg (fun w : ℂ ↦ ‖w‖ ^ 6) hz'
    _ = z.re ^ 6 := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← abs_pow,
        abs_of_nonneg (by positivity : 0 ≤ z.re ^ 6)]

/-! ## The local divisor factor -/

/-- The local Euler factor left after the six denominator variables have
been summed.  A prime must occur in at least two of the six denominators. -/
noncomputable def sixthLocalFactor (p : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.Icc 2 6,
    (Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j

noncomputable def inverseEulerFactor (p : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹)⁻¹

/-- The contribution of one prime occurring in a specified subset of the
six denominator variables. -/
noncomputable def sixthSupportWeight (p : ℝ) (I : Finset (Fin 6)) : ℝ :=
  if 0 < I.card then p ^ (I.card - 1) / (p - 1) ^ I.card else 1

/-- Supports of size one are killed by character orthogonality. -/
def admissibleSixthSupports : Finset (Finset (Fin 6)) :=
  Finset.univ.powerset.filter fun I ↦ I.card ≠ 1

/-- Grouping admissible prime supports by cardinality gives exactly the
local factor used below. -/
lemma sum_sixthSupportWeight_eq (p : ℝ) :
    ∑ I ∈ admissibleSixthSupports, sixthSupportWeight p I =
      sixthLocalFactor p := by
  rw [admissibleSixthSupports, Finset.sum_filter]
  let f : ℕ → ℝ := fun j ↦
    if j ≠ 1 then (if 0 < j then p ^ (j - 1) / (p - 1) ^ j else 1) else 0
  have hgroup := Finset.sum_powerset_apply_card f
    (x := (Finset.univ : Finset (Fin 6)))
  change (∑ I ∈ (Finset.univ : Finset (Fin 6)).powerset, f I.card) =
    sixthLocalFactor p
  rw [hgroup]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [f, sixthLocalFactor, Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.choose]
  ring

/-- The elementary numerical identity behind the constant `716`. -/
lemma choose_six_weighted_sum :
    ∑ j ∈ Finset.Icc 2 6, Nat.choose 6 j * 2 ^ j = 716 := by
  norm_num [Finset.sum_Icc_succ_top, Nat.choose]

/-- For `p ≥ 2`, a local term with support size `j` is bounded by
`choose 6 j * 2^j / p`. -/
lemma local_six_term_mul_le {p : ℝ} (hp : 2 ≤ p) {j : ℕ}
    (hj₂ : 2 ≤ j) :
    p * ((Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j) ≤
      (Nat.choose 6 j : ℝ) * 2 ^ j := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith
  have hratio0 : 0 ≤ p / (p - 1) := div_nonneg hp0 hp1.le
  have hratio : p / (p - 1) ≤ 2 := by
    rw [div_le_iff₀ hp1]
    linarith
  have hpow : (p / (p - 1)) ^ j ≤ (2 : ℝ) ^ j :=
    pow_le_pow_left₀ hratio0 hratio _
  have hj₁ : 1 ≤ j := le_trans (by omega) hj₂
  have hident :
      p * (p ^ (j - 1) / (p - 1) ^ j) = (p / (p - 1)) ^ j := by
    rw [div_pow]
    field_simp
    rw [← pow_succ', Nat.sub_add_cancel hj₁]
  rw [mul_div_assoc, ← mul_assoc, mul_comm p (Nat.choose 6 j : ℝ),
    mul_assoc, hident]
  exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- The sum of the nontrivial local contributions is at most `716 / p`. -/
lemma sixthLocalFactor_sub_one_mul_le (p : ℝ) (hp : 2 ≤ p) :
    p * (sixthLocalFactor p - 1) ≤ 716 := by
  rw [sixthLocalFactor]
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  calc
    ∑ j ∈ Finset.Icc 2 6,
        p * ((Nat.choose 6 j : ℝ) * p ^ (j - 1) / (p - 1) ^ j)
        ≤ ∑ j ∈ Finset.Icc 2 6, (Nat.choose 6 j : ℝ) * 2 ^ j := by
          exact Finset.sum_le_sum fun j hj ↦
            local_six_term_mul_le hp (Finset.mem_Icc.mp hj).1
    _ = 716 := by
      exact_mod_cast choose_six_weighted_sum

/-- Convenient divided form of the local estimate. -/
lemma sixthLocalFactor_le (p : ℝ) (hp : 2 ≤ p) :
    sixthLocalFactor p ≤ 1 + 716 / p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have h := sixthLocalFactor_sub_one_mul_le p hp
  have h' : sixthLocalFactor p - 1 ≤ 716 / p := by
    rw [le_div_iff₀ hp0]
    simpa [mul_comm] using h
  linarith

/-- The linear local bound is absorbed by the `716`-th power of the inverse
Euler factor. -/
lemma one_add_716_div_le_inverseEuler_pow (p : ℝ) (hp : 2 ≤ p) :
    1 + 716 / p ≤ ((1 - p⁻¹)⁻¹) ^ 716 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith
  have hfrac : 1 / p ≤ 1 / (p - 1) := by
    exact one_div_le_one_div_of_le hp1 (by linarith)
  have hlinear : 1 + 716 / p ≤ 1 + (716 : ℝ) * (1 / (p - 1)) := by
    norm_num [div_eq_mul_inv] at hfrac ⊢
    nlinarith
  have hbernoulli :
      1 + (716 : ℝ) * (1 / (p - 1)) ≤
        (1 + 1 / (p - 1)) ^ (716 : ℕ) := by
    exact one_add_mul_le_pow
      (le_trans (by norm_num) (div_nonneg zero_le_one hp1.le)) 716
  calc
    1 + 716 / p ≤ 1 + (716 : ℝ) * (1 / (p - 1)) := hlinear
    _ ≤ (1 + 1 / (p - 1)) ^ (716 : ℕ) := hbernoulli
    _ = ((1 - p⁻¹)⁻¹) ^ 716 := by
      congr 1
      field_simp
      ring

lemma sixthLocalFactor_nonneg (p : ℝ) (hp : 2 ≤ p) :
    0 ≤ sixthLocalFactor p := by
  rw [sixthLocalFactor]
  apply add_nonneg zero_le_one
  exact Finset.sum_nonneg fun j _ ↦ div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
    (pow_nonneg (by linarith) _)

/-- Product form of the local estimate.  This is the exact Euler-product
factor that is passed to the weak Mertens bound. -/
lemma sixthLocalFactor_prod_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, sixthLocalFactor p ≤
      (∏ p ∈ P, inverseEulerFactor p) ^ 716 := by
  calc
    ∏ p ∈ P, sixthLocalFactor p ≤
        ∏ p ∈ P, (inverseEulerFactor p) ^ 716 := by
          refine Finset.prod_le_prod ?_ ?_
          · intro p hpP
            exact sixthLocalFactor_nonneg p (by exact_mod_cast hP p hpP)
          · intro p hpP
            have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hP p hpP
            exact (sixthLocalFactor_le p hpR).trans <| by
              simpa [inverseEulerFactor] using
                one_add_716_div_le_inverseEuler_pow (p : ℝ) hpR
    _ = (∏ p ∈ P, inverseEulerFactor p) ^ 716 := by
          rw [Finset.prod_pow]

/-- The complete local divisor product has the required fixed log-power
bound for a smooth squarefree modulus. -/
theorem exists_sixthLocalFactor_prod_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {s h : ℕ}, 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤
        (C * Real.log (2 * (h : ℝ))) ^ 716 := by
  obtain ⟨C, hC, hbound⟩ := partial_euler_product_le_log_two_mul
  refine ⟨C, hC, ?_⟩
  intro s h hh hsmooth
  calc
    ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤
        (∏ p ∈ s.primeFactors, inverseEulerFactor p) ^ 716 := by
          apply sixthLocalFactor_prod_le
          intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ (partial_euler_product h) ^ 716 := by
          apply pow_le_pow_left₀
          · exact Finset.prod_nonneg fun p hp ↦ by
              exact zero_le_one.trans <| by
                simpa [inverseEulerFactor] using one_le_inverse_prime_factor
                  (Nat.prime_of_mem_primeFactors hp)
          · simpa [inverseEulerFactor] using
              primeFactors_inverse_product_le_partial_euler_product hsmooth
    _ ≤ (C * Real.log (2 * (h : ℝ))) ^ 716 := by
          exact pow_le_pow_left₀
            ((by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound)
            (hbound h hh) 716

/-! ## Finite sixth-moment Markov inequality -/

/-- Counting Markov inequality at half the mean, in the denominator-free
form used in the small-prime argument. -/
lemma sixth_moment_lower_tail {X : Type*} (S : Finset X) (f : X → ℝ)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    ((S.filter fun x ↦ f x < μ / 2).card : ℝ) * μ ^ 6 ≤
      64 * ∑ x ∈ S, |f x - μ| ^ 6 := by
  classical
  have hpoint (x : X) (hx : x ∈ S) (hbad : f x < μ / 2) :
      μ ^ 6 ≤ 64 * |f x - μ| ^ 6 := by
    have hdist : μ / 2 ≤ |f x - μ| := by
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have hhalf : 0 ≤ μ / 2 := by positivity
    have hp := pow_le_pow_left₀ hhalf hdist 6
    nlinarith
  calc
    ((S.filter fun x ↦ f x < μ / 2).card : ℝ) * μ ^ 6 =
        ∑ x ∈ S.filter (fun x ↦ f x < μ / 2), μ ^ 6 := by simp
    _ ≤ ∑ x ∈ S.filter (fun x ↦ f x < μ / 2),
        64 * |f x - μ| ^ 6 := by
          exact Finset.sum_le_sum fun x hx ↦
            hpoint x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ S, 64 * |f x - μ| ^ 6 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro x hxS hx
          positivity
    _ = 64 * ∑ x ∈ S, |f x - μ| ^ 6 := by
          rw [Finset.mul_sum]

/-! ## Absorbing powers of `log` -/

/-- An explicit form of the one-variable bound
`log(2h)^L / h ≤ 2 L^L`.  This is exactly the estimate needed after
the sixth-moment Markov step. -/
lemma log_two_mul_pow_le (L h : ℕ) (hL : 0 < L) (hh : 0 < h) :
    Real.log (2 * (h : ℝ)) ^ L ≤
      2 * (L : ℝ) ^ L * h := by
  have hx0 : 0 ≤ (2 : ℝ) * h := by positivity
  have hx1 : 1 ≤ (2 : ℝ) * h := by
    norm_cast
    omega
  have hlog0 : 0 ≤ Real.log ((2 : ℝ) * h) := Real.log_nonneg hx1
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hLi : 0 < ((L : ℝ)⁻¹) := inv_pos.mpr (by positivity)
  have hbase := Real.log_le_rpow_div hx0 hLi
  have hbase' :
      Real.log ((2 : ℝ) * h) ≤
        (L : ℝ) * (((2 : ℝ) * h) ^ ((L : ℝ)⁻¹)) := by
    convert hbase using 1
    all_goals field_simp
  have hpow := pow_le_pow_left₀ hlog0 hbase' L
  calc
    Real.log (2 * (h : ℝ)) ^ L
        ≤ ((L : ℝ) * (((2 : ℝ) * h) ^ ((L : ℝ)⁻¹))) ^ L := hpow
    _ = (L : ℝ) ^ L * ((2 : ℝ) * h) := by
          rw [mul_pow]
          congr 1
          simpa using Real.rpow_inv_natCast_pow hx0 hL.ne'
    _ = 2 * (L : ℝ) ^ L * h := by ring

/-! ## Exact small-prime interface and its lower-tail consequence -/

/-- The unnormalised sixth centered moment of the number of units in an
interval. -/
noncomputable def centeredSixthMoment (s h : ℕ) : ℝ :=
  ∑ u ∈ Finset.range s,
    |(unitCount s h u : ℝ) - (h : ℝ) * density s| ^ 6

/-- The exact quantitative assertion proved by the smooth-modulus Fourier
argument.  It is named separately so the analytic input and its elementary
consequences have a stable interface. -/
def SmallPrimeSixthMomentBound (A : ℝ) : Prop :=
  0 < A ∧ ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
    (∀ p ∈ s.primeFactors, p ≤ h) →
    centeredSixthMoment s h ≤
      A * s * ((h : ℝ) * density s) ^ 3 *
        Real.log (2 * (h : ℝ)) ^ 1432

/-- Cancelling the positive cube of the mean after applying finite Markov. -/
lemma lower_tail_mul_mean_cube_le_of_sixthMoment
    {s h : ℕ} (hs : 0 < s) (hh : 0 < h) {A : ℝ}
    (hmoment : centeredSixthMoment s h ≤
      A * s * ((h : ℝ) * density s) ^ 3 *
        Real.log (2 * (h : ℝ)) ^ 1432) :
    (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) *
          ((h : ℝ) * density s) ^ 3 ≤
      64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432 := by
  let μ : ℝ := (h : ℝ) * density s
  have hμ : 0 < μ := mul_pos (Nat.cast_pos.mpr hh) (density_pos hs)
  have hmarkov := sixth_moment_lower_tail (Finset.range s)
    (fun u ↦ (unitCount s h u : ℝ)) hμ.le
  have htotal :
      ((((Finset.range s).filter fun u ↦
          (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 6) ≤
        64 * (A * s * μ ^ 3 * Real.log (2 * (h : ℝ)) ^ 1432) :=
    hmarkov.trans (mul_le_mul_of_nonneg_left hmoment (by norm_num))
  change ((((Finset.range s).filter fun u ↦
      (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 3) ≤
    64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432
  rw [← mul_le_mul_iff_right₀ (pow_pos hμ 3)]
  calc
    μ ^ 3 * ((((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 3) =
        (((Finset.range s).filter fun u ↦
          (unitCount s h u : ℝ) < μ / 2).card : ℝ) * μ ^ 6 := by ring
    _ ≤ 64 * (A * s * μ ^ 3 * Real.log (2 * (h : ℝ)) ^ 1432) := htotal
    _ = μ ^ 3 * (64 * A * s * Real.log (2 * (h : ℝ)) ^ 1432) := by ring

/-- The sixth centered-moment assertion implies an `s / h²` bound for
the residues at which the smooth count falls below half its mean. -/
theorem smallPrime_lowerTail_of_sixthMomentBound {A : ℝ}
    (hA : SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) * h ^ 2 ≤
          B * s := by
  obtain ⟨C, hC, hMertens⟩ := exists_smooth_le_log_mul_totient
  have hApos : 0 < A := hA.1
  let B : ℝ := 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro s h hs hsquare hh hsmooth
  let bad : ℝ := (((Finset.range s).filter fun u ↦
    (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ)
  let L : ℝ := Real.log (2 * (h : ℝ))
  have hbad : 0 ≤ bad := by dsimp [bad]; positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by norm_cast; omega)
  have htail : bad * ((h : ℝ) * density s) ^ 3 ≤
      64 * A * s * L ^ 1432 := by
    dsimp [bad, L]
    exact lower_tail_mul_mean_cube_le_of_sixthMoment hs (by omega)
      (hA.2 hs hsquare hh hsmooth)
  have hM := hMertens hs hh hsmooth
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hscale₁ : 1 ≤ C * L * density s := by
    rw [density]
    rw [show C * L * ((s.totient : ℝ) / s) =
      (C * L * (s.totient : ℝ)) / s by ring]
    rw [le_div_iff₀ hsR]
    dsimp [L]
    simpa [mul_assoc] using hM
  have hscale : 1 ≤ C ^ 3 * L ^ 3 * density s ^ 3 := by
    have := pow_le_pow_left₀ zero_le_one hscale₁ 3
    nlinarith
  have hlog := log_two_mul_pow_le 1435 h (by norm_num) (by omega)
  have hpre : bad * (h : ℝ) ^ 3 ≤ B * s * h := by
    calc
      bad * (h : ℝ) ^ 3 ≤
          (bad * (h : ℝ) ^ 3) *
            (C ^ 3 * L ^ 3 * density s ^ 3) := by
              exact le_mul_of_one_le_right (mul_nonneg hbad (by positivity)) hscale
      _ = C ^ 3 * L ^ 3 *
          (bad * ((h : ℝ) * density s) ^ 3) := by ring
      _ ≤ C ^ 3 * L ^ 3 * (64 * A * s * L ^ 1432) := by
          exact mul_le_mul_of_nonneg_left htail
            (mul_nonneg (pow_nonneg hC.le 3) (pow_nonneg hL 3))
      _ = 64 * A * C ^ 3 * s * L ^ 1435 := by ring
      _ ≤ 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435 * s * h := by
          have hnonneg : 0 ≤ 64 * A * C ^ 3 * s := by
            positivity
          calc
            64 * A * C ^ 3 * s * L ^ 1435 ≤
                (64 * A * C ^ 3 * s) *
                  (2 * (1435 : ℝ) ^ 1435 * h) :=
              mul_le_mul_of_nonneg_left hlog hnonneg
            _ = 128 * A * C ^ 3 * (1435 : ℝ) ^ 1435 * s * h := by
              rw [show (128 : ℝ) = 64 * 2 by norm_num]
              ac_rfl
      _ = B * s * h := by rfl
  rw [← mul_le_mul_iff_right₀ (Nat.cast_pos.mpr (by omega : 0 < h))]
  change (h : ℝ) * (bad * (h : ℝ) ^ 2) ≤ (h : ℝ) * (B * s)
  calc
    (h : ℝ) * (bad * (h : ℝ) ^ 2) = bad * (h : ℝ) ^ 3 := by ring
    _ ≤ B * s * h := hpre
    _ = (h : ℝ) * (B * s) := by ring

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/SupportFactor.lean` -/

section
/-!
# Factoring the six-support sum

In the sixth-moment expansion used for Erdős problem 220, each prime chooses
the subset of the six denominator variables in which it occurs.  Orthogonality
kills a choice in which a prime occurs exactly once.  This file proves, purely
by finite combinatorics, that the remaining weighted sum factors into the
expected product of local factors.
-/

open scoped BigOperators

/-! ## One-prime positivity -/

lemma sixthSupportWeight_nonneg {p : ℝ} (hp : 1 ≤ p) (I : Finset (Fin 6)) :
    0 ≤ sixthSupportWeight p I := by
  rw [sixthSupportWeight]
  split_ifs
  · exact div_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg (sub_nonneg.mpr hp) _)
  · exact zero_le_one

/-! ## Six tuples of subsets -/

/-- A six-tuple of subsets of `P`, represented prime-by-prime: `T p` is the
set of indices `i : Fin 6` for which `p` belongs to the `i`-th subset.  This
representation makes the Euler-product factorization literal. -/
abbrev SixSubsetTuple (P : Finset ℕ) := (p : P) → Finset (Fin 6)

/-- The multiplicity with which `p` occurs among the six subsets. -/
def sixMultiplicity {P : Finset ℕ} (T : SixSubsetTuple P) (p : P) : ℕ :=
  (T p).card

/-- Every prime used by the tuple occurs at least twice (equivalently, no
prime has multiplicity exactly one). -/
def IsAdmissibleSixTuple {P : Finset ℕ} (T : SixSubsetTuple P) : Prop :=
  ∀ p : P, sixMultiplicity T p ≠ 1

instance instDecidableIsAdmissibleSixTuple {P : Finset ℕ}
    (T : SixSubsetTuple P) : Decidable (IsAdmissibleSixTuple T) := by
  unfold IsAdmissibleSixTuple
  infer_instance

/-- The `i`-th one of the six subsets is nonempty. -/
def SixthSubsetNonempty {P : Finset ℕ} (T : SixSubsetTuple P) (i : Fin 6) : Prop :=
  ∃ p : P, i ∈ T p

/-- All six individual subsets are nonempty. -/
def AllSixSubsetsNonempty {P : Finset ℕ} (T : SixSubsetTuple P) : Prop :=
  ∀ i : Fin 6, SixthSubsetNonempty T i

instance instDecidableAllSixSubsetsNonempty {P : Finset ℕ}
    (T : SixSubsetTuple P) : Decidable (AllSixSubsetsNonempty T) := by
  unfold AllSixSubsetsNonempty SixthSubsetNonempty
  infer_instance

/-- Product of the prime-support weights attached to a six-tuple. -/
noncomputable def sixSubsetWeight (P : Finset ℕ) (T : SixSubsetTuple P) : ℝ :=
  ∏ p : P, sixthSupportWeight (p : ℝ) (T p)

/-- A version of `sixSubsetWeight` which is zero unless every prime support
survives orthogonality. -/
noncomputable def survivingSixSubsetWeight
    (P : Finset ℕ) (T : SixSubsetTuple P) : ℝ :=
  ∏ p : P, if (T p).card ≠ 1 then
    sixthSupportWeight (p : ℝ) (T p) else 0

lemma sixSubsetWeight_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (T : SixSubsetTuple P) :
    0 ≤ sixSubsetWeight P T := by
  apply Finset.prod_nonneg
  intro p _
  exact sixthSupportWeight_nonneg
    (by exact_mod_cast (hP p p.property).trans' (by omega)) (T p)

/-- Pointwise, the zero-extended weight is the ordinary product weight on an
admissible tuple and zero on a nonadmissible tuple. -/
lemma survivingSixSubsetWeight_eq_ite (P : Finset ℕ) (T : SixSubsetTuple P) :
    survivingSixSubsetWeight P T =
      if IsAdmissibleSixTuple T then sixSubsetWeight P T else 0 := by
  classical
  by_cases hT : IsAdmissibleSixTuple T
  · rw [if_pos hT]
    simp only [survivingSixSubsetWeight, sixSubsetWeight]
    apply Finset.prod_congr rfl
    intro p _
    rw [if_pos (by simpa [sixMultiplicity] using hT p)]
  · rw [if_neg hT]
    rw [survivingSixSubsetWeight]
    have hex : ∃ p : P, ¬ sixMultiplicity T p ≠ 1 := by
      simpa only [IsAdmissibleSixTuple, not_forall] using hT
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    rw [if_neg (by simpa [sixMultiplicity] using hp)]

/-- The unrestricted sum of zero-extended survivor weights factors exactly
as an Euler product. -/
theorem sum_survivingSixSubsetWeight_eq_prod (P : Finset ℕ) :
    ∑ T : SixSubsetTuple P, survivingSixSubsetWeight P T =
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  unfold survivingSixSubsetWeight
  calc
    (∑ T : SixSubsetTuple P,
        ∏ p : P, if (T p).card ≠ 1 then
          sixthSupportWeight (p : ℝ) (T p) else 0) =
        ∏ p : P, ∑ I : Finset (Fin 6), if I.card ≠ 1 then
          sixthSupportWeight (p : ℝ) I else 0 := by
      exact (Fintype.prod_sum (fun (p : P) (I : Finset (Fin 6)) ↦
        if I.card ≠ 1 then sixthSupportWeight (p : ℝ) I else 0)).symm
    _ = ∏ p : P, sixthLocalFactor (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simpa [admissibleSixthSupports] using
          sum_sixthSupportWeight_eq (p : ℝ)
    _ = ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
      simpa using (Finset.prod_coe_sort P (fun p : ℕ ↦ sixthLocalFactor (p : ℝ)))

/-- Exact factorization of the sum over the surviving tuples. -/
theorem sum_admissible_sixSubsetWeight_eq_prod (P : Finset ℕ) :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter IsAdmissibleSixTuple,
        sixSubsetWeight P T =
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  rw [← sum_survivingSixSubsetWeight_eq_prod P]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [survivingSixSubsetWeight_eq_ite]

/-- Any extra restriction on the six individual subsets can only decrease
the survivor sum.  This is the upper-bound form normally used after imposing
nonemptiness of denominator supports. -/
theorem sum_six_subset_weights_le_sixthLocalFactor_prod
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (required : SixSubsetTuple P → Prop) [DecidablePred required] :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ required T),
        sixSubsetWeight P T ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  rw [← sum_admissible_sixSubsetWeight_eq_prod P]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact hT.1
  · intro T hT _
    exact sixSubsetWeight_nonneg P hP T

/-- In particular, requiring every one of the six subsets to be nonempty
still leaves an upper bound by the same local Euler product. -/
theorem sum_nonempty_six_subset_weights_le_sixthLocalFactor_prod
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T),
        sixSubsetWeight P T ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  exact sum_six_subset_weights_le_sixthLocalFactor_prod P hP
    AllSixSubsetsNonempty

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/MomentEnergy.lean` -/

section
/-!
# Six interval-energy estimates

This file is deliberately below the moment expansion in the import graph.  It
packages the six applications of product Parseval which are used after the
finite fundamental lemma.  In particular, it does not mention the Ramanujan
coefficients or the compatible-frequency sum.
-/

open scoped BigOperators

noncomputable section

/-- The interval energy of the primitive product characters on a support. -/
def primitiveIntervalEnergy (T : Finset ℕ) (h : ℕ) : ℝ :=
  ∑ a : PrimitiveFrequencyTuple T,
    ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t‖ ^ 2

/-- Product Parseval bounds the primitive interval energy by `|T-product| h`.
The support must be nonempty: for the empty support the sole character is the
constant character and the claimed estimate is false when `h > 1`. -/
theorem primitiveIntervalEnergy_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty) (h : ℕ) :
    primitiveIntervalEnergy T h ≤ (primeProduct T : ℝ) * h := by
  simpa [primitiveIntervalEnergy] using
    primitiveTuple_intervalEnergy_le T hT hT0 h 0

/-- Apply product Parseval independently to all six supports. -/
theorem six_primitiveIntervalEnergy_sqrt_prod_le
    (U : Fin 6 → Finset ℕ) (h : ℕ)
    (hprime : ∀ i p, p ∈ U i → p.Prime)
    (hne : ∀ i, (U i).Nonempty) :
    (∏ i : Fin 6, Real.sqrt (primitiveIntervalEnergy (U i) h)) ≤
      ∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h) := by
  apply Finset.prod_le_prod
  · intro i hi
    exact Real.sqrt_nonneg _
  · intro i hi
    exact Real.sqrt_le_sqrt
      (primitiveIntervalEnergy_le (U i) (hprime i) (hne i) h)

/-- Substitute the six individual Parseval estimates into any contraction
estimate supplied by the finite fundamental lemma. -/
theorem six_primitiveIntervalEnergy_contraction_le
    (U : Fin 6 → Finset ℕ) (h : ℕ) (C : ℂ) (scale : ℝ)
    (hprime : ∀ i p, p ∈ U i → p.Prime)
    (hne : ∀ i, (U i).Nonempty)
    (hscale : 0 ≤ scale)
    (hfundamental :
      ‖C‖ ≤ scale *
        ∏ i : Fin 6, Real.sqrt (primitiveIntervalEnergy (U i) h)) :
    ‖C‖ ≤ scale *
      ∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h) := by
  exact hfundamental.trans
    (mul_le_mul_of_nonneg_left
      (six_primitiveIntervalEnergy_sqrt_prod_le U h hprime hne) hscale)

/-! ## Normalizing the six Parseval factors -/

/-- Transpose a product over six subsets into a product over their ambient
prime set.  This copy is kept in the lower, cycle-free layer so that the
moment expansion can use it as well. -/
lemma prod_six_supports_eq_prod_filter_card
    {M : Type*} [CommMonoid M] (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (hsub : ∀ i, U i ⊆ P) (f : ℕ → M) :
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
      ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter
          (fun i ↦ p ∈ U i)).card := by
  classical
  calc
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
        ∏ i : Fin 6, ∏ p ∈ P, if p ∈ U i then f p else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      have heq : P.filter (fun p ↦ p ∈ U i) = U i := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · exact fun hp ↦ hp.2
        · exact fun hp ↦ ⟨hsub i hp, hp⟩
      rw [← Finset.prod_filter, heq]
    _ = ∏ p ∈ P, ∏ i : Fin 6, if p ∈ U i then f p else 1 := by
      rw [Finset.prod_comm]
    _ = ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter
          (fun i ↦ p ∈ U i)).card := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← Finset.prod_filter]
      simp

/-- The six copies of the interval length appearing under square roots
multiply to the cube of the interval length. -/
lemma prod_six_sqrt_natCast (h : ℕ) :
    (∏ _i : Fin 6, Real.sqrt (h : ℝ)) = (h : ℝ) ^ 3 := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  calc
    Real.sqrt (h : ℝ) ^ 6 = (Real.sqrt (h : ℝ) ^ 2) ^ 3 := by ring
    _ = (h : ℝ) ^ 3 := by rw [Real.sq_sqrt hh]

/-- Split all six square-root Parseval factors into the common interval
length and the prime factors of the individual supports. -/
lemma prod_six_sqrt_primeProduct_mul (U : Fin 6 → Finset ℕ) (h : ℕ) :
    (∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h)) =
      (h : ℝ) ^ 3 *
        ∏ i : Fin 6, ∏ p ∈ U i, Real.sqrt (p : ℝ) := by
  have hsplit : ∀ i : Fin 6,
      Real.sqrt ((primeProduct (U i) : ℝ) * h) =
        (∏ p ∈ U i, Real.sqrt (p : ℝ)) * Real.sqrt (h : ℝ) := by
    intro i
    rw [Real.sqrt_mul (by positivity)]
    have hcast : (primeProduct (U i) : ℝ) = ∏ p ∈ U i, (p : ℝ) := by
      unfold primeProduct
      rw [Nat.cast_prod]
      exact Finset.prod_coe_sort (U i) (fun p : ℕ ↦ (p : ℝ))
    rw [hcast, Real.sqrt_prod (U i) (fun p _ ↦ Nat.cast_nonneg p)]
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib, prod_six_sqrt_natCast]
  ring

/-- Local cancellation of the fundamental-lemma scale and the Parseval
square roots. -/
lemma sqrt_support_scale_mul_energy
    (p : ℕ) (I : Finset (Fin 6)) (hI : 2 ≤ I.card) :
    Real.sqrt (p : ℝ) ^ (I.card - 2) *
        Real.sqrt (p : ℝ) ^ I.card =
      (p : ℝ) ^ (I.card - 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hI
  rw [hk]
  rw [Nat.add_sub_cancel_left, ← pow_add]
  have hexp : k + (2 + k) = 2 * (k + 1) := by omega
  rw [hexp, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
  congr 1
  omega

/-- One prime's coefficient, fundamental scale, and Parseval square roots
are exactly its sixth-support weight. -/
lemma local_six_support_normalization
    (p : ℕ) (I : Finset (Fin 6)) (hp : 2 ≤ p) (hI : 2 ≤ I.card) :
    (((p - 1 : ℕ) : ℝ)⁻¹) ^ I.card *
        (Real.sqrt (p : ℝ) ^ (I.card - 2) *
          Real.sqrt (p : ℝ) ^ I.card) =
      sixthSupportWeight (p : ℝ) I := by
  rw [sqrt_support_scale_mul_energy p I hI]
  rw [sixthSupportWeight, if_pos (by omega : 0 < I.card)]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  simp only [Nat.cast_one]
  rw [inv_pow]
  simp only [div_eq_mul_inv]
  ring

/-- Exact normalization used after the six Parseval inequalities.  The first
product is the norm of the six Ramanujan coefficients, the second is the
prime-local scale from the fundamental lemma, and the third is the product
of the six Parseval bounds.  Their product is precisely `h^3` times the
product of local support weights. -/
theorem six_support_energy_normalization
    (P : Finset ℕ) (U : Fin 6 → Finset ℕ) (h : ℕ)
    (hsub : ∀ i, U i ⊆ P)
    (hP : ∀ p ∈ P, 2 ≤ p)
    (hmult : ∀ p ∈ P,
      2 ≤ ((Finset.univ : Finset (Fin 6)).filter
        (fun i ↦ p ∈ U i)).card) :
    (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
        ((∏ p ∈ P,
            Real.sqrt (p : ℝ) ^
              (((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card - 2)) *
          (∏ i : Fin 6,
            Real.sqrt ((primeProduct (U i) : ℝ) * h))) =
      (h : ℝ) ^ 3 *
        ∏ p ∈ P,
          sixthSupportWeight (p : ℝ)
            ((Finset.univ : Finset (Fin 6)).filter
              (fun i ↦ p ∈ U i)) := by
  rw [prod_six_sqrt_primeProduct_mul]
  rw [prod_six_supports_eq_prod_filter_card P U hsub
    (fun p ↦ ((p - 1 : ℕ) : ℝ)⁻¹)]
  rw [prod_six_supports_eq_prod_filter_card P U hsub
    (fun p ↦ Real.sqrt (p : ℝ))]
  calc
    (∏ p ∈ P,
        ((p - 1 : ℕ) : ℝ)⁻¹ ^
          ((Finset.univ : Finset (Fin 6)).filter
            (fun i ↦ p ∈ U i)).card) *
        ((∏ p ∈ P,
            Real.sqrt (p : ℝ) ^
              (((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card - 2)) *
          ((h : ℝ) ^ 3 *
            ∏ p ∈ P,
              Real.sqrt (p : ℝ) ^
                ((Finset.univ : Finset (Fin 6)).filter
                  (fun i ↦ p ∈ U i)).card)) =
        (h : ℝ) ^ 3 *
          ∏ p ∈ P,
            (((p - 1 : ℕ) : ℝ)⁻¹ ^
              ((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card) *
              (Real.sqrt (p : ℝ) ^
                  (((Finset.univ : Finset (Fin 6)).filter
                    (fun i ↦ p ∈ U i)).card - 2) *
                Real.sqrt (p : ℝ) ^
                  ((Finset.univ : Finset (Fin 6)).filter
                    (fun i ↦ p ∈ U i)).card) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = (h : ℝ) ^ 3 *
        ∏ p ∈ P,
          sixthSupportWeight (p : ℝ)
            ((Finset.univ : Finset (Fin 6)).filter
              (fun i ↦ p ∈ U i)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      exact local_six_support_normalization p
        ((Finset.univ : Finset (Fin 6)).filter (fun i ↦ p ∈ U i))
        (hP p hp) (hmult p hp)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/SupportAssembly.lean` -/

section
/-!
# Summing estimates indexed by six nonempty prime subsets

This file is the finite bookkeeping bridge between a termwise sixth-moment
estimate and `SupportFactor`.  It deliberately knows nothing about the
Fourier definition of a term: an injective transposition into prime-by-prime
support tuples, a termwise estimate on admissible supports, and vanishing on
nonadmissible supports are enough.
-/

open scoped BigOperators

/-- Six labelled, nonempty subsets of an ambient finite set `P`. -/
def nonemptySixSubsetFamilies (P : Finset ℕ) :
    Finset (Fin 6 → Finset ℕ) :=
  Fintype.piFinset fun _ : Fin 6 ↦ P.powerset.erase ∅

lemma mem_nonemptySixSubsetFamilies {P : Finset ℕ}
    {U : Fin 6 → Finset ℕ} :
    U ∈ nonemptySixSubsetFamilies P ↔
      (∀ i, U i ⊆ P) ∧ (∀ i, (U i).Nonempty) := by
  classical
  rw [nonemptySixSubsetFamilies, Fintype.mem_piFinset]
  constructor
  · intro hU
    constructor
    · intro i
      exact Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hU i))
    · intro i
      exact Finset.nonempty_iff_ne_empty.mpr
        (Finset.ne_of_mem_erase (hU i))
  · rintro ⟨hsub, hne⟩ i
    exact Finset.mem_erase.mpr
      ⟨Finset.nonempty_iff_ne_empty.mp (hne i),
        Finset.mem_powerset.mpr (hsub i)⟩

/-- An injective encoding of a finite family of admissible, nonempty support
tuples has total weight bounded by the complete local Euler product. -/
theorem sum_encoded_admissible_weights_le_localFactorProduct
    {A : Type*} [DecidableEq A] (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (S : Finset A)
    (encode : A → SixSubsetTuple P)
    (hinj : Set.InjOn encode S)
    (hnonempty : ∀ a ∈ S, AllSixSubsetsNonempty (encode a)) :
    ∑ a ∈ S.filter (fun a ↦ IsAdmissibleSixTuple (encode a)),
        sixSubsetWeight P (encode a) ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  let G := S.filter fun a ↦ IsAdmissibleSixTuple (encode a)
  have hinjG : Set.InjOn encode G :=
    hinj.mono (Finset.filter_subset _ _)
  have himage : G.image encode ⊆
      (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T) := by
    intro T hT
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha'.2, hnonempty a ha'.1⟩
  calc
    ∑ a ∈ S.filter (fun a ↦ IsAdmissibleSixTuple (encode a)),
        sixSubsetWeight P (encode a) =
        ∑ T ∈ G.image encode, sixSubsetWeight P T := by
          dsimp [G]
          symm
          exact Finset.sum_image hinjG
    _ ≤ ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
          (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T),
          sixSubsetWeight P T := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro T hT _
        exact sixSubsetWeight_nonneg P hP T
    _ ≤ ∏ p ∈ P, sixthLocalFactor (p : ℝ) :=
      sum_nonempty_six_subset_weights_le_sixthLocalFactor_prod P hP

/-- Finite support assembly in the form used by the sixth-moment proof.

`term U` is allowed to have either sign.  On an admissible support it is
bounded by `scale` times the transposed support weight; on a support having a
prime of multiplicity one it vanishes exactly.  Hence its total over the six
nonempty families is at most `scale` times the local Euler product. -/
theorem sum_six_family_contributions_le_localFactorProduct
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (encode : (Fin 6 → Finset ℕ) → SixSubsetTuple P)
    (hinj : Set.InjOn encode (nonemptySixSubsetFamilies P))
    (hnonempty : ∀ U ∈ nonemptySixSubsetFamilies P,
      AllSixSubsetsNonempty (encode U))
    (scale : ℝ) (hscale : 0 ≤ scale)
    (term : (Fin 6 → Finset ℕ) → ℝ)
    (hterm : ∀ U ∈ nonemptySixSubsetFamilies P,
      IsAdmissibleSixTuple (encode U) →
        term U ≤ scale * sixSubsetWeight P (encode U))
    (hzero : ∀ U ∈ nonemptySixSubsetFamilies P,
      ¬ IsAdmissibleSixTuple (encode U) → term U = 0) :
    ∑ U ∈ nonemptySixSubsetFamilies P, term U ≤
      scale * ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  let S := nonemptySixSubsetFamilies P
  let G := S.filter fun U ↦ IsAdmissibleSixTuple (encode U)
  have hsum_filter :
      (∑ U ∈ S, term U) = ∑ U ∈ G, term U := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U hU
    by_cases hgood : IsAdmissibleSixTuple (encode U)
    · simp [hgood]
    · simp [hgood, hzero U hU hgood]
  rw [hsum_filter]
  calc
    ∑ U ∈ G, term U ≤
        ∑ U ∈ G, scale * sixSubsetWeight P (encode U) := by
      apply Finset.sum_le_sum
      intro U hU
      have hUG := Finset.mem_filter.mp hU
      exact hterm U hUG.1 hUG.2
    _ = scale * ∑ U ∈ G, sixSubsetWeight P (encode U) := by
      rw [Finset.mul_sum]
    _ ≤ scale * ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      dsimp [G, S]
      exact sum_encoded_admissible_weights_le_localFactorProduct
        P hP (nonemptySixSubsetFamilies P) encode hinj hnonempty

/-- The requested normalization, with the scale written as `s * h^3`. -/
theorem sum_six_family_contributions_le_localFactorProduct_natScale
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (encode : (Fin 6 → Finset ℕ) → SixSubsetTuple P)
    (hinj : Set.InjOn encode (nonemptySixSubsetFamilies P))
    (hnonempty : ∀ U ∈ nonemptySixSubsetFamilies P,
      AllSixSubsetsNonempty (encode U))
    (s h : ℕ) (term : (Fin 6 → Finset ℕ) → ℝ)
    (hterm : ∀ U ∈ nonemptySixSubsetFamilies P,
      IsAdmissibleSixTuple (encode U) →
        term U ≤ (s : ℝ) * (h : ℝ) ^ 3 *
          sixSubsetWeight P (encode U))
    (hzero : ∀ U ∈ nonemptySixSubsetFamilies P,
      ¬ IsAdmissibleSixTuple (encode U) → term U = 0) :
    ∑ U ∈ nonemptySixSubsetFamilies P, term U ≤
      (s : ℝ) * (h : ℝ) ^ 3 *
        ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  exact sum_six_family_contributions_le_localFactorProduct
    P hP encode hinj hnonempty ((s : ℝ) * (h : ℝ) ^ 3)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      term hterm hzero

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/MomentExpansion.lean` -/

section
/-!
# The smooth sixth-moment expansion for Erdős 220

This file assembles the exact Ramanujan expansion of the centered interval
count with the finite Cauchy--CRT estimate and the prime-support Euler
product.  The elementary consequences of the resulting moment estimate are
kept in `SmallMoment`.
-/

open scoped BigOperators

noncomputable section

/-! ## The exact nonconstant amplitude -/

/-- The nonconstant part of the squarefree Ramanujan expansion, after
summing over the translated interval. -/
def centeredRamanujanAmplitude (s h u : ℕ) : ℂ :=
  ∑ T ∈ nonconstantRamanujanSubsets s,
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t)

/-- Pointwise, the centered unit count is the density times the nonconstant
Ramanujan amplitude. -/
theorem unitCount_centered_eq_density_mul_amplitude
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    (unitCount s h u : ℂ) - (h : ℂ) * (density s : ℂ) =
      (density s : ℂ) * centeredRamanujanAmplitude s h u := by
  have hexpansion :=
    unitCount_centered_eq_ramanujanSubsetSum s h u hsquare
  rw [fourierDensity_eq_density s hs] at hexpansion
  exact hexpansion

/-- The nonconstant amplitude is real.  This is important: the sixth moment
must be expanded as an exact complex sixth power before any triangle
inequality is used, so that summing over the translate retains character
orthogonality. -/
theorem centeredRamanujanAmplitude_im
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    (centeredRamanujanAmplitude s h u).im = 0 := by
  have hcenter :=
    unitCount_centered_eq_density_mul_amplitude s h u hs hsquare
  have him := congrArg Complex.im hcenter
  have hmul : density s * (centeredRamanujanAmplitude s h u).im = 0 := by
    simpa using him
  exact (mul_eq_zero.mp hmul).resolve_left (density_pos hs).ne'

/-- Consequently the sixth norm power of the amplitude is the real part of
its exact complex sixth power. -/
theorem norm_centeredRamanujanAmplitude_pow_six_eq_re
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
      (centeredRamanujanAmplitude s h u ^ 6).re := by
  have him := centeredRamanujanAmplitude_im s h u hs hsquare
  have hz : centeredRamanujanAmplitude s h u =
      ((centeredRamanujanAmplitude s h u).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  rw [hz, Complex.norm_real, Real.norm_eq_abs]
  norm_cast
  norm_num [Even.pow_abs]

/-- Taking norms in the exact expansion gives the corresponding identity
for each sixth-power summand of the real centered moment. -/
theorem abs_unitCount_centered_pow_six
    (s h u : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    |(unitCount s h u : ℝ) - (h : ℝ) * density s| ^ 6 =
      density s ^ 6 * ‖centeredRamanujanAmplitude s h u‖ ^ 6 := by
  have hcenter :=
    unitCount_centered_eq_density_mul_amplitude s h u hs hsquare
  have hre : (unitCount s h u : ℝ) - (h : ℝ) * density s =
      density s * (centeredRamanujanAmplitude s h u).re := by
    simpa using congrArg Complex.re hcenter
  rw [hre, abs_mul, abs_of_nonneg (density_nonneg s), mul_pow,
    Even.pow_abs]
  rw [norm_pow_six_eq_re_pow_six_of_im_eq_zero
    (centeredRamanujanAmplitude_im s h u hs hsquare)]
  norm_num

/-- Exact reduction of the smooth sixth moment to the sixth norm moment of
the nonconstant Ramanujan amplitude. -/
theorem centeredSixthMoment_eq_density_pow_six_mul
    (s h : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    centeredSixthMoment s h =
      density s ^ 6 *
        ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 := by
  rw [centeredSixthMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact abs_unitCount_centered_pow_six s h u hs hsquare

/-! ## Sixth powers as six labelled copies -/

/-! ## Transposing six divisor supports prime by prime -/

/-- Transpose a six-tuple of prime subsets into the prime-by-prime support
representation used by `SupportFactor`. -/
def familySupportTuple (P : Finset ℕ) (U : Fin 6 → Finset ℕ) :
    SixSubsetTuple P :=
  fun p ↦ Finset.univ.filter fun i ↦ p.1 ∈ U i

@[simp] lemma mem_familySupportTuple (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (p : P) (i : Fin 6) :
    i ∈ familySupportTuple P U p ↔ p.1 ∈ U i := by
  simp [familySupportTuple]

/-- Transposition is injective when all six subsets are contained in the
ambient prime set. -/
lemma familySupportTuple_injective_on (P : Finset ℕ)
    {U V : Fin 6 → Finset ℕ}
    (hU : ∀ i, U i ⊆ P) (hV : ∀ i, V i ⊆ P)
    (h : familySupportTuple P U = familySupportTuple P V) : U = V := by
  funext i
  ext p
  constructor
  · intro hp
    let pp : P := ⟨p, hU i hp⟩
    have hmem : i ∈ familySupportTuple P U pp :=
      (mem_familySupportTuple P U pp i).2 hp
    rw [h] at hmem
    exact (mem_familySupportTuple P V pp i).1 hmem
  · intro hp
    let pp : P := ⟨p, hV i hp⟩
    have hmem : i ∈ familySupportTuple P V pp :=
      (mem_familySupportTuple P V pp i).2 hp
    rw [← h] at hmem
    exact (mem_familySupportTuple P U pp i).1 hmem

/-- If each of the six subsets is nonempty, the transposed support tuple has
the corresponding `AllSixSubsetsNonempty` property. -/
lemma familySupportTuple_all_nonempty (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (hsub : ∀ i, U i ⊆ P)
    (hne : ∀ i, (U i).Nonempty) :
    AllSixSubsetsNonempty (familySupportTuple P U) := by
  intro i
  obtain ⟨p, hp⟩ := hne i
  exact ⟨⟨p, hsub i hp⟩, by simpa using hp⟩

/-- A prime occurring in exactly one of the six supports cannot satisfy the
prime-local compatibility equation, because its unique frequency is a unit
modulo that prime. -/
lemma not_sixPrimeCompatible_of_support_card_one
    {s : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors) (p : s.primeFactors)
    (hpone : (familySupportTuple s.primeFactors U p).card = 1)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) :
    ¬ sixPrimeCompatible s a := by
  classical
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  letI : NeZero p.1 := ⟨hpprime.ne_zero⟩
  letI : Fact (1 < p.1) := ⟨hpprime.one_lt⟩
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hpone
  have hiJ : i ∈ familySupportTuple s.primeFactors U p := by simp [hi]
  have hpi : p.1 ∈ U i := (mem_familySupportTuple _ _ _ _).mp hiJ
  have hlocal : sixLocalFrequency a p.1 =
      ((a i ⟨p.1, hpi⟩).1 : ZMod p.1) := by
    unfold sixLocalFrequency sixLocalFrequencyNat
    rw [Finset.sum_eq_single i]
    · simp [hpi]
    · intro j hj hji
      have hjJ : j ∉ familySupportTuple s.primeFactors U p := by
        rw [hi]
        simpa using hji
      have hpj : p.1 ∉ U j := by
        simpa using hjJ
      simp [hpj]
    · simp
  have hcop : (a i ⟨p.1, hpi⟩).1.Coprime p.1 :=
    (Finset.mem_filter.mp (a i ⟨p.1, hpi⟩).2).2
  have hne : ((a i ⟨p.1, hpi⟩).1 : ZMod p.1) ≠ 0 := by
    letI : Fact (1 < p.1) := ⟨(Nat.prime_of_mem_primeFactors p.2).one_lt⟩
    intro hz
    have hu : ((ZMod.unitOfCoprime (a i ⟨p.1, hpi⟩).1 hcop :
        (ZMod p.1)ˣ) : ZMod p.1) ≠ 0 := Units.ne_zero _
    exact hu (by simpa using hz)
  intro hcompat
  exact hne (hlocal ▸ hcompat p.1 p.2)

/-- Exact sixth-power expansion into six labelled nonconstant divisor
supports.  No absolute values have been introduced at this stage. -/
lemma centeredRamanujanAmplitude_pow_six (s h u : ℕ) :
    centeredRamanujanAmplitude s h u ^ 6 =
      ∑ U ∈ Fintype.piFinset (fun _ : Fin 6 ↦
          nonconstantRamanujanSubsets s),
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm (U i) (u + t) := by
  simpa only [centeredRamanujanAmplitude] using
    (Finset.sum_pow' (nonconstantRamanujanSubsets s)
      (fun T ↦ ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t)) 6)

/-- Summing over the translate is performed *before* estimating any term.
This is the exact arrangement in which additive-character orthogonality
eliminates every prime support of multiplicity one. -/
theorem sum_norm_amplitude_pow_six_eq_re_support_sum
    (s h : ℕ) (hs : 0 < s) (hsquare : Squarefree s) :
    ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
      (∑ U ∈ Fintype.piFinset (fun _ : Fin 6 ↦
          nonconstantRamanujanSubsets s),
        ∑ u ∈ Finset.range s,
          ∏ i : Fin 6,
            ∑ t ∈ Finset.Icc 1 h,
              ramanujanSubsetTerm (U i) (u + t)).re := by
  calc
    ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 =
        ∑ u ∈ Finset.range s,
          (centeredRamanujanAmplitude s h u ^ 6).re := by
      apply Finset.sum_congr rfl
      intro u hu
      exact norm_centeredRamanujanAmplitude_pow_six_eq_re s h u hs hsquare
    _ = (∑ u ∈ Finset.range s,
          centeredRamanujanAmplitude s h u ^ 6).re := by simp
    _ = _ := by
      simp_rw [centeredRamanujanAmplitude_pow_six]
      rw [Finset.sum_comm]

/-! ## Coefficients of a fixed support family -/

/-- The scalar Ramanujan coefficient belonging to one prime subset. -/
def ramanujanSubsetCoefficient (T : Finset ℕ) : ℂ :=
  ∏ p ∈ T, (-(1 : ℂ) / (p - 1 : ℕ))

/-- Product of the six scalar coefficients. -/
def sixRamanujanCoefficient (U : Fin 6 → Finset ℕ) : ℂ :=
  ∏ i : Fin 6, ramanujanSubsetCoefficient (U i)

lemma sum_ramanujanSubsetTerm_eq_coefficient_mul (T : Finset ℕ)
    (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm T (u + t) =
      ramanujanSubsetCoefficient T *
        ∑ a : PrimitiveFrequencyTuple T,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) := by
  exact sum_ramanujanSubsetTerm_eq_frequencySum T h u

/-- The prime-product frequency is an additive character. -/
lemma primitiveTupleCharacter_add {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (m n : ℕ) :
    primitiveTupleCharacter a (m + n) =
      primitiveTupleCharacter a m * primitiveTupleCharacter a n := by
  classical
  unfold primitiveTupleCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  exact Nat.mul_add _ _ _

/-- Translation of an interval factors off the value of the character at
the translating residue. -/
lemma sum_primitiveTupleCharacter_add {T : Finset ℕ}
    (a : PrimitiveFrequencyTuple T) (h u : ℕ) :
    ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) =
      primitiveTupleCharacter a u *
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t := by
  simp_rw [primitiveTupleCharacter_add]
  rw [Finset.mul_sum]

/-- The compatible interval contraction for one fixed family of six prime
supports. -/
def fixedSupportCompatibleIntervalContraction (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℂ :=
  ∑ a : (∀ i, PrimitiveFrequencyTuple (U i)),
    if sixPrimeCompatible s a then
      ∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t
    else 0

/-- If one prime occurs in exactly one support, the compatible contraction
is empty by prime-local character orthogonality. -/
lemma fixedSupportCompatibleIntervalContraction_eq_zero_of_support_card_one
    {s h : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors) (p : s.primeFactors)
    (hpone : (familySupportTuple s.primeFactors U p).card = 1) :
    fixedSupportCompatibleIntervalContraction s h U = 0 := by
  classical
  unfold fixedSupportCompatibleIntervalContraction
  apply Finset.sum_eq_zero
  intro a ha
  rw [if_neg (not_sixPrimeCompatible_of_support_card_one hsub p hpone a)]

/-- Expand the product of the six fixed-support Ramanujan summands into a
single sum over six labelled primitive-frequency tuples. -/
lemma fixedSupportRamanujanProduct_eq_frequencySum
    (U : Fin 6 → Finset ℕ) (h u : ℕ) :
    (∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h, ramanujanSubsetTerm (U i) (u + t)) =
      sixRamanujanCoefficient U *
        ∑ a : (∀ i, PrimitiveFrequencyTuple (U i)),
          ∏ i : Fin 6,
            ∑ t ∈ Finset.Icc 1 h,
              primitiveTupleCharacter (a i) (u + t) := by
  simp_rw [sum_ramanujanSubsetTerm_eq_coefficient_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa using
    (Fintype.prod_sum (R := ℂ)
      (f := fun i : Fin 6 ↦ fun a : PrimitiveFrequencyTuple (U i) ↦
        ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)))

/-- For a fixed six-tuple of frequencies, complete-period orthogonality can
be applied after factoring all six interval translations. -/
lemma sum_six_translated_primitiveTupleCharacter
    {s : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (a : ∀ i, PrimitiveFrequencyTuple (U i)) (h : ℕ) :
    ∑ u ∈ Finset.range s,
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h,
            primitiveTupleCharacter (a i) (u + t) =
      (if sixPrimeCompatible s a then (s : ℂ) else 0) *
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t := by
  simp_rw [sum_primitiveTupleCharacter_add]
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul]
  rw [six_primitiveTupleCharacter_orthogonality hs hsquare hU a]

/-- Exact fixed-support evaluation after summing the translate over a full
period.  This is the bridge from Fourier orthogonality to the finite
compatible-frequency contraction. -/
theorem sum_fixedSupportRamanujanProduct_eq_compatibleContraction
    {s : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hU : ∀ i, U i ⊆ s.primeFactors)
    (h : ℕ) :
    ∑ u ∈ Finset.range s,
        ∏ i : Fin 6,
          ∑ t ∈ Finset.Icc 1 h,
            ramanujanSubsetTerm (U i) (u + t) =
      (s : ℂ) * sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U := by
  simp_rw [fixedSupportRamanujanProduct_eq_frequencySum]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_six_translated_primitiveTupleCharacter hs hsquare hU]
  unfold fixedSupportCompatibleIntervalContraction
  calc
    sixRamanujanCoefficient U *
          ∑ a, (if sixPrimeCompatible s a then (s : ℂ) else 0) *
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t =
        sixRamanujanCoefficient U * ((s : ℂ) *
          ∑ a, if sixPrimeCompatible s a then
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t else 0) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcompat : sixPrimeCompatible s a <;> simp [hcompat]
    _ = (s : ℂ) * sixRamanujanCoefficient U *
          ∑ a, if sixPrimeCompatible s a then
            ∏ i : Fin 6,
              ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter (a i) t else 0 := by
      ring

/-- The real contribution of one fixed six-tuple of nonconstant Ramanujan
supports to the complete-period sixth-power expansion. -/
def fixedSupportMomentContribution (s h : ℕ)
    (U : Fin 6 → Finset ℕ) : ℝ :=
  (∑ u ∈ Finset.range s,
      ∏ i : Fin 6,
        ∑ t ∈ Finset.Icc 1 h,
          ramanujanSubsetTerm (U i) (u + t)).re

/-- The real fixed-support contribution vanishes whenever a prime occurs in
exactly one of the six supports. -/
lemma fixedSupportMomentContribution_eq_zero_of_not_admissible
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ}
    (hU : U ∈ nonemptySixSubsetFamilies s.primeFactors)
    (hbad : ¬ IsAdmissibleSixTuple
      (familySupportTuple s.primeFactors U)) :
    fixedSupportMomentContribution s h U = 0 := by
  classical
  have hsub : ∀ i, U i ⊆ s.primeFactors :=
    (mem_nonemptySixSubsetFamilies.mp hU).1
  simp only [IsAdmissibleSixTuple, sixMultiplicity] at hbad
  push_neg at hbad
  obtain ⟨p, hpone⟩ := hbad
  have hzero :=
    fixedSupportCompatibleIntervalContraction_eq_zero_of_support_card_one
      (h := h) hsub p hpone
  rw [fixedSupportMomentContribution,
    sum_fixedSupportRamanujanProduct_eq_compatibleContraction hs hsquare hsub,
    hzero]
  simp

/-- The analytic input for an admissible support family only has to bound
the norm of its coefficient-weighted compatible contraction. -/
lemma fixedSupportMomentContribution_le_of_contraction_norm
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    {U : Fin 6 → Finset ℕ} (hsub : ∀ i, U i ⊆ s.primeFactors)
    (hnorm : ‖sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U‖ ≤
      (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U)) :
    fixedSupportMomentContribution s h U ≤
      (s : ℝ) * (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U) := by
  rw [fixedSupportMomentContribution,
    sum_fixedSupportRamanujanProduct_eq_compatibleContraction hs hsquare hsub]
  calc
    ((s : ℂ) * sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U).re ≤
        ‖(s : ℂ) * (sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U)‖ := by
      rw [mul_assoc]
      exact Complex.re_le_norm _
    _ = (s : ℝ) * ‖sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U‖ := by
      rw [norm_mul, Complex.norm_natCast]
    _ ≤ (s : ℝ) * ((h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U)) :=
      mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = (s : ℝ) * (h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U) := by ring

/-- Norm of the scalar coefficient, before transposing the two products. -/
lemma norm_sixRamanujanCoefficient (U : Fin 6 → Finset ℕ)
    (hprime : ∀ i p, p ∈ U i → p.Prime) :
    ‖sixRamanujanCoefficient U‖ =
      ∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹ := by
  rw [sixRamanujanCoefficient, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ramanujanSubsetCoefficient, norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (hprime i p hp).one_le
  rw [norm_div, norm_neg, norm_one, Complex.norm_natCast,
    Nat.cast_sub hp1, one_div]

/-- Primes absent from all six supports contribute the neutral local weight,
so the ambient-prime weight may be restricted to the union of the supports. -/
lemma sixSubsetWeight_family_eq_usedPrimes_prod
    (P : Finset ℕ) (U : Fin 6 → Finset ℕ)
    (hsub : ∀ i, U i ⊆ P) :
    sixSubsetWeight P (familySupportTuple P U) =
      ∏ p ∈ usedPrimes U,
        sixthSupportWeight (p : ℝ) (primeSupport U p) := by
  classical
  have hused : usedPrimes U ⊆ P := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
    exact hsub i hi
  unfold sixSubsetWeight
  calc
    (∏ p : P, sixthSupportWeight (p : ℝ)
        (familySupportTuple P U p)) =
        ∏ p ∈ P, sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      simpa [familySupportTuple, primeSupport] using
        (Finset.prod_attach P
          (fun p ↦ sixthSupportWeight (p : ℝ) (primeSupport U p)))
    _ = ∏ p ∈ usedPrimes U,
          sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      symm
      apply Finset.prod_subset hused
      intro p hpP hpnot
      have hnone : primeSupport U p = ∅ := by
        ext i
        simp only [mem_primeSupport]
        constructor
        · intro hpUi
          exact (hpnot (mem_usedPrimes.mpr ⟨i, hpUi⟩)).elim
        · intro hi
          simp at hi
      rw [hnone]
      simp [sixthSupportWeight]

/-- The compatible fundamental lemma, product Parseval, and the exact local
weight normalization give the coefficient-weighted estimate for one
admissible six-support family. -/
theorem norm_coefficient_mul_fixedSupportContraction_le
    {s h : ℕ} {U : Fin 6 → Finset ℕ}
    (hsub : ∀ i, U i ⊆ s.primeFactors)
    (hne : ∀ i, (U i).Nonempty)
    (hadmissible : IsAdmissibleSixTuple
      (familySupportTuple s.primeFactors U)) :
    ‖sixRamanujanCoefficient U *
        fixedSupportCompatibleIntervalContraction s h U‖ ≤
      (h : ℝ) ^ 3 *
        sixSubsetWeight s.primeFactors
          (familySupportTuple s.primeFactors U) := by
  classical
  have hused : usedPrimes U ⊆ s.primeFactors := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
    exact hsub i hi
  have hUused : ∀ i, U i ⊆ usedPrimes U := by
    intro i p hp
    exact mem_usedPrimes.mpr ⟨i, hp⟩
  have hPused : ∀ p ∈ usedPrimes U, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (hused hp)).two_le
  have hnoone : ∀ p ∈ usedPrimes U, (primeSupport U p).card ≠ 1 := by
    intro p hp
    have hpP : p ∈ s.primeFactors := hused hp
    have hadm := hadmissible ⟨p, hpP⟩
    simpa [sixMultiplicity, familySupportTuple, primeSupport] using hadm
  have hmult : ∀ p ∈ usedPrimes U, 2 ≤ (primeSupport U p).card := by
    intro p hp
    have hpos : 0 < (primeSupport U p).card := by
      obtain ⟨i, hi⟩ := mem_usedPrimes.mp hp
      exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩
    exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Nat.ne_of_gt hpos, hnoone p hp⟩)
  have hprime : ∀ i p, p ∈ U i → p.Prime := by
    intro i p hp
    exact Nat.prime_of_mem_primeFactors (hsub i hp)
  let scale : ℝ := ∏ p ∈ usedPrimes U,
    Real.sqrt p ^ ((primeSupport U p).card - 2)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    apply Finset.prod_nonneg
    intro p hp
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hfundamental :
      ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        scale * ∏ i : Fin 6,
          Real.sqrt (primitiveIntervalEnergy (U i) h) := by
    have hbound := compatibleIntervalContraction_le_of_noSingleton
      s h U hused hnoone
    simpa [scale, fixedSupportCompatibleIntervalContraction,
      compatibleIntervalContraction, compatibleFrequencyContraction,
      primitiveIntervalFourier, primitiveIntervalEnergy] using hbound
  have henergy :
      ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        scale * ∏ i : Fin 6,
          Real.sqrt ((primeProduct (U i) : ℝ) * h) :=
    six_primitiveIntervalEnergy_contraction_le U h
      (fixedSupportCompatibleIntervalContraction s h U) scale
      hprime hne hscale hfundamental
  have hcoefficient : 0 ≤
      ∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹ := by
    apply Finset.prod_nonneg
    intro i hi
    apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [norm_mul, norm_sixRamanujanCoefficient U hprime]
  calc
    (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
          ‖fixedSupportCompatibleIntervalContraction s h U‖ ≤
        (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
          (scale * ∏ i : Fin 6,
            Real.sqrt ((primeProduct (U i) : ℝ) * h)) :=
      mul_le_mul_of_nonneg_left henergy hcoefficient
    _ = (h : ℝ) ^ 3 *
          ∏ p ∈ usedPrimes U,
            sixthSupportWeight (p : ℝ) (primeSupport U p) := by
      simpa [scale, primeSupport] using
        (six_support_energy_normalization (usedPrimes U) U h
          hUused hPused hmult)
    _ = (h : ℝ) ^ 3 *
          sixSubsetWeight s.primeFactors
            (familySupportTuple s.primeFactors U) := by
      rw [sixSubsetWeight_family_eq_usedPrimes_prod s.primeFactors U hsub]

/-! ## Finite assembly of the fixed-support estimates -/

/-- The fixed-support contraction bound and multiplicity-one vanishing,
combined with the exact Fourier expansion and the support Euler product. -/
theorem centeredSixthMoment_le_localFactorProduct_of_fixedSupportBounds
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    (hadmissible : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        fixedSupportMomentContribution s h U ≤
          (s : ℝ) * (h : ℝ) ^ 3 *
            sixSubsetWeight s.primeFactors
              (familySupportTuple s.primeFactors U))
    (hvanish : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      ¬ IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        fixedSupportMomentContribution s h U = 0) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  have hP : ∀ p ∈ s.primeFactors, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hinj : Set.InjOn (familySupportTuple s.primeFactors)
      (nonemptySixSubsetFamilies s.primeFactors) := by
    intro U hU V hV hUV
    exact familySupportTuple_injective_on s.primeFactors
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (mem_nonemptySixSubsetFamilies.mp hV).1 hUV
  have hnonempty : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      AllSixSubsetsNonempty (familySupportTuple s.primeFactors U) := by
    intro U hU
    exact familySupportTuple_all_nonempty s.primeFactors U
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (mem_nonemptySixSubsetFamilies.mp hU).2
  have hassembly :
      ∑ U ∈ nonemptySixSubsetFamilies s.primeFactors,
          fixedSupportMomentContribution s h U ≤
        (s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p :=
    sum_six_family_contributions_le_localFactorProduct_natScale
      s.primeFactors hP (familySupportTuple s.primeFactors)
      hinj hnonempty s h (fixedSupportMomentContribution s h)
      hadmissible hvanish
  have hsum :
      ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 ≤
        (s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
    rw [sum_norm_amplitude_pow_six_eq_re_support_sum s h hs hsquare]
    simpa [fixedSupportMomentContribution, nonemptySixSubsetFamilies,
      nonconstantRamanujanSubsets] using hassembly
  have hfactor : 0 ≤ (s : ℝ) * (h : ℝ) ^ 3 *
      ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    · apply Finset.prod_nonneg
      intro p hp
      exact sixthLocalFactor_nonneg p (by exact_mod_cast hP p hp)
  have hdensityPow : density s ^ 6 ≤ density s ^ 3 :=
    pow_le_pow_of_le_one (density_nonneg s) (density_le_one s) (by norm_num)
  rw [centeredSixthMoment_eq_density_pow_six_mul s h hs hsquare]
  calc
    density s ^ 6 *
          ∑ u ∈ Finset.range s, ‖centeredRamanujanAmplitude s h u‖ ^ 6 ≤
        density s ^ 6 * ((s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (density_nonneg s) _)
    _ ≤ density s ^ 3 * ((s : ℝ) * (h : ℝ) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :=
      mul_le_mul_of_nonneg_right hdensityPow hfactor
    _ = (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p := by ring

/-- A compact interface for the sole analytic estimate: it suffices to bound
the coefficient-weighted compatible contraction for every admissible family.
All expansion, vanishing, support summation, and density bookkeeping are then
automatic. -/
theorem centeredSixthMoment_le_localFactorProduct_of_contractionBounds
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s)
    (hcontraction : ∀ U ∈ nonemptySixSubsetFamilies s.primeFactors,
      IsAdmissibleSixTuple (familySupportTuple s.primeFactors U) →
        ‖sixRamanujanCoefficient U *
          fixedSupportCompatibleIntervalContraction s h U‖ ≤
            (h : ℝ) ^ 3 *
              sixSubsetWeight s.primeFactors
                (familySupportTuple s.primeFactors U)) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  apply centeredSixthMoment_le_localFactorProduct_of_fixedSupportBounds
    hs hsquare
  · intro U hU hadmissible
    exact fixedSupportMomentContribution_le_of_contraction_norm hs hsquare
      (mem_nonemptySixSubsetFamilies.mp hU).1
      (hcontraction U hU hadmissible)
  · intro U hU hbad
    exact fixedSupportMomentContribution_eq_zero_of_not_admissible
      hs hsquare hU hbad

/-- The complete smooth-modulus sixth-moment estimate with its explicit
finite Euler product. -/
theorem centeredSixthMoment_le_localFactorProduct
    {s h : ℕ} (hs : 0 < s) (hsquare : Squarefree s) :
    centeredSixthMoment s h ≤
      (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
        ∏ p ∈ s.primeFactors, sixthLocalFactor p := by
  apply centeredSixthMoment_le_localFactorProduct_of_contractionBounds
    hs hsquare
  intro U hU hadmissible
  have hsupport := mem_nonemptySixSubsetFamilies.mp hU
  exact norm_coefficient_mul_fixedSupportContraction_le
    hsupport.1 hsupport.2 hadmissible

/-! ## From the local-factor estimate to the published moment bound -/

/-- The purely algebraic final assembly: once the Fourier/fundamental-lemma
calculation has bounded the moment by the local Euler product, weak Mertens
turns that product into the fixed logarithmic power used by
`SmallPrimeSixthMomentBound`.

This lemma is deliberately kept separate from the proof of the local-factor
estimate below.  Its hypothesis is discharged in this file by
`centeredSixthMoment_le_localFactorProduct`; it is not an assumption of the
final theorem. -/
theorem exists_smallPrimeSixthMomentBound_of_localFactor
    (hlocal : ∀ {s h : ℕ}, 0 < s → Squarefree s →
      centeredSixthMoment s h ≤
        (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p) :
    ∃ A : ℝ, SmallPrimeSixthMomentBound A := by
  obtain ⟨C, hC, hprod⟩ := exists_sixthLocalFactor_prod_le
  let D : ℝ := max C (Real.log 2)⁻¹
  let A : ℝ := D ^ 1432
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := hC.trans_le (le_max_left _ _)
  have hA : 0 < A := pow_pos hD _
  refine ⟨A, hA, ?_⟩
  intro s h hs hsquare hh hsmooth
  let L : ℝ := Real.log (2 * (h : ℝ))
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by norm_cast; omega)
  have hlog_mono : Real.log (2 : ℝ) ≤ L := by
    dsimp [L]
    apply Real.log_le_log
    · norm_num
    · norm_cast
      omega
  have hDlog2 : 1 ≤ D * Real.log 2 := by
    have hinv : (Real.log 2)⁻¹ ≤ D := le_max_right _ _
    calc
      (1 : ℝ) = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ D * Real.log 2 := mul_le_mul_of_nonneg_right hinv hlog2.le
  have hDL : 1 ≤ D * L :=
    hDlog2.trans <| mul_le_mul_of_nonneg_left hlog_mono hD.le
  have hCD : C ≤ D := le_max_left _ _
  have hprod' :
      ∏ p ∈ s.primeFactors, sixthLocalFactor p ≤ D ^ 1432 * L ^ 1432 := by
    calc
      ∏ p ∈ s.primeFactors, sixthLocalFactor p
          ≤ (C * L) ^ 716 := by
            dsimp [L]
            exact hprod hh hsmooth
      _ ≤ (D * L) ^ 716 := by
            exact pow_le_pow_left₀ (mul_nonneg hC.le hL)
              (mul_le_mul_of_nonneg_right hCD hL) _
      _ ≤ (D * L) ^ 1432 := by
            exact pow_le_pow_right₀ hDL (by norm_num)
      _ = D ^ 1432 * L ^ 1432 := by rw [mul_pow]
  have hscale : 0 ≤ (s : ℝ) * ((h : ℝ) * density s) ^ 3 := by
    exact mul_nonneg (Nat.cast_nonneg _) <|
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (density_nonneg s)) _
  calc
    centeredSixthMoment s h ≤
        (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          ∏ p ∈ s.primeFactors, sixthLocalFactor p :=
      hlocal hs hsquare
    _ ≤ (s : ℝ) * ((h : ℝ) * density s) ^ 3 *
          (D ^ 1432 * L ^ 1432) :=
      mul_le_mul_of_nonneg_left hprod' hscale
    _ = A * s * ((h : ℝ) * density s) ^ 3 *
          Real.log (2 * (h : ℝ)) ^ 1432 := by
      dsimp [A, L]
      ring

/-- Unconditional existence of the absolute constant in the small-prime
sixth-moment estimate. -/
theorem exists_smallPrimeSixthMomentBound :
    ∃ A : ℝ, SmallPrimeSixthMomentBound A :=
  exists_smallPrimeSixthMomentBound_of_localFactor
    centeredSixthMoment_le_localFactorProduct

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/LargePrime.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The large-prime occupancy bound for Erdős problem 220

This file proves the finite ``one forbidden residue per prime'' inequality
used in the Montgomery--Vaughan argument.  The proof is entirely finite.  Its
core is an induction over the prime coordinates, with Bernoulli's inequality
providing the induction step.
-/

namespace LargePrime

open scoped BigOperators
open Finset

universe u

/-- A recursively presented product of finite residue spaces. -/
def Config : List ℕ → Type
  | [] => Unit
  | p :: ps => Fin p × Config ps

instance configFinite (ps : List ℕ) : Finite (Config ps) := by
  induction ps with
  | nil => exact Finite.of_fintype Unit
  | cons p ps ih => simpa [Config] using inferInstanceAs (Finite (Fin p × Config ps))

@[simp] theorem natCard_config : ∀ ps : List ℕ, Nat.card (Config ps) = ps.prod
  | [] => by simp [Config]
  | p :: ps => by simp [Config, Nat.card_prod, natCard_config ps]

/-- At each coordinate, every label has its own forbidden residue. -/
inductive Forbidden (α : Type u) : List ℕ → Type (u + 1)
  | nil : Forbidden α []
  | cons {p : ℕ} {ps : List ℕ} (head : α ↪ Fin p) (tail : Forbidden α ps) :
      Forbidden α (p :: ps)

namespace Forbidden

/-- Pull a forbidden-residue family back along an embedding of labels. -/
def comap {α β : Type*} (e : β ↪ α) : {ps : List ℕ} → Forbidden α ps → Forbidden β ps
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons ⟨fun b => head (e b), head.injective.comp e.injective⟩ (tail.comap e)

/-- A configuration hits a label if one coordinate equals its forbidden residue. -/
def Hit {α : Type*} : {ps : List ℕ} → Forbidden α ps → Config ps → α → Prop
  | [], .nil, _, _ => False
  | _ :: _, .cons head tail, x, a => x.1 = head a ∨ tail.Hit x.2 a

@[simp] theorem hit_comap {α β : Type*} {ps : List ℕ} (e : β ↪ α)
    (f : Forbidden α ps) (x : Config ps) (b : β) :
    (f.comap e).Hit x b ↔ f.Hit x (e b) := by
  induction f with
  | nil => simp [comap, Hit]
  | cons head tail ih => simp [comap, Hit, ih]

end Forbidden

/-- Configurations which hit every label. -/
abbrev Covered {α : Type*} {ps : List ℕ} (f : Forbidden α ps) :=
  {x : Config ps // ∀ a, f.Hit x a}

/-- Number of configurations which hit every label. -/
noncomputable def coverCount {α : Type*} {ps : List ℕ} (f : Forbidden α ps) : ℕ :=
  Nat.card (Covered f)

/-- The probability that one fixed label is missed by every coordinate. -/
def avoidProb : List ℕ → ℚ
  | [] => 1
  | p :: ps => ((p - 1 : ℕ) : ℚ) / p * avoidProb ps

/-- Removing the head-forbidden label already hit by `y`. -/
def remainingEmbedding {α : Type*} {p : ℕ} (e : α ↪ Fin p) (y : Fin p) :
    {a : α // e a ≠ y} ↪ α := Function.Embedding.subtype _

/-- Splitting off the first coordinate identifies a covered configuration
with a first residue and a tail configuration covering all labels not already
hit by that residue. -/
noncomputable def coveredConsEquiv {α : Type*} {p : ℕ} {ps : List ℕ}
    (e : α ↪ Fin p) (f : Forbidden α ps) :
    Covered (.cons e f) ≃
      Σ y : Fin p, Covered (f.comap (remainingEmbedding e y)) where
  toFun x :=
    ⟨x.1.1, x.1.2, fun a => by
      rw [Forbidden.hit_comap]
      exact (x.2 a.1).resolve_left fun h => a.2 h.symm⟩
  invFun x :=
    ⟨(x.1, x.2.1), fun a => by
      by_cases h : e a = x.1
      · exact Or.inl h.symm
      · exact Or.inr ((Forbidden.hit_comap (remainingEmbedding e x.1) f x.2.1
          ⟨a, h⟩).mp (x.2.2 ⟨a, h⟩))⟩
  left_inv x := by ext <;> rfl
  right_inv x := by rcases x with ⟨y, x⟩; ext <;> rfl

@[simp] theorem coverCount_cons {α : Type*} [Fintype α] {p : ℕ} {ps : List ℕ}
    (e : α ↪ Fin p) (f : Forbidden α ps) :
    coverCount (.cons e f) =
      ∑ y : Fin p, coverCount (f.comap (remainingEmbedding e y)) := by
  classical
  rw [coverCount, Nat.card_congr (coveredConsEquiv e f), Nat.card_sigma]
  rfl

theorem natCard_remaining {α : Type*} [Fintype α] {p : ℕ}
    (e : α ↪ Fin p) (y : Fin p) :
    Nat.card {a : α // e a ≠ y} =
      if y ∈ Finset.univ.map e then Fintype.card α - 1 else Fintype.card α := by
  classical
  by_cases hy : y ∈ Finset.univ.map e
  · rw [Finset.mem_map] at hy
    obtain ⟨a, _ha, rfl⟩ := hy
    simp [Nat.card_eq_fintype_card, e.injective.eq_iff]
  · have hne : ∀ a, e a ≠ y := fun a h => hy (Finset.mem_map.mpr ⟨a, by simp, h⟩)
    simp [Nat.card_eq_fintype_card, hy, hne]

theorem card_range_embedding {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) :
    (Finset.univ.map e).card = Fintype.card α := by simp

/-- The exact two-level sum which occurs after exposing one coordinate. -/
theorem sum_pow_natCard_remaining {α : Type*} [Fintype α] {p : ℕ}
  (e : α ↪ Fin p) (q : ℚ) :
    (∑ y : Fin p, q ^ Nat.card {a : α // e a ≠ y}) =
      (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) +
        (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
  classical
  let R : Finset (Fin p) := Finset.univ.map e
  have hR : R.card = Fintype.card α := card_range_embedding e
  have hin :
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
        (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) := by
    rw [show (Finset.univ.filter fun x => x ∈ R) = R by ext x; simp [R]]
    calc
      (∑ x ∈ R, q ^ Nat.card {a : α // e a ≠ x}) =
          ∑ _x ∈ R, q ^ (Fintype.card α - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [natCard_remaining, if_pos]
            simpa [R] using hx
      _ = (Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, hR]
  have hout :
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with ¬x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
        (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
    have hcardIn :
        ((Finset.univ : Finset (Fin p)).filter fun x => x ∈ R).card =
          Fintype.card α := by
      rw [show (Finset.univ.filter fun x => x ∈ R) = R by ext x; simp [R], hR]
    have hcardOut :
        ((Finset.univ : Finset (Fin p)).filter fun x => ¬x ∈ R).card =
          p - Fintype.card α := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin p))) (p := fun x => x ∈ R)
      rw [hcardIn, Finset.card_univ, Fintype.card_fin] at hpart
      omega
    calc
      (∑ x ∈ (Finset.univ : Finset (Fin p)) with ¬x ∈ R,
          q ^ Nat.card {a : α // e a ≠ x}) =
          ∑ _x ∈ (Finset.univ : Finset (Fin p)) with ¬_x ∈ R,
            q ^ Fintype.card α := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [natCard_remaining, if_neg]
              simpa [R] using (Finset.mem_filter.mp hx).2
      _ = (p - Fintype.card α : ℕ) * q ^ Fintype.card α := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardOut]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin p)))
    (p := fun y => y ∈ R) (f := fun y => q ^ Nat.card {a : α // e a ≠ y}), hin, hout]

/-- Bernoulli's inequality in the precise homogeneous form used below. -/
theorem first_two_terms_le_add_pow (q r : ℚ) (hq : 0 ≤ q) (hr : 0 ≤ r) (a : ℕ) :
    q ^ a + a * q ^ (a - 1) * r ≤ (q + r) ^ a := by
  exact pow_add_mul_le_add_pow hq (by positivity) a

theorem avoidProb_nonneg : ∀ ps : List ℕ, 0 ≤ avoidProb ps
  | [] => by simp [avoidProb]
  | p :: ps => by
      rw [avoidProb]
      exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (avoidProb_nonneg ps)

theorem avoidProb_le_one : ∀ {ps : List ℕ}, (∀ p ∈ ps, 0 < p) → avoidProb ps ≤ 1
  | [], _ => by simp [avoidProb]
  | p :: ps, hpos => by
      rw [avoidProb]
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
      have hfac : (((p - 1 : ℕ) : ℚ) / p) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hp)]
        exact_mod_cast Nat.sub_le p 1
      exact mul_le_one₀ hfac (avoidProb_nonneg ps) (avoidProb_le_one htail)

/-- Abstract finite negative-dependence bound for independent coordinates,
each of which has one distinct forbidden residue for each label. -/
theorem cover_density_le :
    ∀ (ps : List ℕ) {α : Type*} [Fintype α]
      (hpos : ∀ p ∈ ps, 0 < p) (f : Forbidden α ps),
      (coverCount f : ℚ) / ps.prod ≤
        (1 - avoidProb ps) ^ Fintype.card α := by
  intro ps
  induction ps with
  | nil =>
      intro α _hαF hpos f
      cases f with
      | nil =>
          classical
          by_cases hα : IsEmpty α
          · letI : IsEmpty α := hα
            simp [coverCount, Covered, Forbidden.Hit, avoidProb, Config]
          · let a : α := Classical.choice (not_isEmpty_iff.mp hα)
            have hempty : IsEmpty (Covered (Forbidden.nil : Forbidden α [])) :=
              ⟨fun x => False.elim (x.2 a)⟩
            simp [coverCount, avoidProb, hempty]
  | cons p ps ih =>
      intro α _hαF hpos family
      cases family with
      | cons e f =>
          classical
          have hp : 0 < p := hpos p (by simp)
          have hps : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
          have hprod : 0 < ps.prod := List.prod_pos hps
          let q : ℚ := 1 - avoidProb ps
          have hav0 : 0 ≤ avoidProb ps := avoidProb_nonneg ps
          have hav1 : avoidProb ps ≤ 1 := avoidProb_le_one hps
          have hq0 : 0 ≤ q := sub_nonneg.mpr hav1
          have hpq : (0 : ℚ) < p := by exact_mod_cast hp
          have hcard : Fintype.card α ≤ p := by
            simpa using Fintype.card_le_of_injective e e.injective
          rw [coverCount_cons, List.prod_cons, Nat.cast_sum, Nat.cast_mul, sum_div]
          calc
        (∑ y : Fin p, (coverCount (f.comap (remainingEmbedding e y)) : ℚ) /
            (p * ps.prod)) =
            (1 / p) * ∑ y : Fin p,
              (coverCount (f.comap (remainingEmbedding e y)) : ℚ) / ps.prod := by
                rw [mul_sum]
                apply Finset.sum_congr rfl
                intro y _hy
                field_simp
        _ ≤ (1 / p) * ∑ y : Fin p,
              q ^ Nat.card {a : α // e a ≠ y} := by
                gcongr with y
                simpa [q, Nat.card_eq_fintype_card] using
                  ih (α := {a : α // e a ≠ y}) hps
                    (f.comap (remainingEmbedding e y))
        _ = (1 / p) * ((Fintype.card α : ℚ) * q ^ (Fintype.card α - 1) +
              (p - Fintype.card α : ℕ) * q ^ Fintype.card α) := by
                rw [sum_pow_natCard_remaining]
        _ = q ^ Fintype.card α + (Fintype.card α : ℚ) *
              q ^ (Fintype.card α - 1) * ((1 - q) / p) := by
                rw [Nat.cast_sub hcard]
                generalize Fintype.card α = a at *
                cases a with
                | zero => field_simp; ring
                | succ a =>
                    simp only [Nat.succ_sub_one]
                    rw [pow_succ]
                    field_simp
                    ring
        _ ≤ (q + (1 - q) / p) ^ Fintype.card α := by
                apply first_two_terms_le_add_pow q ((1 - q) / p) hq0
                exact div_nonneg (by dsimp [q]; linarith) hpq.le
        _ = (1 - avoidProb (p :: ps)) ^ Fintype.card α := by
                rw [avoidProb]
                dsimp [q]
                rw [Nat.cast_sub (by omega : 1 ≤ p)]
                field_simp
                congr 1
                ring

/-! ## Arithmetic realization -/

/-- The forbidden residue `-t (mod p)`, written as the representative `p-t`.
The hypotheses used below ensure `0 < t < p`. -/
def negShiftFin (p t : ℕ) (ht0 : 0 < t) (htp : t < p) : Fin p :=
  ⟨p - t, by omega⟩

theorem negShiftFin_injective {α : Type*} {p : ℕ} (t : α → ℕ)
    (ht0 : ∀ a, 0 < t a) (htp : ∀ a, t a < p) (hinj : Function.Injective t) :
    Function.Injective (fun a => negShiftFin p (t a) (ht0 a) (htp a)) := by
  intro a b hab
  apply hinj
  have heq : p - t a = p - t b := congrArg Fin.val hab
  change p - t a = p - t b at heq
  exact (tsub_right_inj (htp a).le (htp b).le).mp heq

/-- Canonical forbidden residues for shifts in `A`, over a list of moduli all
larger than the containing interval. -/
def intervalForbidden (h : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 h) :
    ∀ (ps : List ℕ), (∀ p ∈ ps, h < p) → Forbidden (↑A) ps
  | [], _ => .nil
  | p :: ps, hp =>
      have hphead : h < p := hp p (by simp)
      .cons
        ⟨fun t => negShiftFin p t.1 (Finset.mem_Icc.mp (hA t.2)).1
            ((Finset.mem_Icc.mp (hA t.2)).2.trans_lt hphead),
          negShiftFin_injective (fun t : ↑A => t.1)
            (fun t => (Finset.mem_Icc.mp (hA t.2)).1)
            (fun t => (Finset.mem_Icc.mp (hA t.2)).2.trans_lt hphead)
            Subtype.val_injective⟩
        (intervalForbidden h A hA ps (fun q hq => hp q (by simp [hq])))

/-- Recursive Chinese-remainder equivalence from one residue modulo a product
to the corresponding product of canonical finite residue spaces. -/
noncomputable def crtConfigEquiv :
    ∀ (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
      (hpos : ∀ p ∈ ps, 0 < p), ZMod ps.prod ≃ Config ps
  | [], _, _ => Equiv.ofUnique (ZMod 1) Unit
  | p :: ps, hcop, hpos => by
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
      have hhead : ∀ q ∈ ps, p.Coprime q := (List.pairwise_cons.mp hcop).1
      have hprod : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr hhead
      letI : NeZero p := ⟨hp.ne'⟩
      exact (ZMod.chineseRemainder hprod).toEquiv |>.trans
        (Equiv.prodCongr (ZMod.finEquiv p).symm.toEquiv
          (crtConfigEquiv ps (List.Pairwise.of_cons hcop) htail))

theorem negShiftFin_iff_dvd_add {p t : ℕ} (hp : 0 < p) (ht0 : 0 < t)
    (htp : t < p) (x : Fin p) :
    x = negShiftFin p t ht0 htp ↔ p ∣ x.1 + t := by
  constructor
  · rintro rfl
    simp [negShiftFin, Nat.sub_add_cancel htp.le]
  · intro hd
    apply Fin.ext
    have hsum0 : 0 < x.1 + t := by omega
    have hsum2 : x.1 + t < 2 * p := by omega
    have heq : x.1 + t = p :=
      Nat.eq_of_dvd_of_lt_two_mul hsum0.ne' hd (by simpa [two_mul] using hsum2)
    dsimp [negShiftFin]
    omega

theorem negShiftFin_iff_nonunit {p t : ℕ} (hp : p.Prime) (ht0 : 0 < t)
    (htp : t < p) (x : Fin p) :
    x = negShiftFin p t ht0 htp ↔
      ¬IsUnit ((x.1 + t : ℕ) : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not,
    negShiftFin_iff_dvd_add hp.pos ht0 htp]

theorem natCast_finEquiv {p : ℕ} [NeZero p] (x : Fin p) :
    ((x.1 : ℕ) : ZMod p) = (ZMod.finEquiv p) x := by
  rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv p) x)]
  congr 1
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rfl

theorem primeFactors_toList_pairwise (v : ℕ) :
    v.primeFactors.toList.Pairwise Nat.Coprime := by
  apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _)
  intro p hp q hq hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (by simpa using hp))
    (Nat.prime_of_mem_primeFactors (by simpa using hq))).mpr hpq

/-- Under CRT, the abstract cover event is exactly simultaneous nonunitness
of all shifted residues. -/
theorem intervalForbidden_hit_crt_iff (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) :
    ∀ (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime)
      (hlarge : ∀ p ∈ ps, h < p) (hcop : ps.Pairwise Nat.Coprime)
      (z : ZMod ps.prod) (t : ↑A),
      (intervalForbidden h A hA ps hlarge).Hit
          (crtConfigEquiv ps hcop (fun p hp => (hprime p hp).pos) z) t ↔
        ¬IsUnit (z + (t.1 : ZMod ps.prod)) := by
  intro ps
  induction ps with
  | nil =>
      intro hprime hlarge hcop z t
      simp only [intervalForbidden, Forbidden.Hit, false_iff, not_not]
      change IsUnit ((show ZMod 1 from z) + (t.1 : ZMod 1))
      have hz : (show ZMod 1 from z) + (t.1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hz]
      exact isUnit_one
  | cons p ps ih =>
      intro hprime hlarge hcop z t
      have hp : p.Prime := hprime p (by simp)
      have hp0 : 0 < p := hp.pos
      have htailPrime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (by simp [hq])
      have htailLarge : ∀ q ∈ ps, h < q := fun q hq => hlarge q (by simp [hq])
      have htailCop : ps.Pairwise Nat.Coprime := List.Pairwise.of_cons hcop
      have hheadCop : ∀ q ∈ ps, p.Coprime q := (List.pairwise_cons.mp hcop).1
      have hprodCop : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr hheadCop
      have htp : t.1 < p :=
        (Finset.mem_Icc.mp (hA t.2)).2.trans_lt (hlarge p (by simp))
      have ht0 : 0 < t.1 := (Finset.mem_Icc.mp (hA t.2)).1
      letI : NeZero p := ⟨hp.ne_zero⟩
      let cr : ZMod (p :: ps).prod ≃+* ZMod p × ZMod ps.prod :=
        ZMod.chineseRemainder hprodCop
      let x : Fin p := (ZMod.finEquiv p).symm (cr z).1
      have hxval : ((x.1 : ℕ) : ZMod p) = (cr z).1 := by
        rw [natCast_finEquiv]
        exact (ZMod.finEquiv p).apply_symm_apply (cr z).1
      have hhead :
          x = negShiftFin p t.1 ht0 htp ↔ ¬IsUnit ((cr z).1 + (t.1 : ZMod p)) := by
        rw [← hxval, ← Nat.cast_add]
        exact negShiftFin_iff_nonunit hp ht0 htp x
      have htail := ih htailPrime htailLarge htailCop (cr z).2 t
      have hunit :
          IsUnit (z + (t.1 : ZMod (p :: ps).prod)) ↔
            IsUnit ((cr z).1 + (t.1 : ZMod p)) ∧
              IsUnit ((cr z).2 + (t.1 : ZMod ps.prod)) := by
        have hmap :
            cr (z + (t.1 : ZMod (p :: ps).prod)) =
              ((cr z).1 + (t.1 : ZMod p), (cr z).2 + (t.1 : ZMod ps.prod)) := by
          rw [map_add, map_natCast]
          rfl
        calc
          IsUnit (z + (t.1 : ZMod (p :: ps).prod)) ↔
              IsUnit (cr (z + (t.1 : ZMod (p :: ps).prod))) :=
                (MulEquiv.isUnit_map cr.toMulEquiv).symm
          _ ↔ IsUnit ((cr z).1 + (t.1 : ZMod p)) ∧
                IsUnit ((cr z).2 + (t.1 : ZMod ps.prod)) := by
                  rw [hmap, Prod.isUnit_iff]
      change (x = negShiftFin p t.1 ht0 htp ∨
          (intervalForbidden h A hA ps htailLarge).Hit
            (crtConfigEquiv ps htailCop (fun q hq => (htailPrime q hq).pos) (cr z).2) t) ↔
        ¬IsUnit (z + (t.1 : ZMod (p :: ps).prod))
      rw [hhead, htail, hunit, not_and_or]

/-- Number of residue classes modulo `m` for which every shift in `A` is a
nonunit.  For positive `m` this is the ordinary cardinality of a filtered
`Finset.univ : Finset (ZMod m)`. -/
noncomputable def shiftedNonunitCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  Nat.card {z : ZMod m // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod m))}

/-- The same count in the literal gcd/coprimality formulation on canonical
representatives `0 ≤ z < m`. -/
def shiftedNoncoprimeResidueCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range m).filter fun z =>
    ∀ t : ↑A, ¬Nat.Coprime (z + t.1) m).card

theorem shifted_isUnit_iff_coprime {m : ℕ} [NeZero m] (z : ZMod m) (t : ℕ) :
    IsUnit (z + (t : ZMod m)) ↔ Nat.Coprime (z.val + t) m := by
  rw [← ZMod.natCast_zmod_val z, ← Nat.cast_add, ZMod.isUnit_iff_coprime]
  rw [ZMod.val_natCast_of_lt z.val_lt]

noncomputable def shiftedNonunitEquivFilter {m : ℕ} [NeZero m] (A : Finset ℕ) :
    {z : ZMod m // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod m))} ≃
      {z : ℕ // z ∈ (Finset.range m).filter fun z =>
        ∀ t : ↑A, ¬Nat.Coprime (z + t.1) m} where
  toFun z := ⟨z.1.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr z.1.val_lt,
    fun t => (shifted_isUnit_iff_coprime z.1 t.1).not.mp (z.2 t)⟩⟩
  invFun z :=
    ⟨(z.1 : ZMod m), fun t => by
      rw [shifted_isUnit_iff_coprime,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp z.2).1)]
      exact (Finset.mem_filter.mp z.2).2 t⟩
  left_inv z := by
    apply Subtype.ext
    exact ZMod.natCast_zmod_val z.1
  right_inv z := by
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp z.2).1)

theorem shiftedNonunitCount_eq_noncoprime {m : ℕ} (hm : 0 < m) (A : Finset ℕ) :
    shiftedNonunitCount m A = shiftedNoncoprimeResidueCount m A := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [shiftedNonunitCount, shiftedNoncoprimeResidueCount,
    Nat.card_congr (shiftedNonunitEquivFilter A), Nat.card_eq_fintype_card,
    Fintype.card_coe]

noncomputable def coveredEquivShiftedNonunits (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    Covered (intervalForbidden h A hA ps hlarge) ≃
      {z : ZMod ps.prod // ∀ t : ↑A, ¬IsUnit (z + (t.1 : ZMod ps.prod))} := by
  let E := crtConfigEquiv ps hcop (fun p hp => (hprime p hp).pos)
  refine E.symm.subtypeEquiv ?_
  intro x
  constructor
  · intro hx t
    apply (intervalForbidden_hit_crt_iff h A hA ps hprime hlarge hcop (E.symm x) t).mp
    simpa [E] using hx t
  · intro hx t
    have ht := (intervalForbidden_hit_crt_iff h A hA ps hprime hlarge hcop
      (E.symm x) t).mpr (hx t)
    simpa [E] using ht

theorem coverCount_intervalForbidden (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    coverCount (intervalForbidden h A hA ps hlarge) =
      shiftedNonunitCount ps.prod A := by
  exact Nat.card_congr (coveredEquivShiftedNonunits h A hA ps hprime hlarge hcop)

/-- Large-prime negative dependence for a list of distinct prime moduli. -/
theorem list_largePrime_density_le (h : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hlarge : ∀ p ∈ ps, h < p)
    (hcop : ps.Pairwise Nat.Coprime) :
    (shiftedNonunitCount ps.prod A : ℚ) / ps.prod ≤
      (1 - avoidProb ps) ^ A.card := by
  rw [← coverCount_intervalForbidden h A hA ps hprime hlarge hcop]
  simpa only [Fintype.card_coe] using
    cover_density_le ps (α := ↑A) (fun p hp => (hprime p hp).pos)
      (intervalForbidden h A hA ps hlarge)

theorem avoidProb_eq_prod_div : ∀ (ps : List ℕ),
    avoidProb ps =
      (((ps.map fun p : ℕ => p - 1).prod : ℕ) : ℚ) / ps.prod
  | [] => by simp [avoidProb]
  | p :: ps => by
      rw [avoidProb, avoidProb_eq_prod_div ps]
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
      push_cast
      ring

theorem avoidProb_primeFactors {v : ℕ} (hsq : Squarefree v) :
    avoidProb v.primeFactors.toList = (Nat.totient v : ℚ) / v := by
  rw [avoidProb_eq_prod_div]
  have hprod : v.primeFactors.toList.prod = v := by
    simpa using Nat.prod_primeFactors_of_squarefree hsq
  have hphi : (v.primeFactors.toList.map fun p => p - 1).prod = Nat.totient v := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hsq,
      Nat.div_self (Nat.pos_of_ne_zero hsq.ne_zero), one_mul]
    simp
  rw [hprod, hphi]

/-- Probability form of the large-prime lemma for a squarefree modulus. -/
theorem squarefree_largePrime_density_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    (shiftedNonunitCount v A : ℚ) / v ≤
      (1 - (Nat.totient v : ℚ) / v) ^ A.card := by
  let ps := v.primeFactors.toList
  have hprod : ps.prod = v := by
    simpa [ps] using Nat.prod_primeFactors_of_squarefree hsq
  have hprime : ∀ p ∈ ps, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (by simpa [ps] using hp)
  have hlargeList : ∀ p ∈ ps, h < p := by
    intro p hp
    exact hlarge p (by simpa [ps] using hp)
  have hcop : ps.Pairwise Nat.Coprime := by
    simpa [ps] using primeFactors_toList_pairwise v
  have hd := list_largePrime_density_le h A hA ps hprime hlargeList hcop
  simpa [hprod, ps, avoidProb_primeFactors hsq] using hd

end LargePrime

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220/SmoothRough.lean` -/

section
/-!
# The smooth--rough decomposition for Erdős problem 220

This file contains the arithmetic assembly surrounding the Montgomery--
Vaughan smooth--rough argument.  In particular, it proves that all the
quantities entering the empty-window estimate may be reduced, without any
loss, to the squarefree kernel, and records the canonical factorisation of
that kernel at the interval length.
-/

open scoped BigOperators

/-! ## Reduction to the squarefree kernel -/

/-- The squarefree kernel (radical) of a positive natural number. -/
def squarefreeKernel (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

@[simp] lemma squarefreeKernel_primeFactors (n : ℕ) :
    (squarefreeKernel n).primeFactors = n.primeFactors := by
  exact Nat.primeFactors_prod_primeFactors n

lemma squarefree_squarefreeKernel (n : ℕ) : Squarefree (squarefreeKernel n) := by
  rw [squarefreeKernel]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq ↦ ?_)
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq)

lemma squarefreeKernel_dvd (n : ℕ) : squarefreeKernel n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

lemma squarefreeKernel_pos {n : ℕ} (hn : 0 < n) : 0 < squarefreeKernel n := by
  rw [squarefreeKernel]
  exact Finset.prod_pos fun p hp ↦ Nat.pos_of_mem_primeFactors hp

/-- Coprimality depends only on the squarefree kernel. -/
lemma coprime_squarefreeKernel_iff {n m : ℕ} (hn : 0 < n) :
    (squarefreeKernel n).Coprime m ↔ n.Coprime m := by
  rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd,
    Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨p, hp, hpk, hpm⟩
    exact ⟨p, hp, hpk.trans (squarefreeKernel_dvd n), hpm⟩
  · rintro ⟨p, hp, hpn, hpm⟩
    have hpf : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
    exact ⟨p, hp, Finset.dvd_prod_of_mem id hpf, hpm⟩

lemma unitCount_squarefreeKernel {n h x : ℕ} (hn : 0 < n) :
    unitCount (squarefreeKernel n) h x = unitCount n h x := by
  unfold unitCount
  congr 1
  ext t
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _ht
  exact coprime_squarefreeKernel_iff hn

/-- `unitCount k h` is periodic in the starting point, with period `k`. -/
lemma unitCount_periodic (k h : ℕ) :
    Function.Periodic (unitCount k h) k := by
  intro x
  unfold unitCount
  congr 1
  ext t
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _ht
  exact eq_iff_iff.mp (by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.periodic_coprime k (x + t))

/-- A periodic predicate has the expected number of solutions in an
integral number of periods. -/
lemma card_filter_range_mul_of_periodic (p : ℕ → Prop) [DecidablePred p]
    (d m : ℕ) (hp : Function.Periodic p d) :
    ((Finset.range (m * d)).filter p).card =
      m * ((Finset.range d).filter p).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
      have hshift : (fun k ↦ p (m * d + k)) = p := by
        funext k
        have hh := hp.nsmul m k
        change p (k + m * d) = p k at hh
        simpa only [Nat.add_comm] using hh
      simpa only [hshift]

lemma emptyWindows_squarefreeKernel_pred {n h x : ℕ} (hn : 0 < n) :
    (unitCount (squarefreeKernel n) h x = 0) ↔ (unitCount n h x = 0) := by
  rw [unitCount_squarefreeKernel hn]

/-- Empty windows scale exactly through repeated periods of the squarefree
kernel. -/
lemma card_emptyWindows_eq_kernel_mul {n h : ℕ} (hn : 0 < n) :
    (emptyWindows n h).card =
      (n / squarefreeKernel n) * (emptyWindows (squarefreeKernel n) h).card := by
  let r := squarefreeKernel n
  let q := n / r
  have hr : 0 < r := squarefreeKernel_pos hn
  have hnqr : n = q * r := by
    dsimp [q, r]
    exact (Nat.div_mul_cancel (squarefreeKernel_dvd n)).symm
  have hperiod : Function.Periodic (fun x ↦ unitCount r h x = 0) r :=
    (unitCount_periodic r h).comp (fun z ↦ z = 0)
  have hcard := card_filter_range_mul_of_periodic
    (fun x ↦ unitCount r h x = 0) r q hperiod
  have hpred : (fun x ↦ unitCount n h x = 0) =
      (fun x ↦ unitCount r h x = 0) := by
    funext x
    exact propext (emptyWindows_squarefreeKernel_pred hn).symm
  change (emptyWindows n h).card = q * (emptyWindows r h).card
  simp only [emptyWindows, hpred]
  rw [hnqr]
  exact hcard

/-- Euler's totient scales by the same repetition factor as the window
count. -/
lemma totient_eq_kernel_mul {n : ℕ} (hn : 0 < n) :
    n.totient = (n / squarefreeKernel n) * (squarefreeKernel n).totient := by
  let r := squarefreeKernel n
  have hr : 0 < r := squarefreeKernel_pos hn
  let F := ∏ p ∈ n.primeFactors, (p - 1)
  have hφn : n.totient = (n / r) * F := by
    simpa only [r, F, squarefreeKernel] using
      Nat.totient_eq_div_primeFactors_mul n
  have hφr : r.totient = F := by
    rw [Nat.totient_eq_div_primeFactors_mul r]
    have hpf : r.primeFactors = n.primeFactors := by
      simpa only [r] using squarefreeKernel_primeFactors n
    rw [hpf]
    have hprod : (∏ p ∈ n.primeFactors, p) = r := by rfl
    rw [hprod, Nat.div_self hr]
    simp [F]
  rw [hφn, hφr]

/-- A division-free empty-window estimate for the squarefree kernel scales
to the original modulus with exactly the same constant. -/
lemma emptyWindows_bound_of_kernel {B : ℝ} {n h : ℕ} (hn : 0 < n)
    (H : ((emptyWindows (squarefreeKernel n) h).card : ℝ) * (h : ℝ) ^ 2 *
      ((squarefreeKernel n).totient : ℝ) ^ 2 ≤
        B * (squarefreeKernel n : ℝ) ^ 3) :
    ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
      B * (n : ℝ) ^ 3 := by
  let r := squarefreeKernel n
  let q := n / r
  have hnqr : n = q * r := by
    dsimp [q, r]
    exact (Nat.div_mul_cancel (squarefreeKernel_dvd n)).symm
  have hE : (emptyWindows n h).card = q * (emptyWindows r h).card := by
    simpa only [q, r] using card_emptyWindows_eq_kernel_mul (n := n) (h := h) hn
  have hphi : n.totient = q * r.totient := by
    simpa only [q, r] using totient_eq_kernel_mul hn
  rw [hE, hphi, hnqr]
  push_cast
  calc
    (↑q * ↑(emptyWindows r h).card) * (h : ℝ) ^ 2 *
          (↑q * ↑r.totient) ^ 2 =
        (q : ℝ) ^ 3 *
          ((↑(emptyWindows r h).card) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2) := by
            ring
    _ ≤ (q : ℝ) ^ 3 * (B * (r : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ = B * (↑q * ↑r) ^ 3 := by ring

/-! ## The small-prime/large-prime factorisation -/

/-- Product of the prime factors of `r` which do not exceed `h`. -/
def smoothPart (r h : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p ↦ p ≤ h), p

/-- Product of the prime factors of `r` which exceed `h`. -/
def roughPart (r h : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p ↦ h < p), p

lemma smoothPart_pos (r h : ℕ) : 0 < smoothPart r h := by
  rw [smoothPart]
  exact Finset.prod_pos fun p hp ↦
    Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma roughPart_pos (r h : ℕ) : 0 < roughPart r h := by
  rw [roughPart]
  exact Finset.prod_pos fun p hp ↦
    Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    smoothPart r h * roughPart r h = r := by
  rw [smoothPart, roughPart, ← Finset.prod_union]
  · rw [show r.primeFactors.filter (fun p ↦ p ≤ h) ∪
        r.primeFactors.filter (fun p ↦ h < p) = r.primeFactors by
      ext p
      by_cases hp : p ≤ h
      · simp [hp]
      · have hhp : h < p := Nat.lt_of_not_ge hp
        simp [hp, hhp]]
    exact Nat.prod_primeFactors_of_squarefree hr
  · rw [Finset.disjoint_left]
    intro p hpSmall hpLarge
    have hs := (Finset.mem_filter.mp hpSmall).2
    have hl := (Finset.mem_filter.mp hpLarge).2
    omega

lemma smoothPart_coprime_roughPart {r h : ℕ} (hr : Squarefree r) :
    (smoothPart r h).Coprime (roughPart r h) := by
  apply Nat.coprime_of_squarefree_mul
  rw [smoothPart_mul_roughPart hr]
  exact hr

lemma squarefree_smoothPart {r h : ℕ} (hr : Squarefree r) :
    Squarefree (smoothPart r h) := by
  have hd : smoothPart r h ∣ r :=
    ⟨roughPart r h, (smoothPart_mul_roughPart (h := h) hr).symm⟩
  exact Squarefree.squarefree_of_dvd hd hr

lemma squarefree_roughPart {r h : ℕ} (hr : Squarefree r) :
    Squarefree (roughPart r h) := by
  have hd : roughPart r h ∣ r :=
    ⟨smoothPart r h, by
      rw [mul_comm]
      exact (smoothPart_mul_roughPart (h := h) hr).symm⟩
  exact Squarefree.squarefree_of_dvd hd hr

lemma primeFactors_smoothPart_subset {r h : ℕ} :
    (smoothPart r h).primeFactors ⊆ r.primeFactors.filter (fun p ↦ p ≤ h) := by
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ smoothPart r h := (Nat.mem_primeFactors.mp hp).2.1
  rw [smoothPart, hpPrime.prime.dvd_finsetProd_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqPrime : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hpqeq : p = q := ((hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq).symm
  simpa [hpqeq] using hq

lemma smoothPart_prime_le {r h p : ℕ} (hp : p ∈ (smoothPart r h).primeFactors) :
    p ≤ h := by
  exact (Finset.mem_filter.mp (primeFactors_smoothPart_subset hp)).2

lemma roughPart_prime_gt {r h p : ℕ} (hp : p ∈ (roughPart r h).primeFactors) :
    h < p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ roughPart r h := (Nat.mem_primeFactors.mp hp).2.1
  rw [roughPart, hpPrime.prime.dvd_finsetProd_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqPrime : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hpqeq : p = q := ((hqPrime.dvd_iff_eq hpPrime.ne_one).mp hpq).symm
  simpa [hpqeq] using (Finset.mem_filter.mp hq).2

lemma totient_smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    r.totient = (smoothPart r h).totient * (roughPart r h).totient := by
  rw [← Nat.totient_mul (smoothPart_coprime_roughPart hr),
    smoothPart_mul_roughPart hr]

lemma density_smoothPart_mul_roughPart {r h : ℕ} (hr : Squarefree r) :
    density r = density (smoothPart r h) * density (roughPart r h) := by
  let s := smoothPart r h
  let v := roughPart r h
  have hrv : r = s * v := by
    simpa only [s, v] using (smoothPart_mul_roughPart hr).symm
  have hphi : r.totient = s.totient * v.totient := by
    simpa only [s, v] using totient_smoothPart_mul_roughPart hr
  change density r = density s * density v
  rw [density, density, density, hphi]
  conv_lhs => rw [hrv]
  push_cast
  field_simp [Nat.ne_of_gt (smoothPart_pos r h), Nat.ne_of_gt (roughPart_pos r h)]

/-! ## Exact CRT decomposition of empty windows -/

open LargePrime

/-- Empty windows are the simultaneous shifted-nonunit event used by the
large-prime lemma. -/
lemma card_emptyWindows_eq_shiftedNonunitCount {m : ℕ} (hm : 0 < m) (h : ℕ) :
    (emptyWindows m h).card = shiftedNonunitCount m (Finset.Icc 1 h) := by
  rw [shiftedNonunitCount_eq_noncoprime hm]
  apply congrArg Finset.card
  ext x
  simp only [emptyWindows, shiftedNoncoprimeResidueCount, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hx, hempty⟩
    refine ⟨hx, ?_⟩
    rw [unitCount_eq_zero_iff] at hempty
    intro t
    exact (hempty t.1 (Finset.mem_Icc.mp t.2).1
      (Finset.mem_Icc.mp t.2).2) ∘ Nat.Coprime.symm
  · rintro ⟨hx, hempty⟩
    refine ⟨hx, ?_⟩
    rw [unitCount_eq_zero_iff]
    intro t ht1 hth ht
    exact hempty ⟨t, Finset.mem_Icc.mpr ⟨ht1, hth⟩⟩ ht.symm

/-- Shifts which survive the small-prime coordinate `u`. -/
def survivingShifts (s h : ℕ) [NeZero s] (u : ZMod s) : Finset ℕ :=
  (Finset.Icc 1 h).filter fun t ↦ IsUnit (u + (t : ZMod s))

lemma survivingShifts_subset (s h : ℕ) [NeZero s] (u : ZMod s) :
    survivingShifts s h u ⊆ Finset.Icc 1 h := by
  classical
  exact Finset.filter_subset _ _

lemma card_survivingShifts_eq_unitCount {s : ℕ} [NeZero s]
    (h : ℕ) (u : ZMod s) :
    (survivingShifts s h u).card = unitCount s h u.val := by
  classical
  apply congrArg Finset.card
  ext t
  simp only [survivingShifts, unitCount, Finset.mem_filter, Finset.mem_Icc]
  rw [shifted_isUnit_iff_coprime]
  simp only [Nat.coprime_comm]

lemma crt_shift_isUnit_iff {s v : ℕ} (hcop : s.Coprime v)
    (x : ZMod (s * v)) (t : ℕ) :
    IsUnit (x + (t : ZMod (s * v))) ↔
      IsUnit (((ZMod.chineseRemainder hcop) x).1 + (t : ZMod s)) ∧
        IsUnit (((ZMod.chineseRemainder hcop) x).2 + (t : ZMod v)) := by
  let cr : ZMod (s * v) ≃+* ZMod s × ZMod v := ZMod.chineseRemainder hcop
  have hmap : cr (x + (t : ZMod (s * v))) =
      ((cr x).1 + (t : ZMod s), (cr x).2 + (t : ZMod v)) := by
    rw [map_add, map_natCast]
    rfl
  calc
    IsUnit (x + (t : ZMod (s * v))) ↔
        IsUnit (cr (x + (t : ZMod (s * v)))) :=
      (MulEquiv.isUnit_map cr.toMulEquiv).symm
    _ ↔ IsUnit ((cr x).1 + (t : ZMod s)) ∧
        IsUnit ((cr x).2 + (t : ZMod v)) := by
      rw [hmap, Prod.isUnit_iff]

/-- The simultaneous shifted-nonunit event modulo `s*v`, written as a
dependent sum over the small CRT coordinate. -/
noncomputable def emptyCrtEquiv (s v h : ℕ) [NeZero s] [NeZero v]
    (hcop : s.Coprime v) :
    {x : ZMod (s * v) //
      ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} ≃
      Σ u : ZMod s,
        {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
          ¬IsUnit (z + (t.1 : ZMod v))} := by
  classical
  let cr : ZMod (s * v) ≃+* ZMod s × ZMod v := ZMod.chineseRemainder hcop
  refine
    { toFun := fun x ↦
        ⟨(cr x.1).1, ⟨(cr x.1).2, fun t ht ↦ ?_⟩⟩
      invFun := fun y ↦
        ⟨cr.symm (y.1, y.2.1), fun t ht ↦ ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htmem : t.1 ∈ (Finset.Icc 1 h).filter
        (fun a : ℕ ↦ IsUnit ((cr x.1).1 + (a : ZMod s))) := by
      simpa only [survivingShifts] using t.2
    have hu : IsUnit ((cr x.1).1 + (t.1 : ZMod s)) :=
      (Finset.mem_filter.mp htmem).2
    have hboth : IsUnit (x.1 + (t.1 : ZMod (s * v))) :=
      (crt_shift_isUnit_iff hcop x.1 t.1).mpr ⟨hu, ht⟩
    exact x.2 ⟨t.1, (Finset.mem_filter.mp t.2).1⟩ hboth
  · have hboth := (crt_shift_isUnit_iff hcop (cr.symm (y.1, y.2.1)) t.1).mp ht
    have heq : (ZMod.chineseRemainder hcop) (cr.symm (y.1, y.2.1)) =
        (y.1, y.2.1) := by
      exact cr.apply_symm_apply (y.1, y.2.1)
    rw [heq] at hboth
    have hboth' : IsUnit (y.1 + (t.1 : ZMod s)) ∧
        IsUnit (y.2.1 + (t.1 : ZMod v)) := hboth
    let t' : ↑(survivingShifts s h y.1) :=
      ⟨t.1, by
        change t.1 ∈ (Finset.Icc 1 h).filter
          (fun a : ℕ ↦ IsUnit (y.1 + (a : ZMod s)))
        exact Finset.mem_filter.mpr ⟨t.2, hboth'.1⟩⟩
    exact y.2.2 t' hboth'.2
  · intro x
    apply Subtype.ext
    exact cr.symm_apply_apply x.1
  · rintro ⟨u, z⟩
    have hp := cr.apply_symm_apply (u, z.1)
    have hp1 : (cr (cr.symm (u, z.1))).1 = u := congrArg Prod.fst hp
    have hp2 : (cr (cr.symm (u, z.1))).2 = z.1 := congrArg Prod.snd hp
    apply Sigma.ext hp1
    refine (Subtype.heq_iff_coe_eq ?_).2 hp2
    intro x
    simp only [survivingShifts]
    have hset :
        (Finset.Icc 1 h).filter (fun t : ℕ ↦
          IsUnit ((cr (cr.symm (u, z.1))).1 + (t : ZMod s))) =
        (Finset.Icc 1 h).filter (fun t : ℕ ↦ IsUnit (u + (t : ZMod s))) := by
      exact congrArg (fun w : ZMod s ↦
        (Finset.Icc 1 h).filter (fun t : ℕ ↦ IsUnit (w + (t : ZMod s)))) hp1
    exact eq_iff_iff.mp (congrArg (fun U : Finset ℕ ↦
      ∀ t : ↑U, ¬IsUnit (x + (t.1 : ZMod v))) hset)

theorem shiftedNonunitCount_mul_eq_sum (s v h : ℕ) [NeZero s] [NeZero v]
    (hs : 0 < s) (hv : 0 < v) (hcop : s.Coprime v) :
    shiftedNonunitCount (s * v) (Finset.Icc 1 h) =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
  change Nat.card {x : ZMod (s * v) //
      ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} = _
  calc
    Nat.card {x : ZMod (s * v) //
        ∀ t : ↑(Finset.Icc 1 h), ¬IsUnit (x + (t.1 : ZMod (s * v)))} =
        Nat.card (Σ u : ZMod s,
          {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
            ¬IsUnit (z + (t.1 : ZMod v))}) :=
      Nat.card_congr (emptyCrtEquiv s v h hcop)
    _ = ∑ u : ZMod s, Nat.card
        {z : ZMod v // ∀ t : ↑(survivingShifts s h u),
          ¬IsUnit (z + (t.1 : ZMod v))} := Nat.card_sigma
    _ = ∑ u : ZMod s, shiftedNonunitCount v
        (survivingShifts s h u) := rfl

/-- Exact conditional-count identity behind the smooth--rough argument. -/
theorem card_emptyWindows_mul_eq_sum {s v : ℕ} (hs : 0 < s) (hv : 0 < v)
    [NeZero s] [NeZero v] (hcop : s.Coprime v) (h : ℕ) :
    (emptyWindows (s * v) h).card =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
  rw [card_emptyWindows_eq_shiftedNonunitCount (mul_pos hs hv),
    shiftedNonunitCount_mul_eq_sum s v h hs hv hcop]

/-! ## Two elementary analytic inequalities used in the good/bad split -/

lemma one_sub_pow_le_exp_neg_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a : ℕ) :
    (1 - x) ^ a ≤ Real.exp (-(a * x)) := by
  have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbase : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  calc
    (1 - x) ^ a ≤ Real.exp (-x) ^ a := pow_le_pow_left₀ hbase0 hbase a
    _ = Real.exp (-(a * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- The uniform polynomial form of exponential decay used for good smooth
residue classes. -/
lemma sq_mul_exp_neg_le_two (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 2 := by
  have hseries := Real.pow_div_factorial_le_exp x hx 2
  norm_num [Nat.factorial] at hseries
  have hexp : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ hexp]
  nlinarith

lemma pow_decay_mul_sq_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a : ℕ) :
    (1 - x) ^ a * ((a : ℝ) * x) ^ 2 ≤ 2 := by
  have hdecay := one_sub_pow_le_exp_neg_mul hx0 hx1 a
  have hax0 : 0 ≤ (a : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0
  calc
    (1 - x) ^ a * ((a : ℝ) * x) ^ 2 ≤
        Real.exp (-((a : ℝ) * x)) * ((a : ℝ) * x) ^ 2 := by
      gcongr
    _ ≤ 2 := by
      simpa [mul_comm] using sq_mul_exp_neg_le_two ((a : ℝ) * x) hax0

/-! ## The large-prime pointwise estimate -/

lemma shiftedNonunitCount_le_modulus {v : ℕ} (hv : 0 < v) (A : Finset ℕ) :
    shiftedNonunitCount v A ≤ v := by
  rw [shiftedNonunitCount_eq_noncoprime hv, shiftedNoncoprimeResidueCount]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range v)

/-- Multiplying the large-prime density estimate by the square of its
conditional mean removes all dependence on the number of surviving shifts. -/
lemma largePrime_count_mean_sq_le {v h : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 h) (hv : 0 < v) (hsq : Squarefree v)
    (hlarge : ∀ p ∈ v.primeFactors, h < p) :
    (shiftedNonunitCount v A : ℝ) *
        ((A.card : ℝ) * density v) ^ 2 ≤ 2 * v := by
  have hdQ := squarefree_largePrime_density_le A hA hsq hlarge
  have hdR : (shiftedNonunitCount v A : ℝ) / v ≤
      (1 - (v.totient : ℝ) / v) ^ A.card := by
    have hdCast :
        ((((shiftedNonunitCount v A : ℚ) / v : ℚ) : ℝ)) ≤
          ((((1 - (v.totient : ℚ) / v) ^ A.card : ℚ) : ℝ)) := by
      exact_mod_cast hdQ
    norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow] at hdCast
    exact hdCast
  have hdR' : (shiftedNonunitCount v A : ℝ) / v ≤
      (1 - density v) ^ A.card := by
    simpa only [density] using hdR
  have hdecay := pow_decay_mul_sq_le_two
    (x := density v) (density_pos hv).le (density_le_one v) A.card
  have hprob : (shiftedNonunitCount v A : ℝ) / v *
      ((A.card : ℝ) * density v) ^ 2 ≤ 2 :=
    (mul_le_mul_of_nonneg_right hdR' (sq_nonneg _)).trans hdecay
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  calc
    (shiftedNonunitCount v A : ℝ) * ((A.card : ℝ) * density v) ^ 2 =
        (v : ℝ) * ((shiftedNonunitCount v A : ℝ) / v *
          ((A.card : ℝ) * density v) ^ 2) := by field_simp
    _ ≤ (v : ℝ) * 2 := mul_le_mul_of_nonneg_left hprob hvR.le
    _ = 2 * v := by ring

/-- A smooth residue with at least half the expected number of surviving
shifts contributes at most `8*v` after the natural mean-square weighting. -/
lemma largePrime_good_residue_le {s v h : ℕ} [NeZero s]
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 h) (hv : 0 < v)
    (hsq : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p)
    (hgood : (h : ℝ) * density s / 2 ≤ A.card) :
    (shiftedNonunitCount v A : ℝ) *
        ((h : ℝ) * (density s * density v)) ^ 2 ≤ 8 * v := by
  have hpoint := largePrime_count_mean_sq_le A hA hv hsq hlarge
  have hds0 : 0 ≤ density s := (density_pos (NeZero.pos s)).le
  have hdv0 : 0 ≤ density v := (density_pos hv).le
  have hleft0 : 0 ≤ (h : ℝ) * (density s * density v) := by positivity
  have hright0 : 0 ≤ 2 * ((A.card : ℝ) * density v) := by positivity
  have hmean : (h : ℝ) * (density s * density v) ≤
      2 * ((A.card : ℝ) * density v) := by
    have hm := mul_le_mul_of_nonneg_right hgood hdv0
    nlinarith
  have hsquare : ((h : ℝ) * (density s * density v)) ^ 2 ≤
      (2 * ((A.card : ℝ) * density v)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmean) (add_nonneg hright0 hleft0)]
  calc
    (shiftedNonunitCount v A : ℝ) *
          ((h : ℝ) * (density s * density v)) ^ 2 ≤
        (shiftedNonunitCount v A : ℝ) *
          (2 * ((A.card : ℝ) * density v)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 4 * ((shiftedNonunitCount v A : ℝ) *
          ((A.card : ℝ) * density v) ^ 2) := by ring
    _ ≤ 4 * (2 * v) := mul_le_mul_of_nonneg_left hpoint (by norm_num)
    _ = 8 * v := by ring

/-! ## Good/bad residue summation -/

/-- Canonical representatives identify a filtered set of residues modulo
`s` with the corresponding filter of `range s`. -/
lemma card_filter_zmod_val_eq_range {s : ℕ} [NeZero s]
    (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (ZMod s)).filter (fun u ↦ P u.val)).card =
      ((Finset.range s).filter P).card := by
  classical
  refine Finset.card_bij (fun u _hu ↦ u.val) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.val_lt, hu⟩
  · intro u₁ hu₁ u₂ hu₂ heq
    exact ZMod.val_injective s heq
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    refine ⟨(a : ZMod s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp ha'.1)]
      exact ha'.2
    · exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha'.1)

lemma bad_residue_sum_le {α : Type*} [Fintype α] {B d : ℝ} {s v h : ℕ}
    (hv : 0 < v) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (bad : Finset α)
    (A : α → Finset ℕ)
    (htail : (bad.card : ℝ) * (h : ℝ) ^ 2 ≤ B * s) :
    (∑ u ∈ bad, (shiftedNonunitCount v (A u) : ℝ) *
      ((h : ℝ) * d) ^ 2) ≤ B * s * v := by
  have hweight0 : 0 ≤ ((h : ℝ) * d) ^ 2 := sq_nonneg _
  have hweight : ((h : ℝ) * d) ^ 2 ≤ (h : ℝ) ^ 2 := by
    have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
    have hmul : (h : ℝ) * d ≤ (h : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hd1 hh0
    simpa using pow_le_pow_left₀ (mul_nonneg hh0 hd0) hmul 2
  calc
    (∑ u ∈ bad, (shiftedNonunitCount v (A u) : ℝ) *
        ((h : ℝ) * d) ^ 2) ≤
        ∑ _u ∈ bad, (v : ℝ) * (h : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul
        (by exact_mod_cast shiftedNonunitCount_le_modulus hv (A u))
        hweight hweight0 (Nat.cast_nonneg _)
    _ = (v : ℝ) * ((bad.card : ℝ) * (h : ℝ) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ (v : ℝ) * (B * s) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = B * s * v := by ring

lemma good_residue_sum_le {s v h : ℕ} [NeZero s] (hv : 0 < v)
    (vsquare : Squarefree v) (hlarge : ∀ p ∈ v.primeFactors, h < p)
    (good : Finset (ZMod s))
    (hgood : ∀ u ∈ good, (h : ℝ) * density s / 2 ≤
      (survivingShifts s h u).card) :
    (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
      ((h : ℝ) * (density s * density v)) ^ 2) ≤ 8 * s * v := by
  calc
    (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * (density s * density v)) ^ 2) ≤
        ∑ _u ∈ good, (8 : ℝ) * v := by
      apply Finset.sum_le_sum
      intro u hu
      exact largePrime_good_residue_le (s := s) (survivingShifts s h u)
        (survivingShifts_subset s h u) hv vsquare hlarge (hgood u hu)
    _ = (good.card : ℝ) * ((8 : ℝ) * v) := by simp
    _ ≤ (s : ℝ) * ((8 : ℝ) * v) := by
      gcongr
      exact_mod_cast (Finset.card_le_univ good).trans_eq (by simp)
    _ = 8 * s * v := by ring

/-- The complete smooth--rough assembly for a squarefree modulus, assuming
only the lower-tail consequence of the small-prime moment estimate. -/
theorem squarefree_emptyWindows_bound_of_lowerTail {B : ℝ} (hB0 : 0 ≤ B)
    (hLower : ∀ {s h : ℕ}, 0 < s → Squarefree s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card : ℝ) * h ^ 2 ≤
          B * s)
    {r h : ℕ} (hr : 0 < r) (hrsq : Squarefree r) (hh : 1 ≤ h) :
    ((emptyWindows r h).card : ℝ) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2 ≤
      (B + 8) * (r : ℝ) ^ 3 := by
  classical
  let s := smoothPart r h
  let v := roughPart r h
  have hs : 0 < s := by simpa only [s] using smoothPart_pos r h
  have hv : 0 < v := by simpa only [v] using roughPart_pos r h
  letI : NeZero s := ⟨hs.ne'⟩
  letI : NeZero v := ⟨hv.ne'⟩
  have hsquare : Squarefree s := by
    simpa only [s] using squarefree_smoothPart (h := h) hrsq
  have vsquare : Squarefree v := by
    simpa only [v] using squarefree_roughPart (h := h) hrsq
  have hcop : s.Coprime v := by
    simpa only [s, v] using smoothPart_coprime_roughPart (h := h) hrsq
  have hrprod : s * v = r := by
    simpa only [s, v] using smoothPart_mul_roughPart (h := h) hrsq
  have hsmooth : ∀ p ∈ s.primeFactors, p ≤ h := by
    intro p hp
    simpa only [s] using smoothPart_prime_le (h := h) hp
  have hlarge : ∀ p ∈ v.primeFactors, h < p := by
    intro p hp
    simpa only [v] using roughPart_prime_gt (h := h) hp
  have hdensity : density r = density s * density v := by
    simpa only [s, v] using density_smoothPart_mul_roughPart (h := h) hrsq
  let bad : Finset (ZMod s) := Finset.univ.filter fun u ↦
    (unitCount s h u.val : ℝ) < (h : ℝ) * density s / 2
  let good : Finset (ZMod s) := Finset.univ.filter fun u ↦ u ∉ bad
  have hbadCard : bad.card =
      ((Finset.range s).filter fun u ↦
        (unitCount s h u : ℝ) < (h : ℝ) * density s / 2).card := by
    dsimp only [bad]
    exact card_filter_zmod_val_eq_range (s := s)
      (fun u : ℕ ↦ (unitCount s h u : ℝ) < (h : ℝ) * density s / 2)
  have htail : (bad.card : ℝ) * (h : ℝ) ^ 2 ≤ B * s := by
    rw [hbadCard]
    exact hLower hs hsquare hh hsmooth
  have hbadSum := bad_residue_sum_le hv (density_pos hr).le
    (density_le_one r) bad (fun u ↦ survivingShifts s h u) htail
  have hgoodPoint : ∀ u ∈ good, (h : ℝ) * density s / 2 ≤
      (survivingShifts s h u).card := by
    intro u hu
    have hubad : u ∉ bad := (Finset.mem_filter.mp hu).2
    rw [card_survivingShifts_eq_unitCount]
    exact le_of_not_gt (by
      simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hubad)
  have hgoodSum := good_residue_sum_le hv vsquare hlarge good hgoodPoint
  have hgoodSum' :
      (∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * density r) ^ 2) ≤ 8 * s * v := by
    simpa only [hdensity] using hgoodSum
  have hcount : (emptyWindows r h).card =
      ∑ u : ZMod s, shiftedNonunitCount v (survivingShifts s h u) := by
    rw [← hrprod]
    exact card_emptyWindows_mul_eq_sum hs hv hcop h
  have hsplit :
      (∑ u : ZMod s,
        (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2) =
      (∑ u ∈ bad, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2) +
      ∑ u ∈ good, (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
          ((h : ℝ) * density r) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (ZMod s)))
      (p := fun u ↦ u ∈ bad)
      (f := fun u ↦ (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
        ((h : ℝ) * density r) ^ 2)]
    have hfilterBad : (Finset.univ : Finset (ZMod s)).filter
        (fun u ↦ u ∈ bad) = bad := by ext u; simp
    rw [hfilterBad]
  have hprob : ((emptyWindows r h).card : ℝ) *
      ((h : ℝ) * density r) ^ 2 ≤ (B + 8) * r := by
    calc
      ((emptyWindows r h).card : ℝ) * ((h : ℝ) * density r) ^ 2 =
          (∑ u : ZMod s,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ)) *
              ((h : ℝ) * density r) ^ 2 := by
        simp only [hcount, Nat.cast_sum]
      _ = ∑ u : ZMod s,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2 := by rw [Finset.sum_mul]
      _ = (∑ u ∈ bad,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2) +
          ∑ u ∈ good,
            (shiftedNonunitCount v (survivingShifts s h u) : ℝ) *
              ((h : ℝ) * density r) ^ 2 := hsplit
      _ ≤ B * s * v + 8 * s * v := add_le_add hbadSum hgoodSum'
      _ = (B + 8) * r := by rw [← hrprod]; push_cast; ring
  have hscaled := mul_le_mul_of_nonneg_right hprob (sq_nonneg (r : ℝ))
  calc
    ((emptyWindows r h).card : ℝ) * (h : ℝ) ^ 2 * (r.totient : ℝ) ^ 2 =
        (((emptyWindows r h).card : ℝ) *
          ((h : ℝ) * density r) ^ 2) * (r : ℝ) ^ 2 := by
      rw [density]
      field_simp
    _ ≤ ((B + 8) * (r : ℝ)) * (r : ℝ) ^ 2 := hscaled
    _ = (B + 8) * (r : ℝ) ^ 3 := by ring

/-- The small-prime sixth-moment estimate, together with the finite
smooth--rough argument above, gives the desired empty-window estimate for
every positive modulus. -/
theorem exists_emptyWindows_bound_of_sixthMomentBound {A : ℝ}
    (hA : SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 := by
  obtain ⟨C, hC, hLower⟩ := smallPrime_lowerTail_of_sixthMomentBound hA
  refine ⟨C + 8, by positivity, ?_⟩
  intro n h hn hh
  apply emptyWindows_bound_of_kernel hn
  exact squarefree_emptyWindows_bound_of_lowerTail hC.le hLower
    (squarefreeKernel_pos hn) (squarefree_squarefreeKernel n) hh

theorem exists_emptyWindows_bound_of_exists_sixthMomentBound
    (hMoment : ∃ A : ℝ, SmallPrimeSixthMomentBound A) :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 := by
  obtain ⟨A, hA⟩ := hMoment
  exact exists_emptyWindows_bound_of_sixthMomentBound hA

/-- The unconditional uniform empty-window estimate used in the gap
deduction. -/
theorem exists_emptyWindows_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ {n h : ℕ}, 0 < n → 1 ≤ h →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 * (n.totient : ℝ) ^ 2 ≤
        B * (n : ℝ) ^ 3 :=
  exists_emptyWindows_bound_of_exists_sixthMomentBound
    exists_smallPrimeSixthMomentBound

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos220.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 220.
https://www.erdosproblems.com/forum/thread/220

Informal authors:
- Hugh Montgomery
- Robert Vaughan

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos220.md
-/

/-!
# Erdős Problem 220

Montgomery and Vaughan proved that the sum of the squares of consecutive
gaps between the positive reduced residues modulo `n` is bounded by an
absolute constant times `n² / φ(n)`.  The list `sortedTotatives n` is the
literal increasing list from the problem statement.  At `n = 1` this list is
empty (whereas `Nat.totient 1 = 1`), so its adjacent-gap sum is correctly
interpreted as the empty sum.
-/

open scoped BigOperators

/-- The affirmative resolution of Erdős Problem 220, with `≪` expressed by
one positive real constant independent of the modulus. -/
theorem erdos_220 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤
        C * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  obtain ⟨B, hB, hEmpty⟩ := exists_emptyWindows_bound
  refine ⟨5 + 2 * B, by positivity, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    simpa using (show (0 : ℝ) ≤ 5 + 2 * B by positivity)
  · have hn2 : 2 ≤ n := by omega
    rw [cast_sumSquaredGaps_sortedTotatives hn2]
    exact gapSquareSum_le_of_emptyWindows_bound n (by omega) B hB.le
      (fun h hh hhn ↦ hEmpty (by omega) hh)

end

#print axioms erdos_220
-- 'Erdos220.erdos_220' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos220
