/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdős Problem 178: Balancing Families of Integer Sequences

We prove that given any infinite collection of infinite strictly increasing sequences of
natural numbers, there exists a coloring `f : ℕ → {-1, 1}` such that for each `d`, the
partial sums `|∑ j in range m, f (a i j)|` are uniformly bounded over all `m` and `i < d`.

This answers a question of Erdős in the affirmative, following J. Beck's solution in
"Balancing Families of Integer Sequences" (Combinatorica, 1981).

## Proof outline

The proof has two main components:

1. **Diagonal extraction** (compactness): From a sequence of ±1-valued functions,
   extract a pointwise limit using a free ultrafilter.

2. **Beck's finite balancing theorem** (Theorem 1 of Beck 1981): For any finite number
   of sequences, construct ±1 signs with uniformly bounded partial sums. This uses:
   - **Lemma 1** (pigeonhole): Among sufficiently many integral vectors of bounded norm,
     one can find a non-empty signed subset summing to zero.
   - A hierarchical blocking construction (Lemma 2) where at each level, more rows of
     the incidence matrix are zeroed out by grouping columns into signed blocks.
     The key property is that multiplying a "super-column" whose contribution is already
     zero by ±1 does not disturb the previously zeroed rows (since 0 × ±1 = 0).
   - The bound B(k) for the k-th row is the product of the first k+1 block-size
     parameters, which depends only on k (not on the sequences or the number of rows).
-/
import Mathlib

namespace Erdos178

open Finset BigOperators

/-! ## Part 1: Diagonal Extraction -/

/-- From a sequence of ±1-valued functions, one can find a single ±1-valued function
that agrees with infinitely many of the original functions on any given finite set.
This uses a free ultrafilter on ℕ. -/
lemma diagonal_extraction (g : ℕ → ℕ → ℤ)
    (hg : ∀ d n, g d n = 1 ∨ g d n = -1) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ (S : Finset ℕ) (d₀ : ℕ),
        ∃ d, d₀ ≤ d ∧ ∀ s ∈ S, g d s = f s := by
  set U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      (∀ n, ∀ᶠ d in U, g d n = f n) := by
    have h_const :
        ∀ n, (∀ᶠ d in U, g d n = 1) ∨
          (∀ᶠ d in U, g d n = -1) := by
      intro n
      by_contra! h
      exact absurd (h.1.and h.2) fun h' => by
        obtain ⟨x, hx₁, hx₂⟩ := h'.exists
        specialize hg x n; aesop
    choose f hf using fun n =>
      show ∃ x : ℤ, (∀ᶠ d in U, g d n = x) ∧
          (x = 1 ∨ x = -1) from by
        cases' h_const n with h h
        · exact ⟨1, h, Or.inl rfl⟩
        · exact ⟨-1, h, Or.inr rfl⟩
    exact ⟨f, fun n => (hf n).2, fun n => (hf n).1⟩
  have h_prop : ∀ S : Finset ℕ, ∀ d₀ : ℕ,
      (∀ᶠ d in U, d₀ ≤ d ∧ ∀ s ∈ S, g d s = f s) := by
    intro S d₀
    have := hf.2
    simp_all +decide
    exact Ultrafilter.of_le _
      (Filter.eventually_atTop.mpr ⟨d₀, fun x hx => hx⟩)
  exact ⟨f, hf.1, fun S d₀ =>
    (h_prop S d₀).exists.imp fun d hd => ⟨hd.1, hd.2⟩⟩

/-! ## Part 2: Signed Subset Sum Lemma (Beck's Lemma 1) -/

private lemma pm_one_mul_pm_one {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-
**Beck's Lemma 1 (1-dimensional):** Among `T` integers with absolute value at most
`M`, if `2^T > 2TM + 1`, there exists a non-empty signed subset summing to zero.
-/
lemma signed_zero_sum {T : ℕ} {M : ℕ}
    (hT : 2 * T * M + 1 < 2 ^ T)
    (a : Fin T → ℤ) (ha : ∀ i, |a i| ≤ (M : ℤ)) :
    ∃ (H : Finset (Fin T)) (δ : Fin T → ℤ),
      H.Nonempty ∧ (∀ i ∈ H, δ i = 1 ∨ δ i = -1) ∧
      ∑ i ∈ H, δ i * a i = 0 := by
  -- Step 1: Pigeonhole — find distinct subsets with equal sums
  obtain ⟨I, J, hIJ⟩ : ∃ I J : Finset (Fin T),
      I ≠ J ∧ (∑ i ∈ I, a i) = (∑ i ∈ J, a i) := by
    by_contra! h
    have h_sums :
        image (fun I : Finset (Fin T) => ∑ i ∈ I, a i)
          (powerset (univ : Finset (Fin T))) ⊆
        Icc (-T * M : ℤ) (T * M) := by
      apply image_subset_iff.mpr
      intro I _
      refine mem_Icc.mpr ⟨?_, ?_⟩
      · exact le_trans
          (by norm_num
              nlinarith [show I.card ≤ T from
                le_trans (card_le_univ _) (by norm_num)])
          (sum_le_sum fun i _ => neg_le_of_abs_le (ha i))
      · exact le_trans
          (sum_le_sum fun i _ => le_of_abs_le (ha i))
          (by norm_num
              nlinarith [show I.card ≤ T from
                le_trans (card_le_univ _) (by norm_num)])
    exact absurd (card_le_card h_sums) (by
      rw [card_image_of_injective _ fun I J hij =>
        not_imp_not.mp (h I J) hij]
      norm_num; nlinarith)
  -- Step 2: Build the signed subset from I Δ J
  set H := (I \ J) ∪ (J \ I) with hH_def
  refine ⟨H, fun i =>
    if i ∈ I then if i ∈ J then 0 else 1
    else if i ∈ J then -1 else 0, ?_, ?_, ?_⟩ <;>
    simp_all +decide [sum_ite]
  · -- H nonempty
    by_contra h
    simp only [not_or, not_nonempty_iff_eq_empty] at h
    exact hIJ.1 (Subset.antisymm
      (sdiff_eq_empty_iff_subset.mp h.1)
      (sdiff_eq_empty_iff_subset.mp h.2))
  · -- δ is ±1 on H
    intro i hi
    rcases hi with ⟨hiI, hiJ⟩ | ⟨hiJ, hiI⟩ <;> simp [hiI, hiJ]
  · -- Signed sum is zero
    simp_all +decide [Finset.sum_filter]
    rw [show (I \ J ∪ J \ I) ∩ I = I \ J by ext; aesop,
      show {x ∈ I \ J ∪ J \ I | x ∉ I} ∩ J = J \ I by
        ext; aesop]
    simp_all +decide [Finset.sum_ite]
    rw [Finset.filter_true_of_mem fun x hx =>
      Finset.mem_sdiff.mp hx |>.2]
    have hI_split : ∑ i ∈ I, a i =
        ∑ i ∈ I \ J, a i + ∑ i ∈ I ∩ J, a i := by
      rw [← Finset.sum_union
        (Finset.disjoint_right.mpr fun x hx => by aesop)]
      congr; ext x; by_cases hx : x ∈ J <;> aesop
    have hJ_split : ∑ i ∈ J, a i =
        ∑ i ∈ J \ I, a i + ∑ i ∈ I ∩ J, a i := by
      rw [← Finset.sum_union
        (Finset.disjoint_right.mpr fun x hx => by aesop)]
      congr; ext x; by_cases hx : x ∈ I <;> aesop
    linarith [hI_split, hJ_split]

/-- For any `M`, there exists a threshold `T` satisfying
the pigeonhole condition. -/
lemma exists_pigeonhole_threshold (M : ℕ) :
    ∃ T : ℕ, 0 < T ∧ 2 * T * M + 1 < 2 ^ T := by
  use 2 * M + 2
  induction' M with M ih <;>
    norm_num [Nat.pow_succ', Nat.pow_mul] at *
  cases M <;> norm_num at *
  nlinarith

/-! ## Part 3: Beck's Finite Balancing Theorem -/

/-- The pigeonhole threshold: given bound `M`, choose `T > 0`
with `2^T > 2TM + 1`. -/
noncomputable def Q (M : ℕ) : ℕ :=
  (exists_pigeonhole_threshold M).choose

lemma Q_pos (M : ℕ) : 0 < Q M :=
  (exists_pigeonhole_threshold M).choose_spec.1

lemma Q_spec (M : ℕ) : 2 * Q M * M + 1 < 2 ^ Q M :=
  (exists_pigeonhole_threshold M).choose_spec.2

/-- Product of block-size parameters:
`t_prod 0 = 1`, `t_prod (n+1) = t_prod n * Q(t_prod n)`. -/
noncomputable def t_prod : ℕ → ℕ
  | 0 => 1
  | n + 1 => t_prod n * Q (t_prod n)

lemma t_prod_pos : ∀ n, 0 < t_prod n := by
  intro n; induction n with
  | zero => simp [t_prod]
  | succ n ih => simp [t_prod]; exact ⟨ih, Q_pos _⟩

/-- The bound for the k-th sequence:
`beck_bound k = t_prod(k+1) - 1`. -/
noncomputable def beck_bound (k : ℕ) : ℕ :=
  t_prod (k + 1) - 1

/-! ### Generalized t_prod (G_func) -/

/-- Generalized product of block-size parameters.
`G_func M 0 = M`, `G_func M (n+1) = G_func M n * Q(G_func M n)`.
Satisfies `G_func 1 n = t_prod n`. -/
noncomputable def G_func (M : ℕ) : ℕ → ℕ
  | 0 => M
  | n + 1 => G_func M n * Q (G_func M n)

@[simp]
lemma G_func_zero (M : ℕ) : G_func M 0 = M := rfl

@[simp]
lemma G_func_succ (M n : ℕ) :
    G_func M (n + 1) = G_func M n * Q (G_func M n) := rfl

lemma G_func_one_eq_t_prod : ∀ n, G_func 1 n = t_prod n := by
  intro n; induction n with
  | zero => simp [t_prod]
  | succ n ih => simp [t_prod, ih]

lemma G_func_ge_base (M : ℕ) :
    ∀ n, M ≤ G_func M n := by
  intro n
  induction' n with n ih
  · rfl
  · exact le_trans ih (Nat.le_mul_of_pos_right _ (Q_pos _))

lemma G_func_shift (M : ℕ) :
    ∀ n, G_func (G_func M 1) n = G_func M (n + 1) := by
  intro n
  induction n <;> simp_all +decide [G_func]

/-! ### Buffer decomposition (Beck's Lemma 2, one level) -/

set_option maxHeartbeats 400000 in
/-- **Buffer decomposition.** Given `N` elements with integer values bounded
by `M`, partition `{0,...,N-1}` into K-sets (signed zero-sum subsets) such that
at any prefix, the "physical buffer" (uncovered elements) has fewer than `Q(M)`
elements.

This is proved by induction on `N`: process elements one at a time, maintaining
a buffer. When the buffer reaches size `Q(M)`, extract a K-set using
`signed_zero_sum`. -/
lemma buffer_decomp (N M : ℕ) (hM : 0 < M)
    (val : ℕ → ℤ) (hval : ∀ n, |val n| ≤ (M : ℤ)) :
    ∃ (s : ℕ) (kset : ℕ → Finset ℕ) (delta : ℕ → ℤ),
      s ≤ N ∧
      (∀ l, l < s → kset l ⊆ range N) ∧
      (∀ l, l < s → (kset l).Nonempty) ∧
      (∀ l₁ l₂, l₁ < s → l₂ < s → l₁ ≠ l₂ →
        Disjoint (kset l₁) (kset l₂)) ∧
      (∀ l n, l < s → n ∈ kset l →
        delta n = 1 ∨ delta n = -1) ∧
      (∀ l, l < s → ∑ n ∈ kset l, delta n * val n = 0) ∧
      (∀ l, l < s → (kset l).card ≤ Q M) ∧
      (∀ m, m ≤ N → ∃ p, p ≤ s ∧
        (∀ l, l < p → kset l ⊆ range m) ∧
        (range m \
          ((range p).biUnion kset)).card < Q M) := by
  induction' N with N ih M hM val hval
  · exact ⟨0, fun _ => ∅, fun _ => 1,
      by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num,
      by norm_num; linarith [Q_pos M]⟩
  · obtain ⟨s, kset, delta, hs, hkset, hkset', hkset'',
      hdelta, hdelta', hdelta'', hdelta'''⟩ := ih
    set allK := (range s).biUnion kset
    set buf := range N \ allK
    set buf' := insert N buf
    have hbuf'_card : buf'.card ≤ Q M := by
      have hbuf_card : buf.card < Q M := by
        obtain ⟨p, hp₁, hp₂, hp₃⟩ := hdelta''' N le_rfl
        exact lt_of_le_of_lt (card_le_card (by grind)) hp₃
      grind
    by_cases hbuf'_card_eq : buf'.card = Q M
    · -- Buffer full: extract a K-set
      obtain ⟨H, δ, hH_nonempty, hδ⟩ :
          ∃ H : Finset ℕ, ∃ δ : ℕ → ℤ,
            H ⊆ buf' ∧ H.Nonempty ∧
            (∀ n ∈ H, δ n = 1 ∨ δ n = -1) ∧
            (∑ n ∈ H, δ n * val n = 0) ∧
            H.card ≤ Q M := by
        have h_szs :
            ∃ H : Finset (Fin buf'.card),
              ∃ δ : Fin buf'.card → ℤ,
                H.Nonempty ∧
                (∀ i ∈ H, δ i = 1 ∨ δ i = -1) ∧
                (∑ i ∈ H,
                  δ i * val (buf'.orderEmbOfFin rfl i)) =
                0 := by
          exact signed_zero_sum
            (hbuf'_card_eq.symm ▸ Q_spec M)
            (fun i => val (buf'.orderEmbOfFin rfl i))
            (fun i => hval _)
        obtain ⟨H, δ, hH₁, hH₂, hH₃⟩ := h_szs
        refine ⟨image (fun i => buf'.orderEmbOfFin rfl i) H,
          fun n =>
            if hn : n ∈ image
                (fun i => buf'.orderEmbOfFin rfl i) H
            then δ (Classical.choose (mem_image.mp hn))
            else 1,
          ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp_all +decide [subset_iff]
        · intro n x hx hn
          have := Classical.choose_spec (mem_image.mp
            (show buf'.orderEmbOfFin rfl x ∈
                image (fun i => buf'.orderEmbOfFin rfl i) H
              from mem_image_of_mem _ hx))
          aesop
        · convert hH₃ using 2
          grind +revert
        · exact le_trans card_image_le
            (by simpa [hbuf'_card_eq] using card_le_univ H)
      refine ⟨s + 1,
        fun l => if l < s then kset l
          else if l = s then H else ∅,
        fun n => if n ∈ H then δ n else delta n,
        ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp_all +decide [subset_iff]
      · grind
      · grind
      · intro l₁ l₂ hl₁ hl₂ hne
        split_ifs <;> simp_all +decide [disjoint_left]
        · exact hkset'' _ _ ‹_› ‹_› hne
        · grind
        · grind
      · refine ⟨?_, ?_, ?_, ?_⟩
        · grind
        · intro l hl
          split_ifs <;> simp_all +decide [sum_ite]
          rw [sum_filter, sum_filter, ← sum_add_distrib]
          exact Eq.trans
            (sum_congr rfl fun x hx => by grind)
            (hdelta' l ‹_›)
        · grind
        · intro m hm
          by_cases hm' : m ≤ N
          · obtain ⟨p, hp₁, hp₂, hp₃⟩ := hdelta''' m hm'
            refine ⟨p, Nat.le_succ_of_le hp₁, ?_, ?_⟩
            · grind
            · exact lt_of_le_of_lt
                (card_mono (by
                  simp +contextual [subset_iff]
                  grind))
                hp₃
          · refine ⟨s + 1, ?_, ?_, ?_⟩ <;>
              simp_all +decide
            · grind
            · rw [show m = N + 1 by linarith]
              rw [show (range (s + 1)).biUnion
                    (fun l => if l < s then kset l
                      else if l = s then H else ∅) =
                  allK ∪ H from ?_]
              · rw [show range (N + 1) \ (allK ∪ H) =
                    buf' \ H from ?_]
                · grind
                · grind
              · ext
                simp [mem_biUnion, mem_range]
                constructor
                · grind
                · rintro (h | h)
                  · rw [mem_biUnion] at h
                    obtain ⟨l, hl, hl'⟩ := h
                    exact ⟨l,
                      by linarith [mem_range.mp hl],
                      by aesop⟩
                  · exact ⟨s, le_rfl, by aesop⟩
    · -- Buffer not full: pass through
      refine ⟨s, kset, delta, ?_, ?_, ?_, ?_, ?_⟩ <;>
        try linarith
      · exact fun l hl =>
          Subset.trans (hkset l hl)
            (range_mono (Nat.le_succ _))
      · assumption
      · exact hkset''
      · refine ⟨hdelta, hdelta', hdelta'',
          fun m hm => ?_⟩
        cases hm <;> simp_all +decide
        refine ⟨s, le_rfl,
          fun l hl => Subset.trans (hkset l hl)
            (range_mono (by omega)), ?_⟩
        grind

/-! ### Generalized matrix balancing (Beck's construction) -/

set_option maxHeartbeats 800000 in
/-- **Generalized matrix balancing.** For `r` rows and `N` columns with values
bounded by `M`, there exists a ±1 signing whose weighted prefix sums along each
row `k` are bounded by `G_func M (k+1) - M`.

This is the core of Beck's hierarchical construction, proved by induction on `r`.
At each level, the buffer construction (using `signed_zero_sum`) groups columns
into K-sets that zero out the current row's contribution. The K-set level matrix
has values bounded by `Q(M) * M`, and the inductive hypothesis bounds the
remaining rows. The bound `G_func M (k+1) - M` telescopes correctly. -/
lemma beck_matrix (r N M : ℕ) (hM : 0 < M)
    (V : ℕ → ℕ → ℤ) (hV : ∀ k n, |V k n| ≤ (M : ℤ)) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ m k : ℕ, k < r → m ≤ N →
        |∑ n ∈ range m, f n * V k n| ≤
          ↑(G_func M (k + 1) - M) := by
  induction' r with r ih generalizing N M V
  · exact ⟨fun _ => 1, fun _ => Or.inl rfl,
      by intros; contradiction⟩
  · obtain ⟨s, kset, delta, hs_le_N, hkset_subset,
        hkset_nonempty, hkset_disjoint, hdelta,
        hdelta_sum, hkset_card, h_buffer⟩ :=
      buffer_decomp N M hM (V 0) (hV 0)
    set V' : ℕ → ℕ → ℤ := fun k l =>
      if l < s then ∑ n ∈ kset l, delta n * V (k + 1) n
      else 0
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℤ,
        (∀ n, g n = 1 ∨ g n = -1) ∧
        ∀ m k, k < r → m ≤ s →
          |∑ l ∈ range m, g l * V' k l| ≤
            G_func (Q M * M) (k + 1) - Q M * M := by
      have hV'_bound : ∀ k l, |V' k l| ≤ Q M * M := by
        simp +zetaDelta at *
        intro k l
        split_ifs <;> norm_num
        · exact le_trans (abs_sum_le_sum_abs _ _)
            (le_trans
              (sum_le_sum fun _ _ =>
                show |delta _ * V (k + 1) _| ≤ M by
                  rcases hdelta l _ ‹_› ‹_› with h | h <;>
                    rw [h] <;>
                    simpa [abs_mul] using hV (k + 1) _)
              (by norm_num
                  nlinarith [hkset_card l ‹_›]))
        · positivity
      specialize ih s (Q M * M)
        (mul_pos (Q_pos M) hM) V' (by aesop)
      convert ih using 6
      rw [Nat.cast_sub]
      · norm_num
      · exact G_func_ge_base _ _
    set f : ℕ → ℤ := fun n =>
      if h : ∃ l < s, n ∈ kset l
      then delta n * g (Classical.choose h) else 1
    refine ⟨f, ?_, ?_⟩
    · -- f is ±1
      intro n
      simp only [f]
      split
      · next h =>
          have hcs := Classical.choose_spec h
          exact pm_one_mul_pm_one
            (hdelta _ n hcs.1 hcs.2)
            (hg.1 (Classical.choose h))
      · exact Or.inl rfl
    · intro m k hk hm
      by_cases hk0 : k = 0
      · -- Row 0: K-set sums vanish, buffer bounded
        obtain ⟨p, hp₁, hp₂, hp₃⟩ := h_buffer m hm
        have h_buffer_sum :
            |∑ n ∈ range m \ (range p).biUnion kset,
              f n * V 0 n| ≤
            (range m \ (range p).biUnion kset).card *
              M := by
          have h_each :
              ∀ n ∈ range m \ (range p).biUnion kset,
                |f n * V 0 n| ≤ M := by
            simp +zetaDelta at *
            intro n hn hn'
            split_ifs <;> simp_all +decide [abs_mul]
            cases hdelta _ _
              (Classical.choose_spec
                ‹∃ l < s, n ∈ kset l› |>.1)
              (Classical.choose_spec
                ‹∃ l < s, n ∈ kset l› |>.2) <;>
              cases hg.1
                (Classical.choose
                  ‹∃ l < s, n ∈ kset l›) <;>
              simp +decide [*]
          exact le_trans (abs_sum_le_sum_abs _ _)
            (le_trans (sum_le_sum h_each) (by norm_num))
        have h_Kset_sum :
            ∑ n ∈ (range p).biUnion kset,
              f n * V 0 n = 0 := by
          rw [sum_biUnion]
          · exact sum_eq_zero fun l hl => by
              convert congr_arg (g l * ·)
                (hdelta_sum l
                  (by linarith [mem_range.mp hl])) using 1
              · rw [mul_sum _ _ _]
                exact sum_congr rfl fun n hn => by
                  simp +zetaDelta at *
                  split_ifs with h
                  · have := Classical.choose_spec h
                    rw [show Classical.choose h = l from
                      Classical.not_not.1 fun h' =>
                        disjoint_left.mp
                          (hkset_disjoint _ _
                            this.1 (by linarith) h')
                          this.2 hn]
                    ring
                  · exact False.elim <|
                      h ⟨l, by linarith, hn⟩
              · ring
          · exact fun l hl l' hl' hll' =>
              hkset_disjoint l l'
                (by linarith [mem_range.mp hl])
                (by linarith [mem_range.mp hl'])
                hll'
        have h_combined :
            |∑ n ∈ range m, f n * V 0 n| ≤
            (range m \
              (range p).biUnion kset).card * M := by
          rw [← sum_sdiff
            (show (range p).biUnion kset ⊆ range m from
              biUnion_subset.mpr fun l hl =>
                hp₂ l (mem_range.mp hl))]
          aesop
        simp_all +decide [G_func]
        exact h_combined.trans (by
          rw [Nat.cast_sub (by nlinarith [Q_pos M])]
          push_cast; nlinarith)
      · -- Row k > 0: split into K-set + buffer
        obtain ⟨p, hp_le_s, hp_subset, hp_buffer⟩ :=
          h_buffer m hm
        have h_split_sum :
            ∑ n ∈ range m, f n * V k n =
            ∑ l ∈ range p, g l * V' (k - 1) l +
            ∑ n ∈ range m \ (range p).biUnion kset,
              f n * V k n := by
          have h_step :
              ∑ n ∈ range m, f n * V k n =
              ∑ n ∈ (range p).biUnion kset,
                f n * V k n +
              ∑ n ∈ range m \
                  (range p).biUnion kset,
                f n * V k n := by
            rw [add_comm, sum_sdiff <|
              biUnion_subset.mpr fun l hl =>
                hp_subset l <| mem_range.mp hl]
          rw [h_step, sum_biUnion]
          · refine congrArg₂ (· + ·)
              (sum_congr rfl fun l hl => ?_) rfl
            rw [sum_congr rfl fun n hn => by
              rw [show f n = delta n * g l from by
                simp +zetaDelta at *
                split_ifs with h
                · have := Classical.choose_spec h
                  exact congr_arg _
                    (congr_arg _
                      (Classical.not_not.1 fun h' =>
                        disjoint_left.mp
                          (hkset_disjoint _ _
                            this.1 (by linarith) h')
                          this.2 hn))
                · exact False.elim <|
                    h ⟨l, by linarith, hn⟩]]
            simp +zetaDelta at *
            rw [if_pos (by linarith), mul_sum _ _ _]
            rw [Nat.sub_add_cancel
              (Nat.pos_of_ne_zero hk0)]
            exact sum_congr rfl fun _ _ => by ring
          · exact fun l hl l' hl' hll' =>
              hkset_disjoint l l'
                (by linarith [mem_range.mp hl])
                (by linarith [mem_range.mp hl'])
                hll'
        have h_buffer_sum :
            |∑ n ∈ range m \ (range p).biUnion kset,
              f n * V k n| ≤ (Q M - 1) * M := by
          refine le_trans (abs_sum_le_sum_abs _ _) ?_
          refine le_trans (sum_le_sum fun i hi =>
            show |f i * V k i| ≤ M from ?_) ?_
          · simp +zetaDelta at *
            split_ifs <;> simp_all +decide [abs_mul]
            have h_d : |delta i| ≤ 1 := by
              cases hdelta _ _
                (Classical.choose_spec
                  ‹∃ l < s, i ∈ kset l› |>.1)
                (Classical.choose_spec
                  ‹∃ l < s, i ∈ kset l› |>.2) <;>
                aesop
            have h_g :
                |g (Classical.choose
                  ‹∃ l < s, i ∈ kset l›)| ≤ 1 := by
              cases hg.1
                (Classical.choose
                  ‹∃ l < s, i ∈ kset l›) <;>
                aesop
            exact le_trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul h_d h_g
                  (by positivity) (by positivity))
                (by positivity))
              (by simpa using hV k i)
          · norm_num +zetaDelta at *
            exact mul_le_mul_of_nonneg_right
              (by linarith) (Nat.cast_nonneg _)
        have h_K_set_sum :
            |∑ l ∈ range p, g l * V' (k - 1) l| ≤
              G_func (Q M * M) k - Q M * M := by
          convert hg.2 p (k - 1)
            (Nat.lt_of_lt_of_le (Nat.pred_lt hk0)
              (Nat.le_of_lt_succ hk))
            hp_le_s using 1
          cases k <;> trivial
        rw [Nat.cast_sub]
        · rw [h_split_sum, abs_le]
          constructor <;>
            rw [show G_func M (k + 1) =
                G_func (Q M * M) k from ?_]
          · linarith [abs_le.mp h_K_set_sum,
              abs_le.mp h_buffer_sum]
          · rw [mul_comm]
            exact G_func_shift M k ▸ rfl
          · linarith [abs_le.mp h_K_set_sum,
              abs_le.mp h_buffer_sum]
          · rw [mul_comm]
            exact G_func_shift M k ▸ rfl
        · exact G_func_ge_base M _

/-! ### Deriving beck_finite_version from beck_matrix -/

/-- **Beck's Theorem 1 (Finite version).** For any `r` strictly increasing
sequences and any prefix length `N`, there exists a ±1 signing whose partial
sums along each sequence `k < r` are bounded by `beck_bound k` for all
prefix lengths `m ≤ N`.

Derived from `beck_matrix` by defining the incidence matrix `V(k,n) = 1`
if `n` appears in the first `N` elements of sequence `a k`, else `0`. -/
lemma beck_finite_version (r N : ℕ) (a : ℕ → ℕ → ℕ)
    (ha : ∀ i, StrictMono (a i)) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ m k : ℕ, k < r → m ≤ N →
        |∑ j ∈ range m, f (a k j)| ≤
          ↑(beck_bound k) := by
  unfold beck_bound
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ,
      (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ m k : ℕ, k < r →
        m ≤ (range r).sup (fun k => a k (N - 1)) + 1 →
        |∑ n ∈ range m,
            f n * (if ∃ j < N, n = a k j
              then 1 else 0)| ≤
          ↑(t_prod (k + 1) - 1) := by
    have := @beck_matrix
    convert this r
      ((range r).sup (fun k => a k (N - 1)) + 1)
      1 zero_lt_one
      (fun k n => if ∃ j < N, n = a k j then 1 else 0)
      (fun k n => ?_) using 1
    · rw [show G_func 1 = t_prod from
        funext fun n => G_func_one_eq_t_prod n]
    · aesop
  refine ⟨f, hf.1, fun m k hk hm => ?_⟩
  by_cases hm' : m = 0 <;> simp_all +decide [sum_ite]
  convert hf.2 (a k (m - 1) + 1) k hk _ using 1
  · refine congr_arg _
      (sum_bij (fun x hx => a k x) ?_ ?_ ?_ ?_) <;>
      simp_all +decide
    · exact fun i hi =>
        ⟨(ha k).monotone (Nat.le_pred_of_lt hi),
          i, lt_of_lt_of_le hi hm, rfl⟩
    · exact fun i _ j _ hij => (ha k).injective hij
    · exact fun b hb x hx _ =>
        ⟨x, Nat.lt_of_not_ge fun hx'' => by
          linarith [(ha k).monotone (Nat.sub_le m 1),
            ha k <| Nat.lt_of_lt_of_le
              (Nat.sub_lt (Nat.pos_of_ne_zero hm')
                zero_lt_one)
              hx''],
          rfl⟩
  · exact Nat.succ_le_succ
      (((ha k).monotone (Nat.sub_le_sub_right hm 1)).trans
        (le_sup (f := fun k => a k (N - 1))
          (mem_range.mpr hk)))

/-- **Beck's Finite Balancing Theorem (Theorem 1 of Beck 1981):** There exists
a universal bound function `B` such that for any `r` infinite strictly increasing
sequences of natural numbers, one can find ±1 signs whose partial sums are
bounded by `B k` for the `k`-th sequence.

This follows from `beck_finite_version` (the finite case) combined with
`diagonal_extraction` (compactness of the space of ±1 signings). -/
lemma beck_finite_balancing :
    ∃ B : ℕ → ℕ, ∀ (r : ℕ) (a : ℕ → ℕ → ℕ),
      (∀ i, StrictMono (a i)) →
      ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
        ∀ m k : ℕ, k < r →
          |∑ j ∈ range m, f (a k j)| ≤ ↑(B k) := by
  use beck_bound
  intro r a ha
  choose g hg using fun N => beck_finite_version r N a ha
  obtain ⟨f, hf_pm, hf_agree⟩ :=
    diagonal_extraction g (fun N n => (hg N).1 n)
  refine ⟨f, hf_pm, fun m k hk => ?_⟩
  obtain ⟨N, hN, hagree⟩ :=
    hf_agree ((range m).image (a k)) m
  have hsum : ∑ j ∈ range m, f (a k j) =
      ∑ j ∈ range m, g N (a k j) :=
    sum_congr rfl fun j hj =>
      (hagree (a k j) (mem_image_of_mem _ hj)).symm
  rw [hsum]
  exact (hg N).2 m k hk hN

/-! ## Part 4: Main Theorem (Erdős Problem 178) -/

/-- **Erdős Problem 178** (solved by J. Beck, 1981): Given any infinite
collection of infinite strictly increasing sequences of natural numbers
`a i : ℕ → ℕ`, there exists a function `f : ℕ → {-1, 1}` such that for
each `d ≥ 1`:

  `max_{m, i < d} |∑_{j < m} f(a_i(j))| ≤ C_d`

for some constant `C_d` depending only on `d`. -/
theorem erdos_178 (a : ℕ → ℕ → ℕ)
    (ha : ∀ i, StrictMono (a i)) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ m i : ℕ, i < d →
        |∑ j ∈ range m, f (a i j)| ≤ ↑C := by
  obtain ⟨B, hB⟩ := beck_finite_balancing
  choose g hg using fun d => hB d a ha
  obtain ⟨f, hf_pm, hf_agree⟩ :=
    diagonal_extraction g (fun d n => (hg d).1 n)
  refine ⟨f, hf_pm, fun d =>
    ⟨(range d).sup B, fun m i hi => ?_⟩⟩
  obtain ⟨d', hd', hagree⟩ :=
    hf_agree ((range m).image (a i)) d
  have hsum : ∑ j ∈ range m, f (a i j) =
      ∑ j ∈ range m, g d' (a i j) :=
    sum_congr rfl fun j hj =>
      (hagree (a i j) (mem_image_of_mem _ hj)).symm
  rw [hsum]
  exact le_trans ((hg d').2 m i (by omega))
    (Nat.cast_le.mpr
      (le_sup (f := B) (mem_range.mpr hi)))

#print axioms erdos_178
-- 'Erdos178.erdos_178' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos178