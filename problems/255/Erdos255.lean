import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos255

/-
# Problem Description

Erdős Problem 255. Let `z₁, z₂, … ∈ [0,1]` be an infinite sequence and define the
discrepancy `D_N(I) = #{n ≤ N : zₙ ∈ I} - N |I|`. Must there exist an interval `I ⊆ [0,1]`
with `limsup_{N→∞} |D_N(I)| = ∞`? `erdos_255` proves that there must.

The answer is yes, by Schmidt, and what is proved here is Schmidt's stronger form: the
interval may be taken *anchored*, of the shape `[0,x)`. The conclusion supplies such an `x`
together with `Ico 0 x ⊆ Icc 0 1`, so the witness is visibly an interval inside `[0,1]`.

`anchoredDiscrepancy z N x` is `#{n < N : z n ∈ [0,x)} - N * x`, which is `D_N([0,x))`
since `|[0,x)| = x`. The interval convention is half-open throughout, and the statement
counts membership in `[0,x)` explicitly rather than hiding an endpoint convention behind an
abstraction. The limsup is taken in `EReal`, so `= ⊤` is the literal "`= ∞`".
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos255/Baire.lean` -/

section
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


open Filter Set TopologicalSpace
open scoped Topology

noncomputable section

namespace Erdos255Baire

def prefixCount (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℕ :=
  Nat.count (fun n ↦ z n < x) N

def discrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (prefixCount z N x : ℝ) - (N : ℝ) * x

def regularDomain (z : ℕ → ℝ) : Set ℝ :=
  Ioo 0 1 \ Set.range z

private lemma regularDomain_isGδ (z : ℕ → ℝ) : IsGδ (regularDomain z) := by
  change IsGδ (Ioo (0 : ℝ) 1 ∩ (Set.range z)ᶜ)
  exact isOpen_Ioo.isGδ.inter (Set.countable_range z).isGδ_compl

private lemma regularDomain_nonempty (z : ℕ → ℝ) : (regularDomain z).Nonempty := by
  have hd : Dense (Set.range z)ᶜ := (Set.countable_range z).dense_compl ℝ
  have ho : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hn : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num⟩
  obtain ⟨x, hx, hz⟩ := hd.inter_open_nonempty _ ho hn
  exact ⟨x, hx, hz⟩

private lemma threshold_continuous (z : ℕ → ℝ) (n : ℕ) :
    Continuous (fun x : regularDomain z ↦ if z n < (x : ℝ) then (1 : ℝ) else 0) := by
  let s : Set (regularDomain z) := {x | z n < (x : ℝ)}
  have hsopen : IsOpen s := by
    exact isOpen_Ioi.preimage continuous_subtype_val
  have hsclosed : IsClosed s := by
    have heq : sᶜ = {x : regularDomain z | (x : ℝ) < z n} := by
      ext x
      have hne : (x : ℝ) ≠ z n := by
        intro h
        exact x.property.2 ⟨n, h.symm⟩
      simp only [s, mem_compl_iff, mem_setOf_eq]
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.mp h) hne
      · exact fun h ↦ not_lt.mpr h.le
    have hcopen : IsOpen sᶜ := by
      rw [heq]
      exact isOpen_Iio.preimage continuous_subtype_val
    simpa only [compl_compl] using hcopen.isClosed_compl
  have hsclopen : IsClopen s := ⟨hsclosed, hsopen⟩
  apply Continuous.if
  · intro x hx
    rw [hsclopen.frontier_eq] at hx
    exact hx.elim
  · fun_prop
  · fun_prop

private lemma prefixCount_continuous (z : ℕ → ℝ) (N : ℕ) :
    Continuous (fun x : regularDomain z ↦ (prefixCount z N (x : ℝ) : ℝ)) := by
  induction N with
  | zero =>
      simpa [prefixCount] using
        (continuous_const : Continuous (fun _ : regularDomain z ↦ (0 : ℝ)))
  | succ N ih =>
      convert ih.add (threshold_continuous z N) using 1 <;>
        ext x <;> simp [prefixCount, Nat.count_succ]

private lemma discrepancy_continuous (z : ℕ → ℝ) (N : ℕ) :
    Continuous (fun x : regularDomain z ↦ discrepancy z N (x : ℝ)) := by
  exact (prefixCount_continuous z N).sub
    (continuous_const.mul continuous_subtype_val)

def boundedLayer (z : ℕ → ℝ) (m : ℕ) : Set (regularDomain z) :=
  {x | ∀ N, |discrepancy z N (x : ℝ)| ≤ m}

private lemma boundedLayer_closed (z : ℕ → ℝ) (m : ℕ) :
    IsClosed (boundedLayer z m) := by
  have hN : ∀ N : ℕ, IsClosed {x : regularDomain z |
      |discrepancy z N (x : ℝ)| ≤ m} := by
    intro N
    exact isClosed_Iic.preimage ((discrepancy_continuous z N).abs)
  have heq : boundedLayer z m = ⋂ N : ℕ,
      {x : regularDomain z | |discrepancy z N (x : ℝ)| ≤ m} := by
    ext x
    simp [boundedLayer]
  rw [heq]
  exact isClosed_iInter hN

private lemma threshold_continuousWithinAt_Iic (c x : ℝ) :
    ContinuousWithinAt (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) (Iic x) x := by
  by_cases hcx : c < x
  · have he : ∀ᶠ y in nhdsWithin x (Iic x), c < y :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcx)
    have heq : Filter.EventuallyEq (nhdsWithin x (Iic x))
        (fun _ : ℝ ↦ (1 : ℝ)) (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) := by
      filter_upwards [he] with y hy
      simp [hy]
    change Tendsto (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0)
      (nhdsWithin x (Iic x)) (nhds (if c < x then (1 : ℝ) else 0))
    rw [if_pos hcx]
    exact continuousWithinAt_const.congr' heq
  · have heq : Filter.EventuallyEq (nhdsWithin x (Iic x))
        (fun _ : ℝ ↦ (0 : ℝ)) (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hcy : ¬ c < y := fun h ↦ hcx (h.trans_le hy)
      simp [hcy]
    change Tendsto (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0)
      (nhdsWithin x (Iic x)) (nhds (if c < x then (1 : ℝ) else 0))
    rw [if_neg hcx]
    exact continuousWithinAt_const.congr' heq

private lemma prefixCount_continuousWithinAt_Iic (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ ↦ (prefixCount z N y : ℝ)) (Iic x) x := by
  induction N with
  | zero =>
      simpa [prefixCount] using
        (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ ↦ (0 : ℝ)) (Iic x) x)
  | succ N ih =>
      convert ih.add (threshold_continuousWithinAt_Iic (z N) x) using 1 <;>
        ext y <;> simp [prefixCount, Nat.count_succ]

private lemma discrepancy_continuousWithinAt_Iic (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ContinuousWithinAt (discrepancy z N) (Iic x) x := by
  exact (prefixCount_continuousWithinAt_Iic z N x).sub
    (continuousWithinAt_const.mul continuousWithinAt_id)

private lemma extend_bound_from_regularDomain
    (z : ℕ → ℝ) (m : ℕ) {l r : ℝ} (hl0 : 0 < l) (hr1 : r < 1)
    (hbound : ∀ x : regularDomain z, (x : ℝ) ∈ Ioo l r →
      ∀ N, |discrepancy z N (x : ℝ)| ≤ m) :
    ∀ x ∈ Ioo l r, ∀ N, |discrepancy z N x| ≤ m := by
  intro x hx N
  let S : Set ℝ := Ioo l x ∩ (Set.range z)ᶜ
  have hd : Dense (Set.range z)ᶜ := (Set.countable_range z).dense_compl ℝ
  have hsubcl : Ioo l x ⊆ closure S := by
    simpa only [S] using hd.open_subset_closure_inter (isOpen_Ioo (a := l) (b := x))
  have hxclI : x ∈ closure (Ioo l x) := by
    rw [closure_Ioo hx.1.ne]
    exact ⟨hx.1.le, le_rfl⟩
  have hxcl : x ∈ closure S := by
    exact (isClosed_closure.closure_subset_iff.mpr hsubcl) hxclI
  have hmaps : MapsTo (fun y ↦ |discrepancy z N y|) S (Iic (m : ℝ)) := by
    intro y hy
    have hyreg : y ∈ regularDomain z := ⟨
      ⟨hl0.trans hy.1.1, (hy.1.2.trans hx.2).trans hr1⟩, hy.2⟩
    exact hbound ⟨y, hyreg⟩ ⟨hy.1.1, hy.1.2.trans hx.2⟩ N
  have hcont : ContinuousWithinAt (fun y ↦ |discrepancy z N y|) S x := by
    exact (continuous_abs.continuousAt.comp_continuousWithinAt
      (discrepancy_continuousWithinAt_Iic z N x)).mono fun y hy ↦ hy.1.2.le
  exact (isClosed_Iic.closure_subset (hcont.mem_closure hxcl hmaps))

private lemma count_Ico_add_count_lt (z : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    Nat.count (fun n ↦ a ≤ z n ∧ z n < b) N + prefixCount z N a = prefixCount z N b := by
  induction N with
  | zero => simp [prefixCount]
  | succ N ih =>
      simp only [Nat.count_succ, prefixCount]
      change Nat.count (fun n ↦ a ≤ z n ∧ z n < b) N +
        Nat.count (fun n ↦ z n < a) N = Nat.count (fun n ↦ z n < b) N at ih
      by_cases ha : z N < a
      · have hb : z N < b := ha.trans_le hab
        have hna : ¬ a ≤ z N := not_le_of_gt ha
        simp [ha, hb, hna]
        omega
      · by_cases hb : z N < b
        · have hale : a ≤ z N := le_of_not_gt ha
          simp [ha, hb, hale]
          omega
        · have hp : ¬ (a ≤ z N ∧ z N < b) := fun h ↦ hb h.2
          simp [ha, hb, hp]
          omega

private lemma count_comp_nth_of_infinite
    (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hp : {n | p n}.Infinite) (K : ℕ) :
    Nat.count (fun j ↦ q (Nat.nth p j)) K =
      Nat.count (fun n ↦ p n ∧ q n) (Nat.nth p K) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun j _ ↦ Nat.nth p j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨(Nat.nth_lt_nth hp).2 hj.1, Nat.nth_mem_of_infinite hp j, hj.2⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    exact Nat.nth_injective hp heq
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hnrange : n ∈ Set.range (Nat.nth p) := by
      rw [Nat.range_nth_of_infinite hp]
      exact hn.2.1
    obtain ⟨j, hj⟩ := hnrange
    subst n
    have hjK : j < K := (Nat.nth_lt_nth hp).1 hn.1
    exact ⟨j, by simp [hjK, hn.2.2], rfl⟩

private lemma natCount_congr (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ n, p n ↔ q n) (N : ℕ) : Nat.count p N = Nat.count q N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Nat.count_succ]
      rw [ih]
      simp [h N]

def NoUniformStarDiscrepancy : Prop :=
  ∀ w : ℕ → ℝ, (∀ n, w n ∈ Ico (0 : ℝ) 1) →
    ∀ C : ℝ, ∃ N : ℕ, ∃ x ∈ Icc (0 : ℝ) 1,
      C < |discrepancy w N x|

private lemma local_uniform_impossible
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ)
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hbound : ∀ N x, x ∈ Icc a b → |discrepancy z N x| ≤ C) : False := by
  let p : ℕ → Prop := fun n ↦ a ≤ z n ∧ z n < b
  letI : DecidablePred p := Classical.decPred p
  have hpinf : {n | p n}.Infinite := by
    by_contra hp
    have hpfin : {n | p n}.Finite := Set.not_infinite.mp hp
    let B : ℕ := hpfin.toFinset.card
    let L : ℝ := b - a
    have hL : 0 < L := sub_pos.mpr hab
    obtain ⟨N, hN⟩ := exists_nat_gt (((B : ℝ) + 2 * C) / L)
    have hlarge : (B : ℝ) + 2 * C < (N : ℝ) * L := by
      have := (mul_lt_mul_of_pos_right hN hL)
      field_simp [L, hL.ne'] at this
      nlinarith
    have hcount : Nat.count p N ≤ B := by
      exact Nat.count_le_card hpfin N
    have hid : discrepancy z N b - discrepancy z N a =
        (Nat.count p N : ℝ) - (N : ℝ) * L := by
      have hc := count_Ico_add_count_lt z hab.le N
      have hc' : Nat.count p N + prefixCount z N a = prefixCount z N b := by
        have hcnt : Nat.count p N =
            @Nat.count (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd) N :=
          @natCount_congr p (fun n ↦ a ≤ z n ∧ z n < b) this
            (fun _ ↦ instDecidableAnd) (fun _ ↦ Iff.rfl) N
        rw [hcnt]
        exact hc
      have hcR : (prefixCount z N b : ℝ) =
          (Nat.count p N : ℝ) + prefixCount z N a := by
        exact_mod_cast hc'.symm
      unfold discrepancy
      rw [hcR]
      dsimp [L]
      ring
    have ha := hbound N a ⟨le_rfl, hab.le⟩
    have hb := hbound N b ⟨hab.le, le_rfl⟩
    have hcountR : (Nat.count p N : ℝ) ≤ B := by exact_mod_cast hcount
    rcases abs_le.mp ha with ⟨ha_lower, ha_upper⟩
    rcases abs_le.mp hb with ⟨hb_lower, hb_upper⟩
    nlinarith [hid]
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  let w : ℕ → ℝ := fun k ↦ (z (Nat.nth p k) - a) / L
  have hw : ∀ k, w k ∈ Ico (0 : ℝ) 1 := by
    intro k
    have hk := Nat.nth_mem_of_infinite hpinf k
    change a ≤ z (Nat.nth p k) ∧ z (Nat.nth p k) < b at hk
    constructor
    · exact div_nonneg (sub_nonneg.mpr hk.1) hL.le
    · rw [div_lt_one hL]
      dsimp [L]
      linarith
  obtain ⟨K, y, hy, hbad⟩ := hstar w hw (4 * C)
  let T : ℕ := Nat.nth p K
  let x : ℝ := a + L * y
  have hx : x ∈ Icc a b := by
    dsimp [x, L]
    constructor <;> nlinarith [hy.1, hy.2]
  have hpT : Nat.count p T = K := by
    exact Nat.count_nth_of_infinite hpinf K
  have hendNat : K + prefixCount z T a = prefixCount z T b := by
    have hc := count_Ico_add_count_lt z hab.le T
    have hc' : Nat.count p T + prefixCount z T a = prefixCount z T b := by
      have hcnt : Nat.count p T =
          @Nat.count (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd) T :=
        @natCount_congr p (fun n ↦ a ≤ z n ∧ z n < b) this
          (fun _ ↦ instDecidableAnd) (fun _ ↦ Iff.rfl) T
      rw [hcnt]
      exact hc
    rwa [hpT] at hc'
  have hprefixW : prefixCount w K y =
      Nat.count (fun n ↦ p n ∧ z n < x) T := by
    calc
      prefixCount w K y = Nat.count (fun j ↦ z (Nat.nth p j) < x) K := by
        unfold prefixCount
        apply natCount_congr
        intro j
        dsimp [w, x]
        rw [div_lt_iff₀ hL]
        constructor <;> intro h <;> linarith
      _ = Nat.count (fun n ↦ p n ∧ z n < x) T := by
        exact count_comp_nth_of_infinite p (fun n ↦ z n < x) hpinf K
  have hxle : x ≤ b := hx.2
  have hprefixNat : prefixCount w K y + prefixCount z T a = prefixCount z T x := by
    have hc := count_Ico_add_count_lt z hx.1 T
    have hcnt : Nat.count (fun n ↦ p n ∧ z n < x) T =
        @Nat.count (fun n ↦ a ≤ z n ∧ z n < x) (fun _ ↦ instDecidableAnd) T := by
      apply natCount_congr
      intro n
      dsimp [p]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2.trans_le hxle⟩, h.2⟩
    rw [hprefixW, hcnt]
    exact hc
  have hprefixR : (prefixCount w K y : ℝ) =
      (prefixCount z T x : ℝ) - prefixCount z T a := by
    have hc : (prefixCount w K y : ℝ) + prefixCount z T a = prefixCount z T x := by
      exact_mod_cast hprefixNat
    linarith
  have hendR : (K : ℝ) = (prefixCount z T b : ℝ) - prefixCount z T a := by
    have hc : (K : ℝ) + prefixCount z T a = prefixCount z T b := by
      exact_mod_cast hendNat
    linarith
  have hdw : discrepancy w K y =
      (discrepancy z T x - discrepancy z T a) -
        (discrepancy z T b - discrepancy z T a) * y := by
    unfold discrepancy
    rw [hprefixR, hendR]
    dsimp [x, L]
    ring
  have hxa := hbound T x hx
  have haa := hbound T a ⟨le_rfl, hab.le⟩
  have hbb := hbound T b ⟨hab.le, le_rfl⟩
  have hyabs : |y| ≤ 1 := (abs_le).2 ⟨by linarith [hy.1], hy.2⟩
  have hfinal : |discrepancy w K y| ≤ 4 * C := calc
    |discrepancy w K y| =
        |(discrepancy z T x - discrepancy z T a) -
          (discrepancy z T b - discrepancy z T a) * y| := congrArg abs hdw
    _ ≤ |discrepancy z T x - discrepancy z T a| +
        |(discrepancy z T b - discrepancy z T a) * y| := abs_sub _ _
    _ = |discrepancy z T x - discrepancy z T a| +
        |discrepancy z T b - discrepancy z T a| * |y| := by rw [abs_mul]
    _ ≤ (|discrepancy z T x| + |discrepancy z T a|) +
        (|discrepancy z T b| + |discrepancy z T a|) := by
      gcongr
      · exact abs_sub _ _
      · calc
          |discrepancy z T b - discrepancy z T a| * |y|
              ≤ |discrepancy z T b - discrepancy z T a| * 1 := by gcongr
          _ ≤ |discrepancy z T b| + |discrepancy z T a| := by
            simpa using abs_sub (discrepancy z T b) (discrepancy z T a)
    _ ≤ 4 * C := by linarith
  exact (not_lt_of_ge hfinal) hbad

theorem exists_unbounded_prefix_discrepancy
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ¬ BddAbove (Set.range (fun N ↦ |discrepancy z N x|)) := by
  by_contra h
  push_neg at h
  letI : BaireSpace (regularDomain z) :=
    (regularDomain_isGδ z).baireSpace_of_t2Space_locallyCompactSpace
  letI : Nonempty (regularDomain z) := (regularDomain_nonempty z).to_subtype
  have hcover : ⋃ m : ℕ, boundedLayer z m = Set.univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hb := h (x : ℝ) x.property.1
    rcases hb with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_gt C
    refine ⟨m, ?_⟩
    intro N
    exact (hC ⟨N, rfl⟩).trans hm.le
  obtain ⟨m, x₀, hx₀⟩ :=
    nonempty_interior_of_iUnion_of_closed (boundedLayer_closed z) hcover
  have hnh : interior (boundedLayer z m) ∈ nhds x₀ :=
    isOpen_interior.mem_nhds hx₀
  obtain ⟨u, hu, husub⟩ := (mem_nhds_subtype (regularDomain z) x₀ _).mp hnh
  obtain ⟨l, r, hlr, hlrsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  let A : ℝ := (max l 0 + (x₀ : ℝ)) / 2
  let B : ℝ := ((x₀ : ℝ) + min r 1) / 2
  have hlx : max l 0 < (x₀ : ℝ) := (max_lt_iff).2 ⟨hlr.1, x₀.property.1.1⟩
  have hxr : (x₀ : ℝ) < min r 1 := (lt_min_iff).2 ⟨hlr.2, x₀.property.1.2⟩
  have hA0 : 0 < A := by
    dsimp [A]
    nlinarith [le_max_right l 0, x₀.property.1.1]
  have hlA : l < A := by
    dsimp [A]
    nlinarith [le_max_left l 0, hlx]
  have hAx : A < (x₀ : ℝ) := by dsimp [A]; linarith
  have hxB : (x₀ : ℝ) < B := by dsimp [B]; linarith
  have hBr : B < r := by
    dsimp [B]
    nlinarith [min_le_left r 1, hxr]
  have hB1 : B < 1 := by
    dsimp [B]
    nlinarith [min_le_right r 1, x₀.property.1.2]
  have hboundReg : ∀ x : regularDomain z, (x : ℝ) ∈ Ioo A B →
      ∀ N, |discrepancy z N (x : ℝ)| ≤ m := by
    intro x hxAB
    have hxu : (x : ℝ) ∈ u := hlrsub ⟨hlA.trans hxAB.1, hxAB.2.trans hBr⟩
    exact interior_subset (husub hxu)
  have hall := extend_bound_from_regularDomain z m hA0 hB1 hboundReg
  let c : ℝ := (A + (x₀ : ℝ)) / 2
  let d : ℝ := ((x₀ : ℝ) + B) / 2
  have hcd : c < d := by dsimp [c, d]; linarith
  have hlocal : ∀ N y, y ∈ Icc c d → |discrepancy z N y| ≤ (m : ℝ) := by
    intro N y hy
    apply hall y ?_ N
    constructor
    · have hyl := hy.1
      dsimp [c] at hyl
      linarith [hAx]
    · have hyr := hy.2
      dsimp [d] at hyr
      linarith [hxB]
  exact local_uniform_impossible hstar z hcd (Nat.cast_nonneg m) hlocal

theorem unbounded_endpoint_of_no_uniform
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∀ C : ℝ, ∃ N : ℕ,
      C < |discrepancy z N x| := by
  obtain ⟨x, hx, hub⟩ := exists_unbounded_prefix_discrepancy hstar z
  refine ⟨x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
  intro C
  by_contra h
  push_neg at h
  apply hub
  refine ⟨C, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact h N

end Erdos255Baire

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos255/FiniteRoth.lean` -/

section
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


open Filter Finset Set
open scoped BigOperators



noncomputable section

def prefixCount (y : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ y n < u).card

def starDisc (y : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  prefixCount y N u - N * u

private def halfSize (q d : ℕ) : ℕ := 2 ^ (q + 1 - d)

private def haar (q d i A : ℕ) : ℝ :=
  let h := halfSize q d
  (if A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h) then 1 else 0) -
    (if A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h) then 1 else 0)

private lemma pow_two_pos (n : ℕ) : 0 < 2 ^ n := by positivity

private lemma two_mul_halfSize (q d : ℕ) (hd : d ≤ q + 1) :
    2 * halfSize q d = 2 ^ (q + 2 - d) := by
  unfold halfSize
  rw [show q + 2 - d = (q + 1 - d) + 1 by omega, pow_succ]
  ring

private lemma blocks_end (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    2 * (i + 1) * halfSize q d ≤ 2 ^ (q + 2) := by
  have hip : i + 1 ≤ 2 ^ d := by omega
  calc
    2 * (i + 1) * halfSize q d = (i + 1) * (2 * halfSize q d) := by ring
    _ ≤ 2 ^ d * 2 ^ (q + 2 - d) := Nat.mul_le_mul hip (le_of_eq (two_mul_halfSize q d hd))
    _ = 2 ^ (q + 2) := by
      rw [← pow_add]
      congr 1
      omega

private lemma block_lo_le_mid (q d i : ℕ) :
    2 * i * halfSize q d ≤ (2 * i + 1) * halfSize q d := by
  have hh := pow_two_pos (q + 1 - d)
  dsimp [halfSize]
  nlinarith

private lemma block_mid_le_hi (q d i : ℕ) :
    (2 * i + 1) * halfSize q d ≤ 2 * (i + 1) * halfSize q d := by
  have hh := pow_two_pos (q + 1 - d)
  dsimp [halfSize]
  nlinarith

private lemma sum_ite_mem_Ico_one (Q a b : ℕ) (ha : a ≤ b) (hb : b ≤ Q) :
    ∑ A ∈ Finset.range Q, (if A ∈ Finset.Ico a b then (1 : ℝ) else 0) = b - a := by
  rw [← Finset.sum_filter]
  have heq : (Finset.range Q).filter (fun A ↦ A ∈ Finset.Ico a b) = Finset.Ico a b := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq]
  simp [Nat.cast_sub ha]

private lemma haar_sum (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A = 0 := by
  unfold haar
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_ite_mem_Ico_one, sum_ite_mem_Ico_one]
  · push_cast
    ring
  · exact block_mid_le_hi q d i
  · exact blocks_end q d i hd hi
  · exact block_lo_le_mid q d i
  · exact (block_mid_le_hi q d i).trans (blocks_end q d i hd hi)

private lemma haar_sq_point (q d i A : ℕ) :
    haar q d i A ^ 2 =
      (if A ∈ Finset.Ico (2 * i * halfSize q d) ((2 * i + 1) * halfSize q d)
        then (1 : ℝ) else 0) +
      (if A ∈ Finset.Ico ((2 * i + 1) * halfSize q d) (2 * (i + 1) * halfSize q d)
        then (1 : ℝ) else 0) := by
  unfold haar
  simp only [Finset.mem_Ico]
  by_cases h₁ : 2 * i * halfSize q d ≤ A ∧ A < (2 * i + 1) * halfSize q d
  · have h₂ : ¬ ((2 * i + 1) * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d) := by omega
    simp [h₁, h₂]
  · by_cases h₂ : (2 * i + 1) * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d
    · simp [h₁, h₂]
    · simp [h₁, h₂]

private lemma haar_sq_sum (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A ^ 2 =
      2 * halfSize q d := by
  simp_rw [haar_sq_point, Finset.sum_add_distrib]
  rw [sum_ite_mem_Ico_one, sum_ite_mem_Ico_one]
  · push_cast
    ring
  · exact block_mid_le_hi q d i
  · exact blocks_end q d i hd hi
  · exact block_lo_le_mid q d i
  · exact (block_mid_le_hi q d i).trans (blocks_end q d i hd hi)

private lemma sum_Ico_id (a h : ℕ) :
    ∑ A ∈ Finset.Ico a (a + h), A = h * a + h * (h - 1) / 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  calc
    ∑ k ∈ Finset.range h, (a + k) =
        (∑ _k ∈ Finset.range h, a) + ∑ k ∈ Finset.range h, k := by
          rw [Finset.sum_add_distrib]
    _ = h * a + h * (h - 1) / 2 := by simp [Finset.sum_range_id, Nat.mul_comm]

private lemma sum_cast_ite_mem_Ico (Q a b : ℕ) (ha : a ≤ b) (hb : b ≤ Q) :
    ∑ A ∈ Finset.range Q, (A : ℝ) * (if A ∈ Finset.Ico a b then (1 : ℝ) else 0) =
      ∑ A ∈ Finset.Ico a b, (A : ℝ) := by
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma sum_Ico_cast (a h : ℕ) :
    ∑ A ∈ Finset.Ico a (a + h), (A : ℝ) =
      (h : ℝ) * a + (h * (h - 1) / 2 : ℕ) := by
  calc
    ∑ A ∈ Finset.Ico a (a + h), (A : ℝ) =
        ((∑ A ∈ Finset.Ico a (a + h), A : ℕ) : ℝ) := by
          exact (Nat.cast_sum (Finset.Ico a (a + h)) fun A ↦ A).symm
    _ = (h * a + h * (h - 1) / 2 : ℕ) := by rw [sum_Ico_id]
    _ = (h : ℝ) * a + (h * (h - 1) / 2 : ℕ) := by push_cast; ring

private lemma haar_moment_nat (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), (A : ℝ) * haar q d i A =
      -(halfSize q d : ℝ) ^ 2 := by
  let h := halfSize q d
  have hlo_mid : 2 * i * h ≤ (2 * i + 1) * h := block_lo_le_mid q d i
  have hmid_hi : (2 * i + 1) * h ≤ 2 * (i + 1) * h := block_mid_le_hi q d i
  have hend : 2 * (i + 1) * h ≤ 2 ^ (q + 2) := blocks_end q d i hd hi
  have hleft_end : 2 * i * h + h = (2 * i + 1) * h := by ring
  have hright_end : (2 * i + 1) * h + h = 2 * (i + 1) * h := by ring
  unfold haar
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sum_cast_ite_mem_Ico, sum_cast_ite_mem_Ico]
  · change
      (∑ A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h), (A : ℝ)) -
        (∑ A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h), (A : ℝ)) =
          -(h : ℝ) ^ 2
    have hleft :
        ∑ A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h), (A : ℝ) =
          (h : ℝ) * (2 * i * h) + (h * (h - 1) / 2 : ℕ) := by
      convert sum_Ico_cast (2 * i * h) h using 1 <;> push_cast <;> ring
    have hright :
        ∑ A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h), (A : ℝ) =
          (h : ℝ) * ((2 * i + 1) * h) + (h * (h - 1) / 2 : ℕ) := by
      convert sum_Ico_cast ((2 * i + 1) * h) h using 1 <;> push_cast <;> ring
    rw [hleft, hright]
    dsimp [h]
    push_cast
    ring
  · simpa [h] using hmid_hi
  · simpa [h] using hend
  · simpa [h] using hlo_mid
  · simpa [h] using hmid_hi.trans hend

private lemma halfSize_relation (q d e : ℕ) (hde : d < e) (he : e ≤ q + 1) :
    halfSize q d = 2 * 2 ^ (e - d - 1) * halfSize q e := by
  unfold halfSize
  have hexp : q + 1 - d = (e - d - 1) + 1 + (q + 1 - e) := by omega
  rw [hexp, pow_add, pow_add]
  ring

private lemma no_cross_aligned (h p j k : ℕ) (hh : 0 < h) :
    2 * (j + 1) * h ≤ k * (2 * p * h) ∨
      k * (2 * p * h) ≤ 2 * j * h := by
  by_cases hj : j < k * p
  · left
    have : j + 1 ≤ k * p := by omega
    nlinarith
  · right
    have : k * p ≤ j := by omega
    nlinarith

private lemma comparison_constant_on_block
    {s t b A A' : ℕ} (hcross : t ≤ b ∨ b ≤ s)
    (hA : s ≤ A ∧ A < t) (hA' : s ≤ A' ∧ A' < t) :
    (b ≤ A ↔ b ≤ A') ∧ (A < b ↔ A' < b) := by
  rcases hcross with htb | hbs <;> omega

private lemma haar_eq_zero_of_outside (q d i A : ℕ)
    (hA : ¬ (2 * i * halfSize q d ≤ A ∧
      A < 2 * (i + 1) * halfSize q d)) :
    haar q d i A = 0 := by
  unfold haar
  simp only [Finset.mem_Ico]
  have hleft : ¬ (2 * i * halfSize q d ≤ A ∧
      A < (2 * i + 1) * halfSize q d) := by
    intro h
    apply hA
    exact ⟨h.1, h.2.trans_le (block_mid_le_hi q d i)⟩
  have hright : ¬ ((2 * i + 1) * halfSize q d ≤ A ∧
      A < 2 * (i + 1) * halfSize q d) := by
    intro h
    apply hA
    exact ⟨(block_lo_le_mid q d i).trans h.1, h.2⟩
  simp [hleft, hright]

private lemma haar_coarse_constant_on_fine
    (q d e i j A : ℕ) (hde : d < e) (he : e ≤ q + 1)
    (hA : 2 * j * halfSize q e ≤ A ∧
      A < 2 * (j + 1) * halfSize q e) :
    haar q d i A = haar q d i (2 * j * halfSize q e) := by
  let h := halfSize q e
  let p := 2 ^ (e - d - 1)
  change haar q d i A = haar q d i (2 * j * h)
  have hh : 0 < h := by dsimp [h, halfSize]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hrel : halfSize q d = 2 * p * h := by
    simpa [h, p] using halfSize_relation q d e hde he
  have hs_mem : 2 * j * h ≤ 2 * j * h ∧ 2 * j * h < 2 * (j + 1) * h := by
    constructor
    · rfl
    · nlinarith
  have cross_lo :
      2 * (j + 1) * h ≤ 2 * i * halfSize q d ∨
        2 * i * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * i) hh
  have cross_mid :
      2 * (j + 1) * h ≤ (2 * i + 1) * halfSize q d ∨
        (2 * i + 1) * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * i + 1) hh
  have cross_hi :
      2 * (j + 1) * h ≤ 2 * (i + 1) * halfSize q d ∨
        2 * (i + 1) * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * (i + 1)) hh
  have c_lo := comparison_constant_on_block cross_lo hA hs_mem
  have c_mid := comparison_constant_on_block cross_mid hA hs_mem
  have c_hi := comparison_constant_on_block cross_hi hA hs_mem
  unfold haar
  simp only [Finset.mem_Ico]
  simp only [c_lo.1, c_mid.1, c_mid.2, c_hi.2]

private lemma haar_mul_fine (q d e i j A : ℕ)
    (hde : d < e) (he : e ≤ q + 1) :
    haar q d i A * haar q e j A =
      haar q d i (2 * j * halfSize q e) * haar q e j A := by
  by_cases hA : 2 * j * halfSize q e ≤ A ∧
      A < 2 * (j + 1) * halfSize q e
  · rw [haar_coarse_constant_on_fine q d e i j A hde he hA]
  · rw [haar_eq_zero_of_outside q e j A hA]
    ring

private lemma haar_orthogonal_of_lt
    (q d e i j : ℕ) (hde : d < e) (he : e ≤ q + 1) (hj : j < 2 ^ e) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A = 0 := by
  calc
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A =
        ∑ A ∈ Finset.range (2 ^ (q + 2)),
          haar q d i (2 * j * halfSize q e) * haar q e j A := by
            apply Finset.sum_congr rfl
            intro A hA
            exact haar_mul_fine q d e i j A hde he
    _ = haar q d i (2 * j * halfSize q e) *
        ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q e j A := by
          rw [Finset.mul_sum]
    _ = 0 := by rw [haar_sum q e j he hj, mul_zero]

private lemma haar_mul_eq_zero_of_same_depth_ne
    (q d i j A : ℕ) (hij : i ≠ j) :
    haar q d i A * haar q d j A = 0 := by
  have hh : 0 < halfSize q d := by unfold halfSize; positivity
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · have hsep : 2 * (i + 1) * halfSize q d ≤ 2 * j * halfSize q d := by
      have : i + 1 ≤ j := by omega
      nlinarith
    by_cases hAi : 2 * i * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d
    · have hAj : ¬ (2 * j * halfSize q d ≤ A ∧
          A < 2 * (j + 1) * halfSize q d) := by omega
      rw [haar_eq_zero_of_outside q d j A hAj, mul_zero]
    · rw [haar_eq_zero_of_outside q d i A hAi, zero_mul]
  · have hsep : 2 * (j + 1) * halfSize q d ≤ 2 * i * halfSize q d := by
      have : j + 1 ≤ i := by omega
      nlinarith
    by_cases hAj : 2 * j * halfSize q d ≤ A ∧
        A < 2 * (j + 1) * halfSize q d
    · have hAi : ¬ (2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d) := by omega
      rw [haar_eq_zero_of_outside q d i A hAi, zero_mul]
    · rw [haar_eq_zero_of_outside q d j A hAj, mul_zero]

private lemma haar_orthogonal
    (q d e i j : ℕ) (hd : d ≤ q + 1) (he : e ≤ q + 1)
    (hi : i < 2 ^ d) (hj : j < 2 ^ e) (hne : (d, i) ≠ (e, j)) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A = 0 := by
  rcases lt_trichotomy d e with hde | hde | hde
  · exact haar_orthogonal_of_lt q d e i j hde he hj
  · subst e
    have hij : i ≠ j := by simpa using hne
    simp_rw [haar_mul_eq_zero_of_same_depth_ne q d i j _ hij]
    simp
  · calc
      ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q e j A * haar q d i A := by
            apply Finset.sum_congr rfl
            intro A hA
            ring
      _ = 0 := haar_orthogonal_of_lt q e d j i hde hd hi

private abbrev Rect (q d : ℕ) := Fin (2 ^ d) × Fin (2 ^ (q + 1 - d))

private def inCell (q d i : ℕ) (x : ℝ) : Prop :=
  ((2 * i * halfSize q d : ℕ) : ℝ) / 2 ^ (q + 2) ≤ x ∧
    x < ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) / 2 ^ (q + 2)

private lemma inCell_unique (q d i j : ℕ) (x : ℝ)
    (hi : inCell q d i x) (hj : inCell q d j x) : i = j := by
  by_contra hij
  have hQ : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hindex : i + 1 ≤ j := by omega
    have hsep : ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) ≤
        ((2 * j * halfSize q d : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (i + 1) * halfSize q d ≤ 2 * j * halfSize q d by
        gcongr)
    have := (div_le_div_iff_of_pos_right hQ).mpr hsep
    linarith [hi.2, hj.1]
  · have hindex : j + 1 ≤ i := by omega
    have hsep : ((2 * (j + 1) * halfSize q d : ℕ) : ℝ) ≤
        ((2 * i * halfSize q d : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (j + 1) * halfSize q d ≤ 2 * i * halfSize q d by
        gcongr)
    have := (div_le_div_iff_of_pos_right hQ).mpr hsep
    linarith [hj.2, hi.1]

private def rectsAtPoint (q d : ℕ) (x v : ℝ) : Finset (Rect q d) :=
  by
    classical
    exact Finset.univ.filter fun R ↦ inCell q d R.1 x ∧ inCell q (q + 1 - d) R.2 v

private lemma rectsAtPoint_card_le_one (q d : ℕ) (x v : ℝ) :
    (rectsAtPoint q d x v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro R hR S hS
  simp only [rectsAtPoint, Finset.mem_filter, Finset.mem_univ, true_and] at hR hS
  apply Prod.ext
  · apply Fin.ext
    exact inCell_unique q d R.1 S.1 x hR.1 hS.1
  · apply Fin.ext
    exact inCell_unique q (q + 1 - d) R.2 S.2 v hR.2 hS.2

private def occupiedRects (y : ℕ → ℝ) (q d : ℕ) : Finset (Rect q d) :=
  (Finset.range (2 ^ q)).biUnion fun n ↦
    rectsAtPoint q d (y n) ((n : ℝ) / (2 ^ q : ℕ))

private lemma occupiedRects_card_le (y : ℕ → ℝ) (q d : ℕ) :
    (occupiedRects y q d).card ≤ 2 ^ q := by
  calc
    (occupiedRects y q d).card ≤
        ∑ n ∈ Finset.range (2 ^ q),
          (rectsAtPoint q d (y n) ((n : ℝ) / (2 ^ q : ℕ))).card := by
            exact Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range (2 ^ q), 1 := by
      exact Finset.sum_le_sum fun n hn ↦ rectsAtPoint_card_le_one q d _ _
    _ = 2 ^ q := by simp

private lemma rect_card (q d : ℕ) (hd : d ≤ q + 1) :
    Fintype.card (Rect q d) = 2 * 2 ^ q := by
  simp only [Rect, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_add]
  have : d + (q + 1 - d) = q + 1 := by omega
  rw [this, pow_succ]
  ring

private def emptyRects (y : ℕ → ℝ) (q d : ℕ) : Finset (Rect q d) :=
  Finset.univ \ occupiedRects y q d

private lemma emptyRects_card_ge (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1) :
    2 ^ q ≤ (emptyRects y q d).card := by
  rw [emptyRects, Finset.card_sdiff]
  have hinter : occupiedRects y q d ∩ Finset.univ = occupiedRects y q d := by simp
  rw [hinter, Finset.card_univ, rect_card q d hd]
  have hoc := occupiedRects_card_le y q d
  omega

private lemma emptyRects_card_le (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1) :
    (emptyRects y q d).card ≤ 2 * 2 ^ q := by
  calc
    (emptyRects y q d).card ≤ (Finset.univ : Finset (Rect q d)).card :=
      Finset.card_le_card (Finset.sdiff_subset)
    _ = 2 * 2 ^ q := by rw [Finset.card_univ, rect_card q d hd]

private def tailHaar (q d i : ℕ) (x : ℝ) : ℝ :=
  ∑ A ∈ Finset.range (2 ^ (q + 2)),
    (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A

private lemma tailHaar_eq_zero_of_not_inCell (q d i : ℕ) (x : ℝ)
    (hd : d ≤ q + 1) (hi : i < 2 ^ d) (hx : ¬ inCell q d i x) :
    tailHaar q d i x = 0 := by
  have hQ : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  simp only [inCell, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hpoint : ∀ A ∈ Finset.range (2 ^ (q + 2)),
        (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A =
          haar q d i A := by
      intro A hA
      by_cases hsupp : 2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d
      · have hcast : ((2 * i * halfSize q d : ℕ) : ℝ) ≤ A := by exact_mod_cast hsupp.1
        have hdiv := (div_le_div_iff_of_pos_right hQ).mpr hcast
        simp [hx.trans_le hdiv]
      · rw [haar_eq_zero_of_outside q d i A hsupp]
        simp
    rw [tailHaar]
    calc
      ∑ A ∈ Finset.range (2 ^ (q + 2)),
          (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A :=
            Finset.sum_congr rfl hpoint
      _ = 0 := haar_sum q d i hd hi
  · have hpoint : ∀ A ∈ Finset.range (2 ^ (q + 2)),
        (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A = 0 := by
      intro A hA
      by_cases hsupp : 2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d
      · have hcast : (A : ℝ) ≤ ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) := by
          exact_mod_cast hsupp.2.le
        have hdiv := (div_le_div_iff_of_pos_right hQ).mpr hcast
        simp [not_lt_of_ge (hdiv.trans (le_of_not_gt hx))]
      · rw [haar_eq_zero_of_outside q d i A hsupp]
        simp
    rw [tailHaar]
    exact Finset.sum_eq_zero hpoint

private lemma not_occupied_product_tailHaar_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) (n : ℕ) (hn : n < 2 ^ q) :
    tailHaar q d R.1 (y n) *
      tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) = 0 := by
  classical
  have hnot : R ∉ occupiedRects y q d := (Finset.mem_sdiff.mp hR).2
  have hnotcell : ¬ (inCell q d R.1 (y n) ∧
      inCell q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ))) := by
    intro hcell
    apply hnot
    simp only [occupiedRects, Finset.mem_biUnion, Finset.mem_range]
    refine ⟨n, hn, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  rcases not_and_or.mp hnotcell with hleft | hright
  · rw [tailHaar_eq_zero_of_not_inCell q d R.1 (y n) hd R.1.isLt hleft, zero_mul]
  · have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
    rw [tailHaar_eq_zero_of_not_inCell q (q + 1 - d) R.2
      ((n : ℝ) / (2 ^ q : ℕ)) hvd R.2.isLt hright, mul_zero]

private def rectHaar (q d : ℕ) (R : Rect q d) (A C : ℕ) : ℝ :=
  haar q d R.1 A * haar q (q + 1 - d) R.2 C

private lemma halfSize_mul_complement (q d : ℕ) (hd : d ≤ q + 1) :
    halfSize q d * halfSize q (q + 1 - d) = 2 ^ (q + 1) := by
  rw [halfSize, halfSize, ← pow_add]
  congr 1
  omega

private lemma rectHaar_sq_sum (q d : ℕ) (R : Rect q d) (hd : d ≤ q + 1) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C ^ 2 = (8 * 2 ^ q : ℝ) := by
  have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C ^ 2) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A ^ 2) *
      (∑ C ∈ Finset.range (2 ^ (q + 2)), haar q (q + 1 - d) R.2 C ^ 2) by
    simp only [rectHaar, mul_pow]
    calc
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          haar q d R.1 A ^ 2 * haar q (q + 1 - d) R.2 C ^ 2) =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A ^ 2 *
            (∑ C ∈ Finset.range (2 ^ (q + 2)), haar q (q + 1 - d) R.2 C ^ 2) := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]]
  rw [haar_sq_sum q d R.1 hd R.1.isLt,
    haar_sq_sum q (q + 1 - d) R.2 hvd R.2.isLt]
  norm_cast
  calc
    2 * halfSize q d * (2 * halfSize q (q + 1 - d)) =
        4 * (halfSize q d * halfSize q (q + 1 - d)) := by ring
    _ = 4 * 2 ^ (q + 1) := by rw [halfSize_mul_complement q d hd]
    _ = 8 * 2 ^ q := by rw [pow_succ]; ring

private lemma rectHaar_orthogonal (q d e : ℕ) (R : Rect q d) (S : Rect q e)
    (hd : d ≤ q + 1) (he : e ≤ q + 1)
    (hne : (d, R.1.val, R.2.val) ≠ (e, S.1.val, S.2.val)) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C * rectHaar q e S A C = 0 := by
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C * rectHaar q e S A C) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A * haar q e S.1 A) *
      (∑ C ∈ Finset.range (2 ^ (q + 2)),
        haar q (q + 1 - d) R.2 C * haar q (q + 1 - e) S.2 C) by
    simp only [rectHaar]
    calc
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          (haar q d R.1 A * haar q (q + 1 - d) R.2 C) *
            (haar q e S.1 A * haar q (q + 1 - e) S.2 C)) =
          ∑ A ∈ Finset.range (2 ^ (q + 2)),
            (haar q d R.1 A * haar q e S.1 A) *
              (∑ C ∈ Finset.range (2 ^ (q + 2)),
                haar q (q + 1 - d) R.2 C * haar q (q + 1 - e) S.2 C) := by
            apply Finset.sum_congr rfl
            intro A hA
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro C hC
            ring
      _ = _ := by rw [Finset.sum_mul]]
  by_cases hde : d = e
  · subst e
    by_cases hhor : R.1.val = S.1.val
    · have hver : R.2.val ≠ S.2.val := by
        intro hv
        exact hne (by simp [hhor, hv])
      have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
      rw [haar_orthogonal q (q + 1 - d) (q + 1 - d) R.2 S.2 hvd hvd
          R.2.isLt S.2.isLt (by
          intro h; exact hver (congrArg Prod.snd h))]
      simp
    · rw [haar_orthogonal q d d R.1 S.1 hd hd R.1.isLt S.1.isLt (by
          intro h; exact hhor (congrArg Prod.snd h))]
      simp
  · rw [haar_orthogonal q d e R.1 S.1 hd he R.1.isLt S.1.isLt (by
        intro h; exact hde (congrArg Prod.fst h))]
    simp

private abbrev TaggedRect (q : ℕ) := Σ d : Fin (q + 2), Rect q d

private def taggedEmpty (y : ℕ → ℝ) (q : ℕ) : Finset (TaggedRect q) :=
  (Finset.univ : Finset (Fin (q + 2))).sigma fun d ↦ emptyRects y q d

private def taggedHaar (q : ℕ) (T : TaggedRect q) (A C : ℕ) : ℝ :=
  rectHaar q T.1 T.2 A C

private lemma taggedEmpty_card_ge (y : ℕ → ℝ) (q : ℕ) :
    (q + 2) * 2 ^ q ≤ (taggedEmpty y q).card := by
  rw [taggedEmpty, Finset.card_sigma]
  calc
    (q + 2) * 2 ^ q = ∑ _d ∈ (Finset.univ : Finset (Fin (q + 2))), 2 ^ q := by simp
    _ ≤ ∑ d ∈ (Finset.univ : Finset (Fin (q + 2))), (emptyRects y q d).card := by
      exact Finset.sum_le_sum fun d hd ↦ emptyRects_card_ge y q d (by omega)

private lemma taggedHaar_inner (q : ℕ) (T S : TaggedRect q) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      taggedHaar q T A C * taggedHaar q S A C =
        if T = S then (8 * 2 ^ q : ℝ) else 0 := by
  by_cases hTS : T = S
  · subst S
    rw [if_pos rfl]
    simpa only [taggedHaar, pow_two] using rectHaar_sq_sum q T.1 T.2 (by omega)
  · rw [if_neg hTS]
    apply rectHaar_orthogonal q T.1 S.1 T.2 S.2 (by omega) (by omega)
    intro h
    apply hTS
    have hdval : T.1.val = S.1.val := congrArg (fun z ↦ z.1) h
    have hd : T.1 = S.1 := Fin.ext hdval
    cases T with
    | mk d R =>
      cases S with
      | mk e U =>
        simp only at hd
        subst e
        congr 1
        apply Prod.ext <;> apply Fin.ext
        · exact congrArg (fun z ↦ z.2.1) h
        · exact congrArg (fun z ↦ z.2.2) h

private def testFunction (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  ∑ T ∈ taggedEmpty y q, taggedHaar q T A C

private lemma testFunction_sq_sum (y : ℕ → ℝ) (q : ℕ) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      testFunction y q A C ^ 2 =
        ((taggedEmpty y q).card : ℝ) * (8 * 2 ^ q) := by
  classical
  simp only [testFunction, pow_two]
  simp_rw [Finset.sum_mul_sum]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)),
      ∑ C ∈ Finset.range (2 ^ (q + 2)),
        ∑ T ∈ taggedEmpty y q, ∑ S ∈ taggedEmpty y q,
          taggedHaar q T A C * taggedHaar q S A C) =
      ∑ T ∈ taggedEmpty y q, ∑ S ∈ taggedEmpty y q,
        ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            taggedHaar q T A C * taggedHaar q S A C by
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ T ∈ taggedEmpty y q, ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ∑ S ∈ taggedEmpty y q, taggedHaar q T A C * taggedHaar q S A C := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)), ∑ S ∈ taggedEmpty y q,
            taggedHaar q T A C * taggedHaar q S A C := by rw [Finset.sum_comm]
      _ = ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ S ∈ taggedEmpty y q, ∑ C ∈ Finset.range (2 ^ (q + 2)),
            taggedHaar q T A C * taggedHaar q S A C := by
              apply Finset.sum_congr rfl
              intro T hT
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.sum_comm]]
  simp_rw [taggedHaar_inner]
  simp

private def ceilQuarter (C : ℕ) : ℕ := (C + 3) / 4

private lemma pow_q_add_two (q : ℕ) : 2 ^ (q + 2) = 4 * 2 ^ q := by
  rw [pow_add]
  norm_num
  ring

private lemma ceilQuarter_error (q C : ℕ) :
    abs ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) ≤ 1 := by
  have hlow : C ≤ 4 * ceilQuarter C := by
    unfold ceilQuarter
    omega
  have hhigh : 4 * ceilQuarter C < C + 4 := by
    unfold ceilQuarter
    omega
  have hM : (0 : ℝ) < (2 ^ q : ℕ) := by positivity
  have hideal : (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ) = (C : ℝ) / 4 := by
    rw [pow_q_add_two]
    push_cast
    field_simp
  have hlowR : (C : ℝ) ≤ 4 * (ceilQuarter C : ℝ) := by exact_mod_cast hlow
  have hhighR : 4 * (ceilQuarter C : ℝ) < (C : ℝ) + 4 := by exact_mod_cast hhigh
  rw [hideal, abs_le]
  constructor <;> linarith

private def gridDisc (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
    ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
      ((A : ℝ) / (2 ^ (q + 2) : ℕ))

private lemma gridDisc_abs_le (y : ℕ → ℝ) (B : ℝ)
    (hB : ∀ N u, u ∈ Set.Icc (0 : ℝ) 1 → abs (starDisc y N u) ≤ B)
    (q A C : ℕ) (hA : A < 2 ^ (q + 2)) :
    abs (gridDisc y q A C) ≤ B + 1 := by
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  have hu : (A : ℝ) / (2 ^ (q + 2) : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hQ).mpr
      exact_mod_cast hA.le
  have hstar := hB (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) hu
  have herr := ceilQuarter_error q C
  have huabs : abs ((A : ℝ) / (2 ^ (q + 2) : ℕ)) ≤ 1 := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  rw [gridDisc]
  calc
    abs (starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
        ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
          ((A : ℝ) / (2 ^ (q + 2) : ℕ))) ≤
        abs (starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ))) +
          abs (((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
            ((A : ℝ) / (2 ^ (q + 2) : ℕ))) := abs_add_le _ _
    _ ≤ B + 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg ((ceilQuarter C : ℝ) -
        (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)),
        abs_nonneg ((A : ℝ) / (2 ^ (q + 2) : ℕ))]

/-! A self-contained finite-grid Roth inequality. -/

private def lowerTailHaar (q d i : ℕ) (x : ℝ) : ℝ :=
  ∑ A ∈ Finset.range (2 ^ (q + 2)),
    (if 0 ≤ x ∧ x < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) * haar q d i A

private lemma lowerTailHaar_eq (q d i : ℕ) (x : ℝ) :
    lowerTailHaar q d i x = if 0 ≤ x then tailHaar q d i x else 0 := by
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, lowerTailHaar, tailHaar]
    apply Finset.sum_congr rfl
    intro A hA
    simp [hx]
  · rw [if_neg hx, lowerTailHaar]
    simp [hx]

private lemma not_occupied_product_lower_tail_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) (n : ℕ) (hn : n < 2 ^ q) :
    lowerTailHaar q d R.1 (y n) *
      tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) = 0 := by
  rw [lowerTailHaar_eq]
  split_ifs with hy
  · exact not_occupied_product_tailHaar_eq_zero y q d hd R hR n hn
  · simp

def gridCount (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (2 ^ q),
    (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
      (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0)

def gridDiscrepancy (y : ℕ → ℝ) (lam : ℝ) (q A C : ℕ) : ℝ :=
  gridCount y q A C - lam *
    ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * ((C : ℝ) / (2 ^ (q + 2) : ℕ))

private lemma rawCount_rectHaar_sum_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridCount y q A C * rectHaar q d R A C = 0 := by
  classical
  simp only [gridCount, rectHaar]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      (∑ n ∈ Finset.range (2 ^ q),
        (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
        (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0)) *
        (haar q d R.1 A * haar q (q + 1 - d) R.2 C)) =
      ∑ n ∈ Finset.range (2 ^ q),
        lowerTailHaar q d R.1 (y n) *
          tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) by
    simp only [lowerTailHaar, tailHaar]
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          ∑ n ∈ Finset.range (2 ^ q),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                apply Finset.sum_congr rfl
                intro A hA
                apply Finset.sum_congr rfl
                intro C hC
                apply Finset.sum_congr rfl
                intro n hn
                ring
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ n ∈ Finset.range (2 ^ q),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                apply Finset.sum_congr rfl
                intro A hA
                rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.range (2 ^ q), ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C hC
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  exact Finset.sum_eq_zero fun n hn ↦
    not_occupied_product_lower_tail_eq_zero y q d hd R hR n (Finset.mem_range.mp hn)

private lemma normalized_haar_moment (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)),
      ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d i A =
        -((halfSize q d : ℝ) ^ 2) / (2 ^ (q + 2) : ℕ) := by
  calc
    _ = (∑ A ∈ Finset.range (2 ^ (q + 2)), (A : ℝ) * haar q d i A) /
        (2 ^ (q + 2) : ℕ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro A hA
          ring
    _ = _ := by rw [haar_moment_nat q d i hd hi]

private lemma normalized_moments_product (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) :
    (∑ A ∈ Finset.range (2 ^ (q + 2)),
      ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
    (∑ C ∈ Finset.range (2 ^ (q + 2)),
      ((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C) = 1 / 4 := by
  have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
  rw [normalized_haar_moment q d R.1 hd R.1.isLt,
    normalized_haar_moment q (q + 1 - d) R.2 hvd R.2.isLt]
  have hm := halfSize_mul_complement q d hd
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  rw [pow_q_add_two]
  push_cast
  have hmR : (halfSize q d : ℝ) * (halfSize q (q + 1 - d) : ℝ) =
      (2 ^ (q + 1) : ℕ) := by exact_mod_cast hm
  field_simp
  rw [← mul_pow, hmR]
  norm_cast
  rw [pow_succ]
  ring

private lemma rawGridDisc_rectHaar_sum
    (y : ℕ → ℝ) (lam : ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * rectHaar q d R A C = -lam / 4 := by
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * rectHaar q d R A C) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
        gridCount y q A C * rectHaar q d R A C) - lam *
        ((∑ A ∈ Finset.range (2 ^ (q + 2)),
          ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
        (∑ C ∈ Finset.range (2 ^ (q + 2)),
          ((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C)) by
    simp only [gridDiscrepancy, rectHaar]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = lam * ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            (((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
            (((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C hC
              ring
      _ = _ := by
        rw [Finset.sum_mul_sum]
        ]
  rw [rawCount_rectHaar_sum_eq_zero y q d hd R hR,
    normalized_moments_product q d hd R]
  ring

private lemma rawDisc_testFunction_sum (y : ℕ → ℝ) (lam : ℝ) (q : ℕ) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * testFunction y q A C =
        -((taggedEmpty y q).card : ℝ) * lam / 4 := by
  classical
  simp only [testFunction]
  simp_rw [Finset.mul_sum]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      ∑ T ∈ taggedEmpty y q,
        gridDiscrepancy y lam q A C * taggedHaar q T A C) =
      ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
        ∑ C ∈ Finset.range (2 ^ (q + 2)),
          gridDiscrepancy y lam q A C * taggedHaar q T A C by
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ T ∈ taggedEmpty y q,
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            gridDiscrepancy y lam q A C * taggedHaar q T A C := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]]
  rw [taggedEmpty, Finset.sum_sigma]
  simp only [taggedHaar]
  calc
    _ = ∑ d ∈ (Finset.univ : Finset (Fin (q + 2))),
        ∑ _R ∈ emptyRects y q d, -lam / 4 := by
          apply Finset.sum_congr rfl
          intro d hdmem
          apply Finset.sum_congr rfl
          intro R hR
          exact rawGridDisc_rectHaar_sum y lam q d (by omega) R hR
    _ = (∑ d ∈ (Finset.univ : Finset (Fin (q + 2))),
        ((emptyRects y q d).card : ℝ)) * (-lam / 4) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          simp
    _ = _ := by
      rw [← Nat.cast_sum, ← Finset.card_sigma]
      ring

/-- The finite-grid form of Roth's orthogonal-function argument used for
Erdős Problem 255.  `gridCount y q A C` counts the first `2^q` points in
the anchored rectangle `[0,A/Q) × [0,C/Q)`, where `Q=2^(q+2)` and the second
coordinate of point `n` is `n/2^q`. -/
theorem finite_roth_grid (y : ℕ → ℝ) (lam B : ℝ) (q : ℕ)
    (hlam : 0 ≤ lam) (hB0 : 0 ≤ B)
    (hB : ∀ A C, A < 2 ^ (q + 2) → C < 2 ^ (q + 2) →
      abs (gridDiscrepancy y lam q A C) ≤ B) :
    ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤
      4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 := by
  classical
  let Q : ℕ := 2 ^ (q + 2)
  let M : ℕ := 2 ^ q
  let E : ℕ := (taggedEmpty y q).card
  have hMpos : (0 : ℝ) < M := by
    dsimp [M]
    positivity
  have hE_nat : (q + 2) * M ≤ E := by
    simpa [M, E] using taggedEmpty_card_ge y q
  have hE : (((q + 2) * M : ℕ) : ℝ) ≤ E := by exact_mod_cast hE_nat
  have hEpos : (0 : ℝ) < E := by
    have : 0 < (q + 2) * M := by dsimp [M]; positivity
    exact lt_of_lt_of_le (by exact_mod_cast this) hE
  have hGsquare :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        gridDiscrepancy y lam q p.1 p.2 ^ 2 ≤ (Q : ℝ) ^ 2 * B ^ 2 := by
    calc
      _ ≤ ∑ _p ∈ (Finset.range Q ×ˢ Finset.range Q), B ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have habs := hB p.1 p.2 (by simpa [Q] using Finset.mem_range.mp hp'.1)
          (by simpa [Q] using Finset.mem_range.mp hp'.2)
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hB0).mpr habs
      _ = (Q : ℝ) ^ 2 * B ^ 2 := by
        simp [Q, pow_two]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range Q ×ˢ Finset.range Q)
    (fun p ↦ gridDiscrepancy y lam q p.1 p.2)
    (fun p ↦ testFunction y q p.1 p.2)
  have hpair :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        gridDiscrepancy y lam q p.1 p.2 * testFunction y q p.1 p.2 =
          -(E : ℝ) * lam / 4 := by
    rw [Finset.sum_product]
    simpa [Q, E] using rawDisc_testFunction_sum y lam q
  have hFnorm :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        testFunction y q p.1 p.2 ^ 2 = (E : ℝ) * (8 * M) := by
    rw [Finset.sum_product]
    simpa [Q, M, E] using testFunction_sq_sum y q
  rw [hpair, hFnorm] at hCS
  have hQeq : (Q : ℝ) = 4 * M := by
    dsimp [Q, M]
    rw [pow_q_add_two]
    norm_cast
  have hcore : (E : ℝ) * ((E : ℝ) * lam ^ 2) ≤
      (E : ℝ) * (2048 * (M : ℝ) ^ 3 * B ^ 2) := by
    calc
      (E : ℝ) * ((E : ℝ) * lam ^ 2) = 16 * (-(E : ℝ) * lam / 4) ^ 2 := by ring
      _ ≤ 16 * (((Q : ℝ) ^ 2 * B ^ 2) * ((E : ℝ) * (8 * M))) := by
        gcongr
        exact hCS.trans (mul_le_mul_of_nonneg_right hGsquare (by positivity))
      _ = (E : ℝ) * (2048 * (M : ℝ) ^ 3 * B ^ 2) := by rw [hQeq]; ring
  have hcancel : (E : ℝ) * lam ^ 2 ≤ 2048 * (M : ℝ) ^ 3 * B ^ 2 :=
    (mul_le_mul_iff_of_pos_left hEpos).mp hcore
  have hlower : (((q + 2) * M : ℕ) : ℝ) * lam ^ 2 ≤ (E : ℝ) * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hE (sq_nonneg lam)
  have hpre : ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤
      2048 * (M : ℝ) ^ 2 * B ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hMpos).mp
    calc
      (M : ℝ) * (((q + 2 : ℕ) : ℝ) * lam ^ 2) =
          (((q + 2) * M : ℕ) : ℝ) * lam ^ 2 := by push_cast; ring
      _ ≤ (E : ℝ) * lam ^ 2 := hlower
      _ ≤ 2048 * (M : ℝ) ^ 3 * B ^ 2 := hcancel
      _ = (M : ℝ) * (2048 * (M : ℝ) ^ 2 * B ^ 2) := by ring
  calc
    ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤ 2048 * (M : ℝ) ^ 2 * B ^ 2 := hpre
    _ ≤ 4096 * (M : ℝ) ^ 2 * B ^ 2 := by
      have hnon : 0 ≤ (M : ℝ) ^ 2 * B ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith
    _ = 4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 := by rfl

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos255/NoUniform.lean` -/

section
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


open Filter Finset Set
open scoped BigOperators



noncomputable section

private def timeCut (C : ℕ) : ℕ := (C + 3) / 4

private lemma pow_q_add_two' (q : ℕ) : 2 ^ (q + 2) = 4 * 2 ^ q := by
  rw [pow_add]
  norm_num
  ring

private lemma time_lt_iff (q C n : ℕ) :
    (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) ↔ n < timeCut C := by
  have hM : (0 : ℝ) < (2 ^ q : ℕ) := by positivity
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  rw [div_lt_div_iff₀ hM hQ]
  norm_cast
  rw [pow_q_add_two']
  have hp : 0 < 2 ^ q := by positivity
  constructor
  · intro h
    have : 4 * n < C := by
      apply (Nat.mul_lt_mul_right hp).mp
      nlinarith
    simp only [timeCut]
    omega
  · intro h
    have hfour : 4 * n < C := by
      simp only [timeCut] at h
      omega
    calc
      n * (4 * 2 ^ q) = (4 * n) * 2 ^ q := by ring
      _ < C * 2 ^ q := (Nat.mul_lt_mul_right hp).mpr hfour

private lemma timeCut_le (q C : ℕ) (hC : C < 2 ^ (q + 2)) : timeCut C ≤ 2 ^ q := by
  rw [pow_q_add_two'] at hC
  simp only [timeCut]
  omega

private lemma timeCut_error (q C : ℕ) :
    |(timeCut C : ℝ) - (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((2 ^ (q + 2) : ℕ) : ℝ)))| ≤ 1 := by
  rw [pow_q_add_two']
  have heq : (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((4 * 2 ^ q : ℕ) : ℝ))) = C / 4 := by
    push_cast
    field_simp
  rw [show (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((4 * 2 ^ q : ℕ) : ℝ))) = C / 4 from heq]
  simp only [timeCut]
  have hlo : (C : ℝ) / 4 ≤ ((C + 3) / 4 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    norm_cast
    omega
  have hhi : (((C + 3) / 4 : ℕ) : ℝ) ≤ (C : ℝ) / 4 + 1 := by
    have hn : ((C + 3) / 4) * 4 ≤ C + 4 := by omega
    have hr : ((((C + 3) / 4) * 4 : ℕ) : ℝ) ≤ C + 4 := by exact_mod_cast hn
    push_cast at hr
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma gridCount_eq_prefixCount (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (q A C : ℕ) (hC : C < 2 ^ (q + 2)) :
    gridCount y q A C = prefixCount y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) := by
  have hK := timeCut_le q C hC
  rw [gridCount]
  have hcast : (prefixCount y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) : ℝ) =
      ∑ n ∈ range (timeCut C),
        if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0 := by
    rw [sum_boole]
    simp [prefixCount]
  rw [hcast]
  calc
    ∑ n ∈ range (2 ^ q),
        (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
        (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ)
          then 1 else 0) =
      ∑ n ∈ range (2 ^ q), if n < timeCut C then
        (if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0) else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [time_lt_iff]
      have hyn := (hy n).1
      split_ifs <;> simp_all <;> linarith
    _ = ∑ n ∈ range (timeCut C), if n < timeCut C then
        (if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0) else 0 := by
      symm
      apply sum_subset
      · intro n hn
        simp only [Finset.mem_range] at hn ⊢
        omega
      · intro n hnM hnK
        simp only [Finset.mem_range] at hnM hnK
        simp [hnK]
    _ = ∑ n ∈ range (timeCut C),
        if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [hn]

private lemma gridDiscrepancy_eq (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (q A C : ℕ) (hC : C < 2 ^ (q + 2)) :
    gridDiscrepancy y (2 ^ q : ℕ) q A C =
      starDisc y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
        ((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) *
          ((A : ℝ) / (2 ^ (q + 2) : ℕ)) := by
  rw [gridDiscrepancy, gridCount_eq_prefixCount y hy q A C hC]
  unfold starDisc
  ring

private lemma gridDiscrepancy_abs_le (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (B : ℝ)
    (hB : ∀ N u, u ∈ Icc (0 : ℝ) 1 → |starDisc y N u| ≤ B)
    (q A C : ℕ) (hA : A < 2 ^ (q + 2)) (hC : C < 2 ^ (q + 2)) :
    |gridDiscrepancy y (2 ^ q : ℕ) q A C| ≤ B + 1 := by
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  let u : ℝ := (A : ℝ) / (2 ^ (q + 2) : ℕ)
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [u]; positivity
    · dsimp [u]
      apply (div_le_one hQ).mpr
      exact_mod_cast hA.le
  rw [gridDiscrepancy_eq y hy q A C hC]
  calc
    |starDisc y (timeCut C) u +
        ((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) * u| ≤
      |starDisc y (timeCut C) u| +
        |((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) * u| := abs_add_le _ _
    _ ≤ B + 1 := by
      rw [abs_mul]
      have he := timeCut_error q C
      have huabs : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
      nlinarith [hB (timeCut C) u hu, abs_nonneg u]

/-- No sequence in `[0,1)` has uniformly bounded anchored discrepancy. -/
theorem no_uniform_star_discrepancy (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (B : ℝ) :
    ∃ N : ℕ, ∃ u ∈ Icc (0 : ℝ) 1, B < |starDisc y N u| := by
  by_cases hBneg : B < 0
  · exact ⟨0, 0, by simp, by simpa [starDisc, prefixCount] using hBneg⟩
  have hB0 : 0 ≤ B := le_of_not_gt hBneg
  by_contra hlarge
  push_neg at hlarge
  obtain ⟨q, hq⟩ := exists_nat_gt (4096 * (B + 1) ^ 2)
  let M : ℝ := (2 ^ q : ℕ)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hroth := finite_roth_grid y M (B + 1) q hMpos.le (by linarith)
    (fun A C hA hC ↦ gridDiscrepancy_abs_le y hy B hlarge q A C hA hC)
  have hcancel : ((q + 2 : ℕ) : ℝ) ≤ 4096 * (B + 1) ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hMpos)).mp
    calc
      ((q + 2 : ℕ) : ℝ) * M ^ 2 ≤ 4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * (B + 1) ^ 2 := hroth
      _ = (4096 * (B + 1) ^ 2) * M ^ 2 := by dsimp [M]; ring
  have hqR : 4096 * (B + 1) ^ 2 < (q : ℝ) := hq
  norm_num [Nat.cast_add, Nat.cast_ofNat] at hcancel
  linarith

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos255.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 255.
https://www.erdosproblems.com/forum/thread/255

Informal authors:
- Wolfgang M. Schmidt

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos255.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Erdős Problem 255

For every sequence in `[0,1]`, some interval has unbounded discrepancy.  We
prove the stronger form established by Schmidt: the interval may be chosen to
be an anchored half-open interval `[0,x)`.

The proof has three parts.  `FiniteRoth.lean` proves a finite two-dimensional
Roth inequality by exact sums of dyadic Haar functions.  `NoUniform.lean`
deduces that no sequence in `[0,1)` has uniformly bounded anchored
discrepancy.  `Baire.lean` localizes a hypothetical pointwise bound by the
Baire category theorem, extends it one-sidedly across the countable set of
sequence values, and rescales the resulting local subsequence.  The detailed
mathematical proof and Leanization map are in `tex/255.tex`.

The interval convention is half open.  This is harmless for the problem and,
more importantly, the theorem below explicitly counts membership in `[0,x)`;
there is no endpoint-convention abstraction hidden in the statement.
-/

open Filter Finset Set
open scoped BigOperators Topology



/-- Discrepancy of the first `N` terms in the actual interval `[0,x)`. -/
noncomputable def anchoredDiscrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (((range N).filter fun n ↦ z n ∈ Ico (0 : ℝ) x).card : ℝ) - N * x

lemma baire_prefixCount_eq (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    Erdos255Baire.prefixCount z N x = prefixCount z N x := by
  rw [Erdos255Baire.prefixCount, Nat.count_eq_card_filter_range, prefixCount]

lemma baire_discrepancy_eq (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    Erdos255Baire.discrepancy z N x = starDisc z N x := by
  unfold Erdos255Baire.discrepancy starDisc
  rw [baire_prefixCount_eq]

lemma anchoredDiscrepancy_eq_starDisc (z : ℕ → ℝ)
    (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) (N : ℕ) (x : ℝ) :
    anchoredDiscrepancy z N x = starDisc z N x := by
  unfold anchoredDiscrepancy starDisc prefixCount
  congr 2
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico]
  constructor
  · rintro ⟨hn, hzero, hx⟩
    exact ⟨hn, hx⟩
  · rintro ⟨hn, hx⟩
    exact ⟨hn, (hz n).1, hx⟩

/-- The Baire theorem applies because the finite Roth argument rules out a
uniformly bounded star discrepancy after every local rescaling. -/
lemma noUniformStarDiscrepancy : Erdos255Baire.NoUniformStarDiscrepancy := by
  intro w hw C
  obtain ⟨N, x, hx, hlarge⟩ := no_uniform_star_discrepancy w hw C
  refine ⟨N, x, hx, ?_⟩
  rwa [baire_discrepancy_eq]

/-- Quantitative form used to obtain the limsup statement: an anchored
interval `[0,x)` has discrepancy exceeding every prescribed real bound. -/
theorem erdos_255_unbounded (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∀ C : ℝ, ∃ N : ℕ,
      C < |anchoredDiscrepancy z N x| := by
  obtain ⟨x, hx, hub⟩ :=
    Erdos255Baire.unbounded_endpoint_of_no_uniform noUniformStarDiscrepancy z
  refine ⟨x, hx, ?_⟩
  intro C
  obtain ⟨N, hN⟩ := hub C
  refine ⟨N, ?_⟩
  rwa [anchoredDiscrepancy_eq_starDisc z hz,
    ← baire_discrepancy_eq]

private lemma frequently_gt_of_unbounded (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : ∀ C : ℝ, ∃ n, C < f n) (C : ℝ) : ∃ᶠ n in atTop, C < f n := by
  rw [frequently_atTop]
  intro a
  obtain ⟨n, hn⟩ := h (max C (∑ i ∈ range a, f i))
  refine ⟨n, ?_, lt_of_le_of_lt (le_max_left _ _) hn⟩
  by_contra hna
  have hnmem : n ∈ range a := by simp_all
  have hnle : f n ≤ ∑ i ∈ range a, f i :=
    single_le_sum (fun i _ ↦ hf i) hnmem
  exact (not_lt_of_ge hnle) (lt_of_le_of_lt (le_max_right _ _) hn)

/-- An unbounded nonnegative real sequence has extended-real limsup `⊤`. -/
private lemma limsup_coe_eq_top_of_unbounded (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : ∀ C : ℝ, ∃ n, C < f n) :
    atTop.limsup (fun n ↦ (f n : EReal)) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro C
  have hfreq : ∃ᶠ n in atTop, (C + 1 : EReal) ≤ (f n : EReal) := by
    rw [frequently_atTop]
    intro a
    obtain ⟨n, han, hn⟩ := (frequently_atTop.mp
      (frequently_gt_of_unbounded f hf h (C + 1))) a
    refine ⟨n, han, ?_⟩
    norm_cast
    linarith
  refine lt_of_lt_of_le ?_ (le_limsup_of_frequently_le' hfreq)
  norm_cast
  linarith

/-- **Erdős Problem 255 (Schmidt).**  For every sequence in `[0,1]`, there
is an interval `[0,x) ⊆ [0,1]` for which the limsup of the absolute
discrepancy is infinite. -/
theorem erdos_255 (z : ℕ → ℝ) (hz : ∀ n, z n ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      Ico (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 ∧
      atTop.limsup (fun N ↦ ((|anchoredDiscrepancy z N x| : ℝ) : EReal)) = ⊤ := by
  obtain ⟨x, hx, hub⟩ := erdos_255_unbounded z hz
  refine ⟨x, hx, ?_, limsup_coe_eq_top_of_unbounded
    (fun N ↦ |anchoredDiscrepancy z N x|) (fun _ ↦ abs_nonneg _) hub⟩
  intro y hy
  exact ⟨hy.1, hy.2.le.trans hx.2⟩

end

#print axioms erdos_255
-- 'Erdos255.erdos_255' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos255
