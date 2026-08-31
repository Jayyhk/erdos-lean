import Mathlib

set_option linter.dupNamespace false

namespace Erdos13

/-
# Problem Description

Erdős Problem 13. Let `A ⊆ {1, …, N}` contain no `a, b, c ∈ A` with `a ∣ (b + c)` and
`a < min(b, c)`. Is it true that `|A| ≤ N/3 + O(1)`? `erdos_13` proves that it is.

Asked by Erdős and Sárközy, who observed that `(2N/3, N] ∩ ℕ` is such a set, so the `N/3` is
sharp. The `O(1)` is rendered below as a single constant `C : ℝ` independent of `N`, and the
hypothesis on `A` is `IsForbiddenTripleFree`:
`∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬ a ∣ b + c`.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos13.lean` together with the modules of
`src/latest/ErdosProblems/Erdos13/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, and the whole wrapped
once in `namespace Erdos13` with the upstream trust-base print line removed. No mathematical
content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos13/Erdos13MulStab.lean` -/

section
/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/

/-!
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `Finset.mulStab`: The stabilizer of a **nonempty** finset as a finset.
-/

open Function MulAction
open scoped Pointwise

section
open Finset
variable {ι α : Type*}

local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/
@[to_additive /-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/]
private def _root_.Finset.mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

@[to_additive (attr := simp)]
private lemma _root_.Finset.mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

@[to_additive]
private lemma _root_.Finset.mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

@[to_additive]
private lemma _root_.Finset.mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[to_additive (attr := simp)]
private lemma _root_.Finset.coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

@[to_additive]
private lemma _root_.Finset.mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

@[to_additive]
private lemma _root_.Finset.mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

@[to_additive]
private lemma _root_.Finset.mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

@[to_additive]
private lemma _root_.Finset.Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[to_additive (attr := simp)]
private lemma _root_.Finset.one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

@[to_additive] protected alias ⟨_, _root_.Finset.Nonempty.one_mem_mulStab⟩ := one_mem_mulStab

@[to_additive]
private lemma _root_.Finset.Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, h.one_mem_mulStab⟩

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Finset.Nonempty.of_mulStab, Finset.Nonempty.mulStab⟩

@[to_additive (attr := simp)]
private lemma _root_.Finset.card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

@[to_additive]
private lemma _root_.Finset.Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton h.one_mem_mulStab

@[to_additive]
private lemma _root_.Finset.subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

@[to_additive]
private lemma _root_.Finset.mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

@[to_additive]
private lemma _root_.Finset.mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

@[to_additive]
private lemma _root_.Finset.smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

@[to_additive]
private lemma _root_.Finset.inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (hs.mono subset_union_left), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
private lemma _root_.Finset.mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine fun b hb ↦ mem_div.2 ⟨_, mem_singleton_self _, _, ?_, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

@[to_additive]
private lemma _root_.Finset.subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[to_additive (attr := simp)]
private lemma _root_.Finset.mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[to_additive (attr := simp)]
private lemma _root_.Finset.mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

@[to_additive]
private lemma _root_.Finset.smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

@[to_additive]
private lemma _root_.Finset.mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

@[to_additive]
private lemma _root_.Finset.mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

@[to_additive (attr := simp)]
private lemma _root_.Finset.mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

@[to_additive]
private lemma _root_.Finset.mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

@[to_additive]
private lemma _root_.Finset.preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' (s +ˢ stabilizer α (t : Set α)) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

omit [DecidableEq α] in
@[to_additive]
private lemma _root_.Finset.preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' (s +ˢ stabilizer α (s : Set α)) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

@[to_additive]
private lemma _root_.Finset.pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

@[to_additive]
private lemma _root_.Finset.disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

@[to_additive]
private lemma _root_.Finset.card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

@[to_additive]
private lemma _root_.Finset.card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

@[to_additive]
private lemma _root_.Finset.card_mulStab_le_card : #s.mulStab ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/
@[to_additive (attr := implicit_reducible)
/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.addStab`. -/]
private def _root_.Finset.fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

@[to_additive]
private lemma _root_.Finset.card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  letI : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  letI : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

/-- A version of Lagrange's theorem. -/
@[to_additive /-- A version of Lagrange's theorem. -/]
private lemma _root_.Finset.card_mulStab_mul_card_image_coe' (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(s +ₛ stabilizer α (t : Set α)) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ (s +ˢ stabilizer α (t : Set α))
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp

@[to_additive]
private lemma _root_.Finset.card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((s * t) +ₛ stabilizer α (↑(s * t) : Set α)) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    ↑(s * t) +ˢ stabilizer α (↑(s * t) : Set α)
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp

/-- A version of Lagrange's theorem. -/
@[to_additive /-- A version of Lagrange's theorem. -/]
private lemma _root_.Finset.card_mulStab_mul_card_image_coe (s t : Finset α) :
    #(s * t).mulStab *
      #((s +ₛ stabilizer α (↑(s * t) : Set α)) * (t +ₛ stabilizer α (↑(s * t) : Set α))) =
        #(s * t) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  let this := QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (↑(s * t) : Set α))
    ((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))
  have image_coe_mul :
    ((↑(s * t) : Set α) +ˢ stabilizer α (↑(s * t) : Set α)) =
      (s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)) := by
    simpa [coe_mul] using Set.image_mul (QuotientGroup.mk' (stabilizer α (↑(s * t) : Set α)))
  rw [← image_coe_mul, preimage_image_quotientMk_mulStabilizer, image_coe_mul] at this
  have that :
    (stabilizer α (↑(s * t) : Set α) ×
      ↥((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))) =
      ((s * t).mulStab ×
        ↥((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))) := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  let temp := this.trans (Equiv.cast that)
  replace temp := Fintype.card_congr temp
  simp only [Fintype.card_prod, Fintype.card_coe] at temp
  have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  have h2 : (s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)) =
    ↑((s +ₛ stabilizer α (↑(s * t) : Set α)) * (t +ₛ stabilizer α (↑(s * t) : Set α))) := by simp
  have h3 :
    Fintype.card ((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α))) =
      Fintype.card ((s +ₛ stabilizer α (↑(s * t) : Set α)) *
        (t +ₛ stabilizer α (↑(s * t) : Set α))) := by
    simp_rw [h2]
    congr
  simp only [h1, h3, Fintype.card_coe] at temp
  rw [temp]

@[to_additive]
private lemma _root_.Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #(t +ₛ s) = #t := by
  suffices h : (t : Set α) * s = t by
    simpa [h, eq_comm] using s.card_mul_eq_card_subgroup_mul_card_quotient  t
  apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
  · intro x
    rw [Set.mem_mul]
    aesop
  · rw [← coe_mul, mul_mulStab]

@[to_additive]
private lemma _root_.Finset.mulStab_quotient_commute_subgroup (s : Subgroup α) [DecidablePred (· ∈ s)] (t : Finset α)
    (hst : (s : Set α) ⊆ t.mulStab) : (t.mulStab +ₛ s) = (t +ₛ s).mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have hti : (image (QuotientGroup.mk (s := s)) t).Nonempty := by aesop
  ext x;
  simp only [mem_image, mem_mulStab hti]
  constructor
  · rintro ⟨a, hax⟩
    rw [← hax.2]
    ext z
    simp only [mem_smul_finset, mem_image, smul_eq_mul, exists_exists_and_eq_and]
    constructor
    · rintro ⟨b, hbt, hbaz⟩
      use (b * a)
      rw [← mul_mulStab t]
      refine ⟨mul_mem_mul hbt hax.1, ?_⟩
      rw [← hbaz, QuotientGroup.mk_mul, mul_comm]
    · rintro ⟨b, hbt, hbz⟩
      rw [← hbz, ← mul_mulStab t, mul_comm]
      use a⁻¹ * b
      refine ⟨mul_mem_mul ?_ hbt, by simp⟩
      rw [← mem_coe, coe_mulStab ht]
      aesop
  · intro hx
    have : s ≤ stabilizer α t := by aesop
    obtain ⟨y, hyx⟩ := Quotient.exists_rep x
    refine ⟨y, (mem_mulStab_iff_subset_smul_finset ht).mpr ?_, by simpa⟩
    intros z hzt
    replace hx : image QuotientGroup.mk (y • t) = image (QuotientGroup.mk (s := s)) t := by
      rw [← hx, ← hyx]
      exact image_smul_comm QuotientGroup.mk y t (congrFun rfl)
    have hyz : QuotientGroup.mk z ∈ image (QuotientGroup.mk (s := s)) (y • t) := by aesop
    simp only [mem_image] at hyz
    obtain ⟨a, ha, hayz⟩ := hyz
    obtain ⟨b, hbt, haby⟩ := mem_smul_finset.mp ha
    subst a
    rw [QuotientGroup.eq, smul_eq_mul] at hayz
    replace : ∃ c ∈ mulStab t, (y • b)⁻¹ * z = c := by aesop
    obtain ⟨c, hct, hcbyz⟩ := this
    rw [inv_mul_eq_iff_eq_mul] at hcbyz
    rw [hcbyz, smul_mul_assoc, mul_comm, ← smul_eq_mul]
    exact smul_mem_smul_finset ((mem_mulStab' ht).mp hct hbt)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos13/Erdos13Kneser.lean` -/

section
/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/

/-!
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `Finset.mul_kneser`: Kneser's theorem.
* `Finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/

open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

section
open Finset

/-! ### Auxiliary results -/

@[to_additive]
private lemma _root_.Finset.mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst

@[to_additive]
private lemma _root_.Finset.mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose! hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

@[to_additive]
private lemma _root_.Finset.mul_aux1
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

@[to_additive]
private lemma _root_.Finset.disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose! has
  exact subset_trans has hst

@[to_additive]
private lemma _root_.Finset.disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose! hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose! hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

@[to_additive]
private lemma _root_.Finset.inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
            #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
          #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
        #(a • C.mulStab \
            ((s ∩ a • C.mulStab ∪ t ∩ a • C.mulStab) *
              (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset, Int.ofNat_sub (card_le_card _), card_smul_finset]
      · grw [union_mul, le_sub_iff_add_le, card_union_le]
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose! hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

@[to_additive]
private lemma _root_.Finset.card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs

/-! ### Kneser's theorem -/

variable (s t)

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/
@[to_additive /-- **Kneser's addition theorem**: A lower bound on the size of `s + t` in terms of
its stabilizer. -/]
private theorem _root_.Finset.mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_setOf_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 hC.one_mem_mulStab)
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/
@[to_additive /-- The strict version of **Kneser's addition theorem**. If the LHS of
`Finset.add_kneser` does not equal the RHS, then it is in fact much smaller. -/]
private lemma _root_.Finset.mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos13/Erdos13Additive.lean` -/

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

/-!
# The additive-combinatorial lemma used for Erdős Problem 13

This file contains a finitary proof of the strict form of the
Bardaji--Grynkiewicz alternative needed in Bedert's argument.  The proof is
split into two parts.  First, the stable-hole argument proves that two
normalized subsets of integer intervals have a long interval in their
sumset once the larger diameter is at most the sum of their cardinalities
minus three.  Second, Kneser's theorem applied modulo the larger diameter
supplies this diameter estimate when the cardinality-growth alternative
fails.
-/

open Finset Nat
open scoped Pointwise

namespace Erdos13Additive

/-! ## Elementary hole counts -/

/-- Holes of `S` in the natural interval `[0,M]`. -/
def holes (S : Finset ℕ) (M : ℕ) : Finset ℕ := Icc 0 M \ S

@[simp] lemma mem_holes {S : Finset ℕ} {M x : ℕ} :
    x ∈ holes S M ↔ x ≤ M ∧ x ∉ S := by
  simp [holes]

lemma card_holes {S : Finset ℕ} {M : ℕ} (hS : S ⊆ Icc 0 M) :
    (holes S M).card = M + 1 - S.card := by
  rw [holes, card_sdiff_of_subset hS]
  simp

/-- Holes restricted to a closed subinterval. -/
def holesIcc (S : Finset ℕ) (a b : ℕ) : Finset ℕ := Icc a b \ S

@[simp] lemma mem_holesIcc {S : Finset ℕ} {a b x : ℕ} :
    x ∈ holesIcc S a b ↔ a ≤ x ∧ x ≤ b ∧ x ∉ S := by
  simp only [holesIcc, mem_sdiff, mem_Icc]
  aesop

lemma holesIcc_subset_holes {S : Finset ℕ} {M a b : ℕ}
    (ha : a ≤ b) (hb : b ≤ M) : holesIcc S a b ⊆ holes S M := by
  intro x hx
  have hx' := mem_holesIcc.mp hx
  exact mem_holes.mpr ⟨hx'.2.1.trans hb, hx'.2.2⟩

lemma card_holesIcc_le_card_holes {S : Finset ℕ} {M a b : ℕ}
    (ha : a ≤ b) (hb : b ≤ M) :
    (holesIcc S a b).card ≤ (holes S M).card :=
  card_le_card (holesIcc_subset_holes ha hb)

lemma card_holesIcc_le_length {S : Finset ℕ} {a b : ℕ} :
    (holesIcc S a b).card ≤ b + 1 - a := by
  exact (card_le_card sdiff_subset).trans_eq (by simp)

/-- Two interval hole counts are bounded by the total hole count plus the
hole count in the overlap.  This is the inclusion--exclusion estimate used
in the stable-hole argument. -/
lemma card_holesIcc_add_le_total_add_overlap {S : Finset ℕ} {M a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d) (hbM : b ≤ M) (hdM : d ≤ M) :
    (holesIcc S a b).card + (holesIcc S c d).card ≤
      (holes S M).card + (holesIcc S (max a c) (min b d)).card := by
  let X := holesIcc S a b
  let Y := holesIcc S c d
  have hXY : X ∪ Y ⊆ holes S M := by
    exact union_subset (holesIcc_subset_holes hab hbM)
      (holesIcc_subset_holes hcd hdM)
  have hinter : X ∩ Y ⊆ holesIcc S (max a c) (min b d) := by
    intro x hx
    have hxX := mem_holesIcc.mp (mem_of_mem_inter_left hx)
    have hxY := mem_holesIcc.mp (mem_of_mem_inter_right hx)
    exact mem_holesIcc.mpr ⟨by omega, by omega, hxX.2.2⟩
  have hcardUnion := card_le_card hXY
  have hcardInter := card_le_card hinter
  have hident : (X ∪ Y).card + (X ∩ Y).card =
      (holesIcc S a b).card + (holesIcc S c d).card := by
    simpa [X, Y] using card_union_add_card_inter X Y
  omega

/-! ## The normalized long-interval theorem -/

/-- The holes of a normalized sumset in its full ambient interval. -/
def sumHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  Icc 0 (M + N) \ (A + B)

/-- Left-stable holes of `B`. -/
def leftStable (A B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (holes B N).filter fun x ↦ x ∉ A + B

/-- Right-stable holes of `B`, where `M` is the maximum of `A`. -/
def rightStable (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  (holes B N).filter fun x ↦ x + M ∉ A + B

def stableHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  leftStable A B N ∪ rightStable A B M N

def unstableHoles (A B : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  holes B N \ stableHoles A B M N

@[simp] lemma mem_leftStable {A B : Finset ℕ} {N x : ℕ} :
    x ∈ leftStable A B N ↔ x ≤ N ∧ x ∉ B ∧ x ∉ A + B := by
  simp only [leftStable, mem_filter, mem_holes]
  aesop

@[simp] lemma mem_rightStable {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ rightStable A B M N ↔
      x ≤ N ∧ x ∉ B ∧ x + M ∉ A + B := by
  simp only [rightStable, mem_filter, mem_holes]
  aesop

@[simp] lemma mem_stableHoles {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ stableHoles A B M N ↔
      x ∈ leftStable A B N ∨ x ∈ rightStable A B M N := by
  simp [stableHoles]

@[simp] lemma mem_unstableHoles {A B : Finset ℕ} {M N x : ℕ} :
    x ∈ unstableHoles A B M N ↔
      x ≤ N ∧ x ∉ B ∧ x ∉ stableHoles A B M N := by
  simp only [unstableHoles, mem_sdiff, mem_holes]
  aesop

/-- If a sum below the smaller diameter is absent, the two prefixes contain
at least as many holes as there are candidate representations. -/
lemma prefix_hole_count {A B : Finset ℕ} {M N x : ℕ}
    (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N) (hxN : x ≤ N)
    (hx : x ∉ A + B) :
    x + 1 ≤ (holesIcc A 0 x).card + (holesIcc B 0 x).card := by
  let U := Icc 0 x
  let X := U.filter fun b ↦ x - b ∉ A
  let Y := holesIcc B 0 x
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : x - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hx
        have heq : x - b + b = x := Nat.sub_add_cancel hb'.2
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holesIcc.mpr ⟨by omega, hb'.2, hbB⟩)
    · exact mem_union_left _ (by simpa [X, U, hb, ha])
  have hX : X.image (fun b ↦ x - b) ⊆ holesIcc A 0 x := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    exact mem_holesIcc.mpr ⟨by omega, Nat.sub_le _ _, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ x - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change x - b = x - c at hbc
    omega
  have hXcard : X.card ≤ (holesIcc A 0 x).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  change x + 1 ≤ _
  have hUcard : U.card = x + 1 := by simp [U]
  rw [hUcard] at hcoverCard
  change (X ∪ Y).card ≤ X.card + (holesIcc B 0 x).card at hunionCard
  omega

/-- The reflected version of `prefix_hole_count` for a missing sum at the
right end of the ambient sum interval. -/
lemma suffix_hole_count {A B : Finset ℕ} {M N z : ℕ}
    (hMN : N ≤ M) (hzM : M ≤ z) (hzMN : z ≤ M + N)
    (hz : z ∉ A + B) :
    M + N - z + 1 ≤
      (holesIcc A (z - N) M).card + (holesIcc B (z - M) N).card := by
  let U := Icc (z - M) N
  let X := U.filter fun b ↦ z - b ∉ A
  let Y := holesIcc B (z - M) N
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : z - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hz
        have hbz : b ≤ z := by omega
        have heq : z - b + b = z := Nat.sub_add_cancel hbz
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holesIcc.mpr ⟨hb'.1, hb'.2, hbB⟩)
    · exact mem_union_left _ (by simpa [X, U, hb, ha])
  have hX : X.image (fun b ↦ z - b) ⊆ holesIcc A (z - N) M := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    have hbU := mem_Icc.mp hb'.1
    exact mem_holesIcc.mpr ⟨by omega, by omega, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ z - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change z - b = z - c at hbc
    have hbz : b ≤ z := by omega
    have hcz : c ≤ z := by omega
    omega
  have hXcard : X.card ≤ (holesIcc A (z - N) M).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  have hUcard : U.card = M + N - z + 1 := by
    simp only [U, card_Icc]
    omega
  rw [hUcard] at hcoverCard
  change (X ∪ Y).card ≤ X.card + (holesIcc B (z - M) N).card at hunionCard
  omega

/-- Proposition 4.1 of Bardaji--Grynkiewicz: if the larger-diameter set
has at most `|B|-1` holes, the whole middle interval is in the sumset. -/
lemma middle_interval_subset_sum {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hhole : (holes A M).card + 1 ≤ B.card) :
    Icc N M ⊆ A + B := by
  intro x hx
  have hxI := mem_Icc.mp hx
  by_contra hxsum
  let U := Icc 0 N
  let X := U.filter fun b ↦ x - b ∉ A
  let Y := holes B N
  have hcover : U ⊆ X ∪ Y := by
    intro b hb
    have hb' := mem_Icc.mp hb
    by_cases ha : x - b ∈ A
    · have hbB : b ∉ B := by
        intro hbmem
        apply hxsum
        have hbx : b ≤ x := hb'.2.trans hxI.1
        have heq : x - b + b = x := Nat.sub_add_cancel hbx
        rw [← heq]
        exact Finset.add_mem_add ha hbmem
      exact mem_union_right _ (mem_holes.mpr ⟨hb'.2, hbB⟩)
    · exact mem_union_left _ (by simpa [X, U, hb, ha])
  have hX : X.image (fun b ↦ x - b) ⊆ holes A M := by
    intro a ha
    simp only [mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' := mem_filter.mp hb
    exact mem_holes.mpr ⟨by omega, hb'.2⟩
  have hinj : Set.InjOn (fun b : ℕ ↦ x - b) X := by
    intro b hb c hc hbc
    have hbU := mem_Icc.mp (mem_filter.mp hb).1
    have hcU := mem_Icc.mp (mem_filter.mp hc).1
    change x - b = x - c at hbc
    have hbx : b ≤ x := hbU.2.trans hxI.1
    have hcx : c ≤ x := hcU.2.trans hxI.1
    omega
  have hXcard : X.card ≤ (holes A M).card := by
    rw [← card_image_iff.mpr hinj]
    exact card_le_card hX
  have hcoverCard := card_le_card hcover
  have hunionCard := card_union_le X Y
  have hUcard : U.card = N + 1 := by simp [U]
  have hNcover : N + 1 ≤ X.card + (holes B N).card := by
    calc
      N + 1 = U.card := hUcard.symm
      _ ≤ (X ∪ Y).card := hcoverCard
      _ ≤ X.card + Y.card := hunionCard
      _ = X.card + (holes B N).card := by rfl
  have hBh := card_holes hB
  have hBcard : B.card ≤ N + 1 := by
    simpa using card_le_card hB
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  omega

/-- A hole of `B` cannot be both left- and right-stable under the strict
hole hypothesis. -/
lemma disjoint_left_right {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    Disjoint (leftStable A B N) (rightStable A B M N) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  have hxL' := mem_leftStable.mp hxL
  have hxR' := mem_rightStable.mp hxR
  have hp := prefix_hole_count hA hB hxL'.1 hxL'.2.2
  have hs := suffix_hole_count hMN (by omega) (by omega) hxR'.2.2
  have hs' : N - x + 1 ≤
      (holesIcc A (x + M - N) M).card + (holesIcc B x N).card := by
    have heq : M + N - (x + M) = N - x := by omega
    rw [heq] at hs
    have heq' : x + M - M = x := by omega
    rw [heq'] at hs
    exact hs
  have hAparts := card_holesIcc_add_le_total_add_overlap
    (S := A) (M := M) (a := 0) (b := x) (c := x + M - N) (d := M)
    (by omega) (by omega) (by omega) (by omega)
  have hBparts := card_holesIcc_add_le_total_add_overlap
    (S := B) (M := N) (a := 0) (b := x) (c := x) (d := N)
    (by omega) (by omega) (by omega) (by omega)
  have hAover : (holesIcc A (max 0 (x + M - N)) (min x M)).card ≤ 1 := by
    have hsub : holesIcc A (max 0 (x + M - N)) (min x M) ⊆ {x} := by
      intro y hy
      have hy' := mem_holesIcc.mp hy
      simp only [mem_singleton]
      omega
    exact (card_le_card hsub).trans_eq (by simp)
  have hBover : (holesIcc B (max 0 x) (min x N)).card ≤ 1 := by
    have hsub : holesIcc B (max 0 x) (min x N) ⊆ {x} := by
      intro y hy
      have hy' := mem_holesIcc.mp hy
      simp only [max_eq_right (Nat.zero_le x), min_eq_left hxL'.1] at hy'
      simp only [mem_singleton]
      omega
    exact (card_le_card hsub).trans_eq (by simp)
  have hAh := card_holes hA
  have hBh := card_holes hB
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAhAdd : (holes A M).card + A.card = M + 1 := by omega
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  have hsplit : (x + 1) + (N - x + 1) = N + 2 := by omega
  omega

@[simp] lemma mem_sumHoles {A B : Finset ℕ} {M N z : ℕ} :
    z ∈ sumHoles A B M N ↔ z ≤ M + N ∧ z ∉ A + B := by
  simp [sumHoles]

def stableProjection (M N z : ℕ) : ℕ :=
  if z < N then z else z - M

lemma add_subset_ambient {A B : Finset ℕ} {M N : ℕ}
    (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N) :
    A + B ⊆ Icc 0 (M + N) := by
  intro z hz
  simp only [Finset.mem_add] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have ha' := mem_Icc.mp (hA ha)
  have hb' := mem_Icc.mp (hB hb)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N) :
    (sumHoles A B M N).card = M + N + 1 - (A + B).card := by
  rw [sumHoles, card_sdiff_of_subset (add_subset_ambient hA hB)]
  simp

/-- The missing sums project bijectively to the stable holes of `B`. -/
lemma image_stableProjection_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    (sumHoles A B M N).image (stableProjection M N) =
      stableHoles A B M N := by
  have hmid := middle_interval_subset_sum hMN hA hB (by omega)
  ext x
  constructor
  · intro hx
    simp only [mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' := mem_sumHoles.mp hz
    by_cases hzN : z < N
    · have hzB : z ∉ B := by
        intro hzB
        apply hz'.2
        simpa using Finset.add_mem_add hA0 hzB
      apply mem_stableHoles.mpr
      left
      simpa only [stableProjection, if_pos hzN] using
        (mem_leftStable.mpr ⟨by omega, hzB, hz'.2⟩)
    · have hMz : M < z := by
        by_contra hnot
        have : z ∈ Icc N M := mem_Icc.mpr ⟨by omega, by omega⟩
        exact hz'.2 (hmid this)
      have hzsub : z - M ≤ N := by omega
      have hzB : z - M ∉ B := by
        intro hzB
        apply hz'.2
        have heq : M + (z - M) = z := by omega
        rw [← heq]
        exact Finset.add_mem_add hAM hzB
      apply mem_stableHoles.mpr
      right
      simp only [stableProjection, if_neg hzN]
      have he : z - M + M = z := Nat.sub_add_cancel (by omega)
      exact mem_rightStable.mpr ⟨hzsub, hzB, by simpa [he] using hz'.2⟩
  · intro hx
    rcases mem_stableHoles.mp hx with hxL | hxR
    · have hxL' := mem_leftStable.mp hxL
      have hxN : x < N := by
        by_contra hnot
        have hxEq : x = N := by omega
        subst x
        exact hxL'.2.2 (hmid (mem_Icc.mpr ⟨le_rfl, hMN⟩))
      apply mem_image.mpr
      refine ⟨x, mem_sumHoles.mpr ⟨by omega, hxL'.2.2⟩, ?_⟩
      simp [stableProjection, hxN]
    · have hxR' := mem_rightStable.mp hxR
      let z := x + M
      have hzN : ¬ z < N := by dsimp [z]; omega
      apply mem_image.mpr
      refine ⟨z, mem_sumHoles.mpr ⟨by dsimp [z]; omega, hxR'.2.2⟩, ?_⟩
      simp [stableProjection, z, hzN]

lemma stableProjection_injOn_sumHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    Set.InjOn (stableProjection M N) (sumHoles A B M N) := by
  have hmid := middle_interval_subset_sum hMN hA hB (by omega)
  have hdisj := disjoint_left_right hMN hA hB hhole
  intro z hz w hw heq
  have hz' := mem_sumHoles.mp hz
  have hw' := mem_sumHoles.mp hw
  by_cases hzN : z < N
  · have hzB : z ∉ B := by
      intro hzB
      exact hz'.2 (by simpa using Finset.add_mem_add hA0 hzB)
    have hzL : z ∈ leftStable A B N :=
      mem_leftStable.mpr ⟨by omega, hzB, hz'.2⟩
    by_cases hwN : w < N
    · simpa [stableProjection, hzN, hwN] using heq
    · have hMw : M < w := by
        by_contra hnot
        exact hw'.2 (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
      have hwB : w - M ∉ B := by
        intro hb
        apply hw'.2
        have he : M + (w - M) = w := by omega
        rw [← he]
        exact Finset.add_mem_add hAM hb
      have hwR : w - M ∈ rightStable A B M N :=
        mem_rightStable.mpr ⟨by omega, hwB, by
          have he : w - M + M = w := Nat.sub_add_cancel (by omega)
          simpa [he] using hw'.2⟩
      have hproj : z = w - M := by simpa [stableProjection, hzN, hwN] using heq
      rw [← hproj] at hwR
      exact (Finset.disjoint_left.mp hdisj hzL hwR).elim
  · have hMz : M < z := by
      by_contra hnot
      exact hz'.2 (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
    by_cases hwN : w < N
    · have hwB : w ∉ B := by
        intro hb
        exact hw'.2 (by simpa using Finset.add_mem_add hA0 hb)
      have hwL : w ∈ leftStable A B N :=
        mem_leftStable.mpr ⟨by omega, hwB, hw'.2⟩
      have hzB : z - M ∉ B := by
        intro hb
        apply hz'.2
        have he : M + (z - M) = z := by omega
        rw [← he]
        exact Finset.add_mem_add hAM hb
      have hzR : z - M ∈ rightStable A B M N :=
        mem_rightStable.mpr ⟨by omega, hzB, by
          have he : z - M + M = z := Nat.sub_add_cancel (by omega)
          simpa [he] using hz'.2⟩
      have hproj : z - M = w := by simpa [stableProjection, hzN, hwN] using heq
      rw [hproj] at hzR
      exact (Finset.disjoint_left.mp hdisj hwL hzR).elim
    · have heq' : z - M = w - M := by simpa [stableProjection, hzN, hwN] using heq
      omega

lemma card_stableHoles {A B : Finset ℕ} {M N : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card) :
    (stableHoles A B M N).card = (sumHoles A B M N).card := by
  rw [← image_stableProjection_sumHoles hMN hA hB hA0 hAM hhole,
    card_image_iff.mpr (stableProjection_injOn_sumHoles hMN hA hB hA0 hAM hhole)]

lemma stableHoles_subset_holes (A B : Finset ℕ) (M N : ℕ) :
    stableHoles A B M N ⊆ holes B N := by
  intro x hx
  rcases mem_stableHoles.mp hx with hx | hx
  · have hx' := mem_leftStable.mp hx
    exact mem_holes.mpr ⟨hx'.1, hx'.2.1⟩
  · have hx' := mem_rightStable.mp hx
    exact mem_holes.mpr ⟨hx'.1, hx'.2.1⟩

lemma card_stable_add_unstable (A B : Finset ℕ) (M N : ℕ) :
    (stableHoles A B M N).card + (unstableHoles A B M N).card =
      (holes B N).card := by
  have hsub := stableHoles_subset_holes A B M N
  rw [add_comm]
  simpa [unstableHoles] using card_sdiff_add_card_eq_card hsub

/-- In an inverted pair of disjoint finite ordered sets one can choose a
pair with no member of either set strictly between the two endpoints. -/
lemma exists_adjacent_inversion {L R : Finset ℕ}
    (hinv : ∃ x ∈ L, ∃ y ∈ R, y < x) :
    ∃ x ∈ L, ∃ y ∈ R, y < x ∧
      ∀ z, y < z → z < x → z ∉ L ∪ R := by
  let P : ℕ → Prop := fun d ↦ ∃ x ∈ L, ∃ y ∈ R, y < x ∧ x - y = d
  have hP : ∃ d, P d := by
    obtain ⟨x, hx, y, hy, hyx⟩ := hinv
    exact ⟨x - y, x, hx, y, hy, hyx, rfl⟩
  let d := Nat.find hP
  obtain ⟨x, hx, y, hy, hyx, hxy⟩ := Nat.find_spec hP
  refine ⟨x, hx, y, hy, hyx, ?_⟩
  intro z hyz hzx hz
  rcases mem_union.mp hz with hzL | hzR
  · have hmin : d ≤ z - y := Nat.find_min' hP ⟨z, hzL, y, hy, hyz, rfl⟩
    dsimp [d] at hxy hmin
    omega
  · have hmin : d ≤ x - z := Nat.find_min' hP ⟨x, hx, z, hzR, hzx, rfl⟩
    dsimp [d] at hxy hmin
    omega

/-- Under the strict small-sumset slack, every left-stable hole precedes
every right-stable hole.  This is Proposition 4.5 of the cited paper; the
strict slack used by Bedert avoids its boundary equality case. -/
lemma leftStable_lt_rightStable {A B : Finset ℕ} {M N r : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 2 ≤ B.card)
    (hsumcard : (A + B).card + 1 = A.card + B.card + r)
    (hr : r + 3 ≤ B.card) :
    ∀ x ∈ leftStable A B N, ∀ y ∈ rightStable A B M N, x < y := by
  have hdisj := disjoint_left_right hMN hA hB hhole
  have hsumAmbient := add_subset_ambient hA hB
  have hsumCardLe : (A + B).card ≤ M + N + 1 := by
    simpa using card_le_card hsumAmbient
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAh := card_holes hA
  have hBh := card_holes hB
  have hSh := card_sumHoles hA hB
  have hstable := card_stableHoles hMN hA hB hA0 hAM hhole
  have hpartition := card_stable_add_unstable A B M N
  have hAhAdd : (holes A M).card + A.card = M + 1 := by omega
  have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
  have hShAdd : (sumHoles A B M N).card + (A + B).card = M + N + 1 := by omega
  have hunstable : (unstableHoles A B M N).card + (holes A M).card = r := by omega
  intro x hxL y hyR
  by_contra hxy
  have hyx : y < x := by
    have hne : x ≠ y := by
      intro he
      subst y
      exact Finset.disjoint_left.mp hdisj hxL hyR
    omega
  have hinv : ∃ x ∈ leftStable A B N, ∃ y ∈ rightStable A B M N, y < x :=
    ⟨x, hxL, y, hyR, hyx⟩
  obtain ⟨x, hxL, y, hyR, hyx, hadj⟩ := exists_adjacent_inversion hinv
  have hxL' := mem_leftStable.mp hxL
  have hyR' := mem_rightStable.mp hyR
  have hp := prefix_hole_count hA hB hxL'.1 hxL'.2.2
  have hs0 := suffix_hole_count hMN (by omega) (by omega) hyR'.2.2
  have hs : N - y + 1 ≤
      (holesIcc A (y + M - N) M).card + (holesIcc B y N).card := by
    have heq : M + N - (y + M) = N - y := by omega
    rw [heq] at hs0
    have heq' : y + M - M = y := by omega
    rw [heq'] at hs0
    exact hs0
  have hAparts := card_holesIcc_add_le_total_add_overlap
    (S := A) (M := M) (a := 0) (b := x) (c := y + M - N) (d := M)
    (by omega) (by omega) (by omega) (by omega)
  have hBparts := card_holesIcc_add_le_total_add_overlap
    (S := B) (M := N) (a := 0) (b := x) (c := y) (d := N)
    (by omega) (by omega) (by omega) (by omega)
  have hBover :
      (holesIcc B (max 0 y) (min x N)).card ≤
        (unstableHoles A B M N).card + 2 := by
    have hsub : holesIcc B (max 0 y) (min x N) ⊆
        unstableHoles A B M N ∪ {y, x} := by
      intro z hz
      have hz' := mem_holesIcc.mp hz
      by_cases hzy : z = y
      · subst z
        exact mem_union_right _ (by simp)
      by_cases hzx : z = x
      · subst z
        exact mem_union_right _ (by simp)
      have hyz : y < z := by omega
      have hzxlt : z < x := by omega
      have hnotstable : z ∉ stableHoles A B M N := by
        intro hzstable
        exact hadj z hyz hzxlt (by simpa [stableHoles] using hzstable)
      exact mem_union_left _ (mem_unstableHoles.mpr ⟨by omega, hz'.2.2, hnotstable⟩)
    have hc := card_le_card hsub
    have hu := card_union_le (unstableHoles A B M N) {y, x}
    have hpair : ({y, x} : Finset ℕ).card ≤ 2 := by
      rw [Finset.card_pair (by omega)]
    omega
  by_cases hsep : x < y + M - N
  · have hAover :
        (holesIcc A (max 0 (y + M - N)) (min x M)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' := mem_holesIcc.mp hz
      omega
    have hBlen : (holesIcc B (max 0 y) (min x N)).card ≤ x - y + 1 := by
      have hc := card_holesIcc_le_length (S := B) (a := max 0 y) (b := min x N)
      omega
    omega
  · have hAover :
        (holesIcc A (max 0 (y + M - N)) (min x M)).card ≤
          x - y + N - M + 1 := by
      have hc := card_holesIcc_le_length (S := A)
        (a := max 0 (y + M - N)) (b := min x M)
      omega
    omega

/-- Once cuts have been chosen after all left-stable holes and before all
right-stable holes, the interval between them contains no sumset holes. -/
lemma interval_between_stable_cuts {A B : Finset ℕ} {M N lo c : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A)
    (hhole : (holes A M).card + 1 ≤ B.card)
    (hcN : c ≤ N + 1)
    (hleft : ∀ x ∈ leftStable A B N, x < lo)
    (hright : ∀ x ∈ rightStable A B M N, c ≤ x) :
    Icc lo (M + c - 1) ⊆ A + B := by
  have hmid := middle_interval_subset_sum hMN hA hB hhole
  intro z hz
  have hzI := mem_Icc.mp hz
  by_contra hzsum
  by_cases hzN : z < N
  · have hzB : z ∉ B := by
      intro hb
      exact hzsum (by simpa using Finset.add_mem_add hA0 hb)
    have hzL : z ∈ leftStable A B N :=
      mem_leftStable.mpr ⟨by omega, hzB, hzsum⟩
    exact (not_lt_of_ge hzI.1) (hleft z hzL)
  · have hMz : M < z := by
      by_contra hnot
      exact hzsum (hmid (mem_Icc.mpr ⟨by omega, by omega⟩))
    let x := z - M
    have hxN : x ≤ N := by dsimp [x]; omega
    have hxB : x ∉ B := by
      intro hb
      apply hzsum
      have heq : M + x = z := by dsimp [x]; omega
      rw [← heq]
      exact Finset.add_mem_add hAM hb
    have hxR : x ∈ rightStable A B M N := by
      apply mem_rightStable.mpr
      refine ⟨hxN, hxB, ?_⟩
      have heq : x + M = z := by dsimp [x]; omega
      simpa [heq] using hzsum
    have hcx := hright x hxR
    dsimp [x] at hcx
    have heq : M + (z - M) = z := by omega
    omega

/-- The strict form of Theorem 1.1 of Bardaji--Grynkiewicz used below.
The sets are normalized to have minima zero and maxima `M,N`. -/
theorem normalized_long_interval {A B : Finset ℕ} {M N r : ℕ}
    (hMN : N ≤ M) (hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
    (hA0 : 0 ∈ A) (hAM : M ∈ A) (hB0 : 0 ∈ B) (hBN : N ∈ B)
    (hdiam : M + 3 ≤ A.card + B.card)
    (hsumcard : (A + B).card + 1 = A.card + B.card + r)
    (hr : r + 3 ≤ B.card) :
    ∃ lo, Icc lo (lo + (A.card + B.card - 2)) ⊆ A + B := by
  have hAcard : A.card ≤ M + 1 := by simpa using card_le_card hA
  have hBcard : B.card ≤ N + 1 := by simpa using card_le_card hB
  have hAh := card_holes hA
  have hhole : (holes A M).card + 2 ≤ B.card := by omega
  have horder := leftStable_lt_rightStable hMN hA hB hA0 hAM hhole hsumcard hr
  let L := leftStable A B N
  let R := rightStable A B M N
  by_cases hL : L.Nonempty
  · let e := L.max' hL
    have heL : e ∈ L := L.max'_mem hL
    have heN : e ≤ N := (mem_leftStable.mp heL).1
    have hleft : ∀ x ∈ L, x < e + 1 := by
      intro x hx
      exact Nat.lt_succ_of_le (L.le_max' x hx)
    by_cases hR : R.Nonempty
    · let c := R.min' hR
      have hcR : c ∈ R := R.min'_mem hR
      have hcN : c ≤ N := (mem_rightStable.mp hcR).1
      have hright : ∀ x ∈ R, c ≤ x := by
        intro x hx
        exact R.min'_le x hx
      have hec : e < c := horder e heL c hcR
      have hp0 := prefix_hole_count hA hB heN (mem_leftStable.mp heL).2.2
      have hs0 := suffix_hole_count hMN (by omega) (by omega)
        (mem_rightStable.mp hcR).2.2
      have hs : N - c + 1 ≤
          (holesIcc A (c + M - N) M).card + (holesIcc B c N).card := by
        have heq : M + N - (c + M) = N - c := by omega
        rw [heq] at hs0
        have heq' : c + M - M = c := by omega
        rw [heq'] at hs0
        exact hs0
      have hAparts := card_holesIcc_add_le_total_add_overlap
        (S := A) (M := M) (a := 0) (b := e) (c := c + M - N) (d := M)
        (by omega) (by omega) (by omega) (by omega)
      have hBparts := card_holesIcc_add_le_total_add_overlap
        (S := B) (M := N) (a := 0) (b := e) (c := c) (d := N)
        (by omega) (by omega) (by omega) (by omega)
      have hAover :
          (holesIcc A (max 0 (c + M - N)) (min e M)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz' := mem_holesIcc.mp hz
        omega
      have hBover : (holesIcc B (max 0 c) (min e N)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz' := mem_holesIcc.mp hz
        omega
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + c - (e + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := e + 1) (c := c) (by simpa [L] using hleft) (by simpa [R] using hright)
      refine ⟨e + 1, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨hz'.1, by omega⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      have hp := prefix_hole_count hA hB heN (mem_leftStable.mp heL).2.2
      have hApart := card_holesIcc_le_card_holes (S := A) (M := M)
        (a := 0) (b := e) (by omega) (by omega)
      have hBpart := card_holesIcc_le_card_holes (S := B) (M := N)
        (a := 0) (b := e) (by omega) (by omega)
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + (N + 1) - (e + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := e + 1) (c := N + 1) (by simpa [L] using hleft)
        (by intro x hx; simp [R, hRempty] at hx)
      refine ⟨e + 1, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨hz'.1, by omega⟩
  · have hLempty : L = ∅ := not_nonempty_iff_eq_empty.mp hL
    by_cases hR : R.Nonempty
    · let c := R.min' hR
      have hcR : c ∈ R := R.min'_mem hR
      have hcN : c ≤ N := (mem_rightStable.mp hcR).1
      have hright : ∀ x ∈ R, c ≤ x := by
        intro x hx
        exact R.min'_le x hx
      have hs0 := suffix_hole_count hMN (by omega) (by omega)
        (mem_rightStable.mp hcR).2.2
      have hs : N - c + 1 ≤
          (holesIcc A (c + M - N) M).card + (holesIcc B c N).card := by
        have heq : M + N - (c + M) = N - c := by omega
        rw [heq] at hs0
        have heq' : c + M - M = c := by omega
        rw [heq'] at hs0
        exact hs0
      have hApart := card_holesIcc_le_card_holes (S := A) (M := M)
        (a := c + M - N) (b := M) (by omega) (by omega)
      have hBpart := card_holesIcc_le_card_holes (S := B) (M := N)
        (a := c) (b := N) (by omega) (by omega)
      have hBh := card_holes hB
      have hBhAdd : (holes B N).card + B.card = N + 1 := by omega
      have hgap : A.card + B.card - 1 ≤ M + c := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := 0) (c := c) (by intro x hx; simp [L, hLempty] at hx)
        (by simpa [R] using hright)
      refine ⟨0, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      have hgap : A.card + B.card - 1 ≤ M + (N + 1) := by omega
      have hbig := interval_between_stable_cuts hMN hA hB hA0 hAM (by omega) (by omega)
        (lo := 0) (c := N + 1) (by intro x hx; simp [L, hLempty] at hx)
        (by intro x hx; simp [R, hRempty] at hx)
      refine ⟨0, ?_⟩
      intro z hz
      apply hbig
      have hz' := mem_Icc.mp hz
      exact mem_Icc.mpr ⟨by omega, by omega⟩

/-! ## Residue representatives for Ruzsa's diameter estimate -/

def modImage (S : Finset ℕ) (v : ℕ) : Finset (ZMod v) :=
  S.image fun x : ℕ ↦ (x : ZMod v)

def modFiber (S : Finset ℕ) (v : ℕ) (c : ZMod v) : Finset ℕ :=
  S.filter fun x ↦ (x : ZMod v) = c

@[simp] lemma mem_modImage {S : Finset ℕ} {v : ℕ} {c : ZMod v} :
    c ∈ modImage S v ↔ ∃ x ∈ S, (x : ZMod v) = c := by
  simp [modImage]

@[simp] lemma mem_modFiber {S : Finset ℕ} {v x : ℕ} {c : ZMod v} :
    x ∈ modFiber S v c ↔ x ∈ S ∧ (x : ZMod v) = c := by
  simp [modFiber]

lemma modFiber_nonempty {S : Finset ℕ} {v : ℕ} {c : ZMod v}
    (hc : c ∈ modImage S v) : (modFiber S v c).Nonempty := by
  obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
  exact ⟨x, mem_modFiber.mpr ⟨hx, hxc⟩⟩

/-- The least integer of `S` in a residue represented by `S`. -/
noncomputable def residueRep (S : Finset ℕ) (v : ℕ)
    (c : ↑(modImage S v)) : ℕ :=
  (modFiber S v c.1).min' (modFiber_nonempty c.2)

lemma residueRep_mem (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    residueRep S v c ∈ S := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).1

lemma residueRep_cast (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    ((residueRep S v c : ℕ) : ZMod v) = c.1 := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).2

lemma residueRep_le {S : Finset ℕ} {v z : ℕ} (c : ↑(modImage S v))
    (hz : z ∈ S) (hzc : (z : ZMod v) = c.1) : residueRep S v c ≤ z := by
  apply (modFiber S v c.1).min'_le z
  exact mem_modFiber.mpr ⟨hz, hzc⟩

lemma residueRep_injective (S : Finset ℕ) (v : ℕ) :
    Function.Injective (residueRep S v) := by
  intro c d hcd
  apply Subtype.ext
  rw [← residueRep_cast S v c, ← residueRep_cast S v d, hcd]

noncomputable def residueReps (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (modImage S v).attach.image (residueRep S v)

lemma card_residueReps (S : Finset ℕ) (v : ℕ) :
    (residueReps S v).card = (modImage S v).card := by
  rw [residueReps, card_image_of_injective _ (residueRep_injective S v)]
  simp

lemma residueReps_subset (S : Finset ℕ) (v : ℕ) : residueReps S v ⊆ S := by
  intro z hz
  simp only [residueReps, mem_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  exact residueRep_mem S v c

/-- Reduction modulo `v` commutes with a natural-number sumset. -/
lemma modImage_add (A B : Finset ℕ) (v : ℕ) :
    modImage (A + B) v = modImage A v + modImage B v := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    simp only [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    apply Finset.mem_add.mpr
    refine ⟨(a : ZMod v), mem_modImage.mpr ⟨a, ha, rfl⟩,
      (b : ZMod v), mem_modImage.mpr ⟨b, hb, rfl⟩, ?_⟩
    simpa using hzc
  · intro hc
    simp only [Finset.mem_add] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    obtain ⟨x, hx, hxa⟩ := mem_modImage.mp ha
    obtain ⟨y, hy, hyb⟩ := mem_modImage.mp hb
    apply mem_modImage.mpr
    refine ⟨x + y, Finset.add_mem_add hx hy, ?_⟩
    push_cast
    rw [hxa, hyb]

/-- The `v`-shifted copy of `A` used for the extra lift in every residue
represented by `A`. -/
def shiftedBy (A : Finset ℕ) (v : ℕ) : Finset ℕ := A.image fun a ↦ a + v

lemma card_shiftedBy (A : Finset ℕ) (v : ℕ) : (shiftedBy A v).card = A.card := by
  rw [shiftedBy, Finset.card_image_of_injective]
  intro x y h
  change x + v = y + v at h
  omega

lemma shiftedBy_subset_add {A B : Finset ℕ} {v : ℕ} (hvB : v ∈ B) :
    shiftedBy A v ⊆ A + B := by
  intro z hz
  simp only [shiftedBy, mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  exact Finset.add_mem_add ha hvB

lemma residueReps_disjoint_shiftedBy {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
    Disjoint (residueReps (A + B) v) (shiftedBy A v) := by
  rw [Finset.disjoint_left]
  intro z hzR hzE
  simp only [shiftedBy, mem_image] at hzE
  obtain ⟨a, ha, rfl⟩ := hzE
  simp only [residueReps, mem_image] at hzR
  obtain ⟨c, hc, hrep⟩ := hzR
  have hcast : c.1 = (a : ZMod v) := by
    rw [← residueRep_cast (A + B) v c, hrep]
    simp
  let ca : ↑(modImage (A + B) v) :=
    ⟨(a : ZMod v), mem_modImage.mpr ⟨a, Finset.add_mem_add ha hB0, rfl⟩⟩
  have hca : c = ca := by
    apply Subtype.ext
    exact hcast
  subst c
  have hle : residueRep (A + B) v ca ≤ a :=
    residueRep_le ca (Finset.add_mem_add ha hB0) rfl
  have haU := mem_Icc.mp (hA ha)
  dsimp [ca] at hrep hle
  omega

/-- Ruzsa's basic lift count, equation (4.3): there is one sum for each
sum residue and one further sum for each member of the smaller-diameter
summand. -/
lemma card_modImage_add_add_card_le {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B) :
    (modImage (A + B) v).card + A.card ≤ (A + B).card := by
  have hR := residueReps_subset (A + B) v
  have hE := shiftedBy_subset_add (A := A) hvB
  have hdisj := residueReps_disjoint_shiftedBy hA huv hv hA0 hB0
  rw [← card_residueReps (A + B) v, ← card_shiftedBy A v,
    ← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset hR hE)

lemma natCast_injOn_Ico {v : ℕ} :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (Ico 0 v) := by
  intro x hx y hy hxy
  have hx' := mem_Ico.mp hx
  have hy' := mem_Ico.mp hy
  have hv : 0 < v := by omega
  have hvx := congrArg ZMod.val hxy
  rw [ZMod.val_natCast_of_lt hx'.2, ZMod.val_natCast_of_lt hy'.2] at hvx
  exact hvx

lemma card_modImage_eq_card_of_lt {S : Finset ℕ} {u v : ℕ}
    (hS : S ⊆ Icc 0 u) (huv : u < v) : (modImage S v).card = S.card := by
  apply card_image_iff.mpr
  apply (natCast_injOn_Ico (v := v)).mono
  intro x hx
  have hx' := mem_Icc.mp (hS hx)
  exact mem_Ico.mpr ⟨hx'.1, hx'.2.trans_lt huv⟩

lemma erase_top_subset_Ico {S : Finset ℕ} {v : ℕ} (hS : S ⊆ Icc 0 v) :
    S.erase v ⊆ Ico 0 v := by
  intro x hx
  have hxS := mem_of_mem_erase hx
  have hxI := mem_Icc.mp (hS hxS)
  have hxne := ne_of_mem_erase hx
  exact mem_Ico.mpr ⟨hxI.1, lt_of_le_of_ne hxI.2 hxne⟩

lemma modImage_erase_top {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (h0 : 0 ∈ S) (hvS : v ∈ S) : modImage (S.erase v) v = modImage S v := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    exact mem_modImage.mpr ⟨x, mem_of_mem_erase hx, hxc⟩
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    by_cases hxv : x = v
    · subst x
      apply mem_modImage.mpr
      refine ⟨0, mem_erase.mpr ⟨by omega, h0⟩, ?_⟩
      simpa using hxc
    · exact mem_modImage.mpr ⟨x, mem_erase.mpr ⟨hxv, hx⟩, hxc⟩

lemma card_modImage_add_one_eq {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (hS : S ⊆ Icc 0 v) (h0 : 0 ∈ S) (hvS : v ∈ S) :
    (modImage S v).card + 1 = S.card := by
  have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (S.erase v) :=
    (natCast_injOn_Ico (v := v)).mono (erase_top_subset_Ico hS)
  rw [← modImage_erase_top hv h0 hvS, modImage, card_image_iff.mpr hinj,
    card_erase_of_mem hvS]
  have : 0 < S.card := card_pos.mpr ⟨v, hvS⟩
  omega

lemma zero_mem_modImage {S : Finset ℕ} {v : ℕ} (h0 : 0 ∈ S) :
    (0 : ZMod v) ∈ modImage S v := mem_modImage.mpr ⟨0, h0, by simp⟩

lemma zero_mem_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) : 0 ∈ C.addStab := by
  exact hC.zero_mem_addStab

lemma addStab_add_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x y : G}
    (hx : x ∈ C.addStab) (hy : y ∈ C.addStab) : x + y ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx hy ⊢
  exact (AddAction.stabilizer G (C : Set G)).add_mem hx hy

lemma addStab_neg_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : x ∈ C.addStab) : -x ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx ⊢
  exact (AddAction.stabilizer G (C : Set G)).neg_mem hx

/-- If all residues of a set of integers lie in a subgroup and their
integer gcd is one, that subgroup is all of `ZMod v`. -/
lemma stabilizer_eq_top_of_gcd_one {S : Finset ℕ} {v : ℕ}
    (hgcd : S.gcd (fun n ↦ (n : ℤ)) = 1)
    (K : AddSubgroup (ZMod v)) (hS : ∀ n ∈ S, (n : ZMod v) ∈ K) : K = ⊤ := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul S (fun n ↦ (n : ℤ))
  have hterms : ∀ n ∈ S, (n : ZMod v) * (g n : ZMod v) ∈ K := by
    intro n hn
    have hnK := hS n hn
    have hz := K.zsmul_mem hnK (g n)
    simpa [smul_eq_mul, mul_comm] using hz
  have hsum : ((∑ n ∈ S, (n : ℤ) * g n : ℤ) : ZMod v) ∈ K := by
    push_cast
    exact K.sum_mem fun n hn ↦ hterms n hn
  have hone : (1 : ZMod v) ∈ K := by
    rw [hgcd] at hg
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod v)) hg
    norm_num at hcast
    rw [hcast]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using hsum
  apply (AddSubgroup.eq_top_iff' K).mpr
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  rw [← hz]
  simpa [smul_eq_mul] using K.zsmul_mem hone z

/-! ## The refined lift across a missing stabilizer coset -/

/-- The least integer representative of a residue of `S` which is outside
the prescribed residue set `D`. -/
noncomputable def residueRepOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) (c : ↑(modImage S v \ D)) : ℕ :=
  residueRep S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

/-- One least representative for every residue of `S` outside `D`. -/
noncomputable def residueRepsOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (modImage S v \ D).attach.image (residueRepOutside S v D)

lemma residueRepOutside_mem (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) : residueRepOutside S v D c ∈ S := by
  exact residueRep_mem S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_cast (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) :
    ((residueRepOutside S v D c : ℕ) : ZMod v) = c.1 := by
  exact residueRep_cast S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_injective (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    Function.Injective (residueRepOutside S v D) := by
  intro c e hce
  apply Subtype.ext
  rw [← residueRepOutside_cast S v D c,
    ← residueRepOutside_cast S v D e, hce]

lemma card_residueRepsOutside (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    (residueRepsOutside S v D).card = (modImage S v \ D).card := by
  rw [residueRepsOutside,
    card_image_of_injective _ (residueRepOutside_injective S v D)]
  simp

lemma residueRepsOutside_subset (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    residueRepsOutside S v D ⊆ S := by
  intro z hz
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact residueRepOutside_mem S v D c

lemma cast_not_mem_of_mem_residueRepsOutside {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} (hz : z ∈ residueRepsOutside S v D) :
    (z : ZMod v) ∉ D := by
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  rw [residueRepOutside_cast]
  exact (mem_sdiff.mp c.2).2

/-- Sums in a chosen residue set. -/
def sumsOverResidues (A B : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (A + B).filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_sumsOverResidues {A B : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ sumsOverResidues A B v D ↔ z ∈ A + B ∧ (z : ZMod v) ∈ D := by
  simp [sumsOverResidues]

/-- Ruzsa's refined lift: besides one representative outside `D`, retain
the shifted copy of `A` and every actual sum whose residue lies in `D`.
When `D` misses all residues of `A`, these three collections are disjoint. -/
lemma card_modImage_add_add_card_add_fiber_le {A B : Finset ℕ} {u v : ℕ}
    (D : Finset (ZMod v))
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hD : D ⊆ modImage (A + B) v)
    (hDA : Disjoint D (modImage A v)) :
    (modImage (A + B) v).card + A.card +
        (sumsOverResidues A B v D).card ≤ (A + B).card + D.card := by
  let R := residueRepsOutside (A + B) v D
  let E := shiftedBy A v
  let F := sumsOverResidues A B v D
  have hRS : R ⊆ A + B := residueRepsOutside_subset (A + B) v D
  have hES : E ⊆ A + B := shiftedBy_subset_add hvB
  have hFS : F ⊆ A + B := filter_subset _ _
  have hRE : Disjoint R E := by
    apply Disjoint.mono_left _ (residueReps_disjoint_shiftedBy hA huv hv hA0 hB0)
    intro z hz
    change z ∈ residueRepsOutside (A + B) v D at hz
    simp only [residueRepsOutside, residueReps, mem_image] at hz ⊢
    obtain ⟨c, -, rfl⟩ := hz
    exact ⟨⟨c.1, (mem_sdiff.mp c.2).1⟩, by simp,
      rfl⟩
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_of_mem_residueRepsOutside hzR)
      (mem_sumsOverResidues.mp hzF).2
  have hEF : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro z hzE hzF
    simp only [E, shiftedBy, mem_image] at hzE
    obtain ⟨a, ha, rfl⟩ := hzE
    have haD : (a : ZMod v) ∈ D := by
      simpa using (mem_sumsOverResidues.mp hzF).2
    exact (Finset.disjoint_left.mp hDA) haD
      (mem_modImage.mpr ⟨a, ha, rfl⟩)
  have hREF : Disjoint (R ∪ E) F := by
    rw [Finset.disjoint_left]
    intro z hz hzF
    rcases mem_union.mp hz with hzR | hzE
    · exact (Finset.disjoint_left.mp hRF) hzR hzF
    · exact (Finset.disjoint_left.mp hEF) hzE hzF
  have hU : (R ∪ E) ∪ F ⊆ A + B := union_subset (union_subset hRS hES) hFS
  have hcardU := card_le_card hU
  rw [card_union_of_disjoint hREF, card_union_of_disjoint hRE,
    card_residueRepsOutside, card_shiftedBy] at hcardU
  have hsplit := card_sdiff_add_card_eq_card hD
  change (modImage (A + B) v \ D).card + D.card =
    (modImage (A + B) v).card at hsplit
  change (modImage (A + B) v).card + A.card + F.card ≤
    (A + B).card + D.card
  omega

/-- The integers of `S` whose residues belong to `D`. -/
def residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  S.filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_residueFiberSet {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ residueFiberSet S v D ↔ z ∈ S ∧ (z : ZMod v) ∈ D := by
  simp [residueFiberSet]

lemma modImage_residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) :
    modImage (residueFiberSet S v D) v = modImage S v ∩ D := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    have hz' := mem_residueFiberSet.mp hz
    exact mem_inter.mpr ⟨mem_modImage.mpr ⟨z, hz'.1, hzc⟩, by simpa [hzc] using hz'.2⟩
  · intro hc
    have hc' := mem_inter.mp hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc'.1
    apply mem_modImage.mpr
    exact ⟨z, mem_residueFiberSet.mpr ⟨hz, by simpa [hzc] using hc'.2⟩, hzc⟩

lemma card_modImage_le (S : Finset ℕ) (v : ℕ) :
    (modImage S v).card ≤ S.card := by
  exact card_image_le

/-- Saturating a residue set by `H` fills the coset through any occupied
residue.  The only overcount in adjoining that coset is paid for by the
corresponding integer fiber. -/
lemma card_modImage_add_card_le_saturation_add_fiber
    {S : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a : ZMod v}
    (h0 : (0 : ZMod v) ∈ H) (ha : a ∈ modImage S v) :
    (modImage S v).card + H.card ≤
      (modImage S v + H).card +
        (residueFiberSet S v (a +ᵥ H)).card := by
  let X := modImage S v
  let D := a +ᵥ H
  have hX : X ⊆ X + H := by
    intro x hx
    have : x + 0 ∈ X + H := Finset.add_mem_add hx h0
    simpa using this
  have hD : D ⊆ X + H := vadd_finset_subset_add ha
  have hU : X ∪ D ⊆ X + H := union_subset hX hD
  have hinter : (X ∩ D).card ≤ (residueFiberSet S v D).card := by
    rw [← modImage_residueFiberSet]
    exact card_modImage_le _ _
  have hcardU := card_le_card hU
  have hcardD : D.card = H.card := card_vadd_finset a H
  have hIE := card_union_add_card_inter X D
  change X.card + H.card ≤ (X + H).card + (residueFiberSet S v D).card
  omega

lemma disjoint_vadd_add_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X H : Finset G} {c : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hc : c ∉ X + H) :
    Disjoint (c +ᵥ H) (X + H) := by
  rw [Finset.disjoint_left]
  intro z hzD hzX
  obtain ⟨h₂, hh₂, hh₂z⟩ := mem_vadd_finset.mp hzD
  obtain ⟨x, hx, h₁, hh₁, hh₁z⟩ := mem_add.mp hzX
  change c + h₂ = z at hh₂z
  apply hc
  apply mem_add.mpr
  refine ⟨x, hx, h₁ + -h₂, hadd h₁ hh₁ (-h₂) (hneg h₂ hh₂), ?_⟩
  calc
    x + (h₁ + -h₂) = (x + h₁) + -h₂ := by abel
    _ = z + -h₂ := by rw [hh₁z]
    _ = (c + h₂) + -h₂ := by rw [hh₂z]
    _ = c := by abel

lemma disjoint_self_vadd_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : Finset G} {b : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hb : b ∉ H) :
    Disjoint H (b +ᵥ H) := by
  rw [Finset.disjoint_left]
  intro z hzH hzD
  obtain ⟨h, hh, hhz⟩ := mem_vadd_finset.mp hzD
  change b + h = z at hhz
  apply hb
  have : z + -h ∈ H := hadd z hzH (-h) (hneg h hh)
  convert this using 1
  rw [← hhz]
  abel

lemma residueFiberSet_add_subset_sumsOverResidues
    {A B : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a b c : ZMod v}
    (hc : a + b = c)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) :
    residueFiberSet A v (a +ᵥ H) + residueFiberSet B v (b +ᵥ H) ⊆
      sumsOverResidues A B v (c +ᵥ H) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_residueFiberSet.mp hx
  have hy' := mem_residueFiberSet.mp hy
  obtain ⟨h₁, hh₁, ha⟩ := mem_vadd_finset.mp hx'.2
  obtain ⟨h₂, hh₂, hb⟩ := mem_vadd_finset.mp hy'.2
  change a + h₁ = (x : ZMod v) at ha
  change b + h₂ = (y : ZMod v) at hb
  apply mem_sumsOverResidues.mpr
  constructor
  · exact Finset.add_mem_add hx'.1 hy'.1
  · apply mem_vadd_finset.mpr
    refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
    change c + (h₁ + h₂) = ((x + y : ℕ) : ZMod v)
    push_cast
    rw [← ha, ← hb, ← hc]
    abel

/-! ## Ruzsa's diameter estimate -/

/-- Ruzsa's modular diameter estimate in the normalized situation.  The
set of all elements of the two summands has integer gcd one. -/
theorem ruzsa_normalized_diameter_bound
    {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (hB : B ⊆ Icc 0 v) (huv : u ≤ v)
    (hv : 0 < v) (hA0 : 0 ∈ A) (huA : u ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hgcd : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1) :
    min (A.card + v)
      (A.card + B.card + min A.card B.card - 3) ≤ (A + B).card := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let A₀ := modImage A v
  let B₀ := modImage B v
  let C₀ := A₀ + B₀
  let H := C₀.addStab
  have hA₀zero : (0 : ZMod v) ∈ A₀ := zero_mem_modImage hA0
  have hB₀zero : (0 : ZMod v) ∈ B₀ := zero_mem_modImage hB0
  have hA₀ne : A₀.Nonempty := ⟨0, hA₀zero⟩
  have hB₀ne : B₀.Nonempty := ⟨0, hB₀zero⟩
  have hC₀ne : C₀.Nonempty := by
    rw [Finset.add_nonempty]
    exact ⟨hA₀ne, hB₀ne⟩
  have hHzero : (0 : ZMod v) ∈ H := zero_mem_addStab hC₀ne
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hC₀ne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hC₀ne hx
  have hA₀C₀ : A₀ ⊆ C₀ := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hB₀zero, by simp⟩
  have hB₀C₀ : B₀ ⊆ C₀ := by
    intro b hb
    exact mem_add.mpr ⟨0, hA₀zero, b, hb, by simp⟩
  have hA₀sat : A₀ ⊆ A₀ + H := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hHzero, by simp⟩
  have hB₀sat : B₀ ⊆ B₀ + H := by
    intro b hb
    exact mem_add.mpr ⟨b, hb, 0, hHzero, by simp⟩
  have hA₀H_C₀ : A₀ + H ⊆ C₀ := by
    have hs := add_subset_add hA₀C₀ (subset_rfl : H ⊆ H)
    change A₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀H_C₀ : B₀ + H ⊆ C₀ := by
    have hs := add_subset_add hB₀C₀ (subset_rfl : H ⊆ H)
    change B₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀card : B₀.card + 1 = B.card := by
    exact card_modImage_add_one_eq hv hB hB0 hvB
  have hA₀card : A.card ≤ A₀.card + 1 := by
    by_cases hlt : u < v
    · have h := card_modImage_eq_card_of_lt hA hlt
      change A₀.card = A.card at h
      omega
    · have huv' : u = v := by omega
      subst u
      have h := card_modImage_add_one_eq hv hA hA0 huA
      change A₀.card + 1 = A.card at h
      omega
  have hC₀image : C₀ = modImage (A + B) v := by
    change modImage A v + modImage B v = modImage (A + B) v
    exact (modImage_add A B v).symm
  have hlift : C₀.card + A.card ≤ (A + B).card := by
    rw [hC₀image]
    exact card_modImage_add_add_card_le hA huv hv hA0 hB0 hvB
  have hkneser : (A₀ + H).card + (B₀ + H).card ≤ C₀.card + H.card := by
    have hk := Finset.add_kneser A₀ B₀
    change (A₀ + C₀.addStab).card + (B₀ + C₀.addStab).card ≤
      C₀.card + C₀.addStab.card at hk
    exact hk
  have hHcard : H.card ≤ v := by
    calc
      H.card ≤ (Finset.univ : Finset (ZMod v)).card := card_le_card (subset_univ H)
      _ = v := by simp [ZMod.card]
  by_cases hwhole : H.card = v
  · have hHC₀ : H ⊆ C₀ := by
      intro h hh
      exact hA₀H_C₀ (mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩)
    have hC₀cardle : C₀.card ≤ v := by
      calc
        C₀.card ≤ (Finset.univ : Finset (ZMod v)).card :=
          card_le_card (subset_univ C₀)
        _ = v := by simp [ZMod.card]
    have hC₀card : C₀.card = v := by
      have := card_le_card hHC₀
      omega
    apply (min_le_left _ _).trans
    omega
  · have hHlt : H.card < v := by omega
    have hnotBoth : ¬ (A₀ ⊆ H ∧ B₀ ⊆ H) := by
      rintro ⟨hAH, hBH⟩
      let K : AddSubgroup (ZMod v) := AddAction.stabilizer (ZMod v) (C₀ : Set (ZMod v))
      have hHK : (H : Set (ZMod v)) = (K : Set (ZMod v)) := by
        change (↑C₀.addStab : Set (ZMod v)) = _
        exact coe_addStab hC₀ne
      have hUK : ∀ n ∈ A ∪ B, (n : ZMod v) ∈ K := by
        intro n hn
        have hnH : (n : ZMod v) ∈ H := by
          rcases mem_union.mp hn with hnA | hnB
          · exact hAH (mem_modImage.mpr ⟨n, hnA, rfl⟩)
          · exact hBH (mem_modImage.mpr ⟨n, hnB, rfl⟩)
        have hnHs : (n : ZMod v) ∈ (H : Set (ZMod v)) := hnH
        rw [hHK] at hnHs
        exact hnHs
      have hKtop := stabilizer_eq_top_of_gcd_one hgcd K hUK
      have hHuniv : H = (Finset.univ : Finset (ZMod v)) := by
        ext x
        simp only [mem_univ, iff_true]
        have hxK : x ∈ K := by rw [hKtop]; trivial
        have hxKs : x ∈ (K : Set (ZMod v)) := hxK
        rw [← hHK] at hxKs
        exact hxKs
      have : H.card = v := by simp [hHuniv, ZMod.card]
      omega
    by_cases hBH : B₀ ⊆ H
    · have hAnH : ¬ A₀ ⊆ H := fun hAH ↦ hnotBoth ⟨hAH, hBH⟩
      obtain ⟨a, haA, haH⟩ := Finset.not_subset.mp hAnH
      have hdisj : Disjoint H (a +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg haH
      have hHsub : H ⊆ A₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩
      have hacoset : a +ᵥ H ⊆ A₀ + H := vadd_finset_subset_add haA
      have hAsat : 2 * H.card ≤ (A₀ + H).card := by
        have hc := card_le_card (union_subset hHsub hacoset)
        rw [card_union_of_disjoint hdisj, card_vadd_finset] at hc
        omega
      have hBsatEq : B₀ + H = H := by
        apply Subset.antisymm
        · intro z hz
          obtain ⟨b, hb, h, hh, rfl⟩ := mem_add.mp hz
          exact hHadd b (hBH hb) h hh
        · intro h hh
          exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hC₀lower : 2 * H.card ≤ C₀.card := by
        rw [hBsatEq] at hkneser
        omega
      have hBsmall : B.card ≤ H.card + 1 := by
        have hc := card_le_card hBH
        omega
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega
    · obtain ⟨b', hb'B, hb'H⟩ := Finset.not_subset.mp hBH
      have hdisjBH : Disjoint H (b' +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg hb'H
      have hHsubB : H ⊆ B₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hbcoset : b' +ᵥ H ⊆ B₀ + H := vadd_finset_subset_add hb'B
      have hBsat : 2 * H.card ≤ (B₀ + H).card := by
        have hc := card_le_card (union_subset hHsubB hbcoset)
        rw [card_union_of_disjoint hdisjBH, card_vadd_finset] at hc
        omega
      have hAproperCard : (A₀ + H).card + H.card ≤ C₀.card := by omega
      have hHpos : 0 < H.card := card_pos.mpr ⟨0, hHzero⟩
      have hnotSubset : ¬ C₀ ⊆ A₀ + H := by
        intro hs
        have hc := card_le_card hs
        omega
      obtain ⟨c, hcC, hcA⟩ := Finset.not_subset.mp hnotSubset
      have hDsubC : c +ᵥ H ⊆ C₀ := by
        have hs : c +ᵥ H ⊆ C₀ + H := vadd_finset_subset_add hcC
        change c +ᵥ H ⊆ C₀ + C₀.addStab at hs
        simpa only [add_addStab] using hs
      have hDdisjSat : Disjoint (c +ᵥ H) (A₀ + H) :=
        disjoint_vadd_add_of_not_mem hHadd hHneg hcA
      have hDdisjA : Disjoint (c +ᵥ H) A₀ :=
        hDdisjSat.mono_right hA₀sat
      obtain ⟨a, haA, b, hbB, hab⟩ := mem_add.mp hcC
      let X := a +ᵥ H
      let Y := b +ᵥ H
      let D := c +ᵥ H
      let R := residueFiberSet A v X
      let S := residueFiberSet B v Y
      let F := sumsOverResidues A B v D
      have hRne : R.Nonempty := by
        obtain ⟨x, hxA, hxa⟩ := mem_modImage.mp haA
        refine ⟨x, mem_residueFiberSet.mpr ⟨hxA, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hxa.symm⟩
      have hSne : S.Nonempty := by
        obtain ⟨y, hyB, hyb⟩ := mem_modImage.mp hbB
        refine ⟨y, mem_residueFiberSet.mpr ⟨hyB, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hyb.symm⟩
      have hRF : R + S ⊆ F := by
        exact residueFiberSet_add_subset_sumsOverResidues hab hHadd
      have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hRne hSne
      have hFcard : R.card + S.card ≤ F.card + 1 := by
        have hs := card_le_card hRF
        change R.card + S.card - 1 ≤ (R + S).card at hcauchy
        have hRp : 0 < R.card := card_pos.mpr hRne
        have hSp : 0 < S.card := card_pos.mpr hSne
        omega
      have hAsatFiber : A₀.card + H.card ≤ (A₀ + H).card + R.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero haA
      have hBsatFiber : B₀.card + H.card ≤ (B₀ + H).card + S.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero hbB
      have hDcard : D.card = H.card := card_vadd_finset c H
      have hDimage : D ⊆ modImage (A + B) v := by
        rw [← hC₀image]
        exact hDsubC
      have hrefined : C₀.card + A.card + F.card ≤
          (A + B).card + H.card := by
        have hr := card_modImage_add_add_card_add_fiber_le D hA huv hv hA0 hB0 hvB
          hDimage hDdisjA
        rw [← hC₀image, hDcard] at hr
        exact hr
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega

/-- The normalized strict Bardaji--Grynkiewicz alternative.  Failure of
three-summand growth forces an interval of the full Cauchy--Davenport
length in the sumset. -/
theorem normalized_growth_or_long_interval
    {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (hB : B ⊆ Icc 0 v) (huv : u ≤ v)
    (hv : 0 < v) (hA0 : 0 ∈ A) (huA : u ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hgcd : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1) :
    A.card + B.card + min A.card B.card ≤ (A + B).card + 3 ∨
      ∃ lo, Icc lo (lo + (A.card + B.card - 2)) ⊆ A + B := by
  by_cases hgrowth :
      A.card + B.card + min A.card B.card ≤ (A + B).card + 3
  · exact Or.inl hgrowth
  · right
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hBne : B.Nonempty := ⟨0, hB0⟩
    have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hAne hBne
    have hlow : A.card + B.card ≤ (A + B).card + 1 := by
      change A.card + B.card - 1 ≤ (A + B).card at hcauchy
      have hAp : 0 < A.card := card_pos.mpr hAne
      have hBp : 0 < B.card := card_pos.mpr hBne
      omega
    let r := (A + B).card + 1 - (A.card + B.card)
    have hsumcard : (A + B).card + 1 = A.card + B.card + r := by
      dsimp [r]
      omega
    have hr : r + 3 ≤ A.card := by
      have hm := min_le_left A.card B.card
      omega
    have hruzsa := ruzsa_normalized_diameter_bound hA hB huv hv hA0 huA hB0 hvB hgcd
    have hdiam : v + 3 ≤ B.card + A.card := by
      have hm := min_le_right A.card B.card
      omega
    have hlong := normalized_long_interval (A := B) (B := A)
      (M := v) (N := u) (r := r) huv hB hA hB0 hvB hA0 huA
      hdiam (by simpa [add_comm] using hsumcard) hr
    obtain ⟨lo, hlo⟩ := hlong
    refine ⟨lo, ?_⟩
    simpa only [add_comm (a := B.card) A.card, add_comm (a := B) A] using hlo

/-! ## Translation and division by the common gcd -/

lemma nat_int_finset_gcd (S : Finset ℕ) :
    S.gcd (fun n ↦ (n : ℤ)) =
      (((S.gcd (fun n : ℕ ↦ n) : ℕ) : ℤ)) := by
  induction S using Finset.cons_induction_on with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.gcd_cons ha, Finset.gcd_cons ha, ih]
    rw [← Int.coe_gcd]
    rfl

/-- Translate a natural finset down by `m` and divide by `d`. -/
def normalizeNat (S : Finset ℕ) (m d : ℕ) : Finset ℕ :=
  S.image fun x ↦ (x - m) / d

lemma mem_normalizeNat {S : Finset ℕ} {m d q : ℕ} :
    q ∈ normalizeNat S m d ↔ ∃ x ∈ S, (x - m) / d = q := by
  simp [normalizeNat]

lemma normalizeNat_spec {S : Finset ℕ} {m d : ℕ}
    (hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m)
    {q : ℕ} : q ∈ normalizeNat S m d ↔ ∃ x ∈ S, x = m + d * q := by
  constructor
  · intro hq
    obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
    refine ⟨x, hx, ?_⟩
    have hcancel := Nat.mul_div_cancel' (hdiv x hx)
    have hmx := hmin x hx
    omega
  · rintro ⟨x, hx, rfl⟩
    apply mem_normalizeNat.mpr
    refine ⟨m + d * q, hx, ?_⟩
    have : m + d * q - m = d * q := by omega
    rw [this]
    exact Nat.mul_div_cancel_left q hd

lemma card_normalizeNat {S : Finset ℕ} {m d : ℕ}
    (hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m) :
    (normalizeNat S m d).card = S.card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  have hdx := Nat.mul_div_cancel' (hdiv x hx)
  have hdy := Nat.mul_div_cancel' (hdiv y hy)
  have hmx := hmin x hx
  have hmy := hmin y hy
  change (x - m) / d = (y - m) / d at hxy
  have := congrArg (fun z ↦ d * z) hxy
  rw [hdx, hdy] at this
  omega

lemma normalizeNat_subset_Icc {S : Finset ℕ} {m d M : ℕ}
    (hS : S ⊆ Icc m M) : normalizeNat S m d ⊆ Icc 0 ((M - m) / d) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
  have hxI := mem_Icc.mp (hS hx)
  exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (Nat.sub_le_sub_right hxI.2 m)⟩

lemma zero_mem_normalizeNat {S : Finset ℕ} {m d : ℕ} (hm : m ∈ S) :
    0 ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨m, hm, by simp⟩

lemma top_mem_normalizeNat {S : Finset ℕ} {m d M : ℕ} (hM : M ∈ S) :
    (M - m) / d ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨M, hM, rfl⟩

/-- Reconstructing the original sumset from the translated, divided
summands. -/
lemma sumset_eq_image_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d) (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    S + T = (normalizeNat S s d + normalizeNat T t d).image
      (fun q ↦ s + t + d * q) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    let a := (x - s) / d
    let b := (y - t) / d
    have ha : a ∈ normalizeNat S s d := mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hb : b ∈ normalizeNat T t d := mem_normalizeNat.mpr ⟨y, hy, rfl⟩
    apply mem_image.mpr
    refine ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
    have hdx := Nat.mul_div_cancel' (hSdiv x hx)
    have hdy := Nat.mul_div_cancel' (hTdiv y hy)
    have hsx := hSmin x hx
    have hty := hTmin y hy
    have hxa : x = s + d * a := by dsimp [a]; omega
    have hyb : y = t + d * b := by dsimp [b]; omega
    change s + t + d * (a + b) = x + y
    rw [hxa, hyb]
    ring
  · intro hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hq
    obtain ⟨x, hx, hxa⟩ := (normalizeNat_spec hd hSmin hSdiv).mp ha
    obtain ⟨y, hy, hyb⟩ := (normalizeNat_spec hd hTmin hTdiv).mp hb
    apply mem_add.mpr
    refine ⟨x, hx, y, hy, ?_⟩
    rw [hxa, hyb]
    ring

lemma card_sumset_eq_card_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d)
    (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    (S + T).card = (normalizeNat S s d + normalizeNat T t d).card := by
  rw [sumset_eq_image_normalized hd hSmin hTmin hSdiv hTdiv,
    card_image_iff.mpr]
  intro x hx y hy hxy
  change s + t + d * x = s + t + d * y at hxy
  have hmul : d * x = d * y := Nat.add_left_cancel hxy
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- The local arithmetic progression notation used by the final additive
alternative. -/
def natAP (a d len : ℕ) : Finset ℕ :=
  (range len).image fun j ↦ a + d * j

@[simp] lemma mem_natAP {a d len x : ℕ} :
    x ∈ natAP a d len ↔ ∃ j < len, a + d * j = x := by
  simp [natAP]

def InOneResidue (U : Finset ℕ) (d : ℕ) : Prop :=
  ∃ r : ZMod d, ∀ x ∈ U, (x : ZMod d) = r

/-- The strict additive alternative before symmetrizing the two summands,
assuming the first has no larger diameter than the second. -/
theorem growth_or_long_AP_of_diameter_le {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hdiam : S.max' hS - S.min' hS ≤ T.max' hT - T.min' hT) :
    S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨
      ∃ a d : ℕ, 0 < d ∧
        natAP a d (S.card + T.card - 1) ⊆ S + T ∧
        InOneResidue (S + T) d := by
  let s := S.min' hS
  let t := T.min' hT
  let sM := S.max' hS
  let tM := T.max' hT
  let u := sM - s
  let v := tM - t
  have hsS : s ∈ S := S.min'_mem hS
  have htT : t ∈ T := T.min'_mem hT
  have hsMS : sM ∈ S := S.max'_mem hS
  have htMT : tM ∈ T := T.max'_mem hT
  have hSmin : ∀ x ∈ S, s ≤ x := fun x hx ↦ S.min'_le x hx
  have hTmin : ∀ x ∈ T, t ≤ x := fun x hx ↦ T.min'_le x hx
  have hSmax : ∀ x ∈ S, x ≤ sM := fun x hx ↦ S.le_max' x hx
  have hTmax : ∀ x ∈ T, x ≤ tM := fun x hx ↦ T.le_max' x hx
  have huv : u ≤ v := by simpa [u, v, s, t, sM, tM] using hdiam
  by_cases hv0 : v = 0
  · have hu0 : u = 0 := by omega
    have hScard : S.card = 1 := by
      have hSeq : S = {s} := by
        ext x
        constructor
        · intro hx
          have := hSmin x hx
          have := hSmax x hx
          have hMs : sM = s := by dsimp [u] at hu0; omega
          simp only [mem_singleton]
          omega
        · intro hx
          have hxs : x = s := by simpa using hx
          simpa [hxs] using hsS
      simp [hSeq]
    have hTcard : T.card = 1 := by
      have hTeq : T = {t} := by
        ext x
        constructor
        · intro hx
          have := hTmin x hx
          have := hTmax x hx
          have hMt : tM = t := by dsimp [v] at hv0; omega
          simp only [mem_singleton]
          omega
        · intro hx
          have hxt : x = t := by simpa using hx
          simpa [hxt] using htT
      simp [hTeq]
    left
    have hsumne : (S + T).Nonempty := Finset.add_nonempty.mpr ⟨hS, hT⟩
    have : 0 < (S + T).card := card_pos.mpr hsumne
    omega
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    let S₁ := normalizeNat S s 1
    let T₁ := normalizeNat T t 1
    let W := S₁ ∪ T₁
    let d := W.gcd (fun n : ℕ ↦ n)
    have huS₁ : u ∈ S₁ := by
      have := top_mem_normalizeNat (m := s) (d := 1) hsMS
      simpa [S₁, u, sM, s] using this
    have hvT₁ : v ∈ T₁ := by
      have := top_mem_normalizeNat (m := t) (d := 1) htMT
      simpa [T₁, v, tM, t] using this
    have hvW : v ∈ W := mem_union_right S₁ hvT₁
    have hdne : d ≠ 0 := by
      intro hd0
      have hz := (Finset.gcd_eq_zero_iff.mp hd0) v hvW
      exact hv0 hz
    have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
    have hSdiv : ∀ x ∈ S, d ∣ x - s := by
      intro x hx
      apply Finset.gcd_dvd
      apply mem_union_left T₁
      apply mem_normalizeNat.mpr
      exact ⟨x, hx, by simp⟩
    have hTdiv : ∀ x ∈ T, d ∣ x - t := by
      intro x hx
      apply Finset.gcd_dvd
      apply mem_union_right S₁
      apply mem_normalizeNat.mpr
      exact ⟨x, hx, by simp⟩
    have hdv : d ∣ v := by
      exact Finset.gcd_dvd hvW
    have hdvle : d ≤ v := Nat.le_of_dvd hvpos hdv
    have hvqpos : 0 < v / d := Nat.div_pos hdvle hdpos
    let A := normalizeNat S s d
    let B := normalizeNat T t d
    have hAint : A ⊆ Icc 0 (u / d) := by
      apply normalizeNat_subset_Icc
      intro x hx
      exact mem_Icc.mpr ⟨hSmin x hx, hSmax x hx⟩
    have hBint : B ⊆ Icc 0 (v / d) := by
      apply normalizeNat_subset_Icc
      intro x hx
      exact mem_Icc.mpr ⟨hTmin x hx, hTmax x hx⟩
    have hAzero : 0 ∈ A := zero_mem_normalizeNat hsS
    have hBzero : 0 ∈ B := zero_mem_normalizeNat htT
    have hAtop : u / d ∈ A := by
      have := top_mem_normalizeNat (m := s) (d := d) hsMS
      simpa [A, u, sM, s] using this
    have hBtop : v / d ∈ B := by
      have := top_mem_normalizeNat (m := t) (d := d) htMT
      simpa [B, v, tM, t] using this
    have hqorder : u / d ≤ v / d := Nat.div_le_div_right huv
    have hABW : A ∪ B = W.image (fun z ↦ z / d) := by
      ext q
      simp only [A, B, W, S₁, T₁, normalizeNat, mem_union, mem_image]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨x - s, Or.inl ⟨x, hx, by simp⟩, rfl⟩
        · exact ⟨y - t, Or.inr ⟨y, hy, by simp⟩, rfl⟩
      · rintro ⟨z, (⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩), rfl⟩
        · left
          refine ⟨x, hx, ?_⟩
          simpa using congrArg (fun n ↦ n / d) hxz
        · right
          refine ⟨y, hy, ?_⟩
          simpa using congrArg (fun n ↦ n / d) hyz
    have hWgcd : W.gcd (fun z ↦ z / d) = 1 := by
      exact Finset.gcd_div_id_eq_one hvW hv0
    have hABgcdNat : (A ∪ B).gcd (fun n : ℕ ↦ n) = 1 := by
      rw [hABW, Finset.gcd_image]
      change W.gcd (fun z ↦ z / d) = 1
      exact hWgcd
    have hABgcdInt : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1 := by
      rw [nat_int_finset_gcd, hABgcdNat]
      norm_num
    have hAcard : A.card = S.card := card_normalizeNat hdpos hSmin hSdiv
    have hBcard : B.card = T.card := card_normalizeNat hdpos hTmin hTdiv
    have hsumcard : (S + T).card = (A + B).card :=
      card_sumset_eq_card_normalized hdpos hSmin hTmin hSdiv hTdiv
    have halt := normalized_growth_or_long_interval hAint hBint hqorder hvqpos
      hAzero hAtop hBzero hBtop hABgcdInt
    rcases halt with hgrowth | ⟨lo, hlo⟩
    · left
      simpa only [hAcard, hBcard, ← hsumcard] using hgrowth
    · right
      let a := s + t + d * lo
      refine ⟨a, d, hdpos, ?_, ?_⟩
      · intro z hz
        obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
        have hcardS : 0 < S.card := card_pos.mpr hS
        have hcardT : 0 < T.card := card_pos.mpr hT
        have hq : lo + j ∈ A + B := by
          apply hlo
          apply mem_Icc.mpr
          constructor
          · omega
          · rw [hAcard, hBcard]
            omega
        rw [sumset_eq_image_normalized hdpos hSmin hTmin hSdiv hTdiv]
        apply mem_image.mpr
        refine ⟨lo + j, hq, ?_⟩
        dsimp [a]
        ring
      · refine ⟨((s + t : ℕ) : ZMod d), ?_⟩
        intro z hz
        rw [sumset_eq_image_normalized hdpos hSmin hTmin hSdiv hTdiv] at hz
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
        push_cast
        simp

/-- Strict Bardaji--Grynkiewicz alternative for arbitrary nonempty natural
finsets. -/
theorem growth_or_long_AP {S T : Finset ℕ} (hS : S.Nonempty) (hT : T.Nonempty) :
    S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨
      ∃ a d : ℕ, 0 < d ∧
        natAP a d (S.card + T.card - 1) ⊆ S + T ∧
        InOneResidue (S + T) d := by
  rcases le_total (S.max' hS - S.min' hS) (T.max' hT - T.min' hT) with hle | hle
  · exact growth_or_long_AP_of_diameter_le hS hT hle
  · have h := growth_or_long_AP_of_diameter_le hT hS hle
    simpa only [add_comm (a := T.card) S.card, min_comm, add_comm (a := T) S] using h
end Erdos13Additive

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos13.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 13.
https://www.erdosproblems.com/forum/thread/13

Informal authors:
- Borys Bedert

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos13.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/13.lean
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
# Erdős Problem 13

We formalize Bedert's resolution of the finite property-P problem.  The
mathematical proof and a dependency-by-dependency formalization plan are in
`tex/13.tex` at the repository root.

Reference: B. Bedert, *On a problem of Erdős and Sárközy about sequences
with no term dividing the sum of two larger terms*, arXiv:2301.07065.
-/

open Finset Nat
open scoped Pointwise

/-- A finite set has property P if none of its elements divides a sum of two
strictly larger elements of the set. -/
def IsForbiddenTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬a ∣ b + c

namespace IsForbiddenTripleFree

lemma mono {A B : Finset ℕ} (hA : IsForbiddenTripleFree A) (hBA : B ⊆ A) :
    IsForbiddenTripleFree B := by
  intro a ha b hb c hc hlt
  exact hA a (hBA ha) b (hBA hb) c (hBA hc) hlt

lemma not_dvd_add {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) : ¬a ∣ b + c := by
  exact hA a ha b hb c hc (by simpa [lt_min_iff] using And.intro hab hac)

lemma not_dvd_two_mul {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) : ¬a ∣ 2 * b := by
  simpa [two_mul] using hA.not_dvd_add ha hb hb hab hab

lemma not_dvd_of_lt {A : Finset ℕ} (hA : IsForbiddenTripleFree A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) : ¬a ∣ b := by
  intro hdvd
  exact hA.not_dvd_two_mul ha hb hab (hdvd.mul_left 2)

lemma pos_of_mem {A : Finset ℕ} (_hA : IsForbiddenTripleFree A)
    (hsub : A ⊆ Icc 1 N) {a : ℕ} (ha : a ∈ A) : 0 < a := by
  have := (mem_Icc.mp (hsub ha)).1
  omega

lemma map_div {A : Finset ℕ} (hA : IsForbiddenTripleFree A) {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ a ∈ A, k ∣ a) :
    IsForbiddenTripleFree (A.image (fun a ↦ a / k)) := by
  intro a ha b hb c hc hlt
  simp only [mem_image] at ha hb hc
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  intro hdvd
  have ha_eq : k * (a' / k) = a' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv a' ha')
  have hb_eq : k * (b' / k) = b' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv b' hb')
  have hc_eq : k * (c' / k) = c' := by
    simpa [mul_comm] using Nat.mul_div_cancel' (hdiv c' hc')
  have hlt' : a' < min b' c' := by
    rw [← ha_eq, ← hb_eq, ← hc_eq, min_mul_mul_left]
    exact (Nat.mul_lt_mul_left hk).2 hlt
  apply hA a' ha' b' hb' c' hc' hlt'
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨d, ?_⟩
  have hkd := congrArg (fun x ↦ k * x) hd
  calc
    b' + c' = k * (a' / k * d) := by simpa [mul_add, hb_eq, hc_eq] using hkd
    _ = (k * (a' / k)) * d := by rw [mul_assoc]
    _ = a' * d := by rw [ha_eq]

end IsForbiddenTripleFree

namespace Bedert

/-! We use integer inequalities throughout.  Thus, for example,
`ratSection A N 2 3 1 1` is `A ∩ (2N/3,N]`; no rounding convention is hidden
in the notation. -/

/-- The part of `A` cut out by `p * N < q * x` and `s * x ≤ r * N`. -/
def ratSection (A : Finset ℕ) (N p q r s : ℕ) : Finset ℕ :=
  A.filter fun x ↦ p * N < q * x ∧ s * x ≤ r * N

/-- The elements of a finset in one residue class. -/
def residue (A : Finset ℕ) (r q : ℕ) : Finset ℕ :=
  A.filter fun x ↦ x % q = r % q

@[simp] lemma mem_ratSection {A : Finset ℕ} {N p q r s x : ℕ} :
    x ∈ ratSection A N p q r s ↔ x ∈ A ∧ p * N < q * x ∧ s * x ≤ r * N := by
  simp [ratSection]

@[simp] lemma mem_residue {A : Finset ℕ} {r q x : ℕ} :
    x ∈ residue A r q ↔ x ∈ A ∧ x % q = r % q := by
  simp [residue]

lemma ratSection_subset (A : Finset ℕ) (N p q r s : ℕ) :
    ratSection A N p q r s ⊆ A := by
  intro x hx
  exact (mem_ratSection.mp hx).1

/-- Quotient by `q` is injective on a fixed residue class modulo a positive `q`. -/
lemma div_injOn_residue {S : Finset ℕ} {r q : ℕ} (hq : 0 < q)
    (hS : ∀ x ∈ S, x % q = r % q) : Set.InjOn (fun x : ℕ ↦ x / q) S := by
  intro x hx y hy hxy
  change x / q = y / q at hxy
  have hmod : x % q = y % q := (hS x hx).trans (hS y hy).symm
  calc
    x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
    _ = q * (y / q) + y % q := by rw [hxy, hmod]
    _ = y := Nat.div_add_mod y q

lemma card_Icc_le {S : Finset ℕ} {L U : ℕ} (hS : S ⊆ Icc L U) :
    S.card ≤ (U + 1) - L := by
  simpa using card_le_card hS

/-- Packing disjoint blocks of `q` consecutive integers after the members of
one residue class gives the sharp interval-capacity estimate. -/
lemma mul_card_fixed_zmod_le {S : Finset ℕ} {L U q : ℕ} (i : ZMod q)
    (hS : S ⊆ Icc L U) (hres : ∀ x ∈ S, (x : ZMod q) = i) :
    q * S.card ≤ (U + q) - L := by
  let f : ℕ × ℕ → ℕ := fun xt ↦ xt.1 + xt.2
  let P := S ×ˢ range q
  have hinj : Set.InjOn f P := by
    rintro ⟨x, t⟩ hxt ⟨y, u⟩ hyu heq
    have hxt' : x ∈ S ∧ t < q := by
      change (x, t) ∈ P at hxt
      simpa [P] using hxt
    have hyu' : y ∈ S ∧ u < q := by
      change (y, u) ∈ P at hyu
      simpa [P] using hyu
    have hz : (t : ZMod q) = (u : ZMod q) := by
      have hzsum := congrArg (fun n : ℕ ↦ (n : ZMod q)) heq
      simp only [f, Nat.cast_add] at hzsum
      rw [hres x hxt'.1, hres y hyu'.1] at hzsum
      exact add_left_cancel hzsum
    have htu : t = u := by
      have hzval := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hxt'.2, ZMod.val_natCast_of_lt hyu'.2] at hzval
      exact hzval
    subst u
    change x + t = y + t at heq
    have hxy := Nat.add_right_cancel heq
    subst y
    rfl
  have himage : P.image f ⊆ Ico L (U + q) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨⟨x, t⟩, hxt, rfl⟩ := hz
    simp only [P, mem_product, mem_range] at hxt
    have hx := mem_Icc.mp (hS hxt.1)
    apply mem_Ico.mpr
    change L ≤ x + t ∧ x + t < U + q
    omega
  calc
    q * S.card = P.card := by simp [P, mul_comm]
    _ = (P.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Ico L (U + q)).card := card_le_card himage
    _ = (U + q) - L := by simp

lemma card_add_card_le_of_disjoint_subsets {X Y U : Finset ℕ}
    (hXY : Disjoint X Y) (hX : X ⊆ U) (hY : Y ⊆ U) :
    X.card + Y.card ≤ U.card := by
  rw [← card_union_of_disjoint hXY]
  exact card_le_card (union_subset hX hY)

/-- The disjointness at the heart of Bedert's packing lemma.  Each element
of `k · B` is a multiple of a low element of `A`, whereas `S` consists of
sums of two high elements. -/
lemma mul_image_disjoint_sumset {A B H S : Finset ℕ} {k t : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hB : ∀ b ∈ B, ∃ a ∈ A, a ≤ t ∧ a ∣ k * b)
    (hH : ∀ x ∈ H, x ∈ A ∧ t < x)
    (hS : S ⊆ H + H) :
    Disjoint (B.image fun b ↦ k * b) S := by
  rw [Finset.disjoint_left]
  intro z hzB hzS
  simp only [Finset.mem_image] at hzB
  obtain ⟨b, hb, rfl⟩ := hzB
  obtain ⟨a, ha, hat, hadiv⟩ := hB b hb
  have hsum := hS hzS
  simp only [Finset.mem_add] at hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := hsum
  have hxA := hH x hx
  have hyA := hH y hy
  apply hP.not_dvd_add ha hxA.1 hyA.1 (lt_of_le_of_lt hat hxA.2)
    (lt_of_le_of_lt hat hyA.2)
  rw [hxy]
  exact hadiv

/-- A cardinality form of the packing lemma, with the ambient residue-class
set supplied explicitly. -/
lemma packing {A B H S U : Finset ℕ} {k t : ℕ} (hk : 0 < k)
    (hP : IsForbiddenTripleFree A)
    (hB : ∀ b ∈ B, ∃ a ∈ A, a ≤ t ∧ a ∣ k * b)
    (hH : ∀ x ∈ H, x ∈ A ∧ t < x)
    (hSsum : S ⊆ H + H)
    (hBU : B.image (fun b ↦ k * b) ⊆ U) (hSU : S ⊆ U) :
    B.card + S.card ≤ U.card := by
  have hinj : Function.Injective (fun b : ℕ ↦ k * b) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  have hcard : (B.image fun b ↦ k * b).card = B.card := card_image_of_injective _ hinj
  rw [← hcard]
  exact card_add_card_le_of_disjoint_subsets
    (mul_image_disjoint_sumset hP hB hH hSsum) hBU hSU

/-- A fiber of a natural-number finset in `ZMod q`. -/
def zmodFiber (U : Finset ℕ) (i : ZMod q) : Finset ℕ :=
  U.filter fun x ↦ (x : ZMod q) = i

@[simp] lemma mem_zmodFiber {U : Finset ℕ} {i : ZMod q} {x : ℕ} :
    x ∈ zmodFiber U i ↔ x ∈ U ∧ (x : ZMod q) = i := by
  simp [zmodFiber]

lemma sum_card_zmodFiber (U : Finset ℕ) (q : ℕ) [NeZero q] :
    ∑ i : ZMod q, (zmodFiber U i).card = U.card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := U) (t := Finset.univ)
    (f := fun x : ℕ ↦ (x : ZMod q)) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Bedert's dense-residue argument in its reusable, denominator-cleared
form.  `D` is any strict upper bound for `q` times the size of one fiber.
The hypothesis `D ≤ 2|U|` forces both fibers in the maximizing opposite
pair to be nonempty. -/
lemma dense_residue {U : Finset ℕ} {q D : ℕ} (hq : 0 < q) (a : ZMod q)
    (hcap : ∀ i : ZMod q, q * (zmodFiber U i).card < D)
    (hdense : D ≤ 2 * U.card) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let e : ZMod q ≃ ZMod q :=
    { toFun := fun i ↦ a - i
      invFun := fun i ↦ a - i
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  have hsum : ∑ i : ZMod q, (zmodFiber U i).card = U.card :=
    sum_card_zmodFiber U q
  have he_sum : ∑ i : ZMod q, (zmodFiber U (e i)).card = U.card := by
    calc
      ∑ i : ZMod q, (zmodFiber U (e i)).card =
          ∑ i : ZMod q, (zmodFiber U i).card :=
        e.sum_comp (fun i : ZMod q ↦ (zmodFiber U i).card)
      _ = U.card := hsum
  have hpair_sum :
      ∑ i : ZMod q, ((zmodFiber U i).card + (zmodFiber U (e i)).card) =
        2 * U.card := by
    rw [Finset.sum_add_distrib, hsum, he_sum, two_mul]
  have havg :
      ∃ i : ZMod q, 2 * U.card ≤
        q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
    have hnonempty : (Finset.univ : Finset (ZMod q)).Nonempty := Finset.univ_nonempty
    have hle :
        ∑ _i : ZMod q, 2 * U.card ≤
          ∑ i : ZMod q,
            q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
      have heq :
          ∑ _i : ZMod q, 2 * U.card =
            ∑ i : ZMod q,
              q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
        calc
          ∑ _i : ZMod q, 2 * U.card = q * (2 * U.card) := by
            simp [ZMod.card]
          _ = q * (∑ i : ZMod q,
              ((zmodFiber U i).card + (zmodFiber U (e i)).card)) := by rw [hpair_sum]
          _ = ∑ i : ZMod q,
              q * ((zmodFiber U i).card + (zmodFiber U (e i)).card) := by
            rw [Finset.mul_sum]
      exact heq.le
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hnonempty hle
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := havg
  have hFi : (zmodFiber U i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsmall := hcap (e i)
    simp only [hempty, Finset.card_empty, zero_add] at hi
    omega
  have hFe : (zmodFiber U (e i)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsmall := hcap i
    simp only [hempty, Finset.card_empty, add_zero] at hi
    omega
  have hadd_subset : zmodFiber U i + zmodFiber U (e i) ⊆ zmodFiber (U + U) a := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_zmodFiber.mp hx
    have hy' := mem_zmodFiber.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    rw [Nat.cast_add, hx'.2, hy'.2]
    change i + (a - i) = a
    abel
  have hCD := cauchy_davenport_add_of_linearOrder_isCancelAdd hFi hFe
  have hpair_le :
      (zmodFiber U i).card + (zmodFiber U (e i)).card ≤
        (zmodFiber (U + U) a).card + 1 := by
    have hsumcard := card_le_card hadd_subset
    omega
  exact hi.trans (Nat.mul_le_mul_left q hpair_le)

/-- Bedert's Lemma 3, written without division: if `U` occupies an
`m`-term interval and `m + q ≤ 2|U|`, then every residue class in `U+U`
contains enough elements to satisfy this inequality. -/
lemma dense_residue_Icc {U : Finset ℕ} {k m q : ℕ} (hq : 0 < q)
    (hU : U ⊆ Icc (k + 1) (k + m)) (hdense : m + q ≤ 2 * U.card)
    (a : ZMod q) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  apply dense_residue hq a (D := m + q) ?_ hdense
  intro i
  have hsub : zmodFiber U i ⊆ Icc (k + 1) (k + m) := by
    exact (filter_subset _ _).trans hU
  have hres : ∀ x ∈ zmodFiber U i, (x : ZMod q) = i := by
    intro x hx
    exact (mem_zmodFiber.mp hx).2
  have hcap := mul_card_fixed_zmod_le i hsub hres
  omega

/-! ### Power-window maps -/

/- The paper repeatedly uses windows whose endpoints are rational multiples
of `N`.  Keeping the denominator in the defining inequality avoids every
rounding convention: `scaledMove 0 N 3 a`, for instance, is the least power
of two times `a` whose triple is strictly larger than `N`. -/

lemma exists_scaled_pow_gt {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a) :
    ∃ j : ℕ, T < q * ((b + 2) ^ j * a) := by
  refine ⟨T, ?_⟩
  have hb : 1 < b + 2 := by omega
  have hp : T < (b + 2) ^ T := Nat.lt_pow_self hb
  have hqa : 1 ≤ q * a := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  calc
    T < (b + 2) ^ T := hp
    _ = (b + 2) ^ T * 1 := by simp
    _ ≤ (b + 2) ^ T * (q * a) := Nat.mul_le_mul_left _ hqa
    _ = q * ((b + 2) ^ T * a) := by ac_rfl

/-- Least exponent making `q * ((b+2)^j * a)` exceed `T`. -/
noncomputable def scaledWindowExp (b T q a : ℕ) : ℕ :=
  if hq : 0 < q then
    if ha : 0 < a then Nat.find (exists_scaled_pow_gt (b := b) (T := T) hq ha) else 0
  else 0

/-- Move a positive natural number into a denominator-cleared multiplicative
window by the least power of `b+2`. -/
noncomputable def scaledMove (b T q a : ℕ) : ℕ :=
  (b + 2) ^ scaledWindowExp b T q a * a

lemma lt_scaledMove {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a) :
    T < q * scaledMove b T q a := by
  rw [scaledMove, scaledWindowExp, dif_pos hq, dif_pos ha]
  exact Nat.find_spec (exists_scaled_pow_gt (b := b) (T := T) hq ha)

lemma scaledWindowExp_min {b T q a j : ℕ} (hq : 0 < q) (ha : 0 < a)
    (hj : j < scaledWindowExp b T q a) :
    q * ((b + 2) ^ j * a) ≤ T := by
  rw [scaledWindowExp, dif_pos hq, dif_pos ha] at hj
  exact Nat.le_of_not_gt (Nat.find_min
    (exists_scaled_pow_gt (b := b) (T := T) hq ha) hj)

/-- The upper endpoint supplied by minimality.  This is the exact integral
form used to put the low part of `A` into `(N/3,2N/3]`. -/
lemma scaledMove_le {b T q a : ℕ} (hq : 0 < q) (ha : 0 < a)
    (haT : q * a ≤ (b + 2) * T) :
    q * scaledMove b T q a ≤ (b + 2) * T := by
  by_cases hj : scaledWindowExp b T q a = 0
  · simpa [scaledMove, hj] using haT
  · obtain ⟨j, hjrfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hprev : q * ((b + 2) ^ j * a) ≤ T := by
      apply scaledWindowExp_min hq ha
      omega
    rw [scaledMove, hjrfl, pow_succ']
    nlinarith

lemma dvd_scaledMove (b T q a : ℕ) : a ∣ scaledMove b T q a := by
  exact dvd_mul_left a ((b + 2) ^ scaledWindowExp b T q a)

lemma scaledMove_injOn {A : Finset ℕ} (hP : IsForbiddenTripleFree A)
    (hpos : ∀ a ∈ A, 0 < a) (b T q : ℕ) :
    Set.InjOn (scaledMove b T q) A := by
  intro x hx y hy hxy
  have hbase : 0 < b + 2 := by omega
  have key {u v : ℕ} (hu : u ∈ A) (hv : v ∈ A)
      (huv : scaledMove b T q u = scaledMove b T q v)
      (hle : scaledWindowExp b T q u ≤ scaledWindowExp b T q v) : u = v := by
    let ju := scaledWindowExp b T q u
    let jv := scaledWindowExp b T q v
    have hfactor : u = (b + 2) ^ (jv - ju) * v := by
      have hpow : (b + 2) ^ jv = (b + 2) ^ ju * (b + 2) ^ (jv - ju) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      have heq : (b + 2) ^ ju * u =
          (b + 2) ^ ju * ((b + 2) ^ (jv - ju) * v) := by
        change scaledMove b T q u = _ at huv
        rw [scaledMove, show scaledWindowExp b T q u = ju from rfl,
          scaledMove, show scaledWindowExp b T q v = jv from rfl, hpow, mul_assoc] at huv
        exact huv
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hbase) heq
    by_cases hjeq : ju = jv
    · simpa [hjeq] using hfactor
    · have hjlt : ju < jv := lt_of_le_of_ne hle hjeq
      have hpow2 : 2 ≤ (b + 2) ^ (jv - ju) := by
        have hdiff : jv - ju ≠ 0 := Nat.sub_ne_zero_of_lt hjlt
        exact Nat.one_lt_pow hdiff (by omega : 1 < b + 2)
      have hvu : v < u := by
        have hvpos := hpos v hv
        nlinarith
      exfalso
      apply hP.not_dvd_of_lt hv hu hvu
      refine ⟨(b + 2) ^ (jv - ju), ?_⟩
      simpa [mul_comm] using hfactor
  rcases le_total (scaledWindowExp b T q x) (scaledWindowExp b T q y) with hle | hle
  · exact key hx hy hxy hle
  · exact (key hy hx hxy.symm hle).symm

/-! ### The central-third image -/

/-- The part of `A` at or below `2N/3`, with denominators cleared. -/
def lowTwoThirds (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 3 * a ≤ 2 * N

/-- The part of `A` strictly above `2N/3`. -/
def highThird (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 2 * N < 3 * a

/-- Bedert's `B₁`: move the elements at or below `2N/3` by the least
power of two whose triple is larger than `N`. -/
noncomputable def centralImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowTwoThirds A N).image (scaledMove 0 N 3)

@[simp] lemma mem_lowTwoThirds {A : Finset ℕ} {N a : ℕ} :
    a ∈ lowTwoThirds A N ↔ a ∈ A ∧ 3 * a ≤ 2 * N := by
  simp [lowTwoThirds]

@[simp] lemma mem_highThird {A : Finset ℕ} {N a : ℕ} :
    a ∈ highThird A N ↔ a ∈ A ∧ 2 * N < 3 * a := by
  simp [highThird]

lemma low_union_high (A : Finset ℕ) (N : ℕ) :
    lowTwoThirds A N ∪ highThird A N = A := by
  ext a
  simp only [mem_union, mem_lowTwoThirds, mem_highThird]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro ha
    exact Or.imp (And.intro ha) (And.intro ha) (le_or_gt (3 * a) (2 * N))

lemma low_disjoint_high (A : Finset ℕ) (N : ℕ) :
    Disjoint (lowTwoThirds A N) (highThird A N) := by
  rw [Finset.disjoint_left]
  intro a haL haH
  have hL := (mem_lowTwoThirds.mp haL).2
  have hH := (mem_highThird.mp haH).2
  omega

lemma card_low_add_card_high (A : Finset ℕ) (N : ℕ) :
    (lowTwoThirds A N).card + (highThird A N).card = A.card := by
  rw [← card_union_of_disjoint (low_disjoint_high A N), low_union_high]

lemma centralImage_card {A : Finset ℕ} {N : ℕ} (hP : IsForbiddenTripleFree A)
    (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card = (lowTwoThirds A N).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono (filter_subset _ _))
  intro a ha
  exact hP.pos_of_mem hsub ((filter_subset _ _) ha)

lemma card_centralImage_add_high {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card + (highThird A N).card = A.card := by
  rw [centralImage_card hP hsub, card_low_add_card_high]

lemma centralImage_mem_iff {A : Finset ℕ} {N b : ℕ} :
    b ∈ centralImage A N ↔
      ∃ a ∈ A, 3 * a ≤ 2 * N ∧ scaledMove 0 N 3 a = b := by
  simp only [centralImage, mem_image, mem_lowTwoThirds]
  constructor
  · rintro ⟨a, ⟨ha, haN⟩, rfl⟩
    exact ⟨a, ha, haN, rfl⟩
  · rintro ⟨a, ha, haN, rfl⟩
    exact ⟨a, ⟨ha, haN⟩, rfl⟩

lemma centralImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    centralImage A N ⊆ ratSection (Icc 1 N) N 1 3 2 3 := by
  intro b hb
  obtain ⟨a, haA, haN, rfl⟩ := centralImage_mem_iff.mp hb
  have ha : 0 < a := hP.pos_of_mem hsub haA
  have hlo : N < 3 * scaledMove 0 N 3 a := lt_scaledMove (by omega) ha
  have hhi : 3 * scaledMove 0 N 3 a ≤ 2 * N := by
    simpa using scaledMove_le (b := 0) (T := N) (q := 3) (a := a)
      (by omega) ha haN
  apply mem_ratSection.mpr
  refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_, hhi⟩
  · have hpos : 0 < scaledMove 0 N 3 a := by
      simp only [scaledMove]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) ha
    omega
  · omega
  · simpa using hlo

/-- Every central-image element is a multiple of its originating low
property-P element. -/
lemma centralImage_has_low_divisor {A : Finset ℕ} {N b : ℕ}
    (hb : b ∈ centralImage A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ b := by
  obtain ⟨a, ha, haN, rfl⟩ := centralImage_mem_iff.mp hb
  exact ⟨a, ha, haN, dvd_scaledMove 0 N 3 a⟩

/-! ### Arithmetic progressions and common residue classes -/

/-- A finite arithmetic progression in `ℕ`, parametrized by its number of
terms. -/
def natAP (a d len : ℕ) : Finset ℕ :=
  (range len).image fun j ↦ a + d * j

@[simp] lemma mem_natAP {a d len x : ℕ} :
    x ∈ natAP a d len ↔ ∃ j < len, a + d * j = x := by
  simp [natAP]

lemma card_natAP {a d len : ℕ} (hd : 0 < d) : (natAP a d len).card = len := by
  have hinj : Set.InjOn (fun j : ℕ ↦ a + d * j) (range len) := by
    intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hij)
  rw [natAP, card_image_iff.mpr hinj]
  simp

/-- Every interval of at least `x` consecutive naturals contains a multiple
of the positive integer `x`. -/
lemma exists_dvd_mem_natAP_one {a len x : ℕ} (hx : 0 < x) (hxl : x ≤ len) :
    ∃ y ∈ natAP a 1 len, x ∣ y := by
  by_cases hxa : x ∣ a
  · exact ⟨a, mem_natAP.mpr ⟨0, by omega, by simp⟩, hxa⟩
  · let r := a % x
    let j := x - r
    have hrlt : r < x := by
      exact Nat.mod_lt _ hx
    have hrpos : 0 < r := by
      have hrne : r ≠ 0 := by
        intro hr
        apply hxa
        exact Nat.dvd_of_mod_eq_zero hr
      omega
    have hjlt : j < len := by
      dsimp [j]
      omega
    refine ⟨a + j, mem_natAP.mpr ⟨j, hjlt, by simp⟩, ?_⟩
    refine ⟨a / x + 1, ?_⟩
    have hdiv := Nat.div_add_mod a x
    change a + j = x * (a / x + 1)
    dsimp [j, r]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- All members of `U` occupy one residue class modulo `d`.  The `ZMod`
form is chosen because translating a set or cancelling a fixed summand is
then literal additive cancellation. -/
def InOneResidue (U : Finset ℕ) (d : ℕ) : Prop :=
  ∃ r : ZMod d, ∀ x ∈ U, (x : ZMod d) = r

lemma inOneResidue_mono {U V : Finset ℕ} {d : ℕ}
    (hU : InOneResidue U d) (hVU : V ⊆ U) : InOneResidue V d := by
  obtain ⟨r, hr⟩ := hU
  exact ⟨r, fun x hx ↦ hr x (hVU hx)⟩

lemma inOneResidue_add_left {S T : Finset ℕ} {d : ℕ} (hT : T.Nonempty)
    (hST : InOneResidue (S + T) d) : InOneResidue S d := by
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hST
  refine ⟨r - (t : ZMod d), ?_⟩
  intro x hx
  have hxt := hr (x + t) (Finset.add_mem_add hx ht)
  push_cast at hxt
  rw [← hxt]
  abel

lemma inOneResidue_add_right {S T : Finset ℕ} {d : ℕ} (hS : S.Nonempty)
    (hST : InOneResidue (S + T) d) : InOneResidue T d := by
  rw [add_comm] at hST
  exact inOneResidue_add_left hS hST

/-- The structural alternative used from Bardaji--Grynkiewicz: a long
progression in the sumset, with its step also a common modulus of the whole
sumset. -/
def HasLongSumAP (S T : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ natAP a d (S.card + T.card - 1) ⊆ S + T ∧
    InOneResidue (S + T) d

/-- The exact cardinal alternative in the form used throughout Bedert's
proof. -/
def BGAlternative (S T : Finset ℕ) : Prop :=
  S.card + T.card + min S.card T.card ≤ (S + T).card + 3 ∨ HasLongSumAP S T

/-- The strict Bardaji--Grynkiewicz alternative, transferred from the
normalized additive theorem proved in `Erdos13Additive`. -/
lemma bgAlternative_of_nonempty {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty) : BGAlternative S T := by
  rcases Erdos13Additive.growth_or_long_AP hS hT with hgrowth | hstruct
  · exact Or.inl hgrowth
  · right
    obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
    refine ⟨a, d, hd, ?_, ?_⟩
    · simpa only [natAP, Erdos13Additive.natAP] using hQ
    · simpa only [InOneResidue, Erdos13Additive.InOneResidue] using hres

lemma bgAlternative_self (S : Finset ℕ) : BGAlternative S S := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · left
    simp
  · exact bgAlternative_of_nonempty hS hS

/-! ### The minimum-element estimate -/

/-- Members of `A` in the first full interval above `s`. -/
def firstBlock (A : Finset ℕ) (s : ℕ) : Finset ℕ :=
  A.filter fun x ↦ s < x ∧ x ≤ 2 * s

@[simp] lemma mem_firstBlock {A : Finset ℕ} {s x : ℕ} :
    x ∈ firstBlock A s ↔ x ∈ A ∧ s < x ∧ x ≤ 2 * s := by
  simp [firstBlock]

/-- Reduction modulo `s` is injective on `(s,2s]`. -/
lemma zmod_cast_injOn_firstBlock {A : Finset ℕ} {s : ℕ} (hs : 0 < s) :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod s)) (firstBlock A s) := by
  intro x hx y hy hxy
  have hxI := (mem_firstBlock.mp hx).2
  have hyI := (mem_firstBlock.mp hy).2
  have hmod : x ≡ y [MOD s] := by
    exact (ZMod.natCast_eq_natCast_iff x y s).mp hxy
  rcases le_total x y with hle | hle
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    have hst : s * t < s := by omega
    have ht0 : t = 0 := by
      by_contra ht0
      have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      nlinarith
    simpa [ht0] using ht.symm
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    have hst : s * t < s := by omega
    have ht0 : t = 0 := by
      by_contra ht0
      have : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      nlinarith
    simpa [ht0] using ht

/-- If `s` is the least member of a property-P set, at most half of the
residue classes can occur in `(s,2s]`: a class and its negative cannot both
occur. -/
lemma two_mul_card_firstBlock_le {A : Finset ℕ} {s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsA : s ∈ A) (hs : 0 < s) :
    2 * (firstBlock A s).card ≤ s := by
  letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let R : Finset (ZMod s) := (firstBlock A s).image fun x : ℕ ↦ (x : ZMod s)
  let negR : Finset (ZMod s) := R.image fun r ↦ -r
  have hcardR : R.card = (firstBlock A s).card := by
    apply card_image_iff.mpr
    exact zmod_cast_injOn_firstBlock hs
  have hcardNeg : negR.card = R.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact neg_injective hxy
  have hdisj : Disjoint R negR := by
    rw [Finset.disjoint_left]
    intro r hrR hrNeg
    simp only [negR, Finset.mem_image] at hrNeg
    obtain ⟨q, hqR, hqr⟩ := hrNeg
    simp only [R, Finset.mem_image] at hrR hqR
    obtain ⟨x, hx, hxr⟩ := hrR
    obtain ⟨y, hy, hyq⟩ := hqR
    have hcast : ((x + y : ℕ) : ZMod s) = 0 := by
      rw [Nat.cast_add, hxr, hyq, ← hqr]
      simp
    have hdvd : s ∣ x + y := by
      exact (ZMod.natCast_eq_zero_iff (x + y) s).mp hcast
    have hx' := mem_firstBlock.mp hx
    have hy' := mem_firstBlock.mp hy
    exact hP.not_dvd_add hsA hx'.1 hy'.1 hx'.2.1 hy'.2.1 hdvd
  have hunion : (R ∪ negR).card ≤ s := by
    calc
      (R ∪ negR).card ≤ (Finset.univ : Finset (ZMod s)).card := by
        exact card_le_card (subset_univ _)
      _ = s := by simp [ZMod.card]
  rw [card_union_of_disjoint hdisj, hcardNeg, hcardR] at hunion
  omega

/-- A property-P set with least element `s` is controlled by the first
block above `s` and the completely trivial tail above `2s`. -/
lemma card_le_of_least {A : Finset ℕ} {N s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsA : s ∈ A) (hleast : ∀ x ∈ A, s ≤ x) :
    2 * A.card ≤ 2 + s + 2 * (N - 2 * s) := by
  let T := A.filter fun x ↦ 2 * s < x
  have hdecomp : A = {s} ∪ firstBlock A s ∪ T := by
    ext x
    simp only [mem_union, mem_singleton, mem_firstBlock, T, mem_filter]
    constructor
    · intro hx
      rcases lt_trichotomy x s with hxs | hxs | hxs
      · exact False.elim (by have := hleast x hx; omega)
      · exact Or.inl (Or.inl hxs)
      · by_cases hx2 : x ≤ 2 * s
        · exact Or.inl (Or.inr ⟨hx, hxs, hx2⟩)
        · exact Or.inr ⟨hx, by omega⟩
    · rintro ((rfl | h) | h)
      · exact hsA
      · exact h.1
      · exact h.1
  have hcard : A.card ≤ 1 + (firstBlock A s).card + T.card := by
    have h₁ := card_union_le ({s} : Finset ℕ) (firstBlock A s)
    have h₂ := card_union_le ({s} ∪ firstBlock A s) T
    simp only [card_singleton] at h₁
    calc
      A.card = ({s} ∪ firstBlock A s ∪ T).card := congrArg card hdecomp
      _ ≤ ({s} ∪ firstBlock A s).card + T.card := h₂
      _ ≤ 1 + (firstBlock A s).card + T.card := Nat.add_le_add_right h₁ _
  have hspos : 0 < s := by
    exact (mem_Icc.mp (hsub hsA)).1
  have hfirst := two_mul_card_firstBlock_le hP hsA hspos
  have hTsub : T ⊆ Icc (2 * s + 1) N := by
    intro x hx
    simp only [T, mem_filter] at hx
    exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx.1)).2⟩
  have hTcard := card_Icc_le hTsub
  omega

/-- Once the least element is just past `4N/9`, the elementary opposite
residue pairing already gives the required one-third estimate. -/
lemma three_mul_card_le_of_large_least {A : Finset ℕ} {N s : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsA : s ∈ A) (hleast : ∀ x ∈ A, s ≤ x)
    (hslarge : 4 * N + 9 < 9 * s) :
    3 * A.card ≤ N + 3 := by
  by_cases htop : 2 * N < 3 * s
  · have hAI : A ⊆ Icc s N := by
      intro x hx
      exact mem_Icc.mpr ⟨hleast x hx, (mem_Icc.mp (hsub hx)).2⟩
    have hc := card_Icc_le hAI
    omega
  · have hbasic := card_le_of_least hP hsub hsA hleast
    by_cases hmid : 2 * s ≤ N
    · omega
    · omega

/-! ### The large-top-third branch -/

/-- A sufficiently large subset of the top third cannot occupy one residue
class modulo an integer greater than one. -/
lemma commonDifference_eq_one_of_large_high {H : Finset ℕ} {N d : ℕ}
    (hH : H ⊆ Icc (2 * N / 3 + 1) N)
    (hlarge : 2 * N + 12 ≤ 9 * H.card) (hd : 0 < d)
    (hres : InOneResidue H d) : d = 1 := by
  obtain ⟨r, hr⟩ := hres
  have hcap := mul_card_fixed_zmod_le r hH hr
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    simp only [hzero, card_empty, mul_zero] at hlarge
    omega
  have hcardpos : 0 < H.card := card_pos.mpr hHne
  obtain ⟨x, hx⟩ := hHne
  have hL : 2 * N / 3 + 1 ≤ N := (mem_Icc.mp (hH hx)).1.trans (mem_Icc.mp (hH hx)).2
  by_contra hd1
  have hd2 : 2 ≤ d := by omega
  obtain ⟨k, hk⟩ : ∃ k, H.card = k + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  rw [hk] at hcap hlarge
  have hspan : d * k ≤ N - (2 * N / 3 + 1) := by
    have hrhs : (N + d) - (2 * N / 3 + 1) =
        (N - (2 * N / 3 + 1)) + d := by omega
    rw [hrhs, Nat.mul_add, Nat.mul_one] at hcap
    omega
  have htwo : 2 * k ≤ N - (2 * N / 3 + 1) := by
    exact (Nat.mul_le_mul_right k hd2).trans hspan
  omega

/-- A long unit-step progression in the high-high sumset excludes every
central-or-lower member of `A` whose value is no larger than the progression
length. -/
lemma not_mem_of_le_long_high_sumAP {A H : Finset ℕ} {N a len q : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hH : ∀ x ∈ H, x ∈ A ∧ 2 * N < 3 * x)
    (hQ : natAP q 1 len ⊆ H + H)
    (ha : a ∈ A) (hapos : 0 < a) (halen : a ≤ len) (haN : 3 * a ≤ 2 * N) : False := by
  obtain ⟨y, hyQ, hay⟩ := exists_dvd_mem_natAP_one hapos halen
  have hy := hQ hyQ
  simp only [Finset.mem_add] at hy
  obtain ⟨b, hb, c, hc, rfl⟩ := hy
  have hb' := hH b hb
  have hc' := hH c hc
  apply hP.not_dvd_add ha hb'.1 hc'.1
  · omega
  · omega
  · exact hay

lemma highThird_subset_interval {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    highThird A N ⊆ Icc (2 * N / 3 + 1) N := by
  intro x hx
  have hx' := mem_highThird.mp hx
  exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx'.1)).2⟩

lemma three_mul_card_highThird_le {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    3 * (highThird A N).card ≤ N + 2 := by
  have hc := card_Icc_le (highThird_subset_interval hsub)
  omega

lemma three_mul_card_high_sum_le {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    3 * (highThird A N + highThird A N).card ≤ 2 * N + 2 := by
  have hsumsub : highThird A N + highThird A N ⊆
      Icc (4 * N / 3 + 1) (2 * N) := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_highThird.mp hx
    have hy' := mem_highThird.mp hy
    have hxN := (mem_Icc.mp (hsub hx'.1)).2
    have hyN := (mem_Icc.mp (hsub hy'.1)).2
    apply mem_Icc.mpr
    constructor <;> omega
  have hc := card_Icc_le hsumsub
  omega

/-- Bedert's first case, isolated from the additive-combinatorial theorem.
The only structural input is `BGAlternative H H`. -/
lemma caseOne_of_BG {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : 2 * N + 12 ≤ 9 * (highThird A N).card)
    (hBG : BGAlternative (highThird A N) (highThird A N)) :
    3 * A.card ≤ N + 3 := by
  let H := highThird A N
  change 2 * N + 12 ≤ 9 * H.card at hlarge
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    simp only [H, hzero, card_empty, mul_zero] at hlarge
    omega
  have hHcardpos : 0 < H.card := card_pos.mpr hHne
  have hHmem : ∀ x ∈ H, x ∈ A ∧ 2 * N < 3 * x := by
    intro x hx
    exact mem_highThird.mp hx
  rcases hBG with hgrowth | hstruct
  · have hsum := three_mul_card_high_sum_le hsub
    change H.card + H.card + min H.card H.card ≤ (H + H).card + 3 at hgrowth
    simp only [min_self] at hgrowth
    change 3 * (H + H).card ≤ 2 * N + 2 at hsum
    omega
  · obtain ⟨q, d, hd, hQ, hresSum⟩ := hstruct
    have hresH : InOneResidue H d := inOneResidue_add_left hHne hresSum
    have hd1 : d = 1 := commonDifference_eq_one_of_large_high hHI hlarge hd hresH
    subst d
    have hAne : A.Nonempty := by
      obtain ⟨x, hx⟩ := hHne
      exact ⟨x, (hHmem x hx).1⟩
    let s := A.min' hAne
    have hsA : s ∈ A := A.min'_mem hAne
    have hleast : ∀ x ∈ A, s ≤ x := by
      intro x hx
      exact A.min'_le x hx
    have hspos : 0 < s := (mem_Icc.mp (hsub hsA)).1
    have htopcard := three_mul_card_highThird_le hsub
    have hN : 6 ≤ N := by
      change 3 * H.card ≤ N + 2 at htopcard
      omega
    have hslarge : 4 * N + 9 < 9 * s := by
      by_contra hnot
      have hsupper : 9 * s ≤ 4 * N + 9 := by omega
      have hscentral : 3 * s ≤ 2 * N := by
        by_contra hnotcentral
        omega
      have hlen : s ≤ H.card + H.card - 1 := by
        have hlenlarge : 4 * N + 9 < 9 * (H.card + H.card - 1) := by
          omega
        omega
      exact not_mem_of_le_long_high_sumAP hP hHmem hQ hsA hspos hlen hscentral
    exact three_mul_card_le_of_large_least hP hsub hsA hleast hslarge

lemma caseOne {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : 2 * N + 12 ≤ 9 * (highThird A N).card) :
    3 * A.card ≤ N + 3 :=
  caseOne_of_BG hP hsub hlarge (bgAlternative_self _)

/-! ### Uniform packing estimate for the medium case -/

/-- This is inequalities (6) and (7) of Bedert at once.  A piece of the
central image whose `k`-fold dilate lies in one residue class of the
high-high sum interval satisfies the displayed denominator-cleared bound. -/
lemma medium_packing_bound {A B₀ : Finset ℕ} {N k : ℕ} {r : ZMod 12}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hk : 0 < k) (hB₀ : B₀ ⊆ centralImage A N)
    (hmulI : ∀ b ∈ B₀, k * b ∈ Icc (4 * N / 3 + 1) (2 * N))
    (hmulR : ∀ b ∈ B₀, ((k * b : ℕ) : ZMod 12) = r) :
    3 * (highThird A N).card + 18 * B₀.card ≤ N + 36 := by
  let H := highThird A N
  let L := 4 * N / 3 + 1
  let S := zmodFiber (H + H) r
  let U := zmodFiber (Icc L (2 * N)) r
  change 3 * H.card + 18 * B₀.card ≤ N + 36
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hHinterval : H ⊆ Icc (2 * N / 3 + 1) (2 * N / 3 + (N - 2 * N / 3)) := by
    simpa [H, Nat.add_sub_of_le (by omega : 2 * N / 3 ≤ N)] using hHI
  have hdenseCond : (N - 2 * N / 3) + 12 ≤ 2 * H.card := by
    change N + 144 ≤ 6 * H.card at hmedium
    omega
  have hdense := dense_residue_Icc (q := 12) (by omega) hHinterval hdenseCond r
  have hB : ∀ b ∈ B₀, ∃ a ∈ A, a ≤ 2 * N / 3 ∧ a ∣ k * b := by
    intro b hb
    obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor (hB₀ hb)
    exact ⟨a, haA, by omega, hab.mul_left k⟩
  have hHigh : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ H + H := by
    exact filter_subset _ _
  have hBU : B₀.image (fun b ↦ k * b) ⊆ U := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    apply mem_zmodFiber.mpr
    exact ⟨hmulI b hb, hmulR b hb⟩
  have hsumI : H + H ⊆ Icc L (2 * N) := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_highThird.mp hx
    have hy' := mem_highThird.mp hy
    have hxN := (mem_Icc.mp (hsub hx'.1)).2
    have hyN := (mem_Icc.mp (hsub hy'.1)).2
    apply mem_Icc.mpr
    constructor <;> omega
  have hSU : S ⊆ U := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    exact mem_zmodFiber.mpr ⟨hsumI hz'.1, hz'.2⟩
  have hpack := packing hk hP hB hHigh hSsum hBU hSU
  have hUI : U ⊆ Icc L (2 * N) := (filter_subset _ _)
  have hUres : ∀ x ∈ U, (x : ZMod 12) = r := by
    intro x hx
    exact (mem_zmodFiber.mp hx).2
  have hcap := mul_card_fixed_zmod_le r hUI hUres
  change 2 * H.card ≤ 12 * (S.card + 1) at hdense
  change B₀.card + S.card ≤ U.card at hpack
  change 12 * U.card ≤ (2 * N + 12) - L at hcap
  have hL : 4 * N ≤ 3 * L := by
    dsimp [L]
    omega
  omega

/-- The left half of the central image, split modulo three. -/
noncomputable def centralLeft (A : Finset ℕ) (N i : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun b ↦ 2 * b ≤ N ∧ b % 3 = i % 3

/-- The right half of the central image, split modulo four. -/
noncomputable def centralRight (A : Finset ℕ) (N i : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun b ↦ N < 2 * b ∧ b % 4 = i % 4

@[simp] lemma mem_centralLeft {A : Finset ℕ} {N i b : ℕ} :
    b ∈ centralLeft A N i ↔
      b ∈ centralImage A N ∧ 2 * b ≤ N ∧ b % 3 = i % 3 := by
  simp [centralLeft]

@[simp] lemma mem_centralRight {A : Finset ℕ} {N i b : ℕ} :
    b ∈ centralRight A N i ↔
      b ∈ centralImage A N ∧ N < 2 * b ∧ b % 4 = i % 4 := by
  simp [centralRight]

lemma medium_right_bound {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card) :
    3 * (highThird A N).card + 18 * (centralRight A N i).card ≤ N + 36 := by
  apply medium_packing_bound hP hsub hmedium (k := 3) (r := (3 * i : ZMod 12))
  · omega
  · exact filter_subset _ _
  · intro b hb
    have hb' := mem_centralRight.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro b hb
    have hbmod := (mem_centralRight.mp hb).2.2
    have hm : 3 * b ≡ 3 * i [MOD 12] := by
      have hbi : b ≡ i [MOD 4] := hbmod
      simpa using hbi.mul_left' 3
    simpa [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff (3 * b) (3 * i) 12).mpr hm

/-- The seven medium-case slices partition the central image. -/
lemma card_centralImage_eq_slices (A : Finset ℕ) (N : ℕ) :
    (centralImage A N).card =
      (centralLeft A N 0).card + (centralLeft A N 1).card +
      (centralLeft A N 2).card + (centralRight A N 0).card +
      (centralRight A N 1).card + (centralRight A N 2).card +
      (centralRight A N 3).card := by
  let B := centralImage A N
  let BL := B.filter fun b ↦ 2 * b ≤ N
  let BR := B.filter fun b ↦ N < 2 * b
  have hdisj : Disjoint BL BR := by
    rw [Finset.disjoint_left]
    intro b hbL hbR
    simp only [BL, BR, mem_filter] at hbL hbR
    omega
  have hunion : BL ∪ BR = B := by
    ext b
    simp only [BL, BR, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hb
      exact Or.imp (And.intro hb) (And.intro hb) (le_or_gt (2 * b) N)
  have hcard : B.card = BL.card + BR.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hmapL : (BL : Set ℕ).MapsTo (fun b ↦ b % 3) (range 3) := by
    intro b hb
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hmapR : (BR : Set ℕ).MapsTo (fun b ↦ b % 4) (range 4) := by
    intro b hb
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiberL := Finset.card_eq_sum_card_fiberwise hmapL
  have hfiberR := Finset.card_eq_sum_card_fiberwise hmapR
  have hsliceL (i : ℕ) (hi : i < 3) :
      BL.filter (fun b ↦ b % 3 = i) = centralLeft A N i := by
    ext b
    simp only [BL, B, mem_filter, mem_centralLeft]
    have himod : i % 3 = i := Nat.mod_eq_of_lt hi
    simp only [himod]
    tauto
  have hsliceR (i : ℕ) (hi : i < 4) :
      BR.filter (fun b ↦ b % 4 = i) = centralRight A N i := by
    ext b
    simp only [BR, B, mem_filter, mem_centralRight]
    have himod : i % 4 = i := Nat.mod_eq_of_lt hi
    simp only [himod]
    tauto
  simp only [sum_range_succ, sum_range_zero] at hfiberL hfiberR
  rw [hsliceL 0 (by omega), hsliceL 1 (by omega), hsliceL 2 (by omega)] at hfiberL
  rw [hsliceR 0 (by omega), hsliceR 1 (by omega), hsliceR 2 (by omega),
    hsliceR 3 (by omega)] at hfiberR
  change (centralImage A N).card = BL.card + BR.card at hcard
  omega

lemma medium_done_of_large_right_slice {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hslice : (centralImage A N).card + 12 ≤ 6 * (centralRight A N i).card) :
    3 * A.card ≤ N := by
  have hp := medium_right_bound (i := i) hP hsub hmedium
  have hcard := card_centralImage_add_high hP hsub
  omega

/-- One parity fiber of a finset. -/
def parityPart (H : Finset ℕ) (r : ℕ) : Finset ℕ :=
  H.filter fun x ↦ x % 2 = r % 2

@[simp] lemma mem_parityPart {H : Finset ℕ} {r x : ℕ} :
    x ∈ parityPart H r ↔ x ∈ H ∧ x % 2 = r % 2 := by
  simp [parityPart]

lemma card_parity_parts (H : Finset ℕ) :
    (parityPart H 0).card + (parityPart H 1).card = H.card := by
  have hmap : (H : Set ℕ).MapsTo (fun x ↦ x % 2) (range 2) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at hfiber
  have hzero : H.filter (fun x ↦ x % 2 = 0) = parityPart H 0 := by
    ext x
    simp [parityPart]
  have hone : H.filter (fun x ↦ x % 2 = 1) = parityPart H 1 := by
    ext x
    simp [parityPart]
  rw [hzero, hone] at hfiber
  omega

lemma exists_large_parityPart (H : Finset ℕ) :
    ∃ r < 2, H.card ≤ 2 * (parityPart H r).card := by
  have hc := card_parity_parts H
  rcases le_total (parityPart H 0).card (parityPart H 1).card with h | h
  · exact ⟨1, by omega, by omega⟩
  · exact ⟨0, by omega, by omega⟩

lemma parityPart_sum_even {H : Finset ℕ} {r z : ℕ}
    (hz : z ∈ parityPart H r + parityPart H r) : 2 ∣ z := by
  simp only [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have hxmod := (mem_parityPart.mp hx).2
  have hymod := (mem_parityPart.mp hy).2
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hxmod, hymod]
  have hr : r % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases r % 2 <;> decide

/-- In the medium case, the structural progression in the self-sum of the
larger parity class necessarily has common difference two. -/
lemma medium_structural_step_eq_two {O : Finset ℕ} {N q d : ℕ}
    (hOI : O ⊆ Icc (2 * N / 3 + 1) N)
    (hOlarge : N + 144 ≤ 12 * O.card)
    (hd : 0 < d) (hres : InOneResidue (O + O) d)
    (hQ : natAP q d (O.card + O.card - 1) ⊆ O + O)
    (heven : ∀ z ∈ O + O, 2 ∣ z) : d = 2 := by
  have hOne : InOneResidue O d := by
    have hOneO : O.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hz
      simp only [hz, card_empty, mul_zero] at hOlarge
      omega
    exact inOneResidue_add_left hOneO hres
  obtain ⟨r, hr⟩ := hOne
  have hcap := mul_card_fixed_zmod_le r hOI hr
  have hOpos : 0 < O.card := by omega
  have hL : 2 * N / 3 + 1 ≤ N := by
    obtain ⟨x, hx⟩ := card_pos.mp hOpos
    exact (mem_Icc.mp (hOI hx)).1.trans (mem_Icc.mp (hOI hx)).2
  have hdle : d ≤ 3 := by
    by_contra hnot
    have hd4 : 4 ≤ d := by omega
    obtain ⟨k, hk⟩ : ∃ k, O.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hOpos)
    rw [hk] at hcap hOlarge
    have hrhs : (N + d) - (2 * N / 3 + 1) =
        (N - (2 * N / 3 + 1)) + d := by omega
    rw [hrhs, Nat.mul_add, Nat.mul_one] at hcap
    have hspan : d * k ≤ N - (2 * N / 3 + 1) := by omega
    have hfour : 4 * k ≤ N - (2 * N / 3 + 1) :=
      (Nat.mul_le_mul_right k hd4).trans hspan
    omega
  have hlen : 1 < O.card + O.card - 1 := by omega
  have hq : q ∈ O + O := hQ (mem_natAP.mpr ⟨0, by omega, by simp⟩)
  have hqd : q + d ∈ O + O := hQ (mem_natAP.mpr ⟨1, hlen, by simp⟩)
  have hed : 2 ∣ d := by
    have heq := heven q hq
    have heqd := heven (q + d) hqd
    rw [Nat.dvd_iff_mod_eq_zero] at heq heqd ⊢
    simpa [Nat.add_mod, heq] using heqd
  omega

/-! ### The packing alternative in the medium case -/

/-- Dilation of a natural-number finset. -/
def dilate (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x ↦ k * x

@[simp] lemma mem_dilate {k x : ℕ} {S : Finset ℕ} :
    x ∈ dilate k S ↔ ∃ y ∈ S, k * y = x := by
  simp [dilate]

lemma card_dilate {k : ℕ} (hk : 0 < k) (S : Finset ℕ) :
    (dilate k S).card = S.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hk hxy

lemma disjoint_of_zmod_ne {X Y : Finset ℕ} {q : ℕ} {r s : ZMod q}
    (hrs : r ≠ s) (hX : ∀ x ∈ X, (x : ZMod q) = r)
    (hY : ∀ y ∈ Y, (y : ZMod q) = s) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro z hzX hzY
  exact hrs ((hX z hzX).symm.trans (hY z hzY))

/-- The four dilated slices used in (14) of Bedert's proof. -/
noncomputable def mediumPack (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  dilate 4 (centralLeft A N 0) ∪
  dilate 4 (centralLeft A N 1) ∪
  dilate 4 (centralLeft A N 2) ∪
  dilate 3 (centralRight A N 2)

lemma mediumPack_card (A : Finset ℕ) (N : ℕ) :
    (mediumPack A N).card =
      (centralLeft A N 0).card + (centralLeft A N 1).card +
      (centralLeft A N 2).card + (centralRight A N 2).card := by
  let D0 := dilate 4 (centralLeft A N 0)
  let D1 := dilate 4 (centralLeft A N 1)
  let D2 := dilate 4 (centralLeft A N 2)
  let D3 := dilate 3 (centralRight A N 2)
  have hresL (i : ℕ) (z : ℕ) (hz : z ∈ dilate 4 (centralLeft A N i)) :
      (z : ZMod 12) = (4 * i : ℕ) := by
    obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hbmod := (mem_centralLeft.mp hb).2.2
    have hm : 4 * b ≡ 4 * i [MOD 12] := by
      have hbi : b ≡ i [MOD 3] := hbmod
      simpa using hbi.mul_left' 4
    exact (ZMod.natCast_eq_natCast_iff (4 * b) (4 * i) 12).mpr hm
  have hresR (z : ℕ) (hz : z ∈ dilate 3 (centralRight A N 2)) :
      (z : ZMod 12) = (6 : ℕ) := by
    obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hbmod := (mem_centralRight.mp hb).2.2
    have hm : 3 * b ≡ 3 * 2 [MOD 12] := by
      have hbi : b ≡ 2 [MOD 4] := hbmod
      simpa using hbi.mul_left' 3
    exact (ZMod.natCast_eq_natCast_iff (3 * b) 6 12).mpr (by simpa using hm)
  have h01 : Disjoint D0 D1 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (4 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D1] using hresL 1 z hz
  have h02 : Disjoint D0 D2 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (8 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D2] using hresL 2 z hz
  have h12 : Disjoint D1 D2 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (4 : ZMod 12)) (s := (8 : ZMod 12))
    · decide
    · intro z hz; simpa [D1] using hresL 1 z hz
    · intro z hz; simpa [D2] using hresL 2 z hz
  have h03 : Disjoint D0 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (0 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D0] using hresL 0 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h13 : Disjoint D1 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (4 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D1] using hresL 1 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h23 : Disjoint D2 D3 := by
    apply disjoint_of_zmod_ne (q := 12) (r := (8 : ZMod 12)) (s := (6 : ZMod 12))
    · decide
    · intro z hz; simpa [D2] using hresL 2 z hz
    · intro z hz; simpa [D3] using hresR z hz
  have h012 : Disjoint (D0 ∪ D1) D2 := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    simp only [Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact (Finset.disjoint_left.mp h02) hz hz2
    · exact (Finset.disjoint_left.mp h12) hz hz2
  have h0123 : Disjoint (D0 ∪ D1 ∪ D2) D3 := by
    rw [Finset.disjoint_left]
    intro z hz hz3
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · exact (Finset.disjoint_left.mp h03) hz hz3
    · exact (Finset.disjoint_left.mp h13) hz hz3
    · exact (Finset.disjoint_left.mp h23) hz hz3
  change (D0 ∪ D1 ∪ D2 ∪ D3).card = _
  rw [card_union_of_disjoint h0123, card_union_of_disjoint h012,
    card_union_of_disjoint h01]
  simp [D0, D1, D2, D3, card_dilate]

lemma mediumPack_subset_even_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    mediumPack A N ⊆ zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2) := by
  intro z hz
  simp only [mediumPack, Finset.mem_union] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralLeft.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨2 * b, by omega⟩
  · obtain ⟨b, hb, rfl⟩ := mem_dilate.mp hz
    have hb' := mem_centralRight.mp hb
    have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hb'.1)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [ZMod.natCast_eq_zero_iff]
      rw [Nat.dvd_iff_mod_eq_zero]
      have hbmod : b % 4 = 2 := by simpa using hb'.2.2
      omega

lemma mediumPack_disjoint_sumset {A O : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hO : O ⊆ highThird A N) : Disjoint (mediumPack A N) (O + O) := by
  have hHigh : ∀ x ∈ highThird A N, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hSum : O + O ⊆ highThird A N + highThird A N := by
    exact Finset.add_subset_add hO hO
  have hB (k : ℕ) (B₀ : Finset ℕ) (hB₀ : B₀ ⊆ centralImage A N) :
      ∀ b ∈ B₀, ∃ a ∈ A, a ≤ 2 * N / 3 ∧ a ∣ k * b := by
    intro b hb
    obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor (hB₀ hb)
    exact ⟨a, haA, by omega, hab.mul_left k⟩
  have hD0 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 0) (filter_subset _ _)) hHigh hSum
  have hD1 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 1) (filter_subset _ _)) hHigh hSum
  have hD2 := mul_image_disjoint_sumset hP
    (hB 4 (centralLeft A N 2) (filter_subset _ _)) hHigh hSum
  have hD3 := mul_image_disjoint_sumset hP
    (hB 3 (centralRight A N 2) (filter_subset _ _)) hHigh hSum
  rw [Finset.disjoint_left]
  intro z hz hzO
  simp only [mediumPack, Finset.mem_union] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · exact (Finset.disjoint_left.mp hD0) hz hzO
  · exact (Finset.disjoint_left.mp hD1) hz hzO
  · exact (Finset.disjoint_left.mp hD2) hz hzO
  · exact (Finset.disjoint_left.mp hD3) hz hzO

lemma selfSum_subset_even_interval {A O : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) (hO : O ⊆ highThird A N)
    (heven : ∀ z ∈ O + O, 2 ∣ z) :
    O + O ⊆ zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2) := by
  intro z hz
  simp only [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have hx' := mem_highThird.mp (hO hx)
  have hy' := mem_highThird.mp (hO hy)
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  apply mem_zmodFiber.mpr
  refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [ZMod.natCast_eq_zero_iff]
  exact heven (x + y) (Finset.add_mem_add hx hy)

/-- The growth alternative `|O+O| ≥ 3|O|-3` completes Case 2.  The
three omitted right slices are small, while four distinct dilates and the
self-sum pack into the even part of `(4N/3,2N]`. -/
lemma medium_done_of_sumset_growth {A O : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hO : O ⊆ highThird A N)
    (hOlarge : (highThird A N).card ≤ 2 * O.card)
    (heven : ∀ z ∈ O + O, 2 ∣ z)
    (hgrowth : 3 * O.card ≤ (O + O).card + 3)
    (hsmall0 : 6 * (centralRight A N 0).card < (centralImage A N).card + 12)
    (hsmall1 : 6 * (centralRight A N 1).card < (centralImage A N).card + 12)
    (hsmall3 : 6 * (centralRight A N 3).card < (centralImage A N).card + 12) :
    3 * A.card ≤ N := by
  let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 2)
  have hDU : mediumPack A N ⊆ U := mediumPack_subset_even_interval hP hsub
  have hOU : O + O ⊆ U := selfSum_subset_even_interval hsub hO heven
  have hdisj : Disjoint (mediumPack A N) (O + O) :=
    mediumPack_disjoint_sumset hP hsub hO
  have hcapacity := card_add_card_le_of_disjoint_subsets hdisj hDU hOU
  have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
  have hUres : ∀ z ∈ U, (z : ZMod 2) = (0 : ZMod 2) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hUcap := mul_card_fixed_zmod_le (0 : ZMod 2) hUI hUres
  have hDcard := mediumPack_card A N
  have hpartition := card_centralImage_eq_slices A N
  have hAcard := card_centralImage_add_high hP hsub
  change (mediumPack A N).card + (O + O).card ≤ U.card at hcapacity
  change 2 * U.card ≤ (2 * N + 2) - (4 * N / 3 + 1) at hUcap
  omega

/-! ### Quotients extracted from a long progression -/

/-- Divide precisely those members of `S` which are divisible by `k`. -/
def quotientPart (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (S.filter fun z ↦ k ∣ z).image fun z ↦ z / k

@[simp] lemma mem_quotientPart {S : Finset ℕ} {k x : ℕ} :
    x ∈ quotientPart S k ↔ ∃ z ∈ S, k ∣ z ∧ z / k = x := by
  simp only [quotientPart, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hzS, hkz⟩, hzx⟩
    exact ⟨z, hzS, hkz, hzx⟩
  · rintro ⟨z, hzS, hkz, hzx⟩
    exact ⟨z, ⟨hzS, hkz⟩, hzx⟩

lemma card_quotientPart {S : Finset ℕ} {k : ℕ} (hk : 0 < k) :
    (quotientPart S k).card = (S.filter fun z ↦ k ∣ z).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  change x ∈ S.filter (fun z ↦ k ∣ z) at hx
  change y ∈ S.filter (fun z ↦ k ∣ z) at hy
  have hxmul : k * (x / k) = x := Nat.mul_div_cancel' (Finset.mem_filter.mp hx).2
  have hymul : k * (y / k) = y := Nat.mul_div_cancel' (Finset.mem_filter.mp hy).2
  calc
    x = k * (x / k) := hxmul.symm
    _ = k * (y / k) := congrArg (fun z ↦ k * z) (by simpa using hxy)
    _ = y := hymul

lemma quotientPart_spec {S : Finset ℕ} {k x : ℕ} (hx : x ∈ quotientPart S k) :
    k * x ∈ S := by
  obtain ⟨z, hzS, hkz, rfl⟩ := mem_quotientPart.mp hx
  have heq : k * (z / k) = z := Nat.mul_div_cancel' hkz
  rwa [heq]

/-- A general index injection into the divisible terms of a difference-two
progression.  It is the floor arithmetic behind the `1/2` and `1/3`
counts in Bedert's equation (10). -/
lemma div_terms_natAP_lower {q len k p e : ℕ} (hp : 0 < p) (he : e < p)
    (hbase : k ∣ q + 2 * e) (hstep : k ∣ 2 * p) :
    len / p ≤ ((natAP q 2 len).filter fun z ↦ k ∣ z).card := by
  let I := range (len / p)
  let f : ℕ → ℕ := fun t ↦ q + 2 * (e + p * t)
  have hinj : Set.InjOn f I := by
    intro x hx y hy hxy
    dsimp [f] at hxy
    have h₁ : e + p * x = e + p * y := Nat.eq_of_mul_eq_mul_left (by omega) <|
      Nat.add_left_cancel hxy
    have h₂ : p * x = p * y := Nat.add_left_cancel h₁
    exact Nat.eq_of_mul_eq_mul_left hp h₂
  have himage : I.image f ⊆ (natAP q 2 len).filter fun z ↦ k ∣ z := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht' : t < len / p := by simpa [I] using ht
    have hindex : e + p * t < len := by
      have hsucc : t + 1 ≤ len / p := by omega
      have hmul : p * (t + 1) ≤ p * (len / p) := Nat.mul_le_mul_left p hsucc
      have hdiv : p * (len / p) ≤ len := Nat.mul_div_le len p
      calc
        e + p * t < p + p * t := Nat.add_lt_add_right he (p * t)
        _ = p * (t + 1) := by ring
        _ ≤ len := hmul.trans hdiv
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_natAP.mpr ⟨e + p * t, hindex, rfl⟩
    · obtain ⟨u, hu⟩ := hbase
      obtain ⟨v, hv⟩ := hstep
      refine ⟨u + v * t, ?_⟩
      dsimp [f]
      calc
        q + 2 * (e + p * t) = (q + 2 * e) + (2 * p) * t := by ring
        _ = k * u + (k * v) * t := by rw [hu, hv]
        _ = k * (u + v * t) := by ring
  calc
    len / p = I.card := by simp [I]
    _ = (I.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := card_le_card himage

lemma exists_four_offset {q : ℕ} (hq : 2 ∣ q) :
    ∃ e < 2, 4 ∣ q + 2 * e := by
  rw [Nat.dvd_iff_mod_eq_zero] at hq
  have hq4 : q % 4 < 4 := Nat.mod_lt _ (by omega)
  have hrel : q % 2 = (q % 4) % 2 := by
    exact (Nat.mod_mod_of_dvd q (by omega : 2 ∣ 4)).symm
  interval_cases h : q % 4 <;> simp [h] at hrel
  · exact ⟨0, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · omega
  · exact ⟨1, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · omega

lemma exists_three_offset (q : ℕ) : ∃ e < 3, 3 ∣ q + 2 * e := by
  have hq3 : q % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : q % 3
  · exact ⟨0, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · exact ⟨1, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩
  · exact ⟨2, by omega, by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]; simp [h]⟩

lemma natAP_div_four_lower {q len : ℕ} (hq : 2 ∣ q) :
    len / 2 ≤ ((natAP q 2 len).filter fun z ↦ 4 ∣ z).card := by
  obtain ⟨e, he, hdiv⟩ := exists_four_offset hq
  exact div_terms_natAP_lower (by omega) he hdiv (by norm_num)

lemma natAP_div_three_lower (q len : ℕ) :
    len / 3 ≤ ((natAP q 2 len).filter fun z ↦ 3 ∣ z).card := by
  obtain ⟨e, he, hdiv⟩ := exists_three_offset q
  exact div_terms_natAP_lower (by omega) he hdiv (by norm_num)

lemma centralImage_disjoint_quotientPart {A H S : Finset ℕ} {N k : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hH : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x) (hS : S ⊆ H + H) :
    Disjoint (centralImage A N) (quotientPart S k) := by
  rw [Finset.disjoint_left]
  intro x hxB hxQ
  obtain ⟨a, haA, haN, hax⟩ := centralImage_has_low_divisor hxB
  have hkx : k * x ∈ S := quotientPart_spec hxQ
  have hsum := hS hkx
  simp only [Finset.mem_add] at hsum
  obtain ⟨b, hb, c, hc, hbc⟩ := hsum
  have hb' := hH b hb
  have hc' := hH c hc
  apply hP.not_dvd_add haA hb'.1 hc'.1 (by omega) (by omega)
  rw [hbc]
  exact hax.mul_left k

/-- The long difference-two progression alternative completes Case 2.
This is equations (8)--(12) of Bedert, with every floor loss retained as
an integer inequality. -/
lemma medium_done_of_long_AP {A O : Finset ℕ} {N q : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12)
    (hO : O ⊆ highThird A N)
    (hOlarge : (highThird A N).card ≤ 2 * O.card)
    (heven : ∀ z ∈ O + O, 2 ∣ z)
    (hQfull : natAP q 2 (O.card + O.card - 1) ⊆ O + O) :
    3 * A.card ≤ N + 6 := by
  let H := highThird A N
  let Q := natAP q 2 (H.card - 1)
  let Q3 := quotientPart Q 3
  let Q4 := quotientPart Q 4
  let Ap := Q3 ∪ Q4
  let R := zmodFiber (H + H) (3 : ZMod 6)
  let D := quotientPart R 3
  let C := Ap ∪ D
  change N + 144 ≤ 6 * H.card at hmedium
  change 9 * H.card < 2 * N + 12 at hupper
  change O ⊆ H at hO
  change H.card ≤ 2 * O.card at hOlarge
  have hHpos : 24 ≤ H.card := by
    omega
  have hQsub : Q ⊆ O + O := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    apply hQfull
    apply mem_natAP.mpr
    exact ⟨j, by change j < H.card - 1 at hj; omega, rfl⟩
  have hHI : H ⊆ Icc (2 * N / 3 + 1) N := highThird_subset_interval hsub
  have hQHI : Q ⊆ H + H := hQsub.trans (Finset.add_subset_add hO hO)
  have hQI : Q ⊆ Icc (4 * N / 3 + 1) (2 * N) := by
    intro z hz
    have hsum := hQHI hz
    simp only [Finset.mem_add] at hsum
    obtain ⟨x, hx, y, hy, rfl⟩ := hsum
    have hxI := mem_Icc.mp (hHI hx)
    have hyI := mem_Icc.mp (hHI hy)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hqQ : q ∈ Q := by
    apply mem_natAP.mpr
    exact ⟨0, by change 0 < H.card - 1; omega, by simp⟩
  have hqeven : 2 ∣ q := heven q (hQsub hqQ)
  have hQcard : Q.card = H.card - 1 := by
    simpa [Q] using card_natAP (a := q) (d := 2) (len := H.card - 1) (by omega)
  have hQ4card : H.card ≤ 2 * Q4.card + 2 := by
    have h := natAP_div_four_lower (q := q) (len := H.card - 1) hqeven
    rw [← card_quotientPart (S := Q) (k := 4) (by omega)] at h
    change (H.card - 1) / 2 ≤ Q4.card at h
    omega
  have hQ3card : H.card ≤ 3 * Q3.card + 3 := by
    have h := natAP_div_three_lower q (H.card - 1)
    rw [← card_quotientPart (S := Q) (k := 3) (by omega)] at h
    change (H.card - 1) / 3 ≤ Q3.card at h
    omega
  have hQ34disj : Disjoint Q3 Q4 := by
    rw [Finset.disjoint_left]
    intro x hx3 hx4
    have h3x : 3 * x ∈ Q := quotientPart_spec hx3
    have h4x : 4 * x ∈ Q := quotientPart_spec hx4
    obtain ⟨j3, hj3, heq3⟩ := mem_natAP.mp h3x
    obtain ⟨j4, hj4, heq4⟩ := mem_natAP.mp h4x
    have hqI := mem_Icc.mp (hQI hqQ)
    have hfloor : 4 * N ≤ 3 * (4 * N / 3 + 1) := by omega
    change j3 < H.card - 1 at hj3
    change j4 < H.card - 1 at hj4
    change q + 2 * j3 = 3 * x at heq3
    change q + 2 * j4 = 4 * x at heq4
    omega
  have hApcard : Ap.card = Q3.card + Q4.card := by
    change (Q3 ∪ Q4).card = _
    exact card_union_of_disjoint hQ34disj
  have hHinterval : H ⊆ Icc (2 * N / 3 + 1)
      (2 * N / 3 + (N - 2 * N / 3)) := by
    simpa [H, Nat.add_sub_of_le (by omega : 2 * N / 3 ≤ N)] using hHI
  have hdenseCond : (N - 2 * N / 3) + 6 ≤ 2 * H.card := by
    change N + 144 ≤ 6 * H.card at hmedium
    omega
  have hRdense := dense_residue_Icc (q := 6) (by omega) hHinterval hdenseCond
    (3 : ZMod 6)
  have hDcard : D.card = R.card := by
    change (quotientPart R 3).card = R.card
    rw [card_quotientPart (S := R) (k := 3) (by omega)]
    apply congrArg Finset.card
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.1
    · intro hzR
      refine ⟨hzR, ?_⟩
      have hmodZ := (mem_zmodFiber.mp hzR).2
      have hmod : z % 6 = 3 :=
        (ZMod.natCast_eq_natCast_iff z 3 6).mp hmodZ
      rw [Nat.dvd_iff_mod_eq_zero]
      have hrel : z % 3 = (z % 6) % 3 :=
        (Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)).symm
      omega
  have hDQ3 : Disjoint D Q3 := by
    rw [Finset.disjoint_left]
    intro x hxD hx3
    have h3D : 3 * x ∈ R := quotientPart_spec hxD
    have h3Q : 3 * x ∈ Q := quotientPart_spec hx3
    have hmodZ := (mem_zmodFiber.mp h3D).2
    have hmod : (3 * x) % 6 = 3 := by
      have hm := (ZMod.natCast_eq_natCast_iff (3 * x) 3 6).mp hmodZ
      exact hm
    have he : 2 ∣ 3 * x := heven (3 * x) (hQsub h3Q)
    rw [Nat.dvd_iff_mod_eq_zero] at he
    omega
  let K := Ap ∩ D
  have hKsubQ4 : K ⊆ Q4 := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    have hxAp : x ∈ Ap := hx'.1
    change x ∈ Q3 ∪ Q4 at hxAp
    simp only [Finset.mem_union] at hxAp
    rcases hxAp with hx3 | hx4
    · exact False.elim ((Finset.disjoint_left.mp hDQ3) hx'.2 hx3)
    · exact hx4
  have hKsubD : K ⊆ D := by
    exact fun _ hx ↦ (Finset.mem_inter.mp hx).2
  have hKI : K ⊆ zmodFiber (Icc (4 * N / 9 + 1) (N / 2)) (1 : ZMod 2) := by
    intro x hx
    have hx4 := hKsubQ4 hx
    have hxD := hKsubD hx
    have h4Q : 4 * x ∈ Q := quotientPart_spec hx4
    have h3R : 3 * x ∈ R := quotientPart_spec hxD
    have h4I := mem_Icc.mp (hQI h4Q)
    have h3sum := (mem_zmodFiber.mp h3R).1
    simp only [Finset.mem_add] at h3sum
    obtain ⟨u, hu, v, hv, huv⟩ := h3sum
    have huI := mem_Icc.mp (hHI hu)
    have hvI := mem_Icc.mp (hHI hv)
    have hmodZ := (mem_zmodFiber.mp h3R).2
    have hmod : (3 * x) % 6 = 3 :=
      (ZMod.natCast_eq_natCast_iff (3 * x) 3 6).mp hmodZ
    apply mem_zmodFiber.mpr
    constructor
    · apply mem_Icc.mpr
      constructor <;> omega
    · have hxmod : x % 2 = 1 := by omega
      exact (ZMod.natCast_eq_natCast_iff x 1 2).mpr hxmod
  have hKcap := mul_card_fixed_zmod_le (1 : ZMod 2)
    (hS := hKI.trans (filter_subset _ _)) (fun x hx ↦ (mem_zmodFiber.mp (hKI hx)).2)
  have hCcardEq : C.card + K.card = Ap.card + D.card := by
    simpa [C, K] using Finset.card_union_add_card_inter Ap D
  have hRsum : R ⊆ H + H := filter_subset _ _
  have hHigh : ∀ x ∈ H, x ∈ A ∧ 2 * N / 3 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBdisjQ3 := centralImage_disjoint_quotientPart (k := 3) hP hHigh hQHI
  have hBdisjQ4 := centralImage_disjoint_quotientPart (k := 4) hP hHigh hQHI
  have hBdisjD := centralImage_disjoint_quotientPart (k := 3) hP hHigh hRsum
  have hBdisjC : Disjoint (centralImage A N) C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    change x ∈ Ap ∪ D at hxC
    simp only [Finset.mem_union] at hxC
    rcases hxC with hxAp | hxD
    · change x ∈ Q3 ∪ Q4 at hxAp
      simp only [Finset.mem_union] at hxAp
      rcases hxAp with hx3 | hx4
      · exact (Finset.disjoint_left.mp hBdisjQ3) hxB hx3
      · exact (Finset.disjoint_left.mp hBdisjQ4) hxB hx4
    · exact (Finset.disjoint_left.mp hBdisjD) hxB hxD
  have hCI : C ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro x hxC
    change x ∈ Ap ∪ D at hxC
    simp only [Finset.mem_union] at hxC
    rcases hxC with hxAp | hxD
    · change x ∈ Q3 ∪ Q4 at hxAp
      simp only [Finset.mem_union] at hxAp
      rcases hxAp with hx3 | hx4
      · have h3I := mem_Icc.mp (hQI (quotientPart_spec hx3))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · have h4I := mem_Icc.mp (hQI (quotientPart_spec hx4))
        exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have h3R := quotientPart_spec hxD
      have h3sum := (mem_zmodFiber.mp h3R).1
      simp only [Finset.mem_add] at h3sum
      obtain ⟨u, hu, v, hv, huv⟩ := h3sum
      have huI := mem_Icc.mp (hHI hu)
      have hvI := mem_Icc.mp (hHI hv)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hBI : centralImage A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro b hb
    have hb' := mem_ratSection.mp (centralImage_subset_window hP hsub hb)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcentralCapacity := card_add_card_le_of_disjoint_subsets hBdisjC hBI hCI
  have hCentralCard := card_Icc_le (S := Icc (N / 3 + 1) (2 * N / 3))
    (subset_rfl)
  have hAcard := card_centralImage_add_high hP hsub
  change (centralImage A N).card + H.card = A.card at hAcard
  change 2 * H.card ≤ 6 * (R.card + 1) at hRdense
  change 2 * K.card ≤ (N / 2 + 2) - (4 * N / 9 + 1) at hKcap
  change (centralImage A N).card + C.card ≤
    (Icc (N / 3 + 1) (2 * N / 3)).card at hcentralCapacity
  omega

/-- Complete Case 2 once the Bardaji--Grynkiewicz alternative is available
for the two parity fibers of the top third. -/
lemma caseTwo_of_BG {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12)
    (hBG : ∀ r < 2,
      BGAlternative (parityPart (highThird A N) r) (parityPart (highThird A N) r)) :
    3 * A.card ≤ N + 6 := by
  obtain ⟨r, hr, hrlarge⟩ := exists_large_parityPart (highThird A N)
  let O := parityPart (highThird A N) r
  have hO : O ⊆ highThird A N := filter_subset _ _
  have hOlarge : (highThird A N).card ≤ 2 * O.card := hrlarge
  have heven : ∀ z ∈ O + O, 2 ∣ z := by
    intro z hz
    exact parityPart_sum_even hz
  rcases hBG r hr with hgrowth | hstruct
  · have hgrowth' : 3 * O.card ≤ (O + O).card + 3 := by
      change O.card + O.card + min O.card O.card ≤ (O + O).card + 3 at hgrowth
      simp only [min_self] at hgrowth
      omega
    by_cases hlarge0 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 0).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge0).trans
        (Nat.le_add_right N 6)
    by_cases hlarge1 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 1).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge1).trans
        (Nat.le_add_right N 6)
    by_cases hlarge3 : (centralImage A N).card + 12 ≤
        6 * (centralRight A N 3).card
    · exact (medium_done_of_large_right_slice hP hsub hmedium hlarge3).trans
        (Nat.le_add_right N 6)
    exact (medium_done_of_sumset_growth hP hsub hmedium hO hOlarge heven hgrowth'
      (by omega) (by omega) (by omega)).trans (Nat.le_add_right N 6)
  · obtain ⟨q, d, hd, hQ, hres⟩ := hstruct
    have hOI : O ⊆ Icc (2 * N / 3 + 1) N :=
      hO.trans (highThird_subset_interval hsub)
    have hOmedium : N + 144 ≤ 12 * O.card := by omega
    have hd2 := medium_structural_step_eq_two hOI hOmedium hd hres hQ heven
    subst d
    exact medium_done_of_long_AP hP hsub hmedium hupper hO hOlarge heven hQ

lemma caseTwo {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hmedium : N + 144 ≤ 6 * (highThird A N).card)
    (hupper : 9 * (highThird A N).card < 2 * N + 12) :
    3 * A.card ≤ N + 6 :=
  caseTwo_of_BG hP hsub hmedium hupper fun _ _ ↦ bgAlternative_self _

/-! ### Strengthened-induction infrastructure for Case 3 -/

/-- The additive-constant induction target needed for Problem 13 itself. -/
def CoarseBound (C N : ℕ) (A : Finset ℕ) : Prop :=
  3 * A.card ≤ N + C

/-- The part of `A` in the initial interval ending at `N-a`. -/
def initialPart (A : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  A.filter fun x ↦ x ≤ N - a

/-- The terminal interval of length `a`. -/
def terminalPart (A : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  A.filter fun x ↦ N - a < x

@[simp] lemma mem_initialPart {A : Finset ℕ} {N a x : ℕ} :
    x ∈ initialPart A N a ↔ x ∈ A ∧ x ≤ N - a := by
  simp [initialPart]

@[simp] lemma mem_terminalPart {A : Finset ℕ} {N a x : ℕ} :
    x ∈ terminalPart A N a ↔ x ∈ A ∧ N - a < x := by
  simp [terminalPart]

lemma card_initial_add_terminal (A : Finset ℕ) (N a : ℕ) :
    (initialPart A N a).card + (terminalPart A N a).card = A.card := by
  let P := initialPart A N a
  let T := terminalPart A N a
  have hdisj : Disjoint P T := by
    rw [Finset.disjoint_left]
    intro x hxP hxT
    have hp := mem_initialPart.mp hxP
    have ht := mem_terminalPart.mp hxT
    omega
  have hunion : P ∪ T = A := by
    ext x
    simp only [P, T, Finset.mem_union, mem_initialPart, mem_terminalPart]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      exact (le_or_gt x (N - a)).imp (And.intro hx) (And.intro hx)
  rw [← card_union_of_disjoint hdisj, hunion]

lemma initialPart_subset_Icc {A : Finset ℕ} {N a : ℕ}
    (hsub : A ⊆ Icc 1 N) : initialPart A N a ⊆ Icc 1 (N - a) := by
  intro x hx
  have hx' := mem_initialPart.mp hx
  exact mem_Icc.mpr ⟨(mem_Icc.mp (hsub hx'.1)).1, hx'.2⟩

lemma initialPart_property {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) : IsForbiddenTripleFree (initialPart A N a) :=
  hP.mono (filter_subset _ _)

/-- Failure of the additive-constant target makes every terminal interval
strictly denser than one third. -/
lemma terminal_dense_of_not_coarseBound {A : Finset ℕ} {N a C : ℕ}
    (ha : 0 < a) (haN : a ≤ N)
    (hfail : ¬ CoarseBound C N A)
    (hind : CoarseBound C (N - a) (initialPart A N a)) :
    a < 3 * (terminalPart A N a).card := by
  by_contra hnot
  have htail : 3 * (terminalPart A N a).card ≤ a := by omega
  have hcard := card_initial_add_terminal A N a
  apply hfail
  change 3 * A.card ≤ N + C
  change 3 * (initialPart A N a).card ≤ N - a + C at hind
  have hNa : N - a + a = N := Nat.sub_add_cancel haN
  omega

/-- Elements divisible by `k` in an initial rational segment. -/
def divisibleInitial (A : Finset ℕ) (N k ell : ℕ) : Finset ℕ :=
  A.filter fun x ↦ k ∣ x ∧ ell * x ≤ N

@[simp] lemma mem_divisibleInitial {A : Finset ℕ} {N k ell x : ℕ} :
    x ∈ divisibleInitial A N k ell ↔ x ∈ A ∧ k ∣ x ∧ ell * x ≤ N := by
  simp [divisibleInitial]

lemma card_image_div_divisibleInitial {A : Finset ℕ} {N k ell : ℕ} (hk : 0 < k) :
    ((divisibleInitial A N k ell).image fun x ↦ x / k).card =
      (divisibleInitial A N k ell).card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  change x ∈ divisibleInitial A N k ell at hx
  change y ∈ divisibleInitial A N k ell at hy
  have hxdiv := (mem_divisibleInitial.mp hx).2.1
  have hydiv := (mem_divisibleInitial.mp hy).2.1
  calc
    x = k * (x / k) := (Nat.mul_div_cancel' hxdiv).symm
    _ = k * (y / k) := congrArg (fun z ↦ k * z) (by simpa using hxy)
    _ = y := Nat.mul_div_cancel' hydiv

lemma image_div_divisibleInitial_subset {A : Finset ℕ} {N k ell : ℕ}
    (hk : 0 < k) (hell : 0 < ell) (hsub : A ⊆ Icc 1 N) :
    (divisibleInitial A N k ell).image (fun x ↦ x / k) ⊆
      Icc 1 (N / (k * ell)) := by
  intro y hy
  simp only [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx' := mem_divisibleInitial.mp hx
  have hxpos := (mem_Icc.mp (hsub hx'.1)).1
  have hxmul : k * (x / k) = x := Nat.mul_div_cancel' hx'.2.1
  apply mem_Icc.mpr
  constructor
  · have : 0 < x / k := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd hxpos hx'.2.1
      · exact hk
    omega
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < k * ell)).2
    calc
      x / k * (k * ell) = ell * (k * (x / k)) := by ring
      _ = ell * x := by rw [hxmul]
      _ ≤ N := hx'.2.2

lemma image_div_divisibleInitial_property {A : Finset ℕ} {N k ell : ℕ}
    (hk : 0 < k) (hP : IsForbiddenTripleFree A) :
    IsForbiddenTripleFree
      ((divisibleInitial A N k ell).image fun x ↦ x / k) := by
  apply (hP.mono (filter_subset _ _)).map_div hk
  intro x hx
  exact (mem_divisibleInitial.mp hx).2.1

lemma divisibleInitial_card_bound_coarse {A : Finset ℕ} {N k ell C : ℕ}
    (hk : 0 < k) (hell : 0 < ell) (hP : IsForbiddenTripleFree A)
    (hsub : A ⊆ Icc 1 N)
    (hind : CoarseBound C (N / (k * ell))
      ((divisibleInitial A N k ell).image fun x ↦ x / k)) :
    3 * (divisibleInitial A N k ell).card ≤ N / (k * ell) + C := by
  let D := divisibleInitial A N k ell
  let Q := D.image fun x ↦ x / k
  have hcard : Q.card = D.card := card_image_div_divisibleInitial hk
  change 3 * D.card ≤ N / (k * ell) + C
  rw [← hcard]
  exact hind

/-! ### The basic quotient packing in Case 3 -/

/-- `A ∩ (N/2,N]`. -/
def upperHalf (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ratSection A N 1 2 1 1

/-- `A ∩ (N/2,2N/3]`. -/
def middleSixth (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ratSection A N 1 2 2 3

/-- One residue class modulo three in the upper half. -/
def upperHalfResidue (A : Finset ℕ) (N r : ℕ) : Finset ℕ :=
  (upperHalf A N).filter fun x ↦ x % 3 = r % 3

@[simp] lemma mem_upperHalf {A : Finset ℕ} {N x : ℕ} :
    x ∈ upperHalf A N ↔ x ∈ A ∧ N < 2 * x ∧ x ≤ N := by
  simp [upperHalf]

@[simp] lemma mem_middleSixth {A : Finset ℕ} {N x : ℕ} :
    x ∈ middleSixth A N ↔ x ∈ A ∧ N < 2 * x ∧ 3 * x ≤ 2 * N := by
  simp [middleSixth]

@[simp] lemma mem_upperHalfResidue {A : Finset ℕ} {N r x : ℕ} :
    x ∈ upperHalfResidue A N r ↔
      x ∈ upperHalf A N ∧ x % 3 = r % 3 := by
  simp [upperHalfResidue]

lemma upperHalf_subset_interval {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Icc 1 N) :
    upperHalf A N ⊆ Icc (N / 2 + 1) N := by
  intro x hx
  have hx' := mem_upperHalf.mp hx
  exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp (hsub hx'.1)).2⟩

lemma terminalPart_half_eq_upperHalf {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    terminalPart A N ((N + 1) / 2) = upperHalf A N := by
  ext x
  simp only [mem_terminalPart, mem_upperHalf]
  constructor
  · rintro ⟨hx, htail⟩
    exact ⟨hx, by omega, (mem_Icc.mp (hsub hx)).2⟩
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, by omega⟩

lemma card_middleSixth_add_highThird {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    (middleSixth A N).card + (highThird A N).card = (upperHalf A N).card := by
  have hdisj : Disjoint (middleSixth A N) (highThird A N) := by
    rw [Finset.disjoint_left]
    intro x hxM hxH
    have hm := mem_middleSixth.mp hxM
    have hh := mem_highThird.mp hxH
    omega
  have hunion : middleSixth A N ∪ highThird A N = upperHalf A N := by
    ext x
    simp only [Finset.mem_union, mem_middleSixth, mem_highThird, mem_upperHalf]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, (mem_Icc.mp (hsub h.1)).2⟩
      · exact ⟨h.1, by omega, (mem_Icc.mp (hsub h.1)).2⟩
    · intro h
      by_cases hx : 3 * x ≤ 2 * N
      · exact Or.inl ⟨h.1, h.2.1, hx⟩
      · exact Or.inr ⟨h.1, by omega⟩
  rw [← card_union_of_disjoint hdisj, hunion]

lemma card_upperHalf_residues (A : Finset ℕ) (N : ℕ) :
    (upperHalfResidue A N 0).card + (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card = (upperHalf A N).card := by
  let V := upperHalf A N
  have hmap : (V : Set ℕ).MapsTo (fun x ↦ x % 3) (range 3) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at hfiber
  have hs (i : ℕ) (hi : i < 3) :
      V.filter (fun x ↦ x % 3 = i) = upperHalfResidue A N i := by
    ext x
    have himod : i % 3 = i := Nat.mod_eq_of_lt hi
    simp [V, upperHalfResidue, himod]
  rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega)] at hfiber
  change (upperHalf A N).card = 0 + (upperHalfResidue A N 0).card +
    (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card at hfiber
  omega

/-- The sums from the upper half which are divisible by three, divided by
three (Bedert's `A'''`). -/
def thirdSumQuotient (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  quotientPart (zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)) 3

lemma thirdSumQuotient_card (A : Finset ℕ) (N : ℕ) :
    (thirdSumQuotient A N).card =
      (zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)).card := by
  let R := zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)
  change (quotientPart R 3).card = R.card
  rw [card_quotientPart (S := R) (k := 3) (by omega)]
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hz
    refine ⟨hz, ?_⟩
    have hz0 := (mem_zmodFiber.mp hz).2
    rw [ZMod.natCast_eq_zero_iff] at hz0
    exact hz0

lemma thirdSumQuotient_subset_central {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    thirdSumQuotient A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro x hx
  have h3 := quotientPart_spec hx
  have hsum := (mem_zmodFiber.mp h3).1
  simp only [Finset.mem_add] at hsum
  obtain ⟨u, hu, v, hv, huv⟩ := hsum
  have hu' := mem_upperHalf.mp hu
  have hv' := mem_upperHalf.mp hv
  have huN := (mem_Icc.mp (hsub hu'.1)).2
  have hvN := (mem_Icc.mp (hsub hv'.1)).2
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- Equation (18): the central power-of-two image and `A'''` are
disjoint.  The proof includes the exceptional possibility that the low
divisor is not smaller than both upper-half summands. -/
lemma centralImage_disjoint_thirdSumQuotient {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (centralImage A N) (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro b hbB hbQ
  obtain ⟨a, haA, haN, hab⟩ := centralImage_has_low_divisor hbB
  have hbW := mem_ratSection.mp (centralImage_subset_window hP hsub hbB)
  have hbpos : 0 < b := by omega
  have hapos : 0 < a := hP.pos_of_mem hsub haA
  have hab_le : a ≤ b := Nat.le_of_dvd hbpos hab
  have h3 := quotientPart_spec hbQ
  have hsum := (mem_zmodFiber.mp h3).1
  simp only [Finset.mem_add] at hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  by_cases hax : a < x
  · by_cases hay : a < y
    · apply hP.not_dvd_add haA hx'.1 hy'.1 hax hay
      rw [hxy]
      exact hab.mul_left 3
    · have : x > N := by omega
      omega
  · have : y > N := by omega
    omega

lemma caseThree_basic_packing {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (centralImage A N).card + (thirdSumQuotient A N).card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card := by
  apply card_add_card_le_of_disjoint_subsets
    (centralImage_disjoint_thirdSumQuotient hP hsub)
  · intro b hb
    have hb' := mem_ratSection.mp (centralImage_subset_window hP hsub hb)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact thirdSumQuotient_subset_central hsub

lemma upperHalf_sum_residue_zero_lower {A : Finset ℕ} {N : ℕ}
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty) :
    2 * (upperHalf A N).card ≤
      3 * ((zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)).card + 1) := by
  let V := upperHalf A N
  let V0 := upperHalfResidue A N 0
  let V1 := upperHalfResidue A N 1
  let V2 := upperHalfResidue A N 2
  let R := zmodFiber (V + V) (0 : ZMod 3)
  change 2 * V.card ≤ 3 * (R.card + 1)
  change V1.Nonempty at hV1
  change V2.Nonempty at hV2
  have hpart := card_upperHalf_residues A N
  change V0.card + V1.card + V2.card = V.card at hpart
  have h12sub : V1 + V2 ⊆ R := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
        change x % 3 = 1 % 3
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 2 := by
        apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
        change y % 3 = 2 % 3
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      decide
  have h12cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hV1 hV2
  have h12 : V1.card + V2.card ≤ R.card + 1 := by
    change V1.card + V2.card - 1 ≤ (V1 + V2).card at h12cd
    have hsubcard : (V1 + V2).card ≤ R.card := card_le_card h12sub
    have hV1pos : 0 < V1.card := card_pos.mpr hV1
    have hV2pos : 0 < V2.card := card_pos.mpr hV2
    omega
  by_cases hzero : 3 * V0.card < V.card
  · omega
  · have hV0 : V0.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hV1pos : 0 < V1.card := card_pos.mpr hV1
      simp only [hempty, card_empty, mul_zero] at hzero hpart
      omega
    have h00sub : V0 + V0 ⊆ R := by
      intro z hz
      simp only [Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := mem_upperHalfResidue.mp hx
      have hy' := mem_upperHalfResidue.mp hy
      apply mem_zmodFiber.mpr
      constructor
      · exact Finset.add_mem_add hx'.1 hy'.1
      · have hxZ : (x : ZMod 3) = 0 := by
          apply (ZMod.natCast_eq_natCast_iff x 0 3).mpr
          change x % 3 = 0 % 3
          simpa using hx'.2
        have hyZ : (y : ZMod 3) = 0 := by
          apply (ZMod.natCast_eq_natCast_iff y 0 3).mpr
          change y % 3 = 0 % 3
          simpa using hy'.2
        push_cast
        rw [hxZ, hyZ]
        rfl
    have h00cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hV0 hV0
    have h00 : 2 * V0.card ≤ R.card + 1 := by
      change V0.card + V0.card - 1 ≤ (V0 + V0).card at h00cd
      have hsubcard : (V0 + V0).card ≤ R.card := card_le_card h00sub
      have hV0pos : 0 < V0.card := card_pos.mpr hV0
      omega
    omega

lemma thirdSumQuotient_lower {A : Finset ℕ} {N : ℕ}
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty) :
    2 * (upperHalf A N).card ≤ 3 * ((thirdSumQuotient A N).card + 1) := by
  rw [thirdSumQuotient_card]
  exact upperHalf_sum_residue_zero_lower hV1 hV2

/-- If the middle sixth is larger than half the top third, equation (18)
already gives the ceiling branch of the induction. -/
lemma caseThree_of_large_middle {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV1 : (upperHalfResidue A N 1).Nonempty)
    (hV2 : (upperHalfResidue A N 2).Nonempty)
    (hmid : (highThird A N).card + 3 ≤ 2 * (middleSixth A N).card) :
    3 * A.card ≤ N + 2 := by
  have hVcard := card_middleSixth_add_highThird hsub
  have hD := thirdSumQuotient_lower hV1 hV2
  have hDH : (highThird A N).card ≤ (thirdSumQuotient A N).card := by
    omega
  have hpack := caseThree_basic_packing hP hsub
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  have hAcard := card_centralImage_add_high hP hsub
  omega

/-! ### The modified half-window image (Bedert's Lemma 5) -/

def lowHalf (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter fun a ↦ 2 * a ≤ N

noncomputable def halfImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (scaledMove 0 N 4)

@[simp] lemma mem_lowHalf {A : Finset ℕ} {N a : ℕ} :
    a ∈ lowHalf A N ↔ a ∈ A ∧ 2 * a ≤ N := by
  simp [lowHalf]

lemma halfImage_mem_iff {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImage A N ↔
      ∃ a ∈ A, 2 * a ≤ N ∧ scaledMove 0 N 4 a = b := by
  simp only [halfImage, Finset.mem_image, mem_lowHalf]
  constructor
  · rintro ⟨a, ⟨ha, haN⟩, rfl⟩
    exact ⟨a, ha, haN, rfl⟩
  · rintro ⟨a, ha, haN, rfl⟩
    exact ⟨a, ⟨ha, haN⟩, rfl⟩

lemma halfImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    halfImage A N ⊆ Icc (N / 4 + 1) (N / 2) := by
  intro b hb
  obtain ⟨a, haA, haN, rfl⟩ := halfImage_mem_iff.mp hb
  have hapos := hP.pos_of_mem hsub haA
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 4) (by omega) hapos
  have hup := scaledMove_le (b := 0) (T := N) (q := 4) (by omega) hapos (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma halfImage_has_low_divisor {A : Finset ℕ} {N b : ℕ} (hb : b ∈ halfImage A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ b := by
  obtain ⟨a, haA, haN, rfl⟩ := halfImage_mem_iff.mp hb
  exact ⟨a, haA, haN, dvd_scaledMove 0 N 4 a⟩

noncomputable def halfImageUpper (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ N < 3 * b

noncomputable def halfImageMovable (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ 3 * b ≤ N ∧ b % 4 = 2

noncomputable def halfImageLeftover (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (halfImage A N).filter fun b ↦ 3 * b ≤ N ∧ b % 4 ≠ 2

@[simp] lemma mem_halfImageUpper {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageUpper A N ↔ b ∈ halfImage A N ∧ N < 3 * b := by
  simp [halfImageUpper]

@[simp] lemma mem_halfImageMovable {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageMovable A N ↔
      b ∈ halfImage A N ∧ 3 * b ≤ N ∧ b % 4 = 2 := by
  simp [halfImageMovable]

@[simp] lemma mem_halfImageLeftover {A : Finset ℕ} {N b : ℕ} :
    b ∈ halfImageLeftover A N ↔
      b ∈ halfImage A N ∧ 3 * b ≤ N ∧ b % 4 ≠ 2 := by
  simp [halfImageLeftover]

lemma scaledMove_eq_self_of_odd {T q a : ℕ} (hodd : scaledMove 0 T q a % 2 = 1) :
    scaledMove 0 T q a = a := by
  by_cases he : scaledWindowExp 0 T q a = 0
  · simp [scaledMove, he]
  · have hepos : 0 < scaledWindowExp 0 T q a := Nat.pos_of_ne_zero he
    have hpow : 2 ∣ 2 ^ scaledWindowExp 0 T q a := by
      exact dvd_pow_self 2 (Nat.ne_of_gt hepos)
    have hdiv : 2 ∣ scaledMove 0 T q a := by
      rw [scaledMove]
      exact dvd_mul_of_dvd_left hpow a
    rw [Nat.dvd_iff_mod_eq_zero] at hdiv
    omega

/-! ### The middle-sixth reserve -/

/-- One ordinary residue class modulo four. -/
def modFourPart (H : Finset ℕ) (r : ℕ) : Finset ℕ :=
  H.filter fun x ↦ x % 4 = r % 4

@[simp] lemma mem_modFourPart {H : Finset ℕ} {r x : ℕ} :
    x ∈ modFourPart H r ↔ x ∈ H ∧ x % 4 = r % 4 := by
  simp [modFourPart]

/-- The odd part is the disjoint union of the classes `1` and `3` modulo
four. -/
lemma card_modFour_one_add_three (H : Finset ℕ) :
    (modFourPart H 1).card + (modFourPart H 3).card =
      (parityPart H 1).card := by
  have hdisj : Disjoint (modFourPart H 1) (modFourPart H 3) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    have h1 := (mem_modFourPart.mp hx1).2
    have h3 := (mem_modFourPart.mp hx3).2
    omega
  have hunion : modFourPart H 1 ∪ modFourPart H 3 = parityPart H 1 := by
    ext x
    simp only [Finset.mem_union, mem_modFourPart, mem_parityPart]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, by omega⟩
      · exact ⟨hx.1, by omega⟩
    · intro hx
      have hmod : x % 4 < 4 := Nat.mod_lt _ (by omega)
      have hpar : x % 4 % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd x (by omega : 2 ∣ 4)]
        exact hx.2
      interval_cases x % 4 <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion]

/-- The divisible-by-four sums in the top-third self-sum. -/
def highFourSums (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  zmodFiber (highThird A N + highThird A N) (0 : ZMod 4)

/-- The lower and upper halves partition `A`. -/
lemma card_lowHalf_add_upperHalf {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    (lowHalf A N).card + (upperHalf A N).card = A.card := by
  have hdisj : Disjoint (lowHalf A N) (upperHalf A N) := by
    rw [Finset.disjoint_left]
    intro x hxL hxU
    have hl := mem_lowHalf.mp hxL
    have hu := mem_upperHalf.mp hxU
    omega
  have hunion : lowHalf A N ∪ upperHalf A N = A := by
    ext x
    simp only [Finset.mem_union, mem_lowHalf, mem_upperHalf]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      have hxN := (mem_Icc.mp (hsub hx)).2
      by_cases hlow : 2 * x ≤ N
      · exact Or.inl ⟨hx, hlow⟩
      · exact Or.inr ⟨hx, by omega, hxN⟩
  rw [← card_union_of_disjoint hdisj, hunion]

/-- The same zero-residue growth calculation, retaining only the absolute
additive estimate needed by the final coarse induction. -/
lemma caseThree_zero_growth_coarse {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hgrowth : 3 * (upperHalfResidue A N 0).card ≤
      (upperHalfResidue A N 0 + upperHalfResidue A N 0).card + 3) :
    3 * A.card ≤ N + 11 := by
  let V := upperHalf A N
  let V0 := upperHalfResidue A N 0
  let R := zmodFiber (V + V) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  let B := centralImage A N
  let Y := middleSixth A N
  let H := highThird A N
  have h00 : V0 + V0 ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff x 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 0 := by
        apply (ZMod.natCast_eq_zero_iff y 3).mpr
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      rfl
  have hRlower : 3 * V0.card ≤ R.card + 3 := by
    change 3 * V0.card ≤ (V0 + V0).card + 3 at hgrowth
    have hc := card_le_card h00
    omega
  have hQcard := thirdSumQuotient_card A N
  change Q.card = R.card at hQcard
  change V.card ≤ 3 * V0.card at hdom
  have hVQ : V.card ≤ Q.card + 3 := by omega
  have hpack := caseThree_basic_packing hP hsub
  change B.card + Q.card ≤ (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  omega

/-- In the nonzero-residue branch, sumset growth finishes as soon as the
two residue classes (including the smaller one once more) cover the top
third. -/
lemma caseThree_nonzero_growth {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hgrowth :
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card ≤
          (upperHalfResidue A N 1 + upperHalfResidue A N 2).card + 3)
    (hcover : (highThird A N).card + 3 ≤
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card) :
    3 * A.card ≤ N + 2 := by
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let R := zmodFiber (upperHalf A N + upperHalf A N) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  let B := centralImage A N
  let H := highThird A N
  have h12 : V₁ + V₂ ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hx'.1 hy'.1
    · have hxZ : (x : ZMod 3) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
        change x % 3 = 1 % 3
        simpa using hx'.2
      have hyZ : (y : ZMod 3) = 2 := by
        apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
        change y % 3 = 2 % 3
        simpa using hy'.2
      push_cast
      rw [hxZ, hyZ]
      decide
  have hRcard : (V₁ + V₂).card ≤ R.card := card_le_card h12
  have hQcard := thirdSumQuotient_card A N
  change Q.card = R.card at hQcard
  change V₁.card + V₂.card + min V₁.card V₂.card ≤
    (V₁ + V₂).card + 3 at hgrowth
  change H.card + 3 ≤
    V₁.card + V₂.card + min V₁.card V₂.card at hcover
  have hHQ : H.card ≤ Q.card := by omega
  have hpack := caseThree_basic_packing hP hsub
  change B.card + Q.card ≤ (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
    simp
    omega
  omega

/-- A dense subset of the upper half lying in one class modulo three has
the same residue-rich self-sums as a dense subset of a compressed interval.
The coprimality assumption lets a `q`-fiber and the fixed mod-three class
combine into one class modulo `3q`. -/
lemma dense_residue_upperHalf_fixed_three {U : Finset ℕ} {N q r : ℕ}
    (hq : 0 < q) (hcop : Nat.Coprime 3 q)
    (hU : U ⊆ Icc (N / 2 + 1) N)
    (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hdense : N / 6 + q + 1 ≤ 2 * U.card) (a : ZMod q) :
    2 * U.card ≤ q * ((zmodFiber (U + U) a).card + 1) := by
  apply dense_residue hq a (D := N / 6 + q + 1) ?_ hdense
  intro i
  let F := zmodFiber U i
  by_cases hF : F.Nonempty
  · obtain ⟨x, hxF⟩ := hF
    have hx := mem_zmodFiber.mp hxF
    have hFI : F ⊆ Icc (N / 2 + 1) N := (filter_subset _ _).trans hU
    have hres : ∀ y ∈ F, (y : ZMod (3 * q)) = (x : ZMod (3 * q)) := by
      intro y hyF
      have hy := mem_zmodFiber.mp hyF
      apply (ZMod.natCast_eq_natCast_iff y x (3 * q)).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      constructor
      · change y % 3 = x % 3
        rw [hthree y hy.1, hthree x hx.1]
      · exact (ZMod.natCast_eq_natCast_iff y x q).mp (hy.2.trans hx.2.symm)
    have hcap := mul_card_fixed_zmod_le (x : ZMod (3 * q)) hFI hres
    change 3 * q * F.card ≤ (N + 3 * q) - (N / 2 + 1) at hcap
    change q * F.card < N / 6 + q + 1
    have hL : N / 2 + 1 ≤ N + 3 * q := by omega
    have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
    by_contra hn
    have hlower : N / 6 + q + 1 ≤ q * F.card := by omega
    have hlower3 := Nat.mul_le_mul_left 3 hlower
    have heq : 3 * (q * F.card) = 3 * q * F.card := by ring
    rw [heq] at hlower3
    omega
  · have hFe : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    simp [F, hFe]

/-- The power-of-two half-window image of lower-half elements not divisible
by three. -/
noncomputable def lowNonthreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).image (scaledMove 0 N 4)

noncomputable def lowNonthreeImagePart (A : Finset ℕ) (N r : ℕ) : Finset ℕ :=
  (lowNonthreeImage A N).filter fun x ↦ x % 3 = r % 3

@[simp] lemma mem_lowNonthreeImagePart {A : Finset ℕ} {N r x : ℕ} :
    x ∈ lowNonthreeImagePart A N r ↔
      x ∈ lowNonthreeImage A N ∧ x % 3 = r % 3 := by
  simp [lowNonthreeImagePart]

lemma card_lowNonthreeImage {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (lowNonthreeImage A N).card =
      ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
  intro x hx
  exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)

lemma lowNonthreeImage_subset_halfImage (A : Finset ℕ) (N : ℕ) :
    lowNonthreeImage A N ⊆ halfImage A N := by
  intro z hz
  simp only [lowNonthreeImage, halfImage, mem_image] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, (mem_filter.mp hx).1, rfl⟩

lemma lowNonthreeImage_not_dvd_three {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ lowNonthreeImage A N) : ¬ 3 ∣ z := by
  simp only [lowNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx3 : ¬ 3 ∣ x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact (mem_filter.mp hx).2
  intro hd
  rw [scaledMove] at hd
  rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hd with hp | hxdiv
  · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
    norm_num at this
  · exact hx3 hxdiv

lemma card_lowNonthreeImage_parts {A : Finset ℕ} {N : ℕ} :
    (lowNonthreeImagePart A N 1).card +
      (lowNonthreeImagePart A N 2).card = (lowNonthreeImage A N).card := by
  let C := lowNonthreeImage A N
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hdisj : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 := (mem_lowNonthreeImagePart.mp hz1).2
    have h2 := (mem_lowNonthreeImagePart.mp hz2).2
    omega
  have hunion : C₁ ∪ C₂ = C := by
    ext z
    simp only [C₁, C₂, C, mem_union, mem_lowNonthreeImagePart]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      have hmod := Nat.mod_lt z (by omega : 0 < 3)
      have hn := lowNonthreeImage_not_dvd_three hz
      rw [Nat.dvd_iff_mod_eq_zero] at hn
      interval_cases z % 3 <;> simp_all
  rw [← card_union_of_disjoint hdisj, hunion]

lemma lowNonthreeImage_subset_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    lowNonthreeImage A N ⊆ Icc (N / 4 + 1) (N / 2) :=
  (lowNonthreeImage_subset_halfImage A N).trans (halfImage_subset_window hP hsub)

/-- The modulus-four packing estimate used when one nonzero class modulo
three dominates the upper half. -/
lemma upperThreeClass_pack_four {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = (2 * r) % 3)
    (hdense : N / 6 + 5 ≤ 2 * U.card) :
    12 * B.card + 6 * U.card ≤ N + 24 := by
  let S := zmodFiber (U + U) (0 : ZMod 4)
  let e := 4 * ((2 * r) % 3)
  let W := zmodFiber (Icc (N + 1) (2 * N)) (e : ZMod 12)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 4) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 4)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 4⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ U + U := filter_subset _ _
  have hBW : B.image (fun b ↦ 4 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub
      (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (4 * b) e 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 12).mpr
      have h4 := (ZMod.natCast_eq_zero_iff (x + y) 4).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h4
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hUH hSsum hBW hSW
  have hWI : W ⊆ Icc (N + 1) (2 * N) := filter_subset _ _
  have hWres : ∀ z ∈ W, (z : ZMod 12) = (e : ZMod 12) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (e : ZMod 12) hWI hWres
  change 2 * U.card ≤ 4 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 12 * W.card ≤ (2 * N + 12) - (N + 1) at hcap
  omega

/-- The companion modulus-five packing estimate. -/
lemma upperThreeClass_pack_five {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hdense : N / 6 + 6 ≤ 2 * U.card) :
    10 * B.card + 4 * U.card ≤ N + 30 := by
  let S := zmodFiber (U + U) (0 : ZMod 5)
  let e := 5 * (r % 3)
  let W := zmodFiber (Icc (N + 1) (5 * N / 2)) (e : ZMod 15)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 5) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 5)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 5 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 5⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hSsum : S ⊆ U + U := filter_subset _ _
  have hBW : B.image (fun b ↦ 5 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub
      (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (5 * b) e 15).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 15).mpr
      have h5 := (ZMod.natCast_eq_zero_iff (x + y) 5).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h5
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 5) (t := N / 2) (by omega) hP hBdiv hUH hSsum hBW hSW
  have hWI : W ⊆ Icc (N + 1) (5 * N / 2) := filter_subset _ _
  have hWres : ∀ z ∈ W, (z : ZMod 15) = (e : ZMod 15) := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (e : ZMod 15) hWI hWres
  change 2 * U.card ≤ 5 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 15 * W.card ≤ (5 * N / 2 + 15) - (N + 1) at hcap
  omega

/-- If one nonzero residue class is absent in the nonzero-dominant branch,
the two coprime residue packings and induction on the multiples of three
give a linear saving. -/
lemma caseThree_nonzero_empty {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hempty : ¬ (upperHalfResidue A N 2).Nonempty)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hV₂card : V₂.card = 0 := by
    exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hempty)
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hV₁dense4 : N / 6 + 5 ≤ 2 * V₁.card := by omega
  have hV₁dense5 : N / 6 + 6 ≤ 2 * V₁.card := by omega
  have hV₁sub : V₁ ⊆ V := filter_subset _ _
  have hV₁three : ∀ x ∈ V₁, x % 3 = 1 := by
    intro x hx
    have := (mem_upperHalfResidue.mp hx).2
    simpa using this
  have hp4 := upperThreeClass_pack_four (r := 1) hP hsub hV₁sub hV₁three
    (B := C₂) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₁dense4
  have hp5 := upperThreeClass_pack_five (r := 1) hP hsub hV₁sub hV₁three
    (B := C₁) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₁dense5
  change 12 * C₂.card + 6 * V₁.card ≤ N + 24 at hp4
  change 10 * C₁.card + 4 * V₁.card ≤ N + 30 at hp5
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    hV₁sub.trans (upperHalf_subset_interval hsub)
  have hV₁res : ∀ x ∈ V₁, (x : ZMod 3) = 1 := by
    intro x hx
    apply (ZMod.natCast_eq_natCast_iff' x 1 3).mpr
    simpa using hV₁three x hx
  have hV₁cap := mul_card_fixed_zmod_le (1 : ZMod 3) hV₁I hV₁res
  change 3 * V₁.card ≤ (N + 3) - (N / 2 + 1) at hV₁cap
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, ?_, by have := (mem_Icc.mp (hsub hxL.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hx'.2
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, ?_, by have := (mem_Icc.mp (hsub hxV.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa using hx'.2
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  have hAcover : A.card ≤ D.card + C₁.card + C₂.card + V₁.card := by
    omega
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  change 3 * A.card ≤ N + C
  omega

lemma caseThree_nonzero_empty_one {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hempty : ¬ (upperHalfResidue A N 1).Nonempty)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hV₁card : V₁.card = 0 :=
    card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hempty)
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hV₂dense4 : N / 6 + 5 ≤ 2 * V₂.card := by omega
  have hV₂dense5 : N / 6 + 6 ≤ 2 * V₂.card := by omega
  have hV₂sub : V₂ ⊆ V := filter_subset _ _
  have hV₂three : ∀ x ∈ V₂, x % 3 = 2 % 3 := by
    intro x hx
    exact (mem_upperHalfResidue.mp hx).2
  have hp4 := upperThreeClass_pack_four (r := 2) hP hsub hV₂sub hV₂three
    (B := C₁) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₂dense4
  have hp5 := upperThreeClass_pack_five (r := 2) hP hsub hV₂sub hV₂three
    (B := C₂) (fun _ hb ↦ (mem_lowNonthreeImagePart.mp hb).1)
    (fun _ hb ↦ by simpa using (mem_lowNonthreeImagePart.mp hb).2) hV₂dense5
  change 12 * C₁.card + 6 * V₂.card ≤ N + 24 at hp4
  change 10 * C₂.card + 4 * V₂.card ≤ N + 30 at hp5
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    hV₂sub.trans (upperHalf_subset_interval hsub)
  have hV₂res : ∀ x ∈ V₂, (x : ZMod 3) = 2 := by
    intro x hx
    apply (ZMod.natCast_eq_natCast_iff' x 2 3).mpr
    exact hV₂three x hx
  have hV₂cap := mul_card_fixed_zmod_le (2 : ZMod 3) hV₂I hV₂res
  change 3 * V₂.card ≤ (N + 3) - (N / 2 + 1) at hV₂cap
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, ?_, by have := (mem_Icc.mp (hsub hxL.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hx'.2
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, ?_, by have := (mem_Icc.mp (hsub hxV.1)).2; omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa using hx'.2
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  have hAcover : A.card ≤ D.card + C₁.card + C₂.card + V₂.card := by omega
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  change 3 * A.card ≤ N + C
  omega

/-- The first term of a nonempty progression lying in `V₁ + V₂` is divisible
by three. -/
lemma nonzero_AP_start_dvd_three {A : Finset ℕ} {N a d : ℕ}
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (hQ : natAP a d ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 ∣ a := by
  have hlen : 0 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    have h1 := card_pos.mpr hV₁
    have h2 := card_pos.mpr hV₂
    omega
  have ha : a ∈ upperHalfResidue A N 1 + upperHalfResidue A N 2 :=
    hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp ha
  subst a
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hx3 := (mem_upperHalfResidue.mp hx).2
  have hy3 := (mem_upperHalfResidue.mp hy).2
  omega

/-- In the structural nonzero-residue branch the common difference is one
of `3,6,9`. -/
lemma nonzero_structural_step {A : Finset ℕ} {N a d : ℕ}
    (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hd : 0 < d)
    (hQ : natAP a d ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) d) :
    d = 3 ∨ d = 6 ∨ d = 9 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  have hV₁sub : V₁ ⊆ V := filter_subset _ _
  have hV₂sub : V₂ ⊆ V := filter_subset _ _
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    hV₁sub.trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    hV₂sub.trans (upperHalf_subset_interval hsub)
  have hres₁ : InOneResidue V₁ d := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ d := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change d * V₁.card ≤ (N + d) - (N / 2 + 1) at hcap₁
  change d * V₂.card ≤ (N + d) - (N / 2 + 1) at hcap₂
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hsumlarge : N / 9 + 1 ≤ V₁.card + V₂.card := by omega
  have hlen : 2 ≤ V₁.card + V₂.card - 1 := by
    have hp₁ : 0 < V₁.card := card_pos.mpr hV₁
    have hp₂ : 0 < V₂.card := card_pos.mpr hV₂
    omega
  have hlen0 : 0 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    change 0 < V₁.card + V₂.card - 1
    omega
  have hlen1 : 1 < (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1 := by
    change 1 < V₁.card + V₂.card - 1
    omega
  have hqa : a ∈ V₁ + V₂ := hQ (mem_natAP.mpr ⟨0, hlen0, by simp⟩)
  have hqad : a + d ∈ V₁ + V₂ := by
    apply hQ
    exact mem_natAP.mpr ⟨1, hlen1, by simp⟩
  have hthreeSum : ∀ z ∈ V₁ + V₂, 3 ∣ z := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx3 := (mem_upperHalfResidue.mp hx).2
    have hy3 := (mem_upperHalfResidue.mp hy).2
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    omega
  have h3a := hthreeSum a hqa
  have h3ad := hthreeSum (a + d) hqad
  have h3d : 3 ∣ d := by
    obtain ⟨ka, hka⟩ := h3a
    obtain ⟨kad, hkad⟩ := h3ad
    refine ⟨kad - ka, ?_⟩
    omega
  have hdlt : d < 12 := by
    by_contra hnot
    have hd12 : 12 ≤ d := by omega
    obtain ⟨k₁, hk₁⟩ : ∃ k, V₁.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₁)
    obtain ⟨k₂, hk₂⟩ : ∃ k, V₂.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₂)
    have hL : N / 2 + 1 ≤ N := by omega
    have hspan₁ : d * k₁ ≤ N - (N / 2 + 1) := by
      rw [hk₁, Nat.mul_add, Nat.mul_one] at hcap₁
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap₁
      omega
    have hspan₂ : d * k₂ ≤ N - (N / 2 + 1) := by
      rw [hk₂, Nat.mul_add, Nat.mul_one] at hcap₂
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap₂
      omega
    have hmul₁ : 12 * k₁ ≤ d * k₁ := Nat.mul_le_mul_right k₁ hd12
    have hmul₂ : 12 * k₂ ≤ d * k₂ := Nat.mul_le_mul_right k₂ hd12
    rw [hk₁, hk₂] at hsumlarge
    omega
  obtain ⟨k, hk⟩ := h3d
  have hklt : k < 4 := by nlinarith
  interval_cases k <;> omega

/-- Move lower-half nonmultiples of three into the upper half by powers of
two. -/
noncomputable def upperNonthreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).image (scaledMove 0 N 2)

lemma card_upperNonthreeImage {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (upperNonthreeImage A N).card =
      ((lowHalf A N).filter fun x ↦ x % 3 ≠ 0).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
  intro x hx
  exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)

lemma upperNonthreeImage_subset_interval {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    upperNonthreeImage A N ⊆ Icc (N / 2 + 1) N := by
  intro z hz
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  have hhi := scaledMove_le (b := 0) (T := N) (q := 2) (by omega) hxpos (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma upperNonthreeImage_even {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ upperNonthreeImage A N) : z % 2 = 0 := by
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlo := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  have hexp : 0 < scaledWindowExp 0 N 2 x := by
    by_contra he
    have he0 : scaledWindowExp 0 N 2 x = 0 := by omega
    rw [scaledMove, he0] at hlo
    simp only [pow_zero, one_mul] at hlo
    omega
  rw [scaledMove, Nat.mul_mod]
  have hp : 2 ∣ 2 ^ scaledWindowExp 0 N 2 x := dvd_pow_self 2 (Nat.ne_of_gt hexp)
  rw [Nat.dvd_iff_mod_eq_zero] at hp
  simp [hp]

lemma upperNonthreeImage_mod_three_ne_zero {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ upperNonthreeImage A N) : z % 3 ≠ 0 := by
  simp only [upperNonthreeImage, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx3 := (mem_filter.mp hx).2
  intro hz3
  have hd : 3 ∣ scaledMove 0 N 2 x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hz3
  rw [scaledMove] at hd
  rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hd with hp | hxdiv
  · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
    norm_num at this
  · exact hx3 (Nat.dvd_iff_mod_eq_zero.mp hxdiv)

lemma upperNonthreeImage_disjoint_upperHalf {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (upperNonthreeImage A N) (upperHalf A N) := by
  rw [Finset.disjoint_left]
  intro z hzC hzV
  simp only [upperNonthreeImage, mem_image] at hzC
  obtain ⟨x, hx, rfl⟩ := hzC
  have hxL := mem_lowHalf.mp (mem_filter.mp hx).1
  have hzV' := mem_upperHalf.mp hzV
  have hxpos := hP.pos_of_mem hsub hxL.1
  have hlt := lt_scaledMove (b := 0) (T := N) (q := 2) (by omega) hxpos
  exact hP.not_dvd_of_lt hxL.1 hzV'.1 (by omega) (dvd_scaledMove 0 N 2 x)

/-- A set in the upper half consisting of even nonmultiples of three uses
only the residue classes `2,4 (mod 6)`. -/
lemma six_mul_card_even_nonthree_upper_le {S : Finset ℕ} {N : ℕ}
    (hI : S ⊆ Icc (N / 2 + 1) N)
    (heven : ∀ x ∈ S, x % 2 = 0) (hthree : ∀ x ∈ S, x % 3 ≠ 0) :
    6 * S.card ≤ N + 12 := by
  let S₂ := S.filter fun x ↦ x % 6 = 2
  let S₄ := S.filter fun x ↦ x % 6 = 4
  have hdisj : Disjoint S₂ S₄ := by
    rw [Finset.disjoint_left]
    intro x hx₂ hx₄
    have h₂ := (mem_filter.mp hx₂).2
    have h₄ := (mem_filter.mp hx₄).2
    omega
  have hunion : S₂ ∪ S₄ = S := by
    ext x
    simp only [S₂, S₄, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      have h6 : x % 6 < 6 := Nat.mod_lt _ (by omega)
      have h2rel : x % 2 = (x % 6) % 2 :=
        (Nat.mod_mod_of_dvd x (by omega : 2 ∣ 6)).symm
      have h3rel : x % 3 = (x % 6) % 3 :=
        (Nat.mod_mod_of_dvd x (by omega : 3 ∣ 6)).symm
      have he := heven x hx
      have hn := hthree x hx
      interval_cases x % 6 <;> simp_all
  have hcard : S₂.card + S₄.card = S.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hcap₂ := mul_card_fixed_zmod_le (2 : ZMod 6)
    ((filter_subset _ _).trans hI) (fun x hx ↦ by
      apply (ZMod.natCast_eq_natCast_iff' x 2 6).mpr
      simpa using (mem_filter.mp hx).2)
  have hcap₄ := mul_card_fixed_zmod_le (4 : ZMod 6)
    ((filter_subset _ _).trans hI) (fun x hx ↦ by
      apply (ZMod.natCast_eq_natCast_iff' x 4 6).mpr
      simpa using (mem_filter.mp hx).2)
  change 6 * S₂.card ≤ (N + 6) - (N / 2 + 1) at hcap₂
  change 6 * S₄.card ≤ (N + 6) - (N / 2 + 1) at hcap₄
  omega

/-- An odd subset of the upper half contained in one class modulo nine is
contained in one class modulo eighteen. -/
lemma thirtysix_mul_card_odd_one_mod_nine_upper_le {S : Finset ℕ} {N : ℕ}
    (hI : S ⊆ Icc (N / 2 + 1) N) (hodd : ∀ x ∈ S, x % 2 = 1)
    (hres : InOneResidue S 9) : 36 * S.card ≤ N + 36 := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    obtain ⟨r, hr⟩ := hres
    have hmod : ∀ y ∈ S, (y : ZMod 18) = (x : ZMod 18) := by
      intro y hy
      apply (ZMod.natCast_eq_natCast_iff y x 18).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 2 9)).mp
      constructor
      · change y % 2 = x % 2
        rw [hodd y hy, hodd x hx]
      · exact (ZMod.natCast_eq_natCast_iff y x 9).mp
          ((hr y hy).trans (hr x hx).symm)
    have hcap := mul_card_fixed_zmod_le (x : ZMod 18) hI hmod
    change 18 * S.card ≤ (N + 18) - (N / 2 + 1) at hcap
    omega
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp [he]

/-- When the step-nine progression consists of multiples of nine, its
quotient fills essentially the whole zero residue class in the central
third.  Consequently only constantly many lower-half multiples of three
can remain. -/
lemma caseThree_step_nine_zero_low_multiples {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha : a % 9 = 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 * (((lowHalf A N).filter fun x ↦ x % 3 = 0).card) ≤ 9 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  let Q₃ := natAP (a / 3) 3 len
  let B₀ := zmodFiber (centralImage A N) (0 : ZMod 3)
  let L₀ := (lowHalf A N).filter fun x ↦ x % 3 = 0
  let M₀ := L₀.image (scaledMove 0 N 3)
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hsum : N / 9 + 1 ≤ V₁.card + V₂.card := by omega
  have hlen : N / 9 ≤ len := by omega
  have ha9 : 9 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr ha
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show upperHalfResidue A N 1 ⊆ upperHalf A N from filter_subset _ _)
          (show upperHalfResidue A N 2 ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        apply mem_natAP.mpr
        exact ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        rw [Nat.mul_add]
        have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
        omega⟩
    · have ha3 : 3 * (a / 3) = a := Nat.mul_div_cancel' (dvd_trans (by norm_num) ha9)
      have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by omega
      rw [heq]
      simpa using hz
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃res : ∀ z ∈ Q₃, (z : ZMod 3) = 0 := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    rw [ZMod.natCast_eq_zero_iff]
    have ha3 : 3 ∣ a / 3 := by
      obtain ⟨k, hk⟩ := ha9
      subst a
      exact ⟨k, by omega⟩
    exact dvd_add ha3 (dvd_mul_right 3 j)
  have hB₀I : B₀ ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hzB := (mem_zmodFiber.mp hz).1
    have hzW := mem_ratSection.mp (centralImage_subset_window hP hsub hzB)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hB₀res : ∀ z ∈ B₀, (z : ZMod 3) = 0 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hdisj : Disjoint B₀ Q₃ := by
    apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
    · exact filter_subset _ _
    · exact hQ₃sub
  let W := B₀ ∪ Q₃
  have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hB₀I hQ₃I
  have hWres : ∀ z ∈ W, (z : ZMod 3) = 0 := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact hB₀res z hz
    · exact hQ₃res z hz
  have hWcap := mul_card_fixed_zmod_le (0 : ZMod 3) hWI hWres
  have hWcard : W.card = B₀.card + Q₃.card := card_union_of_disjoint hdisj
  have hQ₃card : Q₃.card = len := by
    exact card_natAP (by omega)
  change 3 * W.card ≤ (2 * N / 3 + 3) - (N / 3 + 1) at hWcap
  have hB₀small : B₀.card ≤ 3 := by omega
  have hM₀card : M₀.card = L₀.card := by
    apply card_image_iff.mpr
    apply scaledMove_injOn (hP.mono ((filter_subset _ _).trans (filter_subset _ _)))
    intro x hx
    exact hP.pos_of_mem hsub ((mem_lowHalf.mp (mem_filter.mp hx).1).1)
  have hM₀B₀ : M₀ ⊆ B₀ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_zmodFiber.mpr
    constructor
    · apply centralImage_mem_iff.mpr
      exact ⟨x, hxL.1, by omega, rfl⟩
    · rw [ZMod.natCast_eq_zero_iff]
      have hx3 : 3 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx'.2
      exact dvd_trans hx3 (dvd_scaledMove 0 N 3 x)
  have hM₀le : M₀.card ≤ B₀.card := card_le_card hM₀B₀
  change 3 * L₀.card ≤ 9
  omega

/-- The `0 (mod 9)` part of the step-nine structural case.  This is the
eight-residue packing in Bedert's equation (34), with explicit floor loss. -/
lemma caseThree_nonzero_step_nine_zero {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha : a % 9 = 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 9) :
    3 * A.card ≤ N + 30 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let C := upperNonthreeImage A N
  let E₁ := parityPart V₁ 0
  let O₁ := parityPart V₁ 1
  let E₂ := parityPart V₂ 0
  let O₂ := parityPart V₂ 1
  let E := C ∪ E₁ ∪ E₂
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 9 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 9 := inOneResidue_add_right hV₁ hres
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 9 * V₁.card ≤ (N + 9) - (N / 2 + 1) at hcap₁
  change 9 * V₂.card ≤ (N + 9) - (N / 2 + 1) at hcap₂
  have hV₀ratio : 2 * V₀.card ≤ V₁.card + V₂.card := by omega
  have hsumcap : 9 * (V₁.card + V₂.card) ≤ N + 18 := by omega
  have hV₀cap : 18 * V₀.card ≤ N + 18 := by nlinarith
  have hCcard := card_upperNonthreeImage hP hsub
  change C.card = Lₙ.card at hCcard
  have hCI := upperNonthreeImage_subset_interval hP hsub
  change C ⊆ Icc (N / 2 + 1) N at hCI
  have hCV : Disjoint C V := upperNonthreeImage_disjoint_upperHalf hP hsub
  have hCE₁ : Disjoint C E₁ := hCV.mono_right <|
    (filter_subset _ _).trans (filter_subset _ _)
  have hCE₂ : Disjoint C E₂ := hCV.mono_right <|
    (filter_subset _ _).trans (filter_subset _ _)
  have hE₁E₂ : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h1 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx₁).1).2
    have h2 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx₂).1).2
    omega
  have hCE₁E₂ : Disjoint (C ∪ E₁) E₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx₂
    rcases mem_union.mp hx with hxC | hxE
    · exact (Finset.disjoint_left.mp hCE₂) hxC hx₂
    · exact (Finset.disjoint_left.mp hE₁E₂) hxE hx₂
  have hEcard : E.card = C.card + E₁.card + E₂.card := by
    change (C ∪ E₁ ∪ E₂).card = _
    rw [card_union_of_disjoint hCE₁E₂, card_union_of_disjoint hCE₁]
  have hEI : E ⊆ Icc (N / 2 + 1) N := by
    exact union_subset (union_subset hCI
      (((filter_subset _ _).trans (filter_subset _ _)).trans
        (upperHalf_subset_interval hsub)))
      (((filter_subset _ _).trans (filter_subset _ _)).trans
        (upperHalf_subset_interval hsub))
  have hEeven : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hxC | hxE
      · exact upperNonthreeImage_even hP hsub hxC
      · simpa using (mem_parityPart.mp hxE).2
    · simpa using (mem_parityPart.mp hx).2
  have hEnonthree : ∀ x ∈ E, x % 3 ≠ 0 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hxC | hxE
      · exact upperNonthreeImage_mod_three_ne_zero hxC
      · have h1 := (mem_upperHalfResidue.mp (mem_parityPart.mp hxE).1).2
        omega
    · have h2 := (mem_upperHalfResidue.mp (mem_parityPart.mp hx).1).2
      omega
  have hEcap := six_mul_card_even_nonthree_upper_le hEI hEeven hEnonthree
  have hO₁I : O₁ ⊆ Icc (N / 2 + 1) N :=
    ((filter_subset _ _).trans hV₁I)
  have hO₂I : O₂ ⊆ Icc (N / 2 + 1) N :=
    ((filter_subset _ _).trans hV₂I)
  have hO₁odd : ∀ x ∈ O₁, x % 2 = 1 := by
    intro x hx; simpa using (mem_parityPart.mp hx).2
  have hO₂odd : ∀ x ∈ O₂, x % 2 = 1 := by
    intro x hx; simpa using (mem_parityPart.mp hx).2
  have hO₁cap := thirtysix_mul_card_odd_one_mod_nine_upper_le hO₁I hO₁odd
    (inOneResidue_mono ⟨r₁, hr₁⟩ (filter_subset _ _))
  have hO₂cap := thirtysix_mul_card_odd_one_mod_nine_upper_le hO₂I hO₂odd
    (inOneResidue_mono ⟨r₂, hr₂⟩ (filter_subset _ _))
  have hpar₁ := card_parity_parts V₁
  have hpar₂ := card_parity_parts V₂
  change E₁.card + O₁.card = V₁.card at hpar₁
  change E₂.card + O₂.card = V₂.card at hpar₂
  have hnonzeroPack : 36 * (C.card + V₁.card + V₂.card) ≤ 8 * N + 216 := by
    omega
  have hL₀small := caseThree_step_nine_zero_low_multiples hP hsub htail hdom ha hQ
  change 3 * L₀.card ≤ 9 at hL₀small
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  omega

/-- Move a point of `(N/4,N/2]` into the central third, doubling precisely
the points in its left part. -/
def halfCentralize (N z : ℕ) : ℕ := if 3 * z ≤ N then 2 * z else z

lemma halfCentralize_injOn_interval (N : ℕ) :
    Set.InjOn (halfCentralize N) (Icc (N / 4 + 1) (N / 2)) := by
  intro x hx y hy hxy
  have hxI := mem_Icc.mp hx
  have hyI := mem_Icc.mp hy
  simp only [halfCentralize] at hxy
  split at hxy <;> split at hxy
  · omega
  · omega
  · omega
  · exact hxy

lemma halfCentralize_subset_central {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Icc (N / 4 + 1) (N / 2)) :
    S.image (halfCentralize N) ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
  have hxI := mem_Icc.mp (hS hx)
  simp only [halfCentralize]
  split
  · exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_image_halfCentralize {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Icc (N / 4 + 1) (N / 2)) :
    (S.image (halfCentralize N)).card = S.card := by
  exact card_image_iff.mpr ((halfCentralize_injOn_interval N).mono hS)

/-- Centralizing the half-window image preserves the fact that each point is
a multiple of an originating lower-half member of `A`. -/
lemma halfCentralize_lowNonthree_has_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ (lowNonthreeImage A N).image (halfCentralize N)) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ z := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  have hbH := lowNonthreeImage_subset_halfImage A N hb
  obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor hbH
  refine ⟨a, ha, haN, ?_⟩
  simp only [halfCentralize]
  split
  · exact dvd_trans hab (dvd_mul_left b 2)
  · exact hab

lemma halfCentralized_lowNonthree_disjoint_thirdSum {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint ((lowNonthreeImage A N).image (halfCentralize N))
      (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro z hzC hzQ
  obtain ⟨a, ha, haN, haz⟩ := halfCentralize_lowNonthree_has_divisor hzC
  have h3z := quotientPart_spec hzQ
  have hsum := (mem_zmodFiber.mp h3z).1
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  apply hP.not_dvd_add ha hx'.1 hy'.1 (by omega) (by omega)
  rw [hxy]
  exact haz.mul_left 3

/-- If the step-nine progression has nonzero residue after division by
three, nearly all of the half-window image is forced into one residue in
each of `(N/4,N/3]` and `(N/3,N/2]`. -/
lemma caseThree_step_nine_nonzero_low_nonthree_data
    {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlen : N / 9 ≤ len) (hq : q % 3 ≠ 0)
    (hQsub : natAP q 3 len ⊆ thirdSumQuotient A N) :
    36 * (lowNonthreeImage A N).card ≤ 3 * N + 300 := by
  let C := lowNonthreeImage A N
  let f := halfCentralize N
  let t := q % 3
  let Bad := C.filter fun z ↦ f z % 3 = t
  let Lo := C.filter fun z ↦ f z % 3 ≠ t ∧ 3 * z ≤ N
  let Hi := C.filter fun z ↦ f z % 3 ≠ t ∧ N < 3 * z
  let FBad := Bad.image f
  let Q₃ := natAP q 3 len
  have hCI := lowNonthreeImage_subset_interval hP hsub
  change C ⊆ Icc (N / 4 + 1) (N / 2) at hCI
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by simpa [Q₃] using hQsub
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃res : ∀ z ∈ Q₃, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    apply (ZMod.natCast_eq_natCast_iff' _ t 3).mpr
    change (q + 3 * j) % 3 = t % 3
    dsimp [t]
    omega
  have hFBadI : FBad ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    exact halfCentralize_subset_central ((filter_subset _ _).trans hCI)
  have hFBadres : ∀ z ∈ FBad, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    apply (ZMod.natCast_eq_natCast_iff' _ t 3).mpr
    have htlt' : t < 3 := Nat.mod_lt _ (by omega)
    simpa [Nat.mod_eq_of_lt htlt'] using (mem_filter.mp hx).2
  have hFQ : Disjoint FBad Q₃ := by
    apply (halfCentralized_lowNonthree_disjoint_thirdSum hP hsub).mono
    · exact image_subset_image (filter_subset _ _)
    · exact hQ₃sub
  let W := FBad ∪ Q₃
  have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hFBadI hQ₃I
  have hWres : ∀ z ∈ W, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact hFBadres z hz
    · exact hQ₃res z hz
  have hWcap := mul_card_fixed_zmod_le (t : ZMod 3) hWI hWres
  have hWcard : W.card = FBad.card + Q₃.card := card_union_of_disjoint hFQ
  have hFBadcard : FBad.card = Bad.card :=
    card_image_halfCentralize ((filter_subset _ _).trans hCI)
  have hQ₃card : Q₃.card = len := card_natAP (by omega)
  change 3 * W.card ≤ (2 * N / 3 + 3) - (N / 3 + 1) at hWcap
  have hBadsmall : Bad.card ≤ 3 := by omega
  have htlt : t < 3 := Nat.mod_lt _ (by omega)
  have htne : t ≠ 0 := by simpa [t] using hq
  have hLoI : Lo ⊆ Icc (N / 4 + 1) (N / 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hCI hz'.1)
    exact mem_Icc.mpr ⟨hzI.1, by omega⟩
  have hHiI : Hi ⊆ Icc (N / 3 + 1) (N / 2) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hCI hz'.1)
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩
  have hLores : ∀ z ∈ Lo, (z : ZMod 3) = (t : ZMod 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzn := lowNonthreeImage_not_dvd_three hz'.1
    rw [Nat.dvd_iff_mod_eq_zero] at hzn
    have hzmod := Nat.mod_lt z (by omega : 0 < 3)
    have hbad := hz'.2.1
    have hf : f z = 2 * z := by simp [f, halfCentralize, hz'.2.2]
    rw [hf, Nat.mul_mod] at hbad
    apply (ZMod.natCast_eq_natCast_iff' z t 3).mpr
    interval_cases t <;> interval_cases z % 3 <;> simp_all
  have hHires : ∀ z ∈ Hi, (z : ZMod 3) = ((3 - t : ℕ) : ZMod 3) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzn := lowNonthreeImage_not_dvd_three hz'.1
    rw [Nat.dvd_iff_mod_eq_zero] at hzn
    have hzmod := Nat.mod_lt z (by omega : 0 < 3)
    have hbad := hz'.2.1
    have hnle : ¬ 3 * z ≤ N := by omega
    have hf : f z = z := by simp [f, halfCentralize, hnle]
    rw [hf] at hbad
    apply (ZMod.natCast_eq_natCast_iff' z (3 - t) 3).mpr
    interval_cases t <;> interval_cases z % 3 <;> simp_all
  have hLocap := mul_card_fixed_zmod_le (t : ZMod 3) hLoI hLores
  have hHicap := mul_card_fixed_zmod_le ((3 - t : ℕ) : ZMod 3) hHiI hHires
  change 3 * Lo.card ≤ (N / 3 + 3) - (N / 4 + 1) at hLocap
  change 3 * Hi.card ≤ (N / 2 + 3) - (N / 3 + 1) at hHicap
  have hparts : Bad.card + Lo.card + Hi.card = C.card := by
    have hdisjBL : Disjoint Bad Lo := by
      rw [Finset.disjoint_left]
      intro z hzB hzL
      exact (mem_filter.mp hzL).2.1 (mem_filter.mp hzB).2
    have hdisjBH : Disjoint Bad Hi := by
      rw [Finset.disjoint_left]
      intro z hzB hzH
      exact (mem_filter.mp hzH).2.1 (mem_filter.mp hzB).2
    have hdisjLH : Disjoint Lo Hi := by
      rw [Finset.disjoint_left]
      intro z hzL hzH
      have hl := (mem_filter.mp hzL).2.2
      have hh := (mem_filter.mp hzH).2.2
      omega
    have hdisj : Disjoint (Bad ∪ Lo) Hi := by
      rw [Finset.disjoint_left]
      intro z hz hzH
      rcases mem_union.mp hz with hz | hz
      · exact (Finset.disjoint_left.mp hdisjBH) hz hzH
      · exact (Finset.disjoint_left.mp hdisjLH) hz hzH
    have hunion : Bad ∪ Lo ∪ Hi = C := by
      ext z
      simp only [Bad, Lo, Hi, mem_union, mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hz
        by_cases hb : f z % 3 = t
        · exact Or.inl (Or.inl ⟨hz, hb⟩)
        · by_cases hlo : 3 * z ≤ N
          · exact Or.inl (Or.inr ⟨hz, hb, hlo⟩)
          · exact Or.inr ⟨hz, hb, by omega⟩
    calc
      Bad.card + Lo.card + Hi.card = (Bad ∪ Lo).card + Hi.card := by
        rw [card_union_of_disjoint hdisjBL]
      _ = (Bad ∪ Lo ∪ Hi).card := (card_union_of_disjoint hdisj).symm
      _ = C.card := congrArg Finset.card hunion
  change 36 * C.card ≤ 3 * N + 300
  omega

lemma caseThree_step_nine_nonzero_low_nonthree {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a) (hat : (a / 3) % 3 ≠ 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    36 * (lowNonthreeImage A N).card ≤ 3 * N + 300 := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  change (N + 1) / 2 < 3 * V.card at htail
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hlen : N / 9 ≤ len := by dsimp [len]; omega
  have hQsub : natAP (a / 3) 3 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₁ ⊆ upperHalf A N from filter_subset _ _)
          (show V₂ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_nine_nonzero_low_nonthree_data hP hsub hlen hat hQsub

/-- Common final estimate for a step-nine progression whose divided start
is nonzero modulo three. -/
lemma caseThree_step_nine_nonzero_data {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hVcap : 6 * (upperHalf A N).card ≤ N + 18)
    (hZcap : 36 * (lowNonthreeImage A N).card ≤ 3 * N + 300)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 2
  let Z := lowNonthreeImage A N
  change 6 * V.card ≤ N + 18 at hVcap
  change 36 * Z.card ≤ 3 * N + 300 at hZcap
  have hZcard := card_lowNonthreeImage hP hsub
  change Z.card = Lₙ.card at hZcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    exact ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, hxL.2⟩
  have hL₀le : L₀.card ≤ D.card := card_le_card hL₀D
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 2)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 6 + C at hDbound
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change 3 * A.card ≤ N + C
  omega

lemma caseThree_nonzero_step_nine_nonzero {A : Finset ℕ} {N C a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a) (hat : (a / 3) % 3 ≠ 0)
    (hQ : natAP a 9 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 9)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 2
  let Z := lowNonthreeImage A N
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 9 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 9 := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 9 * V₁.card ≤ (N + 9) - (N / 2 + 1) at hcap₁
  change 9 * V₂.card ≤ (N + 9) - (N / 2 + 1) at hcap₂
  have hVcap : 6 * V.card ≤ N + 18 := by omega
  have hZcap := caseThree_step_nine_nonzero_low_nonthree hP hsub htail hdom
    ha3 hat hQ
  change 36 * Z.card ≤ 3 * N + 300 at hZcap
  have hZcard := card_lowNonthreeImage hP hsub
  change Z.card = Lₙ.card at hZcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx₀ hxₙ
      exact (mem_filter.mp hxₙ).2 (mem_filter.mp hx₀).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        exact if h : x % 3 = 0 then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    exact ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, hxL.2⟩
  have hL₀le : L₀.card ≤ D.card := card_le_card hL₀D
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 2)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 6 + C at hDbound
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change 3 * A.card ≤ N + C
  omega

/-- The step-six structural case.  Exact terminal density removes the small
linear error used in the paper: the even and odd alternatives both close by
packing into the two parity classes of the central third. -/
lemma caseThree_step_six_data {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hVcap : 4 * (upperHalf A N).card ≤ N + 12)
    (hdomlen : 2 * (upperHalf A N).card ≤ 3 * len + 3)
    (hoddcover : (upperHalf A N).card ≤
      len + (upperHalfResidue A N 0).card + 1)
    (hQsub : natAP q 2 len ⊆ thirdSumQuotient A N) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let Y := middleSixth A N
  let H := highThird A N
  let B := centralImage A N
  let E := parityPart B 0
  let O := parityPart B 1
  let Oₗ := O.filter fun z ↦ 2 * z ≤ N
  let Oᵣ := O.filter fun z ↦ N < 2 * z
  let Q₃ := natAP q 2 len
  change 4 * V.card ≤ N + 12 at hVcap
  change 2 * V.card ≤ 3 * len + 3 at hdomlen
  change V.card ≤ len + V₀.card + 1 at hoddcover
  have hQ₃sub : Q₃ ⊆ thirdSumQuotient A N := by simpa [Q₃] using hQsub
  have hQ₃I : Q₃ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hQ₃sub.trans (thirdSumQuotient_subset_central hsub)
  have hQ₃card : Q₃.card = len := card_natAP (by omega)
  have hBI : B ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hz' := mem_ratSection.mp (centralImage_subset_window hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hBpart := card_parity_parts B
  change E.card + O.card = B.card at hBpart
  have hOpart : Oₗ.card + Oᵣ.card = O.card := by
    have hd : Disjoint Oₗ Oᵣ := by
      rw [Finset.disjoint_left]
      intro z hzₗ hzᵣ
      have hl := (mem_filter.mp hzₗ).2
      have hr := (mem_filter.mp hzᵣ).2
      omega
    have hu : Oₗ ∪ Oᵣ = O := by
      ext z
      simp only [Oₗ, Oᵣ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        exact (le_or_gt (2 * z) N).imp (And.intro hz) (And.intro hz)
    rw [← card_union_of_disjoint hd, hu]
  have hOₗI : Oₗ ⊆ Icc (N / 3 + 1) (N / 2) := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzI := mem_Icc.mp (hBI ((filter_subset _ _) hz'.1))
    exact mem_Icc.mpr ⟨hzI.1, by omega⟩
  have hOₗodd : ∀ z ∈ Oₗ, (z : ZMod 2) = 1 := by
    intro z hz
    apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
    simpa using (mem_parityPart.mp (mem_filter.mp hz).1).2
  have hOₗcap := mul_card_fixed_zmod_le (1 : ZMod 2) hOₗI hOₗodd
  change 2 * Oₗ.card ≤ (N / 2 + 2) - (N / 3 + 1) at hOₗcap
  have hOᵣY : Oᵣ ⊆ Y := by
    intro z hz
    have hz' := mem_filter.mp hz
    have hzO := mem_parityPart.mp hz'.1
    obtain ⟨x, hxA, hxN, hxb⟩ := centralImage_mem_iff.mp
      hzO.1
    have hodd : z % 2 = 1 := by simpa using hzO.2
    have heq : z = x := by
      have := scaledMove_eq_self_of_odd (T := N) (q := 3) (a := x) (by rwa [hxb])
      omega
    have hright : N < 2 * x := by simpa [heq] using hz'.2
    rw [heq]
    apply mem_middleSixth.mpr
    exact ⟨hxA, hright, hxN⟩
  have hOᵣle : Oᵣ.card ≤ Y.card := card_le_card hOᵣY
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hAB := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hAB
  by_cases heven : q % 2 = 0
  · have hQeven : ∀ z ∈ Q₃, (z : ZMod 2) = 0 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
      rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
      omega
    have hEI : E ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hEeven : ∀ z ∈ E, (z : ZMod 2) = 0 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hdisj : Disjoint E Q₃ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hQ₃sub
    let W := E ∪ Q₃
    have hWI : W ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hEI hQ₃I
    have hWres : ∀ z ∈ W, (z : ZMod 2) = 0 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hEeven z hz
      · exact hQeven z hz
    have hWcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWI hWres
    have hWcard : W.card = E.card + Q₃.card := card_union_of_disjoint hdisj
    change 2 * W.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWcap
    have hEbound : 6 * (E.card + len) ≤ N + 6 := by omega
    have hObound : 12 * Oₗ.card ≤ N + 12 := by omega
    have hright : Oᵣ.card + H.card ≤ V.card := by omega
    omega

  · have hodd : q % 2 = 1 := by
      have := Nat.mod_lt q (by omega : 0 < 2)
      omega
    have hQodd : ∀ z ∈ Q₃, (z : ZMod 2) = 1 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
      apply (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr
      omega
    have hOI : O ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hOodd : ∀ z ∈ O, (z : ZMod 2) = 1 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hOQ : Disjoint O Q₃ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hQ₃sub
    let Wₒ := O ∪ Q₃
    have hWₒI : Wₒ ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hOI hQ₃I
    have hWₒres : ∀ z ∈ Wₒ, (z : ZMod 2) = 1 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hOodd z hz
      · exact hQodd z hz
    have hWₒcap := mul_card_fixed_zmod_le (1 : ZMod 2) hWₒI hWₒres
    have hWₒcard : Wₒ.card = O.card + Q₃.card := card_union_of_disjoint hOQ
    let T₀ := V₀.image fun x ↦ 2 * (x / 3)
    have hT₀card : T₀.card = V₀.card := by
      apply card_image_iff.mpr
      intro x hx y hy hxy
      have hx3 : 3 ∣ x := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using (mem_upperHalfResidue.mp hx).2
      have hy3 : 3 ∣ y := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using (mem_upperHalfResidue.mp hy).2
      have hxmul := Nat.mul_div_cancel' hx3
      have hymul := Nat.mul_div_cancel' hy3
      have hdiv : x / 3 = y / 3 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
      calc
        x = 3 * (x / 3) := hxmul.symm
        _ = 3 * (y / 3) := by rw [hdiv]
        _ = y := hymul
    have hT₀sub : T₀ ⊆ thirdSumQuotient A N := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      have hx' := mem_upperHalfResidue.mp hx
      have hxV := mem_upperHalf.mp hx'.1
      have hx3 : 3 ∣ x := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa using hx'.2
      apply mem_quotientPart.mpr
      refine ⟨2 * x, ?_, ?_, ?_⟩
      · apply mem_zmodFiber.mpr
        constructor
        · simpa [two_mul] using Finset.add_mem_add hx'.1 hx'.1
        · rw [ZMod.natCast_eq_zero_iff]
          exact hx3.mul_left 2
      · exact hx3.mul_left 2
      · have heq : 2 * x = 3 * (2 * (x / 3)) := by
          have := Nat.mul_div_cancel' hx3
          omega
        rw [heq]
        simp
    have hT₀I : T₀ ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
      hT₀sub.trans (thirdSumQuotient_subset_central hsub)
    have hT₀even : ∀ z ∈ T₀, (z : ZMod 2) = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 (x / 3)
    have hEI : E ⊆ Icc (N / 3 + 1) (2 * N / 3) := (filter_subset _ _).trans hBI
    have hEeven : ∀ z ∈ E, (z : ZMod 2) = 0 := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
      simpa using (mem_parityPart.mp hz).2
    have hET : Disjoint E T₀ := by
      apply (centralImage_disjoint_thirdSumQuotient hP hsub).mono
      · exact filter_subset _ _
      · exact hT₀sub
    let Wₑ := E ∪ T₀
    have hWₑI : Wₑ ⊆ Icc (N / 3 + 1) (2 * N / 3) := union_subset hEI hT₀I
    have hWₑres : ∀ z ∈ Wₑ, (z : ZMod 2) = 0 := by
      intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact hEeven z hz
      · exact hT₀even z hz
    have hWₑcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWₑI hWₑres
    have hWₑcard : Wₑ.card = E.card + T₀.card := card_union_of_disjoint hET
    change 2 * Wₒ.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWₒcap
    change 2 * Wₑ.card ≤ (2 * N / 3 + 2) - (N / 3 + 1) at hWₑcap
    have hObound : 6 * (O.card + len) ≤ N + 6 := by omega
    have hEbound : 6 * (E.card + V₀.card) ≤ N + 6 := by omega
    omega

lemma caseThree_nonzero_step_six {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (ha3 : 3 ∣ a)
    (hQ : natAP a 6 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2)
    (hres : InOneResidue
      (upperHalfResidue A N 1 + upperHalfResidue A N 2) 6) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let len := V₁.card + V₂.card - 1
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  have hres₁ : InOneResidue V₁ 6 := inOneResidue_add_left hV₂ hres
  have hres₂ : InOneResidue V₂ 6 := inOneResidue_add_right hV₁ hres
  obtain ⟨r₁, hr₁⟩ := hres₁
  obtain ⟨r₂, hr₂⟩ := hres₂
  have hV₁I : V₁ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hV₂I : V₂ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap₁ := mul_card_fixed_zmod_le r₁ hV₁I hr₁
  have hcap₂ := mul_card_fixed_zmod_le r₂ hV₂I hr₂
  change 6 * V₁.card ≤ (N + 6) - (N / 2 + 1) at hcap₁
  change 6 * V₂.card ≤ (N + 6) - (N / 2 + 1) at hcap₂
  have hVcap : 4 * V.card ≤ N + 12 := by omega
  have hdomlen : 2 * V.card ≤ 3 * len + 3 := by dsimp [len]; omega
  have hoddcover : V.card ≤ len + V₀.card + 1 := by dsimp [len]; omega
  have hQsub : natAP (a / 3) 2 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 6 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₁ ⊆ upperHalf A N from filter_subset _ _)
          (show V₂ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 2 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 2 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 6 * j = 3 * (a / 3 + 2 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_six_data hP hsub hVcap hdomlen hoddcover hQsub

/-! ### The step-three structural branch -/

/-- A unit-step interval in the divided upper-half sumset excludes every
member of `A` no larger than the interval. -/
lemma not_mem_of_le_thirdSum_interval {A : Finset ℕ} {N q len x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hxA : x ∈ A) (hxlen : x ≤ len) (hxhalf : 2 * x ≤ N) : False := by
  have hxpos : 0 < x := hP.pos_of_mem hsub hxA
  obtain ⟨y, hyI, hxy⟩ := exists_dvd_mem_natAP_one hxpos hxlen
  have hyQ := quotientPart_spec (hI hyI)
  have hysum := (mem_zmodFiber.mp hyQ).1
  obtain ⟨b, hb, c, hc, hbc⟩ := mem_add.mp hysum
  have hb' := mem_upperHalf.mp hb
  have hc' := mem_upperHalf.mp hc
  have hxb : x < b := by
    omega
  have hxc : x < c := by
    omega
  apply hP.not_dvd_add hxA hb'.1 hc'.1 hxb hxc
  rw [hbc]
  exact hxy.mul_left 3

/-- The same divided interval excludes every multiple of three up to three
times its length. -/
lemma not_mem_three_of_le_thirdSum_interval {A : Finset ℕ} {N q len x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hxA : x ∈ A) (hx3 : 3 ∣ x) (hxlen : x ≤ 3 * len)
    (hxhalf : 2 * x ≤ N) : False := by
  have hxpos : 0 < x := hP.pos_of_mem hsub hxA
  have huPos : 0 < x / 3 := Nat.div_pos (Nat.le_of_dvd hxpos hx3) (by omega)
  have hulen : x / 3 ≤ len := by
    have hxeq : 3 * (x / 3) = x := Nat.mul_div_cancel' hx3
    omega
  obtain ⟨y, hyI, huy⟩ := exists_dvd_mem_natAP_one huPos hulen
  have hyQ := quotientPart_spec (hI hyI)
  have hysum := (mem_zmodFiber.mp hyQ).1
  obtain ⟨b, hb, c, hc, hbc⟩ := mem_add.mp hysum
  have hb' := mem_upperHalf.mp hb
  have hc' := mem_upperHalf.mp hc
  have hxb : x < b := by
    omega
  have hxc : x < c := by
    omega
  apply hP.not_dvd_add hxA hb'.1 hc'.1 hxb hxc
  rw [hbc]
  obtain ⟨k, hk⟩ := huy
  refine ⟨k, ?_⟩
  have hxeq : 3 * (x / 3) = x := Nat.mul_div_cancel' hx3
  calc
    3 * y = 3 * ((x / 3) * k) := by rw [hk]
    _ = (3 * (x / 3)) * k := by ring
    _ = x * k := by rw [hxeq]

/-- Bedert's piecewise compression of the lower half in the step-three
case.  Its five branches are, in order, multiplication by `3`, by `2`, by
`3/2`, and the identity on each of the two remaining intervals. -/
def stepThreeCompress (N x : ℕ) : ℕ :=
  if 6 * x ≤ N then 3 * x
  else if 4 * x ≤ N then 2 * x
  else if 3 * x ≤ N then if x % 2 = 0 then 3 * (x / 2) else x
  else x

lemma dvd_two_stepThreeCompress (N x : ℕ) : x ∣ 2 * stepThreeCompress N x := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · exact ⟨6, by ring⟩
  · exact ⟨4, by ring⟩
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    exact ⟨3, by omega⟩
  · exact ⟨2, by ring⟩
  · exact ⟨2, by ring⟩

/-- The step-three compression maps the relevant lower-half window into
`(N/4,N/2]`. -/
lemma stepThreeCompress_mem_window {N x : ℕ} (hsmall : N / 9 < x)
    (hhalf : 2 * x ≤ N) : stepThreeCompress N x ∈ Icc (N / 4 + 1) (N / 2) := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega
  · apply mem_Icc.mpr
    omega

/-- Every compressed value has its source dividing four times the value. -/
lemma dvd_four_stepThreeCompress (N x : ℕ) : x ∣ 4 * stepThreeCompress N x := by
  simp only [stepThreeCompress]
  split_ifs with h6 h4 h3 heven
  · exact ⟨12, by ring⟩
  · exact ⟨8, by ring⟩
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    exact ⟨6, by omega⟩
  · exact ⟨4, by ring⟩
  · exact ⟨4, by ring⟩

/-- Values in the left third of the compression window are unchanged odd
sources. -/
lemma stepThreeCompress_left {N x : ℕ} (hx : N / 9 < x)
    (hz : stepThreeCompress N x ≤ N / 3) :
    stepThreeCompress N x = x ∧ x % 2 = 1 ∧ N < 4 * x ∧ 3 * x ≤ N := by
  simp only [stepThreeCompress] at hz ⊢
  split_ifs at hz ⊢ with h6 h4 h3 heven
  · omega
  · omega
  · have hx2 : 2 ∣ x := Nat.dvd_of_mod_eq_zero heven
    have hxeq : 2 * (x / 2) = x := Nat.mul_div_cancel' hx2
    omega
  · have hmodlt := Nat.mod_lt x (by omega : 0 < 2)
    omega
  · omega

/-- The piecewise compression is injective on a property-P lower set once
the only exceptional collision is ruled out by excluding small multiples
of three. -/
lemma stepThreeCompress_injOn {A D : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hD : ∀ x ∈ D, x ∈ A ∧ 2 * x ≤ N)
    (hno3 : ∀ x ∈ D, 3 ∣ x → x ≤ N / 3 → False) :
    Set.InjOn (stepThreeCompress N) D := by
  intro x hx y hy hxy
  have hxD := hD x hx
  have hyD := hD y hy
  have contra (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A)
      (huv : u < v) (hd : u ∣ 2 * v) : False :=
    hP.not_dvd_two_mul hu hv huv hd
  simp only [stepThreeCompress] at hxy
  split_ifs at hxy with hx6 hx4 hx3 hxe hy6 hy4 hy3 hye
  all_goals try have hxEvenEq : 2 * (x / 2) = x :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by assumption))
  all_goals try have hyEvenEq : 2 * (y / 2) = y :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by assumption))
  all_goals try omega
  all_goals
    first
    | exact False.elim (hno3 x hx
        ((by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left ⟨y / 2, hxy⟩)
        (by omega))
    | exact False.elim (hno3 y hy
        ((by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left ⟨x / 2, hxy.symm⟩)
        (by omega))
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨3, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨3, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨2, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨2, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨4, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨4, by omega⟩)
    | exact False.elim (contra x y hxD.1 hyD.1 (by omega) ⟨6, by omega⟩)
    | exact False.elim (contra y x hyD.1 hxD.1 (by omega) ⟨6, by omega⟩)

/-- The compressed copy of the lower half used in Bedert's `B₂`. -/
def stepThreeImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (stepThreeCompress N)

def stepThreeImageLeft (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (stepThreeImage A N).filter fun z ↦ z ≤ N / 3

def stepThreeImageRight (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (stepThreeImage A N).filter fun z ↦ N / 3 < z

@[simp] lemma mem_stepThreeImage {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImage A N ↔
      ∃ x ∈ A, 2 * x ≤ N ∧ stepThreeCompress N x = z := by
  simp only [stepThreeImage, mem_image, mem_lowHalf]
  constructor
  · rintro ⟨x, ⟨hxA, hxN⟩, hxz⟩
    exact ⟨x, hxA, hxN, hxz⟩
  · rintro ⟨x, hxA, hxN, hxz⟩
    exact ⟨x, ⟨hxA, hxN⟩, hxz⟩

@[simp] lemma mem_stepThreeImageLeft {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImageLeft A N ↔ z ∈ stepThreeImage A N ∧ z ≤ N / 3 := by
  simp [stepThreeImageLeft]

@[simp] lemma mem_stepThreeImageRight {A : Finset ℕ} {N z : ℕ} :
    z ∈ stepThreeImageRight A N ↔ z ∈ stepThreeImage A N ∧ N / 3 < z := by
  simp [stepThreeImageRight]

lemma stepThreeImage_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False) :
    (stepThreeImage A N).card = (lowHalf A N).card := by
  apply card_image_iff.mpr
  apply stepThreeCompress_injOn hP
  · intro x hx
    exact mem_lowHalf.mp hx
  · exact hno3

lemma stepThreeImage_subset_window {A : Finset ℕ} {N : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    stepThreeImage A N ⊆ Icc (N / 4 + 1) (N / 2) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
  exact stepThreeCompress_mem_window (hsmall x hx) (mem_lowHalf.mp hx).2

lemma card_stepThreeImage_left_add_right (A : Finset ℕ) (N : ℕ) :
    (stepThreeImageLeft A N).card + (stepThreeImageRight A N).card =
      (stepThreeImage A N).card := by
  have hd : Disjoint (stepThreeImageLeft A N) (stepThreeImageRight A N) := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    have hl := mem_stepThreeImageLeft.mp hzL
    have hr := mem_stepThreeImageRight.mp hzR
    omega
  have hu : stepThreeImageLeft A N ∪ stepThreeImageRight A N =
      stepThreeImage A N := by
    ext z
    simp only [mem_union, mem_stepThreeImageLeft, mem_stepThreeImageRight]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      exact (le_or_gt z (N / 3)).imp (And.intro hz) (And.intro hz)
  rw [← card_union_of_disjoint hd, hu]

lemma stepThreeImageLeft_spec {A : Finset ℕ} {N z : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hz : z ∈ stepThreeImageLeft A N) :
    z ∈ A ∧ z % 2 = 1 ∧ N < 4 * z ∧ 3 * z ≤ N := by
  have hz' := mem_stepThreeImageLeft.mp hz
  obtain ⟨x, hx, hzx⟩ := mem_image.mp hz'.1
  have hs := stepThreeCompress_left (hsmall x hx) (by simpa [hzx] using hz'.2)
  have hzx' : z = x := hzx.symm.trans hs.1
  have hxA := (mem_lowHalf.mp hx).1
  rw [hzx']
  exact ⟨hxA, hs.2⟩

lemma stepThreeImageRight_has_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ stepThreeImageRight A N) :
    ∃ x ∈ A, x ≤ N / 2 ∧ x ∣ 4 * z := by
  obtain ⟨x, hxA, hxN, hzx⟩ := mem_stepThreeImage.mp
    (mem_stepThreeImageRight.mp hz).1
  refine ⟨x, hxA, by omega, ?_⟩
  rw [← hzx]
  exact dvd_four_stepThreeCompress N x

lemma stepThreeImageRight_has_divisor_two {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ stepThreeImageRight A N) :
    ∃ x ∈ A, x ≤ N / 2 ∧ x ∣ 2 * z := by
  obtain ⟨x, hxA, hxN, hzx⟩ := mem_stepThreeImage.mp
    (mem_stepThreeImageRight.mp hz).1
  refine ⟨x, hxA, by omega, ?_⟩
  rw [← hzx]
  exact dvd_two_stepThreeCompress N x

lemma card_modThree_parts (S : Finset ℕ) :
    (residue S 0 3).card + (residue S 1 3).card +
      (residue S 2 3).card = S.card := by
  let f : ℕ → ℕ := fun x ↦ x % 3
  have hmap : (S : Set ℕ).MapsTo f (range 3) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have h := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at h
  have heq (r : ℕ) (hr : r < 3) : S.filter (fun x ↦ f x = r) = residue S r 3 := by
    ext x
    simp [f, residue, Nat.mod_eq_of_lt hr]
  rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega)] at h
  omega

/-- Any odd lower-window packing set and either odd residue class modulo
four in the top third fit into one twelfth of the ambient interval. -/
lemma oddLeft_add_high_odd_le {A B : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hBI : B ⊆ Icc (2 * N / 9 + 1) (N / 3))
    (hBodd : ∀ z ∈ B, z % 2 = 1)
    (hBpack : ∀ z ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 6 * z)
    (hi : i = 1 ∨ i = 3) :
    B.card + (modFourPart (highThird A N) i).card ≤ N / 12 + 10 := by
  let H := highThird A N
  let K := modFourPart H i
  let K₀ := residue K 0 3
  let K₁ := residue K 1 3
  let K₂ := residue K 2 3
  let S := zmodFiber (H + H) (6 : ZMod 12)
  let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (6 : ZMod 12)
  have hKpart := card_modThree_parts K
  change K₀.card + K₁.card + K₂.card = K.card at hKpart
  have hKI : K ⊆ Icc (2 * N / 3 + 1) N :=
    (filter_subset _ _).trans (highThird_subset_interval hsub)
  have hHpack : ∀ x ∈ H, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBU : B.image (fun z ↦ 6 * z) ⊆ U := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (hBI hz)
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (6 * z) 6 12).mpr
      have hzmod := Nat.mod_lt z (by omega : 0 < 2)
      have hzodd := hBodd z hz
      omega
  have hSU : S ⊆ U := by
    intro w hw
    have hw' := mem_zmodFiber.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
    have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
    have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
    exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
  have hpack := packing (k := 6) (t := N / 2) (by omega) hP hBpack hHpack
    (filter_subset _ _) hBU hSU
  have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
  have hUres : ∀ z ∈ U, (z : ZMod 12) = 6 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hcap := mul_card_fixed_zmod_le (6 : ZMod 12) hUI hUres
  have hSI : S ⊆ Icc (4 * N / 3 + 1) (2 * N) := hSU.trans hUI
  have hSres : ∀ z ∈ S, (z : ZMod 12) = 6 := by
    intro z hz
    exact (mem_zmodFiber.mp hz).2
  have hScap := mul_card_fixed_zmod_le (6 : ZMod 12) hSI hSres
  change B.card + S.card ≤ U.card at hpack
  change 12 * U.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hcap
  change 12 * S.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hScap
  have hBoddZ : ∀ z ∈ B, (z : ZMod 2) = 1 := by
    intro z hz
    apply (ZMod.natCast_eq_natCast_iff' z 1 2).mpr
    exact hBodd z hz
  have hBcap := mul_card_fixed_zmod_le (1 : ZMod 2) hBI hBoddZ
  change 2 * B.card ≤ (N / 3 + 2) - (2 * N / 9 + 1) at hBcap
  have hsum12 {X Y : Finset ℕ} (hX : X ⊆ K) (hY : Y ⊆ K)
      (hX3 : ∀ x ∈ X, x % 3 = 1) (hY3 : ∀ y ∈ Y, y % 3 = 2) :
      X + Y ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hxK := mem_modFourPart.mp (hX hx)
    have hyK := mem_modFourPart.mp (hY hy)
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add hxK.1 hyK.1
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) 6 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · rw [Nat.add_mod, hX3 x hx, hY3 y hy]
      · rcases hi with rfl | rfl <;> omega
  have hself0 : K₀ + K₀ ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hxK := mem_residue.mp hx
    have hyK := mem_residue.mp hy
    have hx4 := (mem_modFourPart.mp hxK.1).2
    have hy4 := (mem_modFourPart.mp hyK.1).2
    apply mem_zmodFiber.mpr
    constructor
    · exact Finset.add_mem_add (mem_modFourPart.mp hxK.1).1
        (mem_modFourPart.mp hyK.1).1
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) 6 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · have hx0 : x % 3 = 0 := by simpa using hxK.2
        have hy0 : y % 3 = 0 := by simpa using hyK.2
        rw [Nat.add_mod, hx0, hy0]
      · rcases hi with rfl | rfl <;> omega
  have h12sub : K₁ + K₂ ⊆ S := hsum12 (filter_subset _ _) (filter_subset _ _)
    (fun x hx ↦ by simpa using (mem_residue.mp hx).2)
    (fun y hy ↦ by simpa using (mem_residue.mp hy).2)
  by_cases hK₁ : K₁.Nonempty
  · by_cases hK₂ : K₂.Nonempty
    · have h12cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₁ hK₂
      have h12card := card_le_card h12sub
      have h12 : K₁.card + K₂.card ≤ S.card + 1 := by
        change K₁.card + K₂.card - 1 ≤ (K₁ + K₂).card at h12cd
        omega
      have h00 : 2 * K₀.card ≤ S.card + 1 := by
        obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
        · rw [hK₀]
          simp
        · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
          have hc := card_le_card hself0
          omega
      have hKlower : 2 * K.card ≤ 3 * (S.card + 1) := by omega
      change B.card + K.card ≤ N / 12 + 10
      omega
    · have hK₂card : K₂.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hK₂)
      have hK₁I : K₁ ⊆ Icc (2 * N / 3 + 1) N := (filter_subset _ _).trans hKI
      obtain ⟨r, hr⟩ : ∃ r : ZMod 12, ∀ x ∈ K₁, (x : ZMod 12) = r := by
        refine ⟨((3 * i - 2) : ℕ), ?_⟩
        intro x hx
        have hxK := mem_modFourPart.mp (mem_residue.mp hx).1
        apply (ZMod.natCast_eq_natCast_iff' x (3 * i - 2) 12).mpr
        apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
        constructor <;> change _ % _ = _ % _
        · rcases hi with rfl | rfl <;> simpa using (mem_residue.mp hx).2
        · rcases hi with rfl | rfl <;> omega
      have hK₁cap := mul_card_fixed_zmod_le r hK₁I hr
      have h00 : 2 * K₀.card ≤ S.card + 1 := by
        obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
        · rw [hK₀]
          simp
        · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
          have hc := card_le_card hself0
          omega
      change 12 * K₁.card ≤ (N + 12) - (2 * N / 3 + 1) at hK₁cap
      change B.card + K.card ≤ N / 12 + 10
      omega
  · have hK₁card : K₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hK₁)
    have hK₂I : K₂ ⊆ Icc (2 * N / 3 + 1) N := (filter_subset _ _).trans hKI
    obtain ⟨r, hr⟩ : ∃ r : ZMod 12, ∀ x ∈ K₂, (x : ZMod 12) = r := by
      refine ⟨((3 * i + 2) : ℕ), ?_⟩
      intro x hx
      have hxK := mem_modFourPart.mp (mem_residue.mp hx).1
      apply (ZMod.natCast_eq_natCast_iff' x (3 * i + 2) 12).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp
      constructor <;> change _ % _ = _ % _
      · rcases hi with rfl | rfl <;> simpa using (mem_residue.mp hx).2
      · rcases hi with rfl | rfl <;> omega
    have hK₂cap := mul_card_fixed_zmod_le r hK₂I hr
    have h00 : 2 * K₀.card ≤ S.card + 1 := by
      obtain hK₀ | hK₀ := K₀.eq_empty_or_nonempty
      · rw [hK₀]
        simp
      · have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hK₀ hK₀
        have hc := card_le_card hself0
        omega
    change 12 * K₂.card ≤ (N + 12) - (2 * N / 3 + 1) at hK₂cap
    change B.card + K.card ≤ N / 12 + 10
    omega

/-- The left part of `B₂` is the principal instance of the abstract odd
lower-window packing estimate. -/
lemma stepThree_left_add_high_odd_le {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hi : i = 1 ∨ i = 3) :
    (stepThreeImageLeft A N).card +
      (modFourPart (highThird A N) i).card ≤ N / 12 + 10 := by
  let B := stepThreeImageLeft A N
  have hspec : ∀ z ∈ B, z ∈ A ∧ z % 2 = 1 ∧ N < 4 * z ∧ 3 * z ≤ N := by
    intro z hz
    exact stepThreeImageLeft_spec hsmall hz
  apply oddLeft_add_high_odd_le hP hsub
  · intro z hz
    have hz' := hspec z hz
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro z hz
    exact (hspec z hz).2.1
  · intro z hz
    have hz' := hspec z hz
    exact ⟨z, hz'.1, by omega, dvd_mul_left z 6⟩
  · exact hi

/-- Twice the right part of `B₂` packs against the even part of the top
third. -/
lemma stepThree_right_add_high_even_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    (stepThreeImageRight A N).card +
      (parityPart (highThird A N) 0).card ≤ N / 6 + 4 := by
  let B := stepThreeImageRight A N
  let E := parityPart (highThird A N) 0
  let T := B.image fun z ↦ 2 * z
  have hTcard : T.card = B.card := by
    apply card_image_iff.mpr
    intro x hx y hy hxy
    change 2 * x = 2 * y at hxy
    omega
  have hTI : T ⊆ Icc (2 * N / 3 + 1) N := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzR := mem_stepThreeImageRight.mp hz
    have hzI := mem_Icc.mp (stepThreeImage_subset_window hsmall hzR.1)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hEI : E ⊆ Icc (2 * N / 3 + 1) N :=
    (filter_subset _ _).trans (highThird_subset_interval hsub)
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro w hwT hwE
    obtain ⟨z, hz, hzw⟩ := mem_image.mp hwT
    obtain ⟨a, haA, haN, hadiv⟩ := stepThreeImageRight_has_divisor_two hz
    have hwH := mem_highThird.mp (mem_parityPart.mp hwE).1
    apply hP.not_dvd_of_lt haA hwH.1 (by omega)
    simpa [hzw] using hadiv
  let W := T ∪ E
  have hWI : W ⊆ Icc (2 * N / 3 + 1) N := union_subset hTI hEI
  have hWeven : ∀ w ∈ W, (w : ZMod 2) = 0 := by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 z
    · apply (ZMod.natCast_eq_natCast_iff' w 0 2).mpr
      simpa using (mem_parityPart.mp hw).2
  have hcap := mul_card_fixed_zmod_le (0 : ZMod 2) hWI hWeven
  have hWcard : W.card = T.card + E.card := card_union_of_disjoint hdisj
  change 2 * W.card ≤ (N + 2) - (2 * N / 3 + 1) at hcap
  change B.card + E.card ≤ N / 6 + 4
  omega

/-- With small multiples of three excluded, the odd left part of `B₂`
occupies only the two coprime residue classes `1,5 (mod 6)`. -/
lemma stepThree_left_card_le {A : Finset ℕ} {N : ℕ}
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False) :
    36 * (stepThreeImageLeft A N).card ≤ N + 72 := by
  let B := stepThreeImageLeft A N
  let B₁ := residue B 1 6
  let B₅ := residue B 5 6
  have hBI : B ⊆ Icc (N / 4 + 1) (N / 3) := by
    intro z hz
    have hz' := stepThreeImageLeft_spec hsmall hz
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hpart : B₁.card + B₅.card = B.card := by
    have hd : Disjoint B₁ B₅ := by
      rw [Finset.disjoint_left]
      intro z hz1 hz5
      have h1 := (mem_residue.mp hz1).2
      have h5 := (mem_residue.mp hz5).2
      omega
    have hu : B₁ ∪ B₅ = B := by
      change residue B 1 6 ∪ residue B 5 6 = B
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hz' := stepThreeImageLeft_spec hsmall hz
        have hzlow : z ∈ lowHalf A N := mem_lowHalf.mpr ⟨hz'.1, by omega⟩
        have hz3 : z % 3 ≠ 0 := by
          intro heq
          exact hno3 z hzlow (Nat.dvd_of_mod_eq_zero heq) (by omega)
        have hz6 := Nat.mod_lt z (by omega : 0 < 6)
        have hzpar : z % 6 % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 2 ∣ 6)]
          exact hz'.2.1
        have hzthree : z % 6 % 3 ≠ 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)]
          exact hz3
        interval_cases z % 6 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) (hr : r = 1 ∨ r = 5) :
      6 * (residue B r 6).card ≤ (N / 3 + 6) - (N / 4 + 1) := by
    have hI : residue B r 6 ⊆ Icc (N / 4 + 1) (N / 3) :=
      (filter_subset _ _).trans hBI
    have hres : ∀ z ∈ residue B r 6, (z : ZMod 6) = (r : ZMod 6) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 6).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 6) hI hres
  have h1 := hcap 1 (Or.inl rfl)
  have h5 := hcap 5 (Or.inr rfl)
  change 6 * B₁.card ≤ (N / 3 + 6) - (N / 4 + 1) at h1
  change 6 * B₅.card ≤ (N / 3 + 6) - (N / 4 + 1) at h5
  change 36 * B.card ≤ N + 72
  omega

/-- Bedert's `B₂` dichotomy.  If both odd top-third classes occur, their
cross-sum (together with the two even self-sums) packs against the right
part.  If an odd class is absent, direct parity packing controls the whole
compressed lower half together with the top third. -/
lemma stepThree_image_dichotomy {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hsmall : ∀ x ∈ lowHalf A N, N / 9 < x) :
    2 * (stepThreeImageRight A N).card + (highThird A N).card ≤ N / 3 + 12 ∨
      (stepThreeImage A N).card + (highThird A N).card ≤ N / 4 + 24 := by
  let B := stepThreeImage A N
  let Bₗ := stepThreeImageLeft A N
  let Bᵣ := stepThreeImageRight A N
  let H := highThird A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let E := parityPart H 0
  let O := parityPart H 1
  have hBpart := card_stepThreeImage_left_add_right A N
  change Bₗ.card + Bᵣ.card = B.card at hBpart
  have hHfour : H₀.card + H₁.card + H₂.card + H₃.card = H.card := by
    let f : ℕ → ℕ := fun x ↦ x % 4
    have hmap : (H : Set ℕ).MapsTo f (range 4) := by
      intro x hx
      exact mem_range.mpr (Nat.mod_lt _ (by omega))
    have h := Finset.card_eq_sum_card_fiberwise hmap
    simp only [sum_range_succ, sum_range_zero] at h
    have heq (r : ℕ) (hr : r < 4) : H.filter (fun x ↦ f x = r) = modFourPart H r := by
      ext x
      simp [f, modFourPart, Nat.mod_eq_of_lt hr]
    rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega),
      heq 3 (by omega)] at h
    change H.card = 0 + H₀.card + H₁.card + H₂.card + H₃.card at h
    omega
  have hHE := card_parity_parts H
  change E.card + O.card = H.card at hHE
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · left
      let S := zmodFiber (H + H) (0 : ZMod 4)
      let U := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 4)
      have h13 : H₁ + H₃ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        constructor
        · exact Finset.add_mem_add hx'.1 hy'.1
        · rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]
      have h00 : H₀ + H₀ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        exact ⟨Finset.add_mem_add hx'.1 hy'.1, by
          rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]⟩
      have h22 : H₂ + H₂ ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        exact ⟨Finset.add_mem_add hx'.1 hy'.1, by
          rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
            Nat.add_mod, hx'.2, hy'.2]⟩
      have h13cd := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 h3
      have h13c := card_le_card h13
      have h13lower : H₁.card + H₃.card ≤ S.card + 1 := by omega
      have h00lower : 2 * H₀.card ≤ S.card + 1 := by
        obtain he | he := H₀.eq_empty_or_nonempty
        · rw [he]
          simp
        · have hc := cauchy_davenport_add_of_linearOrder_isCancelAdd he he
          have hs := card_le_card h00
          omega
      have h22lower : 2 * H₂.card ≤ S.card + 1 := by
        obtain he | he := H₂.eq_empty_or_nonempty
        · rw [he]
          simp
        · have hc := cauchy_davenport_add_of_linearOrder_isCancelAdd he he
          have hs := card_le_card h22
          omega
      have hHlower : H.card ≤ 2 * (S.card + 1) := by omega
      have hBdiv : ∀ z ∈ Bᵣ, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * z := by
        intro z hz
        exact stepThreeImageRight_has_divisor hz
      have hHhigh : ∀ x ∈ H, x ∈ A ∧ N / 2 < x := by
        intro x hx
        have hx' := mem_highThird.mp hx
        exact ⟨hx'.1, by omega⟩
      have hBU : Bᵣ.image (fun z ↦ 4 * z) ⊆ U := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
        have hzR := mem_stepThreeImageRight.mp hz
        have hzI := mem_Icc.mp (stepThreeImage_subset_window hsmall hzR.1)
        have hzright := hzR.2
        apply mem_zmodFiber.mpr
        exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
          rw [ZMod.natCast_eq_zero_iff]
          exact dvd_mul_right 4 z⟩
      have hSU : S ⊆ U := by
        intro w hw
        have hw' := mem_zmodFiber.mp hw
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
        have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
        have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
        exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
      have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hHhigh
        (filter_subset _ _) hBU hSU
      have hUI : U ⊆ Icc (4 * N / 3 + 1) (2 * N) := filter_subset _ _
      have hUres : ∀ z ∈ U, (z : ZMod 4) = 0 := by
        intro z hz
        exact (mem_zmodFiber.mp hz).2
      have hcap := mul_card_fixed_zmod_le (0 : ZMod 4) hUI hUres
      change Bᵣ.card + S.card ≤ U.card at hp
      change 4 * U.card ≤ (2 * N + 4) - (4 * N / 3 + 1) at hcap
      change 2 * Bᵣ.card + H.card ≤ N / 3 + 12
      omega
    · right
      have hBL := stepThree_left_add_high_odd_le hP hsub hsmall (i := 1) (Or.inl rfl)
      have hH₃card : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hOdd : O.card = H₁.card := by
        have hp := card_modFour_one_add_three H
        change H₁.card + H₃.card = O.card at hp
        omega
      have hBE := stepThree_right_add_high_even_le hP hsub hsmall
      change Bₗ.card + H₁.card ≤ N / 12 + 10 at hBL
      change Bᵣ.card + E.card ≤ N / 6 + 4 at hBE
      change B.card + H.card ≤ N / 4 + 24
      omega
  · right
    have hBL := stepThree_left_add_high_odd_le hP hsub hsmall (i := 3) (Or.inr rfl)
    have hH₁card : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hOdd : O.card = H₃.card := by
      have hp := card_modFour_one_add_three H
      change H₁.card + H₃.card = O.card at hp
      omega
    have hBE := stepThree_right_add_high_even_le hP hsub hsmall
    change Bₗ.card + H₃.card ≤ N / 12 + 10 at hBL
    change Bᵣ.card + E.card ≤ N / 6 + 4 at hBE
    change B.card + H.card ≤ N / 4 + 24
    omega

/-- Division by three turns a step-three progression in the nonzero
upper-half sumset into a genuine interval in `thirdSumQuotient`. -/
lemma stepThree_divided_interval {A : Finset ℕ} {N a len : ℕ}
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 len ⊆
      upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
  intro z hz
  obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
  apply mem_quotientPart.mpr
  refine ⟨a + 3 * j, ?_, ?_, ?_⟩
  · apply mem_zmodFiber.mpr
    constructor
    · apply Finset.add_subset_add
        (show upperHalfResidue A N 1 ⊆ upperHalf A N from filter_subset _ _)
        (show upperHalfResidue A N 2 ⊆ upperHalf A N from filter_subset _ _)
      apply hQ
      exact mem_natAP.mpr ⟨j, hj, rfl⟩
    · rw [ZMod.natCast_eq_zero_iff]
      exact ⟨a / 3 + j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
  · exact ⟨a / 3 + j, by
      have := Nat.mul_div_cancel' ha3
      omega⟩
  · have heq : a + 3 * j = 3 * (a / 3 + j) := by
      have := Nat.mul_div_cancel' ha3
      omega
    rw [heq]
    simpa using hz

lemma three_mul_card_nonthree_le {S : Finset ℕ} {L U : ℕ}
    (hI : S ⊆ Icc L U) (h3 : ∀ z ∈ S, z % 3 ≠ 0) :
    3 * S.card ≤ 2 * ((U + 3) - L) := by
  let S₁ := residue S 1 3
  let S₂ := residue S 2 3
  have hp : S₁.card + S₂.card = S.card := by
    have hd : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have h1 := (mem_residue.mp hz1).2
      have h2 := (mem_residue.mp hz2).2
      omega
    have hu : S₁ ∪ S₂ = S := by
      change residue S 1 3 ∪ residue S 2 3 = S
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hm := Nat.mod_lt z (by omega : 0 < 3)
        have hn := h3 z hz
        interval_cases z % 3 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) :
      3 * (residue S r 3).card ≤ (U + 3) - L := by
    have hSI : residue S r 3 ⊆ Icc L U := (filter_subset _ _).trans hI
    have hr : ∀ z ∈ residue S r 3, (z : ZMod 3) = (r : ZMod 3) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 3).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 3) hSI hr
  have h1 := hcap 1
  have h2 := hcap 2
  change 3 * S₁.card ≤ (U + 3) - L at h1
  change 3 * S₂.card ≤ (U + 3) - L at h2
  omega

lemma six_mul_card_even_nonthree_le {S : Finset ℕ} {L U : ℕ}
    (hI : S ⊆ Icc L U) (heven : ∀ z ∈ S, z % 2 = 0)
    (h3 : ∀ z ∈ S, z % 3 ≠ 0) :
    6 * S.card ≤ 2 * ((U + 6) - L) := by
  let S₂ := residue S 2 6
  let S₄ := residue S 4 6
  have hp : S₂.card + S₄.card = S.card := by
    have hd : Disjoint S₂ S₄ := by
      rw [Finset.disjoint_left]
      intro z hz2 hz4
      have h2 := (mem_residue.mp hz2).2
      have h4 := (mem_residue.mp hz4).2
      omega
    have hu : S₂ ∪ S₄ = S := by
      change residue S 2 6 ∪ residue S 4 6 = S
      ext z
      simp only [mem_union, mem_residue]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        have hm := Nat.mod_lt z (by omega : 0 < 6)
        have h2 : z % 6 % 2 = 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 2 ∣ 6)]
          exact heven z hz
        have hthree : z % 6 % 3 ≠ 0 := by
          rw [Nat.mod_mod_of_dvd z (by omega : 3 ∣ 6)]
          exact h3 z hz
        interval_cases z % 6 <;> simp_all
    rw [← card_union_of_disjoint hd, hu]
  have hcap (r : ℕ) :
      6 * (residue S r 6).card ≤ (U + 6) - L := by
    have hSI : residue S r 6 ⊆ Icc L U := (filter_subset _ _).trans hI
    have hr : ∀ z ∈ residue S r 6, (z : ZMod 6) = (r : ZMod 6) := by
      intro z hz
      apply (ZMod.natCast_eq_natCast_iff' z r 6).mpr
      exact (mem_residue.mp hz).2
    exact mul_card_fixed_zmod_le (r : ZMod 6) hSI hr
  have h2 := hcap 2
  have h4 := hcap 4
  change 6 * S₂.card ≤ (U + 6) - L at h2
  change 6 * S₄.card ≤ (U + 6) - L at h4
  omega

lemma scaledMove_eq_self_of_mem_central {N x : ℕ} (hx : N < 3 * x) :
    scaledMove 0 N 3 x = x := by
  have hxpos : 0 < x := by omega
  have he : scaledWindowExp 0 N 3 x = 0 := by
    by_contra hn
    have hp : 0 < scaledWindowExp 0 N 3 x := by omega
    have hm := scaledWindowExp_min (b := 0) (T := N) (q := 3) (a := x)
      (by omega) hxpos (j := 0) hp
    simp at hm
    omega
  simp [scaledMove, he]

noncomputable def centralRemainder (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (centralImage A N).filter fun z ↦ z ∉ middleSixth A N

lemma middleSixth_subset_centralImage {A : Finset ℕ} {N : ℕ} :
    middleSixth A N ⊆ centralImage A N := by
  intro x hx
  have hx' := mem_middleSixth.mp hx
  apply centralImage_mem_iff.mpr
  exact ⟨x, hx'.1, hx'.2.2, scaledMove_eq_self_of_mem_central (by omega)⟩

lemma card_centralRemainder_add_middle (A : Finset ℕ) (N : ℕ) :
    (centralRemainder A N).card + (middleSixth A N).card =
      (centralImage A N).card := by
  have hd : Disjoint (centralRemainder A N) (middleSixth A N) := by
    rw [Finset.disjoint_left]
    intro z hzD hzY
    exact (mem_filter.mp hzD).2 hzY
  have hu : centralRemainder A N ∪ middleSixth A N = centralImage A N := by
    ext z
    simp only [centralRemainder, mem_union, mem_filter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact middleSixth_subset_centralImage h
    · intro hz
      by_cases hy : z ∈ middleSixth A N
      · exact Or.inr hy
      · exact Or.inl ⟨hz, hy⟩
  rw [← card_union_of_disjoint hd, hu]

lemma centralImage_not_three_below_interval {A : Finset ℕ} {N q len z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hI : natAP q 1 len ⊆ thirdSumQuotient A N)
    (hzB : z ∈ centralImage A N) (hz3 : 3 ∣ z)
    (hzlen : z ≤ 3 * len) (hzhalf : 2 * z ≤ N) : False := by
  obtain ⟨x, hxA, hxN, hxz⟩ := centralImage_mem_iff.mp hzB
  have hxpos := hP.pos_of_mem hsub hxA
  have hzpos : 0 < z := by
    rw [← hxz, scaledMove]
    positivity
  have hxdvd : x ∣ z := by rw [← hxz]; exact dvd_scaledMove 0 N 3 x
  have hxle : x ≤ z := Nat.le_of_dvd hzpos hxdvd
  have hx3 : 3 ∣ x := by
    rw [← hxz, scaledMove] at hz3
    rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hz3 with hp | hp
    · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
      norm_num at this
    · exact hp
  exact not_mem_three_of_le_thirdSum_interval hP hsub hI hxA hx3
    (by omega) (by omega)

lemma centralRemainder_upper_spec {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False)
    (hzD : z ∈ centralRemainder A N) (hzupper : N < 2 * z) :
    z % 2 = 0 ∧ z % 3 ≠ 0 := by
  have hzD' := mem_filter.mp hzD
  have hzI := mem_ratSection.mp (centralImage_subset_window hP hsub hzD'.1)
  obtain ⟨x, hxA, hxN, hxz⟩ := centralImage_mem_iff.mp hzD'.1
  have hxpos := hP.pos_of_mem hsub hxA
  have hzpos : 0 < z := by omega
  have hxdvd : x ∣ z := by rw [← hxz]; exact dvd_scaledMove 0 N 3 x
  have hxle : x ≤ z := Nat.le_of_dvd hzpos hxdvd
  have hxne : x ≠ z := by
    intro heq
    apply hzD'.2
    apply mem_middleSixth.mpr
    exact ⟨by simpa [heq] using hxA, hzupper, hzI.2.2⟩
  have hxlt : x < z := lt_of_le_of_ne hxle hxne
  have htwox : 2 * x ≤ z := by
    obtain ⟨k, hk⟩ := hxdvd
    have hk2 : 2 ≤ k := by
      by_contra hn
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> simp_all
    calc
      2 * x = x * 2 := by omega
      _ ≤ x * k := Nat.mul_le_mul_left x hk2
      _ = z := hk.symm
  constructor
  · by_contra hodd
    have hmod := Nat.mod_lt z (by omega : 0 < 2)
    have hzodd : z % 2 = 1 := by omega
    have heq := scaledMove_eq_self_of_odd (T := N) (q := 3) (a := x)
    apply hxne
    rw [hxz] at heq
    exact (heq hzodd).symm
  · intro hz3mod
    have hz3 : 3 ∣ z := Nat.dvd_of_mod_eq_zero hz3mod
    have hx3 : 3 ∣ x := by
      rw [← hxz, scaledMove] at hz3
      rcases (show Nat.Prime 3 by norm_num).dvd_mul.mp hz3 with hp | hp
      · have : 3 ∣ 2 := (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hp
        norm_num at this
      · exact hp
    have hxlow : x ∈ lowHalf A N := mem_lowHalf.mpr ⟨hxA, by omega⟩
    exact hno3 x hxlow hx3 (by omega)

lemma mem_natAP_one_iff {q len z : ℕ} :
    z ∈ natAP q 1 len ↔ q ≤ z ∧ z < q + len := by
  constructor
  · intro hz
    obtain ⟨j, hj, rfl⟩ := mem_natAP.mp hz
    omega
  · rintro ⟨hl, hu⟩
    apply mem_natAP.mpr
    exact ⟨z - q, by omega, by omega⟩

lemma card_filter_lt_add_ge (S : Finset ℕ) (t : ℕ) :
    (S.filter fun z ↦ z < t).card + (S.filter fun z ↦ t ≤ z).card = S.card := by
  have hd : Disjoint (S.filter fun z ↦ z < t) (S.filter fun z ↦ t ≤ z) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have h₁ := (mem_filter.mp hz₁).2
    have h₂ := (mem_filter.mp hz₂).2
    omega
  have hu : (S.filter fun z ↦ z < t) ∪ (S.filter fun z ↦ t ≤ z) = S := by
    ext z
    simp only [mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      exact (lt_or_ge z t).imp (And.intro hz) (And.intro hz)
  rw [← card_union_of_disjoint hd, hu]

lemma card_filter_le_add_gt (S : Finset ℕ) (t : ℕ) :
    (S.filter fun z ↦ z ≤ t).card + (S.filter fun z ↦ t < z).card = S.card := by
  simpa [Nat.lt_add_one_iff] using card_filter_lt_add_ge S (t + 1)

/-- The complete step-three structural estimate.  The three branches are
the late-start, crossing, and noncrossing positions of the divided
interval. -/
lemma caseThree_step_three_interval {A : Finset ℕ} {N q len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hlenpos : 0 < len)
    (hlen : 2 * (upperHalf A N).card ≤ 3 * (len + 1))
    (hinterval : natAP q 1 len ⊆ thirdSumQuotient A N) :
    3 * A.card ≤ N + 100000 := by
  let V := upperHalf A N
  let Y := middleSixth A N
  let H := highThird A N
  let B := centralImage A N
  let D := centralRemainder A N
  let I := natAP q 1 len
  have hI : I ⊆ thirdSumQuotient A N := by simpa [I] using hinterval
  have hIcard : I.card = len := card_natAP (by omega)
  have hII : I ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    hI.trans (thirdSumQuotient_subset_central hsub)
  have hqI : q ∈ I := mem_natAP.mpr ⟨0, hlenpos, by simp⟩
  have hqcentral := mem_Icc.mp (hII hqI)
  have hBI : B ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
    intro z hz
    have hz' := mem_ratSection.mp (centralImage_subset_window hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hDI : D ⊆ Icc (N / 3 + 1) (2 * N / 3) :=
    (filter_subset _ _).trans hBI
  have hdisjBI : Disjoint B I :=
    (centralImage_disjoint_thirdSumQuotient hP hsub).mono subset_rfl hI
  have hdisjDI : Disjoint D I := hdisjBI.mono (filter_subset _ _) subset_rfl
  have hBH := card_centralImage_add_high hP hsub
  change B.card + H.card = A.card at hBH
  have hDY := card_centralRemainder_add_middle A N
  change D.card + Y.card = B.card at hDY
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  have hVcard : V.card = Y.card + H.card := hYH.symm
  have hDA : D.card + V.card = A.card := by omega
  change 2 * V.card ≤ 3 * (len + 1) at hlen
  have hdomlen := hlen
  by_cases hlarge : H.card + 3 ≤ 2 * Y.card
  · have hHlen : H.card ≤ len := by omega
    have hIQ : I.card ≤ (thirdSumQuotient A N).card := card_le_card hI
    have hHQ : H.card ≤ (thirdSumQuotient A N).card := by omega
    have hpack := caseThree_basic_packing hP hsub
    change B.card + (thirdSumQuotient A N).card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card at hpack
    have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
      simp
      omega
    omega
  have hmid : 2 * Y.card < H.card + 3 := by omega
  change 6 * H.card < N + 144 at hcase3
  have hnine : N / 9 ≤ len := by
    change (N + 1) / 2 < 3 * V.card at htail
    omega
  have hsmall : ∀ x ∈ lowHalf A N, N / 9 < x := by
    intro x hx
    by_contra hn
    exact not_mem_of_le_thirdSum_interval hP hsub hI (mem_lowHalf.mp hx).1
      (by omega) (mem_lowHalf.mp hx).2
  have hno3 : ∀ x ∈ lowHalf A N, 3 ∣ x → x ≤ N / 3 → False := by
    intro x hx hx3 hxN
    exact not_mem_three_of_le_thirdSum_interval hP hsub hI
      (mem_lowHalf.mp hx).1 hx3 (by omega) (mem_lowHalf.mp hx).2
  let C := stepThreeImage A N
  let Cₗ := stepThreeImageLeft A N
  let Cᵣ := stepThreeImageRight A N
  have hCcard := stepThreeImage_card hP hno3
  change C.card = (lowHalf A N).card at hCcard
  have hCpart := card_stepThreeImage_left_add_right A N
  change Cₗ.card + Cᵣ.card = C.card at hCpart
  have hCLcap := stepThree_left_card_le hsmall hno3
  change 36 * Cₗ.card ≤ N + 72 at hCLcap
  have hLV := card_lowHalf_add_upperHalf hsub
  change (lowHalf A N).card + V.card = A.card at hLV
  by_cases hdone : 3 * A.card ≤ N + 300
  · exact hdone.trans (by omega)
  have hdense : 5 * N ≤ 24 * V.card + 20000 := by
    rcases stepThree_image_dichotomy hP hsub hsmall with hright | hwhole
    · change 2 * Cᵣ.card + H.card ≤ N / 3 + 12 at hright
      rw [hVcard]
      omega
    · change C.card + H.card ≤ N / 4 + 24 at hwhole
      have hYupper : 12 * Y.card ≤ N + 300 := by omega
      have hAeq : A.card = C.card + V.card := by omega
      apply False.elim
      apply hdone
      rw [hAeq, hVcard]
      omega
  have hVupper : 4 * V.card ≤ N + 200 := by omega
  have hgap : 5 * N / 12 ≤ 3 * len + 2000 := by omega
  have hDupper : ∀ z ∈ D, N < 2 * z → z % 2 = 0 ∧ z % 3 ≠ 0 := by
    intro z hz hzN
    exact centralRemainder_upper_spec hP hsub hno3 hz hzN
  have hnotI {z : ℕ} (hzB : z ∈ B) : ¬(q ≤ z ∧ z < q + len) := by
    intro hzrange
    exact (Finset.disjoint_left.mp hdisjBI) hzB (mem_natAP_one_iff.mpr hzrange)
  by_cases hlate : 5 * N / 12 < q
  · let Bp := B.filter fun z ↦ z ≤ 5 * N / 12
    let Bt := B.filter fun z ↦ 5 * N / 12 < z
    let P := Bp.filter fun z ↦ z ≤ 3 * len
    let E := Bp.filter fun z ↦ 3 * len < z
    have hBpart := card_filter_le_add_gt B (5 * N / 12)
    change Bp.card + Bt.card = B.card at hBpart
    have hPpart := card_filter_le_add_gt Bp (3 * len)
    change P.card + E.card = Bp.card at hPpart
    have hPI : P ⊆ Icc (N / 3 + 1) (5 * N / 12) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzBp := mem_filter.mp hz'.1
      have hzI := mem_Icc.mp (hBI hzBp.1)
      exact mem_Icc.mpr ⟨hzI.1, hzBp.2⟩
    have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
      intro z hz hz3
      have hz' := mem_filter.mp hz
      have hzB := (mem_filter.mp hz'.1).1
      exact centralImage_not_three_below_interval hP hsub hI hzB
        (Nat.dvd_of_mod_eq_zero hz3) hz'.2 (by
          have hzBp := mem_filter.mp hz'.1
          omega)
    have hPcap := three_mul_card_nonthree_le hPI hP3
    change 3 * P.card ≤ 2 * ((5 * N / 12 + 3) - (N / 3 + 1)) at hPcap
    have hEI : E ⊆ Icc (3 * len + 1) (5 * N / 12) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzBp := mem_filter.mp hz'.1
      exact mem_Icc.mpr ⟨by omega, hzBp.2⟩
    have hEcap := card_Icc_le hEI
    change E.card ≤ (5 * N / 12 + 1) - (3 * len + 1) at hEcap
    have hEsmall : E.card ≤ 2000 := by omega
    have hBtI : Bt ⊆ Icc (5 * N / 12 + 1) (2 * N / 3) := by
      intro z hz
      have hz' := mem_filter.mp hz
      have hzI := mem_Icc.mp (hBI hz'.1)
      exact mem_Icc.mpr ⟨by omega, hzI.2⟩
    have hItail : I ⊆ Icc (5 * N / 12 + 1) (2 * N / 3) := by
      intro z hz
      have hzrange := mem_natAP_one_iff.mp hz
      have hzI := mem_Icc.mp (hII hz)
      exact mem_Icc.mpr ⟨by omega, hzI.2⟩
    have htailpack := card_add_card_le_of_disjoint_subsets
      (hdisjBI.mono (filter_subset _ _) subset_rfl) hBtI hItail
    have htailcap := card_Icc_le
      (S := Icc (5 * N / 12 + 1) (2 * N / 3)) (subset_rfl)
    change Bt.card + I.card ≤ (Icc (5 * N / 12 + 1) (2 * N / 3)).card at htailpack
    change (Icc (5 * N / 12 + 1) (2 * N / 3)).card ≤
      (2 * N / 3 + 1) - (5 * N / 12 + 1) at htailcap
    rw [hIcard] at htailpack
    omega
  · have hq : q ≤ 5 * N / 12 := by omega
    have hqgap : q ≤ 3 * len + 2000 := by omega
    by_cases hcross : N < 2 * (q + len)
    · let Dl := D.filter fun z ↦ z < q
      let Dr := D.filter fun z ↦ q + len ≤ z
      let P := Dl.filter fun z ↦ z ≤ 3 * len
      let E := Dl.filter fun z ↦ 3 * len < z
      have hDpart : Dl.card + Dr.card = D.card := by
        have hd : Disjoint Dl Dr := by
          rw [Finset.disjoint_left]
          intro z hzl hzr
          have hl := (mem_filter.mp hzl).2
          have hr := (mem_filter.mp hzr).2
          omega
        have hu : Dl ∪ Dr = D := by
          ext z
          simp only [Dl, Dr, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            have hn := hnotI ((filter_subset _ _) hz)
            by_cases hl : z < q
            · exact Or.inl ⟨hz, hl⟩
            · exact Or.inr ⟨hz, by omega⟩
        rw [← card_union_of_disjoint hd, hu]
      have hPpart := card_filter_le_add_gt Dl (3 * len)
      change P.card + E.card = Dl.card at hPpart
      have hPI : P ⊆ Icc (N / 3 + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        have hzI := mem_Icc.mp (hDI hzl.1)
        exact mem_Icc.mpr ⟨hzI.1, by omega⟩
      have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
        intro z hz hz3
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact centralImage_not_three_below_interval hP hsub hI
          ((filter_subset _ _) hzl.1) (Nat.dvd_of_mod_eq_zero hz3)
          hz'.2 (by have hzI := mem_Icc.mp (hDI hzl.1); omega)
      have hPcap := three_mul_card_nonthree_le hPI hP3
      change 3 * P.card ≤ 2 * ((q - 1 + 3) - (N / 3 + 1)) at hPcap
      have hEI : E ⊆ Icc (3 * len + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      have hEcap := card_Icc_le hEI
      change E.card ≤ (q - 1 + 1) - (3 * len + 1) at hEcap
      have hEsmall : E.card ≤ 2000 := by omega
      have hDrI : Dr ⊆ Icc (q + len) (2 * N / 3) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzI := mem_Icc.mp (hDI hz'.1)
        exact mem_Icc.mpr ⟨hz'.2, hzI.2⟩
      have hDreven : ∀ z ∈ Dr, z % 2 = 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z hz'.1 (by omega)).1
      have hDr3 : ∀ z ∈ Dr, z % 3 ≠ 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z hz'.1 (by omega)).2
      have hDrcap := six_mul_card_even_nonthree_le hDrI hDreven hDr3
      change 6 * Dr.card ≤ 2 * ((2 * N / 3 + 6) - (q + len)) at hDrcap
      omega
    · have hnoncross : 2 * (q + len) ≤ N := by omega
      let Dl := D.filter fun z ↦ z < q
      let R := D.filter fun z ↦ q + len ≤ z
      let P := Dl.filter fun z ↦ z ≤ 3 * len
      let E := Dl.filter fun z ↦ 3 * len < z
      let Dm := R.filter fun z ↦ 2 * z ≤ N
      let Du := R.filter fun z ↦ N < 2 * z
      have hDpart : Dl.card + R.card = D.card := by
        have hd : Disjoint Dl R := by
          rw [Finset.disjoint_left]
          intro z hzl hzr
          have hl := (mem_filter.mp hzl).2
          have hr := (mem_filter.mp hzr).2
          omega
        have hu : Dl ∪ R = D := by
          ext z
          simp only [Dl, R, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            have hn := hnotI ((filter_subset _ _) hz)
            by_cases hl : z < q
            · exact Or.inl ⟨hz, hl⟩
            · exact Or.inr ⟨hz, by omega⟩
        rw [← card_union_of_disjoint hd, hu]
      have hRpart : Dm.card + Du.card = R.card := by
        have hd : Disjoint Dm Du := by
          rw [Finset.disjoint_left]
          intro z hzm hzu
          have hm := (mem_filter.mp hzm).2
          have hu := (mem_filter.mp hzu).2
          omega
        have hu : Dm ∪ Du = R := by
          ext z
          simp only [Dm, Du, mem_union, mem_filter]
          constructor
          · rintro (h | h) <;> exact h.1
          · intro hz
            exact (le_or_gt (2 * z) N).imp (And.intro hz) (And.intro hz)
        rw [← card_union_of_disjoint hd, hu]
      have hPpart := card_filter_le_add_gt Dl (3 * len)
      change P.card + E.card = Dl.card at hPpart
      have hPI : P ⊆ Icc (N / 3 + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        have hzI := mem_Icc.mp (hDI hzl.1)
        exact mem_Icc.mpr ⟨hzI.1, by omega⟩
      have hP3 : ∀ z ∈ P, z % 3 ≠ 0 := by
        intro z hz hz3
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact centralImage_not_three_below_interval hP hsub hI
          ((filter_subset _ _) hzl.1) (Nat.dvd_of_mod_eq_zero hz3)
          hz'.2 (by have hzI := mem_Icc.mp (hDI hzl.1); omega)
      have hPcap := three_mul_card_nonthree_le hPI hP3
      change 3 * P.card ≤ 2 * ((q - 1 + 3) - (N / 3 + 1)) at hPcap
      have hEI : E ⊆ Icc (3 * len + 1) (q - 1) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzl := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      have hEcap := card_Icc_le hEI
      change E.card ≤ (q - 1 + 1) - (3 * len + 1) at hEcap
      have hEsmall : E.card ≤ 2000 := by omega
      have hDmI : Dm ⊆ Icc (q + len) (N / 2) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzR := mem_filter.mp hz'.1
        exact mem_Icc.mpr ⟨hzR.2, by omega⟩
      have hDmcap := card_Icc_le hDmI
      change Dm.card ≤ (N / 2 + 1) - (q + len) at hDmcap
      have hDuI : Du ⊆ Icc (N / 2 + 1) (2 * N / 3) := by
        intro z hz
        have hz' := mem_filter.mp hz
        have hzI := mem_Icc.mp (hDI ((filter_subset _ _) hz'.1))
        exact mem_Icc.mpr ⟨by omega, hzI.2⟩
      have hDueven : ∀ z ∈ Du, z % 2 = 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z ((filter_subset _ _) hz'.1) hz'.2).1
      have hDu3 : ∀ z ∈ Du, z % 3 ≠ 0 := by
        intro z hz
        have hz' := mem_filter.mp hz
        exact (hDupper z ((filter_subset _ _) hz'.1) hz'.2).2
      have hDucap := six_mul_card_even_nonthree_le hDuI hDueven hDu3
      change 6 * Du.card ≤ 2 * ((2 * N / 3 + 6) - (N / 2 + 1)) at hDucap
      omega

lemma caseThree_nonzero_step_three {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₁ : (upperHalfResidue A N 1).Nonempty)
    (hV₂ : (upperHalfResidue A N 2).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 ((upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card - 1) ⊆
        upperHalfResidue A N 1 + upperHalfResidue A N 2) :
    3 * A.card ≤ N + 100000 := by
  let len := (upperHalfResidue A N 1).card +
    (upperHalfResidue A N 2).card - 1
  have hp₁ : 0 < (upperHalfResidue A N 1).card := card_pos.mpr hV₁
  have hp₂ : 0 < (upperHalfResidue A N 2).card := card_pos.mpr hV₂
  have hlenpos : 0 < len := by dsimp [len]; omega
  have hlen : 2 * (upperHalf A N).card ≤ 3 * (len + 1) := by
    dsimp [len]
    omega
  have hI : natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
    apply stepThree_divided_interval ha3
    simpa [len] using hQ
  exact caseThree_step_three_interval hP hsub htail hcase3 hlenpos hlen hI

/-- The first term of a nonempty progression lying in `V₀ + V₀` is divisible
by three. -/
lemma zero_AP_start_dvd_three {A : Finset ℕ} {N a d : ℕ}
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (hQ : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0) :
    3 ∣ a := by
  have hlen : 0 < 2 * (upperHalfResidue A N 0).card - 1 := by
    have h0 := card_pos.mpr hV₀
    omega
  have ha : a ∈ upperHalfResidue A N 0 + upperHalfResidue A N 0 :=
    hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp ha
  subst a
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hx3 := (mem_upperHalfResidue.mp hx).2
  have hy3 := (mem_upperHalfResidue.mp hy).2
  omega

/-- In the zero-dominant structural branch the common difference is again
one of `3,6,9`. -/
lemma zero_structural_step {A : Finset ℕ} {N a d : ℕ}
    (hsub : A ⊆ Icc 1 N) (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hd : 0 < d)
    (hQ : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) d) :
    d = 3 ∨ d = 6 ∨ d = 9 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  have hV₀sub : V₀ ⊆ V := filter_subset _ _
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    hV₀sub.trans (upperHalf_subset_interval hsub)
  have hres₀ : InOneResidue V₀ d := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change d * V₀.card ≤ (N + d) - (N / 2 + 1) at hcap
  change (N + 1) / 2 < 3 * V.card at htail
  change V.card ≤ 3 * V₀.card at hdom
  have hlarge : N / 18 + 1 ≤ V₀.card := by omega
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlen : 2 ≤ 2 * V₀.card - 1 := by omega
  have hlenpos : 0 < 2 * V₀.card - 1 := by omega
  have hlenone : 1 < 2 * V₀.card - 1 := by omega
  have hqa : a ∈ V₀ + V₀ := hQ (mem_natAP.mpr ⟨0, hlenpos, by simp⟩)
  have hqad : a + d ∈ V₀ + V₀ := by
    apply hQ
    exact mem_natAP.mpr ⟨1, hlenone, by simp⟩
  have hthree : ∀ z ∈ V₀ + V₀, 3 ∣ z := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx3 := (mem_upperHalfResidue.mp hx).2
    have hy3 := (mem_upperHalfResidue.mp hy).2
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
    omega
  have h3a := hthree a hqa
  have h3ad := hthree (a + d) hqad
  have h3d : 3 ∣ d := by
    obtain ⟨u, hu⟩ := h3a
    obtain ⟨v, hv⟩ := h3ad
    exact ⟨v - u, by omega⟩
  have hdlt : d < 12 := by
    by_contra hn
    have hd12 : 12 ≤ d := by omega
    obtain ⟨k, hk⟩ : ∃ k, V₀.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr hV₀)
    have hspan : d * k ≤ N - (N / 2 + 1) := by
      rw [hk, Nat.mul_add, Nat.mul_one] at hcap
      have heq : (N + d) - (N / 2 + 1) = N - (N / 2 + 1) + d := by omega
      rw [heq] at hcap
      omega
    have hmul : 12 * k ≤ d * k := Nat.mul_le_mul_right k hd12
    rw [hk] at hlarge
    omega
  obtain ⟨k, hk⟩ := h3d
  have hklt : k < 4 := by nlinarith
  interval_cases k <;> omega

/-- In the zero-dominant step-nine case the upper-half class cannot itself
be `0 (mod 9)`.  After division by nine, its least element has more than
half a complete block of successors, contradicting opposite-residue
pairing modulo that least element. -/
lemma zero_step_nine_start_nonzero {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 9 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 9) :
    (a / 3) % 3 ≠ 0 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  change (a / 3) % 3 ≠ 0
  intro ha0
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlenpos : 0 < 2 * V₀.card - 1 := by omega
  have hqa : a ∈ V₀ + V₀ := by
    apply hQ
    exact mem_natAP.mpr ⟨0, hlenpos, by simp⟩
  obtain ⟨u, hu, v, hv, huv⟩ := mem_add.mp hqa
  have ha9 : 9 ∣ a := by
    have hk3 : 3 ∣ a / 3 := Nat.dvd_iff_mod_eq_zero.mpr ha0
    obtain ⟨k, hk⟩ := hk3
    refine ⟨k, ?_⟩
    have haeq := Nat.mul_div_cancel' ha3
    omega
  have hsum9 : (u + v) % 9 = 0 := by
    rw [huv]
    exact Nat.dvd_iff_mod_eq_zero.mp ha9
  have hres₀ : InOneResidue V₀ 9 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hdiv9 : ∀ x ∈ V₀, 9 ∣ x := by
    intro x hx
    have hxu : x % 9 = u % 9 :=
      (ZMod.natCast_eq_natCast_iff x u 9).mp ((hr x hx).trans (hr u hu).symm)
    have hvu : v % 9 = u % 9 :=
      (ZMod.natCast_eq_natCast_iff v u 9).mp ((hr v hv).trans (hr u hu).symm)
    have hx3 : x % 3 = 0 := by
      simpa using (mem_upperHalfResidue.mp hx).2
    have hu3 : u % 3 = 0 := by
      simpa using (mem_upperHalfResidue.mp hu).2
    have hxrem3 : x % 9 % 3 = 0 := by
      rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 9)]
      exact hx3
    have hurem3 : u % 9 % 3 = 0 := by
      rw [Nat.mod_mod_of_dvd u (by norm_num : 3 ∣ 9)]
      exact hu3
    have hxlt := Nat.mod_lt x (by omega : 0 < 9)
    have hult := Nat.mod_lt u (by omega : 0 < 9)
    have hvlt := Nat.mod_lt v (by omega : 0 < 9)
    rw [Nat.add_mod] at hsum9
    rw [Nat.dvd_iff_mod_eq_zero]
    interval_cases x % 9 <;> interval_cases u % 9 <;>
      interval_cases v % 9 <;> omega
  let W := V₀.image fun x ↦ x / 9
  have hV₀sub : V₀ ⊆ A :=
    (filter_subset _ _).trans (ratSection_subset A N 1 2 1 1)
  have hPW : IsForbiddenTripleFree W := by
    exact (hP.mono hV₀sub).map_div (by omega) hdiv9
  have hWcard : W.card = V₀.card := by
    apply card_image_iff.mpr
    exact div_injOn_residue (r := 0) (q := 9) (by omega) fun x hx ↦
      Nat.dvd_iff_mod_eq_zero.mp (hdiv9 x hx)
  have hWne : W.Nonempty := hV₀.image _
  have hWI : W ⊆ Icc (N / 18 + 1) (N / 9) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hxV := mem_upperHalf.mp (mem_upperHalfResidue.mp hx).1
    have hxmul := Nat.mul_div_cancel' (hdiv9 x hx)
    apply mem_Icc.mpr
    constructor
    · omega
    · exact Nat.div_le_div_right (mem_Icc.mp (hsub hxV.1)).2
  let s := W.min' hWne
  have hsW : s ∈ W := W.min'_mem hWne
  have hleast : ∀ x ∈ W, s ≤ x := fun x hx ↦ W.min'_le x hx
  have hsI := mem_Icc.mp (hWI hsW)
  have hspos : 0 < s := by omega
  have hWs : W ⊆ Icc s (N / 9) := by
    intro x hx
    exact mem_Icc.mpr ⟨hleast x hx, (mem_Icc.mp (hWI hx)).2⟩
  have hposition := card_Icc_le hWs
  have htop : ∀ x ∈ W, x ≤ 2 * s := by
    intro x hx
    have hxI := mem_Icc.mp (hWI hx)
    omega
  have hdecomp : W = {s} ∪ firstBlock W s := by
    ext x
    simp only [mem_union, mem_singleton, mem_firstBlock]
    constructor
    · intro hx
      by_cases hxs : x = s
      · exact Or.inl hxs
      · exact Or.inr ⟨hx, by have := hleast x hx; omega, htop x hx⟩
    · rintro (rfl | hx)
      · exact hsW
      · exact hx.1
  have hdisj : Disjoint ({s} : Finset ℕ) (firstBlock W s) := by
    rw [Finset.disjoint_left]
    intro x hxs hx
    simp only [mem_singleton] at hxs
    subst x
    have := (mem_firstBlock.mp hx).2.1
    omega
  have hcardDecomp : W.card = 1 + (firstBlock W s).card := by
    calc
      W.card = ({s} ∪ firstBlock W s).card := congrArg Finset.card hdecomp
      _ = ({s} : Finset ℕ).card + (firstBlock W s).card :=
        card_union_of_disjoint hdisj
      _ = 1 + (firstBlock W s).card := by simp
  have hfirst := two_mul_card_firstBlock_le hPW hsW hspos
  change V.card ≤ 3 * V₀.card at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  change W.card ≤ (N / 9 + 1) - s at hposition
  omega

/-- The remaining zero-dominant step-nine branch has divided start `1` or
`2 (mod 3)` and therefore closes by the common half-window packing plus
induction on the lower-half multiples of three. -/
lemma caseThree_zero_step_nine {A : Finset ℕ} {N C a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000 ≤ N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 9 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 9)
    (hind : CoarseBound C (N / 6)
      ((divisibleInitial A N 3 2).image fun x ↦ x / 3)) :
    CoarseBound C N A := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hres₀ : InOneResidue V₀ 9 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change 9 * V₀.card ≤ (N + 9) - (N / 2 + 1) at hcap
  have hVcap : 6 * V.card ≤ N + 18 := by omega
  have hlen : N / 9 ≤ len := by dsimp [len]; omega
  have hat := zero_step_nine_start_nonzero hP hsub hN hV₀ htail hdom ha3 hQ hres
  have hQsub : natAP (a / 3) 3 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 9 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 3 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 3 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 9 * j = 3 * (a / 3 + 3 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  have hZcap := caseThree_step_nine_nonzero_low_nonthree_data
    hP hsub hlen hat hQsub
  exact caseThree_step_nine_nonzero_data hP hsub hN hVcap hZcap hind

/-- The zero-dominant step-six alternative is an instance of the common
parity packing argument above. -/
lemma caseThree_zero_step_six {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 6 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0)
    (hres : InOneResidue
      (upperHalfResidue A N 0 + upperHalfResidue A N 0) 6) :
    3 * A.card ≤ N + 18 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hres₀ : InOneResidue V₀ 6 := inOneResidue_add_left hV₀ hres
  obtain ⟨r, hr⟩ := hres₀
  have hV₀I : V₀ ⊆ Icc (N / 2 + 1) N :=
    (filter_subset _ _).trans (upperHalf_subset_interval hsub)
  have hcap := mul_card_fixed_zmod_le r hV₀I hr
  change 6 * V₀.card ≤ (N + 6) - (N / 2 + 1) at hcap
  have hVcap : 4 * V.card ≤ N + 12 := by omega
  have hdomlen : 2 * V.card ≤ 3 * len + 3 := by
    dsimp [len]
    omega
  have hoddcover : V.card ≤ len + V₀.card + 1 := by
    dsimp [len]
    omega
  have hQsub : natAP (a / 3) 2 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 6 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + 2 * j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + 2 * j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 6 * j = 3 * (a / 3 + 2 * j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_six_data hP hsub hVcap hdomlen hoddcover hQsub

/-- Division by three turns the zero-dominant step-three progression into
the unit-step interval required by the complete step-three estimate. -/
lemma caseThree_zero_step_three {A : Finset ℕ} {N a : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hV₀ : (upperHalfResidue A N 0).Nonempty)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hdom : (upperHalf A N).card ≤
      3 * (upperHalfResidue A N 0).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (ha3 : 3 ∣ a)
    (hQ : natAP a 3 (2 * (upperHalfResidue A N 0).card - 1) ⊆
      upperHalfResidue A N 0 + upperHalfResidue A N 0) :
    3 * A.card ≤ N + 100000 := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let len := 2 * V₀.card - 1
  change V.card ≤ 3 * V₀.card at hdom
  have hp : 0 < V₀.card := card_pos.mpr hV₀
  have hlenpos : 0 < len := by dsimp [len]; omega
  have hlen : 2 * V.card ≤ 3 * (len + 1) := by
    dsimp [len]
    omega
  have hI : natAP (a / 3) 1 len ⊆ thirdSumQuotient A N := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := mem_natAP.mp hz
    apply mem_quotientPart.mpr
    refine ⟨a + 3 * j, ?_, ?_, ?_⟩
    · apply mem_zmodFiber.mpr
      constructor
      · apply Finset.add_subset_add
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
          (show V₀ ⊆ upperHalf A N from filter_subset _ _)
        apply hQ
        exact mem_natAP.mpr ⟨j, hj, rfl⟩
      · rw [ZMod.natCast_eq_zero_iff]
        exact ⟨a / 3 + j, by
          have := Nat.mul_div_cancel' ha3
          omega⟩
    · exact ⟨a / 3 + j, by
        have := Nat.mul_div_cancel' ha3
        omega⟩
    · have heq : a + 3 * j = 3 * (a / 3 + j) := by
        have := Nat.mul_div_cancel' ha3
        omega
      rw [heq]
      simpa using hz
  exact caseThree_step_three_interval hP hsub htail hcase3 hlenpos hlen hI

/-! ### The enhanced central packing for the nonzero growth case -/

/-- A power of three times one property-P element cannot equal twice a
power of three times another.  This is Bedert's basic collision lemma. -/
lemma three_pow_ne_two_three_pow {A : Finset ℕ} (hP : IsForbiddenTripleFree A)
    {a b i j : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hapos : 0 < a)
    (hbpos : 0 < b) : 3 ^ i * a ≠ 2 * (3 ^ j * b) := by
  intro heq
  rcases le_total i j with hij | hji
  · have hp : 3 ^ j = 3 ^ i * 3 ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_of_le hij]
    rw [hp, mul_assoc, ← mul_assoc 2 (3 ^ i), mul_comm 2 (3 ^ i),
      mul_assoc] at heq
    have hcancel : a = 2 * (3 ^ (j - i) * b) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq
    have hba : b < a := by
      have hp1 : 1 ≤ 3 ^ (j - i) :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      nlinarith
    apply hP.not_dvd_of_lt hb ha hba
    exact ⟨2 * 3 ^ (j - i), by simpa [mul_assoc, mul_comm, mul_left_comm]
      using hcancel⟩
  · by_cases heqij : i = j
    · subst i
      have heq' : 3 ^ j * a = 3 ^ j * (2 * b) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using heq
      have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq'
      have hba : b < a := by nlinarith
      apply hP.not_dvd_of_lt hb ha hba
      exact ⟨2, by omega⟩
    · have hji' : j < i := lt_of_le_of_ne hji (Ne.symm heqij)
      have hp : 3 ^ i = 3 ^ j * 3 ^ (i - j) := by
        rw [← pow_add, Nat.add_sub_of_le hji]
      rw [hp, mul_assoc, ← mul_assoc 2 (3 ^ j), mul_comm 2 (3 ^ j),
        mul_assoc] at heq
      have hcancel : 3 ^ (i - j) * a = 2 * b :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 3)) heq
      have hpow : 3 ≤ 3 ^ (i - j) := by
        have hd : 0 < i - j := Nat.sub_pos_of_lt hji'
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
        rw [hk, pow_succ]
        have : 1 ≤ 3 ^ k :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        nlinarith
      have hab : a < b := by nlinarith
      apply hP.not_dvd_two_mul ha hb hab
      exact ⟨3 ^ (i - j), by simpa [mul_comm] using hcancel.symm⟩

/-- First move the lower half by powers of three into `(N/6,N/2]`. -/
noncomputable def tripleHalfBase (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (lowHalf A N).image (scaledMove 1 N 6)

/-- Double precisely the part of the power-three image at most `2N/9`. -/
def tripleHalfAdjust (N z : ℕ) : ℕ := if 9 * z ≤ 2 * N then 2 * z else z

noncomputable def tripleHalfImage (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfBase A N).image (tripleHalfAdjust N)

lemma tripleHalfBase_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfBase A N).card = (lowHalf A N).card := by
  apply card_image_iff.mpr
  apply scaledMove_injOn (hP.mono (filter_subset _ _))
  intro a ha
  exact hP.pos_of_mem hsub (mem_lowHalf.mp ha).1

lemma tripleHalfBase_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleHalfBase A N ⊆ Icc (N / 6 + 1) (N / 2) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  have ha' := mem_lowHalf.mp ha
  have hapos := hP.pos_of_mem hsub ha'.1
  have hlo := lt_scaledMove (b := 1) (T := N) (q := 6) (by omega) hapos
  have hup := scaledMove_le (b := 1) (T := N) (q := 6) (by omega) hapos
    (by omega)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma tripleHalfBase_has_source {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfBase A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ, z = 3 ^ e * a := by
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  exact ⟨a, ha, scaledWindowExp 1 N 6 a, by simp [scaledMove]⟩

lemma tripleHalfBase_no_double {A : Finset ℕ} {N x y : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hx : x ∈ tripleHalfBase A N) (hy : y ∈ tripleHalfBase A N) :
    x ≠ 2 * y := by
  obtain ⟨a, ha, i, rfl⟩ := tripleHalfBase_has_source hx
  obtain ⟨b, hb, j, rfl⟩ := tripleHalfBase_has_source hy
  exact three_pow_ne_two_three_pow (hP.mono (filter_subset _ _)) ha hb
    (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
    (hP.pos_of_mem hsub (mem_lowHalf.mp hb).1)

lemma tripleHalfAdjust_injOn {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Set.InjOn (tripleHalfAdjust N) (tripleHalfBase A N) := by
  intro x hx y hy hxy
  simp only [tripleHalfAdjust] at hxy
  split at hxy <;> split at hxy
  · omega
  · exact False.elim (tripleHalfBase_no_double hP hsub hy hx hxy.symm)
  · exact False.elim (tripleHalfBase_no_double hP hsub hx hy hxy)
  · exact hxy

lemma tripleHalfImage_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfImage A N).card = (lowHalf A N).card := by
  rw [tripleHalfImage, card_image_iff.mpr (tripleHalfAdjust_injOn hP hsub),
    tripleHalfBase_card hP hsub]

lemma tripleHalfImage_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleHalfImage A N ⊆ Icc (2 * N / 9 + 1) (N / 2) := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  have hbI := mem_Icc.mp (tripleHalfBase_subset hP hsub hb)
  simp only [tripleHalfAdjust]
  split
  · exact mem_Icc.mpr ⟨by omega, by omega⟩
  · exact mem_Icc.mpr ⟨by omega, hbI.2⟩

lemma tripleHalfImage_has_source {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfImage A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ,
      z = 3 ^ e * a ∨ z = 2 * (3 ^ e * a) := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
  obtain ⟨a, ha, e, rfl⟩ := tripleHalfBase_has_source hb
  refine ⟨a, ha, e, ?_⟩
  simp only [tripleHalfAdjust]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The four pieces of Bedert's power-three image. -/
noncomputable def tripleOddLow (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦ 3 * z ≤ N ∧ z % 2 = 1

noncomputable def tripleBad (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦
    3 * z ≤ N ∧ z % 2 = 0 ∧ 3 * (z / 2) ∈ tripleHalfImage A N

noncomputable def tripleGood (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦
    3 * z ≤ N ∧ z % 2 = 0 ∧ 3 * (z / 2) ∉ tripleHalfImage A N

noncomputable def tripleUpper (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).filter fun z ↦ N < 3 * z

noncomputable def tripleUpperGood (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleGood A N).image (fun z ↦ 3 * (z / 2)) ∪ tripleUpper A N

lemma tripleHalfImage_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ tripleHalfImage A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ z := by
  obtain ⟨a, ha, e, he | he⟩ := tripleHalfImage_has_source hz
  · refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
    rw [he]
    exact dvd_mul_left a (3 ^ e)
  · refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
    rw [he]
    simpa [mul_assoc] using dvd_mul_left a (2 * 3 ^ e)

lemma tripleImage_partition_card (A : Finset ℕ) (N : ℕ) :
    (tripleOddLow A N).card + (tripleBad A N).card +
      (tripleGood A N).card + (tripleUpper A N).card =
        (tripleHalfImage A N).card := by
  let Z := tripleHalfImage A N
  let O := tripleOddLow A N
  let B := tripleBad A N
  let G := tripleGood A N
  let U := tripleUpper A N
  have hOB : Disjoint O B := by
    rw [Finset.disjoint_left]
    intro z ho hb
    have ho' := (mem_filter.mp ho).2.2
    have hb' := (mem_filter.mp hb).2.2.1
    omega
  have hOG : Disjoint O G := by
    rw [Finset.disjoint_left]
    intro z ho hg
    have ho' := (mem_filter.mp ho).2.2
    have hg' := (mem_filter.mp hg).2.2.1
    omega
  have hOU : Disjoint O U := by
    rw [Finset.disjoint_left]
    intro z ho hu
    have ho' := (mem_filter.mp ho).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hBG : Disjoint B G := by
    rw [Finset.disjoint_left]
    intro z hb hg
    exact (mem_filter.mp hg).2.2.2 (mem_filter.mp hb).2.2.2
  have hBU : Disjoint B U := by
    rw [Finset.disjoint_left]
    intro z hb hu
    have hb' := (mem_filter.mp hb).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hGU : Disjoint G U := by
    rw [Finset.disjoint_left]
    intro z hg hu
    have hg' := (mem_filter.mp hg).2.1
    have hu' := (mem_filter.mp hu).2
    omega
  have hOBG : Disjoint (O ∪ B) G := by
    rw [Finset.disjoint_left]
    intro z hz hg
    rcases mem_union.mp hz with ho | hb
    · exact (Finset.disjoint_left.mp hOG) ho hg
    · exact (Finset.disjoint_left.mp hBG) hb hg
  have hAllU : Disjoint (O ∪ B ∪ G) U := by
    rw [Finset.disjoint_left]
    intro z hz hu
    rcases mem_union.mp hz with hz | hg
    · rcases mem_union.mp hz with ho | hb
      · exact (Finset.disjoint_left.mp hOU) ho hu
      · exact (Finset.disjoint_left.mp hBU) hb hu
    · exact (Finset.disjoint_left.mp hGU) hg hu
  have hunion : O ∪ B ∪ G ∪ U = Z := by
    ext z
    simp only [O, B, G, U, tripleOddLow, tripleBad, tripleGood, tripleUpper,
      mem_union, mem_filter]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hz
      by_cases hlo : 3 * z ≤ N
      · by_cases hodd : z % 2 = 1
        · exact Or.inl (Or.inl (Or.inl ⟨hz, hlo, hodd⟩))
        · have heven : z % 2 = 0 := by
            have := Nat.mod_lt z (by omega : 0 < 2)
            omega
          by_cases hm : 3 * (z / 2) ∈ Z
          · exact Or.inl (Or.inl (Or.inr ⟨hz, hlo, heven, hm⟩))
          · exact Or.inl (Or.inr ⟨hz, hlo, heven, hm⟩)
      · exact Or.inr ⟨hz, by omega⟩
  calc
    O.card + B.card + G.card + U.card =
        (O ∪ B ∪ G ∪ U).card := by
      rw [card_union_of_disjoint hAllU, card_union_of_disjoint hOBG,
        card_union_of_disjoint hOB]
    _ = Z.card := congrArg Finset.card hunion

lemma tripleUpperGood_card {A : Finset ℕ} {N : ℕ} :
    (tripleUpperGood A N).card =
      (tripleGood A N).card + (tripleUpper A N).card := by
  let G := tripleGood A N
  let U := tripleUpper A N
  let f : ℕ → ℕ := fun z ↦ 3 * (z / 2)
  have hinj : Set.InjOn f G := by
    intro x hx y hy hxy
    have hx0 := (mem_filter.mp hx).2.2.1
    have hy0 := (mem_filter.mp hy).2.2.1
    have hx2 : 2 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx0
    have hy2 : 2 ∣ y := Nat.dvd_iff_mod_eq_zero.mpr hy0
    have hdiv : x / 2 = y / 2 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
    calc
      x = 2 * (x / 2) := (Nat.mul_div_cancel' hx2).symm
      _ = 2 * (y / 2) := by rw [hdiv]
      _ = y := Nat.mul_div_cancel' hy2
  have hdisj : Disjoint (G.image f) U := by
    rw [Finset.disjoint_left]
    intro w hw hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact (mem_filter.mp hz).2.2.2 (mem_filter.mp hu).1
  rw [tripleUpperGood, card_union_of_disjoint hdisj,
    card_image_iff.mpr hinj]

lemma tripleUpperGood_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleUpperGood A N ⊆ Icc (N / 3 + 1) (N / 2) := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hz).1)
    have hzlo := (mem_filter.mp hz).2.1
    have hz0 := (mem_filter.mp hz).2.2.1
    have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
    have hzeq := Nat.mul_div_cancel' hz2
    have hzlo' : 2 * N < 9 * z := by omega
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hw).1)
    have hzlo := (mem_filter.mp hw).2
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩

lemma tripleUpperGood_source {A : Finset ℕ} {N w : ℕ}
    (hw : w ∈ tripleUpperGood A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ 2 * w := by
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor (mem_filter.mp hz).1
    refine ⟨a, ha, haN, ?_⟩
    have hz0 := (mem_filter.mp hz).2.2.1
    have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
    have hzeq := Nat.mul_div_cancel' hz2
    have : 2 * (3 * (z / 2)) = 3 * z := by omega
    rw [this]
    exact haz.mul_left 3
  · obtain ⟨a, ha, haN, haw⟩ := tripleHalfImage_source_divisor (mem_filter.mp hw).1
    exact ⟨a, ha, haN, haw.mul_left 2⟩

lemma tripleOddLow_add_high_odd_le {A : Finset ℕ} {N i : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hi : i = 1 ∨ i = 3) :
    (tripleOddLow A N).card + (modFourPart (highThird A N) i).card ≤
      N / 12 + 10 := by
  apply oddLeft_add_high_odd_le hP hsub
  · intro z hz
    have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub (mem_filter.mp hz).1)
    refine mem_Icc.mpr ⟨hzI.1, ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
    simpa [mul_comm] using (mem_filter.mp hz).2.1
  · intro z hz
    exact (mem_filter.mp hz).2.2
  · intro z hz
    obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor (mem_filter.mp hz).1
    exact ⟨a, ha, by omega, haz.mul_left 6⟩
  · exact hi

lemma tripleUpperGood_add_high_even_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleUpperGood A N).card +
      (parityPart (highThird A N) 0).card ≤ N / 6 + 3 := by
  let Z := tripleUpperGood A N
  let E := parityPart (highThird A N) 0
  let W := zmodFiber (Icc (2 * N / 3 + 1) N) (0 : ZMod 2)
  have hZE : Disjoint (Z.image fun z ↦ 2 * z) E := by
    rw [Finset.disjoint_left]
    intro w hw he
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    obtain ⟨a, ha, haN, haz⟩ := tripleUpperGood_source hz
    have he' := mem_highThird.mp (mem_parityPart.mp he).1
    have halt : a < 2 * z := by
      have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
      omega
    exact hP.not_dvd_of_lt ha he'.1 halt haz
  have hZU : Z.image (fun z ↦ 2 * z) ⊆ W := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
    apply mem_zmodFiber.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 2 z⟩
  have hEU : E ⊆ W := by
    intro z hz
    have hz' := mem_parityPart.mp hz
    have hzI := mem_Icc.mp (highThird_subset_interval hsub hz'.1)
    apply mem_zmodFiber.mpr
    refine ⟨mem_Icc.mpr hzI, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff' z 0 2).mpr
    simpa using hz'.2
  have hpack := card_add_card_le_of_disjoint_subsets hZE hZU hEU
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 2 * N / 3 + 1) (U := N)
    (0 : ZMod 2) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  have hZcard : (Z.image fun z ↦ 2 * z).card = Z.card := by
    apply card_image_iff.mpr
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  change (Z.image fun z ↦ 2 * z).card + E.card ≤ W.card at hpack
  change 2 * W.card ≤ (N + 2) - (2 * N / 3 + 1) at hcap
  have hL : 2 * N / 3 + 1 ≤ N + 2 := by omega
  have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
  rw [hZcard] at hpack
  change Z.card + E.card ≤ N / 6 + 3
  omega

/-- With both odd classes present, the divisible-by-four high sumset has
size at least the maximum used in Bedert's Lemma 10, up to one. -/
lemma high_mod_four_max_le_sum_add_one {A : Finset ℕ} {N : ℕ}
    (h1 : (modFourPart (highThird A N) 1).Nonempty)
    (h3 : (modFourPart (highThird A N) 3).Nonempty) :
    max ((modFourPart (highThird A N) 1).card +
          (modFourPart (highThird A N) 3).card)
        (max (2 * (modFourPart (highThird A N) 0).card)
          (2 * (modFourPart (highThird A N) 2).card)) ≤
      (highFourSums A N).card + 1 := by
  let H := highThird A N
  let S := highFourSums A N
  change (modFourPart H 1).Nonempty at h1
  change (modFourPart H 3).Nonempty at h3
  have h13sub : modFourPart H 1 + modFourPart H 3 ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_modFourPart.mp hx
    have hy' := mem_modFourPart.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod, hx'.2, hy'.2]
  have h13cd := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 h3
  have h13card := card_le_card h13sub
  have h13 : (modFourPart H 1).card + (modFourPart H 3).card ≤ S.card + 1 := by
    omega
  have hself (r : ℕ) (hr : r = 0 ∨ r = 2) :
      2 * (modFourPart H r).card ≤ S.card + 1 := by
    obtain hempty | hne := (modFourPart H r).eq_empty_or_nonempty
    · simp [hempty]
    · have hsubself : modFourPart H r + modFourPart H r ⊆ S := by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
        have hx' := mem_modFourPart.mp hx
        have hy' := mem_modFourPart.mp hy
        apply mem_zmodFiber.mpr
        refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
        rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
          Nat.add_mod, hx'.2, hy'.2]
        rcases hr with rfl | rfl <;> decide
      have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hne hne
      have hc := card_le_card hsubself
      omega
  have h0 := hself 0 (Or.inl rfl)
  have h2 := hself 2 (Or.inr rfl)
  change max ((modFourPart H 1).card + (modFourPart H 3).card)
      (max (2 * (modFourPart H 0).card) (2 * (modFourPart H 2).card)) ≤
    S.card + 1
  omega

lemma tripleUpperGood_add_highFourSums_le {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleUpperGood A N).card + (highFourSums A N).card ≤ N / 6 + 4 := by
  let Z := tripleUpperGood A N
  let S := highFourSums A N
  let W := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) (0 : ZMod 4)
  have hB : ∀ z ∈ Z, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * z := by
    intro z hz
    obtain ⟨a, ha, haN, haz⟩ := tripleUpperGood_source hz
    exact ⟨a, ha, by omega, dvd_trans haz (by exact ⟨2, by ring⟩)⟩
  have hH : ∀ x ∈ highThird A N, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hZU : Z.image (fun z ↦ 4 * z) ⊆ W := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hzI := mem_Icc.mp (tripleUpperGood_subset hP hsub hz)
    apply mem_zmodFiber.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by
      rw [ZMod.natCast_eq_zero_iff]
      exact dvd_mul_right 4 z⟩
  have hSU : S ⊆ W := by
    intro w hw
    have hw' := mem_zmodFiber.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hw'.1
    have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
    have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
    exact mem_zmodFiber.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hw'.2⟩
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hB hH
    (filter_subset _ _) hZU hSU
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 4 * N / 3 + 1) (U := 2 * N)
    (0 : ZMod 4) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change Z.card + S.card ≤ W.card at hp
  change 4 * W.card ≤ (2 * N + 4) - (4 * N / 3 + 1) at hcap
  have hL : 4 * N / 3 + 1 ≤ 2 * N + 4 := by omega
  have hraw := (Nat.le_sub_iff_add_le hL).mp hcap
  change Z.card + S.card ≤ N / 6 + 4
  omega

lemma card_modFour_parts (H : Finset ℕ) :
    (modFourPart H 0).card + (modFourPart H 1).card +
      (modFourPart H 2).card + (modFourPart H 3).card = H.card := by
  let f : ℕ → ℕ := fun x ↦ x % 4
  have hmap : (H : Set ℕ).MapsTo f (range 4) := by
    intro x hx
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have h := Finset.card_eq_sum_card_fiberwise hmap
  simp only [sum_range_succ, sum_range_zero] at h
  have heq (r : ℕ) (hr : r < 4) :
      H.filter (fun x ↦ f x = r) = modFourPart H r := by
    ext x
    simp [f, modFourPart, Nat.mod_eq_of_lt hr]
  rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega),
    heq 3 (by omega)] at h
  change H.card = 0 + (modFourPart H 0).card + (modFourPart H 1).card +
    (modFourPart H 2).card + (modFourPart H 3).card at h
  omega

/-- The bad-image reserve used in the hard nonzero growth branch. -/
lemma triple_bad_reserve {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hlarge : N + 2 < 3 * A.card) :
    N ≤ 24 * ((middleSixth A N).card + (tripleBad A N).card) + 2000 := by
  let O := tripleOddLow A N
  let B := tripleBad A N
  let G := tripleGood A N
  let U := tripleUpper A N
  let R := tripleUpperGood A N
  let H := highThird A N
  let Y := middleSixth A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let E := parityPart H 0
  let P := parityPart H 1
  have hZcard := tripleHalfImage_card hP hsub
  have hpart := tripleImage_partition_card A N
  have hRcard := tripleUpperGood_card (A := A) (N := N)
  have hHpart := card_modFour_one_add_three H
  have hHfour := card_modFour_parts H
  have hpar := card_parity_parts H
  have hVpart := card_middleSixth_add_highThird hsub
  have hAV := card_lowHalf_add_upperHalf hsub
  change O.card + B.card + G.card + U.card = (tripleHalfImage A N).card at hpart
  change R.card = G.card + U.card at hRcard
  change H₁.card + H₃.card = P.card at hHpart
  change H₀.card + H₁.card + H₂.card + H₃.card = H.card at hHfour
  change E.card + P.card = H.card at hpar
  change Y.card + H.card = (upperHalf A N).card at hVpart
  change (lowHalf A N).card + (upperHalf A N).card = A.card at hAV
  change (tripleHalfImage A N).card = (lowHalf A N).card at hZcard
  change 6 * H.card < N + 144 at hcase3
  change N + 2 < 3 * A.card at hlarge
  change N ≤ 24 * (Y.card + B.card) + 2000
  have hRe := tripleUpperGood_add_high_even_le hP hsub
  change R.card + E.card ≤ N / 6 + 3 at hRe
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · let M := max (H₁.card + H₃.card) (max (2 * H₀.card) (2 * H₂.card))
      have hM := high_mod_four_max_le_sum_add_one h1 h3
      change M ≤ (highFourSums A N).card + 1 at hM
      have hRS := tripleUpperGood_add_highFourSums_le hP hsub
      change R.card + (highFourSums A N).card ≤ N / 6 + 4 at hRS
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      change O.card + H₃.card ≤ N / 12 + 10 at hO3
      have hOm : O.card + max H₁.card H₃.card ≤ N / 12 + 10 := by
        omega
      have hRM : R.card + M ≤ N / 6 + 5 := by omega
      have hMlower : 3 * H.card ≤ 4 * (M + max H₁.card H₃.card) := by
        dsimp [M]
        omega
      have hcore : 24 * (O.card + R.card + H.card) ≤ 7 * N + 504 := by
        omega
      have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
        omega
      omega
    · have hH₃ : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      have hcore : 4 * (O.card + R.card + H.card) ≤ N + 52 := by omega
      have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
        omega
      omega
  · have hH₁ : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
    change O.card + H₃.card ≤ N / 12 + 10 at hO3
    have hcore : 4 * (O.card + R.card + H.card) ≤ N + 52 := by omega
    have hAeq : A.card = B.card + Y.card + O.card + R.card + H.card := by
      omega
    omega

/-! ### Bedert's final auxiliary set `B₃` -/

def tripleCentralMove (N z : ℕ) : ℕ := if 3 * z ≤ N then 2 * z else z

noncomputable def triplePrimary (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleHalfImage A N).image (tripleCentralMove N) ∪ middleSixth A N

lemma tripleHalfImage_low_mem_base {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleHalfImage A N) (hzlo : 3 * z ≤ N) :
    z ∈ tripleHalfBase A N := by
  obtain ⟨b, hb, hbeq⟩ := mem_image.mp hz
  have hbI := mem_Icc.mp (tripleHalfBase_subset hP hsub hb)
  simp only [tripleHalfAdjust] at hbeq
  split at hbeq
  · omega
  · simpa [hbeq] using hb

lemma tripleHalfImage_no_double_low {A : Finset ℕ} {N x : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hx : x ∈ tripleHalfImage A N) (hxlo : 3 * x ≤ N) :
    2 * x ∉ tripleHalfImage A N := by
  intro h2x
  have hxB := tripleHalfImage_low_mem_base hP hsub hx hxlo
  obtain ⟨b, hb, hbeq⟩ := mem_image.mp h2x
  simp only [tripleHalfAdjust] at hbeq
  split at hbeq
  · have hbx : b = x := by omega
    subst b
    have hxI := mem_Icc.mp (tripleHalfImage_subset hP hsub hx)
    omega
  · apply tripleHalfBase_no_double hP hsub hb hxB
    omega

lemma tripleCentralMove_injOn {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Set.InjOn (tripleCentralMove N) (tripleHalfImage A N) := by
  intro x hx y hy hxy
  simp only [tripleCentralMove] at hxy
  split at hxy <;> split at hxy
  · omega
  · exact False.elim (tripleHalfImage_no_double_low hP hsub hx (by assumption)
      (by simpa [hxy] using hy))
  · exact False.elim (tripleHalfImage_no_double_low hP hsub hy (by assumption)
      (by simpa [hxy] using hx))
  · exact hxy

lemma tripleCentralMove_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleHalfImage A N).image (tripleCentralMove N) ⊆
      Icc (N / 3 + 1) (2 * N / 3) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub hz)
  simp only [tripleCentralMove]
  split
  · have hzlo : 2 * N < 9 * z := by omega
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · omega
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
      omega
  · refine mem_Icc.mpr ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
    omega

lemma tripleCentralMove_source_divisor {A : Finset ℕ} {N w : ℕ}
    (hw : w ∈ (tripleHalfImage A N).image (tripleCentralMove N)) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ w := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, haN, haz⟩ := tripleHalfImage_source_divisor hz
  refine ⟨a, ha, haN, ?_⟩
  simp only [tripleCentralMove]
  split
  · exact haz.mul_left 2
  · exact haz

lemma triplePrimary_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    triplePrimary A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  rcases mem_union.mp hz with hz | hz
  · exact tripleCentralMove_subset hP hsub hz
  · have hz' := mem_middleSixth.mp hz
    have hzN := (mem_Icc.mp (hsub hz'.1)).2
    exact mem_Icc.mpr ⟨by omega, by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
      simpa [mul_comm] using hz'.2.2⟩

lemma triplePrimary_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hz : z ∈ triplePrimary A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ z := by
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨a, ha, haN, haz⟩ := tripleCentralMove_source_divisor hz
    exact ⟨a, ha, by omega, haz⟩
  · have hz' := mem_middleSixth.mp hz
    exact ⟨z, hz'.1, hz'.2.2, dvd_refl z⟩

lemma triplePrimary_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (triplePrimary A N).card =
      (lowHalf A N).card + (middleSixth A N).card := by
  let Z := tripleHalfImage A N
  let f := tripleCentralMove N
  let Y := middleSixth A N
  have hdisj : Disjoint (Z.image f) Y := by
    rw [Finset.disjoint_left]
    intro z hz hy
    obtain ⟨a, ha, haN, haz⟩ := tripleCentralMove_source_divisor hz
    have hy' := mem_middleSixth.mp hy
    have halt : a < z := by omega
    exact hP.not_dvd_of_lt ha hy'.1 halt haz
  change (Z.image f ∪ Y).card = (lowHalf A N).card + Y.card
  rw [card_union_of_disjoint hdisj,
    card_image_iff.mpr (tripleCentralMove_injOn hP hsub),
    tripleHalfImage_card hP hsub]

lemma tripleBad_extra_spec {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleBad A N) :
    ∃ a ∈ lowHalf A N, ∃ e : ℕ,
      4 ∣ z ∧ 9 * (z / 4) = 3 ^ e * a ∧
        N < 2 * (9 * (z / 4)) ∧ 3 * (9 * (z / 4)) ≤ 2 * N := by
  have hzZ := (mem_filter.mp hz).1
  have hzlo := (mem_filter.mp hz).2.1
  have hz0 := (mem_filter.mp hz).2.2.1
  have hwZ := (mem_filter.mp hz).2.2.2
  have hz2 : 2 ∣ z := Nat.dvd_iff_mod_eq_zero.mpr hz0
  have hzeven := Nat.mul_div_cancel' hz2
  have hzB := tripleHalfImage_low_mem_base hP hsub hzZ hzlo
  obtain ⟨a, ha, i, hza⟩ := tripleHalfBase_has_source hzB
  obtain ⟨b, hb, hbw⟩ := mem_image.mp hwZ
  by_cases hbsmall : 9 * b ≤ 2 * N
  · simp only [tripleHalfAdjust, if_pos hbsmall] at hbw
    obtain ⟨c, hc, j, hbc⟩ := tripleHalfBase_has_source hb
    have h4mul : 4 ∣ 3 * z := by
      refine ⟨b, ?_⟩
      omega
    have h4z : 4 ∣ z :=
      (show Nat.Coprime 4 3 by decide).dvd_mul_left.mp h4mul
    have hzfour := Nat.mul_div_cancel' h4z
    have hbeq : b = 3 * (z / 4) := by omega
    refine ⟨c, hc, j + 1, h4z, ?_, ?_, ?_⟩
    · calc
        9 * (z / 4) = 3 * b := by omega
        _ = 3 ^ (j + 1) * c := by rw [hbc, pow_succ]; ring
    · have hzI := mem_Icc.mp (tripleHalfImage_subset hP hsub hzZ)
      omega
    · omega
  · simp only [tripleHalfAdjust, if_neg hbsmall] at hbw
    obtain ⟨c, hc, j, hbc⟩ := tripleHalfBase_has_source hb
    have hcollision : 3 ^ (i + 1) * a = 2 * (3 ^ j * c) := by
      calc
        3 ^ (i + 1) * a = 3 * (3 ^ i * a) := by rw [pow_succ]; ring
        _ = 3 * z := by rw [hza]
        _ = 2 * b := by omega
        _ = 2 * (3 ^ j * c) := by rw [hbc]
    exact False.elim ((three_pow_ne_two_three_pow hP
      (mem_lowHalf.mp ha).1 (mem_lowHalf.mp hc).1
      (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
      (hP.pos_of_mem hsub (mem_lowHalf.mp hc).1)) hcollision)

noncomputable def tripleBadExtra (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (tripleBad A N).image fun z ↦ 9 * (z / 4)

lemma tripleBadExtra_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleBadExtra A N ⊆ Icc (N / 2 + 1) (2 * N / 3) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, e, h4z, hlo, hlow, hupp⟩ := tripleBad_extra_spec hP hsub hz
  refine mem_Icc.mpr ⟨by omega, ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
  simpa [mul_comm] using hupp

lemma tripleBadExtra_source {A : Finset ℕ} {N w : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hw : w ∈ tripleBadExtra A N) :
    ∃ a ∈ A, 2 * a ≤ N ∧ a ∣ w := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
  obtain ⟨a, ha, e, h4z, heq, hlo, hupp⟩ := tripleBad_extra_spec hP hsub hz
  refine ⟨a, (mem_lowHalf.mp ha).1, (mem_lowHalf.mp ha).2, ?_⟩
  rw [heq]
  exact dvd_mul_left a (3 ^ e)

lemma tripleBadExtra_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleBadExtra A N).card = (tripleBad A N).card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  obtain ⟨a, ha, i, hx4, hxa, hxlo, hxhi⟩ := tripleBad_extra_spec hP hsub hx
  obtain ⟨b, hb, j, hy4, hyb, hylo, hyhi⟩ := tripleBad_extra_spec hP hsub hy
  have hqx : 4 * (x / 4) = x := Nat.mul_div_cancel' hx4
  have hqy : 4 * (y / 4) = y := Nat.mul_div_cancel' hy4
  have hq : x / 4 = y / 4 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
  omega

lemma tripleBadExtra_disjoint_triplePrimary {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (tripleBadExtra A N) (triplePrimary A N) := by
  rw [Finset.disjoint_left]
  intro w hwE hwP
  rcases mem_union.mp hwP with hwM | hwY
  · obtain ⟨x, hx, hxw⟩ := mem_image.mp hwM
    have hwI := mem_Icc.mp (tripleBadExtra_subset hP hsub hwE)
    simp only [tripleCentralMove] at hxw
    split at hxw
    · have hxB := tripleHalfImage_low_mem_base hP hsub hx (by assumption)
      obtain ⟨b, hb, j, hxb⟩ := tripleHalfBase_has_source hxB
      obtain ⟨z, hz, hzw⟩ := mem_image.mp hwE
      obtain ⟨a, ha, i, hz4, hza, hzlo, hzhi⟩ :=
        tripleBad_extra_spec hP hsub hz
      have hcollision : 3 ^ i * a = 2 * (3 ^ j * b) := by
        calc
          3 ^ i * a = 9 * (z / 4) := hza.symm
          _ = w := hzw
          _ = 2 * x := hxw.symm
          _ = 2 * (3 ^ j * b) := by rw [hxb]
      exact (three_pow_ne_two_three_pow hP
        (mem_lowHalf.mp ha).1 (mem_lowHalf.mp hb).1
        (hP.pos_of_mem hsub (mem_lowHalf.mp ha).1)
        (hP.pos_of_mem hsub (mem_lowHalf.mp hb).1)) hcollision
    · have hxI := mem_Icc.mp (tripleHalfImage_subset hP hsub hx)
      omega
  · obtain ⟨a, ha, haN, haw⟩ := tripleBadExtra_source hP hsub hwE
    have hwY' := mem_middleSixth.mp hwY
    have halt : a < w := by omega
    exact hP.not_dvd_of_lt ha hwY'.1 halt haw

noncomputable def tripleFinal (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  tripleBadExtra A N ∪ triplePrimary A N

lemma card_lowHalf_add_middleSixth {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    (lowHalf A N).card + (middleSixth A N).card =
      (lowTwoThirds A N).card := by
  have hdisj : Disjoint (lowHalf A N) (middleSixth A N) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx' := mem_lowHalf.mp hx
    have hy' := mem_middleSixth.mp hy
    omega
  have hunion : lowHalf A N ∪ middleSixth A N = lowTwoThirds A N := by
    ext x
    simp only [mem_union, mem_lowHalf, mem_middleSixth, mem_lowTwoThirds]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, by omega⟩
      · exact ⟨hx.1, hx.2.2⟩
    · intro hx
      by_cases hlo : 2 * x ≤ N
      · exact Or.inl ⟨hx.1, hlo⟩
      · exact Or.inr ⟨hx.1, by omega, hx.2⟩
  rw [← card_union_of_disjoint hdisj, hunion]

lemma tripleFinal_card {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (tripleFinal A N).card =
      (lowTwoThirds A N).card + (tripleBad A N).card := by
  rw [tripleFinal,
    card_union_of_disjoint (tripleBadExtra_disjoint_triplePrimary hP hsub),
    tripleBadExtra_card hP hsub, triplePrimary_card hP hsub,
    ← card_lowHalf_add_middleSixth hsub]
  omega

lemma tripleFinal_subset {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    tripleFinal A N ⊆ Icc (N / 3 + 1) (2 * N / 3) := by
  intro z hz
  rcases mem_union.mp hz with hz | hz
  · have hzI := mem_Icc.mp (tripleBadExtra_subset hP hsub hz)
    exact mem_Icc.mpr ⟨by omega, hzI.2⟩
  · exact triplePrimary_subset hP hsub hz

lemma tripleFinal_source_divisor {A : Finset ℕ} {N z : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hz : z ∈ tripleFinal A N) :
    ∃ a ∈ A, 3 * a ≤ 2 * N ∧ a ∣ z := by
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨a, ha, haN, haz⟩ := tripleBadExtra_source hP hsub hz
    exact ⟨a, ha, by omega, haz⟩
  · exact triplePrimary_source_divisor hz

lemma tripleFinal_disjoint_thirdSumQuotient {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    Disjoint (tripleFinal A N) (thirdSumQuotient A N) := by
  rw [Finset.disjoint_left]
  intro b hbB hbQ
  obtain ⟨a, haA, haN, hab⟩ := tripleFinal_source_divisor hP hsub hbB
  have hbW := mem_Icc.mp (tripleFinal_subset hP hsub hbB)
  have hbpos : 0 < b := by omega
  have hapos : 0 < a := hP.pos_of_mem hsub haA
  have hab_le : a ≤ b := Nat.le_of_dvd hbpos hab
  have h3 := quotientPart_spec hbQ
  have hsum := (mem_zmodFiber.mp h3).1
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.mp hsum
  have hx' := mem_upperHalf.mp hx
  have hy' := mem_upperHalf.mp hy
  have hxN := (mem_Icc.mp (hsub hx'.1)).2
  have hyN := (mem_Icc.mp (hsub hy'.1)).2
  by_cases hax : a < x
  · by_cases hay : a < y
    · apply hP.not_dvd_add haA hx'.1 hy'.1 hax hay
      rw [hxy]
      exact hab.mul_left 3
    · have : x > N := by omega
      omega
  · have : y > N := by omega
    omega

lemma caseThree_enhanced_packing {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    (lowTwoThirds A N).card + (tripleBad A N).card +
      (thirdSumQuotient A N).card ≤
        (Icc (N / 3 + 1) (2 * N / 3)).card := by
  have hp := card_add_card_le_of_disjoint_subsets
    (tripleFinal_disjoint_thirdSumQuotient hP hsub)
    (tripleFinal_subset hP hsub) (thirdSumQuotient_subset_central hsub)
  rw [tripleFinal_card hP hsub] at hp
  exact hp

lemma nonzero_decomposition {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N) :
    A.card ≤ (divisibleInitial A N 3 1).card +
      (lowNonthreeImagePart A N 1).card +
      (lowNonthreeImagePart A N 2).card +
      (upperHalfResidue A N 1).card +
      (upperHalfResidue A N 2).card := by
  let V := upperHalf A N
  let V₀ := upperHalfResidue A N 0
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let L := lowHalf A N
  let L₀ := L.filter fun x ↦ x % 3 = 0
  let Lₙ := L.filter fun x ↦ x % 3 ≠ 0
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  have hVpart := card_upperHalf_residues A N
  change V₀.card + V₁.card + V₂.card = V.card at hVpart
  have hCparts := card_lowNonthreeImage_parts (A := A) (N := N)
  have hCcard := card_lowNonthreeImage hP hsub
  change C₁.card + C₂.card = (lowNonthreeImage A N).card at hCparts
  have hCcard' : (lowNonthreeImage A N).card = Lₙ.card := by
    simpa [Lₙ, L] using hCcard
  have hLpart : L₀.card + Lₙ.card = L.card := by
    have hdisj : Disjoint L₀ Lₙ := by
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      exact (mem_filter.mp hxn).2 (mem_filter.mp hx0).2
    have hunion : L₀ ∪ Lₙ = L := by
      ext x
      simp only [L₀, Lₙ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases hmod : x % 3 = 0
        · exact Or.inl ⟨hx, hmod⟩
        · exact Or.inr ⟨hx, hmod⟩
    rw [← card_union_of_disjoint hdisj, hunion]
  have hL₀D : L₀ ⊆ D := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxL := mem_lowHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxL.1, Nat.dvd_iff_mod_eq_zero.mpr hx'.2, ?_⟩
    have hxN := (mem_Icc.mp (hsub hxL.1)).2
    omega
  have hV₀D : V₀ ⊆ D := by
    intro x hx
    have hx' := mem_upperHalfResidue.mp hx
    have hxV := mem_upperHalf.mp hx'.1
    apply mem_divisibleInitial.mpr
    refine ⟨hxV.1, Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hx'.2), ?_⟩
    have hxN := (mem_Icc.mp (hsub hxV.1)).2
    omega
  have hL₀V₀ : Disjoint L₀ V₀ := by
    rw [Finset.disjoint_left]
    intro x hxL hxV
    have hl := mem_lowHalf.mp (mem_filter.mp hxL).1
    have hv := mem_upperHalf.mp (mem_upperHalfResidue.mp hxV).1
    omega
  have hDcover : L₀.card + V₀.card ≤ D.card := by
    rw [← card_union_of_disjoint hL₀V₀]
    exact card_le_card (union_subset hL₀D hV₀D)
  have hAV := card_lowHalf_add_upperHalf hsub
  change L.card + V.card = A.card at hAV
  change A.card ≤ D.card + C₁.card + C₂.card + V₁.card + V₂.card
  omega

lemma modFour_one_add_three_subset {H : Finset ℕ} :
    modFourPart H 1 + modFourPart H 3 ⊆
      zmodFiber (H + H) (0 : ZMod 4) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_modFourPart.mp hx
  have hy' := mem_modFourPart.mp hy
  apply mem_zmodFiber.mpr
  refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.add_mod, hx'.2, hy'.2]

lemma modFour_self_subset {H : Finset ℕ} {r : ℕ} (hr : r = 0 ∨ r = 2) :
    modFourPart H r + modFourPart H r ⊆
      zmodFiber (H + H) (0 : ZMod 4) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_modFourPart.mp hx
  have hy' := mem_modFourPart.mp hy
  apply mem_zmodFiber.mpr
  refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.add_mod, hx'.2, hy'.2]
  rcases hr with rfl | rfl <;> decide

/-- Bedert's Lemma 10/Corollary 1 fork.  Either the middle-sixth/bad-set
reserve is already of order `N/12`, or the divisible-by-four top sumset
contains a progression whose length is at least half the size of the top
third, up to one endpoint. -/
lemma strong_reserve_or_fourAP {A : Finset ℕ} {N : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hlarge : N + 2 < 3 * A.card) :
    N ≤ 12 * ((middleSixth A N).card + (tripleBad A N).card) + 1000 ∨
      ∃ a d len : ℕ, 0 < d ∧
        natAP a d len ⊆ highFourSums A N ∧
        (highThird A N).card ≤ 2 * (len + 1) := by
  let O := tripleOddLow A N
  let B := tripleBad A N
  let R := tripleUpperGood A N
  let H := highThird A N
  let Y := middleSixth A N
  let H₀ := modFourPart H 0
  let H₁ := modFourPart H 1
  let H₂ := modFourPart H 2
  let H₃ := modFourPart H 3
  let S := highFourSums A N
  have hZcard := tripleHalfImage_card hP hsub
  have hpart := tripleImage_partition_card A N
  have hRcard := tripleUpperGood_card (A := A) (N := N)
  have hHfour := card_modFour_parts H
  have hVpart := card_middleSixth_add_highThird hsub
  have hAV := card_lowHalf_add_upperHalf hsub
  change O.card + B.card + (tripleGood A N).card + (tripleUpper A N).card =
    (tripleHalfImage A N).card at hpart
  change R.card = (tripleGood A N).card + (tripleUpper A N).card at hRcard
  change H₀.card + H₁.card + H₂.card + H₃.card = H.card at hHfour
  change Y.card + H.card = (upperHalf A N).card at hVpart
  change (lowHalf A N).card + (upperHalf A N).card = A.card at hAV
  change (tripleHalfImage A N).card = (lowHalf A N).card at hZcard
  change N + 2 < 3 * A.card at hlarge
  by_cases h1 : H₁.Nonempty
  · by_cases h3 : H₃.Nonempty
    · have h13sub : H₁ + H₃ ⊆ S := modFour_one_add_three_subset
      have h00sub : H₀ + H₀ ⊆ S := modFour_self_subset (Or.inl rfl)
      have h22sub : H₂ + H₂ ⊆ S := modFour_self_subset (Or.inr rfl)
      let m13 := H₁.card + H₃.card
      let m0 := 2 * H₀.card
      let m2 := 2 * H₂.card
      have hhalf : H.card ≤ 2 * max m13 (max m0 m2) := by
        dsimp [m13, m0, m2]
        omega
      have hm13pos : 0 < m13 := by
        have hp1 : 0 < H₁.card := card_pos.mpr h1
        have hp3 : 0 < H₃.card := card_pos.mpr h3
        dsimp [m13]
        omega
      have hRS := tripleUpperGood_add_highFourSums_le hP hsub
      change R.card + S.card ≤ N / 6 + 4 at hRS
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      change O.card + H₃.card ≤ N / 12 + 10 at hO3
      have hOmax : O.card + max H₁.card H₃.card ≤ N / 12 + 10 := by omega
      have finish (hHS : H.card ≤ S.card + 3 + max H₁.card H₃.card) :
          N ≤ 12 * (Y.card + B.card) + 1000 := by
        have hcore : O.card + R.card + H.card ≤ N / 4 + 20 := by omega
        omega
      rcases le_total m13 (max m0 m2) with hle | hge
      · rcases le_total m0 m2 with h02 | h20
        · have hm : max m0 m2 = m2 := max_eq_right h02
          rw [hm] at hle hhalf
          have hall : max m13 m2 = m2 := max_eq_right hle
          rw [hall] at hhalf
          have hm2pos : 0 < H₂.card := by dsimp [m2] at hle; omega
          rcases bgAlternative_of_nonempty (S := H₂) (T := H₂)
            (card_pos.mp hm2pos) (card_pos.mp hm2pos) with hg | hs
          · left
            apply finish
            have hc := card_le_card h22sub
            simp only [min_self] at hg
            dsimp [m13, m0, m2] at hle h02
            omega
          · right
            obtain ⟨a, d, hd, hQ, hres⟩ := hs
            refine ⟨a, d, m2 - 1, hd, ?_, ?_⟩
            · simpa [m2, two_mul] using hQ.trans h22sub
            · have hm2pos' : 0 < m2 := by dsimp [m2]; omega
              rw [Nat.sub_add_cancel (by omega : 1 ≤ m2)]
              exact hhalf
        · have hm : max m0 m2 = m0 := max_eq_left h20
          rw [hm] at hle hhalf
          have hall : max m13 m0 = m0 := max_eq_right hle
          rw [hall] at hhalf
          have hm0pos : 0 < H₀.card := by dsimp [m0] at hle; omega
          rcases bgAlternative_of_nonempty (S := H₀) (T := H₀)
            (card_pos.mp hm0pos) (card_pos.mp hm0pos) with hg | hs
          · left
            apply finish
            have hc := card_le_card h00sub
            simp only [min_self] at hg
            dsimp [m13, m0, m2] at hle h20
            omega
          · right
            obtain ⟨a, d, hd, hQ, hres⟩ := hs
            refine ⟨a, d, m0 - 1, hd, ?_, ?_⟩
            · simpa [m0, two_mul] using hQ.trans h00sub
            · have hm0pos' : 0 < m0 := by dsimp [m0]; omega
              rw [Nat.sub_add_cancel (by omega : 1 ≤ m0)]
              exact hhalf
      · have hall : max m13 (max m0 m2) = m13 := max_eq_left hge
        rw [hall] at hhalf
        rcases bgAlternative_of_nonempty h1 h3 with hg | hs
        · left
          apply finish
          have hc := card_le_card h13sub
          change H₁.card + H₃.card + min H₁.card H₃.card ≤
            (H₁ + H₃).card + 3 at hg
          dsimp [m13, m0, m2] at hge
          omega
        · right
          obtain ⟨a, d, hd, hQ, hres⟩ := hs
          refine ⟨a, d, m13 - 1, hd, ?_, ?_⟩
          · simpa [m13] using hQ.trans h13sub
          · rw [Nat.sub_add_cancel (by omega : 1 ≤ m13)]
            exact hhalf
    · left
      have hH₃ : H₃.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h3)
      have hRe := tripleUpperGood_add_high_even_le hP hsub
      change R.card + (parityPart H 0).card ≤ N / 6 + 3 at hRe
      have hO1 := tripleOddLow_add_high_odd_le hP hsub (i := 1) (Or.inl rfl)
      change O.card + H₁.card ≤ N / 12 + 10 at hO1
      have hpar := card_parity_parts H
      have hodd := card_modFour_one_add_three H
      change (parityPart H 0).card + (parityPart H 1).card = H.card at hpar
      change H₁.card + H₃.card = (parityPart H 1).card at hodd
      change N ≤ 12 * (Y.card + B.card) + 1000
      omega
  · left
    have hH₁ : H₁.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h1)
    have hRe := tripleUpperGood_add_high_even_le hP hsub
    change R.card + (parityPart H 0).card ≤ N / 6 + 3 at hRe
    have hO3 := tripleOddLow_add_high_odd_le hP hsub (i := 3) (Or.inr rfl)
    change O.card + H₃.card ≤ N / 12 + 10 at hO3
    have hpar := card_parity_parts H
    have hodd := card_modFour_one_add_three H
    change (parityPart H 0).card + (parityPart H 1).card = H.card at hpar
    change H₁.card + H₃.card = (parityPart H 1).card at hodd
    change N ≤ 12 * (Y.card + B.card) + 1000
    omega

lemma highFourSums_subset_interval {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) :
    highFourSums A N ⊆ Icc (4 * N / 3 + 1) (2 * N) := by
  intro z hz
  have hz' := mem_zmodFiber.mp hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
  have hxI := mem_Icc.mp (highThird_subset_interval hsub hx)
  have hyI := mem_Icc.mp (highThird_subset_interval hsub hy)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma fourAP_step_or_small {A : Finset ℕ} {N a d len : ℕ}
    (hsub : A ⊆ Icc 1 N) (hd : 0 < d)
    (hQ : natAP a d len ⊆ highFourSums A N)
    (hH : (highThird A N).card ≤ 2 * (len + 1)) :
    9 * (highThird A N).card ≤ N + 100 ∨ d = 4 ∨ d = 8 := by
  by_cases hlen : 2 ≤ len
  · have haQ : a ∈ highFourSums A N := hQ (mem_natAP.mpr ⟨0, by omega, by simp⟩)
    have hadQ : a + d ∈ highFourSums A N := by
      apply hQ
      exact mem_natAP.mpr ⟨1, by omega, by simp⟩
    have ha4 : 4 ∣ a := by
      have := (mem_zmodFiber.mp haQ).2
      rw [ZMod.natCast_eq_zero_iff] at this
      exact this
    have had4 : 4 ∣ a + d := by
      have := (mem_zmodFiber.mp hadQ).2
      rw [ZMod.natCast_eq_zero_iff] at this
      exact this
    have hd4 : 4 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero] at ha4 had4 ⊢
      rw [Nat.add_mod, ha4] at had4
      simpa using had4
    rcases hd4 with ⟨k, rfl⟩
    by_cases hk : 3 ≤ k
    · left
      have hlastQ : a + 4 * k * (len - 1) ∈ highFourSums A N := by
        apply hQ
        exact mem_natAP.mpr ⟨len - 1, by omega, by ring⟩
      have haI := mem_Icc.mp (highFourSums_subset_interval hsub haQ)
      have hlI := mem_Icc.mp (highFourSums_subset_interval hsub hlastQ)
      have hwidth : 12 * (len - 1) ≤ 2 * N - (4 * N / 3 + 1) := by
        have hmul : 12 * (len - 1) ≤ 4 * k * (len - 1) := by nlinarith
        omega
      omega
    · right
      have hkpos : 0 < k := by omega
      interval_cases k <;> simp_all
  · left
    omega

lemma exists_AP_residue_offset {a d r : ℕ} (ha : 4 ∣ a)
    (hd : d = 4 ∨ d = 8) (hr : r = 1 ∨ r = 2) :
    ∃ t < 3, (a + d * t) % 12 = (4 * r) % 12 := by
  obtain ⟨k, rfl⟩ := ha
  have hk : k % 3 < 3 := Nat.mod_lt _ (by omega)
  rcases hd with rfl | rfl <;> rcases hr with rfl | rfl <;>
    interval_cases hkm : k % 3 <;>
    first
    | exact ⟨0, by omega, by omega⟩
    | exact ⟨1, by omega, by omega⟩
    | exact ⟨2, by omega, by omega⟩

def apResidueSlice (a d len t : ℕ) : Finset ℕ :=
  (range (len / 3)).image fun j ↦ a + d * (t + 3 * j)

lemma apResidueSlice_card {a d len t : ℕ} (hd : 0 < d) :
    (apResidueSlice a d len t).card = len / 3 := by
  unfold apResidueSlice
  rw [card_image_iff.mpr]
  · simp
  · intro x hx y hy hxy
    have hmul : d * (t + 3 * x) = d * (t + 3 * y) := Nat.add_left_cancel hxy
    have := Nat.eq_of_mul_eq_mul_left hd hmul
    omega

lemma apResidueSlice_subset {a d len t : ℕ} (ht : t < 3) :
    apResidueSlice a d len t ⊆ natAP a d len := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  have hj' := mem_range.mp hj
  apply mem_natAP.mpr
  refine ⟨t + 3 * j, ?_, rfl⟩
  have hdiv : 3 * (len / 3) ≤ len := Nat.mul_div_le len 3
  omega

lemma apResidueSlice_mod {a d len t r : ℕ}
    (hd : d = 4 ∨ d = 8) (ht : (a + d * t) % 12 = (4 * r) % 12) :
    ∀ z ∈ apResidueSlice a d len t, z % 12 = (4 * r) % 12 := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  rcases hd with rfl | rfl
  · have heq : a + 4 * (t + 3 * j) = (a + 4 * t) + j * 12 := by ring
    rw [heq]
    exact (Nat.add_mul_mod_self_right (a + 4 * t) j 12).trans ht
  · have heq : a + 8 * (t + 3 * j) = (a + 8 * t) + (2 * j) * 12 := by ring
    rw [heq]
    exact (Nat.add_mul_mod_self_right (a + 8 * t) (2 * j) 12).trans ht

lemma upperThreeClass_pack_five_low {A U B : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hU : U ⊆ upperHalf A N) (hthree : ∀ x ∈ U, x % 3 = r % 3)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hBlow : ∀ b ∈ B, 5 * b ≤ 2 * N)
    (hdense : N / 6 + 6 ≤ 2 * U.card) :
    15 * B.card + 6 * U.card ≤ N + 30 := by
  let S := zmodFiber (U + U) (0 : ZMod 5)
  let e := 5 * (r % 3)
  let W := zmodFiber (Icc (N + 1) (2 * N)) (e : ZMod 15)
  have hUI : U ⊆ Icc (N / 2 + 1) N := hU.trans (upperHalf_subset_interval hsub)
  have hd := dense_residue_upperHalf_fixed_three (q := 5) (r := r)
    (by omega) (by norm_num) hUI hthree hdense (0 : ZMod 5)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 5 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 5⟩
  have hUH : ∀ x ∈ U, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_upperHalf.mp (hU hx)
    exact ⟨hx'.1, by omega⟩
  have hBW : B.image (fun b ↦ 5 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub (hB hb))
    have hb3 := hBthree b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, hBlow b hb⟩
    · apply (ZMod.natCast_eq_natCast_iff' (5 * b) e 15).mpr
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hSW : S ⊆ W := by
    intro z hz
    have hz' := mem_zmodFiber.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz'.1
    have hxI := mem_Icc.mp (hUI hx)
    have hyI := mem_Icc.mp (hUI hy)
    have hx3 := hthree x hx
    have hy3 := hthree y hy
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (x + y) e 15).mpr
      have h5 := (ZMod.natCast_eq_zero_iff (x + y) 5).mp hz'.2
      rw [Nat.dvd_iff_mod_eq_zero] at h5
      apply (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 5)).mp
      constructor <;> change _ % _ = _ % _ <;> omega
  have hp := packing (k := 5) (t := N / 2) (by omega) hP hBdiv hUH
    (filter_subset _ _) hBW hSW
  have hcap := mul_card_fixed_zmod_le (S := W) (L := N + 1) (U := 2 * N)
    (e : ZMod 15) (filter_subset _ _)
    (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change 2 * U.card ≤ 5 * (S.card + 1) at hd
  change B.card + S.card ≤ W.card at hp
  change 15 * W.card ≤ (2 * N + 15) - (N + 1) at hcap
  omega

lemma fourAP_high_pack {A B P : Finset ℕ} {N r : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hB : B ⊆ lowNonthreeImage A N)
    (hBthree : ∀ b ∈ B, b % 3 = r % 3)
    (hBhigh : ∀ b ∈ B, 2 * N < 5 * b)
    (hPsum : P ⊆ highFourSums A N)
    (hPres : ∀ z ∈ P, z % 12 = (4 * r) % 12) :
    18 * (B.card + P.card) ≤ N + 30 := by
  let W := zmodFiber (Icc (4 * N / 3 + 1) (2 * N)) ((4 * r : ℕ) : ZMod 12)
  have hBdiv : ∀ b ∈ B, ∃ a ∈ A, a ≤ N / 2 ∧ a ∣ 4 * b := by
    intro b hb
    obtain ⟨a, ha, haN, hab⟩ := halfImage_has_low_divisor
      (lowNonthreeImage_subset_halfImage A N (hB hb))
    exact ⟨a, ha, by omega, hab.mul_left 4⟩
  have hH : ∀ x ∈ highThird A N, x ∈ A ∧ N / 2 < x := by
    intro x hx
    have hx' := mem_highThird.mp hx
    exact ⟨hx'.1, by omega⟩
  have hBW : B.image (fun b ↦ 4 * b) ⊆ W := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    have hbI := mem_Icc.mp (lowNonthreeImage_subset_interval hP hsub (hB hb))
    have hb3 := hBthree b hb
    have hbhi := hBhigh b hb
    apply mem_zmodFiber.mpr
    constructor
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · apply (ZMod.natCast_eq_natCast_iff' (4 * b) (4 * r) 12).mpr
      calc
        (4 * b) % 12 = 4 * (b % 3) := Nat.mul_mod_mul_left 4 b 3
        _ = 4 * (r % 3) := by rw [hb3]
        _ = (4 * r) % 12 := (Nat.mul_mod_mul_left 4 r 3).symm
  have hPW : P ⊆ W := by
    intro z hz
    apply mem_zmodFiber.mpr
    refine ⟨highFourSums_subset_interval hsub (hPsum hz), ?_⟩
    apply (ZMod.natCast_eq_natCast_iff' z (4 * r) 12).mpr
    exact hPres z hz
  have hp := packing (k := 4) (t := N / 2) (by omega) hP hBdiv hH
    (hPsum.trans (filter_subset _ _)) hBW hPW
  have hcap := mul_card_fixed_zmod_le (S := W) (L := 4 * N / 3 + 1) (U := 2 * N)
    ((4 * r : ℕ) : ZMod 12)
    (filter_subset _ _) (fun z hz ↦ (mem_zmodFiber.mp hz).2)
  change B.card + P.card ≤ W.card at hp
  change 12 * W.card ≤ (2 * N + 12) - (4 * N / 3 + 1) at hcap
  omega

lemma improved_same_part_bound {A : Finset ℕ} {N r a d len : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hr : r = 1 ∨ r = 2)
    (hd : d = 4 ∨ d = 8) (hlen : 0 < len)
    (hQ : natAP a d len ⊆ highFourSums A N)
    (hH : (highThird A N).card ≤ 2 * (len + 1))
    (hdense : N / 6 + 6 ≤ 2 * (upperHalfResidue A N r).card) :
    90 * (lowNonthreeImagePart A N r).card +
        36 * (upperHalfResidue A N r).card +
        15 * (highThird A N).card ≤ 11 * N + 500 := by
  let U := upperHalfResidue A N r
  let C := lowNonthreeImagePart A N r
  let Cₗ := C.filter fun b ↦ 5 * b ≤ 2 * N
  let Cₕ := C.filter fun b ↦ 2 * N < 5 * b
  have hCpart : Cₗ.card + Cₕ.card = C.card := by
    have hdisj : Disjoint Cₗ Cₕ := by
      rw [Finset.disjoint_left]
      intro b hb hbh
      have hb' := (mem_filter.mp hb).2
      have hbh' := (mem_filter.mp hbh).2
      omega
    have hunion : Cₗ ∪ Cₕ = C := by
      ext b
      simp only [Cₗ, Cₕ, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hb
        exact (le_or_gt (5 * b) (2 * N)).imp (And.intro hb) (And.intro hb)
    rw [← card_union_of_disjoint hdisj, hunion]
  have hUsub : U ⊆ upperHalf A N := filter_subset _ _
  have hUthree : ∀ x ∈ U, x % 3 = r % 3 := by
    intro x hx
    exact (mem_upperHalfResidue.mp hx).2
  have hCsub : C ⊆ lowNonthreeImage A N := by
    intro b hb
    exact (mem_lowNonthreeImagePart.mp hb).1
  have hCthree : ∀ b ∈ C, b % 3 = r % 3 := by
    intro b hb
    exact (mem_lowNonthreeImagePart.mp hb).2
  have hpLow := upperThreeClass_pack_five_low hP hsub hUsub hUthree
    (B := Cₗ) ((filter_subset _ _).trans hCsub)
    (fun b hb ↦ hCthree b (mem_filter.mp hb).1)
    (fun b hb ↦ (mem_filter.mp hb).2) hdense
  change 15 * Cₗ.card + 6 * U.card ≤ N + 30 at hpLow
  have haQ : a ∈ highFourSums A N := hQ (mem_natAP.mpr ⟨0, hlen, by simp⟩)
  have ha4 : 4 ∣ a := by
    have haZ := (mem_zmodFiber.mp haQ).2
    rw [ZMod.natCast_eq_zero_iff] at haZ
    exact haZ
  obtain ⟨t, ht, htmod⟩ := exists_AP_residue_offset ha4 hd hr
  let P := apResidueSlice a d len t
  have hPcard := apResidueSlice_card (a := a) (d := d) (len := len) (t := t)
    (by rcases hd with rfl | rfl <;> omega)
  change P.card = len / 3 at hPcard
  have hPsub : P ⊆ highFourSums A N :=
    (apResidueSlice_subset ht).trans hQ
  have hPres : ∀ z ∈ P, z % 12 = (4 * r) % 12 :=
    apResidueSlice_mod hd htmod
  have hpHigh := fourAP_high_pack hP hsub
    (B := Cₕ) (P := P) ((filter_subset _ _).trans hCsub)
    (fun b hb ↦ hCthree b (mem_filter.mp hb).1)
    (fun b hb ↦ (mem_filter.mp hb).2) hPsub hPres
  change 18 * (Cₕ.card + P.card) ≤ N + 30 at hpHigh
  change 90 * C.card + 36 * U.card + 15 * (highThird A N).card ≤ 11 * N + 500
  have hlenDiv : len ≤ 3 * (len / 3) + 2 := by omega
  omega

/-! The three numerical closures used in the hard nonzero-growth branch are
kept separate from the combinatorial context.  Besides making the constants
auditable, this prevents the Presburger procedure from having to normalize
several dozen irrelevant set-theoretic hypotheses. -/

lemma hard_finish_standard_strong {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hh : 6 * h < n + 144)
    (hr : n ≤ 12 * (y + b) + 1000)
    (hm : 60 * a + 32 * y + 54 * b ≤ 60 * d + 11 * n + 500 + 22 * h) :
    3 * a ≤ n + c := by
  omega

lemma hard_finish_standard_small {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hr : n ≤ 24 * (y + b) + 2000)
    (hh : 9 * h ≤ n + 100)
    (hm : 60 * a + 32 * y + 54 * b ≤ 60 * d + 11 * n + 500 + 22 * h) :
    3 * a ≤ n + c := by
  omega

lemma hard_finish_improved {a y b d h n c : ℕ}
    (hn : 1000000000 ≤ n)
    (hd : 3 * d ≤ n / 3 + c)
    (hh : 6 * h < n + 144)
    (hr : n ≤ 24 * (y + b) + 2000)
    (hm : 180 * a + 96 * y + 162 * b ≤
      180 * d + 37 * n + 2000 + 36 * h) :
    3 * a ≤ n + c := by
  omega

lemma caseThree_nonzero_growth_hard {A : Finset ℕ} {N C : ℕ}
    (hP : IsForbiddenTripleFree A) (hsub : A ⊆ Icc 1 N)
    (hN : 1000000000 ≤ N)
    (hC : 2 ≤ C)
    (htail : (N + 1) / 2 < 3 * (upperHalf A N).card)
    (hcase3 : 6 * (highThird A N).card < N + 144)
    (hdom : 2 * (upperHalf A N).card ≤
      3 * ((upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card))
    (hgrowth :
      (upperHalfResidue A N 1).card + (upperHalfResidue A N 2).card +
        min (upperHalfResidue A N 1).card (upperHalfResidue A N 2).card ≤
          (upperHalfResidue A N 1 + upperHalfResidue A N 2).card + 3)
    (hind : CoarseBound C (N / 3)
      ((divisibleInitial A N 3 1).image fun x ↦ x / 3))
    (hfail : ¬ CoarseBound C N A) : False := by
  let V := upperHalf A N
  let V₁ := upperHalfResidue A N 1
  let V₂ := upperHalfResidue A N 2
  let H := highThird A N
  let Y := middleSixth A N
  let B := tripleBad A N
  let D := divisibleInitial A N 3 1
  let C₁ := lowNonthreeImagePart A N 1
  let C₂ := lowNonthreeImagePart A N 2
  let R := zmodFiber (V + V) (0 : ZMod 3)
  let Q := thirdSumQuotient A N
  have hlarge : N + 2 < 3 * A.card := by
    by_contra hn
    apply hfail
    change 3 * A.card ≤ N + C
    omega
  have h12 : V₁ + V₂ ⊆ R := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    have hx' := mem_upperHalfResidue.mp hx
    have hy' := mem_upperHalfResidue.mp hy
    apply mem_zmodFiber.mpr
    refine ⟨Finset.add_mem_add hx'.1 hy'.1, ?_⟩
    have hxZ : (x : ZMod 3) = 1 := by
      apply (ZMod.natCast_eq_natCast_iff x 1 3).mpr
      change x % 3 = 1 % 3
      simpa using hx'.2
    have hyZ : (y : ZMod 3) = 2 := by
      apply (ZMod.natCast_eq_natCast_iff y 2 3).mpr
      change y % 3 = 2 % 3
      simpa using hy'.2
    push_cast
    rw [hxZ, hyZ]
    decide
  have hsumQ : (V₁ + V₂).card ≤ Q.card := by
    have hc := card_le_card h12
    have hQc := thirdSumQuotient_card A N
    change Q.card = R.card at hQc
    omega
  have hrel : V₁.card + V₂.card + min V₁.card V₂.card + B.card ≤ H.card + 3 := by
    by_contra hn
    have hp := caseThree_enhanced_packing hP hsub
    have hcap : 3 * (Icc (N / 3 + 1) (2 * N / 3)).card ≤ N + 2 := by
      simp
      omega
    have hAH := card_low_add_card_high A N
    change (lowTwoThirds A N).card + H.card = A.card at hAH
    change (lowTwoThirds A N).card + B.card + Q.card ≤
      (Icc (N / 3 + 1) (2 * N / 3)).card at hp
    change V₁.card + V₂.card + min V₁.card V₂.card ≤
      (V₁ + V₂).card + 3 at hgrowth
    have hQB : H.card + 1 ≤ Q.card + B.card := by omega
    apply hfail
    change 3 * A.card ≤ N + C
    omega
  have hYH := card_middleSixth_add_highThird hsub
  change Y.card + H.card = V.card at hYH
  change 2 * V.card ≤ 3 * (V₁.card + V₂.card) at hdom
  change (N + 1) / 2 < 3 * V.card at htail
  change 6 * H.card < N + 144 at hcase3
  have hweak := triple_bad_reserve hP hsub hcase3 hlarge
  change N ≤ 24 * (Y.card + B.card) + 2000 at hweak
  have hbonus :
      N ≤ 12 * (Y.card + B.card) + 1000 ∨
      9 * H.card ≤ N + 100 ∨
      ∃ a d len, 0 < len ∧ (d = 4 ∨ d = 8) ∧
        natAP a d len ⊆ highFourSums A N ∧ H.card ≤ 2 * (len + 1) := by
    rcases strong_reserve_or_fourAP hP hsub hlarge with hs | hp
    · exact Or.inl hs
    · obtain ⟨a, d, len, hd, hQ, hH⟩ := hp
      change H.card ≤ 2 * (len + 1) at hH
      by_cases hlen : 0 < len
      · rcases fourAP_step_or_small hsub hd hQ hH with hsmall | hstep
        · exact Or.inr (Or.inl hsmall)
        · exact Or.inr (Or.inr ⟨a, d, len, hlen, hstep, hQ, hH⟩)
      · right
        left
        have : len = 0 := by omega
        omega
  have hAcover := nonzero_decomposition hP hsub
  change A.card ≤ D.card + C₁.card + C₂.card + V₁.card + V₂.card at hAcover
  have hDbound := divisibleInitial_card_bound_coarse (k := 3) (ell := 1)
    (C := C) (by omega) (by omega) hP hsub hind
  change 3 * D.card ≤ N / 3 + C at hDbound
  have hC₁sub : C₁ ⊆ lowNonthreeImage A N := by
    intro z hz
    exact (mem_lowNonthreeImagePart.mp hz).1
  have hC₂sub : C₂ ⊆ lowNonthreeImage A N := by
    intro z hz
    exact (mem_lowNonthreeImagePart.mp hz).1
  have hC₁res : ∀ z ∈ C₁, z % 3 = 1 := by
    intro z hz
    simpa using (mem_lowNonthreeImagePart.mp hz).2
  have hC₂res : ∀ z ∈ C₂, z % 3 = 2 := by
    intro z hz
    simpa using (mem_lowNonthreeImagePart.mp hz).2
  rcases le_total V₂.card V₁.card with h21 | h12c
  · have hmin : min V₁.card V₂.card = V₂.card := min_eq_right h21
    have hlower : V.card + 3 * Y.card + 3 * B.card ≤ 3 * V₁.card + 9 := by
      rw [hmin] at hrel
      omega
    have hdense : N / 6 + 6 ≤ 2 * V₁.card := by omega
    have hdense4 : N / 6 + 5 ≤ 2 * V₁.card := by omega
    have hVsub : V₁ ⊆ V := filter_subset _ _
    have hVres : ∀ x ∈ V₁, x % 3 = 1 := by
      intro x hx
      simpa using (mem_upperHalfResidue.mp hx).2
    have hp4 := upperThreeClass_pack_four (r := 1) hP hsub hVsub hVres
      (B := C₂) hC₂sub hC₂res hdense4
    have hp5 := upperThreeClass_pack_five (r := 1) hP hsub hVsub hVres
      (B := C₁) hC₁sub hC₁res hdense
    change 12 * C₂.card + 6 * V₁.card ≤ N + 24 at hp4
    change 10 * C₁.card + 4 * V₁.card ≤ N + 30 at hp5
    rcases hbonus with hstrong | hbonus
    · have hmaster :
          60 * A.card + 32 * Y.card + 54 * B.card ≤
            60 * D.card + 11 * N + 500 + 22 * H.card := by omega
      apply hfail
      exact hard_finish_standard_strong hN hDbound hcase3 hstrong hmaster
    · rcases hbonus with hsmall | ⟨a, d, len, hlen, hd, hQ, hH⟩
      · have hmaster :
            60 * A.card + 32 * Y.card + 54 * B.card ≤
              60 * D.card + 11 * N + 500 + 22 * H.card := by omega
        apply hfail
        exact hard_finish_standard_small hN hDbound hweak hsmall hmaster
      · have himp := improved_same_part_bound hP hsub (r := 1)
          (a := a) (d := d) (len := len) (Or.inl rfl) hd hlen hQ hH hdense
        change 90 * C₁.card + 36 * V₁.card + 15 * H.card ≤ 11 * N + 500 at himp
        have hmaster :
            180 * A.card + 96 * Y.card + 162 * B.card ≤
              180 * D.card + 37 * N + 2000 + 36 * H.card := by omega
        apply hfail
        exact hard_finish_improved hN hDbound hcase3 hweak hmaster
  · have hmin : min V₁.card V₂.card = V₁.card := min_eq_left h12c
    have hlower : V.card + 3 * Y.card + 3 * B.card ≤ 3 * V₂.card + 9 := by
      rw [hmin] at hrel
      omega
    have hdense : N / 6 + 6 ≤ 2 * V₂.card := by omega
    have hdense4 : N / 6 + 5 ≤ 2 * V₂.card := by omega
    have hVsub : V₂ ⊆ V := filter_subset _ _
    have hVres : ∀ x ∈ V₂, x % 3 = 2 := by
      intro x hx
      simpa using (mem_upperHalfResidue.mp hx).2
    have hp4 := upperThreeClass_pack_four (r := 2) hP hsub hVsub hVres
      (B := C₁) hC₁sub hC₁res hdense4
    have hp5 := upperThreeClass_pack_five (r := 2) hP hsub hVsub hVres
      (B := C₂) hC₂sub hC₂res hdense
    change 12 * C₁.card + 6 * V₂.card ≤ N + 24 at hp4
    change 10 * C₂.card + 4 * V₂.card ≤ N + 30 at hp5
    rcases hbonus with hstrong | hbonus
    · have hmaster :
          60 * A.card + 32 * Y.card + 54 * B.card ≤
            60 * D.card + 11 * N + 500 + 22 * H.card := by omega
      apply hfail
      exact hard_finish_standard_strong hN hDbound hcase3 hstrong hmaster
    · rcases hbonus with hsmall | ⟨a, d, len, hlen, hd, hQ, hH⟩
      · have hmaster :
            60 * A.card + 32 * Y.card + 54 * B.card ≤
              60 * D.card + 11 * N + 500 + 22 * H.card := by omega
        apply hfail
        exact hard_finish_standard_small hN hDbound hweak hsmall hmaster
      · have himp := improved_same_part_bound hP hsub (r := 2)
          (a := a) (d := d) (len := len) (Or.inr rfl) hd hlen hQ hH hdense
        change 90 * C₂.card + 36 * V₂.card + 15 * H.card ≤ 11 * N + 500 at himp
        have hmaster :
            180 * A.card + 96 * Y.card + 162 * B.card ≤
              180 * D.card + 37 * N + 2000 + 36 * H.card := by omega
        apply hfail
        exact hard_finish_improved hN hDbound hcase3 hweak hmaster

end Bedert

/-! The remaining sections implement the quantitative form of Bedert's
induction. -/

open Bedert

/-- Bedert's quantitative finite theorem, in the weaker form needed here. -/
private theorem bedert_bound : ∃ C : ℕ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N,
    IsForbiddenTripleFree A → 3 * A.card ≤ N + C := by
  refine ⟨2000000000, ?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro A hsub hP
      change CoarseBound 2000000000 N A
      by_cases hsmallN : N < 1000000000
      · have hcard := card_le_card hsub
        simp at hcard
        change 3 * A.card ≤ N + 2000000000
        omega
      have hN : 1000000000 ≤ N := by omega
      have hN1000 : 1000 ≤ N := by omega
      by_contra hfail

      have hhalfPos : 0 < (N + 1) / 2 := by omega
      have hhalfLe : (N + 1) / 2 ≤ N := by omega
      have hhalfLt : N - (N + 1) / 2 < N := by omega
      have hindInitial : CoarseBound 2000000000
          (N - (N + 1) / 2) (initialPart A N ((N + 1) / 2)) := by
        apply ih (N - (N + 1) / 2) hhalfLt
        · exact initialPart_subset_Icc hsub
        · exact initialPart_property hP
      have htail := terminal_dense_of_not_coarseBound
        hhalfPos hhalfLe hfail hindInitial
      rw [terminalPart_half_eq_upperHalf hsub] at htail

      have hind3 : CoarseBound 2000000000 (N / 3)
          ((divisibleInitial A N 3 1).image fun x ↦ x / 3) := by
        apply ih (N / 3) (by omega)
        · simpa using image_div_divisibleInitial_subset
            (A := A) (N := N) (k := 3) (ell := 1)
            (by omega) (by omega) hsub
        · exact image_div_divisibleInitial_property
            (A := A) (N := N) (k := 3) (ell := 1) (by omega) hP
      have hind6 : CoarseBound 2000000000 (N / 6)
          ((divisibleInitial A N 3 2).image fun x ↦ x / 3) := by
        apply ih (N / 6) (by omega)
        · simpa using image_div_divisibleInitial_subset
            (A := A) (N := N) (k := 3) (ell := 2)
            (by omega) (by omega) hsub
        · exact image_div_divisibleInitial_property
            (A := A) (N := N) (k := 3) (ell := 2) (by omega) hP

      by_cases hcase1 : 2 * N + 12 ≤ 9 * (highThird A N).card
      · have hb := caseOne hP hsub hcase1
        apply hfail
        change 3 * A.card ≤ N + 2000000000
        omega
      have hcase1' : 9 * (highThird A N).card < 2 * N + 12 := by omega
      by_cases hcase2 : N + 144 ≤ 6 * (highThird A N).card
      · have hb := caseTwo hP hsub hcase2 hcase1'
        apply hfail
        change 3 * A.card ≤ N + 2000000000
        omega
      have hcase3 : 6 * (highThird A N).card < N + 144 := by omega

      by_cases hzero : (upperHalf A N).card ≤
          3 * (upperHalfResidue A N 0).card
      · have hV0card : 0 < (upperHalfResidue A N 0).card := by
          change (N + 1) / 2 < 3 * (upperHalf A N).card at htail
          omega
        have hV0 : (upperHalfResidue A N 0).Nonempty := Finset.card_pos.mp hV0card
        rcases bgAlternative_self (upperHalfResidue A N 0) with hgrowth | hstruct
        · have hgrowth' : 3 * (upperHalfResidue A N 0).card ≤
              (upperHalfResidue A N 0 + upperHalfResidue A N 0).card + 3 := by
            omega
          have hb := caseThree_zero_growth_coarse hP hsub hzero hgrowth'
          apply hfail
          change 3 * A.card ≤ N + 2000000000
          omega
        · obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
          have hQ' : natAP a d (2 * (upperHalfResidue A N 0).card - 1) ⊆
              upperHalfResidue A N 0 + upperHalfResidue A N 0 := by
            simpa [two_mul] using hQ
          have ha3 := zero_AP_start_dvd_three hV0 hQ'
          rcases zero_structural_step hsub hN1000 hV0 htail hzero hd hQ' hres with
            rfl | rfl | rfl
          · have hb := caseThree_zero_step_three
              hP hsub hV0 htail hzero hcase3 ha3 hQ'
            apply hfail
            change 3 * A.card ≤ N + 2000000000
            omega
          · have hb := caseThree_zero_step_six
              hP hsub hV0 hzero ha3 hQ' hres
            apply hfail
            change 3 * A.card ≤ N + 2000000000
            omega
          · apply hfail
            exact caseThree_zero_step_nine
              hP hsub hN1000 hV0 htail hzero ha3 hQ' hres hind6
      · have hparts := card_upperHalf_residues A N
        have hdom : 2 * (upperHalf A N).card ≤
            3 * ((upperHalfResidue A N 1).card +
              (upperHalfResidue A N 2).card) := by
          omega
        by_cases hV1 : (upperHalfResidue A N 1).Nonempty
        · by_cases hV2 : (upperHalfResidue A N 2).Nonempty
          · by_cases hmid : (highThird A N).card + 3 ≤
                2 * (middleSixth A N).card
            · have hb := caseThree_of_large_middle hP hsub hV1 hV2 hmid
              apply hfail
              change 3 * A.card ≤ N + 2000000000
              omega
            · rcases bgAlternative_of_nonempty hV1 hV2 with hgrowth | hstruct
              · by_cases hcover : (highThird A N).card + 3 ≤
                    (upperHalfResidue A N 1).card +
                      (upperHalfResidue A N 2).card +
                        min (upperHalfResidue A N 1).card
                          (upperHalfResidue A N 2).card
                · have hb := caseThree_nonzero_growth hP hsub hgrowth hcover
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · exact caseThree_nonzero_growth_hard hP hsub hN
                    (by omega) htail hcase3 hdom hgrowth hind3 hfail
              · obtain ⟨a, d, hd, hQ, hres⟩ := hstruct
                have ha3 := nonzero_AP_start_dvd_three hV1 hV2 hQ
                rcases nonzero_structural_step hsub hN1000 hV1 hV2 htail hdom
                    hd hQ hres with rfl | rfl | rfl
                · have hb := caseThree_nonzero_step_three
                    hP hsub hV1 hV2 htail hdom hcase3 ha3 hQ
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · have hb := caseThree_nonzero_step_six
                    hP hsub hV1 hV2 hdom ha3 hQ hres
                  apply hfail
                  change 3 * A.card ≤ N + 2000000000
                  omega
                · by_cases hat : (a / 3) % 3 = 0
                  · have haeq : 3 * (a / 3) = a := Nat.mul_div_cancel' ha3
                    have ha9 : a % 9 = 0 := by omega
                    have hb := caseThree_nonzero_step_nine_zero
                      hP hsub hV1 hV2 htail hdom ha9 hQ hres
                    apply hfail
                    change 3 * A.card ≤ N + 2000000000
                    omega
                  · apply hfail
                    exact caseThree_nonzero_step_nine_nonzero
                      hP hsub hN1000 hV1 hV2 htail hdom ha3 hat hQ hres hind6
          · apply hfail
            exact caseThree_nonzero_empty
              hP hsub hN1000 htail hdom hV2 hind3
        · apply hfail
          exact caseThree_nonzero_empty_one
            hP hsub hN1000 htail hdom hV1 hind3

/-- If `A ⊆ {1, ..., N}` has no `a,b,c ∈ A` such that `a ∣ b+c` and
`a < min b c`, then `|A| ≤ N/3 + O(1)`. -/
theorem erdos_13 : ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N, IsForbiddenTripleFree A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  obtain ⟨C, hC⟩ := bedert_bound
  refine ⟨(C : ℝ) / 3, ?_⟩
  intro N A hsub hP
  have h := hC N A hsub hP
  have h' : (3 : ℝ) * (A.card : ℝ) ≤ (N : ℝ) + C := by
    exact_mod_cast h
  nlinarith

end

#print axioms erdos_13
-- 'Erdos13.erdos_13' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos13
