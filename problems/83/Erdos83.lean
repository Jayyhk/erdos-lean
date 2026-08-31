import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos83

/-
# Problem Description

Erdős Problem 83 ($500), conjectured by Erdős, Ko and Rado. Suppose `𝓕` is a family of
subsets of `[4n]` with `|A| = 2n` for all `A ∈ 𝓕`, and `|A ∩ B| ≥ 2` for every `A, B ∈ 𝓕`.
Then

  `|𝓕| ≤ (C(4n, 2n) - C(2n, n) ^ 2) / 2`.

`erdos_83` proves this. It was established by Ahlswede and Khachatrian, as a case of their
general theorem, and the bound is best possible — take all `2n`-subsets of `[4n]` containing
at least `n + 1` elements of `[2n]`.

`Uniform k 𝓕` is `∀ A ∈ 𝓕, A.card = k` and `TwoIntersecting 𝓕` is `∀ A B ∈ 𝓕,
2 ≤ (A ∩ B).card`, over not-necessarily-distinct `A` and `B` as the statement intends.

The right-hand side uses natural subtraction and division, both of which are exact here:
`C(4n,2n) ≥ C(2n,n)^2` because the latter is one term of the Vandermonde expansion
`C(4n,2n) = ∑ₖ C(2n,k)^2`, and the difference is even because the remaining terms pair up
under `k ↦ 2n - k`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/Compression.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Left compressions for finite uniform set systems

This file supplies the elementary compression machinery used in the proof of
Erdős Problem 83.  Families are represented by finite sets of finite subsets
of `Fin N`.
-/

open scoped BigOperators
open Finset



variable {N k : ℕ}

/-- Every member of `𝒻` has cardinality `k`. -/
def Uniform (k : ℕ) (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒻 → A.card = k

/-- Any two (not necessarily distinct) members meet in at least two points. -/
def TwoIntersecting (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A B⦄, A ∈ 𝒻 → B ∈ 𝒻 → 2 ≤ (A ∩ B).card

/-- Apply the transposition `(i j)` to every element of a finite set. -/
def setTranspose (i j : Fin N) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map (Equiv.swap i j).toEmbedding

@[simp]
theorem mem_setTranspose {i j x : Fin N} {A : Finset (Fin N)} :
    x ∈ setTranspose i j A ↔ Equiv.swap i j x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, hxy⟩
    subst x
    simpa using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨Equiv.swap i j x, hx, by simp⟩

@[simp]
theorem card_setTranspose (i j : Fin N) (A : Finset (Fin N)) :
    (setTranspose i j A).card = A.card := by
  simp [setTranspose]

@[simp]
theorem setTranspose_involutive (i j : Fin N) (A : Finset (Fin N)) :
    setTranspose i j (setTranspose i j A) = A := by
  classical
  ext x
  simp

@[simp]
theorem setTranspose_inter (i j : Fin N) (A B : Finset (Fin N)) :
    setTranspose i j (A ∩ B) = setTranspose i j A ∩ setTranspose i j B := by
  classical
  ext x
  simp

/-- The singleton left shift `j → i`: replace `j` by `i` when possible. -/
def singletonLeftShift (i j : Fin N) (A : Finset (Fin N)) : Finset (Fin N) :=
  if j ∈ A ∧ i ∉ A then setTranspose i j A else A

theorem singletonLeftShift_eq_transpose {i j : Fin N} {A : Finset (Fin N)}
    (h : j ∈ A ∧ i ∉ A) :
    singletonLeftShift i j A = setTranspose i j A := by
  simp [singletonLeftShift, h]

theorem singletonLeftShift_eq_self {i j : Fin N} {A : Finset (Fin N)}
    (h : ¬ (j ∈ A ∧ i ∉ A)) : singletonLeftShift i j A = A := by
  simp [singletonLeftShift, h]

@[simp]
theorem card_singletonLeftShift (i j : Fin N) (A : Finset (Fin N)) :
    (singletonLeftShift i j A).card = A.card := by
  classical
  by_cases h : j ∈ A ∧ i ∉ A
  · simp [singletonLeftShift, h]
  · simp [singletonLeftShift, h]

theorem singletonLeftShift_ne_self_iff {i j : Fin N} {A : Finset (Fin N)} :
    singletonLeftShift i j A ≠ A ↔ j ∈ A ∧ i ∉ A := by
  classical
  constructor
  · intro h
    by_contra hc
    exact h (singletonLeftShift_eq_self hc)
  · rintro hij hEq
    have hj : j ∈ setTranspose i j A := by
      rw [← singletonLeftShift_eq_transpose hij, hEq]
      exact hij.1
    have hi : i ∈ A := by
      simpa using hj
    exact hij.2 hi

/-- The member map underlying the cardinality-preserving family shift.

If the shifted set is already in the family, the original member is retained;
otherwise it is replaced by its singleton left shift.
-/
def familyShiftMember (𝒻 : Finset (Finset (Fin N))) (i j : Fin N)
    (A : Finset (Fin N)) : Finset (Fin N) :=
  if singletonLeftShift i j A ∈ 𝒻 then A else singletonLeftShift i j A

/-- Collision-protected singleton left shift of a finite family. -/
def familyShift (i j : Fin N) (𝒻 : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  𝒻.image (familyShiftMember 𝒻 i j)

theorem familyShiftMember_injective_on (𝒻 : Finset (Finset (Fin N))) (i j : Fin N) :
    Set.InjOn (familyShiftMember 𝒻 i j) 𝒻 := by
  classical
  intro A hA B hB hEq
  by_cases hAs : singletonLeftShift i j A ∈ 𝒻
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using hEq
    · have : A = singletonLeftShift i j B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      exact (hBs (this ▸ hA)).elim
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · have : singletonLeftShift i j A = B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      exact (hAs (this.symm ▸ hB)).elim
    · have hsEq : singletonLeftShift i j A = singletonLeftShift i j B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      have hAne : singletonLeftShift i j A ≠ A := by
        intro h
        exact hAs (h.symm ▸ hA)
      have hBne : singletonLeftShift i j B ≠ B := by
        intro h
        exact hBs (h.symm ▸ hB)
      have hAc := singletonLeftShift_ne_self_iff.mp hAne
      have hBc := singletonLeftShift_ne_self_iff.mp hBne
      rw [singletonLeftShift_eq_transpose hAc,
        singletonLeftShift_eq_transpose hBc] at hsEq
      have := congrArg (setTranspose i j) hsEq
      simpa using this

@[simp]
theorem card_familyShift (i j : Fin N) (𝒻 : Finset (Finset (Fin N))) :
    (familyShift i j 𝒻).card = 𝒻.card := by
  classical
  exact Finset.card_image_iff.mpr (familyShiftMember_injective_on 𝒻 i j)

theorem Uniform.familyShift {k : ℕ} {𝒻 : Finset (Finset (Fin N))}
    (h : Uniform k 𝒻) (i j : Fin N) : Uniform k (familyShift i j 𝒻) := by
  classical
  intro C hC
  rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
  by_cases hs : singletonLeftShift i j A ∈ 𝒻
  · simpa [familyShiftMember, hs] using h hA
  · simpa [familyShiftMember, hs] using h hA

theorem card_inter_transpose_cross (i j : Fin N) (A B : Finset (Fin N)) :
    (setTranspose i j A ∩ B).card = (A ∩ setTranspose i j B).card := by
  classical
  rw [← card_setTranspose i j (setTranspose i j A ∩ B), setTranspose_inter]
  simp

theorem inter_subset_inter_transpose_right {i j : Fin N} {A B : Finset (Fin N)}
    (hA : j ∈ A ∧ i ∉ A) (hB : ¬ (j ∈ B ∧ i ∉ B)) :
    A ∩ B ⊆ A ∩ setTranspose i j B := by
  classical
  intro x hx
  have hxA : x ∈ A := Finset.mem_inter.mp hx |>.1
  have hxB : x ∈ B := Finset.mem_inter.mp hx |>.2
  refine Finset.mem_inter.mpr ⟨hxA, ?_⟩
  rw [mem_setTranspose]
  by_cases hxi : x = i
  · subst x
    exact (hA.2 hxA).elim
  by_cases hxj : x = j
  · subst x
    have hiB : i ∈ B := by
      by_contra hi
      exact hB ⟨hxB, hi⟩
    simpa using hiB
  · simpa [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hxB

private theorem twoInter_of_left_moved
    {𝒻 : Finset (Finset (Fin N))} (h : TwoIntersecting 𝒻)
    {i j : Fin N} {A B : Finset (Fin N)}
    (hA : A ∈ 𝒻) (hB : B ∈ 𝒻)
    (hAs : singletonLeftShift i j A ∉ 𝒻)
    (hBs : singletonLeftShift i j B ∈ 𝒻) :
    2 ≤ (singletonLeftShift i j A ∩ B).card := by
  classical
  have hAne : singletonLeftShift i j A ≠ A := by
    intro hEq
    exact hAs (hEq.symm ▸ hA)
  have hAc : j ∈ A ∧ i ∉ A := singletonLeftShift_ne_self_iff.mp hAne
  rw [singletonLeftShift_eq_transpose hAc]
  by_cases hBc : j ∈ B ∧ i ∉ B
  · have hBt : setTranspose i j B ∈ 𝒻 := by
      simpa [singletonLeftShift_eq_transpose hBc] using hBs
    rw [card_inter_transpose_cross]
    exact h hA hBt
  · rw [card_inter_transpose_cross]
    exact le_trans (h hA hB) (Finset.card_le_card (inter_subset_inter_transpose_right hAc hBc))

theorem TwoIntersecting.familyShift {𝒻 : Finset (Finset (Fin N))}
    (h : TwoIntersecting 𝒻) (i j : Fin N) : TwoIntersecting (familyShift i j 𝒻) := by
  classical
  intro C D hC hD
  rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
  rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
  by_cases hAs : singletonLeftShift i j A ∈ 𝒻
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using h hA hB
    · have hm := twoInter_of_left_moved h hB hA hBs hAs
      simpa [familyShiftMember, hAs, hBs, Finset.inter_comm] using hm
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using
        (twoInter_of_left_moved h hA hB hAs hBs)
    · have hAne : singletonLeftShift i j A ≠ A := by
        intro hEq
        exact hAs (hEq.symm ▸ hA)
      have hBne : singletonLeftShift i j B ≠ B := by
        intro hEq
        exact hBs (hEq.symm ▸ hB)
      have hAc := singletonLeftShift_ne_self_iff.mp hAne
      have hBc := singletonLeftShift_ne_self_iff.mp hBne
      simp only [familyShiftMember, hAs, hBs, if_false]
      rw [singletonLeftShift_eq_transpose hAc,
        singletonLeftShift_eq_transpose hBc]
      have hc := h hA hB
      rw [← card_setTranspose i j (A ∩ B), setTranspose_inter] at hc
      exact hc

/-- Sum of the numeric labels in a set. -/
def setWeight (A : Finset (Fin N)) : ℕ :=
  ∑ x ∈ A, x.val

/-- Total weight of all members of a family. -/
def familyWeight (𝒻 : Finset (Finset (Fin N))) : ℕ :=
  ∑ A ∈ 𝒻, setWeight A

theorem setTranspose_eq_insert_erase {i j : Fin N} {A : Finset (Fin N)}
    (h : j ∈ A ∧ i ∉ A) : setTranspose i j A = insert i (A.erase j) := by
  classical
  ext x
  rw [mem_setTranspose]
  by_cases hxi : x = i
  · subst x
    simp [h.1, h.2]
  by_cases hxj : x = j
  · subst x
    simp [h.2, hxi]
  · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

theorem setWeight_singletonLeftShift_lt {i j : Fin N} {A : Finset (Fin N)}
    (hij : i < j) (hne : singletonLeftShift i j A ≠ A) :
    setWeight (singletonLeftShift i j A) < setWeight A := by
  classical
  have hc : j ∈ A ∧ i ∉ A := singletonLeftShift_ne_self_iff.mp hne
  have hiErase : i ∉ A.erase j := by simp [hc.2]
  have hjErase : j ∉ A.erase j := by simp
  rw [singletonLeftShift_eq_transpose hc, setTranspose_eq_insert_erase hc]
  have hshiftWeight :
      setWeight (insert i (A.erase j)) = i.val + setWeight (A.erase j) := by
    simp [setWeight, hiErase]
  have hAWeight : setWeight A = j.val + setWeight (A.erase j) := by
    calc
      setWeight A = setWeight (insert j (A.erase j)) := by
        rw [Finset.insert_erase hc.1]
      _ = j.val + setWeight (A.erase j) := by
        simp [setWeight, hjErase]
  rw [hshiftWeight, hAWeight]
  exact Nat.add_lt_add_right (show i.val < j.val from hij) (setWeight (A.erase j))

private theorem familyShiftMember_weight_le
    (𝒻 : Finset (Finset (Fin N))) {i j : Fin N} (hij : i < j)
    (A : Finset (Fin N)) (hA : A ∈ 𝒻) :
    setWeight (familyShiftMember 𝒻 i j A) ≤ setWeight A := by
  classical
  by_cases hs : singletonLeftShift i j A ∈ 𝒻
  · simp [familyShiftMember, hs]
  · simp only [familyShiftMember, hs, if_false]
    have hne : singletonLeftShift i j A ≠ A := by
      intro hEq
      exact hs (hEq.symm ▸ hA)
    exact (setWeight_singletonLeftShift_lt hij hne).le

theorem familyWeight_familyShift_lt
    {𝒻 : Finset (Finset (Fin N))} {i j : Fin N}
    (hij : i < j) (hne : familyShift i j 𝒻 ≠ 𝒻) :
    familyWeight (familyShift i j 𝒻) < familyWeight 𝒻 := by
  classical
  have hmove : ∃ A ∈ 𝒻, familyShiftMember 𝒻 i j A ≠ A := by
    by_contra h
    push_neg at h
    apply hne
    ext A
    simp only [familyShift, mem_image]
    constructor
    · rintro ⟨B, hB, rfl⟩
      simpa [h B hB] using hB
    · intro hA
      exact ⟨A, hA, h A hA⟩
  rcases hmove with ⟨A, hA, hAmove⟩
  have hinj := familyShiftMember_injective_on 𝒻 i j
  rw [familyWeight, familyShift, Finset.sum_image hinj]
  apply Finset.sum_lt_sum
  · intro B hB
    exact familyShiftMember_weight_le 𝒻 hij B hB
  · refine ⟨A, hA, ?_⟩
    by_cases hs : singletonLeftShift i j A ∈ 𝒻
    · simp [familyShiftMember, hs] at hAmove
    · simp only [familyShiftMember, hs, if_false] at hAmove ⊢
      exact setWeight_singletonLeftShift_lt hij hAmove

/-- A family fixed by every singleton shift from a larger to a smaller label. -/
def LeftCompressed (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ (i j : Fin N), i < j → familyShift i j 𝒻 = 𝒻

/-- In a left-compressed family, every available left shift of a member is
again a member. -/
theorem LeftCompressed.shifted_mem {𝒻 : Finset (Finset (Fin N))}
    (h : LeftCompressed 𝒻) {i j : Fin N} (hij : i < j)
    {A : Finset (Fin N)} (hA : A ∈ 𝒻) (hj : j ∈ A) (hi : i ∉ A) :
    singletonLeftShift i j A ∈ 𝒻 := by
  classical
  by_contra hs
  have hm : singletonLeftShift i j A ∈ familyShift i j 𝒻 := by
    apply Finset.mem_image.mpr
    refine ⟨A, hA, ?_⟩
    simp [familyShiftMember, hs]
  rw [h i j hij] at hm
  exact hs hm

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/Extremal.lean` -/

section
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The finite set of all `k`-uniform, two-intersecting families on `Fin N`. -/
noncomputable def candidateFamilies (N k : ℕ) :
    Finset (Finset (Finset (Fin N))) :=
  (Finset.univ : Finset (Finset (Finset (Fin N)))).filter fun F =>
    Uniform k F ∧ TwoIntersecting F

@[simp] lemma mem_candidateFamilies {N k : ℕ} {F : Finset (Finset (Fin N))} :
    F ∈ candidateFamilies N k ↔ Uniform k F ∧ TwoIntersecting F := by
  simp [candidateFamilies]

/-- Every valid uniform two-intersecting family occurs in the finite candidate set. -/
lemma mem_candidateFamilies_of_valid {N k : ℕ} {F : Finset (Finset (Fin N))}
    (huniform : Uniform k F) (hinter : TwoIntersecting F) :
    F ∈ candidateFamilies N k :=
  mem_candidateFamilies.mpr ⟨huniform, hinter⟩

/-- The candidate set is nonempty: it always contains the empty family. -/
lemma candidateFamilies_nonempty (N k : ℕ) : (candidateFamilies N k).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [Uniform, TwoIntersecting]

/--
There is a maximum-cardinality uniform two-intersecting family which is left-compressed.

We first maximize cardinality over the finite candidate set. Among all candidates with that
maximum cardinality we minimize `familyWeight`. A nontrivial left shift preserves validity and
cardinality but strictly lowers the weight, so the selected family is fixed by every left shift.
-/
theorem exists_extremal_leftCompressed (N k : ℕ) :
    ∃ Fmax : Finset (Finset (Fin N)),
      Uniform k Fmax ∧
      TwoIntersecting Fmax ∧
      (∀ F : Finset (Finset (Fin N)),
        Uniform k F → TwoIntersecting F → F.card ≤ Fmax.card) ∧
      LeftCompressed Fmax := by
  obtain ⟨F₀, hF₀cand, hF₀max⟩ :=
    Finset.exists_max_image (candidateFamilies N k) Finset.card
      (candidateFamilies_nonempty N k)
  let maximumCandidates :=
    (candidateFamilies N k).filter fun F => F.card = F₀.card
  have hF₀maximum : F₀ ∈ maximumCandidates := by
    simp [maximumCandidates, hF₀cand]
  obtain ⟨Fmax, hFmaxMaximum, hFmaxMin⟩ :=
    Finset.exists_min_image maximumCandidates familyWeight ⟨F₀, hF₀maximum⟩
  have hFmaxCand : Fmax ∈ candidateFamilies N k := by
    exact (Finset.mem_filter.mp hFmaxMaximum).1
  have hFmaxCard : Fmax.card = F₀.card := by
    exact (Finset.mem_filter.mp hFmaxMaximum).2
  have huniform : Uniform k Fmax := (mem_candidateFamilies.mp hFmaxCand).1
  have hinter : TwoIntersecting Fmax := (mem_candidateFamilies.mp hFmaxCand).2
  refine ⟨Fmax, huniform, hinter, ?_, ?_⟩
  · intro F hFuniform hFinter
    have hFcand : F ∈ candidateFamilies N k :=
      mem_candidateFamilies_of_valid hFuniform hFinter
    simpa [hFmaxCard] using hF₀max F hFcand
  · intro i j hij
    by_contra hshift
    have hshiftUniform : Uniform k (familyShift i j Fmax) :=
      huniform.familyShift i j
    have hshiftInter : TwoIntersecting (familyShift i j Fmax) :=
      hinter.familyShift i j
    have hshiftCand : familyShift i j Fmax ∈ candidateFamilies N k :=
      mem_candidateFamilies_of_valid hshiftUniform hshiftInter
    have hshiftCard : (familyShift i j Fmax).card = F₀.card := by
      rw [card_familyShift, hFmaxCard]
    have hshiftMaximum : familyShift i j Fmax ∈ maximumCandidates := by
      exact Finset.mem_filter.mpr ⟨hshiftCand, hshiftCard⟩
    have hmin := hFmaxMin (familyShift i j Fmax) hshiftMaximum
    have hlt := familyWeight_familyShift_lt hij hshift
    omega

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/Incidence.lean` -/

section
/-!
# Incidence and binomial-coefficient helpers for Erdős Problem 83

This file contains the finite double-counting lemma used at the central
defect level, together with cross-multiplied forms of the elementary ratios
between adjacent binomial coefficients.  All statements take values in
`ℕ`, so downstream proofs do not need division or casts.
-/

open scoped BigOperators
open Finset



/-- A nonempty finite set contains a point whose value is at least the
average, in division-free form. -/
lemma exists_card_mul_value_ge_sum {T : Type*} [Fintype T] [Nonempty T]
    (f : T → ℕ) :
    ∃ z ∈ (Finset.univ : Finset T),
      Fintype.card T * f z ≥ ∑ x : T, f x := by
  by_contra h
  push_neg at h
  have hlt :
      ∑ z : T, Fintype.card T * f z <
        ∑ _z : T, ∑ x : T, f x := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun z _hz ↦ h z (Finset.mem_univ z))
  have hleft :
      ∑ z : T, Fintype.card T * f z =
        Fintype.card T * ∑ z : T, f z := by
    rw [Finset.mul_sum]
  have hright :
      ∑ _z : T, ∑ x : T, f x =
        Fintype.card T * ∑ x : T, f x := by simp
  rw [hleft, hright] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Incidence averaging for a uniform finite family of finite sets.

If every member of `P` has `r` elements, then some point lies in at least
the average number of members.  The conclusion is cross-multiplied so that
it remains a statement in `ℕ`. -/
theorem exists_incidence_ge_average {T : Type*} [Fintype T] [DecidableEq T]
    [Nonempty T] (P : Finset (Finset T)) (r : ℕ)
    (hcard : ∀ C ∈ P, C.card = r) :
    ∃ z ∈ (Finset.univ : Finset T),
      Fintype.card T * (P.filter fun C ↦ z ∈ C).card ≥ r * P.card := by
  have hdouble :
      ∑ z : T, (P.filter fun C ↦ z ∈ C).card = r * P.card := by
    calc
      ∑ z : T, (P.filter fun C ↦ z ∈ C).card =
          ∑ z : T, ∑ C ∈ P, if z ∈ C then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro z _hz
            simp
      _ = ∑ C ∈ P, ∑ z : T, if z ∈ C then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ C ∈ P, C.card := by
            apply Finset.sum_congr rfl
            intro C _hC
            simp
      _ = ∑ _C ∈ P, r := by
            apply Finset.sum_congr rfl
            intro C hC
            exact hcard C hC
      _ = r * P.card := by simp [Nat.mul_comm]
  obtain ⟨z, hz, hzavg⟩ :=
    exists_card_mul_value_ge_sum
      (fun z : T ↦ (P.filter fun C ↦ z ∈ C).card)
  exact ⟨z, hz, hdouble ▸ hzavg⟩

/-- The ratio between two binomial coefficients with consecutive upper
indices, written without division. -/
lemma choose_succ_left_cross (n k : ℕ) :
    Nat.choose (n + 1) k * (n + 1 - k) =
      Nat.choose n k * (n + 1) := by
  exact (Nat.choose_mul_succ_eq n k).symm

/-- The ratio between adjacent lower indices of a binomial coefficient,
written without division. -/
lemma choose_succ_right_cross (n k : ℕ) :
    Nat.choose n (k + 1) * (k + 1) =
      Nat.choose n k * (n - k) := by
  exact Nat.choose_succ_right_eq n k

/-- Multiplying the two adjacent-lower-index identities gives a convenient
cross-product identity for two binomial coefficients. -/
lemma choose_adjacent_product_cross (n a b : ℕ) :
    Nat.choose n a * Nat.choose n b * ((n - a) * (n - b)) =
      Nat.choose n (a + 1) * Nat.choose n (b + 1) *
        ((a + 1) * (b + 1)) := by
  have ha := Nat.choose_succ_right_eq n a
  have hb := Nat.choose_succ_right_eq n b
  calc
    Nat.choose n a * Nat.choose n b * ((n - a) * (n - b)) =
        (Nat.choose n a * (n - a)) *
          (Nat.choose n b * (n - b)) := by ac_rfl
    _ = (Nat.choose n (a + 1) * (a + 1)) *
          (Nat.choose n (b + 1) * (b + 1)) := by rw [← ha, ← hb]
    _ = Nat.choose n (a + 1) * Nat.choose n (b + 1) *
          ((a + 1) * (b + 1)) := by ac_rfl

/-- When `a + b = n + 2`, each adjacent-binomial identity can be expressed
using the complementary defect level. -/
lemma choose_mul_index_eq_choose_pred_mul_complement
    {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 2) :
    Nat.choose n a * a = Nat.choose n (a - 1) * (b - 1) := by
  have ha_index : a - 1 + 1 = a := by omega
  have hcomplement : n - (a - 1) = b - 1 := by omega
  simpa only [ha_index, hcomplement] using
    (Nat.choose_succ_right_eq n (a - 1))

/-- The numerical contradiction at noncentral defect levels, separated from
the combinatorial replacement argument.  In fact the strict inequality is
valid for every pair of positive complementary levels. -/
lemma choose_product_lt_pred_product_of_add_eq
    {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 2) :
    Nat.choose n a * Nat.choose n b <
      Nat.choose n (a - 1) * Nat.choose n (b - 1) := by
  have han : a - 1 ≤ n := by omega
  have hbn : b - 1 ≤ n := by omega
  have hpred_pos :
      0 < Nat.choose n (a - 1) * Nat.choose n (b - 1) :=
    Nat.mul_pos (Nat.choose_pos han) (Nat.choose_pos hbn)
  have hfactor : (a - 1) * (b - 1) < a * b := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right (b - 1) (Nat.sub_le a 1)) ?_
    exact Nat.mul_lt_mul_of_pos_left (by omega) ha
  have ha' := choose_mul_index_eq_choose_pred_mul_complement ha hb hab
  have hb' := choose_mul_index_eq_choose_pred_mul_complement
    (n := n) (a := b) (b := a) hb ha (by omega)
  have hmul :
      (Nat.choose n a * Nat.choose n b) * (a * b) =
        (Nat.choose n (a - 1) * Nat.choose n (b - 1)) *
          ((a - 1) * (b - 1)) := by
    calc
      (Nat.choose n a * Nat.choose n b) * (a * b) =
          (Nat.choose n a * a) * (Nat.choose n b * b) := by ac_rfl
      _ = (Nat.choose n (a - 1) * (b - 1)) *
          (Nat.choose n (b - 1) * (a - 1)) := by rw [ha', hb']
      _ = (Nat.choose n (a - 1) * Nat.choose n (b - 1)) *
          ((a - 1) * (b - 1)) := by ac_rfl
  by_contra hnot
  have hle :
      Nat.choose n (a - 1) * Nat.choose n (b - 1) ≤
        Nat.choose n a * Nat.choose n b := Nat.le_of_not_gt hnot
  have hle' := Nat.mul_le_mul_right (a * b) hle
  rw [hmul] at hle'
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_left hfactor hpred_pos)) hle'

/-- Transfer a cross-multiplied strict inequality through the ratio between
`choose (n + 1) k` and `choose n k`.  This is the division-free central-level
estimate used after incidence averaging. -/
lemma choose_succ_left_mul_lt_of_cross_lt
    {n k x y : ℕ} (hk : k ≤ n)
    (hxy : y * (n + 1 - k) < x * (n + 1)) :
    Nat.choose n k * y < Nat.choose (n + 1) k * x := by
  have hchoose_pos : 0 < Nat.choose n k := Nat.choose_pos hk
  have hscaled :
      Nat.choose n k * (y * (n + 1 - k)) <
        Nat.choose n k * (x * (n + 1)) :=
    Nat.mul_lt_mul_of_pos_left hxy hchoose_pos
  have hcross := choose_succ_left_cross n k
  apply Nat.lt_of_mul_lt_mul_right (a := n + 1 - k)
  calc
    (Nat.choose n k * y) * (n + 1 - k) =
        Nat.choose n k * (y * (n + 1 - k)) := by ac_rfl
    _ < Nat.choose n k * (x * (n + 1)) := hscaled
    _ = (Nat.choose n k * (n + 1)) * x := by ac_rfl
    _ = (Nat.choose (n + 1) k * (n + 1 - k)) * x :=
      congrArg (fun q : ℕ ↦ q * x) hcross.symm
    _ = (Nat.choose (n + 1) k * x) * (n + 1 - k) := by ac_rfl

/-- Cross-cancel the positive multiplicities in the two inequalities arising
from the two noncentral defect replacements. -/
lemma mul_mul_le_mul_mul_of_cross_bounds
    {A B C D x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h₁ : A * x ≤ B * y) (h₂ : C * y ≤ D * x) :
    A * C ≤ B * D := by
  have hxy : 0 < x * y := Nat.mul_pos hx hy
  have hprod : (A * x) * (C * y) ≤ (B * y) * (D * x) :=
    Nat.mul_le_mul h₁ h₂
  have hfactored : (x * y) * (A * C) ≤ (x * y) * (B * D) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod
  exact Nat.le_of_mul_le_mul_left hfactored hxy

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/PrefixSets.lean` -/

section
/-!
# Prefix and tail sets for Erdős Problem 83

This file packages the elementary finite-set combinatorics used by the
specialized Ahlswede--Khachatrian defect argument.  The first `ell` points of
`Fin N` form `«prefix» N ell`; the remaining points form `tailAfter N ell`.
-/



open Finset

/-- The first `ell` elements of `Fin N`.  When `ell ≤ N`, this has exactly
`ell` elements. -/
def «prefix» (N ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ x.val < ell

/-- The elements of `Fin N` at or after position `ell`. -/
def tailAfter (N ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ ell ≤ x.val

@[simp] theorem mem_prefix {N ell : ℕ} {x : Fin N} :
    x ∈ «prefix» N ell ↔ x.val < ell := by
  simp [«prefix»]

@[simp] theorem mem_tailAfter {N ell : ℕ} {x : Fin N} :
    x ∈ tailAfter N ell ↔ ell ≤ x.val := by
  simp [tailAfter]

theorem prefix_subset_univ (N ell : ℕ) :
    «prefix» N ell ⊆ (Finset.univ : Finset (Fin N)) := by
  simp

theorem tailAfter_subset_univ (N ell : ℕ) :
    tailAfter N ell ⊆ (Finset.univ : Finset (Fin N)) := by
  simp

/-- The «prefix» has its expected cardinality whenever its endpoint is in the
ambient range. -/
theorem card_prefix {N ell : ℕ} (h : ell ≤ N) :
    («prefix» N ell).card = ell := by
  let hlt : ∀ m ∈ Finset.range ell, m < N := by
    intro m hm
    exact (Finset.mem_range.mp hm).trans_le h
  have hp : «prefix» N ell = (Finset.range ell).attachFin hlt := by
    ext x
    simp only [mem_prefix, Finset.mem_attachFin, Finset.mem_range]
  rw [hp, Finset.card_attachFin, Finset.card_range]

/-- Alias with the definition-first naming order. -/
theorem prefix_card {N ell : ℕ} (h : ell ≤ N) :
    («prefix» N ell).card = ell :=
  card_prefix h

theorem tailAfter_eq_univ_sdiff (N ell : ℕ) :
    tailAfter N ell = (Finset.univ : Finset (Fin N)) \ «prefix» N ell := by
  ext x
  simp only [mem_tailAfter, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_prefix]
  omega

/-- The tail has the complementary cardinality. -/
theorem card_tailAfter {N ell : ℕ} (h : ell ≤ N) :
    (tailAfter N ell).card = N - ell := by
  rw [tailAfter_eq_univ_sdiff]
  simpa [card_prefix h] using
    (Finset.card_sdiff_of_subset (prefix_subset_univ N ell))

/-- Alias with the definition-first naming order. -/
theorem tailAfter_card {N ell : ℕ} (h : ell ≤ N) :
    (tailAfter N ell).card = N - ell :=
  card_tailAfter h

theorem disjoint_prefix_tailAfter (N ell : ℕ) :
    Disjoint («prefix» N ell) (tailAfter N ell) := by
  rw [tailAfter_eq_univ_sdiff]
  exact Finset.disjoint_sdiff

theorem prefix_disjoint_tailAfter (N ell : ℕ) :
    Disjoint («prefix» N ell) (tailAfter N ell) :=
  disjoint_prefix_tailAfter N ell

@[simp] theorem prefix_inter_tailAfter (N ell : ℕ) :
    «prefix» N ell ∩ tailAfter N ell = ∅ := by
  exact Finset.disjoint_iff_inter_eq_empty.mp (disjoint_prefix_tailAfter N ell)

@[simp] theorem tailAfter_inter_prefix (N ell : ℕ) :
    tailAfter N ell ∩ «prefix» N ell = ∅ := by
  rw [Finset.inter_comm, prefix_inter_tailAfter]

theorem prefix_union_tailAfter (N ell : ℕ) :
    «prefix» N ell ∪ tailAfter N ell = (Finset.univ : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_union, mem_prefix, mem_tailAfter, Finset.mem_univ,
    iff_true]
  omega

theorem tailAfter_union_prefix (N ell : ℕ) :
    tailAfter N ell ∪ «prefix» N ell = (Finset.univ : Finset (Fin N)) := by
  rw [Finset.union_comm, prefix_union_tailAfter]

/-- Every finite set is reconstructed from its «prefix» and tail pieces. -/
theorem inter_prefix_union_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    (S ∩ «prefix» N ell) ∪ (S ∩ tailAfter N ell) = S := by
  ext x
  by_cases hx : x.val < ell
  · simp [hx]
  · have hxe : ell ≤ x.val := Nat.le_of_not_gt hx
    simp [hx, hxe]

/-- The two pieces in the preceding decomposition are disjoint. -/
theorem disjoint_inter_prefix_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    Disjoint (S ∩ «prefix» N ell) (S ∩ tailAfter N ell) := by
  exact (disjoint_prefix_tailAfter N ell).mono Finset.inter_subset_right
    Finset.inter_subset_right

/-- Cardinality splits as the sum of the «prefix» and tail cardinalities. -/
theorem card_inter_prefix_add_card_inter_tailAfter {N ell : ℕ}
    (S : Finset (Fin N)) :
    (S ∩ «prefix» N ell).card + (S ∩ tailAfter N ell).card = S.card := by
  rw [← Finset.card_union_of_disjoint
    (disjoint_inter_prefix_inter_tailAfter S),
    inter_prefix_union_inter_tailAfter]

/-- Unioning a «prefix» part and a tail part and then restricting to the «prefix»
recovers the «prefix» part. -/
theorem union_inter_prefix {N ell : ℕ} {A B : Finset (Fin N)}
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ tailAfter N ell) :
    (A ∪ B) ∩ «prefix» N ell = A := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxAB, hxp⟩
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact hxA
    · have hxt := hB hxB
      exact ((Finset.disjoint_left.mp (disjoint_prefix_tailAfter N ell)) hxp hxt).elim
  · intro hxA
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hxA, hA hxA⟩

/-- The tail analogue of `union_inter_prefix`. -/
theorem union_inter_tailAfter {N ell : ℕ} {A B : Finset (Fin N)}
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ tailAfter N ell) :
    (A ∪ B) ∩ tailAfter N ell = B := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxAB, hxt⟩
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · have hxp := hA hxA
      exact ((Finset.disjoint_left.mp (disjoint_prefix_tailAfter N ell)) hxp hxt).elim
    · exact hxB
  · intro hxB
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hxB, hB hxB⟩

/-- Inclusion--exclusion gives the universal lower bound on the intersection
of two subsets of an `ell`-point «prefix». -/
theorem prefix_inter_card_lower_bound {N ell a b : ℕ}
    {A B : Finset (Fin N)} (hN : ell ≤ N)
    (hA : A ⊆ «prefix» N ell) (hB : B ⊆ «prefix» N ell)
    (hAcard : A.card = a) (hBcard : B.card = b) :
    a + b - ell ≤ (A ∩ B).card := by
  have hUnion : A ∪ B ⊆ «prefix» N ell := Finset.union_subset hA hB
  have hUnionCard : (A ∪ B).card ≤ ell := by
    simpa [card_prefix hN] using Finset.card_le_card hUnion
  have hIE := Finset.card_union_add_card_inter A B
  omega

/-- Given a `b`-subset of an `ell`-point «prefix», any feasible `a` admits a
«prefix» subset meeting it in at most one point.

The proof first uses points outside `B`.  If there are not quite enough,
the numerical hypothesis says that exactly one point of `B` is needed. -/
theorem exists_prefix_subset_card_inter_le_one {N ell a b : ℕ}
    (hN : ell ≤ N) (B : Finset (Fin N))
    (hB : B ⊆ «prefix» N ell) (hBcard : B.card = b)
    (ha : a ≤ ell) (hab : a + b ≤ ell + 1) :
    ∃ A : Finset (Fin N),
      A ⊆ «prefix» N ell ∧ A.card = a ∧ (A ∩ B).card ≤ 1 := by
  have hb : b ≤ ell := by
    have := Finset.card_le_card hB
    simpa [hBcard, card_prefix hN] using this
  let C := «prefix» N ell \ B
  have hCcard : C.card = ell - b := by
    dsimp [C]
    simpa [hBcard, card_prefix hN] using Finset.card_sdiff_of_subset hB
  by_cases hac : a ≤ ell - b
  · have hacard : a ≤ C.card := by simpa [hCcard] using hac
    obtain ⟨A, hAC, hAcard⟩ := Finset.exists_subset_card_eq hacard
    refine ⟨A, hAC.trans Finset.sdiff_subset, hAcard, ?_⟩
    have hdisj : Disjoint A B := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxA hxB'
      exact (Finset.mem_sdiff.mp (hAC hxA)).2 hxB'
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  · have haeq : a = ell - b + 1 := by omega
    have hbpos : 0 < B.card := by
      rw [hBcard]
      omega
    obtain ⟨x, hxB⟩ := Finset.card_pos.mp hbpos
    let A := C ∪ {x}
    have hxPrefix : x ∈ «prefix» N ell := hB hxB
    have hxC : x ∉ C := by
      simp [C, hxB]
    have hdisj : Disjoint C ({x} : Finset (Fin N)) := by
      exact Finset.disjoint_singleton_right.mpr hxC
    have hAcard : A.card = a := by
      simp only [A, Finset.card_union_of_disjoint hdisj, hCcard,
        Finset.card_singleton]
      omega
    have hAinter : A ∩ B = {x} := by
      ext y
      simp [A, C, hxB]
    refine ⟨A, ?_, hAcard, ?_⟩
    · exact Finset.union_subset Finset.sdiff_subset
        (Finset.singleton_subset_iff.mpr hxPrefix)
    · rw [hAinter]
      simp

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/Prefix.lean` -/

section
/-!
# Prefix symmetrisation for Erdos Problem 83

This file contains the specialised Ahlswede--Khachatrian defect-level
replacement argument. The ambient points are Fin (4 * q), and all members
of the family have cardinality 2 * q.
-/



open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

/-- Membership in a family depends only on the part at or after ell and on
the cardinality of the part before ell. This is the permutation-free form of
invariance under all permutations of the first ell coordinates. -/
def PrefixInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (ell : ℕ) : Prop :=
  ∀ ⦃A B : Finset (Fin N)⦄,
    A ∩ tailAfter N ell = B ∩ tailAfter N ell →
    (A ∩ «prefix» N ell).card = (B ∩ «prefix» N ell).card →
    (A ∈ F ↔ B ∈ F)

/-- All unions of an a-subset of the prefix with one of the supplied
tails. The tail family is represented in the ambient Fin N. -/
noncomputable def layerFromTails (N ell a : ℕ)
    (P : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) :=
  P.biUnion fun C ↦
    («prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C

lemma mem_layerFromTails {N ell a : ℕ} {P : Finset (Finset (Fin N))}
    {A : Finset (Fin N)} :
    A ∈ layerFromTails N ell a P ↔
      ∃ C ∈ P, ∃ B ⊆ «prefix» N ell, B.card = a ∧ B ∪ C = A := by
  simp [layerFromTails, and_assoc]

private lemma union_right_injective_of_disjoint {α : Type*} [DecidableEq α]
    {S C : Finset α} (hSC : Disjoint S C) :
    Function.Injective (fun B : {B // B ⊆ S} ↦ (B : Finset α) ∪ C) := by
  intro B₁ B₂ h
  change (B₁ : Finset α) ∪ C = (B₂ : Finset α) ∪ C at h
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    have hxU : x ∈ (B₁ : Finset α) ∪ C := mem_union_left _ hx
    rw [h] at hxU
    rcases mem_union.mp hxU with hx₂ | hxC
    · exact hx₂
    · exact (Finset.disjoint_left.mp hSC (B₁.property hx) hxC).elim
  · intro hx
    have hxU : x ∈ (B₂ : Finset α) ∪ C := mem_union_left _ hx
    rw [← h] at hxU
    rcases mem_union.mp hxU with hx₁ | hxC
    · exact hx₁
    · exact (Finset.disjoint_left.mp hSC (B₂.property hx) hxC).elim

private lemma layer_piece_card {N ell a : ℕ} {C : Finset (Fin N)}
    (hC : C ⊆ tailAfter N ell) :
    ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C).card =
      Nat.choose («prefix» N ell).card a := by
  rw [card_image_iff.mpr]
  · exact card_powersetCard _ _
  · intro B₁ hB₁ B₂ hB₂ hEq
    have hB₁s : B₁ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₁).1
    have hB₂s : B₂ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₂).1
    have hd : Disjoint («prefix» N ell) C :=
      (disjoint_prefix_tailAfter N ell).mono_right hC
    let B₁' : {B // B ⊆ «prefix» N ell} := ⟨B₁, hB₁s⟩
    let B₂' : {B // B ⊆ «prefix» N ell} := ⟨B₂, hB₂s⟩
    have hEq' : (B₁' : Finset (Fin N)) ∪ C =
        (B₂' : Finset (Fin N)) ∪ C := hEq
    have hi := union_right_injective_of_disjoint hd hEq'
    exact congrArg Subtype.val hi

private lemma layer_pieces_disjoint {N ell a : ℕ}
    {C₁ C₂ : Finset (Fin N)}
    (hC₁ : C₁ ⊆ tailAfter N ell) (hC₂ : C₂ ⊆ tailAfter N ell)
    (hne : C₁ ≠ C₂) :
    Disjoint
      ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C₁)
      ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C₂) := by
  rw [disjoint_left]
  intro A hA₁ hA₂
  obtain ⟨B₁, hB₁, rfl⟩ := mem_image.mp hA₁
  obtain ⟨B₂, hB₂, hEq⟩ := mem_image.mp hA₂
  have hB₁s : B₁ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₁).1
  have hB₂s : B₂ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₂).1
  have ht₁ : (B₁ ∪ C₁) ∩ tailAfter N ell = C₁ :=
    union_inter_tailAfter hB₁s hC₁
  have ht₂ : (B₂ ∪ C₂) ∩ tailAfter N ell = C₂ :=
    union_inter_tailAfter hB₂s hC₂
  apply hne
  rw [← ht₁, ← ht₂, ← hEq]

lemma card_layerFromTails {N ell a : ℕ} {P : Finset (Finset (Fin N))}
    (hP : ∀ C ∈ P, C ⊆ tailAfter N ell) :
    (layerFromTails N ell a P).card =
      Nat.choose («prefix» N ell).card a * P.card := by
  classical
  rw [layerFromTails, card_biUnion]
  · calc
      ∑ C ∈ P,
          ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C).card =
          ∑ _C ∈ P, Nat.choose («prefix» N ell).card a := by
            apply sum_congr rfl
            intro C hC
            exact layer_piece_card (hP C hC)
      _ = Nat.choose («prefix» N ell).card a * P.card := by
        simp [Nat.mul_comm]
  · intro C₁ hC₁ C₂ hC₂ hne
    exact layer_pieces_disjoint (hP C₁ hC₁) (hP C₂ hC₂) hne

/-- The point immediately following a prefix. -/
def nextPoint {N ell : ℕ} (h : ell < N) : Fin N := ⟨ell, h⟩

@[simp] lemma nextPoint_val {N ell : ℕ} (h : ell < N) :
    (nextPoint h).val = ell := rfl

/-- Move one occupied prefix point to the first point after the prefix. -/
def rightExchange {N : ℕ} (h i : Fin N) (A : Finset (Fin N)) :
    Finset (Fin N) :=
  insert h (A.erase i)

@[simp] lemma mem_rightExchange {N : ℕ} {h i x : Fin N}
    {A : Finset (Fin N)} :
    x ∈ rightExchange h i A ↔ x = h ∨ (x ∈ A ∧ x ≠ i) := by
  simp [rightExchange, eq_comm, and_comm, and_left_comm]

lemma rightExchange_eq_transpose {N : ℕ} {h i : Fin N}
    {A : Finset (Fin N)} (hi : i ∈ A) (hh : h ∉ A) :
    rightExchange h i A = setTranspose i h A := by
  classical
  ext x
  simp only [mem_rightExchange, mem_setTranspose]
  by_cases xh : x = h
  · subst x
    have hne : h ≠ i := by
      intro e
      subst i
      exact hh hi
    simp [hi, hne]
  by_cases xi : x = i
  · subst x
    have hne : i ≠ h := by
      intro e
      subst h
      exact hh hi
    simp [hh, hne]
  · simp [Equiv.swap_apply_of_ne_of_ne xi xh, xh, xi]

lemma card_rightExchange {N : ℕ} {h i : Fin N}
    {A : Finset (Fin N)} (hi : i ∈ A) (hh : h ∉ A) :
    (rightExchange h i A).card = A.card := by
  rw [rightExchange_eq_transpose hi hh, card_setTranspose]

/-- Defective members at the step from prefix length ell to ell+1. -/
noncomputable def defectFamily {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  F.filter fun A ↦
    ∃ i ∈ «prefix» N ell,
      i ∈ A ∧ nextPoint hN ∉ A ∧ rightExchange (nextPoint hN) i A ∉ F

lemma mem_defectFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell : ℕ} {hN : ell < N} {A : Finset (Fin N)} :
    A ∈ defectFamily F ell hN ↔
      A ∈ F ∧ ∃ i ∈ «prefix» N ell,
        i ∈ A ∧ nextPoint hN ∉ A ∧
          rightExchange (nextPoint hN) i A ∉ F := by
  simp [defectFamily]

noncomputable def defectLayer {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  (defectFamily F ell hN).filter fun A ↦ (A ∩ «prefix» N ell).card = a

lemma mem_defectLayer {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell a : ℕ} {hN : ell < N} {A : Finset (Fin N)} :
    A ∈ defectLayer F ell a hN ↔
      A ∈ defectFamily F ell hN ∧ (A ∩ «prefix» N ell).card = a := by
  simp [defectLayer]

/-- The far tails occurring at one defect level. -/
noncomputable def defectTails {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  (defectLayer F ell a hN).image fun A ↦ A ∩ tailAfter N (ell + 1)

lemma mem_defectTails {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell a : ℕ} {hN : ell < N} {C : Finset (Fin N)} :
    C ∈ defectTails F ell a hN ↔
      ∃ A ∈ defectLayer F ell a hN,
        A ∩ tailAfter N (ell + 1) = C := by
  simp [defectTails, eq_comm]

lemma defectTails_subset_tailAfter {N : ℕ}
    {F : Finset (Finset (Fin N))} {ell a : ℕ} {hN : ell < N}
    {C : Finset (Fin N)} (hC : C ∈ defectTails F ell a hN) :
    C ⊆ tailAfter N (ell + 1) := by
  obtain ⟨A, _hA, rfl⟩ := mem_defectTails.mp hC
  exact inter_subset_right

/-- The exchanges associated with a defect level. -/
noncomputable def exchangeLayer {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  layerFromTails N ell (a - 1)
    ((defectTails F ell a hN).image fun C ↦ insert (nextPoint hN) C)

@[simp] lemma nextPoint_not_mem_prefix {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∉ «prefix» N ell := by simp

@[simp] lemma nextPoint_mem_tailAfter {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∈ tailAfter N ell := by simp

@[simp] lemma nextPoint_not_mem_farTail {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∉ tailAfter N (ell + 1) := by simp

private lemma rightExchange_inter_tail {N ell : ℕ} (hN : ell < N)
    {A : Finset (Fin N)} {i : Fin N} (hiP : i ∈ «prefix» N ell) :
    rightExchange (nextPoint hN) i A ∩ tailAfter N ell =
      insert (nextPoint hN) (A ∩ tailAfter N (ell + 1)) := by
  ext x
  simp only [mem_inter, mem_rightExchange, mem_tailAfter, mem_insert,
    nextPoint_val]
  constructor
  · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
    · exact Or.inl rfl
    · by_cases hx : x.val = ell
      · left
        exact Fin.ext hx
      · right
        exact ⟨hxA, by omega⟩
  · rintro (rfl | ⟨hxA, hxell⟩)
    · exact ⟨Or.inl rfl, le_rfl⟩
    · refine ⟨Or.inr ⟨hxA, ?_⟩, by omega⟩
      intro hxi
      subst x
      have := mem_prefix.mp hiP
      omega

private lemma rightExchange_inter_prefix {N ell : ℕ} (hN : ell < N)
    {A : Finset (Fin N)} {i : Fin N} (hiP : i ∈ «prefix» N ell) :
    rightExchange (nextPoint hN) i A ∩ «prefix» N ell =
      (A ∩ «prefix» N ell).erase i := by
  ext x
  simp only [mem_inter, mem_rightExchange, mem_prefix, mem_erase]
  constructor
  · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
    · exfalso
      simpa using hxell
    · exact ⟨hxi, hxA, hxell⟩
  · rintro ⟨hxi, hxA, hxell⟩
    exact ⟨Or.inr ⟨hxA, hxi⟩, hxell⟩

private lemma defect_exchange_not_mem
    {N ell : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) {A : Finset (Fin N)}
    (hA : A ∈ defectFamily F ell hN)
    {i : Fin N} (hiP : i ∈ «prefix» N ell) (hiA : i ∈ A) :
    rightExchange (nextPoint hN) i A ∉ F := by
  rcases (mem_defectFamily.mp hA).2 with
    ⟨j, hjP, hjA, hhA, hjMissing⟩
  intro hiMem
  apply hjMissing
  apply (hinv ?_ ?_).mp hiMem
  · ext x
    simp only [mem_inter, mem_rightExchange, mem_tailAfter, nextPoint_val]
    have hiVal : i.val < ell := mem_prefix.mp hiP
    have hjVal : j.val < ell := mem_prefix.mp hjP
    constructor
    · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
      · exact ⟨Or.inl rfl, le_rfl⟩
      · refine ⟨Or.inr ⟨hxA, ?_⟩, hxell⟩
        intro hxj
        subst x
        omega
    · rintro ⟨rfl | ⟨hxA, hxj⟩, hxell⟩
      · exact ⟨Or.inl rfl, le_rfl⟩
      · refine ⟨Or.inr ⟨hxA, ?_⟩, hxell⟩
        intro hxi
        subst x
        omega
  · rw [rightExchange_inter_prefix hN hiP,
      rightExchange_inter_prefix hN hjP]
    have hiInter : i ∈ A ∩ «prefix» N ell := mem_inter.mpr ⟨hiA, hiP⟩
    have hjInter : j ∈ A ∩ «prefix» N ell := mem_inter.mpr ⟨hjA, hjP⟩
    rw [card_erase_of_mem hiInter, card_erase_of_mem hjInter]

private lemma defect_not_mem_next {N ell : ℕ}
    {F : Finset (Finset (Fin N))} {hN : ell < N}
    {A : Finset (Fin N)} (hA : A ∈ defectFamily F ell hN) :
    nextPoint hN ∉ A := by
  rcases (mem_defectFamily.mp hA).2 with ⟨i, hiP, hiA, hhA, hiM⟩
  exact hhA

private lemma inter_tail_eq_far_of_not_next {N ell : ℕ}
    (hN : ell < N) {A : Finset (Fin N)}
    (hh : nextPoint hN ∉ A) :
    A ∩ tailAfter N ell = A ∩ tailAfter N (ell + 1) := by
  ext x
  simp only [mem_inter, mem_tailAfter]
  constructor
  · rintro ⟨hxA, hx⟩
    refine ⟨hxA, ?_⟩
    by_cases heq : x.val = ell
    · have : x = nextPoint hN := Fin.ext heq
      exact (hh (this ▸ hxA)).elim
    · omega
  · rintro ⟨hxA, hx⟩
    exact ⟨hxA, by omega⟩

private lemma defectLayer_eq_layerFromTails
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    defectLayer F ell a hN =
      layerFromTails N ell a (defectTails F ell a hN) := by
  classical
  ext A
  constructor
  · intro hA
    have hAD := (mem_defectLayer.mp hA).1
    have hcard := (mem_defectLayer.mp hA).2
    have hh := defect_not_mem_next hAD
    apply mem_layerFromTails.mpr
    refine ⟨A ∩ tailAfter N (ell + 1), ?_, A ∩ «prefix» N ell,
      inter_subset_right, hcard, ?_⟩
    · exact mem_defectTails.mpr ⟨A, hA, rfl⟩
    · rw [← inter_tail_eq_far_of_not_next hN hh]
      exact inter_prefix_union_inter_tailAfter A
  · intro hA
    rcases mem_layerFromTails.mp hA with
      ⟨C, hCP, B, hBP, hBcard, rfl⟩
    rcases mem_defectTails.mp hCP with ⟨X, hXD, hXC⟩
    have hXdef := (mem_defectLayer.mp hXD).1
    have hXcard := (mem_defectLayer.mp hXD).2
    have hXmem : X ∈ F := (mem_defectFamily.mp hXdef).1
    have hhX := defect_not_mem_next hXdef
    have hCs : C ⊆ tailAfter N (ell + 1) :=
      defectTails_subset_tailAfter hCP
    have hCt : C ⊆ tailAfter N ell := by
      intro x hx
      have := mem_tailAfter.mp (hCs hx)
      exact mem_tailAfter.mpr (by omega)
    have htailBC : (B ∪ C) ∩ tailAfter N ell = C :=
      union_inter_tailAfter hBP hCt
    have htailX : X ∩ tailAfter N ell = C := by
      rw [inter_tail_eq_far_of_not_next hN hhX, hXC]
    have hprefixBC : (B ∪ C) ∩ «prefix» N ell = B :=
      union_inter_prefix hBP hCt
    have hBCmem : B ∪ C ∈ F :=
      (hinv (htailBC.trans htailX.symm)
        (by rw [hprefixBC, hBcard, hXcard])).mpr hXmem
    have hBpos : 0 < B.card := hBcard ▸ ha
    obtain ⟨i, hiB⟩ := card_pos.mp hBpos
    have hiP : i ∈ «prefix» N ell := hBP hiB
    have hhC : nextPoint hN ∉ C :=
      fun hh ↦ nextPoint_not_mem_farTail hN (hCs hh)
    have hhB : nextPoint hN ∉ B :=
      fun hh ↦ nextPoint_not_mem_prefix hN (hBP hh)
    have hhBC : nextPoint hN ∉ B ∪ C := by
      simp [hhB, hhC]
    have hiBC : i ∈ B ∪ C := mem_union_left _ hiB
    refine mem_defectLayer.mpr ⟨mem_defectFamily.mpr
      ⟨hBCmem, ⟨i, hiP, hiBC, hhBC, ?_⟩⟩, ?_⟩
    · intro hExMem
      have hXprefixPos : 0 < (X ∩ «prefix» N ell).card := hXcard ▸ ha
      obtain ⟨j, hjXprefix⟩ := card_pos.mp hXprefixPos
      have hjX : j ∈ X := (mem_inter.mp hjXprefix).1
      have hjP : j ∈ «prefix» N ell := (mem_inter.mp hjXprefix).2
      have hjMissing := defect_exchange_not_mem hinv hXdef hjP hjX
      apply hjMissing
      apply (hinv ?_ ?_).mp hExMem
      · have hBP' : B ⊆ «prefix» N (ell + 1) := by
          intro x hx
          have := mem_prefix.mp (hBP hx)
          exact mem_prefix.mpr (by omega)
        have htfar : (B ∪ C) ∩ tailAfter N (ell + 1) = C :=
          union_inter_tailAfter hBP' hCs
        rw [rightExchange_inter_tail hN hiP,
          rightExchange_inter_tail hN hjP, htfar, hXC]
      · rw [rightExchange_inter_prefix hN hiP,
          rightExchange_inter_prefix hN hjP, hprefixBC]
        have hiBP : i ∈ B ∩ «prefix» N ell := mem_inter.mpr ⟨hiB, hiP⟩
        rw [card_erase_of_mem hiB, card_erase_of_mem hjXprefix,
          hBcard, hXcard]
    · rw [hprefixBC, hBcard]

private lemma card_defectLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    (defectLayer F ell a hN).card =
      Nat.choose ell a * (defectTails F ell a hN).card := by
  rw [defectLayer_eq_layerFromTails hinv ha,
    card_layerFromTails (fun C hC ↦
      (defectTails_subset_tailAfter hC).trans ?_),
    card_prefix hN.le]
  intro x hx
  simp only [mem_tailAfter] at hx ⊢
  omega

private lemma insert_next_injective_on_farTails {N ell : ℕ}
    (hN : ell < N) (P : Finset (Finset (Fin N)))
    (hP : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1)) :
    Set.InjOn (fun C ↦ insert (nextPoint hN) C)
      (↑P : Set (Finset (Fin N))) := by
  intro C₁ hC₁ C₂ hC₂ hEq
  ext x
  have hh₁ : nextPoint hN ∉ C₁ :=
    fun hh ↦ nextPoint_not_mem_farTail hN (hP C₁ hC₁ hh)
  have hh₂ : nextPoint hN ∉ C₂ :=
    fun hh ↦ nextPoint_not_mem_farTail hN (hP C₂ hC₂ hh)
  by_cases hx : x = nextPoint hN
  · subst x
    simp [hh₁, hh₂]
  · have := congrArg (fun S : Finset (Fin N) ↦ x ∈ S) hEq
    simpa [hx] using this

private lemma card_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N} :
    (exchangeLayer F ell a hN).card =
      Nat.choose ell (a - 1) * (defectTails F ell a hN).card := by
  let P := defectTails F ell a hN
  have hPfar : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1) :=
    fun C hC ↦ defectTails_subset_tailAfter hC
  have hPtail :
      ∀ C ∈ P.image (fun C ↦ insert (nextPoint hN) C),
        C ⊆ tailAfter N ell := by
    intro C hC
    rcases mem_image.mp hC with ⟨D, hDP, rfl⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hxD
    · exact nextPoint_mem_tailAfter hN
    · have := mem_tailAfter.mp (hPfar D hDP hxD)
      exact mem_tailAfter.mpr (by omega)
  rw [exchangeLayer, card_layerFromTails hPtail, card_prefix hN.le,
    card_image_iff.mpr (insert_next_injective_on_farTails hN P hPfar)]

private lemma exchangeLayer_disjoint_family
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    Disjoint (exchangeLayer F ell a hN) F := by
  rw [disjoint_left]
  intro E hE hEF
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, rfl⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  rcases mem_defectTails.mp hCP with ⟨X, hXD, hXC⟩
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hXprefixPos : 0 < (X ∩ «prefix» N ell).card := hXcard ▸ ha
  obtain ⟨j, hjXP⟩ := card_pos.mp hXprefixPos
  have hjX : j ∈ X := (mem_inter.mp hjXP).1
  have hjP : j ∈ «prefix» N ell := (mem_inter.mp hjXP).2
  apply defect_exchange_not_mem hinv hXdef hjP hjX
  apply (hinv ?_ ?_).mpr hEF
  · rw [rightExchange_inter_tail hN hjP, hXC]
    symm
    apply union_inter_tailAfter hBP
    intro x hx
    rcases mem_insert.mp hx with rfl | hxC
    · exact nextPoint_mem_tailAfter hN
    · have hxFar := defectTails_subset_tailAfter hCP hxC
      simp only [mem_tailAfter] at hxFar ⊢
      omega
  · rw [rightExchange_inter_prefix hN hjP,
      union_inter_prefix hBP]
    · rw [hBcard, card_erase_of_mem hjXP, hXcard]
    · intro x hx
      rcases mem_insert.mp hx with rfl | hxC
      · exact nextPoint_mem_tailAfter hN
      · have hxFar := defectTails_subset_tailAfter hCP hxC
        simp only [mem_tailAfter] at hxFar ⊢
        omega

private lemma exchangeLayer_exists_source
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    {E : Finset (Fin N)} (hE : E ∈ exchangeLayer F ell a hN) :
    ∃ X ∈ defectLayer F ell a hN, ∃ i ∈ «prefix» N ell,
      i ∈ X ∧ E = rightExchange (nextPoint hN) i X := by
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, hEeq⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  rcases mem_defectTails.mp hCP with ⟨X₀, hX₀D, hX₀C⟩
  have hX₀card := (mem_defectLayer.mp hX₀D).2
  have haell : a ≤ ell := by
    have hs : (X₀ ∩ «prefix» N ell).card ≤
        («prefix» N ell).card := card_le_card inter_subset_right
    rw [hX₀card, card_prefix hN.le] at hs
    exact hs
  have hBlt : B.card < («prefix» N ell).card := by
    rw [hBcard, card_prefix hN.le]
    omega
  obtain ⟨i, hiP, hiB⟩ :=
    exists_mem_notMem_of_card_lt_card hBlt
  let X := insert i B ∪ C
  have hCs : C ⊆ tailAfter N (ell + 1) :=
    defectTails_subset_tailAfter hCP
  have hCt : C ⊆ tailAfter N ell := by
    intro x hx
    have := mem_tailAfter.mp (hCs hx)
    exact mem_tailAfter.mpr (by omega)
  have hiC : i ∉ C := by
    intro hi
    have hiFar := mem_tailAfter.mp (hCs hi)
    have hiVal := mem_prefix.mp hiP
    omega
  have hXP : insert i B ⊆ «prefix» N ell := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxB
    · exact hiP
    · exact hBP hxB
  have hXcard : (insert i B).card = a := by
    rw [card_insert_of_notMem hiB, hBcard]
    omega
  have hXD : X ∈ defectLayer F ell a hN := by
    rw [defectLayer_eq_layerFromTails hinv ha]
    exact mem_layerFromTails.mpr
      ⟨C, hCP, insert i B, hXP, hXcard, rfl⟩
  refine ⟨X, hXD, i, hiP, ?_, ?_⟩
  · exact mem_union_left _ (mem_insert_self i B)
  · rw [← hEeq]
    ext x
    simp only [X, mem_union, mem_insert, mem_rightExchange]
    constructor
    · rintro (hxB | rfl | hxC)
      · exact Or.inr ⟨Or.inl (Or.inr hxB), by
          intro hxi
          subst x
          exact hiB hxB⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr hxC, by
          intro hxi
          subst x
          exact hiC hxC⟩
    · rintro (rfl | ⟨(rfl | hxB) | hxC, hxi⟩)
      · exact Or.inr (Or.inl rfl)
      · exact (hxi rfl).elim
      · exact Or.inl hxB
      · exact Or.inr (Or.inr hxC)

private lemma exchange_cross_nondefect
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    (hinter : TwoIntersecting F)
    {E Y : Finset (Fin N)}
    (hE : E ∈ exchangeLayer F ell a hN)
    (hYF : Y ∈ F) (hYD : Y ∉ defectFamily F ell hN) :
    2 ≤ (E ∩ Y).card := by
  obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
    exchangeLayer_exists_source hinv ha hE
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF : X ∈ F := (mem_defectFamily.mp hXdef).1
  have hhX := defect_not_mem_next hXdef
  rw [rightExchange_eq_transpose hiX hhX,
    card_inter_transpose_cross]
  by_cases hbad : i ∈ Y ∧ nextPoint hN ∉ Y
  · have hYex : rightExchange (nextPoint hN) i Y ∈ F := by
      by_contra hmissing
      apply hYD
      exact mem_defectFamily.mpr
        ⟨hYF, ⟨i, hiP, hbad.1, hbad.2, hmissing⟩⟩
    rw [← rightExchange_eq_transpose hbad.1 hbad.2]
    exact hinter hXF hYex
  · exact le_trans (hinter hXF hYF) (card_le_card
      (by
        have hs := inter_subset_inter_transpose_right
          (i := nextPoint hN) (j := i) ⟨hiX, hhX⟩ hbad
        have heq : setTranspose (nextPoint hN) i Y =
            setTranspose i (nextPoint hN) Y := by
          unfold setTranspose
          rw [Equiv.swap_comm]
        simpa only [heq] using hs))

private lemma exists_prefix_subset_disjoint
    {N ell a : ℕ} (hN : ell ≤ N) (B : Finset (Fin N))
    (hB : B ⊆ «prefix» N ell) (ha : a + B.card ≤ ell) :
    ∃ A : Finset (Fin N),
      A ⊆ «prefix» N ell ∧ A.card = a ∧ Disjoint A B := by
  let C := «prefix» N ell \ B
  have hBC : B.card ≤ ell := by
    have := card_le_card hB
    simpa [card_prefix hN] using this
  have hCcard : C.card = ell - B.card := by
    dsimp [C]
    simpa [card_prefix hN] using card_sdiff_of_subset hB
  have haC : a ≤ C.card := by omega
  obtain ⟨A, hAC, hAcard⟩ := exists_subset_card_eq haC
  refine ⟨A, hAC.trans sdiff_subset, hAcard, ?_⟩
  exact disjoint_left.mpr fun x hxA hxB ↦
    (mem_sdiff.mp (hAC hxA)).2 hxB

private lemma defect_inter_card_three
    {q ell a b : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    {X Y : Finset (Fin (4 * q))}
    (hXD : X ∈ defectLayer F ell a (by omega))
    (hYD : Y ∈ defectLayer F ell b (by omega))
    (hsum : a + b ≠ ell + 2) :
    3 ≤ (X ∩ Y).card := by
  let hN : ell < 4 * q := by omega
  have hXdef := (mem_defectLayer.mp hXD).1
  have hYdef := (mem_defectLayer.mp hYD).1
  have hXF : X ∈ F := (mem_defectFamily.mp hXdef).1
  have hYF : Y ∈ F := (mem_defectFamily.mp hYdef).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hYcard := (mem_defectLayer.mp hYD).2
  have hhX := defect_not_mem_next hXdef
  have hhY := defect_not_mem_next hYdef
  by_contra hnot
  have hXYle : (X ∩ Y).card ≤ 2 := by omega
  have hXYeq : (X ∩ Y).card = 2 := by
    exact Nat.le_antisymm hXYle (hinter hXF hYF)
  by_cases hlarge : ell + 2 < a + b
  · have hlower := prefix_inter_card_lower_bound (N := 4 * q)
      (ell := ell) (a := a) (b := b) (by omega)
      (A := X ∩ «prefix» (4 * q) ell)
      (B := Y ∩ «prefix» (4 * q) ell)
      inter_subset_right inter_subset_right hXcard hYcard
    have hsub :
        (X ∩ «prefix» (4 * q) ell) ∩
            (Y ∩ «prefix» (4 * q) ell) ⊆ X ∩ Y := by
      intro z hz
      simp only [mem_inter] at hz ⊢
      exact ⟨hz.1.1, hz.2.1⟩
    have hc := card_le_card hsub
    omega
  · have hsmall : a + b ≤ ell + 1 := by omega
    let PX := X ∩ «prefix» (4 * q) ell
    let PY := Y ∩ «prefix» (4 * q) ell
    let CX := X ∩ tailAfter (4 * q) (ell + 1)
    let CY := Y ∩ tailAfter (4 * q) (ell + 1)
    have hPXs : PX ⊆ «prefix» (4 * q) ell := inter_subset_right
    have hPYs : PY ⊆ «prefix» (4 * q) ell := inter_subset_right
    have hPXcard : PX.card = a := hXcard
    have hPYcard : PY.card = b := hYcard
    have hCXmem : CX ∈ defectTails F ell a hN :=
      mem_defectTails.mpr ⟨X, hXD, rfl⟩
    have haell : a ≤ ell := by
      have hc := card_le_card hPXs
      rw [card_prefix (by omega)] at hc
      rw [hPXcard] at hc
      exact hc
    obtain ⟨PZ, hPZs, hPZcard, hPZinter⟩ :
        ∃ PZ : Finset (Fin (4 * q)),
          PZ ⊆ «prefix» (4 * q) ell ∧ PZ.card = a ∧
            (if a + b ≤ ell then (PZ ∩ PY).card = 0
             else (PZ ∩ PY).card ≤ 1) := by
      by_cases hab : a + b ≤ ell
      · obtain ⟨PZ, hPZs, hPZcard, hdisj⟩ :=
          exists_prefix_subset_disjoint (N := 4 * q) (ell := ell)
            (a := a) (by omega) PY hPYs (by simpa [hPYcard] using hab)
        exact ⟨PZ, hPZs, hPZcard, by
          simp [hab, disjoint_iff_inter_eq_empty.mp hdisj]⟩
      · obtain ⟨PZ, hPZs, hPZcard, hinter'⟩ :=
          exists_prefix_subset_card_inter_le_one
            (N := 4 * q) (ell := ell) (a := a) (b := b)
            (by omega) PY hPYs hPYcard haell hsmall
        exact ⟨PZ, hPZs, hPZcard, by simp [hab, hinter']⟩
    let Z := PZ ∪ CX
    have hCXs : CX ⊆ tailAfter (4 * q) ell := by
      intro z hz
      have hz' := mem_tailAfter.mp (inter_subset_right hz)
      exact mem_tailAfter.mpr (by omega)
    have hZD : Z ∈ defectLayer F ell a hN := by
      rw [defectLayer_eq_layerFromTails hinv (by
        rcases (mem_defectFamily.mp hXdef).2 with ⟨i, hiP, hiX, _⟩
        have : 0 < PX.card := card_pos.mpr ⟨i, mem_inter.mpr ⟨hiX, hiP⟩⟩
        simpa [hPXcard] using this)]
      exact mem_layerFromTails.mpr
        ⟨CX, hCXmem, PZ, hPZs, hPZcard, rfl⟩
    have hZF : Z ∈ F :=
      (mem_defectFamily.mp (mem_defectLayer.mp hZD).1).1
    have hhZ := defect_not_mem_next (mem_defectLayer.mp hZD).1
    have hprefixZY :
        (Z ∩ Y) ∩ «prefix» (4 * q) ell = PZ ∩ PY := by
      ext z
      simp only [Z, PY, mem_inter, mem_union]
      constructor
      · rintro ⟨⟨hzPZ | hzCX, hzY⟩, hzP⟩
        · exact ⟨hzPZ, hzY, hzP⟩
        · exact ((disjoint_left.mp
            (disjoint_prefix_tailAfter (4 * q) ell))
              hzP (hCXs hzCX)).elim
      · rintro ⟨hzPZ, hzY, hzP⟩
        exact ⟨⟨Or.inl hzPZ, hzY⟩, hzP⟩
    have htailZY :
        (Z ∩ Y) ∩ tailAfter (4 * q) ell = CX ∩ CY := by
      ext z
      simp only [Z, CY, mem_inter, mem_union]
      constructor
      · rintro ⟨⟨hzPZ | hzCX, hzY⟩, hzTail⟩
        · exact ((disjoint_left.mp
            (disjoint_prefix_tailAfter (4 * q) ell))
              (hPZs hzPZ) hzTail).elim
        · exact ⟨hzCX, hzY, inter_subset_right hzCX⟩
      · rintro ⟨hzCX, hzY, hzFar⟩
        refine ⟨⟨Or.inr hzCX, hzY⟩, ?_⟩
        have hzval := mem_tailAfter.mp hzFar
        exact mem_tailAfter.mpr (by omega)
    have hZYsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) (Z ∩ Y)
    rw [hprefixZY, htailZY] at hZYsplit
    have hXYprefix :
        (X ∩ Y) ∩ «prefix» (4 * q) ell = PX ∩ PY := by
      ext z
      simp [PX, PY, and_assoc, and_left_comm, and_comm]
    have hXYtail :
        (X ∩ Y) ∩ tailAfter (4 * q) ell = CX ∩ CY := by
      have hhXY : nextPoint hN ∉ X ∩ Y :=
        fun h ↦ hhX (mem_inter.mp h).1
      rw [inter_tail_eq_far_of_not_next hN hhXY]
      ext z
      simp [CX, CY, and_assoc, and_left_comm, and_comm]
    have hXYsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) (X ∩ Y)
    rw [hXYprefix, hXYtail, hXYeq] at hXYsplit
    have hfarLe : (CX ∩ CY).card ≤ 2 := by omega
    have hZYle : (Z ∩ Y).card ≤ 2 := by
      by_cases hab : a + b ≤ ell
      · simp [hab] at hPZinter
        calc
          (Z ∩ Y).card =
              (PZ ∩ PY).card + (CX ∩ CY).card := hZYsplit.symm
          _ = (CX ∩ CY).card := by rw [hPZinter]; simp
          _ ≤ 2 := hfarLe
      · have hpLower := prefix_inter_card_lower_bound (N := 4 * q)
          (ell := ell) (a := a) (b := b) (by omega)
          hPXs hPYs hPXcard hPYcard
        simp [hab] at hPZinter
        have hpPos : 1 ≤ (PX ∩ PY).card := by omega
        have hfarLeOne : (CX ∩ CY).card ≤ 1 := by omega
        calc
          (Z ∩ Y).card =
              (PZ ∩ PY).card + (CX ∩ CY).card := hZYsplit.symm
          _ ≤ 1 + 1 := Nat.add_le_add hPZinter hfarLeOne
          _ = 2 := rfl
    have hZYeq : (Z ∩ Y).card = 2 :=
      Nat.le_antisymm hZYle (hinter hZF hYF)
    have hfarPos : 0 < (CX ∩ CY).card := by
      by_cases hab : a + b ≤ ell
      · simp [hab] at hPZinter
        have hfarEq : (CX ∩ CY).card = 2 := by
          calc
            (CX ∩ CY).card = 0 + (CX ∩ CY).card := by omega
            _ = (PZ ∩ PY).card + (CX ∩ CY).card := by
              simp [hPZinter]
            _ = (Z ∩ Y).card := hZYsplit
            _ = 2 := hZYeq
        exact hfarEq ▸ by decide
      · simp [hab] at hPZinter
        have hsum :
            (PZ ∩ PY).card + (CX ∩ CY).card = 2 :=
          hZYsplit.trans hZYeq
        omega
    obtain ⟨z, hzfar⟩ := card_pos.mp hfarPos
    have hzZ : z ∈ Z := by
      exact mem_union_right _ (mem_inter.mp hzfar).1
    have hzY : z ∈ Y := by
      have hzCY : z ∈ CY := (mem_inter.mp hzfar).2
      exact (mem_inter.mp hzCY).1
    have hzval : ell + 1 ≤ z.val :=
      mem_tailAfter.mp (inter_subset_right (mem_inter.mp hzfar).1)
    let S := singletonLeftShift (nextPoint hN) z Z
    have hhz : nextPoint hN < z := by
      exact Fin.mk_lt_mk.mpr (by simpa using hzval)
    have hSF : S ∈ F :=
      hleft.shifted_mem hhz hZF hzZ hhZ
    have hshift :
        S = insert (nextPoint hN) (Z.erase z) := by
      change singletonLeftShift (nextPoint hN) z Z =
        insert (nextPoint hN) (Z.erase z)
      rw [singletonLeftShift_eq_transpose ⟨hzZ, hhZ⟩,
        setTranspose_eq_insert_erase ⟨hzZ, hhZ⟩]
    have hSY : S ∩ Y = (Z ∩ Y).erase z := by
      rw [hshift]
      ext w
      simp only [mem_inter, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hwz, hwZ⟩, hwY⟩
        · exact (hhY hwY).elim
        · exact ⟨hwz, hwZ, hwY⟩
      · rintro ⟨hwz, hwZ, hwY⟩
        exact ⟨Or.inr ⟨hwz, hwZ⟩, hwY⟩
    have hzInter : z ∈ Z ∩ Y := mem_inter.mpr ⟨hzZ, hzY⟩
    have : (S ∩ Y).card = 1 := by
      rw [hSY, card_erase_of_mem hzInter, hZYeq]
    have := hinter hSF hYF
    omega

private lemma two_le_inter_rightExchange_left
    {N : ℕ} {h i : Fin N} {X Y : Finset (Fin N)}
    (hiX : i ∈ X) (hhX : h ∉ X) (hhY : h ∉ Y)
    (hthree : 3 ≤ (X ∩ Y).card) :
    2 ≤ (rightExchange h i X ∩ Y).card := by
  have hsub :
      (X ∩ Y).erase i ⊆ rightExchange h i X ∩ Y := by
    intro z hz
    rcases mem_erase.mp hz with ⟨hzi, hzXY⟩
    rcases mem_inter.mp hzXY with ⟨hzX, hzY⟩
    exact mem_inter.mpr ⟨mem_rightExchange.mpr
      (Or.inr ⟨hzX, hzi⟩), hzY⟩
  have hc := card_le_card hsub
  by_cases hi : i ∈ X ∩ Y
  · rw [card_erase_of_mem hi] at hc
    omega
  · rw [erase_eq_of_notMem hi] at hc
    omega

private lemma two_le_inter_rightExchange_both
    {N : ℕ} {h i j : Fin N} {X Y : Finset (Fin N)}
    (hiX : i ∈ X) (hjY : j ∈ Y) (hhX : h ∉ X) (hhY : h ∉ Y)
    (hthree : 3 ≤ (X ∩ Y).card) :
    2 ≤ (rightExchange h i X ∩ rightExchange h j Y).card := by
  let R := ((X ∩ Y).erase i).erase j
  have hsub :
      insert h R ⊆ rightExchange h i X ∩ rightExchange h j Y := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hzR
    · exact mem_inter.mpr ⟨by simp, by simp⟩
    · rcases mem_erase.mp hzR with ⟨hzj, hzRi⟩
      rcases mem_erase.mp hzRi with ⟨hzi, hzXY⟩
      rcases mem_inter.mp hzXY with ⟨hzX, hzY⟩
      exact mem_inter.mpr
        ⟨mem_rightExchange.mpr (Or.inr ⟨hzX, hzi⟩),
         mem_rightExchange.mpr (Or.inr ⟨hzY, hzj⟩)⟩
  have hhR : h ∉ R := by
    intro hh
    have hhXY : h ∈ X ∩ Y := (mem_erase.mp (mem_erase.mp hh).2).2
    exact hhX (mem_inter.mp hhXY).1
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hhR] at hc
  have hR : (X ∩ Y).card - 2 ≤ R.card := by
    dsimp [R]
    have h₁ : (X ∩ Y).card - 1 ≤ ((X ∩ Y).erase i).card := by
      by_cases hi : i ∈ X ∩ Y
      · rw [card_erase_of_mem hi]
      · rw [erase_eq_of_notMem hi]
        omega
    have h₂ :
        ((X ∩ Y).erase i).card - 1 ≤
          (((X ∩ Y).erase i).erase j).card := by
      by_cases hj : j ∈ (X ∩ Y).erase i
      · rw [card_erase_of_mem hj]
      · rw [erase_eq_of_notMem hj]
        omega
    omega
  omega

private lemma uniform_exchangeLayer
    {N ell a k : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    (hunif : Uniform k F) :
    Uniform k (exchangeLayer F ell a hN) := by
  intro E hE
  obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
    exchangeLayer_exists_source hinv ha hE
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF := (mem_defectFamily.mp hXdef).1
  exact (card_rightExchange hiX (defect_not_mem_next hXdef)).trans
    (hunif hXF)

noncomputable def replaceDefectLevel {N : ℕ}
    (F D E : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) :=
  (F \ D) ∪ E

private lemma uniform_replaceDefectLevel
    {N k : ℕ} {F D E : Finset (Finset (Fin N))}
    (hF : Uniform k F) (hE : Uniform k E) :
    Uniform k (replaceDefectLevel F D E) := by
  intro A hA
  rcases mem_union.mp hA with hAF | hAE
  · exact hF (mem_sdiff.mp hAF).1
  · exact hE hAE

private lemma twoIntersecting_noncentral_replacement
    {q ell a b : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = ell + 2) (hane : a ≠ b) :
    TwoIntersecting
      (replaceDefectLevel F
        (defectLayer F ell b (by omega))
        (exchangeLayer F ell a (by omega))) := by
  intro A B hA hB
  rcases mem_union.mp hA with hAF | hAE
  · rcases mem_union.mp hB with hBF | hBE
    · exact hinter (mem_sdiff.mp hAF).1 (mem_sdiff.mp hBF).1
    · rw [inter_comm]
      have hBF' := (mem_sdiff.mp hAF).1
      have hBDnot := (mem_sdiff.mp hAF).2
      by_cases hBdef : A ∈ defectFamily F ell (by omega)
      · let j := (A ∩ «prefix» (4 * q) ell).card
        have hADj : A ∈ defectLayer F ell j (by omega) :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        have hjne : j ≠ b := by
          intro e
          apply hBDnot
          simpa [e] using hADj
        obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
          exchangeLayer_exists_source hinv ha hBE
        exact two_le_inter_rightExchange_left hiX
          (defect_not_mem_next (mem_defectLayer.mp hXD).1)
          (defect_not_mem_next hBdef)
          (defect_inter_card_three hell hinv hinter hleft
            hXD hADj (by omega))
      · exact exchange_cross_nondefect hinv ha hinter hBE hBF' hBdef
  · rcases mem_union.mp hB with hBF | hBE
    · have hBF' := (mem_sdiff.mp hBF).1
      have hBDnot := (mem_sdiff.mp hBF).2
      by_cases hBdef : B ∈ defectFamily F ell (by omega)
      · let j := (B ∩ «prefix» (4 * q) ell).card
        have hBDj : B ∈ defectLayer F ell j (by omega) :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        have hjne : j ≠ b := by
          intro e
          apply hBDnot
          simpa [e] using hBDj
        obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
          exchangeLayer_exists_source hinv ha hAE
        exact two_le_inter_rightExchange_left hiX
          (defect_not_mem_next (mem_defectLayer.mp hXD).1)
          (defect_not_mem_next hBdef)
          (defect_inter_card_three hell hinv hinter hleft
            hXD hBDj (by omega))
      · exact exchange_cross_nondefect hinv ha hinter hAE hBF' hBdef
    · obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
        exchangeLayer_exists_source hinv ha hAE
      obtain ⟨Y, hYD, j, hjP, hjY, rfl⟩ :=
        exchangeLayer_exists_source hinv ha hBE
      exact two_le_inter_rightExchange_both hiX hjY
        (defect_not_mem_next (mem_defectLayer.mp hXD).1)
        (defect_not_mem_next (mem_defectLayer.mp hYD).1)
        (defect_inter_card_three hell hinv hinter hleft hXD hYD
          (by omega))

private lemma card_replaceDefectLevel
    {N : ℕ} {F D E : Finset (Finset (Fin N))}
    (hD : D ⊆ F) (hE : Disjoint E F) :
    (replaceDefectLevel F D E).card = F.card - D.card + E.card := by
  rw [replaceDefectLevel, card_union_of_disjoint]
  · rw [card_sdiff_of_subset hD, add_comm]
  · exact hE.symm.mono_left sdiff_subset

private lemma defectLayer_subset_family
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N} :
    defectLayer F ell a hN ⊆ F := by
  intro A hA
  exact (mem_defectFamily.mp (mem_defectLayer.mp hA).1).1

private lemma noncentral_defectLayer_empty
    {q ell a : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F)
    (ha : 2 ≤ a) (hale : a ≤ ell)
    (hcentral : 2 * a ≠ ell + 2) :
    defectLayer F ell a (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  let b := ell + 2 - a
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hble : b ≤ ell := by dsimp [b]; omega
  have hab : a + b = ell + 2 := by dsimp [b]; omega
  have hane : a ≠ b := by
    intro e
    apply hcentral
    omega
  by_contra hne
  have hDaPos : 0 < (defectTails F ell a hN).card := by
    have hDapos : 0 < (defectLayer F ell a hN).card := card_pos.mpr (by
      simpa only [nonempty_iff_ne_empty] using hne)
    rw [card_defectLayer hinv (by omega)] at hDapos
    exact Nat.pos_of_mul_pos_left hDapos
  let H₁ := replaceDefectLevel F
    (defectLayer F ell b hN) (exchangeLayer F ell a hN)
  let H₂ := replaceDefectLevel F
    (defectLayer F ell a hN) (exchangeLayer F ell b hN)
  have hH₁unif : Uniform (2 * q) H₁ :=
    uniform_replaceDefectLevel hunif
      (uniform_exchangeLayer hinv (by omega) hunif)
  have hH₂unif : Uniform (2 * q) H₂ :=
    uniform_replaceDefectLevel hunif
      (uniform_exchangeLayer hinv (by omega) hunif)
  have hH₁inter : TwoIntersecting H₁ :=
    twoIntersecting_noncentral_replacement hell hinv hinter hleft
      (by omega) (by omega) hab hane
  have hH₂inter : TwoIntersecting H₂ :=
    twoIntersecting_noncentral_replacement hell hinv hinter hleft
      (by omega) (by omega) (by omega) hane.symm
  have hH₁max := hmax H₁ hH₁unif hH₁inter
  have hH₂max := hmax H₂ hH₂unif hH₂inter
  have hH₁card := card_replaceDefectLevel
    (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := b)
      (F := F) (hN := hN))
    (exchangeLayer_disjoint_family (N := 4 * q) (ell := ell) (a := a)
      (F := F) (hN := hN) hinv (by omega))
  have hH₂card := card_replaceDefectLevel
    (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := a)
      (F := F) (hN := hN))
    (exchangeLayer_disjoint_family (N := 4 * q) (ell := ell) (a := b)
      (F := F) (hN := hN) hinv (by omega))
  have hE₁D₂ :
      (exchangeLayer F ell a hN).card ≤
        (defectLayer F ell b hN).card := by
    have hDcard := card_le_card
      (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := b)
        (F := F) (hN := hN))
    rw [hH₁card] at hH₁max
    omega
  have hE₂D₁ :
      (exchangeLayer F ell b hN).card ≤
        (defectLayer F ell a hN).card := by
    have hDcard := card_le_card
      (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := a)
        (F := F) (hN := hN))
    rw [hH₂card] at hH₂max
    omega
  rw [card_exchangeLayer, card_defectLayer hinv (by omega)] at hE₁D₂
  rw [card_exchangeLayer, card_defectLayer hinv (by omega)] at hE₂D₁
  have hDbPos : 0 < (defectTails F ell b hN).card := by
    by_contra hz
    have : (defectTails F ell b hN).card = 0 := by omega
    rw [this, mul_zero] at hE₁D₂
    have hchoose : 0 < Nat.choose ell (a - 1) :=
      Nat.choose_pos (by omega)
    have hprod :
        0 < Nat.choose ell (a - 1) *
          (defectTails F ell a hN).card :=
      Nat.mul_pos hchoose hDaPos
    omega
  have hcross := mul_mul_le_mul_mul_of_cross_bounds
    hDaPos hDbPos hE₁D₂ hE₂D₁
  have hstrict :=
    choose_product_lt_pred_product_of_add_eq
      (n := ell) (a := a) (b := b) (by omega) (by omega) hab
  have hcross' :
      Nat.choose ell (a - 1) * Nat.choose ell (b - 1) ≤
        Nat.choose ell a * Nat.choose ell b := by
    simpa [Nat.mul_comm] using hcross
  exact (Nat.not_lt_of_ge hcross') hstrict

private lemma exists_incidence_ge_average_on {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) (P : Finset (Finset α)) (r : ℕ)
    (hsub : ∀ C ∈ P, C ⊆ T)
    (hcard : ∀ C ∈ P, C.card = r) :
    ∃ z ∈ T, T.card * (P.filter fun C ↦ z ∈ C).card ≥ r * P.card := by
  have hdouble :
      ∑ z ∈ T, (P.filter fun C ↦ z ∈ C).card = r * P.card := by
    calc
      ∑ z ∈ T, (P.filter fun C ↦ z ∈ C).card =
          ∑ z ∈ T, ∑ C ∈ P, if z ∈ C then (1 : ℕ) else 0 := by
            apply sum_congr rfl
            intro z hz
            simp
      _ = ∑ C ∈ P, ∑ z ∈ T, if z ∈ C then (1 : ℕ) else 0 := by
            rw [sum_comm]
      _ = ∑ C ∈ P, C.card := by
            apply sum_congr rfl
            intro C hC
            have hs := hsub C hC
            calc
              ∑ z ∈ T, (if z ∈ C then (1 : ℕ) else 0) =
                  (T.filter fun z ↦ z ∈ C).card := by
                    rw [Finset.sum_boole (R := ℕ)]
                    simp
              _ = C.card := by
                rw [filter_mem_eq_inter, inter_eq_right.mpr hs]
      _ = ∑ _C ∈ P, r := by
            apply sum_congr rfl
            intro C hC
            exact hcard C hC
      _ = r * P.card := by simp [Nat.mul_comm]
  by_contra h
  push_neg at h
  have hlt :
      ∑ z ∈ T, T.card * (P.filter fun C ↦ z ∈ C).card <
        ∑ _z ∈ T, r * P.card := by
    exact sum_lt_sum_of_nonempty hT
      (fun z hz ↦ h z hz)
  rw [← mul_sum, hdouble] at hlt
  simp at hlt

/-- Exchanges generated by an explicitly supplied subfamily of far tails. -/
noncomputable def exchangeFromTails {N : ℕ}
    (ell a : ℕ) (hN : ell < N) (P : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  layerFromTails N ell (a - 1)
    (P.image fun C ↦ insert (nextPoint hN) C)

private lemma exchangeFromTails_subset_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    exchangeFromTails ell a hN P ⊆ exchangeLayer F ell a hN := by
  intro E hE
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, rfl⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  exact mem_layerFromTails.mpr
    ⟨insert (nextPoint hN) C,
      mem_image.mpr ⟨C, hP hCP, rfl⟩,
      B, hBP, hBcard, rfl⟩

private lemma card_exchangeFromTails
    {N ell a : ℕ} {hN : ell < N} {P : Finset (Finset (Fin N))}
    (hP : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1)) :
    (exchangeFromTails ell a hN P).card =
      Nat.choose ell (a - 1) * P.card := by
  have hPtail :
      ∀ C ∈ P.image (fun C ↦ insert (nextPoint hN) C),
        C ⊆ tailAfter N ell := by
    intro C hC
    rcases mem_image.mp hC with ⟨D, hDP, rfl⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hxD
    · exact nextPoint_mem_tailAfter hN
    · have := mem_tailAfter.mp (hP D hDP hxD)
      exact mem_tailAfter.mpr (by omega)
  rw [exchangeFromTails, card_layerFromTails hPtail, card_prefix hN.le,
    card_image_iff.mpr (insert_next_injective_on_farTails hN P hP)]

private lemma card_defectLayer_from_tail_subfamily
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    (layerFromTails N ell a P).card = Nat.choose ell a * P.card := by
  rw [card_layerFromTails (fun C hC ↦
    (defectTails_subset_tailAfter (hP hC)).trans ?_), card_prefix hN.le]
  intro x hx
  simp only [mem_tailAfter] at hx ⊢
  omega

private lemma layerFromTails_subset_defectLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    layerFromTails N ell a P ⊆ defectLayer F ell a hN := by
  rw [defectLayer_eq_layerFromTails hinv ha]
  intro A hA
  rcases mem_layerFromTails.mp hA with
    ⟨C, hCP, B, hBP, hBcard, rfl⟩
  exact mem_layerFromTails.mpr
    ⟨C, hP hCP, B, hBP, hBcard, rfl⟩

private lemma twoIntersecting_central_replacement
    {q ell i : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    (hi : 0 < i) (hicentral : 2 * i = ell + 2)
    {P Q : Finset (Finset (Fin (4 * q)))}
    (hP : P = defectTails F ell i (by omega))
    (hQP : Q ⊆ P)
    {z : Fin (4 * q)} (hzQ : ∀ C ∈ Q, z ∈ C) :
    TwoIntersecting
      (replaceDefectLevel F
        (layerFromTails (4 * q) ell i (P \ Q))
        (exchangeFromTails ell i (by omega) Q)) := by
  let hN : ell < 4 * q := by omega
  have hQdef :
      Q ⊆ defectTails F ell i hN := by simpa [hP] using hQP
  have hGsub :
      exchangeFromTails ell i hN Q ⊆ exchangeLayer F ell i hN :=
    exchangeFromTails_subset_exchangeLayer hQdef
  have hRsub :
      layerFromTails (4 * q) ell i (P \ Q) ⊆
        defectLayer F ell i hN := by
    apply layerFromTails_subset_defectLayer hinv hi
    intro C hC
    have hCP : C ∈ P := (mem_sdiff.mp hC).1
    simpa [hP] using hCP
  intro A B hA hB
  rcases mem_union.mp hA with hAF | hAG
  · rcases mem_union.mp hB with hBF | hBG
    · exact hinter (mem_sdiff.mp hAF).1 (mem_sdiff.mp hBF).1
    · rw [inter_comm]
      have hAF' := (mem_sdiff.mp hAF).1
      have hARnot := (mem_sdiff.mp hAF).2
      have hBE := hGsub hBG
      by_cases hAdef : A ∈ defectFamily F ell hN
      · let j := (A ∩ «prefix» (4 * q) ell).card
        have hADj : A ∈ defectLayer F ell j hN :=
          mem_defectLayer.mpr ⟨hAdef, rfl⟩
        by_cases hji : j = i
        · have hADi : A ∈ defectLayer F ell i hN := hji ▸ hADj
          have hAtailP :
              A ∩ tailAfter (4 * q) (ell + 1) ∈ P := by
            rw [hP]
            exact mem_defectTails.mpr ⟨A, hADi, rfl⟩
          have hAtailQ :
              A ∩ tailAfter (4 * q) (ell + 1) ∈ Q := by
            by_contra hnQ
            apply hARnot
            apply mem_layerFromTails.mpr
            refine ⟨A ∩ tailAfter (4 * q) (ell + 1),
              mem_sdiff.mpr ⟨hAtailP, hnQ⟩,
              A ∩ «prefix» (4 * q) ell, inter_subset_right,
              (mem_defectLayer.mp hADi).2, ?_⟩
            rw [← inter_tail_eq_far_of_not_next hN
              (defect_not_mem_next hAdef)]
            exact inter_prefix_union_inter_tailAfter A
          rcases mem_layerFromTails.mp hBG with
            ⟨D, hD, BE, hBEP, hBEcard, rfl⟩
          rcases mem_image.mp hD with ⟨CE, hCEQ, rfl⟩
          have hzA : z ∈ A := inter_subset_left
            (hzQ _ hAtailQ)
          have hzCE : z ∈ CE := hzQ _ hCEQ
          have hzTail := defectTails_subset_tailAfter
            (hQdef hCEQ) hzCE
          have hApreS : A ∩ «prefix» (4 * q) ell ⊆
              «prefix» (4 * q) ell := inter_subset_right
          have hlower := prefix_inter_card_lower_bound
            (N := 4 * q) (ell := ell) (a := i - 1) (b := i)
            (by omega) hBEP hApreS hBEcard
            (mem_defectLayer.mp hADi).2
          have hprePos :
              0 < (BE ∩ (A ∩ «prefix» (4 * q) ell)).card := by
            omega
          obtain ⟨w, hw⟩ := card_pos.mp hprePos
          have hwBE := (mem_inter.mp hw).1
          have hwA := (mem_inter.mp (mem_inter.mp hw).2).1
          have hwPre := (mem_inter.mp (mem_inter.mp hw).2).2
          have hwz : w ≠ z := by
            intro e
            subst w
            have hwlt := mem_prefix.mp hwPre
            have hzge := mem_tailAfter.mp hzTail
            omega
          have hpair :
              ({w, z} : Finset (Fin (4 * q))) ⊆
                ((BE ∪ insert (nextPoint hN) CE) ∩ A) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact mem_inter.mpr ⟨mem_union_left _
                hwBE, hwA⟩
            · exact mem_inter.mpr ⟨mem_union_right _
                (mem_insert_of_mem hzCE), hzA⟩
          have hc := card_le_card hpair
          simpa [hwz] using hc
        · obtain ⟨X, hXD, x, hxP, hxX, rfl⟩ :=
            exchangeLayer_exists_source hinv hi hBE
          exact two_le_inter_rightExchange_left hxX
            (defect_not_mem_next (mem_defectLayer.mp hXD).1)
            (defect_not_mem_next hAdef)
            (defect_inter_card_three hell hinv hinter hleft
              hXD hADj (by omega))
      · exact exchange_cross_nondefect hinv hi hinter hBE hAF' hAdef
  · rcases mem_union.mp hB with hBF | hBG
    · have hBF' := (mem_sdiff.mp hBF).1
      have hBRnot := (mem_sdiff.mp hBF).2
      have hAE := hGsub hAG
      by_cases hBdef : B ∈ defectFamily F ell hN
      · let j := (B ∩ «prefix» (4 * q) ell).card
        have hBDj : B ∈ defectLayer F ell j hN :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        by_cases hji : j = i
        · have hBDi : B ∈ defectLayer F ell i hN := hji ▸ hBDj
          have hBtailP :
              B ∩ tailAfter (4 * q) (ell + 1) ∈ P := by
            rw [hP]
            exact mem_defectTails.mpr ⟨B, hBDi, rfl⟩
          have hBtailQ :
              B ∩ tailAfter (4 * q) (ell + 1) ∈ Q := by
            by_contra hnQ
            apply hBRnot
            apply mem_layerFromTails.mpr
            refine ⟨B ∩ tailAfter (4 * q) (ell + 1),
              mem_sdiff.mpr ⟨hBtailP, hnQ⟩,
              B ∩ «prefix» (4 * q) ell, inter_subset_right,
              (mem_defectLayer.mp hBDi).2, ?_⟩
            rw [← inter_tail_eq_far_of_not_next hN
              (defect_not_mem_next hBdef)]
            exact inter_prefix_union_inter_tailAfter B
          rcases mem_layerFromTails.mp hAG with
            ⟨D, hD, BA, hBAP, hBAcard, rfl⟩
          rcases mem_image.mp hD with ⟨CA, hCAQ, rfl⟩
          have hzB : z ∈ B := inter_subset_left
            (hzQ _ hBtailQ)
          have hzCA : z ∈ CA := hzQ _ hCAQ
          have hzTail := defectTails_subset_tailAfter
            (hQdef hCAQ) hzCA
          have hBpreS : B ∩ «prefix» (4 * q) ell ⊆
              «prefix» (4 * q) ell := inter_subset_right
          have hlower := prefix_inter_card_lower_bound
            (N := 4 * q) (ell := ell) (a := i - 1) (b := i)
            (by omega) hBAP hBpreS hBAcard
            (mem_defectLayer.mp hBDi).2
          have hprePos :
              0 < (BA ∩ (B ∩ «prefix» (4 * q) ell)).card := by
            omega
          obtain ⟨w, hw⟩ := card_pos.mp hprePos
          have hwBA := (mem_inter.mp hw).1
          have hwB := (mem_inter.mp (mem_inter.mp hw).2).1
          have hwPre := (mem_inter.mp (mem_inter.mp hw).2).2
          have hwz : w ≠ z := by
            intro e
            subst w
            have hwlt := mem_prefix.mp hwPre
            have hzge := mem_tailAfter.mp hzTail
            omega
          have hpair :
              ({w, z} : Finset (Fin (4 * q))) ⊆
                ((BA ∪ insert (nextPoint hN) CA) ∩ B) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact mem_inter.mpr ⟨mem_union_left _ hwBA, hwB⟩
            · exact mem_inter.mpr ⟨mem_union_right _
                (mem_insert_of_mem hzCA), hzB⟩
          have hc := card_le_card hpair
          simpa [hwz] using hc
        · obtain ⟨X, hXD, x, hxP, hxX, rfl⟩ :=
            exchangeLayer_exists_source hinv hi hAE
          exact two_le_inter_rightExchange_left hxX
            (defect_not_mem_next (mem_defectLayer.mp hXD).1)
            (defect_not_mem_next hBdef)
            (defect_inter_card_three hell hinv hinter hleft
              hXD hBDj (by omega))
      · exact exchange_cross_nondefect hinv hi hinter hAE hBF' hBdef
    · rcases mem_layerFromTails.mp hAG with
        ⟨D₁, hD₁, B₁, hB₁P, hB₁card, rfl⟩
      rcases mem_image.mp hD₁ with ⟨C₁, hC₁Q, rfl⟩
      rcases mem_layerFromTails.mp hBG with
        ⟨D₂, hD₂, B₂, hB₂P, hB₂card, rfl⟩
      rcases mem_image.mp hD₂ with ⟨C₂, hC₂Q, rfl⟩
      have hz₁ : z ∈ C₁ := hzQ _ hC₁Q
      have hz₂ : z ∈ C₂ := hzQ _ hC₂Q
      have hzh : z ≠ nextPoint hN := by
        intro e
        subst z
        have hfar := defectTails_subset_tailAfter
          (hQdef hC₁Q) hz₁
        exact nextPoint_not_mem_farTail hN hfar
      have hpair :
          ({nextPoint hN, z} : Finset (Fin (4 * q))) ⊆
            ((B₁ ∪ insert (nextPoint hN) C₁) ∩
              (B₂ ∪ insert (nextPoint hN) C₂)) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp
        · exact mem_inter.mpr
            ⟨mem_union_right _ (mem_insert_of_mem hz₁),
             mem_union_right _ (mem_insert_of_mem hz₂)⟩
      have hc := card_le_card hpair
      simpa [hzh, Ne.symm hzh] using hc

private lemma central_defectLayer_empty
    {q ell i : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F)
    (hi : 2 ≤ i) (hicentral : 2 * i = ell + 2) :
    defectLayer F ell i (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  let P := defectTails F ell i hN
  by_contra hne
  have hDpos : 0 < (defectLayer F ell i hN).card :=
    card_pos.mpr (by simpa only [nonempty_iff_ne_empty] using hne)
  have hPpos : 0 < P.card := by
    rw [card_defectLayer hinv (by omega)] at hDpos
    dsimp only [P]
    exact Nat.pos_of_mul_pos_left hDpos
  have hPsub : ∀ C ∈ P, C ⊆ tailAfter (4 * q) (ell + 1) := by
    intro C hC
    exact defectTails_subset_tailAfter hC
  have hPcard : ∀ C ∈ P, C.card = 2 * q - i := by
    intro C hC
    rcases mem_defectTails.mp hC with ⟨X, hXD, rfl⟩
    have hXdef := (mem_defectLayer.mp hXD).1
    have hXpre := (mem_defectLayer.mp hXD).2
    have hXmem := (mem_defectFamily.mp hXdef).1
    have hsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) X
    rw [inter_tail_eq_far_of_not_next hN (defect_not_mem_next hXdef),
      hXpre, hunif hXmem] at hsplit
    omega
  let T := tailAfter (4 * q) (ell + 1)
  have hTcard : T.card = 4 * q - (ell + 1) := by
    dsimp only [T]
    exact card_tailAfter (by omega)
  have hTnonempty : T.Nonempty := by
    apply card_pos.mp
    rw [hTcard]
    omega
  obtain ⟨z, hzT, hzavg⟩ :=
    exists_incidence_ge_average_on T hTnonempty P (2 * q - i)
      hPsub hPcard
  let Q := P.filter fun C ↦ z ∈ C
  have hQP : Q ⊆ P := filter_subset _ _
  have hzQ : ∀ C ∈ Q, z ∈ C := by
    intro C hC
    exact (mem_filter.mp hC).2
  have hzavg' : T.card * Q.card ≥ (2 * q - i) * P.card := by
    simpa only [Q] using hzavg
  let R := layerFromTails (4 * q) ell i (P \ Q)
  let E := exchangeFromTails ell i hN Q
  have hRsubD : R ⊆ defectLayer F ell i hN := by
    apply layerFromTails_subset_defectLayer hinv (by omega)
    intro C hC
    exact (mem_sdiff.mp hC).1
  have hRsubF : R ⊆ F :=
    hRsubD.trans defectLayer_subset_family
  have hEsub : E ⊆ exchangeLayer F ell i hN := by
    exact exchangeFromTails_subset_exchangeLayer hQP
  let H := replaceDefectLevel F R E
  have hHunif : Uniform (2 * q) H := by
    apply uniform_replaceDefectLevel hunif
    intro A hA
    exact uniform_exchangeLayer hinv (by omega) hunif (hEsub hA)
  have hHinter : TwoIntersecting H := by
    exact twoIntersecting_central_replacement hell hinv hinter hleft
      (by omega) hicentral (P := P) (Q := Q) rfl hQP hzQ
  have hEdisj : Disjoint E F :=
    (exchangeLayer_disjoint_family hinv (by omega)).mono_left hEsub
  have hHcard : H.card = F.card - R.card + E.card :=
    card_replaceDefectLevel hRsubF hEdisj
  have hHmax := hmax H hHunif hHinter
  have hRleF : R.card ≤ F.card := card_le_card hRsubF
  have hEleR : E.card ≤ R.card := by
    rw [hHcard] at hHmax
    omega
  have hRcard : R.card = Nat.choose ell i * (P \ Q).card := by
    dsimp only [R]
    exact card_defectLayer_from_tail_subfamily hinv (by omega)
      (fun C hC ↦ (mem_sdiff.mp hC).1)
  have hEcard : E.card = Nat.choose ell (i - 1) * Q.card := by
    dsimp only [E]
    exact card_exchangeFromTails (fun C hC ↦ hPsub C (hQP hC))
  have hPQcard : (P \ Q).card = P.card - Q.card :=
    card_sdiff_of_subset hQP
  rw [hRcard, hEcard, hPQcard] at hEleR
  have hpascal :
      Nat.choose (ell + 1) i =
        Nat.choose ell (i - 1) + Nat.choose ell i := by
    have hipred : i - 1 + 1 = i := by omega
    simpa only [hipred] using (Nat.choose_succ_succ' ell (i - 1))
  have hcount :
      Nat.choose (ell + 1) i * Q.card ≤
        Nat.choose ell i * P.card := by
    rw [hpascal, add_mul]
    have hQleP : Q.card ≤ P.card := card_le_card hQP
    have hsplit :
        Nat.choose ell i * (P.card - Q.card) +
            Nat.choose ell i * Q.card =
          Nat.choose ell i * P.card := by
      rw [← mul_add, Nat.sub_add_cancel hQleP]
    exact le_trans (Nat.add_le_add_right hEleR _)
      (le_of_eq hsplit)
  have hiell : i ≤ ell := by omega
  have hTvalue : T.card = 2 * (2 * q - i) + 1 := by
    rw [hTcard]
    omega
  have hsmallValue : ell + 1 - i = i - 1 := by omega
  have hlargeValue : ell + 1 = 2 * i - 1 := by omega
  have hcoef :
      T.card * (ell + 1 - i) < (2 * q - i) * (ell + 1) := by
    rw [hTvalue, hsmallValue, hlargeValue]
    have hiq : i ≤ q := by omega
    have hi2q : i ≤ 2 * q := by omega
    have hqi : 2 * q - i + i = 2 * q := Nat.sub_add_cancel hi2q
    have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
    have hlt : i - 1 < 2 * q - i := by omega
    calc
      (2 * (2 * q - i) + 1) * (i - 1) =
          2 * (2 * q - i) * (i - 1) + (i - 1) := by ring
      _ < 2 * (2 * q - i) * (i - 1) + (2 * q - i) :=
        Nat.add_lt_add_left hlt _
      _ = (2 * q - i) * (2 * i - 1) := by
        have hinner : 2 * (i - 1) + 1 = 2 * i - 1 := by omega
        calc
          2 * (2 * q - i) * (i - 1) + (2 * q - i) =
              (2 * q - i) * (2 * (i - 1) + 1) := by ring
          _ = (2 * q - i) * (2 * i - 1) := by rw [hinner]
  have hcoefScaled := Nat.mul_lt_mul_of_pos_right hcoef hPpos
  have havgScaled := Nat.mul_le_mul_right (ell + 1) hzavg'
  have hcross :
      P.card * (ell + 1 - i) < Q.card * (ell + 1) := by
    apply Nat.lt_of_mul_lt_mul_left (a := T.card)
    calc
      T.card * (P.card * (ell + 1 - i)) =
          (T.card * (ell + 1 - i)) * P.card := by ac_rfl
      _ < ((2 * q - i) * (ell + 1)) * P.card := hcoefScaled
      _ = ((2 * q - i) * P.card) * (ell + 1) := by ac_rfl
      _ ≤ (T.card * Q.card) * (ell + 1) := havgScaled
      _ = T.card * (Q.card * (ell + 1)) := by ac_rfl
  have hstrict := choose_succ_left_mul_lt_of_cross_lt hiell hcross
  exact (Nat.not_lt_of_ge hcount) hstrict

private lemma rightExchange_mem_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    {X : Finset (Fin N)}
    (hXD : X ∈ defectLayer F ell a hN)
    {i : Fin N} (hiP : i ∈ «prefix» N ell) (hiX : i ∈ X) :
    rightExchange (nextPoint hN) i X ∈ exchangeLayer F ell a hN := by
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hhX := defect_not_mem_next hXdef
  apply mem_layerFromTails.mpr
  refine ⟨insert (nextPoint hN) (X ∩ tailAfter N (ell + 1)),
    mem_image.mpr ⟨X ∩ tailAfter N (ell + 1),
      mem_defectTails.mpr ⟨X, hXD, rfl⟩, rfl⟩,
    (X ∩ «prefix» N ell).erase i, ?_, ?_, ?_⟩
  · exact (erase_subset _ _).trans inter_subset_right
  · have hiInter : i ∈ X ∩ «prefix» N ell :=
      mem_inter.mpr ⟨hiX, hiP⟩
    rw [card_erase_of_mem hiInter, hXcard]
  · ext x
    simp only [mem_union, mem_erase, mem_inter, mem_prefix, mem_insert,
      mem_tailAfter, mem_rightExchange, nextPoint_val]
    constructor
    · rintro (⟨hxi, hxX, hxlt⟩ | rfl | ⟨hxX, hxge⟩)
      · exact Or.inr ⟨hxX, hxi⟩
      · exact Or.inl rfl
      · right
        refine ⟨hxX, ?_⟩
        intro hxi
        subst x
        have := mem_prefix.mp hiP
        omega
    · rintro (rfl | ⟨hxX, hxi⟩)
      · exact Or.inr (Or.inl rfl)
      · by_cases hxlt : x.val < ell
        · exact Or.inl ⟨hxi, hxX, hxlt⟩
        · right
          right
          refine ⟨hxX, ?_⟩
          by_cases hxeq : x.val = ell
          · have hxnext : x = nextPoint hN := Fin.ext hxeq
            exact (hhX (hxnext ▸ hxX)).elim
          · omega

private lemma low_defectLayer_empty
    {q ell : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    defectLayer F ell 1 (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  by_contra hne
  obtain ⟨X, hXD⟩ :
      ∃ X, X ∈ defectLayer F ell 1 hN := by
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨X, hX⟩
    exact ⟨X, hX⟩
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF := (mem_defectFamily.mp hXdef).1
  rcases (mem_defectFamily.mp hXdef).2 with
    ⟨i, hiP, hiX, hhX, hiMissing⟩
  let E := rightExchange (nextPoint hN) i X
  have hEexchange : E ∈ exchangeLayer F ell 1 hN := by
    exact rightExchange_mem_exchangeLayer hXD hiP hiX
  have hEcard : E.card = 2 * q := by
    dsimp only [E]
    exact (card_rightExchange hiX hhX).trans (hunif hXF)
  have hEinterF : ∀ {Y}, Y ∈ F → 2 ≤ (E ∩ Y).card := by
    intro Y hYF
    by_cases hYdef : Y ∈ defectFamily F ell hN
    · let j := (Y ∩ «prefix» (4 * q) ell).card
      have hYDj : Y ∈ defectLayer F ell j hN :=
        mem_defectLayer.mpr ⟨hYdef, rfl⟩
      have hjpos : 0 < j := by
        rcases (mem_defectFamily.mp hYdef).2 with
          ⟨w, hwP, hwY, _hwNext, _hwMissing⟩
        exact card_pos.mpr ⟨w, mem_inter.mpr ⟨hwY, hwP⟩⟩
      have hjle : j ≤ ell := by
        have hc := card_le_card
          (inter_subset_right : Y ∩ «prefix» (4 * q) ell ⊆
            «prefix» (4 * q) ell)
        rw [card_prefix (by omega)] at hc
        exact hc
      exact two_le_inter_rightExchange_left hiX hhX
        (defect_not_mem_next hYdef)
        (defect_inter_card_three hell hinv hinter hleft hXD hYDj
          (by omega))
    · exact exchange_cross_nondefect hinv (by omega) hinter
        hEexchange hYF hYdef
  let H := insert E F
  have hHunif : Uniform (2 * q) H := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hAF
    · exact hEcard
    · exact hunif hAF
  have hHinter : TwoIntersecting H := by
    intro A B hA hB
    rcases mem_insert.mp hA with rfl | hAF
    · rcases mem_insert.mp hB with rfl | hBF
      · simpa [hEcard] using (show 2 ≤ 2 * q by omega)
      · exact hEinterF hBF
    · rcases mem_insert.mp hB with rfl | hBF
      · rw [inter_comm]
        exact hEinterF hAF
      · exact hinter hAF hBF
  have hHmax := hmax H hHunif hHinter
  have hEmissing : E ∉ F := hiMissing
  have hHcard : H.card = F.card + 1 := by
    dsimp only [H]
    rw [card_insert_of_notMem hEmissing]
  rw [hHcard] at hHmax
  omega

private lemma all_defects_empty
    {q ell : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    defectFamily F ell (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hXD
  let a := (X ∩ «prefix» (4 * q) ell).card
  have hXDa : X ∈ defectLayer F ell a hN :=
    mem_defectLayer.mpr ⟨hXD, rfl⟩
  have hapos : 0 < a := by
    rcases (mem_defectFamily.mp hXD).2 with
      ⟨i, hiP, hiX, _hiNext, _hiMissing⟩
    exact card_pos.mpr ⟨i, mem_inter.mpr ⟨hiX, hiP⟩⟩
  have hale : a ≤ ell := by
    have hc := card_le_card
      (inter_subset_right : X ∩ «prefix» (4 * q) ell ⊆
        «prefix» (4 * q) ell)
    rw [card_prefix (by omega)] at hc
    exact hc
  by_cases haone : a = 1
  · have hempty := low_defectLayer_empty hell hinv hunif hinter hmax hleft
    rw [haone, hempty] at hXDa
    exact Finset.notMem_empty X hXDa
  · have hatwo : 2 ≤ a := by omega
    by_cases hcentral : 2 * a = ell + 2
    · have hempty := central_defectLayer_empty hell hinv hunif hinter
        hmax hleft hatwo hcentral
      rw [hempty] at hXDa
      exact Finset.notMem_empty X hXDa
    · have hempty := noncentral_defectLayer_empty hell hinv hunif hinter
        hmax hleft hatwo hale hcentral
      rw [hempty] at hXDa
      exact Finset.notMem_empty X hXDa

private lemma inter_prefix_succ_eq {N ell : ℕ} (hN : ell < N)
    (A : Finset (Fin N)) :
    A ∩ «prefix» N (ell + 1) =
      if nextPoint hN ∈ A then
        insert (nextPoint hN) (A ∩ «prefix» N ell)
      else A ∩ «prefix» N ell := by
  by_cases hhA : nextPoint hN ∈ A
  · rw [if_pos hhA]
    ext x
    simp only [mem_inter, mem_prefix, mem_insert, nextPoint_val]
    constructor
    · rintro ⟨hxA, hxlt⟩
      by_cases hxeq : x.val = ell
      · exact Or.inl (Fin.ext hxeq)
      · exact Or.inr ⟨hxA, by omega⟩
    · rintro (rfl | ⟨hxA, hxlt⟩)
      · exact ⟨hhA, by simp⟩
      · exact ⟨hxA, by omega⟩
  · rw [if_neg hhA]
    ext x
    simp only [mem_inter, mem_prefix]
    constructor
    · rintro ⟨hxA, hxlt⟩
      refine ⟨hxA, ?_⟩
      by_cases hxeq : x.val = ell
      · have hxnext : x = nextPoint hN := Fin.ext hxeq
        exact (hhA (hxnext ▸ hxA)).elim
      · omega
    · rintro ⟨hxA, hxlt⟩
      exact ⟨hxA, by omega⟩

private lemma inter_tail_eq_at_next {N ell : ℕ} (hN : ell < N)
    (A : Finset (Fin N)) :
    A ∩ tailAfter N ell =
      if nextPoint hN ∈ A then
        insert (nextPoint hN) (A ∩ tailAfter N (ell + 1))
      else A ∩ tailAfter N (ell + 1) := by
  by_cases hhA : nextPoint hN ∈ A
  · rw [if_pos hhA]
    ext x
    simp only [mem_inter, mem_tailAfter, mem_insert, nextPoint_val]
    constructor
    · rintro ⟨hxA, hxge⟩
      by_cases hxeq : x.val = ell
      · exact Or.inl (Fin.ext hxeq)
      · exact Or.inr ⟨hxA, by omega⟩
    · rintro (rfl | ⟨hxA, hxge⟩)
      · exact ⟨hhA, le_rfl⟩
      · exact ⟨hxA, by omega⟩
  · rw [if_neg hhA]
    exact inter_tail_eq_far_of_not_next hN hhA

private lemma cross_next_membership_iff
    {N ell : ℕ} {F : Finset (Finset (Fin N))} (hN : ell < N)
    (hinv : PrefixInvariant F ell) (hleft : LeftCompressed F)
    (hdef : defectFamily F ell hN = ∅)
    {A B : Finset (Fin N)}
    (hA0 : nextPoint hN ∉ A) (hB1 : nextPoint hN ∈ B)
    (htail : A ∩ tailAfter N (ell + 1) =
      B ∩ tailAfter N (ell + 1))
    (hcard : (A ∩ «prefix» N (ell + 1)).card =
      (B ∩ «prefix» N (ell + 1)).card) :
    (A ∈ F ↔ B ∈ F) := by
  have hpreCard :
      (A ∩ «prefix» N ell).card =
        (B ∩ «prefix» N ell).card + 1 := by
    rw [inter_prefix_succ_eq hN A, if_neg hA0,
      inter_prefix_succ_eq hN B, if_pos hB1] at hcard
    have hhpre : nextPoint hN ∉ B ∩ «prefix» N ell :=
      fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
    rw [card_insert_of_notMem hhpre] at hcard
    omega
  have hlt :
      (B ∩ «prefix» N ell).card <
        (A ∩ «prefix» N ell).card := by omega
  obtain ⟨i, hiAP, hiBP⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hiA : i ∈ A := (mem_inter.mp hiAP).1
  have hiP : i ∈ «prefix» N ell := (mem_inter.mp hiAP).2
  have hiB : i ∉ B := by
    intro hi
    exact hiBP (mem_inter.mpr ⟨hi, hiP⟩)
  constructor
  · intro hAF
    let E := rightExchange (nextPoint hN) i A
    have hEnF : E ∈ F := by
      by_contra hmissing
      have hAdef : A ∈ defectFamily F ell hN :=
        mem_defectFamily.mpr
          ⟨hAF, ⟨i, hiP, hiA, hA0, hmissing⟩⟩
      rw [hdef] at hAdef
      exact Finset.notMem_empty A hAdef
    apply (hinv ?_ ?_).mp hEnF
    · rw [rightExchange_inter_tail hN hiP,
        inter_tail_eq_at_next hN B, if_pos hB1, htail]
    · rw [rightExchange_inter_prefix hN hiP,
        card_erase_of_mem hiAP]
      omega
  · intro hBF
    let L := singletonLeftShift i (nextPoint hN) B
    have hilt : i < nextPoint hN := by
      exact Fin.mk_lt_mk.mpr (mem_prefix.mp hiP)
    have hLF : L ∈ F := hleft.shifted_mem hilt hBF hB1 hiB
    have hLeq : L = insert i (B.erase (nextPoint hN)) := by
      dsimp only [L]
      rw [singletonLeftShift_eq_transpose ⟨hB1, hiB⟩,
        setTranspose_eq_insert_erase ⟨hB1, hiB⟩]
    apply (hinv ?_ ?_).mp hLF
    · rw [inter_tail_eq_at_next hN A, if_neg hA0]
      ext x
      have hxTail := congrArg (fun S : Finset (Fin N) ↦ x ∈ S) htail
      simp only [mem_inter, mem_tailAfter] at hxTail
      simp only [hLeq, mem_inter, mem_insert, mem_erase, mem_tailAfter]
      constructor
      · rintro ⟨rfl | ⟨hxnext, hxB⟩, hxge⟩
        · have := mem_prefix.mp hiP
          omega
        · have hfar : ell + 1 ≤ x.val := by
            by_cases hxeq : x.val = ell
            · have : x = nextPoint hN := Fin.ext hxeq
              exact (hxnext this).elim
            · omega
          exact hxTail.mpr ⟨hxB, hfar⟩
      · rintro ⟨hxA, hxfar⟩
        have hxB := (hxTail.mp ⟨hxA, hxfar⟩).1
        refine ⟨Or.inr ⟨?_, hxB⟩, by omega⟩
        intro hxeq
        subst x
        have hnextval : (nextPoint hN).val = ell := rfl
        omega
    · have hLpre :
          L ∩ «prefix» N ell =
            insert i (B ∩ «prefix» N ell) := by
        ext x
        simp only [hLeq, mem_inter, mem_insert, mem_erase, mem_prefix]
        constructor
        · rintro ⟨rfl | ⟨hxnext, hxB⟩, hxlt⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxB, hxlt⟩
        · rintro (rfl | ⟨hxB, hxlt⟩)
          · exact ⟨Or.inl rfl, mem_prefix.mp hiP⟩
          · refine ⟨Or.inr ⟨?_, hxB⟩, hxlt⟩
            intro hxeq
            subst x
            simpa using hxlt
      rw [hLpre, card_insert_of_notMem hiBP]
      omega

private lemma prefixInvariant_zero {N : ℕ}
    (F : Finset (Finset (Fin N))) : PrefixInvariant F 0 := by
  intro A B htail _hcard
  change A ∩ tailAfter N 0 = B ∩ tailAfter N 0 at htail
  have htailUniv : tailAfter N 0 = (univ : Finset (Fin N)) := by
    ext x
    simp
  rw [htailUniv] at htail
  simp only [inter_univ] at htail
  subst B
  exact Iff.rfl

private lemma prefixInvariant_succ
    {N ell : ℕ} {F : Finset (Finset (Fin N))} (hN : ell < N)
    (hinv : PrefixInvariant F ell) (hleft : LeftCompressed F)
    (hdef : defectFamily F ell hN = ∅) :
    PrefixInvariant F (ell + 1) := by
  intro A B htail hcard
  change A ∩ tailAfter N (ell + 1) =
      B ∩ tailAfter N (ell + 1) at htail
  change (A ∩ «prefix» N (ell + 1)).card =
      (B ∩ «prefix» N (ell + 1)).card at hcard
  by_cases hA : nextPoint hN ∈ A
  · by_cases hB : nextPoint hN ∈ B
    · apply hinv
      · rw [inter_tail_eq_at_next hN A, if_pos hA,
          inter_tail_eq_at_next hN B, if_pos hB, htail]
      · rw [inter_prefix_succ_eq hN A, if_pos hA,
          inter_prefix_succ_eq hN B, if_pos hB] at hcard
        have hhApre : nextPoint hN ∉ A ∩ «prefix» N ell :=
          fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
        have hhBpre : nextPoint hN ∉ B ∩ «prefix» N ell :=
          fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
        rw [card_insert_of_notMem hhApre,
          card_insert_of_notMem hhBpre] at hcard
        omega
    · exact (cross_next_membership_iff hN hinv hleft hdef hB hA
        htail.symm hcard.symm).symm
  · by_cases hB : nextPoint hN ∈ B
    · exact cross_next_membership_iff hN hinv hleft hdef hA hB
        htail hcard
    · apply hinv
      · rw [inter_tail_eq_at_next hN A, if_neg hA,
          inter_tail_eq_at_next hN B, if_neg hB, htail]
      · rw [inter_prefix_succ_eq hN A, if_neg hA,
          inter_prefix_succ_eq hN B, if_neg hB] at hcard
        exact hcard

private lemma prefixInvariant_upto
    {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    ∀ ell, ell ≤ 2 * q → PrefixInvariant F ell := by
  intro ell hell
  induction ell with
  | zero => exact prefixInvariant_zero F
  | succ ell ih =>
      have hell' : ell < 2 * q := by omega
      have hinv : PrefixInvariant F ell := ih (by omega)
      apply prefixInvariant_succ (hN := by omega) hinv hleft
      exact all_defects_empty hell' hinv hunif hinter hmax hleft

/-- A maximum-cardinality left-compressed uniform two-intersecting family of
`2q`-subsets is invariant under all permutations of the first `2q` points,
expressed in the direct prefix-layer form used by the remainder of the proof. -/
theorem prefixInvariant_two_mul {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    PrefixInvariant F (2 * q) := by
  exact prefixInvariant_upto hq hunif hinter hmax hleft (2 * q) le_rfl

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/Counting.lean` -/

section
open Finset

/-- The first block of `2 * q` points in a ground set of size `4 * q`. -/
def firstHalf (q : ℕ) : Finset (Fin (4 * q)) :=
  Finset.univ.filter fun i ↦ i.1 < 2 * q

/-- The complementary block of `2 * q` points. -/
def secondHalf (q : ℕ) : Finset (Fin (4 * q)) :=
  (firstHalf q)ᶜ

/-- The uniform layer consisting of all `2 * q`-subsets of a `4 * q`-set. -/
def uniformFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (Finset.univ : Finset (Fin (4 * q))).powersetCard (2 * q)

/-- The sublayer having exactly `a` points in the first block. -/
def uniformLayer (q a : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ (A ∩ firstHalf q).card = a

/-- The standard extremal family: more than half of a member lies in the first block. -/
def majorityFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ q + 1 ≤ (A ∩ firstHalf q).card

/-- The family paired with `majorityFamily` by complementation. -/
def minorityFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ (A ∩ firstHalf q).card < q

theorem card_firstHalf (q : ℕ) : (firstHalf q).card = 2 * q := by
  classical
  calc
    (firstHalf q).card = (Finset.univ : Finset (Fin (2 * q))).card := by
      apply Finset.card_bij
          (fun i (hi : i ∈ firstHalf q) ↦
            (⟨i.1, (Finset.mem_filter.mp hi).2⟩ : Fin (2 * q)))
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        exact congrArg (fun x : Fin (2 * q) ↦ x.1) hij
      · intro j hj
        let i : Fin (4 * q) := ⟨j.1, by omega⟩
        refine ⟨i, ?_, ?_⟩
        · simp [firstHalf, i]
        · exact Fin.ext rfl
    _ = 2 * q := by simp

theorem card_secondHalf (q : ℕ) : (secondHalf q).card = 2 * q := by
  classical
  rw [secondHalf, Finset.card_compl, card_firstHalf]
  simp only [Fintype.card_fin]
  omega

theorem card_uniformFamily (q : ℕ) :
    (uniformFamily q).card = Nat.choose (4 * q) (2 * q) := by
  simp [uniformFamily, Finset.card_powersetCard]

theorem mem_uniformFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ uniformFamily q ↔ A.card = 2 * q := by
  simp [uniformFamily]

theorem mem_uniformLayer {q a : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ uniformLayer q a ↔ A.card = 2 * q ∧ (A ∩ firstHalf q).card = a := by
  simp [uniformLayer, mem_uniformFamily]

theorem mem_majorityFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ majorityFamily q ↔
      A.card = 2 * q ∧ q + 1 ≤ (A ∩ firstHalf q).card := by
  simp [majorityFamily, mem_uniformFamily]

theorem mem_minorityFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ minorityFamily q ↔
      A.card = 2 * q ∧ (A ∩ firstHalf q).card < q := by
  simp [minorityFamily, mem_uniformFamily]

/-- Count a layer by independently choosing its points in the two equal blocks. -/
theorem card_uniformLayer (q a : ℕ) :
    (uniformLayer q a).card =
      Nat.choose (2 * q) a * Nat.choose (2 * q) (2 * q - a) := by
  classical
  calc
    (uniformLayer q a).card =
        ((firstHalf q).powersetCard a ×ˢ
          (secondHalf q).powersetCard (2 * q - a)).card := by
      apply Finset.card_bij
          (fun A (_ : A ∈ uniformLayer q a) ↦
            (A ∩ firstHalf q, A ∩ secondHalf q))
      · intro A hA
        rw [Finset.mem_product]
        have h := mem_uniformLayer.mp hA
        constructor
        · exact Finset.mem_powersetCard.mpr
            ⟨Finset.inter_subset_right, h.2⟩
        · apply Finset.mem_powersetCard.mpr
          constructor
          · exact Finset.inter_subset_right
          · have hdecomp :
                (A ∩ firstHalf q).card + (A ∩ secondHalf q).card = A.card := by
                rw [secondHalf]
                have hsdiff : A ∩ (firstHalf q)ᶜ = A \ firstHalf q := by
                  ext x
                  simp
                rw [hsdiff]
                exact Finset.card_inter_add_card_sdiff A (firstHalf q)
            have ha : a ≤ 2 * q := by
              rw [← h.2, ← h.1]
              exact Finset.card_le_card Finset.inter_subset_left
            have hsum :
                a + (A ∩ secondHalf q).card = 2 * q := by
              calc
                a + (A ∩ secondHalf q).card =
                    (A ∩ firstHalf q).card + (A ∩ secondHalf q).card := by
                      rw [h.2]
                _ = A.card := hdecomp
                _ = 2 * q := h.1
            exact Nat.eq_sub_of_add_eq' hsum
      · intro A hA B hB hEq
        have hfirst : A ∩ firstHalf q = B ∩ firstHalf q :=
          congrArg Prod.fst hEq
        have hsecond : A ∩ secondHalf q = B ∩ secondHalf q :=
          congrArg Prod.snd hEq
        ext x
        have hsplitA : x ∈ A ↔
            x ∈ A ∩ firstHalf q ∨ x ∈ A ∩ secondHalf q := by
          by_cases hx : x ∈ firstHalf q <;> simp [secondHalf, hx]
        have hsplitB : x ∈ B ↔
            x ∈ B ∩ firstHalf q ∨ x ∈ B ∩ secondHalf q := by
          by_cases hx : x ∈ firstHalf q <;> simp [secondHalf, hx]
        rw [hsplitA, hsplitB, hfirst, hsecond]
      · intro P hP
        rw [Finset.mem_product] at hP
        obtain ⟨hP₁, hP₂⟩ := hP
        have hP₁' := Finset.mem_powersetCard.mp hP₁
        have hP₂' := Finset.mem_powersetCard.mp hP₂
        let A := P.1 ∪ P.2
        have hdisj : Disjoint P.1 P.2 := by
          rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          have hxfirst := hP₁'.1 hx₁
          have hxsecond := hP₂'.1 hx₂
          simp [secondHalf] at hxsecond
          exact hxsecond hxfirst
        have hAcard : A.card = 2 * q := by
          change (P.1 ∪ P.2).card = 2 * q
          rw [Finset.card_union_of_disjoint hdisj, hP₁'.2, hP₂'.2]
          have ha : a ≤ 2 * q := by
            rw [← hP₁'.2, ← card_firstHalf q]
            exact Finset.card_le_card hP₁'.1
          omega
        have hAfirst : A ∩ firstHalf q = P.1 := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx₁ | hx₂
            · exact hx₁
            · have hxsecond := hP₂'.1 hx₂
              have hxfirst := (Finset.mem_inter.mp hx).2
              simp [secondHalf] at hxsecond
              exact (hxsecond hxfirst).elim
          · intro hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, hP₁'.1 hx⟩
        have hAsecond : A ∩ secondHalf q = P.2 := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx₁ | hx₂
            · have hxfirst := hP₁'.1 hx₁
              have hxsecond := (Finset.mem_inter.mp hx).2
              simp [secondHalf] at hxsecond
              exact (hxsecond hxfirst).elim
            · exact hx₂
          · intro hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hx, hP₂'.1 hx⟩
        refine ⟨A, ?_, ?_⟩
        · apply mem_uniformLayer.mpr
          refine ⟨hAcard, ?_⟩
          rw [hAfirst]
          exact hP₁'.2
        · exact Prod.ext hAfirst hAsecond
    _ = Nat.choose (2 * q) a * Nat.choose (2 * q) (2 * q - a) := by
      rw [Finset.card_product, Finset.card_powersetCard,
        Finset.card_powersetCard, card_firstHalf, card_secondHalf]

/-- Any two members of the majority construction meet in at least two points. -/
theorem majorityFamily_two_intersecting {q : ℕ} {A B : Finset (Fin (4 * q))}
    (hA : A ∈ majorityFamily q) (hB : B ∈ majorityFamily q) :
    2 ≤ (A ∩ B).card := by
  classical
  have hA' := (mem_majorityFamily.mp hA).2
  have hB' := (mem_majorityFamily.mp hB).2
  have hunion :
      ((A ∩ firstHalf q) ∪ (B ∩ firstHalf q)).card ≤ 2 * q := by
    rw [← card_firstHalf q]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hcard := Finset.card_union_add_card_inter
    (A ∩ firstHalf q) (B ∩ firstHalf q)
  have hinter : 2 ≤ ((A ∩ firstHalf q) ∩ (B ∩ firstHalf q)).card := by
    omega
  apply le_trans hinter
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_inter] at hx ⊢
  exact ⟨hx.1.1, hx.2.1⟩

private theorem card_majority_eq_card_minority (q : ℕ) :
    (majorityFamily q).card = (minorityFamily q).card := by
  classical
  apply Finset.card_bij (fun A (_ : A ∈ majorityFamily q) ↦ Aᶜ)
  · intro A hA
    have hA' := mem_majorityFamily.mp hA
    apply mem_minorityFamily.mpr
    constructor
    · rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    · have hblock : Aᶜ ∩ firstHalf q = firstHalf q \ A := by
        ext x
        simp [and_comm]
      rw [hblock, Finset.card_sdiff, card_firstHalf]
      have hinter : (A ∩ firstHalf q).card ≤ 2 * q := by
        rw [← card_firstHalf q]
        exact Finset.card_le_card Finset.inter_subset_right
      omega
  · intro A hA B hB hEq
    have := congrArg (fun S : Finset (Fin (4 * q)) ↦ Sᶜ) hEq
    simpa using this
  · intro B hB
    refine ⟨Bᶜ, ?_, ?_⟩
    · have hB' := mem_minorityFamily.mp hB
      apply mem_majorityFamily.mpr
      constructor
      · rw [Finset.card_compl]
        simp only [Fintype.card_fin]
        omega
      · have hblock : Bᶜ ∩ firstHalf q = firstHalf q \ B := by
          ext x
          simp [and_comm]
        rw [hblock, Finset.card_sdiff, card_firstHalf]
        have hinter : (B ∩ firstHalf q).card ≤ 2 * q := by
          rw [← card_firstHalf q]
          exact Finset.card_le_card Finset.inter_subset_right
        omega
    · simp

/-- Exact size of the standard construction, including the degenerate case `q = 0`. -/
theorem card_majorityFamily (q : ℕ) :
    (majorityFamily q).card =
      (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 := by
  classical
  have hdecomp :
      uniformFamily q =
        (majorityFamily q ∪ uniformLayer q q) ∪ minorityFamily q := by
    ext A
    simp only [mem_uniformFamily, Finset.mem_union, mem_majorityFamily,
      mem_uniformLayer, mem_minorityFamily]
    constructor
    · intro hA
      refine Or.elim (lt_trichotomy (A ∩ firstHalf q).card q) ?_ ?_
      · intro hlt
        exact Or.inr ⟨hA, hlt⟩
      · intro hrest
        rcases hrest with heq | hgt
        · exact Or.inl (Or.inr ⟨hA, heq⟩)
        · exact Or.inl (Or.inl ⟨hA, by omega⟩)
    · rintro ((hA | hA) | hA) <;> exact hA.1
  have hdisj₁ : Disjoint (majorityFamily q) (uniformLayer q q) := by
    rw [Finset.disjoint_left]
    intro A hmaj hmid
    have hmaj' := (mem_majorityFamily.mp hmaj).2
    have hmid' := (mem_uniformLayer.mp hmid).2
    omega
  have hdisj₂ : Disjoint (majorityFamily q ∪ uniformLayer q q) (minorityFamily q) := by
    rw [Finset.disjoint_left]
    intro A hhigh hlow
    rcases Finset.mem_union.mp hhigh with hmaj | hmid
    · have hmaj' := (mem_majorityFamily.mp hmaj).2
      have hlow' := (mem_minorityFamily.mp hlow).2
      omega
    · have hmid' := (mem_uniformLayer.mp hmid).2
      have hlow' := (mem_minorityFamily.mp hlow).2
      omega
  have hcount :
      (uniformFamily q).card =
        (majorityFamily q).card + (uniformLayer q q).card +
          (minorityFamily q).card := by
    rw [hdecomp, Finset.card_union_of_disjoint hdisj₂,
      Finset.card_union_of_disjoint hdisj₁]
  rw [card_uniformFamily, card_uniformLayer, ← card_majority_eq_card_minority] at hcount
  have hsymm : Nat.choose (2 * q) (2 * q - q) = Nat.choose (2 * q) q := by
    rw [Nat.choose_symm]
    omega
  rw [hsymm] at hcount
  have hsquare : Nat.choose (2 * q) q * Nat.choose (2 * q) q =
      Nat.choose (2 * q) q ^ 2 := by ring
  rw [hsquare] at hcount
  have hdiff :
      Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2 =
        2 * (majorityFamily q).card := by
    omega
  rw [hdiff]
  omega

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83/DualLayers.lean` -/

section
/-!
# Duality and two-block layers for Erdős Problem 83

This module contains the part of the proof after prefix symmetrisation.  Reversed
complementation transports first-block invariance to the second block.  The two
block invariances then show that a compressed family consists of whole layers;
compression makes the present layers upward closed, while two-intersection
excludes the middle layer.
-/



open Finset

attribute [local instance] Classical.propDecidable

/-- Order reversal on `Fin N`. -/
def reverseFin {N : ℕ} (x : Fin N) : Fin N :=
  ⟨N - 1 - x.1, by omega⟩

@[simp] lemma reverseFin_val {N : ℕ} (x : Fin N) :
    (reverseFin x).1 = N - 1 - x.1 := rfl

@[simp] lemma reverseFin_reverseFin {N : ℕ} (x : Fin N) :
    reverseFin (reverseFin x) = x := by
  ext
  simp [reverseFin]
  omega

/-- Order reversal as an equivalence. -/
def reverseFinEquiv (N : ℕ) : Fin N ≃ Fin N where
  toFun := reverseFin
  invFun := reverseFin
  left_inv := reverseFin_reverseFin
  right_inv := reverseFin_reverseFin

@[simp] lemma reverseFinEquiv_apply {N : ℕ} (x : Fin N) :
    reverseFinEquiv N x = reverseFin x := rfl

@[simp] lemma reverseFinEquiv_symm (N : ℕ) :
    (reverseFinEquiv N).symm = reverseFinEquiv N := by
  rfl

/-- Reversed complement of a finite set. -/
def dualSet {N : ℕ} (A : Finset (Fin N)) : Finset (Fin N) :=
  Aᶜ.map (reverseFinEquiv N).toEmbedding

/-- Reversed complement of every member of a family. -/
def dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  F.image dualSet

@[simp] lemma mem_dualSet {N : ℕ} {A : Finset (Fin N)} {x : Fin N} :
    x ∈ dualSet A ↔ reverseFin x ∉ A := by
  simp [dualSet, reverseFinEquiv]

@[simp] lemma card_dualSet {N : ℕ} (A : Finset (Fin N)) :
    (dualSet A).card = N - A.card := by
  simp only [dualSet, Finset.card_map, Finset.card_compl, Fintype.card_fin]

@[simp] lemma dualSet_dualSet {N : ℕ} (A : Finset (Fin N)) :
    dualSet (dualSet A) = A := by
  ext x
  simp

lemma dualSet_injective {N : ℕ} : Function.Injective (@dualSet N) := by
  intro A B h
  simpa only [dualSet_dualSet] using congrArg dualSet h

@[simp] lemma mem_dualFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    {A : Finset (Fin N)} :
    A ∈ dualFamily F ↔ dualSet A ∈ F := by
  rw [dualFamily, Finset.mem_image]
  constructor
  · rintro ⟨B, hBF, rfl⟩
    simpa using hBF
  · intro hA
    exact ⟨dualSet A, hA, dualSet_dualSet A⟩

@[simp] lemma card_dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    (dualFamily F).card = F.card := by
  exact Finset.card_image_iff.mpr dualSet_injective.injOn

@[simp] lemma dualFamily_dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    dualFamily (dualFamily F) = F := by
  ext A
  simp

/-- Reversed complementation preserves the middle uniform layer. -/
lemma Uniform.dualFamily {N k : ℕ} {F : Finset (Finset (Fin N))}
    (hF : Uniform k F) (hN : N = 2 * k) :
    Uniform k (dualFamily F) := by
  intro A hA
  have hdual : (dualSet A).card = k := hF (mem_dualFamily.mp hA)
  have hle : A.card ≤ N := by
    simpa using Finset.card_le_card (Finset.subset_univ A)
  rw [card_dualSet] at hdual
  omega

/-- On the middle layer, reversed complementation preserves intersection
cardinality. -/
lemma card_dualSet_inter_dualSet {N k : ℕ}
    (hN : N = 2 * k) (A B : Finset (Fin N))
    (hA : A.card = k) (hB : B.card = k) :
    (dualSet A ∩ dualSet B).card = (A ∩ B).card := by
  have heq :
      dualSet A ∩ dualSet B =
        (Aᶜ ∩ Bᶜ).map (reverseFinEquiv N).toEmbedding := by
    ext x
    simp
  have hcompl : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by
    ext x
    simp
  have hunion := Finset.card_union_add_card_inter A B
  rw [heq, Finset.card_map, hcompl, Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

/-- Reversed complementation preserves two-intersection on the middle layer. -/
lemma TwoIntersecting.dualFamily {N k : ℕ}
    {F : Finset (Finset (Fin N))} (hinter : TwoIntersecting F)
    (hN : N = 2 * k) (hunif : Uniform k F) :
    TwoIntersecting (dualFamily F) := by
  intro A B hA hB
  have hdualA : dualSet A ∈ F := mem_dualFamily.mp hA
  have hdualB : dualSet B ∈ F := mem_dualFamily.mp hB
  calc
    2 ≤ (dualSet A ∩ dualSet B).card := hinter hdualA hdualB
    _ = (A ∩ B).card := by
      symm
      simpa using card_dualSet_inter_dualSet hN (dualSet A) (dualSet B)
        (hunif hdualA) (hunif hdualB)

/-- Maximality by cardinality is preserved by reversed complementation. -/
lemma maximal_dualFamily {N k : ℕ} (hN : N = 2 * k)
    {F : Finset (Finset (Fin N))}
    (hunif : Uniform k F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin N)),
      Uniform k G → TwoIntersecting G → G.card ≤ F.card) :
    ∀ G : Finset (Finset (Fin N)),
      Uniform k G → TwoIntersecting G → G.card ≤ (dualFamily F).card := by
  intro G hGunif hGinter
  rw [card_dualFamily]
  simpa using hmax (dualFamily G) (hGunif.dualFamily hN)
    (hGinter.dualFamily hN hGunif)

lemma reverseFin_lt_reverseFin {N : ℕ} {i j : Fin N} (hij : i < j) :
    reverseFin j < reverseFin i := by
  simp only [Fin.lt_iff_val_lt_val, reverseFin_val]
  omega

private lemma reverseFin_swap {N : ℕ} (i j x : Fin N) :
    Equiv.swap (reverseFin j) (reverseFin i) (reverseFin x) =
      reverseFin (Equiv.swap i j x) := by
  rw [Equiv.swap_comm]
  exact (reverseFinEquiv N).injective.swap_apply i j x

lemma dualSet_setTranspose {N : ℕ} (i j : Fin N) (A : Finset (Fin N)) :
    dualSet (setTranspose i j A) =
      setTranspose (reverseFin j) (reverseFin i) (dualSet A) := by
  ext x
  simp only [mem_dualSet, mem_setTranspose]
  have hswap : Equiv.swap i j (reverseFin x) =
      reverseFin (Equiv.swap (reverseFin j) (reverseFin i) x) := by
    simpa using reverseFin_swap (reverseFin j) (reverseFin i) x
  rw [hswap]

lemma dualSet_singletonLeftShift {N : ℕ} (i j : Fin N)
    (A : Finset (Fin N)) :
    dualSet (singletonLeftShift i j A) =
      singletonLeftShift (reverseFin j) (reverseFin i) (dualSet A) := by
  by_cases h : j ∈ A ∧ i ∉ A
  · have hdual : reverseFin i ∈ dualSet A ∧ reverseFin j ∉ dualSet A := by
      constructor
      · simpa using h.2
      · simpa using h.1
    rw [singletonLeftShift_eq_transpose h,
      singletonLeftShift_eq_transpose hdual, dualSet_setTranspose]
  · have hdual : ¬ (reverseFin i ∈ dualSet A ∧ reverseFin j ∉ dualSet A) := by
      intro hd
      apply h
      constructor
      · simpa using hd.2
      · simpa using hd.1
    rw [singletonLeftShift_eq_self h, singletonLeftShift_eq_self hdual]

/-- Left compression is invariant under reversed complementation. -/
lemma LeftCompressed.dualFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    (hleft : LeftCompressed F) : LeftCompressed (Erdos83.dualFamily F) := by
  intro i j hij
  have hclosed : ∀ ⦃A : Finset (Fin N)⦄, A ∈ Erdos83.dualFamily F →
      singletonLeftShift i j A ∈ Erdos83.dualFamily F := by
    intro A hA
    by_cases hmove : j ∈ A ∧ i ∉ A
    · apply mem_dualFamily.mpr
      rw [dualSet_singletonLeftShift]
      exact hleft.shifted_mem (reverseFin_lt_reverseFin hij)
        (mem_dualFamily.mp hA) (by simpa using hmove.2) (by simpa using hmove.1)
    · simpa [singletonLeftShift_eq_self hmove] using hA
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨B, hBF, rfl⟩
    have hshift := hclosed hBF
    simp [familyShiftMember, hshift, hBF]
  · intro hA
    have hshift := hclosed hA
    exact Finset.mem_image.mpr ⟨A, hA, by simp [familyShiftMember, hshift]⟩

/-- Points before the split at `k`. -/
def firstBlock (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ x.1 < k

/-- Points at or after the split at `k`. -/
def secondBlock (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ k ≤ x.1

@[simp] lemma mem_firstBlock {N k : ℕ} {x : Fin N} :
    x ∈ firstBlock N k ↔ x.1 < k := by
  simp [firstBlock]

@[simp] lemma mem_secondBlock {N k : ℕ} {x : Fin N} :
    x ∈ secondBlock N k ↔ k ≤ x.1 := by
  simp [secondBlock]

lemma firstBlock_union_secondBlock (N k : ℕ) :
    firstBlock N k ∪ secondBlock N k = Finset.univ := by
  ext x
  simp [firstBlock, secondBlock]
  omega

lemma firstBlock_disjoint_secondBlock (N k : ℕ) :
    Disjoint (firstBlock N k) (secondBlock N k) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  simp only [mem_firstBlock] at hx
  simp only [mem_secondBlock] at hy
  omega

@[simp] lemma firstBlock_four_mul_two_mul (q : ℕ) :
    firstBlock (4 * q) (2 * q) = firstHalf q := rfl

lemma secondBlock_four_mul_two_mul (q : ℕ) :
    secondBlock (4 * q) (2 * q) = secondHalf q := by
  ext x
  by_cases hx : x.1 < 2 * q
  · simp [secondBlock, secondHalf, firstHalf, hx]
  · have hx' : 2 * q ≤ x.1 := by omega
    simp [secondBlock, secondHalf, firstHalf, hx, hx']

/-- In the `4q`-point ground set, duality exchanges the two blocks and
complements within them. -/
lemma card_dualSet_inter_firstBlock (q : ℕ) (A : Finset (Fin (4 * q))) :
    (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
      2 * q - (A ∩ secondBlock (4 * q) (2 * q)).card := by
  calc
    (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
        (secondBlock (4 * q) (2 * q) \ A).card := by
      apply Finset.card_bij
          (fun x (_ : x ∈ dualSet A ∩ firstBlock (4 * q) (2 * q)) ↦ reverseFin x)
      · intro x hx
        have hxdual := (Finset.mem_inter.mp hx).1
        have hxfirst := (Finset.mem_inter.mp hx).2
        apply Finset.mem_sdiff.mpr
        constructor
        · simp only [mem_secondBlock, reverseFin_val]
          simp only [mem_firstBlock] at hxfirst
          omega
        · simpa using hxdual
      · intro x hx y hy hxy
        exact (reverseFinEquiv (4 * q)).injective hxy
      · intro y hy
        have hysecond := (Finset.mem_sdiff.mp hy).1
        have hyA := (Finset.mem_sdiff.mp hy).2
        refine ⟨reverseFin y, ?_, ?_⟩
        · apply Finset.mem_inter.mpr
          constructor
          · simpa using hyA
          · simp only [mem_firstBlock, reverseFin_val]
            simp only [mem_secondBlock] at hysecond
            omega
        · exact reverseFin_reverseFin y
    _ = 2 * q - (A ∩ secondBlock (4 * q) (2 * q)).card := by
      rw [Finset.card_sdiff, Finset.inter_comm,
        secondBlock_four_mul_two_mul, card_secondHalf]

/-- Membership depends only on the two block cardinalities.  The formulation
with equal intersections is convenient for deriving it from `PrefixInvariant`.
-/
def BlockInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∀ (A B : Finset (Fin N)),
    (A ∩ firstBlock N k).card = (B ∩ firstBlock N k).card →
    (A ∩ secondBlock N k).card = (B ∩ secondBlock N k).card →
    (A ∈ F ↔ B ∈ F)

lemma prefixInvariant_iff {N : ℕ} {F : Finset (Finset (Fin N))} {k : ℕ} :
    PrefixInvariant F k ↔
      ∀ ⦃A B : Finset (Fin N)⦄,
        A ∩ secondBlock N k = B ∩ secondBlock N k →
        (A ∩ firstBlock N k).card = (B ∩ firstBlock N k).card →
        (A ∈ F ↔ B ∈ F) := by
  rfl

/-- The right-handed analogue of `PrefixInvariant`: the first block is fixed
pointwise and membership depends on the cardinality in the second block. -/
def SuffixInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∀ ⦃A B : Finset (Fin N)⦄,
    A ∩ firstBlock N k = B ∩ firstBlock N k →
    (A ∩ secondBlock N k).card = (B ∩ secondBlock N k).card →
    (A ∈ F ↔ B ∈ F)

/-- Prefix invariance of the reversed-complement family is precisely the
right-block invariance needed for the original family. -/
lemma suffixInvariant_of_dual_prefix {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hdual : PrefixInvariant (dualFamily F) (2 * q)) :
    SuffixInvariant F (2 * q) := by
  intro A B hfirst hsecond
  have htail :
      dualSet A ∩ secondBlock (4 * q) (2 * q) =
        dualSet B ∩ secondBlock (4 * q) (2 * q) := by
    ext x
    simp only [Finset.mem_inter, mem_dualSet, mem_secondBlock]
    constructor
    · rintro ⟨hna, hx⟩
      have hrfirst : reverseFin x ∈ firstBlock (4 * q) (2 * q) := by
        simp only [mem_firstBlock, reverseFin_val]
        omega
      have hab : reverseFin x ∈ A ↔ reverseFin x ∈ B := by
        have hmem : reverseFin x ∈ A ∩ firstBlock (4 * q) (2 * q) ↔
            reverseFin x ∈ B ∩ firstBlock (4 * q) (2 * q) := by rw [hfirst]
        simpa only [Finset.mem_inter, hrfirst, and_true] using hmem
      exact ⟨fun hb ↦ hna (hab.mpr hb), hx⟩
    · rintro ⟨hnb, hx⟩
      have hrfirst : reverseFin x ∈ firstBlock (4 * q) (2 * q) := by
        simp only [mem_firstBlock, reverseFin_val]
        omega
      have hab : reverseFin x ∈ A ↔ reverseFin x ∈ B := by
        have hmem : reverseFin x ∈ A ∩ firstBlock (4 * q) (2 * q) ↔
            reverseFin x ∈ B ∩ firstBlock (4 * q) (2 * q) := by rw [hfirst]
        simpa only [Finset.mem_inter, hrfirst, and_true] using hmem
      exact ⟨fun ha ↦ hnb (hab.mp ha), hx⟩
  have hfirstCard :
      (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
        (dualSet B ∩ firstBlock (4 * q) (2 * q)).card := by
    rw [card_dualSet_inter_firstBlock, card_dualSet_inter_firstBlock, hsecond]
  simpa using hdual htail hfirstCard

lemma blockInvariant_of_prefix_suffix {N k : ℕ}
    {F : Finset (Finset (Fin N))}
    (hprefix : PrefixInvariant F k) (hsuffix : SuffixInvariant F k) :
    BlockInvariant F k := by
  intro A B hfirst hsecond
  let C := (B ∩ firstBlock N k) ∪ (A ∩ secondBlock N k)
  have hCfirst : C ∩ firstBlock N k = B ∩ firstBlock N k := by
    ext x
    simp only [C, mem_inter, mem_union, mem_firstBlock, mem_secondBlock]
    constructor
    · rintro ⟨hB | hA, hx⟩
      · exact hB
      · omega
    · intro hx
      exact ⟨Or.inl hx, hx.2⟩
  have hCsecond : C ∩ secondBlock N k = A ∩ secondBlock N k := by
    ext x
    simp only [C, mem_inter, mem_union, mem_firstBlock, mem_secondBlock]
    constructor
    · rintro ⟨hB | hA, hx⟩
      · omega
      · exact hA
    · intro hx
      exact ⟨Or.inr hx, hx.2⟩
  exact (hprefix hCsecond.symm (hfirst.trans (congrArg Finset.card hCfirst).symm)).trans
    (hsuffix hCfirst ((congrArg Finset.card hCsecond).trans hsecond))

lemma card_inter_firstBlock_add_secondBlock {N k : ℕ}
    (A : Finset (Fin N)) :
    (A ∩ firstBlock N k).card + (A ∩ secondBlock N k).card = A.card := by
  exact card_inter_prefix_add_card_inter_tailAfter A

/-- One compression step moves a point from the second half into the first
half, increasing the first-half count by one. -/
lemma exists_member_firstBlock_card_succ {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hleft : LeftCompressed F)
    {A : Finset (Fin (4 * q))} (hA : A ∈ F)
    (hlt : (A ∩ firstBlock (4 * q) (2 * q)).card < 2 * q) :
    ∃ B ∈ F,
      (B ∩ firstBlock (4 * q) (2 * q)).card =
        (A ∩ firstBlock (4 * q) (2 * q)).card + 1 := by
  have hfirstCard : (firstBlock (4 * q) (2 * q)).card = 2 * q := by
    rw [firstBlock_four_mul_two_mul, card_firstHalf]
  have hcardlt :
      (A ∩ firstBlock (4 * q) (2 * q)).card <
        (firstBlock (4 * q) (2 * q)).card := by
    rw [hfirstCard]
    exact hlt
  obtain ⟨i, hiFirst, hiNotInter⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hiA : i ∉ A := by
    intro hi
    exact hiNotInter (Finset.mem_inter.mpr ⟨hi, hiFirst⟩)
  have hdecomp := card_inter_firstBlock_add_secondBlock
    (k := 2 * q) A
  have hsecondPos : 0 < (A ∩ secondBlock (4 * q) (2 * q)).card := by
    have hAcard := hunif hA
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hsecondPos
  have hjA : j ∈ A := (Finset.mem_inter.mp hj).1
  have hjSecond : j ∈ secondBlock (4 * q) (2 * q) :=
    (Finset.mem_inter.mp hj).2
  have hij : i < j := by
    simp only [Fin.lt_iff_val_lt_val]
    simp only [mem_firstBlock] at hiFirst
    simp only [mem_secondBlock] at hjSecond
    omega
  let B := singletonLeftShift i j A
  have hB : B ∈ F := hleft.shifted_mem hij hA hjA hiA
  refine ⟨B, hB, ?_⟩
  have hmove : j ∈ A ∧ i ∉ A := ⟨hjA, hiA⟩
  have hBform : B = insert i (A.erase j) := by
    dsimp only [B]
    rw [singletonLeftShift_eq_transpose hmove,
      setTranspose_eq_insert_erase hmove]
  have hjNotFirst : j ∉ firstBlock (4 * q) (2 * q) := by
    simp only [mem_firstBlock]
    simp only [mem_secondBlock] at hjSecond
    omega
  have hInter :
      B ∩ firstBlock (4 * q) (2 * q) =
        insert i (A ∩ firstBlock (4 * q) (2 * q)) := by
    rw [hBform]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | hx, hxFirst⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx.2, hxFirst⟩
    · rintro (rfl | ⟨hxA, hxFirst⟩)
      · exact ⟨Or.inl rfl, hiFirst⟩
      · have hxj : x ≠ j := by
          intro h
          subst x
          exact hjNotFirst hxFirst
        exact ⟨Or.inr ⟨hxj, hxA⟩, hxFirst⟩
  have hiNot : i ∉ A ∩ firstBlock (4 * q) (2 * q) := by
    intro hi
    exact hiA (Finset.mem_inter.mp hi).1
  rw [hInter, Finset.card_insert_of_notMem hiNot]

/-- Any member whose first-half count is at most `q` can be compressed, layer
by layer, to a member of the middle layer. -/
lemma exists_middle_member {q : ℕ} (hq : 1 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hleft : LeftCompressed F)
    {A : Finset (Fin (4 * q))} (hA : A ∈ F)
    (hle : (A ∩ firstBlock (4 * q) (2 * q)).card ≤ q) :
    ∃ B ∈ F, (B ∩ firstBlock (4 * q) (2 * q)).card = q := by
  generalize hd : q - (A ∩ firstBlock (4 * q) (2 * q)).card = d
  induction d generalizing A with
  | zero =>
      refine ⟨A, hA, ?_⟩
      omega
  | succ d ih =>
      have halt : (A ∩ firstBlock (4 * q) (2 * q)).card < q := by omega
      have haltTwo : (A ∩ firstBlock (4 * q) (2 * q)).card < 2 * q := by omega
      obtain ⟨B, hB, hBcount⟩ :=
        exists_member_firstBlock_card_succ hunif hleft hA haltTwo
      apply ih (A := B)
      · exact hB
      · omega
      · omega

/-- Two-intersection rules out the middle layer once membership is invariant
under permutations inside both halves. -/
lemma middle_layer_absent {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hblock : BlockInvariant F (2 * q)) :
    ∀ {A : Finset (Fin (4 * q))}, A ∈ F →
      (A ∩ firstBlock (4 * q) (2 * q)).card ≠ q := by
  intro A hA hAfirst
  have hdecomp := card_inter_firstBlock_add_secondBlock
    (k := 2 * q) A
  have hAsecond : (A ∩ secondBlock (4 * q) (2 * q)).card = q := by
    have hAcard := hunif hA
    omega
  have hcompFirst :
      (Aᶜ ∩ firstBlock (4 * q) (2 * q)).card = q := by
    have heq : Aᶜ ∩ firstBlock (4 * q) (2 * q) =
        firstBlock (4 * q) (2 * q) \ A := by
      ext x
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
    have hfirstCard : (firstBlock (4 * q) (2 * q)).card = 2 * q := by
      rw [firstBlock_four_mul_two_mul, card_firstHalf]
    rw [hfirstCard]
    rw [hAfirst]
    omega
  have hcompSecond :
      (Aᶜ ∩ secondBlock (4 * q) (2 * q)).card = q := by
    have heq : Aᶜ ∩ secondBlock (4 * q) (2 * q) =
        secondBlock (4 * q) (2 * q) \ A := by
      ext x
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
    have hsecondCard : (secondBlock (4 * q) (2 * q)).card = 2 * q := by
      rw [secondBlock_four_mul_two_mul, card_secondHalf]
    rw [hsecondCard]
    rw [hAsecond]
    omega
  have hAc : Aᶜ ∈ F :=
    (hblock A Aᶜ (hAfirst.trans hcompFirst.symm)
      (hAsecond.trans hcompSecond.symm)).mp hA
  have hcontra := hinter hA hAc
  simpa using hcontra

/-- A compressed, block-invariant uniform two-intersecting family lies in the
standard strict-majority construction. -/
lemma subset_majority_of_blockInvariant {q : ℕ} (hq : 1 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hleft : LeftCompressed F) (hblock : BlockInvariant F (2 * q)) :
    F ⊆ majorityFamily q := by
  intro A hA
  apply mem_majorityFamily.mpr
  refine ⟨hunif hA, ?_⟩
  by_contra hmajority
  have hle : (A ∩ firstBlock (4 * q) (2 * q)).card ≤ q := by
    rw [firstBlock_four_mul_two_mul]
    omega
  obtain ⟨B, hB, hBmiddle⟩ := exists_middle_member hq hunif hleft hA hle
  exact middle_layer_absent hunif hinter hblock hB hBmiddle

/-- The post-prefix extremal conclusion: every maximum-cardinality compressed
family is contained in the standard strict-majority family. -/
theorem extremal_subset_majority {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    F ⊆ majorityFamily q := by
  have hmiddle : 4 * q = 2 * (2 * q) := by omega
  have hdualUnif : Uniform (2 * q) (dualFamily F) :=
    hunif.dualFamily hmiddle
  have hdualInter : TwoIntersecting (dualFamily F) :=
    hinter.dualFamily hmiddle hunif
  have hdualMax :
      ∀ G : Finset (Finset (Fin (4 * q))),
        Uniform (2 * q) G → TwoIntersecting G →
          G.card ≤ (dualFamily F).card :=
    maximal_dualFamily hmiddle hunif hinter hmax
  have hprefix : PrefixInvariant F (2 * q) :=
    prefixInvariant_two_mul hq hunif hinter hmax hleft
  have hdualPrefix : PrefixInvariant (dualFamily F) (2 * q) :=
    prefixInvariant_two_mul hq hdualUnif hdualInter hdualMax hleft.dualFamily
  have hsuffix : SuffixInvariant F (2 * q) :=
    suffixInvariant_of_dual_prefix hdualPrefix
  exact subset_majority_of_blockInvariant (by omega) hunif hinter hleft
    (blockInvariant_of_prefix_suffix hprefix hsuffix)

/-- Cardinality form used by the main Erdős 83 theorem. -/
theorem extremal_card_le_majority {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    F.card ≤ (majorityFamily q).card := by
  exact Finset.card_le_card
    (extremal_subset_majority hq hunif hinter hmax hleft)

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos83.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 83.
https://www.erdosproblems.com/forum/thread/83

Informal authors:
- Rudolf Ahlswede
- Levon H. Khachatrian

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos83.md
-/

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Erdős Problem 83

Ahlswede and Khachatrian proved the sharp bound for a family of `2 * q`-subsets
of a `4 * q`-set whose members pairwise meet in at least two points.  The proof
below uses the specialized pushing--pulling argument formalized in the helper
modules under `ErdosProblems/Erdos83/`.
-/



open Finset

/-- Erdős Problem 83: the sharp bound for two-intersecting middle-layer
families on a `4 * q`-point set. -/
theorem erdos_83 (q : ℕ) (F : Finset (Finset (Fin (4 * q))))
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F) :
    F.card ≤
      (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 := by
  by_cases hq0 : q = 0
  · subst q
    have hF : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      have hcard := hunif hA
      have hmeet := hinter hA hA
      rw [Finset.inter_self, hcard] at hmeet
      omega
    simp [hF]
  by_cases hq1 : q = 1
  · subst q
    have hcardle : F.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro A hA B hB
      have hmeet := hinter hA hB
      have hAcard := hunif hA
      have hBcard := hunif hB
      have hIA : A ∩ B = A :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hIB : A ∩ B = B :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hIA.symm.trans hIB
    norm_num at hcardle ⊢
    exact hcardle
  have hq : 2 ≤ q := by omega
  obtain ⟨Fmax, hmaxUnif, hmaxInter, hmax, hmaxLeft⟩ :=
    exists_extremal_leftCompressed (4 * q) (2 * q)
  calc
    F.card ≤ Fmax.card := hmax F hunif hinter
    _ ≤ (majorityFamily q).card :=
      extremal_card_le_majority hq hmaxUnif hmaxInter hmax hmaxLeft
    _ = (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 :=
      card_majorityFamily q

end

#print axioms erdos_83
-- 'Erdos83.erdos_83' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos83
