import Mathlib

set_option linter.dupNamespace false

namespace Erdos343

/-
# Erdős Problem 343

If $A\subseteq \mathbb{N}$ is a multiset of integers such that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N$$
for all $N$ then must $A$ be subcomplete? That is, must
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
contain an infinite arithmetic progression?

The answer is **yes**, proved by Szemerédi and Vu [SzVu06]: there is an absolute constant $C$
such that every multiset of positive integers with at least $CN$ elements in $\{1,\ldots,N\}$
for all large $N$ is subcomplete. `erdos_343` states it in that form, which is the form in which
the question was answered. A multiset is an occurrence-indexed sequence `A : ℕ → ℕ` of positive
integers, distinct indices being distinct occurrences, and the counting hypothesis is required
only eventually, with no monotonicity of the indexing assumed.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000285), reusing
seven modules of `plby/lean-proofs` (including `ErdosProblems/Erdos344.lean` and a trimmed
section of `ErdosProblems/Erdos360/Core.lean`, as recorded in the submission's vendor manifest).
The 38 modules forming the closure of `erdos_343` are flattened here in dependency order, with the
final theorem renamed from upstream `erdos_343_eventual`; the two corollaries after it, for the
all-$N$ and monotone formulation, are omitted so that `erdos_343` is the last declaration.

Declarations that `erdos_343` does not depend on have been removed.
-/

universe u

/-! ### Upstream module `Jsp285/Definitions.lean` -/

section
/-!
# Erdős Problem 343 (JSP-000285): frozen target statement

Source (erdosproblems.com/343, hashed copy in `ref/erdos343-statement.txt`):
"If `A ⊆ ℕ` is a multiset of integers such that `|A ∩ {1,…,N}| ≫ N` for all `N`
then must `A` be subcomplete?  That is, must `P(A) = {∑_{n∈B} n : B ⊆ A finite}`
contain an infinite arithmetic progression?"  Answered positively by
Szemerédi–Vu (JAMS 2006, Theorem 6.x "Folkman's conjecture"): there is an
absolute constant `C` such that every non-decreasing sequence of positive
integers with `A(n) ≥ C n` for all sufficiently large `n` is subcomplete.

Encoding (identical to plby/lean-proofs `Erdos343` so the two faces are
comparable): a multiset is an occurrence-indexed function `A : ℕ → ℕ`; distinct
indices are distinct occurrences even when the values agree.
-/

open _root_.Filter

/-- Finite subset sums of an infinite multiset represented by indexed occurrences. -/
def SubsetSums (A : ℕ → ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, n = ∑ i ∈ s, A i}

/-- A set contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ S

/-- The occurrence-indexed multiset `A` is subcomplete. -/
def IsSubcomplete (A : ℕ → ℕ) : Prop :=
  ContainsInfiniteAP (SubsetSums A)

/-- The published (Szemerédi–Vu) hypothesis: at least `C * N` occurrences have
value at most `N` for all sufficiently large `N`. -/
def HasEventualLinearCountingLowerBound (C : ℕ) (A : ℕ → ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N

end

/-! ### Upstream module `Jsp285/FreshSelection.lean` -/

/-! Selecting distinct occurrence indices from stagewise finite avoidance. -/

namespace Jsp285

/-- If stage `n` admits a suitable index outside every set of at most `n`
previous indices, the choices can be made simultaneously and injectively. -/
theorem exists_injective_of_finite_avoidance
    (P : ℕ → ℕ → Prop)
    (h : ∀ n (s : Finset ℕ), s.card ≤ n →
      ∃ x, x ∉ s ∧ P n x) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, P n (f n) := by
  classical
  let pick (n : ℕ) (s : Finset ℕ) : ℕ :=
    if hs : s.card ≤ n then Classical.choose (h n s hs) else 0
  have pick_spec (n : ℕ) (s : Finset ℕ) (hs : s.card ≤ n) :
      pick n s ∉ s ∧ P n (pick n s) := by
    simp only [pick, dif_pos hs]
    exact Classical.choose_spec (h n s hs)
  let U : ℕ → Finset ℕ :=
    Nat.rec ∅ (fun n s => insert (pick n s) s)
  have U_zero : U 0 = ∅ := rfl
  have U_succ (n : ℕ) : U (n + 1) = insert (pick n (U n)) (U n) := rfl
  have U_card (n : ℕ) : (U n).card = n := by
    induction n with
    | zero => simp [U_zero]
    | succ n ih =>
        rw [U_succ, Finset.card_insert_of_notMem]
        · omega
        · exact (pick_spec n (U n) (by omega)).1
  let f : ℕ → ℕ := fun n => pick n (U n)
  have f_fresh (n : ℕ) : f n ∉ U n := by
    exact (pick_spec n (U n) (by rw [U_card])).1
  have f_property (n : ℕ) : P n (f n) := by
    exact (pick_spec n (U n) (by rw [U_card])).2
  have earlier_mem (n i : ℕ) (hi : i < n) : f i ∈ U n := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [U_succ]
        by_cases hin : i = n
        · subst i
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ih (by omega))
  refine ⟨f, ?_, f_property⟩
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · exact f_fresh b (hab ▸ earlier_mem b a hablt)
  · exact f_fresh a (hab.symm ▸ earlier_mem a b hbalt)

end Jsp285

/-! ### Upstream module `Jsp285/DensitySelection.lean` -/

/-! Two disjoint occurrence sequences selected from eventual linear counting witnesses. -/

namespace Jsp285

/-- Eventual linear finite counts yield two disjoint injective occurrence
sequences whose values grow at most like `i / D`. -/
theorem exists_two_linear_selections
    (A : ℕ → ℕ) (D N₀ : ℕ) (hD : 0 < D) (_hN₀ : 1 ≤ N₀)
    (hcount : ∀ N : ℕ, N₀ ≤ N → ∃ s : Finset ℕ,
      8 * D * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N) :
    ∃ β ρ : ℕ → ℕ,
      Function.Injective β ∧ Function.Injective ρ ∧
      Disjoint (Set.range β) (Set.range ρ) ∧
      ∃ I₀ : ℕ, ∀ i : ℕ, I₀ ≤ i →
        A (β i) ≤ i / D ∧ A (ρ i) ≤ i / D := by
  let Nstage : ℕ → ℕ := fun j ↦
    max N₀ (((j / 2) / (2 * D)) + 1)
  let P : ℕ → ℕ → Prop := fun j x ↦ A x ≤ Nstage j
  have havoid : ∀ j (u : Finset ℕ), u.card ≤ j →
      ∃ x, x ∉ u ∧ P j x := by
    intro j u hu
    have hNstage : N₀ ≤ Nstage j := Nat.le_max_left _ _
    obtain ⟨s, hscard, hsbox⟩ := hcount (Nstage j) hNstage
    have hden : 0 < 2 * D := by omega
    have hlt := Nat.lt_mul_div_succ (j / 2) hden
    have hright : (j / 2) / (2 * D) + 1 ≤ Nstage j :=
      Nat.le_max_right _ _
    have hjcard : j + 1 ≤ 8 * D * Nstage j := by
      calc
        j + 1 ≤ 4 * (j / 2 + 1) := by omega
        _ ≤ 4 * ((2 * D) * ((j / 2) / (2 * D) + 1)) :=
          Nat.mul_le_mul_left 4 (Nat.lt_iff_add_one_le.mp hlt)
        _ ≤ 4 * ((2 * D) * Nstage j) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (2 * D) hright)
        _ = 8 * D * Nstage j := by ring
    have hus : u.card < s.card := by omega
    obtain ⟨x, hxs, hxu⟩ := Finset.exists_mem_notMem_of_card_lt_card hus
    exact ⟨x, hxu, hsbox x hxs⟩
  obtain ⟨f, hf, hfP⟩ := exists_injective_of_finite_avoidance P havoid
  let β : ℕ → ℕ := fun i ↦ f (2 * i)
  let ρ : ℕ → ℕ := fun i ↦ f (2 * i + 1)
  have hβ : Function.Injective β := by
    intro i j hij
    exact Nat.mul_left_cancel (by omega) (hf hij)
  have hρ : Function.Injective ρ := by
    intro i j hij
    have hij' := hf hij
    omega
  have hdisj : Disjoint (Set.range β) (Set.range ρ) := by
    rw [Set.disjoint_range_iff]
    intro i j hij
    have hij' := hf hij
    omega
  refine ⟨β, ρ, hβ, hρ, hdisj, max (D * N₀) (2 * D), ?_⟩
  intro i hi
  have hiN₀ : D * N₀ ≤ i := (Nat.le_max_left _ _).trans hi
  have hi2D : 2 * D ≤ i := (Nat.le_max_right _ _).trans hi
  have hN₀div : N₀ ≤ i / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa [Nat.mul_comm] using hiN₀
  have hqpos : 1 ≤ i / (2 * D) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * D)).mpr
    simpa using hi2D
  have htwodiv : 2 * (i / (2 * D)) ≤ i / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    have h := Nat.mul_div_le i (2 * D)
    nlinarith
  have hstage : max N₀ (i / (2 * D) + 1) ≤ i / D := by
    apply max_le hN₀div
    exact (by omega : i / (2 * D) + 1 ≤ i / D)
  constructor
  · have heven : (2 * i) / 2 = i := by omega
    have hstageEven : Nstage (2 * i) ≤ i / D := by
      dsimp only [Nstage]
      rw [heven]
      exact hstage
    exact (hfP (2 * i)).trans hstageEven
  · have hodd : (2 * i + 1) / 2 = i := by omega
    have hstageOdd : Nstage (2 * i + 1) ≤ i / D := by
      dsimp only [Nstage]
      rw [hodd]
      exact hstage
    exact (hfP (2 * i + 1)).trans hstageOdd

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceSums.lean` -/

/-!
Finite subset sums indexed by occurrences. Equal weights retain separate indices.
-/

namespace Jsp285

variable {ι M : Type*} [AddCommMonoid M] [DecidableEq M]

/-- Sums of all subsets of a finite occurrence set. -/
def occurrenceSums (v : ι → M) (I : Finset ι) : Finset M :=
  I.powerset.image fun J ↦ ∑ i ∈ J, v i

/-- Membership exhibits the actual occurrences used, without identifying equal weights. -/
lemma mem_occurrenceSums {v : ι → M} {I : Finset ι} {x : M} :
    x ∈ occurrenceSums v I ↔ ∃ J ⊆ I, (∑ i ∈ J, v i) = x := by
  simp [occurrenceSums]

/-- The empty subset gives zero. -/
lemma zero_mem_occurrenceSums (v : ι → M) (I : Finset ι) :
    0 ∈ occurrenceSums v I := by
  exact mem_occurrenceSums.mpr ⟨∅, Finset.empty_subset _, by simp⟩

/-- Increasing the available occurrence set preserves every subset sum. -/
lemma occurrenceSums_mono (v : ι → M) {I J : Finset ι} (h : I ⊆ J) :
    occurrenceSums v I ⊆ occurrenceSums v J := by
  rintro x hx
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  exact mem_occurrenceSums.mpr ⟨K, hK.trans h, rfl⟩

/-- Sums supported on disjoint occurrence sets can be added without reuse. -/
lemma add_mem_occurrenceSums [DecidableEq ι] {v : ι → M} {I J : Finset ι}
    (hdisj : Disjoint I J) {x y : M}
    (hx : x ∈ occurrenceSums v I) (hy : y ∈ occurrenceSums v J) :
    x + y ∈ occurrenceSums v (I ∪ J) := by
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  obtain ⟨L, hL, rfl⟩ := mem_occurrenceSums.mp hy
  refine mem_occurrenceSums.mpr ⟨K ∪ L, Finset.union_subset_union hK hL, ?_⟩
  exact Finset.sum_union (hdisj.mono hK hL)

/-- With natural weights, every subset sum is bounded by the total mass. -/
lemma occurrenceSum_le_mass {v : ι → ℕ} {I : Finset ι} {x : ℕ}
    (hx : x ∈ occurrenceSums v I) : x ≤ ∑ i ∈ I, v i := by
  obtain ⟨J, hJ, rfl⟩ := mem_occurrenceSums.mp hx
  exact Finset.sum_le_sum_of_subset hJ

/-- Scaling each selected weight scales each subset sum. -/
lemma scale_mem_occurrenceSums {v w : ι → ℕ} {I J : Finset ι} {d x : ℕ}
    (hJI : J ⊆ I) (hscale : ∀ i ∈ J, d * w i = v i)
    (hx : x ∈ occurrenceSums w J) : d * x ∈ occurrenceSums v I := by
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  refine mem_occurrenceSums.mpr ⟨K, hK.trans hJI, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (hscale i (hK hi)).symm

end Jsp285

/-! ### Upstream module `Jsp285/InfiniteSums.lean` -/

/-! Finite occurrence subset sums drawn from a possibly infinite index set. -/

namespace Jsp285

/-- A finite selection of occurrence indices from `S`, with their actual weights. -/
def indexedSubsetSums {ι : Type*} (v : ι → ℕ) (S : Set ι) : Set ℕ :=
  {x | ∃ I : Finset ι, (↑I : Set ι) ⊆ S ∧ x = ∑ i ∈ I, v i}

/-- The finite and infinite representations agree on finite index sets. -/
lemma indexedSubsetSums_finset {ι : Type*} (v : ι → ℕ) (I : Finset ι) :
    indexedSubsetSums v (↑I : Set ι) = (occurrenceSums v I : Set ℕ) := by
  ext x
  simp only [indexedSubsetSums, Set.mem_ofPred_eq, Finset.coe_subset,
    Finset.mem_coe, mem_occurrenceSums]
  exact exists_congr fun J ↦ and_congr_right fun _ ↦ eq_comm

/-- Enlarging the allowed index set preserves each witnessed sum. -/
lemma indexedSubsetSums_mono {ι : Type*} (v : ι → ℕ) {S T : Set ι}
    (hST : S ⊆ T) : indexedSubsetSums v S ⊆ indexedSubsetSums v T := by
  rintro x ⟨I, hI, rfl⟩
  exact ⟨I, hI.trans hST, rfl⟩

/-- Disjoint occurrence supports permit adding their finite sums. -/
lemma add_mem_indexedSubsetSums {ι : Type*} (v : ι → ℕ) {S T : Set ι}
    (hST : Disjoint S T) {x y : ℕ}
    (hx : x ∈ indexedSubsetSums v S) (hy : y ∈ indexedSubsetSums v T) :
    x + y ∈ indexedSubsetSums v (S ∪ T) := by
  classical
  obtain ⟨I, hI, rfl⟩ := hx
  obtain ⟨J, hJ, rfl⟩ := hy
  have hIJ : Disjoint I J := Finset.disjoint_left.mpr fun i hi hj ↦
    Set.disjoint_left.mp hST (hI hi) (hJ hj)
  refine ⟨I ∪ J, ?_, (Finset.sum_union hIJ).symm⟩
  intro i hi
  exact (Finset.mem_union.mp hi).elim (fun h ↦ Or.inl (hI h))
    (fun h ↦ Or.inr (hJ h))

end Jsp285

/-! ### Upstream module `ErdosProblems/Erdos587/Erdos587Core.lean` -/

/-!
# Elementary additive-combinatorial core used by Erdős 344 and 360

This module separates the unconditional finite-group subset-sum machinery
from the analytic dependencies used later in `Erdos587.lean`.
-/

namespace Erdos587

/-! ## Modular subset-sum growth

The common-divisor branch can be obtained without a quadratic exponential
sum.  Starting from `{0}` in a finite additive group, adjoining a term either
strictly enlarges the set of reachable subset sums or translates that set to
itself.  There are at most `|G| - 1` strict enlargements.  Every term of the
second kind stabilizes the final reachable set; if that set is proper, these
terms therefore lie in a proper additive subgroup. -/

section ModularSubsetSumGrowth

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translate a finset in an additive group.  Keeping this operation explicit
avoids any ambiguity between pointwise addition and scalar actions. -/
def addTranslate (a : G) (S : Finset G) : Finset G :=
  S.image fun x => a + x

@[simp] lemma mem_addTranslate {a x : G} {S : Finset G} :
    x ∈ addTranslate a S ↔ -a + x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    have : y = -a + x := by
      rw [← hxy]
      abel
    simpa [this] using hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨-a + x, hx, ?_⟩
    abel

lemma card_addTranslate (a : G) (S : Finset G) :
    (addTranslate a S).card = S.card := by
  rw [addTranslate, Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

@[simp] lemma addTranslate_zero (S : Finset G) : addTranslate 0 S = S := by
  ext x
  simp [mem_addTranslate]

lemma addTranslate_add (a b : G) (S : Finset G) :
    addTranslate a (addTranslate b S) = addTranslate (a + b) S := by
  ext x
  simp only [mem_addTranslate]
  constructor <;> intro hx
  · convert hx using 1; abel
  · convert hx using 1; abel

lemma addTranslate_union (a : G) (S T : Finset G) :
    addTranslate a (S ∪ T) = addTranslate a S ∪ addTranslate a T := by
  ext x
  simp [mem_addTranslate]

/-- All subset sums of a list, with occurrences distinguished by the list
positions. -/
def listSubsetSums : List G → Finset G
  | [] => {0}
  | a :: A =>
      let S := listSubsetSums A
      S ∪ addTranslate a S

@[simp] lemma listSubsetSums_nil : listSubsetSums ([] : List G) = {0} := rfl

@[simp] lemma listSubsetSums_cons (a : G) (A : List G) :
    listSubsetSums (a :: A) =
      listSubsetSums A ∪ addTranslate a (listSubsetSums A) := rfl

lemma zero_mem_listSubsetSums (A : List G) : 0 ∈ listSubsetSums A := by
  induction A with
  | nil => simp
  | cons a A ih => simp [listSubsetSums, ih]

/-- Witness characterization of `listSubsetSums`. -/
lemma mem_listSubsetSums_iff {A : List G} {x : G} :
    x ∈ listSubsetSums A ↔ ∃ T : List G, T.Sublist A ∧ T.sum = x := by
  induction A generalizing x with
  | nil =>
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa [listSubsetSums] using hx
        subst x
        exact ⟨[], List.nil_sublist _, by simp⟩
      · rintro ⟨T, hT, rfl⟩
        have hTnil : T = [] := List.sublist_nil.mp hT
        subst T
        simp [listSubsetSums]
  | cons a A ih =>
      constructor
      · intro hx
        rw [listSubsetSums_cons, Finset.mem_union] at hx
        rcases hx with hx | hx
        · obtain ⟨T, hTA, rfl⟩ := ih.mp hx
          exact ⟨T, hTA.cons a, rfl⟩
        · rw [mem_addTranslate] at hx
          obtain ⟨T, hTA, hsum⟩ := ih.mp hx
          refine ⟨a :: T, hTA.cons_cons a, ?_⟩
          simp only [List.sum_cons]
          rw [hsum]
          abel
      · rintro ⟨T, hT, rfl⟩
        rw [listSubsetSums_cons, Finset.mem_union]
        rcases List.sublist_cons_iff.mp hT with hTA | ⟨U, rfl, hUA⟩
        · exact Or.inl (ih.mpr ⟨T, hTA, rfl⟩)
        · apply Or.inr
          rw [mem_addTranslate]
          apply ih.mpr
          refine ⟨U, hUA, ?_⟩
          simp

/-- Terms which do not enlarge the subset-sum set of the suffix. -/
def subsetSumStableTerms : List G → List G
  | [] => []
  | a :: A =>
      if addTranslate a (listSubsetSums A) = listSubsetSums A then
        a :: subsetSumStableTerms A
      else
        subsetSumStableTerms A

/-- Terms which strictly enlarge the subset-sum set of the suffix. -/
def subsetSumGrowthTerms : List G → List G
  | [] => []
  | a :: A =>
      if addTranslate a (listSubsetSums A) = listSubsetSums A then
        subsetSumGrowthTerms A
      else
        a :: subsetSumGrowthTerms A

/-- Stable and growth occurrences partition the original list, up to
permutation. -/
lemma stable_append_growth_perm (A : List G) :
    (subsetSumStableTerms A ++ subsetSumGrowthTerms A).Perm A := by
  induction A with
  | nil => exact List.Perm.nil
  | cons a A ih =>
      by_cases h : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumStableTerms, subsetSumGrowthTerms, h] using ih.cons a
      · have hmove :
            (subsetSumStableTerms A ++ a :: subsetSumGrowthTerms A).Perm
              (a :: subsetSumStableTerms A ++ subsetSumGrowthTerms A) := by
          simp
        simpa [subsetSumStableTerms, subsetSumGrowthTerms, h] using
          hmove.trans (ih.cons a)

/-- Once a term stabilizes the subset sums of a suffix, it also stabilizes
the subset sums after any earlier terms have been adjoined. -/
lemma mem_stable_stabilizes_listSubsetSums {A : List G} {b : G}
    (hb : b ∈ subsetSumStableTerms A) :
    addTranslate b (listSubsetSums A) = listSubsetSums A := by
  induction A with
  | nil => simp [subsetSumStableTerms] at hb
  | cons a A ih =>
      by_cases ha : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simp only [subsetSumStableTerms, ha, if_pos, List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp [listSubsetSums_cons, ha]
        · have hbstab := ih hb
          simpa [listSubsetSums_cons, ha] using hbstab
      · simp only [subsetSumStableTerms, ha] at hb
        have hbstab := ih hb
        rw [listSubsetSums_cons, addTranslate_union, hbstab,
          addTranslate_add, add_comm b a, ← addTranslate_add, hbstab]

/-- The number of strict growth terms is bounded by the number of reachable
residues minus one. -/
lemma growth_length_add_one_le_card_listSubsetSums (A : List G) :
    (subsetSumGrowthTerms A).length + 1 ≤ (listSubsetSums A).card := by
  induction A with
  | nil => simp [subsetSumGrowthTerms, listSubsetSums]
  | cons a A ih =>
      by_cases ha : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumGrowthTerms, listSubsetSums_cons, ha] using ih
      · have hproper : listSubsetSums A ⊂
            listSubsetSums A ∪ addTranslate a (listSubsetSums A) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
          intro heq
          have hsub : addTranslate a (listSubsetSums A) ⊆ listSubsetSums A := by
            intro x hx
            have : x ∈ listSubsetSums A ∪ addTranslate a (listSubsetSums A) :=
              Finset.mem_union_right _ hx
            rwa [← heq] at this
          exact ha (Finset.eq_of_subset_of_card_le hsub (by
            rw [card_addTranslate]))
        have hcard : (listSubsetSums A).card + 1 ≤
            (listSubsetSums (a :: A)).card := by
          have hlt := Finset.card_lt_card hproper
          simp only [listSubsetSums_cons]
          omega
        simp only [subsetSumGrowthTerms, ha, ite_false, List.length_cons]
        omega

/-- The subgroup of translations preserving a finite set. -/
def finsetAddStabilizer (S : Finset G) : AddSubgroup G where
  carrier := {a | addTranslate a S = S}
  zero_mem' := addTranslate_zero S
  add_mem' {a b} ha hb := by
    change addTranslate (a + b) S = S
    change addTranslate a S = S at ha
    change addTranslate b S = S at hb
    rw [← addTranslate_add, hb, ha]
  neg_mem' {a} ha := by
    change addTranslate (-a) S = S
    change addTranslate a S = S at ha
    calc
      addTranslate (-a) S = addTranslate (-a) (addTranslate a S) := by rw [ha]
      _ = addTranslate (-a + a) S := addTranslate_add _ _ _
      _ = S := by simp

@[simp] lemma mem_finsetAddStabilizer {S : Finset G} {a : G} :
    a ∈ finsetAddStabilizer S ↔ addTranslate a S = S := Iff.rfl

/-- A proper nonempty finset has a proper translation stabilizer. -/
lemma finsetAddStabilizer_ne_top [Fintype G] {S : Finset G}
    (hS0 : 0 ∈ S) (hSproper : S ≠ Finset.univ) :
    finsetAddStabilizer S ≠ ⊤ := by
  intro htop
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hxstab : x ∈ finsetAddStabilizer S := by rw [htop]; simp
  have hxmem : x + 0 ∈ addTranslate x S := by
    exact Finset.mem_image.mpr ⟨0, hS0, rfl⟩
  rw [mem_finsetAddStabilizer.mp hxstab] at hxmem
  simpa using hxmem

end ModularSubsetSumGrowth

end Erdos587

/-! ### Upstream module `ErdosProblems/Erdos13/Erdos13MulStab.lean` -/

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

open _root_.Function MulAction
open scoped Pointwise

section
open _root_.Finset
variable {ι α : Type*}

local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

open _root_.Finset in
/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/
@[to_additive /-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/]
def _root_.Finset.mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

@[to_additive] protected alias ⟨_, _root_.Finset.Nonempty.one_mem_mulStab⟩ := one_mem_mulStab

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, h.one_mem_mulStab⟩

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton h.one_mem_mulStab

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine fun b hb ↦ mem_div.2 ⟨_, mem_singleton_self _, _, ?_, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

open _root_.Finset in
@[to_additive (attr := simp)]
lemma _root_.Finset.mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' (s +ˢ stabilizer α (t : Set α)) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

open _root_.Finset in
omit [DecidableEq α] in
@[to_additive]
lemma _root_.Finset.preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' (s +ˢ stabilizer α (s : Set α)) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.card_mulStab_le_card : #s.mulStab ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

open _root_.Finset in
/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/
@[to_additive (attr := implicit_reducible)
/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.addStab`. -/]
private def _root_.Finset.fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  let _ : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  let _ : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

open _root_.Finset in
/-- A version of Lagrange's theorem. -/
@[to_additive /-- A version of Lagrange's theorem. -/]
lemma _root_.Finset.card_mulStab_mul_card_image_coe' (s t : Finset α)
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
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

open _root_.Finset in
/-- A version of Lagrange's theorem. -/
@[to_additive /-- A version of Lagrange's theorem. -/]
lemma _root_.Finset.card_mulStab_mul_card_image_coe (s t : Finset α) :
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #(t +ₛ s) = #t := by
  suffices h : (t : Set α) * s = t by
    simpa [h, eq_comm] using s.card_mul_eq_card_subgroup_mul_card_quotient  t
  apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
  · intro x
    rw [Set.mem_mul]
    aesop
  · rw [← coe_mul, mul_mulStab]

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_quotient_commute_subgroup (s : Subgroup α) [DecidablePred (· ∈ s)] (t : Finset α)
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

/-! ### Upstream module `ErdosProblems/Erdos13/Erdos13Kneser.lean` -/

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

open _root_.Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

section
/-! ### Auxiliary results -/

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.mul_aux1
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose! has
  exact subset_trans has hst

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
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

open _root_.Finset in
@[to_additive]
lemma _root_.Finset.inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
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

open _root_.Finset in
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

open _root_.Finset in
/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/
@[to_additive /-- **Kneser's addition theorem**: A lower bound on the size of `s + t` in terms of
its stabilizer. -/]
theorem _root_.Finset.mul_kneser :
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
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
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

open _root_.Finset in
/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/
@[to_additive /-- The strict version of **Kneser's addition theorem**. If the LHS of
`Finset.add_kneser` does not equal the RHS, then it is in fact much smaller. -/]
lemma _root_.Finset.mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _

end

end

/-! ### Upstream module `ErdosProblems/Erdos13/Erdos13Additive.lean` -/

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

open _root_.Finset _root_.Nat
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
    (_ha : a ≤ b) (hb : b ≤ M) : holesIcc S a b ⊆ holes S M := by
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
    (_hA : A ⊆ Icc 0 M) (_hB : B ⊆ Icc 0 N) (_hxN : x ≤ N)
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
    · exact mem_union_left _ (by simp [X, U, hb, ha])
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
    · exact mem_union_left _ (by simp [X, U, hb, ha])
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
    (hMN : N ≤ M) (_hA : A ⊆ Icc 0 M) (hB : B ⊆ Icc 0 N)
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
    · exact mem_union_left _ (by simp [X, U, hb, ha])
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
    (hA0 : 0 ∈ A) (hAM : M ∈ A) (_hB0 : 0 ∈ B) (_hBN : N ∈ B)
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
    (hA : A ⊆ Icc 0 u) (_huv : u ≤ v) (hv : 0 < v)
    (_hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
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
    (h0 : 0 ∈ S) (_hvS : v ∈ S) : modImage (S.erase v) v = modImage S v := by
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
  let _ : NeZero v := ⟨Nat.ne_of_gt hv⟩
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
    (_hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m) :
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

/-! ### Upstream module `ErdosProblems/Erdos360/Core.lean` -/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-! ### Almost-period estimates -/

/-! ### Extending an interval of subset sums -/

/-! ### Kneser growth for a set escaping proper cosets -/

end Erdos360

/-! ### Upstream module `ErdosProblems/Erdos697/Erdos697Bernoulli.lean` -/

/-!
# Sharp finite Bernoulli tail estimates for Erdős Problem 697

The CRT model in the main argument gives independent, non-identically
distributed Bernoulli variables.  The lemmas below prove Chernoff bounds
directly as identities and inequalities between finite sums over a
powerset.  The cutoff ratios are arbitrary fixed `r < 1` and `r > 1`;
this flexibility is what preserves Hall's sharp constant.
-/

namespace Erdos697.Bernoulli

noncomputable section

/-- The probability weight of the subset `T` in the independent Bernoulli
model indexed by `s`.  The definition is meaningful for every `T`; all
applications restrict to `T ⊆ s`. -/
def weight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (T : Finset ι) : ℝ :=
  (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)

theorem weight_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {T : Finset ι} (hT : T ∈ s.powerset) : 0 ≤ weight s p T := by
  have hsub : T ⊆ s := Finset.mem_powerset.mp hT
  exact mul_nonneg
    (Finset.prod_nonneg (fun i hi => hp0 i (hsub hi)))
    (Finset.prod_nonneg (fun i hi => by
      have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
      linarith [hp1 i his]))

/-- Exact probability-generating-function identity. -/
theorem sum_pow_card_mul_weight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (a : ℝ) :
    (∑ T ∈ s.powerset, a ^ T.card * weight s p T) =
      ∏ i ∈ s, ((1 - p i) + p i * a) := by
  unfold weight
  calc
    (∑ T ∈ s.powerset,
        a ^ T.card * ((∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i))) =
        ∏ i ∈ s, (p i * a + (1 - p i)) := by
          rw [Finset.prod_add]
          apply Finset.sum_congr rfl
          intro T _
          have hprod_mul :
              (∏ i ∈ T, p i * a) =
                (∏ i ∈ T, p i) * a ^ T.card := by
            rw [Finset.prod_mul_distrib]
            simp [Finset.prod_const]
          rw [hprod_mul]
          ring
    _ = ∏ i ∈ s, ((1 - p i) + p i * a) := by
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- A lower-tail Chernoff bound at every fixed proportion `r < 1` of the
mean.  The explicit coefficient multiplying `EW` is strictly negative;
see `lower_exponent_neg`. -/
theorem lower_tail_chernoff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW r : ℝ} (hEW : EW = ∑ i ∈ s, p i)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hK : (K : ℝ) ≤ r * EW) :
    (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T) ≤
      Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
  classical
  let t : ℝ := (1 - r) / (2 * r)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := 1 / (1 + t) - 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have honept : 0 < 1 + t := by linarith
  have ha_le : a ≤ 1 / (1 + t) := by
    have hexp : 1 + t ≤ Real.exp t := by
      simpa [add_comm] using Real.add_one_le_exp t
    have hinv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ :=
      inv_anti₀ honept hexp
    simpa [a, Real.exp_neg, one_div] using hinv
  have hb_nonpos : b ≤ 0 := by
    dsimp [b]
    have : 1 / (1 + t) ≤ 1 := (div_le_one₀ honept).2 (by linarith)
    linarith
  have hfactor_nonneg : ∀ i ∈ s, 0 ≤ (1 - p i) + p i * a := by
    intro i hi
    nlinarith [hp0 i hi, hp1 i hi,
      mul_nonneg (hp0 i hi) ha_nonneg]
  have hfactor_le : ∀ i ∈ s,
      (1 - p i) + p i * a ≤ Real.exp (b * p i) := by
    intro i hi
    have hpa : p i * a ≤ p i * (1 / (1 + t)) :=
      mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
    calc
      (1 - p i) + p i * a
          ≤ (1 - p i) + p i * (1 / (1 + t)) := by linarith
      _ = 1 + b * p i := by dsimp [b]; ring
      _ = b * p i + 1 := by ring
      _ ≤ Real.exp (b * p i) := Real.add_one_le_exp _
  have hgen_le :
      (∑ T ∈ s.powerset, a ^ T.card * weight s p T) ≤
        Real.exp (b * EW) := by
    rw [sum_pow_card_mul_weight]
    calc
      ∏ i ∈ s, ((1 - p i) + p i * a)
          ≤ ∏ i ∈ s, Real.exp (b * p i) :=
            Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (b * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, ← hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T) ≤
        Real.exp (t * (K : ℝ)) *
          (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T)
          ≤ ∑ T ∈ s.powerset.filter (fun T => T.card < K),
              Real.exp (t * (K : ℝ)) *
                (a ^ T.card * weight s p T) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTpowerset : T ∈ s.powerset :=
              (Finset.mem_filter.mp hT).1
            have hTcard : T.card ≤ K :=
              Nat.le_of_lt (Finset.mem_filter.mp hT).2
            have hscale :
                1 ≤ Real.exp (t * (K : ℝ)) * a ^ T.card := by
              dsimp [a]
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.one_le_exp
              have hcast : (T.card : ℝ) ≤ K := by exact_mod_cast hTcard
              nlinarith
            have hwT : 0 ≤ weight s p T :=
              weight_nonneg s p hp0 hp1 hTpowerset
            calc
              weight s p T
                  ≤ (Real.exp (t * (K : ℝ)) * a ^ T.card) *
                      weight s p T := le_mul_of_one_le_left hwT hscale
              _ = Real.exp (t * (K : ℝ)) *
                    (a ^ T.card * weight s p T) := by ring
      _ = Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset.filter (fun T => T.card < K),
              a ^ T.card * weight s p T) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro T hT
                exact (Finset.mem_filter.mp hT).1
              · intro T hTpowerset _
                exact mul_nonneg (pow_nonneg ha_nonneg _)
                  (weight_nonneg s p hp0 hp1 hTpowerset)
            · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => T.card < K), weight s p T)
        ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := htail_le_gen
    _ ≤ Real.exp (t * (K : ℝ)) * Real.exp (b * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp (t * (K : ℝ) + b * EW) := by rw [Real.exp_add]
    _ ≤ Real.exp ((r * t + b) * EW) := by
      apply Real.exp_le_exp.mpr
      have hEW_nonneg : 0 ≤ EW := by
        rw [hEW]
        exact Finset.sum_nonneg (fun i hi => hp0 i hi)
      nlinarith
    _ = Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
      rfl

/-- An upper-tail Chernoff bound at every fixed proportion `r > 1` of the
mean.  The explicit coefficient multiplying `EW` is strictly negative;
see `upper_exponent_neg`. -/
theorem upper_tail_chernoff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW r : ℝ} (hEW : EW = ∑ i ∈ s, p i)
    (hr : 1 < r)
    (hK : r * EW ≤ (K : ℝ)) :
    (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T) ≤
      Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
            (1 / (1 - ((r - 1) / (2 * r))) - 1)) * EW) := by
  classical
  let t : ℝ := (r - 1) / (2 * r)
  let a : ℝ := Real.exp t
  let b : ℝ := 1 / (1 - t) - 1
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_lt_one : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity : 0 < 2 * r)]
    linarith
  have hone_sub_t : 0 < 1 - t := sub_pos.mpr ht_lt_one
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have ha_le : a ≤ 1 / (1 - t) := by
    have hexp : 1 - t ≤ Real.exp (-t) := by
      convert Real.add_one_le_exp (-t) using 1
      ring
    have hinv : (Real.exp (-t))⁻¹ ≤ (1 - t)⁻¹ :=
      inv_anti₀ hone_sub_t hexp
    simpa [a, Real.exp_neg, one_div] using hinv
  have hfactor_nonneg : ∀ i ∈ s, 0 ≤ (1 - p i) + p i * a := by
    intro i hi
    nlinarith [hp0 i hi, hp1 i hi,
      mul_nonneg (hp0 i hi) ha_nonneg]
  have hfactor_le : ∀ i ∈ s,
      (1 - p i) + p i * a ≤ Real.exp (b * p i) := by
    intro i hi
    have hpa : p i * a ≤ p i * (1 / (1 - t)) :=
      mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
    calc
      (1 - p i) + p i * a
          ≤ (1 - p i) + p i * (1 / (1 - t)) := by linarith
      _ = 1 + b * p i := by dsimp [b]; ring
      _ = b * p i + 1 := by ring
      _ ≤ Real.exp (b * p i) := Real.add_one_le_exp _
  have hgen_le :
      (∑ T ∈ s.powerset, a ^ T.card * weight s p T) ≤
        Real.exp (b * EW) := by
    rw [sum_pow_card_mul_weight]
    calc
      ∏ i ∈ s, ((1 - p i) + p i * a)
          ≤ ∏ i ∈ s, Real.exp (b * p i) :=
            Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (b * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, ← hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T) ≤
        Real.exp (-(t * (K : ℝ))) *
          (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T)
          ≤ ∑ T ∈ s.powerset.filter (fun T => K ≤ T.card),
              Real.exp (-(t * (K : ℝ))) *
                (a ^ T.card * weight s p T) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTpowerset : T ∈ s.powerset :=
              (Finset.mem_filter.mp hT).1
            have hTcard : K ≤ T.card := (Finset.mem_filter.mp hT).2
            have hscale :
                1 ≤ Real.exp (-(t * (K : ℝ))) * a ^ T.card := by
              dsimp [a]
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.one_le_exp
              have hcast : (K : ℝ) ≤ T.card := by exact_mod_cast hTcard
              nlinarith
            have hwT : 0 ≤ weight s p T :=
              weight_nonneg s p hp0 hp1 hTpowerset
            calc
              weight s p T
                  ≤ (Real.exp (-(t * (K : ℝ))) * a ^ T.card) *
                      weight s p T := le_mul_of_one_le_left hwT hscale
              _ = Real.exp (-(t * (K : ℝ))) *
                    (a ^ T.card * weight s p T) := by ring
      _ = Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card),
              a ^ T.card * weight s p T) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro T hT
                exact (Finset.mem_filter.mp hT).1
              · intro T hTpowerset _
                exact mul_nonneg (pow_nonneg ha_nonneg _)
                  (weight_nonneg s p hp0 hp1 hTpowerset)
            · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => K ≤ T.card), weight s p T)
        ≤ Real.exp (-(t * (K : ℝ))) *
            (∑ T ∈ s.powerset, a ^ T.card * weight s p T) := htail_le_gen
    _ ≤ Real.exp (-(t * (K : ℝ))) * Real.exp (b * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp (-(t * (K : ℝ)) + b * EW) := by rw [Real.exp_add]
    _ ≤ Real.exp ((-(r * t) + b) * EW) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
            (1 / (1 - ((r - 1) / (2 * r))) - 1)) * EW) := by
      rfl

/-! ## Odds factorization -/

end

end Erdos697.Bernoulli

/-! ### Upstream module `ErdosProblems/Erdos344.lean` -/

/-!
# Erdős Problem 344

The mathematical proof and the formal dependency map are in `tex/344.tex`.
-/

namespace Erdos344

open scoped Pointwise _root_.Topology

attribute [local instance] Classical.propDecidable
noncomputable local instance (A : Set ℕ) : DecidablePred A := Classical.decPred A

/-- `S` contains a nonconstant finite arithmetic progression of length `k`. -/
def ContainsFiniteAP (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- `S` contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ S

/-- A set has arbitrarily long finite progressions with one fixed positive
common difference. -/
def HasFixedStepProgressions (S : Set ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ, ∃ a : ℕ, ∀ i < k, a + i * d ∈ S

/-- An additive `q`-net with width `K`: every interval
`[n*q, (n+K)*q]` contains a member of `S` divisible by `q`. -/
def IsAddNet (q K : ℕ) (S : Set ℕ) : Prop :=
  0 < q ∧ ∀ n : ℕ, ∃ s ∈ S, q ∣ s ∧ n * q ≤ s ∧ s ≤ (n + K) * q

lemma containsFiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T) {k : ℕ}
    (hS : ContainsFiniteAP S k) : ContainsFiniteAP T k := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i hi ↦ hST (h i hi)⟩

lemma containsInfiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T)
    (hS : ContainsInfiniteAP S) : ContainsInfiniteAP T := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i ↦ hST (h i)⟩

/-! ### Counting and increasing enumerations -/

lemma addNet_add_finiteAP {S T : Set ℕ} {q K a : ℕ}
    (hnet : IsAddNet q K T)
    (hAP : ∀ i < K + 1, a + i * q ∈ S) :
    ContainsInfiniteAP (S + T) := by
  refine ⟨a + K * q, q, hnet.1, ?_⟩
  intro n
  obtain ⟨s, hsT, hq, hlo, hhi⟩ := hnet.2 n
  obtain ⟨t, rfl⟩ := hq
  have hnle : n ≤ t := by
    rw [Nat.mul_comm n q] at hlo
    exact Nat.le_of_mul_le_mul_left hlo hnet.1
  have htle : t ≤ n + K := by
    rw [Nat.mul_comm (n + K) q] at hhi
    exact Nat.le_of_mul_le_mul_left hhi hnet.1
  let i := n + K - t
  have hiK : i ≤ K := by
    dsimp [i]
    omega
  have hi : i < K + 1 := by omega
  have hit : i + t = n + K := by
    dsimp [i]
    omega
  have hsum : (a + i * q) + q * t = (a + K * q) + n * q := by
    calc
      (a + i * q) + q * t = a + (i + t) * q := by ring
      _ = a + (n + K) * q := by rw [hit]
      _ = (a + K * q) + n * q := by ring
  rw [← hsum]
  exact ⟨a + i * q, hAP i hi, q * t, hsT, rfl⟩

/-! ### Lowering a finite progression's common difference -/

/-- Explicit membership form of common-difference lowering. -/
lemma lowerStep_of_residue_translates_mem {S U : Set ℕ}
    {a q M L Z : ℕ} (_hq : 0 < q) (hM : 0 < M)
    (hAP : ∀ j < L, a + j * (q * M) ∈ S)
    (hres : ∀ i < M, ∃ u ∈ U, ∃ z ≤ Z, u = i * q + (q * M) * z) :
    ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈ S + U := by
  intro n hn
  let i := n % M
  let k := n / M
  have hi : i < M := Nat.mod_lt n hM
  obtain ⟨u, huU, z, hzZ, rfl⟩ := hres i hi
  let j := Z + k - z
  have hk : k < L - Z := by
    apply (Nat.div_lt_iff_lt_mul hM).2
    simpa [Nat.mul_comm] using hn
  have hzsum : z ≤ Z + k := hzZ.trans (Nat.le_add_right Z k)
  have hjEq : j + z = Z + k := by
    dsimp [j]
    omega
  have hsubpos : 0 < L - Z := (Nat.zero_le k).trans_lt hk
  have hZL : Z ≤ L := (Nat.sub_pos_iff_lt.mp hsubpos).le
  have hsubadd : L - Z + Z = L := Nat.sub_add_cancel hZL
  have hjL : j < L := by
    dsimp [j]
    omega
  have hnDecomp : n = k * M + i := by
    simpa [k, i] using (Nat.div_add_mod' n M).symm
  have hsum :
      (a + j * (q * M)) + (i * q + (q * M) * z) =
        (a + (q * M) * Z) + n * q := by
    calc
      (a + j * (q * M)) + (i * q + (q * M) * z) =
          a + (j + z) * (q * M) + i * q := by ring
      _ = a + (Z + k) * (q * M) + i * q := by rw [hjEq]
      _ = (a + (q * M) * Z) + (k * M + i) * q := by ring
      _ = (a + (q * M) * Z) + n * q := by rw [← hnDecomp]
  rw [← hsum]
  exact ⟨a + j * (q * M), hAP j hjL,
    i * q + (q * M) * z, huU, rfl⟩

/-! ### Graham's bounded-gap argument, in a finite coverage form -/

private def prefixSum (y : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, y i

/-! ### Subgroups of a finite cyclic group -/

/-- Every additive subgroup of `ZMod d` consists exactly of the multiples
of a positive divisor `q` of `d`.  The formulation records the two directions
needed for the residue-stabilization argument below. -/
lemma exists_generator_modulus {d : ℕ} (hd : 0 < d)
    (K : AddSubgroup (ZMod d)) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧
      (∀ x : ZMod d, x ∈ K → q ∣ x.val) ∧
      (∀ i : ℕ, (i * q : ZMod d) ∈ K) := by
  let : NeZero d := ⟨hd.ne'⟩
  let V := Finset.univ.filter fun x : ZMod d ↦ x ∈ K ∧ x ≠ 0
  by_cases hV : V.Nonempty
  · obtain ⟨g, hgV, hgmin⟩ := Finset.exists_min_image V ZMod.val hV
    have hgK : g ∈ K := (Finset.mem_filter.mp hgV).2.1
    have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgV).2.2
    let q := g.val
    have hqpos : 0 < q :=
      Nat.pos_of_ne_zero (fun h ↦ hg0 ((ZMod.val_eq_zero g).mp h))
    have hqd : q < d := g.val_lt
    have hmin : ∀ x : ZMod d, x ∈ K → x ≠ 0 → q ≤ x.val := by
      intro x hxK hx0
      exact hgmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hx0⟩)
    have hcastg : (q : ZMod d) = g := ZMod.natCast_zmod_val g
    have hqdvd : q ∣ d := by
      let r := d % q
      have hrq : r < q := Nat.mod_lt d hqpos
      have hrd : r < d := hrq.trans hqd
      have hsumZ : ((d / q * q : ℕ) : ZMod d) + (r : ZMod d) = 0 := by
        have hsum := congrArg (fun n : ℕ ↦ (n : ZMod d)) (Nat.div_add_mod' d q)
        push_cast at hsum
        simpa [r] using hsum
      have hcast : (r : ZMod d) = -((d / q : ℕ) • g) := by
        rw [← hcastg]
        simp only [nsmul_eq_mul]
        apply (eq_neg_iff_add_eq_zero).2
        simpa [add_comm] using hsumZ
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.neg_mem (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    refine ⟨q, hqpos, hqdvd, ?_, ?_⟩
    · intro x hxK
      let r := x.val % q
      have hrq : r < q := Nat.mod_lt x.val hqpos
      have hrd : r < d := hrq.trans hqd
      have hmul : x.val / q * q ≤ x.val := by
        simpa [mul_comm] using Nat.mul_div_le x.val q
      have hdecomp : x.val % q + x.val / q * q = x.val := by
        simpa [mul_comm] using Nat.mod_add_div x.val q
      have hsub : x.val - x.val / q * q = r := by
        dsimp [r]
        omega
      have hcast : (r : ZMod d) = x - (x.val / q : ℕ) • g := by
        calc
          (r : ZMod d) = ((x.val - x.val / q * q : ℕ) : ZMod d) := by rw [hsub]
          _ = (x.val : ZMod d) - (x.val / q * q : ℕ) := by
            rw [Nat.cast_sub hmul]
          _ = x - (x.val / q : ℕ) • g := by
            rw [ZMod.natCast_zmod_val x, Nat.cast_mul, hcastg]
            simp [nsmul_eq_mul]
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.sub_mem hxK (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    · intro i
      have hi : (i * q : ZMod d) = i • g := by
        rw [← hcastg]
        simp [nsmul_eq_mul]
      rw [hi]
      exact K.nsmul_mem hgK i
  · refine ⟨d, hd, dvd_rfl, ?_, ?_⟩
    · intro x hxK
      have hx0 : x = 0 := by
        by_contra hxne
        exact hV ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hxne⟩⟩
      rw [hx0]
      simp
    · intro i
      simp

/-! ### Divisor-sensitive modular completeness -/

/-- A homomorphism sends the subset sums of a list onto the subset sums of
the mapped list. -/
lemma image_listSubsetSums_map {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
    (f : G →+ H) (A : List G) :
    (Erdos587.listSubsetSums A).image f =
      Erdos587.listSubsetSums (A.map f) := by
  have image_addTranslate (a : G) (S : Finset G) :
      (Erdos587.addTranslate a S).image f =
        Erdos587.addTranslate (f a) (S.image f) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      rw [Erdos587.mem_addTranslate] at hx ⊢
      apply Finset.mem_image.mpr
      refine ⟨-a + x, hx, ?_⟩
      rw [map_add, map_neg, hxy]
    · intro hy
      rw [Erdos587.mem_addTranslate] at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨a + x, ?_, ?_⟩
      · rw [Erdos587.mem_addTranslate]
        simpa
      · rw [map_add, hxy]
        abel
  induction A with
  | nil => simp [Erdos587.listSubsetSums]
  | cons a A ih =>
      simp only [Erdos587.listSubsetSums_cons, List.map_cons,
        Finset.image_union, ih]
      rw [image_addTranslate, ih]

lemma zmod_castHom_eq_zero_iff_val_dvd {q d : ℕ} [NeZero q]
    (hdq : d ∣ q) (x : ZMod q) :
    ZMod.castHom hdq (ZMod d) x = 0 ↔ d ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- If a surjective homomorphism has exactly the translation stabilizer of
`S` as its kernel, the image of `S` has trivial translation stabilizer. -/
lemma image_stabilizer_eq_bot {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Finite G]
    [AddCommGroup H] [DecidableEq H] [Finite H]
    (f : G →+ H) (hf : Function.Surjective f) (S : Finset G)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    Erdos587.finsetAddStabilizer (S.image f) = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hy' : Erdos587.addTranslate (f x) (S.image f) = S.image f := hy
  have hxsub : Erdos587.addTranslate x S ⊆ S := by
    intro z hz
    have hs : -x + z ∈ S := Erdos587.mem_addTranslate.mp hz
    have hfs : f (-x + z) ∈ S.image f :=
      Finset.mem_image.mpr ⟨_, hs, rfl⟩
    have hfztrans : f z ∈ Erdos587.addTranslate (f x) (S.image f) := by
      apply Finset.mem_image.mpr
      refine ⟨f (-x + z), hfs, ?_⟩
      simp only [map_add, map_neg]
      abel
    rw [hy'] at hfztrans
    obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfztrans
    have hzero : f (z - t) = 0 := by
      rw [map_sub, hft]
      simp
    have hstab : z - t ∈ Erdos587.finsetAddStabilizer S :=
      (hker _).mp hzero
    have hmem : (z - t) + t ∈ Erdos587.addTranslate (z - t) S := by
      apply Finset.mem_image.mpr
      exact ⟨t, ht, rfl⟩
    rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
    simpa using hmem
  have hxstab : Erdos587.addTranslate x S = S := by
    exact Finset.eq_of_subset_of_card_le hxsub (by
      rw [Erdos587.card_addTranslate])
  have hxker : f x = 0 := (hker x).mpr hxstab
  simp [hxker]

/-- Under the same kernel hypothesis, a proper set has proper image. -/
lemma image_ne_univ_of_stabilizer_kernel {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (S : Finset G) (hSproper : S ≠ Finset.univ)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    S.image f ≠ Finset.univ := by
  intro himage
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hfx : f x ∈ S.image f := by rw [himage]; simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfx
  have hzero : f (x - t) = 0 := by rw [map_sub, hft]; simp
  have hstab : x - t ∈ Erdos587.finsetAddStabilizer S :=
    (hker _).mp hzero
  have hmem : (x - t) + t ∈ Erdos587.addTranslate (x - t) S := by
    apply Finset.mem_image.mpr
    exact ⟨t, ht, rfl⟩
  rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
  simpa using hmem

/-- If the final subset-sum stabilizer is trivial and the subset sums are
proper, fewer than `|G|-1` list occurrences are nonzero. -/
lemma nonzero_length_add_one_lt_card_of_stabilizer_bot
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : List G)
    (hproper : Erdos587.listSubsetSums A ≠ Finset.univ)
    (hstab : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums A) = ⊥) :
    (A.filter fun a => a ≠ 0).length + 1 < Fintype.card G := by
  have hstable :
      (Erdos587.subsetSumStableTerms A).filter (fun a => a ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have haStab : a ∈ Erdos587.finsetAddStabilizer
        (Erdos587.listSubsetSums A) :=
      Erdos587.mem_stable_stabilizes_listSubsetSums ha
    rw [hstab] at haStab
    simpa using haStab
  have hperm :=
    (Erdos587.stable_append_growth_perm A).filter (fun a => a ≠ 0)
  have hlen :
      (A.filter fun a => a ≠ 0).length ≤
        (Erdos587.subsetSumGrowthTerms A).length := by
    rw [← hperm.length_eq, List.filter_append, hstable]
    exact List.length_filter_le _ _
  have hcardlt : (Erdos587.listSubsetSums A).card < Fintype.card G := by
    have hss : Erdos587.listSubsetSums A ⊂ (Finset.univ : Finset G) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩
    exact Finset.card_lt_card hss
  have hgrowth := Erdos587.growth_length_add_one_le_card_listSubsetSums A
  omega

lemma length_filter_zmod_castHom_ne_zero
    {q d : ℕ} [NeZero q] [NeZero d] (hdq : d ∣ q) (A : List ℕ) :
    ((A.map fun a : ℕ => ZMod.castHom hdq (ZMod d) (a : ZMod q)).filter
      fun x => x ≠ 0).length =
      (A.filter fun a => ¬ d ∣ a).length := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.map_cons, map_natCast]
      have ih' :
          ((A.map fun a : ℕ => (a : ZMod d)).filter fun x => x ≠ 0).length =
            (A.filter fun a => ¬ d ∣ a).length := by
        simpa only [map_natCast] using ih
      by_cases ha : d ∣ a
      · have ha0 : (a : ZMod d) = 0 :=
          (ZMod.natCast_eq_zero_iff a d).mpr ha
        rw [List.filter_cons_of_neg (by simpa using ha0),
          List.filter_cons_of_neg (by simpa using ha)]
        exact ih'
      · have ha0 : (a : ZMod d) ≠ 0 :=
          fun h => ha ((ZMod.natCast_eq_zero_iff a d).mp h)
        rw [List.filter_cons_of_pos (by simp [ha0]),
          List.filter_cons_of_pos (by simp [ha]),
          List.length_cons, List.length_cons, ih']

/-- A divisor-diverse list is complete modulo `q`.  This is the
Conlon--Fox--Pham modular completeness criterion: for every divisor `d > 1`
of `q`, `d - 1` nonmultiples force all residues to occur as subset sums. -/
theorem listSubsetSums_mod_eq_univ_of_divisor_diverse
    {q : ℕ} [NeZero q] (hq : 0 < q) (A : List ℕ)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ (A.filter fun a => ¬ d ∣ a).length) :
    Erdos587.listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) =
      Finset.univ := by
  let M : List (ZMod q) := A.map fun a : ℕ => (a : ZMod q)
  let S : Finset (ZMod q) := Erdos587.listSubsetSums M
  by_contra hproper
  have hproperS : S ≠ Finset.univ := by simpa [S, M] using hproper
  let K : AddSubgroup (ZMod q) := Erdos587.finsetAddStabilizer S
  have hKproper : K ≠ ⊤ :=
    Erdos587.finsetAddStabilizer_ne_top
      (by simpa [S] using Erdos587.zero_mem_listSubsetSums M) hproperS
  obtain ⟨d, hdpos, hdq, hKdiv, hmultK⟩ := exists_generator_modulus hq K
  have hdgt : 1 < d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    apply hKproper
    apply top_unique
    intro x _
    rw [← ZMod.natCast_zmod_val x]
    simpa [hd1] using hmultK x.val
  let : NeZero d := ⟨hdpos.ne'⟩
  let f : ZMod q →+ ZMod d :=
    (ZMod.castHom hdq (ZMod d)).toAddMonoidHom
  have hfsurj : Function.Surjective f := by
    intro y
    refine ⟨(y.val : ZMod q), ?_⟩
    have hdqle : d ≤ q := Nat.le_of_dvd hq hdq
    have hyq : y.val < q := y.val_lt.trans_le hdqle
    dsimp [f]
    rw [ZMod.cast_eq_val, ZMod.val_natCast, Nat.mod_eq_of_lt hyq]
    exact ZMod.natCast_zmod_val y
  have hker : ∀ x : ZMod q,
      f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S := by
    intro x
    constructor
    · intro hx
      have hdval : d ∣ x.val :=
        (zmod_castHom_eq_zero_iff_val_dvd hdq x).mp (by
          simpa [f] using hx)
      obtain ⟨i, hi⟩ := hdval
      have hxrepr : x = (i * d : ℕ) := by
        calc
          x = (x.val : ZMod q) := (ZMod.natCast_zmod_val x).symm
          _ = (d * i : ℕ) := by rw [hi]
          _ = (i * d : ℕ) := by rw [mul_comm]
      rw [hxrepr]
      change ((i * d : ℕ) : ZMod q) ∈ K
      simpa only [Nat.cast_mul] using hmultK i
    · intro hx
      apply (zmod_castHom_eq_zero_iff_val_dvd hdq x).mpr
      exact hKdiv x hx
  let B : List (ZMod d) := M.map f
  have himage : S.image f = Erdos587.listSubsetSums B := by
    simpa [S, B] using image_listSubsetSums_map f M
  have hproperB : Erdos587.listSubsetSums B ≠ Finset.univ := by
    intro hall
    have himageProper := image_ne_univ_of_stabilizer_kernel
      f S hproperS hker
    apply himageProper
    rw [himage, hall]
  have hstabB : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums B) = ⊥ := by
    have hstab := image_stabilizer_eq_bot f hfsurj S hker
    rwa [himage] at hstab
  have hfew := nonzero_length_add_one_lt_card_of_stabilizer_bot
    B hproperB hstabB
  have hfew' : (B.filter fun a => a ≠ 0).length + 1 < d := by
    simpa [ZMod.card] using hfew
  have hfilter :
      (B.filter fun a => a ≠ 0).length =
        (A.filter fun a => ¬ d ∣ a).length := by
    simpa [B, M, f, List.map_map, Function.comp_def] using
      length_filter_zmod_castHom_ne_zero hdq A
  rw [hfilter] at hfew'
  have hlower := hdiverse d hdgt hdq
  omega

/-! ### The unsaturated modular-growth step -/

/-! ### Coset fibres of ordinary finite subset sums -/

/-! ### The cyclic modulus attached to a remaining phase set -/

/-! ### The deterministic modular phase recursion -/

/-! ### Common-divisor extraction -/

lemma prod_pos_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → 0 < factors.prod
  | [], _ => by simp
  | e :: factors, h => by
      simp only [List.prod_cons]
      exact Nat.mul_pos (by have := h e (by simp); omega)
        (prod_pos_of_one_lt factors (by
          intro a ha
          exact h a (by simp [ha])))

lemma sum_le_prod_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → factors.sum ≤ factors.prod
  | [], _ => by simp
  | [e], h => by simp
  | e :: f :: factors, h => by
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ f :: factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      have hfprod : 2 ≤ (f :: factors).prod := by
        have hf : 2 ≤ f := htail f (by simp)
        simp only [List.prod_cons]
        exact hf.trans (Nat.le_mul_of_pos_right f
          (prod_pos_of_one_lt factors (by
            intro a ha
            exact htail a (by simp [ha]))))
      have ih := sum_le_prod_of_one_lt (f :: factors) htail
      simp only [List.sum_cons, List.prod_cons]
      calc
        e + (f :: factors).sum ≤ e + (f :: factors).prod :=
          Nat.add_le_add_left ih e
        _ ≤ e * (f :: factors).prod := by nlinarith

lemma length_le_log_prod_of_one_lt (factors : List ℕ)
    (h : ∀ e ∈ factors, 1 < e) :
    factors.length ≤ Nat.log 2 factors.prod := by
  apply Nat.le_log_of_pow_le (by omega)
  induction factors with
  | nil => simp
  | cons e factors ih =>
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      simp only [List.length_cons, List.prod_cons, pow_succ]
      simpa [mul_comm] using Nat.mul_le_mul (ih htail) he

/-! The finite completion needs a lower pool whose elements are all smaller
than a reserved pivot pool.  The reserve required after division by `d` is
only `P / d`; charging that geometrically decreasing quantity during the
divisor descent avoids an erroneous extra logarithmic factor. -/

/-! A second form of the descent pays for a scale-dependent collision
budget.  After division by the accumulated divisor `d`, the possible number
of representatives of one residue is proportional to `Q / d`.  These terms
form a geometric series along the descent, so their total cost is at most
`2 * Q`, rather than acquiring an extra logarithm. -/

/-! ### A finite simultaneous-balancing lemma -/

open Erdos697.Bernoulli in
lemma bernoulliHalf_weight {ι : Type*} [DecidableEq ι]
    (s T : Finset ι) (hT : T ⊆ s) :
    weight s (fun _ ↦ (2 : ℝ)⁻¹) T = (2 : ℝ)⁻¹ ^ s.card := by
  rw [weight]
  simp only [Finset.prod_const]
  rw [show 1 - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num, ← pow_add]
  congr 1
  have hle := Finset.card_le_card hT
  rw [Finset.card_sdiff_of_subset hT]
  omega

lemma card_powerset_filter_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (P : Finset ι → Prop)
    [DecidablePred P] :
    (s.powerset.filter fun T ↦ P (T ∩ F)).card =
      (F.powerset.filter P).card * 2 ^ (s \ F).card := by
  let A := F.powerset.filter P
  let D := (s \ F).powerset
  have hfamily : s.powerset.filter (fun T ↦ P (T ∩ F)) =
      Finset.image₂ (· ∪ ·) A D := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image₂,
      A, D]
    constructor
    · rintro ⟨hTs, hP⟩
      refine ⟨T ∩ F, ⟨Finset.inter_subset_right, hP⟩,
        T \ F, ?_, ?_⟩
      · exact Finset.sdiff_subset_sdiff hTs (by rfl)
      · simpa [Finset.union_comm] using Finset.sdiff_union_inter T F
    · rintro ⟨U, ⟨hUF, hPU⟩, V, hVD, rfl⟩
      have hVs : V ⊆ s := hVD.trans Finset.sdiff_subset
      have hVnot : ∀ x ∈ V, x ∉ F := by
        intro x hxV hxF
        exact (Finset.mem_sdiff.mp (hVD hxV)).2 hxF
      have hinter : (U ∪ V) ∩ F = U := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxU | hxV, hxF⟩
          · exact hxU
          · exact (hVnot x hxV hxF).elim
        · intro hxU
          exact ⟨Or.inl hxU, hUF hxU⟩
      refine ⟨Finset.union_subset (hUF.trans hF) hVs, ?_⟩
      rw [hinter]
      exact hPU
  rw [hfamily]
  have hinj : ((A : Set (Finset ι)) ×ˢ (D : Set (Finset ι))).InjOn
      (fun x ↦ x.1 ∪ x.2) := by
    rintro ⟨U, V⟩ ⟨hUA, hVDmem⟩ ⟨U', V'⟩ ⟨hU'A, hV'Dmem⟩ huv
    have hUF : U ⊆ F := (Finset.mem_filter.mp hUA).1
      |> Finset.mem_powerset.mp
    have hU'F : U' ⊆ F := (Finset.mem_filter.mp hU'A).1
      |> Finset.mem_powerset.mp
    have hVD : V ⊆ s \ F := Finset.mem_powerset.mp hVDmem
    have hV'D : V' ⊆ s \ F := Finset.mem_powerset.mp hV'Dmem
    change U ∪ V = U' ∪ V' at huv
    have hU : U = U' := by
      ext x
      constructor
      · intro hxU
        have hx : x ∈ U' ∪ V' := by
          rw [← huv]
          exact Finset.mem_union_left V hxU
        rcases Finset.mem_union.mp hx with hxU' | hxV'
        · exact hxU'
        · exact ((Finset.mem_sdiff.mp (hV'D hxV')).2 (hUF hxU)).elim
      · intro hxU'
        have hx : x ∈ U ∪ V := by
          rw [huv]
          exact Finset.mem_union_left V' hxU'
        rcases Finset.mem_union.mp hx with hxU | hxV
        · exact hxU
        · exact ((Finset.mem_sdiff.mp (hVD hxV)).2 (hU'F hxU')).elim
    subst U'
    change U ∪ V = U ∪ V' at huv
    have hV : V = V' := by
      ext x
      constructor
      · intro hxV
        have hx : x ∈ U ∪ V' := by
          rw [← huv]
          exact Finset.mem_union_right U hxV
        rcases Finset.mem_union.mp hx with hxU | hxV'
        · exact ((Finset.mem_sdiff.mp (hVD hxV)).2 (hUF hxU)).elim
        · exact hxV'
      · intro hxV'
        have hx : x ∈ U ∪ V := by
          rw [huv]
          exact Finset.mem_union_right U hxV'
        rcases Finset.mem_union.mp hx with hxU | hxV
        · exact ((Finset.mem_sdiff.mp (hV'D hxV')).2 (hUF hxU)).elim
        · exact hxV
    subst V'
    rfl
  rw [Finset.card_image₂_iff.mpr hinj]
  simp [A, D]

open Erdos697.Bernoulli in
lemma sum_bernoulliHalf_filter_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (P : Finset ι → Prop)
    [DecidablePred P] :
    (∑ T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      ∑ U ∈ F.powerset.filter P, weight F (fun _ ↦ (2 : ℝ)⁻¹) U := by
  rw [show (∑ T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
      weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      ((s.powerset.filter fun T ↦ P (T ∩ F)).card : ℝ) *
        (2 : ℝ)⁻¹ ^ s.card by
    calc
      _ = ∑ _T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
          (2 : ℝ)⁻¹ ^ s.card := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [bernoulliHalf_weight s T
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)]
      _ = _ := by simp]
  rw [show (∑ U ∈ F.powerset.filter P,
      weight F (fun _ ↦ (2 : ℝ)⁻¹) U) =
      ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card by
    calc
      _ = ∑ _U ∈ F.powerset.filter P, (2 : ℝ)⁻¹ ^ F.card := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [bernoulliHalf_weight F U
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1)]
      _ = _ := by simp]
  rw [card_powerset_filter_inter s F hF P, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  have hcard : F.card + (s \ F).card = s.card := by
    have hle := Finset.card_le_card hF
    rw [Finset.card_sdiff_of_subset hF]
    omega
  rw [← hcard, pow_add]
  have hpow : (2 : ℝ) ^ (s \ F).card * (2 : ℝ)⁻¹ ^ (s \ F).card = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((F.powerset.filter P).card : ℝ) * (2 : ℝ) ^ (s \ F).card *
          ((2 : ℝ)⁻¹ ^ F.card * (2 : ℝ)⁻¹ ^ (s \ F).card) =
        ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card *
          ((2 : ℝ) ^ (s \ F).card * (2 : ℝ)⁻¹ ^ (s \ F).card) := by ring
    _ = ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card := by
      rw [hpow]
      ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_lower_nine_twentieths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ) (hK : 20 * K ≤ 9 * F.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ F).card < K),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 1000)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ U.card < K)]
  have htail := lower_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (9 : ℝ) / 10)
    (by simp; ring) (by norm_num) (by norm_num) (by
      have hKr : (20 * K : ℝ) ≤ (9 * F.card : ℕ) := by
        exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  calc
    _ ≤ Real.exp (-((F.card : ℝ) / 760)) := by
      convert htail using 1; norm_num; ring
    _ ≤ Real.exp (-((F.card : ℝ) / 1000)) := by
      apply Real.exp_le_exp.mpr
      have hcard : (0 : ℝ) ≤ F.card := by positivity
      nlinarith

open Erdos697.Bernoulli in
lemma bernoulliHalf_upper_eleven_twentieths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ)
    (hK : 11 * F.card ≤ 20 * K) :
    (∑ T ∈ s.powerset.filter (fun T ↦ K ≤ (T ∩ F).card),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 1000)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ K ≤ U.card)]
  have htail := upper_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (11 : ℝ) / 10)
    (by simp; ring) (by norm_num) (by
      have hKr : (11 * F.card : ℝ) ≤ (20 * K : ℕ) := by
        exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  calc
    _ ≤ Real.exp (-((F.card : ℝ) / 840)) := by
      convert htail using 1; norm_num; ring
    _ ≤ Real.exp (-((F.card : ℝ) / 1000)) := by
      apply Real.exp_le_exp.mpr
      have hcard : (0 : ℝ) ≤ F.card := by positivity
      nlinarith

lemma two_mul_exp_neg_log_bound (r : ℕ) :
    (2 * r : ℝ) * Real.exp
      (-((Nat.log 2 (2 * r + 1) + 1 : ℕ) : ℝ)) < 1 := by
  let L := Nat.log 2 (2 * r + 1) + 1
  have hnat : 2 * r < 2 ^ L := by
    calc
      2 * r < 2 * r + 1 := by omega
      _ < 2 ^ (Nat.log 2 (2 * r + 1)).succ :=
        Nat.lt_pow_succ_log_self (by omega) _
      _ = 2 ^ L := by simp [L]
  have hcast : (2 * r : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast hnat
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp 1 using 1; norm_num
  have hpow : (2 : ℝ) ^ L ≤ Real.exp (L : ℝ) := by
    calc
      (2 : ℝ) ^ L ≤ (Real.exp 1) ^ L :=
        pow_le_pow_left₀ (by norm_num) he2 _
      _ = Real.exp (L : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hinv : Real.exp (-((L : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ L)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) hpow
  calc
    (2 * r : ℝ) * Real.exp
        (-((Nat.log 2 (2 * r + 1) + 1 : ℕ) : ℝ)) =
        (2 * r : ℝ) * Real.exp (-((L : ℕ) : ℝ)) := by rfl
    _ ≤ (2 * r : ℝ) * ((2 : ℝ) ^ L)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ < 1 := by
      simpa [div_eq_mul_inv] using
        ((div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)).2 hcast)

open Erdos697.Bernoulli in
lemma sum_bernoulliHalf_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : Finset (Finset ι)) (hE : E ⊆ s.powerset) :
    (∑ T ∈ E, weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      (E.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
  calc
    _ = ∑ _T ∈ E, (2 : ℝ)⁻¹ ^ s.card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [bernoulliHalf_weight s T (Finset.mem_powerset.mp (hE hT))]
    _ = _ := by simp

/-- A much tighter simultaneous bisection.  The weaker exponential constant
is harmless, while the nine-twentieths/eleven-twentieths window remains tight
enough after fifteen recursive levels for the finite filling argument. -/
theorem exists_simultaneously_balanced_subset_tight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (family : Finset (Finset ι))
    (hsub : ∀ F ∈ family, F ⊆ s)
    (hlarge : ∀ F ∈ family,
      1000 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ F.card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ F ∈ family,
      9 * F.card / 20 ≤ (T ∩ F).card ∧
        (T ∩ F).card < 11 * F.card / 20 + 1 := by
  let L := Nat.log 2 (2 * family.card + 1) + 1
  let low : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ (T ∩ F).card < 9 * F.card / 20
  let high : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ 11 * F.card / 20 + 1 ≤ (T ∩ F).card
  let bad : Finset ι → Finset (Finset ι) := fun F ↦ low F ∪ high F
  let Bad := family.biUnion bad
  have hlowSub (F : Finset ι) : low F ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hhighSub (F : Finset ι) : high F ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hbadSub (F : Finset ι) : bad F ⊆ s.powerset :=
    Finset.union_subset (hlowSub F) (hhighSub F)
  have hBadSub : Bad ⊆ s.powerset := by
    intro T hT
    change T ∈ family.biUnion bad at hT
    obtain ⟨F, hF, hTF⟩ := Finset.mem_biUnion.mp hT
    exact hbadSub F hTF
  have hlow (F : Finset ι) (hF : F ∈ family) :
      ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_lower_nine_twentieths s F (hsub F hF)
      (9 * F.card / 20) (by omega)
    rw [sum_bernoulliHalf_finset s (low F) (hlowSub F)] at htail
    have hcard : 1000 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 1000 := by
      have hcardR : (1000 * L : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast hcard
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by
      have hFnonneg : (0 : ℝ) ≤ F.card := by positivity
      nlinarith))
  have hhigh (F : Finset ι) (hF : F ∈ family) :
      ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_upper_eleven_twentieths s F (hsub F hF)
      (11 * F.card / 20 + 1) (by omega)
    rw [sum_bernoulliHalf_finset s (high F) (hhighSub F)] at htail
    have hcard : 1000 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 1000 := by
      have hcardR : (1000 * L : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast hcard
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hbad (F : Finset ι) (hF : F ∈ family) :
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        2 * Real.exp (-((L : ℕ) : ℝ)) := by
    have hcard := Finset.card_union_le (low F) (high F)
    have hcardR : ((bad F).card : ℝ) ≤
        (low F).card + (high F).card := by
      exact_mod_cast hcard
    have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
    calc
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (((low F).card : ℝ) + ((high F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hcardR hpnonneg
      _ = ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card +
          ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        ring
      _ ≤ Real.exp (-((L : ℕ) : ℝ)) +
          Real.exp (-((L : ℕ) : ℝ)) :=
        add_le_add (hlow F hF) (hhigh F hF)
      _ = 2 * Real.exp (-((L : ℕ) : ℝ)) := by ring
  have hBadCard := Finset.card_biUnion_le (s := family) (t := bad)
  have hBadCardR : (Bad.card : ℝ) ≤
      ∑ F ∈ family, ((bad F).card : ℝ) := by
    exact_mod_cast hBadCard
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
  have hBadProb : (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card < 1 := by
    calc
      (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (∑ F ∈ family, ((bad F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hBadCardR hpnonneg
      _ = ∑ F ∈ family,
          ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        rw [Finset.sum_mul]
      _ ≤ ∑ _F ∈ family, 2 * Real.exp (-((L : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro F hF
        exact hbad F hF
      _ = (2 * family.card : ℝ) * Real.exp (-((L : ℕ) : ℝ)) := by
        simp
        ring
      _ < 1 := by
        simpa [L] using two_mul_exp_neg_log_bound family.card
  have hwhole : (s.powerset.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card = 1 := by
    simp
  have hcardltR : (Bad.card : ℝ) < s.powerset.card := by
    have hp : 0 < (2 : ℝ)⁻¹ ^ s.card := by positivity
    nlinarith
  have hcardlt : Bad.card < s.powerset.card := by exact_mod_cast hcardltR
  obtain ⟨T, hT⟩ := Finset.sdiff_nonempty_of_card_lt_card hcardlt
  rw [Finset.mem_sdiff] at hT
  refine ⟨T, Finset.mem_powerset.mp hT.1, ?_⟩
  intro F hF
  have hnotBad : T ∉ bad F := by
    intro hTF
    exact hT.2 (Finset.mem_biUnion.mpr ⟨F, hF, hTF⟩)
  change T ∉ low F ∪ high F at hnotBad
  rw [Finset.mem_union, not_or] at hnotBad
  constructor
  · have h := hnotBad.1
    change T ∉ s.powerset.filter
      (fun T ↦ (T ∩ F).card < 9 * F.card / 20) at h
    rw [Finset.mem_filter, not_and_or] at h
    exact le_of_not_gt (h.resolve_left (by simpa using hT.1))
  · have h := hnotBad.2
    change T ∉ s.powerset.filter
      (fun T ↦ 11 * F.card / 20 + 1 ≤ (T ∩ F).card) at h
    rw [Finset.mem_filter, not_and_or] at h
    exact lt_of_not_ge (h.resolve_left (by simpa using hT.1))

theorem exists_simultaneously_balanced_subset_tight_indexed
    {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      1000 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ j ∈ J,
      9 * (F j).card / 20 ≤ (T ∩ F j).card ∧
        (T ∩ F j).card < 11 * (F j).card / 20 + 1 := by
  classical
  let family := J.image F
  have hfamilyCard : family.card ≤ J.card := Finset.card_image_le
  have hlog : Nat.log 2 (2 * family.card + 1) ≤
      Nat.log 2 (2 * J.card + 1) := by
    apply Nat.log_mono_right
    omega
  have hfamilySub : ∀ G ∈ family, G ⊆ s := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact hsub j hj
  have hfamilyLarge : ∀ G ∈ family,
      1000 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ G.card := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right hlog 1)).trans
      (hlarge j hj)
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset_tight
    s family hfamilySub hfamilyLarge
  refine ⟨T, hTs, ?_⟩
  intro j hj
  exact hT (F j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem exists_balanced_bipartition_tight_indexed
    {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      1000 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T U : Finset ι, Disjoint T U ∧ T ∪ U = s ∧
      ∀ j ∈ J,
        (9 * (F j).card / 20 ≤ (T ∩ F j).card ∧
          (T ∩ F j).card < 11 * (F j).card / 20 + 2) ∧
        (9 * (F j).card / 20 ≤ (U ∩ F j).card ∧
          (U ∩ F j).card < 11 * (F j).card / 20 + 2) := by
  classical
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset_tight_indexed
    s J F hsub hlarge
  let U := s \ T
  refine ⟨T, U, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hTs, ?_⟩
  intro j hj
  refine ⟨⟨(hT j hj).1, (hT j hj).2.trans_le (by omega)⟩, ?_⟩
  have hEq : U ∩ F j = F j \ (T ∩ F j) := by
    ext x
    simp only [U, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxs, hxT⟩, hxF⟩
      exact ⟨hxF, fun hx ↦ hxT hx.1⟩
    · rintro ⟨hxF, hxnot⟩
      exact ⟨⟨hsub j hj hxF, fun hxT ↦ hxnot ⟨hxT, hxF⟩⟩, hxF⟩
  have hinter : T ∩ F j ⊆ F j := Finset.inter_subset_right
  have hcard : (U ∩ F j).card =
      (F j).card - (T ∩ F j).card := by
    rw [hEq, Finset.card_sdiff_of_subset hinter]
  have hsumle : 9 * (F j).card / 20 + 11 * (F j).card / 20 ≤
      (F j).card := by
    calc
      9 * (F j).card / 20 + 11 * (F j).card / 20 ≤
          (9 * (F j).card + 11 * (F j).card) / 20 :=
        Nat.div_add_div_le_add_div
      _ = (F j).card := by omega
  have hsumge : (F j).card ≤
      9 * (F j).card / 20 + 11 * (F j).card / 20 + 1 := by
    have h := Nat.add_div_le_div_add_div_add_one
      (9 * (F j).card) (11 * (F j).card) 20
    have hleft : (9 * (F j).card + 11 * (F j).card) / 20 =
        (F j).card := by omega
    rw [hleft] at h
    exact h
  have hlo := (hT j hj).1
  have hhi := (hT j hj).2
  rw [hcard]
  constructor <;> omega

/-! ### Recursive simultaneous balancing -/

/-- A perfect binary tree of natural-number sumsets.  It is declared here
because the partition machinery below maps its leaves into such a tree. -/
inductive SumTree : ℕ → Type
  | leaf (S : Finset ℕ) : SumTree 0
  | node {t : ℕ} (left right : SumTree t) : SumTree (t + 1)

namespace SumTree

def carrier : {t : ℕ} → SumTree t → Finset ℕ
  | 0, leaf S => S
  | _ + 1, node left right => carrier left + carrier right

def AllLeaves (P : Finset ℕ → Prop) : {t : ℕ} → SumTree t → Prop
  | 0, leaf S => P S
  | _ + 1, node left right => AllLeaves P left ∧ AllLeaves P right

/-- Cardinality forced at depth `t` if every additive merge keeps growing. -/
def growthLower (k : ℕ) : ℕ → ℕ
  | 0 => k
  | t + 1 => 3 * growthLower k t - 3

lemma growthLower_ge {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, k ≤ growthLower k t := by
  intro t
  induction t with
  | zero => simp [growthLower]
  | succ t ih =>
      rw [growthLower]
      have htwo : 2 ≤ growthLower k t := hk.trans ih
      omega

end SumTree

/-- A perfect binary tree whose leaves are finsets.  Unlike `SumTree`, its
internal operation is union; it records a genuine disjoint partition of the
original labelled set. -/
inductive PartitionTree (ι : Type u) : ℕ → Type u
  | leaf (S : Finset ι) : PartitionTree ι 0
  | node {t : ℕ} (left right : PartitionTree ι t) : PartitionTree ι (t + 1)

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

def carrier : {t : ℕ} → PartitionTree ι t → Finset ι
  | 0, leaf S => S
  | _ + 1, node left right => carrier left ∪ carrier right

def AllLeaves (P : Finset ι → Prop) : {t : ℕ} → PartitionTree ι t → Prop
  | 0, leaf S => P S
  | _ + 1, node left right => AllLeaves P left ∧ AllLeaves P right

def PairwiseDisjoint : {t : ℕ} → PartitionTree ι t → Prop
  | 0, leaf _ => True
  | _ + 1, node left right =>
      PairwiseDisjoint left ∧ PairwiseDisjoint right ∧
        Disjoint left.carrier right.carrier

omit [DecidableEq ι] in
lemma AllLeaves.mono {t : ℕ} {T : PartitionTree ι t}
    {P Q : Finset ι → Prop} (h : T.AllLeaves P)
    (hPQ : ∀ S, P S → Q S) : T.AllLeaves Q := by
  induction T with
  | leaf S => exact hPQ S h
  | node left right ihl ihr =>
      exact ⟨ihl h.1, ihr h.2⟩

omit [DecidableEq ι] in
lemma AllLeaves.and {t : ℕ} {T : PartitionTree ι t}
    {P Q : Finset ι → Prop} (hP : T.AllLeaves P)
    (hQ : T.AllLeaves Q) : T.AllLeaves fun S ↦ P S ∧ Q S := by
  induction T with
  | leaf S => exact ⟨hP, hQ⟩
  | node left right ihl ihr =>
      exact ⟨ihl hP.1 hQ.1, ihr hP.2 hQ.2⟩

lemma allLeaves_subset_carrier {t : ℕ} (T : PartitionTree ι t) :
    T.AllLeaves fun S ↦ S ⊆ T.carrier := by
  induction T with
  | leaf S => exact fun _ h ↦ h
  | node left right ihl ihr =>
      exact ⟨
        ihl.mono fun S hS x hx ↦ Finset.mem_union_left _ (hS hx),
        ihr.mono fun S hS x hx ↦ Finset.mem_union_right _ (hS hx)⟩

lemma tight_split_card_ratios {p c : ℕ} (hp : 200 ≤ p)
    (hlow : 9 * p / 20 ≤ c) (hhigh : c < 11 * p / 20 + 2) :
    89 * p ≤ 200 * c ∧ 200 * c ≤ 111 * p := by
  constructor <;> omega

private lemma balancing_threshold_pos (r : ℕ) :
    0 < 1000 * (Nat.log 2 (2 * r + 1) + 1) := by positivity

private lemma balancing_threshold_ge_two_hundred (r : ℕ) :
    200 ≤ 1000 * (Nat.log 2 (2 * r + 1) + 1) := by
  have : 1 ≤ Nat.log 2 (2 * r + 1) + 1 := by omega
  nlinarith

/-- Iterating the tight Bernoulli split produces a perfect disjoint partition.
Every tracked subset has, in every leaf, between the displayed fixed powers
of its ideal share.  The hypothesis is written in multiplication form so it
can be propagated without any floor or divisibility assumptions. -/
theorem exists_tight_partition
    {κ : Type*}
    (t : ℕ) (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
        89 ^ t * (F j).card) :
    ∃ T : PartitionTree ι t,
      T.carrier = s ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦ ∀ j ∈ J,
        89 ^ t * (F j).card ≤ 200 ^ t * (C ∩ F j).card ∧
        200 ^ t * (C ∩ F j).card ≤ 111 ^ t * (F j).card := by
  classical
  induction t generalizing s F with
  | zero =>
      refine ⟨.leaf s, rfl, trivial, ?_⟩
      intro j hj
      have hinter : s ∩ F j = F j := Finset.inter_eq_right.mpr (hsub j hj)
      simp [hinter]
  | succ t ih =>
      let Q := 1000 * (Nat.log 2 (2 * J.card + 1) + 1)
      have hQpos : 0 < Q := balancing_threshold_pos J.card
      have hQ200 : 200 ≤ Q := balancing_threshold_ge_two_hundred J.card
      have hlargeSplit : ∀ j ∈ J, Q ≤ (F j).card := by
        intro j hj
        have hp89 : 89 ^ (t + 1) ≤ 200 ^ (t + 1) := by
          exact Nat.pow_le_pow_left (by omega : 89 ≤ 200) (t + 1)
        have hmul : 200 ^ (t + 1) * Q ≤
            200 ^ (t + 1) * (F j).card := by
          calc
            200 ^ (t + 1) * Q = Q * 200 ^ (t + 1) := by ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ ≤ 200 ^ (t + 1) * (F j).card :=
              Nat.mul_le_mul_right (F j).card hp89
        exact Nat.le_of_mul_le_mul_left hmul (pow_pos (by omega) _)
      obtain ⟨u, v, huv, huvUnion, hsplit⟩ :=
        exists_balanced_bipartition_tight_indexed s J F hsub (by
          intro j hj
          simpa [Q] using hlargeSplit j hj)
      have hratioU : ∀ j ∈ J,
          89 * (F j).card ≤ 200 * (u ∩ F j).card ∧
            200 * (u ∩ F j).card ≤ 111 * (F j).card := by
        intro j hj
        exact tight_split_card_ratios
          (hQ200.trans (hlargeSplit j hj)) (hsplit j hj).1.1
            (hsplit j hj).1.2
      have hratioV : ∀ j ∈ J,
          89 * (F j).card ≤ 200 * (v ∩ F j).card ∧
            200 * (v ∩ F j).card ≤ 111 * (F j).card := by
        intro j hj
        exact tight_split_card_ratios
          (hQ200.trans (hlargeSplit j hj)) (hsplit j hj).2.1
            (hsplit j hj).2.2
      let Fu : κ → Finset ι := fun j ↦ u ∩ F j
      let Fv : κ → Finset ι := fun j ↦ v ∩ F j
      have hsubU : ∀ j ∈ J, Fu j ⊆ u := by
        intro j hj
        exact Finset.inter_subset_left
      have hsubV : ∀ j ∈ J, Fv j ⊆ v := by
        intro j hj
        exact Finset.inter_subset_left
      have hlargeU : ∀ j ∈ J, Q * 200 ^ t ≤
          89 ^ t * (Fu j).card := by
        intro j hj
        have hmul : 200 * (Q * 200 ^ t) ≤
            200 * (89 ^ t * (Fu j).card) := by
          calc
            200 * (Q * 200 ^ t) = Q * 200 ^ (t + 1) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ = 89 ^ t * (89 * (F j).card) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ t * (200 * (Fu j).card) :=
              Nat.mul_le_mul_left _ (hratioU j hj).1
            _ = 200 * (89 ^ t * (Fu j).card) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (by omega)
      have hlargeV : ∀ j ∈ J, Q * 200 ^ t ≤
          89 ^ t * (Fv j).card := by
        intro j hj
        have hmul : 200 * (Q * 200 ^ t) ≤
            200 * (89 ^ t * (Fv j).card) := by
          calc
            200 * (Q * 200 ^ t) = Q * 200 ^ (t + 1) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ = 89 ^ t * (89 * (F j).card) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ t * (200 * (Fv j).card) :=
              Nat.mul_le_mul_left _ (hratioV j hj).1
            _ = 200 * (89 ^ t * (Fv j).card) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (by omega)
      obtain ⟨Tu, hTuCarrier, hTuDisj, hTuLeaves⟩ :=
        ih u Fu hsubU (by simpa [Q] using hlargeU)
      obtain ⟨Tv, hTvCarrier, hTvDisj, hTvLeaves⟩ :=
        ih v Fv hsubV (by simpa [Q] using hlargeV)
      let T : PartitionTree ι (t + 1) := .node Tu Tv
      refine ⟨T, ?_, ?_, ?_⟩
      · change Tu.carrier ∪ Tv.carrier = s
        rw [hTuCarrier, hTvCarrier, huvUnion]
      · exact ⟨hTuDisj, hTvDisj, by simpa [hTuCarrier, hTvCarrier] using huv⟩
      · constructor
        · refine (hTuLeaves.and (allLeaves_subset_carrier Tu)).mono ?_
          rintro C ⟨hC, hCsubTu⟩ j hj
          have hCsub : C ⊆ u := by simpa [hTuCarrier] using hCsubTu
          have hinter : C ∩ Fu j = C ∩ F j := by
            ext x
            simp only [Fu, Finset.mem_inter]
            tauto
          have hCj := hC j hj
          rw [hinter] at hCj
          refine ⟨?_, ?_⟩
          · calc
              89 ^ (t + 1) * (F j).card =
                  89 ^ t * (89 * (F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 89 ^ t * (200 * (Fu j).card) :=
                Nat.mul_le_mul_left _ (hratioU j hj).1
              _ = 200 * (89 ^ t * (Fu j).card) := by ring
              _ ≤ 200 * (200 ^ t * (C ∩ F j).card) :=
                Nat.mul_le_mul_left 200 hCj.1
              _ = 200 ^ (t + 1) * (C ∩ F j).card := by
                rw [pow_succ]
                ring
          · calc
              200 ^ (t + 1) * (C ∩ F j).card =
                  200 * (200 ^ t * (C ∩ F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 200 * (111 ^ t * (Fu j).card) :=
                Nat.mul_le_mul_left 200 hCj.2
              _ = 111 ^ t * (200 * (Fu j).card) := by ring
              _ ≤ 111 ^ t * (111 * (F j).card) :=
                Nat.mul_le_mul_left _ (hratioU j hj).2
              _ = 111 ^ (t + 1) * (F j).card := by
                rw [pow_succ]
                ring
        · refine (hTvLeaves.and (allLeaves_subset_carrier Tv)).mono ?_
          rintro C ⟨hC, hCsubTv⟩ j hj
          have hCsub : C ⊆ v := by simpa [hTvCarrier] using hCsubTv
          have hinter : C ∩ Fv j = C ∩ F j := by
            ext x
            simp only [Fv, Finset.mem_inter]
            tauto
          have hCj := hC j hj
          rw [hinter] at hCj
          refine ⟨?_, ?_⟩
          · calc
              89 ^ (t + 1) * (F j).card =
                  89 ^ t * (89 * (F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 89 ^ t * (200 * (Fv j).card) :=
                Nat.mul_le_mul_left _ (hratioV j hj).1
              _ = 200 * (89 ^ t * (Fv j).card) := by ring
              _ ≤ 200 * (200 ^ t * (C ∩ F j).card) :=
                Nat.mul_le_mul_left 200 hCj.1
              _ = 200 ^ (t + 1) * (C ∩ F j).card := by
                rw [pow_succ]
                ring
          · calc
              200 ^ (t + 1) * (C ∩ F j).card =
                  200 * (200 ^ t * (C ∩ F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 200 * (111 ^ t * (Fv j).card) :=
                Nat.mul_le_mul_left 200 hCj.2
              _ = 111 ^ t * (200 * (Fv j).card) := by ring
              _ ≤ 111 ^ t * (111 * (F j).card) :=
                Nat.mul_le_mul_left _ (hratioV j hj).2
              _ = 111 ^ (t + 1) * (F j).card := by
                rw [pow_succ]
                ring

end PartitionTree

/-! ### Bounded integer subset sums and modular pivots -/

noncomputable def natAddTranslate (b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x ↦ x + b

lemma card_union_natAddTranslate (b : ℕ) (S : Finset ℕ) :
    (S ∪ natAddTranslate b S).card =
      S.card + (natAddTranslate b S \ S).card := by
  have h := Finset.card_sdiff_add_card (natAddTranslate b S) S
  rw [Finset.union_comm] at h
  omega

/-- Adding the integer modulus creates at least one new sum in every residue
class already occupied by `S`. -/
lemma card_add_modulus_growth {b : ℕ} [NeZero b] (hb : 0 < b)
    (S : Finset ℕ) :
    S.card + (S.image fun x : ℕ ↦ (x : ZMod b)).card ≤
      (S ∪ natAddTranslate b S).card := by
  classical
  let R : Finset (ZMod b) := S.image fun x : ℕ ↦ (x : ZMod b)
  let fiber : R → Finset ℕ := fun r ↦
    Finset.filter (fun x : ℕ ↦ (x : ZMod b) = r.1) S
  have hfiber (r : R) : (fiber r).Nonempty := by
    obtain ⟨x, hxS, hxr⟩ := Finset.mem_image.mp r.2
    refine ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩⟩
    exact hxr
  let pick (r : R) := (fiber r).max' (hfiber r)
  let f : R → ℕ := fun r ↦ pick r + b
  have hmaps : ∀ r ∈ R.attach, f r ∈ natAddTranslate b S \ S := by
    intro r hr
    have hpickFiber : pick r ∈ fiber r := (fiber r).max'_mem (hfiber r)
    have hpickS : pick r ∈ S := (Finset.mem_filter.mp hpickFiber).1
    have hpickCast : (pick r : ZMod b) = r.1 :=
      (Finset.mem_filter.mp hpickFiber).2
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_image.mpr ⟨pick r, hpickS, rfl⟩
    · intro hnewS
      have hcast : ((pick r + b : ℕ) : ZMod b) = r.1 := by
        simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using hpickCast
      have hnewFiber : pick r + b ∈ fiber r :=
        Finset.mem_filter.mpr ⟨hnewS, hcast⟩
      have hle := (fiber r).le_max' (pick r + b) hnewFiber
      have hle' : pick r + b ≤ pick r := by simpa [pick] using hle
      omega
  have hinj : Set.InjOn f R.attach := by
    intro r hr q hq heq
    apply Subtype.ext
    have hpickEq : pick r = pick q := Nat.add_right_cancel heq
    have hrmem := (Finset.mem_filter.mp ((fiber r).max'_mem (hfiber r))).2
    have hqmem := (Finset.mem_filter.mp ((fiber q).max'_mem (hfiber q))).2
    calc
      r.1 = (pick r : ZMod b) := hrmem.symm
      _ = (pick q : ZMod b) := by rw [hpickEq]
      _ = q.1 := hqmem
  have hnew : R.card ≤ (natAddTranslate b S \ S).card := by
    rw [← Finset.card_attach]
    exact Finset.card_le_card_of_injOn f hmaps hinj
  rw [card_union_natAddTranslate]
  exact Nat.add_le_add_left hnew S.card

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

def zipUnion : {t : ℕ} → PartitionTree ι t → PartitionTree ι t →
    PartitionTree ι t
  | 0, .leaf A, .leaf B => .leaf (A ∪ B)
  | _ + 1, .node A₁ A₂, .node B₁ B₂ =>
      .node (zipUnion A₁ B₁) (zipUnion A₂ B₂)

lemma carrier_zipUnion {t : ℕ} (A B : PartitionTree ι t) :
    (zipUnion A B).carrier = A.carrier ∪ B.carrier := by
  induction A with
  | leaf A => cases B; rfl
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          simp only [zipUnion, carrier, ih₁, ih₂]
          ext x
          simp only [Finset.mem_union]
          tauto

lemma pairwiseDisjoint_zipUnion {t : ℕ} {A B : PartitionTree ι t}
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier) :
    (zipUnion A B).PairwiseDisjoint := by
  induction A with
  | leaf A => cases B; trivial
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          rcases hA with ⟨hA₁, hA₂, hA12⟩
          rcases hB with ⟨hB₁, hB₂, hB12⟩
          have hA₁B₁ : Disjoint A₁.carrier B₁.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_left _ hx)
              (fun x hx ↦ Finset.mem_union_left _ hx)
          have hA₂B₂ : Disjoint A₂.carrier B₂.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_right _ hx)
              (fun x hx ↦ Finset.mem_union_right _ hx)
          refine ⟨ih₁ hA₁ hB₁ hA₁B₁, ih₂ hA₂ hB₂ hA₂B₂, ?_⟩
          rw [carrier_zipUnion, carrier_zipUnion, Finset.disjoint_left]
          intro x hxLeft hxRight
          rw [Finset.mem_union] at hxLeft hxRight
          rcases hxLeft with hxA₁ | hxB₁ <;>
            rcases hxRight with hxA₂ | hxB₂
          · exact Finset.disjoint_left.mp hA12 hxA₁ hxA₂
          · exact Finset.disjoint_left.mp hAB
              (Finset.mem_union_left _ hxA₁) (Finset.mem_union_right _ hxB₂)
          · exact Finset.disjoint_left.mp hAB
              (Finset.mem_union_right _ hxA₂) (Finset.mem_union_left _ hxB₁)
          · exact Finset.disjoint_left.mp hB12 hxB₁ hxB₂

def mapSumTree (f : Finset ι → Finset ℕ) :
    {t : ℕ} → PartitionTree ι t → SumTree t
  | 0, .leaf A => .leaf (f A)
  | _ + 1, .node A B => .node (mapSumTree f A) (mapSumTree f B)

omit [DecidableEq ι] in
lemma allLeaves_mapSumTree {t : ℕ} (f : Finset ι → Finset ℕ)
    (T : PartitionTree ι t) (P : Finset ℕ → Prop) :
    (mapSumTree f T).AllLeaves P ↔ T.AllLeaves fun C ↦ P (f C) := by
  induction T with
  | leaf C => rfl
  | node A B ihA ihB =>
      simp only [mapSumTree, SumTree.AllLeaves, AllLeaves, ihA, ihB]

end PartitionTree

lemma growthLower_ge_pow_mul {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, 3 ^ t * (k - 2) + 2 ≤ SumTree.growthLower k t := by
  intro t
  induction t with
  | zero => simp only [pow_zero, one_mul, SumTree.growthLower]; omega
  | succ t ih =>
    rw [SumTree.growthLower, pow_succ]
    have hmul := Nat.mul_le_mul_left 3 ih
    have hge := SumTree.growthLower_ge hk t
    rw [show 3 ^ t * 3 * (k - 2) = 3 * (3 ^ t * (k - 2)) by ring]
    omega

/-! The eventual estimates in the finite theorem are kept elementary.  The
only analytic-looking error is polylogarithmic; the next two lemmas dominate
it by the integer square root once the binary logarithm is at least `64`. -/

/-! Fixed numerical parameters for the finite completion.  The large density
constant is intentionally very wasteful: it pays simultaneously for divisor
descent, dyadic pruning, forty-nine balanced splitting levels, and all integer
rounding errors. -/

lemma depth_fortyEight_growth
    {q : ℕ} (hq : 32 ≤ q) :
    2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 <
      SumTree.growthLower (89 ^ 49 * (q / 16)) 48 := by
  have hr : 2 ≤ q / 16 := by omega
  have hk : 2 ≤ 89 ^ 49 * (q / 16) := by
    have : 1 ≤ 89 ^ 49 := one_le_pow₀ (by omega)
    nlinarith
  have hgrowth := growthLower_ge_pow_mul hk 48
  have hqround : q + 1 ≤ 24 * (q / 16) := by omega
  have hcoef :
      2 ^ 48 * (40 * 111 ^ 49) * 24 <
        3 ^ 48 * (89 ^ 49 - 1) := by norm_num
  have hminus :
      (89 ^ 49 - 1) * (q / 16) ≤
        89 ^ 49 * (q / 16) - 2 := by
    calc
      (89 ^ 49 - 1) * (q / 16) =
          89 ^ 49 * (q / 16) - 1 * (q / 16) := by
            rw [Nat.sub_mul]
      _ = 89 ^ 49 * (q / 16) - q / 16 := by simp
      _ ≤ 89 ^ 49 * (q / 16) - 2 :=
        Nat.sub_le_sub_left hr _
  have hstrict :
      2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 <
        3 ^ 48 * (89 ^ 49 * (q / 16) - 2) + 2 := by
    calc
      2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 ≤
          (2 ^ 48 * (40 * 111 ^ 49) * 24) * (q / 16) + 1 := by
            have hscaled := Nat.mul_le_mul_left
              (2 ^ 48 * (40 * 111 ^ 49)) hqround
            have hadd := Nat.add_le_add_right hscaled 1
            convert hadd using 1 <;> ring
      _ < (3 ^ 48 * (89 ^ 49 - 1)) * (q / 16) + 2 := by
            have hpos : 0 < q / 16 := by omega
            have hmul := Nat.mul_lt_mul_of_pos_right hcoef hpos
            omega
      _ ≤ 3 ^ 48 * (89 ^ 49 * (q / 16) - 2) + 2 := by
            have hadd := Nat.add_le_add_right
              (Nat.mul_le_mul_left (3 ^ 48) hminus) 2
            convert hadd using 1; ring
  exact hstrict.trans_le hgrowth

/-! ### Dyadic pruning and weighted balance

The finite assembly partitions a set many times.  Cardinal balance alone is
not enough: a leaf could receive all of the very large elements.  We first
discard the occupied dyadic value classes that are too small, then track every
remaining class through the simultaneous partition.  The next definitions
and lemmas turn the resulting classwise cardinal estimates into estimates for
the sums of the elements. -/

/-! ### Stabilization of finite subset-sum residues -/

lemma exists_eq_add_mul_of_zmod_eq {u r d : ℕ} (_hd : 0 < d) (hr : r < d)
    (h : (u : ZMod d) = (r : ZMod d)) :
    ∃ z : ℕ, u = r + d * z := by
  let : NeZero d := ⟨_hd.ne'⟩
  have hmod : u % d = r := by
    have := (ZMod.natCast_eq_natCast_iff' u r d).mp h
    simpa [Nat.mod_eq_of_lt hr] using this
  refine ⟨u / d, ?_⟩
  calc
    u = u % d + d * (u / d) := (Nat.mod_add_div u d).symm
    _ = r + d * (u / d) := by rw [hmod]

/-! ### Merging progressions while decreasing the common difference -/

lemma coprime_AP_residues {q M r : ℕ}
    (_hq : 0 < q) (hM : 0 < M) (hr : 0 < r) (hcop : M.Coprime r) :
    ∀ i < M, ∃ t < M, ∃ z ≤ r,
      t * (q * r) = i * q + (q * M) * z := by
  let : NeZero M := ⟨hM.ne'⟩
  let ur : (ZMod M)ˣ := ZMod.unitOfCoprime r hcop.symm
  intro i hi
  let x : ZMod M := (i : ZMod M) * (ur⁻¹ : (ZMod M)ˣ)
  let t := x.val
  have htM : t < M := x.val_lt
  have htrCast : (t * r : ZMod M) = (i : ZMod M) := by
    change (x.val : ZMod M) * (r : ZMod M) = (i : ZMod M)
    rw [ZMod.natCast_zmod_val x]
    change ((i : ZMod M) * (↑(ur⁻¹) : ZMod M)) * (r : ZMod M) = i
    have hur : (r : ZMod M) = (ur : ZMod M) := rfl
    rw [hur]
    simp [mul_assoc]
  obtain ⟨z, htr⟩ := exists_eq_add_mul_of_zmod_eq
    (u := t * r) (r := i) (d := M) hM hi (by
      simpa only [Nat.cast_mul] using htrCast)
  have hz : z ≤ r := by
    have htz : M * z ≤ t * r := by omega
    have htrlt : t * r < M * r := (Nat.mul_lt_mul_right hr).2 htM
    have hmz : M * z < M * r := htz.trans_lt htrlt
    exact ((Nat.mul_lt_mul_left hM).mp hmz).le
  refine ⟨t, htM, z, hz, ?_⟩
  calc
    t * (q * r) = q * (t * r) := by ring
    _ = q * (i + M * z) := by rw [htr]
    _ = i * q + (q * M) * z := by ring

/-- The sum of a `q*M` progression and a sufficiently long `q*r`
progression contains a long `q` progression when `M` and `r` are coprime. -/
lemma merge_AP_by_gcd {S U : Set ℕ}
    {a b q M r LS LU : ℕ}
    (hq : 0 < q) (hM : 0 < M) (hr : 0 < r) (hcop : M.Coprime r)
    (hMU : M ≤ LU)
    (hS : ∀ j < LS, a + j * (q * M) ∈ S)
    (hU : ∀ t < LU, b + t * (q * r) ∈ U) :
    ∀ n < M * (LS - r),
      (a + b + (q * M) * r) + n * q ∈ S + U := by
  let U₀ : Set ℕ := {u | b + u ∈ U}
  have hres : ∀ i < M, ∃ u ∈ U₀, ∃ z ≤ r,
      u = i * q + (q * M) * z := by
    intro i hi
    obtain ⟨t, htM, z, hzr, heq⟩ := coprime_AP_residues hq hM hr hcop i hi
    refine ⟨t * (q * r), ?_, z, hzr, heq⟩
    exact hU t (htM.trans_le hMU)
  intro n hn
  have hx := lowerStep_of_residue_translates_mem hq hM hS hres n hn
  obtain ⟨s, hs, u, hu, hsum⟩ := hx
  change s + u = (a + (q * M) * r) + n * q at hsum
  refine ⟨s, hs, b + u, hu, ?_⟩
  calc
    s + (b + u) = b + (s + u) := by omega
    _ = b + ((a + (q * M) * r) + n * q) := by rw [hsum]
    _ = (a + b + (q * M) * r) + n * q := by omega

/-! ### A binary-tree filling lemma -/

namespace SumTree

lemma zero_mem_carrier {t : ℕ} {T : SumTree t}
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S) : 0 ∈ T.carrier := by
  induction T with
  | leaf S => exact hzero
  | node left right ihl ihr =>
      exact Finset.add_mem_add (ihl hzero.1) (ihr hzero.2)

lemma carrier_subset_Icc {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier ⊆ Finset.Icc 0 (2 ^ t * m) := by
  induction T with
  | leaf S => simpa [carrier, AllLeaves] using hbox
  | @node t left right ihl ihr =>
      intro z hz
      rw [carrier, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := Finset.mem_Icc.mp (ihl hbox.1 hx)
      have hy' := Finset.mem_Icc.mp (ihr hbox.2 hy)
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.zero_le _
      · calc
          x + y ≤ 2 ^ t * m + 2 ^ t * m := Nat.add_le_add hx'.2 hy'.2
          _ = 2 ^ t * 2 * m := by ring
          _ = 2 ^ (t + 1) * m := by rw [pow_succ]

lemma card_carrier_le {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier.card ≤ 2 ^ t * m + 1 := by
  have hsub := carrier_subset_Icc hbox
  have hcard := Finset.card_le_card hsub
  simpa using hcard

private lemma left_subset_carrier {t : ℕ} (left right : SumTree t)
    (hzero : 0 ∈ right.carrier) :
    (left.carrier : Set ℕ) ⊆ ((SumTree.node left right).carrier : Finset ℕ) := by
  intro x hx
  exact Finset.add_mem_add hx hzero

private lemma right_subset_carrier {t : ℕ} (left right : SumTree t)
    (hzero : 0 ∈ left.carrier) :
    (right.carrier : Set ℕ) ⊆ ((SumTree.node left right).carrier : Finset ℕ) := by
  intro x hx
  change x ∈ left.carrier + right.carrier
  simpa using Finset.add_mem_add hzero hx

/-- Tree alternative behind the rank-one filling argument: either a merge
has already produced a progression of the initial target length, or all
merges grow and the root has the corresponding recursively forced size. -/
lemma containsAP_or_card_growth {t k : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card) :
    ContainsFiniteAP (T.carrier : Set ℕ) (2 * k - 1) ∨
      growthLower k t ≤ T.carrier.card := by
  induction T with
  | leaf S =>
      right
      simpa [carrier, AllLeaves, growthLower] using hcard
  | @node t left right ihl ihr =>
      rcases ihl hzero.1 hcard.1 with hAP | hleft
      · left
        exact containsFiniteAP_mono
          (left_subset_carrier left right (zero_mem_carrier hzero.2)) hAP
      rcases ihr hzero.2 hcard.2 with hAP | hright
      · left
        exact containsFiniteAP_mono
          (right_subset_carrier left right (zero_mem_carrier hzero.1)) hAP
      have hleftne : left.carrier.Nonempty := ⟨0, zero_mem_carrier hzero.1⟩
      have hrightne : right.carrier.Nonempty := ⟨0, zero_mem_carrier hzero.2⟩
      rcases Erdos13Additive.growth_or_long_AP hleftne hrightne with hgrow | hprog
      · right
        rw [growthLower]
        have hmin : growthLower k t ≤
            min left.carrier.card right.carrier.card := by
          exact le_min hleft hright
        have hsum : 3 * growthLower k t ≤
            left.carrier.card + right.carrier.card +
              min left.carrier.card right.carrier.card := by
          omega
        have hroot : left.carrier + right.carrier =
            (SumTree.node left right).carrier := rfl
        rw [hroot] at hgrow
        omega
      · left
        obtain ⟨a, d, hd, hprog, -⟩ := hprog
        refine ⟨a, d, hd, ?_⟩
        intro i hi
        apply hprog
        rw [Erdos13Additive.mem_natAP]
        refine ⟨i, ?_, ?_⟩
        · have hkleft : k ≤ left.carrier.card :=
            (growthLower_ge hk t).trans hleft
          have hkright : k ≤ right.carrier.card :=
            (growthLower_ge hk t).trans hright
          omega
        · simp [mul_comm]

/-- Quantitative rank-one filling lemma.  If a perfect family of dense
one-dimensional leaves is deep enough that perpetual growth would exceed the
ambient interval, its iterated sum contains a long arithmetic progression. -/
theorem containsFiniteAP_of_growth_exceeds_diameter
    {t k m : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card)
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m)
    (hexceed : 2 ^ t * m + 1 < growthLower k t) :
    ContainsFiniteAP (T.carrier : Set ℕ) (2 * k - 1) := by
  rcases containsAP_or_card_growth hk hzero hcard with hAP | hgrowth
  · exact hAP
  · have hupp := card_carrier_le hbox
    omega

end SumTree

/-! ### The small-doubling rank-one containment step -/

/-! ### Dyadic blocks and a fixed progression difference -/

/-! ### Assembly of the infinite theorem from the finite theorem -/

end Erdos344

/-! ### Upstream module `Jsp285/MergedBlocks.lean` -/

/-! Merge disjoint occurrence blocks while their positive AP steps divide one fixed integer. -/

namespace Jsp285

open scoped Pointwise

/-- The exponentially increasing target length of block `i`. -/
def blockLength (L i : ℕ) : ℕ := 2 ^ i * L

/-- The occurrence indices used through block `i`. -/
def usedBlocks (B : ℕ → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).biUnion B

/-- The next disjoint block can be merged using the gcd of the progression steps. -/
theorem exists_merged_occurrence_blocks (v : ℕ → ℕ) (B : ℕ → Finset ℕ)
    (L : ℕ) (_hL : 2 ≤ L) (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hAP : ∀ i, ∃ a d : ℕ, 0 < d ∧ 16 * d ≤ blockLength L i ∧
      ∀ j < blockLength L i, a + j * d ∈ occurrenceSums v (B i)) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
      ∀ j < blockLength L i / 2, a + j * d ∈ occurrenceSums v (usedBlocks B i) := by
  obtain ⟨a₀, D, hD, hDsmall, hAP₀⟩ := hAP 0
  have hDL : 16 * D ≤ L := by simpa [blockLength] using hDsmall
  refine ⟨D, hD, ?_⟩
  intro i
  induction i with
  | zero =>
    refine ⟨a₀, D, hD, dvd_rfl, ?_⟩
    intro j hj
    simpa [usedBlocks] using hAP₀ j (hj.trans_le (Nat.div_le_self _ _))
  | succ i ih =>
    obtain ⟨aOld, dOld, hdOld, hdOldD, hOld⟩ := ih
    obtain ⟨aNew, dNew, hdNew, hdNewBound, hNew⟩ := hAP (i + 1)
    let q := Nat.gcd dNew dOld
    let M := dNew / q
    let r := dOld / q
    have hq : 0 < q := Nat.gcd_pos_of_pos_left dOld hdNew
    have hqdNew : q ∣ dNew := Nat.gcd_dvd_left _ _
    have hqdOld : q ∣ dOld := Nat.gcd_dvd_right _ _
    have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hdNew hqdNew) hq
    have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hdOld hqdOld) hq
    have hdNewEq : q * M = dNew := Nat.mul_div_cancel' hqdNew
    have hdOldEq : q * r = dOld := Nat.mul_div_cancel' hqdOld
    have hcop : M.Coprime r := Nat.coprime_div_gcd_div_gcd hq
    have hnext : blockLength L (i + 1) = 2 * blockLength L i := by
      simp [blockLength, pow_succ]
      ring
    have hLnext : L ≤ blockLength L (i + 1) :=
      Nat.le_mul_of_pos_left L (pow_pos (by omega) _)
    have hMle : M ≤ dNew := Nat.div_le_self _ _
    have hMU : M ≤ blockLength L i / 2 := by omega
    have hrOld : r ≤ dOld := Nat.div_le_self _ _
    have hOldD : dOld ≤ D := Nat.le_of_dvd hD hdOldD
    have hrHalf : r ≤ blockLength L (i + 1) / 2 := by omega
    have hlen : blockLength L (i + 1) / 2 ≤ M * (blockLength L (i + 1) - r) := by
      have hsub : blockLength L (i + 1) / 2 ≤ blockLength L (i + 1) - r := by omega
      exact hsub.trans (Nat.le_mul_of_pos_left _ hM)
    have hmerge := Erdos344.merge_AP_by_gcd hq hM hr hcop hMU
      (S := (occurrenceSums v (B (i + 1)) : Set ℕ))
      (U := (occurrenceSums v (usedBlocks B i) : Set ℕ))
      (by simpa [hdNewEq] using hNew) (by simpa [hdOldEq] using hOld)
    have hBU : Disjoint (B (i + 1)) (usedBlocks B i) := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxU
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxU
      have hjlt : j < i + 1 := Finset.mem_range.mp hj
      exact Finset.disjoint_left.mp (hdisj (by omega : i + 1 ≠ j)) hxB hxj
    have hUsed : B (i + 1) ∪ usedBlocks B i = usedBlocks B (i + 1) := by
      simp [usedBlocks, Finset.range_add_one, Finset.biUnion_insert]
    refine ⟨aNew + aOld + (q * M) * r, q, hq, hqdOld.trans hdOldD, ?_⟩
    intro j hj
    obtain ⟨x, hx, y, hy, hxy⟩ := hmerge j (hj.trans_le hlen)
    change x + y = aNew + aOld + (q * M) * r + j * q at hxy
    have hsum := add_mem_occurrenceSums hBU hx hy
    rwa [hUsed, hxy] at hsum

end Jsp285

/-! ### Upstream module `Jsp285/FixedStepFromBlocks.lean` -/

namespace Jsp285

/-- If every merged occurrence block contains a long progression whose
positive step divides one fixed integer, one step occurs on infinitely many
blocks and gives arbitrarily long progressions in all indexed subset sums. -/
theorem fixedStep_of_merged_occurrence_blocks
    (v : ℕ → ℕ) (B : ℕ → Finset ℕ) (L D : ℕ)
    (hL : 2 ≤ L) (hD : 0 < D)
    (hmerged : ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
      ∀ j < blockLength L i / 2,
        a + j * d ∈ occurrenceSums v (usedBlocks B i)) :
    Erdos344.HasFixedStepProgressions (indexedSubsetSums v Set.univ) := by
  let aa : ℕ → ℕ := fun i => (hmerged i).choose
  let dd : ℕ → ℕ := fun i => (hmerged i).choose_spec.choose
  have hspec (i : ℕ) : 0 < dd i ∧ dd i ∣ D ∧
      ∀ j < blockLength L i / 2,
        aa i + j * dd i ∈ occurrenceSums v (usedBlocks B i) :=
    (hmerged i).choose_spec.choose_spec
  have hddle (i : ℕ) : dd i ≤ D :=
    Nat.le_of_dvd hD (hspec i).2.1
  let f : ℕ → Fin (D + 1) := fun i =>
    ⟨dd i, Nat.lt_succ_of_le (hddle i)⟩
  obtain ⟨w, hw⟩ := Finite.exists_infinite_fiber f
  have hwset : (f ⁻¹' {w}).Infinite := Set.infinite_coe_iff.mp hw
  have hwpos : 0 < w.val := by
    obtain ⟨i, hi, -⟩ := hwset.exists_gt 0
    have hfi : f i = w := by simpa using hi
    have hval := congrArg (fun x : Fin (D + 1) => x.val) hfi
    change dd i = w.val at hval
    simpa [← hval] using (hspec i).1
  refine ⟨w.val, hwpos, ?_⟩
  intro k
  obtain ⟨i, hiFiber, hki⟩ := hwset.exists_gt k
  have hfi : f i = w := by simpa using hiFiber
  have hval := congrArg (fun x : Fin (D + 1) => x.val) hfi
  change dd i = w.val at hval
  refine ⟨aa i, ?_⟩
  intro j hj
  have hiHalf : i ≤ blockLength L i / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    calc
      i * 2 ≤ 2 ^ i * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt i.lt_two_pow_self)
      _ ≤ 2 ^ i * L := Nat.mul_le_mul_left (2 ^ i) hL
      _ = blockLength L i := by rfl
  have hx := (hspec i).2.2 j
    (hj.trans_le ((Nat.le_of_lt hki).trans hiHalf))
  rw [hval] at hx
  obtain ⟨J, hJ, hsum⟩ := mem_occurrenceSums.mp hx
  exact ⟨J, Set.subset_univ _, hsum.symm⟩

end Jsp285

/-! ### Upstream module `Jsp285/DivisorExtraction.lean` -/

/-!
Occurrence-preserving divisor extraction for the finite multiset theorem.
Adapts the credited plby Erdos344 descent, retaining indices with equal weights.
-/

namespace Jsp285

/-- Finite divisor descent that retains occurrence indices, so repeated weights never merge. -/
theorem exists_divisorExtractionAux {ι : Type*} [DecidableEq ι]
    (B L K d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ι) (v : ι → ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ι, ∃ w : ι → ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧ Z ⊆ Y ∧
      (∀ i ∈ Z, q * w i = v i) ∧
      Y.card - Z.card ≤ L * factors.length + K * factors.sum ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ (Z.filter fun i ↦ ¬e ∣ w i).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y v with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (Y.filter fun i ↦ ¬e ∣ v i).card < L + K * e
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := Y.filter fun i ↦ e ∣ v i
        let v' : ι → ℕ := fun i ↦ v i / e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, w, factors, hq, hqprod, hfactors, hdqB, hZY', hscale,
            hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' v' rfl
        refine ⟨e * q, Z, w, e :: factors, Nat.mul_pos hepos hq, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun hae ↦ hae ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · exact hZY'.trans (Finset.filter_subset _ _)
        · intro i hi
          have hiY' : i ∈ Y' := hZY' hi
          have hediv : e ∣ v i := (Finset.mem_filter.mp hiY').2
          calc
            (e * q) * w i = e * (q * w i) := by ring
            _ = e * v' i := by rw [hscale i hi]
            _ = v i := by
              simp only [v']
              exact Nat.mul_div_cancel' hediv
        · have hZle : Z.card ≤ Y'.card :=
            Finset.card_le_card hZY'
          have hY'le : Y'.card ≤ Y.card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          have hfilter : Y'.card + (Y.filter fun i ↦ ¬e ∣ v i).card = Y.card := by
            simpa only [Y'] using
              Finset.card_filter_add_card_filter_not (s := Y) (fun i ↦ e ∣ v i)
          have hfirst : Y.card - Y'.card ≤ L + K * e := by omega
          rw [hsplit]
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e) +
                  (L * factors.length + K * factors.sum) :=
              Nat.add_le_add hfirst hloss
            _ = L * (e :: factors).length + K * (e :: factors).sum := by
              simp only [List.length_cons, List.sum_cons]
              ring
        · intro a ha hbound
          exact hdiverse a ha (by simpa [mul_assoc] using hbound)
      · refine ⟨1, Y, v, [], by omega, by simp, by simp, ?_, by simp, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using Nat.lt_of_not_ge hnot

end Jsp285

/-! ### Upstream module `Jsp285/ExtractionBounds.lean` -/

/-! Quantitative and value bounds for occurrence-preserving divisor extraction. -/

namespace Jsp285

/-- The factor list gives a logarithmic fixed charge and a linear divisor charge. -/
theorem exists_divisorExtraction {ι : Type*} [DecidableEq ι]
    (B L K : ℕ) (hB : 0 < B) (Y : Finset ι) (v : ι → ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ι, ∃ w : ι → ℕ,
      0 < d ∧ d ≤ B ∧ Z ⊆ Y ∧
      (∀ i ∈ Z, d * w i = v i) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun i ↦ ¬e ∣ w i).card := by
  obtain ⟨d, Z, w, factors, hd, hdprod, hfactors, hdB, hZY,
    hscale, hloss, hdiverse⟩ := exists_divisorExtractionAux B L K 1 (by omega) hB Y v
  refine ⟨d, Z, w, hd, by simpa using hdB, hZY, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤ L * factors.length + K * factors.sum := hloss
      _ ≤ L * Nat.log 2 B + K * B := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left
          exact (Erdos344.length_le_log_prod_of_one_lt factors hfactors).trans
            (Nat.log_mono_right (by simpa [hdprod] using hdB))
        · apply Nat.mul_le_mul_left
          exact (Erdos344.sum_le_prod_of_one_lt factors hfactors).trans
            (by simpa [hdprod] using hdB)
  · intro e he hde
    exact hdiverse e he (by simpa using hde)

/-- Exact scaling transfers the original positive box to the normalized weights. -/
lemma normalized_weight_bounds {ι : Type*} {v w : ι → ℕ} {Y Z : Finset ι}
    {d n : ℕ} (hd : 0 < d) (hZY : Z ⊆ Y)
    (hbox : ∀ i ∈ Y, 0 < v i ∧ v i ≤ n)
    (hscale : ∀ i ∈ Z, d * w i = v i) :
    ∀ i ∈ Z, 0 < w i ∧ w i ≤ n / d := by
  intro i hi
  obtain ⟨hpos, hle⟩ := hbox i (hZY hi)
  have heq := hscale i hi
  constructor
  · by_contra h
    have : w i = 0 := by omega
    simp [this] at heq
    omega
  · apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceDyadic.lean` -/

/-! Dyadic classes of occurrence weights, preserving repeated values. -/

namespace Jsp285

/-- The occurrence indices whose weights have dyadic logarithm `j`. -/
def dyadicBin {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (j : ℕ) : Finset ι :=
  Y.filter fun i ↦ Nat.log 2 (v i) = j

/-- The weight in one dyadic bin lies between its cardinality times the lower
endpoint and twice that quantity. -/
lemma dyadicBin_weight_bounds {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (j : ℕ)
    (hpos : ∀ i ∈ Y, 0 < v i) :
    (dyadicBin v Y j).card * 2 ^ j ≤ ∑ i ∈ dyadicBin v Y j, v i ∧
      (∑ i ∈ dyadicBin v Y j, v i) ≤
        2 * ((dyadicBin v Y j).card * 2 ^ j) := by
  constructor
  · calc
      (dyadicBin v Y j).card * 2 ^ j =
          ∑ _i ∈ dyadicBin v Y j, 2 ^ j := by simp
      _ ≤ ∑ i ∈ dyadicBin v Y j, v i := by
        apply Finset.sum_le_sum
        intro i hi
        have hilog := (Finset.mem_filter.mp hi).2
        have hipos := hpos i (Finset.filter_subset _ _ hi)
        simpa [hilog] using Nat.pow_log_le_self 2 hipos.ne'
  · calc
      (∑ i ∈ dyadicBin v Y j, v i) ≤
          ∑ _i ∈ dyadicBin v Y j, 2 * 2 ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        have hilog := (Finset.mem_filter.mp hi).2
        have hiupper := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (v i)
        rw [hilog, pow_succ] at hiupper
        simpa [mul_comm] using hiupper.le
      _ = 2 * ((dyadicBin v Y j).card * 2 ^ j) := by simp; ring

/-- Positive weights bounded by `N` are partitioned by their dyadic logarithms. -/
lemma sum_dyadicBins {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (N : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
      ∑ i ∈ dyadicBin v Y j, v i) = ∑ i ∈ Y, v i := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, dyadicBin,
      Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hiY, _⟩
      exact hiY
    · intro hiY
      refine ⟨Nat.log 2 (v i), ?_, hiY, rfl⟩
      exact Nat.lt_succ_of_le <| Nat.log_mono_right (hY i hiY).2
  · change Set.PairwiseDisjoint
      (Finset.range (Nat.log 2 N + 1) : Set ℕ)
      (fun j ↦ Y.filter fun i ↦ Nat.log 2 (v i) = j)
    exact Set.pairwiseDisjoint_filter
      (fun i : ι ↦ Nat.log 2 (v i))
      (Finset.range (Nat.log 2 N + 1) : Set ℕ) Y

/-- Classwise balance in every dyadic weight class implies total weight balance. -/
theorem dyadic_weight_balance {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y S : Finset ι) (N a b c : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) (hS : S ⊆ Y)
    (hclasses : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      a * (dyadicBin v Y j).card ≤ b * (dyadicBin v S j).card ∧
      b * (dyadicBin v S j).card ≤ c * (dyadicBin v Y j).card) :
    a * (∑ i ∈ Y, v i) ≤ 2 * b * (∑ i ∈ S, v i) ∧
      b * (∑ i ∈ S, v i) ≤ 2 * c * (∑ i ∈ Y, v i) := by
  have hSweights : ∀ i ∈ S, 0 < v i ∧ v i ≤ N := fun i hi ↦ hY i (hS hi)
  rw [← sum_dyadicBins v Y N hY, ← sum_dyadicBins v S N hSweights]
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hYbounds := dyadicBin_weight_bounds v Y j (fun i hi ↦ (hY i hi).1)
    have hSbounds := dyadicBin_weight_bounds v S j (fun i hi ↦ (hSweights i hi).1)
    calc
      a * (∑ i ∈ dyadicBin v Y j, v i) ≤
          a * (2 * ((dyadicBin v Y j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left a hYbounds.2
      _ = 2 * (a * (dyadicBin v Y j).card) * 2 ^ j := by ring
      _ ≤ 2 * (b * (dyadicBin v S j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) <|
          Nat.mul_le_mul_left 2 (hclasses j hj).1
      _ = 2 * b * ((dyadicBin v S j).card * 2 ^ j) := by ring
      _ ≤ 2 * b * (∑ i ∈ dyadicBin v S j, v i) :=
        Nat.mul_le_mul_left (2 * b) hSbounds.1
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hYbounds := dyadicBin_weight_bounds v Y j (fun i hi ↦ (hY i hi).1)
    have hSbounds := dyadicBin_weight_bounds v S j (fun i hi ↦ (hSweights i hi).1)
    calc
      b * (∑ i ∈ dyadicBin v S j, v i) ≤
          b * (2 * ((dyadicBin v S j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left b hSbounds.2
      _ = 2 * (b * (dyadicBin v S j).card) * 2 ^ j := by ring
      _ ≤ 2 * (c * (dyadicBin v Y j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) <|
          Nat.mul_le_mul_left 2 (hclasses j hj).2
      _ = 2 * c * ((dyadicBin v Y j).card * 2 ^ j) := by ring
      _ ≤ 2 * c * (∑ i ∈ dyadicBin v Y j, v i) :=
        Nat.mul_le_mul_left (2 * c) hYbounds.1

end Jsp285

/-! ### Upstream module `Jsp285/OccurrencePrune.lean` -/

/-! Removing small dyadic classes of occurrence weights. -/

namespace Jsp285

/-- Remove every occurrence whose entire dyadic weight class has size below `Q`. -/
def dyadicPrune {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q : ℕ) : Finset ι :=
  Y.filter fun i ↦ Q ≤ (dyadicBin v Y (Nat.log 2 (v i))).card

/-- Dyadic pruning only removes occurrence indices. -/
lemma dyadicPrune_subset {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q : ℕ) :
    dyadicPrune v Y Q ⊆ Y :=
  Finset.filter_subset _ _

/-- Pruning either keeps an original dyadic bin whole or deletes it whole. -/
lemma dyadicBin_dyadicPrune {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q j : ℕ) :
    dyadicBin v (dyadicPrune v Y Q) j =
      if Q ≤ (dyadicBin v Y j).card then dyadicBin v Y j else ∅ := by
  ext i
  by_cases hlarge : Q ≤ (dyadicBin v Y j).card
  · rw [if_pos hlarge]
    constructor
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      have hiPrune := Finset.mem_filter.mp hiBin.1
      exact Finset.mem_filter.mpr ⟨hiPrune.1, hiBin.2⟩
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hiBin.1, ?_⟩, hiBin.2⟩
      simpa only [hiBin.2] using hlarge
  · rw [if_neg hlarge]
    constructor
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      have hiPrune := Finset.mem_filter.mp hiBin.1
      exact (hlarge <| by simpa only [hiBin.2] using hiPrune.2).elim
    · intro hi
      simp at hi

/-- Pruning small dyadic classes loses at most `Q` occurrences for each
possible logarithm of a positive weight bounded by `N`. -/
theorem card_sub_dyadicPrune_le {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (N Q : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) :
    Y.card - (dyadicPrune v Y Q).card ≤ (Nat.log 2 N + 1) * Q := by
  rw [← Finset.card_sdiff_of_subset (dyadicPrune_subset v Y Q)]
  let Jsmall := (Finset.range (Nat.log 2 N + 1)).filter fun j ↦
    (dyadicBin v Y j).card < Q
  let U := Jsmall.biUnion fun j ↦ dyadicBin v Y j
  have hlost : Y \ dyadicPrune v Y Q ⊆ U := by
    intro i hi
    have hiY := (Finset.mem_sdiff.mp hi).1
    have hinot := (Finset.mem_sdiff.mp hi).2
    have hilog : Nat.log 2 (v i) < Nat.log 2 N + 1 :=
      Nat.lt_succ_of_le <| Nat.log_mono_right (hY i hiY).2
    have hismall : (dyadicBin v Y (Nat.log 2 (v i))).card < Q := by
      simpa only [dyadicPrune, Finset.mem_filter, hiY, true_and, not_le] using hinot
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 (v i), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilog, hismall⟩
    · exact Finset.mem_filter.mpr ⟨hiY, rfl⟩
  have hUcard : U.card ≤ ∑ j ∈ Jsmall, (dyadicBin v Y j).card :=
    Finset.card_biUnion_le
  have hsum : (∑ j ∈ Jsmall, (dyadicBin v Y j).card) ≤ Jsmall.card * Q := by
    calc
      (∑ j ∈ Jsmall, (dyadicBin v Y j).card) ≤ ∑ _j ∈ Jsmall, Q := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2.le
      _ = Jsmall.card * Q := by simp
  have hJcard : Jsmall.card ≤ Nat.log 2 N + 1 := by
    calc
      Jsmall.card ≤ (Finset.range (Nat.log 2 N + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.log 2 N + 1 := by simp
  calc
    (Y \ dyadicPrune v Y Q).card ≤ U.card := Finset.card_le_card hlost
    _ ≤ ∑ j ∈ Jsmall, (dyadicBin v Y j).card := hUcard
    _ ≤ Jsmall.card * Q := hsum
    _ ≤ (Nat.log 2 N + 1) * Q := Nat.mul_le_mul_right Q hJcard

end Jsp285

/-! ### Upstream module `Jsp285/FiniteConstants.lean` -/

/-! Absolute constants and uniform elementary bounds for the multiset construction. -/

namespace Jsp285

/-- Partition depth amplification in the proved finite sum-tree theorem. -/
def partitionMass : ℕ := 200 ^ 49

/-- The finite occurrence theorem uses this absolute linear coefficient. -/
def finiteCoefficient : ℕ := 200000 * partitionMass

/-- A cubic in the binary logarithm is bounded uniformly, including small inputs. -/
lemma cube_succ_le_eight_pow (k : ℕ) : (k + 1) ^ 3 ≤ 8 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · have hk3 : 3 ≤ k := by omega
        have hsq : 9 ≤ k ^ 2 := by nlinarith
        have hcube := Nat.mul_le_mul_left k hsq
        calc
          (k + 1 + 1) ^ 3 ≤ 2 * (k + 1) ^ 3 := by nlinarith
          _ ≤ 2 * (8 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
          _ = 8 * 2 ^ (k + 1) := by ring

/-- The logarithmic extraction and pruning charges fit inside a linear budget. -/
lemma log_cube_le (n : ℕ) (hn : 0 < n) : (Nat.log 2 n + 1) ^ 3 ≤ 8 * n := by
  exact (cube_succ_le_eight_pow _).trans
    (Nat.mul_le_mul_left 8 (Nat.pow_log_le_self 2 hn.ne'))

/-- Total extraction and dyadic-pruning loss is linear in the original bound. -/
lemma extraction_prune_loss_bound (n H : ℕ) (hn : 0 < n) :
    ((Nat.log 2 n + 2) * (10000 * H * (Nat.log 2 n + 1))) * Nat.log 2 n +
      H * n + (Nat.log 2 n + 1) * (10000 * H * (Nat.log 2 n + 1)) ≤
        160001 * H * n := by
  have h := Nat.mul_le_mul_left (20000 * H) (log_cube_le n hn)
  nlinarith [Nat.zero_le (H * Nat.log 2 n)]

/-- Tracking at most three times the ambient bound fits the chosen threshold. -/
lemma tracking_threshold_le (n m H : ℕ) (hn : 0 < n) (hm : m ≤ 3 * n) :
    1000 * (Nat.log 2 (2 * m + 1) + 1) * H ≤
      10000 * H * (Nat.log 2 n + 1) := by
  have hbound : 2 * m + 1 ≤ 8 * n := by omega
  have hlog : Nat.log 2 (8 * n) = Nat.log 2 n + 3 := by
    rw [show 8 * n = ((n * 2) * 2) * 2 by ring]
    rw [Nat.log_mul_base (by omega) (by positivity),
      Nat.log_mul_base (by omega) (by positivity),
      Nat.log_mul_base (by omega) hn.ne']
  have hmono := Nat.log_mono_right (b := 2) hbound
  rw [hlog] at hmono
  have hscaled := Nat.mul_le_mul_right (1000 * H) hmono
  nlinarith [Nat.zero_le (H * Nat.log 2 n)]

end Jsp285

/-! ### Upstream module `Jsp285/PreparedOccurrences.lean` -/

/-! Extraction and pruning retain linearly many diverse occurrence indices. -/

namespace Jsp285

/-- Filtering a subset loses no more elements than were removed from the whole set. -/
lemma filter_card_loss_le {ι : Type*} [DecidableEq ι] {S Z : Finset ι}
    (hSZ : S ⊆ Z) (p : ι → Prop) [DecidablePred p] :
    (Z.filter p).card - (S.filter p).card ≤ Z.card - S.card := by
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset_filter p hSZ),
    ← Finset.card_sdiff_of_subset hSZ]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_filter] at hi ⊢
  tauto

/-- Absolute mass and diversity reserves after normalization and whole-bin pruning. -/
theorem exists_prepared_occurrences {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (v : ι → ℕ) (I : Finset ι)
    (hbox : ∀ i ∈ I, 0 < v i ∧ v i ≤ n)
    (hcount : finiteCoefficient * n ≤ I.card) :
    ∃ d : ℕ, ∃ S : Finset ι, ∃ w : ι → ℕ,
      0 < d ∧ d ≤ n ∧ S ⊆ I ∧
      (∀ i ∈ S, d * w i = v i) ∧
      (∀ i ∈ S, 0 < w i ∧ w i ≤ n / d) ∧
      39999 * partitionMass * n ≤ S.card ∧
      (∀ e : ℕ, 1 < e → d * e ≤ n →
        10000 * partitionMass * (Nat.log 2 n + 1) + partitionMass * e ≤
          (S.filter fun i ↦ ¬e ∣ w i).card) ∧
      (∀ j : ℕ, (dyadicBin w S j).Nonempty →
        10000 * partitionMass * (Nat.log 2 n + 1) ≤ (dyadicBin w S j).card) := by
  classical
  let H := partitionMass
  let r := Nat.log 2 n + 1
  let Q := 10000 * H * r
  let L := (r + 1) * Q
  obtain ⟨d, Z, w, hd, hdn, hZI, hscale, hloss, hdiv⟩ :=
    exists_divisorExtraction n L H hn I v
  have hnorm := normalized_weight_bounds hd hZI hbox hscale
  have hZbox : ∀ i ∈ Z, 0 < w i ∧ w i ≤ n := by
    intro i hi
    exact ⟨(hnorm i hi).1, (hnorm i hi).2.trans (Nat.div_le_self _ _)⟩
  let S := dyadicPrune w Z Q
  have hSZ : S ⊆ Z := dyadicPrune_subset w Z Q
  have hSI : S ⊆ I := hSZ.trans hZI
  have hprune : Z.card - S.card ≤ r * Q := card_sub_dyadicPrune_le w Z n Q hZbox
  have htotal : I.card - S.card ≤ 160001 * H * n := by
    have hZle := Finset.card_le_card hZI
    have hSle := Finset.card_le_card hSZ
    have hsplit : I.card - S.card = (I.card - Z.card) + (Z.card - S.card) := by
      omega
    rw [hsplit]
    exact (Nat.add_le_add hloss hprune).trans (extraction_prune_loss_bound n H hn)
  have hremaining : 39999 * H * n ≤ S.card := by
    change 200000 * H * n ≤ I.card at hcount
    have hnat : I.card ≤ (I.card - S.card) + S.card := by omega
    nlinarith
  refine ⟨d, S, w, hd, hdn, hSI, fun i hi ↦ hscale i (hSZ hi),
    fun i hi ↦ hnorm i (hSZ hi), hremaining, ?_, ?_⟩
  · intro e he hde
    have hstart := hdiv e he hde
    have hdiff := (filter_card_loss_le hSZ (fun i ↦ ¬e ∣ w i)).trans hprune
    have hformula : L = r * Q + Q := by dsimp [L]; ring
    change Q + H * e ≤ _
    rw [hformula] at hstart
    omega
  · intro j hj
    change Q ≤ (dyadicBin w S j).card
    dsimp only [S] at hj ⊢
    by_cases h : Q ≤ (dyadicBin w Z j).card
    · simp [dyadicBin_dyadicPrune, h]
    · rw [dyadicBin_dyadicPrune, if_neg h] at hj
      exact (Finset.not_nonempty_empty hj).elim

end Jsp285

/-! ### Upstream module `Jsp285/OccurrencePartition.lean` -/

/-!
Occurrence-indexed simultaneous divisor and dyadic partition.
Adapted from plby Erdos344.exists_dyadic_diverse_partition with attribution retained.
-/

namespace Jsp285

open Erdos344

/-- Balance the full carrier, divisor classes and specified dyadic bins simultaneously. -/
theorem exists_dyadic_diverse_partition {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (t : ℕ) (S : Finset ι) (Q : ℕ) (E Jbins : Finset ℕ)
    (hwhole : Q ≤ S.card)
    (hdiv : ∀ e ∈ E, Q ≤ (S.filter fun x ↦ ¬e ∣ v x).card)
    (hbin : ∀ j ∈ Jbins,
      Q ≤ (dyadicBin v S j).card)
    (hQ : (1000 * (Nat.log 2
        (2 * (1 + E.card + (Jbins).card) + 1) + 1)) *
        200 ^ t ≤ Q) :
    ∃ T : PartitionTree ι t,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        (89 ^ t * S.card ≤ 200 ^ t * C.card ∧
          200 ^ t * C.card ≤ 111 ^ t * S.card) ∧
        (∀ e ∈ E,
          89 ^ t * (S.filter fun x ↦ ¬e ∣ v x).card ≤
              200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ v x)).card ∧
          200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ v x)).card ≤
              111 ^ t * (S.filter fun x ↦ ¬e ∣ v x).card) ∧
        (∀ j ∈ Jbins,
          89 ^ t * (dyadicBin v S j).card ≤
              200 ^ t * (C ∩ dyadicBin v S j).card ∧
          200 ^ t * (C ∩ dyadicBin v S j).card ≤
              111 ^ t * (dyadicBin v S j).card) := by
  classical
  let κ := Unit ⊕ (ℕ ⊕ ℕ)
  let Jwhole : Finset κ := {Sum.inl ()}
  let Jdiv : Finset κ := E.image fun e ↦ Sum.inr (Sum.inl e)
  let Jbin : Finset κ :=
    (Jbins).image fun j ↦ Sum.inr (Sum.inr j)
  let J := Jwhole ∪ Jdiv ∪ Jbin
  let F : κ → Finset ι
    | Sum.inl _ => S
    | Sum.inr (Sum.inl e) => S.filter fun x ↦ ¬e ∣ v x
    | Sum.inr (Sum.inr j) => dyadicBin v S j
  have hJcard : J.card ≤
      1 + E.card + (Jbins).card := by
    calc
      J.card ≤ (Jwhole ∪ Jdiv).card + Jbin.card := Finset.card_union_le _ _
      _ ≤ (Jwhole.card + Jdiv.card) + Jbin.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 1 + E.card + (Jbins).card := by
        have hdivCard : Jdiv.card ≤ E.card := by
          dsimp only [Jdiv]
          exact Finset.card_image_le
        have hbinCard : Jbin.card ≤ (Jbins).card := by
          dsimp only [Jbin]
          exact Finset.card_image_le
        simp only [Jwhole, Finset.card_singleton]
        omega
  have hlog : Nat.log 2 (2 * J.card + 1) ≤
      Nat.log 2
        (2 * (1 + E.card + (Jbins).card) + 1) := by
    apply Nat.log_mono_right
    omega
  have hsub : ∀ z ∈ J, F z ⊆ S := by
    intro z hz
    rcases z with _ | z
    · exact Finset.Subset.rfl
    · rcases z with e | j
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
  have hlarge : ∀ z ∈ J,
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
        89 ^ t * (F z).card := by
    intro z hz
    have hthreshold :
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := by
      calc
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
            (1000 * (Nat.log 2
              (2 * (1 + E.card +
                (Jbins).card) + 1) + 1)) * 200 ^ t := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add_right hlog 1
        _ ≤ Q := hQ
    have hFQ : Q ≤ (F z).card := by
      rcases z with z | z
      · simpa [F] using hwhole
      · rcases z with e | j
        · have hzdiv : Sum.inr (Sum.inl e) ∈ Jdiv := by
            have hz' : Sum.inr (Sum.inl e) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inl e) ∈ Jbin := Finset.mem_union.mp hz
            rcases hz' with hz' | hzbin
            · exact (Finset.mem_union.mp hz').resolve_left (by simp [Jwhole])
            · exfalso
              simp [Jbin] at hzbin
          have he : e ∈ E := by simpa [Jdiv] using hzdiv
          simpa [F] using hdiv e he
        · have hzbin : Sum.inr (Sum.inr j) ∈ Jbin := by
            have hz' : Sum.inr (Sum.inr j) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inr j) ∈ Jbin := Finset.mem_union.mp hz
            exact hz'.resolve_left (by
              intro h
              rcases Finset.mem_union.mp h with hw | hd
              · simp [Jwhole] at hw
              · simp [Jdiv] at hd)
          have hj : j ∈ Jbins := by
            simpa [Jbin] using hzbin
          simpa [F] using hbin j hj
    calc
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := hthreshold
      _ ≤ (F z).card := hFQ
      _ = 1 * (F z).card := by simp
      _ ≤ 89 ^ t * (F z).card :=
        Nat.mul_le_mul_right (F z).card (one_le_pow₀ (by omega))
  obtain ⟨T, hTcarrier, hTdisj, hTleaves⟩ :=
    PartitionTree.exists_tight_partition t S J F hsub hlarge
  refine ⟨T, hTcarrier, hTdisj, ?_⟩
  refine (hTleaves.and (PartitionTree.allLeaves_subset_carrier T)).mono ?_
  rintro C ⟨hC, hCsub⟩
  have hCS : C ⊆ S := by simpa [hTcarrier] using hCsub
  have hwholeMem : Sum.inl () ∈ J := by simp [J, Jwhole]
  have hwholeRatio := hC (Sum.inl ()) hwholeMem
  have hwholeInter : C ∩ S = C := Finset.inter_eq_left.mpr hCS
  refine ⟨by simpa [F, hwholeInter] using hwholeRatio, ?_, ?_⟩
  · intro e he
    have hz : Sum.inr (Sum.inl e) ∈ J := by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inl e)) hz
  · intro j hj
    have hz : Sum.inr (Sum.inr j) ∈ J := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inr j)) hz

end Jsp285

/-! ### Upstream module `Jsp285/OccupiedBalance.lean` -/

/-! It suffices to balance the occupied weight classes. -/

namespace Jsp285

/-- Balance of occupied class intersections yields the full weighted mass bounds. -/
lemma dyadic_weight_balance_occupied {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y C : Finset ι) (N a b c : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) (hCY : C ⊆ Y)
    (hclasses : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      (dyadicBin v Y j).Nonempty →
        a * (dyadicBin v Y j).card ≤ b * (C ∩ dyadicBin v Y j).card ∧
        b * (C ∩ dyadicBin v Y j).card ≤ c * (dyadicBin v Y j).card) :
    a * (∑ i ∈ Y, v i) ≤ 2 * b * (∑ i ∈ C, v i) ∧
      b * (∑ i ∈ C, v i) ≤ 2 * c * (∑ i ∈ Y, v i) := by
  apply dyadic_weight_balance v Y C N a b c hY hCY
  intro j hj
  have hinter : C ∩ dyadicBin v Y j = dyadicBin v C j := by
    ext i
    simp only [Finset.mem_inter, dyadicBin, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hCY h.1, h.2⟩⟩
  by_cases hne : (dyadicBin v Y j).Nonempty
  · simpa [hinter] using hclasses j hj hne
  · have he : dyadicBin v Y j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hC : dyadicBin v C j = ∅ := by rw [← hinter, he]; simp
    simp [he, hC]

end Jsp285

/-! ### Upstream module `Jsp285/BalancedOccurrences.lean` -/

/-! Balanced depth-49 leaves from prepared occurrence indices. -/

namespace Jsp285

/-- Prepared occurrence weights have a depth-49 partition whose leaves retain
divisor diversity and a fixed proportion of the total weight. -/
theorem exists_balanced_occurrence_partition
    {ι : Type*} [DecidableEq ι] (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (_hdn : d ≤ n) (w : ι → ℕ) (S : Finset ι)
    (hbox : ∀ i ∈ S, 0 < w i ∧ w i ≤ n / d)
    (hcount : 39999 * partitionMass * n ≤ S.card)
    (hdiv : ∀ e : ℕ, 1 < e → d * e ≤ n →
      10000 * partitionMass * (Nat.log 2 n + 1) + partitionMass * e ≤
        (S.filter fun i ↦ ¬e ∣ w i).card)
    (hbin : ∀ j : ℕ, (dyadicBin w S j).Nonempty →
      10000 * partitionMass * (Nat.log 2 n + 1) ≤
        (dyadicBin w S j).card) :
    ∃ T : Erdos344.PartitionTree ι 49,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        C ⊆ S ∧
        (∀ e : ℕ, 1 < e → e ≤ n / d →
          e - 1 ≤ (C.filter fun i ↦ ¬e ∣ w i).card) ∧
        89 ^ 49 * (∑ i ∈ S, w i) ≤
          2 * partitionMass * (∑ i ∈ C, w i) ∧
        partitionMass * (∑ i ∈ C, w i) ≤
          2 * 111 ^ 49 * (∑ i ∈ S, w i) := by
  let Q := 10000 * partitionMass * (Nat.log 2 n + 1)
  let E := Finset.Icc 2 (n / d)
  let Jbins := (Finset.range (Nat.log 2 n + 1)).filter fun j ↦
    (dyadicBin w S j).Nonempty
  let m := 1 + E.card + Jbins.card
  have hr : Nat.log 2 n + 1 ≤ n := by
    exact Nat.lt_succ_iff.mp <| Nat.add_lt_add_right
      (Nat.log_lt_self 2 hn.ne') 1
  have hEcard : E.card ≤ n := by
    dsimp only [E]
    rw [Nat.card_Icc]
    have hdivle := Nat.div_le_self n d
    omega
  have hJcard : Jbins.card ≤ n := by
    calc
      Jbins.card ≤ (Finset.range (Nat.log 2 n + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.log 2 n + 1 := by simp
      _ ≤ n := hr
  have hm : m ≤ 3 * n := by
    dsimp only [m]
    omega
  have hQ : Q ≤ S.card := by
    have hscaled := Nat.mul_le_mul_left (10000 * partitionMass) hr
    have hQcount : Q ≤ 39999 * partitionMass * n := by
      dsimp only [Q]
      nlinarith [Nat.zero_le (partitionMass * n)]
    exact hQcount.trans hcount
  have hQthreshold :
      (1000 * (Nat.log 2 (2 * (1 + E.card + Jbins.card) + 1) + 1)) *
          200 ^ 49 ≤ Q := by
    have hthreshold := tracking_threshold_le n m partitionMass hn hm
    simpa only [m, Q, partitionMass] using hthreshold
  have hdivTracked : ∀ e ∈ E, Q ≤ (S.filter fun i ↦ ¬e ∣ w i).card := by
    intro e he
    have heIcc := Finset.mem_Icc.mp he
    have hde : d * e ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp heIcc.2
    exact (Nat.le_add_right Q (partitionMass * e)).trans
      (hdiv e heIcc.1 hde)
  have hbinTracked : ∀ j ∈ Jbins, Q ≤ (dyadicBin w S j).card := by
    intro j hj
    exact hbin j (Finset.mem_filter.mp hj).2
  obtain ⟨T, hTcarrier, hTdisj, hTleaves⟩ :=
    exists_dyadic_diverse_partition w 49 S Q E Jbins hQ hdivTracked
      hbinTracked hQthreshold
  refine ⟨T, hTcarrier, hTdisj, ?_⟩
  refine (hTleaves.and (Erdos344.PartitionTree.allLeaves_subset_carrier T)).mono ?_
  rintro C ⟨hraw, hCcarrier⟩
  have hCS : C ⊆ S := by simpa only [hTcarrier] using hCcarrier
  refine ⟨hCS, ?_, ?_⟩
  · intro e he heN
    have heE : e ∈ E := Finset.mem_Icc.mpr ⟨he, heN⟩
    have hde : d * e ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp heN
    have hclassS := hdiv e he hde
    have hclassRaw := (hraw.2.1 e heE).1
    have hinter : C ∩ (S.filter fun i ↦ ¬e ∣ w i) =
        C.filter fun i ↦ ¬e ∣ w i := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hCS h.1, h.2⟩⟩
    rw [hinter] at hclassRaw
    have hmassPos : 0 < partitionMass := by norm_num [partitionMass]
    have hone : (S.filter fun i ↦ ¬e ∣ w i).card ≤
        89 ^ 49 * (S.filter fun i ↦ ¬e ∣ w i).card := by
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    change 89 ^ 49 * (S.filter fun i ↦ ¬e ∣ w i).card ≤
      partitionMass * (C.filter fun i ↦ ¬e ∣ w i).card at hclassRaw
    change Q + partitionMass * e ≤ _ at hclassS
    have hHe : partitionMass * e ≤
        (S.filter fun i ↦ ¬e ∣ w i).card := by omega
    have hprod : partitionMass * e ≤
        partitionMass * (C.filter fun i ↦ ¬e ∣ w i).card :=
      hHe.trans <| hone.trans hclassRaw
    have heCard := Nat.le_of_mul_le_mul_left hprod hmassPos
    omega
  · have hSbox : ∀ i ∈ S, 0 < w i ∧ w i ≤ n := by
      intro i hi
      exact ⟨(hbox i hi).1, (hbox i hi).2.trans (Nat.div_le_self n d)⟩
    apply dyadic_weight_balance_occupied w S C n (89 ^ 49)
      partitionMass (111 ^ 49) hSbox hCS
    intro j hj hjne
    have hjJ : j ∈ Jbins := Finset.mem_filter.mpr ⟨hj, hjne⟩
    simpa only [partitionMass] using hraw.2.2 j hjJ

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceTree.lean` -/

/-! Partition trees of occurrence indices and their actual weighted subset sums. -/

namespace Jsp285

/-- Leafwise properties combine under the pointwise union of two partition
trees at the same depth. -/
lemma allLeaves_zipUnion_of_separate
    {ι : Type*} [DecidableEq ι] {t : ℕ}
    {P Q R : Finset ι → Prop} (A B : Erdos344.PartitionTree ι t)
    (hA : A.AllLeaves P) (hB : B.AllLeaves Q)
    (hcombine : ∀ C D, P C → Q D → R (C ∪ D)) :
    (A.zipUnion B).AllLeaves R := by
  induction A with
  | leaf C =>
      cases B with
      | leaf D => exact hcombine C D hA hB
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          exact ⟨ih₁ B₁ hA.1 hB.1, ih₂ B₂ hA.2 hB.2⟩

/-- The additive carrier obtained by mapping every leaf to its occurrence
subset sums is contained in the subset sums of the whole occurrence carrier. -/
lemma carrier_map_occurrenceSums_subset
    {ι : Type*} [DecidableEq ι] {t : ℕ} (v : ι → ℕ)
    (T : Erdos344.PartitionTree ι t) (hdisj : T.PairwiseDisjoint) :
    (T.mapSumTree (occurrenceSums v)).carrier ⊆ occurrenceSums v T.carrier := by
  induction T with
  | leaf C => exact fun _ hx => hx
  | node A B ihA ihB =>
      rcases hdisj with ⟨hA, hB, hAB⟩
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      exact add_mem_occurrenceSums hAB (ihA hA ha) (ihB hB hb)

/-- A deep disjoint occurrence tree with large bounded leaf sumsets contains
the progression supplied by the generic sum-tree growth theorem. -/
theorem containsFiniteAP_of_occurrence_tree
    {ι : Type*} [DecidableEq ι] {t K box : ℕ} (v : ι → ℕ)
    (T : Erdos344.PartitionTree ι t) (hK : 2 ≤ K)
    (hdisj : T.PairwiseDisjoint)
    (hcard : T.AllLeaves fun C => K ≤ (occurrenceSums v C).card)
    (hbox : T.AllLeaves fun C => occurrenceSums v C ⊆ Finset.Icc 0 box)
    (hexceed : 2 ^ t * box + 1 < Erdos344.SumTree.growthLower K t) :
    Erdos344.ContainsFiniteAP (occurrenceSums v T.carrier : Set ℕ) (2 * K - 1) := by
  let U := T.mapSumTree (occurrenceSums v)
  have hzeroT : T.AllLeaves fun C => 0 ∈ occurrenceSums v C :=
    hcard.mono fun C _ => zero_mem_occurrenceSums v C
  have hzeroU : U.AllLeaves fun S => 0 ∈ S := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => 0 ∈ S)).mpr hzeroT
  have hcardU : U.AllLeaves fun S => K ≤ S.card := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => K ≤ S.card)).mpr hcard
  have hboxU : U.AllLeaves fun S => S ⊆ Finset.Icc 0 box := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => S ⊆ Finset.Icc 0 box)).mpr hbox
  have hAP := Erdos344.SumTree.containsFiniteAP_of_growth_exceeds_diameter
    hK hzeroU hcardU hboxU hexceed
  exact Erdos344.containsFiniteAP_mono
    (carrier_map_occurrenceSums_subset v T hdisj) hAP

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceModular.lean` -/

/-! Modular completeness using distinct occurrence indices, with repeated weights allowed. -/

namespace Jsp285

/-- Divisor diversity of the occurrence weights forces their subset sums to
cover every residue modulo `q`.  Occurrences remain distinguished even when
several of them have the same weight. -/
theorem occurrenceSums_mod_eq_univ_of_divisor_diverse
    {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q]
    (hq : 0 < q) (v : ι → ℕ) (I : Finset ι)
    (hdiverse : ∀ e : ℕ, 1 < e → e ∣ q →
      e - 1 ≤ (I.filter fun i => ¬ e ∣ v i).card) :
    (occurrenceSums v I).image (fun x : ℕ => (x : ZMod q)) = Finset.univ := by
  have hlist :
      Erdos587.listSubsetSums
          (I.toList.map fun i => (v i : ZMod q)) = Finset.univ := by
    have h := Erdos344.listSubsetSums_mod_eq_univ_of_divisor_diverse
      hq (I.toList.map v) (by
        intro e he heq
        have hlen :
            ((I.toList.map v).filter fun a => ¬ e ∣ a).length =
              (I.filter fun i => ¬ e ∣ v i).card := by
          rw [List.filter_map, List.length_map]
          have hc := I.nodup_toList.card_eq_countP
            (P := fun i => ¬ e ∣ v i)
          simpa [List.countP_eq_length_filter, Function.comp_def] using hc.symm
        rw [hlen]
        exact hdiverse e he heq)
    simpa [List.map_map, Function.comp_def] using h
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  have hz : z ∈ Erdos587.listSubsetSums
      (I.toList.map fun i => (v i : ZMod q)) := by
    rw [hlist]
    exact Finset.mem_univ z
  obtain ⟨T, hTI, hTsum⟩ :=
    Erdos587.mem_listSubsetSums_iff.mp hz
  obtain ⟨U, hUI, rfl⟩ :=
    (List.sublist_map_iff (l₂ := I.toList)
      (f := fun i => (v i : ZMod q))).mp hTI
  refine Finset.mem_image.mpr ⟨U.toFinset.sum v, ?_, ?_⟩
  · apply mem_occurrenceSums.mpr
    refine ⟨U.toFinset, ?_, rfl⟩
    intro i hi
    exact Finset.mem_toList.mp (hUI.mem (List.mem_toFinset.mp hi))
  · rw [List.sum_toFinset v (I.nodup_toList.sublist hUI)]
    simpa [Function.comp_def] using hTsum

end Jsp285

/-! ### Upstream module `Jsp285/OccurrencePivot.lean` -/

/-! Adding distinct pivot occurrences with repeated weights. -/

namespace Jsp285

/-- Adjoining a fresh occurrence contains both the old subset sums and their
translate by the weight of that occurrence. -/
lemma union_natAddTranslate_occurrenceSums_subset
    {ι : Type*} [DecidableEq ι] (v : ι → ℕ) (I : Finset ι) (i : ι)
    (hi : i ∉ I) :
    occurrenceSums v I ∪ Erdos344.natAddTranslate (v i) (occurrenceSums v I) ⊆
      occurrenceSums v (insert i I) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact occurrenceSums_mono v (Finset.subset_insert i I) hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨J, hJI, rfl⟩ := mem_occurrenceSums.mp hy
    apply mem_occurrenceSums.mpr
    refine ⟨insert i J, Finset.insert_subset_insert i hJI, ?_⟩
    rw [Finset.sum_insert (fun hij => hi (hJI hij))]
    omega

/-- Adding distinct positive pivot occurrences grows the occurrence subset-sum
set by at least the sum of their weights, provided the base sums cover every
residue modulo each pivot weight. -/
theorem card_occurrenceSums_add_pivots
    {ι : Type*} [DecidableEq ι] (v : ι → ℕ) (B P : Finset ι)
    (hdisj : Disjoint B P) (hpos : ∀ i ∈ P, 0 < v i)
    (hcover : ∀ i ∈ P, ∀ z : ZMod (v i),
      ∃ x ∈ occurrenceSums v B, (x : ZMod (v i)) = z) :
    (occurrenceSums v B).card + ∑ i ∈ P, v i ≤
      (occurrenceSums v (B ∪ P)).card := by
  classical
  induction P using Finset.induction with
  | empty => simp
  | @insert i P hiP ih =>
      have hiB : i ∉ B := by
        intro hi
        exact Finset.disjoint_left.mp hdisj hi
          (Finset.mem_insert_self i P)
      have hdisjP : Disjoint B P :=
        hdisj.mono_right (Finset.subset_insert i P)
      have hposP : ∀ j ∈ P, 0 < v j := by
        intro j hj
        exact hpos j (Finset.mem_insert_of_mem hj)
      have hcoverP : ∀ j ∈ P, ∀ z : ZMod (v j),
          ∃ x ∈ occurrenceSums v B, (x : ZMod (v j)) = z := by
        intro j hj
        exact hcover j (Finset.mem_insert_of_mem hj)
      have hIH := ih hdisjP hposP hcoverP
      have hvi : 0 < v i := hpos i (Finset.mem_insert_self i P)
      let _ : NeZero (v i) := ⟨hvi.ne'⟩
      let T := occurrenceSums v (B ∪ P)
      have hbase : occurrenceSums v B ⊆ T :=
        occurrenceSums_mono v (Finset.subset_union_left)
      have hres :
          (T.image fun x : ℕ => (x : ZMod (v i))).card = v i := by
        have himage : T.image (fun x : ℕ => (x : ZMod (v i))) = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro z
          obtain ⟨x, hx, hxz⟩ := hcover i (Finset.mem_insert_self i P) z
          exact Finset.mem_image.mpr ⟨x, hbase hx, hxz⟩
        rw [himage, Finset.card_univ, ZMod.card]
      have hgrowth := Erdos344.card_add_modulus_growth hvi T
      have hiBP : i ∉ B ∪ P := by simp [hiB, hiP]
      have hsubset :
          T ∪ Erdos344.natAddTranslate (v i) T ⊆
            occurrenceSums v (insert i (B ∪ P)) :=
        union_natAddTranslate_occurrenceSums_subset v (B ∪ P) i hiBP
      rw [Finset.sum_insert hiP, Finset.union_insert]
      calc
        (occurrenceSums v B).card + (v i + ∑ j ∈ P, v j) =
            ((occurrenceSums v B).card + ∑ j ∈ P, v j) + v i := by omega
        _ ≤ T.card + v i := Nat.add_le_add_right hIH _
        _ = T.card + (T.image fun x : ℕ => (x : ZMod (v i))).card := by
          rw [hres]
        _ ≤ (T ∪ Erdos344.natAddTranslate (v i) T).card := hgrowth
        _ ≤ (occurrenceSums v (insert i (B ∪ P))).card :=
          Finset.card_le_card hsubset

end Jsp285

/-! ### Upstream module `Jsp285/LeafMassBounds.lean` -/

/-! Convert balanced occurrence masses and modular coverage into sum-tree leaf bounds. -/

namespace Jsp285

/-- Modularly diverse base occurrences and balanced pair masses give the
cardinality and interval bounds required of a sum-tree leaf. -/
theorem pair_leaf_bounds {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (B P : Finset ι) (N W H a b : ℕ)
    (hH : 0 < H) (hdisj : Disjoint B P)
    (hposP : ∀ i ∈ P, 0 < v i ∧ v i ≤ N)
    (hdivB : ∀ e : ℕ, 1 < e → e ≤ N →
      e - 1 ≤ (B.filter fun i ↦ ¬e ∣ v i).card)
    (hlower : a * W ≤ 2 * H * (∑ i ∈ P, v i))
    (hupper : H * ((∑ i ∈ B, v i) + ∑ i ∈ P, v i) ≤ 4 * b * W) :
    a * ((W / H) / 16) ≤ (occurrenceSums v (B ∪ P)).card ∧
      occurrenceSums v (B ∪ P) ⊆
        Finset.Icc 0 (40 * b * (W / H + 1)) := by
  have hcover : ∀ i ∈ P, ∀ z : ZMod (v i),
      ∃ x ∈ occurrenceSums v B, (x : ZMod (v i)) = z := by
    intro i hi z
    have hvipos := (hposP i hi).1
    let _ : NeZero (v i) := ⟨hvipos.ne'⟩
    have hmod := occurrenceSums_mod_eq_univ_of_divisor_diverse
      hvipos v B (by
        intro e he hedvd
        apply hdivB e he
        exact (Nat.le_of_dvd hvipos hedvd).trans (hposP i hi).2)
    have hz : z ∈ (occurrenceSums v B).image
        (fun x : ℕ ↦ (x : ZMod (v i))) := by
      rw [hmod]
      exact Finset.mem_univ z
    exact Finset.mem_image.mp hz
  have hpivot := card_occurrenceSums_add_pivots v B P hdisj
    (fun i hi ↦ (hposP i hi).1) hcover
  have hmassCard : (∑ i ∈ P, v i) ≤
      (occurrenceSums v (B ∪ P)).card := by
    omega
  have hquot : H * (W / H) ≤ W := Nat.mul_div_le W H
  have haquot : a * (W / H) ≤ 2 * (∑ i ∈ P, v i) := by
    have hscaled := Nat.mul_le_mul_left a hquot
    nlinarith
  have htwo : 2 * ((W / H) / 16) ≤ W / H := by
    have hsixteen := Nat.mul_div_le (W / H) 16
    omega
  have hKmass : a * ((W / H) / 16) ≤ ∑ i ∈ P, v i := by
    have hscaled := Nat.mul_le_mul_left a htwo
    nlinarith
  constructor
  · exact hKmass.trans hmassCard
  · intro x hx
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.zero_le x, ?_⟩
    have hxmass := occurrenceSum_le_mass hx
    rw [Finset.sum_union hdisj] at hxmass
    have hWlt : W < H * (W / H + 1) := Nat.lt_mul_div_succ W hH
    have htotal : (∑ i ∈ B, v i) + ∑ i ∈ P, v i ≤
        4 * b * (W / H + 1) := by
      nlinarith
    calc
      x ≤ (∑ i ∈ B, v i) + ∑ i ∈ P, v i := hxmass
      _ ≤ 4 * b * (W / H + 1) := htotal
      _ = 4 * (b * (W / H + 1)) := by ring
      _ ≤ 40 * (b * (W / H + 1)) :=
        Nat.mul_le_mul_right (b * (W / H + 1)) (by omega)
      _ = 40 * b * (W / H + 1) := by ring

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceAP.lean` -/

/-! The existing depth-48 growth theorem applied to balanced occurrence leaves. -/

namespace Jsp285

open Erdos344

/-- Balanced disjoint occurrence leaves yield an AP at the original target length. -/
theorem containsAP_of_balanced_occurrence_tree {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (S : Finset ι) (N n : ℕ) (hn : 0 < n)
    (hbox : ∀ i ∈ S, 0 < v i ∧ v i ≤ N)
    (hmass : 39999 * partitionMass * n ≤ ∑ i ∈ S, v i)
    (T : PartitionTree ι 49) (hcarrier : T.carrier = S)
    (hdisj : T.PairwiseDisjoint)
    (hleaf : T.AllLeaves fun C ↦ C ⊆ S ∧
      (∀ e : ℕ, 1 < e → e ≤ N → e - 1 ≤ (C.filter fun i ↦ ¬e ∣ v i).card) ∧
      89 ^ 49 * (∑ i ∈ S, v i) ≤ 2 * partitionMass * (∑ i ∈ C, v i) ∧
      partitionMass * (∑ i ∈ C, v i) ≤ 2 * 111 ^ 49 * (∑ i ∈ S, v i)) :
    ContainsFiniteAP (occurrenceSums v S : Set ℕ) n := by
  let W := ∑ i ∈ S, v i
  let q := W / partitionMass
  let K := 89 ^ 49 * (q / 16)
  let box := 40 * 111 ^ 49 * (q + 1)
  have hH : 0 < partitionMass := by norm_num [partitionMass]
  have hq : 39999 * n ≤ q := by
    apply (Nat.le_div_iff_mul_le hH).mpr
    simpa [W, mul_assoc, mul_comm, mul_left_comm] using hmass
  have hq32 : 32 ≤ q := by omega
  have hquot : 2 * n ≤ q / 16 := by omega
  have ha : 1 ≤ 89 ^ 49 := one_le_pow₀ (by omega)
  have hKlarge : 2 * n ≤ K := hquot.trans (Nat.le_mul_of_pos_left _ ha)
  have hK : 2 ≤ K := by omega
  cases T with
  | node A B =>
    have hA := hleaf.1.and (PartitionTree.allLeaves_subset_carrier A)
    have hB := hleaf.2.and (PartitionTree.allLeaves_subset_carrier B)
    have hpaired : (PartitionTree.zipUnion A B).AllLeaves fun C ↦
        K ≤ (occurrenceSums v C).card ∧
          occurrenceSums v C ⊆ Finset.Icc 0 box := by
      apply allLeaves_zipUnion_of_separate A B hA hB
      intro C P hC hP
      have hCP : Disjoint C P := hdisj.2.2.mono hC.2 hP.2
      have hpairmass : partitionMass * ((∑ i ∈ C, v i) + ∑ i ∈ P, v i) ≤
          4 * 111 ^ 49 * W := by
        have hCmass := hC.1.2.2.2
        have hPmass := hP.1.2.2.2
        dsimp [W]
        nlinarith
      exact pair_leaf_bounds v C P N W partitionMass (89 ^ 49) (111 ^ 49)
        hH hCP (fun i hi ↦ hbox i (hP.1.1 hi)) hC.1.2.1
        hP.1.2.2.1 hpairmass
    have hzipdisj := PartitionTree.pairwiseDisjoint_zipUnion
      hdisj.1 hdisj.2.1 hdisj.2.2
    have hAP := containsFiniteAP_of_occurrence_tree v (PartitionTree.zipUnion A B)
      hK hzipdisj (hpaired.mono fun C h ↦ h.1) (hpaired.mono fun C h ↦ h.2)
      (depth_fortyEight_growth hq32)
    have hzipcarrier : (PartitionTree.zipUnion A B).carrier = S := by
      rw [PartitionTree.carrier_zipUnion]
      exact hcarrier
    rw [hzipcarrier] at hAP
    obtain ⟨a, d, hd, hterms⟩ := hAP
    refine ⟨a, d, hd, ?_⟩
    intro i hi
    exact hterms i (by omega)

end Jsp285

/-! ### Upstream module `Jsp285/FiniteMultiset.lean` -/

/-! The finite multiset theorem, with every occurrence bridge discharged. -/

namespace Jsp285

/-- Linearly many occurrences in `[1,n]` have an `n`-term AP among their subset sums. -/
theorem finite_multiset_AP {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (v : ι → ℕ) (I : Finset ι)
    (hbox : ∀ i ∈ I, 0 < v i ∧ v i ≤ n)
    (hcount : finiteCoefficient * n ≤ I.card) :
    Erdos344.ContainsFiniteAP (occurrenceSums v I : Set ℕ) n := by
  obtain ⟨d, S, w, hd, hdn, hSI, hscale, hnorm, hSlarge, hdiv, hbin⟩ :=
    exists_prepared_occurrences n hn v I hbox hcount
  obtain ⟨T, hcarrier, hdisj, hleaf⟩ :=
    exists_balanced_occurrence_partition n d hn hd hdn w S hnorm hSlarge hdiv hbin
  have hmass : 39999 * partitionMass * n ≤ ∑ i ∈ S, w i := by
    apply hSlarge.trans
    calc
      S.card = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, w i := Finset.sum_le_sum fun i hi ↦ (hnorm i hi).1
  obtain ⟨a, e, he, hterms⟩ := containsAP_of_balanced_occurrence_tree
    w S (n / d) n hn hnorm hmass T hcarrier hdisj hleaf
  refine ⟨d * a, d * e, Nat.mul_pos hd he, ?_⟩
  intro j hj
  have hscaled := scale_mem_occurrenceSums hSI hscale (hterms j hj)
  change d * a + j * (d * e) ∈ occurrenceSums v I
  convert hscaled using 1
  ring

end Jsp285

/-! ### Upstream module `Jsp285/InfiniteConstants.lean` -/

/-! Absolute counting coefficient for the occurrence-indexed infinite extension. -/

namespace Jsp285

/-- Slack in the selected sequences makes the finite AP steps small. -/
def infiniteScale : ℕ := 64 * finiteCoefficient ^ 2

/-- The original eventual counting hypothesis will use this absolute coefficient. -/
def infiniteCoefficient : ℕ := 8 * infiniteScale

/-- The finite coefficient is positive. -/
lemma finiteCoefficient_pos : 0 < finiteCoefficient := by
  norm_num [finiteCoefficient, partitionMass]

/-- The selected-sequence scale is positive. -/
lemma infiniteScale_pos : 0 < infiniteScale := by
  unfold infiniteScale
  have := finiteCoefficient_pos
  positivity

/-- The scale is large enough to keep every selected block within its AP target box. -/
lemma two_mul_finiteCoefficient_le_infiniteScale :
    2 * finiteCoefficient ≤ infiniteScale := by
  have := finiteCoefficient_pos
  unfold infiniteScale
  nlinarith [Nat.le_mul_self finiteCoefficient]

/-- At least a factor of two is available for the reservoir growth argument. -/
lemma two_le_infiniteScale : 2 ≤ infiniteScale := by
  have := finiteCoefficient_pos
  have := two_mul_finiteCoefficient_le_infiniteScale
  omega

/-- The final counting coefficient is strictly positive. -/
lemma infiniteCoefficient_pos : 0 < infiniteCoefficient := by
  unfold infiniteCoefficient
  exact Nat.mul_pos (by omega) infiniteScale_pos

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceBlocks.lean` -/

/-! Long occurrence blocks contain arithmetic progressions with small steps. -/

namespace Jsp285

/-- A linearly bounded positive occurrence sequence supplies an `L`-term AP
whose step is at most `L / 16` in the standard geometric index block. -/
theorem exists_small_step_block_AP
    (b : ℕ → ℕ) (hpos : ∀ j : ℕ, 0 < b j) (I₀ L : ℕ) (hL : 2 ≤ L)
    (hstart : I₀ ≤ finiteCoefficient * L)
    (hbound : ∀ j : ℕ, I₀ ≤ j → b j ≤ j / infiniteScale) :
    ∃ a d : ℕ, 0 < d ∧ 16 * d ≤ L ∧
      ∀ k < L, a + k * d ∈ occurrenceSums b
        (Finset.Ico (finiteCoefficient * L) (2 * finiteCoefficient * L)) := by
  let B := Finset.Ico (finiteCoefficient * L) (2 * finiteCoefficient * L)
  have hbox : ∀ j ∈ B, 0 < b j ∧ b j ≤ L := by
    intro j hj
    have hjIco := Finset.mem_Ico.mp hj
    have hjstart : I₀ ≤ j := hstart.trans hjIco.1
    have hscale : 2 * finiteCoefficient * L ≤ infiniteScale * L := by
      exact Nat.mul_le_mul_right L two_mul_finiteCoefficient_le_infiniteScale
    have hjscale : j ≤ infiniteScale * L := hjIco.2.le.trans hscale
    exact ⟨hpos j, (hbound j hjstart).trans (Nat.div_le_of_le_mul hjscale)⟩
  have hBcardEq : B.card = finiteCoefficient * L := by
    dsimp only [B]
    rw [Nat.card_Ico]
    have hrewrite : 2 * finiteCoefficient * L =
        2 * (finiteCoefficient * L) := by ring
    rw [hrewrite]
    omega
  have hBcard : finiteCoefficient * L ≤ B.card := hBcardEq.ge
  obtain ⟨a, d, hd, hterms⟩ :=
    finite_multiset_AP L (by omega) b B hbox hBcard
  let T := ∑ j ∈ B, b j
  have hDT : infiniteScale * T ≤
      2 * finiteCoefficient ^ 2 * L ^ 2 := by
    calc
      infiniteScale * T = ∑ j ∈ B, infiniteScale * b j := by
        simp only [T, Finset.mul_sum]
      _ ≤ ∑ _j ∈ B, 2 * finiteCoefficient * L := by
        apply Finset.sum_le_sum
        intro j hj
        have hjIco := Finset.mem_Ico.mp hj
        have hjstart : I₀ ≤ j := hstart.trans hjIco.1
        calc
          infiniteScale * b j ≤ infiniteScale * (j / infiniteScale) :=
            Nat.mul_le_mul_left infiniteScale (hbound j hjstart)
          _ ≤ j := Nat.mul_div_le j infiniteScale
          _ ≤ 2 * finiteCoefficient * L := hjIco.2.le
      _ = B.card * (2 * finiteCoefficient * L) := by simp
      _ = 2 * finiteCoefficient ^ 2 * L ^ 2 := by
        rw [hBcardEq]
        ring
  have hlastMem := hterms (L - 1) (by omega)
  have hlastMass := occurrenceSum_le_mass hlastMem
  have hlast : (L - 1) * d ≤ T := by
    change a + (L - 1) * d ≤ T at hlastMass
    omega
  have hLtwice : L ≤ 2 * (L - 1) := by omega
  have hfirst : L * (infiniteScale * d) ≤
      2 * infiniteScale * ((L - 1) * d) := by
    have h := Nat.mul_le_mul_right (infiniteScale * d) hLtwice
    nlinarith
  have hlastScaled : 2 * infiniteScale * ((L - 1) * d) ≤
      2 * infiniteScale * T :=
    Nat.mul_le_mul_left (2 * infiniteScale) hlast
  have hDTscaled : 2 * infiniteScale * T ≤
      4 * finiteCoefficient ^ 2 * L ^ 2 := by
    have h := Nat.mul_le_mul_left 2 hDT
    nlinarith
  have hcancelL : infiniteScale * d ≤
      4 * finiteCoefficient ^ 2 * L := by
    apply Nat.le_of_mul_le_mul_left (c := L) (hc := by omega)
    calc
      L * (infiniteScale * d) ≤ 2 * infiniteScale * ((L - 1) * d) := hfirst
      _ ≤ 2 * infiniteScale * T := hlastScaled
      _ ≤ 4 * finiteCoefficient ^ 2 * L ^ 2 := hDTscaled
      _ = L * (4 * finiteCoefficient ^ 2 * L) := by ring
  have hfactor : 0 < 4 * finiteCoefficient ^ 2 := by
    have := finiteCoefficient_pos
    positivity
  have hstep : 16 * d ≤ L := by
    refine Nat.le_of_mul_le_mul_left ?_ hfactor
    calc
      (4 * finiteCoefficient ^ 2) * (16 * d) = infiniteScale * d := by
          simp only [infiniteScale]
          ring
      _ ≤ 4 * finiteCoefficient ^ 2 * L := hcancelL
  exact ⟨a, d, hd, hstep, hterms⟩

end Jsp285

/-! ### Upstream module `Jsp285/LinearFixedStep.lean` -/

namespace Jsp285

/-- A positive occurrence sequence with an eventual linear bound has
arbitrarily long subset-sum progressions with one fixed positive step. -/
theorem fixedStep_of_linear_bound
    (b : ℕ → ℕ) (hpos : ∀ i : ℕ, 0 < b i)
    (hbound : ∃ I₀ : ℕ, ∀ i : ℕ, I₀ ≤ i → b i ≤ i / infiniteScale) :
    Erdos344.HasFixedStepProgressions (indexedSubsetSums b Set.univ) := by
  obtain ⟨I₀, hbound⟩ := hbound
  let L := max 2 I₀
  let B : ℕ → Finset ℕ := fun i ↦
    Finset.Ico (finiteCoefficient * blockLength L i)
      (2 * finiteCoefficient * blockLength L i)
  have hL : 2 ≤ L := Nat.le_max_left _ _
  have hI₀L : I₀ ≤ L := Nat.le_max_right _ _
  have hlengthMono : ∀ {i j : ℕ}, i ≤ j →
      blockLength L i ≤ blockLength L j := by
    intro i j hij
    exact Nat.mul_le_mul_right L (Nat.pow_le_pow_right (by omega) hij)
  have hnext (i : ℕ) : blockLength L (i + 1) = 2 * blockLength L i := by
    simp [blockLength, pow_succ]
    ring
  have hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxi' := Finset.mem_Ico.mp hxi
    have hxj' := Finset.mem_Ico.mp hxj
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hsep : 2 * finiteCoefficient * blockLength L i ≤
          finiteCoefficient * blockLength L j := by
        calc
          2 * finiteCoefficient * blockLength L i =
              finiteCoefficient * blockLength L (i + 1) := by rw [hnext]; ring
          _ ≤ finiteCoefficient * blockLength L j :=
            Nat.mul_le_mul_left finiteCoefficient (hlengthMono (by omega))
      omega
    · have hsep : 2 * finiteCoefficient * blockLength L j ≤
          finiteCoefficient * blockLength L i := by
        calc
          2 * finiteCoefficient * blockLength L j =
              finiteCoefficient * blockLength L (j + 1) := by rw [hnext]; ring
          _ ≤ finiteCoefficient * blockLength L i :=
            Nat.mul_le_mul_left finiteCoefficient (hlengthMono (by omega))
      omega
  have hAP : ∀ i, ∃ a d : ℕ, 0 < d ∧
      16 * d ≤ blockLength L i ∧
      ∀ j < blockLength L i, a + j * d ∈ occurrenceSums b (B i) := by
    intro i
    have hLLi : L ≤ blockLength L i := by
      simpa [blockLength] using hlengthMono (i := 0) (j := i) (Nat.zero_le i)
    have hstart : I₀ ≤ finiteCoefficient * blockLength L i := by
      apply hI₀L.trans <| hLLi.trans ?_
      exact Nat.le_mul_of_pos_left _ finiteCoefficient_pos
    simpa only [B] using exists_small_step_block_AP b hpos I₀
      (blockLength L i) (hL.trans hLLi) hstart hbound
  obtain ⟨D, hD, hmerged⟩ :=
    exists_merged_occurrence_blocks b B L hL hdisj hAP
  exact fixedStep_of_merged_occurrence_blocks b B L D hL hD hmerged

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceNet.lean` -/

/-! Graham's additive-net construction for arbitrary occurrence sequences. -/

namespace Jsp285

/-- Sum of the occurrences strictly before index `n`. -/
def occurrencePrefixSum (y : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, y i

/-- The occurrence-indexed form of the prefix approximation lemma used in
Graham's additive-net construction in `Erdos344`. -/
private lemma exists_prefix_occurrenceSum_near (y : ℕ → ℕ) (m₀ : ℕ)
    (hgrowth : ∀ m, m₀ ≤ m → y m ≤ occurrencePrefixSum y m) :
    ∀ n, m₀ ≤ n → ∀ x ≤ occurrencePrefixSum y n,
      ∃ F : Finset ℕ, F ⊆ Finset.range n ∧
        (∑ i ∈ F, y i) ≤ x ∧
          x ≤ (∑ i ∈ F, y i) + occurrencePrefixSum y m₀ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro x hx
      exact ⟨∅, by simp, by simp, by simpa using hx⟩
  | succ n hn ih =>
      intro x hx
      by_cases hsmall : x ≤ occurrencePrefixSum y n
      · obtain ⟨F, hF, hFlo, hFhi⟩ := ih x hsmall
        exact ⟨F, hF.trans (by simp), hFlo, hFhi⟩
      · have hyn : y n ≤ occurrencePrefixSum y n := hgrowth n hn
        have hyx : y n ≤ x := hyn.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
        have hsub : x - y n ≤ occurrencePrefixSum y n := by
          rw [occurrencePrefixSum, Finset.sum_range_succ,
            ← occurrencePrefixSum] at hx
          omega
        obtain ⟨F, hF, hFlo, hFhi⟩ := ih (x - y n) hsub
        have hnF : n ∉ F := fun h => by
          have := hF h
          simp at this
        refine ⟨insert n F, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · exact Finset.mem_range.mpr
              ((Finset.mem_range.mp (hF hi)).trans (Nat.lt_succ_self n))
        · rw [Finset.sum_insert hnF]
          omega
        · rw [Finset.sum_insert hnF]
          omega

/-- A positive occurrence sequence in one residue subgroup, satisfying
Graham's eventual prefix-growth condition, has an additive net of indexed
subset sums.  Repeated values remain distinct occurrences. -/
theorem exists_addNet_indexedSubsetSums {q : ℕ} (hq : 0 < q)
    (y : ℕ → ℕ) (hypos : ∀ i, 0 < y i) (hyq : ∀ i, q ∣ y i)
    (hgrowth : ∃ m₀, ∀ m, m₀ ≤ m → y m ≤ occurrencePrefixSum y m) :
    ∃ K, Erdos344.IsAddNet q K (indexedSubsetSums y Set.univ) := by
  obtain ⟨m₀, hgrowth⟩ := hgrowth
  let K := occurrencePrefixSum y m₀
  refine ⟨K, hq, ?_⟩
  intro n
  let x := (n + K) * q
  let N := max m₀ x
  have hmN : m₀ ≤ N := le_max_left _ _
  have hxN : x ≤ N := le_max_right _ _
  have hid : N ≤ occurrencePrefixSum y N := by
    calc
      N = ∑ _i ∈ Finset.range N, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range N, y i := by
        exact Finset.sum_le_sum fun i _ => hypos i
      _ = occurrencePrefixSum y N := rfl
  have hxsum : x ≤ occurrencePrefixSum y N := hxN.trans hid
  obtain ⟨F, hFN, hFlo, hFhi⟩ :=
    exists_prefix_occurrenceSum_near y m₀ hgrowth N hmN x hxsum
  let s := ∑ i ∈ F, y i
  have hmem : s ∈ indexedSubsetSums y Set.univ := by
    exact ⟨F, Set.subset_univ _, rfl⟩
  have hdiv : q ∣ s := by
    exact Finset.dvd_sum fun i _ => hyq i
  have hKq : K ≤ K * q := by
    have : 1 ≤ q := hq
    nlinarith
  refine ⟨s, hmem, hdiv, ?_, ?_⟩
  · have hFhi' : x ≤ s + K * q := by
      exact hFhi.trans (Nat.add_le_add_left (by simpa [K] using hKq) _)
    dsimp [x] at hFhi'
    rw [Nat.add_mul] at hFhi'
    exact Nat.le_of_add_le_add_right hFhi'
  · exact hFlo

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceResidues.lean` -/

/-! Residue stabilization with finite supports in occurrence indices. -/

namespace Jsp285

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

private noncomputable def occurrenceResidues (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter fun z =>
    ∃ I : Finset ℕ, (∑ i ∈ I, (y i : ZMod d)) = z

private lemma mem_occurrenceResidues_iff {y : ℕ → ℕ} {d : ℕ} [NeZero d]
    {z : ZMod d} :
    z ∈ occurrenceResidues y d ↔
      ∃ I : Finset ℕ, (∑ i ∈ I, (y i : ZMod d)) = z := by
  simp [occurrenceResidues]

private noncomputable def occurrenceResidueWitness (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) : Finset ℕ :=
  Classical.choose (mem_occurrenceResidues_iff.mp z.property)

private lemma occurrenceResidueWitness_spec (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) :
    (∑ i ∈ occurrenceResidueWitness y d z, (y i : ZMod d)) = z :=
  Classical.choose_spec (mem_occurrenceResidues_iff.mp z.property)

private noncomputable def occurrenceResidueSupport (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] : Finset ℕ :=
  (occurrenceResidues y d).attach.biUnion (occurrenceResidueWitness y d)

private lemma witness_subset_occurrenceResidueSupport (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) :
    occurrenceResidueWitness y d z ⊆ occurrenceResidueSupport y d := by
  intro i hi
  rw [occurrenceResidueSupport, Finset.mem_biUnion]
  exact ⟨z, Finset.mem_attach _ _, hi⟩

/-- Modulo a positive `d`, all sufficiently late occurrence weights are
divisible by some `q ∣ d`, while the initial occurrences represent every
multiple of `q` modulo `d`. -/
theorem exists_occurrence_residue_stabilization (y : ℕ → ℕ)
    {d : ℕ} (hd : 0 < d) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧ ∃ s : ℕ,
      (∀ j, s ≤ j → q ∣ y j) ∧
      (∀ i < d / q, ∃ u ∈ occurrenceSums y (Finset.range s),
        (u : ZMod d) = (i * q : ZMod d)) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let R := occurrenceResidues y d
  let K := AddAction.stabilizer (ZMod d) R
  obtain ⟨q, hqpos, hqd, hKdiv, hmultK⟩ :=
    Erdos344.exists_generator_modulus hd K
  let s := (occurrenceResidueSupport y d).sup id + 1
  refine ⟨q, hqpos, hqd, s, ?_, ?_⟩
  · intro j hj
    have hjlarge : (occurrenceResidueSupport y d).sup id < j := by
      simpa [s] using hj
    have hjK : (y j : ZMod d) ∈ K := by
      rw [AddAction.mem_stabilizer_finset']
      intro z hz
      let z' : occurrenceResidues y d := ⟨z, hz⟩
      let I := occurrenceResidueWitness y d z'
      have hjI : j ∉ I := by
        intro hjI
        have hjsupp : j ∈ occurrenceResidueSupport y d :=
          witness_subset_occurrenceResidueSupport y d z' hjI
        have hjle := Finset.le_sup (f := id) hjsupp
        exact (not_le_of_gt hjlarge) (by simpa using hjle)
      rw [mem_occurrenceResidues_iff]
      refine ⟨insert j I, ?_⟩
      rw [Finset.sum_insert hjI]
      change (y j : ZMod d) + (∑ i ∈ I, (y i : ZMod d)) = _
      rw [occurrenceResidueWitness_spec y d z']
      rfl
    have hqmod : q ∣ (y j : ZMod d).val := hKdiv _ hjK
    have hqrem : q ∣ y j % d := by
      simpa [ZMod.val_natCast] using hqmod
    have hqdpart : q ∣ d * (y j / d) := dvd_mul_of_dvd_left hqd _
    rw [← Nat.mod_add_div (y j) d]
    exact dvd_add hqrem hqdpart
  · intro i hi
    have hiK : (i * q : ZMod d) ∈ K := hmultK i
    have hzero : (0 : ZMod d) ∈ R := by
      rw [mem_occurrenceResidues_iff]
      exact ⟨∅, by simp⟩
    have hiR : (i * q : ZMod d) ∈ R := by
      have := (AddAction.mem_stabilizer_finset'.mp hiK) hzero
      simpa using this
    let z : occurrenceResidues y d := ⟨(i * q : ZMod d), hiR⟩
    let I := occurrenceResidueWitness y d z
    have hIrange : I ⊆ Finset.range s := by
      intro j hjI
      have hjsupp : j ∈ occurrenceResidueSupport y d :=
        witness_subset_occurrenceResidueSupport y d z hjI
      have hjle := Finset.le_sup (f := id) hjsupp
      rw [Finset.mem_range]
      simpa [s] using Nat.lt_succ_of_le (by simpa using hjle)
    refine ⟨∑ j ∈ I, y j, ?_, ?_⟩
    · exact mem_occurrenceSums.mpr ⟨I, hIrange, rfl⟩
    · simpa [I, z] using occurrenceResidueWitness_spec y d z

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceTransport.lean` -/

/-! Transport subset-sum witnesses through injective maps of occurrence indices. -/

namespace Jsp285

open scoped BigOperators Pointwise

/-- An injective map of occurrence indices transports every finite indexed
subset sum to the image support. -/
lemma indexedSubsetSums_comp_subset_image
    {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (v : κ → ℕ) (S : Set ι) :
    indexedSubsetSums (v ∘ f) S ⊆ indexedSubsetSums v (f '' S) := by
  classical
  rintro x ⟨I, hI, rfl⟩
  refine ⟨I.image f, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i, hI hi, rfl⟩
  · rw [Finset.sum_image hf.injOn]
    rfl

/-- Sums of a shifted occurrence sequence use only indices in its tail. -/
lemma indexedSubsetSums_tail_subset (r : ℕ → ℕ) (s : ℕ) :
    indexedSubsetSums (fun i => r (s + i)) Set.univ ⊆
      indexedSubsetSums r (Set.Ici s) := by
  let f : ℕ → ℕ := fun i => s + i
  have hf : Function.Injective f := fun _ _ h => Nat.add_left_cancel h
  have htransport := indexedSubsetSums_comp_subset_image f hf r Set.univ
  apply htransport.trans
  apply indexedSubsetSums_mono r
  rintro _ ⟨i, -, rfl⟩
  exact Nat.le_add_right s i

/-- Finite prefix occurrence sums are finite indexed sums supported below the
prefix endpoint. -/
lemma occurrenceSums_range_subset_indexedSubsetSums_Iio
    (r : ℕ → ℕ) (s : ℕ) :
    (occurrenceSums r (Finset.range s) : Set ℕ) ⊆
      indexedSubsetSums r (Set.Iio s) := by
  rw [← indexedSubsetSums_finset]
  apply indexedSubsetSums_mono r
  intro i hi
  exact Finset.mem_range.mp hi

/-- Sums transported from two disjoint injective index streams combine into
an indexed subset sum of the original occurrence sequence. -/
lemma add_indexedSubsetSums_comp_subset
    (A : ℕ → ℕ) (β ρ : ℕ → ℕ)
    (hβ : Function.Injective β) (hρ : Function.Injective ρ)
    (hdisj : Disjoint (Set.range β) (Set.range ρ)) :
    indexedSubsetSums (A ∘ β) Set.univ +
        indexedSubsetSums (A ∘ ρ) Set.univ ⊆
      indexedSubsetSums A Set.univ := by
  rintro x ⟨b, hb, r, hr, rfl⟩
  have hb' : b ∈ indexedSubsetSums A (Set.range β) := by
    simpa only [Set.image_univ] using
      indexedSubsetSums_comp_subset_image β hβ A Set.univ hb
  have hr' : r ∈ indexedSubsetSums A (Set.range ρ) := by
    simpa only [Set.image_univ] using
      indexedSubsetSums_comp_subset_image ρ hρ A Set.univ hr
  exact indexedSubsetSums_mono A (Set.union_subset (Set.subset_univ _)
    (Set.subset_univ _)) (add_mem_indexedSubsetSums A hdisj hb' hr')

end Jsp285

/-! ### Upstream module `Jsp285/OccurrenceEndgame.lean` -/

namespace Jsp285

open scoped BigOperators Pointwise

/-- Occurrence-indexed form of the Szemerédi--Vu endgame: a fixed-step source
and a positive, eventually linearly bounded residue source combine to contain
an infinite arithmetic progression. -/
theorem fixedStep_and_occurrence_residue_part
    (b r : ℕ → ℕ) (hrpos : ∀ i, 0 < r i) (D : ℕ) (hD : 2 ≤ D)
    (hrbound : ∃ I₀, ∀ i, I₀ ≤ i → r i ≤ i / D)
    (hfixed : Erdos344.HasFixedStepProgressions
      (indexedSubsetSums b Set.univ)) :
    Erdos344.ContainsInfiniteAP
      (indexedSubsetSums b Set.univ + indexedSubsetSums r Set.univ) := by
  obtain ⟨d, hd, hlong⟩ := hfixed
  obtain ⟨q, hqpos, hqd, s, htailq, hresmod⟩ :=
    exists_occurrence_residue_stabilization r hd
  let y : ℕ → ℕ := fun j => r (s + j)
  have hypos : ∀ j, 0 < y j := fun j => hrpos (s + j)
  have hyq : ∀ j, q ∣ y j := by
    intro j
    exact htailq (s + j) (Nat.le_add_right s j)
  obtain ⟨I₀, hI₀⟩ := hrbound
  have hygrowth : ∃ m₀, ∀ j, m₀ ≤ j → y j ≤ occurrencePrefixSum y j := by
    refine ⟨max I₀ s, ?_⟩
    intro j hj
    have hI₀j : I₀ ≤ s + j :=
      (le_max_left I₀ s).trans hj |>.trans (Nat.le_add_left j s)
    have hsj : s ≤ j := (le_max_right I₀ s).trans hj
    have hsumle : s + j ≤ D * j := by
      calc
        s + j ≤ j + j := Nat.add_le_add_right hsj j
        _ = 2 * j := by omega
        _ ≤ D * j := Nat.mul_le_mul_right j hD
    have hyj : y j ≤ j :=
      (hI₀ (s + j) hI₀j).trans (Nat.div_le_of_le_mul hsumle)
    calc
      y j ≤ j := hyj
      _ = ∑ _i ∈ Finset.range j, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range j, y i := by
        exact Finset.sum_le_sum fun i _ => hypos i
      _ = occurrencePrefixSum y j := rfl
  obtain ⟨K, hnet⟩ :=
    exists_addNet_indexedSubsetSums hqpos y hypos hyq hygrowth
  let M := d / q
  have hqle : q ≤ d := Nat.le_of_dvd hd hqd
  have hMpos : 0 < M := Nat.div_pos hqle hqpos
  have hdEq : q * M = d := Nat.mul_div_cancel' hqd
  let P := occurrenceSums r (Finset.range s)
  let Z := ∑ i ∈ Finset.range s, r i
  let L := Z + (K + 1)
  obtain ⟨a, ha⟩ := hlong L
  have hAP : ∀ j < L,
      a + j * (q * M) ∈ indexedSubsetSums b Set.univ := by
    simpa [hdEq] using ha
  have hres : ∀ i < M, ∃ u ∈ (P : Set ℕ),
      ∃ z ≤ Z, u = i * q + (q * M) * z := by
    intro i hi
    obtain ⟨u, huP, hucong⟩ := hresmod i (by simpa [M] using hi)
    have hiqd : i * q < d := by
      rw [← hdEq]
      nlinarith
    have hucong' : (u : ZMod d) = (i * q : ℕ) := by
      simpa only [Nat.cast_mul] using hucong
    obtain ⟨z, huz⟩ :=
      Erdos344.exists_eq_add_mul_of_zmod_eq hd hiqd hucong'
    have hz : z ≤ Z := by
      have hzu : z ≤ u := by
        have hdz : z ≤ d * z := Nat.le_mul_of_pos_left z hd
        omega
      exact hzu.trans (occurrenceSum_le_mass huP)
    exact ⟨u, huP, z, hz, by simpa [hdEq, mul_comm] using huz⟩
  have hlength : K + 1 ≤ M * (L - Z) := by
    have : L - Z = K + 1 := by simp [L]
    rw [this]
    nlinarith
  have hlowered : ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈
        indexedSubsetSums b Set.univ + (P : Set ℕ) :=
    Erdos344.lowerStep_of_residue_translates_mem hqpos hMpos hAP hres
  have hfinite : ∀ n < K + 1,
      (a + (q * M) * Z) + n * q ∈
        indexedSubsetSums b Set.univ + (P : Set ℕ) :=
    fun n hn => hlowered n (hn.trans_le hlength)
  have hinf := Erdos344.addNet_add_finiteAP hnet hfinite
  apply Erdos344.containsInfiniteAP_mono ?_ hinf
  rintro x ⟨bp, hbp, t, ht, rfl⟩
  obtain ⟨bv, hb, p, hp, rfl⟩ := hbp
  have hp' : p ∈ indexedSubsetSums r (Set.Iio s) :=
    occurrenceSums_range_subset_indexedSubsetSums_Iio r s hp
  have ht' : t ∈ indexedSubsetSums r (Set.Ici s) := by
    exact indexedSubsetSums_tail_subset r s ht
  have hpt : p + t ∈ indexedSubsetSums r Set.univ := by
    have hdisj : Disjoint (Set.Iio s) (Set.Ici s) :=
      Set.Iio_disjoint_Ici le_rfl
    have hadd := add_mem_indexedSubsetSums r hdisj hp' ht'
    simpa only [Set.Iio_union_Ici] using hadd
  exact ⟨bv, hb, p + t, hpt, by ring⟩

end Jsp285

/-! ### Upstream module `Jsp285/Main.lean` -/

/-! The full eventual-density theorem for arbitrary occurrence-indexed multisets. -/

namespace Jsp285

/-- The auxiliary indexed-sum model is exactly the literal frozen object on all indices. -/
lemma indexedSubsetSums_univ_eq (A : ℕ → ℕ) :
    indexedSubsetSums A Set.univ = Erdos343.SubsetSums A := by
  ext x
  simp [indexedSubsetSums, Erdos343.SubsetSums]

/-- The proved finite theorem closes every input needed by the infinite extension. -/
theorem subcomplete_of_eventual_count (A : ℕ → ℕ) (hpos : ∀ i, 0 < A i)
    (hcount : Erdos343.HasEventualLinearCountingLowerBound infiniteCoefficient A) :
    Erdos343.IsSubcomplete A := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcount
  let N₁ := max N₀ 1
  have hcount' : ∀ N, N₁ ≤ N → ∃ s : Finset ℕ,
      8 * infiniteScale * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N := by
    intro N hN
    exact hN₀ N ((le_max_left _ _).trans hN)
  obtain ⟨β, ρ, hβ, hρ, hdisj, I₀, hbound⟩ :=
    exists_two_linear_selections A infiniteScale N₁ infiniteScale_pos
      (le_max_right _ _) hcount'
  have hfixed := fixedStep_of_linear_bound (A ∘ β) (fun i ↦ hpos (β i))
    ⟨I₀, fun i hi ↦ (hbound i hi).1⟩
  have hAP := fixedStep_and_occurrence_residue_part (A ∘ β) (A ∘ ρ)
    (fun i ↦ hpos (ρ i)) infiniteScale two_le_infiniteScale
    ⟨I₀, fun i hi ↦ (hbound i hi).2⟩ hfixed
  have hfull := Erdos344.containsInfiniteAP_mono
    (add_indexedSubsetSums_comp_subset A β ρ hβ hρ hdisj) hAP
  rw [indexedSubsetSums_univ_eq] at hfull
  exact hfull

end Jsp285

/-! ### Upstream module `Jsp285/Statement.lean` -/

/-- **Target (Szemerédi–Vu, Folkman's conjecture).**  Some absolute constant
`C` works for every multiset of positive integers whose counting function is
eventually at least `C * N`.  No monotonicity of the occurrence indexing is
assumed. -/
theorem erdos_343 :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      (∀ i, 0 < A i) →
      HasEventualLinearCountingLowerBound C A →
      IsSubcomplete A := by
  exact ⟨Jsp285.infiniteCoefficient, Jsp285.infiniteCoefficient_pos,
    Jsp285.subcomplete_of_eventual_count⟩

#print axioms erdos_343
-- 'Erdos343.erdos_343' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos343
