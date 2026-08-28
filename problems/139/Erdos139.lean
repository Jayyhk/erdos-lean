import Mathlib

namespace Erdos139

/-
# Problem Description

Erdős Problem 139 (Szemerédi's theorem). Let `r_k(N)` be the size of the largest subset of
`{1, …, N}` containing no non-trivial `k`-term arithmetic progression. Prove that
`r_k(N) = o(N)`. `erdos_139` proves this. Erdős offered $1000 for it.

A conjecture of Erdős and Turán, proved by Szemerédi [Sz75]; the best known bounds are due to
Kelley and Meka [KeMe23] for `k = 3`, Green and Tao [GrTa17] for `k = 4`, and Leng, Sah and
Sawhney [LSS24] for `k ≥ 5`. Below, `r k N` is `Set.IsAPOfLengthFree.maxCard k N`, the
supremum of `S.card` over `S ⊆ Finset.Icc 1 N` that are `k`-AP-free, and `r_k(N) = o(N)` is
rendered as `r k N / N → 0`.

The proof formalised here is a full development of Szemerédi's theorem via hypergraph
regularity and removal, together with a transference argument; it is the largest single
dependency closure in this repository so far.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos139.lean` together with the ninety modules of
`src/latest/Wikipedia/SzemeredisTheorem/`. Those files are concatenated here in dependency
order, with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, and the whole wrapped
once in `namespace Erdos139` with the upstream trust-base print line removed. No mathematical
content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/FormalConjectures139.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

open scoped BigOperators Topology

variable {α : Type*} [AddCommMonoid α]

/-- A set is an arithmetic progression of length `l`, first term `a`, and
difference `d`. Cardinality is included so repeated terms are not nontrivial. -/
def _root_.Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length `l`. -/
def _root_.Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

section

theorem _root_.Set.IsAPOfLength.card {s : Set α} {l : ℕ∞} (h : s.IsAPOfLength l) : ENat.card s = l :=
  h.choose_spec.choose_spec.1

end

/-- A set is free of nontrivial arithmetic progressions of length `l`. -/
def _root_.Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

section

/-- The largest cardinality of a `k`-AP-free subset of `{1, ..., N}`. -/
noncomputable def _root_.Set.IsAPOfLengthFree.maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}

end

namespace SzemeredisTheorem

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

private def candidateCards (k N : ℕ) : Set ℕ :=
  {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}

private lemma empty_isAPOfLengthFree (k : ℕ) :
    (∅ : Set ℕ).IsAPOfLengthFree k := by
  intro t ht hAP
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht
  subst t
  have hk0 : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  have hk0' : k = 0 := by exact_mod_cast hk0
  subst k
  simp

private lemma candidateCards_nonempty (k N : ℕ) :
    (candidateCards k N).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨∅, by simp, by simpa using empty_isAPOfLengthFree k, rfl⟩

private lemma candidateCards_bddAbove (k N : ℕ) :
    BddAbove (candidateCards k N) := by
  refine ⟨N, ?_⟩
  rintro n ⟨S, hS, -, rfl⟩
  exact (Finset.card_mono hS).trans_eq (by simp)

/-- The supremum in `maxCard` is attained by an AP-free subset. -/
theorem exists_maxCard_witness (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  have hm := Nat.sSup_mem (candidateCards_nonempty k N)
    (candidateCards_bddAbove k N)
  change r k N ∈ candidateCards k N at hm
  rcases hm with ⟨S, hS, hfree, hcard⟩
  exact ⟨S, hS, hfree, hcard⟩

/-- The finitary density form of Szemerédi's theorem. -/
def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → δ * (N : ℝ) ≤ (A.card : ℝ) →
        ¬(A : Set ℕ).IsAPOfLengthFree k

private lemma arithmeticProgressionSet_card
    (a d k : ℕ) (hd : 0 < d) :
    ENat.card {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} = k := by
  let f : ℕ → ℕ := fun i ↦ a + i * d
  have hf : Function.Injective f := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro i
    dsimp [f]
    nlinarith
  have hset : {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} =
      f '' {i : ℕ | i < k} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [hset]
  simp only [ENat.card_coe_set_eq, hf.encard_image, Set.Nat.encard_range]

/-- A positive-difference parameter progression has the exact set/cardinality
form used by the Formal Conjectures specification. -/
theorem arithmeticProgressionSet_isAP
    (a d k : ℕ) (hd : 0 < d) :
    Set.IsAPOfLength
      {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} (k : ℕ∞) := by
  refine ⟨a, d, arithmeticProgressionSet_card a d k hd, ?_⟩
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩

/-- A parameterized positive-step progression witnesses non-freeness. -/
theorem not_isAPOfLengthFree_of_parameters {A : Set ℕ} {k a d : ℕ}
    (hk : 1 < k) (hd : 0 < d)
    (hmem : ∀ i < k, a + i * d ∈ A) :
    ¬A.IsAPOfLengthFree k := by
  intro hfree
  let t : Set ℕ := {x | ∃ i : ℕ, i < k ∧ x = a + i * d}
  have ht : t ⊆ A := by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact hmem i hi
  have hAP : t.IsAPOfLength k := arithmeticProgressionSet_isAP a d k hd
  have hle := hfree t ht hAP
  have hnle : ¬(k : ℕ∞) ≤ 1 := by exact_mod_cast (not_le.mpr hk)
  exact hnle hle

/-- A finitary density theorem implies the Formal Conjectures extremal limit. -/
theorem tendsto_maxCard_div_of_finitarySzemeredi {k : ℕ}
    (hSz : FinitarySzemeredi k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀, hSz⟩ := hSz ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hNpos : 0 < N := hN₀.trans_le hN
  obtain ⟨S, hS, hfree, hcard⟩ := exists_maxCard_witness k N
  have hlt : (S.card : ℝ) < ε * (N : ℝ) := by
    rw [lt_iff_not_ge]
    intro hdense
    exact (hSz N hN S hS hdense) hfree
  have hratio : (r k N : ℝ) / (N : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < N), ← hcard]
    exact hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hratio
  · positivity

end SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Statement.lean` -/

section
/-!
# The Lean Eval statement of Szemerédi's theorem

This module records the definitions used by the Lean theorem-proving
evaluation.  Keeping them in a small module makes the public theorem's type
easy to compare verbatim with the challenge statement.
-/

namespace SzemeredisTheorem

open scoped BigOperators

end SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Finite/Mean.lean` -/

section
/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The normalized average of a real-valued function on a finite type. -/
noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

/-- Real-valued indicator of a finite subset of a finite type. -/
def finsetIndicator {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0

@[simp]
theorem finsetIndicator_of_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp]
theorem finsetIndicator_of_not_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

@[simp]
theorem mean_empty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]

@[simp]
theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  exact Fintype.expect_const c

@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  exact Finset.expect_add_distrib Finset.univ f g

theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  exact Finset.expect_sub_distrib Finset.univ f g

theorem mean_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  rw [mean, mean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

theorem mean_le_of_le_const {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    mean f ≤ c := by
  simpa using mean_mono (f := f) (g := fun _ => c) hf

/-- The normalized average over two independent finite variables. -/
noncomputable def mean₂ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) : ℝ :=
  mean (fun x => mean (f x))

theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Finite/ProductMean.lean` -/

section
/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Finite/CauchySchwarz.lean` -/

section
/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Global Cauchy--Schwarz for a normalized finite mean. -/
theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

/-- The square of a normalized mean is the mean over two independent copies
of the variable. -/
theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

/-- Squaring an inner mean duplicates its variable under the outer mean. -/
theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean` -/

section
/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finite hypergraph bundle over a fixed finite base hypergraph `H`.
The projection is required to be injective on every bundle edge, and every
bundle edge projects to an edge of `H`. -/
structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- A bundle is closed under inclusion when every subedge of every bundle
edge is again a bundle edge. -/
def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

/-- The order of a bundle is the largest cardinality of one of its edges.
The empty bundle has order zero. -/
def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card

/-- Every edge cardinality is bounded by the order of the bundle. -/
theorem edge_card_le_order
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg

/-- Erase one occurrence edge while retaining the same projection. -/
def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

/-- Erasing an edge cannot increase bundle order. -/
theorem eraseEdge_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).order ≤ B.order := by
  unfold order eraseEdge
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order (Finset.mem_of_mem_erase hg)

/-- Erasing a maximum-cardinality edge from a downward-closed bundle
preserves downward closure. -/
theorem eraseEdge_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.eraseEdge g₀).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hfB : f ∈ B.edges :=
    hclosed hgB hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfB⟩
  intro hfg₀
  subst f
  have hcard₂ : g.card ≤ g₀.card :=
    hmax g hgB
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hfg hcard₂
  exact (Finset.mem_erase.mp hg).1 heq.symm

/-! ## Local tuples and pulled-back base weights -/

/-- Restriction of a full bundle assignment to one occurrence edge. -/
def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

/-- Projection gives a bijection from an occurrence edge to its image in
the base vertex set. -/
noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

/-- Transport an occurrence-edge tuple to its projected base edge. -/
noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

/-- A family of local weights indexed by all finite base edges. -/
abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

/-- Pointwise unit-interval bounds on the edges of a base hypergraph. -/
def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

/-- Pull a base edge-weight family back along a bundle projection.  Values
away from the bundle edge family are set to one and are never used in the
bundle product. -/
noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1

@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]

/-- Pullback preserves unit-interval bounds on every bundle edge. -/
theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-! ## Bundle products and normalized counts -/

/-- Unit-interval bounds on an ambient occurrence-edge weight family, on
the edges used by a bundle. -/
def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1

/-- Pulling back a bounded base family gives a bounded bundle family. -/
theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y

/-- Product of all local edge weights on one full bundle assignment. -/
noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

/-- Normalized count of a weighted hypergraph bundle. -/
noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)

theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1

theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)

/-- Unit-interval bounds survive erasing an occurrence edge. -/
theorem WeightsInUnitInterval.eraseEdge
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    (B.eraseEdge g₀).WeightsInUnitInterval A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y

/-- The product left after removing one selected occurrence edge. -/
noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

/-- Contribution obtained by placing a local function at one selected edge
and retaining all other bundle factors. -/
noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)

/-- Factoring a selected edge out of the bundle product. -/
theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm

/-- Exact main/defect/uniform decomposition at one selected edge. -/
theorem bundleCount_decompose_edge
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by
  rw [B.bundleCount_eq_edgeContribution A hg₀]
  unfold edgeContribution bundleCount
  calc
    mean (fun x : K → G =>
        A g₀ (edgeTuple g₀ x) *
          B.edgeRemainder g₀ A x) =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x +
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x +
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      apply congrArg mean
      funext x
      rw [hdecomp]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      rw [mean_add, mean_add]
    _ =
        p * (B.eraseEdge g₀).bundleCount A +
          B.edgeContribution g₀ b A +
          B.edgeContribution g₀ c A := by
      rw [mean_smul]
      rfl

/-- A constant local term contributes that constant times the bundle count
with the selected edge erased. -/
theorem edgeContribution_const
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ (fun _ => p) A =
      p * (B.eraseEdge g₀).bundleCount A := by
  unfold edgeContribution bundleCount
  rw [← mean_smul]
  rfl

/-! ## Freezing the outside variables -/

/-- Coordinates outside a selected occurrence edge. -/
abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

/-- Split the occurrence-vertex set into a selected edge and its
complement. -/
noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

/-- Split a full bundle assignment into its selected-edge and outside
coordinates. -/
noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))

@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

/-- Recombining a selected-edge tuple and an outside tuple recovers the
selected-edge tuple on restriction. -/
@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp

/-- Fubini decomposition into selected-edge and outside assignments. -/
theorem mean_splitEdge
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g} → G =>
        fun z : EdgeComplement g → G =>
          f ((splitEdgeEquiv g).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g} → G) ×
            (EdgeComplement g → G) =>
              f ((splitEdgeEquiv g).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv (splitEdgeEquiv g)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : {v : K // v ∈ g} → G =>
            fun z : EdgeComplement g → G =>
              f ((splitEdgeEquiv g).symm (y, z))))

/-- The remaining bundle product after fixing the selected edge tuple and
the outside tuple. -/
noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

/-- Conditional average of the remaining bundle product after the selected
edge tuple is fixed. -/
noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)

/-- A selected-edge contribution is the pairing of its local function with
the conditional average of all remaining factors. -/
theorem edgeContribution_eq_mean_mul_remainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (fun y =>
        q y * B.edgeRemainderAverage g₀ A y) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀]
  unfold mean₂ edgeRemainderAverage edgeRemainderFiber
  apply congrArg mean
  funext y
  simp only [edgeTuple_splitEdgeEquiv_symm]
  rw [mean_smul]

/-- Inner selected-edge correlation after all outside variables have been
frozen. -/
noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)

/-- The selected-edge contribution is the outside average of the
correlations obtained by freezing the outside variables. -/
theorem edgeContribution_eq_mean_frozenEdgeCorrelation
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (B.frozenEdgeCorrelation g₀ q A) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀, mean₂_comm]
  unfold frozenEdgeCorrelation edgeRemainderFiber mean₂
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (edgeTuple g₀
        ((splitEdgeEquiv g₀).symm (y, z))) *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z)) =
      q y *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z))
  rw [edgeTuple_splitEdgeEquiv_symm]

/-- Uniform control after freezing the outside variables controls the full
uniform contribution. -/
theorem abs_edgeContribution_le_of_frozen
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (hfrozen :
      ∀ z, |B.frozenEdgeCorrelation g₀ q A z| ≤ ε) :
    |B.edgeContribution g₀ q A| ≤ ε := by
  rw [B.edgeContribution_eq_mean_frozenEdgeCorrelation]
  calc
    |mean (B.frozenEdgeCorrelation g₀ q A)| ≤
        mean (fun z =>
          |B.frozenEdgeCorrelation g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : EdgeComplement g₀ → G => ε) :=
      mean_mono hfrozen
    _ = ε := mean_const _

/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

/-- The exact doubled moment created by Cauchy--Schwarz at a selected
edge. -/
noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)

theorem doubledRemainderMoment_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.doubledRemainderMoment g₀ A :=
  mean_nonneg fun _ => sq_nonneg _

/-- The doubled moment is exactly the average obtained by taking two
independent copies of every outside variable. -/
theorem doubledRemainderMoment_eq_mean₂_pair
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean₂ (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          B.edgeRemainderFiber g₀ A y z.1 *
            B.edgeRemainderFiber g₀ A y z.2) := by
  unfold doubledRemainderMoment edgeRemainderAverage
  exact mean_inner_sq_eq_mean₂_pair
    (B.edgeRemainderFiber g₀ A)

/-- Cauchy--Schwarz bounds a selected-edge contribution by the local square
mass of its edge term times the doubled lower-rank remainder moment. -/
theorem edgeContribution_sq_le_localSquare_mul_doubled
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.doubledRemainderMoment g₀ A := by
  rw [B.edgeContribution_eq_mean_mul_remainderAverage]
  exact mean_mul_sq_le_product q
    (B.edgeRemainderAverage g₀ A)

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean` -/

section
/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- Occurrence vertices after identifying `g₀` and doubling its
complement. -/
abbrev DoubledOccurrenceVertex (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × EdgeComplement g₀)

/-- Forget the copy label of a doubled occurrence vertex. -/
def doubledVertexForget
    (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1

/-- Put an old occurrence vertex into one of the two copies, sharing it
when it lies in `g₀`. -/
def doubledVertexLift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    DoubledOccurrenceVertex g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩

@[simp]
theorem doubledVertexForget_lift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    doubledVertexForget g₀
        (doubledVertexLift g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [doubledVertexLift, doubledVertexForget, hv]

/-- A fixed-copy lift is injective. -/
theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h

/-- Assemble one assignment on the shared vertices and two assignments on
the outside vertices into an assignment on the doubled occurrence set. -/
def doubledAssignment
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    DoubledOccurrenceVertex g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v

/-- Splitting an assignment on the doubled occurrence set recovers exactly
one shared assignment and a pair of independent outside assignments. -/
def splitDoubledAssignmentEquiv
    (g₀ : Finset K) :
    (DoubledOccurrenceVertex g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((EdgeComplement g₀ → G) ×
          (EdgeComplement g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := doubledAssignment g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, zfalse, ztrue⟩
    rfl

omit [DecidableEq K] in
@[simp]
theorem splitDoubledAssignmentEquiv_symm_apply
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    (splitDoubledAssignmentEquiv g₀).symm (y, z) =
      doubledAssignment g₀ y z :=
  rfl

/-- Fubini decomposition for the doubled occurrence variables. -/
theorem mean_splitDoubledAssignment
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f ((splitDoubledAssignmentEquiv g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitDoubledAssignmentEquiv g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f (doubledAssignment g₀ p.1 p.2)) =
        _
      exact
        mean_prod_type
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G) =>
              f (doubledAssignment g₀ y z))

/-- On the first copy, a doubled assignment agrees with the ordinary
assignment assembled from the shared tuple and first outside tuple. -/
@[simp]
theorem doubledAssignment_lift_false
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

/-- On the second copy, a doubled assignment agrees with the ordinary
assignment assembled from the shared tuple and second outside tuple. -/
@[simp]
theorem doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

/-- Lift an old occurrence edge into one Boolean copy. -/
def doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (DoubledOccurrenceVertex g₀) :=
  g.image (doubledVertexLift g₀ copy)

theorem mem_doubledEdge
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    doubledVertexLift g₀ copy v ∈
      doubledEdge g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Forgetting a lifted edge recovers the original edge. -/
@[simp]
theorem image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩

/-- Lifting preserves edge cardinality. -/
@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]

/-- An edge wholly contained in the shared edge is unchanged by its copy
label.  This is the precise collision which prevents treating doubled
edges as a multiset-free bundle without an extra hypothesis. -/
theorem doubledEdge_copy_independent_of_subset
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g := by
  unfold doubledEdge
  apply Finset.image_congr
  intro v hv
  simp [doubledVertexLift, hg hv]

/-- A vertex outside `g₀` distinguishes the two Boolean copies of an
edge. -/
theorem doubledEdge_false_ne_true_of_mem_complement
    (g₀ : Finset K) {g : Finset K}
    {v : K} (hvg : v ∈ g) (hvoutside : v ∉ g₀) :
    doubledEdge g₀ false g ≠
      doubledEdge g₀ true g := by
  intro hedges
  have hv :
      doubledVertexLift g₀ false v ∈
        doubledEdge g₀ true g := by
    rw [← hedges]
    exact mem_doubledEdge g₀ false g v hvg
  obtain ⟨w, hwg, hwv⟩ :=
    Finset.mem_image.mp hv
  have hwv' : w = v := by
    have := congrArg
      (doubledVertexForget g₀) hwv
    simpa using this
  subst w
  simp [doubledVertexLift, hvoutside] at hwv

/-- The two labelled copies coincide exactly when the old edge has no
outside vertex. -/
theorem doubledEdge_false_eq_true_iff_subset
    (g₀ : Finset K) (g : Finset K) :
    doubledEdge g₀ false g =
        doubledEdge g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro hedges v hvg
    by_contra hvoutside
    exact
      doubledEdge_false_ne_true_of_mem_complement
        g₀ hvg hvoutside hedges
  · intro hg
    exact doubledEdge_copy_independent_of_subset
      g₀ hg false true

/-- Every old edge/copy pair which contributes an edge to the doubled
bundle. -/
abbrev DoubledEdgeSource
    (B : HypergraphBundle J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}

/-- The doubled edge belonging to one source edge and one copy. -/
def doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    Finset (DoubledOccurrenceVertex g₀) :=
  doubledEdge g₀ s.1 s.2.1

/-- Product indexed by the two labelled copies of every remaining edge.
This source-indexed form retains multiplicity even before one proves that
distinct sources give distinct doubled `Finset` edges. -/
noncomputable def doubledSourceProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : DoubledOccurrenceVertex g₀ → G) : ℝ :=
  ∏ s : B.DoubledEdgeSource g₀,
    A s.2.1 (fun v =>
      x (doubledVertexLift g₀ s.1 v.1))

/-- The source-indexed product on an assembled doubled assignment is
exactly the product of the two remainder fibers. -/
theorem doubledSourceProduct_doubledAssignment
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by
  classical
  unfold doubledSourceProduct
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [doubledAssignment_lift_true,
    doubledAssignment_lift_false]
  have hfalse :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))))
  have htrue :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))))
  rw [htrue, hfalse]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  rw [mul_comm]
  rfl

/-- The doubled Cauchy--Schwarz moment is a single normalized mean over
assignments on the doubled occurrence-vertex set.  The integrand is the
source-indexed product, so the identity is valid even when the two copies
of an edge contained in `g₀` coincide as `Finset`s. -/
theorem doubledRemainderMoment_eq_mean_doubledSourceProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean (B.doubledSourceProduct g₀ A) := by
  rw [B.doubledRemainderMoment_eq_mean₂_pair]
  rw [mean_splitDoubledAssignment]
  simp_rw [B.doubledSourceProduct_doubledAssignment]

/-- The finite family of all lifted remaining edges.  Using an image
correctly identifies two lifted edges when all their vertices lie in the
shared selected edge. -/
def doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    Finset (Finset (DoubledOccurrenceVertex g₀)) :=
  Finset.univ.image (B.doubledEdgeOfSource g₀)

theorem mem_doubledEdges_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (d : Finset (DoubledOccurrenceVertex g₀)) :
    d ∈ B.doubledEdges g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          doubledEdge g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, hsd⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩

/-- The doubled occurrence projection forgets the copy label and then uses
the original bundle projection. -/
def doubledProjection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → J :=
  fun v => B.projection (doubledVertexForget g₀ v)

@[simp]
theorem doubledProjection_lift
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.doubledProjection g₀
        (doubledVertexLift g₀ copy v) =
      B.projection v := by
  simp [doubledProjection]

/-- A lifted occurrence edge has the same projected base edge. -/
@[simp]
theorem image_doubledProjection_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (B.doubledProjection g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using hvj⟩
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv,
          by simpa using hvj⟩

/-- The occurrence bundle obtained by identifying `g₀` and duplicating all
outside vertices and remaining edges. -/
def duplicateOutside
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J (DoubledOccurrenceVertex g₀) H where
  edges := B.doubledEdges g₀
  projection := B.doubledProjection g₀
  projection_injective_on_edge := by
    intro d hd v hv w hw hvw
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    obtain ⟨v₀, hv₀, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, hw₀, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (doubledVertexLift g₀ copy)
    apply B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg) hv₀ hw₀
    simpa using hvw
  projection_mem_base := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    rw [image_doubledProjection_doubledEdge]
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl

/-- Every doubled edge has the cardinality of the source edge which
produced it. -/
theorem duplicateOutside_edge_card
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ (B.duplicateOutside g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, hgd⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  subst d
  exact ⟨g, hg, card_doubledEdge g₀ copy g⟩

/-- Duplication does not increase bundle order. -/
theorem duplicateOutside_order_le_eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤
      (B.eraseEdge g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, hdg⟩ :=
    B.duplicateOutside_edge_card g₀ hd
  rw [hdg]
  exact (B.eraseEdge g₀).edge_card_le_order hg

/-- In particular, duplication does not increase the original order. -/
theorem duplicateOutside_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤ B.order :=
  (B.duplicateOutside_order_le_eraseEdge g₀).trans
    (B.eraseEdge_order_le g₀)

/-- There are at most two doubled occurrence edges for each remaining
source edge. -/
theorem card_doubledEdges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.doubledEdges g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  calc
    (Finset.univ.image
        (B.doubledEdgeOfSource g₀)).card ≤
        (Finset.univ :
          Finset (B.DoubledEdgeSource g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [DoubledEdgeSource]

/-- A doubled edge is stable under lifting after forgetting its vertices. -/
theorem doubledEdge_image_forget_of_subset
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    have huLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← hwv, ← huw, huLift]
    exact hu
  · intro hv
    have hvLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨doubledVertexForget g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        hvLift⟩

/-- Downward closure is preserved whenever it is already available after
erasing the selected edge. -/
theorem duplicateOutside_closed
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by
  intro d hd f hfd
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  let h : Finset K :=
    f.image (doubledVertexForget g₀)
  have hhg : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ :=
      Finset.mem_image.mp (hfd hw)
    rw [← hwv, ← huw]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    hclosed hg hhg
  have hlift :
      doubledEdge g₀ copy h = f :=
    doubledEdge_image_forget_of_subset
      g₀ copy hfd
  rw [← hlift]
  exact
    (B.mem_doubledEdges_iff g₀
      (doubledEdge g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩

/-- Erasing a maximum edge from a downward-closed bundle and then doubling
preserves downward closure. -/
theorem duplicateOutside_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion :=
  B.duplicateOutside_closed g₀
    (B.eraseEdge_closed_of_maximal
      hclosed hg₀ hmax)

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean` -/

section
/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- Pointwise idempotence of a base-edge weight family on the base
hypergraph.  Real-valued indicator families satisfy this condition. -/
def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

/-- Equality of finite sets transports their membership subtypes. -/
def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)

@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

/-- Transporting a function on a finite-set membership subtype amounts to
precomposing with the inverse membership transport. -/
theorem cast_finsetPi_apply
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((finsetMembershipEquivOfEq h).symm a) := by
  subst t
  rfl

/-- The forward map of `projectionEquiv` is the bundle projection. -/
@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

/-- A product is unchanged when its indexing map identifies factors whose
common value is idempotent. -/
theorem prod_comp_eq_prod_image_of_idempotent
    {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hw' :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih hw',
        Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w hfa]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w hfa
      · rw [Finset.prod_insert hfa]

/-- Evaluating a pulled-back base weight on a lifted occurrence edge agrees
with evaluating the original pulled-back weight on its labelled source. -/
theorem pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by
  classical
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      doubledEdge g₀ copy g ∈
        (B.duplicateOutside g₀).edges := by
    exact
      (B.mem_doubledEdges_iff g₀
        (doubledEdge g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd,
    B.pullbackBaseEdgeWeight_of_mem A hgB]
  have himage :
      (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection =
        g.image B.projection := by
    exact B.image_doubledProjection_doubledEdge g₀ copy g
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(doubledEdge g₀ copy g).image
        (B.duplicateOutside g₀).projection,
      (B.duplicateOutside g₀).projectedEdgeTuple hd
        (edgeTuple (doubledEdge g₀ copy g) x)⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB
        (fun v =>
          x (doubledVertexLift g₀ copy v.1))⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jleft :
      {j : J //
        j ∈ (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let v : {v : K // v ∈ g} :=
    (B.projectionEquiv hgB).symm j
  have hjv :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.projectionEquiv hgB).apply_symm_apply j
  have hvlift :
      doubledVertexLift g₀ copy v.1 ∈
        doubledEdge g₀ copy g :=
    mem_doubledEdge g₀ copy g v.1 v.2
  have hpreimage :
      ((B.duplicateOutside g₀).projectionEquiv hd).symm jleft =
        ⟨doubledVertexLift g₀ copy v.1, hvlift⟩ := by
    apply ((B.duplicateOutside g₀).projectionEquiv hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      jleft.1 = j.1 := by
        exact
          finsetMembershipEquivOfEq_symm_val
            himage j
      _ = B.projection v.1 :=
        congrArg Subtype.val hjv.symm
      _ =
          (((B.duplicateOutside g₀).projectionEquiv hd)
            ⟨doubledVertexLift g₀ copy v.1,
              hvlift⟩).1 := by
        rw [projectionEquiv_apply_val,
          duplicateOutside_projection,
          doubledProjection_lift]
  unfold lhsInput rhsInput projectedEdgeTuple edgeTuple
  change
    x (((B.duplicateOutside g₀).projectionEquiv hd).symm
        jleft).1 =
      x (doubledVertexLift g₀ copy v.1)
  rw [hpreimage]

/-- The weight of an actual doubled occurrence edge at a fixed doubled
assignment. -/
noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)

/-- A source factor is the factor attached to its actual doubled edge. -/
theorem doubledBundleEdgeFactor_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledBundleEdgeFactor g₀ A x
        (B.doubledEdgeOfSource g₀ s) =
      B.pullbackBaseEdgeWeight A s.2.1
        (fun v =>
          x (doubledVertexLift g₀ s.1 v.1)) := by
  exact
    B.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
      g₀ A s.1 s.2.2 x

/-- Every actual doubled-edge factor is idempotent when the base weights
are idempotent. -/
theorem doubledBundleEdgeFactor_idempotent
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀))
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledBundleEdgeFactor g₀ A x d *
        B.doubledBundleEdgeFactor g₀ A x d =
      B.doubledBundleEdgeFactor g₀ A x d := by
  classical
  unfold doubledBundleEdgeFactor
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd]
  exact hA _ ((B.duplicateOutside g₀).projection_mem_base d hd) _

/-- For indicator base weights, the source-indexed doubled product is
exactly the ordinary bundle product of the duplicated bundle. -/
theorem doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  unfold doubledSourceProduct
  calc
    (∏ s : B.DoubledEdgeSource g₀,
        B.pullbackBaseEdgeWeight A s.2.1
          (fun v =>
            x (doubledVertexLift g₀ s.1 v.1))) =
        ∏ s : B.DoubledEdgeSource g₀,
          B.doubledBundleEdgeFactor g₀ A x
            (B.doubledEdgeOfSource g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.doubledBundleEdgeFactor_doubledEdgeOfSource
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.DoubledEdgeSource g₀)).image
                (B.doubledEdgeOfSource g₀),
          B.doubledBundleEdgeFactor g₀ A x d := by
      apply prod_comp_eq_prod_image_of_idempotent
      intro d hd
      apply B.doubledBundleEdgeFactor_idempotent
        g₀ A hA x d
      simpa [doubledEdges] using hd
    _ =
        (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
      rfl

/-- Consequently the doubled Cauchy--Schwarz remainder moment is the
ordinary count of the duplicated bundle for pulled-back indicator
weights.  Downward closure and maximality ensure that this duplicated
bundle remains a downward-closed bundle of no larger order. -/
theorem doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  have _hduplicateClosed :
      (B.duplicateOutside g₀).IsClosedUnderInclusion :=
    B.duplicateOutside_closed_of_maximal
      hclosed hg₀ hmax
  rw [B.doubledRemainderMoment_eq_mean_doubledSourceProduct]
  unfold bundleCount
  apply congrArg mean
  funext x
  exact
    B.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
      g₀ A hA x

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean` -/

section
/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/

/-- Retain exactly the occurrence edges satisfying `P`. -/
def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1

@[simp]
theorem filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges = B.edges.filter P :=
  rfl

@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]

@[simp]
theorem filterEdges_projection
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).projection = B.projection :=
  rfl

/-- Edge filtering cannot increase the number of occurrence edges. -/
theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A hereditary edge predicate preserves downward closure. -/
theorem filterEdges_closed
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (hclosed : B.IsClosedUnderInclusion)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.filterEdges P).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hg' := (B.mem_filterEdges_edges P g).1 hg
  exact (B.mem_filterEdges_edges P f).2
    ⟨hclosed hg'.1 hfg, hP hg'.2 hfg⟩

/-! ## The lower-order and strict-boundary filtrations -/

/-- The subbundle consisting of edges whose cardinality is strictly below
`d`. -/
def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d

@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]

/-- For a positive cutoff, every edge in the lower-order subbundle has
order strictly below that cutoff, including when the subbundle is empty. -/
theorem lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.lowerOrder d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2

theorem card_lowerOrder_edges_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (d : ℕ) :
    (B.lowerOrder d).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact (Finset.card_le_card hfg).trans_lt hg

/-- The strict-boundary subbundle below `g₀`. -/
def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀

@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl

@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]

/-- A strict boundary has order below the size of its ambient edge. -/
theorem strictBoundary_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.strictBoundary g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2

theorem card_strictBoundary_edges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem strictBoundary_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    (B.strictBoundary g₀).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact lt_of_le_of_lt hfg hg

/-! ## Main-density products -/

/-- Product of a base density over all occurrence edges of a bundle. -/
noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)

@[simp]
theorem bundleMainProduct_filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p =
      ∏ g ∈ B.edges.filter P,
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_lowerOrder
    (B : HypergraphBundle J K H)
    (d : ℕ) (p : Finset J → ℝ) :
    (B.lowerOrder d).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g.card < d),
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_strictBoundary
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g ⊂ g₀),
        p (g.image B.projection) :=
  rfl

/-- Erasing one edge removes precisely its main-density factor. -/
theorem bundleMainProduct_eraseEdge_mul
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.eraseEdge g₀).bundleMainProduct p *
        p (g₀.image B.projection) =
      B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  simp only [eraseEdge]
  rw [Finset.prod_erase_mul _ _ hg₀]

/-! ## The main product under duplication -/

/-- A fixed labelled lift is injective on occurrence edges.  Forgetting
the doubled vertices is a left inverse. -/
theorem doubledEdge_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledEdge g₀ copy) := by
  intro g h hgh
  have himage :=
    congrArg
      (Finset.image (doubledVertexForget g₀)) hgh
  simpa using himage

/-- The doubled edge family is the union of the two fixed-copy images. -/
theorem doubledEdges_eq_image_union
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨true, g, hg, rfl⟩

/-- Removing the first-copy image from the second-copy image leaves
exactly those old edges which meet the complement of the shared edge. -/
theorem image_true_sdiff_image_false
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have hdtrue :
        d ∈ s.image (doubledEdge g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hdtrue
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro hgsub
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (doubledEdge_copy_independent_of_subset
        g₀ hgsub false true)
  · intro hd
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro hfalse
    obtain ⟨h, hh, hhg⟩ :=
      Finset.mem_image.mp hfalse
    have hgh : h = g := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀)) hhg
      simpa using himage
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((doubledEdge_false_eq_true_iff_subset
        g₀ g).1 hhg)

/-- A fixed-copy image has the same projected main-density product as its
source edge family. -/
theorem prod_image_doubledEdge_main
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (doubledEdge g₀ copy),
        p (d.image (B.doubledProjection g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (doubledEdge_injective g₀ copy).injOn]
  simp

/-- General main-density product identity for duplication.  Edges
contained in `g₀` have only one actual doubled copy; all other remaining
edges have two. -/
theorem bundleMainProduct_duplicateOutside
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (doubledEdge g₀ false)
  let second :=
    s.image (doubledEdge g₀ true)
  have hsplit :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.duplicateOutside g₀).bundleMainProduct p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.doubledProjection g₀)) := by
      unfold bundleMainProduct first second
      simp only [duplicateOutside_edges,
        duplicateOutside_projection]
      rw [B.doubledEdges_eq_image_union g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.doubledProjection g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.doubledProjection g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.doubledProjection g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [image_true_sdiff_image_false]
      rw [B.prod_image_doubledEdge_main g₀ false]
      rw [B.prod_image_doubledEdge_main g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [hsplit]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl

/-- **Lower-order duplication identity.**  Duplicating the lower-order
subbundle around `g₀` contributes one copy of every strict-boundary
density and the square of every other lower-order density. -/
theorem bundleMainProduct_duplicateOutside_lowerOrder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.lowerOrder g₀.card).bundleMainProduct_duplicateOutside g₀ p]
  have hg₀' :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have hboundary :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB,
        Finset.card_lt_card hgstrict⟩, hgstrict.1⟩
  have hexterior :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [lowerOrder, strictBoundary,
    filterEdges, bundleMainProduct]
  rw [Finset.erase_eq_of_notMem hg₀',
    hboundary, hexterior]

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean` -/

section
/-!
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Local strict-boundary products -/

/-- Restrict a tuple on `g` to a subedge `f`. -/
def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩

omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

/-- Product of all strict-boundary occurrence-edge weights, viewed as a
function of a tuple on the selected edge.  The subtype index retains the
proof that every factor really is a strict subedge of `g₀`. -/
noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)

/-- The local strict-boundary product is exactly the ordinary bundle
product of the strict-boundary subbundle. -/
theorem strictBoundaryLocalProduct_edgeTuple
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
        (edgeTuple g₀ x) =
      (B.strictBoundary g₀).bundleProduct A x := by
  classical
  unfold strictBoundaryLocalProduct
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.strictBoundary g₀).edges},
      A g.1
        (restrictEdgeTuple
          (((B.mem_strictBoundary_edges g₀ g.1).1
            g.2).2.1)
          (edgeTuple g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.strictBoundary g₀).edges},
          A g.1 (edgeTuple g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact restrictEdgeTuple_edgeTuple _ x
    _ =
        ∏ g ∈ (B.strictBoundary g₀).edges,
          A g (edgeTuple g x) :=
      Finset.prod_coe_sort
        (B.strictBoundary g₀).edges
        (fun g => A g (edgeTuple g x))
    _ = (B.strictBoundary g₀).bundleProduct A x := by
      rfl

/-- Every strict-boundary edge occurs in the erased remainder. -/
theorem strictBoundary_edges_subset_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges ⊆
      B.edges.erase g₀ := by
  intro g hg
  have hg' :=
    (B.mem_strictBoundary_edges g₀ g).1 hg
  exact Finset.mem_erase.mpr
    ⟨hg'.2.ne, hg'.1⟩

/-- Pointwise idempotence of an occurrence-edge weight family. -/
def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y

/-- Pullback preserves pointwise idempotence. -/
theorem pullbackBaseEdgeWeight_weightsIdempotent
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.WeightsIdempotent
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-- If `s ⊆ t` and all factors on `s` are idempotent, multiplying the
`t`-product by the `s`-product does not change it. -/
theorem prod_mul_prod_eq_right_of_subset_of_idempotent
    {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hat : a ∈ t :=
        hst (Finset.mem_insert_self a s)
      have hst' : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun hia => ha (hia ▸ hi),
            hst (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f hat]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) hst' hf']

/-- The strict-boundary product is already present in the selected-edge
remainder.  Thus an idempotent boundary product may be inserted for free. -/
theorem strictBoundaryLocalProduct_mul_edgeRemainder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
          (edgeTuple g₀ x) *
        B.edgeRemainder g₀ A x =
      B.edgeRemainder g₀ A x := by
  rw [B.strictBoundaryLocalProduct_edgeTuple]
  unfold edgeRemainder bundleProduct
  apply prod_mul_prod_eq_right_of_subset_of_idempotent
    (B.strictBoundary g₀).edges
    (B.edges.erase g₀)
    (fun g => A g (edgeTuple g x))
    (B.strictBoundary_edges_subset_erase g₀)
  intro g hg
  exact hA g
    (Finset.mem_of_mem_erase
      (B.strictBoundary_edges_subset_erase g₀ hg))
    (edgeTuple g x)

/-- Localizing a selected-edge function to the strict boundary does not
change its contribution.  This is the exact insertion used before the
localized defect estimate. -/
theorem edgeContribution_mul_strictBoundaryLocalProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A) :
    B.edgeContribution g₀ q A =
      B.edgeContribution g₀
        (fun y =>
          q y *
            B.strictBoundaryLocalProduct g₀ A y)
        A := by
  unfold edgeContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.strictBoundaryLocalProduct_mul_edgeRemainder
      g₀ A hA x]

/-! ## Main-product cancellation at a selected edge -/

/-- Product of the lower-order main densities which do not lie in the
selected edge. -/
noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

/-- Product of the main densities on the erased edges which are not
strictly lower than the selected edge.  Under maximality these are exactly
the other edges of the selected rank. -/
noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)

/-- Projection preserves the cardinality of every occurrence edge. -/
theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm

/-- Nonnegative base densities give a nonnegative bundle main product. -/
theorem bundleMainProduct_nonneg
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.bundleMainProduct p := by
  unfold bundleMainProduct
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.projection_mem_base g hg)

/-- The lower-order main product splits into the strict boundary and the
lower-order exterior. -/
theorem bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have hboundary :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB, Finset.card_lt_card hgstrict⟩,
        hgstrict.1⟩
  have hexterior :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold bundleMainProduct lowerExteriorMainProduct
  simp only [lowerOrder_edges, strictBoundary_edges]
  rw [← hboundary, ← hexterior]
  exact hsplit.symm

/-- The strict-boundary factor in the localized defect and the main
product of the duplicated lower-order bundle form the square of the full
lower-order main product.  This is the cancellation which prevents the
defect estimate from paying every lower-rank density a second time. -/
theorem boundary_mul_duplicateLower_main_eq_lowerOrder_sq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p *
        ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      ((B.lowerOrder g₀.card).bundleMainProduct p) ^ 2 := by
  rw [B.bundleMainProduct_duplicateOutside_lowerOrder
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    g₀ p]
  unfold lowerExteriorMainProduct
  ring

/-- Erasing the selected edge leaves the lower-order product times the
product of the other edges at least as large as the selected edge. -/
theorem lowerOrder_mul_maximalRemainder_eq_erase_main
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p *
        B.maximalRemainderMainProduct g₀ p =
      (B.eraseEdge g₀).bundleMainProduct p := by
  classical
  have hlower :
      (B.edges.erase g₀).filter
          (fun g => g.card < g₀.card) =
        B.edges.filter
          (fun g => g.card < g₀.card) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_hne, hgB⟩, hgcard⟩
      exact ⟨hgB, hgcard⟩
    · rintro ⟨hgB, hgcard⟩
      exact ⟨⟨fun hgg₀ => by
        subst g
        exact Nat.lt_irrefl _ hgcard, hgB⟩,
        hgcard⟩
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (B.edges.erase g₀)
      (fun g => g.card < g₀.card)
      (fun g => p (g.image B.projection))
  unfold bundleMainProduct maximalRemainderMainProduct
  simp only [lowerOrder_edges, eraseEdge_edges]
  rw [← hlower]
  exact hsplit

/-- Under maximality, every factor in `maximalRemainderMainProduct` is
another factor of exactly the selected rank. -/
theorem card_eq_selected_of_mem_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (hmax g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)

/-- The number of other selected-rank edges is at most the number of
edges left after erasing the selected one. -/
theorem card_maximalRemainder_le_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- A same-rank density floor controls the entire maximal-rank remainder
product. -/
theorem pow_card_maximalRemainder_le
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by
  classical
  unfold maximalRemainderMainProduct
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.projection_mem_base g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.card_image_projection
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.card_eq_selected_of_mem_maximalRemainder
          hmax hg

/-! ## Discarding the other maximal-rank factors -/

/-- Pullbacks through two bundles with the same occurrence projection
agree on every edge common to the two bundles. -/
theorem pullbackBaseEdgeWeight_eq_of_projection_eq
    (B C : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hprojection : B.projection = C.projection)
    {g : Finset K}
    (hgB : g ∈ B.edges) (hgC : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      C.pullbackBaseEdgeWeight A g y := by
  classical
  rw [B.pullbackBaseEdgeWeight_of_mem A hgB y,
    C.pullbackBaseEdgeWeight_of_mem A hgC y]
  have himage :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) hprojection
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB y⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.projectedEdgeTuple hgC y⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let vB := (B.projectionEquiv hgB).symm jB
  let vC := (C.projectionEquiv hgC).symm j
  have hjB : jB.1 = j.1 :=
    finsetMembershipEquivOfEq_symm_val himage j
  have hvB :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.projectionEquiv hgB).apply_symm_apply jB)
  have hvC' :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.projectionEquiv hgC).apply_symm_apply j)
  have hvC :
      B.projection vC.1 = j.1 := by
    rw [hprojection]
    exact hvC'
  have hval : vB.1 = vC.1 :=
    B.projection_injective_on_edge g hgB
      vB.2 vC.2
      ((hvB.trans hjB).trans hvC.symm)
  unfold lhsInput rhsInput projectedEdgeTuple
  change y vB = y vC
  exact congrArg y (Subtype.ext hval)

/-- The doubled lower-order edge family is a subfamily of the full
doubled remainder edge family. -/
theorem doubledEdges_lowerOrder_subset
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.lowerOrder g₀.card).doubledEdges g₀ ⊆
      B.doubledEdges g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, hgd⟩ :=
    ((B.lowerOrder g₀.card).mem_doubledEdges_iff
      g₀ d).1 hd
  apply (B.mem_doubledEdges_iff g₀ d).2
  refine ⟨copy, g, ?_, hgd⟩
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.mem_lowerOrder_edges g₀.card g).1
        hgLower).1⟩

/-- For pulled-back `[0,1]` weights, deleting every other maximal-rank
factor can only increase the doubled bundle product. -/
theorem duplicateOutside_bundleProduct_le_lowerOrder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleProduct
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  let C := B.duplicateOutside g₀
  let D := (B.lowerOrder g₀.card).duplicateOutside g₀
  have hDC : D.edges ⊆ C.edges := by
    simpa [C, D] using
      B.doubledEdges_lowerOrder_subset g₀
  have hprojection : C.projection = D.projection := by
    rfl
  unfold bundleProduct
  calc
    (∏ d ∈ C.edges,
        C.pullbackBaseEdgeWeight A
          d (edgeTuple d x)) ≤
        ∏ d ∈ D.edges,
          C.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
        hDC
      · intro d hd
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).1
      · intro d hd _hdD
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).2
    _ =
        ∏ d ∈ D.edges,
          D.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact C.pullbackBaseEdgeWeight_eq_of_projection_eq
        D A hprojection (hDC hd) hd (edgeTuple d x)

/-- **Maximal-factor discard.**  For indicator base weights, the exact
doubled remainder moment is bounded by the count of the duplicated
lower-order bundle. -/
theorem doubledRemainderMoment_pullback_le_lowerOrder
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  rw [B.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    hclosed hg₀ hmax A hAidempotent]
  unfold bundleCount
  apply mean_mono
  intro x
  exact B.duplicateOutside_bundleProduct_le_lowerOrder
    g₀ A hA01 x

/-- A localized defect square bound and the maximal-factor discard give
the source-faithful square-root defect estimate.  The two lower-order
counts in this statement are precisely the two outer-induction calls. -/
theorem abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by
  let boundaryCount :=
    (B.strictBoundary g₀).bundleCount
      ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)
  let lowerDoubledCount :=
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
        (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)
  have hboundary0 : 0 ≤ boundaryCount := by
    apply (B.strictBoundary g₀).bundleCount_nonneg
    exact
      (B.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hlower0 : 0 ≤ lowerDoubledCount := by
    apply
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
    exact
      ((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hmoment0 :
      0 ≤ B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) :=
    B.doubledRemainderMoment_nonneg g₀
      (B.pullbackBaseEdgeWeight A)
  have hmoment :
      B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
        lowerDoubledCount :=
    B.doubledRemainderMoment_pullback_le_lowerOrder
      hclosed hg₀ hmax A hA01 hAidempotent
  have hsq :
      B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A) ^ 2 ≤
        (β * boundaryCount) * lowerDoubledCount := by
    calc
      B.edgeContribution g₀ q
            (B.pullbackBaseEdgeWeight A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        B.edgeContribution_sq_le_localSquare_mul_doubled
          g₀ q (B.pullbackBaseEdgeWeight A)
      _ ≤
          (β * boundaryCount) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        mul_le_mul_of_nonneg_right hlocalized hmoment0
      _ ≤ (β * boundaryCount) * lowerDoubledCount :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hβ hboundary0)
  have hradicand :
      0 ≤ (β * boundaryCount) * lowerDoubledCount :=
    mul_nonneg (mul_nonneg hβ hboundary0) hlower0
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hradicand]
  exact hsq

end HypergraphBundle

/-! ## Numerical envelope for the double induction -/

/-- A quantitative envelope for Tao's double induction on bundle order
and bundle size.

The recurrence has three pieces:

* the error already accumulated after erasing the selected edge;
* the localized defect error, controlled by two lower-order bundle calls;
* the common frozen-uniformity error.

The field `rankFloor` says that `μ d` is a common lower bound for every
density at rank at most `d`. -/
structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

/-- The one-step increment appearing in a bundle-counting envelope. -/
noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

/-- Restatement of the envelope recurrence using the named increment. -/
theorem IsBundleCountingEnvelope.add_stepIncrement_le
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        bundleCountingStepIncrement α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [bundleCountingStepIncrement, add_assoc] using hE.step d n

/-- Both lower-order correction factors in the envelope are nonnegative. -/
theorem IsBundleCountingEnvelope.lower_correction_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.error_nonneg d (n + 1)])
    (by linarith [hE.error_nonneg d (2 * (n + 1))])

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleEnvelopeSelection.lean` -/

section
/-!
# Small parameters for the bundle-counting envelope

The generalized bundle-counting induction asks for an error array indexed
both by bundle order and by the number of occurrence edges.  At one step,
the array must absorb

```text
sqrt (β * (1 + lower error) * (1 + doubled lower error)) / α^n
  + τ / μ^n.
```

This file gives a self-contained numerical solution when all density
floors are bounded below by one common number `a`.  We put both the defect
and frozen-uniformity errors equal to `t²` and define the array by equality
in the required recurrence.  For each fixed finite pair `(r, L)`, this
array is continuous in `t` and is zero at `t = 0`.  Consequently one can
choose a strictly positive `t`, as small as desired, for which the final
error is below any prescribed positive reserve.

Using a square as the common small parameter has two conveniences:
nonnegativity is automatic for every real `t`, and the square root in the
recurrence remains a globally continuous function of `t`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## The equality schedule -/

/-- The contribution added while adjoining the `(n + 1)`st occurrence
edge at the next order. -/
noncomputable def bundleCommonStepIncrement
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt
        (t ^ 2 *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      a ^ (n + 1) +
    t ^ 2 / a ^ (n + 1)

/-- Given the complete error row at lower order, form the next row by
summing the one-edge increments. -/
noncomputable def bundleCommonNextRow
    (a t : ℝ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n

/-- The common-floor bundle-counting error schedule.

Order zero is exact.  Each positive-order row is obtained from the
preceding row by `bundleCommonNextRow`. -/
noncomputable def bundleCommonEnvelopeError
    (a t : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d)

@[simp]
theorem bundleCommonNextRow_zero
    (a t : ℝ) (lower : ℕ → ℝ) :
    bundleCommonNextRow a t lower 0 = 0 :=
  rfl

@[simp]
theorem bundleCommonNextRow_succ
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) :
    bundleCommonNextRow a t lower (n + 1) =
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_zero_order
    (a t : ℝ) (n : ℕ) :
    bundleCommonEnvelopeError a t 0 n = 0 :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_succ_order
    (a t : ℝ) (d n : ℕ) :
    bundleCommonEnvelopeError a t (d + 1) n =
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d) n :=
  rfl

/-! ## Positivity and monotonicity -/

/-! ## The envelope interface -/

/-! ## Vanishing at the origin and finite-horizon selection -/

/-- At zero defect and zero frozen-uniformity error, the schedule is
identically zero. -/
@[simp]
theorem bundleCommonNextRow_zero_parameter
    (a : ℝ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n, bundleCommonNextRow a 0 lower n = 0 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ, ihn]
      simp [bundleCommonStepIncrement, hlower]

/-- Every fixed entry of the schedule is zero at the origin. -/
@[simp]
theorem bundleCommonEnvelopeError_zero_parameter
    (a : ℝ) :
    ∀ d n, bundleCommonEnvelopeError a 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ihd =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_zero_parameter a
        (bundleCommonEnvelopeError a 0 d) ihd n

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean` -/

section
/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## Prefix density floors -/

/-- The least density encountered through rank `d`, written recursively so
that no finite-set choice is involved. -/
def bundleRankwiseDensityFloor (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bundleRankwiseDensityFloor α d) (α (d + 1))

@[simp]
theorem bundleRankwiseDensityFloor_zero (α : ℕ → ℝ) :
    bundleRankwiseDensityFloor α 0 = α 0 :=
  rfl

@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl

/-- A positive rankwise density schedule has positive prefix floors. -/
theorem bundleRankwiseDensityFloor_pos
    {α : ℕ → ℝ} (hα : ∀ d, 0 < α d) :
    ∀ d, 0 < bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => simpa using hα 0
  | succ d ih =>
      simpa using lt_min ih (hα (d + 1))

/-- The prefix floor at `d` lies below every density of rank at most `d`. -/
theorem bundleRankwiseDensityFloor_le
    (α : ℕ → ℝ) {i d : ℕ} (hid : i ≤ d) :
    bundleRankwiseDensityFloor α d ≤ α i := by
  induction d with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hid
      subst i
      exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      by_cases hi : i = d + 1
      · subst i
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hid hi)))

/-! ## The rankwise recurrence -/

/-- The rank-`d + 1` contribution from adjoining the `(n + 1)`st edge. -/
noncomputable def bundleRankwiseStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

/-- Construct the next error row.  The first branch of the maximum preserves
the preceding-order estimate, while the second absorbs the new counting
increment exactly. -/
noncomputable def bundleRankwiseNextRow
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n)

/-- The rankwise bundle-counting envelope. -/
noncomputable def bundleRankwiseEnvelopeError
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d)

@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl

@[simp]
theorem bundleRankwiseNextRow_succ
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n) :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

/-! ## Positivity and monotonicity -/

theorem bundleRankwiseStepIncrement_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (lower : ℕ → ℝ) (d n : ℕ) :
    0 ≤ bundleRankwiseStepIncrement α β μ τ lower d n := by
  unfold bundleRankwiseStepIncrement
  exact add_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hα _) _))
    (div_nonneg hτ (pow_nonneg (hμ _) _))

theorem bundleRankwiseNextRow_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleRankwiseNextRow α β μ τ d lower n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (add_nonneg ih
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ lower d n))

theorem bundleRankwiseEnvelopeError_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) :
    ∀ d n, 0 ≤ bundleRankwiseEnvelopeError α β μ τ d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_nonneg hα hμ hτ d _ n

@[simp]
theorem bundleRankwiseEnvelopeError_zero_card
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, bundleRankwiseEnvelopeError α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp

/-- Every rankwise row increases with the number of occurrence edges. -/
theorem bundleRankwiseEnvelopeError_monotone_card
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) :
    Monotone (bundleRankwiseEnvelopeError α β μ τ d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero => simp
  | succ d =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (le_add_of_nonneg_right
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ _ d n))

/-- The maximum in the row constructor makes the error monotone in rank. -/
theorem bundleRankwiseEnvelopeError_le_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ d n ≤
      bundleRankwiseEnvelopeError α β μ τ (d + 1) n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_left _ _

theorem bundleRankwiseEnvelopeError_monotone_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    Monotone (fun d => bundleRankwiseEnvelopeError α β μ τ d n) := by
  apply monotone_nat_of_le_succ
  exact fun d => bundleRankwiseEnvelopeError_le_succ_order α β μ τ d n

/-! ## The generalized-counting interface -/

/-- The rankwise equality/max schedule is a counting envelope with the
prefix-minimum density floor. -/
theorem bundleRankwiseEnvelopeError_isEnvelope
    {α β : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) :
    IsBundleCountingEnvelope α β
      (bundleRankwiseDensityFloor α) τ
      (bundleRankwiseEnvelopeError α β
        (bundleRankwiseDensityFloor α) τ) := by
  let μ := bundleRankwiseDensityFloor α
  have hμ : ∀ d, 0 < μ d := bundleRankwiseDensityFloor_pos hα
  refine
    { density_pos := hα
      density_le_one := hα_one
      defect_nonneg := hβ
      uniform_nonneg := hτ
      floor_pos := hμ
      rankFloor := ?_
      error_nonneg := bundleRankwiseEnvelopeError_nonneg
        (fun d => (hα d).le) (fun d => (hμ d).le) hτ
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact bundleRankwiseDensityFloor_le α hid
  · intro d d' n hdd'
    exact (bundleRankwiseEnvelopeError_monotone_order α β μ τ n) hdd'
  · intro d n n' hnn'
    exact (bundleRankwiseEnvelopeError_monotone_card
      (fun q => (hα q).le) (fun q => (hμ q).le) hτ d) hnn'
  · intro d n
    have hstep :
        bundleRankwiseNextRow α β μ τ d
              (bundleRankwiseEnvelopeError α β μ τ d) n +
            bundleRankwiseStepIncrement α β μ τ
              (bundleRankwiseEnvelopeError α β μ τ d) d n ≤
          max (bundleRankwiseEnvelopeError α β μ τ d (n + 1))
            (bundleRankwiseNextRow α β μ τ d
                (bundleRankwiseEnvelopeError α β μ τ d) n +
              bundleRankwiseStepIncrement α β μ τ
                (bundleRankwiseEnvelopeError α β μ τ d) d n) :=
      le_max_right _ _
    simp [μ, bundleRankwiseStepIncrement, add_assoc] at hstep ⊢

/-! ## Vanishing and continuous rankwise parameter paths -/

/-- If every rank defect and the frozen-uniformity error vanish, the next
row is zero over a zero lower row. -/
@[simp]
theorem bundleRankwiseNextRow_zero_parameters
    (α μ : ℕ → ℝ) (d : ℕ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n,
      bundleRankwiseNextRow α (fun _ => 0) μ 0 d lower n = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ, ih]
      simp [bundleRankwiseStepIncrement, hlower]

/-- The complete rankwise schedule vanishes when all analytic errors do. -/
@[simp]
theorem bundleRankwiseEnvelopeError_zero_parameters
    (α μ : ℕ → ℝ) :
    ∀ d n,
      bundleRankwiseEnvelopeError α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_zero_parameters α μ d _ ih n

/-! ## Density-scaled finite-horizon selection -/

/-- A defect schedule whose rank-`d` reserve uses only `α d` (besides the
common scalar and the caller-chosen exponent). -/
noncomputable def bundleRankwiseScaledDefect
    (α : ℕ → ℝ) (power : ℕ → ℕ) (t : ℝ) (d : ℕ) : ℝ :=
  (t * (α d) ^ (power d)) ^ 2

/-- A frozen-uniformity reserve scaled by the prefix density floor at the
finite rank horizon. -/
noncomputable def bundleRankwiseScaledUniformity
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) (t : ℝ) : ℝ :=
  (t *
      (bundleRankwiseDensityFloor α rankBound) ^ uniformPower) ^ 2

@[simp]
theorem bundleRankwiseScaledDefect_zero
    (α : ℕ → ℝ) (power : ℕ → ℕ) (d : ℕ) :
    bundleRankwiseScaledDefect α power 0 d = 0 := by
  simp [bundleRankwiseScaledDefect]

@[simp]
theorem bundleRankwiseScaledUniformity_zero
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) :
    bundleRankwiseScaledUniformity α rankBound uniformPower 0 = 0 := by
  simp [bundleRankwiseScaledUniformity]

/-! ## Explicit finite-horizon sufficient bounds -/

/-- Reverse-doubling edge horizon: lower-order calls made while controlling
rank `d + 1` through its horizon fit into the rank-`d` horizon. -/
def bundleReverseDoublingHorizon
    (rankBound edgeBound d : ℕ) : ℕ :=
  (edgeBound + 1) * 2 ^ (rankBound - d)

theorem bundleReverseDoublingHorizon_two_mul_succ
    {rankBound edgeBound d : ℕ} (hd : d < rankBound) :
    2 * bundleReverseDoublingHorizon rankBound edgeBound (d + 1) =
      bundleReverseDoublingHorizon rankBound edgeBound d := by
  have hsub : rankBound - d = rankBound - (d + 1) + 1 := by
    omega
  simp only [bundleReverseDoublingHorizon, hsub, pow_succ]
  ring

theorem bundleReverseDoublingHorizon_le_zero
    (rankBound edgeBound d : ℕ) :
    bundleReverseDoublingHorizon rankBound edgeBound d ≤
      bundleReverseDoublingHorizon rankBound edgeBound 0 := by
  unfold bundleReverseDoublingHorizon
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le rankBound d)

/-- If the two lower-row entries are bounded by `B`, the actual one-edge
increment is bounded by the sum of a defect-only and a uniformity-only
majorant.  This is the separation used by the finite-horizon theorem below. -/
theorem bundleRankwiseStepIncrement_le_of_lower_le
    {α β μ : ℕ → ℝ} {τ B η : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (lower : ℕ → ℝ) (d n : ℕ)
    (hlower_nonneg : ∀ m, 0 ≤ lower m)
    (hlower₁ : lower (n + 1) ≤ B)
    (hlower₂ : lower (2 * (n + 1)) ≤ B)
    (hdefect :
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform :
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseStepIncrement α β μ τ lower d n ≤ η := by
  have hlower₁nonneg : 0 ≤ 1 + lower (n + 1) := by
    linarith [hlower_nonneg (n + 1)]
  have hlower₂nonneg : 0 ≤ 1 + lower (2 * (n + 1)) := by
    linarith [hlower_nonneg (2 * (n + 1))]
  have hB₁nonneg : 0 ≤ 1 + B := by
    linarith [hlower_nonneg (n + 1), hlower₁]
  have hproduct :
      (1 + lower (n + 1)) * (1 + lower (2 * (n + 1))) ≤
        (1 + B) * (1 + B) := by
    exact mul_le_mul
      (by linarith)
      (by linarith)
      hlower₂nonneg hB₁nonneg
  have hradicand :
      β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1))) ≤
        β (d + 1) * (1 + B) * (1 + B) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (hβ (d + 1))
  have hsqrt :
      Real.sqrt
          (β (d + 1) *
            (1 + lower (n + 1)) *
            (1 + lower (2 * (n + 1)))) ≤
        Real.sqrt (β (d + 1) * (1 + B) * (1 + B)) :=
    Real.sqrt_le_sqrt hradicand
  have hnormalized :
      Real.sqrt
            (β (d + 1) *
              (1 + lower (n + 1)) *
              (1 + lower (2 * (n + 1)))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2 :=
    (div_le_div_of_nonneg_right hsqrt
      (pow_nonneg (hα (d + 1)) (n + 1))).trans hdefect
  unfold bundleRankwiseStepIncrement
  linarith

/-- A finite-rank/cardinality estimate from separated numerical hypotheses.

`horizon` must reverse-double, because one counting step at rank `d + 1`
consults lower-order bundles of sizes `n + 1` and `2(n + 1)`.  The defect
hypothesis at rank `d + 1` mentions only `β (d + 1)` and `α (d + 1)`;
the uniformity hypothesis mentions only `τ` and `μ (d + 1)`.  Thus the two
analytic parameters can be scheduled independently once a common per-step
budget `η` and a harmless lower-error cap `B` have been fixed. -/
theorem bundleRankwiseEnvelopeError_le_finiteBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound : ℕ) (horizon : ℕ → ℕ)
    (hreverse : ∀ d, d < rankBound →
      2 * horizon (d + 1) ≤ horizon d)
    (hzero : ∀ d, d ≤ rankBound → horizon d ≤ horizon 0)
    (hcap :
      (rankBound : ℝ) * (horizon 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ rankBound → ∀ n, n ≤ horizon d →
      bundleRankwiseEnvelopeError α β μ τ d n ≤
        (d : ℝ) * (horizon 0 : ℝ) * η := by
  intro d hd
  induction d with
  | zero =>
      intro n hn
      simp
  | succ d ih =>
      have hdlt : d < rankBound := Nat.lt_of_succ_le hd
      let lower := bundleRankwiseEnvelopeError α β μ τ d
      have hlower_nonneg : ∀ m, 0 ≤ lower m :=
        bundleRankwiseEnvelopeError_nonneg hα hμ hτ d
      have hdle : d ≤ rankBound := Nat.le_of_lt hdlt
      have hdbound :
          (d : ℝ) * (horizon 0 : ℝ) * η ≤ B := by
        have hdcast : (d : ℝ) ≤ rankBound := by exact_mod_cast hdle
        have hq0 : 0 ≤ (horizon 0 : ℝ) := by positivity
        have hscale : 0 ≤ (horizon 0 : ℝ) * η := mul_nonneg hq0 hη
        calc
          (d : ℝ) * (horizon 0 : ℝ) * η =
              (d : ℝ) * ((horizon 0 : ℝ) * η) := by ring
          _ ≤ (rankBound : ℝ) * ((horizon 0 : ℝ) * η) :=
            mul_le_mul_of_nonneg_right hdcast hscale
          _ = (rankBound : ℝ) * (horizon 0 : ℝ) * η := by ring
          _ ≤ B := hcap
      have hrow : ∀ m, m ≤ horizon (d + 1) →
          bundleRankwiseNextRow α β μ τ d lower m ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η := by
        intro m hm
        induction m with
        | zero =>
            simp only [bundleRankwiseNextRow_zero, Nat.cast_zero, zero_mul,
              add_zero]
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hη
        | succ m ihm =>
            have hmle : m ≤ horizon (d + 1) := Nat.le_trans (Nat.le_succ m) hm
            have hm_lt : m < horizon (d + 1) := Nat.lt_of_succ_le hm
            have hsmall₁ : m + 1 ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hsmall₂ : 2 * (m + 1) ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hlower₁raw := ih hdle (m + 1) hsmall₁
            have hlower₂raw := ih hdle (2 * (m + 1)) hsmall₂
            have hlower₁ : lower (m + 1) ≤ B := hlower₁raw.trans hdbound
            have hlower₂ : lower (2 * (m + 1)) ≤ B := hlower₂raw.trans hdbound
            have hincrement :
                bundleRankwiseStepIncrement α β μ τ lower d m ≤ η :=
              bundleRankwiseStepIncrement_le_of_lower_le hα hβ lower d m
                hlower_nonneg hlower₁ hlower₂
                (hdefect d hdlt m hm_lt) (huniform d hdlt m hm_lt)
            rw [bundleRankwiseNextRow_succ]
            apply max_le
            · calc
                lower (m + 1) ≤
                    (d : ℝ) * (horizon 0 : ℝ) * η := hlower₁raw
                _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η :=
                  le_add_of_nonneg_right (mul_nonneg (by positivity) hη)
            · calc
                bundleRankwiseNextRow α β μ τ d lower m +
                      bundleRankwiseStepIncrement α β μ τ lower d m ≤
                    ((d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η) + η :=
                  add_le_add (ihm hmle) hincrement
                _ = (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η := by
                  push_cast
                  ring
      intro n hn
      rw [bundleRankwiseEnvelopeError_succ_order]
      have hmain := hrow n hn
      have hnzero : n ≤ horizon 0 := hn.trans (hzero (d + 1) hd)
      have hncast : (n : ℝ) ≤ horizon 0 := by exact_mod_cast hnzero
      have hηscale : (n : ℝ) * η ≤ (horizon 0 : ℝ) * η :=
        mul_le_mul_of_nonneg_right hncast hη
      calc
        bundleRankwiseNextRow α β μ τ d lower n ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (n : ℝ) * η := hmain
        _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
            (horizon 0 : ℝ) * η := add_le_add_right hηscale _
        _ = ((d + 1 : ℕ) : ℝ) * (horizon 0 : ℝ) * η := by
          push_cast
          ring

/-- Specialization of the finite-budget theorem to the canonical
reverse-doubling horizons. -/
theorem bundleRankwiseEnvelopeError_le_reverseDoublingBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseEnvelopeError α β μ τ rankBound (edgeBound + 1) ≤
      (rankBound : ℝ) *
        (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η := by
  apply bundleRankwiseEnvelopeError_le_finiteBudget hα hβ hμ hτ hη
    rankBound (bundleReverseDoublingHorizon rankBound edgeBound)
    (fun d hd => (bundleReverseDoublingHorizon_two_mul_succ hd).le)
    (fun d _hd => bundleReverseDoublingHorizon_le_zero rankBound edgeBound d)
    hcap hdefect huniform rankBound le_rfl (edgeBound + 1)
  simp [bundleReverseDoublingHorizon]

/-- A ready-to-use half-error criterion with prefix density floors.

The cap `1` makes every lower correction factor at most `2`.  The defect
conditions remain rank-local, while the uniform conditions use only the
prefix floor.  The conclusion packages both the global counting-envelope
interface and the finite error estimate needed for positivity. -/
theorem bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
    {α β : ℕ → ℝ} {τ η : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ 1)
    (hfinal :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η < 1 / 2)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ /
          (bundleRankwiseDensityFloor α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    IsBundleCountingEnvelope α β
        (bundleRankwiseDensityFloor α) τ
        (bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ) ∧
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound < 1 / 2 := by
  have hμ : ∀ d, 0 ≤ bundleRankwiseDensityFloor α d :=
    fun d => (bundleRankwiseDensityFloor_pos hα d).le
  have hbound :=
    bundleRankwiseEnvelopeError_le_reverseDoublingBudget
      (fun d => (hα d).le) hβ hμ hτ hη rankBound edgeBound
      hcap hdefect huniform
  have hcard :
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound ≤
        bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound (edgeBound + 1) :=
    (bundleRankwiseEnvelopeError_monotone_card
      (fun d => (hα d).le) hμ hτ rankBound) (Nat.le_succ edgeBound)
  exact ⟨bundleRankwiseEnvelopeError_isEnvelope hα hα_one hβ hτ,
    (hcard.trans hbound).trans_lt hfinal⟩

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Finite/Bonferroni.lean` -/

section
/-!
# Elementary finite Bonferroni bounds

This file records the first two truncations of inclusion--exclusion for a
finite family of zero--one real-valued functions.  The upper bound deliberately
sums ordered pairs of distinct indices; this is a harmless factor-two
overcount that avoids choosing an order on the index type.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized finite mean commutes with a finite sum. -/
theorem mean_finset_sum {α κ : Type*}
    [Fintype α] [Fintype κ]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/ConditionalAverage.lean` -/

section
/-!
# Conditional averages on finite partitions

Hypergraph regularity in this project is finite.  A partition of `univ`
therefore carries an elementary conditional average: on each atom, replace a
function by its normalized average over that atom.  This file establishes the
algebraic facts needed by the later energy-increment argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Average `f` on the atom of `P` containing `x`. -/
noncomputable def conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f

theorem conditionalMean_eq_of_part_eq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hxy : P.part x = P.part y) :
    conditionalMean P f x = conditionalMean P f y := by
  rw [conditionalMean, conditionalMean, hxy]

/-- Conditional averages are constant on every partition atom. -/
theorem conditionalMean_eq_of_mem_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    conditionalMean P f y = conditionalMean P f x := by
  apply conditionalMean_eq_of_part_eq
  apply P.part_eq_of_mem
  · simp
  · exact hy

theorem conditionalMean_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ conditionalMean P f x := by
  exact Finset.expect_nonneg fun y _ => hf y

theorem conditionalMean_sub {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y - g y) x =
      conditionalMean P f x - conditionalMean P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g

theorem conditionalMean_smul {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => c * f y) x =
      c * conditionalMean P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm

@[simp]
theorem conditionalMean_const {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (x : Ω) :
    conditionalMean P (fun _ => c) x = c := by
  rw [conditionalMean]
  exact Finset.expect_const (by simp) c

/-- Averaging a conditional average over the same partition does nothing. -/
@[simp]
theorem conditionalMean_idem {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean P f) x =
      conditionalMean P f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean P f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean P f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part P f hy
    _ = conditionalMean P f x :=
      Finset.expect_const (by simp) _

/-- On one atom, summing its conditional average recovers the original
sum on that atom. -/
theorem sum_conditionalMean_on_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [conditionalMean, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f

/-- Conditional averaging preserves the total sum. -/
theorem sum_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, conditionalMean P f x = ∑ x, f x := by
  classical
  have hparts :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, conditionalMean P f x =
        ∑ x ∈ P.parts.biUnion id, conditionalMean P f x := by
      exact Finset.sum_congr hparts.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, conditionalMean P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sum_conditionalMean_on_part P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr hparts fun _ _ => rfl

/-- Conditional averaging preserves the normalized global mean. -/
theorem mean_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (conditionalMean P f) = mean f := by
  change (𝔼 x, conditionalMean P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, sum_conditionalMean P f]

/-- Finite Jensen/Cauchy--Schwarz on the atom containing `x`. -/
theorem conditionalMean_sq_le {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P f x ^ 2 ≤
      conditionalMean P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [conditionalMean,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h

/-- The `L²` energy of a function relative to a finite partition. -/
noncomputable def partitionEnergy {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => conditionalMean P f x ^ 2

theorem partitionEnergy_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ partitionEnergy P f := by
  exact mean_nonneg fun x => sq_nonneg _

/-- Conditional expectation is an `L²` contraction. -/
theorem partitionEnergy_le_mean_sq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    partitionEnergy P f ≤ mean fun x => f x ^ 2 := by
  calc
    partitionEnergy P f ≤
        mean (conditionalMean P fun x => f x ^ 2) :=
      mean_mono fun x => conditionalMean_sq_le P f x
    _ = mean (fun x => f x ^ 2) :=
      mean_conditionalMean P fun x => f x ^ 2

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FacePartition.lean` -/

section
/-!
# Finite face partitions

The finite regularity argument uses partitions of finite face spaces.  This
file fixes the refinement convention, packages common refinements and
partitions generated by cuts, and constructs pullbacks along maps of finite
types.

Mathlib orders `Finpartition` by refinement: `P ≤ Q` means that `P` is finer
than `Q`.  Consequently the lattice infimum is the common refinement.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A partition of all elements of a finite face space. -/
abbrev FacePartition (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :=
  Finpartition (Finset.univ : Finset Ω)

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A face partition is determined by its atom lookup function. -/
theorem ext_of_part_eq {P Q : FacePartition Ω}
    (h : ∀ x, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    have hxs : Q.part x = s :=
      (h x).symm.trans (P.part_eq_of_mem hs hx)
    rw [← hxs]
    exact Q.part_mem.2 (Finset.mem_univ x)
  · intro hs
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hs
    have hxs : P.part x = s :=
      (h x).trans (Q.part_eq_of_mem hs hx)
    rw [← hxs]
    exact P.part_mem.2 (Finset.mem_univ x)

/-- Refinement shrinks the atom containing every point. -/
theorem part_subset_of_le {P Q : FacePartition Ω}
    (h : P ≤ Q) (x : Ω) :
    P.part x ⊆ Q.part x := by
  obtain ⟨s, hs, hsub⟩ :=
    h (P.part_mem.2 (Finset.mem_univ x))
  have hxs : x ∈ s :=
    hsub (P.mem_part (Finset.mem_univ x))
  rw [Q.part_eq_of_mem hs hxs]
  exact hsub

/-- Pointwise atom inclusion characterizes the refinement order. -/
theorem le_iff_part_subset {P Q : FacePartition Ω} :
    P ≤ Q ↔ ∀ x, P.part x ⊆ Q.part x := by
  constructor
  · exact fun h x => part_subset_of_le h x
  · intro h s hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), ?_⟩
    rw [← P.part_eq_of_mem hs hx]
    exact h x

/-- The indiscrete face partition. -/
def indiscrete : FacePartition Ω :=
  ⊤

/-- The discrete face partition. -/
def discrete : FacePartition Ω :=
  ⊥

@[simp]
theorem part_indiscrete (x : Ω) :
    (indiscrete : FacePartition Ω).part x = Finset.univ := by
  change (⊤ : FacePartition Ω).part x = Finset.univ
  have hmem :
      (⊤ : FacePartition Ω).part x ∈
        (⊤ : FacePartition Ω).parts :=
    (⊤ : FacePartition Ω).part_mem.2 (Finset.mem_univ x)
  exact Finset.mem_singleton.mp
    (Finpartition.parts_top_subset
      (Finset.univ : Finset Ω) hmem)

@[simp]
theorem part_discrete (x : Ω) :
    (discrete : FacePartition Ω).part x = {x} := by
  apply Finpartition.part_eq_of_mem
  · rw [discrete, Finpartition.mem_bot_iff]
    exact ⟨x, Finset.mem_univ x, rfl⟩
  · exact Finset.mem_singleton_self x

/-- Partition complexity measured by the number of atoms. -/
def complexity (P : FacePartition Ω) : ℕ :=
  P.parts.card

/-- A canonical representative of a partition atom. -/
noncomputable def representative
    (P : FacePartition Ω) (a : P.parts) : Ω :=
  Classical.choose (P.nonempty_of_mem_parts a.2)

/-- The canonical representative belongs to its atom. -/
theorem representative_mem
    (P : FacePartition Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)

/-- Looking up the atom of its representative recovers the chosen atom. -/
theorem part_representative
    (P : FacePartition Ω) (a : P.parts) :
    P.part (P.representative a) = a.1 :=
  P.part_eq_of_mem a.2 (P.representative_mem a)

@[simp]
theorem complexity_discrete :
    complexity (discrete : FacePartition Ω) = Fintype.card Ω := by
  simp [complexity, discrete]

@[simp]
theorem complexity_indiscrete [Nonempty Ω] :
    complexity (indiscrete : FacePartition Ω) = 1 := by
  let x : Ω := Classical.choice inferInstance
  have huniv :
      (Finset.univ : Finset Ω) ∈
        (⊤ : FacePartition Ω).parts := by
    have hx :=
      (⊤ : FacePartition Ω).part_mem.2
        (Finset.mem_univ x)
    change
      (indiscrete : FacePartition Ω).part x ∈
        (indiscrete : FacePartition Ω).parts at hx
    rw [part_indiscrete] at hx
    exact hx
  have hparts :
      (⊤ : FacePartition Ω).parts =
        {(Finset.univ : Finset Ω)} := by
    apply Finset.Subset.antisymm
    · exact Finpartition.parts_top_subset _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      simpa [hs] using huniv
  simp [complexity, indiscrete, hparts]

/-- The common refinement of two face partitions.  This is an infimum
because the `Finpartition` order points from finer to coarser partitions. -/
def join (P Q : FacePartition Ω) : FacePartition Ω :=
  P ⊓ Q

theorem join_le_left (P Q : FacePartition Ω) :
    join P Q ≤ P :=
  inf_le_left

theorem join_le_right (P Q : FacePartition Ω) :
    join P Q ≤ Q :=
  inf_le_right

theorem le_join_iff {P Q R : FacePartition Ω} :
    R ≤ join P Q ↔ R ≤ P ∧ R ≤ Q :=
  le_inf_iff

@[simp]
theorem part_join (P Q : FacePartition Ω) (x : Ω) :
    (join P Q).part x = P.part x ∩ Q.part x := by
  apply Finpartition.part_eq_of_mem
  · rw [join, Finpartition.parts_inf]
    apply Finset.mem_erase.mpr
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(P.part x, Q.part x), ?_, rfl⟩
      simp
  · simp

/-- A binary common refinement has at most the product of the two atom
counts. -/
theorem complexity_join_le (P Q : FacePartition Ω) :
    complexity (join P Q) ≤ complexity P * complexity Q := by
  change (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card
  calc
    (P ⊓ Q).parts.card =
        (((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).erase ⊥).card :=
      congrArg Finset.card (Finpartition.parts_inf P Q)
    _ ≤
        ((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (P.parts ×ˢ Q.parts).card :=
      Finset.card_image_le
    _ = P.parts.card * Q.parts.card :=
      Finset.card_product P.parts Q.parts

/-! ## Finite common refinements -/

/-- The common refinement of a finite family of face partitions.  The empty
family gives the indiscrete partition. -/
def joinFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω) :
    FacePartition Ω :=
  s.inf P

@[simp]
theorem joinFinset_empty {ι : Type*} [DecidableEq ι]
    (P : ι → FacePartition Ω) :
    joinFinset ∅ P = indiscrete :=
  rfl

@[simp]
theorem joinFinset_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (P : ι → FacePartition Ω) :
    joinFinset (insert a s) P =
      join (P a) (joinFinset s P) := by
  simp [joinFinset, join]

/-- A finite common refinement refines each partition in the family. -/
theorem joinFinset_le_of_mem {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : ι → FacePartition Ω)
    {i : ι} (hi : i ∈ s) :
    joinFinset s P ≤ P i :=
  Finset.inf_le hi

/-- The universal property of a finite common refinement. -/
theorem le_joinFinset_iff {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {P : ι → FacePartition Ω}
    {Q : FacePartition Ω} :
    Q ≤ joinFinset s P ↔ ∀ i ∈ s, Q ≤ P i :=
  Finset.le_inf_iff

/-- Two points lie in the same atom of a finite common refinement exactly
when they lie in the same atom of every constituent partition. -/
theorem mem_part_joinFinset_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω)
    (x y : Ω) :
    y ∈ (joinFinset s P).part x ↔
      ∀ i ∈ s, y ∈ (P i).part x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [joinFinset_empty]
      simp
  | @insert a s ha ih =>
      simp only [joinFinset_insert, part_join,
        Finset.mem_inter, Finset.mem_insert, forall_eq_or_imp,
        ih]

/-- The partition generated by a finite family of cuts.  Two points lie in
the same atom exactly when every cut gives them the same membership bit. -/
def generatedBy (F : Finset (Finset Ω)) : FacePartition Ω :=
  Finpartition.atomise Finset.univ F

/-- The generator-membership signature is the exact atom relation for
`generatedBy`. -/
@[simp]
theorem mem_part_generatedBy_iff (F : Finset (Finset Ω))
    (x y : Ω) :
    y ∈ (generatedBy F).part x ↔
      ∀ s ∈ F, (x ∈ s ↔ y ∈ s) := by
  classical
  let P : FacePartition Ω := generatedBy F
  have hp : P.part x ∈ P.parts :=
    P.part_mem.2 (Finset.mem_univ x)
  have hpAtom :
      P.part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts := by
    change
      (Finpartition.atomise
        (Finset.univ : Finset Ω) F).part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts at hp
    exact hp
  obtain ⟨_, Q, hQ, hpart⟩ :=
    Finpartition.mem_atomise.mp hpAtom
  have hmem := Finset.ext_iff.mp hpart
  have hx : x ∈ P.part x :=
    P.mem_part (Finset.mem_univ x)
  have hxAtom := (hmem x).2 hx
  simp only [Finset.mem_filter] at hxAtom
  constructor
  · intro hy s hs
    have hyAtom := (hmem y).2 hy
    simp only [Finset.mem_filter] at hyAtom
    exact (hxAtom.2 s hs).symm.trans (hyAtom.2 s hs)
  · intro hsignature
    apply (hmem y).1
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    intro s hs
    exact (hxAtom.2 s hs).trans (hsignature s hs)

/-- Adding generators refines the generated partition. -/
theorem generatedBy_antitone {F G : Finset (Finset Ω)}
    (hFG : F ⊆ G) :
    generatedBy G ≤ generatedBy F := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_generatedBy_iff] at hy ⊢
  intro s hs
  exact hy s (hFG hs)

/-- A partition generated by `m` cuts has at most `2^m` atoms. -/
theorem complexity_generatedBy_le (F : Finset (Finset Ω)) :
    complexity (generatedBy F) ≤ 2 ^ F.card := by
  exact Finpartition.card_atomise_le

/-- No cuts generate the indiscrete partition. -/
@[simp]
theorem generatedBy_empty :
    generatedBy (∅ : Finset (Finset Ω)) =
      indiscrete := by
  apply ext_of_part_eq
  intro x
  ext y
  simp [mem_part_generatedBy_iff, part_indiscrete]

/-- The equivalence relation of belonging to the same atom. -/
abbrev atomSetoid (P : FacePartition Ω) : Setoid Ω :=
  Setoid.ker P.part

@[simp]
theorem atomSetoid_rel (P : FacePartition Ω) (x y : Ω) :
    atomSetoid P x y ↔ P.part x = P.part y :=
  Iff.rfl

/-- The same-atom relation transported along a map. -/
def pullbackSetoid {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : Setoid Ω where
  r x y := Q.part (f x) = Q.part (f y)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

instance instDecidableRelPullbackSetoid {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) :
    DecidableRel (pullbackSetoid f Q) := by
  intro x y
  change Decidable (Q.part (f x) = Q.part (f y))
  infer_instance

/-- Pull a partition back along a map of finite face spaces. -/
def pullback {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : FacePartition Ω :=
  Finpartition.ofSetoid (pullbackSetoid f Q)

@[simp]
theorem mem_part_pullback_iff {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      Q.part (f x) = Q.part (f y) := by
  change
    y ∈
        (Finpartition.ofSetoid
          (pullbackSetoid f Q)).part x ↔
      Q.part (f x) = Q.part (f y)
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- Membership in a pullback atom is exactly membership of the image in
the target atom. -/
theorem mem_part_pullback_iff_image_mem {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      f y ∈ Q.part (f x) := by
  rw [mem_part_pullback_iff]
  constructor
  · intro h
    exact
      (Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).2 h.symm
  · intro h
    exact
      ((Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).1 h).symm

/-- Pullback preserves refinement. -/
theorem pullback_mono {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) {P Q : FacePartition Λ}
    (h : P ≤ Q) :
    pullback f P ≤ pullback f Q := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_pullback_iff_image_mem] at hy ⊢
  exact part_subset_of_le h (f x) hy

/-- Pullback along the identity map does not change a partition. -/
@[simp]
theorem pullback_id (P : FacePartition Ω) :
    pullback id P = P := by
  apply ext_of_part_eq
  intro x
  ext y
  simp only [mem_part_pullback_iff_image_mem, id_eq]

end FacePartition

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Energy.lean` -/

section
/-!
# Energy under refinement of finite face partitions

For mathlib's refinement order, `P ≤ Q` means that `P` is finer than `Q`.
This file proves both finite tower identities and the corresponding
monotonicity of `partitionEnergy`.  The stronger Pythagorean identity records
the energy increment exactly as the mean-square difference of the two
conditional averages.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Fine conditional averaging preserves the sum on each atom of every
coarser partition. -/
theorem sum_conditionalMean_on_coarser_part
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  let fineParts : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have hUnion : fineParts.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 hxt
    · intro hxs
      obtain ⟨t, ht, hxt⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, htu⟩ := hPQ ht
      have hus : u = s :=
        Q.eq_of_mem_parts hu hs (htu hxt) hxs
      have hts : t ⊆ s := by
        simpa [hus] using htu
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩, hxt⟩
  have hdisjoint :
      (↑fineParts : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ fineParts.biUnion id,
          conditionalMean P f x := by
      exact Finset.sum_congr hUnion.symm fun _ _ => rfl
    _ =
        ∑ t ∈ fineParts,
          ∑ x ∈ t, conditionalMean P f x :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ fineParts, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_conditionalMean_on_part P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ fineParts.biUnion id, f x :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr hUnion fun _ _ => rfl

/-- Coarse-after-fine tower identity. -/
@[simp]
theorem conditionalMean_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean Q (conditionalMean P f) x =
      conditionalMean Q f x := by
  change
    Finset.expect (Q.part x) (conditionalMean P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    sum_conditionalMean_on_coarser_part P Q hPQ f
      (Q.part_mem.2 (Finset.mem_univ x))]

/-- Fine-after-coarse tower identity.  A function constant on coarse atoms is
already constant on every finer atom. -/
@[simp]
theorem conditionalMean_reverse_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean Q f) x =
      conditionalMean Q f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean Q f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part Q f
        (FacePartition.part_subset_of_le hPQ x hy)
    _ = conditionalMean Q f x :=
      Finset.expect_const (by simp) _

/-- A factor constant on the current atom can be pulled out of a conditional
average. -/
theorem conditionalMean_mul_right_of_constant_on_part
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    conditionalMean P (fun y => u y * v y) x =
      conditionalMean P u x * v x := by
  calc
    conditionalMean P (fun y => u y * v y) x =
        conditionalMean P (fun y => v x * u y) x := by
      rw [conditionalMean, conditionalMean]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * conditionalMean P u x :=
      conditionalMean_smul P (v x) u x
    _ = conditionalMean P u x * v x := by
      ring

/-- A conditional average is measurable with respect to its own partition,
so it can be pulled out of another conditional average over that partition. -/
theorem conditionalMean_mul_conditionalMean_right
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => u y * conditionalMean P v y) x =
      conditionalMean P u x * conditionalMean P v x := by
  apply conditionalMean_mul_right_of_constant_on_part
  intro y hy
  exact conditionalMean_eq_of_mem_part P v hy

/-- The fine and coarse conditional averages have the same mixed second
moment as the coarse conditional average has second moment. -/
theorem mean_conditionalMean_mul_eq_sq_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      conditionalMean P f x * conditionalMean Q f x) =
      mean (fun x => conditionalMean Q f x ^ 2) := by
  calc
    mean (fun x =>
        conditionalMean P f x * conditionalMean Q f x) =
        mean (conditionalMean Q (fun x =>
          conditionalMean P f x * conditionalMean Q f x)) :=
      (mean_conditionalMean Q _).symm
    _ =
        mean (fun x =>
          conditionalMean Q (conditionalMean P f) x *
            conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_conditionalMean_right
        Q (conditionalMean P f) f x
    _ =
        mean (fun x =>
          conditionalMean Q f x * conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      rw [conditionalMean_tower_of_le P Q hPQ]
    _ = mean (fun x => conditionalMean Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]

/-- Exact Pythagorean identity for refinement: the energy increment is the
mean-square distance between the fine and coarse conditional averages. -/
theorem partitionEnergy_pythagorean
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f =
      partitionEnergy Q f +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) := by
  have hcross :=
    mean_conditionalMean_mul_eq_sq_of_le P Q hPQ f
  have hdiff :
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) =
        mean (fun x => conditionalMean P f x ^ 2) -
          2 * mean (fun x =>
            conditionalMean P f x * conditionalMean Q f x) +
          mean (fun x => conditionalMean Q f x ^ 2) := by
    calc
      mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) =
          mean (fun x =>
            conditionalMean P f x ^ 2 -
              2 * (conditionalMean P f x *
                conditionalMean Q f x) +
              conditionalMean Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => conditionalMean P f x ^ 2) -
            2 * mean (fun x =>
              conditionalMean P f x * conditionalMean Q f x) +
            mean (fun x => conditionalMean Q f x ^ 2) := by
        rw [mean_add, mean_sub, mean_smul]
  change
    mean (fun x => conditionalMean P f x ^ 2) =
      mean (fun x => conditionalMean Q f x ^ 2) +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2)
  rw [hdiff, hcross]
  ring

/-- Equivalent variance form of the Pythagorean identity. -/
theorem partitionEnergy_sub_eq_mean_sq
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f - partitionEnergy Q f =
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  ring

/-- Refinement can only increase partition energy. -/
theorem partitionEnergy_mono
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy Q f ≤ partitionEnergy P f := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  exact le_add_of_nonneg_right
    (mean_nonneg fun x => sq_nonneg _)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Regularity.lean` -/

section
/-!
# A finite energy-increment regularity step

This file isolates the quantitative part of finite hypergraph regularity which
is independent of the eventual removal argument.  A state consists of a
partition of one finite face space.  For a hypergraph with several face
spaces, such states are simply assembled into a dependent family
(`FaceRegularitySystem` below).

A Boolean cut test is represented by its support `A : Finset Ω`, and hence by
the `{0,1}`-valued function `finsetIndicator A`.  Refining a state by `A`
means adjoining its membership bit to the current partition.  The central
result, `energy_increment_of_booleanCut`, says

`ε ≤ |𝔼 x, residual x * 1_A x|`

implies an energy gain of at least `ε ^ 2`.  The proof is the exact finite
conditional-expectation proof: the new partition makes `1_A` measurable,
Cauchy--Schwarz bounds the correlation by the squared norm of the new
projection, and the Pythagorean identity identifies that norm with the energy
increment.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A canonical finite `{0,1}`-valued cut test, represented by its support. -/
abbrev BooleanCutTest (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω

namespace BooleanCutTest

/-- Evaluation of a Boolean cut test as a real-valued function. -/
def eval (A : BooleanCutTest Ω) : Ω → ℝ :=
  finsetIndicator A

omit [Fintype Ω] in
@[simp]
theorem eval_of_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  finsetIndicator_of_mem hx

omit [Fintype Ω] in
@[simp]
theorem eval_of_not_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  finsetIndicator_of_not_mem hx

omit [Fintype Ω] in
theorem eval_sq (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_le_one (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

end BooleanCutTest

/-- A real-valued function is measurable with respect to `P` when it is
constant on every atom of `P`. -/
def IsPartitionMeasurable (P : FacePartition Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x

namespace IsPartitionMeasurable

/-- Measurability is preserved when the partition is refined. -/
theorem of_le {P Q : FacePartition Ω} {g : Ω → ℝ}
    (hPQ : P ≤ Q) (hg : IsPartitionMeasurable Q g) :
    IsPartitionMeasurable P g := by
  intro x y hy
  exact hg x y (FacePartition.part_subset_of_le hPQ x hy)

/-- Every conditional average is measurable for its partition. -/
theorem conditionalMean (P : FacePartition Ω) (f : Ω → ℝ) :
    IsPartitionMeasurable P (conditionalMean P f) := by
  intro x y hy
  exact conditionalMean_eq_of_mem_part P f hy

end IsPartitionMeasurable

/-- The indicator of a generator is measurable for the partition generated
by that cut. -/
theorem booleanCut_measurable_generatedBy (A : BooleanCutTest Ω) :
    IsPartitionMeasurable
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have hxy : x ∈ A ↔ y ∈ A := by
    have hsignature :=
      (FacePartition.mem_part_generatedBy_iff
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact hsignature A (by simp)
  by_cases hx : x ∈ A
  · have hyA : y ∈ A := hxy.mp hx
    simp [hx, hyA]
  · have hyA : y ∉ A := by
      intro hy
      exact hx (hxy.mpr hy)
    simp [hx, hyA]

/-- Minimal regularity state for one finite face space. -/
structure FaceRegularityState (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : FacePartition Ω

/-- A collection of per-edge (or per-face-type) regularity states. -/
abbrev FaceRegularitySystem
    (ι : Type*) (face : ι → Type*)
    [∀ i, Fintype (face i)] [∀ i, DecidableEq (face i)] :=
  ∀ i, FaceRegularityState (face i)

namespace FaceRegularityState

/-- The structured component at the current state. -/
noncomputable def structured (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  conditionalMean S.partition f

/-- The residual after removing the current structured component. -/
noncomputable def residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x

/-- The `L²` energy visible at the current state. -/
noncomputable def energy (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : ℝ :=
  partitionEnergy S.partition f

/-- Residual correlation with a Boolean cut test. -/
noncomputable def booleanCutCorrelation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x

/-- Adjoin one cut-membership bit to the current partition. -/
def refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) : FaceRegularityState Ω where
  partition :=
    FacePartition.join S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω)))

@[simp]
theorem partition_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy ({A} : Finset (Finset Ω))) :=
  rfl

/-- Refining by a cut really refines the old partition. -/
theorem refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition ≤ S.partition :=
  FacePartition.join_le_left _ _

/-- The adjoined cut is measurable for the refined partition. -/
theorem booleanCut_measurable_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    IsPartitionMeasurable (S.refineBy A).partition A.eval := by
  apply IsPartitionMeasurable.of_le
    (FacePartition.join_le_right S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))))
  exact booleanCut_measurable_generatedBy A

/-- The residual has conditional mean zero on every current atom. -/
@[simp]
theorem conditionalMean_residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean S.partition (S.residual f) x = 0 := by
  change
    conditionalMean S.partition
      (fun y => f y - conditionalMean S.partition f y) x = 0
  rw [conditionalMean_sub]
  rw [conditionalMean_idem]
  ring

/-- The residual has global mean zero. -/
@[simp]
theorem mean_residual (S : FaceRegularityState Ω) (f : Ω → ℝ) :
    mean (S.residual f) = 0 := by
  change
    mean (fun x => f x - conditionalMean S.partition f x) = 0
  rw [mean_sub]
  rw [mean_conditionalMean]
  ring

/-- Projecting the old residual onto a refinement gives exactly the change
in structured components. -/
theorem conditionalMean_residual_refineBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) (x : Ω) :
    conditionalMean (S.refineBy A).partition (S.residual f) x =
      (S.refineBy A).structured f x - S.structured f x := by
  change
    conditionalMean (S.refineBy A).partition
        (fun y => f y - conditionalMean S.partition f y) x =
      conditionalMean (S.refineBy A).partition f x -
        conditionalMean S.partition f x
  rw [conditionalMean_sub]
  rw [conditionalMean_reverse_tower_of_le
    (S.refineBy A).partition S.partition (S.refineBy_le A)]

/-- A measurable factor may be pulled through a conditional projection in a
global pairing. -/
theorem mean_mul_eq_mean_conditionalMean_mul
    (P : FacePartition Ω) (u v : Ω → ℝ)
    (hv : IsPartitionMeasurable P v) :
    mean (fun x => u x * v x) =
      mean (fun x => conditionalMean P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (conditionalMean P (fun x => u x * v x)) :=
      (mean_conditionalMean P _).symm
    _ = mean (fun x => conditionalMean P u x * v x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_right_of_constant_on_part
        P u v x (hv x)

/-- The residual/cut pairing is the pairing of the new structured increment
with the same cut. -/
theorem booleanCutCorrelation_eq_projection
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [booleanCutCorrelation]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          conditionalMean (S.refineBy A).partition (S.residual f) x *
            A.eval x) :=
      mean_mul_eq_mean_conditionalMean_mul
        (S.refineBy A).partition (S.residual f) A.eval
        (S.booleanCut_measurable_refineBy A)
    _ = mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.conditionalMean_residual_refineBy f A x]

omit [DecidableEq Ω] in
/-- Global finite Cauchy--Schwarz for the normalized mean. -/
theorem mean_mul_sq_le_sq_mul_sq (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

/-- A Boolean cut test has squared `L²` norm at most one. -/
theorem mean_booleanCut_sq_le_one [Nonempty Ω]
    (A : BooleanCutTest Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  rw [A.eval_sq x]
  exact A.eval_le_one x

/-- Pythagoras identifies the energy increment under one cut refinement. -/
theorem energy_refineBy_sub_eq_mean_sq
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).energy f - S.energy f =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      (S.refineBy A).partition S.partition (S.refineBy_le A) f

/-- Squared residual correlation with a Boolean cut is bounded by the exact
energy gained after adjoining that cut. -/
theorem booleanCutCorrelation_sq_le_energyIncrement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A ^ 2 ≤
      (S.refineBy A).energy f - S.energy f := by
  rw [S.booleanCutCorrelation_eq_projection f A]
  let d : Ω → ℝ :=
    fun x => (S.refineBy A).structured f x - S.structured f x
  have hcs :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    mean_mul_sq_le_sq_mul_sq d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hA := mean_booleanCut_sq_le_one A
  calc
    mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := hcs
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.refineBy A).energy f - S.energy f := by
      exact (S.energy_refineBy_sub_eq_mean_sq f A).symm

/-- **Quantitative energy increment.**  Residual correlation at least `ε`
in absolute value against a `{0,1}` cut test forces energy gain at least
`ε ^ 2` after adjoining that test. -/
theorem energy_increment_of_booleanCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcorrelation : ε ≤ |S.booleanCutCorrelation f A|) :
    S.energy f + ε ^ 2 ≤ (S.refineBy A).energy f := by
  have hsquare :
      ε ^ 2 ≤ S.booleanCutCorrelation f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hcorrelation
  have hincrement :=
    S.booleanCutCorrelation_sq_le_energyIncrement f A
  linarith

/-- A state is regular against a finite family of Boolean cuts if every
residual correlation is at most `ε` in absolute value. -/
def IsRegularAgainst (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    (ε : ℝ) : Prop :=
  ∀ A ∈ cuts, |S.booleanCutCorrelation f A| ≤ ε

/-- Failure of regularity supplies a cut whose correlation is strictly above
the threshold. -/
theorem exists_booleanCut_of_not_regular
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬ S.IsRegularAgainst f cuts ε) :
    ∃ A ∈ cuts, ε < |S.booleanCutCorrelation f A| := by
  classical
  by_contra hnone
  apply h
  intro A hA
  by_contra hle
  apply hnone
  exact ⟨A, hA, lt_of_not_ge hle⟩

/-- Select a violating Boolean cut when the current state is irregular.
At a regular state the empty cut is used, so iteration remains total. -/
noncomputable def chosenIrregularCut
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsRegularAgainst f cuts ε then ∅
    else
      Classical.choose
        (S.exists_booleanCut_of_not_regular f cuts h)

/-- The actual weak-regularity refinement run obtained by repeatedly
adjoining the selected violating cut. -/
noncomputable def regularityRun
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := regularityRun S f cuts ε n
      T.refineBy (T.chosenIrregularCut f cuts ε)

@[simp]
theorem regularityRun_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem regularityRun_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRun f cuts ε (n + 1) =
      (S.regularityRun f cuts ε n).refineBy
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε) :=
  rfl

/-- The finite family of Boolean cuts adjoined during the first `n` steps
of the canonical run. -/
noncomputable def regularityRunCuts
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.regularityRun f cuts ε i).chosenIrregularCut
      f cuts ε

@[simp]
theorem regularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRunCuts f cuts ε 0 = ∅ := by
  simp [regularityRunCuts]

@[simp]
theorem regularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
        (S.regularityRunCuts f cuts ε n) := by
  classical
  simp [regularityRunCuts, Finset.range_add_one]

end FaceRegularityState

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutDiscrepancy.lean` -/

section
/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Delete coordinate `i` from an `r`-tuple. The impossible `r = 0`
case is discharged by eliminating `i : Fin 0`. -/
def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)

@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl

@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

/-- A family of cut tests, one for each deleted coordinate. -/
abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

/-- Every member of a cut-test family takes values in `[0,1]`. -/
def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

theorem IsBoundedCutTest.nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

theorem isBoundedCutTest_const
    {G : Type*} {r : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsBoundedCutTest (fun _ : Fin r => fun _ : Fin (r - 1) → G => c) :=
  ⟨fun _ _ => hc0, fun _ _ => hc1⟩

@[simp]
theorem isBoundedCutTest_zero
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (0 : ℝ)) :=
  isBoundedCutTest_const (by positivity) (by norm_num)

@[simp]
theorem isBoundedCutTest_one
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) :=
  isBoundedCutTest_const (by positivity) le_rfl

theorem IsBoundedCutTest.mono
    {G : Type*} {r : ℕ} {u v : CutTestFamily G r}
    (hu : IsBoundedCutTest u)
    (hv0 : ∀ i x, 0 ≤ v i x)
    (hvu : ∀ i x, v i x ≤ u i x) :
    IsBoundedCutTest v :=
  ⟨hv0, fun i x => (hvu i x).trans (hu.le_one i x)⟩

/-- The cut correlation of `f-g` with a family of deleted-coordinate
tests. -/
noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

/-- `f` and `g` differ by at most `ε` against every product of
`[0,1]`-valued deleted-coordinate tests. -/
def CutDiscrepancyLe
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |cutCorrelation r f g u| ≤ ε

@[simp]
theorem cutCorrelation_self
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f f u = 0 := by
  simp [cutCorrelation]

theorem cutCorrelation_swap
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r g f u = -cutCorrelation r f g u := by
  calc
    cutCorrelation r g f u =
        mean (fun x : Fin r → G =>
          (-1 : ℝ) *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              ∏ i, u i (eraseCoordinate i x))) := by
      apply congrArg mean
      funext x
      ring
    _ = (-1 : ℝ) *
        mean (fun x : Fin r → G =>
          (f (∑ i, x i) - g (∑ i, x i)) *
            ∏ i, u i (eraseCoordinate i x)) :=
      mean_smul _ _
    _ = -cutCorrelation r f g u := by
      simp [cutCorrelation]

theorem CutDiscrepancyLe.mono
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε ε' : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hε : ε ≤ ε') :
    CutDiscrepancyLe r f g ε' := by
  intro u hu0 hu1
  exact (h u hu0 hu1).trans hε

theorem CutDiscrepancyLe.refl
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) :
    CutDiscrepancyLe r f f 0 := by
  intro u _ _
  simp

theorem CutDiscrepancyLe.symm
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    CutDiscrepancyLe r g f ε := by
  intro u hu0 hu1
  rw [cutCorrelation_swap, abs_neg]
  exact h u hu0 hu1

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/GeneralizedConvolution.lean` -/

section
/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The tuple with prescribed coordinate sum `z` and prescribed tail `y`.
The zeroth coordinate is the unique value making the total sum equal `z`. -/
def sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (z - ∑ i, y i) y

@[simp]
theorem sumFiberTuple_zero {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    sumFiberTuple n z y 0 = z - ∑ i, y i :=
  rfl

@[simp]
theorem sumFiberTuple_succ {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) (i : Fin n) :
    sumFiberTuple n z y i.succ = y i :=
  rfl

@[simp]
theorem sum_sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    ∑ i, sumFiberTuple n z y i = z := by
  simp [sumFiberTuple, Fin.sum_univ_succ]

/-- The density, relative to uniform measure on `G`, of the only nonempty
fiber of the zero-coordinate sum map. It equals `|G|` at zero and vanishes
elsewhere. -/
noncomputable def zeroFiberDelta
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) : ℝ := by
  classical
  exact if z = 0 then (Fintype.card G : ℝ) else 0

@[simp]
theorem zeroFiberDelta_zero
    {G : Type*} [Fintype G] [AddCommGroup G] :
    zeroFiberDelta (G := G) 0 = Fintype.card G := by
  classical
  simp [zeroFiberDelta]

@[simp]
theorem zeroFiberDelta_of_ne
    {G : Type*} [Fintype G] [AddCommGroup G]
    {z : G} (hz : z ≠ 0) :
    zeroFiberDelta z = 0 := by
  classical
  simp [zeroFiberDelta, hz]

/-- The normalized fiber convolution of an arbitrary tuple weight.

For `r = n + 1`, this is the average of `w` on the fiber with sum `z`,
parametrized by `sumFiberTuple`. For `r = 0`, the scaled delta convention
preserves the exact disintegration identity. -/
noncomputable def fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (z : G) : ℝ := by
  cases r with
  | zero =>
      exact zeroFiberDelta z * w (fun i => Fin.elim0 i)
  | succ n =>
      exact mean fun y : Fin n → G => w (sumFiberTuple n z y)

@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl

@[simp]
theorem fiberConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    fiberConvolution (n + 1) w z =
      mean fun y : Fin n → G => w (sumFiberTuple n z y) :=
  rfl

/-- The product weight associated to a family of deleted-coordinate tests. -/
def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]

@[simp]
theorem cutTestProduct_mul
    {G : Type*} {r : ℕ} (u v : CutTestFamily G r)
    (x : Fin r → G) :
    cutTestProduct (fun i y => u i y * v i y) x =
      cutTestProduct u x * cutTestProduct v x := by
  simp [cutTestProduct, Finset.prod_mul_distrib]

/-- The generalized convolution attached to a family of cut tests. -/
noncomputable def generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) (z : G) : ℝ :=
  fiberConvolution r (cutTestProduct u) z

@[simp]
theorem generalizedConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (u : CutTestFamily G 0) (z : G) :
    generalizedConvolution 0 u z = zeroFiberDelta z := by
  simp [generalizedConvolution, cutTestProduct]

@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl

theorem fiberConvolution_smul
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (c : ℝ) (w : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => c * w x) z =
      c * fiberConvolution r w z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero]
      ring
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ]
      exact mean_smul c (fun y : Fin n → G =>
        w (sumFiberTuple n z y))

@[simp]
theorem fiberConvolution_zero_weight
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (z : G) :
    fiberConvolution r (fun _ => (0 : ℝ)) z = 0 := by
  simpa using fiberConvolution_smul r 0 (fun _ => (1 : ℝ)) z

@[simp]
theorem fiberConvolution_const_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (c : ℝ) (z : G) :
    fiberConvolution (n + 1) (fun _ => c) z = c := by
  rw [fiberConvolution_succ]
  exact mean_const c

@[simp]
theorem generalizedConvolution_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by
  rw [generalizedConvolution_succ]
  calc
    mean (fun y : Fin n → G =>
        cutTestProduct
          (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ))
          (sumFiberTuple n z y)) =
        mean (fun _ : Fin n → G => (1 : ℝ)) := by
      apply congrArg mean
      funext y
      exact cutTestProduct_one (sumFiberTuple n z y)
    _ = 1 := mean_const 1

@[simp]
theorem generalizedConvolution_zero_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (0 : ℝ)) z = 0 := by
  rw [generalizedConvolution_succ]
  simp [cutTestProduct]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean` -/

section
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise

/-- Normalized pairing on a finite probability space. -/
noncomputable def finitePairing
    {Ω : Type*} [Fintype Ω] (f q : Ω → ℝ) : ℝ :=
  mean (fun x => f x * q x)

theorem finitePairing_add_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f + g) q =
      finitePairing f q + finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_smul_left
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing (c • f) q = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Pointwise membership in the dense-model cube. -/
def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1

theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2

/-- Pairing with a fixed test as a linear functional. -/
noncomputable def finitePairingLinearMap
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := finitePairing f q
  map_add' f g := finitePairing_add_left f g q
  map_smul' c f := by
    simpa [smul_eq_mul] using finitePairing_smul_left c f q

/-- Pairing is continuous because its domain is finite-dimensional. -/
noncomputable def finitePairingCLM
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] ℝ :=
  (finitePairingLinearMap q).toContinuousLinearMap

@[simp]
theorem finitePairingCLM_apply
    {Ω : Type*} [Fintype Ω] (q f : Ω → ℝ) :
    finitePairingCLM q f = finitePairing f q :=
  rfl

/-- The vector of pairings against a finite family of tests. -/
noncomputable def finiteTestProfile
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] (τ → ℝ) :=
  ContinuousLinearMap.pi (fun t => finitePairingCLM (q t))

@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl

/-- Linear combination of a finite test family. -/
noncomputable def finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) : Ω → ℝ :=
  ∑ t, c t • q t

@[simp]
theorem finiteTestCombination_zero
    {Ω τ : Type*} [Fintype τ] (q : τ → Ω → ℝ) :
    finiteTestCombination q 0 = 0 := by
  classical
  ext x
  simp [finiteTestCombination]

/-- Pointwise positive part. -/
def positivePart {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => max (q x) 0

@[simp]
theorem positivePart_apply
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positivePart q x = max (q x) 0 :=
  rfl

@[simp]
theorem positivePart_of_nonneg
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : 0 ≤ q x) :
    positivePart q x = q x :=
  max_eq_left hx

@[simp]
theorem positivePart_of_nonpos
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : q x ≤ 0) :
    positivePart q x = 0 :=
  max_eq_right hx

@[simp]
theorem positivePart_zero {Ω : Type*} :
    positivePart (0 : Ω → ℝ) = 0 := by
  ext x
  simp [positivePart]

/-- The Boolean vertex of the unit cube which maximizes pairing with `q`. -/
noncomputable def positiveSupportIndicator
    {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => if 0 ≤ q x then 1 else 0

@[simp]
theorem positiveSupportIndicator_mul
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positiveSupportIndicator q x * q x =
      positivePart q x := by
  by_cases hx : 0 ≤ q x
  · simp [positiveSupportIndicator, positivePart, hx]
  · have hx' : q x ≤ 0 := le_of_not_ge hx
    simp [positiveSupportIndicator, positivePart, hx, hx']

/-- The pairing of the constant-one function is the mean. -/
@[simp]
theorem finitePairing_one_left
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (fun _ : Ω => (1 : ℝ)) q = mean q := by
  simp [finitePairing]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean` -/

section
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/

/-- Product of a finite sequence of tests.  The degree-zero monomial is the
constant-one function. -/
def testMonomial
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) : Ω → ℝ :=
  fun x => ∏ i, q (s i) x

@[simp]
theorem testMonomial_apply
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) (x : Ω) :
    testMonomial q s x = ∏ i, q (s i) x :=
  rfl

@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

/-! ## Bounded combinations and approximation of positive part -/

/-! ## Quantitative positive-part correlation -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean` -/

section
/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/

/-- Product Bernoulli weight of a Boolean assignment. -/
def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

/-- Real indicator of one bit of an assignment. -/
def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0

theorem bernoulliAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ bernoulliAssignmentWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using hp0 i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [hp1 i]

/-- Product Bernoulli weights sum to one. -/
theorem sum_bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp

/-- Bernoulli moment of a selected finite set of coordinates. -/
theorem sum_bernoulliAssignmentWeight_mul_selected
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (s : Finset κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i =
      ∏ i ∈ s, p i := by
  calc
    (∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i) =
        ∑ b : κ → Bool,
          ∏ i,
            (if b i then p i else 1 - p i) *
              (if i ∈ s then booleanValue b i else 1) := by
      apply Fintype.sum_congr
      intro b
      have hselected :
          (∏ i ∈ s, booleanValue b i) =
            ∏ i, if i ∈ s then booleanValue b i else 1 :=
        (Fintype.prod_ite_mem s
          (fun i => booleanValue b i)).symm
      rw [bernoulliAssignmentWeight, hselected]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ bit : Bool,
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∏ i ∈ s, p i := by
      exact Fintype.prod_ite_mem s p

/-- Bernoulli moment pulled back along an embedding. -/
theorem sum_bernoulliAssignmentWeight_mul_embedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i : ι, booleanValue b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (sum_bernoulliAssignmentWeight_mul_selected p
      (Finset.univ.map e))

/-! ## Boolean cut coordinates -/

/-- One scalar coordinate in a cut-test family. -/
abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

/-- A Boolean choice for every scalar coordinate of a cut-test family. -/
abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

/-- Regard a Boolean assignment as a `{0,1}`-valued cut-test family. -/
def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩

/-- Flatten a cut-test family to its finite vector of scalar coordinates. -/
def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

/-- The coordinates selected by one full tuple, as an embedding indexed by
the edge colour.  Injectivity is immediate from the colour component. -/
def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

/-- Exact Bernoulli mixture identity for one product of cut tests. -/
theorem cutTestProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) :
    cutTestProduct u x =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  symm
  simpa [cutTestProduct, cutTestCoordinateValue,
    cutTestFamilyOfBooleanAssignment,
    usedCutTestCoordinateEmbedding_apply] using
    (sum_bernoulliAssignmentWeight_mul_embedding
      (cutTestCoordinateValue u)
      (usedCutTestCoordinateEmbedding x))

/-! ## The finite dense-model test family -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakRegularity.lean` -/

section
/-!
# Weak regularity against lower-face cut tests

For a function on `Fin r → G`, the hypergraph cut tests are products of
`r` functions, with the `i`th factor omitting coordinate `i`.  A Boolean
cut-test family has a support in the full tuple space.  This file connects
those supports to the abstract energy-increment machinery and proves a
genuine finite weak-regularity lemma:

* the output refines the input partition;
* its complexity grows by an ambient-size-independent power of two;
* the residual is small against every `[0,1]`-valued lower-face cut test.

The passage from Boolean to bounded tests is an exact finite Bernoulli
mixture, not an approximation.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The full-tuple support of a Boolean lower-face cut-test family. -/
noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true

@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]

/-- The indicator of a Boolean cut support is exactly the corresponding
product of Boolean lower-face tests. -/
theorem booleanFaceCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, eraseCoordinate i x⟩ = true
  · have hx : x ∈ booleanFaceCutSupport b := by
      simp [booleanFaceCutSupport, h]
    rw [BooleanCutTest.eval_of_mem _ hx]
    unfold cutTestProduct
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [cutTestFamilyOfBooleanAssignment, booleanValue, h i]
  · have hx : x ∉ booleanFaceCutSupport b := by
      simpa [booleanFaceCutSupport] using h
    rw [BooleanCutTest.eval_of_not_mem _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, eraseCoordinate i x⟩ with
    | false =>
        unfold cutTestProduct
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [cutTestFamilyOfBooleanAssignment,
          booleanValue, hb]
    | true =>
        exact (hi hb).elim

/-- The finite family of all Boolean lower-face cut supports. -/
noncomputable def booleanFaceCutSupports
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ) :
    Finset (BooleanCutTest (Fin r → G)) := by
  classical
  exact Finset.univ.image booleanFaceCutSupport

namespace FaceRegularityState

/-- Correlation of a regularity residual with a lower-face product test. -/
noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x

/-- On Boolean tests, face-cut correlation is the existing Boolean support
correlation used by the energy increment. -/
theorem faceCutCorrelation_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : BooleanCutAssignment G r) :
    S.faceCutCorrelation f
        (cutTestFamilyOfBooleanAssignment b) =
      S.booleanCutCorrelation f (booleanFaceCutSupport b) := by
  unfold faceCutCorrelation booleanCutCorrelation
  apply congrArg mean
  funext x
  rw [booleanFaceCutSupport_eval]

/-- Exact Bernoulli-mixture formula for one face-cut correlation. -/
theorem faceCutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold faceCutCorrelation
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cutTestProduct u x) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      rw [cutTestProduct_eq_sum_boolean u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : BooleanCutAssignment G r,
          mean (fun x : Fin r → G =>
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

/-- Weak cut regularity of one face function. -/
def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε

end FaceRegularityState

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FamilyRegularity.lean` -/

section
/-!
# Simultaneous weak regularity for a finite family

The all-rank hypergraph regularity argument must regularize every atom of a
bounded-complexity partition, not merely the original edge indicator.  This
file supplies the finite-family energy-increment engine needed for that step.

For a family `f : ι → Ω → ℝ`, the potential is the sum of the partition
energies of all `f i`.  It lies between zero and `Fintype.card ι` when every
target is `[0,1]`-valued.  If any target has a Boolean-cut correlation larger
than `ε`, adjoining that cut increases its energy by at least `ε ^ 2`, while
monotonicity shows that every other summand can only increase.  Thus a common
refinement regular for the whole family is reached in fewer than any `m`
with

`Fintype.card ι < m * ε ^ 2`.

As in `Regularity.lean`, the canonical run records its actual generators.
The last theorem specializes the abstract result to lower-face product tests,
which is the form used by the forthcoming shared-skeleton regularity system.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]
  [Fintype ι] [DecidableEq ι]

namespace FaceRegularityState

/-- One state is regular for a family when it is regular for every member. -/
def IsFamilyRegularAgainst
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) : Prop :=
  ∀ i, S.IsRegularAgainst (f i) cuts ε

/-- Failure of family regularity identifies both a target and a violating
Boolean cut. -/
theorem exists_index_booleanCut_of_not_familyRegular
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι, ∃ A ∈ cuts,
      ε < |S.booleanCutCorrelation (f i) A| := by
  classical
  unfold IsFamilyRegularAgainst at h
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨A, hA, hcorr⟩ :=
    S.exists_booleanCut_of_not_regular (f i) cuts hi
  exact ⟨i, A, hA, hcorr⟩

/-- Data attached to a failure of simultaneous regularity. -/
structure FamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) where
  index : ι
  cut : BooleanCutTest Ω
  mem_cuts : cut ∈ cuts
  correlation :
    ε < |S.booleanCutCorrelation (f index) cut|

/-- Choose one violating target/cut pair from a failed family-regularity
statement. -/
noncomputable def chosenFamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.FamilyIrregularWitness f cuts ε := by
  classical
  let hex :=
    S.exists_index_booleanCut_of_not_familyRegular f cuts h
  let i : ι := Classical.choose hex
  let hi := Classical.choose_spec hex
  let A : BooleanCutTest Ω := Classical.choose hi
  have hA :=
    (Classical.choose_spec hi).1
  have hcorr :=
    (Classical.choose_spec hi).2
  exact ⟨i, A, hA, hcorr⟩

/-- Select a violating cut for the family.  Once regularity has been reached,
the empty cut is used so that the iteration remains total. -/
noncomputable def chosenFamilyIrregularCut
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsFamilyRegularAgainst f cuts ε then ∅
    else (S.chosenFamilyIrregularWitness f cuts ε h).cut

/-- Canonical common refinement run for a finite family. -/
noncomputable def familyRegularityRun
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := familyRegularityRun S f cuts ε n
      T.refineBy (T.chosenFamilyIrregularCut f cuts ε)

@[simp]
theorem familyRegularityRun_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem familyRegularityRun_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRun f cuts ε (n + 1) =
      (S.familyRegularityRun f cuts ε n).refineBy
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε) :=
  rfl

/-- The finite set of cuts adjoined during the first `n` family steps. -/
noncomputable def familyRegularityRunCuts
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.familyRegularityRun f cuts ε i).chosenFamilyIrregularCut
      f cuts ε

@[simp]
theorem familyRegularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRunCuts f cuts ε 0 = ∅ := by
  simp [familyRegularityRunCuts]

@[simp]
theorem familyRegularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε)
        (S.familyRegularityRunCuts f cuts ε n) := by
  classical
  simp [familyRegularityRunCuts, Finset.range_add_one]

end FaceRegularityState

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GeneratorCells.lean` -/

section
/-!
# Lower-face cells generated by weak-regularity cuts

A cut used by simplex weak regularity is the support of a product of
Boolean predicates on the codimension-one faces.  An atom generated by
finitely many such cuts is therefore a finite union of cells which factor
over those lower faces.

This file makes that statement exact.  For a generator which contains the
reference tuple, every lower-face predicate must be true.  For a generator
which does not contain it, a branch records one coordinate at which the
predicate is false.  There are at most `r ^ |F|` branches, independently of
the size of the ambient vertex class.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A chosen Boolean lower-face assignment representing a cut support.
Outside the canonical family of cut supports it defaults to the constantly
false assignment. -/
noncomputable def representingBooleanFaceCutAssignment
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ)
    (A : BooleanCutTest (Fin r → G)) :
    BooleanCutAssignment G r := by
  classical
  exact
    if hA : A ∈ booleanFaceCutSupports G r then
      Classical.choose
        (show ∃ b : BooleanCutAssignment G r,
            booleanFaceCutSupport b = A by
          obtain ⟨b, _hb, hsupport⟩ :=
            Finset.mem_image.mp hA
          exact ⟨b, hsupport⟩)
    else
      fun _ => false

/-- One branch chooses a failed lower face for every negative generator. -/
abbrev GeneratorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :=
  F → Fin r

@[simp]
theorem card_generatorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :
    Fintype.card (GeneratorBranch F) = r ^ F.card := by
  simp [GeneratorBranch]

/-- The lower-face cell at coordinate `i` for a reference tuple and a
branch.  Positive generators impose their predicate at every coordinate;
a negative generator imposes failure at the coordinate selected by the
branch. -/
noncomputable def lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r) :
    BooleanCutTest (Fin (r - 1) → G) := by
  classical
  exact Finset.univ.filter fun z =>
    ∀ A : F,
      (y ∈ A.1 →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = true) ∧
      (y ∉ A.1 → w A = i →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = false)

@[simp]
theorem mem_lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r)
    (z : Fin (r - 1) → G) :
    z ∈ lowerGeneratorCell F y w i ↔
      ∀ A : F,
        (y ∈ A.1 →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = true) ∧
        (y ∉ A.1 → w A = i →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = false) := by
  simp [lowerGeneratorCell]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPattern.lean` -/

section
/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The increasing rank-`r` face among `k` vertex classes with a specified
canonical order. -/
abbrev OrderedFace (k r : ℕ) :=
  Fin r ↪o Fin k

instance orderedFaceDecidableEq
    (k r : ℕ) : DecidableEq (OrderedFace k r) :=
  Function.Injective.decidableEq
    (f := fun e : OrderedFace k r => (e : Fin r → Fin k))
    DFunLike.coe_injective

/-- Restrict a full labelled tuple along an ordered face. -/
def orderedFaceTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)

/-- Vertex coordinates outside an ordered face. -/
abbrev OrderedFaceComplement
    {k r : ℕ} (e : OrderedFace k r) :=
  {v : Fin k // v ∉ Set.range e}

/-- Split the full vertex index into an ordered face and its complement. -/
noncomputable def orderedFaceSumEquiv
    {k r : ℕ} (e : OrderedFace k r) :
    Fin r ⊕ OrderedFaceComplement e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (OrderedFaceComplement e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))

/-- Split a full tuple into its values on an ordered face and on the
complementary vertex coordinates. -/
noncomputable def splitOrderedFaceEquiv
    {G : Type*} {k r : ℕ} (e : OrderedFace k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (OrderedFaceComplement e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (orderedFaceSumEquiv e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ OrderedFaceComplement e => G))

@[simp]
theorem splitOrderedFaceEquiv_fst
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).1 =
      orderedFaceTuple e x := by
  funext i
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceTuple]
  rfl

/-- Restrict a full tuple to the complementary vertex coordinates. -/
def orderedFaceComplementTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    OrderedFaceComplement e → G :=
  fun v => x v.1

@[simp]
theorem splitOrderedFaceEquiv_snd
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).2 =
      orderedFaceComplementTuple e x := by
  funext v
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceComplementTuple]

@[simp]
theorem orderedFaceTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = y := by
  rw [← splitOrderedFaceEquiv_fst]
  simp

@[simp]
theorem orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceComplementTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = z := by
  rw [← splitOrderedFaceEquiv_snd]
  simp

/-- Fubini decomposition of a full-tuple mean into an ordered face and its
complement. -/
theorem mean_splitOrderedFace
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : OrderedFace k r) (f : (Fin k → G) → ℝ) :
    mean f =
      mean₂ (fun y : Fin r → G =>
        fun z : OrderedFaceComplement e → G =>
          f ((splitOrderedFaceEquiv e).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          (Fin r → G) × (OrderedFaceComplement e → G) =>
            f ((splitOrderedFaceEquiv e).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitOrderedFaceEquiv e)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : Fin r → G =>
            fun z : OrderedFaceComplement e → G =>
              f ((splitOrderedFaceEquiv e).symm (y, z))))

/-- A weighted complete ordered rank-`r` pattern. -/
structure WeightedOrderedPattern
    (G : Type*) (k r : ℕ) where
  edgeWeight : OrderedFace k r → (Fin r → G) → ℝ

namespace WeightedOrderedPattern

/-- Product of all ordered face weights on a labelled full tuple. -/
noncomputable def patternWeight
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : OrderedFace k r,
    H.edgeWeight e (orderedFaceTuple e x)

/-- Normalized density of labelled pattern occurrences. -/
noncomputable def patternCount
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : ℝ :=
  mean H.patternWeight

end WeightedOrderedPattern

/-- A predicate-valued complete ordered rank-`r` pattern. -/
structure OrderedPattern
    (G : Type*) (k r : ℕ) where
  edge : OrderedFace k r → (Fin r → G) → Prop

namespace OrderedPattern

/-- A labelled full tuple satisfies every ordered edge predicate. -/
def IsOccurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (orderedFaceTuple e x)

/-- The finite set of labelled occurrences. -/
noncomputable def occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.IsOccurrence

@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

/-- Regard predicates as zero-one edge weights. -/
noncomputable def toWeighted
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    WeightedOrderedPattern G k r := by
  classical
  exact
    { edgeWeight := fun e y =>
        if H.edge e y then 1 else 0 }

/-- An occurrence has zero-one pattern weight one. -/
theorem toWeighted_patternWeight_of_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 1 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  apply Finset.prod_eq_one
  intro e _he
  simp [toWeighted, hx e]

/-- A nonoccurrence has zero-one pattern weight zero. -/
theorem toWeighted_patternWeight_of_not_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 0 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [toWeighted, he]

/-- The weighted normalized count is exactly the normalized cardinality of
the occurrence finset. -/
theorem toWeighted_patternCount_eq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.patternCount =
      (H.occurrenceFinset.card : ℝ) /
        Fintype.card (Fin k → G) := by
  rw [WeightedOrderedPattern.patternCount]
  have hfun :
      H.toWeighted.patternWeight =
        finsetIndicator H.occurrenceFinset := by
    funext x
    by_cases hx : H.IsOccurrence x
    · rw [H.toWeighted_patternWeight_of_occurrence hx,
        finsetIndicator_of_mem]
      exact (H.mem_occurrenceFinset x).2 hx
    · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
        finsetIndicator_of_not_mem]
      exact fun hmem =>
        hx ((H.mem_occurrenceFinset x).1 hmem)
  rw [hfun, mean_finsetIndicator]

/-- One deleted rank-`r` face set for every ordered face. -/
abbrev DeletionFamily
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : OrderedFace k r) → Finset (Fin r → G)

/-- Every original occurrence meets at least one deleted ordered face. -/
def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (D : DeletionFamily (G := G) k r) : Prop :=
  ∀ x, x ∈ H.occurrenceFinset →
    ∃ e, orderedFaceTuple e x ∈ D e

/-- Normalized density of the deletion in one ordered face. -/
noncomputable def faceDeletionDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k r)
    (e : OrderedFace k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)

/-- Empty ordered deletion family. -/
def emptyDeletion
    {G : Type*} [DecidableEq G] (k r : ℕ) :
    DeletionFamily (G := G) k r :=
  fun _ => ∅

@[simp]
theorem faceDeletionDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (e : OrderedFace k r) :
    faceDeletionDensity
        (emptyDeletion (G := G) k r) e = 0 := by
  simp [faceDeletionDensity, emptyDeletion]

end OrderedPattern

/-- Uniform per-ordered-face removal for complete ordered rank-`r`
patterns on `k` equal finite vertex classes. -/
def HasUniformOrderedPatternRemoval (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/Count.lean` -/

section
/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The `j`th term of a cyclic arithmetic progression. -/
def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

/-- The weight contributed by one cyclic `k`-term progression. -/
def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

/-- The normalized weighted count of cyclic `k`-term progressions. The
average includes the diagonal `d = 0`. -/
noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

theorem cyclicAPProduct_nonneg {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cyclicAPProduct k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (cyclicAPTerm a d j)

@[simp]
theorem cyclicAPProduct_const (k N : ℕ) (c : ℝ) (a d : ZMod N) :
    cyclicAPProduct k N (fun _ => c) a d = c ^ k := by
  simp [cyclicAPProduct]

@[simp]
theorem cyclicAPCount_const (k N : ℕ) [NeZero N] (c : ℝ) :
    cyclicAPCount k N (fun _ => c) = c ^ k := by
  simp [cyclicAPCount, mean₂]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/LinearForms/Basic.lean` -/

section
/-!
# Affine forms and the arithmetic-progression linear-forms system

The relative Szemerédi theorem uses one specific family of linear forms.  For
`j < k` and a vertex `ω` of the cube with the `j`th coordinate deleted, the
form is

`ψ_{j,ω}(x) = ∑ i ≠ j, (i - j) * xᵢ^(ωᵢ)`.

The quantitative predicate at the end of this file says that every
subproduct of these `k * 2^(k-1)` forms has normalized average within `η` of
one.  Encoding subproducts by Boolean exponents exactly matches the
Conlon--Fox--Zhao linear-forms condition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finitely supported affine form, represented by all of its coefficients
on a finite index type. -/
structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

/-- Evaluate an affine form at a vector. -/
def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i

@[simp]
theorem eval_zero {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) :
    ψ.eval (fun _ => 0) = ψ.constant := by
  simp [eval]

end AffineForm

/-- A point carrying two independent values in every one of `k`
coordinates. -/
abbrev CubePoint (k N : ℕ) :=
  Fin k → Bool → ZMod N

/-- A Boolean vertex of the `(k-1)`-cube obtained by deleting coordinate
`j`. -/
abbrev DeletedCube (k : ℕ) (j : Fin k) :=
  {i : Fin k // i ≠ j} → Bool

/-- The Conlon--Fox--Zhao form indexed by `j` and `ω`. -/
def apLinearForm (k N : ℕ) (j : Fin k) (ω : DeletedCube k j)
    (x : CubePoint k N) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i.1 (ω i)

/-- Boolean choices of the subproduct of the arithmetic-progression linear-forms
system to be tested. -/
abbrev LinearFormsExponent (k : ℕ) :=
  (j : Fin k) → DeletedCube k j → Bool

/-- The subproduct selected by `e`, evaluated at the doubled variable
vector `x`. -/
def linearFormsProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (e : LinearFormsExponent k) (x : CubePoint k N) : ℝ :=
  ∏ j : Fin k, ∏ ω : DeletedCube k j,
    if e j ω then ν (apLinearForm k N j ω x) else 1

/-- Quantitative `k`-linear-forms condition.

Every subproduct of the canonical arithmetic-progression forms must have
normalized average within `η` of one. -/
def HasLinearFormsCondition (k N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (η : ℝ) : Prop :=
  ∀ e : LinearFormsExponent k,
    |mean (linearFormsProduct k N ν e) - 1| ≤ η

theorem HasLinearFormsCondition.mono {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η η' : ℝ}
    (hν : HasLinearFormsCondition k N ν η) (hη : η ≤ η') :
    HasLinearFormsCondition k N ν η' :=
  fun e => (hν e).trans hη

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Simplex.lean` -/

section
/-!
# Partite weighted simplices

The dense and relative Szemerédi arguments are organized as counting lemmas
for a `(k-1)`-uniform, `k`-partite simplex.  An edge of colour `j` depends on
every vertex coordinate except `j`.  Keeping that dependency in the type
prevents accidental use of the omitted coordinate and matches the dependent
index used by the CFZ blow-up forms.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A vector with coordinate `j` deleted. -/
abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

/-- Delete coordinate `j` from a dependent vector. -/
def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

/-- A weighted `(k-1)`-uniform, `k`-partite hypergraph. -/
structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

namespace WeightedSimplexSystem

/-- Product of the `k` edge weights on a labelled simplex. -/
def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

/-- Normalized count of labelled weighted simplices. -/
noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight

end WeightedSimplexSystem

/-- The one-copy arithmetic-progression form attached to edge `j`. -/
def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

/-- Sum of all simplex coordinates.  It becomes the common difference,
up to sign, in the encoded progression. -/
def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

/-- First moment of the simplex coordinates.  It becomes the initial term
of the encoded progression. -/
def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

/-- The edge form is the first moment minus `j` times the coordinate sum.
Consequently, the `k` edge values of one simplex form a cyclic arithmetic
progression. -/
theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The weighted simplex system whose simplices encode arithmetic
progressions. -/
def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)

/-- A labelled simplex in the AP system contributes exactly the weight of
the cyclic progression with initial term the coordinate moment and common
difference the negative coordinate sum. -/
theorem apSimplexSystem_simplexWeight
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (apSimplexForm k N j (deleteCoordinate x j)) =
      f (cyclicAPTerm
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) j)
  congr 1
  rw [apSimplexForm_deleteCoordinate]
  simp [cyclicAPTerm]
  ring

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/APCorrespondence.lean` -/

section
/-!
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Sum of the free coordinates in a fiber of the AP parameter map. -/
def simplexTailSum (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i

/-- First moment of the free coordinates, using their actual positions
`2, ..., r + 1` in the full simplex vector. -/
def simplexTailMoment (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i

/-- Reconstruct simplex coordinates from a cyclic initial term `a`, common
difference `d`, and the remaining `r` free coordinates. -/
def simplexCoordinatesOfAP (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (simplexTailMoment r N y - a - d - simplexTailSum r N y)
    (Fin.cases (a - simplexTailMoment r N y) y)

@[simp]
theorem simplexCoordinatesOfAP_zero (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 0 =
      simplexTailMoment r N y - a - d - simplexTailSum r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_one (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 1 =
      a - simplexTailMoment r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_succ_succ (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    simplexCoordinatesOfAP r N a d y i.succ.succ = y i :=
  rfl

/-- Split the coordinate sum into the first two and the free tail. -/
theorem simplexCoordinateSum_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateSum (r + 2) N x =
      x 0 + x 1 +
        simplexTailSum r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateSum, simplexTailSum, Fin.sum_univ_succ,
    add_assoc]

/-- Split the coordinate moment into coordinate one and the free tail;
coordinate zero has coefficient zero. -/
theorem simplexCoordinateMoment_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateMoment (r + 2) N x =
      x 1 + simplexTailMoment r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateMoment, simplexTailMoment,
    Fin.sum_univ_succ]

@[simp]
theorem simplexCoordinateSum_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateSum (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = -d := by
  rw [simplexCoordinateSum_decompose]
  simp
  ring

@[simp]
theorem simplexCoordinateMoment_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateMoment (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = a := by
  rw [simplexCoordinateMoment_decompose]
  simp

/-- The exact coordinate change: AP parameters, together with `r` free
coordinates, are equivalent to simplex coordinates of length `r + 2`. -/
def simplexAPEquiv (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((simplexCoordinateMoment (r + 2) N x,
      -simplexCoordinateSum (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := simplexCoordinatesOfAP r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [simplexCoordinatesOfAP_zero,
        simplexCoordinateMoment_decompose,
        simplexCoordinateSum_decompose]
      ring
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [simplexCoordinatesOfAP_one,
        simplexCoordinateMoment_decompose]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          simplexCoordinateMoment (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            a
        exact simplexCoordinateMoment_coordinatesOfAP r N a d tail
      · change
          -simplexCoordinateSum (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            d
        rw [simplexCoordinateSum_coordinatesOfAP]
        simp
    · funext i
      change simplexCoordinatesOfAP r N a d tail i.succ.succ = tail i
      exact simplexCoordinatesOfAP_succ_succ r N a d tail i

/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

/-- A normalized average over a product is the corresponding iterated
normalized average. -/
theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

/-- Averaging a function that ignores a nonempty product coordinate does
not change its normalized average. -/
theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]

/-- Exact normalized AP/simplex count correspondence.  The extra `r`
simplex coordinates form a uniform fiber over every pair `(a, d)`, so
normalization removes that fiber with no cardinality factor. -/
theorem apSimplexSystem_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by
  rw [WeightedSimplexSystem.simplexCount, cyclicAPCount]
  calc
    mean (apSimplexSystem (r + 2) N f).simplexWeight =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cyclicAPProduct (r + 2) N f
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact apSimplexSystem_simplexWeight (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cyclicAPProduct (r + 2) N f y.1.1 y.1.2) := by
      apply mean_equiv (simplexAPEquiv r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2) := by
      exact mean_prod_fst
        (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2)
    _ =
        mean₂ (fun a d =>
          cyclicAPProduct (r + 2) N f a d) := by
      exact mean_prod
        (fun a d => cyclicAPProduct (r + 2) N f a d)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutTransport.lean` -/

section
/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Multiplication by a unit, regarded only as an additive automorphism. -/
noncomputable def mulAddEquivOfIsUnit
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a) :
    R ≃+ R :=
  DistribMulAction.toAddEquiv R ha.unit

@[simp]
theorem mulAddEquivOfIsUnit_apply
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a)
    (x : R) :
    mulAddEquivOfIsUnit a ha x = a * x := by
  change (ha.unit : R) * x = a * x
  rw [IsUnit.unit_spec]

/-- Apply an additive automorphism independently in every coordinate. -/
def coordinatewiseAddEquiv
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G) :
    (ι → G) ≃ (ι → G) where
  toFun x i := e i (x i)
  invFun x i := (e i).symm (x i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (e i).apply_symm_apply (x i)

@[simp]
theorem coordinatewiseAddEquiv_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    coordinatewiseAddEquiv e x i = e i (x i) :=
  rfl

@[simp]
theorem coordinatewiseAddEquiv_symm_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    (coordinatewiseAddEquiv e).symm x i =
      (e i).symm (x i) :=
  rfl

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/APCut.lean` -/

section
/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Every nonzero AP coefficient is a unit modulo a modulus coprime to
`(k-1)!`. -/
theorem apCoefficient_isUnit_of_coprime_factorial
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    IsUnit (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime]
  have hdiff :
      (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos :
      0 < Int.natAbs ((i : ℤ) - (j : ℤ)) :=
    Int.natAbs_pos.mpr hdiff
  have hle :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k - 1 := by
    have hi : (i : ℕ) ≤ k - 1 := by omega
    have hj : (j : ℕ) ≤ k - 1 := by omega
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have hdvd :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ∣
        Nat.factorial (k - 1) :=
    Nat.dvd_factorial hpos hle
  simpa using hN.coprime_dvd_right hdvd

/-- Multiplication by one AP coefficient as an additive automorphism. -/
noncomputable def apCoefficientAddEquiv
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    ZMod N ≃+ ZMod N :=
  mulAddEquivOfIsUnit
    ((((i : ℤ) - (j : ℤ) : ℤ) : ZMod N))
    (apCoefficient_isUnit_of_coprime_factorial hN i j hij)

@[simp]
theorem apCoefficientAddEquiv_apply
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) (x : ZMod N) :
    apCoefficientAddEquiv hN i j hij x =
      (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x := by
  simp [apCoefficientAddEquiv]

/-- `Fin n` is canonically equivalent to the coordinates of `Fin (n+1)`
other than `j`. -/
noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl

/-- Convert an ordinary `Fin n` tuple to the dependent deleted-coordinate
tuple for colour `j`. -/
noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]

/-- The coordinate automorphisms attached to one AP face. -/
noncomputable def apFaceScalingEquiv
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) :
    ZMod N ≃+ ZMod N :=
  apCoefficientAddEquiv
    (by simpa using hN) (j.succAbove t) j
    (Fin.succAbove_ne j t)

@[simp]
theorem apFaceScalingEquiv_apply
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) (x : ZMod N) :
    apFaceScalingEquiv hN j t x =
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * x) := by
  simp [apFaceScalingEquiv]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean` -/

section
/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/APSimplexCut.lean` -/

section
/-!
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The factors other than colour `j` in the ordered telescoping term.
The first factor selects the old weight below `j`; the second selects the
new weight above `j`.  At `i = j` both factors are one. -/
def orderedAPEdgeFactor
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j i : Fin k) (x : Fin k → ZMod N) : ℝ :=
  (if i < j then
      f (apSimplexForm k N i (deleteCoordinate x i))
    else 1) *
  (if j < i then
      g (apSimplexForm k N i (deleteCoordinate x i))
    else 1)

@[simp]
theorem orderedAPEdgeFactor_self
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin k) (x : Fin k → ZMod N) :
    orderedAPEdgeFactor k N f g j j x = 1 := by
  simp [orderedAPEdgeFactor]

/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*} [DecidableEq G]
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexCounting.lean` -/

section
/-!
# Stable weighted simplex counts

Relative counting will eventually use cut discrepancy and densification.
This file records the elementary endpoint: uniformly close edge weights in
`[0,1]` have close simplex counts.  The proof is the finite telescoping
estimate for products, followed by averaging.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakCounting.lean` -/

section
/-!
# Weak-regularity counting for simplex systems

Each deleted face of a simplex with `n+1` colours is canonically presented as
an ordinary `Fin n → G` tuple.  A family of regularity states therefore gives
a structured simplex system by conditionally averaging every edge weight.

The main result is an exact weak counting lemma.  If every edge residual is
small against lower-face product cuts, then the original and structured
simplex counts differ by at most `(n+1) ε`.  The proof fixes the missing
vertex in one telescoping term; the remaining edge factors become precisely a
bounded cut-test family on the distinguished edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Canonical `Fin n` presentation of a dependent deleted-coordinate
vector. -/
noncomputable def deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedFaceTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedFaceTuple j (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedFaceTuple]

@[simp]
theorem finTupleToDeletedVector_deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j (deletedFaceTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
      ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

@[simp]
theorem deletedFaceTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedFaceTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

/-- Reparameterize one edge weight by the canonical `Fin n` face tuple. -/
noncomputable def canonicalEdgeFunction
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)

/-- A regularity state for every edge colour. -/
abbrev SimplexRegularitySystem
    (G : Type*) (n : ℕ)
    [Fintype G] [DecidableEq G] :=
  (j : Fin (n + 1)) →
    FaceRegularityState (Fin n → G)

/-- Replace every edge weight by its conditional mean in the corresponding
regularity state. -/
noncomputable def regularizedSimplexSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) :
    WeightedSimplexSystem (fun _ : Fin (n + 1) => G) where
  edgeWeight j x :=
    (S j).structured (canonicalEdgeFunction H j)
      (deletedFaceTuple j x)

@[simp]
theorem regularizedSimplexSystem_edge_finTuple
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) (y : Fin n → G) :
    (regularizedSimplexSystem H S).edgeWeight j
        (finTupleToDeletedVector j y) =
      (S j).structured (canonicalEdgeFunction H j) y := by
  simp [regularizedSimplexSystem]

/-- The non-distinguished factors in an ordered simplex telescoping term. -/
def orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j i : Fin k) (x : Fin k → G) : ℝ :=
  (if i < j then H.edgeWeight i (deleteCoordinate x i) else 1) *
  (if j < i then K.edgeWeight i (deleteCoordinate x i) else 1)

@[simp]
theorem orderedSimplexEdgeFactor_self
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    orderedSimplexEdgeFactor H K j j x = 1 := by
  simp [orderedSimplexEdgeFactor]

/-- Insert the omitted coordinate into a tuple presented with the
subtraction-based arity used by `eraseCoordinate`. -/
def insertErasedCoordinate
    {G : Type*} {n : ℕ} (t : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    Fin n → G := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => exact Fin.insertNth t a z

@[simp]
theorem insertErasedCoordinate_eraseCoordinate
    {G : Type*} [DecidableEq G] {n : ℕ}
    (t : Fin n) (a : G) (y : Fin n → G) :
    insertErasedCoordinate t a (eraseCoordinate t y) =
      Function.update y t a := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m =>
      exact insertNth_eraseCoordinate_eq_update t a y

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedCounting.lean` -/

section
/-!
# Weak counting for complete ordered patterns

The simplex counting lemma handles the codimension-one pattern with one
edge for each missing vertex.  Recursive hypergraph removal also needs the
same argument for every complete ordered rank-`r` pattern on `k` vertex
classes.

The central point is combinatorial.  If `e` and `f` are distinct increasing
rank-`r` faces, some vertex of `e` is absent from `f`.  After all coordinates
outside `e` are fixed, the `f`-edge factor therefore omits one coordinate of
the `e`-tuple and is a valid cut-test factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A fixed enumeration order for the finite type of increasing faces.  The
particular order is irrelevant; it only chooses a telescoping order. -/
noncomputable local instance orderedFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) := by
  classical
  exact (Fintype.equivFin (OrderedFace k r)).linearOrder

/-- A weak-regularity state for every ordered rank-`r` face. -/
abbrev OrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :=
  (e : OrderedFace k r) →
    FaceRegularityState (Fin r → G)

/-- Replace each ordered edge weight by its conditional mean in the
corresponding regularity state. -/
noncomputable def regularizedOrderedPattern
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    WeightedOrderedPattern G k r where
  edgeWeight e :=
    (S e).structured (H.edgeWeight e)

@[simp]
theorem regularizedOrderedPattern_edgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    (regularizedOrderedPattern H S).edgeWeight e y =
      (S e).structured (H.edgeWeight e) y :=
  rfl

/-- The non-distinguished factor in an ordered product-telescoping term. -/
noncomputable def orderedPatternEdgeFactor
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e f : OrderedFace k r) (x : Fin k → G) : ℝ :=
  (if f < e then
      H.edgeWeight f (orderedFaceTuple f x)
    else 1) *
    (if e < f then
      K.edgeWeight f (orderedFaceTuple f x)
    else 1)

@[simp]
theorem orderedPatternEdgeFactor_self
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) :
    orderedPatternEdgeFactor H K e e x = 1 := by
  simp [orderedPatternEdgeFactor]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRegularizedCells.lean` -/

section
/-!
# Generator-retaining regularization for complete ordered patterns

This packages simultaneous weak regularization of every increasing
rank-`r` face on `k` vertex classes.  Besides the counting conclusion, it
retains the Boolean face-cut generators.  Consequently every structured
top atom is an explicit union of products of rank-`r - 1` cells.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The indiscrete regularity state on every ordered face. -/
def indiscreteOrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :
    OrderedRegularitySystem G k r :=
  fun _ => ⟨FacePartition.indiscrete⟩

@[simp]
theorem indiscreteOrderedRegularitySystem_partition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (e : OrderedFace k r) :
    (indiscreteOrderedRegularitySystem G k r e).partition =
      FacePartition.indiscrete :=
  rfl

/-- Simultaneous regularization data for all ordered faces, including the
actual lower-face generators. -/
structure GeneratedOrderedPatternRegularization
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (H : WeightedOrderedPattern G k r)
    (ε : ℝ) where
  state : OrderedRegularitySystem G k r
  generators :
    (e : OrderedFace k r) →
      Finset (BooleanCutTest (Fin r → G))
  budgetLength : OrderedFace k r → ℕ
  stepIndex : OrderedFace k r → ℕ
  budget_large :
    ∀ e, 1 < (budgetLength e : ℝ) * ε ^ 2
  step_lt_budget :
    ∀ e, stepIndex e < budgetLength e
  partition_eq_generated :
    ∀ e, (state e).partition =
      FacePartition.generatedBy (generators e)
  generators_supported :
    ∀ e, generators e ⊆ booleanFaceCutSupports G r
  generator_card_le :
    ∀ e, (generators e).card ≤ stepIndex e
  regular :
    ∀ e, (state e).IsFaceCutRegular
      (H.edgeWeight e) ε
  count_close :
    |H.patternCount -
        (regularizedOrderedPattern H state).patternCount| ≤
      (Fintype.card (OrderedFace k r) : ℝ) * ε
  complexity_le :
    ∀ e, FacePartition.complexity (state e).partition ≤
      2 ^ stepIndex e

namespace GeneratedOrderedPatternRegularization

/-- A simultaneous lower-face branch choice for every ordered top face. -/
abbrev BranchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    GeneratorBranch (R.generators e)

@[simp]
theorem card_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.BranchSystem =
      ∏ e : OrderedFace k r,
        r ^ (R.generators e).card := by
  simp [BranchSystem]

/-- One structured atom choice for every ordered top face. -/
abbrev TopAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    (R.state e).partition.parts

@[simp]
theorem card_topAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.TopAtomChoice =
      ∏ e : OrderedFace k r,
        FacePartition.complexity
          (R.state e).partition := by
  simp [TopAtomChoice, FacePartition.complexity]

end GeneratedOrderedPatternRegularization

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Unweighted.lean` -/

section
/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- An unweighted `(k - 1)`-uniform, `k`-partite hypergraph. -/
structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph

/-- The finite set of edges of one colour. -/
noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    Finset (DeletedVector V j) := by
  classical
  exact Finset.univ.filter (H.edge j)

@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k)
    (x : DeletedVector V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]

/-- The finite set of labelled simplices. -/
noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

/-- Regard an unweighted hypergraph as a zero-one weighted system. -/
noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }

@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]

/-- A zero-one simplex weight is exactly the indicator of the labelled
simplex finset. -/
theorem toWeighted_simplexWeight_eq_indicator {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by
  classical
  by_cases hx : x ∈ H.simplexFinset
  · have hedges :
        ∀ j, H.edge j (deleteCoordinate x j) :=
      (H.mem_simplexFinset x).mp hx
    simp [WeightedSimplexSystem.simplexWeight, toWeighted,
      finsetIndicator, hx, hedges]
  · have hnot :
        ¬∀ j, H.edge j (deleteCoordinate x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.toWeighted.edgeWeight i (deleteCoordinate x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact toWeighted_edgeWeight_of_not_edge H hj
    rw [WeightedSimplexSystem.simplexWeight, hzero]
    exact (finsetIndicator_of_not_mem hx).symm

/-- The normalized weighted count is the number of labelled simplices divided
by the size of the ambient product. -/
theorem toWeighted_simplexCount_eq_card_div {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) :
    H.toWeighted.simplexCount =
      (H.simplexFinset.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [WeightedSimplexSystem.simplexCount]
  have hfun :
      H.toWeighted.simplexWeight =
        finsetIndicator H.simplexFinset := by
    funext x
    exact toWeighted_simplexWeight_eq_indicator H x
  rw [hfun, mean_finsetIndicator]

/-- A family of deleted edge sets meets every labelled simplex. -/
def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j

end SimplexHypergraph

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Removal.lean` -/

section
/-!
# Finite deletion framework for simplex removal

This file supplies the finite combinatorial interface surrounding the deep
hypergraph-removal argument.  A deletion family consists of one finite set of
deleted faces for each colour.  We construct the surviving hypergraph, prove
that covers are exactly the deletion families with no surviving simplex, and
develop monotonicity, cost normalization, trimming, canonical covers, and
existence of a minimum finite cover.

No quantitative hypergraph-removal theorem is asserted here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace SimplexHypergraph

/-- One finite set of deleted faces for each edge colour. -/
abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)

/-- Delete a family of faces from an unweighted simplex hypergraph. -/
noncomputable def deleteEdges {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    SimplexHypergraph V := by
  classical
  exact
    { edge := fun j x => H.edge j x ∧ x ∉ deleted j }

@[simp]
theorem deleteEdges_edge {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) (x : DeletedVector V j) :
    (H.deleteEdges deleted).edge j x ↔
      H.edge j x ∧ x ∉ deleted j := by
  classical
  simp [deleteEdges]

/-- Exact description of the labelled simplices surviving a deletion. -/
@[simp]
theorem mem_deleteEdges_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (x : (i : Fin k) → V i) :
    x ∈ (H.deleteEdges deleted).simplexFinset ↔
      x ∈ H.simplexFinset ∧
        ∀ j, deleteCoordinate x j ∉ deleted j := by
  classical
  simp only [mem_simplexFinset, deleteEdges_edge, forall_and]

/-- A finite hypergraph is simplex-free when its labelled simplex finset is
empty. -/
def IsSimplexFree {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : SimplexHypergraph V) : Prop :=
  H.simplexFinset = ∅

/-- The empty deletion family. -/
def emptyDeletion {k : ℕ} (V : Fin k → Type*) :
    DeletionFamily V :=
  fun _ => ∅

@[simp]
theorem mem_emptyDeletion {k : ℕ} {V : Fin k → Type*}
    (j : Fin k) (x : DeletedVector V j) :
    x ∉ emptyDeletion V j := by
  simp [emptyDeletion]

/-- Deleting nothing leaves the labelled simplex finset unchanged. -/
@[simp]
theorem deleteEdges_empty_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    (H.deleteEdges (emptyDeletion V)).simplexFinset =
      H.simplexFinset := by
  classical
  ext x
  simp

/-- A cover remains a cover after enlarging each deleted-face set. -/
theorem IsSimplexCover.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : DeletionFamily V}
    (hcover : H.IsSimplexCover deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    H.IsSimplexCover deleted₂ := by
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  exact ⟨j, hdel j hj⟩

/-- Total number of deleted coloured faces. -/
def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card

@[simp]
theorem deletionCount_empty {k : ℕ} (V : Fin k → Type*) :
    deletionCount (emptyDeletion V) = 0 := by
  simp [deletionCount, emptyDeletion]

/-- Total number of available coloured face slots. -/
def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)

@[simp]
theorem card_deletedVector_fin (k n : ℕ) (j : Fin k) :
    Fintype.card
        (DeletedVector (fun _ : Fin k => Fin n) j) =
      n ^ (k - 1) := by
  simp [DeletedVector, Fintype.card_pi]

@[simp]
theorem deletionCapacity_fin (k n : ℕ) :
    deletionCapacity (fun _ : Fin k => Fin n) =
      k * n ^ (k - 1) := by
  simp [deletionCapacity]

/-- Density of the deleted faces in one colour class. -/
noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)

@[simp]
theorem colorDeletionDensity_fin {k n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin k => Fin n))
    (j : Fin k) :
    colorDeletionDensity deleted j =
      ((deleted j).card : ℝ) / (n ^ (k - 1) : ℕ) := by
  simp [colorDeletionDensity]

/-- Deleted-face density among all coloured face slots.  If the capacity is
zero, Lean's field division convention makes the value zero. -/
noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)

@[simp]
theorem normalizedDeletionCost_empty {k : ℕ}
    (V : Fin k → Type*) [∀ i, Fintype (V i)] :
    normalizedDeletionCost (emptyDeletion V) = 0 := by
  simp [normalizedDeletionCost]

end SimplexHypergraph

/-- No labelled simplex survives after deleting the specified faces. -/
def NoSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) : Prop :=
  (H.deleteEdges deleted).IsSimplexFree

/-- Exact correspondence between combinatorial covers and simplex-free
surviving hypergraphs. -/
theorem isSimplexCover_iff_noSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) :
    H.IsSimplexCover deleted ↔
      NoSimplexAfterDeleting H deleted := by
  classical
  constructor
  · intro hcover
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree,
      Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [SimplexHypergraph.mem_deleteEdges_simplexFinset] at hx
    obtain ⟨j, hj⟩ := hcover x hx.1
    exact hx.2 j hj
  · intro hfree x hx
    by_contra h
    push Not at h
    have hsurvives :
        x ∈ (H.deleteEdges deleted).simplexFinset :=
      (H.mem_deleteEdges_simplexFinset deleted x).2 ⟨hx, h⟩
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree] at hfree
    rw [hfree] at hsurvives
    simp at hsurvives

/-- Enlarging a deletion family preserves absence of surviving simplices. -/
theorem NoSimplexAfterDeleting.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : SimplexHypergraph.DeletionFamily V}
    (hfree : NoSimplexAfterDeleting H deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    NoSimplexAfterDeleting H deleted₂ := by
  apply (isSimplexCover_iff_noSimplexAfterDeleting H deleted₂).1
  apply SimplexHypergraph.IsSimplexCover.mono
    ((isSimplexCover_iff_noSimplexAfterDeleting
      H deleted₁).2 hfree)
  exact hdel

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StructuredCleaning.lean` -/

section
/-!
# Cleaning low-density structured cells

Given a zero-one edge function and a finite partition, delete the actual
edges lying in atoms whose conditional edge density is below `τ`.  The
conditional-expectation identity charges those deletions by at most a
`τ`-fraction of the ambient face space.

For a simplex system with equal vertex classes, applying this independently
to every colour still has normalized deletion cost at most `τ`.  Moreover,
every original simplex avoiding the deletion has structured edge weight at
least `τ` in every colour, hence structured simplex weight at least `τ^k`.

This is the top-rank cleaning step.  The full removal proof must apply the
same principle recursively to lower skeleton cells in order to replace the
ambient-size-dependent one-tuple bound by a uniform counting bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace FaceRegularityState

/-- The set on which the structured conditional density is below `τ`. -/
noncomputable def structuredSublevel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact Finset.univ.filter fun x => S.structured f x < τ

@[simp]
theorem mem_structuredSublevel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ)
    (x : Ω) :
    x ∈ S.structuredSublevel f τ ↔
      S.structured f x < τ := by
  simp [structuredSublevel]

/-- The portion of a zero-one function lying in low-density structured
atoms. -/
noncomputable def lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    Finset Ω := by
  classical
  exact Finset.univ.filter fun x =>
    f x = 1 ∧ S.structured f x < τ

@[simp]
theorem mem_lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ)
    (x : Ω) :
    x ∈ S.lowStructuredOneFinset f τ ↔
      f x = 1 ∧ S.structured f x < τ := by
  simp [lowStructuredOneFinset]

end FaceRegularityState

/-- The canonical equivalence between a dependent deleted face and its
ordered `Fin n` presentation. -/
noncomputable def deletedFaceEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedFaceTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedFaceTuple j
  right_inv := deletedFaceTuple_finTupleToDeletedVector j

/-- Delete precisely those actual edges whose structured atom density is
below `τ`. -/
noncomputable def lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) :=
  fun j =>
    ((S j).lowStructuredOneFinset
      (canonicalEdgeFunction H.toWeighted j) τ).map
        (deletedFaceEquiv j).symm.toEmbedding

@[simp]
theorem card_lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ)
    (j : Fin (n + 1)) :
    (lowStructuredDeletion H S τ j).card =
      ((S j).lowStructuredOneFinset
        (canonicalEdgeFunction H.toWeighted j) τ).card := by
  classical
  simp [lowStructuredDeletion]

@[simp]
theorem mem_lowStructuredDeletion_iff
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ lowStructuredDeletion H S τ j ↔
      deletedFaceTuple j x ∈
        (S j).lowStructuredOneFinset
          (canonicalEdgeFunction H.toWeighted j) τ := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have heq :
        y = deletedFaceTuple j x := by
      change y = (deletedFaceEquiv j) x
      calc
        y =
            (deletedFaceEquiv j)
              ((deletedFaceEquiv j).symm y) :=
          ((deletedFaceEquiv j).apply_symm_apply y).symm
        _ = (deletedFaceEquiv j) x :=
          congrArg (deletedFaceEquiv j) hyx
    simpa [heq] using hy
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨deletedFaceTuple j x, hx, ?_⟩
    exact (deletedFaceEquiv j).symm_apply_apply x

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedCellLifting.lean` -/

section
/-!
# Lower-rank cells and lifted ordered-pattern deletions

This file is the exact combinatorial interface for the rank induction in
ordered hypergraph removal.  Deleting one coordinate from an increasing
rank-`r` face gives an increasing rank-`r - 1` face.  The lower cells
generated by a structured top atom therefore assemble into a complete
ordered lower-rank pattern.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Delete coordinate `i` from an increasing ordered face. -/
def eraseOrderedFace
    {k r : ℕ} (e : OrderedFace k r) (i : Fin r) :
    OrderedFace k (r - 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      exact (Fin.succAboveOrderEmb i).trans e

/-- Restricting a full tuple to a deleted ordered face is the same as
erasing the corresponding coordinate from the top-face tuple. -/
@[simp]
theorem orderedFaceTuple_eraseOrderedFace
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (i : Fin r)
    (x : Fin k → G) :
    orderedFaceTuple (eraseOrderedFace e i) x =
      eraseCoordinate i (orderedFaceTuple e x) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      rfl

namespace OrderedPattern

/-- The cylinder over one deleted lower-rank face set. -/
noncomputable def deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    eraseCoordinate i y ∈ D (eraseOrderedFace e i)

@[simp]
theorem mem_deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r)
    (y : Fin r → G) :
    y ∈ deletionCylinder D e i ↔
      eraseCoordinate i y ∈
        D (eraseOrderedFace e i) := by
  simp [deletionCylinder]

/-- Lift a lower-rank deletion family by taking the union of all coordinate
cylinders inside each ordered top face. -/
noncomputable def liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1)) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun i =>
      deletionCylinder D e i

@[simp]
theorem mem_liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ liftLowerDeletion D e ↔
      ∃ i : Fin r,
        eraseCoordinate i y ∈
          D (eraseOrderedFace e i) := by
  classical
  simp [liftLowerDeletion]

/-- Union a finite family of ordered deletion families face by face. -/
noncomputable def unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun t => D t e

@[simp]
theorem mem_unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ unionDeletion D e ↔
      ∃ t : ι, y ∈ D t e := by
  classical
  simp [unionDeletion]

/-- Delete actual ordered edges which lie in structured atoms of density
below `τ`. -/
noncomputable def lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) :
    DeletionFamily (G := G) k r :=
  fun e =>
    (S e).lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ

@[simp]
theorem mem_lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) (e : OrderedFace k r)
    (y : Fin r → G) :
    y ∈ lowStructuredDeletion H S τ e ↔
      H.toWeighted.edgeWeight e y = 1 ∧
        (S e).structured
          (H.toWeighted.edgeWeight e) y < τ := by
  exact
    (S e).mem_lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ y

end OrderedPattern

namespace GeneratedOrderedPatternRegularization

/-- The finite index of every simultaneous top-atom and lower-branch
choice. -/
abbrev CellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  R.TopAtomChoice × R.BranchSystem

@[simp]
theorem card_cellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.CellIndex =
      Fintype.card R.TopAtomChoice *
        Fintype.card R.BranchSystem := by
  simp [CellIndex]

end GeneratedOrderedPatternRegularization

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedBoundaryPartition.lean` -/

section
/-!
# Shared ordered-face partitions and boundary pullbacks

The hypergraph-complex regularity proof uses one genuine partition on every
ordered lower face.  If `e` is an upper face, its boundary partition is not
an independently generated partition of the whole upper tuple space.  It is
the common refinement of the pullbacks of the shared partitions on the
immediate subfaces `eraseOrderedFace e i`.

This file implements that architecture.  Its central membership theorem says
that two upper tuples lie in the same boundary atom exactly when every pair
of erased tuples lies in the same atom of the corresponding genuine lower
face partition.  This is the compatibility needed for closed atom
configurations and localized energy estimates.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Coordinate deletion specialized to a successor arity.  This
definition has codomain `Fin j → G` on the nose, avoiding transports through
the propositionally equal expression `Fin (j + 1 - 1) → G`. -/
def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

/-- Immediate ordered subface specialized to a successor rank. -/
def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseBoundaryFace
    {G : Type*} {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    orderedFaceTuple (eraseBoundaryFace e i) x =
      eraseBoundaryCoordinate i (orderedFaceTuple e x) :=
  rfl

/-- A shared partition on every ordered face of one fixed rank. -/
abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

/-- Pointwise refinement of shared ordered-face partitions. -/
def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines

/-- Pull one actual lower-face partition back to an upper tuple space. -/
def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

/-- Common refinement of the pullbacks from every immediate subface. -/
def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

/-- The full boundary partition refines each one-coordinate pullback. -/
theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

/-- Refining all genuine lower-face partitions refines every induced
boundary partition. -/
theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

/-- Exact boundary-atom membership: every erased upper tuple must belong to
the corresponding shared lower-face atom. -/
theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

/-- Canonical boundary atom containing an upper tuple. -/
noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩

@[simp]
theorem orderedBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryAtomAt P e x).1 =
      (orderedBoundaryPartition P e).part x :=
  rfl

/-- Conditional mean of an upper-face function relative to its shared
immediate boundary. -/
noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f

/-- A bounded hierarchy of shared partitions, one layer for every rank from
zero through `r`. -/
structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex

/-- Extract a numerically indexed layer from a bounded partition complex. -/
def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩

/-- The immediate-boundary partition supplied by rank `j` of a complex. -/
def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : OrderedPartitionComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  orderedBoundaryPartition (C.layer j (Nat.le_of_lt hj)) e

/-- Pointwise refinement at every rank of two partition complexes. -/
def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl

theorem Refines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : OrderedPartitionComplex G k r}
    (hCD : C.Refines D) (hDE : D.Refines E) :
    C.Refines E :=
  fun j e => le_trans (hCD j e) (hDE j e)

end OrderedPartitionComplex

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedAtomEnergy.lean` -/

section
/-!
# Atom-family energy on shared ordered boundaries

Full hypergraph regularity simultaneously controls the indicators of every
atom in an upper-face partition.  Because those atoms are disjoint and
exhaust the tuple space, their aggregate conditional-expectation energy is
at most one.  This is substantially sharper than treating them as an
arbitrary family, whose naive energy budget is the number of targets.

This file first proves the generic finite-partition atom identities, then
specializes the energy to the shared ordered-boundary partitions from
`OrderedBoundaryPartition.lean`.  The final Pythagorean identity is the exact
coarse/fine defect budget used to show that most closed atom configurations
are good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Indicators of genuine partition atoms -/

/-- Indicator of one genuine atom of a finite partition. -/
def partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) :
    Ω → ℝ :=
  finsetIndicator a.1

@[simp]
theorem partitionAtomIndicator_of_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    partitionAtomIndicator Q a x = 1 :=
  finsetIndicator_of_mem hx

@[simp]
theorem partitionAtomIndicator_of_not_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    partitionAtomIndicator Q a x = 0 :=
  finsetIndicator_of_not_mem hx

theorem partitionAtomIndicator_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    0 ≤ partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ^ 2 =
      partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

/-- The genuine partition atoms form an exact pointwise partition of
unity. -/
theorem sum_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts, partitionAtomIndicator Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact partitionAtomIndicator_of_mem Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb hba
    apply partitionAtomIndicator_of_not_mem
    intro hxb
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 hxb
        (Q.mem_part (Finset.mem_univ x))
    exact hba heq
  · intro hax
    exact (hax (Finset.mem_univ ax)).elim

/-- Aggregate energy of all genuine atoms of `Q`, observed through `P`. -/
noncomputable def partitionAtomEnergy
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) : ℝ :=
  ∑ a : Q.parts,
    Wikipedia.SzemeredisTheorem.partitionEnergy P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) :
    0 ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  exact Finset.sum_nonneg fun a _ =>
    Wikipedia.SzemeredisTheorem.partitionEnergy_nonneg P
      (partitionAtomIndicator Q a)

/-- Disjointness improves the aggregate atom-energy budget from the number
of atoms to one. -/
theorem partitionAtomEnergy_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : FacePartition Ω) :
    partitionAtomEnergy P Q ≤ 1 := by
  unfold partitionAtomEnergy
  calc
    (∑ a : Q.parts,
        Wikipedia.SzemeredisTheorem.partitionEnergy P
          (partitionAtomIndicator Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            partitionAtomIndicator Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact partitionEnergy_le_mean_sq P
        (partitionAtomIndicator Q a)
    _ =
        ∑ a : Q.parts,
          mean (partitionAtomIndicator Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact partitionAtomIndicator_sq Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, partitionAtomIndicator Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => partitionAtomIndicator Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact sum_partitionAtomIndicator Q x
    _ = 1 := mean_const 1

/-- Refinement of the observing partition increases aggregate atom
energy. -/
theorem partitionAtomEnergy_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy R Q ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  apply Finset.sum_le_sum
  intro a _
  exact partitionEnergy_mono P R hPR
    (partitionAtomIndicator Q a)

/-- Exact aggregate Pythagorean identity for all upper atoms. -/
theorem partitionAtomEnergy_sub_eq_sum_mean_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy P Q - partitionAtomEnergy R Q =
      ∑ a : Q.parts,
        mean (fun x =>
          (conditionalMean P (partitionAtomIndicator Q a) x -
            conditionalMean R (partitionAtomIndicator Q a) x) ^ 2) := by
  unfold partitionAtomEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact partitionEnergy_sub_eq_mean_sq P R hPR
    (partitionAtomIndicator Q a)

/-! ## Ordered shared-boundary atom energy -/

/-- Aggregate energy of an upper-face partition, observed through the
shared partitions on its immediate lower faces. -/
noncomputable def orderedAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) : ℝ :=
  partitionAtomEnergy (orderedBoundaryPartition lower e) upper

theorem orderedAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    0 ≤ orderedAtomEnergy lower e upper :=
  partitionAtomEnergy_nonneg _ _

theorem orderedAtomEnergy_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy lower e upper ≤ 1 :=
  partitionAtomEnergy_le_one _ _

/-- Refining the shared lower layer increases every upper-face atom
energy. -/
theorem orderedAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy coarse e upper ≤
      orderedAtomEnergy fine e upper := by
  exact partitionAtomEnergy_mono
    (orderedBoundaryPartition_mono hfc e) upper

/-- The coarse/fine gap is the sum, over genuine upper atoms, of the exact
mean-square changes in their boundary conditional densities. -/
theorem orderedAtomEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy fine e upper -
        orderedAtomEnergy coarse e upper =
      ∑ a : upper.parts,
        mean (fun x =>
          (orderedBoundaryStructured fine e
                (partitionAtomIndicator upper a) x -
            orderedBoundaryStructured coarse e
                (partitionAtomIndicator upper a) x) ^ 2) := by
  exact partitionAtomEnergy_sub_eq_sum_mean_sq
    (orderedBoundaryPartition_mono hfc e) upper

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/PreliminaryOrderedRegularity.lean` -/

section
/-!
# Distributed preliminary ordered regularity

A Boolean cut witness on an upper face is a product of one predicate on each
immediate lower face.  In the shared-face architecture, adjoining such a
witness must refine those genuine lower-face partitions, rather than adjoin
the whole product support to an independent upper partition.

This file carries out that distributed refinement for one witness.  It
proves that the induced new boundary refines the abstract one-cut upper
refinement, and therefore inherits the same `ε²` energy increment.  Summing
the disjoint upper-atom energies over every upper face gives the preliminary
regularity potential.  A single violating atom/cut witness raises this
global potential by `ε²`, while the whole potential is bounded by the number
of upper faces.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A Boolean product-cut assignment at successor arity, with the deleted
tuple type normalized to `Fin j → G`. -/
abbrev BoundaryBooleanCutAssignment
    (G : Type*) (j : ℕ) :=
  (i : Fin (j + 1)) → (Fin j → G) → Bool

/-- The support of one coordinate predicate in a boundary Boolean cut. -/
noncomputable def boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    BooleanCutTest (Fin j → G) := by
  classical
  exact Finset.univ.filter fun z => b i z = true

@[simp]
theorem mem_boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    z ∈ boundaryBooleanComponentCut b i ↔
      b i z = true := by
  simp [boundaryBooleanComponentCut]

/-- Full upper-tuple support of a boundary Boolean product cut. -/
noncomputable def boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutTest (Fin (j + 1) → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b i (eraseBoundaryCoordinate i x) = true

@[simp]
theorem mem_boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    x ∈ boundaryBooleanCutSupport b ↔
      ∀ i, b i (eraseBoundaryCoordinate i x) = true := by
  simp [boundaryBooleanCutSupport]

/-- Lower-face component cuts contributed to one genuine lower face by a
single upper witness.  The definition allows repeated incidences, although
for an increasing ordered face the immediate subfaces are distinct. -/
noncomputable def orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    Finset (BooleanCutTest (Fin j → G)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)).image
      (fun i => boundaryBooleanComponentCut b i)

theorem boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    boundaryBooleanComponentCut b i ∈
      orderedBoundaryComponentCuts e b
        (eraseBoundaryFace e i) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp

/-- Distribute one upper Boolean witness to its genuine immediate subface
partitions. -/
noncomputable def refineOrderedFacePartitionsByBoundaryCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionSystem G k j :=
  fun g =>
    FacePartition.join (P g)
      (FacePartition.generatedBy
        (orderedBoundaryComponentCuts e b g))

/-- Distributed component refinement refines every old genuine lower-face
partition. -/
theorem refineOrderedFacePartitionsByBoundaryCut_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionRefines
      (refineOrderedFacePartitionsByBoundaryCut P e b) P := by
  intro g
  exact FacePartition.join_le_left _ _

/-- At incidence `i`, the refined genuine subface partition also refines
the partition generated by that component predicate alone. -/
theorem refineOrderedFacePartitionsByBoundaryCut_le_component
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i) ≤
      FacePartition.generatedBy
        ({boundaryBooleanComponentCut b i} :
          Finset (Finset (Fin j → G))) := by
  apply le_trans (FacePartition.join_le_right _ _)
  apply FacePartition.generatedBy_antitone
  intro A hA
  have hAeq : A = boundaryBooleanComponentCut b i := by
    simpa using hA
  subst A
  exact
    boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
      e b i

/-- Membership in a refined immediate lower atom preserves the corresponding
Boolean component bit. -/
theorem boundaryComponentBit_eq_of_mem_refined_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1))
    (x y : Fin j → G)
    (hy :
      y ∈
        (refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i)).part x) :
    b i x = b i y := by
  have hpart :
      y ∈
        (FacePartition.generatedBy
          ({boundaryBooleanComponentCut b i} :
            Finset (Finset (Fin j → G)))).part x :=
    FacePartition.part_subset_of_le
      (refineOrderedFacePartitionsByBoundaryCut_le_component
        P e b i) x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({boundaryBooleanComponentCut b i} :
        Finset (Finset (Fin j → G))) x y).1 hpart
      (boundaryBooleanComponentCut b i) (by simp)
  cases hbx : b i x <;> cases hby : b i y <;>
    simp [mem_boundaryBooleanComponentCut, hbx, hby] at hsignature ⊢

/-- The distributed boundary refinement makes the full Boolean product
support measurable.  Equivalently, it refines the partition generated by
that support. -/
theorem orderedBoundaryPartition_refined_le_generatedSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      FacePartition.generatedBy
        ({boundaryBooleanCutSupport b} :
          Finset (Finset (Fin (j + 1) → G))) := by
  rw [FacePartition.le_iff_part_subset]
  intro x y hy
  rw [FacePartition.mem_part_generatedBy_iff]
  intro A hA
  have hAeq : A = boundaryBooleanCutSupport b := by
    simpa using hA
  subst A
  rw [mem_boundaryBooleanCutSupport,
    mem_boundaryBooleanCutSupport]
  have hboundary :=
    (mem_orderedBoundaryPartition_part_iff
      (refineOrderedFacePartitionsByBoundaryCut P e b)
      e x y).1 hy
  constructor
  · intro hx i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit ▸ hx i
  · intro hy' i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit.symm ▸ hy' i

/-- The induced distributed boundary refines the abstract refinement
obtained by adjoining the full upper support in one step. -/
theorem orderedBoundaryPartition_refined_le_refineBy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
      orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      ((⟨orderedBoundaryPartition P e⟩ :
          FaceRegularityState (Fin (j + 1) → G)).refineBy
        (boundaryBooleanCutSupport b)).partition := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact orderedBoundaryPartition_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines P e b) e
  · exact orderedBoundaryPartition_refined_le_generatedSupport
      P e b

/-- Aggregate upper-atom energy of a whole rank layer. -/
noncomputable def orderedLayerAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) : ℝ :=
  ∑ e : OrderedFace k (j + 1),
    orderedAtomEnergy lower e (upper e)

theorem orderedLayerAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    0 ≤ orderedLayerAtomEnergy lower upper := by
  unfold orderedLayerAtomEnergy
  exact Finset.sum_nonneg fun e _ =>
    orderedAtomEnergy_nonneg lower e (upper e)

/-- The atom-energy potential of a whole upper layer is bounded by the
number of upper faces. -/
theorem orderedLayerAtomEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy lower upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
  unfold orderedLayerAtomEnergy
  calc
    (∑ e : OrderedFace k (j + 1),
        orderedAtomEnergy lower e (upper e)) ≤
        ∑ _e : OrderedFace k (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact orderedAtomEnergy_le_one lower e (upper e)
    _ = (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
      simp

theorem orderedLayerAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy coarse upper ≤
      orderedLayerAtomEnergy fine upper := by
  unfold orderedLayerAtomEnergy
  apply Finset.sum_le_sum
  intro e _
  exact orderedAtomEnergy_mono hfc e (upper e)

/-- One violating upper atom and one Boolean boundary product cut raise the
global layer atom-energy potential by at least `ε²`. -/
theorem orderedLayerAtomEnergy_increment_of_boundaryCut
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (e : OrderedFace k (j + 1))
    (a : (upper e).parts)
    (b : BoundaryBooleanCutAssignment G j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorrelation :
      ε ≤
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
            (partitionAtomIndicator (upper e) a)
            (boundaryBooleanCutSupport b)|) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (refineOrderedFacePartitionsByBoundaryCut lower e b)
        upper := by
  classical
  let fine :=
    refineOrderedFacePartitionsByBoundaryCut lower e b
  let S : FaceRegularityState (Fin (j + 1) → G) :=
    ⟨orderedBoundaryPartition lower e⟩
  have hincrement :
      S.energy (partitionAtomIndicator (upper e) a) + ε ^ 2 ≤
        (S.refineBy (boundaryBooleanCutSupport b)).energy
          (partitionAtomIndicator (upper e) a) :=
    S.energy_increment_of_booleanCut
      (partitionAtomIndicator (upper e) a)
      (boundaryBooleanCutSupport b) hε hcorrelation
  have hrefined :
      orderedBoundaryPartition fine e ≤
        (S.refineBy (boundaryBooleanCutSupport b)).partition := by
    exact orderedBoundaryPartition_refined_le_refineBy
      lower e b
  have hatom :
      orderedAtomEnergy lower e (upper e) + ε ^ 2 ≤
        orderedAtomEnergy fine e (upper e) := by
    unfold orderedAtomEnergy partitionAtomEnergy
    let U : Finset (upper e).parts := Finset.univ
    have haU : a ∈ U := by simp [U]
    have hother :
        ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c) ≤
          ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) := by
      apply Finset.sum_le_sum
      intro c _
      exact partitionEnergy_mono
        (orderedBoundaryPartition fine e)
        (orderedBoundaryPartition lower e)
        (orderedBoundaryPartition_mono
          (refineOrderedFacePartitionsByBoundaryCut_refines
            lower e b) e)
        (partitionAtomIndicator (upper e) c)
    have hchosen :
        partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
            ε ^ 2 ≤
          partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) := by
      exact le_trans hincrement
        (partitionEnergy_mono
          (orderedBoundaryPartition fine e)
          (S.refineBy (boundaryBooleanCutSupport b)).partition
          hrefined
          (partitionAtomIndicator (upper e) a))
    change
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
          ε ^ 2 ≤
        ∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition fine e)
            (partitionAtomIndicator (upper e) c)
    calc
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
            ε ^ 2 =
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c)) +
            (partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
              ε ^ 2) := by
        rw [← Finset.sum_erase_add U _ haU]
        ring
      _ ≤
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c)) +
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) :=
        add_le_add hother hchosen
      _ =
          ∑ c ∈ U,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) :=
        Finset.sum_erase_add U _ haU
  unfold orderedLayerAtomEnergy
  let E : Finset (OrderedFace k (j + 1)) := Finset.univ
  have heE : e ∈ E := by simp [E]
  have hotherFaces :
      ∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d) ≤
        ∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d) := by
    apply Finset.sum_le_sum
    intro d _
    exact orderedAtomEnergy_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines
        lower e b)
      d (upper d)
  change
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
        ε ^ 2 ≤
      ∑ d ∈ E, orderedAtomEnergy fine d (upper d)
  calc
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
          ε ^ 2 =
        (∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d)) +
        (orderedAtomEnergy lower e (upper e) + ε ^ 2) := by
      rw [← Finset.sum_erase_add E _ heE]
      ring
    _ ≤
        (∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d)) +
        orderedAtomEnergy fine e (upper e) :=
      add_le_add hotherFaces hatom
    _ =
        ∑ d ∈ E, orderedAtomEnergy fine d (upper d) :=
      Finset.sum_erase_add E _ heE

/-! ## Canonical preliminary regularity run -/

/-- Every upper atom has small residual correlation with every Boolean
boundary product cut. -/
def IsPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts)
      (b : BoundaryBooleanCutAssignment G j),
    |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower e⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper e) a)
        (boundaryBooleanCutSupport b)| ≤ ε

/-- Failure of preliminary regularity supplies an upper face, one genuine
upper atom, and a violating Boolean boundary cut. -/
theorem exists_boundaryCut_of_not_preliminaryRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ}
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    ∃ (e : OrderedFace k (j + 1))
        (a : (upper e).parts)
        (b : BoundaryBooleanCutAssignment G j),
      ε <
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
          (partitionAtomIndicator (upper e) a)
          (boundaryBooleanCutSupport b)| := by
  unfold IsPreliminaryOrderedRegular at h
  obtain ⟨e, he⟩ := not_forall.mp h
  obtain ⟨a, ha⟩ := not_forall.mp he
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨e, a, b, lt_of_not_ge hb⟩

/-- Chosen data witnessing a failure of preliminary regularity. -/
structure PreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) where
  face : OrderedFace k (j + 1)
  atom : (upper face).parts
  cut : BoundaryBooleanCutAssignment G j
  correlation :
    ε <
      |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower face⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper face) atom)
        (boundaryBooleanCutSupport cut)|

noncomputable def chosenPreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    PreliminaryIrregularWitness lower upper ε := by
  classical
  let hex :=
    exists_boundaryCut_of_not_preliminaryRegular
      lower upper h
  let e := Classical.choose hex
  let he := Classical.choose_spec hex
  let a := Classical.choose he
  let ha := Classical.choose_spec he
  let b := Classical.choose ha
  have hcorr := Classical.choose_spec ha
  exact ⟨e, a, b, hcorr⟩

/-- One total preliminary-regularity step.  At a regular layer it is the
identity; otherwise it distributes the chosen violating cut. -/
noncomputable def preliminaryOrderedRegularityStep
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionSystem G k j := by
  classical
  exact
    if h : IsPreliminaryOrderedRegular lower upper ε then
      lower
    else
      let W :=
        chosenPreliminaryIrregularWitness lower upper ε h
      refineOrderedFacePartitionsByBoundaryCut
        lower W.face W.cut

/-- Every preliminary step refines the current shared lower layer. -/
theorem preliminaryOrderedRegularityStep_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityStep lower upper ε)
      lower := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simpa [preliminaryOrderedRegularityStep, h] using
      OrderedFacePartitionRefines.refl lower
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact refineOrderedFacePartitionsByBoundaryCut_refines
      lower W.face W.cut

/-- At an irregular layer, one total step raises atom energy by `ε²`. -/
theorem preliminaryOrderedRegularityStep_energy_increment
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (preliminaryOrderedRegularityStep lower upper ε)
        upper := by
  classical
  simp only [preliminaryOrderedRegularityStep, dif_neg h]
  let W :=
    chosenPreliminaryIrregularWitness lower upper ε h
  exact orderedLayerAtomEnergy_increment_of_boundaryCut
    lower upper W.face W.atom W.cut hε
    (le_of_lt W.correlation)

/-- Canonical iteration of distributed preliminary refinement. -/
noncomputable def preliminaryOrderedRegularityRun
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => lower
  | n + 1 =>
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε

@[simp]
theorem preliminaryOrderedRegularityRun_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    preliminaryOrderedRegularityRun lower upper ε 0 =
      lower :=
  rfl

@[simp]
theorem preliminaryOrderedRegularityRun_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    preliminaryOrderedRegularityRun lower upper ε (n + 1) =
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε :=
  rfl

/-- Every run layer refines the initial shared lower layer. -/
theorem preliminaryOrderedRegularityRun_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityRun lower upper ε n)
      lower := by
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl lower
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (preliminaryOrderedRegularityStep_refines
          (preliminaryOrderedRegularityRun lower upper ε n)
          upper ε)
        ih

/-- The canonical run reaches simultaneous atom regularity before any
prescribed cutoff exceeding the finite layer-energy budget. -/
theorem exists_preliminaryOrderedRegularityRun_index_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      IsPreliminaryOrderedRegular
        (preliminaryOrderedRegularityRun
          lower upper ε n)
        upper ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬IsPreliminaryOrderedRegular
          (preliminaryOrderedRegularityRun
            lower upper ε n)
          upper ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper +
            ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1))
            upper := by
    intro n hn
    rw [preliminaryOrderedRegularityRun_succ]
    exact preliminaryOrderedRegularityStep_energy_increment
      (preliminaryOrderedRegularityRun
        lower upper ε n)
      upper hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε i)
              upper +
              ε ^ 2 ≤
            orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε (i + 1))
              upper) →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε 0)
            upper +
            (n : ℝ) * ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε 0)
                upper +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              (orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε 0)
                  upper +
                (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤
              orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε n)
                  upper +
                ε ^ 2 := by
            linarith
          _ ≤
              orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε (n + 1))
                upper :=
            hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤
        orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε 0)
          upper :=
    orderedLayerAtomEnergy_nonneg _ _
  have hupper :
      orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε m)
          upper ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) :=
    orderedLayerAtomEnergy_le_card _ _
  linarith

/-! ## Ambient-independent complexity bounds -/

theorem card_orderedBoundaryComponentCuts_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    (orderedBoundaryComponentCuts e b g).card ≤
      j + 1 := by
  classical
  let I : Finset (Fin (j + 1)) :=
    (Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)
  calc
    (orderedBoundaryComponentCuts e b g).card ≤
        I.card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (j + 1))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = j + 1 := by simp

/-- One distributed witness multiplies the complexity of each genuine lower
partition by at most `2^(j+1)`. -/
theorem complexity_refineOrderedFacePartitionsByBoundaryCut_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (P g) := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy
            (orderedBoundaryComponentCuts e b g)) ≤
        2 ^ (j + 1) := by
    exact le_trans
      (FacePartition.complexity_generatedBy_le
        (orderedBoundaryComponentCuts e b g))
      (Nat.pow_le_pow_right (by decide)
        (card_orderedBoundaryComponentCuts_le e b g))
  calc
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
        FacePartition.complexity (P g) *
          FacePartition.complexity
            (FacePartition.generatedBy
              (orderedBoundaryComponentCuts e b g)) :=
      FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity (P g) *
          2 ^ (j + 1) :=
      Nat.mul_le_mul_left _ hgenerated
    _ =
        2 ^ (j + 1) *
          FacePartition.complexity (P g) :=
      Nat.mul_comm _ _

theorem complexity_preliminaryOrderedRegularityStep_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityStep
          lower upper ε g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (lower g) := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simp only [preliminaryOrderedRegularityStep, dif_pos h]
    exact Nat.le_mul_of_pos_left _
      (by positivity : 0 < 2 ^ (j + 1))
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact
      complexity_refineOrderedFacePartitionsByBoundaryCut_le
        lower W.face W.cut g

/-- Complexity after `n` preliminary steps remains independent of
`Fintype.card G`. -/
theorem complexity_preliminaryOrderedRegularityRun_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityRun
          lower upper ε n g) ≤
      (2 ^ (j + 1)) ^ n *
        FacePartition.complexity (lower g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1) g) ≤
            2 ^ (j + 1) *
              FacePartition.complexity
                (preliminaryOrderedRegularityRun
                  lower upper ε n g) := by
          rw [preliminaryOrderedRegularityRun_succ]
          exact complexity_preliminaryOrderedRegularityStep_le
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper ε g
        _ ≤
            2 ^ (j + 1) *
              ((2 ^ (j + 1)) ^ n *
                FacePartition.complexity (lower g)) :=
          Nat.mul_le_mul_left _ ih
        _ =
            (2 ^ (j + 1)) ^ (n + 1) *
              FacePartition.complexity (lower g) := by
          rw [pow_succ]
          ring

/-- Fixed-budget preliminary regularity with its explicit
ambient-independent lower-layer complexity certificate. -/
theorem exists_preliminaryOrderedRegular_refinement_with_complexity_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ fine : OrderedFacePartitionSystem G k j,
        n < m ∧
        OrderedFacePartitionRefines fine lower ∧
        IsPreliminaryOrderedRegular fine upper ε ∧
        ∀ g,
          FacePartition.complexity (fine g) ≤
            (2 ^ (j + 1)) ^ n *
              FacePartition.complexity (lower g) := by
  obtain ⟨n, hn, hregular⟩ :=
    exists_preliminaryOrderedRegularityRun_index_before
      lower upper hε hlong
  exact
    ⟨n,
      preliminaryOrderedRegularityRun lower upper ε n,
      hn,
      preliminaryOrderedRegularityRun_refines
        lower upper ε n,
      hregular,
      complexity_preliminaryOrderedRegularityRun_le
        lower upper ε n⟩

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/BoundaryBernoulli.lean` -/

section
/-!
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Curry an ordinary Boolean cut assignment at successor arity into the
boundary-assignment presentation. -/
def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

/-- Uncurry a boundary Boolean assignment into the ordinary cut-coordinate
presentation. -/
def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

/-- The curried and uncurried Boolean boundary assignments are equivalent. -/
def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary

@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b

/-- The Bernoulli coefficient of one boundary Boolean assignment. -/
def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

/-- Boundary Bernoulli coefficients sum to one. -/
theorem sum_boundaryBernoulliWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1)) :
    ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b = 1 := by
  classical
  calc
    (∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b) =
        ∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b := by
      symm
      exact
        Fintype.sum_equiv
          (booleanBoundaryAssignmentEquiv G j)
          (fun b : BooleanCutAssignment G (j + 1) =>
            bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b)
          (fun b : BoundaryBooleanCutAssignment G j =>
            boundaryBernoulliWeight u b)
          (fun b => by simp [boundaryBernoulliWeight])
    _ = 1 :=
      sum_bernoulliAssignmentWeight
        (cutTestCoordinateValue u)

/-- Bounded boundary factors give nonnegative Bernoulli coefficients. -/
theorem boundaryBernoulliWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (b : BoundaryBooleanCutAssignment G j) :
    0 ≤ boundaryBernoulliWeight u b := by
  exact
    bernoulliAssignmentWeight_nonneg
      (p := cutTestCoordinateValue u)
      (fun q => hu.nonneg q.1 q.2)
      (fun q => hu.le_one q.1 q.2)
      (booleanAssignmentOfBoundary b)

/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl

/-- The boundary support of a curried assignment is the ordinary Boolean
face-cut support of its uncurried assignment. -/
theorem boundaryBooleanCutSupport_eq_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanCutSupport b =
      booleanFaceCutSupport (booleanAssignmentOfBoundary b) := by
  classical
  ext x
  rw [mem_boundaryBooleanCutSupport,
    mem_booleanFaceCutSupport]
  simp only [booleanAssignmentOfBoundary,
    eraseBoundaryCoordinate_eq_eraseCoordinate]

namespace FaceRegularityState

/-- Exact convex-mixture formula for residual correlation against a bounded
boundary product.  The identity itself does not require boundedness. -/
theorem faceCutCorrelation_eq_sum_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : CutTestFamily G (j + 1)) :
    S.faceCutCorrelation f u =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b) := by
  classical
  rw [S.faceCutCorrelation_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b))
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b))
      (fun b => by
        rw [S.faceCutCorrelation_boolean]
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eq_booleanFaceCutSupport])

/-- Uniform control of all Boolean boundary products controls every bounded
`[0,1]`-valued boundary product, with no loss in the error. -/
theorem abs_faceCutCorrelation_le_of_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    {ε : ℝ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BoundaryBooleanCutAssignment G j,
        |S.booleanCutCorrelation f
          (boundaryBooleanCutSupport b)| ≤ ε) :
    |S.faceCutCorrelation f u| ≤ ε := by
  rw [S.faceCutCorrelation_eq_sum_boundaryBoolean]
  calc
    |∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b)| ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          |boundaryBernoulliWeight u b *
            S.booleanCutCorrelation f
              (boundaryBooleanCutSupport b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          boundaryBernoulliWeight u b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw : 0 ≤ boundaryBernoulliWeight u b :=
        boundaryBernoulliWeight_nonneg u hu b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_boundaryBernoulliWeight, one_mul]

end FaceRegularityState

/-- Preliminary ordered regularity tested against every bounded boundary
product rather than only Boolean boundary products. -/
def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε

/-- Boolean preliminary ordered regularity implies bounded-test preliminary
ordered regularity with exactly the same error. -/
theorem IsPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower upper ε) :
    IsPreliminaryOrderedBoundedRegular
      lower upper ε := by
  intro e a u hu
  exact
    FaceRegularityState.abs_faceCutCorrelation_le_of_boundaryBoolean
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (partitionAtomIndicator (upper e) a)
      u hu (fun b => hregular e a b)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FullOrderedRegularity.lean` -/

section
/-!
# All-rank ordered preliminary regularity

The preliminary energy increment acts on one adjacent pair of ranks: it
refines the shared rank-`j` partitions while keeping rank `j + 1` fixed.
This file assembles those refinements into one compatible partition complex.
The ranks are processed from top to bottom.  Consequently, once the pair
`(j, j + 1)` has been regularized, later steps only change lower ranks and
cannot invalidate it.

The resulting theorem has a separate tolerance and finite energy budget at
every adjacent pair.  It returns an explicit stopping-time schedule, a
refining complex which is preliminarily regular at every rank, and the
ambient-independent complexity multiplier at every non-top layer.

We also package coarse/fine complexes and their boundary atom-energy gap.
The gap uses the atoms of the fine upper layer at both endpoints; with that
choice, refinement of the lower boundary gives honest monotonicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedPartitionComplex

/-- The top shared-face layer of a bounded ordered partition complex. -/
def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

/-- Forget the top layer of a nontrivial ordered partition complex. -/
def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

/-- Append one new top layer to an ordered partition complex. -/
def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

/-- Replace only the top layer of an ordered partition complex. -/
def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j

@[simp]
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]

@[simp]
theorem dropTop_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).dropTop = C := by
  cases C with
  | mk partition =>
      simp [dropTop, appendTop]

@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

@[simp]
theorem withTopLayer_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1))
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (withTopLayer C top).partition j.castSucc =
      C.partition j.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]

@[simp]
theorem withTopLayer_partition_castSucc_general
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (i : Fin r) :
    (withTopLayer C top).partition i.castSucc =
      C.partition i.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]

/-- Appending pointwise-refining top and lower layers preserves refinement
of the whole complex. -/
theorem appendTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    {fineTop coarseTop :
      OrderedFacePartitionSystem G k (r + 1)}
    (hfc : fine.Refines coarse)
    (htop : OrderedFacePartitionRefines fineTop coarseTop) :
    (appendTop fine fineTop).Refines
      (appendTop coarse coarseTop) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [appendTop, Fin.lastCases_last]
      change OrderedFace k (r + 1) at e
      change fineTop e ≤ coarseTop e
      exact htop e
  | cast i =>
      simp only [appendTop, Fin.lastCases_castSucc]
      change OrderedFace k i.1 at e
      change fine.partition i e ≤ coarse.partition i e
      exact hfc i e

/-- Replacing the top layer by a refinement refines the original complex
and leaves every lower layer unchanged. -/
theorem withTopLayer_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (htop : OrderedFacePartitionRefines top C.topLayer) :
    (withTopLayer C top).Refines C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [withTopLayer, Fin.lastCases_last]
      change OrderedFace k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact htop e
  | cast i =>
      simp only [withTopLayer, Fin.lastCases_castSucc]
      exact le_rfl

end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/

/-- A pair of compatible ordered partition complexes, with the fine complex
refining the coarse one at every genuine face. -/
structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

namespace OrderedCoarseFineComplex

/-- At rank `j`, compare coarse and fine lower boundaries against the same
family of atoms: the atoms of the fine rank-`j+1` layer.  Freezing this upper
family is what makes the gap monotone. -/
noncomputable def layerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.fine.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.fine.partition j.succ)

/-- Total frozen-upper-family gap over every adjacent pair of ranks. -/
noncomputable def totalAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) : ℝ :=
  ∑ j : Fin r, P.layerAtomEnergyGap j

end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/

/-- One tolerance for every adjacent rank pair `(j, j + 1)`. -/
abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

/-- One finite iteration budget for every adjacent rank pair. -/
abbrev OrderedRegularityBudget (r : ℕ) := Fin r → ℕ

/-- The actual stopping index selected at every adjacent rank pair. -/
abbrev OrderedRegularityStepSchedule (r : ℕ) := Fin r → ℕ

/-- Every adjacent rank pair in a complex is preliminarily regular. -/
def IsFullyPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

/-- The per-rank budgets strictly exceed the corresponding atom-energy
ceilings after division by the squared tolerances. -/
def IsOrderedRegularityBudget
    (k r : ℕ)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) : Prop :=
  ∀ j : Fin r,
    (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
      (m j : ℝ) * (ε j) ^ 2

/-- The explicit ambient-independent complexity certificate associated to
a stopping-time schedule.  The top layer is deliberately excluded: it is
preserved exactly. -/
def HasOrderedRegularityComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (steps : OrderedRegularityStepSchedule r) : Prop :=
  ∀ (j : Fin r) (e : OrderedFace k j.1),
    FacePartition.complexity
        (fine.partition j.castSucc e) ≤
      (2 ^ (j.1 + 1)) ^ (steps j) *
        FacePartition.complexity
          (coarse.partition j.castSucc e)

/-! ## The top-down all-rank construction -/

/-- Complete output data for the all-rank preliminary regularity pass. -/
structure FullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (coarse : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) where
  steps : OrderedRegularityStepSchedule r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  topLayer_eq :
    fine.topLayer = coarse.topLayer
  steps_lt : ∀ j, steps j < m j
  regular :
    IsFullyPreliminaryOrderedRegular fine ε
  complexity :
    HasOrderedRegularityComplexityBound
      fine coarse steps

/-- A top-down pass combines the adjacent-rank energy increments into one
compatible complex.  Each non-top rank is changed exactly during its own
stage.  Thus its final complexity is bounded by its own stopping-time
multiplier, without any factor involving `Fintype.card G`. -/
theorem exists_fullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget : IsOrderedRegularityBudget k r ε m) :
    Nonempty (FullOrderedRegularityCertificate C ε m) := by
  induction r with
  | zero =>
      let steps : OrderedRegularityStepSchedule 0 :=
        fun j => Fin.elim0 j
      refine ⟨{
        steps := steps
        fine := C
        refines := OrderedPartitionComplex.Refines.refl C
        topLayer_eq := rfl
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerComplex : OrderedPartitionComplex G k r :=
        C.dropTop
      let upper : OrderedFacePartitionSystem G k (r + 1) :=
        C.topLayer
      have hεtop : 0 ≤ ε (Fin.last r) :=
        hε (Fin.last r)
      have hbudgetTop :
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 := by
        have hb := hbudget (Fin.last r)
        change
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 at hb
        exact hb
      obtain ⟨n, lower, hn, hlowerRefines,
          hlowerRegular, hlowerComplexity⟩ :=
        exists_preliminaryOrderedRegular_refinement_with_complexity_before
          lowerComplex.topLayer upper hεtop hbudgetTop
      let prepared : OrderedPartitionComplex G k r :=
        lowerComplex.withTopLayer lower
      have hpreparedRefines :
          prepared.Refines lowerComplex := by
        exact OrderedPartitionComplex.withTopLayer_refines
          lowerComplex lower hlowerRefines
      let εlower : OrderedRegularityTolerance r :=
        fun j => ε j.castSucc
      let mlower : OrderedRegularityBudget r :=
        fun j => m j.castSucc
      have hεlower : ∀ j, 0 ≤ εlower j := by
        intro j
        exact hε j.castSucc
      have hbudgetLower :
          IsOrderedRegularityBudget k r εlower mlower := by
        intro j
        exact hbudget j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower mlower hεlower hbudgetLower
      let fine : OrderedPartitionComplex G k (r + 1) :=
        lowerCertificate.fine.appendTop upper
      let steps : OrderedRegularityStepSchedule (r + 1) :=
        fun j =>
          Fin.lastCases n lowerCertificate.steps j
      have hlowerCertificateTop :
          lowerCertificate.fine.topLayer = lower := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.topLayer_eq
          _ = lower :=
            OrderedPartitionComplex.topLayer_withTopLayer
              lowerComplex lower
      refine ⟨{
        steps := steps
        fine := fine
        refines := ?_
        topLayer_eq := ?_
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · have hprefixFinal :
            lowerCertificate.fine.Refines lowerComplex :=
          OrderedPartitionComplex.Refines.trans
            lowerCertificate.refines hpreparedRefines
        have happended :
            fine.Refines
              (lowerComplex.appendTop upper) := by
          exact OrderedPartitionComplex.appendTop_refines
            hprefixFinal
            (OrderedFacePartitionRefines.refl upper)
        simpa [fine, lowerComplex, upper] using happended
      · simp [fine, upper]
      · intro j
        cases j using Fin.lastCases with
        | last =>
            simpa [steps] using hn
        | cast i =>
            simpa [steps] using
              lowerCertificate.steps_lt i
      · intro j
        cases j using Fin.lastCases with
        | last =>
            have htop :
                IsPreliminaryOrderedRegular
                  lowerCertificate.fine.topLayer
                  upper (ε (Fin.last r)) := by
              rw [hlowerCertificateTop]
              exact hlowerRegular
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              Fin.succ_last]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k r
                (lowerCertificate.fine.partition
                  (Fin.last r))
                upper (ε (Fin.last r))
            exact htop
        | cast i =>
            have hi := lowerCertificate.regular i
            simp only [fine, εlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.succ_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition i.castSucc)
                (lowerCertificate.fine.partition i.succ)
                (ε i.castSucc)
            exact hi
      · intro j
        cases j using Fin.lastCases with
        | last =>
            intro e
            have htop :
                FacePartition.complexity
                    (lowerCertificate.fine.topLayer e) ≤
                  (2 ^ (r + 1)) ^ n *
                    FacePartition.complexity
                      (lowerComplex.topLayer e) := by
              rw [hlowerCertificateTop]
              exact hlowerComplexity e
            simp only [fine, steps,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_last]
            change OrderedFace k r at e
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    (Fin.last r) e) ≤
                (2 ^ (r + 1)) ^ n *
                  FacePartition.complexity
                    (C.partition
                      (Fin.last r).castSucc e)
            exact htop
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hi := lowerCertificate.complexity i e
            simp only [prepared, lowerComplex,
              OrderedPartitionComplex.withTopLayer,
              OrderedPartitionComplex.dropTop,
              Fin.lastCases_castSucc] at hi
            simp only [fine, steps, εlower, mlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                (2 ^ (i.1 + 1)) ^
                    lowerCertificate.steps i *
                  FacePartition.complexity
                    (C.partition
                      i.castSucc.castSucc e)
            exact hi

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedGoodAtoms.lean` -/

section
/-!
# Good ordered atoms and localized bad-base accounting

The hypergraph removal argument must localize a global coarse--fine energy
gap to genuine boundary atoms.  This file supplies the finite bookkeeping
for that step.

For an arbitrary finite partition we define the union of a selected family
of atoms and prove that its normalized mass is the sum of the atom masses.
Sublevel atoms charge only a small part of a target atom, while atoms on
which a nonnegative local average is large satisfy a finite Markov bound.
Applying this to the square of a coarse--fine conditional-density defect
gives the headline estimate

```text
mass (upperAtom ∩ badBase) ≤
  densityThreshold + atomEnergyGap / defectThreshold.
```

The final section specializes these definitions to shared ordered
boundaries and packages realizable closed atom configurations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Canonical atoms and unions of genuine partition atoms -/

/-- The canonical genuine atom containing `x`. -/
def partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩

@[simp]
theorem partitionAtomAt_val
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    (partitionAtomAt P x).1 = P.part x :=
  rfl

@[simp]
theorem partitionAtomAt_eq_iff_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) (a : P.parts) :
    partitionAtomAt P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx

theorem partitionAtomAt_eq_iff_mem_part
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x y : Ω) :
    partitionAtomAt P y = partitionAtomAt P x ↔
      y ∈ P.part x := by
  rw [partitionAtomAt_eq_iff_mem]
  rfl

/-- The indicator of a genuine partition atom is measurable for that
partition. -/
theorem partitionAtomIndicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (a : P.parts) :
    IsPartitionMeasurable P (partitionAtomIndicator P a) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  by_cases hx : x ∈ a.1
  · have hax : partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hx
    have hay : partitionAtomAt P y = a := hxy.trans hax
    have hy' : y ∈ a.1 :=
      (partitionAtomAt_eq_iff_mem P y a).1 hay
    simp [partitionAtomIndicator_of_mem P a hx,
      partitionAtomIndicator_of_mem P a hy']
  · have hy' : y ∉ a.1 := by
      intro hya
      have hay : partitionAtomAt P y = a :=
        (partitionAtomAt_eq_iff_mem P y a).2 hya
      have hax : partitionAtomAt P x = a :=
        hxy.symm.trans hay
      exact hx ((partitionAtomAt_eq_iff_mem P x a).1 hax)
    simp [partitionAtomIndicator_of_not_mem P a hx,
      partitionAtomIndicator_of_not_mem P a hy']

/-- Union of a selected finite family of genuine partition atoms. -/
def partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1

@[simp]
theorem mem_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      ∃ a ∈ s, x ∈ a.1 := by
  simp [partitionAtomUnion]

/-- Membership in an atom union is determined by the canonical atom. -/
theorem mem_partitionAtomUnion_iff_atomAt_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      partitionAtomAt P x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    have hcanonical :
        partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hxa
    simpa [hcanonical] using ha
  · intro hx
    exact
      (mem_partitionAtomUnion P s x).2
        ⟨partitionAtomAt P x, hx,
          P.mem_part (Finset.mem_univ x)⟩

/-- The indicator of an atom union is the sum of the indicators of its
selected atoms. -/
theorem finsetIndicator_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    finsetIndicator (partitionAtomUnion P s) x =
      ∑ a ∈ s, partitionAtomIndicator P a x := by
  classical
  by_cases hx : x ∈ partitionAtomUnion P s
  · obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    rw [finsetIndicator_of_mem hx,
      Finset.sum_eq_single a]
    · exact (partitionAtomIndicator_of_mem P a hxa).symm
    · intro b hb hba
      apply partitionAtomIndicator_of_not_mem
      intro hxb
      have hab : b = a := by
        apply Subtype.ext
        exact P.eq_of_mem_parts b.2 a.2 hxb hxa
      exact hba hab
    · intro hnot
      exact (hnot ha).elim
  · rw [finsetIndicator_of_not_mem hx]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    apply partitionAtomIndicator_of_not_mem
    intro hxa
    exact hx
      ((mem_partitionAtomUnion P s x).2 ⟨a, ha, hxa⟩)

/-- Every union of atoms is measurable for the underlying partition. -/
theorem partitionAtomUnion_indicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    IsPartitionMeasurable P
      (finsetIndicator (partitionAtomUnion P s)) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  have hmem :
      y ∈ partitionAtomUnion P s ↔
        x ∈ partitionAtomUnion P s := by
    rw [mem_partitionAtomUnion_iff_atomAt_mem,
      mem_partitionAtomUnion_iff_atomAt_mem, hxy]
  by_cases hx : x ∈ partitionAtomUnion P s
  · have hy' : y ∈ partitionAtomUnion P s := hmem.mpr hx
    simp [finsetIndicator_of_mem hx,
      finsetIndicator_of_mem hy']
  · have hy' : y ∉ partitionAtomUnion P s :=
      fun h => hx (hmem.mp h)
    simp [finsetIndicator_of_not_mem hx,
      finsetIndicator_of_not_mem hy']

/-- Localizing a function to one genuine atom multiplies the atom mass by
the conditional average on that atom. -/
theorem mean_mul_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts) :
    mean (fun x => f x * partitionAtomIndicator P a x) =
      conditionalMean P f (P.representative a) *
        mean (partitionAtomIndicator P a) := by
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P f (partitionAtomIndicator P a)
    (partitionAtomIndicator_measurable P a)]
  rw [← mean_smul]
  apply congrArg mean
  funext x
  by_cases hx : x ∈ a.1
  · rw [partitionAtomIndicator_of_mem P a hx,
      mul_one, mul_one]
    have hrep :
        P.representative a ∈ P.part x := by
      rw [P.part_eq_of_mem a.2 hx]
      exact P.representative_mem a
    exact
      (conditionalMean_eq_of_mem_part P f hrep).symm
  · rw [partitionAtomIndicator_of_not_mem P a hx,
      mul_zero, mul_zero]

/-- Conditional control on one atom implies the equivalent localized
global-mass inequality. -/
theorem mean_mul_partitionAtomIndicator_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts)
    {β : ℝ}
    (hβ : conditionalMean P f (P.representative a) ≤ β) :
    mean (fun x => f x * partitionAtomIndicator P a x) ≤
      β * mean (partitionAtomIndicator P a) := by
  rw [mean_mul_partitionAtomIndicator P f a]
  apply mul_le_mul_of_nonneg_right hβ
  exact mean_nonneg fun x =>
    partitionAtomIndicator_nonneg P a x

/-! ## Sublevel atoms and low-density charging -/

/-- Atoms on which the conditional average of `f` is below `α`. -/
noncomputable def smallAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    conditionalMean P f (P.representative b) < α

/-- Union of the atoms on which the conditional average is below `α`. -/
noncomputable def smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (smallAverageBaseAtoms P f α)

@[simp]
theorem mem_smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ)
    (x : Ω) :
    x ∈ smallAverageBaseSupport P f α ↔
      conditionalMean P f x < α := by
  rw [smallAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [smallAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

/-- The part of `A` lying above atoms of conditional `A`-density below
`α` has normalized mass at most `α`. -/
theorem mean_indicator_inter_smallAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : FacePartition Ω) (A : Finset Ω)
    {α : ℝ} (hα : 0 ≤ α) :
    mean (finsetIndicator
      (A ∩ smallAverageBaseSupport P (finsetIndicator A) α)) ≤
      α := by
  rw [show
      finsetIndicator
          (A ∩ smallAverageBaseSupport P (finsetIndicator A) α) =
        fun x =>
          finsetIndicator A x *
            finsetIndicator
              (smallAverageBaseSupport
                P (finsetIndicator A) α) x by
    funext x
    by_cases hxA : x ∈ A <;>
      by_cases hxB :
        x ∈ smallAverageBaseSupport P (finsetIndicator A) α <;>
      simp [hxA, hxB]]
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P (finsetIndicator A)
      (finsetIndicator
        (smallAverageBaseSupport P (finsetIndicator A) α))
      (partitionAtomUnion_indicator_measurable P
        (smallAverageBaseAtoms P (finsetIndicator A) α))]
  calc
    mean (fun x =>
        conditionalMean P (finsetIndicator A) x *
          finsetIndicator
            (smallAverageBaseSupport P
              (finsetIndicator A) α) x) ≤
        mean (fun _x : Ω => α) := by
      apply mean_mono
      intro x
      by_cases hx :
          x ∈ smallAverageBaseSupport P (finsetIndicator A) α
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_smallAverageBaseSupport
            P (finsetIndicator A) α x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact hα
    _ = α := mean_const α

/-! ## Large local averages and finite Markov bounds -/

/-- Atoms on which the conditional average of `f` exceeds `β`. -/
noncomputable def largeAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < conditionalMean P f (P.representative b)

/-- Union of atoms on which the conditional average of `f` exceeds `β`. -/
noncomputable def largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (largeAverageBaseAtoms P f β)

@[simp]
theorem mem_largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ)
    (x : Ω) :
    x ∈ largeAverageBaseSupport P f β ↔
      β < conditionalMean P f x := by
  rw [largeAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [largeAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

/-- Finite Markov inequality localized to genuine partition atoms. -/
theorem mul_mean_indicator_largeAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (_hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (largeAverageBaseSupport P f β)) ≤
      mean f := by
  rw [← mean_smul]
  calc
    mean (fun x =>
        β * finsetIndicator
          (largeAverageBaseSupport P f β) x) ≤
        mean (conditionalMean P f) := by
      apply mean_mono
      intro x
      by_cases hx : x ∈ largeAverageBaseSupport P f β
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_largeAverageBaseSupport P f β x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact conditionalMean_nonneg P hf x
    _ = mean f := mean_conditionalMean P f

/-! ## Coarse--fine defect bases -/

/-- Change in the conditional density of one upper atom between a fine and
a coarse observing partition. -/
noncomputable def atomBoundaryDefect
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  conditionalMean fine (partitionAtomIndicator upper a) x -
    conditionalMean coarse (partitionAtomIndicator upper a) x

/-- Squared coarse--fine conditional-density defect of one upper atom. -/
noncomputable def atomBoundaryDefectSq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  atomBoundaryDefect fine coarse upper a x ^ 2

theorem atomBoundaryDefectSq_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) :
    0 ≤ atomBoundaryDefectSq fine coarse upper a x :=
  sq_nonneg _

/-- Coarse boundary atoms whose local mean-square defect exceeds `β`. -/
noncomputable def largeDefectBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset coarse.parts :=
  largeAverageBaseAtoms coarse
    (atomBoundaryDefectSq fine coarse upper a) β

/-- Union of coarse boundary atoms with excessive local defect. -/
noncomputable def largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion coarse
    (largeDefectBaseAtoms fine coarse upper a β)

@[simp]
theorem mem_largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) (x : Ω) :
    x ∈ largeDefectBaseSupport fine coarse upper a β ↔
      β <
        conditionalMean coarse
          (atomBoundaryDefectSq fine coarse upper a) x := by
  exact
    mem_largeAverageBaseSupport coarse
      (atomBoundaryDefectSq fine coarse upper a) β x

/-- Union of the low-density and large-defect coarse bad bases for one
upper atom. -/
noncomputable def atomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (α β : ℝ) :
    Finset Ω :=
  smallAverageBaseSupport coarse
      (partitionAtomIndicator upper a) α ∪
    largeDefectBaseSupport fine coarse upper a β

/-- Elementary normalized union bound, with the second set allowed to be
larger than its intersection with `A`. -/
theorem mean_indicator_inter_union_le_add
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B C : Finset Ω) :
    mean (finsetIndicator (A ∩ (B ∪ C))) ≤
      mean (finsetIndicator (A ∩ B)) +
        mean (finsetIndicator C) := by
  rw [← mean_add]
  apply mean_mono
  intro x
  by_cases hx : x ∈ A ∩ (B ∪ C)
  · rw [finsetIndicator_of_mem hx]
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with hxB | hxC
    · have hxAB : x ∈ A ∩ B :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩
      rw [finsetIndicator_of_mem hxAB]
      exact le_add_of_nonneg_right
        (by
          by_cases hxc : x ∈ C <;> simp [hxc])
    · rw [finsetIndicator_of_mem hxC]
      exact le_add_of_nonneg_left
        (by
          by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
  · rw [finsetIndicator_of_not_mem hx]
    exact add_nonneg
      (by
        by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
      (by
        by_cases hxc : x ∈ C <;> simp [hxc])

/-! ## Ordered boundary specialization -/

/-- Canonical genuine atom on one ordered face. -/
def orderedFaceAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (P e).parts :=
  partitionAtomAt (P e) x

@[simp]
theorem orderedFaceAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (orderedFaceAtomAt P e x).1 = (P e).part x :=
  rfl

/-- Ordered version of the coarse--fine conditional-density defect. -/
noncomputable def orderedAtomBoundaryDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  atomBoundaryDefect
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a x

/-- Normalized mass of one genuine ordered coarse boundary atom. -/
noncomputable def orderedBoundaryAtomMass
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : (orderedBoundaryPartition coarse e).parts) : ℝ :=
  mean
    (partitionAtomIndicator
      (orderedBoundaryPartition coarse e) b)

/-- Global mass of the squared defect localized to one genuine ordered
coarse boundary atom. -/
noncomputable def orderedLocalizedAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (orderedBoundaryPartition coarse e).parts) : ℝ :=
  mean fun x =>
    orderedAtomBoundaryDefect fine coarse e upper a x ^ 2 *
      partitionAtomIndicator
        (orderedBoundaryPartition coarse e) b x

/-- A conditional local defect bound gives the localized mass inequality
used by the good-configuration counting argument. -/
theorem orderedLocalizedAtomDefectSq_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (orderedBoundaryPartition coarse e).parts)
    {β : ℝ}
    (hβ :
      conditionalMean (orderedBoundaryPartition coarse e)
          (fun x =>
            orderedAtomBoundaryDefect
              fine coarse e upper a x ^ 2)
          ((orderedBoundaryPartition coarse e).representative b) ≤
        β) :
    orderedLocalizedAtomDefectSq fine coarse e upper a b ≤
      β * orderedBoundaryAtomMass coarse e b := by
  exact
    mean_mul_partitionAtomIndicator_le
      (orderedBoundaryPartition coarse e)
      (fun x =>
        orderedAtomBoundaryDefect fine coarse e upper a x ^ 2)
      b hβ

/-- Union of low-density and excessive-defect ordered coarse boundary
atoms. -/
noncomputable def orderedAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  atomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a α β

/-! ## Good local configurations and closed atom configurations -/

/-- One upper atom is good at a coarse boundary point when its coarse
conditional density is at least `α` and its coarse-boundary local average
of the squared fine--coarse defect is at most `β`. -/
def OrderedAtomIsGoodAtBoundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ) : Prop :=
  α ≤
      orderedBoundaryStructured coarse e
        (partitionAtomIndicator upper a) x ∧
    conditionalMean (orderedBoundaryPartition coarse e)
        (fun y => orderedAtomBoundaryDefect
          fine coarse e upper a y ^ 2) x ≤
      β

/-- The local-average defect clause in pointwise goodness implies the
localized global-mass clause on the canonical boundary atom. -/
theorem OrderedAtomIsGoodAtBoundary.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ)
    (hgood :
      OrderedAtomIsGoodAtBoundary
        fine coarse e upper a x α β) :
    orderedLocalizedAtomDefectSq
        fine coarse e upper a
        (orderedBoundaryAtomAt coarse e x) ≤
      β *
        orderedBoundaryAtomMass coarse e
          (orderedBoundaryAtomAt coarse e x) := by
  apply orderedLocalizedAtomDefectSq_le
  have hrep :
      (orderedBoundaryPartition coarse e).representative
          (orderedBoundaryAtomAt coarse e x) ∈
        (orderedBoundaryPartition coarse e).part x := by
    exact
      (orderedBoundaryPartition coarse e).representative_mem
        (orderedBoundaryAtomAt coarse e x)
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedBoundaryPartition coarse e)
      (fun y =>
        orderedAtomBoundaryDefect
          fine coarse e upper a y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

/-- A realizable closed atom configuration for all ranks of an ordered
partition complex.  The witness ensures that all chosen atoms are
compatible under restriction. -/
structure ClosedOrderedAtomConfiguration
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : OrderedPartitionComplex G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        (C.partition j e).parts
  mem_atom :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      orderedFaceTuple e witness ∈ (atom j e).1

namespace ClosedOrderedAtomConfiguration

/-- The canonical closed configuration realized by a full ordered tuple. -/
def ofTuple
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : OrderedPartitionComplex G k r)
    (x : Fin k → G) :
    ClosedOrderedAtomConfiguration G k r C where
  witness := x
  atom j e :=
    partitionAtomAt (C.partition j e)
      (orderedFaceTuple e x)
  mem_atom j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (orderedFaceTuple e x))

/-- Every atom of a realizable closed configuration is the canonical atom
of its witness. -/
theorem atom_eq_partitionAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (j : Fin (r + 1)) (e : OrderedFace k j.1) :
    A.atom j e =
      partitionAtomAt (C.partition j e)
        (orderedFaceTuple e A.witness) := by
  apply Subtype.ext
  exact
    ((C.partition j e).part_eq_of_mem
      (A.atom j e).2 (A.mem_atom j e)).symm

end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseAtomBridge.lean` -/

section
/-!
# Passing from fine upper atoms to coarse upper atoms

Strong ordered regularity naturally controls every atom of a fine upper
partition, while the removal argument benefits from choosing its closed
configuration in a fixed coarse complex.  This file supplies the finite
bridge between those two choices.

For a refinement `fineUpper ≤ coarseUpper`, every coarse atom is the
disjoint union of the fine atoms which it contains.  Consequently its
indicator is their sum.  Linearity then transfers cut regularity, with the
number of contained fine atoms as the exact loss.  The same decomposition,
followed by finite Cauchy--Schwarz and a fiberwise sum, controls the
coarse-upper atom-energy gap by the fine-upper gap with only one fine
complexity factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse fibers of fine atoms -/

/-- The coarse atom containing the canonical representative of a fine
atom.  Under `fineUpper ≤ coarseUpper`, the whole fine atom lies in this
coarse atom. -/
noncomputable def coarseAtomOfFineAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (b : fineUpper.parts) :
    coarseUpper.parts :=
  partitionAtomAt coarseUpper
    (fineUpper.representative b)

/-- The fiber of fine atoms assigned to one coarse atom. -/
noncomputable def fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) :
    Finset fineUpper.parts := by
  classical
  exact
    (Finset.univ : Finset fineUpper.parts).filter fun b =>
      coarseAtomOfFineAtom fineUpper coarseUpper b = a

@[simp]
theorem mem_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) (b : fineUpper.parts) :
    b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a ↔
      coarseAtomOfFineAtom fineUpper coarseUpper b = a := by
  classical
  simp [fineAtomsInCoarseAtom]

/-- Refinement puts every point of a fine atom in the coarse atom selected
by its representative. -/
theorem fineAtom_subset_coarseAtomOfFineAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (b : fineUpper.parts) :
    b.1 ⊆
      (coarseAtomOfFineAtom fineUpper coarseUpper b).1 := by
  have hsubset :=
    FacePartition.part_subset_of_le hupper
      (fineUpper.representative b)
  rw [fineUpper.part_representative b] at hsubset
  exact hsubset

/-- Taking the fine atom at a point and then passing to its coarse atom is
the same as taking the coarse atom at that point. -/
theorem coarseAtomOfFineAtom_partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (x : Ω) :
    coarseAtomOfFineAtom fineUpper coarseUpper
        (partitionAtomAt fineUpper x) =
      partitionAtomAt coarseUpper x := by
  apply Subtype.ext
  have hrepresentative :
      fineUpper.representative
          (partitionAtomAt fineUpper x) ∈
        coarseUpper.part x := by
    apply FacePartition.part_subset_of_le hupper x
    exact fineUpper.representative_mem
      (partitionAtomAt fineUpper x)
  exact coarseUpper.part_eq_of_mem
    (coarseUpper.part_mem.2 (Finset.mem_univ x))
    hrepresentative

/-- A coarse atom is exactly the union of its contained fine atoms. -/
theorem partitionAtomUnion_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) :
    partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) =
      a.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, hxb⟩ :=
      (mem_partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) x).1 hx
    have hba :
        coarseAtomOfFineAtom fineUpper coarseUpper b = a :=
      (mem_fineAtomsInCoarseAtom
        fineUpper coarseUpper a b).1 hb
    rw [← hba]
    exact fineAtom_subset_coarseAtomOfFineAtom
      hupper b hxb
  · intro hx
    apply
      (mem_partitionAtomUnion fineUpper
        (fineAtomsInCoarseAtom fineUpper coarseUpper a) x).2
    refine ⟨partitionAtomAt fineUpper x, ?_, ?_⟩
    · apply
        (mem_fineAtomsInCoarseAtom
          fineUpper coarseUpper a
          (partitionAtomAt fineUpper x)).2
      rw [coarseAtomOfFineAtom_partitionAtomAt
        hupper x]
      exact
        (partitionAtomAt_eq_iff_mem
          coarseUpper x a).2 hx
    · exact fineUpper.mem_part (Finset.mem_univ x)

/-- The indicator of a coarse atom is the sum of the indicators of its
contained fine atoms. -/
theorem partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) (x : Ω) :
    partitionAtomIndicator coarseUpper a x =
      ∑ b ∈ fineAtomsInCoarseAtom
          fineUpper coarseUpper a,
        partitionAtomIndicator fineUpper b x := by
  rw [← finsetIndicator_partitionAtomUnion
    fineUpper
    (fineAtomsInCoarseAtom fineUpper coarseUpper a) x]
  unfold partitionAtomIndicator
  rw [partitionAtomUnion_fineAtomsInCoarseAtom
    hupper a]

/-- Function-valued form of the coarse-atom indicator decomposition. -/
theorem partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts) :
    partitionAtomIndicator coarseUpper a =
      fun x =>
        ∑ b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a,
          partitionAtomIndicator fineUpper b x := by
  funext x
  exact partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom
    hupper a x

/-- A coarse fiber contains no more atoms than the whole fine
partition. -/
theorem card_fineAtomsInCoarseAtom_le_complexity
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) :
    (fineAtomsInCoarseAtom fineUpper coarseUpper a).card ≤
      FacePartition.complexity fineUpper := by
  classical
  calc
    (fineAtomsInCoarseAtom
        fineUpper coarseUpper a).card ≤
        (Finset.univ : Finset fineUpper.parts).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = FacePartition.complexity fineUpper := by
      simp [FacePartition.complexity]

/-! ## Linear transfer of cut regularity -/

/-- Conditional averaging commutes with a sum over an arbitrary finite
index set. -/
theorem conditionalMean_finset_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    (P : FacePartition Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, conditionalMean P (f i) x := by
  unfold conditionalMean
  exact Finset.expect_sum_comm (P.part x) s
    (fun y i => f i y)

/-- Boolean-cut correlation is linear over a finite sum of target
functions. -/
theorem FaceRegularityState.booleanCutCorrelation_finset_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    (S : FaceRegularityState Ω)
    (s : Finset ι) (f : ι → Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation
        (fun x => ∑ i ∈ s, f i x) A =
      ∑ i ∈ s, S.booleanCutCorrelation (f i) A := by
  unfold FaceRegularityState.booleanCutCorrelation
  calc
    mean (fun x =>
        S.residual (fun y => ∑ i ∈ s, f i y) x *
          A.eval x) =
        mean (fun x =>
          ∑ i ∈ s,
            S.residual (f i) x * A.eval x) := by
      apply congrArg mean
      funext x
      unfold FaceRegularityState.residual
        FaceRegularityState.structured
      rw [conditionalMean_finset_sum]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    _ =
        ∑ i ∈ s,
          mean (fun x =>
            S.residual (f i) x * A.eval x) :=
      mean_finset_sum s
        (fun i x => S.residual (f i) x * A.eval x)
    _ =
        ∑ i ∈ s,
          S.booleanCutCorrelation (f i) A := by
      rfl

/-- Boolean-cut version of the coarse-atom regularity transfer. -/
theorem FaceRegularityState.abs_coarseAtom_booleanCutCorrelation_le_card_mul
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω)
    {fineUpper coarseUpper : FacePartition Ω}
    (hupper : fineUpper ≤ coarseUpper)
    (a : coarseUpper.parts)
    (A : BooleanCutTest Ω)
    {ε : ℝ}
    (hregular :
      ∀ b : fineUpper.parts,
        |S.booleanCutCorrelation
          (partitionAtomIndicator fineUpper b) A| ≤ ε)
    :
    |S.booleanCutCorrelation
        (partitionAtomIndicator coarseUpper a) A| ≤
      ((fineAtomsInCoarseAtom
        fineUpper coarseUpper a).card : ℝ) * ε := by
  rw [partitionAtomIndicator_eq_sum_fineAtomsInCoarseAtom_fun
    hupper a,
    S.booleanCutCorrelation_finset_sum]
  calc
    |∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
        S.booleanCutCorrelation
          (partitionAtomIndicator fineUpper b) A| ≤
        ∑ b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a,
          |S.booleanCutCorrelation
            (partitionAtomIndicator fineUpper b) A| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _b ∈ fineAtomsInCoarseAtom
            fineUpper coarseUpper a, ε := by
      apply Finset.sum_le_sum
      intro b _
      exact hregular b
    _ =
        ((fineAtomsInCoarseAtom
          fineUpper coarseUpper a).card : ℝ) * ε := by
      simp

/-- A uniform bound on fine-upper complexity transfers preliminary
regularity itself from the fine upper system to the coarse upper system. -/
theorem IsPreliminaryOrderedRegular.coarseUpper
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (fineUpper coarseUpper :
      OrderedFacePartitionSystem G k (j + 1))
    (hupper :
      OrderedFacePartitionRefines fineUpper coarseUpper)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hregular :
      IsPreliminaryOrderedRegular lower fineUpper ε)
    (M : ℕ)
    (hcomplexity :
      ∀ e, FacePartition.complexity (fineUpper e) ≤ M) :
    IsPreliminaryOrderedRegular
      lower coarseUpper ((M : ℝ) * ε) := by
  intro e a b
  have hcard :=
    FaceRegularityState.abs_coarseAtom_booleanCutCorrelation_le_card_mul
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (hupper e) a
      (boundaryBooleanCutSupport b)
      (fun c => hregular e c b)
  exact le_trans hcard
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr
        ((card_fineAtomsInCoarseAtom_le_complexity
          (fineUpper e) (coarseUpper e) a).trans
          (hcomplexity e)))
      hε)

/-! ## Coarse-upper atom-energy gaps -/

namespace OrderedCoarseFineComplex

/-- The lower-boundary energy gap measured against the atoms of the
*coarse* upper face partition. -/
noncomputable def coarseUpperFaceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.coarse.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.coarse.partition j.succ e)

/-- Coarse-upper local gaps are nonnegative. -/
theorem coarseUpperFaceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.coarseUpperFaceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.coarse.partition j.succ e)

/-- The rank-`j` coarse-upper gap, summed over all ordered upper faces. -/
noncomputable def coarseUpperLayerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.coarse.partition j.succ)

/-- A coarse-upper layer gap is the sum of its local face gaps. -/
theorem coarseUpperLayerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.coarseUpperLayerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.coarseUpperFaceAtomEnergyGap j e := by
  unfold coarseUpperLayerAtomEnergyGap
    coarseUpperFaceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl

end OrderedCoarseFineComplex

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedEnergy.lean` -/

section
/-!
# Aggregate energy for ordered hypergraph systems

Strong regularity compares two nested partition systems simultaneously on
every ordered face.  This file packages the pointwise refinement relation,
the sum of the visible face energies, its exact Pythagorean increment, and
the elementary adjacent-gap pigeonhole principle.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A fixed enumeration used only to unfold ordered telescoping terms. -/
noncomputable local instance orderedEnergyFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) :=
  (Fintype.equivFin (OrderedFace k r)).linearOrder

/-- Pointwise refinement of ordered regularity systems.  As for
`FacePartition`, the finer system is written on the left. -/
def OrderedRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (T S : OrderedRegularitySystem G k r) : Prop :=
  ∀ e, (T e).partition ≤ (S e).partition

theorem OrderedRefines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (S : OrderedRegularitySystem G k r) :
    OrderedRefines S S :=
  fun _ => le_rfl

theorem OrderedRefines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {U T S : OrderedRegularitySystem G k r}
    (hUT : OrderedRefines U T)
    (hTS : OrderedRefines T S) :
    OrderedRefines U S :=
  fun e => (hUT e).trans (hTS e)

/-- Averaging a function pulled back along one ordered face gives its face
average. -/
theorem mean_comp_orderedFaceTuple
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    (e : OrderedFace k r)
    (f : (Fin r → G) → ℝ) :
    mean (fun x : Fin k → G =>
      f (orderedFaceTuple e x)) = mean f := by
  rw [mean_splitOrderedFace e]
  unfold mean₂
  simp

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemoval.lean` -/

section
/-!
# Bad-base cleaning for ordered hypergraph complexes

For each upper tuple, the frozen fine upper partition chooses a unique
genuine atom.  The tuple is bad when its coarse boundary lies in the bad
base attached to that very atom.  Summing over the disjoint upper atoms gives
the sharp
cleaning estimate

```
mass(own-atom bad base) ≤
  complexity(upper) * densityThreshold
    + atomEnergyGap / defectThreshold.
```

The second half of the file pulls these bad sets back to every subface of a
top ordered edge.  Exact finite Fubini preserves normalized density, and a
finite union bound gives the deletion-cost estimate needed by ordered
hypergraph removal.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Finite union bounds -/

/-- The indicator of a finite union is bounded by the sum of the
indicators. -/
theorem finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (s : Finset ι) (F : ι → Finset Ω) (x : Ω) :
    finsetIndicator (s.biUnion F) x ≤
      ∑ i ∈ s, finsetIndicator (F i) x := by
  by_cases hx : x ∈ s.biUnion F
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    rw [finsetIndicator_of_mem hx]
    calc
      1 = finsetIndicator (F i) x :=
        (finsetIndicator_of_mem hxi).symm
      _ ≤ ∑ j ∈ s, finsetIndicator (F j) x := by
        apply Finset.single_le_sum
          (s := s)
          (f := fun j => finsetIndicator (F j) x)
        · intro j hj
          by_cases hxj : x ∈ F j <;> simp [hxj]
        · exact hi
  · rw [finsetIndicator_of_not_mem hx]
    exact Finset.sum_nonneg fun i _ => by
      by_cases hxi : x ∈ F i <;> simp [hxi]

/-- Normalized finite union bound. -/
theorem mean_finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    [Fintype ι] [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (finsetIndicator (s.biUnion F)) ≤
      ∑ i ∈ s, mean (finsetIndicator (F i)) := by
  calc
    mean (finsetIndicator (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          finsetIndicator (F i) x) :=
      mean_mono (finsetIndicator_biUnion_le_sum s F)
    _ = ∑ i ∈ s, mean (finsetIndicator (F i)) :=
      mean_finset_sum s (fun i => finsetIndicator (F i))

/-! ## The bad base attached to the tuple's own upper atom -/

/-- Union, over all genuine upper atoms, of the part of that atom lying
above its own bad boundary base. -/
noncomputable def ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) : Finset Ω := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ atomBadBaseSupport fine coarse upper a α β

@[simp]
theorem mem_ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) (x : Ω) :
    x ∈ ownAtomBadBaseSupport fine coarse upper α β ↔
      x ∈ atomBadBaseSupport fine coarse upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [ownAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ atomBadBaseSupport
          fine coarse upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical :
        partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [ownAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine
      ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_inter.mpr
    exact
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

/-! ## Ordered specialization -/

/-- Tuples whose boundary lies in the bad base attached to their own
genuine upper atom. -/
noncomputable def orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  ownAtomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper α β

@[simp]
theorem mem_orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) (x : Fin (j + 1) → G) :
    x ∈ orderedOwnAtomBadBaseSupport
        fine coarse e upper α β ↔
      x ∈ orderedAtomBadBaseSupport
        fine coarse e upper
          (partitionAtomAt upper x) α β := by
  exact
    mem_ownAtomBadBaseSupport
      (orderedBoundaryPartition fine e)
      (orderedBoundaryPartition coarse e)
      upper α β x

/-! ## Pullback to top faces -/

/-- A positive-rank ordered subface of an `r`-tuple.  The first component
stores one less than its arity. -/
abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)

/-- Every smaller ordered face factors through an ordered face of any
intermediate admissible rank.  This is the exact extension lemma used to
turn survival of all top-face deletions into avoidance on every lower
face. -/
theorem exists_orderedFace_factor_through
    {k s r : ℕ} (hsr : s ≤ r) (hrk : r ≤ k)
    (f : OrderedFace k s) :
    ∃ e : OrderedFace k r, ∃ d : OrderedFace r s,
      d.trans e = f := by
  classical
  let sf : Finset (Fin k) :=
    Finset.univ.map f.toEmbedding
  have hsf_card : sf.card = s := by
    rw [show sf.card =
        (Finset.univ : Finset (Fin s)).card by
      exact Finset.card_map f.toEmbedding]
    simp
  have hsf_univ : sf ⊆ Finset.univ :=
    Finset.subset_univ sf
  obtain ⟨t, hsf_t, _ht_univ, ht⟩ :=
    Finset.exists_subsuperset_card_eq
      hsf_univ
      (by simpa [hsf_card] using hsr)
      (by simpa using hrk)
  let e : OrderedFace k r :=
    t.orderEmbOfFin ht
  have hf_mem (i : Fin s) : f i ∈ t := by
    apply hsf_t
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_univ i, rfl⟩
  let ft : Fin s ↪o t :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨f i, hf_mem i⟩)
      (fun _ _ hij => f.strictMono hij)
  let d : OrderedFace r s :=
    ft.trans (t.orderIsoOfFin ht).symm.toOrderEmbedding
  refine ⟨e, d, ?_⟩
  apply RelEmbedding.ext
  intro i
  change
    t.orderEmbOfFin ht
        ((t.orderIsoOfFin ht).symm
          ⟨f i, hf_mem i⟩) =
      f i
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp

/-- Pull a finite set on one ordered face back to the full tuple space. -/
noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]

/-- Pullback along an ordered coordinate face preserves normalized
density. -/
theorem mean_indicator_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    mean (finsetIndicator
        (orderedFacePullbackFinset d S)) =
      mean (finsetIndicator S) := by
  rw [show
      finsetIndicator (orderedFacePullbackFinset d S) =
        fun y => finsetIndicator S
          (orderedFaceTuple d y) by
    funext y
    by_cases hy : orderedFaceTuple d y ∈ S
    · rw [finsetIndicator_of_mem hy,
        finsetIndicator_of_mem]
      exact
        (mem_orderedFacePullbackFinset d S y).2 hy
    · rw [finsetIndicator_of_not_mem hy,
        finsetIndicator_of_not_mem]
      exact fun h =>
        hy ((mem_orderedFacePullbackFinset d S y).1 h)]
  exact mean_comp_orderedFaceTuple d
    (finsetIndicator S)

/-! ## Surviving tuples induce good closed configurations -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseOrderedRemoval.lean` -/

section
/-!
# Bad-base cleaning for coarse ordered atom configurations

The existing ordered cleaning argument selects upper atoms from the fine
complex.  For the eventual removal contradiction it is useful instead to
select a closed configuration in the fixed coarse complex.  The boundary
comparison is still mixed: conditional densities and square defects compare
the fine lower boundary with the coarse lower boundary, but the selected
upper atom belongs to the coarse upper partition.

This file packages that mixed goodness predicate, its own-coarse-atom bad
support, and the associated top-face deletion family.  The direct cleaning
bound is

```
coarseUpperComplexity * α + coarseUpperAtomEnergyGap / β.
```

`CoarseAtomBridge` then replaces the coarse-upper gap by one fine-upper
complexity factor times the existing fine-upper atom-energy gap.  No
configuration counting or parameter selection is performed here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse-own-atom bad bases -/

namespace OrderedCoarseFineComplex

/-- Tuples whose mixed fine/coarse boundary lies in the bad base attached
to their own atom of the coarse upper face partition. -/
noncomputable def orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) :
    Finset (Fin (j.1 + 1) → G) :=
  orderedOwnAtomBadBaseSupport
    (P.fine.partition j.castSucc)
    (P.coarse.partition j.castSucc)
    e
    (P.coarse.partition j.succ e)
    α β

@[simp]
theorem mem_orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) (x : Fin (j.1 + 1) → G) :
    x ∈ P.orderedCoarseOwnAtomBadBaseSupport j e α β ↔
      x ∈ orderedAtomBadBaseSupport
        (P.fine.partition j.castSucc)
        (P.coarse.partition j.castSucc)
        e
        (P.coarse.partition j.succ e)
        (partitionAtomAt
          (P.coarse.partition j.succ e) x)
        α β := by
  exact
    mem_orderedOwnAtomBadBaseSupport
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.castSucc)
      e (P.coarse.partition j.succ e) α β x

end OrderedCoarseFineComplex

/-! ## Mixed goodness for a coarse closed configuration -/

namespace ClosedOrderedAtomConfiguration

/-- Goodness at one successor-rank face for a configuration whose selected
upper atom is coarse, while the conditioned boundary comparison remains
fine versus coarse. -/
def IsMixedGoodAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (P.fine.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    e
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).succ e)
    (A.atom (⟨j, hj⟩ : Fin r).succ e)
    (orderedFaceTuple e A.witness)
    α β

/-- Rank-dependent mixed goodness for a realizable coarse closed atom
configuration. -/
def IsMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj : j < r) (e : OrderedFace k (j + 1)),
    A.IsMixedGoodAt P j hj e
      (α (j + 1)) (β (j + 1))

end ClosedOrderedAtomConfiguration

/-! ## Pullback to top faces -/

/-! ## Surviving tuples induce mixed-good coarse configurations -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/BundleCountingRecurrence.lean` -/

section
/-!
# Quantitative recurrence for positive bundle counts

After the analytic work at one maximal bundle edge, a good-configuration
count satisfies a scalar recurrence

```
count(s) = p(e) * count(s.erase e) + error,
```

where `0 ≤ p(e) ≤ 1` and the absolute error is uniformly bounded.  The
maximal edge may depend on `s`; no global enumeration is required.  This
file solves that recurrence on arbitrary finite edge families.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Edge-dependent recurrence errors -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedConfigurationCounting.lean` -/

section
/-!
# Positive counts for good closed ordered configurations

This file turns the local good-atom estimates into a direct positive-count
recurrence.  The edge index contains every positive-rank ordered face of an
ordered partition complex.  On downward-closed face families, the count is
the normalized mean of the selected atom indicators.  On other families we
use the exact product of the coarse densities; this total extension lets us
apply the finite abstract recurrence without asking localized estimates on
families which omit their boundary.

At a maximum-rank face, the remaining product contains every proper
boundary factor.  Thus it is supported on the canonical coarse boundary
atom.  The identity

```text
1_A = p + (E_fine 1_A - p) + (1_A - E_fine 1_A)
```

then gives the recurrence.  The uniform term is tested against a bounded
boundary product after freezing the outside variables.  The defect term is
bounded by localized Cauchy--Schwarz; the boundary support and unit bounds
make its square at most the good-atom defect threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive-rank faces and immediate downward closure -/

/-- A positive-rank ordered face of a complex with ranks `0, ..., r`.
`lowerRank = j` represents an actual face of rank `j + 1`. -/
structure PositiveOrderedFace (k r : ℕ) where
  lowerRank : Fin r
  face : OrderedFace k (lowerRank.1 + 1)
deriving DecidableEq

namespace PositiveOrderedFace

/-- Positive ordered faces are the dependent sum of their rank index and
their increasing face. -/
def equivSigma (k r : ℕ) :
    PositiveOrderedFace k r ≃
      Σ j : Fin r, OrderedFace k (j.1 + 1) where
  toFun e := ⟨e.lowerRank, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance instFintype (k r : ℕ) :
    Fintype (PositiveOrderedFace k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, OrderedFace k (j.1 + 1))
    (equivSigma k r).symm

/-- Actual cardinality/rank of a positive ordered face. -/
def rank {k r : ℕ} (e : PositiveOrderedFace k r) : ℕ :=
  e.lowerRank.1 + 1

@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]

/-- A positive immediate boundary face, obtained by erasing one coordinate.
The positivity hypothesis says that the original face has rank at least
two. -/
noncomputable def boundary
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨e.lowerRank.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.lowerRank.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.lowerRank.1 := by
    simp only [j]
    omega
  exact hj ▸ eraseBoundaryFace e.face i

@[simp]
theorem boundary_lowerRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).lowerRank.1 =
      e.lowerRank.1 - 1 := by
  rfl

theorem boundary_rank_lt
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).rank < e.rank := by
  simp only [rank, boundary_lowerRank]
  omega

end PositiveOrderedFace

/-- A positive face family contains every positive immediate boundary face
of each of its members. -/
def IsDownwardClosedPositiveFaces
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r)) : Prop :=
  ∀ (e : PositiveOrderedFace k r), e ∈ s →
    ∀ (hpos : 0 < e.lowerRank.1)
      (i : Fin (e.lowerRank.1 + 1)),
      e.boundary hpos i ∈ s

theorem downwardClosed_empty
    {k r : ℕ} :
    IsDownwardClosedPositiveFaces
      (∅ : Finset (PositiveOrderedFace k r)) := by
  intro e he
  simp at he

/-! ## Missing coordinates for lower-or-equal rank faces -/

/-! ## Selected atom weights and counts -/

/-- Indicator of the atom selected by a closed configuration at one
positive-rank face. -/
def configurationFaceWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (C.partition e.lowerRank.succ e.face)
    (A.atom e.lowerRank.succ e.face) y

theorem configurationFaceWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ configurationFaceWeight A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem configurationFaceWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

/-- Product of the selected atom indicators over a partial positive-face
family. -/
noncomputable def partialConfigurationWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    configurationFaceWeight A e
      (orderedFaceTuple e.face x)

/-- Normalized count of one partial closed atom configuration. -/
noncomputable def partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  mean (partialConfigurationWeight A s)

/-- Full normalized count of the selected positive-rank atoms. -/
noncomputable def fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) : ℝ :=
  partialConfigurationCount A Finset.univ

@[simp]
theorem partialConfigurationWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    partialConfigurationWeight A ∅ x = 1 := by
  simp [partialConfigurationWeight]

@[simp]
theorem partialConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    partialConfigurationCount A ∅ = 1 := by
  change mean (fun _x : Fin k → G => (1 : ℝ)) = 1
  exact mean_const 1

theorem partialConfigurationWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    partialConfigurationWeight A s x ≤ 1 := by
  unfold partialConfigurationWeight
  apply Finset.prod_le_one
  · intro e he
    exact configurationFaceWeight_nonneg A e _
  · intro e he
    exact configurationFaceWeight_le_one A e _

/-! ## Freezing and grouping a maximum-rank remainder -/

/-! ## Coarse densities, defects, and boundary support -/

/-- Rank-normalized lower layer attached to a positive face. -/
def positiveFaceLowerLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    OrderedFacePartitionSystem G k e.lowerRank.1 :=
  C.partition e.lowerRank.castSucc

/-- Coarse conditional density of the selected fine atom at one face. -/
noncomputable def configurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

/-- A nonzero selected factor on an immediate positive boundary face puts
the erased tuple in the corresponding coarse boundary atom. -/
theorem coarse_boundary_mem_of_boundary_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  rcases e with ⟨⟨n, hn⟩, eface⟩
  cases n with
  | zero =>
      simp at hpos
  | succ n =>
      let f :=
        (⟨⟨n, by omega⟩,
            eraseBoundaryFace eface i⟩ :
          PositiveOrderedFace k r)
      have hfine :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hweight
          (partitionAtomIndicator_of_not_mem
            (P.fine.partition f.lowerRank.succ f.face)
            (A.atom f.lowerRank.succ f.face) hnot)
      have hcanonical :
          (A.atom f.lowerRank.succ f.face).1 =
            (P.fine.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) := by
        exact congrArg Subtype.val
          (A.atom_eq_partitionAtomAt
            f.lowerRank.succ f.face)
      rw [hcanonical] at hfine
      have hcoarse :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) :=
        FacePartition.part_subset_of_le
          (P.refines f.lowerRank.succ f.face)
          (orderedFaceTuple f.face A.witness) hfine
      let j : Fin (r + 1) :=
        ⟨n + 1, Nat.lt_succ_of_lt hn⟩
      have hfj : f.lowerRank.succ = j := by
        apply Fin.ext
        rfl
      have hcoarse' :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition j f.face).part
              (orderedFaceTuple f.face A.witness) := by
        subst j
        exact hcoarse
      simpa [f, j, positiveFaceLowerLayer,
        OrderedPartitionComplex.layer] using hcoarse'

/-! ## Selected-face contributions and exact decomposition -/

/-! ## Uniform contribution -/

/-! ## Localized defect contribution -/

/-! ## The one-face recurrence -/

/-- Extend the genuine partial configuration count to all positive-face
families.  Non-closed families use the exact product of coarse densities;
this is only an induction device, and agrees with the genuine count on the
full downward-closed family. -/
noncomputable def extendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, configurationCoarseDensity P A e

@[simp]
theorem extendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine) :
    extendedConfigurationCount P A ∅ = 1 := by
  rw [extendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

/-! ## Quantitative full-count lower bound and positivity -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseConfigurationCounting.lean` -/

section
/-!
# Positive counts for mixed-good coarse configurations

A closed configuration in this file selects atoms of the coarse complex.
The selected coarse upper atom is decomposed using conditional expectation
first on the fine lower boundary and then on the coarse lower boundary.
Thus the main density and defect are exactly those controlled by
`ClosedOrderedAtomConfiguration.IsMixedGood`, while the uniform term is
controlled by regularity of the fine lower boundary against the coarse upper
partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A diagonal pair used only for coarse boundary support -/

/-- Regard the coarse endpoint as both sides of a coarse/fine pair.  This
lets the generic boundary-support lemmas for configuration weights be reused
without introducing a second copy of their combinatorial proof. -/
def OrderedCoarseFineComplex.coarseDiagonal
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    OrderedCoarseFineComplex G k r where
  coarse := P.coarse
  fine := P.coarse
  refines := OrderedPartitionComplex.Refines.refl P.coarse

/-! ## Mixed coarse/fine conditional decomposition -/

/-- Coarse-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

/-- Fine-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

/-- Fine-boundary density minus the coarse-boundary density selected by the
configuration witness. -/
noncomputable def mixedConfigurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationFineDensity P A e y -
    mixedConfigurationCoarseDensity P A e

/-- Residual of a coarse upper atom after conditioning on the fine lower
boundary. -/
noncomputable def mixedConfigurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    mixedConfigurationFineDensity P A e y

/-- Indicator of the canonical coarse boundary atom determined by the
coarse configuration witness. -/
noncomputable def mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y

/-- Exact three-term decomposition of a selected coarse atom. -/
theorem mixedConfigurationFaceWeight_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y =
      mixedConfigurationCoarseDensity P A e +
        mixedConfigurationDefect P A e y +
        mixedConfigurationUniform P A e y := by
  unfold mixedConfigurationDefect mixedConfigurationUniform
  ring

/-! ## Coarse boundary support and selected-face decomposition -/

/-- A nonzero immediate boundary weight lies in the coarse boundary atom
selected by the coarse configuration. -/
theorem coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  exact
    coarse_boundary_mem_of_boundary_weight_ne_zero
      P.coarseDiagonal A e hpos i x hweight

/-! ## Mixed coarse-upper regularity and the uniform contribution -/

/-- At every rank, the fine lower boundary is regular against the coarse
upper atom family. -/
def IsFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (τ : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      (τ j)

/-- Mixed all-rank preliminary regularity specializes to the selected coarse
upper atom at a positive face. -/
theorem mixedConfigurationFace_isFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (e : PositiveOrderedFace k r) :
    (⟨orderedBoundaryPartition
        (positiveFaceLowerLayer P.fine e) e.face⟩ :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G)).IsFaceCutRegular
      (partitionAtomIndicator
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face))
      (τ e.lowerRank) := by
  rw [positiveFaceLowerLayer]
  exact
    (hregular e.lowerRank).toBounded
      e.face
      (A.atom e.lowerRank.succ e.face)

/-! ## Localized mixed defect contribution -/

/-- On the canonical coarse boundary atom, the mixed configuration defect
is the usual fine-minus-coarse boundary defect of the selected coarse upper
atom. -/
theorem mixedConfigurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    mixedConfigurationDefect P A e y *
        mixedConfigurationBoundaryIndicator P A e y =
      orderedAtomBoundaryDefect
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face) y *
        mixedConfigurationBoundaryIndicator P A e y := by
  let Q :=
    orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face
  let b : Q.parts :=
    orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness)
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  by_cases hy : y ∈ b.1
  · have hcoarse :
        conditionalMean Q f y =
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) := by
      exact conditionalMean_eq_of_mem_part Q f hy
    rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_mem _ _ hy,
      mul_one, mul_one]
    change
      conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) =
        conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f y
    rw [hcoarse]
  · rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_not_mem _ _ hy,
      mul_zero, mul_zero]

/-! ## One-face recurrence -/

/-! ## Rank-dependent totalized recurrence -/

/-- Extend a partial coarse-configuration count to arbitrary face families.
As in the fine-configuration argument, non-downward-closed families use the
exact product of their mixed coarse densities only as an induction device. -/
noncomputable def mixedExtendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, mixedConfigurationCoarseDensity P A e

@[simp]
theorem mixedExtendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    mixedExtendedConfigurationCount P A ∅ = 1 := by
  rw [mixedExtendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

/-! ## Rankwise full-count lower bounds -/

/-! ## Fine-regular complexity corollaries -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/ConfigurationWeightedDefect.lean` -/

section
/-!
# Configuration-weighted defect estimates

The first coarse-configuration counting lemma bounds the square of a defect
contribution by the bare goodness threshold `β`.  Its Cauchy--Schwarz proof
actually retains the square mean of the remaining configuration weight.
Since every configuration factor is an atom indicator, that square mean is
exactly the remaining partial configuration count.

This file records the sharper estimate

```
defectContribution ^ 2 ≤ β * partialConfigurationCount (s.erase e).
```

It is useful for parameter hierarchies: a defect introduced while adjoining
a maximal face is charged relative to the already-counted lower
configuration, rather than against the ambient probability space.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Idempotence of configuration indicators -/

/-! ## The mixed defect with its remaining-count factor -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationBridge.lean` -/

section
/-!
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/

/-- The (unordered) range edge of a positive ordered face. -/
def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]

theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega

@[simp]
theorem mem_positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (v : Fin k) :
    v ∈ positiveOrderedFaceEdge e ↔
      v ∈ Set.range e.face := by
  simp [positiveOrderedFaceEdge]

/-- The positive ordered face obtained by increasingly enumerating a
nonempty edge of cardinality at most `r`. -/
noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  simp [positiveOrderedFaceEdge,
    positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _

/-- Passing from a positive ordered face to its range edge is injective:
an increasing enumeration of a finite linearly ordered set is unique. -/
theorem positiveOrderedFaceEdge_injective
    {k r : ℕ} :
    Function.Injective
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)) := by
  intro e f hef
  have hrank : e.rank = f.rank := by
    rw [← positiveOrderedFaceEdge_card e,
      ← positiveOrderedFaceEdge_card f, hef]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [PositiveOrderedFace.rank] at hrank
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) hef
    simpa [positiveOrderedFaceEdge] using hv
  have hef' : e = f :=
    (OrderEmbedding.range_inj).mp hrange
  subst f
  rfl

@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)

/-! ## The complete initial bundle -/

/-- The base hypergraph consisting of the empty edge and every positive
ordered edge of rank at most `r`. -/
noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]

theorem empty_not_mem_positiveOrderedFaceEdge_image
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (positiveOrderedFaceEdge :
          PositiveOrderedFace k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, hedge⟩ :=
    Finset.mem_image.mp h
  exact (positiveOrderedFaceEdge_nonempty e).ne_empty
    hedge

/-- The explicit edge family is exactly the family of subsets of
cardinality at most `r`. -/
@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

/-- The initial bundle has one occurrence vertex above each base vertex
and uses the identity projection. -/
noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg

@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl

theorem orderedConfigurationInitialBundle_closed
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).IsClosedUnderInclusion := by
  intro g hg f hfg
  rw [orderedConfigurationInitialBundle_edges] at hg ⊢
  rw [mem_orderedConfigurationBaseEdges_iff] at hg ⊢
  exact (Finset.card_le_card hfg).trans hg

/-! ## Canonical local tuples and base weights -/

/-- Reindex a tuple on a nonempty finite edge by its increasing
enumeration. -/
noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)

/-- The increasing order isomorphism of a positive face range recovers
the original ordered-face coordinate. -/
@[simp]
theorem positiveOrderedFaceEdge_orderIsoOfFin_val
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (i : Fin (e.lowerRank.1 + 1)) :
    ((positiveOrderedFaceEdge e).orderIsoOfFin
        (by
          simp [PositiveOrderedFace.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have hcanonical :
      e.face =
        (positiveOrderedFaceEdge e).orderEmbOfFin
          (by
            simp [PositiveOrderedFace.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [positiveOrderedFaceEdge]
  exact congrArg (fun f => f i) hcanonical.symm

/-- Indicator base weights corresponding to a closed ordered atom
configuration.  The empty edge and irrelevant edges carry weight one. -/
noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]

/-- On the range of a positive face, the canonical edge tuple is the
usual ordered-face tuple. -/
@[simp]
theorem orderedConfigurationBaseWeight_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y :
      {v : Fin k // v ∈ positiveOrderedFaceEdge e} → G) :
    orderedConfigurationBaseWeight A
        (positiveOrderedFaceEdge e) y =
      configurationFaceWeight A e
        (fun i =>
          y ⟨e.face i,
            (mem_positiveOrderedFaceEdge e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [orderedConfigurationBaseWeight,
    dif_pos (positiveOrderedFaceEdge_nonempty e),
    dif_pos (positiveOrderedFaceEdge_card_le e)]
  change
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
        ⟨positiveOrderedFaceOfEdge
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e),
          orderedConfigurationEdgeTuple
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e) y⟩ =
      (fun p :
          (Σ f : PositiveOrderedFace k r,
            Fin (f.lowerRank.1 + 1) → G) =>
        configurationFaceWeight A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (mem_positiveOrderedFaceEdge e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
  have he :
      positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e) = e :=
    positiveOrderedFaceOfEdge_edge e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : PositiveOrderedFace k r =>
        Fin (f.lowerRank.1 + 1)) he)
  intro i i' hii
  apply heq_of_eq
  unfold orderedConfigurationEdgeTuple
  apply congrArg y
  apply Subtype.ext
  have hn :
      (positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e)).lowerRank.1 + 1 =
        e.lowerRank.1 + 1 :=
    congrArg (fun f : PositiveOrderedFace k r =>
      f.lowerRank.1 + 1) he
  have hval : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans hii)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have hcastVal :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact hcastVal hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (positiveOrderedFaceEdge e).orderEmbOfFin _ i =
        (positiveOrderedFaceEdge e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hval
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        positiveOrderedFaceEdge_orderIsoOfFin_val e i'

/-- The configuration indicator weights take values in the unit
interval on the whole base hypergraph. -/
theorem orderedConfigurationBaseWeight_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsInUnitInterval
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      exact
        ⟨configurationFaceWeight_nonneg A _ _,
          configurationFaceWeight_le_one A _ _⟩
    · simp [htr]
  · simp [ht0]

/-- The configuration base weights are pointwise idempotent, as required
when duplicate bundle edges are identified. -/
theorem orderedConfigurationBaseWeight_idempotent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsIdempotent
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      simpa [configurationFaceWeight, pow_two] using
        (partitionAtomIndicator_sq
          (C.partition
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (A.atom
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (orderedConfigurationEdgeTuple t ht0 htr y))
    · simp [htr]
  · simp [ht0]

/-! ## Main densities -/

/-- The base main density attached to a mixed coarse configuration.  As
for the weight, the empty and irrelevant edges carry the neutral value
one. -/
noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dif_pos (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dif_pos hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)

/-! ## Exact initial count and product identities -/

/-- With the identity projection, transporting an edge tuple to the base
edge does not change any of its values. -/
theorem orderedConfigurationInitialBundle_projectedEdgeTuple
    {G : Type*} {k r : ℕ}
    {g : Finset (Fin k)}
    (hg :
      g ∈ (orderedConfigurationInitialBundle k r).edges)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).projectedEdgeTuple hg
          (HypergraphBundle.edgeTuple g x) =
      fun j => x j.1 := by
  funext j
  have hj :
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 := by
    have happly :=
      congrArg Subtype.val
        (((orderedConfigurationInitialBundle k r).projectionEquiv hg).apply_symm_apply j)
    change
      (orderedConfigurationInitialBundle k r).projection
          (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    change
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    exact happly
  unfold HypergraphBundle.projectedEdgeTuple
    HypergraphBundle.edgeTuple
  exact congrArg x hj

theorem orderedConfigurationInitialBundle_pullback_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (HypergraphBundle.edgeTuple ∅ x) = 1 := by
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      (empty_mem_orderedConfigurationBaseEdges k r)]
  exact orderedConfigurationBaseWeight_empty A _

/-- A positive-face factor in the pulled-back initial bundle is exactly
the corresponding selected atom indicator. -/
theorem orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)
          (positiveOrderedFaceEdge e)
          (HypergraphBundle.edgeTuple
            (positiveOrderedFaceEdge e) x) =
      configurationFaceWeight A e
        (orderedFaceTuple e.face x) := by
  have hedge :
      positiveOrderedFaceEdge e ∈
        (orderedConfigurationInitialBundle k r).edges := by
    rw [orderedConfigurationInitialBundle_edges,
      mem_orderedConfigurationBaseEdges_iff]
    exact positiveOrderedFaceEdge_card_le e
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hedge]
  have himage :
      (positiveOrderedFaceEdge e).image
          (orderedConfigurationInitialBundle k r).projection =
        positiveOrderedFaceEdge e := by
    simpa only [orderedConfigurationInitialBundle_projection] using
      (Finset.image_id :
        (positiveOrderedFaceEdge e).image id =
          positiveOrderedFaceEdge e)
  have hpair :
      (⟨(positiveOrderedFaceEdge e).image
            (orderedConfigurationInitialBundle k r).projection,
          (orderedConfigurationInitialBundle k r).projectedEdgeTuple
            hedge
            (HypergraphBundle.edgeTuple
              (positiveOrderedFaceEdge e) x)⟩ :
        Σ t : Finset (Fin k), ({j : Fin k // j ∈ t} → G)) =
      ⟨positiveOrderedFaceEdge e,
        HypergraphBundle.edgeTuple
          (positiveOrderedFaceEdge e) x⟩ := by
    apply Sigma.ext himage
    simp only
    apply Function.hfunext
      (congrArg
        (fun t : Finset (Fin k) =>
          {j : Fin k // j ∈ t}) himage)
    intro j j' hjj
    apply heq_of_eq
    rw [congrFun
      (orderedConfigurationInitialBundle_projectedEdgeTuple
        hedge x) j]
    apply congrArg x
    exact
      (Subtype.heq_iff_coe_eq
        (fun v : Fin k => by
          rw [himage])).1 hjj
  have hweight :=
    congrArg
      (fun p :
          (Σ t : Finset (Fin k),
            ({j : Fin k // j ∈ t} → G)) =>
        orderedConfigurationBaseWeight A p.1 p.2)
      hpair
  rw [hweight]
  rw [orderedConfigurationBaseWeight_positiveOrderedFaceEdge]
  apply congrArg (configurationFaceWeight A e)
  funext i
  rfl

/-- Pointwise, the product of all initial bundle factors is the full
ordered-configuration indicator. -/
theorem orderedConfigurationInitialBundle_bundleProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).bundleProduct
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) x =
      partialConfigurationWeight A Finset.univ x := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [orderedConfigurationInitialBundle_edges]
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r)]
  rw [orderedConfigurationInitialBundle_pullback_empty]
  simp only [one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  unfold partialConfigurationWeight
  apply Finset.prod_congr rfl
  intro e he
  exact
    orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
      A e x

/-- The normalized initial bundle count is exactly the full ordered
configuration count. -/
theorem orderedConfigurationInitialBundle_bundleCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    (orderedConfigurationInitialBundle k r).bundleCount
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) =
      fullConfigurationCount A := by
  unfold HypergraphBundle.bundleCount
    fullConfigurationCount partialConfigurationCount
  apply congrArg mean
  funext x
  exact orderedConfigurationInitialBundle_bundleProduct A x

/-- The main product of the initial bundle is the product of all mixed
coarse densities; the extra empty-edge factor is one. -/
theorem orderedConfigurationInitialBundle_bundleMainProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    (orderedConfigurationInitialBundle k r).bundleMainProduct
          (orderedConfigurationBaseDensity P A) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      orderedConfigurationBaseDensity P A
        (g.image
          (orderedConfigurationInitialBundle k r).projection)) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [orderedConfigurationInitialBundle_edges,
    orderedConfigurationInitialBundle_projection]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      orderedConfigurationBaseDensity P A g) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r),
    orderedConfigurationBaseDensity_empty,
    one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  simp

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean` -/

section
/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/

/-- On a subbundle with the same occurrence projection, pulling a base
weight back before or after passing to the subbundle gives the same
bundle product. -/
theorem bundleProduct_pullback_eq_of_subset_of_projection_eq
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G)
    (x : K → G) :
    C.bundleProduct (B.pullbackBaseEdgeWeight A) x =
      C.bundleProduct (C.pullbackBaseEdgeWeight A) x := by
  unfold bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  exact B.pullbackBaseEdgeWeight_eq_of_projection_eq
    C A hprojection (hCB hg) hg (edgeTuple g x)

/-- Count-level version of canonical pullback invariance. -/
theorem bundleCount_pullback_eq_of_subset_of_projection_eq
    [Fintype K] [Fintype G]
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G) :
    C.bundleCount (B.pullbackBaseEdgeWeight A) =
      C.bundleCount (C.pullbackBaseEdgeWeight A) := by
  unfold bundleCount
  apply congrArg mean
  funext x
  exact B.bundleProduct_pullback_eq_of_subset_of_projection_eq
    C hCB hprojection A x

/-- In particular, the erased count may always be written using the
canonical pullback of the erased bundle. -/
theorem eraseEdge_bundleCount_pullback
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (A : BaseEdgeWeight J G) :
    (B.eraseEdge g₀).bundleCount
        (B.pullbackBaseEdgeWeight A) =
      (B.eraseEdge g₀).bundleCount
        ((B.eraseEdge g₀).pullbackBaseEdgeWeight A) := by
  apply B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.eraseEdge g₀)
  · exact Finset.erase_subset _ _
  · rfl

/-! ## Structural bounds for the two outer-induction bundles -/

/-- The duplicated lower-order bundle remains downward closed. -/
theorem duplicateOutside_lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).IsClosedUnderInclusion := by
  apply (B.lowerOrder g₀.card).duplicateOutside_closed
    g₀
  intro g hg f hfg
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  have hfLower :
      f ∈ (B.lowerOrder g₀.card).edges :=
    B.lowerOrder_closed hclosed g₀.card
      hgLower hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfLower⟩
  intro hfg₀
  subst f
  have hgcard :
      g.card < g₀.card :=
    ((B.mem_lowerOrder_edges g₀.card g).1
      hgLower).2
  have hcardle : g₀.card ≤ g.card :=
    Finset.card_le_card hfg
  exact (Nat.not_le_of_gt hgcard) hcardle

/-- Duplicating the lower-order subbundle still has order strictly below
the selected edge. -/
theorem duplicateOutside_lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).order <
      g₀.card := by
  exact
    ((B.lowerOrder g₀.card).duplicateOutside_order_le
      g₀).trans_lt
      (B.lowerOrder_order_lt
        (Finset.card_pos.mpr hg₀))

/-- The duplicated lower-order bundle has at most twice as many edges as
the original bundle. -/
theorem card_duplicateOutside_lowerOrder_le
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card ≤
      2 * B.edges.card := by
  calc
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card =
        ((B.lowerOrder g₀.card).doubledEdges g₀).card := by
      rfl
    _ ≤
        2 *
          ((B.lowerOrder g₀.card).edges.erase g₀).card :=
      (B.lowerOrder g₀.card).card_doubledEdges_le g₀
    _ ≤ 2 * (B.lowerOrder g₀.card).edges.card :=
      Nat.mul_le_mul_left 2
        Finset.card_erase_le
    _ ≤ 2 * B.edges.card :=
      Nat.mul_le_mul_left 2
        (B.card_lowerOrder_edges_le g₀.card)

/-! ## Elementary main-product and induction helpers -/

/-- A bundle of positive order has a maximal occurrence edge which
realizes its order. -/
theorem exists_edge_card_eq_order
    (B : HypergraphBundle J K H)
    (horder : 0 < B.order) :
    ∃ g₀ ∈ B.edges,
      g₀.card = B.order ∧
        ∀ g ∈ B.edges, g.card ≤ g₀.card := by
  have hedges : B.edges.Nonempty := by
    by_contra hempty
    have hbe : B.edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [order, hbe] at horder
  obtain ⟨g₀, hg₀, hsup⟩ :=
    Finset.exists_mem_eq_sup B.edges hedges Finset.card
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · simpa [order] using hsup.symm
  · intro g hg
    rw [← hsup]
    exact Finset.le_sup hg

/-- A relative absolute-error estimate gives the corresponding upper
bound for the count. -/
theorem count_le_one_add_error_mul_main
    {count main error : ℝ}
    (herror : |count - main| ≤ error * main) :
    count ≤ (1 + error) * main := by
  have hleft : count - main ≤ |count - main| :=
    le_abs_self _
  calc
    count ≤ main + |count - main| := by
      linarith
    _ ≤ main + error * main :=
      add_le_add_right herror main
    _ = (1 + error) * main := by
      ring

/-- It is enough to check a density floor on the actual occurrence edges
of a bundle. -/
theorem pow_card_edges_le_bundleMainProduct_of_edges
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        exact hp g hg

/-- The selected density together with all other selected-rank densities
is bounded below by one floor factor per edge of the original bundle. -/
theorem pow_card_edges_le_selected_mul_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^ B.edges.card ≤
      p (g₀.image B.projection) *
        B.maximalRemainderMainProduct g₀ p := by
  let s :=
    (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)
  have hscard :
      s.card ≤ (B.edges.erase g₀).card :=
    B.card_maximalRemainder_le_erase g₀
  have hpmax :
      a ^ s.card ≤
        B.maximalRemainderMainProduct g₀ p :=
    B.pow_card_maximalRemainder_le
      hmax p ha0 hp
  have hpow :
      a ^ (B.edges.erase g₀).card ≤
        a ^ s.card :=
    pow_le_pow_of_le_one ha0 ha1 hscard
  have hremain :
      a ^ (B.edges.erase g₀).card ≤
        B.maximalRemainderMainProduct g₀ p :=
    hpow.trans hpmax
  have hselected :
      a ≤ p (g₀.image B.projection) := by
    apply hp _ (B.projection_mem_base g₀ hg₀)
    exact B.card_image_projection hg₀
  have hselected0 :
      0 ≤ p (g₀.image B.projection) :=
    ha0.trans hselected
  calc
    a ^ B.edges.card =
        a * a ^ (B.edges.erase g₀).card := by
      rw [← Finset.card_erase_add_one hg₀,
        pow_succ, mul_comm]
    _ ≤
        p (g₀.image B.projection) *
          a ^ (B.edges.erase g₀).card :=
      mul_le_mul_of_nonneg_right hselected
        (pow_nonneg ha0 _)
    _ ≤
        p (g₀.image B.projection) *
          B.maximalRemainderMainProduct g₀ p :=
      mul_le_mul_of_nonneg_left hremain hselected0

/-- Neutral empty-edge weights make every order-zero bundle count exact. -/
theorem bundleCount_eq_bundleMainProduct_of_order_zero
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (horder : B.order = 0) :
    B.bundleCount (B.pullbackBaseEdgeWeight A) =
      B.bundleMainProduct p := by
  have hedgeEmpty :
      ∀ g ∈ B.edges, g = ∅ := by
    intro g hg
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp
      (horder ▸ B.edge_card_le_order hg)
  have hproduct :
      ∀ x : K → G,
        B.bundleProduct
            (B.pullbackBaseEdgeWeight A) x = 1 := by
    intro x
    unfold bundleProduct
    apply Finset.prod_eq_one
    intro g hg
    have hge : g = ∅ :=
      hedgeEmpty g hg
    subst g
    rw [B.pullbackBaseEdgeWeight_of_mem A hg]
    exact hAempty _
  have hmain :
      B.bundleMainProduct p = 1 := by
    unfold bundleMainProduct
    apply Finset.prod_eq_one
    intro g hg
    rw [hedgeEmpty g hg]
    simp [hpempty]
  rw [hmain]
  unfold bundleCount
  calc
    mean
        (B.bundleProduct
          (B.pullbackBaseEdgeWeight A)) =
        mean (fun _x : K → G => 1) := by
      apply congrArg mean
      funext x
      exact hproduct x
    _ = 1 := mean_const 1

end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

/-- The exact analytic output of one maximal-edge step in Tao's bundle
counting proof.  No induction estimate or density normalization is hidden
in this hypothesis. -/
def HasTaoBundleCountingStep
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.bundleCount (B.pullbackBaseEdgeWeight A) -
          p (g₀.image B.projection) *
            (B.eraseEdge g₀).bundleCount
              ((B.eraseEdge g₀).pullbackBaseEdgeWeight A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.strictBoundary g₀).bundleCount
                ((B.strictBoundary g₀).pullbackBaseEdgeWeight A) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                  A)) +
          τ

/-! ## Full double induction -/

omit [DecidableEq G] in
/-- **Relative generalized bundle counting.**  A source-faithful
maximal-edge analytic step and a numerical envelope control every closed
bundle, uniformly in its occurrence-vertex type. -/
theorem abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
    [Nonempty G]
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hA01 :
      HypergraphBundle.BaseWeightsInUnitInterval H A)
    (_hAidempotent :
      HypergraphBundle.BaseWeightsIdempotent H A)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (hpLower :
      ∀ e ∈ H, α e.card ≤ p e)
    (hstep :
      HasTaoBundleCountingStep
        (H := H) A p β τ)
    (hE :
      IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount (B.pullbackBaseEdgeWeight A) -
        B.bundleMainProduct p| ≤
      E B.order B.edges.card *
        B.bundleMainProduct p := by
  let P : ℕ → ℕ → Prop :=
    fun d n =>
      ∀ (K' : Type) [Fintype K'] [DecidableEq K']
        (C : HypergraphBundle J K' H),
        C.order ≤ d →
        C.edges.card ≤ n →
        C.IsClosedUnderInclusion →
        |C.bundleCount (C.pullbackBaseEdgeWeight A) -
            C.bundleMainProduct p| ≤
          E d n * C.bundleMainProduct p
  have hp0 :
      ∀ e ∈ H, 0 ≤ p e := by
    intro e he
    exact (hE.density_pos e.card).le.trans
      (hpLower e he)
  unfold HasTaoBundleCountingStep at hstep
  have hP : ∀ d n, P d n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihOrder =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihCard =>
            dsimp [P]
            intro K' _instK' _decK' C hCd hCn hclosedC
            by_cases horderEq : C.order = d
            · by_cases hcardEq : C.edges.card = n
              · by_cases hd0 : d = 0
                · have hzero : C.order = 0 :=
                    horderEq.trans hd0
                  have hexact :=
                    C.bundleCount_eq_bundleMainProduct_of_order_zero
                      A p hAempty hpempty hzero
                  rw [hexact, sub_self, abs_zero]
                  exact mul_nonneg
                    (hE.error_nonneg d n)
                    (C.bundleMainProduct_nonneg p hp0)
                · have hdpos : 0 < d :=
                    Nat.pos_of_ne_zero hd0
                  obtain ⟨g₀, hg₀, hgcard, hmax⟩ :=
                    C.exists_edge_card_eq_order
                      (horderEq.symm ▸ hdpos)
                  have hgcardD : g₀.card = d :=
                    hgcard.trans horderEq
                  have hg₀ne : g₀.Nonempty := by
                    apply Finset.card_pos.mp
                    rw [hgcardD]
                    exact hdpos
                  obtain ⟨d₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hd0
                  have hn0 : n ≠ 0 := by
                    intro hn
                    have hcardzero : C.edges.card = 0 :=
                      hcardEq.trans hn
                    exact
                      (Finset.card_ne_zero.mpr
                        ⟨g₀, hg₀⟩) hcardzero
                  obtain ⟨n₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hn0
                  let Cerase := C.eraseEdge g₀
                  let Cboundary := C.strictBoundary g₀
                  let Clower :=
                    (C.lowerOrder g₀.card).duplicateOutside g₀
                  have hCeraseClosed :
                      Cerase.IsClosedUnderInclusion :=
                    C.eraseEdge_closed_of_maximal
                      hclosedC hg₀ hmax
                  have hCeraseOrder :
                      Cerase.order ≤ d₀ + 1 := by
                    exact
                      (C.eraseEdge_order_le g₀).trans_eq
                        horderEq
                  have hCeraseCard :
                      Cerase.edges.card ≤ n₀ := by
                    have hcard :
                        Cerase.edges.card = n₀ := by
                      simp [Cerase,
                        Finset.card_erase_of_mem hg₀,
                        hcardEq]
                    exact hcard.le
                  have hEraseIH :=
                    (ihCard n₀ (Nat.lt_succ_self n₀))
                      K' Cerase hCeraseOrder
                        hCeraseCard hCeraseClosed
                  have hCboundaryClosed :
                      Cboundary.IsClosedUnderInclusion :=
                    C.strictBoundary_closed hclosedC g₀
                  have hCboundaryOrder :
                      Cboundary.order ≤ d₀ := by
                    have hlt :
                        Cboundary.order < d₀ + 1 := by
                      simpa [Cboundary, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.strictBoundary_order_lt hg₀ne
                    omega
                  have hCboundaryCard :
                      Cboundary.edges.card ≤ n₀ + 1 := by
                    exact
                      (C.card_strictBoundary_edges_le g₀).trans_eq
                        hcardEq
                  have hBoundaryIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (n₀ + 1))
                      K' Cboundary hCboundaryOrder
                        hCboundaryCard hCboundaryClosed
                  have hClowerClosed :
                      Clower.IsClosedUnderInclusion := by
                    dsimp [Clower]
                    exact C.duplicateOutside_lowerOrder_closed
                      hclosedC g₀
                  have hClowerOrder :
                      Clower.order ≤ d₀ := by
                    have hlt :
                        Clower.order < d₀ + 1 := by
                      simpa [Clower, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.duplicateOutside_lowerOrder_order_lt
                          hg₀ne
                    omega
                  have hClowerCard :
                      Clower.edges.card ≤
                        2 * (n₀ + 1) := by
                    dsimp [Clower]
                    exact
                      (C.card_duplicateOutside_lowerOrder_le
                        g₀).trans_eq
                        (congrArg (fun m => 2 * m)
                          hcardEq)
                  have hLowerIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (2 * (n₀ + 1)))
                      (HypergraphBundle.DoubledOccurrenceVertex g₀)
                      Clower hClowerOrder
                        hClowerCard hClowerClosed
                  let mainErase :=
                    Cerase.bundleMainProduct p
                  let mainBoundary :=
                    Cboundary.bundleMainProduct p
                  let mainLower :=
                    Clower.bundleMainProduct p
                  let mainLowerOrder :=
                    (C.lowerOrder g₀.card).bundleMainProduct p
                  let mainMax :=
                    C.maximalRemainderMainProduct g₀ p
                  let mainC := C.bundleMainProduct p
                  let countErase :=
                    Cerase.bundleCount
                      (Cerase.pullbackBaseEdgeWeight A)
                  let countBoundary :=
                    Cboundary.bundleCount
                      (Cboundary.pullbackBaseEdgeWeight A)
                  let countLower :=
                    Clower.bundleCount
                      (Clower.pullbackBaseEdgeWeight A)
                  let p₀ :=
                    p (g₀.image C.projection)
                  have hmainErase0 : 0 ≤ mainErase := by
                    dsimp [mainErase, Cerase]
                    exact
                      (C.eraseEdge g₀).bundleMainProduct_nonneg p hp0
                  have hmainBoundary0 :
                      0 ≤ mainBoundary := by
                    dsimp [mainBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleMainProduct_nonneg p hp0
                  have hmainLower0 :
                      0 ≤ mainLower := by
                    dsimp [mainLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct_nonneg
                        p hp0
                  have hmainLowerOrder0 :
                      0 ≤ mainLowerOrder := by
                    dsimp [mainLowerOrder]
                    exact
                      (C.lowerOrder g₀.card).bundleMainProduct_nonneg p hp0
                  have hmainC0 : 0 ≤ mainC := by
                    dsimp [mainC]
                    exact C.bundleMainProduct_nonneg p hp0
                  have hcountBoundary0 :
                      0 ≤ countBoundary := by
                    dsimp [countBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleCount_nonneg
                        ((C.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                            A hA01)
                  have hcountLower0 :
                      0 ≤ countLower := by
                    dsimp [countLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
                          (((C.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                              A hA01)
                  have hcountBoundary :
                      countBoundary ≤
                        (1 + E d₀ (n₀ + 1)) *
                          mainBoundary :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hBoundaryIH
                  have hcountLower :
                      countLower ≤
                        (1 + E d₀
                            (2 * (n₀ + 1))) *
                          mainLower :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hLowerIH
                  have hcorrection0 :
                      0 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) :=
                    hE.lower_correction_nonneg d₀ n₀
                  have hfirstCorrection0 :
                      0 ≤ 1 + E d₀ (n₀ + 1) := by
                    linarith
                      [hE.error_nonneg d₀ (n₀ + 1)]
                  have hβ0 :
                      0 ≤ β (d₀ + 1) :=
                    hE.defect_nonneg _
                  have hradicand :
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                        β (d₀ + 1) *
                            ((1 + E d₀ (n₀ + 1)) *
                              mainBoundary) *
                          ((1 + E d₀
                              (2 * (n₀ + 1))) *
                            mainLower) := by
                    calc
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            countLower :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            hcountBoundary hβ0)
                          hcountLower0
                      _ ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            ((1 + E d₀
                                (2 * (n₀ + 1))) *
                              mainLower) :=
                        mul_le_mul_of_nonneg_left
                          hcountLower
                          (mul_nonneg hβ0
                            (mul_nonneg
                              hfirstCorrection0
                              hmainBoundary0))
                  let rootCorrection :=
                    Real.sqrt
                      (β (d₀ + 1) *
                        (1 + E d₀ (n₀ + 1)) *
                        (1 + E d₀
                          (2 * (n₀ + 1))))
                  have hrootCorrection0 :
                      0 ≤ rootCorrection :=
                    Real.sqrt_nonneg _
                  have hmainBoundaryLower :
                      mainBoundary * mainLower =
                        mainLowerOrder ^ 2 := by
                    dsimp [mainBoundary, mainLower,
                      mainLowerOrder, Cboundary, Clower]
                    exact
                      C.boundary_mul_duplicateLower_main_eq_lowerOrder_sq
                        g₀ p
                  have hcoefficient0 :
                      0 ≤
                        β (d₀ + 1) *
                          (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) := by
                    rw [mul_assoc]
                    exact mul_nonneg hβ0 hcorrection0
                  have hsqrt :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        rootCorrection * mainLowerOrder := by
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          Real.sqrt
                            (β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                              ((1 + E d₀
                                  (2 * (n₀ + 1))) *
                                mainLower)) :=
                        Real.sqrt_le_sqrt hradicand
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                (mainBoundary * mainLower)) := by
                        congr 1
                        ring
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                mainLowerOrder ^ 2) := by
                        congr 1
                        rw [hmainBoundaryLower]
                      _ = rootCorrection * mainLowerOrder := by
                        dsimp [rootCorrection]
                        rw [Real.sqrt_mul hcoefficient0]
                        rw [Real.sqrt_sq hmainLowerOrder0]
                  have hαp :
                      α (d₀ + 1) ^ (n₀ + 1) ≤
                        p₀ * mainMax := by
                    dsimp [p₀, mainMax]
                    have hpow :=
                      C.pow_card_edges_le_selected_mul_maximalRemainder
                        hg₀ hmax p
                        (hE.density_pos g₀.card).le
                        (hE.density_le_one g₀.card)
                        (fun e he hcard =>
                          hpLower e he |>
                            fun h => by
                              simpa [hcard] using h)
                    simpa [hgcardD, hcardEq,
                      Nat.succ_eq_add_one] using hpow
                  have hαpowpos :
                      0 < α (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.density_pos _) _
                  have hmainFactor :
                      mainLowerOrder * (p₀ * mainMax) =
                        mainC := by
                    dsimp [mainLowerOrder, p₀, mainMax,
                      mainC, Cerase]
                    calc
                      (C.lowerOrder g₀.card).bundleMainProduct p *
                          (p (g₀.image C.projection) *
                            C.maximalRemainderMainProduct
                              g₀ p) =
                          ((C.lowerOrder g₀.card).bundleMainProduct p *
                            C.maximalRemainderMainProduct
                              g₀ p) *
                            p (g₀.image C.projection) := by
                        ring
                      _ =
                          (C.eraseEdge g₀).bundleMainProduct p *
                            p (g₀.image C.projection) := by
                        rw [
                          C.lowerOrder_mul_maximalRemainder_eq_erase_main
                            g₀ p]
                      _ = C.bundleMainProduct p :=
                        C.bundleMainProduct_eraseEdge_mul
                          p hg₀
                  have hsqrtNormalized :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        (rootCorrection /
                            α (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    have hscaled :
                        rootCorrection ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax) := by
                      calc
                        rootCorrection =
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              α (d₀ + 1) ^ (n₀ + 1) := by
                          field_simp
                        _ ≤
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              (p₀ * mainMax) :=
                          mul_le_mul_of_nonneg_left hαp
                            (div_nonneg hrootCorrection0
                              hαpowpos.le)
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          rootCorrection * mainLowerOrder :=
                        hsqrt
                      _ ≤
                          ((rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax)) *
                              mainLowerOrder :=
                        mul_le_mul_of_nonneg_right
                          hscaled hmainLowerOrder0
                      _ =
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        rw [← hmainFactor]
                        ring
                  have hμmain :
                      μ (d₀ + 1) ^ (n₀ + 1) ≤
                        mainC := by
                    dsimp [mainC]
                    have hpow :=
                      C.pow_card_edges_le_bundleMainProduct_of_edges
                        p (hE.floor_pos (d₀ + 1)).le
                        (fun g hg => by
                          have hcard :
                              g.card ≤ d₀ + 1 := by
                            exact
                              (C.edge_card_le_order hg).trans_eq
                                (by
                                  simpa [Nat.succ_eq_add_one] using
                                    horderEq)
                          exact
                            (hE.rankFloor hcard).trans
                              (hpLower _
                                (C.projection_mem_base g hg) |>
                                  fun h => by
                                    simpa [C.card_image_projection hg]
                                      using h))
                    simpa [hcardEq] using hpow
                  have hμpowpos :
                      0 < μ (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.floor_pos _) _
                  have huniformNormalized :
                      τ ≤
                        (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      τ =
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                              μ (d₀ + 1) ^ (n₀ + 1) := by
                        field_simp
                      _ ≤
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC :=
                        mul_le_mul_of_nonneg_left hμmain
                          (div_nonneg hE.uniform_nonneg
                            hμpowpos.le)
                  have hstepRaw :=
                    hstep K' C hclosedC hg₀ hmax
                  have hstepNormalized :
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                          Real.sqrt
                              (β (d₀ + 1) *
                                countBoundary * countLower) +
                            τ := by
                        simpa [p₀, countErase,
                          countBoundary, countLower,
                          Cerase, Cboundary, Clower,
                          hgcardD] using hstepRaw
                      _ ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              mainC +
                            (τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                              mainC :=
                        add_le_add hsqrtNormalized
                          huniformNormalized
                      _ =
                          (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        ring
                  have hp₀0 : 0 ≤ p₀ := by
                    dsimp [p₀]
                    exact hp0 _
                      (C.projection_mem_base g₀ hg₀)
                  have hmainEraseFactor :
                      p₀ * mainErase = mainC := by
                    dsimp [p₀, mainErase, mainC,
                      Cerase]
                    rw [mul_comm]
                    exact
                      C.bundleMainProduct_eraseEdge_mul
                        p hg₀
                  have hEraseNormalized :
                      p₀ *
                          |countErase - mainErase| ≤
                        E (d₀ + 1) n₀ * mainC := by
                    calc
                      p₀ *
                            |countErase - mainErase| ≤
                          p₀ *
                            (E (d₀ + 1) n₀ *
                              mainErase) :=
                        mul_le_mul_of_nonneg_left
                          hEraseIH hp₀0
                      _ =
                          E (d₀ + 1) n₀ * mainC := by
                        rw [← hmainEraseFactor]
                        ring
                  have hdecompose :
                      C.bundleCount
                            (C.pullbackBaseEdgeWeight A) -
                          mainC =
                        (C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase) := by
                    rw [← hmainEraseFactor]
                    ring
                  rw [hdecompose]
                  calc
                    |(C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase)| ≤
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          |p₀ * (countErase - mainErase)| :=
                      abs_add_le _ _
                    _ =
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          p₀ * |countErase - mainErase| := by
                      rw [abs_mul, abs_of_nonneg hp₀0]
                    _ ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC +
                          E (d₀ + 1) n₀ * mainC :=
                      add_le_add hstepNormalized
                        hEraseNormalized
                    _ =
                        (E (d₀ + 1) n₀ +
                            (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1))) *
                          mainC := by
                      ring
                    _ ≤
                        E (d₀ + 1) (n₀ + 1) *
                          mainC := by
                      apply mul_le_mul_of_nonneg_right
                      · simpa [rootCorrection,
                          bundleCountingStepIncrement,
                          add_assoc] using
                          hE.add_stepIncrement_le d₀ n₀
                      · exact hmainC0
              · have hcardLt : C.edges.card < n :=
                  lt_of_le_of_ne hCn
                    hcardEq
                have hsmall :=
                  (ihCard C.edges.card hcardLt)
                    K' C hCd le_rfl hclosedC
                have hmain0 :
                    0 ≤ C.bundleMainProduct p :=
                  C.bundleMainProduct_nonneg p hp0
                exact hsmall.trans
                  (mul_le_mul_of_nonneg_right
                    (hE.error_mono_card hCn) hmain0)
            · have horderLt : C.order < d :=
                lt_of_le_of_ne hCd
                  horderEq
              have hsmall :=
                (ihOrder C.order horderLt n)
                  K' C le_rfl hCn hclosedC
              have hmain0 :
                  0 ≤ C.bundleMainProduct p :=
                C.bundleMainProduct_nonneg p hp0
              exact hsmall.trans
                (mul_le_mul_of_nonneg_right
                  (hE.error_mono_order hCd) hmain0)
  exact
    (hP B.order B.edges.card)
      K B le_rfl le_rfl hclosed

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationStep.lean` -/

section
/-!
# The ordered-configuration one-edge bundle step

This file isolates the last analytic bridge between ordered atom
configurations and Tao's generalized bundle-counting induction.

For a nonempty occurrence edge `g₀`, its bundle projection is a nonempty
base edge of cardinality at most `r`, hence has a canonical positive
ordered face.  Pulling the configuration indicator back to `g₀` then has
the exact mixed decomposition

```
indicator = coarse density + boundary defect + fine-boundary residual.
```

The generalized counting file already turns a boundary-localized square
estimate into the required square-root error and turns frozen correlation
bounds into the required uniform error.  The two predicates below state
exactly the remaining transport obligations.

The localized-defect predicate is deliberately *weighted by the complete
strict-boundary bundle count*.  The existing
`ClosedOrderedAtomConfiguration.IsMixedGood` estimate controls the defect
on the canonical coarse boundary atom.  Since a strict bundle boundary
also contains all lower-rank configuration factors, obtaining the
weighted statement is an additional hypothesis; it does not follow merely
by discarding factors from the unweighted localized mass.

The frozen-uniformity predicate is the combinatorial reindexing statement
that, after the outside occurrence variables are fixed, the remaining
bundle product is a bounded cut test on the selected projected face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical face of a nonempty occurrence edge -/

/-- A nonempty occurrence edge has nonempty projected base edge. -/
theorem projectedEdge_nonempty
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

/-- Every projected occurrence edge has cardinality at most the complex
rank. -/
theorem projectedEdge_card_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

/-- The positive ordered face canonically enumerating the projection of a
nonempty occurrence edge. -/
noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

/-- Transport an occurrence-edge tuple first to the projected base edge
and then to its increasing ordered enumeration. -/
noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

/-! ## The transported mixed decomposition -/

/-- The fine-minus-coarse boundary defect on a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

/-- The coarse-upper residual after conditioning on the fine boundary,
transported to a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

/-- The projected base density is the mixed coarse density of the
canonical projected face. -/
theorem orderedConfigurationBaseDensity_projectedEdge
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    orderedConfigurationBaseDensity P A
        (g.image B.projection) =
      mixedConfigurationCoarseDensity P A
        (B.orderedConfigurationBundleFace hg hne) := by
  unfold orderedConfigurationBaseDensity
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  rfl

/-- Exact main/defect/uniform decomposition after pullback to any nonempty
occurrence edge. -/
theorem pullback_orderedConfigurationBaseWeight_decompose
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g y =
      orderedConfigurationBaseDensity P A
          (g.image B.projection) +
        B.orderedConfigurationBundleDefect P A hg hne y +
        B.orderedConfigurationBundleUniform P A hg hne y := by
  rw [B.pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hg y]
  rw [B.orderedConfigurationBaseDensity_projectedEdge
    P A hg hne]
  unfold orderedConfigurationBaseWeight
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  exact
    mixedConfigurationFaceWeight_decompose P A
      (B.orderedConfigurationBundleFace hg hne)
      (B.orderedConfigurationBundleFaceTuple hg hne y)

/-! ## The two exact transport obligations -/

/-- The selected defect multiplied by the complete strict-boundary
configuration indicator. -/
noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

/-- Missing weighted localization statement for ordered configurations in
arbitrary closed bundles.

This is stronger than the currently available unweighted localized defect
bound: the right side is the actual strict-boundary bundle count, not the
mass of the containing coarse boundary atom. -/
def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

/-- Missing frozen-cut transport statement for ordered configurations in
arbitrary bundles.  It says precisely that every frozen remainder is a
bounded face cut covered by the common mixed preliminary regularity
tolerance. -/
def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

/-! ## Assembly of the one-edge input -/

/-- The two transport obligations, together with the exact decomposition,
give the analytic one-edge hypothesis consumed by the relative generalized
bundle-counting induction. -/
theorem hasTaoBundleCountingStep_orderedConfiguration
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hlocalized :
      HasOrderedConfigurationBundleLocalizedDefect P A β)
    (hfrozen :
      HasOrderedConfigurationBundleFrozenUniformity P A τ) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax
  by_cases hne : g₀.Nonempty
  · let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    let p :=
      orderedConfigurationBaseDensity P A
        (g₀.image B.projection)
    let b :=
      B.orderedConfigurationBundleDefect
        P A hg₀ hne
    let c :=
      B.orderedConfigurationBundleUniform
        P A hg₀ hne
    let bLocalized :=
      B.orderedConfigurationBundleLocalizedDefect
        P A hg₀ hne
    have hdecomp :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.pullback_orderedConfigurationBaseWeight_decompose
          P A hg₀ hne y
    have hcount :
        B.bundleCount W =
          p * (B.eraseEdge g₀).bundleCount W +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W :=
      B.bundleCount_decompose_edge
        W hg₀ p b c hdecomp
    have herase :
        (B.eraseEdge g₀).bundleCount W =
          (B.eraseEdge g₀).bundleCount
            ((B.eraseEdge g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      exact
        B.eraseEdge_bundleCount_pullback g₀
          (orderedConfigurationBaseWeight A)
    have hIdempotent :
        B.WeightsIdempotent W := by
      exact B.pullbackBaseEdgeWeight_weightsIdempotent
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseWeight_idempotent A)
    have hlocalizeContribution :
        B.edgeContribution g₀ b W =
          B.edgeContribution g₀ bLocalized W := by
      change B.edgeContribution g₀ b W =
        B.edgeContribution g₀
          (fun y =>
            b y * B.strictBoundaryLocalProduct g₀ W y) W
      exact B.edgeContribution_mul_strictBoundaryLocalProduct
        g₀ b W hIdempotent
    have hdefect :
        |B.edgeContribution g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.strictBoundary g₀).bundleCount
                  ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                  (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) := by
      rw [hlocalizeContribution]
      exact
        B.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
          hclosed hg₀ hmax
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (orderedConfigurationBaseWeight_idempotent A)
          bLocalized (hβ g₀.card)
          (hlocalized K B hclosed hg₀ hmax hne)
    have huniform :
        |B.edgeContribution g₀ c W| ≤ τ := by
      exact B.abs_edgeContribution_le_of_frozen
        g₀ c W
        (hfrozen K B hclosed hg₀ hmax hne)
    rw [hcount, herase]
    calc
      |p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W -
          p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))| =
          |B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.edgeContribution g₀ b W| +
            |B.edgeContribution g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.strictBoundary g₀).bundleCount
                    ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) *
                ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                    (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) +
            τ :=
        add_le_add hdefect huniform
  · have hg₀empty : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    subst g₀
    let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    have hweight :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.pullbackBaseEdgeWeight_of_mem
        (orderedConfigurationBaseWeight A) hg₀ y]
      simp only [Finset.image_empty]
      exact orderedConfigurationBaseWeight_empty A
        (B.projectedEdgeTuple hg₀ y)
    have hcount :
        B.bundleCount W =
          (B.eraseEdge ∅).bundleCount
            ((B.eraseEdge ∅).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      calc
        B.bundleCount W =
            B.edgeContribution ∅ (W ∅) W :=
          B.bundleCount_eq_edgeContribution W hg₀
        _ =
            B.edgeContribution ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.edgeContribution ∅ q W)
          funext y
          exact hweight y
        _ = (B.eraseEdge ∅).bundleCount W := by
          rw [B.edgeContribution_const]
          simp
        _ =
            (B.eraseEdge ∅).bundleCount
              ((B.eraseEdge ∅).pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A)) :=
          B.eraseEdge_bundleCount_pullback ∅
            (orderedConfigurationBaseWeight A)
    rw [hcount, Finset.image_empty,
      orderedConfigurationBaseDensity_empty,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) hτ

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFrozenUniformity.lean` -/

section
/-!
# Frozen bundle uniformity

This file records the exact interface between mixed preliminary
regularity and the frozen-uniformity input of generalized bundle
counting.

For a selected occurrence edge `g₀`, preliminary regularity applies on
the canonically enumerated projected face.  What remains is a purely
combinatorial representation statement: after the occurrence variables
outside `g₀` have been fixed, the erased bundle product is a bounded
lower-face cut test on that projected face.

The representation is separated from the analytic implication for two
reasons.

* It makes explicit that no stronger analytic regularity lemma is needed.
  Ordinary bounded face-cut regularity is exactly the required norm.
* It gives the source-style regularity certificate a precise target while
  the dependent reindexing of arbitrary bundle vertices is developed.

The key combinatorial fact behind the representation is that every
remaining occurrence edge omits a vertex of `g₀`: if it contained all of
`g₀`, maximality of `g₀` would force equality, contradicting its presence
in the erased edge family.  Injectivity of the bundle projection on
`g₀` transports such a missing occurrence vertex to a missing coordinate
of the canonical positive ordered face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## A missing selected vertex -/

/-- Every edge left after erasing a maximum-cardinality edge omits at
least one vertex of the selected edge.  This is the structural reason that
each frozen remainder factor belongs to a proper-face cut coordinate. -/
theorem exists_selectedVertex_not_mem_of_mem_erase
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra hmissing
  have hsubset : g₀ ⊆ g := by
    intro v hv
    by_contra hvg
    exact hmissing ⟨v, hv, hvg⟩
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hsubset (hmax g hgB)
  exact (Finset.mem_erase.mp hg).1 heq.symm

/-! ## The selected face regularity state -/

/-- The fine-boundary regularity state on the canonical projected face of
an occurrence edge. -/
noncomputable def orderedConfigurationBundleFaceState
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    FaceRegularityState
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  ⟨orderedBoundaryPartition
    (positiveFaceLowerLayer P.fine
      (B.orderedConfigurationBundleFace hg hne))
    (B.orderedConfigurationBundleFace hg hne).face⟩

/-- The coarse upper atom whose fine-boundary residual is the selected
bundle uniform function. -/
noncomputable def orderedConfigurationBundleFaceTarget
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
      G) → ℝ :=
  partitionAtomIndicator
    (P.coarse.partition
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)
    (A.atom
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)

/-! ## The exact combinatorial transport obligation -/

/-- Every frozen bundle remainder has a bounded cut representation on
the selected projected face.

This predicate contains no analytic estimate.  Its equality is the
dependent reindexing theorem: the selected occurrence tuple is transported
through `projectionEquiv` and the increasing enumeration of its projected
edge, while every remaining occurrence-edge factor is assigned to one
coordinate that it omits. -/
def HasOrderedConfigurationBundleFrozenCutRepresentation
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        ∃ u :
            CutTestFamily G
              ((B.orderedConfigurationBundleFace
                hg₀ hne).lowerRank.1 + 1),
          IsBoundedCutTest u ∧
            B.frozenEdgeCorrelation g₀
                (B.orderedConfigurationBundleUniform
                  P A hg₀ hne)
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) z =
              (B.orderedConfigurationBundleFaceState
                  P hg₀ hne).faceCutCorrelation
                (B.orderedConfigurationBundleFaceTarget
                  P A hg₀ hne)
                u

/-! ## Preliminary regularity gives the frozen estimate -/

/-- Common-tolerance mixed preliminary regularity gives frozen bundle
uniformity once the remainder has been reindexed as a bounded face cut. -/
theorem hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (hcut :
      HasOrderedConfigurationBundleFrozenCutRepresentation P A) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax hne z
  obtain ⟨u, hu, hreindex⟩ :=
    hcut K B hclosed hg₀ hmax hne z
  rw [hreindex]
  exact
    mixedConfigurationFace_isFaceCutRegular
      P A (fun _ => τ) hregular
      (B.orderedConfigurationBundleFace hg₀ hne)
      u hu

/-! ## Source-full certificate -/

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFrozenCut.lean` -/

section
/-!
# Frozen bundle remainders are face cuts

Fix a maximum-cardinality nonempty occurrence edge `g₀`.  Every other
occurrence edge omits a vertex of `g₀`; we assign that edge to the
corresponding coordinate in the increasing enumeration of the projected
edge.  After the variables outside `g₀` are frozen, factors with the same
assigned coordinate form one member of a face-cut family.

The construction groups *occurrence* edges, rather than projected faces.
This is important because distinct occurrence edges in a bundle may have
the same projection.  The resulting product therefore retains every
factor with its correct multiplicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical occurrence-edge ordering -/

/-- The increasing enumeration of the projected selected edge. -/
noncomputable def frozenProjectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

/-- Increasing projected coordinates, lifted to their unique occurrence
vertices in the selected edge. -/
noncomputable def frozenOccurrenceOrderEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.frozenProjectedEdgeOrderIso hg hne).trans
    (B.projectionEquiv hg).symm

/-- Reindex selected-occurrence-edge tuples by their canonical projected
face coordinates. -/
noncomputable def frozenBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.frozenProjectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.frozenBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold frozenBundleFaceTupleEquiv frozenProjectedEdgeOrderIso
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple
  rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

/-! ## Assigning each remainder edge to a missing coordinate -/

/-- A totalized selected vertex omitted by a remainder occurrence edge.
The fallback branch is never used in the cut product. -/
noncomputable def frozenBundleMissingVertex
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax),
      (Classical.choose_spec
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).1⟩
  else
    ⟨Classical.choose hne, Classical.choose_spec hne⟩

theorem frozenBundleMissingVertex_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenBundleMissingVertex hmax hne g).1 ∉ g := by
  classical
  simp only [frozenBundleMissingVertex, dif_pos hg]
  exact
    (Classical.choose_spec
      (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).2

/-- Coordinate of the selected missing occurrence vertex. -/
noncomputable def frozenBundleMissingCoordinate
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
    (B.frozenBundleMissingVertex hmax hne g)

/-! ## Reconstructing and grouping a frozen remainder -/

/-- Insert an arbitrary value at one erased canonical face coordinate and
transport the resulting tuple back to the selected occurrence edge. -/
noncomputable def frozenBundleInsertedSelectedTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.frozenBundleFaceTupleEquiv hg₀ hne).symm
    (Fin.insertNth i a y)

/-- Recombine an inserted selected-edge tuple with the frozen outside
variables. -/
noncomputable def frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G)
    (z : EdgeComplement g₀ → G) : K → G :=
  (splitEdgeEquiv g₀).symm
    (B.frozenBundleInsertedSelectedTuple hg₀ hne i a y, z)

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (edgeTuple_splitEdgeEquiv_symm g₀ y z) ⟨v, hv⟩
  exact h

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_not_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold splitEdgeEquiv
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (edgeSumEquiv g₀)
      y z ⟨v, hv⟩ using 1 ;
    simp [edgeSumEquiv]

omit [Fintype G] [DecidableEq G] in
/-- Replacing the coordinate assigned to `g` does not alter the tuple
seen by `g`, since that occurrence edge omits the assigned vertex. -/
theorem edgeTuple_frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by
  classical
  funext w
  unfold edgeTuple
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  by_cases hw₀ : w.1 ∈ g₀
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    unfold frozenBundleInsertedSelectedTuple
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    let q :=
      (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
        (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀})
    have hqi : q ≠ i := by
      intro h
      have hsub :
          (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀}) =
            B.frozenBundleMissingVertex hmax hne g := by
        apply (B.frozenOccurrenceOrderEquiv hg₀ hne).symm.injective
        simpa only [q, i, frozenBundleMissingCoordinate] using h
      apply B.frozenBundleMissingVertex_not_mem hmax hne hg
      have hwval :
          w.1 =
            (B.frozenBundleMissingVertex hmax hne g).1 :=
        congrArg Subtype.val hsub
      rw [← hwval]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [hqi]
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]

/-- The grouped frozen remainder cut test.  The product is indexed by
occurrence edges, so repeated projected faces remain separate factors. -/
noncomputable def frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    CutTestFamily G
      ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
      then
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a y z))
      else 1

/-- Every grouped remainder cut factor lies in `[0,1]`. -/
theorem frozenBundleRemainderCutTest_bounded
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    IsBoundedCutTest
      (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) := by
  constructor
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_nonneg
    intro g hg
    split_ifs
    · exact
        (B.pullbackBaseEdgeWeight_unitInterval
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (Finset.mem_of_mem_erase hg) _).1
    · positivity
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_le_one
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).1
      · positivity
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).2
      · exact le_rfl

/-- The cut product is exactly the complete frozen bundle remainder. -/
theorem cutTestProduct_frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G) :
    cutTestProduct
        (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) x =
      B.edgeRemainderFiber g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A))
        ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x) z := by
  classical
  unfold cutTestProduct frozenBundleRemainderCutTest
  rw [Finset.prod_comm]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  calc
    (∏ q :
        Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1),
        if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = q
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
              (B.frozenBundleInsertedAssignment hg₀ hne q a
                (Fin.removeNth q x) z))
        else 1) =
        (if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
                (Fin.removeNth i x) z))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q hqi
      have hnecoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g ≠ q := by
        intro h
        exact hqi h.symm
      simp [hnecoord]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
              (Fin.removeNth i x) z)) := by
      simp [i]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z))) := by
      rw [B.edgeTuple_frozenBundleInsertedAssignment
        hg₀ hmax hne hg a x z]

/-! ## Exact correlation transport -/

/-- Every frozen remainder of an arbitrary closed bundle is a bounded cut
test on the canonical selected projected face. -/
theorem hasOrderedConfigurationBundleFrozenCutRepresentation
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A := by
  intro K _instK _decK B _hclosed g₀ hg₀ hmax hne z
  let a : G := Classical.choice inferInstance
  let u :=
    B.frozenBundleRemainderCutTest A hg₀ hmax hne a z
  refine ⟨u, ?_, ?_⟩
  · exact
      B.frozenBundleRemainderCutTest_bounded
        P A hg₀ hmax hne a z
  · unfold frozenEdgeCorrelation
    unfold FaceRegularityState.faceCutCorrelation
    apply mean_equiv
      (B.frozenBundleFaceTupleEquiv hg₀ hne)
    intro y
    rw [B.cutTestProduct_frozenBundleRemainderCutTest
      P A hg₀ hmax hne a z]
    simp only [Equiv.symm_apply_apply]
    rw [B.frozenBundleFaceTupleEquiv_apply]
    rfl

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedFullBoundary.lean` -/

section
/-!
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/

/-- Every nonempty proper ordered subface of an `n + 1` tuple.

The `lowerRank` field of `PositiveOrderedFace (n + 1) n` ranges over
`0, ..., n - 1`, so its actual rank ranges over `1, ..., n`. -/
abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

/-! ## The full lower partition -/

/-- The layer of the ambient complex carrying a proper positive subface. -/
abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩

@[simp]
theorem orderedFullLowerComplexRank_val
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (orderedFullLowerComplexRank e d).1 =
      d.lowerRank.1 + 1 :=
  rfl

/-- A local proper subface, transported into the ambient labelled face. -/
abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face

/-- Restricting through the ambient face agrees with first selecting the
upper tuple and then selecting its local proper subface. -/
@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl

/-- Pull the genuine partition on one proper ambient subface back to the
selected upper tuple space. -/
noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

/-- Common refinement of the pullbacks from every nonempty proper ordered
subface. -/
noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)

/-- The source-faithful full lower boundary.  We explicitly join the
ordinary immediate boundary with the positive strict-subface join.  For
rank greater than one the immediate constituents already occur in the
positive join; for rank one the immediate rank-zero face space is a
singleton.  Keeping this harmless factor explicit makes the refinement to
the boundary used by the counting decomposition definitional. -/
noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)

/-- The full lower boundary refines the immediate boundary used in the
standard coarse/fine counting decomposition. -/
theorem orderedFullLowerBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedBoundaryPartition
        (positiveFaceLowerLayer C e) e.face := by
  exact FacePartition.join_le_left _ _

/-- Exact atom membership for the full lower boundary. -/
theorem mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    y ∈ (orderedFullLowerBoundaryPartition C e).part x ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryPartition, FacePartition.part_join,
    Finset.mem_inter, orderedFullLowerPositivePartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedFullLowerConstituentPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

/-! ## Selected full-lower atoms and their weights -/

/-- Canonical full-lower atom containing a selected upper tuple. -/
noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x

@[simp]
theorem orderedFullLowerBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryAtomAt C e x).1 =
      (orderedFullLowerBoundaryPartition C e).part x :=
  rfl

/-- Indicator of the full-lower atom selected by `x`. -/
noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y

@[simp]
theorem orderedFullLowerBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ^ 2 =
      orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_sq _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_self
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x x = 1 := by
  apply partitionAtomIndicator_of_mem
  exact
    (orderedFullLowerBoundaryPartition C e).mem_part
      (Finset.mem_univ x)

/-! ## Source full-lower goodness -/

/-- The source density term is the existing immediate-boundary coarse
conditional density.  The full lower boundary is used to localize its
fine--coarse defect, not to alter the three-term counting decomposition. -/
noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

/-- The defect in the source-goodness test is the existing immediate
fine-boundary density minus immediate coarse-boundary density.  Conditioning
its square on the full strict lower atom is the extra source-faithful
localization. -/
noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

/-- The coarse full-lower atom selected by a closed configuration. -/
noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y

@[simp]
theorem sourceFullMixedBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ^ 2 =
      sourceFullMixedBoundaryWeight P A e y :=
  orderedFullLowerBoundaryWeight_sq _ _ _ _

/-- Source mixed goodness at one positive face.  The first clause is the
coarse density floor.  The second is the conditional square average of the
fine--coarse defect on the selected full-lower coarse atom. -/
def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

/-- Source mixed goodness simultaneously at every positive ordered face. -/
def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

/-- The global square-defect mass localized by the selected full-lower
coarse atom. -/
noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y

/-- Pointwise source goodness yields the localized weighted-defect estimate
used in the source counting argument. -/
theorem SourceFullMixedGoodAtFace.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (hgood : SourceFullMixedGoodAtFace P A e α β) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β * mean (sourceFullMixedBoundaryWeight P A e) := by
  unfold sourceFullMixedLocalizedDefectSq
  apply mean_mul_partitionAtomIndicator_le
    (orderedFullLowerBoundaryPartition P.coarse e)
    (fun y => sourceFullMixedDefect P A e y ^ 2)
    (orderedFullLowerBoundaryAtomAt P.coarse e
      (orderedFaceTuple e.face A.witness))
  have hrep :
      (orderedFullLowerBoundaryPartition P.coarse e).representative
          (orderedFullLowerBoundaryAtomAt P.coarse e
            (orderedFaceTuple e.face A.witness)) ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness) := by
    exact
      (orderedFullLowerBoundaryPartition P.coarse e).representative_mem
        (orderedFullLowerBoundaryAtomAt P.coarse e
          (orderedFaceTuple e.face A.witness))
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedFullLowerBoundaryPartition P.coarse e)
      (fun y => sourceFullMixedDefect P A e y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

/-- The all-face source-goodness predicate specializes to its localized
weighted-defect consequence at any positive face. -/
theorem ClosedOrderedAtomConfiguration.IsSourceFullMixedGood.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β e.rank *
        mean (sourceFullMixedBoundaryWeight P A e) :=
  (hgood e).localized_defect P A e
    (α e.rank) (β e.rank)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleSourceGoodnessBridge.lean` -/

section
/-!
# Source-full goodness supplies the bundle-localized defect bound

For a maximal nonempty occurrence edge of a closed bundle, projection is a
bijection onto the corresponding base edge.  Consequently its strict
occurrence boundary is just another indexing of all proper subsets of that
base edge.  The product of the configuration indicators on those subsets is
the indicator of the full lower atom used in `OrderedFullBoundary`.

This file makes that reindexing explicit.  It then transports the source-full
localized square estimate along the induced equivalence of tuple spaces.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## Tuple reindexing -/

/-- The canonical enumeration of the projected edge. -/
noncomputable def projectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

@[simp]
theorem projectedEdgeOrderIso_apply_val
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (i : Fin ((B.orderedConfigurationBundleFace
      hg hne).lowerRank.1 + 1)) :
    ((B.projectedEdgeOrderIso hg hne) i).1 =
      (B.orderedConfigurationBundleFace hg hne).face i := by
  rfl

/-- Reindex occurrence-edge assignments by the increasing enumeration of
their projected base edge. -/
noncomputable def orderedConfigurationBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.projectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem orderedConfigurationBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.orderedConfigurationBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold orderedConfigurationBundleFaceTupleEquiv
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple projectedEdgeOrderIso
  rfl

/-! ## Proper subfaces -/

/-- The positive ambient face obtained from a proper positive local
subface. -/
def ambientPositiveFaceOfProperSubface
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    PositiveOrderedFace k r where
  lowerRank :=
    ⟨d.lowerRank.1,
      lt_trans d.lowerRank.2 e.lowerRank.2⟩
  face := orderedFullLowerAmbientFace e d

@[simp]
theorem ambientPositiveFaceOfProperSubface_rank
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (ambientPositiveFaceOfProperSubface e d).rank = d.rank := by
  rfl

theorem ambientPositiveFaceOfProperSubface_edge_ssubset
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    positiveOrderedFaceEdge
        (ambientPositiveFaceOfProperSubface e d) ⊂
      positiveOrderedFaceEdge e := by
  constructor
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨d.face i, rfl⟩
  · intro h
    have hcard :=
      Finset.card_le_card h
    rw [positiveOrderedFaceEdge_card,
      positiveOrderedFaceEdge_card] at hcard
    exact
      (Nat.not_le_of_gt
        (properPositiveOrderedSubface_rank_lt_upper d)) hcard

/-- Every positive face whose range is a proper subset of `e` factors
uniquely through a proper positive local subface of `e`. -/
theorem exists_properPositiveOrderedSubface_of_edge_ssubset
    (e f : PositiveOrderedFace k r)
    (hfe :
      positiveOrderedFaceEdge f ⊂
        positiveOrderedFaceEdge e) :
    ∃ d : ProperPositiveOrderedSubface e.lowerRank.1,
      ambientPositiveFaceOfProperSubface e d = f := by
  have hrank : f.rank < e.rank := by
    rw [← positiveOrderedFaceEdge_card,
      ← positiveOrderedFaceEdge_card]
    exact Finset.card_lt_card hfe
  have hrange :
      Set.range f.face ⊆ Set.range e.face := by
    intro v hv
    rw [← mem_positiveOrderedFaceEdge] at hv ⊢
    exact hfe.1 hv
  choose q hq using fun i : Fin (f.lowerRank.1 + 1) =>
    hrange ⟨i, rfl⟩
  have hqmono : StrictMono q := by
    intro i j hij
    apply e.face.lt_iff_lt.mp
    rw [hq i, hq j]
    exact f.face.strictMono hij
  let dface : OrderedFace
      (e.lowerRank.1 + 1) (f.lowerRank.1 + 1) :=
    OrderEmbedding.ofStrictMono q hqmono
  have hdlt : f.lowerRank.1 < e.lowerRank.1 := by
    simpa [PositiveOrderedFace.rank] using hrank
  let d : ProperPositiveOrderedSubface e.lowerRank.1 :=
    ⟨⟨f.lowerRank.1, hdlt⟩, dface⟩
  refine ⟨d, ?_⟩
  apply positiveOrderedFaceEdge_injective
  apply Finset.Subset.antisymm
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, (hq i).symm⟩
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, hq i⟩

/-- The finite family of all positive ambient faces strictly below `e`. -/
noncomputable def orderedConfigurationStrictFaceFamily
    (e : PositiveOrderedFace k r) :
    Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun f =>
    positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e

@[simp]
theorem mem_orderedConfigurationStrictFaceFamily
    (e f : PositiveOrderedFace k r) :
    f ∈ orderedConfigurationStrictFaceFamily e ↔
      positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e := by
  simp [orderedConfigurationStrictFaceFamily]

/-- Every positive immediate boundary is a proper positive subface. -/
theorem positiveOrderedFaceEdge_boundary_ssubset
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    positiveOrderedFaceEdge (e.boundary hpos i) ⊂
      positiveOrderedFaceEdge e := by
  rcases e with ⟨⟨j, hjr⟩, eface⟩
  cases j with
  | zero =>
      simp at hpos
  | succ n =>
      constructor
      · intro v hv
        rw [mem_positiveOrderedFaceEdge] at hv ⊢
        obtain ⟨q, rfl⟩ := hv
        exact ⟨i.succAbove q, rfl⟩
      · intro h
        have hc := Finset.card_le_card h
        rw [positiveOrderedFaceEdge_card,
          positiveOrderedFaceEdge_card] at hc
        exact
          (Nat.not_le_of_gt
            ((⟨⟨n + 1, hjr⟩, eface⟩ :
                PositiveOrderedFace k r).boundary_rank_lt
              hpos i)) hc

/-! ## The full-lower atom as a strict-face product -/

/-- Extend a selected upper-face tuple by the configuration witness on
the complementary coordinates. -/
noncomputable def extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    Fin k → G :=
  (splitOrderedFaceEquiv e.face).symm
    (y, orderedFaceComplementTuple e.face A.witness)

@[simp]
theorem orderedFaceTuple_extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFaceTuple e.face
        (extendConfigurationFaceTuple P A e y) = y := by
  exact orderedFaceTuple_splitOrderedFaceEquiv_symm _ _ _

/-- Extending the canonical projected tuple recovers the original
occurrence-edge tuple at every projected vertex. -/
@[simp]
theorem extendConfigurationFaceTuple_projection
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G)
    (v : {v : K // v ∈ g}) :
    extendConfigurationFaceTuple P A
        (B.orderedConfigurationBundleFace hg hne)
        (B.orderedConfigurationBundleFaceTuple hg hne y)
        (B.projection v.1) =
      y v := by
  let j := B.projectionEquiv hg v
  let i :=
    (B.projectedEdgeOrderIso hg hne).symm j
  have hi :
      B.projectedEdgeOrderIso hg hne i = j :=
    (B.projectedEdgeOrderIso hg hne).apply_symm_apply j
  have hface :
      (B.orderedConfigurationBundleFace hg hne).face i =
        B.projection v.1 := by
    calc
      (B.orderedConfigurationBundleFace hg hne).face i =
          ((B.projectedEdgeOrderIso hg hne) i).1 := by
        rw [B.projectedEdgeOrderIso_apply_val]
      _ = j.1 := congrArg Subtype.val hi
      _ = B.projection v.1 := by
        exact B.projectionEquiv_apply_val hg v
  rw [← hface]
  change
    orderedFaceTuple
        (B.orderedConfigurationBundleFace hg hne).face
        (extendConfigurationFaceTuple P A
          (B.orderedConfigurationBundleFace hg hne)
          (B.orderedConfigurationBundleFaceTuple hg hne y)) i =
      y v
  rw [orderedFaceTuple_extendConfigurationFaceTuple]
  change
    B.projectedEdgeTuple hg y
        ((B.projectedEdgeOrderIso hg hne) i) =
      y v
  rw [hi]
  exact congrArg y
    ((B.projectionEquiv hg).symm_apply_apply v)

/-- Product form of the selected full-lower atom. -/
theorem sourceFullMixedBoundaryWeight_eq_strictFaceProduct
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y =
      partialConfigurationWeight A
        (orderedConfigurationStrictFaceFamily e)
        (extendConfigurationFaceTuple P A e y) := by
  classical
  let x := extendConfigurationFaceTuple P A e y
  have hxe : orderedFaceTuple e.face x = y :=
    orderedFaceTuple_extendConfigurationFaceTuple P A e y
  by_cases hy :
      y ∈ (orderedFullLowerBoundaryPartition P.coarse e).part
        (orderedFaceTuple e.face A.witness)
  · rw [show sourceFullMixedBoundaryWeight P A e y = 1 by
          exact partitionAtomIndicator_of_mem _ _ hy]
    unfold partialConfigurationWeight
    symm
    apply Finset.prod_eq_one
    intro f hf
    have hfe :
      positiveOrderedFaceEdge f ⊂
          positiveOrderedFaceEdge e :=
      (mem_orderedConfigurationStrictFaceFamily e f).1
        hf
    obtain ⟨d, rfl⟩ :=
      exists_properPositiveOrderedSubface_of_edge_ssubset e f hfe
    unfold configurationFaceWeight
    apply partitionAtomIndicator_of_mem
    have hd :=
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).1 hy |>.2 d
    change
      orderedFaceTuple
          (orderedFullLowerAmbientFace e d) x ∈
        (A.atom
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).1
    rw [A.atom_eq_partitionAtomAt]
    change
      orderedFaceTuple d.face
          (orderedFaceTuple e.face x) ∈
        (P.coarse.partition
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).part
          (orderedFaceTuple d.face
            (orderedFaceTuple e.face A.witness))
    rw [hxe]
    exact hd
  · rw [show sourceFullMixedBoundaryWeight P A e y = 0 by
          exact partitionAtomIndicator_of_not_mem _ _ hy]
    by_contra hprod
    have hprod' :
        partialConfigurationWeight A
            (orderedConfigurationStrictFaceFamily e) x ≠ 0 :=
      fun hz => hprod hz.symm
    have hall :
        ∀ f ∈ orderedConfigurationStrictFaceFamily e,
          configurationFaceWeight A f
              (orderedFaceTuple f.face x) ≠ 0 := by
      intro f hf
      exact Finset.prod_ne_zero_iff.mp
        (by simpa [partialConfigurationWeight] using hprod') f hf
    exfalso
    apply hy
    apply
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).2
    constructor
    · rw [mem_orderedBoundaryPartition_part_iff]
      intro i
      by_cases he0 : e.lowerRank.1 = 0
      · have hsub :
            eraseBoundaryCoordinate i y =
              eraseBoundaryCoordinate i
                (orderedFaceTuple e.face A.witness) :=
          by
            funext q
            have hq : q.1 < 0 := by
              simpa [he0] using q.2
            omega
        rw [hsub]
        exact
          (positiveFaceLowerLayer P.coarse e
            (eraseBoundaryFace e.face i)).mem_part
            (Finset.mem_univ _)
      · have hepos : 0 < e.lowerRank.1 :=
          Nat.pos_of_ne_zero he0
        let f := e.boundary hepos i
        have hfstrict :
            positiveOrderedFaceEdge f ⊂
              positiveOrderedFaceEdge e := by
          exact positiveOrderedFaceEdge_boundary_ssubset
            e hepos i
        have hfmem :
            f ∈ orderedConfigurationStrictFaceFamily e :=
          (mem_orderedConfigurationStrictFaceFamily e f).2 hfstrict
        have hfweight := hall f hfmem
        rw [← hxe]
        exact
          coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
            P A e hepos i x hfweight
    · intro d
      let f := ambientPositiveFaceOfProperSubface e d
      have hfmem :
          f ∈ orderedConfigurationStrictFaceFamily e :=
        (mem_orderedConfigurationStrictFaceFamily e f).2
          (ambientPositiveFaceOfProperSubface_edge_ssubset e d)
      have hfweight := hall f hfmem
      unfold configurationFaceWeight at hfweight
      have hfatom :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hfweight
          (partitionAtomIndicator_of_not_mem _ _ hnot)
      rw [A.atom_eq_partitionAtomAt] at hfatom
      change
        orderedFaceTuple
            (orderedFullLowerAmbientFace e d) x ∈
          (P.coarse.partition
            (orderedFullLowerComplexRank e d)
            (orderedFullLowerAmbientFace e d)).part
            (orderedFaceTuple
              (orderedFullLowerAmbientFace e d) A.witness)
        at hfatom
      simp only [orderedFaceTuple_orderedFullLowerAmbientFace]
        at hfatom
      simpa only [hxe] using hfatom

/-! ## Reindexing a closed bundle boundary -/

/-- Lift a projected subset back to the unique occurrence subedge inside
`g₀`. -/
def liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t

theorem liftProjectedSubedge_subset
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    B.liftProjectedSubedge g₀ t ⊆ g₀ := by
  exact Finset.filter_subset _ _

theorem image_liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) {t : Finset (Fin k)}
    (ht : t ⊆ g₀.image B.projection) :
    (B.liftProjectedSubedge g₀ t).image B.projection = t := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hv).2
  · intro hj
    obtain ⟨v, hvg, hvj⟩ :=
      Finset.mem_image.mp (ht hj)
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvg, ?_⟩, hvj⟩
    exact hvj ▸ hj

theorem liftProjectedSubedge_image_eq
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hgg₀ : g ⊆ g₀) :
    B.liftProjectedSubedge g₀
        (g.image B.projection) = g := by
  ext v
  constructor
  · intro hv
    have hvg₀ := (Finset.mem_filter.mp hv).1
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).2
    have hwg₀ : w ∈ g₀ := hgg₀ hwg
    have hwv' : w = v :=
      B.projection_injective_on_edge g₀ hg₀ hwg₀ hvg₀ hwv
    exact hwv' ▸ hwg
  · intro hv
    exact Finset.mem_filter.mpr
      ⟨hgg₀ hv,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-! The substantial pointwise identity. -/

theorem strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (y : {v : K // v ∈ g₀} → G) :
    B.strictBoundaryLocalProduct g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) y =
      sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)
        (B.orderedConfigurationBundleFaceTuple hg₀ hne y) := by
  classical
  let e := B.orderedConfigurationBundleFace hg₀ hne
  let u := B.orderedConfigurationBundleFaceTuple hg₀ hne y
  let x := extendConfigurationFaceTuple P A e u
  have heedge :
      positiveOrderedFaceEdge e =
        g₀.image B.projection := by
    dsimp [e, orderedConfigurationBundleFace]
    exact positiveOrderedFaceEdge_ofEdge
      (g₀.image B.projection)
      (B.projectedEdge_nonempty hg₀ hne)
      (B.projectedEdge_card_le hg₀)
  let z : EdgeComplement g₀ → G :=
    fun v => A.witness (B.projection v.1)
  let xK : K → G :=
    (splitEdgeEquiv g₀).symm (y, z)
  have hxK : edgeTuple g₀ xK = y := by
    exact edgeTuple_splitEdgeEquiv_symm g₀ y z
  have hlocalProduct :
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK := by
    calc
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A))
          (edgeTuple g₀ xK) := by
            rw [hxK]
      _ =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK :=
        B.strictBoundaryLocalProduct_edgeTuple g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK
  have hempty : ∅ ∈ (B.strictBoundary g₀).edges := by
    apply (B.mem_strictBoundary_edges g₀ ∅).2
    refine ⟨hclosed hg₀ (Finset.empty_subset g₀), ?_⟩
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.empty_subset _, hne.ne_empty.symm⟩
  have hemptyWeight :
      B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (edgeTuple ∅ xK) = 1 := by
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      ((B.mem_strictBoundary_edges g₀ ∅).1 hempty).1]
    exact orderedConfigurationBaseWeight_empty A _
  rw [hlocalProduct]
  rw [sourceFullMixedBoundaryWeight_eq_strictFaceProduct P A e u]
  unfold bundleProduct partialConfigurationWeight
  rw [← Finset.prod_erase_mul _ _ hempty,
    hemptyWeight, mul_one]
  apply Finset.prod_bij
    (fun g _hg =>
      positiveOrderedFaceOfEdge
        (g.image B.projection)
        (Finset.image_nonempty.mpr
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_erase.mp _hg).1))
        (B.projectedEdge_card_le
          (((B.mem_strictBoundary_edges g₀ g).1
            (Finset.mem_of_mem_erase _hg)).1)))
  · intro g hg
    simp only [Finset.mem_erase] at hg
    rw [mem_orderedConfigurationStrictFaceFamily]
    rw [positiveOrderedFaceEdge_ofEdge]
    rw [heedge]
    have hgstrict :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2
    constructor
    · intro j hj
      obtain ⟨v, hvg, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr
        ⟨v, hgstrict.1 hvg, rfl⟩
    · intro hreverse
      apply hgstrict.2
      intro v hvg₀
      obtain ⟨w, hwg, hwv⟩ :=
        Finset.mem_image.mp
          (hreverse
            (Finset.mem_image.mpr
              ⟨v, hvg₀, rfl⟩))
      have hwg₀ : w ∈ g₀ := hgstrict.1 hwg
      have hwv' : w = v :=
        B.projection_injective_on_edge
          g₀ hg₀ hwg₀ hvg₀ hwv
      exact hwv' ▸ hwg
  · intro g₁ hg₁ g₂ hg₂ heq
    have himage :
        g₁.image B.projection =
          g₂.image B.projection := by
      simpa only [positiveOrderedFaceEdge_ofEdge] using
        congrArg positiveOrderedFaceEdge heq
    have hg₁sub :=
      ((B.mem_strictBoundary_edges g₀ g₁).1
        (Finset.mem_of_mem_erase hg₁)).2.1
    have hg₂sub :=
      ((B.mem_strictBoundary_edges g₀ g₂).1
        (Finset.mem_of_mem_erase hg₂)).2.1
    rw [← B.liftProjectedSubedge_image_eq hg₀ hg₁sub,
      ← B.liftProjectedSubedge_image_eq hg₀ hg₂sub,
      himage]
  · intro f hf
    have hfe :=
      (mem_orderedConfigurationStrictFaceFamily e f).1 hf
    let t := positiveOrderedFaceEdge f
    let g := B.liftProjectedSubedge g₀ t
    have ht : t ⊆ g₀.image B.projection := by
      simpa [e, orderedConfigurationBundleFace,
        positiveOrderedFaceEdge_ofEdge] using hfe.1
    have hgsub : g ⊆ g₀ :=
      B.liftProjectedSubedge_subset g₀ t
    have hgmem : g ∈ B.edges :=
      hclosed hg₀ hgsub
    have himage : g.image B.projection = t :=
      B.image_liftProjectedSubedge g₀ ht
    have hgne : g ≠ ∅ := by
      intro hzero
      have : t = ∅ := by simpa [hzero] using himage.symm
      have htne := positiveOrderedFaceEdge_nonempty f
      change t.Nonempty at htne
      rw [this] at htne
      exact Finset.not_nonempty_empty htne
    have hgproper : g ⊂ g₀ := by
      refine ⟨hgsub, ?_⟩
      intro hgg
      have hgeq : g = g₀ :=
        Finset.Subset.antisymm hgsub hgg
      have : t = g₀.image B.projection := by
        rw [← himage, hgeq]
      apply hfe.2
      rw [heedge, ← this]
    refine ⟨g, Finset.mem_erase.mpr
      ⟨hgne,
        (B.mem_strictBoundary_edges g₀ g).2
          ⟨hgmem, hgproper⟩⟩, ?_⟩
    apply positiveOrderedFaceEdge_injective
    simpa only [positiveOrderedFaceEdge_ofEdge] using himage
  · intro g hg
    simp only [Finset.mem_erase] at hg
    have hgB :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).1
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A) hgB]
    unfold orderedConfigurationBaseWeight
    simp only [dif_pos (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hg.1))]
    simp only [dif_pos (B.projectedEdge_card_le hgB)]
    congr 1
    have hgne : g.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hg.1
    change
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) =
        orderedFaceTuple
          (B.orderedConfigurationBundleFace hgB hgne).face x
    funext i
    let v : {v : K // v ∈ g} :=
      (B.projectionEquiv hgB).symm
        (B.projectedEdgeOrderIso hgB hgne i)
    have hgsub :
        g ⊆ g₀ :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2.1
    let v₀ : {v : K // v ∈ g₀} :=
      ⟨v.1, hgsub v.2⟩
    have hprojection :
        (B.orderedConfigurationBundleFace hgB hgne).face i =
          B.projection v₀.1 := by
      calc
        (B.orderedConfigurationBundleFace hgB hgne).face i =
            (B.projectedEdgeOrderIso hgB hgne i).1 := by
          rw [B.projectedEdgeOrderIso_apply_val]
        _ = ((B.projectionEquiv hgB) v).1 := by
          rw [Equiv.apply_symm_apply]
        _ = B.projection v.1 :=
          B.projectionEquiv_apply_val hgB v
        _ = B.projection v₀.1 := rfl
    calc
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) i =
          xK v.1 := by
        rfl
      _ = y v₀ := by
        have hv := congrFun hxK v₀
        exact hv
      _ = x (B.projection v₀.1) := by
        symm
        exact
          B.extendConfigurationFaceTuple_projection
            P A hg₀ hne y v₀
      _ =
          orderedFaceTuple
            (B.orderedConfigurationBundleFace hgB hgne).face
            x i := by
        rw [orderedFaceTuple, hprojection]

/-! ## Transport of the localized estimate -/

theorem strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty) :
    (B.strictBoundary g₀).bundleCount
        ((B.strictBoundary g₀).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) =
      mean (sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)) := by
  classical
  rw [← B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.strictBoundary g₀)
    (Finset.filter_subset _ _)
    rfl
    (orderedConfigurationBaseWeight A)]
  cases isEmpty_or_nonempty G with
  | inl hG =>
      letI : IsEmpty G := hG
      haveI : Nonempty K := ⟨hne.choose⟩
      haveI :
          Nonempty
            (Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1)) :=
        ⟨⟨0, Nat.succ_pos _⟩⟩
      simp only [bundleCount, mean_empty]
  | inr hG =>
      letI : Nonempty G := hG
      unfold bundleCount
      rw [mean_splitEdge g₀]
      unfold mean₂
      have hfiber :
          ∀ y : {v : K // v ∈ g₀} → G,
            mean (fun z : EdgeComplement g₀ → G =>
                (B.strictBoundary g₀).bundleProduct
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A))
                  ((splitEdgeEquiv g₀).symm (y, z))) =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv
                  hg₀ hne y) := by
        intro y
        calc
          mean (fun z : EdgeComplement g₀ → G =>
              (B.strictBoundary g₀).bundleProduct
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))
                ((splitEdgeEquiv g₀).symm (y, z))) =
              mean (fun _z : EdgeComplement g₀ → G =>
                B.strictBoundaryLocalProduct g₀
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A)) y) := by
            apply congrArg mean
            funext z
            rw [← B.strictBoundaryLocalProduct_edgeTuple g₀
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z))]
            rw [edgeTuple_splitEdgeEquiv_symm]
          _ =
              B.strictBoundaryLocalProduct g₀
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) y := by
            exact mean_const _
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTuple hg₀ hne y) :=
            B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
              P A hclosed hg₀ hne y
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y) := by
            rw [orderedConfigurationBundleFaceTupleEquiv_apply]
      rw [show
        (fun y : {v : K // v ∈ g₀} → G =>
          mean (fun z : EdgeComplement g₀ → G =>
            (B.strictBoundary g₀).bundleProduct
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z)))) =
          fun y =>
            sourceFullMixedBoundaryWeight P A
              (B.orderedConfigurationBundleFace hg₀ hne)
              (B.orderedConfigurationBundleFaceTupleEquiv
                hg₀ hne y) by
        funext y
        exact hfiber y]
      exact mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
        (fun y =>
          sourceFullMixedBoundaryWeight P A
            (B.orderedConfigurationBundleFace hg₀ hne)
            (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y))
        (sourceFullMixedBoundaryWeight P A
          (B.orderedConfigurationBundleFace hg₀ hne))
        (fun _ => rfl)

/-- Source-full mixed goodness is exactly the weighted localization input
required by the generalized bundle-counting step. -/
theorem hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β) :
    HasOrderedConfigurationBundleLocalizedDefect P A β := by
  intro K _ _ B hclosed g₀ hg₀ hmax hne
  let e := B.orderedConfigurationBundleFace hg₀ hne
  have hrank : e.rank = g₀.card := by
    unfold e orderedConfigurationBundleFace
    rw [← positiveOrderedFaceEdge_card]
    rw [positiveOrderedFaceEdge_ofEdge]
    exact B.card_image_projection hg₀
  have hlocal := hgood.localized_defect P A α β e
  rw [← hrank]
  rw [B.strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    P A hclosed hg₀ hne]
  calc
    mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) =
        sourceFullMixedLocalizedDefectSq P A e := by
      apply mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
      intro y
      unfold orderedConfigurationBundleLocalizedDefect
        orderedConfigurationBundleDefect
        sourceFullMixedDefect
      rw [B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
        P A hclosed hg₀ hne y]
      rw [mul_pow, sourceFullMixedBoundaryWeight_sq]
      rw [orderedConfigurationBundleFaceTupleEquiv_apply]
    _ ≤
        β e.rank *
          mean (sourceFullMixedBoundaryWeight P A e) :=
      hlocal

end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleCounting.lean` -/

section
/-!
# Source-full generalized bundle counting

This file assembles the source-full goodness and preliminary-regularity
certificates into the relative generalized bundle-counting theorem.  The
common density floor is `a`, while both analytic errors are `t ^ 2`; the
explicit schedule `bundleCommonEnvelopeError a t` then controls every
closed bundle pulled back from the ordered configuration.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The common density floor on base edges -/

/-! ## Relative counting for every closed pullback bundle -/

/-! ## Initial bundle and positivity -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StrongFullOrderedRegularity.lean` -/

section
/-!
# Strong all-rank ordered regularity towers

This file iterates the all-rank preliminary regularity theorem using
tolerance and budget schedules fixed before the tower is constructed.
Every transition refines the preceding complex, preserves its top layer,
and is regular for all bounded boundary products at the scheduled
tolerance.  A recursive numerical factor bounds every non-top partition
complexity independently of the ambient type.

For energy selection, the upper atom family must be held fixed.  We
therefore prove an adjacent-gap pigeonhole theorem for an arbitrary fixed
target complex.  The final section records the exact identity relating this
valid fixed-target potential to the moving-upper potential of consecutive
tower stages.  Its extra upper-refinement loss is the precise obstruction
to obtaining Tao's strong coarse/fine conclusion from a naive moving
potential.

All schedules in this file are arguments to the construction; none is
chosen after inspecting an ambient-dependent partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded-test all-rank regularity -/

/-- Every adjacent pair is regular against arbitrary `[0,1]`-valued
boundary factors. -/
def IsFullyPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedBoundedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

/-- Boolean all-rank preliminary regularity controls bounded boundary
products with no loss. -/
theorem IsFullyPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    {ε : OrderedRegularityTolerance r}
    (h : IsFullyPreliminaryOrderedRegular C ε) :
    IsFullyPreliminaryOrderedBoundedRegular C ε := by
  intro j
  exact (h j).toBounded

/-! ## Canonical precomputed tower -/

/-- Canonical choice of one all-rank fixed-budget certificate. -/
noncomputable def chosenFullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (budget : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget :
      IsOrderedRegularityBudget k r ε budget) :
    FullOrderedRegularityCertificate C ε budget :=
  Classical.choice
    (exists_fullOrderedRegularityCertificate
      C ε budget hε hbudget)

/-- An infinite tower whose `n`th transition uses only the schedules
`ε n` and `budget n`, both supplied before construction. -/
noncomputable def strongFullOrderedRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    ℕ → OrderedPartitionComplex G k r
  | 0 => initial
  | n + 1 =>
      (chosenFullOrderedRegularityCertificate
        (strongFullOrderedRegularityTower
          initial ε budget hε hbudget n)
        (ε n) (budget n) (hε n) (hbudget n)).fine

@[simp]
theorem strongFullOrderedRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    strongFullOrderedRegularityTower
      initial ε budget hε hbudget 0 = initial :=
  rfl

@[simp]
theorem strongFullOrderedRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    strongFullOrderedRegularityTower
        initial ε budget hε hbudget (n + 1) =
      (chosenFullOrderedRegularityCertificate
        (strongFullOrderedRegularityTower
          initial ε budget hε hbudget n)
        (ε n) (budget n) (hε n) (hbudget n)).fine :=
  rfl

/-! ## Recursive ambient-independent complexity bound -/

/-- Precomputed multiplicative complexity factor through the first `n`
tower transitions at rank `j`. -/
def strongFullOrderedComplexityFactor
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j.1 + 1)) ^ (budget n j) *
        strongFullOrderedComplexityFactor budget j n

@[simp]
theorem strongFullOrderedComplexityFactor_zero
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) :
    strongFullOrderedComplexityFactor budget j 0 = 1 :=
  rfl

@[simp]
theorem strongFullOrderedComplexityFactor_succ
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) (n : ℕ) :
    strongFullOrderedComplexityFactor budget j (n + 1) =
      (2 ^ (j.1 + 1)) ^ (budget n j) *
        strongFullOrderedComplexityFactor budget j n :=
  rfl

/-! ## Fixed-upper-family all-rank energy -/

/-! ## Moving-upper bridge and the exact loss -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StrongOrderedComplexRegularity.lean` -/

section
/-!
# Strong coarse/fine regularity for ordered partition complexes

The changing-upper-family obstruction disappears if ranks are selected from
top to bottom.  At rank `j`, freeze the already chosen fine rank-`j+1`
partition and run a long tower of rank-`j` refinements.  An energy
pigeonhole then selects nested coarse/fine rank-`j` partitions with small
energy gap against that fixed upper family.  The fine rank-`j` partition
becomes the frozen target for the next lower rank.

This file first proves the fixed-upper one-rank selector, including fully
precomputed tolerance, budget, and complexity schedules.  It then assembles
those selectors recursively into two ordered partition complexes.  The
resulting fine complex is bounded-test preliminarily regular at every rank,
refines the coarse complex, and has a genuinely small
`totalAtomEnergyGap`: every summand is measured against the corresponding
final fine upper layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## One fixed-upper regularity step -/

/-- Output of one fixed-budget lower-layer regularization with its explicit
step count and complexity certificate. -/
structure FixedUpperLayerRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ) where
  steps : ℕ
  fine : OrderedFacePartitionSystem G k j
  steps_lt : steps < budget
  refines : OrderedFacePartitionRefines fine lower
  regular : IsPreliminaryOrderedRegular fine upper ε
  complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        (2 ^ (j + 1)) ^ steps *
          FacePartition.complexity (lower e)

theorem FixedUpperLayerRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {budget : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    Nonempty
      (FixedUpperLayerRegularityCertificate
        G k j lower upper ε budget) := by
  obtain ⟨steps, fine, hsteps, hrefines,
      hregular, hcomplexity⟩ :=
    exists_preliminaryOrderedRegular_refinement_with_complexity_before
      lower upper hε hlong
  exact ⟨{
    steps := steps
    fine := fine
    steps_lt := hsteps
    refines := hrefines
    regular := hregular
    complexity := hcomplexity }⟩

/-- Canonical choice of one fixed-upper lower-layer regularization. -/
noncomputable def chosenFixedUpperLayerRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    FixedUpperLayerRegularityCertificate
      G k j lower upper ε budget :=
  Classical.choice
    (FixedUpperLayerRegularityCertificate.nonempty
      lower upper hε hlong)

/-! ## Canonical fixed-upper tower -/

/-- A lower-layer tower whose upper atom family remains fixed throughout. -/
noncomputable def fixedUpperLayerRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => initial
  | n + 1 =>
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine

@[simp]
theorem fixedUpperLayerRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong 0 = initial :=
  rfl

@[simp]
theorem fixedUpperLayerRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1) =
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine :=
  rfl

/-- Every fixed-upper tower transition refines its predecessor. -/
theorem fixedUpperLayerRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    OrderedFacePartitionRefines
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).refines

/-- Every fixed-upper tower stage refines the initial lower layer. -/
theorem fixedUpperLayerRegularityTower_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      OrderedFacePartitionRefines
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl initial
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong n)
        ih

/-- Stage `n+1` is regular for the fixed upper family at tolerance `ε n`. -/
theorem fixedUpperLayerRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    IsPreliminaryOrderedRegular
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      upper (ε n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).regular

/-- Recursive complexity factor for a fixed-upper rank-`j` tower. -/
def fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (budget n) *
        fixedUpperLayerComplexityFactor j budget n

/-- Complexity after `n` fixed-upper stages remains ambient-independent. -/
theorem complexity_fixedUpperLayerRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : OrderedFace k j),
      FacePartition.complexity
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n e) ≤
        fixedUpperLayerComplexityFactor j budget n *
          FacePartition.complexity (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      intro e
      let certificate :=
        chosenFixedUpperLayerRegularityCertificate
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n)
          upper (ε n) (budget n)
          (hε n) (hlong n)
      have hstep := certificate.complexity e
      have hexponent :
          (2 ^ (j + 1)) ^ certificate.steps ≤
            (2 ^ (j + 1)) ^ (budget n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt certificate.steps_lt)
      rw [fixedUpperLayerRegularityTower_succ]
      calc
        FacePartition.complexity (certificate.fine e) ≤
            (2 ^ (j + 1)) ^ certificate.steps *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          hstep
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          Nat.mul_le_mul_right _ hexponent
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              (fixedUpperLayerComplexityFactor
                  j budget n *
                FacePartition.complexity (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            fixedUpperLayerComplexityFactor
                j budget (n + 1) *
              FacePartition.complexity (initial e) := by
          simp [fixedUpperLayerComplexityFactor,
            Nat.mul_assoc]

/-! ## Fixed-upper adjacent selection -/

/-- Selected coarse/fine lower layers for one fixed upper atom family. -/
structure FixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (ε index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ)
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

/-- A bounded real sequence has an adjacent increment at most its endpoint
budget divided by the number of transitions. -/
theorem exists_adjacent_real_sub_le_div
    (E : ℕ → ℝ) {length : ℕ}
    (hlength : 0 < length)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [htel]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

/-- Fixed-upper strong selection at one rank. -/
theorem FixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (hlength : 0 < length) :
    Nonempty
      (FixedUpperLayerCoarseFine
        G k j initial upper ε budget length) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_le_div
      (fun n => orderedLayerAtomEnergy
        (tower n) upper)
      hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact fixedUpperLayerRegularityTower_refines
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_refines_initial
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_regular
      initial upper ε budget hε hlong i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong i)
        upper)
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong i
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong (i + 1)

/-- Canonical fixed-upper coarse/fine choice. -/
noncomputable def chosenFixedUpperLayerCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (hlength : 0 < length) :
    FixedUpperLayerCoarseFine
      G k j initial upper ε budget length :=
  Classical.choice
    (FixedUpperLayerCoarseFine.nonempty
      initial upper ε budget hε hlong hlength)

/-! ## Top-down all-rank assembly -/

/-- Tolerance selected from the precomputed inner timescale at each rank. -/
def selectedOrderedComplexTolerance
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    OrderedRegularityTolerance r :=
  fun j => ε j (index j)

/-- Complete top-down strong regularity certificate. -/
structure StrongOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (selectedOrderedComplexTolerance ε index)
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace StrongOrderedComplexRegularityCertificate

/-- Package the selected complexes as an ordered coarse/fine pair. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end StrongOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/

/-- Top-down frozen-upper construction of strong ordered complex
regularity. -/
theorem StrongOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    Nonempty
      (StrongOrderedComplexRegularityCertificate
        G k r initial ε budget length) := by
  induction r with
  | zero =>
      let index : Fin 0 → ℕ := fun j => Fin.elim0 j
      refine ⟨{
        index := index
        coarse := initial
        fine := initial
        refines :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_refines_initial :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_topLayer_eq := rfl
        fine_topLayer_eq := rfl
        index_lt := ?_
        regular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerInitial :
          OrderedFacePartitionSystem G k r :=
        initial.dropTop.topLayer
      let upper :
          OrderedFacePartitionSystem G k (r + 1) :=
        initial.topLayer
      have hεtop :
          ∀ n, 0 ≤ ε (Fin.last r) n :=
        fun n => hε (Fin.last r) n
      have hlongTop :
          ∀ n,
            (Fintype.card
              (OrderedFace k (r + 1)) : ℝ) <
              (budget (Fin.last r) n : ℝ) *
                (ε (Fin.last r) n) ^ 2 := by
        intro n
        have h := hlong (Fin.last r) n
        change
          (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
            (budget (Fin.last r) n : ℝ) *
              (ε (Fin.last r) n) ^ 2 at h
        exact h
      let topChoice :=
        chosenFixedUpperLayerCoarseFine
          lowerInitial upper
          (ε (Fin.last r))
          (budget (Fin.last r))
          hεtop hlongTop
          (length (Fin.last r))
          (hlength (Fin.last r))
      let prepared :
          OrderedPartitionComplex G k r :=
        initial.dropTop.withTopLayer topChoice.fine
      let εlower : (j : Fin r) → ℕ → ℝ :=
        fun j => ε j.castSucc
      let budgetLower : (j : Fin r) → ℕ → ℕ :=
        fun j => budget j.castSucc
      let lengthLower : Fin r → ℕ :=
        fun j => length j.castSucc
      have hεlower :
          ∀ j n, 0 ≤ εlower j n :=
        fun j n => hε j.castSucc n
      have hlongLower :
          ∀ j n,
            (Fintype.card
              (OrderedFace k (j.1 + 1)) : ℝ) <
              (budgetLower j n : ℝ) *
                (εlower j n) ^ 2 :=
        fun j n => hlong j.castSucc n
      have hlengthLower :
          ∀ j, 0 < lengthLower j :=
        fun j => hlength j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower budgetLower lengthLower
          hεlower hlongLower hlengthLower
      let coarsePrefix :
          OrderedPartitionComplex G k r :=
        lowerCertificate.coarse.withTopLayer
          topChoice.coarse
      let coarse :
          OrderedPartitionComplex G k (r + 1) :=
        coarsePrefix.appendTop upper
      let fine :
          OrderedPartitionComplex G k (r + 1) :=
        lowerCertificate.fine.appendTop upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases topChoice.index
            lowerCertificate.index j
      have hlowerFineTop :
          lowerCertificate.fine.topLayer =
            topChoice.fine := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.fine_topLayer_eq
          _ = topChoice.fine :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.fine
      have hlowerCoarseTop :
          lowerCertificate.coarse.topLayer =
            topChoice.fine := by
        calc
          lowerCertificate.coarse.topLayer =
              prepared.topLayer :=
            lowerCertificate.coarse_topLayer_eq
          _ = topChoice.fine :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.fine
      refine ⟨{
        index := index
        coarse := coarse
        fine := fine
        refines := ?_
        coarse_refines_initial := ?_
        coarse_topLayer_eq := ?_
        fine_topLayer_eq := ?_
        index_lt := ?_
        regular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · have hprefix :
            lowerCertificate.fine.Refines
              coarsePrefix := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              have heq :
                  lowerCertificate.fine.partition
                      (Fin.last r) e =
                    topChoice.fine e :=
                congrFun hlowerFineTop e
              rw [heq]
              exact topChoice.refines e
          | cast i =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              exact lowerCertificate.refines
                i.castSucc e
        exact OrderedPartitionComplex.appendTop_refines
          hprefix
          (OrderedFacePartitionRefines.refl upper)
      · have hprefix :
            coarsePrefix.Refines initial.dropTop := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              exact topChoice.coarse_refines_initial e
          | cast i =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              have h :=
                lowerCertificate.coarse_refines_initial
                  i.castSucc e
              simpa only [prepared,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc,
                OrderedPartitionComplex.dropTop] using h
        have happend :=
          OrderedPartitionComplex.appendTop_refines
            hprefix
            (OrderedFacePartitionRefines.refl upper)
        simpa [coarse, upper] using happend
      · simp [coarse, upper]
      · simp [fine, upper]
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simpa [index] using topChoice.index_lt
        | cast i =>
            simpa [index, lengthLower] using
              lowerCertificate.index_lt i
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              Fin.succ_last,
              selectedOrderedComplexTolerance,
              index, Fin.lastCases_last]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k r
                (lowerCertificate.fine.partition
                  (Fin.last r))
                upper
                (ε (Fin.last r) topChoice.index)
            have hregular := topChoice.fine_regular
            rw [← hlowerFineTop] at hregular
            exact hregular
        | cast i =>
            have hregular :=
              lowerCertificate.regular i
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.succ_castSucc,
              selectedOrderedComplexTolerance,
              index, Fin.lastCases_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition
                  i.castSucc)
                (lowerCertificate.fine.partition i.succ)
                (ε i.castSucc
                  (lowerCertificate.index i))
            exact hregular
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_nonneg
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                orderedLayerAtomEnergy
                    lowerCertificate.fine.topLayer upper -
                  orderedLayerAtomEnergy
                    topChoice.coarse upper
            rw [hlowerFineTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_nonneg i
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc]
            convert hgap using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_le
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              orderedLayerAtomEnergy
                    lowerCertificate.fine.topLayer upper -
                  orderedLayerAtomEnergy
                    topChoice.coarse upper ≤
                (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [hlowerFineTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_le i
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc, lengthLower]
            convert hgap using 1 <;> rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have hcomplexity :=
              topChoice.coarse_complexity e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            change OrderedFace k r at e
            change
              FacePartition.complexity
                    (topChoice.coarse e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    topChoice.index *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.coarse_complexity i e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.coarse.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change OrderedFace k r at e
            have hcomplexity :=
              topChoice.fine_complexity e
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_last]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    (Fin.last r) e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    (topChoice.index + 1) *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                lowerCertificate.fine.partition
                    (Fin.last r) e =
                  topChoice.fine e :=
              congrFun hlowerFineTop e
            rw [heq]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.fine_complexity i e
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i + 1) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1

/-! ## Quantitative consequences -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseTargetRegularity.lean` -/

section
/-!
# Strong ordered regularity with coarse upper targets

The usual top-down strong certificate freezes the final fine upper layer
while selecting the adjacent coarse/fine lower layers.  For coarse
configuration counting and cleaning, the more useful target is instead the
final coarse upper layer.

This file carries out that variant directly.  At the current top rank we
select a coarse/fine lower pair against the unchanged top layer.  The
recursive call is then made with the selected *coarse* lower layer as its
top layer.  After recursion, only the fine prefix's top layer is replaced
by the selected fine layer.  Thus every lower-rank regularity statement and
energy gap keeps the recursively selected coarse upper layer as its target.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A top-down strong regularity certificate in which the observing fine
lower boundary is regular against the final coarse upper layer, and the
rankwise energy gap is measured against that same coarse upper layer. -/
structure CoarseTargetOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  mixedRegular :
    ∀ j : Fin r,
      IsPreliminaryOrderedRegular
        (fine.partition j.castSucc)
        (coarse.partition j.succ)
        (ε j (index j))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Forget the quantitative certificate and retain its compatible
coarse/fine complexes. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/

/-- Top-down construction of a strong certificate whose upper target at
every adjacent rank is the final coarse layer. -/
theorem CoarseTargetOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    Nonempty
      (CoarseTargetOrderedComplexRegularityCertificate
        G k r initial ε budget length) := by
  induction r with
  | zero =>
      let index : Fin 0 → ℕ := fun j => Fin.elim0 j
      refine ⟨{
        index := index
        coarse := initial
        fine := initial
        refines :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_refines_initial :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_topLayer_eq := rfl
        fine_topLayer_eq := rfl
        index_lt := ?_
        mixedRegular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerInitial :
          OrderedFacePartitionSystem G k r :=
        initial.dropTop.topLayer
      let upper :
          OrderedFacePartitionSystem G k (r + 1) :=
        initial.topLayer
      have hεtop :
          ∀ n, 0 ≤ ε (Fin.last r) n :=
        fun n => hε (Fin.last r) n
      have hlongTop :
          ∀ n,
            (Fintype.card
              (OrderedFace k (r + 1)) : ℝ) <
              (budget (Fin.last r) n : ℝ) *
                (ε (Fin.last r) n) ^ 2 := by
        intro n
        have h := hlong (Fin.last r) n
        change
          (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
            (budget (Fin.last r) n : ℝ) *
              (ε (Fin.last r) n) ^ 2 at h
        exact h
      let topChoice :=
        chosenFixedUpperLayerCoarseFine
          lowerInitial upper
          (ε (Fin.last r))
          (budget (Fin.last r))
          hεtop hlongTop
          (length (Fin.last r))
          (hlength (Fin.last r))
      let prepared :
          OrderedPartitionComplex G k r :=
        initial.dropTop.withTopLayer topChoice.coarse
      let εlower : (j : Fin r) → ℕ → ℝ :=
        fun j => ε j.castSucc
      let budgetLower : (j : Fin r) → ℕ → ℕ :=
        fun j => budget j.castSucc
      let lengthLower : Fin r → ℕ :=
        fun j => length j.castSucc
      have hεlower :
          ∀ j n, 0 ≤ εlower j n :=
        fun j n => hε j.castSucc n
      have hlongLower :
          ∀ j n,
            (Fintype.card
              (OrderedFace k (j.1 + 1)) : ℝ) <
              (budgetLower j n : ℝ) *
                (εlower j n) ^ 2 :=
        fun j n => hlong j.castSucc n
      have hlengthLower :
          ∀ j, 0 < lengthLower j :=
        fun j => hlength j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower budgetLower lengthLower
          hεlower hlongLower hlengthLower
      let coarsePrefix :
          OrderedPartitionComplex G k r :=
        lowerCertificate.coarse
      let finePrefix :
          OrderedPartitionComplex G k r :=
        lowerCertificate.fine.withTopLayer topChoice.fine
      let coarse :
          OrderedPartitionComplex G k (r + 1) :=
        coarsePrefix.appendTop upper
      let fine :
          OrderedPartitionComplex G k (r + 1) :=
        finePrefix.appendTop upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases topChoice.index
            lowerCertificate.index j
      have hlowerFineTop :
          lowerCertificate.fine.topLayer =
            topChoice.coarse := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.fine_topLayer_eq
          _ = topChoice.coarse :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.coarse
      have hlowerCoarseTop :
          lowerCertificate.coarse.topLayer =
            topChoice.coarse := by
        calc
          lowerCertificate.coarse.topLayer =
              prepared.topLayer :=
            lowerCertificate.coarse_topLayer_eq
          _ = topChoice.coarse :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.coarse
      refine ⟨{
        index := index
        coarse := coarse
        fine := fine
        refines := ?_
        coarse_refines_initial := ?_
        coarse_topLayer_eq := ?_
        fine_topLayer_eq := ?_
        index_lt := ?_
        mixedRegular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · have hprefix :
            finePrefix.Refines coarsePrefix := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [finePrefix, coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              have heq :
                  lowerCertificate.coarse.partition
                      (Fin.last r) e =
                    topChoice.coarse e :=
                congrFun hlowerCoarseTop e
              rw [heq]
              exact topChoice.refines e
          | cast i =>
              simp only [finePrefix, coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              exact lowerCertificate.refines
                i.castSucc e
        exact OrderedPartitionComplex.appendTop_refines
          hprefix
          (OrderedFacePartitionRefines.refl upper)
      · have hprepared :
            prepared.Refines initial.dropTop := by
          exact OrderedPartitionComplex.withTopLayer_refines
            initial.dropTop topChoice.coarse
            (by
              simpa only [lowerInitial] using
                topChoice.coarse_refines_initial)
        have hprefix :
            coarsePrefix.Refines initial.dropTop :=
          OrderedPartitionComplex.Refines.trans
            lowerCertificate.coarse_refines_initial
            hprepared
        have happend :=
          OrderedPartitionComplex.appendTop_refines
            hprefix
            (OrderedFacePartitionRefines.refl upper)
        simpa [coarse, coarsePrefix, upper] using happend
      · simp [coarse, upper]
      · simp [fine, upper]
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simpa [index] using topChoice.index_lt
        | cast i =>
            simpa [index, lengthLower] using
              lowerCertificate.index_lt i
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last,
              index, Fin.lastCases_last]
            exact topChoice.fine_regular
        | cast i =>
            have hregular :=
              lowerCertificate.mixedRegular i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              index, Fin.lastCases_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition
                  i.castSucc)
                (lowerCertificate.coarse.partition
                  i.succ)
                (ε i.castSucc
                  (lowerCertificate.index i))
            exact hregular
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_nonneg
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                orderedLayerAtomEnergy
                    topChoice.fine upper -
                  orderedLayerAtomEnergy
                    lowerCertificate.coarse.topLayer
                    upper
            rw [hlowerCoarseTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_nonneg i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc]
            convert hgap using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_le
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              orderedLayerAtomEnergy
                    topChoice.fine upper -
                  orderedLayerAtomEnergy
                    lowerCertificate.coarse.topLayer
                    upper ≤
                (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [hlowerCoarseTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_le i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              lengthLower]
            convert hgap using 1 <;> rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change OrderedFace k r at e
            have hcomplexity :=
              topChoice.coarse_complexity e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_last]
            change
              FacePartition.complexity
                  (lowerCertificate.coarse.partition
                    (Fin.last r) e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    topChoice.index *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                lowerCertificate.coarse.partition
                    (Fin.last r) e =
                  topChoice.coarse e :=
              congrFun hlowerCoarseTop e
            rw [heq]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.coarse_complexity i e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.coarse.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change OrderedFace k r at e
            have hcomplexity :=
              topChoice.fine_complexity e
            simp only [fine, finePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.fine_complexity i e
            simp only [fine, finePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i + 1) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1

/-! ## Total coarse-target gap -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/AdaptiveCoarseTargetRegularity.lean` -/

section
/-!
# Adaptive top-down coarse-target regularity

The fixed-vector coarse-target theorem chooses one tower index at every
rank, but fixes all tower lengths before any of those choices are known.
For the removal argument this is unnecessarily rigid: after the top-rank
index has been selected, the horizon at the next rank may be chosen as a
function of that index, and so on.

This file packages such data as a finite decision tree.  A node contains
the tolerance, budget, and horizon for the current (highest remaining)
rank, together with one subtree for every admissible index.  Thus a branch
is genuinely path dependent.  A landing is a root-to-leaf branch.  Its
data are flattened in the bottom-up rank order used by
`CoarseTargetOrderedComplexRegularityCertificate`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A finite tree of top-down regularity schedules.

At a node of height `r + 1`, the displayed schedule is used at rank `r`.
After an index `i : Fin length` is selected, `next i` is the schedule for
the remaining ranks.  In particular, every later horizon may depend on all
earlier selected indices. -/
inductive AdaptiveCoarseTargetSchedule (k : ℕ) : ℕ → Type
  | nil : AdaptiveCoarseTargetSchedule k 0
  | node {r : ℕ}
      (tolerance : ℕ → ℝ)
      (budget : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → AdaptiveCoarseTargetSchedule k r) :
      AdaptiveCoarseTargetSchedule k (r + 1)

namespace AdaptiveCoarseTargetSchedule

/-- The local energy-increment hypotheses hold at every node of an
adaptive schedule tree. -/
def IsAdmissible {k r : ℕ} :
    AdaptiveCoarseTargetSchedule k r → Prop
  | .nil => True
  | .node tolerance budget length next =>
      (∀ n, 0 ≤ tolerance n) ∧
      (∀ n,
        (Fintype.card (OrderedFace k r) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible

/-- A root-to-leaf landing in an adaptive schedule tree. -/
inductive Landing {k : ℕ} :
    {r : ℕ} → AdaptiveCoarseTargetSchedule k r → Type
  | nil : Landing (.nil : AdaptiveCoarseTargetSchedule k 0)
  | node {r : ℕ}
      {tolerance : ℕ → ℝ}
      {budget : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → AdaptiveCoarseTargetSchedule k r}
      (index : Fin length)
      (lower : Landing (next index)) :
      Landing (.node tolerance budget length next)

namespace Landing

/-- Flatten the tolerances along a landing into bottom-up rank order. -/
def tolerance {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (tolerance := tolerance) _ lower =>
      fun j => Fin.lastCases tolerance lower.tolerance j

/-- Flatten the tower budgets along a landing into bottom-up rank order. -/
def budget {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (budget := budget) _ lower =>
      fun j => Fin.lastCases budget lower.budget j

/-- Flatten the tower horizons along a landing into bottom-up rank order. -/
def length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j

/-- Flatten the selected indices along a landing into bottom-up rank order. -/
def index {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node chosen lower =>
      fun j => Fin.lastCases chosen.1 lower.index j

@[simp]
theorem tolerance_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance (Fin.last r) =
      tolerance := by
  simp [Landing.tolerance]

@[simp]
theorem tolerance_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j.castSucc =
      lower.tolerance j := by
  simp [Landing.tolerance]

@[simp]
theorem budget_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget (Fin.last r) =
      budget := by
  simp [Landing.budget]

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

@[simp]
theorem length_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length (Fin.last r) =
      length := by
  simp [Landing.length]

@[simp]
theorem length_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j.castSucc =
      lower.length j := by
  simp [Landing.length]

@[simp]
theorem index_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index (Fin.last r) =
      chosen.1 := by
  simp [Landing.index]

@[simp]
theorem index_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index j.castSucc =
      lower.index j := by
  simp [Landing.index]

/-- Every landing records indices within its path-dependent horizons. -/
theorem index_lt_length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    ∀ j, P.index j < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | node chosen lower ih =>
      intro j
      cases j using Fin.lastCases with
      | last =>
          simp [index, length]
      | cast j =>
          simpa [index, length] using ih j

/-- Admissibility supplies nonnegative tolerances along every landing. -/
theorem tolerance_nonneg {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j n, 0 ≤ P.tolerance j n := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨htolerance, _hbudget, _hlength, hnext⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          simpa using htolerance n
      | cast j =>
          simpa using ih (hnext chosen) j n

/-- Admissibility supplies the local regularity-budget inequality along
every landing. -/
theorem budget_spec {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j n,
      (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
        (P.budget j n : ℝ) * (P.tolerance j n) ^ 2 := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨_htolerance, hbudget, _hlength, hnext⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          change
            (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
              ((Landing.node
                (tolerance := tolerance) (budget := budget)
                chosen lower).budget (Fin.last r) n : ℕ) *
                (Landing.node
                  (tolerance := tolerance) (budget := budget)
                  chosen lower).tolerance (Fin.last r) n ^ 2
          rw [budget_node_last, tolerance_node_last]
          exact hbudget n
      | cast j =>
          change
            (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
              ((Landing.node
                (tolerance := tolerance) (budget := budget)
                chosen lower).budget j.castSucc n : ℕ) *
                (Landing.node
                  (tolerance := tolerance) (budget := budget)
                  chosen lower).tolerance j.castSucc n ^ 2
          rw [budget_node_castSucc, tolerance_node_castSucc]
          exact ih (hnext chosen) j n

/-- Admissibility supplies positive path-dependent horizons along every
landing. -/
theorem length_pos {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j, 0 < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨_htolerance, _hbudget, hlength, hnext⟩
      intro j
      cases j using Fin.lastCases with
      | last =>
          simpa using hlength
      | cast j =>
          simpa using ih (hnext chosen) j

end Landing

/-- A realization of an adaptive schedule is a landing together with an
ordinary coarse-target certificate whose actual selected indices are
exactly the indices of that landing.  Consequently the flattened schedule
used at every lower rank is the subtree chosen by the earlier, higher-rank
certificate indices. -/
structure Realization
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r) where
  landing : S.Landing
  certificate :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial
        landing.tolerance landing.budget landing.length
  index_eq : certificate.index = landing.index

/-- Every admissible adaptive schedule has a genuine top-down realization.

The proof is a downward rank induction.  At the current top rank it runs
the fixed-upper adjacent-energy selector, uses the selected index to enter
the corresponding subtree, and only then constructs the lower-rank
certificate.  The concluding equality of index vectors rules out the
spurious interpretation in which a branch is chosen independently of the
regularity certificate. -/
theorem Realization.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    Nonempty (Realization k r initial S) := by
  induction r with
  | zero =>
      cases S with
      | nil =>
          let landing :
              (AdaptiveCoarseTargetSchedule.nil :
                AdaptiveCoarseTargetSchedule k 0).Landing :=
            Landing.nil
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k 0 initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := initial
            fine := initial
            refines :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_refines_initial :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_topLayer_eq := rfl
            fine_topLayer_eq := rfl
            index_lt := fun j => Fin.elim0 j
            mixedRegular := fun j => Fin.elim0 j
            gap_nonneg := fun j => Fin.elim0 j
            gap_le := fun j => Fin.elim0 j
            coarse_complexity := fun j => Fin.elim0 j
            fine_complexity := fun j => Fin.elim0 j }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩
  | succ r ih =>
      cases S with
      | @node _ tolerance budget length next =>
          rcases hS with
            ⟨htolerance, hbudget, hlength, hnext⟩
          let lowerInitial :
              OrderedFacePartitionSystem G k r :=
            initial.dropTop.topLayer
          let upper :
              OrderedFacePartitionSystem G k (r + 1) :=
            initial.topLayer
          let topChoice :=
            chosenFixedUpperLayerCoarseFine
              lowerInitial upper tolerance budget
              htolerance hbudget length hlength
          let chosen : Fin length :=
            ⟨topChoice.index, topChoice.index_lt⟩
          let prepared :
              OrderedPartitionComplex G k r :=
            initial.dropTop.withTopLayer topChoice.coarse
          obtain ⟨lowerRealization⟩ :=
            ih prepared (next chosen) (hnext chosen)
          let lowerLanding := lowerRealization.landing
          let lowerCertificate := lowerRealization.certificate
          have hindexLower :
              lowerCertificate.index = lowerLanding.index :=
            lowerRealization.index_eq
          let landing :
              (AdaptiveCoarseTargetSchedule.node
                tolerance budget length next).Landing :=
            Landing.node
              (tolerance := tolerance) (budget := budget)
              chosen lowerLanding
          let coarsePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.coarse
          let finePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.fine.withTopLayer topChoice.fine
          let coarse :
              OrderedPartitionComplex G k (r + 1) :=
            coarsePrefix.appendTop upper
          let fine :
              OrderedPartitionComplex G k (r + 1) :=
            finePrefix.appendTop upper
          have hlowerFineTop :
              lowerCertificate.fine.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.fine.topLayer =
                  prepared.topLayer :=
                lowerCertificate.fine_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          have hlowerCoarseTop :
              lowerCertificate.coarse.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.coarse.topLayer =
                  prepared.topLayer :=
                lowerCertificate.coarse_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k (r + 1) initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := coarse
            fine := fine
            refines := by
              have hprefix :
                  finePrefix.Refines coarsePrefix := by
                intro q e
                cases q using Fin.lastCases with
                | last =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_last]
                    change OrderedFace k r at e
                    have heq :
                        lowerCertificate.coarse.partition
                            (Fin.last r) e =
                          topChoice.coarse e :=
                      congrFun hlowerCoarseTop e
                    rw [heq]
                    exact topChoice.refines e
                | cast i =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_castSucc]
                    exact lowerCertificate.refines
                      i.castSucc e
              exact OrderedPartitionComplex.appendTop_refines
                hprefix
                (OrderedFacePartitionRefines.refl upper)
            coarse_refines_initial := by
              have hprepared :
                  prepared.Refines initial.dropTop := by
                exact
                  OrderedPartitionComplex.withTopLayer_refines
                    initial.dropTop topChoice.coarse
                    (by
                      simpa only [lowerInitial] using
                        topChoice.coarse_refines_initial)
              have hprefix :
                  coarsePrefix.Refines initial.dropTop :=
                OrderedPartitionComplex.Refines.trans
                  lowerCertificate.coarse_refines_initial
                  hprepared
              have happend :=
                OrderedPartitionComplex.appendTop_refines
                  hprefix
                  (OrderedFacePartitionRefines.refl upper)
              simpa [coarse, coarsePrefix, upper] using happend
            coarse_topLayer_eq := by
              simp [coarse, upper]
            fine_topLayer_eq := by
              simp [fine, upper]
            index_lt := by
              exact landing.index_lt_length
            mixedRegular := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    IsPreliminaryOrderedRegular
                      topChoice.fine upper
                      (landing.tolerance (Fin.last r)
                        (landing.index (Fin.last r)))
                  simpa [landing, chosen] using
                    topChoice.fine_regular
              | cast i =>
                  have hregular :=
                    lowerCertificate.mixedRegular i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    @IsPreliminaryOrderedRegular
                      G _ _ k i.1
                      (lowerCertificate.fine.partition
                        i.castSucc)
                      (lowerCertificate.coarse.partition
                        i.succ)
                      (landing.tolerance i.castSucc
                        (landing.index i.castSucc))
                  rw [show landing.tolerance i.castSucc =
                      lowerLanding.tolerance i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  exact hregular
            gap_nonneg := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_nonneg
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    0 ≤
                      orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper
                  rw [hlowerCoarseTop]
                  exact hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_nonneg i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  convert hgap using 1
            gap_le := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_le
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper ≤
                      (Fintype.card
                        (OrderedFace k (r + 1)) : ℝ) /
                          (landing.length (Fin.last r) : ℝ)
                  rw [hlowerCoarseTop]
                  simpa [landing] using hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_le i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    orderedLayerAtomEnergy
                          (lowerCertificate.fine.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) -
                        orderedLayerAtomEnergy
                          (lowerCertificate.coarse.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) ≤
                      (Fintype.card
                        (OrderedFace k (i.1 + 1)) : ℝ) /
                          (landing.length i.castSucc : ℝ)
                  rw [show landing.length i.castSucc =
                      lowerLanding.length i by
                        simp [landing]]
                  exact hgap
            coarse_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.coarse_complexity e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          (Fin.last r) e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r)) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  have heq :
                      lowerCertificate.coarse.partition
                          (Fin.last r) e =
                        topChoice.coarse e :=
                    congrFun hlowerCoarseTop e
                  rw [heq]
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1 <;> rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.coarse_complexity i e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
                  all_goals rfl
            fine_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.fine_complexity e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last]
                  change
                    FacePartition.complexity
                        (topChoice.fine e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r) + 1) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1
                  all_goals rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.fine_complexity i e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.fine.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc + 1) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
                  all_goals rfl }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩

/-- Explicit existential form of adaptive coarse-target regularity.

This is the principal conversion endpoint for downstream arguments: it
returns an ordinary certificate, so all existing counting and cleaning
lemmas apply unchanged, while the equality identifies its index vector
with the realized decision-tree branch. -/
theorem exists_landing_certificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    ∃ P : S.Landing,
      ∃ R :
          CoarseTargetOrderedComplexRegularityCertificate
            G k r initial P.tolerance P.budget P.length,
        R.index = P.index := by
  obtain ⟨realization⟩ :=
    Realization.nonempty initial S hS
  exact
    ⟨realization.landing, realization.certificate,
      realization.index_eq⟩

end AdaptiveCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalParameters.lean` -/

section
/-!
# Quantitative parameters for ordered hypergraph removal

This file contains only the numerical layer of ordered removal.  Semantic
cover and contradiction arguments live elsewhere.

For a removal allowance `ξ > 0` and a uniform bound `M` on every selected
fine partition, write `S` for the number of positive subfaces of one top
face and `N` for the number of positive faces in the whole ordered
configuration.  We choose

```
ρ = min (1 / 2) (ξ / (4 * (S * M + 1))),
θ = ρ ^ N / (4 * (N + 1)),
α = ρ,   δ = η = θ,   β = θ²,
γ = ξ * β / 4.
```

Then the sharp cleaning error is at most

```
S * M * α + γ / β ≤ ξ / 2 < ξ,
```

whereas the configuration-count lower bound is strictly positive because

```
N * (η + δ) < ρ ^ N.
```

The final sections give ambient-independent ceiling schedules for weak
regularity and frozen-upper energy selection, derive a uniform complexity
bound from `StrongOrderedComplexRegularityCertificate`, and state bridge
theorems.  The bridge makes the remaining diagonal compatibility
transparent: the selected regularity tolerance must be at most `θ`, and
the reciprocal-timescale energy budget must be at most `γ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Face counts and explicit thresholds -/

/-- Number of positive faces in the complete ordered configuration. -/
noncomputable def orderedRemovalConfigurationFaceCount (k r : ℕ) : ℕ :=
  Fintype.card (PositiveOrderedFace k r)

/-- Number of positive subfaces occurring below one top rank-`r` face. -/
noncomputable def orderedRemovalTopSubfaceCount (r : ℕ) : ℕ :=
  Fintype.card (OrderedPositiveSubface r)

/-- The product `S * M` which multiplies the low-density threshold in the
per-top-face cleaning estimate. -/
noncomputable def orderedRemovalComplexityCoefficient (r M : ℕ) : ℕ :=
  orderedRemovalTopSubfaceCount r * M

/-- Constant density floor and low-density cleaning threshold. -/
noncomputable def orderedRemovalDensityFloor
    (r M : ℕ) (ξ : ℝ) : ℝ :=
  min (1 / 2)
    (ξ /
      (4 *
        ((orderedRemovalComplexityCoefficient r M : ℝ) + 1)))

/-- Equal regularity and square-root defect error reserved for one
configuration-count recurrence step. -/
noncomputable def orderedRemovalCountingError
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalDensityFloor r M ξ ^
      orderedRemovalConfigurationFaceCount k r /
    (4 *
      ((orderedRemovalConfigurationFaceCount k r : ℝ) + 1))

/-- Defect threshold used by good atoms. -/
noncomputable def orderedRemovalDefectThreshold
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalCountingError k r M ξ ^ 2

/-- Frozen-upper total atom-energy target. -/
noncomputable def orderedRemovalEnergyGapTarget
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  ξ * orderedRemovalDefectThreshold k r M ξ / 4

/-! ## Arithmetic margins -/

/-! ## Ambient-independent ceiling schedules -/

/-- A ceiling budget which is long enough to run one preliminary
regularity pass at tolerance `τ`. -/
noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1

/-- The ceiling construction satisfies the strict energy-length
hypothesis of one fixed-upper preliminary regularity pass. -/
theorem orderedRemovalRegularityBudget_spec
    {k j : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
      (orderedRemovalRegularityBudget k j τ : ℝ) * τ ^ 2 := by
  have hsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hquot :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          τ ^ 2 <
        (orderedRemovalRegularityBudget k j τ : ℝ) := by
    unfold orderedRemovalRegularityBudget
    calc
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (OrderedFace k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ hsq).1 hquot

/-! ## A uniform complexity bound for the strong certificate -/

/-- A deliberately coarse uniform bound for every rank of the selected
fine complex.  The sum dominates the factor at each non-top rank, while
the leading `1` also covers the unchanged top layer. -/
def orderedRemovalFinePartitionComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) : ℕ :=
  initialBound *
    (1 +
      ∑ j : Fin r,
        fixedUpperLayerComplexityFactor
          j.1 (budget j) (length j))

/-! ## Rank-sensitive target interface

The current counting theorem replaces every density floor by one global
`ρ` and every analytic error by global maxima `η, δ`.  The following
formulas record the sharper rank-dependent target without asserting a new
counting theorem.

* `orderedRemovalRankCleaningError` is the exact rankwise analogue of the
  sharp deletion estimate: upper complexity times `α`, plus the rank gap
  divided by `β`.
* `orderedRemovalRankDensityProduct` is the product of the actual
  rank-dependent density floors over all positive faces.
* `orderedRemovalRankCountingError` is one rank-dependent analytic error
  per positive face.

A rank-sensitive recurrence proving `count ≥ densityProduct - countingError`
would remove the present `min α` / `max ε` collapse.  Whether that interface,
together with a diagonal strong selector, closes the remaining schedule
feedback is deliberately left as a separate mathematical obligation.
-/

/-- Rank-dependent version of the sharp top-face cleaning error. -/
noncomputable def orderedRemovalRankCleaningError
    (r : ℕ)
    (complexity : Fin r → ℕ)
    (α : ℕ → ℝ)
    (gap : Fin r → ℝ)
    (β : ℕ → ℝ) : ℝ :=
  ∑ j : Fin r,
    ((Fintype.card
        (OrderedFace r (j.1 + 1)) : ℝ) *
        (complexity j : ℝ) * α (j.1 + 1) +
      gap j / β (j.1 + 1))

/-- Product of rank-dependent density floors over all positive ordered
faces in the complete configuration. -/
noncomputable def orderedRemovalRankDensityProduct
    (k r : ℕ) (α : ℕ → ℝ) : ℝ :=
  ∏ e : PositiveOrderedFace k r, α e.rank

/-- Sum of rank-dependent regularity and square-root defect errors over
all positive ordered faces. -/
noncomputable def orderedRemovalRankCountingError
    (k r : ℕ)
    (η : Fin r → ℝ)
    (δ : ℕ → ℝ) : ℝ :=
  ∑ e : PositiveOrderedFace k r,
    (η e.lowerRank + δ e.rank)

/-! ## Bridge from a compatible strong certificate -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GrowthFunctionRegularity.lean` -/

section
/-!
# One-rank growth-function regularity

This file packages the preliminary one-rank selector underlying the
growth-function form of hypergraph regularity.  For a natural-valued growth
function `F`, an initial complexity bound `M₀`, and a fixed upper layer, the
schedule is constructed triangularly:

```
M 0       = M₀,
τ n       = 1 / F (M n),
B n       = ⌈card (OrderedFace k (j + 1)) / (τ n)²⌉ + 1,
M (n + 1) = (2^(j+1))^(B n) * M n.
```

The existing fixed-upper tower then selects adjacent coarse and fine stages.
The fine stage is preliminarily regular with error exactly `τ i`; a
one-rank energy pigeonhole makes the coarse/fine gap at most any prescribed
positive `γ`.  All numerical schedules are ambient-independent.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Natural growth functions -/

/-- A natural growth function is monotone and lies strictly above the
diagonal.  The latter hypothesis ensures that all reciprocal tolerances are
positive, including when the initial complexity bound is zero. -/
structure NatGrowthFunction where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  above_diagonal : ∀ n, n + 1 ≤ toFun n

namespace NatGrowthFunction

instance : CoeFun NatGrowthFunction (fun _ => ℕ → ℕ) :=
  ⟨NatGrowthFunction.toFun⟩

theorem monotone (F : NatGrowthFunction) :
    Monotone F :=
  F.monotone'

theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)

end NatGrowthFunction

/-! ## The triangular numerical schedule -/

/-- Reciprocal growth-function tolerance at a displayed complexity. -/
noncomputable def growthRegularityStepTolerance
    (F : NatGrowthFunction) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)

/-- Ceiling budget for one preliminary regularity pass at the reciprocal
growth-function tolerance. -/
noncomputable def growthRegularityStepBudget
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  orderedRemovalRegularityBudget
    k j (growthRegularityStepTolerance F M)

/-- The triangular complexity sequence generated by the fixed-upper tower
factor and the budget computed from the current complexity. -/
noncomputable def growthRegularityComplexity
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ
  | 0 => initialBound
  | n + 1 =>
      (2 ^ (j + 1)) ^
          growthRegularityStepBudget
            k j F
              (growthRegularityComplexity
                k j initialBound F n) *
        growthRegularityComplexity
          k j initialBound F n

/-- Stagewise reciprocal tolerance obtained from the triangular complexity
sequence. -/
noncomputable def growthRegularityTolerance
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℝ :=
  fun n =>
    growthRegularityStepTolerance F
      (growthRegularityComplexity
        k j initialBound F n)

/-- Stagewise ceiling budget obtained from the same triangular sequence. -/
noncomputable def growthRegularityBudget
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ :=
  fun n =>
    growthRegularityStepBudget k j F
      (growthRegularityComplexity
        k j initialBound F n)

@[simp]
theorem growthRegularityComplexity_zero
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
      k j initialBound F 0 = initialBound :=
  rfl

@[simp]
theorem growthRegularityComplexity_succ
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      (2 ^ (j + 1)) ^
          growthRegularityBudget
            k j initialBound F n *
        growthRegularityComplexity
          k j initialBound F n :=
  rfl

@[simp]
theorem growthRegularityTolerance_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityTolerance
        k j initialBound F n =
      1 /
        (F (growthRegularityComplexity
          k j initialBound F n) : ℝ) :=
  rfl

@[simp]
theorem growthRegularityBudget_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityBudget
        k j initialBound F n =
      Nat.ceil
          ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
            (growthRegularityTolerance
              k j initialBound F n) ^ 2) +
        1 :=
  rfl

theorem growthRegularityStepTolerance_pos
    (F : NatGrowthFunction) (M : ℕ) :
    0 < growthRegularityStepTolerance F M := by
  unfold growthRegularityStepTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)

theorem growthRegularityTolerance_pos
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      0 <
        growthRegularityTolerance
          k j initialBound F n := by
  intro n
  exact growthRegularityStepTolerance_pos F
    (growthRegularityComplexity
      k j initialBound F n)

/-- Every triangular ceiling budget is strictly long enough for the
corresponding preliminary regularity pass. -/
theorem growthRegularityBudget_spec
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
        (growthRegularityBudget
            k j initialBound F n : ℝ) *
          (growthRegularityTolerance
            k j initialBound F n) ^ 2 := by
  intro n
  exact orderedRemovalRegularityBudget_spec
    (growthRegularityTolerance_pos
      k j initialBound F n)

/-- The triangular sequence is exactly the standard fixed-upper recursive
complexity factor multiplied by the initial bound. -/
theorem growthRegularityComplexity_eq_factor_mul
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      growthRegularityComplexity
          k j initialBound F n =
        fixedUpperLayerComplexityFactor
            j (growthRegularityBudget
              k j initialBound F) n *
          initialBound := by
  intro n
  induction n with
  | zero =>
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      rw [growthRegularityComplexity_succ, ih]
      simp [fixedUpperLayerComplexityFactor,
        Nat.mul_assoc]

/-! ## A one-rank energy timescale -/

/-- Ceiling length making the rank-`j` aggregate energy increment at most
the prescribed positive target. -/
noncomputable def growthRegularityLength
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (OrderedFace k (j + 1)) : ℝ) / γ) +
    1

theorem growthRegularityLength_pos
    (k j : ℕ) (γ : ℝ) :
    0 < growthRegularityLength k j γ := by
  unfold growthRegularityLength
  omega

/-- The reciprocal one-rank energy budget is strictly smaller than `γ`. -/
theorem orderedFace_card_div_growthRegularityLength_lt
    {k j : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (Fintype.card
        (OrderedFace k (j + 1)) : ℝ) /
        (growthRegularityLength k j γ : ℝ) <
      γ := by
  let A : ℝ :=
    (Fintype.card
      (OrderedFace k (j + 1)) : ℝ)
  let L : ℕ :=
    growthRegularityLength k j γ
  have hLNat : 0 < L :=
    growthRegularityLength_pos k j γ
  have hLCast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLNat
  have hquot : A / γ < (L : ℝ) := by
    dsimp only [A, L]
    unfold growthRegularityLength
    calc
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) / γ ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hA : A < (L : ℝ) * γ :=
    (div_lt_iff₀ hγ).1 hquot
  apply (div_lt_iff₀ hLCast).2
  simpa [mul_comm] using hA

/-! ## Growth-function fixed-upper selection -/

/-- Selected adjacent fixed-upper tower stages with their bounds rewritten
in terms of the triangular growth-function complexity sequence. -/
structure GrowthFunctionFixedUpperCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j initialBound : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (F : NatGrowthFunction) (γ : ℝ) where
  index : ℕ
  index_lt :
    index < growthRegularityLength k j γ
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper
      (1 /
        (F (growthRegularityComplexity
          k j initialBound F index) : ℝ))
  gap_nonneg :
    0 ≤
      orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤ γ
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        growthRegularityComplexity
          k j initialBound F index
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        growthRegularityComplexity
          k j initialBound F (index + 1)

/-- One-rank preliminary growth-function selector obtained from the
fixed-upper coarse/fine tower. -/
theorem GrowthFunctionFixedUpperCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j initialBound : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (F : NatGrowthFunction) {γ : ℝ} (hγ : 0 < γ)
    (hinitial :
      ∀ e,
        FacePartition.complexity (initial e) ≤
          initialBound) :
    Nonempty
      (GrowthFunctionFixedUpperCertificate
        G k j initialBound initial upper F γ) := by
  let τ : ℕ → ℝ :=
    growthRegularityTolerance k j initialBound F
  let B : ℕ → ℕ :=
    growthRegularityBudget k j initialBound F
  let L : ℕ :=
    growthRegularityLength k j γ
  obtain ⟨R⟩ :=
    FixedUpperLayerCoarseFine.nonempty
      initial upper τ B
      (fun n =>
        (growthRegularityTolerance_pos
          k j initialBound F n).le)
      (growthRegularityBudget_spec
        k j initialBound F)
      (growthRegularityLength_pos k j γ)
  refine ⟨{
    index := R.index
    index_lt := R.index_lt
    coarse := R.coarse
    fine := R.fine
    refines := R.refines
    coarse_refines_initial :=
      R.coarse_refines_initial
    fine_regular := ?_
    gap_nonneg := R.gap_nonneg
    gap_le := ?_
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · simpa [τ, growthRegularityTolerance_eq] using
      R.fine_regular
  · exact R.gap_le.trans
      (orderedFace_card_div_growthRegularityLength_lt
        hγ).le
  · intro e
    calc
      FacePartition.complexity (R.coarse e) ≤
          fixedUpperLayerComplexityFactor
              j B R.index *
            FacePartition.complexity (initial e) :=
        R.coarse_complexity e
      _ ≤
          fixedUpperLayerComplexityFactor
              j B R.index *
            initialBound :=
        Nat.mul_le_mul_left _ (hinitial e)
      _ =
          growthRegularityComplexity
            k j initialBound F R.index := by
        rw [growthRegularityComplexity_eq_factor_mul]
  · intro e
    calc
      FacePartition.complexity (R.fine e) ≤
          fixedUpperLayerComplexityFactor
              j B (R.index + 1) *
            FacePartition.complexity (initial e) :=
        R.fine_complexity e
      _ ≤
          fixedUpperLayerComplexityFactor
              j B (R.index + 1) *
            initialBound :=
        Nat.mul_le_mul_left _ (hinitial e)
      _ =
          growthRegularityComplexity
            k j initialBound F (R.index + 1) := by
        rw [growthRegularityComplexity_eq_factor_mul]

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GrowthFunctionComplexRegularity.lean` -/

section
/-!
# All-rank growth-function ordered regularity

This file has two layers.

First, it records the finite descending hierarchy used in the
growth-function formulation:

```
M_d ≤ F(M_d) = M_{d-1} ≤ ⋯ ≤ M_0.
```

The canonical hierarchy is obtained by iterating `F` upward from `M_d`.

Second, it instantiates the existing top-down fixed-upper composition with
the triangular schedules from `GrowthFunctionRegularity`.  At rank `j`, the
selected fine lower layer is preliminarily regular against the final fine
upper layer with error exactly `1 / F(M_j)`, where `M_j` is the selected
triangular bound at that rank.  The adjacent energy gap is at most the
prescribed rankwise target `γ j`.  Complexity bookkeeping is stated for
every layer, including the unchanged top layer.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Finite descending growth hierarchies -/

/-- A finite hierarchy indexed from the largest scale `0` down to the
smallest scale `depth`.  Each upper scale is exactly the growth-function
image of the next lower scale. -/
structure DescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth : ℕ) where
  level : Fin (depth + 1) → ℕ
  step_eq :
    ∀ i : Fin depth,
      level i.castSucc = F (level i.succ)

namespace DescendingGrowthHierarchy

/-- The lower member of each adjacent pair is at most its growth-function
image. -/
theorem lower_le_growth
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) := by
  exact (Nat.le_succ _).trans
    (F.above_diagonal (H.level i.succ))

/-- The growth-function image of a lower scale is the preceding upper
scale. -/
theorem growth_eq_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    F (H.level i.succ) = H.level i.castSucc :=
  (H.step_eq i).symm

/-- The hierarchy is antitone in its finite index: later/deeper scales are
no larger than earlier scales. -/
theorem antitone
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth) :
    Antitone H.level := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  exact (H.lower_le_growth i).trans_eq
    (H.growth_eq_upper i)

end DescendingGrowthHierarchy

/-- The canonical descending hierarchy with prescribed bottom scale,
obtained by iterating `F` toward index zero. -/
def canonicalDescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    DescendingGrowthHierarchy F depth where
  level q :=
    (F.toFun ^[depth - q.1]) bottom
  step_eq := by
    intro i
    have hexponent :
        depth - i.castSucc.1 =
          (depth - i.succ.1) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hexponent]
    exact Function.iterate_succ_apply'
      F.toFun (depth - i.succ.1) bottom

@[simp]
theorem canonicalDescendingGrowthHierarchy_last
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level (Fin.last depth) =
        bottom := by
  simp [canonicalDescendingGrowthHierarchy]

@[simp]
theorem canonicalDescendingGrowthHierarchy_zero
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level 0 =
        (F.toFun ^[depth]) bottom := by
  simp [canonicalDescendingGrowthHierarchy]

/-! ## Rankwise triangular schedules -/

/-- Growth-function tolerance schedule at every non-top rank. -/
noncomputable def growthComplexRegularityTolerance
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℝ :=
  fun j =>
    growthRegularityTolerance
      k j.1 (initialBound j.castSucc) F

/-- Ceiling preliminary-regularity budget at every non-top rank. -/
noncomputable def growthComplexRegularityBudget
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℕ :=
  fun j =>
    growthRegularityBudget
      k j.1 (initialBound j.castSucc) F

/-- Rankwise energy-pigeonhole length associated to the target `γ j`. -/
noncomputable def growthComplexRegularityLength
    (k r : ℕ) (γ : Fin r → ℝ) :
    Fin r → ℕ :=
  fun j =>
    growthRegularityLength k j.1 (γ j)

/-- Selected coarse complexity bound at one non-top rank. -/
noncomputable def selectedGrowthCoarseComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j)

/-- Selected fine complexity bound at one non-top rank. -/
noncomputable def selectedGrowthFineComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j + 1)

/-- Bound for every selected coarse layer.  The top layer is unchanged;
every lower layer uses its own selected triangular stage. -/
noncomputable def selectedGrowthCoarseLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthCoarseComplexityBound
        k r initialBound F index j)

/-- Bound for every selected fine layer, with the same unchanged top layer
and the following triangular stage at every lower rank. -/
noncomputable def selectedGrowthFineLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthFineComplexityBound
        k r initialBound F index j)

theorem growthComplexRegularityTolerance_pos
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      0 <
        growthComplexRegularityTolerance
          k r initialBound F j n := by
  intro j n
  exact growthRegularityTolerance_pos
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityBudget_spec
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (growthComplexRegularityBudget
            k r initialBound F j n : ℝ) *
          (growthComplexRegularityTolerance
            k r initialBound F j n) ^ 2 := by
  intro j n
  exact growthRegularityBudget_spec
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityLength_pos
    (k r : ℕ) (γ : Fin r → ℝ) :
    ∀ j,
      0 <
        growthComplexRegularityLength k r γ j := by
  intro j
  exact growthRegularityLength_pos k j.1 (γ j)

/-! ## All-rank growth-function certificate -/

/-- Top-down all-rank fixed-upper regularity with growth-function errors and
rank-exact complexity bounds. -/
structure GrowthFunctionOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt :
    ∀ j : Fin r,
      index j <
        growthRegularityLength k j.1 (γ j)
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound F index j) : ℝ))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        γ j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (coarse.partition q e) ≤
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F index q
  fine_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (fine.partition q e) ≤
        selectedGrowthFineLayerComplexityBound
          k r initialBound F index q

/-! ## Existence by the top-down fixed-upper composition -/

/-- The one-rank growth-function selectors compose down all ranks.  This is
the existing source-faithful frozen-fine-upper recursion, instantiated with
the triangular schedules and with all bounds rewritten into their selected
growth-function form. -/
theorem GrowthFunctionOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ)
    (hγ : ∀ j, 0 < γ j)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
          (initial.partition q e) ≤ initialBound q) :
    Nonempty
      (GrowthFunctionOrderedComplexRegularityCertificate
        G k r initial initialBound F γ) := by
  let τ : (j : Fin r) → ℕ → ℝ :=
    growthComplexRegularityTolerance
      k r initialBound F
  let B : (j : Fin r) → ℕ → ℕ :=
    growthComplexRegularityBudget
      k r initialBound F
  let L : Fin r → ℕ :=
    growthComplexRegularityLength k r γ
  obtain ⟨R⟩ :=
    StrongOrderedComplexRegularityCertificate.nonempty
      initial τ B L
      (fun j n =>
        (growthComplexRegularityTolerance_pos
          k r initialBound F j n).le)
      (growthComplexRegularityBudget_spec
        k r initialBound F)
      (growthComplexRegularityLength_pos k r γ)
  refine ⟨{
    index := R.index
    coarse := R.coarse
    fine := R.fine
    refines := R.refines
    coarse_refines_initial :=
      R.coarse_refines_initial
    coarse_topLayer_eq := R.coarse_topLayer_eq
    fine_topLayer_eq := R.fine_topLayer_eq
    index_lt := ?_
    regular := ?_
    gap_nonneg := R.gap_nonneg
    gap_le := ?_
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · intro j
    simpa [L, growthComplexRegularityLength] using
      R.index_lt j
  · intro j
    have hregular := R.regular j
    simpa [τ, growthComplexRegularityTolerance,
      selectedOrderedComplexTolerance,
      selectedGrowthCoarseComplexityBound,
      growthRegularityTolerance_eq] using hregular
  · intro j
    exact (R.gap_le j).trans
      (by
        simpa [L, growthComplexRegularityLength] using
          (orderedFace_card_div_growthRegularityLength_lt
            (hγ j)).le)
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.coarse_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthCoarseLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.coarse_complexity i e
        calc
          FacePartition.complexity
              (R.coarse.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthCoarseLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthCoarseLayerComplexityBound,
              selectedGrowthCoarseComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.fine_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthFineLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.fine_complexity i e
        calc
          FacePartition.complexity
              (R.fine.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthFineLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthFineLayerComplexityBound,
              selectedGrowthFineComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/TowerDominatingGrowth.lean` -/

section
/-!
# Finite-stage tower-dominating growth functions

The triangular regularity schedule at rank `j` has one-step map

```
T_{F,j}(M) =
  (2^(j+1))^(orderedRemovalRegularityBudget k j (1 / F(M))) * M.
```

It is circular to ask, without further proof, for one growth function to
dominate the tower map formed from its own reciprocal tolerance.  The finite
regularity argument does not need such a fixed point.  Instead, this file
constructs a sequence

```
F₀ = F,   F_{s+1} = majorant of F_s and every T_{F_s,j}, j < r.
```

The construction first takes bounded maxima in the complexity variable and
then a finite maximum over the relevant ranks.  Consequently every `F_s` is
monotone and strictly above the diagonal, while `F_{s+1}` dominates every
one-step map computed with `F_s`.  This gives the exact stage-shifted
inequality

```
M_{F_s,j}(n+1) ≤ F_{s+1}(M_{F_s,j}(n)).
```

The last section applies this inequality to every selected rank of
`GrowthFunctionOrderedComplexRegularityCertificate` and embeds each selected
coarse/fine pair in an honest one-step `DescendingGrowthHierarchy`.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The one-step map and bounded envelopes -/

/-- One triangular complexity step at rank `j`, using the reciprocal
tolerance determined by `F` at the current complexity `M`. -/
noncomputable def growthRegularityOneStep
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  (2 ^ (j + 1)) ^
      growthRegularityStepBudget k j F M * M

@[simp]
theorem growthRegularityComplexity_succ_eq_oneStep
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      growthRegularityOneStep k j F
        (growthRegularityComplexity
          k j initialBound F n) :=
  rfl

/-- Maximum of the rank-`j` one-step map on the interval `0, ..., M`.
The recursive definition avoids needing any monotonicity theorem for the
ceiling-containing one-step map itself. -/
noncomputable def boundedGrowthRegularityOneStepMaximum
    (k j : ℕ) (F : NatGrowthFunction) : ℕ → ℕ
  | 0 => growthRegularityOneStep k j F 0
  | M + 1 =>
      max
        (boundedGrowthRegularityOneStepMaximum k j F M)
        (growthRegularityOneStep k j F (M + 1))

theorem boundedGrowthRegularityOneStepMaximum_monotone
    (k j : ℕ) (F : NatGrowthFunction) :
    Monotone
      (boundedGrowthRegularityOneStepMaximum k j F) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [boundedGrowthRegularityOneStepMaximum]
  exact le_max_left _ _

/-- Maximum of all bounded one-step envelopes at ranks
`0, ..., r - 1`. -/
noncomputable def finiteRankGrowthRegularityOneStepMaximum
    (k : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      max
        (finiteRankGrowthRegularityOneStepMaximum k F M r)
        (boundedGrowthRegularityOneStepMaximum k r F M)

theorem finiteRankGrowthRegularityOneStepMaximum_monotone
    (k r : ℕ) (F : NatGrowthFunction) :
    Monotone
      (fun M =>
        finiteRankGrowthRegularityOneStepMaximum
          k F M r) := by
  intro a b hab
  induction r with
  | zero =>
      simp [finiteRankGrowthRegularityOneStepMaximum]
  | succ r ih =>
      simp only [finiteRankGrowthRegularityOneStepMaximum]
      exact max_le_max ih
        (boundedGrowthRegularityOneStepMaximum_monotone
          k r F hab)

/-! ## One majorant stage -/

/-- The next tower-dominating stage.  At input `M` it simultaneously
dominates `M + 1`, the old value `F M`, and every rank-`j` one-step value
at every input at most `M`, for `j < r`. -/
noncomputable def towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) :
    NatGrowthFunction where
  toFun M :=
    max (M + 1)
      (max (F M)
        (finiteRankGrowthRegularityOneStepMaximum
          k F M r))
  monotone' := by
    intro a b hab
    exact max_le_max
      (Nat.add_le_add_right hab 1)
      (max_le_max
        (F.monotone hab)
        (finiteRankGrowthRegularityOneStepMaximum_monotone
          k r F hab))
  above_diagonal := by
    intro M
    exact le_max_left _ _

@[simp]
theorem towerDominatingGrowth_apply
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    towerDominatingGrowth k r F M =
      max (M + 1)
        (max (F M)
          (finiteRankGrowthRegularityOneStepMaximum
            k F M r)) :=
  rfl

/-! ## Iterated finite-stage closure -/

/-- Iteration of the finite tower-majorant operation, starting from the
requested growth function at stage zero. -/
noncomputable def towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ℕ → NatGrowthFunction
  | 0 => F
  | stage + 1 =>
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage)

@[simp]
theorem towerDominatingGrowthIteration_zero
    (k r : ℕ) (F : NatGrowthFunction) :
    towerDominatingGrowthIteration k r F 0 = F :=
  rfl

@[simp]
theorem towerDominatingGrowthIteration_succ
    (k r : ℕ) (F : NatGrowthFunction) (stage : ℕ) :
    towerDominatingGrowthIteration k r F (stage + 1) =
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage) :=
  rfl

/-! ## Finite maxima for simultaneous hierarchy bounds -/

/-- Maximum of a finite family of natural numbers.  The recursive
`Fin.lastCases` presentation is convenient for later all-layer bounds and
does not introduce a choice of an optimizing index. -/
def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))

/-- Every member of a finite family is bounded by `finiteMaximum`. -/
theorem le_finiteMaximum :
    ∀ {n : ℕ} (value : Fin n → ℕ) (i : Fin n),
      value i ≤ finiteMaximum n value
  | 0, _, i => Fin.elim0 i
  | n + 1, value, i => by
      cases i using Fin.lastCases with
      | last =>
          rw [finiteMaximum]
          exact le_max_right _ _
      | cast i =>
          rw [finiteMaximum]
          exact
            (le_finiteMaximum
              (fun q => value q.castSucc) i).trans
              (le_max_left _ _)

/-! ## Bridge to selected all-rank certificates -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- The exact one-link descending hierarchy associated to a selected rank.
Its lower level is the selected coarse bound and its upper level is the next
majorant stage applied to that bound. -/
noncomputable def selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) 1 :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level (Fin.last 1) =
      selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level 0 =
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  simp [selectedRankTowerHierarchy]

/-! ### One hierarchy containing all independently selected layers -/

/-- A single numerical bound containing all selected fine-layer bounds,
including the unchanged top layer. -/
noncomputable def selectedFineLayerMaximum
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) : ℕ :=
  finiteMaximum (r + 1)
    (selectedGrowthFineLayerComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index)

/-- A canonical depth-`r` descending hierarchy whose bottom already
dominates every independently selected fine-layer bound.  This is coarse,
but it is simultaneous and its adjacent growth equalities are exact. -/
noncomputable def selectedAllRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) r :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

@[simp]
theorem selectedAllRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    (selectedAllRankTowerHierarchy R).level (Fin.last r) =
      selectedFineLayerMaximum R := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

end GrowthFunctionOrderedComplexRegularityCertificate

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullCoarseTargetRegularity.lean` -/

section
/-!
# Source-style full coarse-target regularity

Tao's full regularity lemma does not choose the parameters at the different
ranks independently.  It first fixes a lower scale and then descends through
the ranks with a sufficiently fast auxiliary growth function.  The selected
scales have the shape

```
scaleFloor ≤ M_r,
F(M_{j + 1}) ≤ M_j,
gap_j ≤ 1 / F(M_{j + 1})^2,
regularity_j ≤ 1 / F(M_0).
```

This file isolates the exact adaptive certificate needed for that induction.
A `SourceFullCoarseTargetSchedule` is a finite top-down decision tree together
with numerical scale data on its genuine landings.  Its hypotheses are all
finite and ambient-independent.  The main compiler realizes the tree by
`AdaptiveCoarseTargetSchedule.exists_landing_certificate` and returns an
ordinary `CoarseTargetOrderedComplexRegularityCertificate` carrying the
source-style scale hierarchy.

The rank-zero plan and a genuine successor constructor are proved below.
The successor constructor makes the remaining mathematical obligation
explicit: after the current top index is selected, the lower plan must have
been built with scale floor `F(topScale)`, and the already fixed top
tolerance must be bounded by the common reciprocal attached to every landing
of that lower plan.  Constructing these lower plans uniformly is precisely
the auxiliary faster-growth induction in the source proof.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Source numerical targets -/

/-- The single preliminary-regularity tolerance used to compare every
selected rank with the largest selected scale `M₀`. -/
noncomputable def sourceFullCommonTolerance
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)

/-- The source energy-gap target at the lower boundary of a rank-`j + 1`
upper layer. -/
noncomputable def sourceFullRankGap
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2

theorem sourceFullCommonTolerance_pos
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) :
    0 < sourceFullCommonTolerance F scale := by
  unfold sourceFullCommonTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive (scale 0))

/-! ## Numerical bounds selected by an adaptive landing -/

/-- The coarse-layer complexity bound supplied directly by an adaptive
landing and an initial layerwise bound.  The unchanged top layer keeps its
initial bound; a non-top layer uses the selected fixed-upper tower factor. -/
def adaptiveSelectedCoarseLayerBound
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      fixedUpperLayerComplexityFactor
          j.1 (P.budget j) (P.index j) *
        initialBound j.castSucc)

/-! ## Adaptive source-full plans -/

/-- Ambient-independent source-full numerical data on an adaptive
coarse-target schedule.

The scales may depend on the genuine landing.  No condition is imposed on a
Cartesian product of unrelated stage indices.  `scaleFloor` is fixed before
the ambient finite type and is forced below the deepest scale on every
landing. -/
structure SourceFullCoarseTargetSchedule
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  scale : schedule.Landing → Fin (r + 1) → ℕ
  scaleFloor_le_deepest :
    ∀ P, scaleFloor ≤ scale P (Fin.last r)
  scale_hierarchy :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  selected_tolerance_le_common :
    ∀ P (j : Fin r),
      P.tolerance j (P.index j) ≤
        sourceFullCommonTolerance F (scale P)
  reciprocal_gap_le :
    ∀ P (j : Fin r),
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        sourceFullRankGap F (scale P) j
  selected_coarse_bound :
    ∀ P q,
      adaptiveSelectedCoarseLayerBound initialBound P q ≤
        scale P q

namespace SourceFullCoarseTargetSchedule

/-- The scale hierarchy is antitone: deeper scales are no larger than
shallower scales. -/
theorem scale_antitone
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (S.scale P j.succ)).trans
        (S.scale_hierarchy P j))

/-- The fixed scale floor lies below every selected scale, not only the
deepest one. -/
theorem scaleFloor_le
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing)
    (q : Fin (r + 1)) :
    scaleFloor ≤ S.scale P q := by
  exact (S.scaleFloor_le_deepest P).trans
    (S.scale_antitone P (Fin.le_last q))

/-! ## Realized source-full certificates -/

/-- A realized coarse-target certificate with Tao's full-regularity scale
hierarchy.  The ordinary certificate retains all refinement and exact
mixed-regularity data; this wrapper records the common discrepancy, the
rankwise source gaps, and the selected coarse complexity scales. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length
  scale : Fin (r + 1) → ℕ
  scaleFloor_le : ∀ q, scaleFloor ≤ scale q
  scale_hierarchy :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  selected_tolerance_nonneg :
    ∀ j : Fin r,
      0 ≤
        selectedOrderedComplexTolerance
          tolerance regularity.index j
  selected_tolerance_le_common :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance
          tolerance regularity.index j ≤
        sourceFullCommonTolerance F scale
  rank_gap_le :
    ∀ j : Fin r,
      regularity.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
        sourceFullRankGap F scale j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (regularity.coarse.partition q e) ≤
        scale q

/-- Every source-full adaptive plan realizes an ordinary coarse-target
certificate with the advertised source scale hierarchy. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty
      (Certificate k r initial initialBound F scaleFloor) := by
  obtain ⟨P, R, hindex⟩ :=
    S.schedule.exists_landing_certificate
      initial S.schedule_admissible
  refine ⟨{
    tolerance := P.tolerance
    budget := P.budget
    length := P.length
    regularity := R
    scale := S.scale P
    scaleFloor_le := S.scaleFloor_le P
    scale_hierarchy := S.scale_hierarchy P
    selected_tolerance_nonneg := ?_
    selected_tolerance_le_common := ?_
    rank_gap_le := ?_
    coarse_complexity := ?_ }⟩
  · intro j
    simp only [selectedOrderedComplexTolerance]
    rw [congrFun hindex j]
    exact
      P.tolerance_nonneg S.schedule_admissible
        j (P.index j)
  · intro j
    simpa [selectedOrderedComplexTolerance, hindex] using
      S.selected_tolerance_le_common P j
  · intro j
    have hgap := R.gap_le j
    have hreciprocal := S.reciprocal_gap_le P j
    change
      orderedLayerAtomEnergy
            (R.fine.partition j.castSucc)
            (R.coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (R.coarse.partition j.castSucc)
            (R.coarse.partition j.succ) ≤
        sourceFullRankGap F (S.scale P) j
    exact hgap.trans hreciprocal
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.coarse_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        calc
          FacePartition.complexity
                (initial.partition (Fin.last r) e) ≤
              initialBound (Fin.last r) :=
            hinitial (Fin.last r) e
          _ =
              adaptiveSelectedCoarseLayerBound
                initialBound P (Fin.last r) := by
            simp [adaptiveSelectedCoarseLayerBound]
          _ ≤ S.scale P (Fin.last r) :=
            S.selected_coarse_bound P (Fin.last r)
    | cast j =>
        intro e
        calc
          FacePartition.complexity
                (R.coarse.partition j.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                    j.1 (P.budget j) (P.index j) *
                FacePartition.complexity
                    (initial.partition j.castSucc e) := by
            rw [← congrFun hindex j]
            exact R.coarse_complexity j e
          _ ≤
              fixedUpperLayerComplexityFactor
                    j.1 (P.budget j) (P.index j) *
                initialBound j.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial j.castSucc e)
          _ =
              adaptiveSelectedCoarseLayerBound
                initialBound P j.castSucc := by
            simp [adaptiveSelectedCoarseLayerBound]
          _ ≤ S.scale P j.castSucc :=
            S.selected_coarse_bound P j.castSucc

/-! ## Rank-zero plan -/

/-- Rank zero has no regularity choices.  The only selected scale is the
maximum of the requested scale floor and the initial top-layer bound. -/
def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    SourceFullCoarseTargetSchedule
      k 0 initialBound F scaleFloor where
  schedule := .nil
  schedule_admissible := trivial
  scale := fun _ _ =>
    max scaleFloor (initialBound 0)
  scaleFloor_le_deepest := by
    intro P
    exact le_max_left _ _
  scale_hierarchy := by
    intro P j
    exact Fin.elim0 j
  selected_tolerance_le_common := by
    intro P j
    exact Fin.elim0 j
  reciprocal_gap_le := by
    intro P j
    exact Fin.elim0 j
  selected_coarse_bound := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max scaleFloor (initialBound 0)
    exact le_max_right _ _

/-! ## A genuine top-down successor constructor -/

/-- Prepend one deepest scale to the scale vector of a selected lower
landing.  Naming this dependent match separately gives downstream proofs a
stable simplification rule. -/
def nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (P :
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length next).Landing) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node chosen lower =>
      Fin.lastCases topScale
        (lowerScale chosen lower)

@[simp]
theorem nodeScale_node
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower) =
      Fin.lastCases topScale
        (lowerScale chosen lower) :=
  rfl

@[simp]
theorem nodeScale_node_last
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        (Fin.last (r + 1)) =
      topScale := by
  simp [nodeScale]

@[simp]
theorem nodeScale_node_castSucc
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (q : Fin (r + 1)) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        q.castSucc =
      lowerScale chosen lower q := by
  simp [nodeScale]

@[simp]
theorem sourceFullCommonTolerance_nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    sourceFullCommonTolerance F
        (nodeScale (tolerance := tolerance) (budget := budget)
          topScale lowerScale
          (AdaptiveCoarseTargetSchedule.Landing.node
            (tolerance := tolerance) (budget := budget)
            chosen lower)) =
      sourceFullCommonTolerance F
        (lowerScale chosen lower) := by
  unfold sourceFullCommonTolerance
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [nodeScale_node_castSucc]

/-- Initial layer bounds seen by the lower subtree after the current
top-rank stage `i` has been selected.

The new lower top layer is the selected coarse layer, hence its bound is the
selected fixed-upper tower factor times the old rank-`r` input bound.  All
strictly lower input layers are unchanged. -/
def lowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (budget : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (fixedUpperLayerComplexityFactor r budget i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- Extend source-full lower plans by one new top rank.

`topScale` is the new deepest scale.  Once the top energy selector chooses
`i`, the construction enters `next i`; that lower plan starts at scale floor
`F(topScale)`, which proves the new hierarchy link.  The only genuinely
source-specific compatibility hypothesis is `htopTolerance`: the top
tolerance fixed at stage `i` must already be no larger than the common
reciprocal attached to every landing of the selected lower plan. -/
def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (topScale : ℕ)
    (tolerance : ℕ → ℝ)
    (budget : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        SourceFullCoarseTargetSchedule
          k r (lowerInitialBound initialBound budget i)
            F (F topScale))
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    (hlength : 0 < length)
    (hscaleFloor : scaleFloor ≤ topScale)
    (hinitialTop :
      initialBound (Fin.last (r + 1)) ≤ topScale)
    (htopTolerance :
      ∀ (i : Fin length)
          (P : (next i).schedule.Landing),
        tolerance i.1 ≤
          sourceFullCommonTolerance F ((next i).scale P))
    (htopGap :
      (Fintype.card
          (OrderedFace k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F topScale : ℝ) ^ 2) :
    SourceFullCoarseTargetSchedule
      k (r + 1) initialBound F scaleFloor where
  schedule :=
    .node tolerance budget length
      (fun i => (next i).schedule)
  schedule_admissible := by
    exact ⟨htolerance, hbudget, hlength,
      fun i => (next i).schedule_admissible⟩
  scale :=
    nodeScale topScale
      (fun i => (next i).scale)
  scaleFloor_le_deepest := by
    intro P
    cases P with
    | node chosen lower =>
        simpa only [nodeScale_node_last] using
          hscaleFloor
  scale_hierarchy := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              nodeScale_node_last,
              nodeScale_node_castSucc] using
              (next chosen).scaleFloor_le_deepest lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              nodeScale_node_castSucc] using
              (next chosen).scale_hierarchy lower q
  selected_tolerance_le_common := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last,
              AdaptiveCoarseTargetSchedule.Landing.index_node_last,
              sourceFullCommonTolerance_nodeScale] using
              htopTolerance chosen lower
        | cast q =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc,
              AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc,
              sourceFullCommonTolerance_nodeScale] using
              (next chosen).selected_tolerance_le_common
                lower q
  reciprocal_gap_le := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_last,
              sourceFullRankGap, Fin.succ_last,
              nodeScale_node_last, Fin.val_last]
            convert htopGap using 1
        | cast q =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc,
              sourceFullRankGap, Fin.succ_castSucc,
              nodeScale_node_castSucc,
              Fin.val_castSucc]
            convert
              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1
  selected_coarse_bound := by
    intro P q
    cases P with
    | node chosen lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [adaptiveSelectedCoarseLayerBound,
              nodeScale_node_last] using
              hinitialTop
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower (Fin.last r)
            | cast j =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower j.castSucc

/-! ## The finite faster-growth induction -/

/-- A source-full plan together with a landing-independent upper bound for
its largest selected scale.  The bound is auxiliary: it is used only while
constructing the tolerance at the preceding rank and is erased from the
public existence theorem. -/
structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  plan :
    SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor
  ceiling : ℕ
  scale_zero_le :
    ∀ P : plan.schedule.Landing,
      plan.scale P 0 ≤ ceiling

namespace Bounded

/-- Transport only the initial-bound index of a bounded plan.  Its
numerical ceiling is definitionally unchanged. -/
def castInitialBound
    {k r : ℕ}
    {initialBound newInitialBound :
      Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : Bounded k r initialBound F scaleFloor)
    (h : initialBound = newInitialBound) :
    Bounded k r newInitialBound F scaleFloor where
  plan := h ▸ S.plan
  ceiling := S.ceiling
  scale_zero_le := by
    subst newInitialBound
    exact S.scale_zero_le

end Bounded

/-- The bounded form of the rank-zero plan. -/
def boundedZero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Bounded k 0 initialBound F scaleFloor where
  plan := zero k initialBound F scaleFloor
  ceiling := max scaleFloor (initialBound 0)
  scale_zero_le := by
    intro P
    change
      max scaleFloor (initialBound 0) ≤
        max scaleFloor (initialBound 0)
    exact le_rfl

/-- The lower input bound when the already accumulated top-tower
complexity factor is `factor`. -/
def factorLowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- The accumulated fixed-upper factor before stage `n`.

At stage `n`, the lower plan is first constructed from the factor already
accumulated at stages `< n`.  Its uniform ceiling then determines the
current reciprocal tolerance and hence the current budget.  That new budget
is used only in the factor for stage `n + 1`.  This one-stage shift is the
finite fast-growth device which removes the apparent circularity. -/
noncomputable def sourceFullStageFactor
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n
      let lower :=
        lowerBuilder
          (factorLowerInitialBound
            initialBound previous)
      let tolerance :=
        growthRegularityStepTolerance
          F lower.ceiling
      let budget :=
        orderedRemovalRegularityBudget
          k r tolerance
      (2 ^ (r + 1)) ^ budget * previous

/-- The lower input bound presented at top-tower stage `n`. -/
noncomputable def sourceFullStageBound
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  factorLowerInitialBound initialBound
    (sourceFullStageFactor
      initialBound F topScale lowerBuilder n)

/-- The bounded lower plan selected before the current top-stage tolerance
and budget are fixed. -/
noncomputable def sourceFullStagePlan
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Bounded k r
      (sourceFullStageBound
        initialBound F topScale lowerBuilder n)
      F (F topScale) :=
  lowerBuilder
    (sourceFullStageBound
      initialBound F topScale lowerBuilder n)

/-- The current top-stage tolerance, chosen from the already constructed
lower plan's uniform scale ceiling. -/
noncomputable def sourceFullStageTolerance
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℝ :=
  growthRegularityStepTolerance F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

/-- The ceiling budget corresponding to the current top-stage tolerance. -/
noncomputable def sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℕ :=
  orderedRemovalRegularityBudget k r
    (sourceFullStageTolerance
      initialBound F topScale lowerBuilder n)

@[simp]
theorem sourceFullStageFactor_zero
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    sourceFullStageFactor
      initialBound F topScale lowerBuilder 0 = 1 :=
  rfl

@[simp]
theorem sourceFullStageFactor_succ
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    sourceFullStageFactor
        initialBound F topScale lowerBuilder (n + 1) =
      (2 ^ (r + 1)) ^
          sourceFullStageBudget
            initialBound F topScale lowerBuilder n *
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n :=
  rfl

/-- The explicitly accumulated stage factor is exactly the standard
fixed-upper tower factor for the recursively chosen budget stream. -/
theorem fixedUpperLayerComplexityFactor_sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ∀ n,
      fixedUpperLayerComplexityFactor r
          (sourceFullStageBudget
            initialBound F topScale lowerBuilder) n =
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            fixedUpperLayerComplexityFactor r
              (sourceFullStageBudget
                initialBound F topScale lowerBuilder) n =
          (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            sourceFullStageFactor
              initialBound F topScale lowerBuilder n
      rw [ih]

/-- Rewriting the accumulated factor identifies the lower input bound used
by the generic successor constructor with the one used to build stage
`i`.  This is the local prefix-invariance statement: the factor at `i`
depends only on budgets at stages `< i`. -/
theorem lowerInitialBound_sourceFullStageBudget
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i =
      sourceFullStageBound
        initialBound F topScale lowerBuilder i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound,
        fixedUpperLayerComplexityFactor_sourceFullStageBudget]
  | cast q =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound]

/-- The stage-`i` lower plan, transported to the syntactic initial-bound
family expected by `node`. -/
noncomputable def sourceFullStageNext
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    Bounded k r
      (lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i)
      F (F topScale) :=
  (sourceFullStagePlan
      initialBound F topScale lowerBuilder i.1).castInitialBound
    (lowerInitialBound_sourceFullStageBudget
      initialBound F topScale lowerBuilder i).symm

@[simp]
theorem sourceFullStageNext_ceiling
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    (sourceFullStageNext
      initialBound F topScale lowerBuilder i).ceiling =
      (sourceFullStagePlan
        initialBound F topScale lowerBuilder i.1).ceiling :=
  rfl

theorem sourceFullStageTolerance_pos
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    0 <
      sourceFullStageTolerance
        initialBound F topScale lowerBuilder n := by
  exact growthRegularityStepTolerance_pos F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

/-- Strengthened source-full existence with a uniform upper bound on the
largest scale.  The proof is by rank induction.  Its successor step is a
finite recursion through the top energy horizon, so there is no fixed-point
assumption on `F`. -/
theorem bounded_nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (Bounded k r initialBound F scaleFloor) := by
  induction r generalizing scaleFloor with
  | zero =>
      exact
        ⟨boundedZero
          k initialBound F scaleFloor⟩
  | succ r ih =>
      let topScale : ℕ :=
        max scaleFloor
          (initialBound (Fin.last (r + 1)))
      let gap : ℝ :=
        1 / (F topScale : ℝ) ^ 2
      let length : ℕ :=
        growthRegularityLength k r gap
      let lowerBuilder :
          (bound : Fin (r + 1) → ℕ) →
            Bounded k r bound F (F topScale) :=
        fun bound =>
          Classical.choice
            (ih bound (F topScale))
      let tolerance : ℕ → ℝ :=
        sourceFullStageTolerance
          initialBound F topScale lowerBuilder
      let budget : ℕ → ℕ :=
        sourceFullStageBudget
          initialBound F topScale lowerBuilder
      let next :
          (i : Fin length) →
            Bounded k r
              (lowerInitialBound initialBound budget i)
              F (F topScale) :=
        fun i =>
          sourceFullStageNext
            initialBound F topScale lowerBuilder i
      have hgap_pos : 0 < gap := by
        dsimp only [gap]
        exact one_div_pos.mpr
          (sq_pos_of_pos
            (by exact_mod_cast F.positive topScale))
      let plan :
          SourceFullCoarseTargetSchedule
            k (r + 1) initialBound F scaleFloor :=
        node topScale tolerance budget length
          (fun i => (next i).plan)
          (by
            intro n
            exact
              (sourceFullStageTolerance_pos
                initialBound F topScale lowerBuilder n).le)
          (by
            intro n
            change
              (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) <
                (sourceFullStageBudget
                    initialBound F topScale lowerBuilder n : ℝ) *
                  (sourceFullStageTolerance
                    initialBound F topScale lowerBuilder n) ^ 2
            exact
              orderedRemovalRegularityBudget_spec
                (sourceFullStageTolerance_pos
                  initialBound F topScale lowerBuilder n))
          (by
            exact growthRegularityLength_pos k r gap)
          (by
            exact le_max_left _ _)
          (by
            exact le_max_right _ _)
          (by
            intro i P
            have hscale :
                (next i).plan.scale P 0 ≤
                  (sourceFullStagePlan
                    initialBound F topScale
                      lowerBuilder i.1).ceiling := by
              exact
                ((next i).scale_zero_le P).trans_eq
                  (sourceFullStageNext_ceiling
                    initialBound F topScale
                      lowerBuilder i)
            change
              growthRegularityStepTolerance F
                    (sourceFullStagePlan
                      initialBound F topScale
                        lowerBuilder i.1).ceiling ≤
                sourceFullCommonTolerance F
                  ((next i).plan.scale P)
            unfold growthRegularityStepTolerance
              sourceFullCommonTolerance
            apply one_div_le_one_div_of_le
            · exact_mod_cast
                F.positive ((next i).plan.scale P 0)
            · exact_mod_cast F.monotone hscale)
          (by
            have hgap :=
              orderedFace_card_div_growthRegularityLength_lt
                (k := k) (j := r) hgap_pos
            exact hgap.le)
      let ceiling : ℕ :=
        finiteMaximum length
          (fun i => (next i).ceiling)
      refine ⟨{
        plan := plan
        ceiling := ceiling
        scale_zero_le := ?_ }⟩
      intro P
      cases P with
      | node chosen lower =>
          dsimp only [plan, ceiling, node]
          change
            nodeScale topScale
                (fun i => (next i).plan.scale)
                (AdaptiveCoarseTargetSchedule.Landing.node
                  chosen lower) 0 ≤
              finiteMaximum length
                (fun i => (next i).ceiling)
          rw [show
            (0 : Fin (r + 2)) =
              (0 : Fin (r + 1)).castSucc by rfl]
          rw [nodeScale_node_castSucc]
          exact
            ((next chosen).scale_zero_le lower).trans
              (le_finiteMaximum
                (fun i => (next i).ceiling) chosen)

/-- Tao's finite faster-growth induction supplies a source-full plan for
every natural growth function, every initial layerwise bound, and every
requested deepest-scale floor. -/
theorem nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (SourceFullCoarseTargetSchedule
        k r initialBound F scaleFloor) := by
  obtain ⟨S⟩ :=
    bounded_nonempty
      k r initialBound F scaleFloor
  exact ⟨S.plan⟩

end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullRankwiseBundleCounting.lean` -/

section
/-!
# Rankwise source-full bundle counting

The source full-regularity hierarchy supplies a different density and
defect threshold at each positive rank, together with one common
fine-boundary regularity error.  This file assembles those data directly
with the generalized bundle-counting envelope.

Unlike `SourceFullBundleCounting`, no parameter is required to be constant
in the rank.  The final lower bound is quantitative: if the chosen envelope
has error below one half, then every source-full good closed configuration
has count at least one half of the product of its prescribed rankwise
density floors.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The finite horizon of the initial configuration bundle -/

/-- Every edge of the initial ordered-configuration bundle has cardinality
at most the complex rank. -/
theorem orderedConfigurationInitialBundle_order_le
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).order ≤ r := by
  unfold HypergraphBundle.order
  rw [orderedConfigurationInitialBundle_edges]
  apply Finset.sup_le
  intro e he
  exact (mem_orderedConfigurationBaseEdges_iff e).1 he

/-! ## The source-full regularity certificate as a counting input -/

/-- The selected mixed-regularity tolerances in a source-full certificate
are all bounded by its advertised common reciprocal tolerance. -/
theorem SourceFullCoarseTargetSchedule.Certificate.isFullyMixedPreliminaryOrderedRegular_common
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (R : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    IsFullyMixedPreliminaryOrderedRegular
      R.regularity.toCoarseFine
      (fun _ => sourceFullCommonTolerance F R.scale) := by
  intro j e a b
  exact
    (R.regularity.mixedRegular j e a b).trans
      (R.selected_tolerance_le_common j)

/-! ## Rankwise base-density and one-edge inputs -/

/-- Rankwise source-full goodness supplies the base-density lower bound on
every edge of the ordered-configuration base hypergraph.  Rank zero is the
neutral empty edge and is handled by `α 0 ≤ 1`. -/
theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hgood : A.IsSourceFullMixedGood P α β) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      α e.card ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using hαzero
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    have hrank :
        (positiveOrderedFaceOfEdge e hene her).rank = e.card := by
      rw [← positiveOrderedFaceEdge_card,
        positiveOrderedFaceEdge_ofEdge]
    rw [hrank] at hdensity
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

/-- Rankwise source-full localized defects and a common frozen-uniformity
bound give the one-edge input used by relative generalized counting. -/
theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A β τ hβ hτ
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A α β hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A τ hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

/-! ## Relative counting with an arbitrary rankwise envelope -/

/-- General source-full relative counting with rankwise density and defect
arrays and an arbitrary valid bundle-counting envelope. -/
theorem abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      E B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      α β μ τ E
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
        P A α β hαzero hgood)
      (hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
        P A α β τ hβ hτ hgood hregular)
      henvelope K inferInstance inferInstance B hclosed

/-! ## Initial configuration and a uniform quantitative lower bound -/

/-- The initial ordered-configuration count is bounded below by the
rankwise main-density product times one minus the selected envelope error. -/
theorem one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E) :
    (1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
      P A α β μ τ E hαzero hβ hτ hgood hregular henvelope
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

/-- Error below one half gives a quantitative source-full configuration
count: one half of the product of the prescribed rankwise density floors. -/
theorem half_rankwiseDensityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  have hlower :=
    one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A α β μ τ E (hαone 0) hβ hτ hgood hregular henvelope
  have hfloorProduct_nonneg :
      0 ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
    exact Finset.prod_nonneg fun e _ => (hα e.rank).le
  have hdensityProduct :
      (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        ∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_le_prod
    · intro e _he
      exact (hα e.rank).le
    · intro e _he
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1
  have hone :
      (1 / 2 : ℝ) ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  have hone_nonneg :
      0 ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  calc
    (1 / 2 : ℝ) *
          (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r, α e.rank) :=
      mul_le_mul_of_nonneg_right hone hfloorProduct_nonneg
    _ ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) := by
      exact mul_le_mul_of_nonneg_left hdensityProduct hone_nonneg
    _ ≤ fullConfigurationCount A :=
      hlower

/-- It is enough to control the envelope at the ambient complex rank:
the initial configuration bundle has order at most that rank, and every
valid envelope is monotone in its order argument. -/
theorem half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E r (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  apply
    half_rankwiseDensityProduct_le_fullConfigurationCount
      P A α β μ τ E hα hαone hβ hτ hgood hregular henvelope
  exact
    (henvelope.error_mono_order
      (orderedConfigurationInitialBundle_order_le k r)).trans_lt
      herror

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullGoodAtoms.lean` -/

section
/-!
# Source-full good atoms and sharp bad-cell cleaning

The source hypergraph regularity argument tests the square of the usual
fine-immediate-boundary minus coarse-immediate-boundary defect after
conditioning on the join of every proper lower face.  This file implements
that test without changing the defect whose global square mass is paid for
by the ordinary adjacent-boundary atom-energy increment.

For a fixed upper atom, the bad base is the union of

* the usual low coarse-density support, observed on the immediate coarse
  boundary; and
* the support on which the full-lower conditional average of the same
  immediate-boundary defect square exceeds the chosen threshold.

Markov's inequality charges the second support directly to the immediate
atom-energy increment.  Summing over the disjoint upper atoms therefore
gives

```
upperComplexity * α + immediateAtomEnergyGap / β,
```

with no factor involving the complexity of the full-lower partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Full-lower large-defect supports -/

/-- The immediate-boundary square defect of one selected upper atom.

The partition used to *average* this function below is the source-full lower
boundary, but the function itself remains the ordinary adjacent-boundary
fine-minus-coarse defect.  This is what permits the cleaning loss to be
charged to the existing atom-energy increment. -/
noncomputable def sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  atomBoundaryDefectSq
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face)
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    upper a x

theorem sourceFullAtomDefectSq_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ P.sourceFullAtomDefectSq e upper a x := by
  exact atomBoundaryDefectSq_nonneg _ _ upper a x

/-- Full-lower coarse atoms on which the conditional square average of the
immediate-boundary defect exceeds `β`. -/
noncomputable def sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  largeAverageBaseSupport
    (orderedFullLowerBoundaryPartition P.coarse e)
    (P.sourceFullAtomDefectSq e upper a) β

@[simp]
theorem mem_sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullLargeDefectBaseSupport e upper a β ↔
      β <
        conditionalMean
          (orderedFullLowerBoundaryPartition P.coarse e)
          (P.sourceFullAtomDefectSq e upper a) x := by
  exact
    mem_largeAverageBaseSupport
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a) β x

/-- Markov accounting on the source-full boundary.  The right hand side is
the global mass of the *immediate* defect square, so no full-boundary
complexity enters. -/
theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) := by
  exact
    mul_mean_indicator_largeAverageBaseSupport_le
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a)
      (P.sourceFullAtomDefectSq_nonneg e upper a)
      hβ

/-- Divided form of the source-full Markov estimate. -/
theorem mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ.le

/-! ## Low-density union and own-atom accounting -/

/-- The adjacent-boundary atom-energy gap is exactly the sum of the
source-full defect-square masses.  The full-lower partition is used only
to localize those masses and therefore does not occur in this identity. -/
theorem orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G)) :
    orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper =
      ∑ a : upper.parts,
        mean (P.sourceFullAtomDefectSq e upper a) := by
  rw [orderedAtomEnergy_sub_eq_sum_mean_sq
    (fine := positiveFaceLowerLayer P.fine e)
    (coarse := positiveFaceLowerLayer P.coarse e)
    (fun f => P.refines e.lowerRank.castSucc f)
    e.face upper]
  rfl

/-- The source-full bad base for one upper atom.  Its density component is
still measured on the immediate coarse boundary, exactly as in the mixed
counting decomposition. -/
noncomputable def sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  smallAverageBaseSupport
      (orderedBoundaryPartition
        (positiveFaceLowerLayer P.coarse e) e.face)
      (partitionAtomIndicator upper a) α ∪
    P.sourceFullLargeDefectBaseSupport e upper a β

@[simp]
theorem mem_sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullAtomBadBaseSupport e upper a α β ↔
      conditionalMean
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) x < α ∨
        β <
          conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x := by
  rw [sourceFullAtomBadBaseSupport, Finset.mem_union,
    mem_smallAverageBaseSupport,
    P.mem_sourceFullLargeDefectBaseSupport]

/-- The local bad part of one upper atom costs one density threshold plus
the mean square of that atom's immediate defect divided by `β`. -/
theorem mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
      α + mean (P.sourceFullAtomDefectSq e upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩
            smallAverageBaseSupport
              (orderedBoundaryPartition
                (positiveFaceLowerLayer P.coarse e) e.face)
              (partitionAtomIndicator upper a) α)) +
          mean (finsetIndicator
            (P.sourceFullLargeDefectBaseSupport
              e upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α)
          (P.sourceFullLargeDefectBaseSupport e upper a β)
    _ ≤
        α + mean (P.sourceFullAtomDefectSq e upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          a.1 hα)
        (P.mean_indicator_sourceFullLargeDefectBaseSupport_le
          e upper a hβ)

/-- Union over all upper atoms of the part of that atom lying above its own
source-full bad base. -/
noncomputable def sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.sourceFullAtomBadBaseSupport e upper a α β

@[simp]
theorem mem_sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullOwnAtomBadBaseSupport e upper α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [sourceFullOwnAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ P.sourceFullAtomBadBaseSupport
          e upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical : partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [sourceFullOwnAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

/-- **Sharp source-full own-atom cleaning estimate.**  The source-full
partition appears only in Markov localization.  The quantitative loss is
the upper complexity times `α` plus the existing immediate-boundary
atom-energy gap divided by `β`. -/
theorem mean_indicator_sourceFullOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy
            (positiveFaceLowerLayer P.fine e) e.face upper -
          orderedAtomEnergy
            (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
  calc
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α + mean
            (P.sourceFullAtomDefectSq e upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        P.mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
          e upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (orderedAtomEnergy
              (positiveFaceLowerLayer P.fine e) e.face upper -
            orderedAtomEnergy
              (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Fintype.card_coe]
      rw [← P.orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
        e upper]
      rfl

/-! ## The coarse upper partition selected by configurations -/

/-- Source-full own-atom bad support for the coarse upper partition used by
mixed configuration counting. -/
noncomputable def sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  P.sourceFullOwnAtomBadBaseSupport e
    (P.coarse.partition e.lowerRank.succ e.face) α β

@[simp]
theorem mem_sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullCoarseOwnAtomBadBaseSupport e α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e
        (P.coarse.partition e.lowerRank.succ e.face)
        (partitionAtomAt
          (P.coarse.partition e.lowerRank.succ e.face) x)
        α β := by
  exact
    P.mem_sourceFullOwnAtomBadBaseSupport e
      (P.coarse.partition e.lowerRank.succ e.face) α β x

/-- Specialized sharp cleaning estimate for the coarse upper atoms used by
the source mixed counting argument. -/
theorem mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullCoarseOwnAtomBadBaseSupport e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition e.lowerRank.succ e.face) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap
          e.lowerRank e.face / β := by
  unfold sourceFullCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  exact
    P.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
      e (P.coarse.partition e.lowerRank.succ e.face) hα hβ

end OrderedCoarseFineComplex

/-! ## Avoidance implies source-full mixed goodness -/

/-- On the selected full-lower atom, the mixed defect is pointwise equal to
the ordinary immediate-boundary atom defect. -/
theorem sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G)
    (hy :
      y ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness)) :
    sourceFullMixedDefect P A e y =
      orderedAtomBoundaryDefect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face) y := by
  have himmediate :
      y ∈
        (orderedBoundaryPartition
          (positiveFaceLowerLayer P.coarse e) e.face).part
          (orderedFaceTuple e.face A.witness) :=
    FacePartition.part_subset_of_le
      (orderedFullLowerBoundaryPartition_le_immediate
        P.coarse e)
      (orderedFaceTuple e.face A.witness) hy
  have hindicator :
      mixedConfigurationBoundaryIndicator P A e y = 1 := by
    unfold mixedConfigurationBoundaryIndicator
    exact partitionAtomIndicator_of_mem _ _ himmediate
  have h :=
    mixedConfigurationDefect_mul_boundaryIndicator P A e y
  rw [hindicator, mul_one, mul_one] at h
  simpa [sourceFullMixedDefect] using h

/-- Consequently, conditioning the mixed defect square on the selected
full-lower atom is the same as conditioning the immediate atom defect
square there. -/
theorem conditionalMean_sourceFullMixedDefect_sq_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) =
      conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (P.sourceFullAtomDefectSq e
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face))
        (orderedFaceTuple e.face A.witness) := by
  unfold conditionalMean
  apply Finset.expect_congr rfl
  intro y hy
  rw [sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    P A e y hy]
  rfl

namespace ClosedOrderedAtomConfiguration

/-- A coarse closed configuration avoids the source-full cleaning support
when its selected tuple misses its own bad base at every positive face. -/
def AvoidsSourceFullBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    orderedFaceTuple e.face A.witness ∉
      P.sourceFullCoarseOwnAtomBadBaseSupport e
        (α e.rank) (β e.rank)

/-- Avoidance of the own coarse upper atom's source-full bad base implies
source mixed goodness at one positive face. -/
theorem sourceFullMixedGoodAtFace_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e.face A.witness ∉
        P.sourceFullCoarseOwnAtomBadBaseSupport e α β) :
    SourceFullMixedGoodAtFace P A e α β := by
  let upper :=
    P.coarse.partition e.lowerRank.succ e.face
  let a : upper.parts :=
    A.atom e.lowerRank.succ e.face
  let x : Fin (e.lowerRank.1 + 1) → G :=
    orderedFaceTuple e.face A.witness
  have hcanonical :
      partitionAtomAt upper x = a := by
    exact (A.atom_eq_partitionAtomAt
      e.lowerRank.succ e.face).symm
  have hlocal :
      x ∉ P.sourceFullAtomBadBaseSupport
        e upper a α β := by
    intro hbad
    apply havoid
    apply
      (P.mem_sourceFullCoarseOwnAtomBadBaseSupport
        e α β x).2
    change
      x ∈ P.sourceFullAtomBadBaseSupport
        e upper (partitionAtomAt upper x) α β
    rw [hcanonical]
    exact hbad
  have hlow :
      x ∉
        smallAverageBaseSupport
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) α := by
    intro h
    exact hlocal (Finset.mem_union_left _ h)
  have hlarge :
      x ∉
        P.sourceFullLargeDefectBaseSupport
          e upper a β := by
    intro h
    exact hlocal (Finset.mem_union_right _ h)
  constructor
  · have hdensity :
        α ≤
          conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) x :=
      not_lt.mp fun h =>
        hlow
          ((mem_smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α x).2 h)
    simpa [sourceFullMixedCoarseDensity,
      mixedConfigurationCoarseDensity, upper, a, x,
      orderedBoundaryStructured] using hdensity
  · rw [conditionalMean_sourceFullMixedDefect_sq_eq P A e]
    have hdefect :
        conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x ≤
          β :=
      not_lt.mp fun h =>
        hlarge
          ((P.mem_sourceFullLargeDefectBaseSupport
            e upper a β x).2 h)
    simpa [upper, a, x] using hdefect

/-- Simultaneous avoidance of the source-full bad base at every positive
face implies the all-face source-goodness predicate used by counting. -/
theorem isSourceFullMixedGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid : A.AvoidsSourceFullBadBases P α β) :
    A.IsSourceFullMixedGood P α β := by
  intro e
  exact
    A.sourceFullMixedGoodAtFace_of_not_mem_badBase
      P e (α e.rank) (β e.rank) (havoid e)

end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPatternPartition.lean` -/

section
/-!
# Ordered pattern edge partitions

The top layer used in ordered removal must remember the original
hypergraph.  For every top face we therefore generate a two-cell partition
from its edge set.  Any later refinement of that layer has atoms which are
monochromatic for the original edge predicate.

The lower layers of `orderedPatternInitialComplex` are indiscrete.  This is
the canonical starting complex for the all-rank regularity argument.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Edge supports and their two-cell partitions -/

/-- The finite support of one ordered edge predicate. -/
noncomputable def OrderedPattern.edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) : Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter (H.edge e)

@[simp]
theorem OrderedPattern.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [OrderedPattern.edgeFinset]

/-- The two-cell top partition generated by the edge set on each ordered
top face. -/
noncomputable def orderedPatternTopPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedFacePartitionSystem G k r := by
  classical
  exact fun e =>
    FacePartition.generatedBy ({H.edgeFinset e} :
      Finset (Finset (Fin r → G)))

/-- Every original edge/nonedge top partition has at most two atoms. -/
theorem complexity_orderedPatternTopPartition_le_two
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) :
    FacePartition.complexity
        (orderedPatternTopPartition H e) ≤ 2 := by
  simpa [orderedPatternTopPartition] using
    FacePartition.complexity_generatedBy_le
      ({H.edgeFinset e} :
        Finset (Finset (Fin r → G)))

/-- Membership in an atom of a refinement of a two-cell partition
preserves membership in its generating set. -/
theorem mem_of_mem_part_of_le_generatedBy_singleton
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : FacePartition Ω} {S : Finset Ω}
    (hP : P ≤ FacePartition.generatedBy
      ({S} : Finset (Finset Ω)))
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ P.part x) :
    y ∈ S := by
  have hyGenerated :
      y ∈
        (FacePartition.generatedBy
          ({S} : Finset (Finset Ω))).part x :=
    FacePartition.part_subset_of_le hP x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({S} : Finset (Finset Ω)) x y).1 hyGenerated
  exact (hsignature S (by simp)).1 hx

/-- A refinement of the pattern top partition cannot move an edge tuple
into a nonedge within the same atom. -/
theorem orderedPattern_edge_of_mem_refinedTopAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {P : OrderedFacePartitionSystem G k r}
    (hP : OrderedFacePartitionRefines P
      (orderedPatternTopPartition H))
    (e : OrderedFace k r) {x y : Fin r → G}
    (hx : H.edge e x) (hy : y ∈ (P e).part x) :
    H.edge e y := by
  rw [← H.mem_edgeFinset e y]
  exact
    mem_of_mem_part_of_le_generatedBy_singleton
      (hP e)
      ((H.mem_edgeFinset e x).2 hx) hy

/-! ## Canonical initial complex -/

/-- The all-indiscrete ordered partition complex. -/
def indiscreteOrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) : OrderedPartitionComplex G k r where
  partition _ _ := FacePartition.indiscrete

/-- The canonical regularity input: indiscrete below the top, with the top
layer generated by the original ordered edge predicates. -/
noncomputable def orderedPatternInitialComplex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedPartitionComplex G k r :=
  (indiscreteOrderedPartitionComplex G k r).withTopLayer
    (orderedPatternTopPartition H)

@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _

/-- Refining the initial complex in particular refines the original
edge/nonedge partition at the top rank. -/
theorem orderedPatternTopPartition_refines_of_complex_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : C.Refines (orderedPatternInitialComplex H)) :
    OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H) := by
  intro e
  change
    C.partition (Fin.last r) e ≤
      orderedPatternTopPartition H e
  rw [← orderedPatternInitialComplex_topLayer H]
  exact hC (Fin.last r) e

/-! ## Closed configurations contained in the original pattern -/

/-- If the witness of a closed configuration is an occurrence, then every
tuple in each of its selected top atoms remains an edge. -/
theorem ClosedOrderedAtomConfiguration.edge_of_mem_topAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (e : OrderedFace k r) (y : Fin r → G)
    (hy : y ∈ (A.atom (Fin.last r) e).1) :
    H.edge e y := by
  apply
    orderedPattern_edge_of_mem_refinedTopAtom
      H hC e (hA e)
  have hw :
      orderedFaceTuple e A.witness ∈
        (A.atom (Fin.last r) e).1 :=
    A.mem_atom (Fin.last r) e
  have hpart :
      (C.topLayer e).part
          (orderedFaceTuple e A.witness) =
        (A.atom (Fin.last r) e).1 := by
    exact
      (C.topLayer e).part_eq_of_mem
        (A.atom (Fin.last r) e).2 hw
  rwa [hpart]

/-- Every full tuple realizing all selected top atoms of an occurring
closed configuration is itself an occurrence of the original pattern. -/
theorem ClosedOrderedAtomConfiguration.isOccurrence_of_mem_topAtoms
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G)
    (hx :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∈
          (A.atom (Fin.last r) e).1) :
    H.IsOccurrence x := by
  intro e
  exact A.edge_of_mem_topAtom H hC hA e
    (orderedFaceTuple e x) (hx e)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalTheorem.lean` -/

section
/-!
# The ordered removal cover contradiction

This file joins the three semantic parts of ordered hypergraph removal.

* The top partition remembers the original edge predicates.
* A tuple surviving every bad-base deletion determines a good closed fine
  atom configuration.
* The configuration counting lemma gives every good configuration a
  uniform lower count.

Every tuple counted by the selected configuration remains an occurrence of
the original pattern, because its selected top atoms are edge-monochromatic.
Thus an occurrence surviving all deletions would force the original pattern
count above the assumed small-count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The selected configuration lies inside the original pattern -/

/-- Regard a top face of successor rank as a positive ordered face. -/
def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e

@[simp]
theorem topPositiveOrderedFace_rank
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).rank = n + 1 := by
  rfl

@[simp]
theorem topPositiveOrderedFace_lowerRank_succ
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).lowerRank.succ =
      Fin.last (n + 1) := by
  apply Fin.ext
  rfl

/-- If a full tuple is not an occurrence, then the full selected
configuration weight of an occurring closed configuration vanishes on that
tuple. -/
theorem partialConfigurationWeight_univ_eq_zero_of_not_occurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    partialConfigurationWeight A Finset.univ x = 0 := by
  have hmissing :
      ∃ e : OrderedFace k (n + 1),
        orderedFaceTuple e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.isOccurrence_of_mem_topAtoms
        H hC hA x h)
  obtain ⟨e, he⟩ := hmissing
  unfold partialConfigurationWeight
  apply Finset.prod_eq_zero
    (Finset.mem_univ (topPositiveOrderedFace e))
  unfold configurationFaceWeight
  change
    partitionAtomIndicator
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (orderedFaceTuple e x) =
      0
  exact
    partitionAtomIndicator_of_not_mem
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he

/-- Pointwise, the indicator product for an occurring closed configuration
is bounded by the original zero-one pattern weight. -/
theorem partialConfigurationWeight_univ_le_patternWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G) :
    partialConfigurationWeight A Finset.univ x ≤
      H.toWeighted.patternWeight x := by
  by_cases hx : H.IsOccurrence x
  · rw [H.toWeighted_patternWeight_of_occurrence hx]
    exact partialConfigurationWeight_le_one
      A Finset.univ x
  · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
      partialConfigurationWeight_univ_eq_zero_of_not_occurrence
        H hC A hA hx]

/-- The normalized count of an occurring closed configuration is bounded
by the normalized count of the original pattern. -/
theorem fullConfigurationCount_le_patternCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness) :
    fullConfigurationCount A ≤
      H.toWeighted.patternCount := by
  unfold fullConfigurationCount partialConfigurationCount
    WeightedOrderedPattern.patternCount
  exact mean_mono
    (partialConfigurationWeight_univ_le_patternWeight
      H hC A hA)

/-! ## The cover contradiction -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullOrderedRemoval.lean` -/

section
/-!
# Source-full bad-base cleaning and the ordered removal contradiction

The source-full counting argument conditions the usual adjacent-boundary
square defect on the join of every proper lower face.  `SourceFullGoodAtoms`
shows that cleaning the resulting bad bases nevertheless costs only

```
upper complexity * density threshold + adjacent atom-energy gap / defect threshold.
```

This file pulls those bad bases back to top faces, records the corresponding
normalized deletion bounds, and proves the semantic cover contradiction.  A
tuple surviving every top-face deletion induces its canonical coarse closed
configuration; factorization of each positive face through a top face shows
that this configuration avoids every source-full bad base and is therefore
source-full mixed-good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Pulling source-full bad bases back to top faces -/

/-- Delete a top tuple when one of its positive-rank subfaces lies in the
source-full bad base attached to its own coarse upper atom. -/
noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

/-- Source-full bad-base deletions, one finite set for every top ordered
face. -/
noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β

/-- Direct normalized union-bound cost of one source-full top deletion. -/
theorem mean_indicator_sourceFullTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        P.mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (hα q.1.1) (hβ q.1.1)

/-- Per-top-face deletion density in terms of the coarse upper complexity and
the coarse-upper adjacent atom-energy gap. -/
theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (P.sourceFullBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.sourceFullTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      sourceFullBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    P.mean_indicator_sourceFullTopBadBaseDeletion_le
      e α β hα hβ

end OrderedCoarseFineComplex

/-! ## Surviving tuples are source-full mixed-good -/

namespace ClosedOrderedAtomConfiguration

/-- If a full tuple avoids every source-full top deletion, its canonical
coarse closed atom configuration is source-full mixed-good at every positive
face. -/
theorem isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.sourceFullTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsSourceFullMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isSourceFullMixedGood_of_avoids_badBases
      P α β
  intro f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr f.lowerRank.2) hrk f.face
  apply havoid e
  rw [OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.lowerRank, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  change
    orderedFaceTuple (d.trans e) x ∈
      P.sourceFullCoarseOwnAtomBadBaseSupport
        ({ lowerRank := f.lowerRank
           face := d.trans e } : PositiveOrderedFace k r)
        (α (f.lowerRank.1 + 1))
        (β (f.lowerRank.1 + 1))
  rw [hde]
  exact hbad

end ClosedOrderedAtomConfiguration

/-! ## Abstract source-good cover contradiction -/

/-- A uniform lower count for every source-full mixed-good coarse
configuration forces the source-full bad-base family to cover every
occurrence of the original pattern. -/
theorem sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.sourceFullBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsSourceFullMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalParameters.lean` -/

section
/-!
# Ambient-independent source-full bundle-removal parameters

This file packages two pieces of the final numerical diagonal.

* `sourceBundleDensity δ m = δ / (m + 1)` pays for a coarse upper
  partition of complexity at most `m` without choosing a global complexity
  window.
* `sourceBundleDefectScale δ η N m = η * sourceBundleDensity δ m ^ N`
  is small relative to every density power up to the fixed finite bundle
  horizon `N`.

The polynomial growth function

```
F(m) = Q * (m + 1)^N + (m + 1)
```

then makes both the common preliminary-regularity tolerance and the
rankwise source energy gaps small at the *same selected scale*.  This is the
pointwise choice which removes the apparent global complexity fixed point.

The last section retains the uniform ceiling supplied by
`SourceFullCoarseTargetSchedule.Bounded` when realizing the numerical plan
over an ambient finite type.  The older `certificate_nonempty` theorem
forgets the landing and hence cannot expose this ceiling to the uniform
count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Scale-dependent density and defect parameters -/

/-- Density threshold attached to a coarse complexity scale. -/
noncomputable def sourceBundleDensity (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)

/-- Square-root defect threshold attached to the same scale. -/
noncomputable def sourceBundleDefectScale
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * sourceBundleDensity δ m ^ N

theorem sourceBundleDensity_pos
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    0 < sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    0 ≤ sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_le_one
    {δ : ℝ} (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) (m : ℕ) :
    sourceBundleDensity δ m ≤ 1 := by
  unfold sourceBundleDensity
  have hden : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self hδ0 hden).trans hδ

theorem sourceBundleDensity_antitone
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Antitone (sourceBundleDensity δ) := by
  intro a b hab
  unfold sourceBundleDensity
  apply div_le_div_of_nonneg_left hδ
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1

/-- The low-density cleaning term at scale `m` costs at most `δ`. -/
theorem mul_sourceBundleDensity_le
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    (m : ℝ) * sourceBundleDensity δ m ≤ δ := by
  unfold sourceBundleDensity
  have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    (m : ℝ) * (δ / (m + 1 : ℕ)) =
        δ * ((m : ℝ) / (m + 1 : ℕ)) := by ring
    _ ≤ δ * 1 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (div_le_one hden).2 (by norm_num)
    _ = δ := mul_one δ

theorem sourceBundleDefectScale_pos
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_pos hη (pow_pos (sourceBundleDensity_pos hδ m) N)

theorem sourceBundleDefectScale_nonneg
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (N m : ℕ) :
    0 ≤ sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_nonneg hη
    (pow_nonneg (sourceBundleDensity_nonneg hδ m) N)

/-! ## Rankwise schedules attached to a selected scale hierarchy -/

/-- Extend a finite selected scale hierarchy to all natural ranks by
clamping at its deepest rank.  Bundle-counting envelopes are indexed by
all naturals even though source-full configurations only query ranks at
most `r`. -/
def sourceBundleSelectedScale
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩

@[simp]
theorem sourceBundleSelectedScale_zero
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    sourceBundleSelectedScale scale 0 = scale 0 := by
  simp [sourceBundleSelectedScale]

theorem sourceBundleSelectedScale_of_le
    {r d : ℕ} (scale : Fin (r + 1) → ℕ) (hd : d ≤ r) :
    sourceBundleSelectedScale scale d =
      scale ⟨d, Nat.lt_succ_iff.mpr hd⟩ := by
  simp [sourceBundleSelectedScale, Nat.min_eq_left hd]

/-- The density schedule obtained by evaluating `sourceBundleDensity` at
the selected scale of each rank. -/
noncomputable def sourceBundleRankwiseDensity
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDensity δ (sourceBundleSelectedScale scale d)

/-- The squared localized-defect schedule paired with the selected
rankwise density schedule. -/
noncomputable def sourceBundleRankwiseDefect
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDefectScale δ κ N
      (sourceBundleSelectedScale scale d) ^ 2

theorem sourceBundleRankwiseDensity_pos
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 < sourceBundleRankwiseDensity δ scale d :=
  sourceBundleDensity_pos hδ _

theorem sourceBundleRankwiseDensity_le_one
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    sourceBundleRankwiseDensity δ scale d ≤ 1 :=
  sourceBundleDensity_le_one hδ_one hδ _

theorem sourceBundleRankwiseDefect_nonneg
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 ≤ sourceBundleRankwiseDefect δ κ N scale d :=
  sq_nonneg _

/-- Antitonicity of the selected scales makes rank zero the least density
in the extended rankwise density schedule. -/
theorem sourceBundleRankwiseDensity_zero_le
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {scale : Fin (r + 1) → ℕ} (hscale : Antitone scale)
    (d : ℕ) :
    sourceBundleRankwiseDensity δ scale 0 ≤
      sourceBundleRankwiseDensity δ scale d := by
  apply sourceBundleDensity_antitone hδ
  exact hscale (Fin.zero_le _)

/-- If the zeroth entry is a lower bound for a schedule, it is also a
lower bound for every finite prefix minimum. -/
theorem le_bundleRankwiseDensityFloor_of_zero_le
    {α : ℕ → ℝ} (hα : ∀ d, α 0 ≤ α d) :
    ∀ d, α 0 ≤ bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      exact le_min ih (hα (d + 1))

/-! ## Polynomial pointwise growth -/

/-- A monotone growth function which dominates `Q * (m + 1)^N` at every
scale. -/
def sourceBundleRemovalGrowth (Q N : ℕ) : NatGrowthFunction where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  above_diagonal := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))

@[simp]
theorem sourceBundleRemovalGrowth_apply
    (Q N m : ℕ) :
    sourceBundleRemovalGrowth Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl

theorem sourceBundleRemovalGrowth_polynomial_le
    (Q N m : ℕ) :
    Q * (m + 1) ^ N ≤ sourceBundleRemovalGrowth Q N m := by
  rw [sourceBundleRemovalGrowth_apply]
  exact Nat.le_add_right _ _

/-- The two scalar inequalities required of the polynomial coefficient.
The first pays for the normalized frozen-uniformity term and the second for
the source energy-gap cleaning term. -/
structure SourceBundleRemovalGrowthConditions
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  gap :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)

/-- A natural polynomial coefficient satisfying both source-bundle
inequalities exists for every pair of positive real parameters. -/
theorem exists_sourceBundleRemovalGrowthCoefficient
    {δ η : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hη : 0 < η) (_hη_one : η ≤ 1) (N : ℕ) :
    ∃ Q : ℕ,
      SourceBundleRemovalGrowthConditions δ η N Q := by
  let x : ℝ := η ^ 2 * δ ^ (2 * N + 1)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / x)
  have hQpos : 0 < (Q : ℝ) := (div_pos one_pos hx).trans hQ
  have hQone : (1 : ℝ) ≤ Q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by exact_mod_cast ne_of_gt hQpos))
  have hQx : 1 < (Q : ℝ) * x := by
    calc
      1 = (1 / x) * x := by field_simp
      _ < (Q : ℝ) * x := mul_lt_mul_of_pos_right hQ hx
  refine ⟨Q, ?_, ?_⟩
  · have hpow : δ ^ (2 * N + 1) ≤ δ ^ N := by
      exact pow_le_pow_of_le_one hδ.le hδ_one (by omega)
    calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * η ^ 2 * δ ^ N := by
        dsimp [x]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (sq_nonneg η))
            hQpos.le)
  · calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * ((Q : ℝ) * x) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hQone
            (mul_nonneg hQpos.le hx.le))
      _ = δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := by
        dsimp [x]
        ring

/-- The polynomial growth value makes the common reciprocal tolerance at
scale `m` no larger than the normalized finite-horizon target. -/
theorem one_div_sourceBundleRemovalGrowth_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    1 / (sourceBundleRemovalGrowth Q N m : ℝ) ≤
      η ^ 2 * sourceBundleDensity δ m ^ N := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  apply (div_le_iff₀ hF).2
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  calc
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N := hQ.uniform
    _ =
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) := by
      unfold sourceBundleDensity
      rw [div_pow]
      field_simp
    _ ≤
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          (sourceBundleRemovalGrowth Q N m : ℕ) := by
      apply mul_le_mul_of_nonneg_left hpoly
      exact mul_nonneg (sq_nonneg η)
        (pow_nonneg (sourceBundleDensity_nonneg hδ.le m) N)

/-- After division by the scale-dependent squared defect threshold, the
source rank-gap target costs at most `δ`. -/
theorem sourceFullRankGap_div_sourceBundleDefectScale_sq_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    (1 / (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2) /
          sourceBundleDefectScale δ η N m ^ 2 ≤
      δ := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  have ht : 0 < sourceBundleDefectScale δ η N m :=
    sourceBundleDefectScale_pos hδ hη N m
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  rw [div_le_iff₀ (sq_pos_of_pos hF)]
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  have hpolySq :
      ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 ≤
        (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg Q) (pow_nonneg hx.le N))
        hF.le).2 hpoly
  calc
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := hQ.gap
    _ =
        δ * (((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      unfold sourceBundleDefectScale sourceBundleDensity
      rw [div_pow]
      field_simp
      ring
    _ ≤
        δ * ((sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact mul_le_mul_of_nonneg_right hpolySq (sq_nonneg _)
    _ =
        δ * sourceBundleDefectScale δ η N m ^ 2 *
          (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
      ring

/-! ## Finite-horizon normalized counting bounds -/

/-- The density-scaled defect is small after normalization by every density
power up to its chosen horizon.  The factor four is the lower-error cap
appearing in the reverse-doubling bundle envelope. -/
theorem sqrt_sourceBundleDefectScale_sq_four_div_pow_le
    {δ κ step : ℝ} {N p m : ℕ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 ≤ κ) (hκ_step : 4 * κ ≤ step)
    (hp : p ≤ N) :
    Real.sqrt
          (sourceBundleDefectScale δ κ N m ^ 2 *
            (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
        sourceBundleDensity δ m ^ p ≤
      step / 2 := by
  let a := sourceBundleDensity δ m
  let t := sourceBundleDefectScale δ κ N m
  have ha : 0 < a := sourceBundleDensity_pos hδ m
  have ha_one : a ≤ 1 :=
    sourceBundleDensity_le_one hδ_one hδ.le m
  have ht : 0 ≤ t :=
    sourceBundleDefectScale_nonneg hδ.le hκ N m
  have hpow : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hsqrt :
      Real.sqrt (t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) =
        2 * t := by
    rw [show
      t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) =
        (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) ht)
  rw [show sourceBundleDefectScale δ κ N m = t by rfl,
    show sourceBundleDensity δ m = a by rfl, hsqrt]
  have hnormalized : 2 * t / a ^ p ≤ 2 * κ := by
    apply (div_le_iff₀ (pow_pos ha p)).2
    calc
      2 * t = (2 * κ) * a ^ N := by
        dsimp [t, a, sourceBundleDefectScale]
        ring
      _ ≤ (2 * κ) * a ^ p :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hnormalized.trans (by linarith)

/-- A tolerance bounded by `κ² a^N` remains at most `κ²` after
normalization by any larger density floor to a power at most `N`. -/
theorem div_pow_le_sq_of_le_scaled_pow
    {τ κ a μ : ℝ} {p N : ℕ}
    (ha : 0 < a) (ha_one : a ≤ 1) (haμ : a ≤ μ)
    (hτ : τ ≤ κ ^ 2 * a ^ N) (hp : p ≤ N) :
    τ / μ ^ p ≤ κ ^ 2 := by
  have hμ : 0 < μ := ha.trans_le haμ
  have hpow₁ : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hpow₂ : a ^ p ≤ μ ^ p :=
    pow_le_pow_left₀ ha.le haμ p
  apply (div_le_iff₀ (pow_pos hμ p)).2
  exact hτ.trans
    (mul_le_mul_of_nonneg_left (hpow₁.trans hpow₂) (sq_nonneg κ))

/-- The explicit source-full hierarchy, viewed just as a selected scale
array, feeds the reverse-doubling bundle envelope.  All hypotheses are
scalar and ambient-independent. -/
theorem sourceBundleRankwiseEnvelope_and_error_lt_half
    {r edgeBound Q : ℕ} {δ κ step : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 < κ) (hstep : 0 ≤ step)
    (hκ_step : 4 * κ ≤ step)
    (hκ_sq : κ ^ 2 ≤ step / 2)
    (hcap :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step ≤ 1)
    (hfinal :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step < 1 / 2)
    (hQ : SourceBundleRemovalGrowthConditions δ κ
      (bundleReverseDoublingHorizon r edgeBound 0) Q)
    (scale : Fin (r + 1) → ℕ) (hscale : Antitone scale) :
    IsBundleCountingEnvelope
        (sourceBundleRankwiseDensity δ scale)
        (sourceBundleRankwiseDefect δ κ
          (bundleReverseDoublingHorizon r edgeBound 0) scale)
        (bundleRankwiseDensityFloor
          (sourceBundleRankwiseDensity δ scale))
        (sourceFullCommonTolerance
          (sourceBundleRemovalGrowth Q
            (bundleReverseDoublingHorizon r edgeBound 0)) scale)
        (bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)) ∧
      bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)
          r edgeBound < 1 / 2 := by
  let N := bundleReverseDoublingHorizon r edgeBound 0
  let α := sourceBundleRankwiseDensity δ scale
  let β := sourceBundleRankwiseDefect δ κ N scale
  let μ := bundleRankwiseDensityFloor α
  let τ := sourceFullCommonTolerance
    (sourceBundleRemovalGrowth Q N) scale
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N scale d
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos
      (sourceBundleRemovalGrowth Q N) scale).le
  have hαzero : ∀ d, α 0 ≤ α d := by
    intro d
    exact sourceBundleRankwiseDensity_zero_le hδ.le hscale d
  have hfinitePower :
      ∀ d, d < r → ∀ n,
        n < bundleReverseDoublingHorizon r edgeBound (d + 1) →
          n + 1 ≤ N := by
    intro d _hd n hn
    have hhorizon :=
      bundleReverseDoublingHorizon_le_zero r edgeBound (d + 1)
    dsimp only [N]
    omega
  apply
    (bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
      hα hα_one hβ hτ hstep r edgeBound hcap hfinal)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    simpa only [α, β, N, sourceBundleRankwiseDefect,
      sourceBundleRankwiseDensity] using
      (sqrt_sourceBundleDefectScale_sq_four_div_pow_le
        hδ hδ_one hκ.le hκ_step hp)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    have ha0 : 0 < α 0 := hα 0
    have ha0_one : α 0 ≤ 1 := hα_one 0
    have ha0μ : α 0 ≤ μ (d + 1) :=
      le_bundleRankwiseDensityFloor_of_zero_le hαzero (d + 1)
    have hτscaled : τ ≤ κ ^ 2 * (α 0) ^ N := by
      simpa only [τ, α, N, sourceFullCommonTolerance,
        sourceBundleRankwiseDensity, sourceBundleSelectedScale_zero] using
        (one_div_sourceBundleRemovalGrowth_le hδ hκ hQ (scale 0))
    exact
      (div_pow_le_sq_of_le_scaled_pow
        ha0 ha0_one ha0μ hτscaled hp).trans hκ_sq

namespace SourceFullCoarseTargetSchedule.Certificate

/-- The scale hierarchy stored in a realized source-full certificate is
antitone. -/
theorem scale_antitone
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (C.scale j.succ)).trans
        (C.scale_hierarchy j))

end SourceFullCoarseTargetSchedule.Certificate

/-! ## A bounded realized certificate -/

namespace SourceFullCoarseTargetSchedule.Bounded

/-- A realized source-full certificate which remembers the numerical
ceiling of the ambient-independent bounded plan. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r) where
  toSourceFull :
    SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor
  scale_zero_le_ceiling : toSourceFull.scale 0 ≤ S.ceiling

/-- Realize a bounded numerical plan while retaining its landing-independent
ceiling. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty (Certificate S initial) := by
  obtain ⟨P, R, hindex⟩ :=
    S.plan.schedule.exists_landing_certificate
      initial S.plan.schedule_admissible
  let C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor :=
    { tolerance := P.tolerance
      budget := P.budget
      length := P.length
      regularity := R
      scale := S.plan.scale P
      scaleFloor_le := S.plan.scaleFloor_le P
      scale_hierarchy := S.plan.scale_hierarchy P
      selected_tolerance_nonneg := by
        intro j
        simp only [selectedOrderedComplexTolerance]
        rw [congrFun hindex j]
        exact
          P.tolerance_nonneg S.plan.schedule_admissible
            j (P.index j)
      selected_tolerance_le_common := by
        intro j
        simpa [selectedOrderedComplexTolerance, hindex] using
          S.plan.selected_tolerance_le_common P j
      rank_gap_le := by
        intro j
        have hgap := R.gap_le j
        have hreciprocal := S.plan.reciprocal_gap_le P j
        change
          orderedLayerAtomEnergy
                (R.fine.partition j.castSucc)
                (R.coarse.partition j.succ) -
              orderedLayerAtomEnergy
                (R.coarse.partition j.castSucc)
                (R.coarse.partition j.succ) ≤
            sourceFullRankGap F (S.plan.scale P) j
        exact hgap.trans hreciprocal
      coarse_complexity := by
        intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have htop := congrFun R.coarse_topLayer_eq e
            simp only [OrderedPartitionComplex.topLayer] at htop
            rw [htop]
            calc
              FacePartition.complexity
                    (initial.partition (Fin.last r) e) ≤
                  initialBound (Fin.last r) :=
                hinitial (Fin.last r) e
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P (Fin.last r) := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P (Fin.last r) :=
                S.plan.selected_coarse_bound P (Fin.last r)
        | cast j =>
            intro e
            calc
              FacePartition.complexity
                    (R.coarse.partition j.castSucc e) ≤
                  fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    FacePartition.complexity
                        (initial.partition j.castSucc e) := by
                rw [← congrFun hindex j]
                exact R.coarse_complexity j e
              _ ≤ fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    initialBound j.castSucc :=
                Nat.mul_le_mul_left _ (hinitial j.castSucc e)
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P j.castSucc := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P j.castSucc :=
                S.plan.selected_coarse_bound P j.castSucc }
  exact ⟨⟨C, S.scale_zero_le P⟩⟩

end SourceFullCoarseTargetSchedule.Bounded

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalAssembly.lean` -/

section
/-!
# Schedule-level assembly of ordered hypergraph removal

The structural regularity theorem accepts a tolerance schedule, a
weak-regularity budget at every stage, and one energy-selection length at
every rank.  `OrderedRemovalParameters` identifies the two numerical
inequalities those schedules must satisfy.  This file performs all remaining
quantifier and semantic assembly.

The main theorem is deliberately conditional on the existence of compatible
ambient-independent schedules.  It proves that such schedules imply
`HasUniformOrderedPatternRemoval`; no fixed point or diagonal selector is
assumed to have been constructed here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The canonical pattern complex has complexity at most two -/

/-- Every layer of the canonical edge-monochromatic input complex has at
most two atoms.  Lower layers are indiscrete and the top layer is generated
by one edge predicate. -/
theorem complexity_orderedPatternInitialComplex_le_two
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        FacePartition.complexity
            ((orderedPatternInitialComplex H).topLayer e) ≤ 2
      rw [orderedPatternInitialComplex_topLayer]
      exact complexity_orderedPatternTopPartition_le_two H e
  | cast i =>
      intro e
      simp [orderedPatternInitialComplex,
        indiscreteOrderedPartitionComplex,
        OrderedPartitionComplex.withTopLayer]

/-! ## Ambient-independent compatible schedules -/

/-- A complete schedule whose inequalities are strong enough for the
fine-configuration ordered-removal pipeline.

The bound in `tolerance_le` and `reciprocal_gap_le` uses only the displayed
natural schedules and `initialBound`, so the data are independent of the
ambient finite type and the input pattern. -/
structure OrderedRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  tolerance_le :
    ∀ j n,
      tolerance j n ≤
        orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ
  reciprocal_gap_le :
    (∑ j : Fin r,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
        (length j : ℝ)) ≤
      orderedRemovalEnergyGapTarget k r
        (orderedRemovalFinePartitionComplexityBound
          r initialBound budget length) ξ

namespace OrderedRemovalSchedule

/-- A compatible schedule supplies a strong regularity certificate over
every ambient finite type and every initial complex. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : OrderedRemovalSchedule k r initialBound ξ)
    (initial : OrderedPartitionComplex G k r) :
    Nonempty
      (StrongOrderedComplexRegularityCertificate
        G k r initial S.tolerance S.budget S.length) := by
  exact StrongOrderedComplexRegularityCertificate.nonempty
    initial S.tolerance S.budget S.length
    (fun j n => (S.tolerance_pos j n).le)
    S.budget_spec S.length_pos

end OrderedRemovalSchedule

/-! ## Conditional uniform ordered removal -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalAssembly.lean` -/

section
/-!
# Source-full bundle-counting removal assembly

This file joins the ambient-independent source-full regularity plan to the
rankwise bundle-counting theorem and the source-full bad-base deletion family.
The selected regularity scale is clipped to the finite rank horizon.  Since
the selected scales decrease with rank while `sourceBundleDensity` decreases
with its scale, the resulting density schedule increases with rank; hence its
bundle prefix floor is exactly its rank-zero value.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Ambient-independent scalar budgets -/

/-- The largest edge horizon queried by the reverse-doubling recurrence. -/
noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

/-- Each positive subface spends two copies of this allowance: one for
low density and one for its source-full defect. -/
noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

/-- The per-step reserve in the explicit reverse-doubling envelope. -/
noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

/-- The square-root defect coefficient; the factor eight leaves room for
both halves of every one-edge counting increment. -/
noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

theorem sourceBundleRemovalDensityBudget_pos
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < sourceBundleRemovalDensityBudget ε r := by
  unfold sourceBundleRemovalDensityBudget
  positivity

theorem sourceBundleRemovalDensityBudget_le_one
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    sourceBundleRemovalDensityBudget ε r ≤ 1 := by
  unfold sourceBundleRemovalDensityBudget
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  have hden : (1 : ℝ) ≤
      (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ) := by
    push_cast
    have hcard :
        (0 : ℝ) ≤ Fintype.card (OrderedPositiveSubface r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) hden).trans hmin

/-- The total deletion cost of all positive subfaces fits below the input
allowance. -/
theorem card_mul_two_sourceBundleRemovalDensityBudget_le
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        (sourceBundleRemovalDensityBudget ε r +
          sourceBundleRemovalDensityBudget ε r) ≤ ε := by
  let s := Fintype.card (OrderedPositiveSubface r)
  let x : ℝ := min ε 1
  have hx : 0 < x := lt_min hε zero_lt_one
  have hden : (0 : ℝ) < (4 * (s + 1 : ℕ) : ℕ) := by
    positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  calc
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (sourceBundleRemovalDensityBudget ε r +
            sourceBundleRemovalDensityBudget ε r) =
        ((2 * (s : ℝ)) * x) / (4 * (s + 1 : ℕ) : ℕ) := by
      simp only [sourceBundleRemovalDensityBudget, s, x]
      ring
    _ ≤ x := by
      apply (div_le_iff₀ hden).2
      push_cast
      nlinarith
    _ ≤ ε := min_le_left _ _

theorem sourceBundleRemovalStep_pos (k r : ℕ) :
    0 < sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalStep
  positivity

theorem sourceBundleRemovalStep_le_one (k r : ℕ) :
    sourceBundleRemovalStep k r ≤ 1 := by
  unfold sourceBundleRemovalStep
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ sourceBundleRemovalHorizon k r := by
    positivity
  nlinarith [mul_nonneg hr hH]

theorem sourceBundleRemovalKappa_pos (k r : ℕ) :
    0 < sourceBundleRemovalKappa k r := by
  unfold sourceBundleRemovalKappa
  exact div_pos (sourceBundleRemovalStep_pos k r) (by norm_num)

theorem sourceBundleRemovalKappa_le_one (k r : ℕ) :
    sourceBundleRemovalKappa k r ≤ 1 := by
  unfold sourceBundleRemovalKappa
  have hstep := sourceBundleRemovalStep_le_one k r
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem four_mul_sourceBundleRemovalKappa_le_step (k r : ℕ) :
    4 * sourceBundleRemovalKappa k r ≤
      sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalKappa
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem sourceBundleRemovalKappa_sq_le_half_step (k r : ℕ) :
    sourceBundleRemovalKappa k r ^ 2 ≤
      sourceBundleRemovalStep k r / 2 := by
  unfold sourceBundleRemovalKappa
  have hpos := sourceBundleRemovalStep_pos k r
  have hone := sourceBundleRemovalStep_le_one k r
  nlinarith [sq_nonneg (sourceBundleRemovalStep k r)]

/-- The chosen step reserve makes the entire finite envelope smaller than
one quarter, and therefore supplies both the cap and strict half-error
hypotheses. -/
theorem sourceBundleRemovalStep_total_le_quarter (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 / 4 := by
  let p := r * sourceBundleRemovalHorizon k r
  have hden : (0 : ℝ) < (4 * (p + 1 : ℕ) : ℕ) := by
    positivity
  rw [show
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
          sourceBundleRemovalStep k r =
        (p : ℝ) / (4 * (p + 1 : ℕ) : ℕ) by
      simp only [sourceBundleRemovalStep, p]
      push_cast
      ring]
  apply (div_le_iff₀ hden).2
  push_cast
  have hp : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem sourceBundleRemovalStep_total_le_one (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans (by norm_num)

theorem sourceBundleRemovalStep_total_lt_half (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r < 1 / 2 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans_lt (by norm_num)

/-! ## A uniform count threshold from the bounded scale ceiling -/

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)

theorem sourceBundleRemovalCountThreshold_pos
    {δ : ℝ} (hδ : 0 < δ) (k r ceiling : ℕ) :
    0 < sourceBundleRemovalCountThreshold k r ceiling δ := by
  unfold sourceBundleRemovalCountThreshold
  exact mul_pos (by norm_num)
    (pow_pos (sourceBundleDensity_pos hδ ceiling) _)

/-! ## End-to-end source-full ordered removal -/

/-- Tao's source-full hierarchy, the rankwise bundle-counting envelope, and
source-full bad-base cleaning prove uniform ordered removal at every positive
rank. -/
theorem hasUniformOrderedPatternRemoval_sourceFull
    (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let edgeBound : ℕ :=
    (orderedConfigurationInitialBundle k r).edges.card
  let N : ℕ := sourceBundleRemovalHorizon k r
  let δ : ℝ := sourceBundleRemovalDensityBudget ε r
  let step : ℝ := sourceBundleRemovalStep k r
  let κ : ℝ := sourceBundleRemovalKappa k r
  have hδ : 0 < δ := by
    exact sourceBundleRemovalDensityBudget_pos hε r
  have hδ_one : δ ≤ 1 := by
    exact sourceBundleRemovalDensityBudget_le_one hε r
  have hstep : 0 < step := by
    exact sourceBundleRemovalStep_pos k r
  have hκ : 0 < κ := by
    exact sourceBundleRemovalKappa_pos k r
  have hκ_one : κ ≤ 1 := by
    exact sourceBundleRemovalKappa_le_one k r
  have hκ_step : 4 * κ ≤ step := by
    exact four_mul_sourceBundleRemovalKappa_le_step k r
  have hκ_sq : κ ^ 2 ≤ step / 2 := by
    exact sourceBundleRemovalKappa_sq_le_half_step k r
  obtain ⟨Q, hQ⟩ :=
    exists_sourceBundleRemovalGrowthCoefficient
      hδ hδ_one hκ hκ_one N
  let F : NatGrowthFunction := sourceBundleRemovalGrowth Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (SourceFullCoarseTargetSchedule.bounded_nonempty
        k r initialBound F 0)
  let c : ℝ :=
    sourceBundleRemovalCountThreshold k r S.ceiling δ
  have hc : 0 < c := by
    exact sourceBundleRemovalCountThreshold_pos hδ k r S.ceiling
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let initial : OrderedPartitionComplex G k r :=
    orderedPatternInitialComplex H
  obtain ⟨Cbounded⟩ :=
    S.certificate_nonempty initial (by
      intro q e
      exact complexity_orderedPatternInitialComplex_le_two H q e)
  let C := Cbounded.toSourceFull
  let P : OrderedCoarseFineComplex G k r :=
    C.regularity.toCoarseFine
  let α : ℕ → ℝ := sourceBundleRankwiseDensity δ C.scale
  let β : ℕ → ℝ := sourceBundleRankwiseDefect δ κ N C.scale
  let μ : ℕ → ℝ := bundleRankwiseDensityFloor α
  let τ : ℝ := sourceFullCommonTolerance F C.scale
  let E : ℕ → ℕ → ℝ :=
    bundleRankwiseEnvelopeError α β μ τ
  let D : OrderedPattern.DeletionFamily (G := G) k r :=
    P.sourceFullBadBaseDeletionFamily α β
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ C.scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one C.scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N C.scale d
  have hβ_pos : ∀ d, 0 < β d := by
    intro d
    unfold β sourceBundleRankwiseDefect
    exact sq_pos_of_pos
      (sourceBundleDefectScale_pos hδ hκ N _)
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos F C.scale).le
  have hscale : Antitone C.scale := C.scale_antitone
  have henvelopeRaw :=
    sourceBundleRankwiseEnvelope_and_error_lt_half
      (r := r) (edgeBound := edgeBound) (Q := Q)
      hδ hδ_one hκ hstep.le hκ_step hκ_sq
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_le_one k r)
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_lt_half k r)
      (by simpa [N, edgeBound, sourceBundleRemovalHorizon] using hQ)
      C.scale hscale
  have henvelope : IsBundleCountingEnvelope α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.1
  have herror : E r edgeBound < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.2
  have hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ) := by
    simpa [P, τ] using
      C.isFullyMixedPreliminaryOrderedRegular_common
  have hthreshold :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) := by
    have hfloor : 0 ≤ sourceBundleDensity δ S.ceiling :=
      (sourceBundleDensity_pos hδ S.ceiling).le
    have hpoint : ∀ e : PositiveOrderedFace k r,
        sourceBundleDensity δ S.ceiling ≤ α e.rank := by
      intro e
      unfold α sourceBundleRankwiseDensity
      apply sourceBundleDensity_antitone hδ.le
      exact
        (hscale (Fin.zero_le _)).trans
          Cbounded.scale_zero_le_ceiling
    have hprod :
        sourceBundleDensity δ S.ceiling ^
            Fintype.card (PositiveOrderedFace k r) ≤
          ∏ e : PositiveOrderedFace k r, α e.rank := by
      calc
        sourceBundleDensity δ S.ceiling ^
              Fintype.card (PositiveOrderedFace k r) =
            ∏ _e : PositiveOrderedFace k r,
              sourceBundleDensity δ S.ceiling := by simp
        _ ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
          apply Finset.prod_le_prod
          · intro e _he
            exact hfloor
          · intro e _he
            exact hpoint e
    simpa [c, sourceBundleRemovalCountThreshold] using
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration G k r P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A := by
    intro A hgood
    exact hthreshold.trans
      (half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
        P A α β μ τ E hα hα_one hβ hτ hgood hregular
        henvelope (by simpa [edgeBound] using herror))
  have hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H) := by
    simpa [P, initial,
      CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
        C.regularity.coarse_refines_initial
  have hcover : H.IsCover D := by
    exact
      sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
        (by simpa [r] using hrank) H P hinitial α β c hcount hgoodCount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbase :=
    P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
      α β (fun j => (hα (j + 1)).le) (fun j => hβ_pos (j + 1)) e
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using hbase
    _ ≤ ∑ _q : OrderedPositiveSubface r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have hselected :
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            sourceBundleSelectedScale_of_le C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have hcomplexity :
          FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
          C.coarse_complexity q.1.succ (q.2.trans e)
      have hlow :
          (FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (FacePartition.complexity
                (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr hcomplexity) (hα _).le
          _ = (C.scale q.1.succ : ℝ) *
                sourceBundleDensity δ (C.scale q.1.succ) := by
            simp [α, sourceBundleRankwiseDensity, hselected]
          _ ≤ δ := mul_sourceBundleDensity_le hδ.le _
      have hfaceLayer :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.coarseUpperLayerAtomEnergyGap q.1 := by
        rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face q.1]
        exact Finset.single_le_sum
          (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have hlayer :
          P.coarseUpperLayerAtomEnergyGap q.1 ≤
            sourceFullRankGap F C.scale q.1 := by
        simpa [P] using C.rank_gap_le q.1
      have hdefect :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              sourceFullRankGap F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (hfaceLayer.trans hlayer) (hβ _)
          _ =
              (1 /
                  (sourceBundleRemovalGrowth Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                sourceBundleDefectScale δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, sourceFullRankGap, β,
              sourceBundleRankwiseDefect, hselected]
          _ ≤ δ :=
            sourceFullRankGap_div_sourceBundleDefectScale_sq_le
              hδ hκ hQ (C.scale q.1.succ)
      exact add_le_add hlow hdefect
    _ = (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        card_mul_two_sourceBundleRemovalDensityBudget_le hε (n + 1)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Szemeredi/Weighted.lean` -/

section
/-!
# From dense sets to bounded dense weights

The hypergraph-removal layer will first produce a quantitative progression
count for dense finite sets.  This file proves the standard thresholding
step that upgrades such a theorem to functions `g : ZMod N → [0,1]`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A quantitative dense-set arithmetic-progression counting statement at
one fixed modulus. -/
def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

/-- Uniform dense-set AP counting with one lower bound for every nontrivial
cyclic modulus. -/
def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/APRemoval.lean` -/

section
/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The unweighted partite hypergraph cut out by membership of each AP form
in `A`. -/
def apSetHypergraph (k N : ℕ) (A : Finset (ZMod N)) :
    SimplexHypergraph (fun _ : Fin k => ZMod N) where
  edge j x := apSimplexForm k N j x ∈ A

@[simp]
theorem apSetHypergraph_edge
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).edge j x ↔
      apSimplexForm k N j x ∈ A :=
  Iff.rfl

/-- The zero-one weight of the AP-set hypergraph is exactly the set
indicator evaluated on the corresponding AP form. -/
@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

/-- The labelled simplex density of the AP-set hypergraph is its normalized
cyclic arithmetic-progression count. -/
theorem apSetHypergraph_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (apSetHypergraph (r + 2) N A).toWeighted.simplexCount =
      cyclicAPCount (r + 2) N (finsetIndicator A) := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount
    r N (finsetIndicator A)]
  simp only [WeightedSimplexSystem.simplexCount]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact apSetHypergraph_toWeighted_edgeWeight
    (r + 2) N A j (deleteCoordinate x j)

/-- Parameters for degenerate AP simplices: a member of `A` and the free
tail in the AP/simplex coordinate equivalence. -/
abbrev DiagonalAPParameter
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)

/-- The labelled simplex corresponding to the constant progression with
value `a`. -/
def diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) → ZMod N :=
  simplexCoordinatesOfAP r N p.1.1 0 p.2

@[simp]
theorem simplexCoordinateSum_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateSum (r + 2) N
      (diagonalAPSimplex r N A p) = 0 := by
  simp [diagonalAPSimplex]

@[simp]
theorem simplexCoordinateMoment_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateMoment (r + 2) N
      (diagonalAPSimplex r N A p) = p.1.1 := by
  simp [diagonalAPSimplex]

/-- Every edge form on a degenerate AP simplex is the same member of `A`. -/
@[simp]
theorem apSimplexForm_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A)
    (j : Fin (r + 2)) :
    apSimplexForm (r + 2) N j
        (deleteCoordinate (diagonalAPSimplex r N A p) j) =
      p.1.1 := by
  rw [apSimplexForm_deleteCoordinate,
    simplexCoordinateMoment_diagonalAPSimplex,
    simplexCoordinateSum_diagonalAPSimplex]
  simp

/-- Every degenerate AP parameter gives an actual labelled simplex of the
AP-set hypergraph. -/
theorem diagonalAPSimplex_mem_simplexFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    diagonalAPSimplex r N A p ∈
      (apSetHypergraph (r + 2) N A).simplexFinset := by
  letI : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [SimplexHypergraph.mem_simplexFinset]
  intro j
  rw [apSetHypergraph_edge,
    apSimplexForm_diagonalAPSimplex]
  exact p.1.2

/-- Distinct degenerate AP parameters give distinct labelled simplices. -/
theorem diagonalAPSimplex_injective
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (diagonalAPSimplex r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have hmoment :=
      congrArg
        (simplexCoordinateMoment (r + 2) N) hpq
    simpa using hmoment
  · funext i
    exact congrFun hpq i.succ.succ

/-- Present a dependent deleted-coordinate vector by the canonical
`Fin n` list of its remaining coordinates. -/
noncomputable def deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedVectorToFinTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

/-- A full tuple is determined by one deleted-coordinate tuple together
with its total sum. -/
theorem eq_of_deletedVectorToFinTuple_eq_of_sum_eq
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (hjl : j = l)
    (hdeleted :
      deletedVectorToFinTuple j (deleteCoordinate x j) =
        deletedVectorToFinTuple l (deleteCoordinate y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have hother :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [hother]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t

namespace SimplexHypergraph

/-- All deleted coloured faces, embedded into one fixed finite type by the
canonical ordering of each deleted coordinate space. -/
noncomputable def deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (deleted j).image fun x =>
      (j, deletedVectorToFinTuple j x)

theorem mem_deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ deleted j) :
    (j, deletedVectorToFinTuple j x) ∈
      deletionSlotFinset deleted := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The fixed-type union of deletion slots has cardinality at most the sum
of the individual coloured deletion cardinalities. -/
theorem card_deletionSlotFinset_le_deletionCount
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    (deletionSlotFinset deleted).card ≤
      deletionCount deleted := by
  classical
  calc
    (deletionSlotFinset deleted).card ≤
        ∑ j : Fin (n + 1),
          ((deleted j).image fun x =>
            (j, deletedVectorToFinTuple j x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (n + 1), (deleted j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le
    _ = deletionCount deleted := rfl

end SimplexHypergraph

/-- Choose one deleted colour witnessing that a cover meets a given
degenerate arithmetic-progression simplex. -/
noncomputable def diagonalCoverColor
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) :=
  Classical.choose
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

/-- Encode the face selected by a cover in a fixed finite disjoint union of
coloured deletion slots. -/
noncomputable def diagonalCoveredSlot
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := diagonalCoverColor r N A deleted hcover p
  (j, deletedVectorToFinTuple j
    (deleteCoordinate (diagonalAPSimplex r N A p) j))

theorem diagonalCoveredSlot_mem_deletionSlotFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    diagonalCoveredSlot r N A deleted hcover p ∈
      SimplexHypergraph.deletionSlotFinset deleted := by
  classical
  exact SimplexHypergraph.mem_deletionSlotFinset deleted
    (diagonalCoverColor r N A deleted hcover p)
    (deleteCoordinate (diagonalAPSimplex r N A p)
      (diagonalCoverColor r N A deleted hcover p))
    (diagonalCoverColor_mem r N A deleted hcover p)

/-- No deleted coloured face can cover two different members of the
degenerate simplex family.  Equality off the deleted coordinate and equality
of the total coordinate sums recover the whole labelled simplex. -/
theorem diagonalCoveredSlot_injective
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Function.Injective
      (diagonalCoveredSlot r N A deleted hcover) := by
  intro p q hpq
  apply diagonalAPSimplex_injective r N A
  apply eq_of_deletedVectorToFinTuple_eq_of_sum_eq
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A p) =
        simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A q)
    simp

/-- The parameter set for the degenerate simplex family has the expected
cardinality `|A| N^r`. -/
@[simp]
theorem card_diagonalAPParameter
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    Fintype.card (DiagonalAPParameter r N A) =
      A.card * N ^ r := by
  simp [DiagonalAPParameter, ZMod.card]

/-- Every cover of the AP-set hypergraph deletes at least one distinct face
for each member of the degenerate simplex family. -/
theorem card_diagonalAPParameter_le_deletionCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Fintype.card (DiagonalAPParameter r N A) ≤
      SimplexHypergraph.deletionCount deleted := by
  classical
  let f := diagonalCoveredSlot r N A deleted hcover
  calc
    Fintype.card (DiagonalAPParameter r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ 
        (diagonalCoveredSlot_injective r N A deleted hcover)]
      simp
    _ ≤
        (SimplexHypergraph.deletionSlotFinset deleted).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact diagonalCoveredSlot_mem_deletionSlotFinset
        r N A deleted hcover p
    _ ≤ SimplexHypergraph.deletionCount deleted :=
      SimplexHypergraph.card_deletionSlotFinset_le_deletionCount
        deleted

/-- For constant vertex classes `ZMod N`, the total number of coloured face
slots is `(r+2) N^(r+1)`. -/
@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]

/-- A simplex cover of the AP-set hypergraph has normalized deletion cost at
least one `1/(r+2)` share of the density of `A`.  This is the exact
edge-disjoint-degenerate-simplices estimate used in the removal argument. -/
theorem mean_finsetIndicator_div_le_normalizedDeletionCost
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by
  have hcount :
      A.card * N ^ r ≤
        SimplexHypergraph.deletionCount deleted := by
    simpa using
      card_diagonalAPParameter_le_deletionCount
        r N A deleted hcover
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [mean_finsetIndicator, ZMod.card,
    SimplexHypergraph.normalizedDeletionCost,
    deletionCapacity_zmod]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (SimplexHypergraph.deletionCount deleted : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity

/-- Uniform partite simplex removal on cyclic vertex classes of a fixed
number of colours.  The constant is independent of the modulus.  This is the
precise deep combinatorial input still required from the hypergraph
regularity/removal development. -/
def HasUniformCyclicPartiteSimplexRemoval (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            SimplexHypergraph (fun _ : Fin k => ZMod N),
          H.toWeighted.simplexCount < c →
            ∃ deleted :
                SimplexHypergraph.DeletionFamily
                  (fun _ : Fin k => ZMod N),
              H.IsSimplexCover deleted ∧
                SimplexHypergraph.normalizedDeletionCost
                    deleted ≤ ε

/-- Uniform partite simplex removal implies a uniform quantitative dense
Szemerédi theorem.  The proof is the standard contrapositive: a set whose AP
hypergraph has too few simplices admits a cheap cover, while the
edge-disjoint degenerate simplices force every cover to cost at least
`density / k`. -/
theorem exists_uniformDenseAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have hbase : 0 < δ / (r + 2 : ℝ) :=
    div_pos hδ hk
  have hε : 0 < ε := by
    exact div_pos hbase (by norm_num)
  obtain ⟨c, hc, hremove⟩ := hrem ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra hcount
  have hcount_lt :
      cyclicAPCount (r + 2) N (finsetIndicator A) < c :=
    lt_of_not_ge hcount
  have hsimplex_lt :
      (apSetHypergraph (r + 2) N A).toWeighted.simplexCount <
        c := by
    simpa [apSetHypergraph_simplexCount_eq_cyclicAPCount]
      using hcount_lt
  obtain ⟨deleted, hcover, hcost⟩ :=
    hremove N (apSetHypergraph (r + 2) N A) hsimplex_lt
  have hlower :
      mean (finsetIndicator A) / (r + 2 : ℝ) ≤
        SimplexHypergraph.normalizedDeletionCost deleted :=
    mean_finsetIndicator_div_le_normalizedDeletionCost
      r N A deleted hcover
  have hdensity :
      δ / (r + 2 : ℝ) ≤
        mean (finsetIndicator A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have hε_lt : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedSimplexBridge.lean` -/

section
/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The colour `j` regarded as the increasing codimension-one face which
omits `j`. -/
def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

/-- Colours of an `(n + 1)`-vertex simplex are equivalent to increasing
rank-`n` faces.  The construction factors through finite subsets so that its
forward map is definitionally the complement of a singleton. -/
noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)

@[simp]
theorem orderedFacetEquiv_apply
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp

/-- The two standard presentations of a deleted coordinate vector are
mutually inverse. -/
@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

/-- Reindexing identifies the deleted-vector space of every colour with the
same ordinary tuple space. -/
noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl

@[simp]
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr

/-- Regard an equal-vertex simplex hypergraph as a complete ordered pattern.
An arbitrary ordered face is first decoded as its unique omitted colour. -/
noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)

@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]

/-- Ordered occurrences are exactly labelled simplices. -/
theorem SimplexHypergraph.toOrderedPattern_isOccurrence_iff
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.toOrderedPattern.IsOccurrence x ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  constructor
  · intro hx j
    have hj := hx (orderedFacet j)
    rw [H.toOrderedPattern_edge_orderedFacet] at hj
    simpa using hj
  · intro hx e
    let j := (orderedFacetEquiv n).symm e
    have he : orderedFacet j = e := by
      rw [← orderedFacetEquiv_apply]
      exact (orderedFacetEquiv n).apply_symm_apply e
    rw [← he]
    rw [H.toOrderedPattern_edge_orderedFacet]
    simpa using hx j

/-- The finite occurrence set is unchanged by the ordered presentation. -/
theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]

/-- In particular, the zero-one normalized pattern count is exactly the
zero-one normalized simplex count. -/
theorem SimplexHypergraph.toOrderedPattern_patternCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.toWeighted.patternCount =
      H.toWeighted.simplexCount := by
  rw [OrderedPattern.toWeighted_patternCount_eq,
    SimplexHypergraph.toWeighted_simplexCount_eq_card_div,
    H.toOrderedPattern_occurrenceFinset]

/-- Send an ordered deletion on the face omitting `j` to the corresponding
dependent deleted-vector space. -/
noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)

@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩

/-- Reindexing a deletion face does not change its cardinality. -/
@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple

/-- A cover of the ordered presentation transports to a simplex cover. -/
theorem SimplexHypergraph.isSimplexCover_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (hcover : H.toOrderedPattern.IsCover D) :
    H.IsSimplexCover (orderedDeletionToSimplex D) := by
  intro x hx
  have hxOrdered :
      x ∈ H.toOrderedPattern.occurrenceFinset := by
    rw [H.toOrderedPattern_occurrenceFinset]
    exact hx
  obtain ⟨e, he⟩ := hcover x hxOrdered
  let j := (orderedFacetEquiv n).symm e
  have heq : orderedFacet j = e := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).apply_symm_apply e
  refine ⟨j, (mem_orderedDeletionToSimplex_iff D j _).2 ?_⟩
  rw [
    deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple,
    heq]
  exact he

/-- The deletion density of a transported colour is its ordered-face
density. -/
theorem colorDeletionDensity_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (orderedDeletionToSimplex D) j =
      OrderedPattern.faceDeletionDensity
        D (orderedFacet j) := by
  rw [SimplexHypergraph.colorDeletionDensity,
    OrderedPattern.faceDeletionDensity,
    card_orderedDeletionToSimplex]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedVectorFinTupleEquiv j)
  rw [hcard]

/-- Uniform ordered-face density bounds imply the same bound for total
normalized simplex deletion cost. -/
theorem normalizedDeletionCost_orderedDeletionToSimplex_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε) :
    SimplexHypergraph.normalizedDeletionCost
        (orderedDeletionToSimplex D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedVectorFinTupleEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((orderedDeletionToSimplex D j).card : ℝ) ≤
        ε * M := by
    have hdensity :=
      colorDeletionDensity_orderedDeletionToSimplex D j
    have hbound := hD (orderedFacet j)
    rw [← hdensity] at hbound
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hbound
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hbound
  have hcount :
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((orderedDeletionToSimplex D j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (ε * M) := by
        simp
  have hcapacity :
      SimplexHypergraph.deletionCapacity
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold SimplexHypergraph.deletionCapacity
    simp_rw [hface]
    simp
  rw [SimplexHypergraph.normalizedDeletionCost,
    hcapacity]
  have hdenom :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ hdenom).2
  calc
    (SimplexHypergraph.deletionCount
        (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := hcount
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring

/-- Uniform ordered removal for rank `n` patterns on `n + 1` equal vertex
classes implies uniform cyclic partite simplex removal on `n + 1` colours. -/
theorem hasUniformCyclicPartiteSimplexRemoval_of_ordered
    (n : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (n + 1) n) :
    HasUniformCyclicPartiteSimplexRemoval (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, hremove⟩ := hordered ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H hcount
  have horderedCount :
      H.toOrderedPattern.toWeighted.patternCount < c := by
    rw [H.toOrderedPattern_patternCount]
    exact hcount
  obtain ⟨D, hcover, hD⟩ :=
    hremove (ZMod N) H.toOrderedPattern horderedCount
  exact
    ⟨orderedDeletionToSimplex D,
      H.isSimplexCover_orderedDeletionToSimplex D hcover,
      normalizedDeletionCost_orderedDeletionToSimplex_le D hD⟩

/-- The successor-indexed bridge in the arithmetic-progression convention:
rank `r + 1` ordered removal on `r + 2` classes supplies the
`r + 2`-colour simplex-removal input. -/
theorem hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1)) :
    HasUniformCyclicPartiteSimplexRemoval (r + 2) := by
  simpa [Nat.add_assoc] using
    (hasUniformCyclicPartiteSimplexRemoval_of_ordered
      (r + 1) (by simpa [Nat.add_assoc] using hordered))

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Szemeredi/OrderedRemoval.lean` -/

section
/-!
# Dense Szemerédi consequences of ordered hypergraph removal

The equal-vertex bridge turns ordered rank-`r + 1` removal on `r + 2`
classes into cyclic partite simplex removal.  The standard arithmetic-
progression hypergraph construction then gives uniform dense and weighted
Szemerédi bounds.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Ordered rank-`r + 1` removal on `r + 2` equal classes gives a positive
uniform lower bound for dense cyclic `(r + 2)`-term progression counts. -/
theorem exists_uniformDenseAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c :=
  exists_uniformDenseAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

/-- A length-indexed formulation of the dense consequence. -/
theorem exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformDenseAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/Main.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Szemerédi's theorem

This file assembles the hypergraph-removal development into the quantitative
cyclic form of Szemerédi's theorem. For every progression length `k ≥ 2` and
positive density `δ`, there is a positive constant `c` such that every subset
of every nontrivial finite cyclic group having density at least `δ` contains
at least normalized mass `c` of `k`-term arithmetic progressions.
-/

namespace Wikipedia.SzemeredisTheorem

/-- **Szemerédi's theorem**, in uniform quantitative cyclic counting form. -/
theorem szemeredi (k : ℕ) (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ HasUniformDenseAPCount k δ c := by
  refine
    exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
      k hk ?_ hδ
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact hasUniformOrderedPatternRemoval_sourceFull
    k (k - 2) (by omega)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean` -/

section
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The unnormalized mass of all cyclic `k`-term progressions. -/
noncomputable def cyclicAPMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cyclicAPProduct k N f a d

/-- The unnormalized contribution from constant cyclic progressions. -/
noncomputable def cyclicAPDiagonalMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cyclicAPProduct k N f a 0

/-- The unnormalized mass of cyclic progressions with nonzero common
difference.  This is zero, rather than ill-defined, if no nonzero difference
exists. -/
noncomputable def cyclicAPOffDiagMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cyclicAPProduct k N f a d

@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

theorem cyclicAPDiagonalMass_eq_sum_pow
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPDiagonalMass k N f = ∑ a : ZMod N, f a ^ k := by
  simp [cyclicAPDiagonalMass]

/-- A pointwise bound `0 ≤ x ≤ B` controls its `k`th power by one copy of
`x` and `k - 1` copies of `B`. -/
theorem pow_le_pow_pred_mul
    {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ≤ B ^ (k - 1) * x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hB0 : 0 ≤ B := hx0.trans hxB
  have hpow : x ^ m ≤ B ^ m :=
    pow_le_pow_left₀ hx0 hxB m
  simpa [Nat.add_comm, pow_succ', Nat.add_sub_cancel, mul_comm] using
    (mul_le_mul_of_nonneg_right hpow hx0)

/-- The diagonal mass is bounded by the pointwise height to the power
`k-1`, times `N` times the mean.  This is the form used to show that
diagonal progressions are negligible for the W-tricked prime weight. -/
theorem cyclicAPDiagonalMass_le
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    cyclicAPDiagonalMass k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by
  rw [cyclicAPDiagonalMass_eq_sum_pow]
  calc
    ∑ a : ZMod N, f a ^ k ≤
        ∑ a : ZMod N, B ^ (k - 1) * f a := by
      exact Finset.sum_le_sum fun a _ =>
        pow_le_pow_pred_mul (hf0 a) (hfB a) hk
    _ = B ^ (k - 1) * ∑ a : ZMod N, f a := by
      rw [Finset.mul_sum]
    _ = B ^ (k - 1) * ((N : ℝ) * mean f) := by
      rw [← Fintype.card_mul_expect]
      simp [mean, ZMod.card]
    _ = B ^ (k - 1) * (N : ℝ) * mean f := by ring

/-- The full unnormalized mass splits into its diagonal and off-diagonal
parts. -/
theorem cyclicAPMass_eq_diagonal_add_offDiagMass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f := by
  classical
  rw [cyclicAPMass, cyclicAPDiagonalMass, cyclicAPOffDiagMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hdiagonal :
      ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d = 0),
        cyclicAPProduct k N f a d =
          cyclicAPProduct k N f a 0 := by
    apply Finset.sum_eq_single 0
    · intro d hd hd0
      exact (hd0 (Finset.mem_filter.mp hd).2).elim
    · simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun d : ZMod N => d = 0)
    (f := fun d => cyclicAPProduct k N f a d)]
  rw [hdiagonal]

/-- If the full mass strictly exceeds its diagonal contribution, the
off-diagonal mass is positive. -/
theorem cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ)
    (h :
      cyclicAPDiagonalMass k N f <
        cyclicAPMass k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  rw [cyclicAPMass_eq_diagonal_add_offDiagMass] at h
  linarith

/-- The normalized count is the full mass divided once for each cyclic
parameter. -/
theorem cyclicAPCount_eq_mass_div_div
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPCount k N f =
      cyclicAPMass k N f / (N : ℝ) / (N : ℝ) := by
  simp [cyclicAPCount, cyclicAPMass, mean₂, mean,
    Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_div]

/-- Clearing the two nonzero normalization factors recovers the full
unnormalized mass. -/
theorem cyclicAPMass_eq_mul_mul_count
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      (N : ℝ) * (N : ℝ) * cyclicAPCount k N f := by
  rw [cyclicAPCount_eq_mass_div_div]
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp

/-- A normalized count which dominates the normalized diagonal-height bound
already forces positive off-diagonal mass. -/
theorem cyclicAPOffDiagMass_pos_of_count
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hcount :
      B ^ (k - 1) * mean f <
        (N : ℝ) * cyclicAPCount k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  apply cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    cyclicAPDiagonalMass k N f ≤
        B ^ (k - 1) * (N : ℝ) * mean f :=
      cyclicAPDiagonalMass_le hk hf0 hfB
    _ = (N : ℝ) * (B ^ (k - 1) * mean f) := by ring
    _ < (N : ℝ) *
        ((N : ℝ) * cyclicAPCount k N f) :=
      mul_lt_mul_of_pos_left hcount hN
    _ = cyclicAPMass k N f := by
      rw [cyclicAPMass_eq_mul_mul_count]
      ring

/-- For nonnegative weights, a cyclic progression has positive product
exactly when each of its factors is positive. -/
theorem cyclicAPProduct_pos_iff_of_nonneg
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cyclicAPProduct k N f a d ↔
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  constructor
  · intro hprod j
    have hprod_ne :
        (∏ i : Fin k, f (cyclicAPTerm a d i)) ≠ 0 := by
      simpa only [cyclicAPProduct] using ne_of_gt hprod
    have hfactor_ne : f (cyclicAPTerm a d j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod_ne j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hf _) (Ne.symm hfactor_ne)
  · intro hfactor
    rw [cyclicAPProduct]
    exact Finset.prod_pos fun j _ => hfactor j

/-- Positive off-diagonal mass extracts a nonconstant cyclic progression on
which every factor of the nonnegative weight is strictly positive. -/
theorem exists_cyclicAP_of_offDiagMass_pos
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < cyclicAPOffDiagMass k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  classical
  rw [cyclicAPOffDiagMass] at hmass
  have houter_nonneg :
      ∀ a ∈ (Finset.univ : Finset (ZMod N)),
        0 ≤
          ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
            cyclicAPProduct k N f a d := by
    intro a _
    exact Finset.sum_nonneg fun d _ => cyclicAPProduct_nonneg hf a d
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg houter_nonneg).mp hmass
  have hinner_nonneg :
      ∀ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
        0 ≤ cyclicAPProduct k N f a d := by
    intro d _
    exact cyclicAPProduct_nonneg hf a d
  obtain ⟨d, hdmem, hdpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hinner_nonneg).mp ha
  refine ⟨a, d, (Finset.mem_filter.mp hdmem).2, ?_⟩
  exact (cyclicAPProduct_pos_iff_of_nonneg hf a d).mp hdpos

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/ShortInterval.lean` -/

section
/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The standard natural representative of the `j`th term of a cyclic
progression. -/
def cyclicAPVal {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val

@[simp]
theorem cyclicAPVal_cast {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (cyclicAPVal a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _

/-- Three points in an integer interval of width `U-L` have second
difference of absolute value at most twice that width. -/
theorem abs_secondDifference_le {L U z₀ z₁ z₂ : ℤ}
    (hz₀ : L ≤ z₀ ∧ z₀ ≤ U)
    (hz₁ : L ≤ z₁ ∧ z₁ ≤ U)
    (hz₂ : L ≤ z₂ ∧ z₂ ≤ U) :
    |z₂ - 2 * z₁ + z₀| ≤ 2 * (U - L) := by
  rw [abs_le]
  constructor <;> linarith

/-- The standard representatives of a cyclic progression supported in an
interval of width less than `N/2` have vanishing integer second
differences. -/
theorem cyclicAPVal_secondDifference_eq_zero {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ i : ℕ, i < k →
        L ≤ cyclicAPVal a d i ∧ cyclicAPVal a d i ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (cyclicAPVal a d (j + 2) : ℤ) -
        2 * cyclicAPVal a d (j + 1) +
        cyclicAPVal a d j = 0 := by
  let z : ℤ :=
    (cyclicAPVal a d (j + 2) : ℤ) -
      2 * cyclicAPVal a d (j + 1) +
      cyclicAPVal a d j
  apply Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) (x := z)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [z]
    push_cast
    simp only [cyclicAPVal_cast, Nat.cast_add, Nat.cast_ofNat]
    ring
  · exact lt_of_le_of_lt
      (abs_secondDifference_le
        (hmem j (by omega))
        (hmem (j + 1) (by omega))
        (hmem (j + 2) hj))
      hwidth

/-- A sequence with zero second differences is affine. -/
theorem eq_affine_of_secondDifference_zero
    (z : ℕ → ℤ) (k : ℕ)
    (hsecond :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro
      ring
  | one =>
      intro
      ring
  | more j ihj ihj₁ =>
      intro hj
      have hj₀ : j < k := by omega
      have hj₁ : j + 1 < k := by omega
      have hs := hsecond j hj
      rw [ihj hj₀, ihj₁ hj₁] at hs
      push_cast at hs ⊢
      linarith

/-- Short support converts all standard representatives of a cyclic
progression into one ordinary integer affine progression. -/
theorem cyclicAPVal_eq_affine {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∀ j : ℕ, j < k →
      (cyclicAPVal a d j : ℤ) =
        cyclicAPVal a d 0 +
          (j : ℤ) *
            ((cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0) := by
  apply eq_affine_of_secondDifference_zero
  intro j hj
  exact cyclicAPVal_secondDifference_eq_zero a d L U hmem hwidth j hj

/-- A nonzero cyclic common difference gives distinct zeroth and first
standard representatives. -/
theorem cyclicAPVal_one_sub_zero_ne_zero {N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) :
    (cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0 ≠ 0 := by
  intro hzero
  have hval : cyclicAPVal a d 1 = cyclicAPVal a d 0 := by
    exact_mod_cast sub_eq_zero.mp hzero
  have had : a + d = a := by
    apply ZMod.val_injective N
    simpa [cyclicAPVal] using hval
  apply hd
  apply add_left_cancel (a := a)
  simpa using had

/-- The integer common difference exposed by short-interval unwrapping is
nonzero whenever the cyclic difference is nonzero. -/
theorem cyclicAPVal_isIntegerAP {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ j : ℕ, j < k →
        (cyclicAPVal a d j : ℤ) =
          cyclicAPVal a d 0 + (j : ℤ) * s := by
  refine ⟨(cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0,
    cyclicAPVal_one_sub_zero_ne_zero a d hd, ?_⟩
  exact cyclicAPVal_eq_affine a d L U hmem hwidth

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem/UpperDensity.lean` -/

section
/-!
# From the finite cyclic theorem to the upper-density theorem

The finite theorem supplies many progressions in a dense subset of a cyclic
group.  We place a dense natural-number prefix in a cyclic group four times
as large.  At sufficiently large scales the quantitative lower bound beats
the diagonal progressions; a nonconstant cyclic progression can then be
unwrapped without modular wraparound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The inclusive prefix density appearing in the Lean Eval definition. -/
noncomputable def prefixDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)

/-- The elements of `A` in the inclusive prefix through `n`. -/
noncomputable def naturalPrefix (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (n + 1)).filter (fun k => k ∈ A)

theorem prefixDensity_eq_card (A : Set ℕ) (n : ℕ) :
    prefixDensity A n = (naturalPrefix A n).card / (n + 1 : ℕ) := by
  classical
  simp [prefixDensity, naturalPrefix, Set.indicator]

/-- The copy of a natural prefix inside `ZMod N`, selected by standard
representatives. -/
noncomputable def cyclicPrefix (A : Set ℕ) (n N : ℕ) [NeZero N] : Finset (ZMod N) :=
  by
    classical
    exact Finset.univ.filter fun x => x.val < n + 1 ∧ x.val ∈ A

theorem cyclicPrefix_card {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    (cyclicPrefix A n N).card = (naturalPrefix A n).card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod N))
  · intro x hx
    simp only [naturalPrefix, cyclicPrefix, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [ZMod.val_natCast_of_lt]
      · exact (Finset.mem_range.mp hx.1)
      · exact (Finset.mem_range.mp hx.1).trans_le hN
    · rw [ZMod.val_natCast_of_lt]
      · exact hx.2
      · exact (Finset.mem_range.mp hx.1).trans_le hN
  · intro x hx y hy hxy
    simp only [naturalPrefix, Finset.mem_filter] at hx hy
    have hxN : x < N := (Finset.mem_range.mp hx.1).trans_le hN
    have hyN : y < N := (Finset.mem_range.mp hy.1).trans_le hN
    have hval := congrArg (ZMod.val : ZMod N → ℕ) hxy
    simpa [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] using hval
  · intro z hz
    simp only [cyclicPrefix, Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · simp only [naturalPrefix, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hz.2.1, hz.2.2⟩
    · exact ZMod.natCast_zmod_val z

theorem mean_cyclicPrefix {A : Set ℕ} {n N : ℕ} [NeZero N]
    (hN : n + 1 ≤ N) :
    mean (finsetIndicator (cyclicPrefix A n N)) =
      prefixDensity A n * ((n + 1 : ℕ) / N : ℝ) := by
  rw [mean_finsetIndicator, cyclicPrefix_card hN, prefixDensity_eq_card]
  simp only [ZMod.card]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Unwrap a nonconstant cyclic progression contained in a short natural
interval.  If its integer common difference is negative, reverse the order
of its terms. -/
theorem exists_naturalAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/Wikipedia/SzemeredisTheorem.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

open scoped Topology

namespace SzemeredisTheorem

private theorem finitarySzemeredi_of_cyclic_count {k : ℕ} (hk : 1 < k) :
    FinitarySzemeredi k := by
  intro δ hδ
  let K : ℕ := max 2 k
  have hKtwo : 2 ≤ K := le_max_left 2 k
  have hkK : k ≤ K := le_max_right 2 k
  obtain ⟨c, hc, huniform⟩ :=
    Wikipedia.SzemeredisTheorem.szemeredi K hKtwo (by positivity : 0 < δ / 8)
  obtain ⟨m : ℕ, hm : 1 / c < m⟩ := exists_nat_gt (1 / c)
  refine ⟨max 1 m, by simp, ?_⟩
  intro N hN A hA hdense
  have hNpos : 0 < N := (le_max_left 1 m).trans hN
  let M : ℕ := 4 * (N + 1)
  letI : NeZero M := ⟨by dsimp [M]; omega⟩
  have hNM : N + 1 ≤ M := by
    dsimp [M]
    omega
  let S : Finset (ZMod M) :=
    Wikipedia.SzemeredisTheorem.cyclicPrefix (A : Set ℕ) N M
  have hprefix : Wikipedia.SzemeredisTheorem.naturalPrefix (A : Set ℕ) N = A := by
    ext x
    simp only [Wikipedia.SzemeredisTheorem.naturalPrefix, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hx
      have hxI := hA hx
      simp only [Finset.mem_Icc] at hxI
      exact ⟨by omega, hx⟩
  have hmean : δ / 8 ≤
      Wikipedia.SzemeredisTheorem.mean
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by
    rw [show S = Wikipedia.SzemeredisTheorem.cyclicPrefix (A : Set ℕ) N M from rfl,
      Wikipedia.SzemeredisTheorem.mean_cyclicPrefix (A := (A : Set ℕ)) hNM,
      Wikipedia.SzemeredisTheorem.prefixDensity_eq_card, hprefix]
    have hratio : (((N + 1 : ℕ) : ℝ) / (M : ℕ)) = 1 / 4 := by
      dsimp [M]
      push_cast
      field_simp
    rw [hratio]
    have htwo : N + 1 ≤ 2 * N := by omega
    have hscale : (δ / 2) * (N + 1 : ℕ) ≤ δ * (N : ℝ) := by
      calc
        (δ / 2) * (N + 1 : ℕ) ≤ (δ / 2) * (2 * N : ℕ) := by
          gcongr
        _ = δ * (N : ℝ) := by push_cast; ring
    have hdense' : δ / 2 ≤ (A.card : ℝ) / (N + 1 : ℕ) := by
      have hden : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      exact (le_div_iff₀ hden).2 (hscale.trans hdense)
    nlinarith
  have hcyclic :
      c ≤ Wikipedia.SzemeredisTheorem.cyclicAPCount K M
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) :=
    huniform M S hmean
  have hf0 : ∀ x : ZMod M,
      0 ≤ Wikipedia.SzemeredisTheorem.finsetIndicator S x := by
    intro x
    unfold Wikipedia.SzemeredisTheorem.finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod M,
      Wikipedia.SzemeredisTheorem.finsetIndicator S x ≤ 1 := by
    intro x
    unfold Wikipedia.SzemeredisTheorem.finsetIndicator
    split <;> norm_num
  have hmean_one : Wikipedia.SzemeredisTheorem.mean
      (Wikipedia.SzemeredisTheorem.finsetIndicator S) ≤ 1 :=
    Wikipedia.SzemeredisTheorem.mean_le_of_le_const hf1
  have hm_real : 1 / c < (N : ℝ) :=
    hm.trans_le (by exact_mod_cast ((le_max_right 1 m).trans hN))
  have hone_N : 1 < (M : ℝ) * c := by
    have hone : 1 < (N : ℝ) * c := (div_lt_iff₀ hc).mp hm_real
    have hNM' : (N : ℝ) ≤ M := by
      exact_mod_cast (show N ≤ M by dsimp [M]; omega)
    exact hone.trans_le (mul_le_mul_of_nonneg_right hNM' hc.le)
  have hoffdiag :
      0 < Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass K M
        (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by
    apply Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass_pos_of_count
      (by omega) hf0 hf1
    calc
      1 ^ (K - 1) * Wikipedia.SzemeredisTheorem.mean
          (Wikipedia.SzemeredisTheorem.finsetIndicator S) =
          Wikipedia.SzemeredisTheorem.mean
            (Wikipedia.SzemeredisTheorem.finsetIndicator S) := by simp
      _ ≤ 1 := hmean_one
      _ < (M : ℝ) * c := hone_N
      _ ≤ (M : ℝ) * Wikipedia.SzemeredisTheorem.cyclicAPCount K M
          (Wikipedia.SzemeredisTheorem.finsetIndicator S) :=
        mul_le_mul_of_nonneg_left hcyclic (by positivity)
  obtain ⟨a, d, hd, hpositive⟩ :=
    Wikipedia.SzemeredisTheorem.exists_cyclicAP_of_offDiagMass_pos hf0 hoffdiag
  have htermS : ∀ j : ℕ, j < K → a + (j : ZMod M) * d ∈ S := by
    intro j hj
    let jf : Fin K := ⟨j, hj⟩
    have hp := hpositive jf
    have hmem : Wikipedia.SzemeredisTheorem.cyclicAPTerm a d jf ∈ S := by
      by_contra hnot
      rw [Wikipedia.SzemeredisTheorem.finsetIndicator_of_not_mem hnot] at hp
      linarith
    simpa [Wikipedia.SzemeredisTheorem.cyclicAPTerm, jf] using hmem
  have htermData : ∀ j : ℕ, j < K →
      Wikipedia.SzemeredisTheorem.cyclicAPVal a d j < N + 1 ∧
        Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ∈ (A : Set ℕ) := by
    intro j hj
    have hmem := htermS j hj
    simpa [S, Wikipedia.SzemeredisTheorem.cyclicPrefix,
      Wikipedia.SzemeredisTheorem.cyclicAPVal] using hmem
  have hinterval : ∀ j : ℕ, j < K →
      (0 : ℤ) ≤ Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ∧
        Wikipedia.SzemeredisTheorem.cyclicAPVal a d j ≤ (N : ℤ) := by
    intro j hj
    have hmem := htermData j hj
    constructor
    · positivity
    · exact_mod_cast (Nat.lt_succ_iff.mp hmem.1)
  have hwidth : 2 * ((N : ℤ) - 0) < (M : ℤ) := by
    dsimp [M]
    push_cast
    omega
  obtain ⟨x, step, hstep, hprogression⟩ :=
    Wikipedia.SzemeredisTheorem.exists_naturalAP_of_cyclicAPVal_shortInterval
      a d hd hKtwo 0 N hinterval hwidth
      (fun j hj => (htermData j hj).2)
  exact not_isAPOfLengthFree_of_parameters hk hstep
    (fun j hj => by simpa [Nat.mul_comm] using hprogression j (hj.trans_le hkK))

theorem szemeredis_theorem (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) :=
  tendsto_maxCard_div_of_finitarySzemeredi
    (finitarySzemeredi_of_cyclic_count hk)

end SzemeredisTheorem

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos139.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 139.
https://www.erdosproblems.com/forum/thread/139

Informal authors:
- Endre Szemerédi

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos139.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/139.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

open scoped Topology

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/-- Erdős Problem 139: the largest `k`-AP-free subset of `{1, ..., N}`
has cardinality `o(N)`. -/
theorem erdos_139 (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) :=
  SzemeredisTheorem.szemeredis_theorem k hk

end

#print axioms erdos_139
-- 'Erdos139.erdos_139' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos139
