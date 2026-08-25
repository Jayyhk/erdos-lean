import Mathlib

set_option linter.flexible false

namespace Erdos658

/-
# Problem Description

Erdős Problem 658. `erdos_658` is proved unconditionally here: the Frankl–Rödl theorem,
previously assumed in this repository as the axiom `frankl_roedl_theorem`, is proved
rather than assumed.

The original proof was found by: plby (github.com/plby/lean-proofs), file
`src/latest/ErdosProblems/Erdos658.lean` together with its 81-module import closure,
which includes `Util/FranklRodl` and the `Wikipedia/SzemeredisTheorem` hypergraph-removal
development.

Flattened single-file vendoring of that closure, concatenated in dependency order with
project-internal imports removed, leaving `Mathlib` as the only import. Each upstream
module keeps its own `section` so that file-scoped `variable`/`open` declarations cannot
leak across the concatenation, and is named in the comment that opens it. The root
module's own `namespace Erdos658` is dropped in favour of the single outer one. No
mathematical content is changed.
-/

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Finite/Mean.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Finite/ProductMean.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Finite/CauchySchwarz.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleEnvelopeSelection.lean` -/

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

open Filter Topology

/-! ## The equality schedule -/

/-! ## Positivity and monotonicity -/

/-! ## The envelope interface -/

/-! ## Vanishing at the origin and finite-horizon selection -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean` -/

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

/-! ## Density-scaled finite-horizon selection -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Finite/Bonferroni.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/ConditionalAverage.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FacePartition.lean` -/

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

end FacePartition

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Energy.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Regularity.lean` -/

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

end FaceRegularityState

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/CutDiscrepancy.lean` -/

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

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/GeneralizedConvolution.lean` -/

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

/-- The product weight associated to a family of deleted-coordinate tests. -/
def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean` -/

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

open scoped Pointwise

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean` -/

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

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/

/-! ## Bounded combinations and approximation of positive part -/

/-! ## Quantitative positive-part correlation -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakRegularity.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FamilyRegularity.lean` -/

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

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]
  [Fintype ι] [DecidableEq ι]

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GeneratorCells.lean` -/

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

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPattern.lean` -/

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
theorem orderedFaceTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = y := by
  rw [← splitOrderedFaceEquiv_fst]
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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/Count.lean` -/

section

/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/LinearForms/Basic.lean` -/

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

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Simplex.lean` -/

section

/-!
# Partite weighted simplices

The dense and relative Szemerédi arguments are organized as counting lemmas
for a `(k-1)`-uniform, `k`-partite simplex.  An edge of colour `j` depends on
every vertex coordinate except `j`.  Keeping that dependency in the type
prevents accidental use of the omitted coordinate and matches the dependent
index used by the CFZ blow-up forms.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/APCorrespondence.lean` -/

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

/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/CutTransport.lean` -/

section

/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/APCut.lean` -/

section

/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean` -/

section

/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/APSimplexCut.lean` -/

section

/-!
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexCounting.lean` -/

section

/-!
# Stable weighted simplex counts

Relative counting will eventually use cut discrepancy and densification.
This file records the elementary endpoint: uniformly close edge weights in
`[0,1]` have close simplex counts.  The proof is the finite telescoping
estimate for products, followed by averaging.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakCounting.lean` -/

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

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedCounting.lean` -/

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

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRegularizedCells.lean` -/

section

/-!
# Generator-retaining regularization for complete ordered patterns

This packages simultaneous weak regularization of every increasing
rank-`r` face on `k` vertex classes.  Besides the counting conclusion, it
retains the Boolean face-cut generators.  Consequently every structured
top atom is an explicit union of products of rank-`r - 1` cells.
-/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Unweighted.lean` -/

section

/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Removal.lean` -/

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

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StructuredCleaning.lean` -/

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

open scoped BigOperators

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedCellLifting.lean` -/

section

/-!
# Lower-rank cells and lifted ordered-pattern deletions

This file is the exact combinatorial interface for the rank induction in
ordered hypergraph removal.  Deleting one coordinate from an increasing
rank-`r` face gives an increasing rank-`r - 1` face.  The lower cells
generated by a structured top atom therefore assemble into a complete
ordered lower-rank pattern.
-/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedBoundaryPartition.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedAtomEnergy.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/PreliminaryOrderedRegularity.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/BoundaryBernoulli.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FullOrderedRegularity.lean` -/

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
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

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

/-! ## Rank schedules and simultaneous preliminary regularity -/

/-- One tolerance for every adjacent rank pair `(j, j + 1)`. -/
abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

/-! ## The top-down all-rank construction -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedGoodAtoms.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseAtomBridge.lean` -/

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

/-! ## Linear transfer of cut regularity -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedEnergy.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemoval.lean` -/

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

/-! ## Ordered specialization -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseOrderedRemoval.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/BundleCountingRecurrence.lean` -/

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

open scoped BigOperators

/-! ## Edge-dependent recurrence errors -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedConfigurationCounting.lean` -/

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

/-! ## Quantitative full-count lower bound and positivity -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseConfigurationCounting.lean` -/

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

/-! ## Rankwise full-count lower bounds -/

/-! ## Fine-regular complexity corollaries -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/ConfigurationWeightedDefect.lean` -/

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

/-! ## Idempotence of configuration indicators -/

/-! ## The mixed defect with its remaining-count factor -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationBridge.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationStep.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFrozenUniformity.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFrozenCut.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedFullBoundary.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleSourceGoodnessBridge.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleCounting.lean` -/

section

/-!
# Source-full generalized bundle counting

This file assembles the source-full goodness and preliminary-regularity
certificates into the relative generalized bundle-counting theorem.  The
common density floor is `a`, while both analytic errors are `t ^ 2`; the
explicit schedule `bundleCommonEnvelopeError a t` then controls every
closed bundle pulled back from the ordered configuration.
-/

open scoped BigOperators

/-! ## The common density floor on base edges -/

/-! ## Relative counting for every closed pullback bundle -/

/-! ## Initial bundle and positivity -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StrongFullOrderedRegularity.lean` -/

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

open scoped BigOperators

/-! ## Bounded-test all-rank regularity -/

/-! ## Canonical precomputed tower -/

/-! ## Recursive ambient-independent complexity bound -/

/-! ## Fixed-upper-family all-rank energy -/

/-! ## Moving-upper bridge and the exact loss -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StrongOrderedComplexRegularity.lean` -/

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

/-! ## Existence by downward rank induction -/

/-! ## Quantitative consequences -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseTargetRegularity.lean` -/

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

/-! ## Total coarse-target gap -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/AdaptiveCoarseTargetRegularity.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalParameters.lean` -/

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

/-! ## Bridge from a compatible strong certificate -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GrowthFunctionRegularity.lean` -/

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

theorem growthRegularityStepTolerance_pos
    (F : NatGrowthFunction) (M : ℕ) :
    0 < growthRegularityStepTolerance F M := by
  unfold growthRegularityStepTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)

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

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GrowthFunctionComplexRegularity.lean` -/

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

/-! ## Finite descending growth hierarchies -/

/-! ## Rankwise triangular schedules -/

/-! ## All-rank growth-function certificate -/

/-! ## Existence by the top-down fixed-upper composition -/

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/TowerDominatingGrowth.lean` -/

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

/-! ## One majorant stage -/

/-! ## Iterated finite-stage closure -/

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

/-! ### One hierarchy containing all independently selected layers -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullCoarseTargetRegularity.lean` -/

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

end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullRankwiseBundleCounting.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullGoodAtoms.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPatternPartition.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalTheorem.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullOrderedRemoval.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalParameters.lean` -/

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

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalAssembly.lean` -/

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

/-! ## Conditional uniform ordered removal -/

end Wikipedia.SzemeredisTheorem

end

/-! ### Upstream module `src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalAssembly.lean` -/

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

/-! ### Upstream module `src/latest/Util/FranklRodl.lean` -/

section

/-!
# The Frankl–Rödl unique-clique bound

The rank-three, four-partite hypergraph-removal theorem supplies the analytic
input. Uniqueness of the clique containing each edge makes every face projection
injective on tetrahedra; removal then bounds the original edge set.
-/

open Finset
open scoped BigOperators

/-- The unique-clique form of the Frankl–Rödl theorem for 3-uniform hypergraphs. -/
def Theorem_2_2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
    ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card ≥ n₀ →
    (∀ e ∈ E, e.card = 3 ∧ e ⊆ V) →
    (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ 4 ∧
      (∀ t ⊆ K, t.card = 3 → t ∈ E) ∧ e ⊆ K) →
    (E.card : ℝ) < ε * (V.card : ℝ) ^ 3

namespace FranklRodl

open Wikipedia.SzemeredisTheorem

private theorem pair_in_face :
    ∀ i j : Fin 4, ∃ e : OrderedFace 4 3, ∃ a b : Fin 3,
      e a = i ∧ e b = j := by
  intro i j
  have h : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := h i j
  have hi : i ∈ Set.range (Fin.succAboveOrderEmb k) := by
    simpa [Fin.range_succAboveOrderEmb] using hki.symm
  have hj : j ∈ Set.range (Fin.succAboveOrderEmb k) := by
    simpa [Fin.range_succAboveOrderEmb] using hkj.symm
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  exact ⟨Fin.succAboveOrderEmb k, a, b, ha, hb⟩

private theorem three_set_is_face :
    ∀ S : Finset (Fin 4), S.card = 3 →
      ∃ e : OrderedFace 4 3, univ.image e = S := by
  intro S hS
  exact ⟨S.orderEmbOfFin hS, S.image_orderEmbOfFin_univ hS⟩

private theorem outside_face_unique :
    ∀ e : OrderedFace 4 3, ∀ i j : Fin 4,
      (∀ a, e a ≠ i) → (∀ a, e a ≠ j) → i = j := by
  intro e i j hi hj
  have h01 := e.strictMono (show (0 : Fin 3) < 1 by decide)
  have h12 := e.strictMono (show (1 : Fin 3) < 2 by decide)
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  have hj0 := hj 0
  have hj1 := hj 1
  have hj2 := hj 2
  omega

variable {V : Finset ℕ}

private def vertices {r : ℕ} (x : Fin r → V) : Finset ℕ :=
  univ.image fun i => (x i : ℕ)

private theorem vertices_subset {r : ℕ} (x : Fin r → V) :
    vertices x ⊆ V := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact (x i).property

private theorem vertices_card {r : ℕ} {x : Fin r → V}
    (hx : Function.Injective x) : (vertices x).card = r := by
  rw [vertices, card_image_of_injective]
  · simp
  · exact Subtype.val_injective.comp hx

private def pattern (V : Finset ℕ) (E : Finset (Finset ℕ)) :
    OrderedPattern V 4 3 where
  edge _ y := Function.Injective y ∧ vertices y ∈ E

private theorem occurrence_injective {E : Finset (Finset ℕ)}
    {x : Fin 4 → V} (hx : (pattern V E).IsOccurrence x) :
    Function.Injective x := by
  intro i j hij
  obtain ⟨e, a, b, ha, hb⟩ := pair_in_face i j
  have hab : a = b := (hx e).1 (by simpa [orderedFaceTuple, ha, hb] using hij)
  simpa [ha, hb] using congrArg e hab

private theorem face_vertices_subset (x : Fin 4 → V) (e : OrderedFace 4 3) :
    vertices (orderedFaceTuple e x) ⊆ vertices x := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨e i, mem_univ _, rfl⟩

private theorem three_subset_is_face {x : Fin 4 → V}
    (hx : Function.Injective x) {t : Finset ℕ}
    (ht : t ⊆ vertices x) (hcard : t.card = 3) :
    ∃ e : OrderedFace 4 3, vertices (orderedFaceTuple e x) = t := by
  classical
  let S : Finset (Fin 4) := univ.filter fun i => (x i : ℕ) ∈ t
  have himage : S.image (fun i => (x i : ℕ)) = t := by
    ext a
    simp only [mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (mem_filter.mp hi).2
    · intro ha
      obtain ⟨i, _, hi⟩ := mem_image.mp (ht ha)
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa [hi] using ha⟩, hi⟩
  have hS : S.card = 3 := by
    rw [← hcard, ← himage]
    exact (card_image_of_injective S (Subtype.val_injective.comp hx)).symm
  obtain ⟨e, he⟩ := three_set_is_face S hS
  refine ⟨e, ?_⟩
  rw [← himage, ← he, image_image]
  rfl

private def IsClique (V : Finset ℕ) (E : Finset (Finset ℕ))
    (K : Finset ℕ) : Prop :=
  K ⊆ V ∧ 4 ≤ K.card ∧ ∀ t ⊆ K, t.card = 3 → t ∈ E

private theorem occurrence_clique {E : Finset (Finset ℕ)}
    {x : Fin 4 → V} (hx : (pattern V E).IsOccurrence x) :
    IsClique V E (vertices x) := by
  have hinj := occurrence_injective hx
  refine ⟨vertices_subset x, (vertices_card hinj).ge, ?_⟩
  intro t ht hcard
  obtain ⟨e, rfl⟩ := three_subset_is_face hinj ht hcard
  exact (hx e).2

private theorem face_projection_injective {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    (e : OrderedFace 4 3) :
    Set.InjOn (fun x : Fin 4 → V => orderedFaceTuple e x)
      ↑(pattern V E).occurrenceFinset := by
  classical
  intro x hx y hy hxy
  change orderedFaceTuple e x = orderedFaceTuple e y at hxy
  have hx' := ((pattern V E).mem_occurrenceFinset x).mp hx
  have hy' := ((pattern V E).mem_occurrenceFinset y).mp hy
  obtain ⟨K, _, hK⟩ := hunique _ (hx' e).2
  have hKx := hK _ ⟨occurrence_clique hx', face_vertices_subset x e⟩
  have hKy := hK _ ⟨occurrence_clique hy', by
    rw [hxy]
    exact face_vertices_subset y e⟩
  have hrange : vertices x = vertices y := hKx.trans hKy.symm
  have hxi := occurrence_injective hx'
  funext i
  by_cases hi : ∃ a, e a = i
  · obtain ⟨a, rfl⟩ := hi
    exact congrFun hxy a
  · have hmem : (x i : ℕ) ∈ vertices y := by
      rw [← hrange]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := mem_image.mp hmem
    have hj' : y j = x i := Subtype.ext hj
    have hji : j = i := outside_face_unique e j i
      (by
        intro a ha
        have hval : x (e a) = x i :=
          (congrFun hxy a).trans (by simpa [orderedFaceTuple, ha] using hj')
        exact hi ⟨a, hxi hval⟩)
      (by simpa using hi)
    simpa [hji] using hj'.symm

private theorem occurrence_card_le {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K) :
    (pattern V E).occurrenceFinset.card ≤ V.card ^ 3 := by
  classical
  let e : OrderedFace 4 3 := Fin.succAboveOrderEmb 0
  calc
    (pattern V E).occurrenceFinset.card ≤
        (univ : Finset (Fin 3 → V)).card :=
      card_le_card_of_injOn (orderedFaceTuple e)
        (fun _ _ => mem_univ _) (face_projection_injective hunique e)
    _ = V.card ^ 3 := by simp

private theorem edge_in_occurrence {E : Finset (Finset ℕ)}
    (hE : ∀ t ∈ E, t.card = 3)
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    {t : Finset ℕ} (ht : t ∈ E) :
    ∃ x ∈ (pattern V E).occurrenceFinset, ∃ e : OrderedFace 4 3,
      vertices (orderedFaceTuple e x) = t := by
  classical
  obtain ⟨K, ⟨hKV, hKcard, hKE⟩, htK⟩ := (hunique t ht).exists
  obtain ⟨L, htL, hLK, hLcard⟩ :=
    exists_subsuperset_card_eq htK (by have := hE t ht; omega : t.card ≤ 4) hKcard
  let x : Fin 4 → V := fun i =>
    ⟨L.orderEmbOfFin hLcard i, hKV (hLK (L.orderEmbOfFin_mem hLcard i))⟩
  have hxi : Function.Injective x := by
    intro i j hij
    exact (L.orderEmbOfFin hLcard).injective (congrArg (fun z : V => (z : ℕ)) hij)
  have hxL : vertices x = L := L.image_orderEmbOfFin_univ hLcard
  have hx : (pattern V E).IsOccurrence x := by
    intro e
    refine ⟨hxi.comp e.injective, hKE _ ?_ (vertices_card (hxi.comp e.injective))⟩
    exact (face_vertices_subset x e).trans (by simpa [hxL] using hLK)
  refine ⟨x, ((pattern V E).mem_occurrenceFinset x).mpr hx, ?_⟩
  exact three_subset_is_face hxi (by simpa [hxL] using htL) (hE t ht)

private theorem edge_card_le {E : Finset (Finset ℕ)}
    (hE : ∀ t ∈ E, t.card = 3)
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K) :
    E.card ≤ Fintype.card (OrderedFace 4 3) * (pattern V E).occurrenceFinset.card := by
  classical
  have hsub : E ⊆ (pattern V E).occurrenceFinset.biUnion
      (fun x => univ.image fun e : OrderedFace 4 3 => vertices (orderedFaceTuple e x)) := by
    intro t ht
    obtain ⟨x, hx, e, he⟩ := edge_in_occurrence hE hunique ht
    exact mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨e, mem_univ _, he⟩⟩
  calc
    E.card ≤ _ := card_le_card hsub
    _ ≤ ∑ x ∈ (pattern V E).occurrenceFinset,
        (univ.image fun e : OrderedFace 4 3 => vertices (orderedFaceTuple e x)).card :=
      card_biUnion_le
    _ ≤ ∑ _x ∈ (pattern V E).occurrenceFinset, Fintype.card (OrderedFace 4 3) := by
      apply sum_le_sum
      intro x _
      exact card_image_le.trans_eq (card_univ)
    _ = _ := by simp [mul_comm]

private theorem occurrence_card_le_deletions {E : Finset (Finset ℕ)}
    (hunique : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K)
    (D : OrderedPattern.DeletionFamily (G := V) 4 3)
    (hD : (pattern V E).IsCover D) :
    (pattern V E).occurrenceFinset.card ≤ ∑ e, (D e).card := by
  classical
  have hsub : (pattern V E).occurrenceFinset ⊆
      univ.biUnion (fun e : OrderedFace 4 3 =>
        (pattern V E).occurrenceFinset.filter fun x => orderedFaceTuple e x ∈ D e) := by
    intro x hx
    obtain ⟨e, he⟩ := hD x hx
    exact mem_biUnion.mpr ⟨e, mem_univ _, mem_filter.mpr ⟨hx, he⟩⟩
  calc
    (pattern V E).occurrenceFinset.card ≤ _ := card_le_card hsub
    _ ≤ ∑ e : OrderedFace 4 3,
        ((pattern V E).occurrenceFinset.filter fun x => orderedFaceTuple e x ∈ D e).card :=
      card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro e _
      exact card_le_card_of_injOn (orderedFaceTuple e)
        (fun _ hx => (mem_filter.mp hx).2)
        (fun _ hx _ hy hxy => face_projection_injective hunique e
          (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy)

end FranklRodl

open FranklRodl Wikipedia.SzemeredisTheorem in
/-- Frankl–Rödl's unique-clique bound, proved from uniform hypergraph removal. -/
theorem frankl_roedl_theorem : Theorem_2_2 := by
  classical
  intro ε hε
  let M := Fintype.card (OrderedFace 4 3)
  have hM : (0 : ℝ) < M := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨Fin.succAboveOrderEmb (0 : Fin 4)⟩ : 0 < Fintype.card (OrderedFace 4 3))
  let η := ε / (2 * (M : ℝ) ^ 2)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨c, hc, hrem⟩ :=
    hasUniformOrderedPatternRemoval_sourceFull 4 2 (by omega) η hη
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (1 / c))
  refine ⟨n₀, ?_⟩
  intro V E hV hE hunique
  have hn : (1 : ℝ) < V.card := by
    exact ((le_max_left 1 (1 / c)).trans_lt hn₀).trans_le (by exact_mod_cast hV)
  have hnpos : (0 : ℝ) < V.card := by linarith
  have hVpos : 0 < V.card := by exact_mod_cast hnpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  let : Nonempty V := ⟨⟨v, hv⟩⟩
  have hu : ∀ t ∈ E, ∃! K, IsClique V E K ∧ t ⊆ K := by
    simpa only [IsClique, and_assoc] using hunique
  have hcount : (pattern V E).toWeighted.patternCount < c := by
    rw [OrderedPattern.toWeighted_patternCount_eq]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
    have hupper : ((pattern V E).occurrenceFinset.card : ℝ) ≤ (V.card : ℝ) ^ 3 := by
      exact_mod_cast occurrence_card_le hu
    have hlarge : 1 / c < (V.card : ℝ) :=
      ((le_max_right 1 (1 / c)).trans_lt hn₀).trans_le (by exact_mod_cast hV)
    have hinv : 1 / (V.card : ℝ) < c := by
      rw [div_lt_iff₀ hnpos]
      have := (div_lt_iff₀ hc).mp hlarge
      nlinarith
    calc
      ((pattern V E).occurrenceFinset.card : ℝ) / (V.card : ℝ) ^ 4 ≤
          (V.card : ℝ) ^ 3 / (V.card : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right hupper (by positivity)
      _ = 1 / (V.card : ℝ) := by field_simp
      _ < c := hinv
  obtain ⟨D, hcover, hsmall⟩ := hrem V (pattern V E) hcount
  have hD : ∀ e, ((D e).card : ℝ) ≤ η * (V.card : ℝ) ^ 3 := by
    intro e
    have h := hsmall e
    simp only [OrderedPattern.faceDeletionDensity, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] at h
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (V.card : ℝ) ^ 3)).mp h
  have hC : ((pattern V E).occurrenceFinset.card : ℝ) ≤
      (M : ℝ) * (η * (V.card : ℝ) ^ 3) := by
    calc
      ((pattern V E).occurrenceFinset.card : ℝ) ≤ ∑ e, ((D e).card : ℝ) := by
        exact_mod_cast occurrence_card_le_deletions hu D hcover
      _ ≤ ∑ _e : OrderedFace 4 3, η * (V.card : ℝ) ^ 3 :=
        sum_le_sum fun e _ => hD e
      _ = _ := by simp [M]
  have hEC : (E.card : ℝ) ≤ (M : ℝ) * (pattern V E).occurrenceFinset.card := by
    exact_mod_cast edge_card_le (fun t ht => (hE t ht).1) hu
  calc
    (E.card : ℝ) ≤ (M : ℝ) * ((M : ℝ) * (η * (V.card : ℝ) ^ 3)) :=
      hEC.trans (mul_le_mul_of_nonneg_left hC hM.le)
    _ = ε / 2 * (V.card : ℝ) ^ 3 := by dsimp [η]; field_simp
    _ < ε * (V.card : ℝ) ^ 3 :=
      mul_lt_mul_of_pos_right (by linarith) (pow_pos hnpos _)

end

/-! ### Upstream module `src/latest/ErdosProblems/Erdos658.lean` -/

section

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 658.
https://www.erdosproblems.com/forum/thread/658

Informal authors:
- József Solymosi
- Peter Frankl
- Vojtěch Rödl

Formal authors:
- Aristotle
- John Jennings

URLs:
- https://www.erdosproblems.com/forum/thread/658#post-5654
- https://www.erdosproblems.com/forum/thread/658#post-5677
- https://gist.githubusercontent.com/JohnEdwardJennings/ca7d49761fb51d28613bafc956742fbc/raw/c326fd7918276292e641af92c32d3ecbe3c31ee0/Erdos658.lean
- https://gist.githubusercontent.com/JohnEdwardJennings/ca7d49761fb51d28613bafc956742fbc/raw/93dbf493e26aa377f7e78390903be146745fa7ec/Erdos658.lean
-/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/

/-!
# Erdős Problem 658: Squares in Dense Lattice Subsets

This file formalizes Theorem 1.1 from J. Solymosi's paper
"A Note on a Question of Erdős and Graham" (Combinatorics,
Probability and Computing, 2004), along with its dependencies.

## Main Results

* `Theorem_1_1` : For any δ > 0, sufficiently large N
  guarantees every subset of [N]² of size ≥ δN² contains an
  axis-aligned square.
* `Theorem_1_2` : The 3D analogue for quadruples of the
  form (1.1).
* `Proposition_1_3` : Theorem 1.2 implies Theorem 1.1
  (via a lifting argument).
* `Theorem_2_2` : The Frankl–Rödl theorem on linear
  3-uniform hypergraphs (proved from hypergraph removal).
* `Conjecture_2_1` : The generalization to k-uniform
  hypergraphs (stated).

## References

* J. Solymosi, *A Note on a Question of Erdős and Graham*,
  2004
* P. Frankl and V. Rödl, *Extremal problems on set systems*,
  2002
-/

section
open Finset

/-! ## §1. Grid Definitions -/

/-- The grid `[N] = {0, 1, …, N-1}` as a `Finset ℤ`. -/
def gridRange (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (↑· : ℕ → ℤ)

/-- The grid `[N]²`. -/
def grid2 (N : ℕ) : Finset (ℤ × ℤ) :=
  gridRange N ×ˢ gridRange N

/-- The grid `[N]³`. -/
def grid3 (N : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  gridRange N ×ˢ (gridRange N ×ˢ gridRange N)

/-! ## §2. Pattern Definitions -/

/-- A set `S ⊆ ℤ²` contains an axis-aligned square with nonzero side length. -/
def ContainsSquare (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ a b d : ℤ, d ≠ 0 ∧
    (a, b) ∈ S ∧ (a + d, b) ∈ S ∧
    (a, b + d) ∈ S ∧ (a + d, b + d) ∈ S

/-- A set `S ⊆ ℤ³` contains a quadruple of the form
`{(a,b,c), (a+d,b,c), (a,b+d,c), (a+d,b+d,c+d)}` with `d ≠ 0`. -/
def ContainsQuadruple (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ a b c d : ℤ, d ≠ 0 ∧
    (a, b, c) ∈ S ∧ (a + d, b, c) ∈ S ∧
    (a, b + d, c) ∈ S ∧ (a + d, b + d, c + d) ∈ S

/-! ## §3. Statements of Theorem 2.2 and Conjecture 2.1

Theorem 2.2 (Frankl–Rödl) is proved in `Util.FranklRodl` and is
taken as a hypothesis in the proofs that follow.
Conjecture 2.1 is its generalization. -/

/-- **Conjecture 2.1** (Frankl–Rödl conjecture):
For any integer `k ≥ 2`, if `G` is a `k`-uniform hypergraph such that every edge
belongs to exactly one complete subgraph (of size ≥ `k+1`), then
`|E(G)| = o(|V(G)|^k)`.
See [Solymosi, *A Note on a Question of Erdős and Graham*, Conjecture 2.1]. -/
def Conjecture_2_1 : Prop :=
  ∀ (k : ℕ), k ≥ 2 → ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
    ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card ≥ n₀ →
    (∀ e ∈ E, e.card = k ∧ e ⊆ V) →
    (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ k + 1 ∧
      (∀ t ⊆ K, t.card = k → t ∈ E) ∧ e ⊆ K) →
    (E.card : ℝ) < ε * (V.card : ℝ) ^ k

/-! ## §4. Vertex Encoding and Hypergraph Construction

For a point `(a, b, c) ∈ [N]³`, the four plane families assign indices:
- Family 0: `c`          (plane `z = c`)
- Family 1: `-a + c`     (plane `-x + z = -a + c`)
- Family 2: `-b + c`     (plane `-y + z = -b + c`)
- Family 3: `a + b - c`  (plane `x + y - z = a + b - c`)

We encode `(family f, plane index i)` as the natural number
`f * (3 * N) + (i + N).toNat`, placing each family in a disjoint range. -/

/-- Encode vertex `(family f, plane index i)` as a natural number. -/
def encVertex (N : ℕ) (f : ℕ) (i : ℤ) : ℕ :=
  f * (3 * N) + (i + ↑N).toNat

/-- The four encoded vertices through a point `(a, b, c)`. -/
def vertexOf (N : ℕ) (a b c : ℤ) : Fin 4 → ℕ
  | 0 => encVertex N 0 c
  | 1 => encVertex N 1 (-a + c)
  | 2 => encVertex N 2 (-b + c)
  | 3 => encVertex N 3 (a + b - c)

/-- The four edges (3-element subsets) generated by a point `(a, b, c)`.
Each edge omits one of the four families. -/
def pointEdges (N : ℕ) (a b c : ℤ) : Finset (Finset ℕ) :=
  let v := vertexOf N a b c
  {{v 0, v 1, v 2}, {v 0, v 1, v 3},
   {v 0, v 2, v 3}, {v 1, v 2, v 3}}

/-- The full edge set of the hypergraph constructed from `S ⊆ [N]³`. -/
def edgeSet (N : ℕ) (S : Finset (ℤ × ℤ × ℤ)) : Finset (Finset ℕ) :=
  S.biUnion fun p => pointEdges N p.1 p.2.1 p.2.2

/-- The vertex set (a superset of all vertices that appear). -/
def vertexSet (N : ℕ) : Finset ℕ :=
  Finset.range (12 * N)

/-- The family of a vertex `v` (quotient `v / (3 * N)`). -/
def familyOf (N : ℕ) (v : ℕ) : ℕ := v / (3 * N)

/-! ## §5. Encoding Lemmas -/

/-- `gridRange N` has cardinality `N`. -/
lemma gridRange_card (N : ℕ) : (gridRange N).card = N := by
  simp [gridRange, Finset.card_image_of_injective _ Nat.cast_injective]

/-- Membership in `gridRange N` is equivalent to `0 ≤ x ∧ x < N`. -/
lemma mem_gridRange {N : ℕ} {x : ℤ} :
    x ∈ gridRange N ↔ 0 ≤ x ∧ x < N := by
  simp only [gridRange, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨Int.natCast_nonneg n, Int.ofNat_lt.mpr hn⟩
  · rintro ⟨h0, hN⟩
    exact ⟨x.toNat, by omega, by omega⟩

/-- `encVertex` lands in the correct family. -/
lemma encVertex_family {N : ℕ} (hN : N ≥ 1) {f : ℕ} (_hf : f < 4) {i : ℤ}
    (_hi : 0 ≤ i + ↑N) (hi' : i + ↑N < 3 * ↑N) :
    familyOf N (encVertex N f i) = f := by
  unfold familyOf encVertex
  rw [Nat.add_div] <;> norm_num
  · rw [Nat.mul_div_cancel _ (by positivity), if_neg]
      <;> norm_num
    · grind
    · exact Nat.mod_lt _ (by positivity)
  · linarith

/-- `encVertex` is bounded by `12 * N`. -/
lemma encVertex_lt {N : ℕ} (hN : N ≥ 1) {f : ℕ} (hf : f < 4)
    {i : ℤ} (hi : 0 ≤ i + ↑N) (hi' : i + ↑N < 3 * ↑N) :
    encVertex N f i < 12 * N := by
  unfold encVertex
  interval_cases f <;> linarith [Int.toNat_of_nonneg hi]

/-! ## §6. Edge Properties -/

/-- The vertices of an edge from a point in `[N]³` are distinct. -/
lemma vertexOf_injective {N : ℕ} (hN : N ≥ 1) {a b c : ℤ}
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N) :
    Function.Injective (vertexOf N a b c) := by
  unfold vertexOf
  intro x y
  fin_cases x <;> fin_cases y <;> simp +decide
  all_goals
    unfold encVertex
    omega

/-- Each edge from a point in `[N]³` has cardinality 3. -/
lemma edge_card_three {N : ℕ} (hN : N ≥ 1) {a b c : ℤ}
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N) :
    ∀ e ∈ pointEdges N a b c, e.card = 3 := by
  unfold pointEdges
  simp +decide
  have h_distinct : Function.Injective (vertexOf N a b c) :=
    vertexOf_injective hN ha hb hc
  simp +decide [h_distinct.eq_iff]

/-- Every edge in `E` has card 3 and is a subset of `V`. -/
lemma edgeSet_valid {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) :
    ∀ e ∈ edgeSet N S, e.card = 3 ∧ e ⊆ vertexSet N := by
  intro e he
  rw [edgeSet] at he
  simp_all +decide [pointEdges]
  obtain ⟨a, b, c, h₁, rfl | rfl | rfl | rfl⟩ := he
    <;> simp_all +decide [grid3]
  · have := hS h₁
    simp_all +decide [Finset.subset_iff, mem_gridRange]
    unfold vertexOf
    simp +decide [*, vertexSet]
    unfold encVertex
    simp +decide [*]
    grind
  · have := hS h₁
    simp_all +decide [Finset.subset_iff, mem_gridRange]
    unfold vertexOf vertexSet
    simp_all +decide [Finset.mem_range]
    unfold encVertex
    simp +decide [*]
    grind
  · have := hS h₁
    simp_all +decide [Finset.subset_iff, mem_gridRange]
    grind +locals
  · have := hS h₁
    simp_all +decide [Finset.subset_iff, mem_gridRange]
    unfold vertexOf
    simp +decide [*, vertexSet]
    unfold encVertex
    simp +decide [*]
    grind

/-! ## §7. Injection from S to E

Each point `(a,b,c) ∈ S` maps to the edge `{v₀, v₁, v₂}`
(families 0,1,2). This map is injective because the edge
uniquely determines the point. -/

/-- The "first edge" map from `S` to `E`. -/
def firstEdge (N : ℕ) (p : ℤ × ℤ × ℤ) : Finset ℕ :=
  {vertexOf N p.1 p.2.1 p.2.2 0,
   vertexOf N p.1 p.2.1 p.2.2 1,
   vertexOf N p.1 p.2.1 p.2.2 2}

/-- The first edge of `(a,b,c)` belongs to `pointEdges`. -/
lemma firstEdge_mem_pointEdges (N : ℕ) (a b c : ℤ) :
    firstEdge N (a, b, c) ∈ pointEdges N a b c := by
  simp [firstEdge, pointEdges]

/-- The first edge of a point in `S` belongs to `edgeSet`. -/
lemma firstEdge_mem_edgeSet {N : ℕ}
    {S : Finset (ℤ × ℤ × ℤ)} {p : ℤ × ℤ × ℤ} (hp : p ∈ S) :
    firstEdge N p ∈ edgeSet N S := by
  simp only [edgeSet, Finset.mem_biUnion]
  exact ⟨p, hp, firstEdge_mem_pointEdges N p.1 p.2.1 p.2.2⟩

/-- The first-edge map is injective on `grid3 N` for `N ≥ 1`. -/
lemma firstEdge_injective {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) :
    Set.InjOn (firstEdge N) (↑S) := by
  intro p hp q hq
  unfold firstEdge
  simp +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
  intro h₀ h₁ h₂ h₃ h₄ h₅
  have := hS hp
  have := hS hq
  simp_all +decide only [grid3]
  simp_all +decide [Finset.mem_product, mem_gridRange]
  unfold vertexOf at *
  unfold encVertex at *
  grind

/-- `|S| ≤ |edgeSet N S|` via the injective first-edge map. -/
lemma card_S_le_edgeSet {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) :
    S.card ≤ (edgeSet N S).card := by
  calc S.card
      = (S.image (firstEdge N)).card := by
        rw [Finset.card_image_of_injOn (firstEdge_injective hN hS)]
    _ ≤ (edgeSet N S).card := by
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_image] at he
        obtain ⟨p, hp, rfl⟩ := he
        exact firstEdge_mem_edgeSet hp

/-! ## §8. Unique Clique Property

The main geometric argument: if `S` has no quadruple of the form (1.1),
then every edge in the hypergraph belongs to exactly one clique. -/

/-- Every edge in `E` has vertices from 3 distinct families. -/
lemma edge_families_distinct {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    {e : Finset ℕ} (he : e ∈ edgeSet N S) :
    ∃ f₁ f₂ f₃ : ℕ, f₁ < f₂ ∧ f₂ < f₃ ∧ f₃ < 4 ∧
      ∃ v₁ v₂ v₃, e = {v₁, v₂, v₃} ∧
        familyOf N v₁ = f₁ ∧ familyOf N v₂ = f₂ ∧
        familyOf N v₃ = f₃ := by
  unfold edgeSet at he
  simp_all +decide [Finset.mem_biUnion]
  rcases he with ⟨a, b, c, hS, he⟩
  unfold pointEdges at he
  simp_all +decide
  have h_families :
      familyOf N (vertexOf N a b c 0) = 0 ∧
      familyOf N (vertexOf N a b c 1) = 1 ∧
      familyOf N (vertexOf N a b c 2) = 2 ∧
      familyOf N (vertexOf N a b c 3) = 3 := by
    have h_bounds :
        0 ≤ a ∧ a < N ∧ 0 ≤ b ∧ b < N ∧ 0 ≤ c ∧ c < N := by
      have := ‹S ⊆ grid3 N› hS
      simp_all +decide [grid3]
      unfold gridRange at this
      aesop
    exact ⟨
      encVertex_family hN (by norm_num) (by linarith) (by linarith),
      encVertex_family hN (by norm_num) (by linarith) (by linarith),
      encVertex_family hN (by norm_num) (by linarith) (by linarith),
      encVertex_family hN (by norm_num) (by linarith) (by linarith)⟩
  grind

/-- The four-point quadruple from non-concurrent planes. -/
lemma quadruple_of_nonconcurrent {N : ℕ} (_hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} {i j k l : ℤ}
    (h012 : (i - j, i - k, i) ∈ S)
    (h013 : (i - j, l + j, i) ∈ S)
    (h023 : (l + k, i - k, i) ∈ S)
    (h123 : (k + l, j + l, j + k + l) ∈ S)
    (hne : l ≠ i - j - k) :
    ContainsQuadruple S := by
  use i - j, i - k, i, j + k + l - i
  grind

/-- The clique through a point: the set of 4 vertices through `(a,b,c)`. -/
def pointClique (N : ℕ) (a b c : ℤ) : Finset ℕ :=
  {vertexOf N a b c 0, vertexOf N a b c 1,
   vertexOf N a b c 2, vertexOf N a b c 3}

/-- The point clique has cardinality 4. -/
lemma pointClique_card {N : ℕ} (hN : N ≥ 1) {a b c : ℤ}
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N) :
    (pointClique N a b c).card = 4 := by
  convert Set.toFinset_card _
  any_goals exact Set.range (fun i : Fin 4 => vertexOf N a b c i)
  all_goals try infer_instance
  · simp +decide [pointClique, Set.toFinset_range]
    simp +decide [Fin.univ_succ]
  · rw [Set.card_range_of_injective]
    · rfl
    · exact vertexOf_injective hN ha hb hc

/-- Every 3-element subset of the point clique is an edge. -/
lemma pointClique_edges {N : ℕ} (_hN : N ≥ 1) {a b c : ℤ}
    (_ha : 0 ≤ a ∧ a < ↑N) (_hb : 0 ≤ b ∧ b < ↑N)
    (_hc : 0 ≤ c ∧ c < ↑N)
    {S : Finset (ℤ × ℤ × ℤ)} (_hS : S ⊆ grid3 N)
    (hmem : (a, b, c) ∈ S) :
    ∀ t ⊆ pointClique N a b c,
      t.card = 3 → t ∈ edgeSet N S := by
  intro t ht ht'
  have := Finset.card_eq_three.mp ht'
  obtain ⟨x, y, z, hxyz⟩ := this
  simp_all +decide only [subset_iff, edgeSet]
  unfold pointEdges pointClique at *
  simp_all +decide [Finset.mem_insert, Finset.mem_singleton]
  use a, b, c, hmem
  simp_all +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
  rcases ht with
    ⟨rfl | rfl | rfl | rfl,
     rfl | rfl | rfl | rfl,
     rfl | rfl | rfl | rfl⟩
    <;> simp +decide at hxyz ⊢

/-- The point clique is a subset of the vertex set. -/
lemma pointClique_sub_vertexSet {N : ℕ} (_hN : N ≥ 1) {a b c : ℤ}
    (_ha : 0 ≤ a ∧ a < ↑N) (_hb : 0 ≤ b ∧ b < ↑N)
    (_hc : 0 ≤ c ∧ c < ↑N) :
    pointClique N a b c ⊆ vertexSet N := by
  intro x hx
  unfold pointClique at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals
    unfold vertexOf vertexSet
    apply Finset.mem_range.mpr
  · exact encVertex_lt _hN (by decide) (by linarith) (by linarith)
  · exact encVertex_lt _hN (by decide) (by linarith) (by linarith)
  · exact encVertex_lt _hN (by decide) (by linarith) (by linarith)
  · exact encVertex_lt _hN (by decide) (by linarith) (by linarith)

/-- Extract the generating point from an edge. -/
lemma edge_from_point {N : ℕ} {S : Finset (ℤ × ℤ × ℤ)}
    {e : Finset ℕ} (he : e ∈ edgeSet N S) :
    ∃ a b c : ℤ,
      (a, b, c) ∈ S ∧ e ∈ pointEdges N a b c := by
  simp only [edgeSet, Finset.mem_biUnion] at he
  obtain ⟨⟨a, b, c⟩, hmem, he⟩ := he
  exact ⟨a, b, c, hmem, he⟩

/-- Grid membership gives coordinate bounds. -/
lemma grid_mem_bounds {N : ℕ} {S : Finset (ℤ × ℤ × ℤ)}
    (hS : S ⊆ grid3 N) {a b c : ℤ} (hmem : (a, b, c) ∈ S) :
    (0 ≤ a ∧ a < ↑N) ∧ (0 ≤ b ∧ b < ↑N) ∧ (0 ≤ c ∧ c < ↑N) := by
  have := hS hmem
  simp only [grid3, Finset.mem_product] at this
  exact ⟨mem_gridRange.mp this.1,
    mem_gridRange.mp this.2.1, mem_gridRange.mp this.2.2⟩

/-- Each edge is a subset of its generating point's clique. -/
lemma edge_sub_pointClique (N : ℕ) (a b c : ℤ)
    {e : Finset ℕ} (he : e ∈ pointEdges N a b c) :
    e ⊆ pointClique N a b c := by
  unfold pointEdges at he
  unfold pointClique
  aesop

/-- No edge has two vertices from the same family. -/
lemma no_same_family_in_edge {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    {e : Finset ℕ} (he : e ∈ edgeSet N S)
    {u v : ℕ} (hu : u ∈ e) (hv : v ∈ e) (huv : u ≠ v) :
    familyOf N u ≠ familyOf N v := by
  have h_families_distinct :
      ∃ f₁ f₂ f₃ : ℕ, f₁ < f₂ ∧ f₂ < f₃ ∧ f₃ < 4 ∧
        ∃ v₁ v₂ v₃ : ℕ, e = {v₁, v₂, v₃} ∧
          familyOf N v₁ = f₁ ∧ familyOf N v₂ = f₂ ∧
          familyOf N v₃ = f₃ :=
    edge_families_distinct hN hS he
  grind

/-- Any clique has at most 4 elements (pigeonhole on families). -/
lemma clique_card_le_four {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S) :
    K.card ≤ 4 := by
  contrapose! hK_edges
  obtain ⟨u, w, hu, hw, h_family⟩ :
      ∃ u w : ℕ, u ∈ K ∧ w ∈ K ∧ u ≠ w ∧
        familyOf N u = familyOf N w := by
    have h_pigeonhole :
        Finset.card (Finset.image (fun v => familyOf N v) K) ≤ 4 := by
      have h_family_range : ∀ v ∈ K, familyOf N v < 4 := by
        intro v hv
        have := hK_sub hv
        simp_all +decide [vertexSet]
        exact Nat.div_lt_of_lt_mul <| by linarith
      exact le_trans
        (Finset.card_le_card
          (Finset.image_subset_iff.mpr fun v hv =>
            Finset.mem_range.mpr (h_family_range v hv)))
        (by norm_num)
    contrapose! h_pigeonhole
    rw [Finset.card_image_of_injOn fun u hu v hv huv => by
      contrapose! huv
      exact h_pigeonhole u v hu hv huv]
    linarith
  obtain ⟨x, hx⟩ : ∃ x ∈ K, x ≠ u ∧ x ≠ w :=
    Exists.imp (by aesop)
      (Finset.exists_mem_ne
        (show 1 < Finset.card (Finset.erase K u) from by
          rw [Finset.card_erase_of_mem hu]
          omega)
        w)
  refine ⟨{u, w, x}, ?_, ?_, ?_⟩
    <;> simp_all +decide [Finset.insert_subset_iff]
  · grind
  · intro H
    exact absurd
      (no_same_family_in_edge hN hS H (by aesop) (by aesop) h_family.1)
      (by aesop)

/-- An edge with vertices from families 0, 1, 3 implies its intersection
point is in S. -/
lemma edge_013_mem {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) {i j l : ℤ}
    (hi : 0 ≤ i + ↑N ∧ i + ↑N < 3 * ↑N)
    (hj : 0 ≤ j + ↑N ∧ j + ↑N < 3 * ↑N)
    (hl : 0 ≤ l + ↑N ∧ l + ↑N < 3 * ↑N)
    (he : ({encVertex N 0 i, encVertex N 1 j,
            encVertex N 3 l} : Finset ℕ) ∈ edgeSet N S) :
    (i - j, l + j, i) ∈ S := by
  obtain ⟨p, hp, hp'⟩ := Finset.mem_biUnion.mp he
  obtain ⟨a, b, c, ha, hb, hc, h_eq⟩ :
      ∃ a b c : ℤ, p = (a, b, c) ∧
        (0 ≤ a ∧ a < N) ∧ (0 ≤ b ∧ b < N) ∧ (0 ≤ c ∧ c < N) := by
    have := grid_mem_bounds hS hp
    aesop
  simp_all +decide [pointEdges]
  rcases hp' with hp' | hp' | hp' | hp'
    <;> simp_all +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
  · unfold vertexOf at *
    unfold encVertex at *
    grind
  · unfold vertexOf at *
    simp_all +decide [encVertex]
    have h_eqs : i = c ∧ j = -a + c ∧ l = a + b - c := by omega
    grind +extAll
  · unfold vertexOf at hp'
    unfold encVertex at *
    grind
  · grind +locals

/-- An edge with vertices from families 0, 2, 3 implies its intersection
point is in S. -/
lemma edge_023_mem {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) {i k l : ℤ}
    (hi : 0 ≤ i + ↑N ∧ i + ↑N < 3 * ↑N)
    (hk : 0 ≤ k + ↑N ∧ k + ↑N < 3 * ↑N)
    (hl : 0 ≤ l + ↑N ∧ l + ↑N < 3 * ↑N)
    (he : ({encVertex N 0 i, encVertex N 2 k,
            encVertex N 3 l} : Finset ℕ) ∈ edgeSet N S) :
    (l + k, i - k, i) ∈ S := by
  obtain ⟨a, b, c, hp⟩ :
      ∃ a b c : ℤ, (a, b, c) ∈ S ∧
        ({encVertex N 0 i, encVertex N 2 k,
          encVertex N 3 l} : Finset ℕ) =
          {encVertex N 0 i, encVertex N 2 k, encVertex N 3 l} ∧
        ({encVertex N 0 i, encVertex N 2 k,
          encVertex N 3 l} : Finset ℕ) ∈ pointEdges N a b c := by
    unfold edgeSet at he
    aesop
  obtain ⟨ha, hb, hc⟩ := grid_mem_bounds hS hp.1
  have h_eq :
      encVertex N 0 c = encVertex N 0 i ∧
      encVertex N 2 (-b + c) = encVertex N 2 k ∧
      encVertex N 3 (a + b - c) = encVertex N 3 l := by
    unfold pointEdges at hp
    unfold vertexOf at hp
    simp_all +decide [Finset.ext_iff]
    rcases hp.2 with h | h | h | h
      <;> have := h (encVertex N 0 i)
      <;> have := h (encVertex N 2 k)
      <;> have := h (encVertex N 3 l)
      <;> simp_all +decide [encVertex]
    · omega
    · omega
    · grind +qlia
    · omega
  unfold encVertex at h_eq
  grind

/-- An edge with vertices from families 1, 2, 3 implies its intersection
point is in S. -/
lemma edge_123_mem {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) {j k l : ℤ}
    (hj : 0 ≤ j + ↑N ∧ j + ↑N < 3 * ↑N)
    (hk : 0 ≤ k + ↑N ∧ k + ↑N < 3 * ↑N)
    (hl : 0 ≤ l + ↑N ∧ l + ↑N < 3 * ↑N)
    (he : ({encVertex N 1 j, encVertex N 2 k,
            encVertex N 3 l} : Finset ℕ) ∈ edgeSet N S) :
    (k + l, j + l, j + k + l) ∈ S := by
  obtain ⟨p, hp, hp'⟩ := Finset.mem_biUnion.mp he
  unfold pointEdges at hp'
  have := grid_mem_bounds hS hp
  simp_all +decide [Finset.ext_iff]
  rcases hp' with hp' | hp' | hp' | hp'
    <;> have := hp' (encVertex N 1 j)
    <;> have := hp' (encVertex N 2 k)
    <;> have := hp' (encVertex N 3 l)
    <;> simp_all +decide [vertexOf]
  · unfold encVertex at *
    grind +revert
  · unfold encVertex at *
    grind
  · unfold encVertex at *
    grind
  · unfold encVertex at *
    grind

/-- Key concurrent argument: if v0, v1, v2 ∈ K and v' ∈ K \ {v0,v1,v2},
then v' = v3. This uses the family argument and `quadruple_of_nonconcurrent`. -/
lemma fourth_vertex_012 {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N) (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {v' : ℕ} (hv' : v' ∈ K)
    (hv0 : vertexOf N a b c 0 ∈ K)
    (hv1 : vertexOf N a b c 1 ∈ K)
    (hv2 : vertexOf N a b c 2 ∈ K)
    (hne0 : v' ≠ vertexOf N a b c 0)
    (hne1 : v' ≠ vertexOf N a b c 1)
    (hne2 : v' ≠ vertexOf N a b c 2) :
    v' = vertexOf N a b c 3 := by
  have h_family_v' : familyOf N v' = 3 := by
    have h_fam_ne :
        familyOf N v' ≠ 0 ∧ familyOf N v' ≠ 1 ∧ familyOf N v' ≠ 2 := by
      have h_ne : ∀ u v : ℕ, u ∈ K → v ∈ K → u ≠ v →
          familyOf N u ≠ familyOf N v := by
        intro u v hu hv huv
        have h_edge : ∃ e ∈ edgeSet N S, u ∈ e ∧ v ∈ e ∧ e.card = 3 := by
          obtain ⟨w, hw⟩ : ∃ w ∈ K, w ≠ u ∧ w ≠ v := by grind +locals
          use {u, v, w}
          grind
        obtain ⟨e, he₁, he₂, he₃, _⟩ := h_edge
        exact no_same_family_in_edge hN hS he₁ he₂ he₃ huv
      have h_fam :
          familyOf N (vertexOf N a b c 0) = 0 ∧
          familyOf N (vertexOf N a b c 1) = 1 ∧
          familyOf N (vertexOf N a b c 2) = 2 :=
        ⟨encVertex_family hN (by decide) (by linarith) (by linarith),
         encVertex_family hN (by decide) (by linarith) (by linarith),
         encVertex_family hN (by decide) (by linarith) (by linarith)⟩
      grind +ring
    have h_range : familyOf N v' < 4 :=
      Nat.div_lt_of_lt_mul <| by
        linarith [Finset.mem_range.mp (hK_sub hv')]
    interval_cases familyOf N v' <;> trivial
  obtain ⟨l, hl⟩ :
      ∃ l : ℤ, v' = encVertex N 3 l ∧
        0 ≤ l + ↑N ∧ l + ↑N < 3 * ↑N := by
    unfold familyOf at h_family_v'
    unfold encVertex
    use v' % (3 * N) - N
    norm_num [Nat.div_eq_of_lt] at *
    exact ⟨by
      norm_cast
      nlinarith [Nat.mod_add_div v' (3 * N),
        Int.toNat_of_nonneg
          (Int.emod_nonneg v' (by positivity : (3 * N : ℤ) ≠ 0))],
      Int.emod_nonneg _ (by positivity),
      Int.emod_lt_of_pos _ (by positivity)⟩
  have h013 : (a, l - a + c, c) ∈ S := by
    have h013 :
        ({encVertex N 0 c, encVertex N 1 (-a + c),
          encVertex N 3 l} : Finset ℕ) ∈ edgeSet N S := by
      convert hK_edges
        {vertexOf N a b c 0, vertexOf N a b c 1, v'} _ _
        using 1 <;> simp_all +decide [Finset.subset_iff]
      · simp [vertexOf]
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          <;> simp +decide [*]
        · exact Ne.symm hne1
        · exact ⟨by
            exact fun h => by
              have := vertexOf_injective hN ha hb hc
              have := @this 0 1
              aesop,
            by tauto⟩
    convert edge_013_mem hN hS _ _ _ h013 using 1
    · ring_nf
    · constructor <;> linarith
    · constructor <;> linarith
    · tauto
  have h023 : (l - b + c, b, c) ∈ S := by
    have h023 :
        ({encVertex N 0 c, encVertex N 2 (-b + c),
          encVertex N 3 l} : Finset ℕ) ∈ edgeSet N S := by
      convert hK_edges _ _ _ using 1
      · simp_all +decide [Finset.subset_iff]
        exact ⟨hv0, hv2⟩
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
          <;> simp +decide [*, encVertex]
        · omega
        · constructor <;> omega
    convert edge_023_mem hN hS _ _ _ h023 using 1
    · ring_nf
    · constructor <;> linarith
    · constructor <;> linarith
    · tauto
  have h123 :
      ((-b + c) + l, (-a + c) + l,
       (-a + c) + (-b + c) + l) ∈ S := by
    convert edge_123_mem hN hS _ _ _ _ using 1
    · constructor <;> linarith
    · constructor <;> linarith
    · tauto
    · convert hK_edges
        {vertexOf N a b c 1, vertexOf N a b c 2, v'} _ _ using 1
      · aesop
      · simp_all +decide [Finset.insert_subset_iff]
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          <;> simp +decide [*]
        · grind
        · constructor <;> intro h
            <;> have := vertexOf_injective hN ha hb hc
            <;> simp_all +decide [Function.Injective]
          exact absurd (@this 1 2) (by simp +decide [h])
  by_cases h_eq : l = a + b - c
  · aesop
  · contrapose! hnoQ
    use a, b, c, l - a - b + c
    exact ⟨by
      contrapose! h_eq
      linarith, hmem,
      by
        convert h023 using 1
        ring_nf,
      by
        convert h013 using 1
        ring_nf,
      by
        convert h123 using 1
        ring_nf⟩

/-- An edge with vertices from families 0, 1, 2 implies its intersection
point is in S. -/
lemma edge_012_mem {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N) {i j k : ℤ}
    (hi : 0 ≤ i + ↑N ∧ i + ↑N < 3 * ↑N)
    (hj : 0 ≤ j + ↑N ∧ j + ↑N < 3 * ↑N)
    (hk : 0 ≤ k + ↑N ∧ k + ↑N < 3 * ↑N)
    (he : ({encVertex N 0 i, encVertex N 1 j,
            encVertex N 2 k} : Finset ℕ) ∈ edgeSet N S) :
    (i - j, i - k, i) ∈ S := by
  revert he
  intro he
  obtain ⟨p, hp, hp'⟩ := Finset.mem_biUnion.mp he
  have h_bounds :
      (0 ≤ p.1 ∧ p.1 < ↑N) ∧
      (0 ≤ p.2.1 ∧ p.2.1 < ↑N) ∧
      (0 ≤ p.2.2 ∧ p.2.2 < ↑N) :=
    grid_mem_bounds hS hp
  simp_all +decide [pointEdges]
  rcases hp' with hp' | hp' | hp' | hp'
    <;> simp_all +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
  · simp_all +decide [encVertex, vertexOf]
    have h_eq : i = p.2.2 ∧ j = -p.1 + p.2.2 ∧ k = -p.2.1 + p.2.2 := by
      omega
    aesop
  · unfold vertexOf at *
    simp_all +decide [encVertex]
    omega
  · unfold vertexOf at *
    simp_all +decide [encVertex]
    omega
  · unfold vertexOf at *
    simp_all +decide
    unfold encVertex at *
    omega

/-- In a clique K of size ≥ 4, any two distinct members have distinct
families. -/
lemma distinct_families_in_clique {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    {K : Finset ℕ} (_hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    (hK_card : 4 ≤ K.card)
    {u v : ℕ} (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
    familyOf N u ≠ familyOf N v := by
  obtain ⟨w, hwK, hw⟩ : ∃ w ∈ K, w ≠ u ∧ w ≠ v :=
    Exists.imp (by aesop)
      (Finset.exists_mem_ne
        (show 1 < # (K.erase u) from by
          rw [Finset.card_erase_of_mem hu]
          omega)
        v)
  have h_edge : {u, v, w} ∈ edgeSet N S := by grind
  exact no_same_family_in_edge hN hS h_edge
    (by aesop) (by aesop) (by aesop)

/-- Helper: the fourth vertex in a clique containing v0, v1, v3 has
family 2. -/
lemma fourth_vertex_013_family {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    {a b c : ℤ} (ha : 0 ≤ a ∧ a < ↑N)
    (hb : 0 ≤ b ∧ b < ↑N) (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {v' : ℕ} (hv' : v' ∈ K)
    (hv0 : vertexOf N a b c 0 ∈ K)
    (hv1 : vertexOf N a b c 1 ∈ K)
    (hv3 : vertexOf N a b c 3 ∈ K)
    (hne0 : v' ≠ vertexOf N a b c 0)
    (hne1 : v' ≠ vertexOf N a b c 1)
    (hne3 : v' ≠ vertexOf N a b c 3) :
    familyOf N v' = 2 := by
  -- v' is in K and K has ≥ 4 distinct elements, so v' must belong to a
  -- different family than v0, v1, and v3.
  have h_family_distinct :
      familyOf N v' ≠ familyOf N (vertexOf N a b c 0) ∧
      familyOf N v' ≠ familyOf N (vertexOf N a b c 1) ∧
      familyOf N v' ≠ familyOf N (vertexOf N a b c 3) := by
    have h_unique_clique : ∀ u v : ℕ, u ∈ K → v ∈ K → u ≠ v →
        familyOf N u ≠ familyOf N v := by
      intro u v hu hv huv
      apply distinct_families_in_clique hN hS hK_sub hK_edges
      · have h_card :
            Finset.card ({v', vertexOf N a b c 0,
              vertexOf N a b c 1, vertexOf N a b c 3} : Finset ℕ) =
            4 := by
          rw [Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem]
            <;> simp +decide [*]
          · unfold vertexOf
            simp +decide [encVertex]
            omega
          · constructor <;> intro h
              <;> have := vertexOf_injective hN ha hb hc
              <;> simp_all +decide [Function.Injective]
            · exact absurd (this h) (by decide)
            · exact absurd (@this 0 3 h) (by decide)
        exact h_card ▸ Finset.card_le_card
          (Finset.insert_subset_iff.mpr
            ⟨hv', Finset.insert_subset_iff.mpr
              ⟨hv0, Finset.insert_subset_iff.mpr
                ⟨hv1, Finset.singleton_subset_iff.mpr hv3⟩⟩⟩)
      · assumption
      · assumption
      · assumption
    exact ⟨h_unique_clique _ _ hv' hv0 hne0,
      h_unique_clique _ _ hv' hv1 hne1,
      h_unique_clique _ _ hv' hv3 hne3⟩
  -- Since familyOf N v' is not 0, 1, or 3, it must be 2.
  have h_family_2 :
      familyOf N (vertexOf N a b c 0) = 0 ∧
      familyOf N (vertexOf N a b c 1) = 1 ∧
      familyOf N (vertexOf N a b c 3) = 3 := by
    exact ⟨encVertex_family hN (by decide) (by omega) (by omega),
      encVertex_family hN (by decide) (by omega) (by omega),
      encVertex_family hN (by decide) (by omega) (by omega)⟩
  have h_family_2 : familyOf N v' < 4 :=
    Nat.div_lt_of_lt_mul <| by
      linarith [Finset.mem_range.mp (hK_sub hv')]
  grind

/-- Extract `encVertex N 2 k` data from a vertex in family 2. -/
lemma family2_to_encVertex {N : ℕ} (hN : N ≥ 1) {v' : ℕ}
    (_hv'_mem : v' ∈ vertexSet N) (h_family : familyOf N v' = 2) :
    ∃ k : ℤ, v' = encVertex N 2 k ∧
      0 ≤ k + ↑N ∧ k + ↑N < 3 * ↑N := by
  unfold familyOf at h_family
  unfold encVertex
  use v' - 2 * (3 * N) - N
  rw [Nat.div_eq_iff] at h_family
  · omega
  · linarith

/-- The fourth vertex of a clique containing {v0, v1, v3} equals v2. -/
lemma fourth_vertex_013 {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {v' : ℕ} (hv' : v' ∈ K)
    (hv0 : vertexOf N a b c 0 ∈ K)
    (hv1 : vertexOf N a b c 1 ∈ K)
    (hv3 : vertexOf N a b c 3 ∈ K)
    (hne0 : v' ≠ vertexOf N a b c 0)
    (hne1 : v' ≠ vertexOf N a b c 1)
    (hne3 : v' ≠ vertexOf N a b c 3) :
    v' = vertexOf N a b c 2 := by
  obtain ⟨k, hk⟩ := family2_to_encVertex hN (hK_sub hv') (by
    apply fourth_vertex_013_family hN hS ha hb hc hK_sub hK_edges
      hv' hv0 hv1 hv3 hne0 hne1 hne3)
  contrapose! hnoQ
  have h_edge012 : (a, c - k, c) ∈ S := by
    have h_point :
        ({encVertex N 0 c, encVertex N 1 (-a + c),
          encVertex N 2 k} : Finset ℕ) ∈ edgeSet N S := by
      convert hK_edges _ _ _ using 1
      · simp_all +decide [Finset.subset_iff]
        exact ⟨hv0, hv1⟩
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
          <;> simp +decide [*, encVertex]
        · lia
        · omega
    convert edge_012_mem hN hS _ _ _ h_point using 1
    · ring_nf
    · constructor <;> linarith
    · constructor <;> linarith
    · tauto
  have h_edge023 : (a + b - c + k, c - k, c) ∈ S := by
    have h_edge023 :
        ({encVertex N 0 c, encVertex N 2 k,
          encVertex N 3 (a + b - c)} : Finset ℕ) ∈ edgeSet N S := by
      convert hK_edges _ _ _ using 1
      · simp_all +decide [Finset.subset_iff]
        exact ⟨hv0, hv3⟩
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
          <;> simp +decide [*, encVertex]
        · grind
        · constructor <;> omega
    have := edge_023_mem hN hS
      (show 0 ≤ c + ↑N ∧ c + ↑N < 3 * ↑N from ⟨by linarith, by linarith⟩)
      (show 0 ≤ k + ↑N ∧ k + ↑N < 3 * ↑N from ⟨by linarith, by linarith⟩)
      (show 0 ≤ a + b - c + ↑N ∧ a + b - c + ↑N < 3 * ↑N from
        ⟨by linarith, by linarith⟩)
      h_edge023
    aesop
  have h_edge123 : (k + (a + b - c), b, k + b) ∈ S := by
    convert edge_123_mem hN hS _ _ _ _ using 1
    rotate_left
    · exact -a + c
    · exact k
    · exact a + b - c
    · constructor <;> linarith
    · tauto
    · constructor <;> linarith
    · convert hK_edges {vertexOf N a b c 1, vertexOf N a b c 3, v'} _ _
        using 1
      · aesop
      · simp_all +decide [Finset.insert_subset_iff]
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem] <;> simp +decide [*]
        · grind
        · constructor <;> intro h <;> simp_all +decide [vertexOf]
          unfold encVertex at h
          norm_num at h
          omega
    · ring_nf
  use a, c - k, c, b - (c - k)
  grind +locals

set_option maxHeartbeats 800000 in
-- Complex family analysis requires extra heartbeats.
/-- The fourth vertex of a clique containing {v0, v2, v3} equals v1. -/
lemma fourth_vertex_023 {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {v' : ℕ} (hv' : v' ∈ K)
    (hv0 : vertexOf N a b c 0 ∈ K)
    (hv2 : vertexOf N a b c 2 ∈ K)
    (hv3 : vertexOf N a b c 3 ∈ K)
    (hne0 : v' ≠ vertexOf N a b c 0)
    (hne2 : v' ≠ vertexOf N a b c 2)
    (hne3 : v' ≠ vertexOf N a b c 3) :
    v' = vertexOf N a b c 1 := by
  obtain ⟨j, hj⟩ :
      ∃ j : ℤ, v' = encVertex N 1 j ∧
        0 ≤ j + N ∧ j + N < 3 * N := by
    have h_family : familyOf N v' = 1 := by
      have h_family :
          familyOf N v' ≠ 0 ∧ familyOf N v' ≠ 2 ∧
          familyOf N v' ≠ 3 := by
        refine ⟨?_, ?_, ?_⟩
        · intro h
          have := distinct_families_in_clique hN hS hK_sub hK_edges
            (show 4 ≤ K.card from ?_) hv' hv0
          · simp_all +decide
            exact this (by
              rw [show familyOf N (vertexOf N a b c 0) = 0 from by
                exact encVertex_family hN (by norm_num)
                  (by linarith) (by linarith)])
          · refine Finset.card_le_card
              (show {v', vertexOf N a b c 0, vertexOf N a b c 2,
                  vertexOf N a b c 3} ⊆ K from by
                simp_all +decide [Finset.insert_subset_iff,
                  Finset.singleton_subset_iff])
              |> le_trans ?_
            grind +locals
        · intro h
          have := distinct_families_in_clique hN hS hK_sub hK_edges
            (show 4 ≤ K.card from ?_) hv' hv2
          · simp_all +decide
            contrapose! this
            rw [show vertexOf N a b c 2 = encVertex N 2 (-b + c) from rfl,
              encVertex_family]
              <;> norm_num [ha, hb, hc]
            · linarith
            · linarith
            · linarith
          · refine Finset.card_le_card
              (show {v', vertexOf N a b c 0, vertexOf N a b c 2,
                  vertexOf N a b c 3} ⊆ K from by
                simp_all +decide [Finset.insert_subset_iff,
                  Finset.singleton_subset_iff])
              |> le_trans ?_
            rw [Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem]
              <;> simp +decide [*]
            · unfold vertexOf
              simp +decide [encVertex]
              omega
            · constructor <;> intro H
                <;> have := vertexOf_injective hN ha hb hc
                <;> simp_all +decide [Function.Injective]
              · exact absurd (this H) (by decide)
              · exact absurd (this H) (by decide)
        · intro h
          have := distinct_families_in_clique hN hS hK_sub hK_edges
            (show 4 ≤ K.card from ?_) hv' hv3
          · simp_all +decide
            unfold vertexOf at *
            simp_all +decide [familyOf]
            unfold encVertex at *
            simp_all +decide []
            exact this (by
              rw [Nat.le_antisymm_iff]
              exact ⟨Nat.le_div_iff_mul_le (by positivity) |>.2 <| by
                linarith [Int.toNat_of_nonneg
                  (by linarith : 0 ≤ a + b - c + N)],
                Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by
                  linarith [Int.toNat_of_nonneg
                    (by linarith : 0 ≤ a + b - c + N)]⟩)
          · have h_card : K.card ≥ 4 := by
              have h_distinct :
                  v' ≠ vertexOf N a b c 0 ∧
                  v' ≠ vertexOf N a b c 2 ∧
                  v' ≠ vertexOf N a b c 3 ∧
                  vertexOf N a b c 0 ≠ vertexOf N a b c 2 ∧
                  vertexOf N a b c 0 ≠ vertexOf N a b c 3 ∧
                  vertexOf N a b c 2 ≠ vertexOf N a b c 3 := by
                grind +locals
              exact Finset.card_le_card
                (show {v', vertexOf N a b c 0, vertexOf N a b c 2,
                    vertexOf N a b c 3} ⊆ K from by
                  simp_all +decide [Finset.insert_subset_iff,
                    Finset.singleton_subset_iff])
                |> le_trans (by simp +decide [*])
            exact h_card
      have h_family : familyOf N v' < 4 :=
        Nat.div_lt_of_lt_mul <| by
          linarith [Finset.mem_range.mp (hK_sub hv')]
      interval_cases familyOf N v' <;> trivial
    unfold familyOf encVertex at *
    use (v' % (3 * N)) - N
    norm_num +zetaDelta at *
    exact ⟨by
      nlinarith [Nat.mod_add_div v' (3 * N),
        Int.toNat_of_nonneg
          (Int.emod_nonneg v' (by positivity : (3 * N : ℤ) ≠ 0))],
      Int.emod_nonneg _ (by positivity),
      Int.emod_lt_of_pos _ (by positivity)⟩
  -- By Lemma edge_012_mem, we have (i - j, i - k, i) ∈ S.
  have h012 : (c - j, c - (-b + c), c) ∈ S := by
    apply edge_012_mem hN hS
    · constructor <;> linarith
    · tauto
    · constructor <;> linarith
    · convert hK_edges _ _ _ using 1
      · simp_all +decide [Finset.subset_iff]
        exact ⟨hv0, hv2⟩
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
          <;> simp +decide [*, encVertex]
        · omega
        · omega
  -- By Lemma edge_013_mem, we have (i - j, l + j, i) ∈ S.
  have h013 : (c - j, (a + b - c) + j, c) ∈ S := by
    apply edge_013_mem hN hS
    · constructor <;> linarith
    · tauto
    · constructor <;> linarith
    · convert hK_edges {v', vertexOf N a b c 0, vertexOf N a b c 3} _ _
        using 1
      · unfold vertexOf
        aesop
      · simp_all +decide [Finset.insert_subset_iff]
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem] <;> simp +decide [*]
        · unfold vertexOf
          simp +decide [encVertex]
          omega
        · grind
  -- By Lemma edge_123_mem, we have (k + l, j + l, j + k + l) ∈ S.
  have h123 :
      ((-b + c) + (a + b - c), j + (a + b - c),
       j + (-b + c) + (a + b - c)) ∈ S := by
    apply edge_123_mem hN hS
    · tauto
    · constructor <;> linarith
    · constructor <;> linarith
    · convert hK_edges {v', vertexOf N a b c 2, vertexOf N a b c 3} _ _
        using 1
      · aesop
      · simp_all +decide [Finset.insert_subset_iff]
      · rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem] <;> simp +decide [*]
        · unfold vertexOf
          simp +decide [encVertex]
          omega
        · grind
  by_cases h : j = -a + c <;> simp_all +decide
  · exact Nat.add_zero ((1 * (3 * N)).add (-a + c + ↑N).toNat)
  · contrapose! hnoQ
    use c - j, b, c, j - (-a + c)
    lia

set_option maxHeartbeats 800000 in
-- Complex family analysis requires extra heartbeats.
/-- The fourth vertex of a clique containing {v1, v2, v3} equals v0. -/
lemma fourth_vertex_123 {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {v' : ℕ} (hv' : v' ∈ K)
    (hv1 : vertexOf N a b c 1 ∈ K)
    (hv2 : vertexOf N a b c 2 ∈ K)
    (hv3 : vertexOf N a b c 3 ∈ K)
    (hne1 : v' ≠ vertexOf N a b c 1)
    (hne2 : v' ≠ vertexOf N a b c 2)
    (hne3 : v' ≠ vertexOf N a b c 3) :
    v' = vertexOf N a b c 0 := by
  -- v' is in K and distinct from v1, v2, v3. We need to show v' = v0.
  have h_family : familyOf N v' = 0 := by
    have h_family :
        familyOf N v' ≠ 1 ∧ familyOf N v' ≠ 2 ∧ familyOf N v' ≠ 3 := by
      have h_family :
          familyOf N (vertexOf N a b c 1) = 1 ∧
          familyOf N (vertexOf N a b c 2) = 2 ∧
          familyOf N (vertexOf N a b c 3) = 3 := by
        unfold vertexOf
        simp +decide [familyOf]
        unfold encVertex
        norm_num [Nat.add_div, Nat.mul_div_assoc, hN]
        exact ⟨
          Nat.le_antisymm
            (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by
              linarith [Int.toNat_of_nonneg (by linarith : 0 ≤ -a + c + N)])
            (Nat.le_div_iff_mul_le (by linarith) |>.2 <| by
              linarith [Int.toNat_of_nonneg
                (by linarith : 0 ≤ -a + c + N)]),
          Nat.le_antisymm
            (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by
              linarith [Int.toNat_of_nonneg (by linarith : 0 ≤ -b + c + N)])
            (Nat.le_div_iff_mul_le (by linarith) |>.2 <| by
              linarith [Int.toNat_of_nonneg
                (by linarith : 0 ≤ -b + c + N)]),
          Nat.le_antisymm
            (Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by
              linarith [Int.toNat_of_nonneg
                (by linarith : 0 ≤ a + b - c + N)])
            (Nat.le_div_iff_mul_le (by linarith) |>.2 <| by
              linarith [Int.toNat_of_nonneg
                (by linarith : 0 ≤ a + b - c + N)])⟩
      have h_family : ∀ u v : ℕ, u ∈ K → v ∈ K → u ≠ v →
          familyOf N u ≠ familyOf N v := by
        intro u v hu hv huv
        apply distinct_families_in_clique hN hS hK_sub hK_edges
        · have h_card :
              K.card ≥ Finset.card ({v', vertexOf N a b c 1,
                vertexOf N a b c 2, vertexOf N a b c 3} : Finset ℕ) := by
            exact Finset.card_le_card
              (Finset.insert_subset_iff.mpr
                ⟨hv', Finset.insert_subset_iff.mpr
                  ⟨hv1, Finset.insert_subset_iff.mpr
                    ⟨hv2, Finset.singleton_subset_iff.mpr hv3⟩⟩⟩)
          grind
        · assumption
        · assumption
        · assumption
      grind
    have h_family : familyOf N v' < 4 := by
      have := hK_sub hv'
      simp_all +decide [vertexSet]
      exact Nat.div_lt_of_lt_mul <| by linarith
    grind
  -- By definition of familyOf, we know that v' = encVertex N 0 i for some i.
  obtain ⟨i, hi⟩ :
      ∃ i : ℤ, v' = encVertex N 0 i ∧
        0 ≤ i + ↑N ∧ i + ↑N < 3 * ↑N := by
    unfold familyOf at h_family
    simp_all +decide
    use v' - N
    simp_all +decide [encVertex]
    exact_mod_cast h_family.resolve_left (by linarith)
  have h_edges :
      ({encVertex N 0 i, encVertex N 1 (-a + c),
        encVertex N 2 (-b + c)} : Finset ℕ) ∈ edgeSet N S ∧
      ({encVertex N 0 i, encVertex N 1 (-a + c),
        encVertex N 3 (a + b - c)} : Finset ℕ) ∈ edgeSet N S ∧
      ({encVertex N 0 i, encVertex N 2 (-b + c),
        encVertex N 3 (a + b - c)} : Finset ℕ) ∈ edgeSet N S := by
    refine ⟨hK_edges _ ?_ ?_, hK_edges _ ?_ ?_, hK_edges _ ?_ ?_⟩
      <;> simp_all +decide [Finset.subset_iff]
    any_goals
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
        <;> simp +decide [*]
    any_goals
      rw [encVertex, encVertex]
      omega
    all_goals tauto
  have h_points :
      (i - (-a + c), i - (-b + c), i) ∈ S ∧
      (i - (-a + c), (a + b - c) + (-a + c), i) ∈ S ∧
      ((a + b - c) + (-b + c), i - (-b + c), i) ∈ S := by
    exact ⟨
      edge_012_mem hN hS ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        h_edges.1,
      edge_013_mem hN hS ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        h_edges.2.1,
      edge_023_mem hN hS ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        h_edges.2.2⟩
  by_cases hi : i = c
  · aesop
  · contrapose! hnoQ
    apply quadruple_of_nonconcurrent hN
    · exact h_points.1
    · exact h_points.2.1
    · convert h_points.2.2 using 1
    · convert hmem using 1
      ring_nf
    · omega

/-- If e ∈ pointEdges and e ⊆ K with |K| ≥ 4, then pointClique ⊆ K. -/
lemma pointClique_sub_clique {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_card : K.card ≥ 4)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {e : Finset ℕ} (he_pe : e ∈ pointEdges N a b c)
    (he_K : e ⊆ K) :
    pointClique N a b c ⊆ K := by
  -- Find a vertex v' in K that's not in e.
  obtain ⟨v', hv'_mem, hv'_ne⟩ : ∃ v', v' ∈ K ∧ v' ∉ e := by
    exact Finset.not_subset.mp fun h => by
      have := Finset.card_le_card h
      exact absurd this (by
        have := edge_card_three hN ha hb hc e he_pe
        linarith)
  -- By case analysis on which edge it is, apply the appropriate
  -- fourth_vertex lemma to show v' equals the missing vertex.
  have h_case :
      e = {vertexOf N a b c 0, vertexOf N a b c 1,
           vertexOf N a b c 2} ∨
      e = {vertexOf N a b c 0, vertexOf N a b c 1,
           vertexOf N a b c 3} ∨
      e = {vertexOf N a b c 0, vertexOf N a b c 2,
           vertexOf N a b c 3} ∨
      e = {vertexOf N a b c 1, vertexOf N a b c 2,
           vertexOf N a b c 3} := by
    unfold pointEdges at he_pe
    aesop
  obtain rfl | rfl | rfl | rfl := h_case
    <;> simp_all +decide [pointClique]
  · have hv'_eq : v' = vertexOf N a b c 3 := by
      apply fourth_vertex_012 hN hS hnoQ hmem ha hb hc hK_sub hK_edges
        hv'_mem (he_K (by simp)) (he_K (by simp)) (he_K (by simp))
        hv'_ne.left hv'_ne.right.left hv'_ne.right.right
    simp_all +decide [Finset.insert_subset_iff]
  · have hv'_eq : v' = vertexOf N a b c 2 := by
      apply fourth_vertex_013 hN hS hnoQ hmem ha hb hc hK_sub hK_edges
        hv'_mem (he_K (by simp)) (he_K (by simp)) (he_K (by simp))
        hv'_ne.1 hv'_ne.2.1 hv'_ne.2.2
    simp_all +decide [Finset.insert_subset_iff]
  · have hv'_eq : v' = vertexOf N a b c 1 := by
      apply fourth_vertex_023 hN hS hnoQ hmem ha hb hc hK_sub hK_edges
        hv'_mem (he_K (by simp)) (he_K (by simp)) (he_K (by simp))
        hv'_ne.left hv'_ne.right.left hv'_ne.right.right
    simp_all +decide [Finset.subset_iff]
  · have hv'_eq : v' = vertexOf N a b c 0 := by
      apply fourth_vertex_123 hN hS hnoQ hmem ha hb hc hK_sub hK_edges
        hv'_mem (he_K (by simp +decide)) (he_K (by simp +decide))
        (he_K (by simp +decide)) hv'_ne.1 hv'_ne.2.1 hv'_ne.2.2
    grind

/-- A clique K containing an edge from pointEdges must equal pointClique. -/
lemma clique_eq_pointClique {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S)
    {a b c : ℤ} (hmem : (a, b, c) ∈ S)
    (ha : 0 ≤ a ∧ a < ↑N) (hb : 0 ≤ b ∧ b < ↑N)
    (hc : 0 ≤ c ∧ c < ↑N)
    {K : Finset ℕ} (hK_sub : K ⊆ vertexSet N)
    (hK_card : K.card ≥ 4)
    (hK_edges : ∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S)
    {e : Finset ℕ} (he_pe : e ∈ pointEdges N a b c)
    (he_K : e ⊆ K) :
    K = pointClique N a b c := by
  refine Eq.symm (Finset.eq_of_subset_of_card_le (?_ : pointClique N a b c ⊆ K) ?_)
  · apply pointClique_sub_clique hN hS hnoQ hmem ha hb hc hK_sub
      hK_card hK_edges he_pe he_K
  · exact le_trans (clique_card_le_four hN hS hK_sub hK_edges)
      (by rw [pointClique_card hN ha hb hc])

/-- Every edge belongs to exactly one clique when S has no quadruple. -/
lemma unique_clique_property {N : ℕ} (hN : N ≥ 1)
    {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ grid3 N)
    (hnoQ : ¬ContainsQuadruple S) :
    ∀ e ∈ edgeSet N S, ∃! K,
      K ⊆ vertexSet N ∧ K.card ≥ 4 ∧
      (∀ t ⊆ K, t.card = 3 → t ∈ edgeSet N S) ∧ e ⊆ K := by
  -- For each edge e, extract a point (a,b,c) using `edge_from_point`.
  intro e he
  obtain ⟨a, b, c, hmem, he_pe⟩ := edge_from_point he
  -- Show that the pointClique is a clique.
  have hclique :
      pointClique N a b c ⊆ vertexSet N ∧
      (pointClique N a b c).card = 4 ∧
      (∀ t ⊆ pointClique N a b c, t.card = 3 → t ∈ edgeSet N S) ∧
      e ⊆ pointClique N a b c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply pointClique_sub_vertexSet hN
      · exact grid_mem_bounds hS hmem |>.1
      · have := grid_mem_bounds hS hmem
        aesop
      · exact grid_mem_bounds hS hmem |>.2.2
    · apply pointClique_card hN
      · exact grid_mem_bounds hS hmem |>.1
      · exact grid_mem_bounds hS hmem |>.2.1
      · have := grid_mem_bounds hS hmem
        aesop
    · apply_rules [pointClique_edges]
      · exact grid_mem_bounds hS hmem |>.1
      · exact grid_mem_bounds hS hmem |>.2.1
      · exact grid_mem_bounds hS hmem |>.2.2
    · exact edge_sub_pointClique N a b c he_pe
  refine ⟨pointClique N a b c, ?_, ?_⟩
  · aesop
  · intro y hy
    exact clique_eq_pointClique hN hS hnoQ hmem
      (grid_mem_bounds hS hmem |>.1)
      (grid_mem_bounds hS hmem |>.2.1)
      (grid_mem_bounds hS hmem |>.2.2)
      hy.1 hy.2.1 hy.2.2.1 he_pe hy.2.2.2

/-! ## §9. Quadruple-Free Bound -/

/-- If the Frankl–Rödl theorem holds and S ⊆ [N]³ is quadruple-free,
then |S| < ε N³. -/
theorem quadruple_free_bound (hFR : Theorem_2_2) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ × ℤ), S ⊆ grid3 N →
        ¬ContainsQuadruple S →
        (S.card : ℝ) < ε * (↑N) ^ 3 := by
  intro ε hε_pos
  obtain ⟨n₀, hn₀⟩ := hFR (ε / 1728) (by positivity)
  refine ⟨n₀ * 1728, fun N hN S hS hnoQ => ?_⟩
  refine lt_of_le_of_lt (Nat.cast_le.mpr (card_S_le_edgeSet (by linarith) hS)) ?_
  refine lt_of_lt_of_le (hn₀ (vertexSet N) (edgeSet N S) ?_ ?_ ?_) ?_
  · unfold vertexSet
    norm_num
    linarith
  · exact edgeSet_valid (by linarith) hS
  · apply_rules [unique_clique_property]
    linarith
  · unfold vertexSet
    norm_num
    ring_nf
    norm_num [hε_pos]

/-! ## §10. Theorem 1.2 -/

/-- **Theorem 1.2** (Solymosi, 2004). -/
theorem Theorem_1_2 (hFR : (∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
  ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
  V.card ≥ n₀ →
  (∀ e ∈ E, e.card = 3 ∧ e ⊆ V) →
  (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ 4 ∧
    (∀ t ⊆ K, t.card = 3 → t ∈ E) ∧ e ⊆ K) →
  (E.card : ℝ) < ε * (V.card : ℝ) ^ 3)) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ × ℤ), S ⊆ grid3 N →
        δ * (↑N) ^ 3 ≤ ↑S.card →
        ContainsQuadruple S := by
  intro δ hδ
  by_contra! h
  obtain ⟨N₀, hN₀⟩ := quadruple_free_bound hFR δ hδ
  obtain ⟨N, hN₁, S, hS₁, hS₂, hS₃⟩ := h N₀
  exact not_lt_of_ge hS₂ (hN₀ N hN₁ S hS₁ hS₃)

/-! ## §11. Proposition 1.3 and Theorem 1.1 -/

/-- The lifting map: `S × [N] → [N]³`. -/
def liftSet (S : Finset (ℤ × ℤ)) (N : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (S ×ˢ gridRange N).image (fun p => (p.1.1, p.1.2, p.2))

/-- The lifted set is a subset of `grid3 N`. -/
lemma liftSet_sub_grid3 {S : Finset (ℤ × ℤ)} {N : ℕ}
    (hS : S ⊆ grid2 N) : liftSet S N ⊆ grid3 N := by
  unfold liftSet grid3 grid2 at *
  grind +ring

/-- The cardinality of the lifted set is `|S| * N`. -/
lemma liftSet_card {S : Finset (ℤ × ℤ)} {N : ℕ} :
    (liftSet S N).card = S.card * N := by
  unfold liftSet
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_product, gridRange_card]
  · intro ⟨⟨a₁, b₁⟩, c₁⟩ ⟨⟨a₂, b₂⟩, c₂⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- A quadruple in the lifted set yields a square in the original set. -/
lemma liftSet_quadruple_implies_square
    {S : Finset (ℤ × ℤ)} {N : ℕ}
    (hQ : ContainsQuadruple (liftSet S N)) :
    ContainsSquare S := by
  obtain ⟨a, b, c, d, hd, h1, h2, h3, h4⟩ := hQ
  use a, b, d
  unfold liftSet at *
  aesop

/-- **Proposition 1.3** (Solymosi, 2004). -/
theorem Proposition_1_3
    (h12 : ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ × ℤ), S ⊆ grid3 N →
        δ * (↑N) ^ 3 ≤ ↑S.card → ContainsQuadruple S) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ), S ⊆ grid2 N →
        δ * (↑N) ^ 2 ≤ ↑S.card → ContainsSquare S := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := h12 δ hδ
  use N₀ + 1
  intro N hN S hS hδS
  contrapose! hN₀
  refine ⟨N, by linarith, liftSet S N, ?_, ?_, ?_⟩
  · exact liftSet_sub_grid3 hS
  · rw [liftSet_card]
    norm_num
    nlinarith
  · exact fun h => hN₀ <| liftSet_quadruple_implies_square h

/-- **Theorem 1.1** (Erdős–Graham conjecture on squares). -/
theorem Theorem_1_1 (hFR : Theorem_2_2) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ), S ⊆ grid2 N →
        δ * (↑N) ^ 2 ≤ ↑S.card → ContainsSquare S := by
  convert Proposition_1_3 _ using 1
  exact Theorem_1_2 hFR

theorem erdos_658 :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ S : Finset (ℤ × ℤ), S ⊆ grid2 N →
        δ * (↑N) ^ 2 ≤ ↑S.card → ContainsSquare S :=
  Theorem_1_1 frankl_roedl_theorem

end

end

#print axioms erdos_658
-- 'Erdos658.erdos_658' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos658
