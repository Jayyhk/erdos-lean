import Mathlib

namespace Erdos1025

/-
# Erdős Problem 1025

Let $f$ map every pair of elements of $\{1,\ldots,n\}$ to a point outside that pair, and call
$X$ independent if $x,y \in X$ implies $f(x,y) \notin X$. Let $g(n)$ be the largest size of an
independent set guaranteed for every such $f$. Estimate $g(n)$.

The answer is $g(n) = \Theta(n^{1/2})$: Spencer proved $g(n) \gg n^{1/2}$ and Conlon, Fox and
Sudakov proved $g(n) \ll n^{1/2}$, together pinning down the order that Erdős and Hajnal had
bracketed only between $n^{1/3}$ and $(n\log n)^{1/2}$. `erdos_1025` states exactly that.

The lower bound is the three-uniform case of Spencer's deletion argument; the upper bound is the
Conlon--Fox--Sudakov square-grid construction. The proof runs through the Park--Pham theorem, so
plby's `ErdosProblems/Erdos202.lean` is vendored below ahead of the problem file; its internal
internal soundness checks and its root-level `alias` are dropped, since only one such check belongs
in a single-file entry and the alias would name a namespace outside this file.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/BooleanFamilies.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 1.

Finite Boolean families, upper closures, increasing predicate, minimal
members, and the `ell(U)` complexity bound used by the Park–Pham
expectation-threshold theorem.

All definitions live over a finite ground universe `X : Finset α`. We
avoid any general measure theory; subsets of `X` are represented as
`Finset α` filtered by `S ⊆ X`.
-/

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- The upper closure of `A` inside the universe `X`: the set of subsets
`T ⊆ X` that contain some member of `A`. -/
def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

end

end ParkPham
end Erdos202

/-! =============================================================
    Section from: Erdos/P202/ParkPham/ProductMeasure.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 2.

Finite Bernoulli product measure on subsets of a finite universe `X`,
expressed as a finite sum (no `MeasureTheory`). Used by the expectation-
threshold theorem and the random-partition argument downstream.
-/

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Bernoulli mass of a subset `S ⊆ X` at density `p`. -/
noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

/-- Bernoulli probability of a family `U` of subsets of `X` at density `p`. -/
noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

omit [DecidableEq α] in
lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity

omit [DecidableEq α] in
/-- Bernoulli weights sum to 1 over the powerset of any finite set `X`,
for any `p ∈ ℝ`. This is the finite binomial identity. -/
lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  -- Group by cardinality and use the binomial theorem.
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  -- Reshape RHS to match.
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]

/-! ## Marginal at a fixed subset

If `U = upClosureIn X {T₀}` (the upper closure of a single set), then
`muP X U p = p^|T₀|`. This is the "probability that random subset at
density `p` contains `T₀`" identity used by the random-partition argument.
-/

/-- The upper closure of a singleton family `{T₀}` inside `X` is
`{T ⊆ X : T₀ ⊆ T}`. -/
lemma upClosureIn_singleton (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) :
    upClosureIn X {T₀} =
      X.powerset.filter (fun T => T₀ ⊆ T) := by
  classical
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hS, hST⟩
    rcases Finset.mem_singleton.mp hS with rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hST⟩
  · intro hT
    rcases Finset.mem_filter.mp hT with ⟨hTX, hT₀T⟩
    exact mem_upClosureIn.mpr ⟨Finset.mem_powerset.mp hTX, T₀,
      Finset.mem_singleton.mpr rfl, hT₀T⟩

/-- **Marginal identity.** For `T₀ ⊆ X` and `p ∈ [0,1]`,
`muP X (upClosureIn X {T₀}) p = p^|T₀|`. -/
theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  -- Reparametrize: subsets `S ⊆ X` with `T₀ ⊆ S` correspond bijectively
  -- to subsets `S' ⊆ X \ T₀` via `S = T₀ ∪ S'`. The Bernoulli mass factors
  -- as `p^|T₀| · p^|S'| · (1-p)^(|X\T₀|-|S'|)`, and the inner sum is 1.
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  -- Set up the bijection.
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    -- Use sdiff: S' = (T₀ ∪ S') \ T₀ when T₀ is disjoint from S'.
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  -- The image of Y.powerset under f is exactly the filter we sum over.
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · -- f (T \ T₀) = T₀ ∪ (T \ T₀) = T, since T₀ ⊆ T (via S₀ = T₀ ⊆ T).
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        change T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  -- Now: muP = Σ_{T in filter} bernoulli T = Σ_{S' ⊆ Y} bernoulli (T₀ ∪ S').
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  -- bernoulliMass X (T₀ ∪ S') p = p^|T₀ ∪ S'| (1-p)^(|X| - |T₀ ∪ S'|)
  --                              = p^(|T₀| + |S'|) (1-p)^(|Y| - |S'|)
  --                              = p^|T₀| · [p^|S'| (1-p)^(|Y| - |S'|)]
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    change p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    change p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  -- Apply hkey, factor out p^|T₀|, and use sum_bernoulliMass_eq_one on Y.
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]

end

end ParkPham
end Erdos202

/-! =============================================================
    Section from: Erdos/P202/ParkPham/Smallness.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 3.

The `p`-small predicate underlying the Kahn–Kalai expectation threshold:
a family `U` is `p`-small if some "cover" `G` (a finite family whose
upper closure contains `U`) has total `p`-weight at most `1/2`.

`qSmallUpper X U q` asserts that `U` is NOT `p`-small for any `p > q`,
i.e. the threshold lies in `[0, q]`. This is the form consumed by the
Park–Pham theorem in `Threshold.lean`.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/Fragments.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment infrastructure.

This file starts the source-aligned formalization of the Park--Pham /
Kahn--Kalai expectation-threshold proof.  The "simple proof" route of
Park--Vondrak works with fragments

  F(H, W) = {S \ W | S in H}

and their inclusion-minimal members, then splits those minimal fragments into
large and small parts at a cardinality cutoff.  The deep probabilistic cost
lemma is not proved here; this file only provides the finite set-system
bookkeeping needed to state it cleanly.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/Cost.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, finite cover cost.

The Park--Pham/Park--Vondrak proofs use the cost of a family: the minimum
`p`-weight of a cover.  The existing `pSmall` predicate only needs existence
of a cover of weight at most `1/2`; this file packages the corresponding
finite minimum over covers supported on the ground set `X`.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/FragmentCost.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment cost bookkeeping.

This file connects the fragment infrastructure to the finite cover-cost API.
The key local step in the Park--Vondrak proof is that minimal fragments split
into small and large parts, and cost subadditivity gives

  cost(H) <= cost(S_m(F*(H,W))) + cost(L_m(F*(H,W))).

No probabilistic estimate is used here.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/FragmentIteration.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment iteration bookkeeping.

This file packages the deterministic Park--Vondrak iteration skeleton.  It
does not prove the probabilistic large-fragment estimate; it only proves that
if the accumulated large-fragment cost losses are strictly smaller than the
initial cover cost, then the final cutoff-`1` small-fragment step forces an
original generator to be contained in the union of the exposed sets.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/Threshold.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 4.

# Status

This file formalizes the Park–Pham / Kahn–Kalai expectation-threshold package
used by the spread-disjointness layer.  The finite Boolean-family reductions,
fragment-cost iteration, and scalar snoc budget schedule are all proved in
`ParkPham/`; the exported theorem below has no project-level assumption
dependency.

# Classical content

The Kahn–Kalai expectation-threshold conjecture, proved by Jinyoung Park
and Huy Tuan Pham in 2022 (arXiv:2203.17207), states roughly:

  For every increasing family `U` on a finite ground set `X`, the actual
  threshold `p_c(U)` differs from the expectation threshold `q(U)` by at
  most a logarithmic factor:
        `p_c(U) ≤ C · q(U) · log(ℓ(U))`
  for an absolute constant `C` and a complexity parameter
  `ℓ(U) := max(2, max cardinality of minimal members of U)`.

In the finite form below we phrase the conclusion as: if `q` is an upper
bound on the expectation threshold (in the sense of `qSmallUpper`), then
at density `p = C · q · log(ℓ(U))` the product measure `muP X U p` is at
least `1/2`.

# Shape decision

The deep input is stated as an existential package at the exact threshold
`p = C_KK q log ell`, in the genuinely subcritical case `p < 1`.
The endpoint case `p = 1` is elementary and is proved below, using
`muP_one_of_nonempty_increasing`.  The "any larger `p`" downstream interface is
then derived using the finite density-monotonicity theorem `muP_mono_density`.

# Formalization status

The final scalar schedule uses constant block length `64` and power-of-two
cutoffs of length `Nat.log 2 m + 1`, reducing the recursive snoc budget to the
finite geometric bound `∑ (1/16)^(2^j) < 1/4`.
-/

/-! =============================================================
    Section from: Erdos/P202/ParkPham/ParkPhamTheorem.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 5.

Consequences of the Park–Pham threshold theorem for spread families:

1. `pSmall_mono_density`: `pSmall` decreases monotonically as `p` decreases.
2. `qSmallUpper_of_not_pSmall`: lifting `¬ pSmall at p₀` to
   `qSmallUpper X U p₀`.
3. `not_pSmall_of_spread`: the counting argument showing that the upper
   closure of a `κ`-spread family is not `p`-small at `p = κ⁻¹`. **Proved.**
4. `mu_at_partition_density_ge_half`: chains (3), (2), and
   `park_pham_threshold` to get `muP ≥ 1/2` at density `1/(2r)` when
   `κ ≥ Csp · r · log(ek)`. **Proved against the threshold package.**
-/

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-! ## Main consequence: muP ≥ 1/2 at partition density

The chain is:
1. `not_pSmall_of_spread` gives `¬ pSmall X (upClosureIn X A) (1/κ)`.
2. `qSmallUpper_of_not_pSmall` lifts to `qSmallUpper X U (1/κ)`.
3. `park_pham_threshold` gives `muP ≥ 1/2` at any density
   `≥ CKK · (1/κ) · log(ell U)`.
4. From `κ ≥ Csp · r · log(ek)` and `ell U ≤ max 2 k ≤ ek`, derive
   `CKK · (1/κ) · log(ell U) ≤ 1/(2r)` with `Csp := max 10 (8 · CKK)`.

The bookkeeping in step 4 is purely algebraic (log inequalities and a few
positivity arguments). It is isolated behind the named Park--Pham threshold
target for a focused subpass. -/

end

end ParkPham
end Erdos202

/-! =============================================================
    Section from: Erdos/P202/ParkPham/SpreadDisjointness.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 6.

Final spread-disjointness theorem via the random-partition argument.

# Strategy

Given a κ-spread, k-uniform, nonempty family A with
`κ ≥ Csp · r · log(ek)`:

1. By `mu_at_partition_density_ge_half`, the Bernoulli measure of
   `upClosureIn X A` at density `1/(2r)` is at least `1/2`.
2. Equivalently (via the random-partition / coloring identification): for
   a uniformly random coloring `c : X → Fin (2r)`, the expected number
   of color classes `c⁻¹(i)` that contain a member of A is at least `r`.
3. Hence there exists a coloring with at least `r` "successful" parts.
4. Pick one member of A inside each successful part. The parts are
   pairwise disjoint, so the chosen members are pairwise disjoint.

The translation from "muP ≥ 1/2" to "∃ r pairwise-disjoint members"
(steps 2-4) is purely finite/discrete bookkeeping with no analytic
content.  This file proves that bookkeeping directly, then combines it
with the named Park--Pham threshold package.
-/

/-! =============================================================
    Section from: Erdos/P202/SpreadCore.lean
    ============================================================= -/

/-
Erdős Problem 202 — Spread / dense-core layer.

The new ingredient in the May 2026 proof is the spread-core lemma replacing
the Erdős–Lovász / minimal-family loss in the BFV descending chain.

This file:
  * states the finite combinatorial spread-disjointness consequence of
    Park–Pham (Kahn–Kalai) as a derived theorem.
  * derives the dense-core corollary used downstream.

Park–Pham theorem reference: arXiv:2203.17207. We do NOT formalize the full
expectation-threshold theorem here; we isolate exactly the finite consequence
the descending chain needs.
-/

namespace Erdos202

open Finset
open scoped BigOperators

universe u

/-! ## Spread-disjointness (discharged via Park–Pham layer)

Definitions `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`
live in `Erdos.P202.SpreadDefs`. The finite spread-disjointness
consequence of Park–Pham is now proved as
`Erdos202.ParkPham.spread_disjointness_theorem`; the historical name
`spread_disjointness_input` is preserved here as a derived theorem so
downstream consumers (chain, dense-core, optimization) need no edits. -/

end Erdos202

/-! =============================================================
    Section from: Erdos/P202/BFV/Mertens.lean
    ============================================================= -/

/-
Erdős Problem 202 — Mertens / Euler-product estimate.

# Status

This file proves the consumer-shaped weighted-sum bound used by the BFV
omega-tail proof in `Erdos/P202/BFV/OmegaTail.lean`.

# Relation to P694's `mertens_product`

The repo's `Erdos/P694/Proof.lean:417` axiomatizes **Mertens' third theorem**
(the product form `∏_{p ≤ y} p/(p-1) ~ e^γ · log y`). P202 only needs a weak
Mertens-style upper bound `∑_{p ≤ y} 1/p = O(log log y)`, proved below from
Mathlib's Chebyshev upper bound for `Nat.primeCounting`. The sharp Mertens
second theorem is also derivable from Mertens 3rd by taking logs:
  `log ∏_{p ≤ y} (1 - 1/p)^{-1} = ∑_{p ≤ y} (1/p + 1/(2 p²) + …)
                                = ∑_{p ≤ y} 1/p + O(1)`.

P694's sharper product-form Mertens input remains a separate issue, but P202 no
longer depends on it.

# Classical content

The finite Hardy-Ramanujan sieve bookkeeping is proved in this file, as is the
weak reciprocal-prime upper bound:

* **A Mertens-type upper bound**: there exist constants `A > 0` and `C` such
   that for all sufficiently large `N`,
   `∑_{p prime, p ≤ N} (1 / p : ℝ) ≤ A * Real.log (Real.log N) + C`.
   Mertens' second theorem gives the sharp `A = 1`.  For this P202 consumer,
   any fixed `A` is enough because `BFVz N * log log N = sqrt(log N) = o(Z(N))`.
   In Mathlib `v4.27.0`, the prime-counting function `Nat.primeCounting` and
   Chebyshev's upper bound on it are available; the dyadic summation below
   packages them into the reciprocal-prime bound needed here.

Combining the proved finite sieve below with this Mertens input: with
`BFVz N := √(log N) / log log N`,
  `∏_{p ≤ N} (1 + BFVz N / p)
     ≤ Real.exp (BFVz N * ∑_{p ≤ N} 1 / p)
     ≤ Real.exp (BFVz N * (A * Real.log (Real.log N) + C))`,
which is `≤ Real.exp (ε * Zscale N)` eventually for any `ε > 0`, since
`BFVz N · log log N = √(log N) = Zscale N / √(log log N) = o(Zscale N)`.

# Where this is consumed

* `Erdos.P202.BFV.OmegaExact` → `Erdos.P202.BFV.OmegaCountInput` →
  supplies the historical `Erdos202.bfv_omega_count_input` interface.

-/

/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaTail.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV omega-tail estimates.

This file contains the elementary Rankin counting step used before the
BFV/Hardy-Ramanujan analytic input.  The Euler-product estimate is proved in
`Erdos.P202.BFV.Mertens`.
-/

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Rankin's inequality for omega tails

The BFV Rankin parameter `BFVz N := √(log N) / log log N` lives in
`Erdos.P202.BFV.Mertens`, alongside the weighted omega-sum estimate consumed
below. -/

end Erdos202

/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaExact.lean
    ============================================================= -/

/-
Erdos Problem 202 -- exact omega-count reduction.

This file reduces an exact omega level to the omega-tail estimate from
`OmegaTail.lean` and performs the scale algebra for the BFV `W` factor.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaCountInput.lean
    ============================================================= -/

/-
Erdos Problem 202 -- theorem-shaped BFV omega-count input.

This file exposes the theorem name intended to replace
`Erdos202.bfv_omega_count_input` in a later review step.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/PrimeIntervals.lean
    ============================================================= -/

/-
Erdos Problem 202 -- prime supply for the BFV lower construction.

This file defines the `dyadicPrimeInterval` used by the explicit lower
construction. The analytic lower bound on its cardinality lives in
`Erdos.P202.BFV.Chebyshev`; this file contains only definitions.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/Chebyshev.lean
    ============================================================= -/

/-
Erdős Problem 202 — Chebyshev-style dyadic-interval prime cardinality bound.

# Status

This file proves the prime-supply theorem consumed by the BFV lower path
construction.  The lower bound has a fixed positive Chebyshev constant, which
is enough for the `Lscale (-(1 + ε), N)` BFV lower-bound target.

# Classical content

Chebyshev (1850) proved that there exist absolute constants `c_1, c_2 > 0`
with `c_1 · y / log y ≤ π(y) ≤ c_2 · y / log y`. Subtracting gives, for
some absolute `c > 0`,
  `π(2y) − π(y) ≥ c · y / log y`  for all sufficiently large `y`.

Mathlib `v4.27.0` already has Chebyshev's `θ`-function bounds
(`Nat.theta_le`, `Nat.theta_le_id`, `Nat.id_lt_theta`, etc.) and the
prime-counting function `Nat.primeCounting`. What is NOT packaged is the
Chebyshev-style dyadic-interval lower bound `π(2y) − π(y) ≥ c · y / log y`
nor its `(1 − ε) · y / log y` PNT-strength refinement.

The earlier `(1 - ε)` PNT-strength target has been replaced by the fixed
positive constant `dyadicPrimeIntervalConstant = log 4 / 16`.  The proof below
uses central-binomial/Bertrand-style estimates rather than PNT.

# Where this is consumed

* `Erdos.P202.BFV.Chebyshev.dyadicPrimeInterval_card_lower_bound`
* downstream: `Erdos.P202.BFV.LowerPathConstruction.lowerPath_f_lower_bound_eventually`
  → `Erdos.P202.BFV.LowerBoundInput.bfv_lower_bound_theorem`
  → supplies the historical `Erdos202.bfv_lower_bound_input` interface.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/LowerPathScales.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower construction, source-aligned path scales.

This file is a non-consuming scaffold for replacing the current fixed-root
lower construction in `LowerConstruction.lean`.  The key point is the BFV
source scale:

* roughly `2 * M(N)` prime blocks,
* logarithmic gap about `(1 / 2) * log log N - sqrt (log log N)`,
* exact normalization `prod_i (2 * Y_i) = N`.

The existing rooted construction fixes a whole root block and is too small for
the lower-bound target.  These path scales are the product/capacity side of the
BFV Section 2 construction, isolated so the later refactor can proceed without
destabilizing the current proof path.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/LowerPathConstruction.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower construction, source-aligned rooted path family.

This file builds on `LowerPathScales.lean` and defines the finite objects for
the BFV-compatible lower-bound refactor.  It is intentionally not wired into
`LowerBoundInput.lean` yet: the live lower theorem still uses
`LowerConstruction.lean`.  The point here is to grow a fully proved replacement
around the corrected path scales.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/LowerBoundInput.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower-bound theorem.

This file proves the theorem with the same signature as
`Erdos202.bfv_lower_bound_input`, using the source-aligned rooted path lower
construction from `LowerPathConstruction.lean`.
-/

/-! =============================================================
    Section from: Erdos/P202/BFVInputs.lean
    ============================================================= -/

/-
Erdős Problem 202 — BFV inputs layer.

The BFV (de la Bretèche–Ford–Vandehey) input interface used by
the descending chain:

  * `bfv_omega_count_input`       : count of `n ≤ y` with `omega n = K - W`,
                                     uniform in K, W in the BFV range.
  * `bfv_lower_bound_input`       : matching lower bound `f(N) ≥ N · L(-(1+ε), N)`.

The omega-count and lower-bound historical names are theorem aliases to the
current BFV subdirectory replacements.  The pruning theorem is proved in
`Erdos.P202.BFV.Pruning`, which imports this file for the `PrunedData`
structure.
-/

/-! =============================================================
    Section from: Erdos/P202/P202Chain.lean
    ============================================================= -/

/-
Erdős Problem 202 — Descending chain.

Heart of the new contribution. Builds an `R`-step chain of pairwise coprime
prime-power blocks `P_1, …, P_R` such that every surviving modulus has
`P_{≤r}` as an exact divisor, residues agree mod `P_{≤r}`, and the size
inequality (PDF eq. 9)

  P_r ≤ (N / |Q'|) · exp((-d/2 + ε) Z) · (log N)^{W_{r-1}/2} · LowerOrder(N, ω(P_{≤r}))

holds at each step.

Combines the gcd criterion (`P202Basic.lean`), the dense-core lemma
(`SpreadCore.lean`), and the BFV ω-count input (`BFVInputs.lean`).
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/Filtering.lean
    ============================================================= -/

/-
Erdos Problem 202 -- finite filtering helpers for BFV pruning.

These lemmas are deliberately elementary.  They isolate the finite-set
bookkeeping used by the pruning step from the analytic BFV estimates.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/RadMultiplicity.lean
    ============================================================= -/

/-
Erdos Problem 202 -- radical multiplicity in BFV pruning.

For fixed radical, fixed omega, and bounded `hExp`, BFV Lemma 3.3 gives a
finite multiplicity bound.  This is a finite combinatorial theorem, but the
full exponent-vector encoding is kept isolated here so the final pruning file
only consumes a single clean interface.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/HExpRare.lean
    ============================================================= -/

/-
Erdos Problem 202 -- rarity of large hExp values in BFV pruning.

The paper-shaped BFV Lemma 3.2 estimate is isolated as a named theorem stub.
The super-`L` consumer form used by pruning is proved from that estimate by
explicit scale algebra.
-/

/-! =============================================================
    Section from: Erdos/P202/BFV/Pruning.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV pruning theorem.

This file proves `bfv_pruning_theorem`, the pruning interface consumed by the
upper-bound argument.
-/

namespace Erdos202

open Filter Finset

/-!
The pruning proof uses the following BFV-local inputs:

* `bfv_lower_bound_theorem` to compare deleted sets with a near-extremal `Q`.
* `bfv_omega_tail_theorem` to delete the large-omega tail.
* `hExp_rare_count_rankin_squarefull` to delete large hExp values.
* `rad_multiplicity_bfv33` and `choose_one_per_fiber_card_lower` to choose one
  representative per radical.

The remaining work in this file is epsilon bookkeeping: each deletion and each
pigeonhole loss is bounded by a small `Lscale(η, N)` factor, and the factors are
combined with `Lscale_add`.
-/

end Erdos202

/-! =============================================================
    Section from: Erdos/P202/P202Optimization.lean
    ============================================================= -/

/-
Erdős Problem 202 — Final optimization layer.

Converts the chain inequality into the upper bound `f(N) ≤ N · L(-(1-ε), N)`.

Key explicit replacements (versus the PDF):

  * `(π²/6)`-constants → `2`, via the elementary `∑_{ν=1}^m 1/ν² ≤ 2`.
  * `T = ∑ W_{r-1}` is bounded by `R K - R(R-1)/2` (no informal `O(R)`).
  * The single inequality `c σ - c²/4 ≤ σ²` is a square-completion.

The `o(1)` of the PDF is replaced by an explicit `η`-quantifier:
"for every `η > 0`, eventually `1 - η ≤ c σ_N - c²/4 + η`".
-/

/-! =============================================================
    Section from: Erdos/P202/P202Main.lean
    ============================================================= -/

/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input),
  * lower bound from `bfv_lower_bound_theorem`.

The historical omega-count and lower-bound input names now point to theorem
aliases.  The current non-core trust boundary is visible through
the check on `Erdos202.erdos_202`: the only project-level dependency is
the Park--Pham threshold package.

The check at the foot of this file audits the public path.
-/

namespace Erdos202

open Filter
open scoped BigOperators

/-! ## Dependency audit

The block below audits the public theorem path.  The expected output is only
the standard Mathlib core assumptions `propext`, `Classical.choice`, and
`Quot.sound`.
-/

end Erdos202

/-! ## Dependency audit -/

-- [propext, Classical.choice, Quot.sound]
-- Classical.choice, Quot.sound]

/-! ### Upstream module `ErdosProblems/Erdos1025.lean` (plby/lean-proofs) -/

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1025.
https://www.erdosproblems.com/forum/thread/1025

Informal authors:
- David Conlon
- Jacob Fox
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1025.md
-/

/-!
# Erdős Problem 1025

For every map from the unordered pairs of an `n`-element set to a point outside the
pair, let an independent set be a set containing no pair together with its image.
This file proves that the largest size which is guaranteed for every such map is
of order `sqrt n`.

The lower bound is the three-uniform case of Spencer's deletion argument.  The
upper bound is the square-grid construction of Conlon--Fox--Sudakov, specialized
to maps from pairs to points.
-/

open scoped BigOperators

open Filter Finset Function
open Asymptotics

noncomputable section

/-- The type of unordered pairs of distinct elements of `α`. -/
abbrev Pair (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

namespace Pair

variable {α β : Type*}

/-- The two-element finset underlying an unordered pair. -/
def vertices [DecidableEq α] (e : Pair α) : Finset α := e.1.toFinset

@[simp]
lemma card_vertices [DecidableEq α] (e : Pair α) : e.vertices.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.1 e.2

/-- Construct an unordered pair from two distinct elements. -/
def mk {x y : α} (h : x ≠ y) : Pair α :=
  ⟨s(x, y), by simpa only [Sym2.mk_isDiag_iff] using h⟩

@[simp]
lemma vertices_mk [DecidableEq α] {x y : α} (h : x ≠ y) :
    (mk h).vertices = {x, y} := by
  simp [vertices, mk, Sym2.toFinset_mk_eq]

/-- Transport unordered pairs along an equivalence. -/
def map (e : α ≃ β) : Pair α ≃ Pair β where
  toFun p := ⟨p.1.map e, by
    rw [Sym2.isDiag_map e.injective]
    exact p.2⟩
  invFun p := ⟨p.1.map e.symm, by
    rw [Sym2.isDiag_map e.symm.injective]
    exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv p := by
    apply Subtype.ext
    simp [Sym2.map_map]

end Pair

/-- The value of a set mapping never equals either endpoint of its input pair. -/
def AvoidsEndpoints {α : Type*} [DecidableEq α] (f : Pair α → α) : Prop :=
  ∀ e, f e ∉ e.vertices

/-- `X` is independent when it contains no input pair together with its image. -/
def Independent {α : Type*} [DecidableEq α] (f : Pair α → α) (X : Finset α) : Prop :=
  ∀ e, e.vertices ⊆ X → f e ∉ X

/-- `k` is universally guaranteed for maps on the canonical `n`-element set. -/
def Guaranteed (n k : ℕ) : Prop :=
  k ≤ n ∧ ∀ f : Pair (Fin n) → Fin n, AvoidsEndpoints f →
    ∃ X : Finset (Fin n), Independent f X ∧ k ≤ X.card

/-- The largest universally guaranteed independent-set size. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guaranteed n) n

lemma guaranteed_zero (n : ℕ) : Guaranteed n 0 := by
  refine ⟨Nat.zero_le n, ?_⟩
  intro f hf
  exact ⟨∅, by simp [Independent], Nat.zero_le _⟩

lemma g_spec (n : ℕ) : Guaranteed n (g n) := by
  classical
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le n) (guaranteed_zero n)

lemma le_g_of_guaranteed {n k : ℕ} (h : Guaranteed n k) : k ≤ g n := by
  classical
  exact Nat.le_findGreatest h.1 h

/-! ### Explicit finite Bernoulli averages

These helper lemmas keep the probabilistic argument as finite sums over a
powerset. -/

open Erdos202.ParkPham

lemma sum_bernoulliMass_indicator_superset {V : Type*} [DecidableEq V]
    (X T : Finset V) (hTX : T ⊆ X) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) = p ^ T.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) =
        muP X (upClosureIn X {T}) p := by
          rw [upClosureIn_singleton X T hTX]
          simp only [muP, Finset.mem_filter, Finset.mem_powerset]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro W hW
          simp [Finset.mem_powerset.mp hW]
    _ = p ^ T.card := muP_upClosure_single X T hTX hp0 hp1

lemma sum_bernoulliMass_contained_count {V : Type*} [DecidableEq V]
    (X : Finset V) (A : Finset (Finset V)) {k : ℕ}
    (hAX : ∀ T ∈ A, T ⊆ X) (hcard : ∀ T ∈ A, T.card = k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
      p ^ k * A.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ T ∈ A, bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [← Finset.mul_sum, Finset.sum_boole]
    _ = ∑ T ∈ A,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ A, p ^ T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          exact sum_bernoulliMass_indicator_superset X T (hAX T hT) hp0 hp1
    _ = p ^ k * A.card := by
          rw [Finset.sum_congr rfl (fun T hT => by rw [hcard T hT])]
          simp [mul_comm]

lemma sum_bernoulliMass_card {V : Type*}
    (X : Finset V) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
      p * X.card := by
  classical
  calc
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ v ∈ X, bernoulliMass X W p * (if v ∈ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hWX : W ⊆ X := Finset.mem_powerset.mp hW
            have hfilter : X.filter (· ∈ W) = W := by
              ext v
              simp only [Finset.mem_filter]
              constructor
              · exact And.right
              · intro hv
                exact ⟨hWX hv, hv⟩
            rw [show (W.card : ℝ) =
                ∑ v ∈ X, if v ∈ W then (1 : ℝ) else 0 by
              rw [Finset.sum_boole]
              rw [hfilter]]
            rw [Finset.mul_sum]
    _ = ∑ v ∈ X,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if ({v} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro W hW
          simp
    _ = ∑ _v ∈ X, p := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa using sum_bernoulliMass_indicator_superset X ({v} : Finset V)
            (by simpa using hv) hp0 hp1
    _ = p * X.card := by simp [mul_comm]

lemma exists_ge_of_bernoulli_average_ge {V : Type*}
    (X : Finset V) {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset V → ℝ)
    (havg : a ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W) :
    ∃ W ∈ X.powerset, a ≤ F W := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum_lt :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) <
        ∑ W ∈ X.powerset, bernoulliMass X W p * a := by
    apply Finset.sum_lt_sum
    · intro W hW
      exact mul_le_mul_of_nonneg_left (le_of_lt (hnone W hW))
        (bernoulliMass_nonneg hp0 hp1)
    · have hone : (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := by
        symm
        exact sum_bernoulliMass_eq_one X (by ring)
      have hposmass : ∃ W ∈ X.powerset, 0 < bernoulliMass X W p := by
        by_contra hz
        push Not at hz
        have hallzero : ∀ W ∈ X.powerset, bernoulliMass X W p = 0 := by
          intro W hW
          exact le_antisymm (hz W hW) (bernoulliMass_nonneg hp0 hp1)
        have : (1 : ℝ) = 0 := by
          calc
            (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := hone
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro W hW
              exact hallzero W hW
        norm_num at this
      rcases hposmass with ⟨W, hW, hmass⟩
      refine ⟨W, hW, ?_⟩
      exact mul_lt_mul_of_pos_left (hnone W hW) hmass
  have hconst :
      (∑ W ∈ X.powerset, bernoulliMass X W p * a) = a := by
    rw [← Finset.sum_mul, sum_bernoulliMass_eq_one X (by ring), one_mul]
  linarith

/-! ## The Spencer lower bound -/

/-- The three-element set generated by a pair and the value of the map. -/
def triple {α : Type*} [DecidableEq α] (f : Pair α → α) (e : Pair α) : Finset α :=
  insert (f e) e.vertices

lemma card_triple {α : Type*} [DecidableEq α] {f : Pair α → α}
    (hf : AvoidsEndpoints f) (e : Pair α) : (triple f e).card = 3 := by
  rw [triple, card_insert_of_notMem (hf e), Pair.card_vertices]

/-- The finite family of all triples generated by a set mapping. -/
def tripleFamily {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) : Finset (Finset α) :=
  Finset.univ.image (triple f)

lemma mem_tripleFamily {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) (e : Pair α) : triple f e ∈ tripleFamily f := by
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

lemma tripleFamily_card_le_sq {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) :
    (tripleFamily f).card ≤ (Fintype.card α) ^ 2 := by
  calc
    (tripleFamily f).card ≤ Fintype.card (Pair α) := by
      simpa [tripleFamily] using Finset.card_image_le (s := (Finset.univ : Finset (Pair α)))
        (f := triple f)
    _ = (Fintype.card α).choose 2 := Sym2.card_subtype_not_diag
    _ ≤ (Fintype.card α) ^ 2 := Nat.choose_le_pow _ _

/-- Bernoulli sampling followed by deleting one vertex from every surviving
three-set.  This is the finite probabilistic core of Spencer's lower bound. -/
lemma exists_threeSetFree_large {α : Type*} [Fintype α]
    (A : Finset (Finset α))
    (hAcard : ∀ T ∈ A, T.card = 3)
    (hcount : A.card ≤ (Fintype.card α) ^ 2)
    (hn : 1 ≤ Fintype.card α) :
    ∃ U : Finset α,
      (∀ T ∈ A, ¬ T ⊆ U) ∧
      Real.sqrt (Fintype.card α : ℝ) / 4 ≤ (U.card : ℝ) := by
  classical
  let n : ℕ := Fintype.card α
  let X : Finset α := Finset.univ
  let p : ℝ := 1 / (2 * Real.sqrt n)
  let Y : Finset α → ℝ := fun W =>
    (W.card : ℝ) - ((A.filter (fun T => T ⊆ W)).card : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [Real.sq_sqrt (le_of_lt hn0)]
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    have hden : 0 < 2 * Real.sqrt (n : ℝ) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hAX : ∀ T ∈ A, T ⊆ X := by
    intro T hT
    exact Finset.subset_univ T
  have havg_eq :
      (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        p * n - p ^ 3 * A.card := by
    rw [show (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) -
        ∑ W ∈ X.powerset,
          bernoulliMass X W p * ((A.filter (fun T => T ⊆ W)).card : ℝ) by
      simp only [Y, mul_sub, Finset.sum_sub_distrib]]
    rw [sum_bernoulliMass_card X hp0 hp1,
      sum_bernoulliMass_contained_count X A hAX hAcard hp0 hp1]
    simp [X, n]
  have hcount_real : (A.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hcount
  have havg_lower :
      Real.sqrt (n : ℝ) / 4 ≤ p * n - p ^ 3 * A.card := by
    dsimp [p]
    have hp3 : 0 ≤ (1 / (2 * Real.sqrt (n : ℝ))) ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcount_real hp3
    field_simp
    nlinarith [hsqrt_sq]
  have havg :
      Real.sqrt (n : ℝ) / 4 ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * Y W := by
    rw [havg_eq]
    exact havg_lower
  obtain ⟨W, hWX, hWY⟩ :=
    exists_ge_of_bernoulli_average_ge X hp0 hp1 Y havg
  let B : Finset (Finset α) := A.filter (fun T => T ⊆ W)
  let pick : {T // T ∈ B} → α := fun T =>
    Classical.choose <| by
      have hTcard : T.1.card = 3 := hAcard T.1 (Finset.mem_filter.mp T.2).1
      exact Finset.card_pos.mp (hTcard.trans_gt (by norm_num))
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hTcard : T.1.card = 3 := hAcard T.1 (Finset.mem_filter.mp T.2).1
      exact Finset.card_pos.mp (hTcard.trans_gt (by norm_num))
  let deleted : Finset α := B.attach.image pick
  let U : Finset α := W \ deleted
  have hdeletedW : deleted ⊆ W := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    exact (Finset.mem_filter.mp T.2).2 (hpick_mem T)
  have hUcard_nat : W.card - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      W.card - B.card ≤ W.card - deleted.card := Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simpa [U] using Finset.card_sdiff_of_subset hdeletedW
  have hYU : Y W ≤ (U.card : ℝ) := by
    by_cases hBW : B.card ≤ W.card
    · rw [show Y W = ((W.card - B.card : ℕ) : ℝ) by
        simp only [Y]
        exact (Nat.cast_sub hBW).symm]
      exact_mod_cast hUcard_nat
    · have hnonpos : Y W ≤ 0 := by
        simp only [Y]
        exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_not_ge hBW)
      exact hnonpos.trans (Nat.cast_nonneg U.card)
  refine ⟨U, ?_, hWY.trans hYU⟩
  intro T hTA hTU
  have hTW : T ⊆ W := hTU.trans Finset.sdiff_subset
  have hTB : T ∈ B := Finset.mem_filter.mpr ⟨hTA, hTW⟩
  let TT : {T // T ∈ B} := ⟨T, hTB⟩
  have hpdel : pick TT ∈ deleted :=
    Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
  have hpU : pick TT ∈ U := hTU (hpick_mem TT)
  exact (Finset.mem_sdiff.mp hpU).2 hpdel

/-- Every admissible set mapping has an independent set of real cardinality
at least one quarter of the square root of the order. -/
lemma exists_independent_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) (hf : AvoidsEndpoints f)
    (hn : 1 ≤ Fintype.card α) :
    ∃ U : Finset α, Independent f U ∧
      Real.sqrt (Fintype.card α : ℝ) / 4 ≤ (U.card : ℝ) := by
  classical
  let A := tripleFamily f
  obtain ⟨U, hfree, hcard⟩ := exists_threeSetFree_large A
    (fun T hT => by
      rcases Finset.mem_image.mp hT with ⟨e, he, rfl⟩
      exact card_triple hf e)
    (tripleFamily_card_le_sq f) hn
  refine ⟨U, ?_, hcard⟩
  intro e he hfe
  exact hfree (triple f e) (mem_tripleFamily f e) <| by
    intro x hx
    simp only [triple, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hfe
    · exact he hx

/-! ## The square-grid construction -/

/-- A square grid together with some extra vertices. -/
abbrev Padded (q s : ℕ) := (Fin q × Fin q) ⊕ Fin s

lemma exists_outside_pair {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) : ∃ x : α, x ∉ e.vertices := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset α) ⊆ e.vertices := by
    intro x hx
    exact h x
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ, Pair.card_vertices] at this
  omega

/-- A chosen third point outside an unordered pair. -/
def thirdVertex {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) : α :=
  Classical.choose (exists_outside_pair hcard e)

lemma thirdVertex_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) :
    thirdVertex hcard e ∉ e.vertices :=
  Classical.choose_spec (exists_outside_pair hcard e)

/-- A symmetric fallback value.  Only its off-diagonal behavior is used. -/
def fallbackSym {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Sym2 α) : α :=
  if he : ¬ e.IsDiag then thirdVertex hcard ⟨e, he⟩ else e.out.1

lemma fallbackSym_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) :
    fallbackSym hcard e.1 ∉ e.vertices := by
  simp only [fallbackSym, e.2]
  exact thirdVertex_not_mem hcard e

lemma fallbackSym_mk_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) {a b : α} (hab : a ≠ b) :
    fallbackSym hcard s(a, b) ∉ ({a, b} : Finset α) := by
  simpa [Pair.mk, Pair.vertices, Sym2.toFinset_mk_eq] using
    fallbackSym_not_mem hcard (Pair.mk hab)

/-- The crossed-corner rule, with the symmetric fallback in all other cases. -/
def gridValue {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    (a b : Padded q s) : Padded q s :=
  match a, b with
  | Sum.inl a, Sum.inl b =>
      if a.1 < b.1 ∧ a.2 ≠ b.2 then Sum.inl (a.1, b.2)
      else if b.1 < a.1 ∧ b.2 ≠ a.2 then Sum.inl (b.1, a.2)
      else fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inl b)
  | _, _ => fallbackSym hcard s(a, b)

lemma gridValue_comm {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    (a b : Padded q s) : gridValue hcard a b = gridValue hcard b a := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          by_cases h₁ : a.1 < b.1 ∧ a.2 ≠ b.2
          · have h₂ : ¬ (b.1 < a.1 ∧ b.2 ≠ a.2) := by
              intro h₂
              exact (asymm h₁.1 h₂.1)
            rw [gridValue, gridValue, if_pos h₁, if_neg h₂, if_pos h₁]
          · by_cases h₂ : b.1 < a.1 ∧ b.2 ≠ a.2
            · rw [gridValue, gridValue, if_neg h₁, if_pos h₂, if_pos h₂]
            · have heq : s((Sum.inl a : Padded q s), Sum.inl b) =
                  s((Sum.inl b : Padded q s), Sum.inl a) := Sym2.eq_swap
              rw [gridValue, gridValue, if_neg h₁, if_neg h₂, if_neg h₂, if_neg h₁,
                heq]
      | inr b =>
          have heq : s((Sum.inl a : Padded q s), Sum.inr b) =
              s((Sum.inr b : Padded q s), Sum.inl a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inr b) =
            fallbackSym hcard s((Sum.inr b : Padded q s), Sum.inl a)
          rw [heq]
  | inr a =>
      cases b with
      | inl b =>
          have heq : s((Sum.inr a : Padded q s), Sum.inl b) =
              s((Sum.inl b : Padded q s), Sum.inr a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inl b) =
            fallbackSym hcard s((Sum.inl b : Padded q s), Sum.inr a)
          rw [heq]
      | inr b =>
          have heq : s((Sum.inr a : Padded q s), Sum.inr b) =
              s((Sum.inr b : Padded q s), Sum.inr a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inr b) =
            fallbackSym hcard s((Sum.inr b : Padded q s), Sum.inr a)
          rw [heq]

/-- The CFS grid set mapping. -/
def gridMap {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s)) :
    Pair (Padded q s) → Padded q s := fun e =>
  e.1.lift ⟨gridValue hcard, gridValue_comm hcard⟩

@[simp]
lemma gridMap_mk {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {a b : Padded q s} (hab : a ≠ b) :
    gridMap hcard (Pair.mk hab) = gridValue hcard a b := by
  simp [gridMap, Pair.mk]

lemma gridValue_corner {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {x x' y z : Fin q} (hxx : x < x') (hzy : z ≠ y) :
    gridValue hcard (Sum.inl (x, z)) (Sum.inl (x', y)) = Sum.inl (x, y) := by
  rw [gridValue, if_pos ⟨hxx, hzy⟩]

lemma gridValue_not_mem {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {a b : Padded q s} (hab : a ≠ b) :
    gridValue hcard a b ∉ ({a, b} : Finset (Padded q s)) := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          by_cases h₁ : a.1 < b.1 ∧ a.2 ≠ b.2
          · rw [gridValue, if_pos h₁]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            constructor
            · intro heq
              have hsnd := congrArg Prod.snd (Sum.inl.inj heq)
              exact h₁.2 hsnd.symm
            · intro heq
              have hfst := congrArg Prod.fst (Sum.inl.inj heq)
              exact (ne_of_lt h₁.1) hfst
          · by_cases h₂ : b.1 < a.1 ∧ b.2 ≠ a.2
            · rw [gridValue, if_neg h₁, if_pos h₂]
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              constructor
              · intro heq
                have hfst := congrArg Prod.fst (Sum.inl.inj heq)
                exact (ne_of_lt h₂.1) hfst
              · intro heq
                have hsnd := congrArg Prod.snd (Sum.inl.inj heq)
                exact h₂.2 hsnd.symm
            · rw [gridValue, if_neg h₁, if_neg h₂]
              exact fallbackSym_mk_not_mem hcard hab
      | inr b =>
          change fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inr b) ∉
            ({Sum.inl a, Sum.inr b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab
  | inr a =>
      cases b with
      | inl b =>
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inl b) ∉
            ({Sum.inr a, Sum.inl b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab
      | inr b =>
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inr b) ∉
            ({Sum.inr a, Sum.inr b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab

lemma gridMap_avoids {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s)) :
    AvoidsEndpoints (gridMap hcard) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      have hab : a ≠ b := by
        rwa [Sym2.mk_isDiag_iff] at he
      simpa [gridMap, Pair.vertices, Sym2.toFinset_mk_eq] using
        gridValue_not_mem hcard hab

/-- A point is the unique selected point in its first-coordinate fibre. -/
def UniqueFirst {q : ℕ} (C : Finset (Fin q × Fin q)) (p : Fin q × Fin q) : Prop :=
  ∀ r ∈ C, r.1 = p.1 → r = p

/-- The specialized CFS pruning argument: the core contributes at most `2q`
points and the padded part contributes at most `s` points. -/
lemma gridMap_independent_card {q s : ℕ}
    (hcard : 3 ≤ Fintype.card (Padded q s))
    (X : Finset (Padded q s)) (hX : Independent (gridMap hcard) X) :
    X.card ≤ 2 * q + s := by
  classical
  let C : Finset (Fin q × Fin q) := X.toLeft
  let U : Finset (Fin q × Fin q) := C.filter (UniqueFirst C)
  let V : Finset (Fin q × Fin q) := C.filter (fun p => ¬ UniqueFirst C p)
  have hU : U.card ≤ q := by
    calc
      U.card ≤ (Finset.univ : Finset (Fin q)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro p hp
          exact Finset.mem_univ p.1
        · intro p hp p' hp' heq
          have hp_unique : UniqueFirst C p := (Finset.mem_filter.mp hp).2
          exact (hp_unique p' (Finset.mem_filter.mp hp').1 heq.symm).symm
      _ = q := by simp
  have no_equal_second_of_lt :
      ∀ {p p' : Fin q × Fin q}, p ∈ V → p' ∈ V → p.2 = p'.2 → p.1 < p'.1 → False := by
    intro p p' hp hp' hsnd hfst
    have hp_not_unique : ¬ UniqueFirst C p := (Finset.mem_filter.mp hp).2
    simp only [UniqueFirst] at hp_not_unique
    push Not at hp_not_unique
    obtain ⟨r, hrC, hrfst, hrne⟩ := hp_not_unique
    have hrsnd : r.2 ≠ p'.2 := by
      intro hrsnd
      apply hrne
      apply Prod.ext
      · exact hrfst
      · exact hrsnd.trans hsnd.symm
    have hr_lt : r.1 < p'.1 := by simpa [hrfst] using hfst
    have hep : (Sum.inl r : Padded q s) ≠ Sum.inl p' := by
      intro heq
      have : r = p' := Sum.inl.inj heq
      exact (ne_of_lt hr_lt) (congrArg Prod.fst this)
    have hrX : (Sum.inl r : Padded q s) ∈ X := by simpa [C] using hrC
    have hp'X : (Sum.inl p' : Padded q s) ∈ X := by
      simpa [C] using (Finset.mem_filter.mp hp').1
    have hpX : (Sum.inl p : Padded q s) ∈ X := by
      simpa [C] using (Finset.mem_filter.mp hp).1
    have hendpoints : (Pair.mk hep).vertices ⊆ X := by
      simp only [Pair.vertices_mk, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hrX, hp'X⟩
    have hout := hX (Pair.mk hep) hendpoints
    have hcorner : gridMap hcard (Pair.mk hep) = (Sum.inl p : Padded q s) := by
      rw [gridMap_mk, gridValue_corner hcard hr_lt hrsnd]
      exact congrArg Sum.inl (Prod.ext hrfst hsnd.symm)
    exact hout (hcorner ▸ hpX)
  have hV : V.card ≤ q := by
    calc
      V.card ≤ (Finset.univ : Finset (Fin q)).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro p hp
          exact Finset.mem_univ p.2
        · intro p hp p' hp' hsnd
          by_cases hfst : p.1 = p'.1
          · exact Prod.ext hfst hsnd
          · rcases lt_or_gt_of_ne hfst with hlt | hgt
            · exact False.elim (no_equal_second_of_lt hp hp' hsnd hlt)
            · exact False.elim (no_equal_second_of_lt hp' hp hsnd.symm hgt)
      _ = q := by simp
  have hC : C.card ≤ 2 * q := by
    have hpartition := C.card_filter_add_card_filter_not (UniqueFirst C)
    have hUV : U.card + V.card = C.card := by simpa [U, V] using hpartition
    omega
  have hright : X.toRight.card ≤ s := by
    calc
      X.toRight.card ≤ (Finset.univ : Finset (Fin s)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = s := by simp
  have hsplit := Finset.card_toLeft_add_card_toRight (u := X)
  change X.toLeft.card ≤ 2 * q at hC
  omega

/-! ## Transport and padding -/

lemma sym2_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : Sym2 α) :
    (p.map e).toFinset = p.toFinset.map e.toEmbedding := by
  induction p using Sym2.ind with
  | h x y =>
      simp [Sym2.toFinset_mk_eq, Sym2.map_mk]

@[simp]
lemma Pair.vertices_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : Pair α) :
    ((Pair.map e) p).vertices = p.vertices.map e.toEmbedding := by
  exact sym2_toFinset_map e p.1

/-- Transport a set mapping along an equivalence of vertex types. -/
def transportMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Pair α → α) : Pair β → β := fun p =>
  e (f ((Pair.map e).symm p))

lemma transportMap_avoids {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {f : Pair α → α} (hf : AvoidsEndpoints f) :
    AvoidsEndpoints (transportMap e f) := by
  intro p hp
  let p' : Pair α := (Pair.map e).symm p
  have hverts : p.vertices = p'.vertices.map e.toEmbedding := by
    have h := Pair.vertices_map e p'
    simpa [p'] using h
  rw [hverts] at hp
  have : f p' ∈ p'.vertices := by simpa [transportMap, p'] using hp
  exact hf p' this

/-- Pulling an independent set back along an equivalence preserves independence. -/
lemma independent_map_symm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Pair α → α) (X : Finset β)
    (hX : Independent (transportMap e f) X) :
    Independent f (X.map e.symm.toEmbedding) := by
  intro p hp hfp
  let pe : Pair β := Pair.map e p
  have hpe : pe.vertices ⊆ X := by
    intro x hx
    rw [Pair.vertices_map] at hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hypre : y ∈ X.map e.symm.toEmbedding := hp hy
    simpa using hypre
  have hout : transportMap e f pe ∉ X := hX pe hpe
  apply hout
  have : e (f p) ∈ X := by simpa using hfp
  simpa [transportMap, pe] using this

lemma padded_card (q s : ℕ) : Fintype.card (Padded q s) = q * q + s := by
  simp [Padded]

/-- For every `n ≥ 4`, the padded square grid supplies an admissible mapping
whose independent sets have size at most `4 * floor(sqrt n)`. -/
lemma upper_witness (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : Pair (Fin n) → Fin n,
      AvoidsEndpoints f ∧
      ∀ X : Finset (Fin n), Independent f X → X.card ≤ 4 * Nat.sqrt n := by
  classical
  let q : ℕ := Nat.sqrt n
  let s : ℕ := n - q * q
  have hsq : q * q ≤ n := by simpa [q] using Nat.sqrt_le n
  have hs : s ≤ 2 * q := by
    have hadd : n ≤ q * q + q + q := by simpa [q] using Nat.sqrt_le_add n
    dsimp [s]
    omega
  have hcard_eq : Fintype.card (Padded q s) = n := by
    rw [padded_card]
    dsimp [s]
    omega
  have hcard : 3 ≤ Fintype.card (Padded q s) := by
    rw [hcard_eq]
    omega
  let e : Padded q s ≃ Fin n := Fintype.equivOfCardEq (by simpa using hcard_eq)
  let f : Pair (Fin n) → Fin n := transportMap e (gridMap hcard)
  refine ⟨f, transportMap_avoids e (gridMap_avoids hcard), ?_⟩
  intro X hX
  let X' : Finset (Padded q s) := X.map e.symm.toEmbedding
  have hX' : Independent (gridMap hcard) X' := by
    exact independent_map_symm e (gridMap hcard) X hX
  have hgrid : X'.card ≤ 2 * q + s := gridMap_independent_card hcard X' hX'
  have hXcard : X'.card = X.card := by simp [X']
  rw [hXcard] at hgrid
  simpa [q] using hgrid.trans (by omega : 2 * q + s ≤ 4 * q)

lemma g_upper (n : ℕ) (hn : 4 ≤ n) : g n ≤ 4 * Nat.sqrt n := by
  obtain ⟨f, hf, hbound⟩ := upper_witness n hn
  obtain ⟨X, hX, hgX⟩ := (g_spec n).2 f hf
  exact hgX.trans (hbound X hX)

/-! ## Packaging the two estimates -/

/-- The integer part of one quarter of the real square root is universally
guaranteed. -/
lemma guaranteed_floor_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Guaranteed n ⌊Real.sqrt (n : ℝ) / 4⌋₊ := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · apply Nat.floor_le_of_le
    nlinarith
  · intro f hf
    have hnfin : 1 ≤ Fintype.card (Fin n) := by simpa using hn
    obtain ⟨U, hU, hcard⟩ := exists_independent_sqrt f hf hnfin
    refine ⟨U, hU, ?_⟩
    have hfloor :
        ((⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) / 4 :=
      Nat.floor_le (by positivity)
    have hcard' : Real.sqrt (n : ℝ) / 4 ≤ (U.card : ℝ) := by
      simpa using hcard
    have hfloor' : ((⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (U.card : ℝ) :=
      hfloor.trans hcard'
    exact_mod_cast hfloor'

lemma floor_sqrt_le_g (n : ℕ) (hn : 1 ≤ n) :
    ⌊Real.sqrt (n : ℝ) / 4⌋₊ ≤ g n :=
  le_g_of_guaranteed (guaranteed_floor_sqrt n hn)

lemma sqrt_le_eight_g (n : ℕ) (hn : 64 ≤ n) :
    Real.sqrt (n : ℝ) ≤ 8 * (g n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hsqrt8 : (8 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hn
  have hfloor_lt :
      Real.sqrt (n : ℝ) / 4 <
        (⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor_g :
      (⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℝ) ≤ (g n : ℝ) := by
    exact_mod_cast floor_sqrt_le_g n hn1
  nlinarith

lemma g_real_upper (n : ℕ) (hn : 4 ≤ n) :
    (g n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
  have hnat : (g n : ℝ) ≤ 4 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast g_upper n hn
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  exact hnat.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))

lemma g_isBigO_sqrt :
    (fun n : ℕ ↦ (g n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hg0 : 0 ≤ (g n : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hg0, abs_of_nonneg hs0] using
    g_real_upper n hn

lemma sqrt_isBigO_g :
    (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (g n : ℝ)) := by
  refine IsBigO.of_bound 8 ?_
  filter_upwards [Filter.eventually_ge_atTop 64] with n hn
  have hg0 : 0 ≤ (g n : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hg0, abs_of_nonneg hs0] using
    sqrt_le_eight_g n hn

/-- Erdős Problem 1025: the guaranteed independent-set size is of order
the square root of the number of vertices. -/
theorem erdos_1025 :
    (fun n : ℕ ↦ (g n : ℝ)) =Θ[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  exact ⟨g_isBigO_sqrt, sqrt_isBigO_g⟩

end

#print axioms erdos_1025
-- 'Erdos1025.erdos_1025' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1025
