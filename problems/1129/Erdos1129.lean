import Mathlib

namespace Erdos1129

/-
# Erdős Problem 1129

For $x_1,\ldots,x_n\in [-1,1]$ let
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$. Describe which choice of $x_i$
minimise
$$\Lambda(x_1,\ldots,x_n)=\max_{x\in [-1,1]} \sum_k \lvert l_k(x)\rvert.$$

The minimisers are characterised by the work of Kilgore [Ki77] and de Boor and Pinkus
[dBPi78] on the conjecture of Bernstein and Erdős. `erdos_1129` states the complete answer for
distinct nodes, with the extreme nodes free to move: a family of at least two nodes minimises
$\Lambda$ if and only if the maxima of $\sum_k \lvert l_k \rvert$ between consecutive nodes are all
equal and its values at $-1$ and $1$ do not exceed that common maximum; and a single node is
always optimal, with $\Lambda = 1$. `NodeFamily n` is $n$ distinct nodes in $[-1,1]$,
`lagrangeFundamental` is $l_k$, and `lebesgueOn nodes (-1) 1` is $\Lambda$.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000936), building on
the de Boor--Pinkus development of `randyxian08/jsp000958-lean`, whose modules are vendored
unchanged. The 32 modules forming the closure of `erdos_1129` are flattened here in dependency
order. `erdos_1129` is added here: it combines upstream's
`minimizer_iff_equioscillating_and_controlled_tails` and `singleton_nodes_optimal`, and adds
no mathematical content.

Declarations that `erdos_1129` does not depend on have been removed.
-/

/-! ### Upstream module `Randy1153/Statement.lean` -/

/-!
# The statement of Randy problem 1153

This file gives an independent, literal formalization of the problem.  A
`NodeFamily n` consists of exactly `n` pairwise distinct real interpolation
nodes in `[-1, 1]`.  The Lagrange fundamental functions and their associated
Lebesgue function are exposed below before the asymptotic target is stated.

The informal expression `o(1)` is represented by an epsilon/eventual
quantifier.  Its threshold may depend on the fixed interval and on epsilon,
but is chosen before the node family, so the assertion is uniform over all
node configurations.
-/

namespace Randy1153

open _root_.Polynomial

noncomputable section

/-- An injectively enumerated family of exactly `n` nodes in `[-1, 1]`. -/
structure NodeFamily (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_Icc : ∀ i, point i ∈ Set.Icc (-1 : ℝ) 1

/-- The `k`th Lagrange fundamental polynomial for `nodes`. -/
def lagrangeBasis {n : ℕ} (nodes : NodeFamily n) (k : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes.point k

/-- The source formula for the `k`th Lagrange fundamental function:

`∏ i ≠ k, (t - xᵢ) / (xₖ - xᵢ)`.
-/
def lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n)
    (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (t - nodes.point i) / (nodes.point k - nodes.point i)

/-- `lagrangeBasis` is visibly the product of its normalized linear factors. -/
lemma lagrangeBasis_eq_product {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeBasis nodes k =
      ∏ i ∈ Finset.univ.erase k,
        (Polynomial.X - Polynomial.C (nodes.point i)) *
          Polynomial.C (nodes.point k - nodes.point i)⁻¹ := by
  classical
  simp only [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor]
  apply Finset.prod_congr rfl
  intro i _
  exact mul_comm _ _

/-- Evaluating the polynomial gives the literal fundamental-function formula. -/
lemma lagrangeBasis_eval {n : ℕ} (nodes : NodeFamily n) (k : Fin n) (t : ℝ) :
    (lagrangeBasis nodes k).eval t = lagrangeFundamental nodes k t := by
  classical
  rw [lagrangeBasis_eq_product]
  simp only [lagrangeFundamental, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv]

/-- A fundamental function is one at its own node. -/
@[simp]
lemma lagrangeBasis_eval_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).eval (nodes.point k) = 1 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_self nodes.injective.injOn (Finset.mem_univ k))

/-- A fundamental function vanishes at every other node. -/
@[simp]
lemma lagrangeBasis_eval_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    (lagrangeBasis nodes k).eval (nodes.point j) = 0 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_of_ne (s := Finset.univ) (v := nodes.point)
      (i := k) (j := j) hjk.symm (Finset.mem_univ j))

/-- The Lebesgue function associated to a node family. -/
def lebesgueFunction {n : ℕ} (nodes : NodeFamily n) (t : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeFundamental nodes k t|

/-- Every Lagrange fundamental function is continuous. -/
lemma continuous_lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    Continuous (lagrangeFundamental nodes k) := by
  exact (lagrangeBasis nodes k).continuous.congr fun t => lagrangeBasis_eval nodes k t

/-- A finite sum of absolute values of fundamental functions is continuous. -/
lemma continuous_lebesgueFunction {n : ℕ} (nodes : NodeFamily n) :
    Continuous (lebesgueFunction nodes) := by
  classical
  exact continuous_finset_sum Finset.univ fun k _ =>
    (continuous_lagrangeFundamental nodes k).abs

/-- The supremum of the Lebesgue function on the closed interval `[a, b]`.
For the nonempty intervals used in `Target`, continuity makes this supremum a
maximum; using `sSup` keeps the statement independent of a chosen maximizer. -/
def lebesgueOn {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : ℝ :=
  sSup (lebesgueFunction nodes '' Set.Icc a b)

/-- On a nonempty closed interval, `lebesgueOn` is attained by the Lebesgue
function and is an upper bound for every other value on that interval. -/
lemma exists_lebesgueOn_eq_and_ge {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ t ∈ Set.Icc a b,
      lebesgueOn nodes a b = lebesgueFunction nodes t ∧
        ∀ u ∈ Set.Icc a b, lebesgueFunction nodes u ≤ lebesgueFunction nodes t := by
  simpa only [lebesgueOn] using
    (isCompact_Icc.exists_sSup_image_eq_and_ge (Set.nonempty_Icc.mpr hab)
      (continuous_lebesgueFunction nodes).continuousOn)

end

end Randy1153

/-! ### Upstream module `Randy1153/Basic.lean` -/

/-!
# Basic facts about the Randy 1153 interpolation objects

This module develops elementary consequences of the frozen statement
interface.  It does not introduce a second representation of nodes or of the
Lagrange and Lebesgue functions.
-/

namespace Randy1153

noncomputable section

/-- Two node families with the same enumerating function are equal; the
remaining fields are propositions. -/
@[ext]
lemma NodeFamily.ext {n : ℕ} {x y : NodeFamily n} (h : x.point = y.point) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The literal fundamental function is one at its own node. -/
@[simp]
lemma lagrangeFundamental_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeFundamental nodes k (nodes.point k) = 1 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_self nodes k

/-- The literal fundamental function vanishes at every other node. -/
@[simp]
lemma lagrangeFundamental_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    lagrangeFundamental nodes k (nodes.point j) = 0 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_of_ne nodes hjk

/-- At every interpolation node, the Lebesgue function equals one. -/
@[simp]
lemma lebesgueFunction_at_node {n : ℕ} (nodes : NodeFamily n) (j : Fin n) :
    lebesgueFunction nodes (nodes.point j) = 1 := by
  classical
  rw [lebesgueFunction, Fintype.sum_eq_single j]
  · simp
  · intro k hjk
    simp [lagrangeFundamental_of_ne nodes hjk.symm]

end

end Randy1153

/-! ### Upstream module `Randy1153/NodeOrder.lean` -/

/-!
# Ordering and reindexing node families

The public `NodeFamily` remains permutation invariant.  This module supplies
an internal strictly increasing representation, together with checked
transport lemmas showing that Lagrange and Lebesgue data do not depend on the
enumeration.
-/

namespace Randy1153

noncomputable section

namespace NodeFamily

/-- Reindex a node family by a permutation of `Fin n`. -/
def reindex {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) : NodeFamily n where
  point := nodes.point ∘ e
  injective := nodes.injective.comp e.injective
  mem_Icc i := nodes.mem_Icc (e i)

@[simp]
lemma reindex_point {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex e).point i = nodes.point (e i) :=
  rfl

end NodeFamily

/-- Reindexing carries the fundamental function indexed by `k` to the
fundamental function indexed by `e k`. -/
lemma lagrangeFundamental_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (k : Fin n) (t : ℝ) :
    lagrangeFundamental (nodes.reindex e) k t =
      lagrangeFundamental nodes (e k) t := by
  classical
  simp only [lagrangeFundamental, NodeFamily.reindex_point]
  apply Finset.prod_equiv e
  · intro i
    simp
  · intro i _
    rfl

/-- The Lebesgue function is independent of the enumeration of its nodes. -/
lemma lebesgueFunction_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (t : ℝ) :
    lebesgueFunction (nodes.reindex e) t = lebesgueFunction nodes t := by
  simp only [lebesgueFunction, lagrangeFundamental_reindex]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The interval supremum of the Lebesgue function is permutation invariant. -/
lemma lebesgueOn_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (a b : ℝ) :
    lebesgueOn (nodes.reindex e) a b = lebesgueOn nodes a b := by
  simp only [lebesgueOn, lebesgueFunction_reindex]

/-- An internally ordered node family.  The public theorem will obtain this
from an arbitrary `NodeFamily` by the canonical sorting construction below. -/
structure OrderedNodes (n : ℕ) extends NodeFamily n where
  strictMono : StrictMono point

namespace OrderedNodes

/-- Earlier indices of an ordered family give strictly smaller nodes. -/
lemma point_lt {n : ℕ} (nodes : OrderedNodes n) {i j : Fin n} (hij : i < j) :
    nodes.point i < nodes.point j :=
  nodes.strictMono hij

/-- Every ordered node retains the lower endpoint bound. -/
lemma neg_one_le {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (-1 : ℝ) ≤ nodes.point i :=
  (nodes.mem_Icc i).1

/-- Every ordered node retains the upper endpoint bound. -/
lemma le_one {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    nodes.point i ≤ (1 : ℝ) :=
  (nodes.mem_Icc i).2

end OrderedNodes

namespace NodeFamily

/-- The finite set underlying a node family. -/
def nodeFinset {n : ℕ} (nodes : NodeFamily n) : Finset ℝ :=
  Finset.univ.image nodes.point

@[simp]
lemma mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (x : ℝ) :
    x ∈ nodes.nodeFinset ↔ ∃ i : Fin n, nodes.point i = x := by
  simp [nodeFinset]

/-- Injectivity ensures that the set of nodes has cardinality exactly `n`. -/
@[simp]
lemma card_nodeFinset {n : ℕ} (nodes : NodeFamily n) : nodes.nodeFinset.card = n := by
  classical
  rw [nodeFinset, Finset.card_image_of_injOn nodes.injective.injOn,
    Finset.card_univ, Fintype.card_fin]

/-- The increasing enumeration of the underlying finite set of nodes. -/
def sortedPoint {n : ℕ} (nodes : NodeFamily n) : Fin n ↪o ℝ :=
  nodes.nodeFinset.orderEmbOfFin (card_nodeFinset nodes)

@[simp]
lemma sortedPoint_mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sortedPoint i ∈ nodes.nodeFinset :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Canonically sort an arbitrary node family into a strictly increasing one. -/
def sorted {n : ℕ} (nodes : NodeFamily n) : OrderedNodes n where
  point := nodes.sortedPoint
  injective := nodes.sortedPoint.injective
  mem_Icc i := by
    rcases (mem_nodeFinset nodes (nodes.sortedPoint i)).mp
      (sortedPoint_mem_nodeFinset nodes i) with ⟨j, hj⟩
    rw [← hj]
    exact nodes.mem_Icc j
  strictMono := nodes.sortedPoint.strictMono

@[simp]
lemma sorted_point {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sorted.point i = nodes.sortedPoint i :=
  rfl

/-- The original enumeration is equivalent to its finite range. -/
def rangeEquiv {n : ℕ} (nodes : NodeFamily n) : Fin n ≃ ↥nodes.nodeFinset :=
  Equiv.ofBijective
    (fun i => ⟨nodes.point i, (mem_nodeFinset nodes _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => nodes.injective (congrArg Subtype.val h), fun y => by
      rcases (mem_nodeFinset nodes y).mp y.property with ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp]
lemma coe_rangeEquiv_apply {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    ((nodes.rangeEquiv i : nodes.nodeFinset) : ℝ) = nodes.point i :=
  rfl

/-- The permutation which reads the original nodes in increasing order. -/
def sortingPerm {n : ℕ} (nodes : NodeFamily n) : Equiv.Perm (Fin n) :=
  nodes.nodeFinset.orderIsoOfFin (card_nodeFinset nodes) |>.toEquiv |>.trans
    nodes.rangeEquiv.symm

/-- Applying `sortingPerm` to the old enumeration gives the canonical sorted
enumeration pointwise. -/
lemma point_sortingPerm {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.point (nodes.sortingPerm i) = nodes.sorted.point i := by
  simpa only [sortingPerm, Equiv.trans_apply, coe_rangeEquiv_apply, sorted_point,
    sortedPoint, Finset.coe_orderIsoOfFin_apply] using
    congrArg Subtype.val
      (nodes.rangeEquiv.apply_symm_apply
        (nodes.nodeFinset.orderIsoOfFin (card_nodeFinset nodes) i))

/-- The canonical sorted family really is a reindexing, rather than a new set
of nodes. -/
lemma reindex_sortingPerm {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex nodes.sortingPerm = nodes.sorted.toNodeFamily := by
  apply NodeFamily.ext
  funext i
  exact point_sortingPerm nodes i

/-- Sorting preserves the full Lebesgue function. -/
lemma lebesgueFunction_sorted {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    lebesgueFunction nodes.sorted.toNodeFamily t = lebesgueFunction nodes t := by
  rw [← reindex_sortingPerm nodes, lebesgueFunction_reindex]

/-- Sorting preserves every interval supremum of the Lebesgue function. -/
lemma lebesgueOn_sorted {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) :
    lebesgueOn nodes.sorted.toNodeFamily a b = lebesgueOn nodes a b := by
  rw [← reindex_sortingPerm nodes, lebesgueOn_reindex]

end NodeFamily

end

end Randy1153

/-! ### Upstream module `Randy1153/GapPolynomial.lean` -/

/-!
# Signed polynomials on nodal gaps

For strictly ordered interpolation nodes, every Lagrange fundamental function
has a constant sign on each closed nodal gap.  This file fixes one sign
convention and packages the polynomial which agrees with the Lebesgue
function on that gap.

The convention is source-compatible with the polynomials `F_i` in Section 2
of de Boor--Pinkus (1978): the coefficient of a cardinal polynomial is `-1`
once for every node strictly between its index and the gap, and `+1` at both
endpoints of the gap.  In particular, adjacent gap polynomials sum to twice
the cardinal polynomial at their common node.
-/

namespace Randy1153

open _root_.Polynomial
noncomputable section

/-- The left node index of the gap indexed by `g : Fin (n - 1)`.

This explicit embedding avoids relying on the non-definitional equality
`n - 1 + 1 = n`. -/
def gapLeftIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val, by omega⟩

/-- The right node index of the gap indexed by `g : Fin (n - 1)`. -/
def gapRightIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val + 1, by omega⟩

@[simp]
lemma gapLeftIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapLeftIndex g).val = g.val :=
  rfl

@[simp]
lemma gapRightIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapRightIndex g).val = g.val + 1 :=
  rfl

lemma gapLeftIndex_lt_rightIndex {n : ℕ} (g : Fin (n - 1)) :
    gapLeftIndex g < gapRightIndex g := by
  simp [Fin.lt_def]

/-- The closed real interval belonging to a nodal gap. -/
def closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Icc (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

/-- The open real interval belonging to a nodal gap. -/
def openGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Ioo (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

lemma gap_left_lt_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    nodes.point (gapLeftIndex g) < nodes.point (gapRightIndex g) :=
  nodes.point_lt (gapLeftIndex_lt_rightIndex g)

lemma openGap_nonempty {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (openGap nodes g).Nonempty :=
  Set.nonempty_Ioo.mpr (gap_left_lt_right nodes g)

/-- Whether the factor belonging to `j` contributes a negative sign to the
`k`th cardinal polynomial on gap `g`.

The two disjuncts say respectively that `j` lies between the gap and `k` on
the right, or between `k` and the gap on the left. -/
def gapNegative {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : Prop :=
  (j < k ∧ g.val < j.val) ∨ (k < j ∧ j.val ≤ g.val)

instance gapNegativeDecidable {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    Decidable (gapNegative g k j) := by
  unfold gapNegative
  infer_instance

/-- The sign of one normalized linear factor on a gap. -/
def gapSignFactor {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : ℝ :=
  if gapNegative g k j then -1 else 1

/-- The sign of the `k`th Lagrange fundamental function on gap `g`. -/
def gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, gapSignFactor g k j

lemma gapSignFactor_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    gapSignFactor g k j = 1 ∨ gapSignFactor g k j = -1 := by
  simp only [gapSignFactor]
  split_ifs <;> simp

lemma gapCoefficient_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k = 1 ∨ gapCoefficient g k = -1 := by
  classical
  rw [gapCoefficient]
  generalize Finset.univ.erase k = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      rcases gapSignFactor_eq_one_or_neg_one g k j with h | h <;>
        rcases ih with h' | h' <;> simp [h, h']

@[simp]
lemma abs_gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    |gapCoefficient g k| = 1 := by
  rcases gapCoefficient_eq_one_or_neg_one g k with h | h <;> simp [h]

lemma gapCoefficient_ne_zero {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k ≠ 0 := by
  intro h
  have habs := abs_gapCoefficient g k
  simp [h] at habs

private lemma prod_gapSignFactor_eq_pow_card_filter {n : ℕ}
    (g : Fin (n - 1)) (k : Fin n) (s : Finset (Fin n)) :
    (∏ j ∈ s, gapSignFactor g k j) =
      (-1 : ℝ) ^ (s.filter (gapNegative g k)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs, Finset.filter_insert, ih]
      by_cases hj : gapNegative g k j
      · have hjfilter : j ∉ s.filter (gapNegative g k) := by simp [hjs]
        simp [hj, hjfilter, gapSignFactor, pow_succ]
      · simp [hj, gapSignFactor]

private lemma negative_filter_eq_Ioc {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioc k (gapLeftIndex g) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioc, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · have : j.val < k.val := hjklt
      omega
    · exact ⟨hkj, by simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg⟩
  · rintro ⟨hkj, hjg⟩
    refine ⟨hkj.ne', Or.inr ⟨hkj, ?_⟩⟩
    simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg

private lemma negative_filter_eq_Ioo {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioo (gapLeftIndex g) k := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioo, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · exact ⟨by simpa only [Fin.lt_def, gapLeftIndex_val] using hgj, hjklt⟩
    · have : k.val < j.val := hkj
      omega
  · rintro ⟨hgj, hjk⟩
    refine ⟨hjk.ne, Or.inl ⟨hjk, ?_⟩⟩
    simpa only [Fin.lt_def, gapLeftIndex_val] using hgj

/-- Closed form of the gap sign to the left of (or at) the left endpoint. -/
lemma gapCoefficient_of_le {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (g.val - k.val) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioc g k hkg, Fin.card_Ioc]
  rfl

/-- Closed form of the gap sign to the right of the left endpoint. -/
lemma gapCoefficient_of_lt {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (k.val - g.val - 1) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioo g k hgk, Fin.card_Ioo]
  rfl

@[simp]
lemma gapCoefficient_left {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapLeftIndex g) = 1 := by
  rw [gapCoefficient_of_le]
  · simp
  · simp

@[simp]
lemma gapCoefficient_right {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapRightIndex g) = 1 := by
  rw [gapCoefficient_of_lt]
  · simp
  · simp

/-- Away from its own gap, the nodal values of a gap polynomial alternate in
sign.  This is the first sign pattern used in the source interlacing proof. -/
lemma gapCoefficient_right_eq_neg_left_of_ne {n : ℕ}
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    gapCoefficient g (gapRightIndex h) =
      -gapCoefficient g (gapLeftIndex h) := by
  rcases lt_or_gt_of_ne hhg with hhglt | hghlt
  · have hright_le : (gapRightIndex h).val ≤ g.val := by
      simp only [gapRightIndex_val]
      omega
    have hleft_le : (gapLeftIndex h).val ≤ g.val := by
      simp only [gapLeftIndex_val]
      omega
    rw [gapCoefficient_of_le g _ hright_le,
      gapCoefficient_of_le g _ hleft_le]
    have hexp : g.val - (gapLeftIndex h).val =
        (g.val - (gapRightIndex h).val) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring
  · have hgleft : g.val < (gapLeftIndex h).val := by
      simp only [gapLeftIndex_val]
      omega
    have hgright : g.val < (gapRightIndex h).val := by
      simp only [gapRightIndex_val]
      omega
    rw [gapCoefficient_of_lt g _ hgright,
      gapCoefficient_of_lt g _ hgleft]
    have hexp : (gapRightIndex h).val - g.val - 1 =
        ((gapLeftIndex h).val - g.val - 1) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring

/-- With at least three nodes, every gap sign vector contains a negative
coefficient.  The two-node exception is real: its Lebesgue function is
identically one on the only gap. -/
lemma exists_gapCoefficient_eq_neg_one {n : ℕ} (hn : 3 ≤ n) (g : Fin (n - 1)) :
    ∃ k : Fin n, gapCoefficient g k = -1 := by
  by_cases hg0 : g.val = 0
  · let k : Fin n := ⟨2, by omega⟩
    refine ⟨k, ?_⟩
    have hgk : g.val < k.val := by simp [k, hg0]
    rw [gapCoefficient_of_lt g k hgk]
    simp [k, hg0]
  · let k : Fin n := ⟨g.val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hkg : k.val ≤ g.val := by simp [k]
    rw [gapCoefficient_of_le g k hkg]
    have hexp : g.val - k.val = 1 := by
      simp only [k]
      omega
    rw [hexp]
    norm_num

/-- The signed interpolation polynomial which agrees with the Lebesgue
function on the gap. -/
def gapPolynomial {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ nodes.point (gapCoefficient g)

lemma gapPolynomial_eval_node {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1))
    (k : Fin n) :
    (gapPolynomial nodes g).eval (nodes.point k) = gapCoefficient g k := by
  simpa only [gapPolynomial] using
    (Lagrange.eval_interpolate_at_node (r := gapCoefficient g)
      nodes.injective.injOn (Finset.mem_univ k))

@[simp]
lemma gapPolynomial_eval_left {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapLeftIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_left]

@[simp]
lemma gapPolynomial_eval_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapRightIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_right]

lemma degree_gapPolynomial_le {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).degree ≤ (n - 1 : ℕ) := by
  simpa only [gapPolynomial, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.degree_interpolate_le (s := Finset.univ) (r := gapCoefficient g)
      nodes.injective.injOn)

private lemma numerator_nonneg_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ closedGap nodes g) :
    0 ≤ t - nodes.point j := by
  rw [sub_nonneg]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans ht.1

private lemma numerator_nonpos_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ closedGap nodes g) :
    t - nodes.point j ≤ 0 := by
  rw [sub_nonpos]
  exact ht.2.trans (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))

private lemma numerator_pos_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ openGap nodes g) :
    0 < t - nodes.point j := by
  rw [sub_pos]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans_lt ht.1

private lemma numerator_neg_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ openGap nodes g) :
    t - nodes.point j < 0 := by
  rw [sub_neg]
  exact ht.2.trans_le (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))

private lemma denominator_pos_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hjk : j < k) :
    0 < nodes.point k - nodes.point j := by
  rw [sub_pos]
  exact nodes.point_lt hjk

private lemma denominator_neg_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hkj : k < j) :
    nodes.point k - nodes.point j < 0 := by
  rw [sub_neg]
  exact nodes.point_lt hkj

/-- Each normalized linear factor has the sign encoded by `gapSignFactor` on
the closed gap. -/
lemma gapSignFactor_mul_div_nonneg {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, if_pos hneg, neg_one_mul]
    apply neg_nonneg.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_nonpos_of_nonpos_of_nonneg
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt).le
    · exact div_nonpos_of_nonneg_of_nonpos
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj).le
  · rw [gapSignFactor, if_neg hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_nonneg
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt).le
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_nonneg_of_nonpos
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj).le

/-- In the open gap none of the factors vanish, so the signed factor is
strictly positive. -/
lemma gapSignFactor_mul_div_pos {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, if_pos hneg, neg_one_mul]
    apply neg_pos.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_neg_of_neg_of_pos
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt)
    · exact div_neg_of_pos_of_neg
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj)
  · rw [gapSignFactor, if_neg hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_pos
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt)
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_pos_of_neg_of_neg
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj)

/-- The signed fundamental function is nonnegative on its closed gap. -/
lemma gapCoefficient_mul_lagrangeFundamental_nonneg {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_nonneg fun j hj =>
    gapSignFactor_mul_div_nonneg nodes g (Finset.mem_erase.mp hj).1 ht

/-- Strict signed positivity in the open gap. -/
lemma gapCoefficient_mul_lagrangeFundamental_pos {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_pos fun j hj =>
    gapSignFactor_mul_div_pos nodes g (Finset.mem_erase.mp hj).1 ht

/-- Absolute value removes exactly the coefficient selected for the gap. -/
lemma abs_lagrangeFundamental_eq_gapCoefficient_mul {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    |lagrangeFundamental nodes.toNodeFamily k t| =
      gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  calc
    |lagrangeFundamental nodes.toNodeFamily k t| =
        |gapCoefficient g k| * |lagrangeFundamental nodes.toNodeFamily k t| := by simp
    _ = |gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t| :=
      (abs_mul _ _).symm
    _ = gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t :=
      abs_of_nonneg (gapCoefficient_mul_lagrangeFundamental_nonneg nodes g k ht)

lemma gapPolynomial_eval_eq_sum {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (t : ℝ) :
    (gapPolynomial nodes g).eval t =
      ∑ k : Fin n, gapCoefficient g k *
        lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  simp only [gapPolynomial, Lagrange.interpolate_apply, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  change gapCoefficient g k * (lagrangeBasis nodes.toNodeFamily k).eval t = _
  rw [lagrangeBasis_eval]

/-- The Lagrange fundamental functions form a partition of unity. -/
lemma sum_lagrangeFundamental_eq_one {n : ℕ} (nodes : OrderedNodes n)
    (hn : 0 < n) (t : ℝ) :
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t = 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hbasis := Lagrange.sum_basis nodes.injective.injOn huniv
  have heval := congrArg (Polynomial.eval t) hbasis
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_one] at heval
  calc
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t =
        ∑ k : Fin n, (Lagrange.basis Finset.univ nodes.point k).eval t := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← lagrangeBasis_eval]
      rfl
    _ = 1 := by simpa using heval

/-- On the whole closed nodal gap, the signed polynomial is the Lebesgue
function.  Endpoint inclusion is useful later when taking compact maxima. -/
lemma lebesgueFunction_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    lebesgueFunction nodes.toNodeFamily t = (gapPolynomial nodes g).eval t := by
  rw [lebesgueFunction, gapPolynomial_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact abs_lagrangeFundamental_eq_gapCoefficient_mul nodes g k ht

/-- For at least three nodes the Lebesgue/gap polynomial is strictly greater
than one in the open gap.  The explicit cardinality hypothesis records the
genuine two-node exception. -/
lemma one_lt_eval_gapPolynomial_of_mem_openGap {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ openGap nodes g) :
    1 < (gapPolynomial nodes g).eval t := by
  obtain ⟨k, hcoeff⟩ := exists_gapCoefficient_eq_neg_one hn g
  let f : Fin n → ℝ := fun j => lagrangeFundamental nodes.toNodeFamily j t
  have hfk : f k < 0 := by
    have hpos := gapCoefficient_mul_lagrangeFundamental_pos nodes g k ht
    rw [hcoeff, neg_one_mul] at hpos
    exact neg_pos.mp hpos
  have hsum : ∑ j : Fin n, f j = 1 := by
    exact sum_lagrangeFundamental_eq_one nodes (by omega) t
  have hsumErase : ∑ j ∈ Finset.univ.erase k, f j = 1 - f k := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)] at hsum
    linarith
  have habsErase :
      |∑ j ∈ Finset.univ.erase k, f j| ≤
        ∑ j ∈ Finset.univ.erase k, |f j| :=
    Finset.abs_sum_le_sum_abs f (Finset.univ.erase k)
  have hlower : 1 - 2 * f k ≤ lebesgueFunction nodes.toNodeFamily t := by
    rw [lebesgueFunction, ← Finset.add_sum_erase Finset.univ
      (fun j => |f j|) (Finset.mem_univ k)]
    calc
      1 - 2 * f k = |f k| + |∑ j ∈ Finset.univ.erase k, f j| := by
        rw [abs_of_neg hfk, hsumErase, abs_of_pos (by linarith)]
        ring
      _ ≤ |f k| + ∑ j ∈ Finset.univ.erase k, |f j| :=
        add_le_add (le_refl _) habsErase
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g
    ⟨ht.1.le, ht.2.le⟩]
  linarith

/-- The local Lebesgue height on the `g`th closed gap. -/
def gapHeight {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  lebesgueOn nodes.toNodeFamily
    (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

/-- The compact gap height is attained by the signed gap polynomial. -/
lemma exists_gapHeight_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    ∃ t ∈ closedGap nodes g,
      gapHeight nodes g = (gapPolynomial nodes g).eval t ∧
        ∀ u ∈ closedGap nodes g,
          (gapPolynomial nodes g).eval u ≤ (gapPolynomial nodes g).eval t := by
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
    (gap_left_lt_right nodes g).le
  refine ⟨t, ht, ?_, ?_⟩
  · rw [gapHeight, heq, ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
  · intro u hu
    rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g hu,
      ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
    exact hmax u hu

end

end Randy1153

/-! ### Upstream module `Randy1153/DeBoorPinkus/NodeSpace.lean` -/

/-!
# Endpoint-fixed node arrays

The polynomial part of de Boor--Pinkus fixes the first and last interpolation
nodes and varies the interior nodes in an open simplex.  This file records
that space without identifying it magically with Euclidean space.  The later
global-topology phase must construct and prove the required homeomorphism.

Our `EndpointArray d A B` has `d` interior nodes and therefore `d + 2` nodes
and `d + 1` nodal gaps.  It extends the project's ordered-node type, so all
nodes remain in `[-1,1]`, which is the application needed for Randy 1153.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Interval hypotheses under which the project-level endpoint array exists.
The source assumes only `A < B`; the extra bounds are exactly those inherited
from the public `NodeFamily` used by Randy 1153. -/
def AdmissibleInterval (A B : ℝ) : Prop :=
  (-1 : ℝ) ≤ A ∧ A < B ∧ B ≤ 1

/-- Index of the fixed left endpoint among `d + 2` nodes. -/
def endpointLeftIndex (d : ℕ) : Fin (d + 2) :=
  ⟨0, by omega⟩

/-- Index of the fixed right endpoint among `d + 2` nodes. -/
def endpointRightIndex (d : ℕ) : Fin (d + 2) :=
  Fin.last (d + 1)

/-- Index of interior coordinate `i` among the full endpoint-fixed array. -/
def interiorNodeIndex {d : ℕ} (i : Fin d) : Fin (d + 2) :=
  ⟨i.val + 1, by omega⟩

@[simp]
lemma endpointLeftIndex_val (d : ℕ) : (endpointLeftIndex d).val = 0 :=
  rfl

@[simp]
lemma endpointRightIndex_val (d : ℕ) : (endpointRightIndex d).val = d + 1 :=
  rfl

@[simp]
lemma interiorNodeIndex_val {d : ℕ} (i : Fin d) :
    (interiorNodeIndex i).val = i.val + 1 :=
  rfl

lemma endpointLeftIndex_lt_interior {d : ℕ} (i : Fin d) :
    endpointLeftIndex d < interiorNodeIndex i := by
  simp [Fin.lt_def]

lemma interior_lt_endpointRightIndex {d : ℕ} (i : Fin d) :
    interiorNodeIndex i < endpointRightIndex d := by
  simp [Fin.lt_def]

lemma interiorNodeIndex_strictMono {d : ℕ} :
    StrictMono (interiorNodeIndex : Fin d → Fin (d + 2)) := by
  intro i j hij
  simpa only [Fin.lt_def, interiorNodeIndex_val] using Nat.add_lt_add_right hij 1

/-- An ordered array with `d` interior nodes and fixed endpoint values `A,B`. -/
structure EndpointArray (d : ℕ) (A B : ℝ) extends OrderedNodes (d + 2) where
  left_endpoint : point (endpointLeftIndex d) = A
  right_endpoint : point (endpointRightIndex d) = B

namespace EndpointArray

/-- The interior-coordinate vector of an endpoint-fixed array. -/
def interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.point (interiorNodeIndex i)

@[simp]
lemma interior_apply {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i = nodes.point (interiorNodeIndex i) :=
  rfl

lemma left_lt_interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    A < nodes.interior i := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (interiorNodeIndex i) :=
      nodes.strictMono (endpointLeftIndex_lt_interior i)
    _ = nodes.interior i := rfl

lemma interior_lt_right {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i < B := by
  calc
    nodes.interior i = nodes.point (interiorNodeIndex i) := rfl
    _ < nodes.point (endpointRightIndex d) :=
      nodes.strictMono (interior_lt_endpointRightIndex i)
    _ = B := nodes.right_endpoint

lemma interior_strictMono {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    StrictMono nodes.interior :=
  nodes.strictMono.comp interiorNodeIndex_strictMono

lemma endpoints_lt {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : A < B := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (endpointRightIndex d) := nodes.strictMono (by simp [Fin.lt_def])
    _ = B := nodes.right_endpoint

lemma neg_one_le_left {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    (-1 : ℝ) ≤ A := by
  rw [← nodes.left_endpoint]
  exact nodes.neg_one_le _

lemma right_le_one {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    B ≤ (1 : ℝ) := by
  rw [← nodes.right_endpoint]
  exact nodes.le_one _

lemma admissibleInterval {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    AdmissibleInterval A B :=
  ⟨nodes.neg_one_le_left, nodes.endpoints_lt, nodes.right_le_one⟩

/-- Gap height of an endpoint-fixed array.  There are `d + 1` such gaps. -/
def height {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  gapHeight nodes.toOrderedNodes g

end EndpointArray

/-- The source's open simplex in interior-coordinate form. -/
def endpointNodeSpace (d : ℕ) (A B : ℝ) : Set (Fin d → ℝ) :=
  {u | (∀ i, A < u i) ∧ StrictMono u ∧ ∀ i, u i < B}

lemma EndpointArray.interior_mem_endpointNodeSpace {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    nodes.interior ∈ endpointNodeSpace d A B :=
  ⟨nodes.left_lt_interior, nodes.interior_strictMono, nodes.interior_lt_right⟩

/-- The source topology is the coordinate topology on the varying interior
nodes.  A later module must still prove that `interior` identifies
`EndpointArray` homeomorphically with the open simplex `endpointNodeSpace`. -/
instance endpointArrayTopologicalSpace (d : ℕ) (A B : ℝ) :
    TopologicalSpace (EndpointArray d A B) :=
  TopologicalSpace.induced EndpointArray.interior inferInstance

/-- The coordinate simplex is open.  This is the local-topology input; no
global Euclidean homeomorphism is claimed here. -/
lemma isOpen_endpointNodeSpace (d : ℕ) (A B : ℝ) :
    IsOpen (endpointNodeSpace d A B) := by
  have hopenLeft : IsOpen {u : Fin d → ℝ | ∀ i, A < u i} := by
    rw [show {u : Fin d → ℝ | ∀ i, A < u i} =
        ⋂ i : Fin d, {u | A < u i} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hopenRight : IsOpen {u : Fin d → ℝ | ∀ i, u i < B} := by
    rw [show {u : Fin d → ℝ | ∀ i, u i < B} =
        ⋂ i : Fin d, {u | u i < B} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hopenMono : IsOpen {u : Fin d → ℝ | StrictMono u} := by
    rw [show {u : Fin d → ℝ | StrictMono u} =
        ⋂ i : Fin d, ⋂ j : Fin d, ⋂ (_h : i < j), {u | u i < u j} by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _h => isOpen_lt (continuous_apply i) (continuous_apply j)
  rw [show endpointNodeSpace d A B =
      {u : Fin d → ℝ | ∀ i, A < u i} ∩
        ({u : Fin d → ℝ | StrictMono u} ∩ {u : Fin d → ℝ | ∀ i, u i < B}) by
    ext u
    simp [endpointNodeSpace]]
  exact hopenLeft.inter (hopenMono.inter hopenRight)

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Jsp936/Definitions.lean` -/

/-! Full free-node optimization target. Canonical theory is credited to randyxian08. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- Global minimality among every injectively enumerated family of the same size. -/
def IsOptimal {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∀ other : NodeFamily n, lebesgueOn nodes (-1) 1 ≤ lebesgueOn other (-1) 1

/-- All actual internal gap maxima agree, and both exterior endpoint values fit below them. -/
def EquioscillatingWithControlledTails {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  (∀ i j : Fin (d + 1), gapHeight nodes.sorted i = gapHeight nodes.sorted j) ∧
    lebesgueFunction nodes (-1) ≤ gapHeight nodes.sorted (0 : Fin (d + 1)) ∧
    lebesgueFunction nodes 1 ≤ gapHeight nodes.sorted (0 : Fin (d + 1))

end
end Jsp936

/-! ### Upstream module `Jsp936/NormalizedNodes.lean` -/

/-! Positive affine normalization of the extreme nodes of an ordered family. -/
namespace Jsp936
open Randy1153
open Randy1153.DeBoorPinkus
noncomputable section

/-- The positive affine order isomorphism carrying `a` to `-1` and `b` to `1`. -/
def intervalNormalize (a b : ℝ) (hab : a < b) : ℝ ≃o ℝ where
  toFun t := 2 * (t - a) / (b - a) - 1
  invFun y := a + (b - a) * (y + 1) / 2
  left_inv t := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hba]
    ring
  right_inv y := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hba]
    ring
  map_rel_iff' := by
    intro x y
    change 2 * (x - a) / (b - a) - 1 ≤ 2 * (y - a) / (b - a) - 1 ↔ x ≤ y
    rw [sub_le_sub_iff_right]
    rw [div_le_div_iff₀ (sub_pos.mpr hab) (sub_pos.mpr hab)]
    constructor <;> intro h <;> nlinarith

@[simp]
lemma intervalNormalize_apply (a b : ℝ) (hab : a < b) (t : ℝ) :
    intervalNormalize a b hab t = 2 * (t - a) / (b - a) - 1 :=
  rfl

@[simp]
lemma intervalNormalize_right (a b : ℝ) (hab : a < b) :
    intervalNormalize a b hab b = 1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [intervalNormalize_apply]
  field_simp [hba]
  ring

/-- The positive affine map normalizing the two extreme points of `nodes`. -/
def normalizingMap {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ ≃o ℝ :=
  intervalNormalize
    (nodes.point (endpointLeftIndex d))
    (nodes.point (endpointRightIndex d))
    (nodes.strictMono (by simp [Fin.lt_def]))

@[simp]
lemma normalizingMap_left {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    normalizingMap nodes (nodes.point (endpointLeftIndex d)) = -1 := by
  simp [normalizingMap]

@[simp]
lemma normalizingMap_right {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    normalizingMap nodes (nodes.point (endpointRightIndex d)) = 1 := by
  apply intervalNormalize_right

/-- Normalize an ordered family by sending its extreme points to `-1` and `1`. -/
def normalizedNodes {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    EndpointArray d (-1) 1 where
  point i := normalizingMap nodes (nodes.point i)
  injective := (normalizingMap nodes).injective.comp nodes.injective
  mem_Icc i := by
    constructor
    · rw [← normalizingMap_left nodes]
      exact (normalizingMap nodes).monotone <|
        nodes.strictMono.monotone (Fin.zero_le i)
    · rw [← normalizingMap_right nodes]
      exact (normalizingMap nodes).monotone <|
        nodes.strictMono.monotone (Fin.le_last i)
  strictMono := (normalizingMap nodes).strictMono.comp nodes.strictMono
  left_endpoint := normalizingMap_left nodes
  right_endpoint := normalizingMap_right nodes

@[simp]
lemma normalizedNodes_point {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 2)) :
    (normalizedNodes nodes).point i = normalizingMap nodes (nodes.point i) :=
  rfl

end
end Jsp936

/-! ### Upstream module `Jsp936/AffineNormalization.lean` -/

/-! Preservation of Lagrange and Lebesgue data under positive affine normalization. -/
namespace Jsp936
open Randy1153 _root_.Set
open Randy1153.DeBoorPinkus
noncomputable section

/-- The normalizing map scales every difference by the same positive constant. -/
private lemma normalizingMap_sub {d : ℕ} (nodes : OrderedNodes (d + 2)) (x y : ℝ) :
    normalizingMap nodes x - normalizingMap nodes y =
      2 / (nodes.point (endpointRightIndex d) - nodes.point (endpointLeftIndex d)) *
        (x - y) := by
  simp only [normalizingMap, intervalNormalize_apply]
  ring

/-- Normalizing both the nodes and the evaluation point preserves each fundamental function. -/
theorem lagrangeFundamental_normalized {d : ℕ} (nodes : OrderedNodes (d + 2))
    (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (normalizedNodes nodes).toNodeFamily k (normalizingMap nodes t) =
      lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  simp only [lagrangeFundamental, normalizedNodes_point]
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  have hnodes : nodes.point k - nodes.point i ≠ 0 := by
    exact sub_ne_zero.mpr (nodes.injective.ne hik.symm)
  have hextremes :
      nodes.point (endpointRightIndex d) - nodes.point (endpointLeftIndex d) ≠ 0 := by
    exact sub_ne_zero.mpr (nodes.injective.ne (by simp [endpointLeftIndex,
      endpointRightIndex]))
  rw [normalizingMap_sub nodes t (nodes.point i),
    normalizingMap_sub nodes (nodes.point k) (nodes.point i)]
  field_simp [hnodes, hextremes]

/-- Normalizing the nodes and argument preserves the full Lebesgue function. -/
theorem lebesgueFunction_normalized {d : ℕ} (nodes : OrderedNodes (d + 2)) (t : ℝ) :
    lebesgueFunction (normalizedNodes nodes).toNodeFamily (normalizingMap nodes t) =
      lebesgueFunction nodes.toNodeFamily t := by
  simp only [lebesgueFunction, lagrangeFundamental_normalized]

/-- Positive affine normalization carries every interval Lebesgue maximum to its image interval. -/
theorem lebesgueOn_normalized {d : ℕ} (nodes : OrderedNodes (d + 2)) (a b : ℝ) :
    lebesgueOn (normalizedNodes nodes).toNodeFamily
        (normalizingMap nodes a) (normalizingMap nodes b) =
      lebesgueOn nodes.toNodeFamily a b := by
  unfold lebesgueOn
  rw [← (normalizingMap nodes).image_Icc, image_image]
  congr 1
  apply image_congr
  intro t _
  exact lebesgueFunction_normalized nodes t

/-- Positive affine normalization preserves every actual closed-gap maximum. -/
theorem gapHeight_normalized {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) :
    gapHeight (normalizedNodes nodes).toOrderedNodes g = gapHeight nodes g := by
  simpa only [gapHeight, normalizedNodes_point] using
    lebesgueOn_normalized nodes (nodes.point (gapLeftIndex g))
      (nodes.point (gapRightIndex g))

end
end Jsp936

/-! ### Upstream module `Jsp936/Bounds.lean` -/

/-! Bounds for the actual maximum of the Lebesgue function on a closed interval. -/
namespace Jsp936
open Randy1153 _root_.Set
noncomputable section

/-- The actual Lebesgue maximum is bounded exactly when every value on the interval is
bounded. -/
theorem lebesgueOn_le_iff {n : ℕ} (nodes : NodeFamily n) (a b C : ℝ) (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ C ↔ ∀ t ∈ Icc a b, lebesgueFunction nodes t ≤ C := by
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  constructor
  · intro hC u hu
    calc
      lebesgueFunction nodes u ≤ lebesgueFunction nodes t := hmax u hu
      _ = lebesgueOn nodes a b := heq.symm
      _ ≤ C := hC
  · intro hC
    rw [heq]
    exact hC t ht

/-- Every value on a nonempty closed interval is at most its actual Lebesgue maximum. -/
theorem lebesgueFunction_le_on {n : ℕ} (nodes : NodeFamily n) {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc a b) :
    lebesgueFunction nodes t ≤ lebesgueOn nodes a b := by
  exact (lebesgueOn_le_iff nodes a b (lebesgueOn nodes a b) hab).mp le_rfl t ht

/-- Enlarging a nonempty closed interval cannot decrease the actual Lebesgue maximum. -/
theorem lebesgueOn_mono {n : ℕ} (nodes : NodeFamily n) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hbd : b ≤ d) :
    lebesgueOn nodes a b ≤ lebesgueOn nodes c d := by
  obtain ⟨t, ht, heq, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [heq]
  exact lebesgueFunction_le_on nodes hcd ⟨hca.trans ht.1, ht.2.trans hbd⟩

end
end Jsp936

/-! ### Upstream module `Jsp936/TailBounds.lean` -/

/-! Pointwise bounds for the exterior tails of a Lebesgue function. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- To the left of every node, the Lebesgue function is bounded by its value at `-1`. -/
theorem lebesgueFunction_le_left_endpoint {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (ht : -1 ≤ t) (hleft : ∀ i : Fin n, t ≤ nodes.point i) :
    lebesgueFunction nodes t ≤ lebesgueFunction nodes (-1) := by
  classical
  simp only [lebesgueFunction]
  apply Finset.sum_le_sum
  intro k _
  simp only [lagrangeFundamental, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_div, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos (sub_nonpos.mpr (hleft i)),
      abs_of_nonpos (sub_nonpos.mpr (nodes.mem_Icc i).1)]
    linarith

/-- To the right of every node, the Lebesgue function is bounded by its value at `1`. -/
theorem lebesgueFunction_le_right_endpoint {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (ht : t ≤ 1) (hright : ∀ i : Fin n, nodes.point i ≤ t) :
    lebesgueFunction nodes t ≤ lebesgueFunction nodes 1 := by
  classical
  simp only [lebesgueFunction]
  apply Finset.sum_le_sum
  intro k _
  simp only [lagrangeFundamental, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_div, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr (hright i)),
      abs_of_nonneg (sub_nonneg.mpr (nodes.mem_Icc i).2)]
    linarith

end
end Jsp936

/-! ### Upstream module `Jsp936/GapCover.lean` -/

/-! Covering the interval between extreme nodes by its consecutive closed gaps. -/
namespace Jsp936
open Randy1153 _root_.Set
noncomputable section

/-- Every point between the extreme ordered nodes belongs to a consecutive closed gap. -/
theorem exists_mem_closedGap {d : ℕ} (nodes : OrderedNodes (d + 2)) {t : ℝ}
    (hlo : nodes.point 0 ≤ t) (hhi : t ≤ nodes.point (Fin.last (d + 1))) :
    ∃ g : Fin (d + 1), t ∈ closedGap nodes g := by
  have hcover (i : Fin (d + 2)) (hi : t ≤ nodes.point i) :
      ∃ g : Fin (d + 1), t ∈ closedGap nodes g := by
    induction i using Fin.induction with
    | zero =>
        refine ⟨0, ?_⟩
        simp only [closedGap, mem_Icc, gapLeftIndex, gapRightIndex]
        exact ⟨hlo, hi.trans (nodes.strictMono.monotone (by simp))⟩
    | succ i ih =>
        by_cases hprev : t ≤ nodes.point i.castSucc
        · exact ih hprev
        · refine ⟨i, ?_⟩
          simp only [closedGap, mem_Icc, gapLeftIndex, gapRightIndex]
          exact ⟨le_of_not_ge hprev, hi⟩
  exact hcover (Fin.last (d + 1)) hhi

/-- A gap maximum is at most the maximum on the whole interpolation interval. -/
theorem gapHeight_le_lebesgueOn {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) :
    gapHeight nodes g ≤ lebesgueOn nodes.toNodeFamily (-1) 1 := by
  apply lebesgueOn_mono nodes.toNodeFamily
  · exact (gap_left_lt_right nodes g).le
  · norm_num
  · exact nodes.neg_one_le (gapLeftIndex g)
  · exact nodes.le_one (gapRightIndex g)

/-- Gap bounds together with the two endpoint bounds control the whole interval maximum. -/
theorem lebesgueOn_le_of_gapHeight_le {d : ℕ} (nodes : OrderedNodes (d + 2)) (C : ℝ)
    (hgaps : ∀ g : Fin (d + 1), gapHeight nodes g ≤ C)
    (hleft : lebesgueFunction nodes.toNodeFamily (-1) ≤ C)
    (hright : lebesgueFunction nodes.toNodeFamily 1 ≤ C) :
    lebesgueOn nodes.toNodeFamily (-1) 1 ≤ C := by
  apply (lebesgueOn_le_iff nodes.toNodeFamily (-1) 1 C (by norm_num)).2
  intro t ht
  by_cases hleftTail : t ≤ nodes.point 0
  · exact (lebesgueFunction_le_left_endpoint nodes.toNodeFamily t ht.1 fun i ↦
      hleftTail.trans (nodes.strictMono.monotone (Fin.zero_le i))).trans hleft
  by_cases hrightTail : nodes.point (Fin.last (d + 1)) ≤ t
  · exact (lebesgueFunction_le_right_endpoint nodes.toNodeFamily t ht.2 fun i ↦
      (nodes.strictMono.monotone (Fin.le_last i)).trans hrightTail).trans hright
  obtain ⟨g, htg⟩ := exists_mem_closedGap nodes
    (le_of_not_ge hleftTail) (le_of_not_ge hrightTail)
  exact (lebesgueFunction_le_on nodes.toNodeFamily (gap_left_lt_right nodes g).le htg).trans
    (hgaps g)

end
end Jsp936

/-! ### Upstream module `Randy1153/DeBoorPinkus/GapCritical.lean` -/

/-!
# Attained gap maxima and interior critical points

The compact maximum supplied by `gapHeight` is made into a named point here.
For at least three nodes, the strict interior inequality for the signed gap
polynomial forces every such chosen maximum away from the two endpoints.
Fermat's theorem then makes it a genuine derivative root.

For `n ≥ 4`, a private root in each other gap factors the polynomial into
real linear factors, with at most one final linear quotient.  Its logarithmic
derivative is therefore strictly decreasing on the root-free owning gap.
This proves the required uniqueness without assuming the downstream
cross-interlacing target.  The two-node case remains explicitly exceptional:
there the only gap polynomial is identically one, so every point is critical.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Polynomial
open scoped _root_.Topology

noncomputable section

/-- A compact maximizer of the signed polynomial on its own closed gap. -/
def gapArgmax {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  Classical.choose (exists_gapHeight_eq_eval_gapPolynomial nodes g)

lemma gapArgmax_mem_closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ closedGap nodes g :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).1

lemma gapHeight_eq_eval_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    gapHeight nodes g = (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.1

lemma gapPolynomial_eval_le_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    (gapPolynomial nodes g).eval t ≤
      (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.2 t ht

/-- For at least three nodes, the compact maximum lies strictly inside its
gap.  The cardinality hypothesis is sharp; see
`gapPolynomial_eq_one_of_two_nodes`. -/
lemma gapArgmax_mem_openGap {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n)
    (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ openGap nodes g := by
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt : 1 < (gapPolynomial nodes g).eval t :=
    one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hmaxgt : 1 < (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
    htgt.trans_le (gapPolynomial_eval_le_gapArgmax nodes g ⟨ht.1.le, ht.2.le⟩)
  have hclosed := gapArgmax_mem_closedGap nodes g
  refine ⟨lt_of_le_of_ne hclosed.1 ?_, lt_of_le_of_ne hclosed.2 ?_⟩
  · intro heq
    rw [← heq, gapPolynomial_eval_left] at hmaxgt
    exact (lt_irrefl 1) hmaxgt
  · intro heq
    rw [heq, gapPolynomial_eval_right] at hmaxgt
    exact (lt_irrefl 1) hmaxgt

/-- Every chosen gap maximum is a derivative root once the gap has a genuine
interior maximum. -/
lemma gapPolynomial_derivative_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.eval (gapArgmax nodes g) = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  have hopen := gapArgmax_mem_openGap nodes hn g
  have hmaxOn : IsMaxOn (fun t : ℝ => p.eval t) (closedGap nodes g)
      (gapArgmax nodes g) := by
    intro t ht
    exact gapPolynomial_eval_le_gapArgmax nodes g ht
  have hlocal : IsLocalMax (fun t : ℝ => p.eval t) (gapArgmax nodes g) :=
    hmaxOn.isLocalMax (Icc_mem_nhds hopen.1 hopen.2)
  simpa only [p] using hlocal.hasDerivAt_eq_zero (p.hasDerivAt (gapArgmax nodes g))

/-- In every nondegenerate (`n ≥ 3`) case the derivative polynomial itself
is nonzero.  This keeps membership in its finite real-root multiset honest. -/
lemma gapPolynomial_derivative_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative ≠ 0 := by
  intro hderiv
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hderiv
  have heq := congrArg (Polynomial.eval t) hconst
  have heqLeft := congrArg
    (Polynomial.eval (nodes.point (gapLeftIndex g))) hconst
  simp only [Polynomial.eval_C] at heq heqLeft
  rw [gapPolynomial_eval_left] at heqLeft
  linarith

lemma gapArgmax_mem_derivative_roots {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ (gapPolynomial nodes g).derivative.roots := by
  rw [Polynomial.mem_roots (gapPolynomial_derivative_ne_zero nodes hn g)]
  exact gapPolynomial_derivative_eval_gapArgmax nodes hn g

/-! ### Real splitting and strict logarithmic concavity

This section is deliberately upstream of `Interlacing.lean`: that module
imports this one.  We therefore use private chosen roots in the other gaps,
rather than importing or assuming the later public root-placement API.
-/

private lemma gapPolynomial_ne_zero_critical {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapPolynomial nodes g ≠ 0 := by
  intro hzero
  have h := gapPolynomial_eval_left nodes g
  rw [hzero, Polynomial.eval_zero] at h
  norm_num at h

private abbrev CriticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}

@[simp]
private lemma card_criticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (CriticalOtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega

private theorem exists_criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    ∃ r ∈ openGap nodes h, (gapPolynomial nodes g).eval r = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let a : ℝ := nodes.point (gapLeftIndex h)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hab : a ≤ b := (gap_left_lt_right nodes h).le
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have ha : p.eval a = gapCoefficient g (gapLeftIndex h) := by
    exact gapPolynomial_eval_node nodes g (gapLeftIndex h)
  have hb : p.eval b = -gapCoefficient g (gapLeftIndex h) := by
    simp only [p, b]
    rw [gapPolynomial_eval_node, gapCoefficient_right_eq_neg_left_of_ne g h hhg]
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex h) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

private def criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : CriticalOtherGapIndex g) : ℝ :=
  Classical.choose (exists_criticalOtherGapRoot nodes g h.1 h.property)

private lemma criticalOtherGapRoot_mem_openGap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    criticalOtherGapRoot nodes g h ∈ openGap nodes h.1 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).1

private lemma gapPolynomial_eval_criticalOtherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    (gapPolynomial nodes g).eval (criticalOtherGapRoot nodes g h) = 0 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).2

private lemma criticalOtherGapRoot_strictMono {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    StrictMono (criticalOtherGapRoot nodes g) := by
  intro h k hhk
  have hindex : gapRightIndex h.1 ≤ gapLeftIndex k.1 := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    have hval : h.1.val < k.1.val := hhk
    omega
  calc
    criticalOtherGapRoot nodes g h < nodes.point (gapRightIndex h.1) :=
      (criticalOtherGapRoot_mem_openGap nodes g h).2
    _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
    _ < criticalOtherGapRoot nodes g k :=
      (criticalOtherGapRoot_mem_openGap nodes g k).1

/-- Every gap polynomial splits over `ℝ`.  The proof uses one root in each
other nodal gap; after their product is divided out, the interpolation degree
budget leaves a quotient of degree at most one. -/
theorem gapPolynomial_splits {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : (gapPolynomial nodes g).Splits := by
  classical
  let p : ℝ[X] := gapPolynomial nodes g
  let root : CriticalOtherGapIndex g → ℝ := criticalOtherGapRoot nodes g
  let D : ℝ[X] := ∏ h : CriticalOtherGapIndex g, (X - C (root h))
  have hrootInjective : Function.Injective root :=
    (criticalOtherGapRoot_strictMono nodes g).injective
  have hDvd : D ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro h
      rw [Polynomial.dvd_iff_isRoot]
      exact gapPolynomial_eval_criticalOtherGapRoot nodes g h
  obtain ⟨q, hq⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Monic
    exact monic_prod_of_monic _ _ fun h _hh => monic_X_sub_C (root h)
  have hDsplits : D.Splits := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Splits
    exact Polynomial.Splits.prod fun h _hh => Polynomial.Splits.X_sub_C (root h)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hqne : q ≠ 0 := by
    intro hzero
    apply hp
    rw [hzero, mul_zero] at hq
    exact hq
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_criticalOtherGapIndex]
  have hpdegree : p.natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hqdegree : q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hDne hqne, hDdegree] at hnat
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  change p.Splits
  rw [hq]
  exact hDsplits.mul (Polynomial.Splits.of_natDegree_le_one hqdegree)

private lemma gapPolynomial_root_not_mem_closedGap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hr : r ∈ (gapPolynomial nodes g).roots) :
    r ∉ closedGap nodes g := by
  intro hrclosed
  have hroot : (gapPolynomial nodes g).eval r = 0 := by
    rw [← Polynomial.IsRoot]
    exact (Polynomial.mem_roots (gapPolynomial_ne_zero_critical nodes g)).mp hr
  by_cases hleft : r = nodes.point (gapLeftIndex g)
  · rw [hleft, gapPolynomial_eval_left] at hroot
    norm_num at hroot
  by_cases hright : r = nodes.point (gapRightIndex g)
  · rw [hright, gapPolynomial_eval_right] at hroot
    norm_num at hroot
  have hopen : r ∈ openGap nodes g :=
    ⟨lt_of_le_of_ne hrclosed.1 (Ne.symm hleft),
      lt_of_le_of_ne hrclosed.2 hright⟩
  have hpos := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g hopen
  linarith

private lemma reciprocal_sub_strictAnti {a b x y r : ℝ}
    (hxy : x < y) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hr : r < a ∨ b < r) :
    1 / (y - r) < 1 / (x - r) := by
  have hxr : x - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans hx.1))
    · exact ne_of_lt (sub_neg.mpr (hx.2.trans hr))
  have hyr : y - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans (hx.1.trans hxy)))
    · exact ne_of_lt (sub_neg.mpr (hy.2.trans hr))
  have hprod : 0 < (x - r) * (y - r) := by
    rcases hr with hr | hr
    · exact mul_pos (sub_pos.mpr (hr.trans hx.1))
        (sub_pos.mpr (hr.trans hy.1))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans hr))
        (sub_neg.mpr (hy.2.trans hr))
  rw [← sub_pos]
  rw [show 1 / (x - r) - 1 / (y - r) =
      (y - x) / ((x - r) * (y - r)) by field_simp; ring]
  exact div_pos (sub_pos.mpr hxy) hprod

private lemma hasDerivAt_reciprocal_sub (x r : ℝ) (hxr : x ≠ r) :
    HasDerivAt (fun y : ℝ => 1 / (y - r)) (-1 / (x - r) ^ 2) x := by
  have hne : x - r ≠ 0 := sub_ne_zero.mpr hxr
  simpa only [one_div, id_eq, sub_eq_add_neg, add_comm] using
    ((hasDerivAt_id x).sub_const r).inv hne

private lemma hasDerivAt_rootReciprocalSum (roots : Multiset ℝ) (x : ℝ)
    (hx : ∀ r ∈ roots, x ≠ r) :
    HasDerivAt
      (fun y : ℝ => (roots.map fun r => 1 / (y - r)).sum)
      ((roots.map fun r => -1 / (x - r) ^ 2).sum) x := by
  induction roots using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | cons r roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (hasDerivAt_reciprocal_sub x r (hx r (by simp))).add
        (ih fun s hs => hx s (by simp [hs]))

/-- The logarithmic derivative `F'_g/F_g` is strictly decreasing throughout
the polynomial's own gap.  This is the root-budget form of the source's
critical-point argument. -/
theorem gapLogDerivative_strictAntiOn {n : ℕ} (nodes : OrderedNodes n)
    (hn : 4 ≤ n) (g : Fin (n - 1)) :
    StrictAntiOn
      (fun x => (gapPolynomial nodes g).derivative.eval x /
        (gapPolynomial nodes g).eval x)
      (openGap nodes g) := by
  intro x hx y hy hxy
  let p : ℝ[X] := gapPolynomial nodes g
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hpx : p.eval x ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hx))
  have hpy : p.eval y ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hy))
  change p.derivative.eval y / p.eval y < p.derivative.eval x / p.eval x
  rw [hsplit.eval_derivative_div_eval_of_ne_zero hpx,
    hsplit.eval_derivative_div_eval_of_ne_zero hpy]
  apply Multiset.sum_lt_sum
  · intro r hr
    apply (reciprocal_sub_strictAnti hxy hx hy ?_).le
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout
  · have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (hsplit.roots_ne_zero hnat)
    refine ⟨r, hr, reciprocal_sub_strictAnti hxy hx hy ?_⟩
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout

/-- For `n ≥ 4`, every derivative zero in the polynomial's own open gap is
the chosen compact maximizer. -/
lemma eq_gapArgmax_of_derivative_eval_eq_zero {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hrgap : r ∈ openGap nodes g)
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  have harggap := gapArgmax_mem_openGap nodes (by omega) g
  have harg := gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hanti := gapLogDerivative_strictAntiOn nodes hn g
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hanti hrgap harggap hlt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict
  · have hstrict := hanti harggap hrgap hgt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict

/-- Strict logarithmic concavity makes the critical point nondegenerate:
`F''_g(τ_g) < 0`.  This is stronger than uniqueness as a set-theoretic root
and is what makes division by `(X-τ_g)` retain a nonzero value at `τ_g`. -/
lemma gapPolynomial_secondDerivative_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) < 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let τ : ℝ := gapArgmax nodes g
  have hτgap : τ ∈ openGap nodes g := gapArgmax_mem_openGap nodes (by omega) g
  have hpτpos : 0 < p.eval τ := zero_lt_one.trans
    (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hτgap)
  have hpτ : p.eval τ ≠ 0 := hpτpos.ne'
  have hcrit : p.derivative.eval τ = 0 := by
    exact gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hrootNe : ∀ r ∈ p.roots, τ ≠ r := by
    intro r hr heq
    apply gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    rw [← heq]
    exact gapArgmax_mem_closedGap nodes g
  have hsumDeriv := hasDerivAt_rootReciprocalSum p.roots τ hrootNe
  have hevent :
      (fun x : ℝ => p.derivative.eval x / p.eval x) =ᶠ[𝓝 τ]
        (fun x : ℝ => (p.roots.map fun r => 1 / (x - r)).sum) := by
    filter_upwards [Ioo_mem_nhds hτgap.1 hτgap.2] with x hx
    exact hsplit.eval_derivative_div_eval_of_ne_zero
      (ne_of_gt (zero_lt_one.trans
        (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hx)))
  have hquotDeriv : HasDerivAt
      (fun x : ℝ => p.derivative.eval x / p.eval x)
      (p.derivative.derivative.eval τ / p.eval τ) τ := by
    have hraw := (p.derivative.hasDerivAt τ).div (p.hasDerivAt τ) hpτ
    apply hraw.congr_deriv
    rw [hcrit]
    field_simp
    ring
  have hcoeff :
      p.derivative.derivative.eval τ / p.eval τ =
        (p.roots.map fun r => -1 / (τ - r) ^ 2).sum :=
    hquotDeriv.unique (hsumDeriv.congr_of_eventuallyEq hevent)
  have hroots : p.roots ≠ 0 := by
    have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    exact hsplit.roots_ne_zero hnat
  have hterm (r : ℝ) (hr : r ∈ p.roots) : -1 / (τ - r) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr (hrootNe r hr)))
  have hsumneg : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum < 0 := by
    have hlt : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum <
        (p.roots.map fun _r => (0 : ℝ)).sum := by
      apply Multiset.sum_lt_sum
      · intro r hr
        exact (hterm r hr).le
      · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
        exact ⟨r, hr, hterm r hr⟩
    simpa using hlt
  have hratio : p.derivative.derivative.eval τ / p.eval τ < 0 := by
    rw [hcoeff]
    exact hsumneg
  rcases (div_neg_iff.mp hratio) with hbad | hneg
  · exact (not_lt_of_ge hpτpos.le hbad.2).elim
  · exact hneg.1

/-- Quotient of `F'_g` by the unique critical factor `(X - τ_g)`. -/
def gapDerivativeQuotient {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : ℝ[X] :=
  (gapPolynomial nodes g).derivative /ₘ (X - C (gapArgmax nodes g))

/-- Exact factorization consumed by the source Lemma 2 sign table and the
Jacobian evaluation matrix. -/
lemma X_sub_C_gapArgmax_mul_gapDerivativeQuotient {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (X - C (gapArgmax nodes g)) * gapDerivativeQuotient nodes g =
      (gapPolynomial nodes g).derivative := by
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (gapPolynomial_derivative_eval_gapArgmax nodes hn g)

lemma gapDerivativeQuotient_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) =
      (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) := by
  have h := congrArg (Polynomial.eval (gapArgmax nodes g))
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      (gapPolynomial nodes g).derivative (gapArgmax nodes g))
  simpa [gapDerivativeQuotient] using h

lemma gapDerivativeQuotient_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) < 0 := by
  rw [gapDerivativeQuotient_eval_gapArgmax]
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes hn g

/-- The critical quotient has the `≤ n-3` degree required by the source
Lemma 2/Jacobian matrix. -/
lemma natDegree_gapDerivativeQuotient_le_sub_three {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).natDegree ≤ n - 3 := by
  have hp : gapPolynomial nodes g ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hderivative :
      (gapPolynomial nodes g).derivative.natDegree ≤ n - 2 := by
    calc
      (gapPolynomial nodes g).derivative.natDegree ≤
          (gapPolynomial nodes g).natDegree - 1 :=
        Polynomial.natDegree_derivative_le _
      _ ≤ (n - 1) - 1 := Nat.sub_le_sub_right hpdegree 1
      _ = n - 2 := by omega
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  calc
    (gapPolynomial nodes g).derivative.natDegree - 1 ≤ (n - 2) - 1 :=
      Nat.sub_le_sub_right hderivative 1
    _ = n - 3 := by omega

/-- With exactly three nodes the derivative is at most linear. -/
lemma natDegree_gapPolynomial_derivative_le_one_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) :
    (gapPolynomial nodes g).derivative.natDegree ≤ 1 := by
  have hp : gapPolynomial nodes g ≠ 0 := by
    intro hzero
    have h := gapPolynomial_eval_left nodes g
    rw [hzero, Polynomial.eval_zero] at h
    norm_num at h
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ 2 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  exact (Polynomial.natDegree_derivative_le _).trans <| by omega

/-- The three-node case of the unique-critical-point claim: the chosen gap
maximizer is the derivative polynomial's unique real root, globally. -/
lemma eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) {r : ℝ}
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  let dp : ℝ[X] := (gapPolynomial nodes g).derivative
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero nodes (by norm_num) g
  have hrmem : r ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdp]
    exact hr
  have hamem : gapArgmax nodes g ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact gapArgmax_mem_derivative_roots nodes (by norm_num) g
  by_contra hne
  have hpair : ({r, gapArgmax nodes g} : Finset ℝ) ⊆ dp.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hrmem
    · exact hamem
  have hcard : 2 ≤ dp.roots.toFinset.card := by
    have := Finset.card_le_card hpair
    simpa [hne] using this
  have hdegree : dp.roots.toFinset.card ≤ 1 :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' dp).trans
        (natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes g)
  omega

/-- In the two-node case the unique gap coefficient vector is constantly
one, hence the gap polynomial is the constant polynomial one. -/
lemma gapPolynomial_eq_one_of_two_nodes (nodes : OrderedNodes 2) (g : Fin 1) :
    gapPolynomial nodes g = 1 := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  have hcoeff : (gapCoefficient (0 : Fin 1) : Fin 2 → ℝ) = 1 := by
    funext k
    fin_cases k <;> simp [gapCoefficient_of_le, gapCoefficient_of_lt]
  rw [gapPolynomial, hcoeff]
  exact Lagrange.interpolate_one nodes.injective.injOn
    ⟨(0 : Fin 2), Finset.mem_univ _⟩

@[simp]
lemma gapPolynomial_derivative_eq_zero_of_two_nodes (nodes : OrderedNodes 2)
    (g : Fin 1) :
    (gapPolynomial nodes g).derivative = 0 := by
  rw [gapPolynomial_eq_one_of_two_nodes]
  simp

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Interlacing.lean` -/

/-!
# First root-separation lemmas for the de Boor--Pinkus source kernel

Section 2 of de Boor--Pinkus begins its interlacing argument with the facts
that the signed polynomial for one gap changes sign across every other nodal
gap and its derivative vanishes in its own gap.  This file proves those
facts, strictly orders one root in every other gap, proves those selected
roots simple by making the source's implicit multiplicity/parity argument
explicit, and isolates the one remaining degree slot.  Exhaustion in the
degree-`n-2` branch is proved exactly; the degree-`n-1` branch and cross-
polynomial strict interlacing remain for the full source Lemmas 1 and 2.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Every point in an earlier open nodal gap lies before every point in a
later open nodal gap. -/
lemma openGap_point_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    {g h : Fin (n - 1)} (hgh : g < h) {x y : ℝ}
    (hx : x ∈ openGap nodes g) (hy : y ∈ openGap nodes h) :
    x < y := by
  have hindex : gapRightIndex g ≤ gapLeftIndex h := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    omega
  calc
    x < nodes.point (gapRightIndex g) := hx.2
    _ ≤ nodes.point (gapLeftIndex h) := nodes.strictMono.monotone hindex
    _ < y := hy.1

/-- Indices of all nodal gaps other than `g`. -/
abbrev OtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}

@[simp]
lemma card_otherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (OtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/CrossInterlacing.lean` -/

/-!
# Cross-polynomial root separation

This file follows the proof of de Boor--Pinkus, Section 2, Lemma 1.  For two
gap polynomials `F_g,F_h` with `g<h`, the source uses the two combinations

`F_g - (-1)^(h-g) F_h` and `F_g + (-1)^(h-g) F_h`.

The first vanishes at all nodal points outside the block and alternates at
the nodes inside it; the second has the complementary nodal pattern.  The
root counts, quotient parity, and resulting signs below prove equations
`(5a--f)` and their strict common-gap root order.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Polynomial
noncomputable section

/-- The parity factor used by the source for a pair of gap indices. -/
def gapPairParity {n : ℕ} (g h : Fin (n - 1)) : ℝ :=
  (-1 : ℝ) ^ (h.val - g.val)

lemma gapPairParity_eq_one_or_neg_one {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h = 1 ∨ gapPairParity g h = -1 := by
  rw [gapPairParity]
  generalize h.val - g.val = m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      rcases ih with ih | ih <;> simp [ih]

@[simp]
lemma sq_gapPairParity {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h ^ 2 = 1 := by
  rcases gapPairParity_eq_one_or_neg_one g h with hp | hp <;> simp [hp]

/-- Coefficient relation underlying both source combinations. -/
lemma gapPairParity_mul_gapCoefficient {n : ℕ} (g h : Fin (n - 1))
    (hgh : g < h) (k : Fin n) :
    gapPairParity g h * gapCoefficient h k =
      if k.val ≤ g.val ∨ h.val < k.val then
        gapCoefficient g k
      else
        -gapCoefficient g k := by
  by_cases hkg : k.val ≤ g.val
  · have hkh : k.val ≤ h.val := hkg.trans hgh.le
    rw [if_pos (Or.inl hkg), gapPairParity, gapCoefficient_of_le g k hkg,
      gapCoefficient_of_le h k hkh]
    have hexp : (h.val - g.val) + (h.val - k.val) =
        (g.val - k.val) + 2 * (h.val - g.val) := by omega
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  · have hgk : g.val < k.val := Nat.lt_of_not_ge hkg
    by_cases hhk : h.val < k.val
    · rw [if_pos (Or.inr hhk), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_lt h k hhk]
      have hexp : (h.val - g.val) + (k.val - h.val - 1) =
          k.val - g.val - 1 := by omega
      rw [← pow_add, hexp]
    · have hkle : k.val ≤ h.val := Nat.le_of_not_gt hhk
      rw [if_neg (by simp [hkg, hhk]), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_le h k hkle]
      have hexp : (h.val - g.val) + (h.val - k.val) =
          (k.val - g.val - 1) + (2 * (h.val - k.val) + 1) := by omega
      rw [← pow_add, hexp, pow_add]
      have hodd : (-1 : ℝ) ^ (2 * (h.val - k.val) + 1) = -1 := by
        rw [pow_add, pow_mul]
        norm_num
      rw [hodd]
      ring

/-- Source `G₁`: difference combination, zero outside the index block. -/
def gapDifferenceCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g - C (gapPairParity g h) * gapPolynomial nodes h

/-- Source `G₂`: sum combination, zero inside the index block. -/
def gapSumCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g + C (gapPairParity g h) * gapPolynomial nodes h

lemma gapDifferenceCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapDifferenceCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 0
      else 2 * gapCoefficient g k := by
  rw [gapDifferenceCombination, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring

lemma gapSumCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapSumCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 2 * gapCoefficient g k
      else 0 := by
  rw [gapSumCombination, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring

lemma degree_gapDifferenceCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)

lemma degree_gapSumCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapSumCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_add_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)

lemma gapDifferenceCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapDifferenceCombination nodes g h ≠ 0 := by
  let k : Fin n := gapRightIndex g
  have hinside : ¬(k.val ≤ g.val ∨ h.val < k.val) := by
    simp only [k, gapRightIndex_val]
    omega
  have heval := gapDifferenceCombination_eval_node nodes g h hgh k
  rw [if_neg hinside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm

/-- The difference combination has a root in every gap strictly between
`g` and `h`; these are the non-nodal roots in the source count for `G₁`. -/
theorem exists_gapDifferenceCombination_root_in_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hgq : g < q) (hqh : q < h) :
    ∃ r ∈ openGap nodes q, (gapDifferenceCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftInside : ¬((gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val) := by
    simp only [gapLeftIndex_val]
    omega
  have hrightInside : ¬((gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val) := by
    simp only [gapRightIndex_val]
    omega
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_neg hleftInside] using
      gapDifferenceCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := ne_of_gt hgq
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_neg hrightInside] using
          gapDifferenceCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

/-- The complete `n-1`-point root list for the difference combination:
outside the block use its nodal roots; inside use the IVT root in that gap. -/
def gapDifferenceRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) : ℝ :=
  if hqg : q.val ≤ g.val then
    nodes.point (gapLeftIndex q)
  else if hhq : h.val ≤ q.val then
    nodes.point (gapRightIndex q)
  else
    Classical.choose (exists_gapDifferenceCombination_root_in_middleGap
      nodes g h q hgh (by omega) (by omega))

lemma gapDifferenceRootPoint_eq_left_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqg : q.val ≤ g.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapLeftIndex q) := by
  simp [gapDifferenceRootPoint, hqg]

lemma gapDifferenceRootPoint_eq_right_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hhq : h.val ≤ q.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapRightIndex q) := by
  have hnqg : ¬q.val ≤ g.val := by omega
  simp [gapDifferenceRootPoint, hnqg, hhq]

lemma gapDifferenceRootPoint_mem_openGap_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) (hgq : g < q) (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q ∈ openGap nodes q := by
  have hnqg : ¬q.val ≤ g.val := by omega
  have hnhq : ¬h.val ≤ q.val := by omega
  simp only [gapDifferenceRootPoint, dif_neg hnqg, dif_neg hnhq]
  exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
    nodes g h q hgh hgq hqh)).1

lemma gapDifferenceCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).eval
      (gapDifferenceRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapDifferenceCombination_eval_node nodes g h hgh]
    simp [hqg]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapDifferenceCombination_eval_node nodes g h hgh]
      simp [hhq]
    · have hgq : g < q := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      simp only [gapDifferenceRootPoint, dif_neg hqg, dif_neg hhq]
      exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
        nodes g h q hgh hgq hqh)).2

lemma gapDifferenceRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) :
    gapDifferenceRootPoint nodes g h hgh q ∈ closedGap nodes q := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact ⟨le_rfl, (gap_left_lt_right nodes q).le⟩
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
      exact ⟨(gap_left_lt_right nodes q).le, le_rfl⟩
    · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      have hopen := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      exact ⟨hopen.1.le, hopen.2.le⟩

lemma gapDifferenceRootPoint_lt_right_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact gap_left_lt_right nodes q
  · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).2

lemma left_lt_gapDifferenceRootPoint_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hgq : g < q) :
    nodes.point (gapLeftIndex q) < gapDifferenceRootPoint nodes g h hgh q := by
  by_cases hhq : h.val ≤ q.val
  · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
    exact gap_left_lt_right nodes q
  · have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).1

lemma gapDifferenceRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapDifferenceRootPoint nodes g h hgh) := by
  intro q r hqr
  by_cases hqh : q < h
  · calc
      gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) :=
        gapDifferenceRootPoint_lt_right_of_lt nodes g h hgh q hqh
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapDifferenceRootPoint nodes g h hgh r :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).1
  · have hhq : h ≤ q := le_of_not_gt hqh
    have hgr : g < r := hgh.trans_le (hhq.trans hqr.le)
    calc
      gapDifferenceRootPoint nodes g h hgh q ≤ nodes.point (gapRightIndex q) :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh q).2
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ < gapDifferenceRootPoint nodes g h hgh r :=
        left_lt_gapDifferenceRootPoint_of_lt nodes g h hgh r hgr

lemma gapSumCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapSumCombination nodes g h ≠ 0 := by
  let k : Fin n := gapLeftIndex g
  have houtside : k.val ≤ g.val ∨ h.val < k.val := by
    exact Or.inl (by simp only [k, gapLeftIndex_val]; exact le_rfl)
  have heval := gapSumCombination_eval_node nodes g h hgh k
  rw [if_pos houtside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm

/-- The sum combination has a root in every nodal gap outside the closed
index block from `g` through `h`. -/
theorem exists_gapSumCombination_root_in_outerGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hq : q < g ∨ h < q) :
    ∃ r ∈ openGap nodes q, (gapSumCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapSumCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftOutside : (gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapLeftIndex_val]; omega)
    · exact Or.inr (by simp only [gapLeftIndex_val]; omega)
  have hrightOutside : (gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapRightIndex_val]; omega)
    · exact Or.inr (by simp only [gapRightIndex_val]; omega)
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_pos hleftOutside] using
      gapSumCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := by rcases hq with hqg | hhq <;> omega
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_pos hrightOutside] using
          gapSumCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

/-- A complete source-count list of `n-2` distinct roots of the sum
combination.  The omitted gap index is `h`: outside the block the entry is
an IVT root, while inside the block it is the right nodal endpoint. -/
def gapSumRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) : ℝ :=
  if hqg : q.1 < g then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))
  else if hhq : h < q.1 then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))
  else
    nodes.point (gapRightIndex q.1)

lemma gapSumRootPoint_mem_openGap_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q ∈ openGap nodes q.1 := by
  rcases hq with hqg | hhq
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).1
  · have hnqg : ¬q.1 < g := by omega
    simp only [gapSumRootPoint, dif_neg hnqg, dif_pos hhq]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))).1

lemma gapSumRootPoint_eq_right_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) (hqh : q.1 < h) :
    gapSumRootPoint nodes g h hgh q = nodes.point (gapRightIndex q.1) := by
  have hnqg : ¬q.1 < g := not_lt.mpr hgq
  have hnhq : ¬h < q.1 := not_lt.mpr hqh.le
  simp [gapSumRootPoint, hnqg, hnhq]

lemma gapSumCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) :
    (gapSumCombination nodes g h).eval
      (gapSumRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.1 < g
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).2
  · by_cases hhq : h < q.1
    · simp only [gapSumRootPoint, dif_neg hqg, dif_pos hhq]
      exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
        nodes g h q.1 hgh (Or.inr hhq))).2
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh,
        gapSumCombination_eval_node nodes g h hgh]
      simp only [gapRightIndex_val]
      split_ifs with houtside
      · rcases houtside with houtside | houtside <;> omega
      · rfl

lemma gapSumRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) :
    gapSumRootPoint nodes g h hgh q ∈ closedGap nodes q.1 := by
  by_cases hqg : q.1 < g
  · have hopen := gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inl hqg)
    exact ⟨hopen.1.le, hopen.2.le⟩
  · by_cases hhq : h < q.1
    · have hopen := gapSumRootPoint_mem_openGap_of_outer
        nodes g h hgh q (Or.inr hhq)
      exact ⟨hopen.1.le, hopen.2.le⟩
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      exact ⟨(gap_left_lt_right nodes q.1).le, le_rfl⟩

lemma gapSumRootPoint_lt_right_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
  (gapSumRootPoint_mem_openGap_of_outer nodes g h hgh q hq).2

lemma left_lt_gapSumRootPoint_of_g_le {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) :
    nodes.point (gapLeftIndex q.1) < gapSumRootPoint nodes g h hgh q := by
  by_cases hhq : h < q.1
  · exact (gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inr hhq)).1
  · have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
    rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
    exact gap_left_lt_right nodes q.1

lemma gapSumRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapSumRootPoint nodes g h hgh) := by
  intro q r hqr
  have hqrval : q.1 < r.1 := hqr
  by_cases hqg : q.1 < g
  · calc
      gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
        gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inl hqg)
      _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapSumRootPoint nodes g h hgh r :=
        (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
  · by_cases hhq : h < q.1
    · calc
        gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
          gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inr hhq)
        _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        _ ≤ gapSumRootPoint nodes g h hgh r :=
          (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      have hgr : g ≤ r.1 := hgq.trans hqrval.le
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      calc
        nodes.point (gapRightIndex q.1) ≤ nodes.point (gapLeftIndex r.1) :=
          nodes.strictMono.monotone <| by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
        _ < gapSumRootPoint nodes g h hgh r :=
          left_lt_gapSumRootPoint_of_g_le nodes g h hgh r hgr

lemma natDegree_gapSumCombination_le_sub_one {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    (gapSumCombination nodes g h).natDegree ≤ n - 1 := by
  have hdegree := degree_gapSumCombination_le nodes g h
  rw [Polynomial.degree_eq_natDegree
    (gapSumCombination_ne_zero nodes g h hgh)] at hdegree
  exact_mod_cast hdegree

private lemma neg_one_pow_card_filter_mul_prod_pos {α : Type*}
    [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hneg : ∀ x ∈ s, p x → f x < 0)
    (hpos : ∀ x ∈ s, ¬p x → 0 < f x) :
    0 < (-1 : ℝ) ^ (s.filter p).card * ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have ih' := ih (fun y hy => hneg y (Finset.mem_insert_of_mem hy))
        (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      by_cases hpx : p x
      · have hfx : f x < 0 := hneg x (Finset.mem_insert_self x s) hpx
        have hxfilter : x ∉ s.filter p := by simp [hxs]
        rw [Finset.filter_insert, if_pos hpx,
          Finset.card_insert_of_notMem hxfilter, pow_succ,
          Finset.prod_insert hxs]
        nlinarith
      · have hfx : 0 < f x := hpos x (Finset.mem_insert_self x s) hpx
        rw [Finset.filter_insert, if_neg hpx, Finset.prod_insert hxs]
        calc
          0 < ((-1 : ℝ) ^ (s.filter p).card * ∏ y ∈ s, f y) * f x :=
            mul_pos ih' hfx
          _ = (-1 : ℝ) ^ (s.filter p).card * (f x * ∏ y ∈ s, f y) := by ring

private lemma card_filter_middle_otherGapIndex {n : ℕ}
    (g h : Fin (n - 1)) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun q => g ≤ q.1 ∧ q.1 < h)).card = h.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun q => g ≤ q.1 ∧ q.1 < h)
  have himage : S.image (fun q => q.1) = Finset.Ico g h := by
    ext q
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨r, ⟨hgr, hrh⟩, rfl⟩
      exact ⟨hgr, hrh⟩
    · intro hq
      exact ⟨⟨q, ne_of_lt hq.2⟩, ⟨hq.1, hq.2⟩, rfl⟩
  calc
    S.card = (S.image (fun q => q.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g h).card := congrArg Finset.card himage
    _ = h.val - g.val := by simp

private lemma eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos
    (Q : ℝ[X]) {a b x : ℝ} (hdegree : Q.natDegree ≤ 1)
    (hprod : 0 < Q.eval a * Q.eval b) (hx : x ∈ Set.Ioo a b) :
    Q.eval x ≠ 0 := by
  intro hxzero
  have hxroot : Q.IsRoot x := hxzero
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hxroot
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hprod
    norm_num at hprod
  have hRne : R ≠ 0 := by
    intro hzero
    apply hQne
    rw [hzero, mul_zero] at hR
    exact hR
  have hRdegree : R.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hR
    rw [Polynomial.natDegree_mul (X_sub_C_ne_zero x) hRne,
      natDegree_X_sub_C] at hnat
    omega
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hRdegree
  have hc : c ≠ 0 := by
    intro hc
    apply hQne
    simpa [hc] using hR
  have hQprodNeg : Q.eval a * Q.eval b < 0 := by
    rw [hR]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    calc
      (a - x) * c * ((b - x) * c) =
          ((a - x) * (b - x)) * c ^ 2 := by ring
      _ < 0 := mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx.1) (sub_pos.mpr hx.2))
        (sq_pos_of_ne_zero hc)
  exact hprod.not_gt hQprodNeg

private lemma eval_mul_eval_pos_of_no_root_between (P : ℝ[X])
    {a b : ℝ} (hab : a < b) (ha : P.eval a ≠ 0) (hb : P.eval b ≠ 0)
    (hroot : ∀ {x : ℝ}, x ∈ Set.Ioo a b → ¬P.IsRoot x) :
    0 < P.eval a * P.eval b := by
  have hprodne : P.eval a * P.eval b ≠ 0 := mul_ne_zero ha hb
  apply lt_of_le_of_ne (le_of_not_gt fun hneg => ?_) hprodne.symm
  rcases mul_neg_iff.mp hneg with hsign | hsign
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) :=
      ⟨hsign.2, hsign.1⟩
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo' hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := hsign
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero

/-- Product of the `n-2` explicitly listed roots of the sum combination. -/
def gapSumRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ k : OtherGapIndex h, (X - C (gapSumRootPoint nodes g h hgh k))

/-- Reusable checked factor data behind the source's parity argument. -/
structure GapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  quotient : ℝ[X]
  factor : gapSumCombination nodes g h =
    gapSumRootProduct nodes g h hgh * quotient
  quotient_ne_zero : quotient ≠ 0
  quotient_natDegree_le_one : quotient.natDegree ≤ 1
  quotient_endpoint_product_pos :
    0 < quotient.eval (nodes.point (gapLeftIndex g)) *
      quotient.eval (nodes.point (gapRightIndex h))

private theorem exists_gapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapSumFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapSumCombination nodes g h
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapSumCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapSumRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact gapSumCombination_eval_rootPoint nodes g h hgh k
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (root k)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_otherGapIndex]
  have hQdegree : Q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      simpa only [P] using natDegree_gapSumCombination_le_sub_one nodes g h hgh
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (b - root k)
  let middle : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < h
  have hpairNeg : ∀ k : OtherGapIndex h, middle k → pairValue k < 0 := by
    intro k hk
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk.2
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootb : root k < b := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapRightIndex_val]
      omega
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootb)
  have hpairPos : ∀ k : OtherGapIndex h, ¬middle k → 0 < pairValue k := by
    intro k hk
    have hkouter : k.1 < g ∨ h < k.1 := by
      by_cases hkg : k.1 < g
      · exact Or.inl hkg
      · right
        have hgk : g ≤ k.1 := le_of_not_gt hkg
        have hnotlt : ¬k.1 < h := fun hlt => hk ⟨hgk, hlt⟩
        exact lt_of_le_of_ne (le_of_not_gt hnotlt) k.property.symm
    rcases hkouter with hkg | hhk
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hab))
    · have hbroot : b < root k := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inr hhk)
        have hindex : gapRightIndex h ≤ gapLeftIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          b = nodes.point (gapRightIndex h) := rfl
          _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
          _ < root k := by simpa only [root] using hmem.1
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbroot))
        (sub_neg.mpr hbroot)
  have hpairProduct :
      0 < gapPairParity g h * ∏ k : OtherGapIndex h, pairValue k := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) middle pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_middle_otherGapIndex g h] at hsign
    simpa [gapPairParity] using hsign
  have hDevalProduct : 0 < gapPairParity g h * (D.eval a * D.eval b) := by
    have heq : D.eval a * D.eval b = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    exact hpairProduct
  have hPa : P.eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hPb : P.eval b = 2 * gapPairParity g h := by
    have houtside : (gapRightIndex h).val ≤ g.val ∨
        h.val < (gapRightIndex h).val := Or.inr (by simp)
    have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapRightIndex h)
    have hhval : h.val < (gapRightIndex h).val := by simp
    rw [if_pos houtside,
      gapCoefficient_of_lt h (gapRightIndex h) hhval] at hrel
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside, hrel.symm]
    simp only [gapRightIndex_val]
    norm_num
  have hPevalProduct : 0 < gapPairParity g h * (P.eval a * P.eval b) := by
    rw [hPa, hPb]
    nlinarith [sq_gapPairParity g h]
  have hQevalProduct : 0 < Q.eval a * Q.eval b := by
    have hfactor : gapPairParity g h * (P.eval a * P.eval b) =
        (gapPairParity g h * (D.eval a * D.eval b)) * (Q.eval a * Q.eval b) := by
      rw [hQ]
      simp only [Polynomial.eval_mul]
      ring
    have hmul : 0 < (gapPairParity g h * (D.eval a * D.eval b)) *
        (Q.eval a * Q.eval b) := by rwa [← hfactor]
    rcases mul_pos_iff.mp hmul with hgood | hbad
    · exact hgood.2
    · exact (hDevalProduct.not_gt hbad.1).elim
  refine ⟨⟨Q, ?_, hQne, hQdegree, ?_⟩⟩
  · simpa only [P, D] using hQ
  · simpa only [a, b] using hQevalProduct

private lemma card_filter_between_otherGapIndex {n : ℕ}
    (h g u : Fin (n - 1)) (huh : u < h) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun k => g ≤ k.1 ∧ k.1 < u)).card = u.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun k => g ≤ k.1 ∧ k.1 < u)
  have himage : S.image (fun k => k.1) = Finset.Ico g u := by
    ext k
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hgj, hju⟩, rfl⟩
      exact ⟨hgj, hju⟩
    · intro hk
      exact ⟨⟨k, ne_of_lt (hk.2.trans huh)⟩, ⟨hk.1, hk.2⟩, rfl⟩
  calc
    S.card = (S.image (fun k => k.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g u).card := congrArg Finset.card himage
    _ = u.val - g.val := by simp

/-- Source `(5f)` sign on every middle gap. -/
theorem gapSumCombination_sign_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hgq : g ≤ q) (hqh : q < h) {x : ℝ} (hx : x ∈ openGap nodes q) :
    0 < (-1 : ℝ) ^ (q.val - g.val) *
      (gapSumCombination nodes g h).eval x := by
  classical
  let data := Classical.choice (exists_gapSumFactorData nodes g h hgh)
  let Q : ℝ[X] := data.quotient
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hax : a < x := by
    have hindex : gapLeftIndex g ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapLeftIndex_val]
      omega
    exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
  have hxb : x < b := by
    have hindex : gapRightIndex q ≤ gapRightIndex h := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val]
      omega
    exact hx.2.trans_le (nodes.strictMono.monotone hindex)
  have hQa : Q.eval a ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt data.quotient_endpoint_product_pos)
  have hQx : Q.eval x ≠ 0 :=
    eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hax, hxb⟩
  have hQax : 0 < Q.eval a * Q.eval x := by
    apply eval_mul_eval_pos_of_no_root_between Q hax hQa hQx
    intro z hz hzroot
    have hzne := eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hz.1, hz.2.trans hxb⟩
    exact hzne hzroot
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (x - root k)
  let before : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < q
  have hpairNeg : ∀ k : OtherGapIndex h, before k → pairValue k < 0 := by
    intro k hk
    have hk_h : k.1 < h := hk.2.trans hqh
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk_h
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootx : root k < x := by
      rw [hrootEq]
      have hindex : gapRightIndex k.1 ≤ gapLeftIndex q := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootx)
  have hpairPos : ∀ k : OtherGapIndex h, ¬before k → 0 < pairValue k := by
    intro k hk
    by_cases hkg : k.1 < g
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hax))
    · have hgk : g ≤ k.1 := le_of_not_gt hkg
      have hqk : q ≤ k.1 := by
        by_contra hnot
        exact hk ⟨hgk, lt_of_not_ge hnot⟩
      have hxroot : x < root k := by
        by_cases hhk : h < k.1
        · have hmem := gapSumRootPoint_mem_openGap_of_outer
            nodes g h hgh k (Or.inr hhk)
          have hindex : gapRightIndex q ≤ gapLeftIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
          calc
            x < nodes.point (gapRightIndex q) := hx.2
            _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
            _ < root k := by simpa only [root] using hmem.1
        · have hkh : k.1 < h :=
            lt_of_le_of_ne (le_of_not_gt hhk) k.property
          have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
            simpa only [root] using gapSumRootPoint_eq_right_of_between
              nodes g h hgh k hgk hkh
          rw [hrootEq]
          have hindex : gapRightIndex q ≤ gapRightIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val]
            omega
          exact hx.2.trans_le (nodes.strictMono.monotone hindex)
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hax.trans hxroot))
        (sub_neg.mpr hxroot)
  have hDax : 0 < (-1 : ℝ) ^ (q.val - g.val) * (D.eval a * D.eval x) := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) before pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_between_otherGapIndex h g q hqh] at hsign
    have heq : D.eval a * D.eval x = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    simpa using hsign
  have hPa : (gapSumCombination nodes g h).eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hfactor : gapSumCombination nodes g h = D * Q := by
    simpa only [D, Q] using data.factor
  have htotal : 0 < (-1 : ℝ) ^ (q.val - g.val) *
      ((gapSumCombination nodes g h).eval a *
        (gapSumCombination nodes g h).eval x) := by
    rw [hfactor]
    simp only [Polynomial.eval_mul]
    nlinarith [mul_pos hDax hQax]
  rw [hPa] at htotal
  nlinarith

/-- Monic product over the exhaustive root list of the difference
combination. -/
def gapDifferenceRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ q : Fin (n - 1), (X - C (gapDifferenceRootPoint nodes g h hgh q))

/-- Since the difference combination has exactly `n-1` roots and degree at
most `n-1`, it is a nonzero scalar multiple of its monic root product. -/
structure GapDifferenceFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  factor : gapDifferenceCombination nodes g h =
    gapDifferenceRootProduct nodes g h hgh * C scale

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/DerivativeInterlacing.lean` -/

/-!
# Derivative interlacing and the critical-quotient sign table

This file isolates source Lemma 2 of de Boor--Pinkus.  The critical points
`gapArgmax nodes g` are written in their actual nodal-gap order, and the
quotient `gapDerivativeQuotient nodes g = F'_g / (X - τ_g)` is kept in the
fixed sign convention of `GapCritical`.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Polynomial
noncomputable section

/-- Critical points occur in strict nodal-gap order. -/
lemma gapArgmax_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) {g h : Fin (n - 1)} (hgh : g < h) :
    gapArgmax nodes g < gapArgmax nodes h := by
  exact openGap_point_lt_of_gap_lt nodes hgh
    (gapArgmax_mem_openGap nodes hn g)
    (gapArgmax_mem_openGap nodes hn h)

lemma gapArgmax_strictMono {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    StrictMono (gapArgmax nodes) :=
  fun _g _h hgh => gapArgmax_lt_of_gap_lt nodes hn hgh

/-- Off the removed critical point, quotient evaluation is exactly derivative
evaluation divided by the ordered critical-point displacement. -/
lemma gapDerivativeQuotient_eval_eq_derivative_div {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (i j : Fin (n - 1)) (hij : j ≠ i) :
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) =
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) /
        (gapArgmax nodes j - gapArgmax nodes i) := by
  have hargne : gapArgmax nodes j - gapArgmax nodes i ≠ 0 := by
    rw [sub_ne_zero]
    exact (gapArgmax_strictMono nodes hn).injective.ne hij
  have hfactor := congrArg (Polynomial.eval (gapArgmax nodes j))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  rw [eq_div_iff hargne]
  calc
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) *
        (gapArgmax nodes j - gapArgmax nodes i) =
        (gapArgmax nodes j - gapArgmax nodes i) *
          (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) := by ring
    _ = (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) := hfactor

/-- The raw quotient sign table used by the Jacobian evaluation matrix.
The committed sign convention makes every diagonal entry negative.  Every
off-diagonal entry has checkerboard sign `(-1)^(i+j)`.

The finite Markov/Wronskian argument below inhabits this proposition for
every `n ≥ 4`; the separate constant-quotient proof handles `n = 3`. -/
def DerivativeQuotientSignTable {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  (∀ i : Fin (n - 1),
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes i) < 0) ∧
  (∀ i j : Fin (n - 1), i ≠ j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j))

/-- The derivative-evaluation form of the off-diagonal part of source
Lemma 2.  Splitting at `i<j` is intentional: the factor
`\tau_j-\tau_i` changes sign across the diagonal.

This is the exact finite Markov conclusion proved below from the source's
sum/difference root counts and a checked negative-squares Wronskian
identity. -/
def CrossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) : Prop :=
  (∀ i j : Fin (n - 1), i < j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j)) ∧
  (∀ i j : Fin (n - 1), j < i →
    (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) < 0)

/-- Conversely, once the finite Markov derivative signs are known, division
by the ordered critical displacement gives the paper's quotient sign table.
The diagonal is supplied independently by strict concavity on the owning
gap. -/
theorem derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable
    {n : ℕ} (nodes : OrderedNodes n) (hn : 4 ≤ n)
    (hcross : CrossDerivativeCriticalSignTable nodes) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · exact fun i => gapDerivativeQuotient_eval_gapArgmax_neg nodes hn i
  · intro i j hij
    rw [gapDerivativeQuotient_eval_eq_derivative_div nodes (by omega) i j hij.symm]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos (hcross.1 i j hijlt)
          (sub_pos.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hijlt))
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos_of_neg_of_neg (hcross.2 i j hjilt)
          (sub_neg.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hjilt))

/-! ### A finite Markov kernel via the two source combinations

For `D = F_g - ε F_h` and `S = F_g + ε F_h`, the checked roots of
`D` are exhaustive and simple.  The source `S`-roots lie one in every
interval between consecutive `D`-roots.  The following elementary
Lagrange/Wronskian kernel is the finite specialization needed here: if the
residues `S(d_k) / D'(d_k)` are positive, then

`D S' - D' S < 0`

on the whole real line.  This is the sum-of-negative-squares proof of the
Markov monotonicity assertion, not an imported interlacing theorem. -/

private def finiteRootProduct {m : ℕ} (d : Fin m → ℝ) : ℝ[X] :=
  ∏ k : Fin m, (X - C (d k))

private def finiteRootComplement {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  ∏ l ∈ (Finset.univ.erase k : Finset (Fin m)), (X - C (d l))

private lemma finiteRootProduct_eq_mul_complement {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    finiteRootProduct d = (X - C (d k)) * finiteRootComplement d k := by
  classical
  rw [finiteRootProduct, Fintype.prod_eq_mul_prod_compl k]
  simp only [finiteRootComplement, Finset.compl_singleton]

private lemma finiteRootComplement_eval_self_ne_zero {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    (finiteRootComplement d k).eval (d k) ≠ 0 := by
  classical
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  exact sub_ne_zero.mpr (hd.ne hlk.symm)

private lemma finiteRootProduct_derivative_eval_root {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    (finiteRootProduct d).derivative.eval (d k) =
      (finiteRootComplement d k).eval (d k) := by
  rw [finiteRootProduct_eq_mul_complement d k, Polynomial.derivative_mul]
  simp

/-- Cardinal basis attached to a finite strictly ordered root list, written
in the unnormalized complement-product form needed by the Wronskian
calculation. -/
private def finiteRootBasis {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  C ((finiteRootComplement d k).eval (d k))⁻¹ *
    finiteRootComplement d k

private lemma finiteRootBasis_eval_self {m : ℕ} {d : Fin m → ℝ}
    (hd : Function.Injective d) (k : Fin m) :
    (finiteRootBasis d k).eval (d k) = 1 := by
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  exact inv_mul_cancel₀ (finiteRootComplement_eval_self_ne_zero hd k)

private lemma finiteRootBasis_eval_of_ne {m : ℕ} {d : Fin m → ℝ}
    (k l : Fin m) (hlk : l ≠ k) :
    (finiteRootBasis d k).eval (d l) = 0 := by
  classical
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  suffices (finiteRootComplement d k).eval (d l) = 0 by rw [this, mul_zero]
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩)
  simp

private lemma finiteRootBasis_eq_lagrangeBasis {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    finiteRootBasis d k = Lagrange.basis Finset.univ d k := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hd.injOn
  · have hEvalNe := finiteRootComplement_eval_self_ne_zero hd k
    have hComplementNe : finiteRootComplement d k ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.eval_zero] at hEvalNe
      exact hEvalNe rfl
    rw [finiteRootBasis, Polynomial.degree_mul,
      Polynomial.degree_C (inv_ne_zero hEvalNe), zero_add,
      Polynomial.degree_eq_natDegree hComplementNe,
      finiteRootComplement, natDegree_finset_prod_X_sub_C_eq_card,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · have hdegree := Lagrange.degree_basis hd.injOn (Finset.mem_univ k)
    rw [hdegree, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · intro l _hl
    by_cases hlk : l = k
    · subst l
      rw [finiteRootBasis_eval_self hd]
      exact (Lagrange.eval_basis_self hd.injOn (Finset.mem_univ k)).symm
    · rw [finiteRootBasis_eval_of_ne k l hlk]
      exact (Lagrange.eval_basis_of_ne (Ne.symm hlk) (Finset.mem_univ l)).symm

private lemma finiteRootBasis_wronskian {m : ℕ} (d : Fin m → ℝ)
    (scale : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (finiteRootBasis d k).eval x) =
      -(scale * ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  rw [finiteRootProduct_eq_mul_complement d k]
  simp only [finiteRootBasis, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring

private lemma finiteRootScaledBasis_wronskian {m : ℕ}
    (d : Fin m → ℝ) (scale value : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (C value * finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (C value * finiteRootBasis d k).eval x) =
      -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  have hbase := finiteRootBasis_wronskian d scale k x
  calc
    (finiteRootProduct d * C scale).eval x *
          (C value * finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (C value * finiteRootBasis d k).eval x =
        value * ((finiteRootProduct d * C scale).eval x *
          (finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (finiteRootBasis d k).eval x) := by
            simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
              zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
            ring
    _ = value * (-(scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2) := by rw [hbase]
    _ = -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by ring

private def finiteRootInterpolant {m : ℕ} (d : Fin m → ℝ)
    (S : ℝ[X]) : ℝ[X] :=
  ∑ k : Fin m, C (S.eval (d k)) * finiteRootBasis d k

private lemma finiteRootInterpolant_eq_lagrange {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    finiteRootInterpolant d S =
      Lagrange.interpolate Finset.univ d (fun k => S.eval (d k)) := by
  classical
  rw [finiteRootInterpolant, Lagrange.interpolate_apply]
  simp only [finiteRootBasis_eq_lagrangeBasis hd]

private lemma finiteRootInterpolant_degree_lt {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    (finiteRootInterpolant d S).degree < m := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ) (v := d)
      (fun k => S.eval (d k)) hd.injOn

private lemma finiteRootInterpolant_eval_root {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X])
    (k : Fin m) :
    (finiteRootInterpolant d S).eval (d k) = S.eval (d k) := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  exact Lagrange.eval_interpolate_at_node _ hd.injOn (Finset.mem_univ k)

private lemma exists_finiteRootComplement_eval_ne_zero {m : ℕ}
    (hm : 0 < m) {d : Fin m → ℝ} (hd : Function.Injective d) (x : ℝ) :
    ∃ k : Fin m, (finiteRootComplement d k).eval x ≠ 0 := by
  classical
  by_cases hx : ∃ k : Fin m, x = d k
  · obtain ⟨k, rfl⟩ := hx
    exact ⟨k, finiteRootComplement_eval_self_ne_zero hd k⟩
  · let k : Fin m := ⟨0, hm⟩
    refine ⟨k, ?_⟩
    simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro l _hl
    exact sub_ne_zero.mpr (fun heq => hx ⟨l, heq⟩)

/-- Finite V. A. Markov specialization in the form actually consumed below.
The proof is Lagrange interpolation modulo the exhaustive root product.
Every residue contributes a negative square, and at least one complementary
root product is nonzero at each real point. -/
private theorem finite_markov_wronskian_neg {m : ℕ} (hm : 0 < m)
    (d : Fin m → ℝ) (hd : Function.Injective d) (scale : ℝ)
    (hscale : scale ≠ 0) (S : ℝ[X]) (hSdegree : S.natDegree ≤ m)
    (hresidue : ∀ k : Fin m,
      0 < S.eval (d k) *
        (finiteRootProduct d * C scale).derivative.eval (d k))
    (x : ℝ) :
    (finiteRootProduct d * C scale).eval x * S.derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x * S.eval x < 0 := by
  classical
  let M : ℝ[X] := finiteRootProduct d
  let D : ℝ[X] := M * C scale
  let R : ℝ[X] := finiteRootInterpolant d S
  have hMmonic : M.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)), (X - C (d k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (d k)
  have hMne : M ≠ 0 := hMmonic.ne_zero
  have hMdegree : M.natDegree = m := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)),
      (X - C (d k))).natDegree = m
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hRdegree : R.degree < m := by
    simpa only [R] using finiteRootInterpolant_degree_lt hd S
  have hRnatDegree : R.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hRdegree.le
  have hMdvd : M ∣ S - R := by
    change (∏ k : Fin m, (X - C (d k))) ∣ S - R
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hd
    · intro k
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
        Polynomial.eval_sub]
      change S.eval (d k) - (finiteRootInterpolant d S).eval (d k) = 0
      rw [finiteRootInterpolant_eval_root hd S k, sub_self]
  obtain ⟨Q, hQ⟩ := hMdvd
  have hSRdegree : (S - R).natDegree ≤ m :=
    (Polynomial.natDegree_sub_le S R).trans (max_le hSdegree hRnatDegree)
  have hQdegree : Q.natDegree = 0 := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    · have hproduct : (M * Q).natDegree ≤ m := by
        rw [← hQ]
        exact hSRdegree
      rw [Polynomial.natDegree_mul hMne hQzero, hMdegree] at hproduct
      omega
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hSfactor : S = R + M * C q := by
    rw [← hq] at hQ
    calc
      S = (S - R) + R := by ring
      _ = M * C q + R := by rw [hQ]
      _ = R + M * C q := by ring
  have hWinvariant :
      D.eval x * S.derivative.eval x - D.derivative.eval x * S.eval x =
        D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x := by
    rw [hSfactor]
    dsimp only [D]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, mul_zero, add_zero,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  let coefficient : Fin m → ℝ := fun k =>
    S.eval (d k) * scale *
      ((finiteRootComplement d k).eval (d k))⁻¹
  have hcoefficient : ∀ k : Fin m, 0 < coefficient k := by
    intro k
    let e : ℝ := (finiteRootComplement d k).eval (d k)
    have he : e ≠ 0 := finiteRootComplement_eval_self_ne_zero hd k
    have hderivative : D.derivative.eval (d k) = e * scale := by
      simp only [D, M, Polynomial.derivative_mul, Polynomial.derivative_C,
        mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
      rw [finiteRootProduct_derivative_eval_root]
    have hpositive : 0 < S.eval (d k) * (e * scale) := by
      rw [← hderivative]
      simpa only [D, M] using hresidue k
    have he2 : 0 < e ^ 2 := sq_pos_of_ne_zero he
    have heq : coefficient k * e ^ 2 = S.eval (d k) * (e * scale) := by
      dsimp only [coefficient, e]
      field_simp
    nlinarith
  have hWsum :
      D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x =
        -∑ k : Fin m, coefficient k *
          ((finiteRootComplement d k).eval x) ^ 2 := by
    simp only [R, finiteRootInterpolant, Polynomial.derivative_sum,
      Polynomial.eval_finset_sum]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [finiteRootScaledBasis_wronskian]
    simp only [coefficient]
    ring
  have hsumPos : 0 < ∑ k : Fin m, coefficient k *
      ((finiteRootComplement d k).eval x) ^ 2 := by
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hcoefficient k).le (sq_nonneg _)
    · obtain ⟨k, hk⟩ := exists_finiteRootComplement_eval_ne_zero hm hd x
      exact ⟨k, Finset.mem_univ k,
        mul_pos (hcoefficient k) (sq_pos_of_ne_zero hk)⟩
  rw [hWinvariant, hWsum]
  exact neg_neg_of_pos hsumPos

private lemma negOnePowFilter_mul_prod_pos {α : Type*}
    [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hneg : ∀ x ∈ s, p x → f x < 0)
    (hpos : ∀ x ∈ s, ¬p x → 0 < f x) :
    0 < (-1 : ℝ) ^ (s.filter p).card * ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have ih' := ih (fun y hy => hneg y (Finset.mem_insert_of_mem hy))
        (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      by_cases hpx : p x
      · have hfx : f x < 0 := hneg x (Finset.mem_insert_self x s) hpx
        have hxfilter : x ∉ s.filter p := by simp [hxs]
        rw [Finset.filter_insert, if_pos hpx,
          Finset.card_insert_of_notMem hxfilter, pow_succ,
          Finset.prod_insert hxs]
        nlinarith
      · have hfx : 0 < f x := hpos x (Finset.mem_insert_self x s) hpx
        rw [Finset.filter_insert, if_neg hpx, Finset.prod_insert hxs]
        calc
          0 < ((-1 : ℝ) ^ (s.filter p).card * ∏ y ∈ s, f y) * f x :=
            mul_pos ih' hfx
          _ = (-1 : ℝ) ^ (s.filter p).card *
              (f x * ∏ y ∈ s, f y) := by ring

private lemma card_filter_gt_erase_fin {m : ℕ} (k : Fin m) :
    (((Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l))).card = m - 1 - k.val := by
  have heq : (Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l) = Finset.Ioi k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_Ioi]
    omega
  rw [heq]
  simp

/-- Sign of the derivative of a monic product at its `k`th strictly ordered
root. -/
private lemma finiteRootComplement_checkerboard_sign {m : ℕ}
    {d : Fin m → ℝ} (hd : StrictMono d) (k : Fin m) :
    0 < (-1 : ℝ) ^ (m - 1 - k.val) *
      (finiteRootComplement d k).eval (d k) := by
  classical
  have hsign := negOnePowFilter_mul_prod_pos
    (Finset.univ.erase k : Finset (Fin m)) (fun l => k < l)
    (fun l => d k - d l)
    (fun l _hl hkl => sub_neg.mpr (hd hkl))
    (fun l hl hnkl => by
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      exact sub_pos.mpr (hd (lt_of_le_of_ne (le_of_not_gt hnkl) hlk)))
  rw [card_filter_gt_erase_fin k] at hsign
  simpa only [finiteRootComplement, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hsign

/-- Public `CrossInterlacing` exposes the factor-data structure but keeps its
choice private.  Reconstruct the witness here so the Markov kernel can use
the actual leading scale without assuming it. -/
private theorem exists_markovGapDifferenceFactorData {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapDifferenceFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let D : ℝ[X] := gapDifferenceRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapDifferenceCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro q
      rw [Polynomial.dvd_iff_isRoot]
      exact gapDifferenceCombination_eval_rootPoint nodes g h hgh q
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).Monic
    exact monic_prod_of_monic _ _ fun q _hq => monic_X_sub_C (root q)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 1 := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).natDegree = n - 1
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hQdegree : Q.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      have hdegree := degree_gapDifferenceCombination_le nodes g h
      rw [Polynomial.degree_eq_natDegree hP] at hdegree
      exact_mod_cast hdegree
    omega
  obtain ⟨c, hcQ⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hc : c ≠ 0 := by
    intro hzero
    apply hQne
    rw [← hcQ, hzero, C_0]
  refine ⟨⟨c, hc, ?_⟩⟩
  calc
    gapDifferenceCombination nodes g h = P := rfl
    _ = D * Q := hQ
    _ = gapDifferenceRootProduct nodes g h hgh * C c := by
      rw [← hcQ]

private lemma negOnePow_add_eq_sub {a b : ℕ} (hab : a ≤ b) :
    (-1 : ℝ) ^ (a + b) = (-1 : ℝ) ^ (b - a) := by
  have heq : a + b = (b - a) + 2 * a := by omega
  rw [heq, pow_add, pow_mul]
  norm_num

@[simp]
private lemma sq_negOnePow (a : ℕ) : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
  rw [← pow_mul]
  have heq : a * 2 = 2 * a := by omega
  rw [heq, pow_mul]
  norm_num

/-- The source sum combination has the same checkerboard sign as the
derivative of the difference combination at every exhaustive difference
root. -/
private lemma gapSumCombination_eval_differenceRoot_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapSumCombination_eval_node nodes g h hgh]
    have houtside : (gapLeftIndex q).val ≤ g.val ∨
        h.val < (gapLeftIndex q).val := Or.inl (by simpa using hqg)
    rw [if_pos houtside,
      gapCoefficient_of_le g (gapLeftIndex q) (by simpa using hqg)]
    simp only [gapLeftIndex_val]
    have hparity : (-1 : ℝ) ^ (g.val + q.val) =
        (-1 : ℝ) ^ (g.val - q.val) := by
      simpa only [Nat.add_comm] using negOnePow_add_eq_sub hqg
    rw [hparity]
    nlinarith [sq_negOnePow (g.val - q.val)]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapSumCombination_eval_node nodes g h hgh]
      have houtside : (gapRightIndex q).val ≤ g.val ∨
          h.val < (gapRightIndex q).val := Or.inr (by simp; omega)
      have hgk : g.val < (gapRightIndex q).val := by simp; omega
      rw [if_pos houtside, gapCoefficient_of_lt g (gapRightIndex q) hgk]
      simp only [gapRightIndex_val]
      have hgq : g.val ≤ q.val := by omega
      have hexp : q.val + 1 - g.val - 1 = q.val - g.val := by omega
      rw [hexp]
      rw [negOnePow_add_eq_sub hgq]
      nlinarith [sq_negOnePow (q.val - g.val)]
    · have hgq : g < q := Fin.lt_def.mpr (by omega)
      have hqh : q < h := Fin.lt_def.mpr (by omega)
      have hmem := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      have hsign := gapSumCombination_sign_middleGap
        nodes g h q hgh hgq.le hqh hmem
      have hparity : (-1 : ℝ) ^ (g.val + q.val) =
          (-1 : ℝ) ^ (q.val - g.val) :=
        negOnePow_add_eq_sub hgq.le
      rwa [hparity]

private lemma card_filter_gt_fin {m : ℕ} (g : Fin m) :
    ((Finset.univ : Finset (Fin m)).filter (fun q => g < q)).card =
      m - 1 - g.val := by
  have heq : (Finset.univ : Finset (Fin m)).filter (fun q => g < q) =
      Finset.Ioi g := by
    ext q
    simp
  rw [heq]
  simp

private lemma negOnePow_two_complements_eq_add {m : ℕ}
    (g q : Fin m) :
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
      (-1 : ℝ) ^ (g.val + q.val) := by
  have heq : (m - 1 - g.val) + (m - 1 - q.val) +
      (g.val + q.val) = 2 * (m - 1) := by omega
  have hproduct :
      ((-1 : ℝ) ^ (m - 1 - g.val) *
        (-1 : ℝ) ^ (m - 1 - q.val)) *
          (-1 : ℝ) ^ (g.val + q.val) = 1 := by
    rw [← pow_add, ← pow_add, heq, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
        ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) * 1 := by ring
    _ = ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (((-1 : ℝ) ^ (g.val + q.val)) ^ 2) := by
          rw [sq_negOnePow]
    _ = ((((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (-1 : ℝ) ^ (g.val + q.val)) *
          (-1 : ℝ) ^ (g.val + q.val)) := by ring
    _ = (-1 : ℝ) ^ (g.val + q.val) := by rw [hproduct]; ring

/-- Sign of the scalar multiplying the exhaustive difference-root product,
anchored by the source value `D(x_{g+1}) = 2`. -/
private lemma gapDifferenceScale_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (n - 2 - g.val) * data.scale := by
  classical
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let y : ℝ := nodes.point (gapRightIndex g)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hMySign : 0 < (-1 : ℝ) ^ (n - 2 - g.val) * M.eval y := by
    have hsign := negOnePowFilter_mul_prod_pos
      (Finset.univ : Finset (Fin (n - 1))) (fun q => g < q)
      (fun q => y - root q)
      (fun q _hq hgq => by
        have hleft : y ≤ nodes.point (gapLeftIndex q) := by
          apply nodes.strictMono.monotone
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        have hroot : nodes.point (gapLeftIndex q) < root q := by
          simpa only [root] using left_lt_gapDifferenceRootPoint_of_lt
            nodes g h hgh q hgq
        exact sub_neg.mpr (hleft.trans_lt hroot))
      (fun q _hq hngq => by
        have hqg : q.val ≤ g.val := by omega
        have hroot : root q = nodes.point (gapLeftIndex q) := by
          simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
            nodes g h hgh q hqg
        change 0 < y - root q
        rw [hroot]
        exact sub_pos.mpr (nodes.strictMono (by
          apply Fin.lt_def.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega)))
    rw [card_filter_gt_fin g] at hsign
    simpa only [M, finiteRootProduct, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, root, y]
      using hsign
  have hDy : (gapDifferenceCombination nodes g h).eval y = 2 := by
    rw [gapDifferenceCombination_eval_node nodes g h hgh]
    have hinside : ¬((gapRightIndex g).val ≤ g.val ∨
        h.val < (gapRightIndex g).val) := by
      simp only [gapRightIndex_val]
      omega
    rw [if_neg hinside]
    simp
  have hMscale : M.eval y * data.scale = 2 := by
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C] at hDy
    exact hDy
  have hsquare := sq_negOnePow (n - 2 - g.val)
  by_contra hnot
  have hle : (-1 : ℝ) ^ (n - 2 - g.val) * data.scale ≤ 0 :=
    le_of_not_gt hnot
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hMySign.le hle
  have heq :
      ((-1 : ℝ) ^ (n - 2 - g.val) * M.eval y) *
          ((-1 : ℝ) ^ (n - 2 - g.val) * data.scale) =
        M.eval y * data.scale := by nlinarith
  rw [heq, hMscale] at hproduct
  norm_num at hproduct

private lemma gapDifference_derivative_eval_root_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let e : ℝ := (finiteRootComplement root q).eval (root q)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hderivative :
      (gapDifferenceCombination nodes g h).derivative.eval (root q) =
        e * data.scale := by
    rw [hfactor]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
      mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
    rw [finiteRootProduct_derivative_eval_root]
  have hscale := gapDifferenceScale_checkerboard nodes g h hgh data
  have hcomplement :
      0 < (-1 : ℝ) ^ (n - 2 - q.val) * e := by
    simpa only [e, root] using finiteRootComplement_checkerboard_sign
      (gapDifferenceRootPoint_strictMono nodes g h hgh) q
  have hparity := negOnePow_two_complements_eq_add
    (m := n - 1) g q
  rw [show n - 1 - 1 = n - 2 by omega] at hparity
  rw [hderivative, ← hparity]
  nlinarith [mul_pos hscale hcomplement]

private lemma gapDifference_sum_residue_pos {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  have hsum := gapSumCombination_eval_differenceRoot_checkerboard
    nodes g h q hgh
  have hderiv := gapDifference_derivative_eval_root_checkerboard
    nodes g h q hgh data
  have hsquare := sq_negOnePow (g.val + q.val)
  nlinarith [mul_pos hsum hderiv]

/-- The strict Wronskian form of the finite Markov theorem for the two
source combinations.  In particular it covers both possible degree cases
for `S`: the interpolation remainder removes a possible same-degree
exterior root automatically. -/
theorem gapCombination_wronskian_neg {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x < 0 := by
  let data := Classical.choice
    (exists_markovGapDifferenceFactorData nodes g h hgh)
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  have hm : 0 < n - 1 := by
    have := g.isLt
    omega
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hmarkov := finite_markov_wronskian_neg hm root
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
    data.scale data.scale_ne_zero (gapSumCombination nodes g h)
    (natDegree_gapSumCombination_le_sub_one nodes g h hgh)
    (fun q => by
      have hr := gapDifference_sum_residue_pos nodes g h q hgh data
      rw [hfactor] at hr
      simpa only [root] using hr) x
  rw [← hfactor] at hmarkov
  exact hmarkov

private lemma gapCombination_wronskian_eq_gapPolynomials {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x =
      2 * gapPairParity g h *
        ((gapPolynomial nodes g).eval x *
            (gapPolynomial nodes h).derivative.eval x -
          (gapPolynomial nodes g).derivative.eval x *
            (gapPolynomial nodes h).eval x) := by
  simp only [gapDifferenceCombination, gapSumCombination,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

/-- Source Lemma 2 in the exact oriented form required by the quotient sign
table.  The proof specializes the checked negative Wronskian at the two
ordered own-gap critical points. -/
theorem crossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    CrossDerivativeCriticalSignTable nodes := by
  constructor
  · intro i j hij
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes i j hij x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : 0 < (gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : 0 < gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x := by
      rcases mul_pos_iff.mp hprod with hgood | hbad
      · exact hgood.1
      · exact (not_lt_of_ge hjpos.le hbad.2).elim
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity i j := by
      rw [gapPairParity]
      exact negOnePow_add_eq_sub hij.le
    rwa [hparity]
  · intro i j hji
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes j i hji x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : (gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x < 0 := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x < 0 := by
      rcases mul_neg_iff.mp hprod with hgood | hbad
      · exact (not_lt_of_ge hjpos.le hgood.2).elim
      · exact hbad.1
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity j i := by
      rw [gapPairParity, Nat.add_comm]
      exact negOnePow_add_eq_sub hji.le
    rwa [hparity]

/-- Complete general quotient sign table, including the diagonal supplied
by strict own-gap concavity. -/
theorem derivativeQuotientSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) :
    DerivativeQuotientSignTable nodes :=
  derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable nodes hn
    (crossDerivativeCriticalSignTable nodes (by omega))

/-- In the three-node case the removed-critical-factor quotient is constant. -/
lemma natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) :
    (gapDerivativeQuotient nodes i).natDegree = 0 := by
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  have hdegree := natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes i
  omega

/-- The three-node quotient has the same value at every point. -/
lemma gapDerivativeQuotient_eval_eq_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x y : ℝ) :
    (gapDerivativeQuotient nodes i).eval x =
      (gapDerivativeQuotient nodes i).eval y := by
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp
    (natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes nodes i)
  rw [← hc]
  simp

/-- For three nodes the constant critical quotient is strictly negative.
This is the complete low-dimensional (`d=1`) sign table. -/
lemma gapDerivativeQuotient_eval_neg_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x : ℝ) :
    (gapDerivativeQuotient nodes i).eval x < 0 := by
  let p : ℝ[X] := gapPolynomial nodes i
  let a : ℝ := nodes.point (gapLeftIndex i)
  let τ : ℝ := gapArgmax nodes i
  have haτ : a < τ := (gapArgmax_mem_openGap nodes (by norm_num) i).1
  have hpa : p.eval a = 1 := by
    simpa only [p, a] using gapPolynomial_eval_left nodes i
  have hpτ : 1 < p.eval τ := by
    exact one_lt_eval_gapPolynomial_of_mem_openGap nodes (by norm_num) i
      (gapArgmax_mem_openGap nodes (by norm_num) i)
  obtain ⟨z, hz, hderiv⟩ := exists_deriv_eq_slope p.eval haτ
    p.continuous.continuousOn p.differentiable.differentiableOn
  have hslope : 0 < (p.eval τ - p.eval a) / (τ - a) :=
    div_pos (by rw [hpa]; linarith) (sub_pos.mpr haτ)
  have hdpz : 0 < p.derivative.eval z := by
    have hpderiv : deriv p.eval z = p.derivative.eval z := by
      simp only [Polynomial.deriv]
    rw [← hpderiv, hderiv]
    exact hslope
  have hfactor := congrArg (Polynomial.eval z)
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes (by norm_num) i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  have hzτ : z - τ < 0 := sub_neg.mpr hz.2
  have hqz : (gapDerivativeQuotient nodes i).eval z < 0 := by
    have hmul : 0 < (z - τ) * (gapDerivativeQuotient nodes i).eval z := by
      rwa [hfactor]
    rcases mul_pos_iff.mp hmul with hbad | hgood
    · exact (not_lt_of_ge hbad.1.le hzτ).elim
    · exact hgood.2
  rw [gapDerivativeQuotient_eval_eq_of_three_nodes nodes i x z]
  exact hqz

/-- Complete quotient sign table in the three-node (`d=1`) case. -/
theorem derivativeQuotientSignTable_three_nodes (nodes : OrderedNodes 3) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · intro i
    exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes i _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals
      exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes _ _

/-- Uniform nondegenerate sign-table API.  The proof keeps the constant
`n = 3` quotient separate from the strict-concavity `n ≥ 4` branch. -/
theorem derivativeQuotientSignTable_of_three_le {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    DerivativeQuotientSignTable nodes := by
  by_cases heq : n = 3
  · subst n
    exact derivativeQuotientSignTable_three_nodes nodes
  · exact derivativeQuotientSignTable nodes (by omega)

/-! ### The genuine two-node exception -/

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Simplex.lean` -/

/-!
# The endpoint-array simplex

This file supplies the global coordinate identification deliberately omitted
from `NodeSpace`.  An endpoint array is reconstructed from its `d` interior
coordinates, and the induced topology makes this reconstruction a
homeomorphism with the open ordered simplex.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Every full node index is the left endpoint, the right endpoint, or one
of the interior indices.  The statement remains valid when `d = 0`. -/
lemma endpoint_index_cases {d : ℕ} (k : Fin (d + 2)) :
    k = endpointLeftIndex d ∨ k = endpointRightIndex d ∨
      ∃ i : Fin d, k = interiorNodeIndex i := by
  by_cases hk0 : k.val = 0
  · exact Or.inl (Fin.ext hk0)
  by_cases hkLast : k.val = d + 1
  · exact Or.inr (Or.inl (Fin.ext hkLast))
  right
  right
  let i : Fin d := ⟨k.val - 1, by omega⟩
  exact ⟨i, Fin.ext (by simp [i]; omega)⟩

/-- Full node coordinate obtained by adjoining fixed endpoints to an
interior vector. -/
def endpointPoint {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  if hkLeft : k = endpointLeftIndex d then A
  else if hkRight : k = endpointRightIndex d then B
  else u ⟨k.val - 1, by
    have hkPos : 0 < k.val := by
      by_contra hk
      have hk0 : k.val = 0 := Nat.eq_zero_of_not_pos hk
      exact hkLeft (Fin.ext hk0)
    have hkLt : k.val < d + 1 := by
      have := k.isLt
      have hkNe : k.val ≠ d + 1 := by
        intro hk
        exact hkRight (Fin.ext hk)
      omega
    omega⟩

@[simp]
lemma endpointPoint_left {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointLeftIndex d) = A := by
  simp [endpointPoint]

@[simp]
lemma endpointPoint_right {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointRightIndex d) = B := by
  have hne : endpointRightIndex d ≠ endpointLeftIndex d := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [endpointPoint, hne]

@[simp]
lemma endpointPoint_interior {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (i : Fin d) :
    endpointPoint A B u (interiorNodeIndex i) = u i := by
  have hleft : interiorNodeIndex i ≠ endpointLeftIndex d :=
    (endpointLeftIndex_lt_interior i).ne'
  have hright : interiorNodeIndex i ≠ endpointRightIndex d :=
    (interior_lt_endpointRightIndex i).ne
  simp only [endpointPoint, dif_neg hleft, dif_neg hright]
  congr 1

/-- Strict ordering of the adjoined full coordinate vector. -/
lemma endpointPoint_strictMono {d : ℕ} {A B : ℝ} {u : Fin d → ℝ}
    (hAB : A < B) (hu : u ∈ endpointNodeSpace d A B) :
    StrictMono (endpointPoint A B u) := by
  intro i j hij
  rcases endpoint_index_cases i with hi | hi | ⟨r, hi⟩
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      exact (lt_irrefl _ hij).elim
    · subst j
      simpa using hAB
    · subst j
      simpa using hu.1 s
  · subst i
    have : ¬endpointRightIndex d < j := by
      simp only [Fin.lt_def, endpointRightIndex_val]
      omega
    exact (this hij).elim
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      have : ¬interiorNodeIndex r < endpointLeftIndex d := by simp [Fin.lt_def]
      exact (this hij).elim
    · subst j
      simpa using hu.2.2 r
    · subst j
      have hrs : r < s := by
        change r.val + 1 < s.val + 1 at hij
        exact Fin.lt_def.mpr (Nat.add_lt_add_iff_right.mp hij)
      simpa using hu.2.1 hrs

/-- Every coordinate of the adjoined full vector remains in `[-1,1]`. -/
lemma endpointPoint_mem_Icc {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) {u : Fin d → ℝ}
    (hu : u ∈ endpointNodeSpace d A B) (k : Fin (d + 2)) :
    endpointPoint A B u k ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [endpointPoint_left]
    exact ⟨hAB.1, le_trans hAB.2.1.le hAB.2.2⟩
  · subst k
    rw [endpointPoint_right]
    exact ⟨hAB.1.trans hAB.2.1.le, hAB.2.2⟩
  · subst k
    rw [endpointPoint_interior]
    exact ⟨hAB.1.trans (hu.1 i).le, (hu.2.2 i).le.trans hAB.2.2⟩

/-- Reconstruct an endpoint array from a point of the open coordinate
simplex. -/
def endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    EndpointArray d A B where
  point := endpointPoint A B u.1
  injective := (endpointPoint_strictMono hAB.2.1 u.2).injective
  mem_Icc := endpointPoint_mem_Icc hAB u.2
  strictMono := endpointPoint_strictMono hAB.2.1 u.2
  left_endpoint := endpointPoint_left A B u.1
  right_endpoint := endpointPoint_right A B u.1

@[simp]
lemma endpointArrayOfInterior_point {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    (endpointArrayOfInterior hAB u).point k = endpointPoint A B u.1 k :=
  rfl

@[simp]
lemma interior_endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (endpointArrayOfInterior hAB u).interior = u.1 := by
  funext i
  exact endpointPoint_interior A B u.1 i

/-- Endpoint arrays are extensional in their full point function. -/
lemma EndpointArray.ext {d : ℕ} {A B : ℝ} {x y : EndpointArray d A B}
    (h : ∀ k, x.point k = y.point k) : x = y := by
  cases x with
  | mk x hxLeft hxRight => cases x with
    | mk x hxMono =>
      cases y with
      | mk y hyLeft hyRight => cases y with
        | mk y hyMono =>
            simp only [EndpointArray.mk.injEq, OrderedNodes.mk.injEq,
              NodeFamily.ext_iff]
            exact funext h

/-- Interior coordinates determine the endpoint array. -/
lemma EndpointArray.ext_interior {d : ℕ} {A B : ℝ}
    {x y : EndpointArray d A B} (h : x.interior = y.interior) : x = y := by
  apply EndpointArray.ext
  intro k
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [x.left_endpoint, y.left_endpoint]
  · subst k
    rw [x.right_endpoint, y.right_endpoint]
  · subst k
    exact congrFun h i

@[simp]
lemma endpointArrayOfInterior_interior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfInterior hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ = nodes := by
  apply EndpointArray.ext_interior
  exact interior_endpointArrayOfInterior hAB _

/-- Exact equivalence between endpoint arrays and their interior-coordinate
open simplex. -/
def endpointArrayEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toFun nodes := ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  invFun := endpointArrayOfInterior hAB
  left_inv := endpointArrayOfInterior_interior hAB
  right_inv u := Subtype.ext (interior_endpointArrayOfInterior hAB u)

/-- The induced topology on endpoint arrays makes the coordinate equivalence
a genuine homeomorphism. -/
def endpointArrayHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toEquiv := endpointArrayEquiv hAB
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_induced_dom _
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦
      (endpointArrayOfInterior hAB u).interior)
    convert (continuous_subtype_val : Continuous
      (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦ u.1)) using 1
    funext u
    exact interior_endpointArrayOfInterior hAB u

/-! ## Positive spacings and log-ratio coordinates -/

/-- Positive `(d+1)`-tuples with prescribed total length. -/
def positiveSpacingSimplex (d : ℕ) (L : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {s | (∀ g, 0 < s g) ∧ ∑ g, s g = L}

/-- Softmax denominator with the last spacing used as reference. -/
def logRatioDenominator {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  1 + ∑ i, Real.exp (z i)

lemma logRatioDenominator_pos {d : ℕ} (z : Fin d → ℝ) :
    0 < logRatioDenominator z := by
  unfold logRatioDenominator
  positivity

/-- Inverse log-ratio spacings.  The final coordinate is the reference
weight `1`; the first `d` weights are `exp (z i)`. -/
def softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  fun g ↦ Fin.lastCases
    (L / logRatioDenominator z)
    (fun i ↦ L * Real.exp (z i) / logRatioDenominator z) g

@[simp]
lemma softmaxSpacing_last {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    softmaxSpacing L z (Fin.last d) = L / logRatioDenominator z := by
  simp [softmaxSpacing]

@[simp]
lemma softmaxSpacing_castSucc {d : ℕ} (L : ℝ) (z : Fin d → ℝ)
    (i : Fin d) :
    softmaxSpacing L z i.castSucc =
      L * Real.exp (z i) / logRatioDenominator z := by
  simp [softmaxSpacing]

lemma softmaxSpacing_pos {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) (g : Fin (d + 1)) :
    0 < softmaxSpacing L z g := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last]
    exact div_pos hL (logRatioDenominator_pos z)
  · rw [softmaxSpacing_castSucc]
    exact div_pos (mul_pos hL (Real.exp_pos _)) (logRatioDenominator_pos z)

lemma sum_softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    ∑ g, softmaxSpacing L z g = L := by
  rw [Fin.sum_univ_castSucc]
  simp only [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  unfold logRatioDenominator at *
  field_simp
  ring

lemma softmaxSpacing_mem_positiveSpacingSimplex {d : ℕ} {L : ℝ}
    (hL : 0 < L) (z : Fin d → ℝ) :
    softmaxSpacing L z ∈ positiveSpacingSimplex d L :=
  ⟨softmaxSpacing_pos hL z, sum_softmaxSpacing L z⟩

/-- Logarithms of the first `d` spacings relative to the final spacing. -/
def spacingLogRatio {d : ℕ} (s : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i ↦ Real.log (s i.castSucc / s (Fin.last d))

@[simp]
lemma spacingLogRatio_softmaxSpacing {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) :
    spacingLogRatio (softmaxSpacing L z) = z := by
  funext i
  unfold spacingLogRatio
  rw [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hL0 : L ≠ 0 := hL.ne'
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  have hratio :
      (L * Real.exp (z i) / logRatioDenominator z) /
          (L / logRatioDenominator z) = Real.exp (z i) := by
    field_simp
  rw [hratio, Real.log_exp]

lemma exp_spacingLogRatio {d : ℕ} {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) (i : Fin d) :
    Real.exp (spacingLogRatio s i) = s i.castSucc / s (Fin.last d) := by
  unfold spacingLogRatio
  exact Real.exp_log (div_pos (hs _) (hs _))

lemma logRatioDenominator_spacingLogRatio {d : ℕ}
    {s : Fin (d + 1) → ℝ} (hs : ∀ g, 0 < s g) :
    logRatioDenominator (spacingLogRatio s) =
      (∑ g, s g) / s (Fin.last d) := by
  unfold logRatioDenominator
  simp_rw [exp_spacingLogRatio hs]
  rw [Fin.sum_univ_castSucc]
  have href : s (Fin.last d) ≠ 0 := (hs _).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  field_simp
  ring

@[simp]
lemma softmaxSpacing_spacingLogRatio {d : ℕ} {L : ℝ} (hL : 0 < L)
    (s : Fin (d + 1) → ℝ) (hs : ∀ g, 0 < s g)
    (hsum : ∑ g, s g = L) :
    softmaxSpacing L (spacingLogRatio s) = s := by
  funext g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp
  · rw [softmaxSpacing_castSucc, exp_spacingLogRatio hs,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp

/-- Positive normalized spacings are exactly log-ratio coordinates in
`Fin d → ℝ`. -/
def positiveSpacingLogRatioEquiv {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toFun z := ⟨softmaxSpacing L z, softmaxSpacing_mem_positiveSpacingSimplex hL z⟩
  invFun s := spacingLogRatio s.1
  left_inv := spacingLogRatio_softmaxSpacing hL
  right_inv s := Subtype.ext
    (softmaxSpacing_spacingLogRatio hL s.1 s.2.1 s.2.2)

lemma continuous_logRatioDenominator {d : ℕ} :
    Continuous (logRatioDenominator : (Fin d → ℝ) → ℝ) := by
  unfold logRatioDenominator
  exact continuous_const.add (continuous_finset_sum Finset.univ fun i _ ↦
    (continuous_apply i).rexp)

lemma continuous_softmaxSpacing {d : ℕ} (L : ℝ) :
    Continuous (softmaxSpacing L : (Fin d → ℝ) → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · simpa only [softmaxSpacing_last] using
      continuous_const.div continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')
  · simpa only [softmaxSpacing_castSucc] using
      (continuous_const.mul (continuous_apply i).rexp).div
        continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')

lemma continuous_spacingLogRatio_positive {d : ℕ} {L : ℝ} :
    Continuous (fun s :
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} ↦
        spacingLogRatio s.1) := by
  apply continuous_pi
  intro i
  let X := {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L}
  have hnum : Continuous (fun s : X ↦ s.1 i.castSucc) :=
    (continuous_apply i.castSucc).comp continuous_subtype_val
  have href : Continuous (fun s : X ↦ s.1 (Fin.last d)) :=
    (continuous_apply (Fin.last d)).comp continuous_subtype_val
  have hdiv : Continuous (fun s : X ↦ s.1 i.castSucc / s.1 (Fin.last d)) :=
    hnum.div href (fun s ↦ (s.2.1 _).ne')
  exact hdiv.log (fun s ↦ div_ne_zero (s.2.1 _).ne' (s.2.1 _).ne')

/-- Homeomorphism from Euclidean log-ratio coordinates to the positive
normalized spacing simplex. -/
def positiveSpacingLogRatioHomeomorph {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toEquiv := positiveSpacingLogRatioEquiv hL
  continuous_toFun := Continuous.subtype_mk (continuous_softmaxSpacing L) _
  continuous_invFun := continuous_spacingLogRatio_positive

/-! ## Endpoint arrays as normalized positive spacings -/

/-- Consecutive positive spacings of an endpoint array. -/
def endpointSpacing {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Fin (d + 1) → ℝ :=
  fun g ↦ nodes.point (gapRightIndex g) - nodes.point (gapLeftIndex g)

lemma endpointSpacing_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    0 < endpointSpacing nodes g := by
  exact sub_pos.mpr (nodes.point_lt
    (gapLeftIndex_lt_rightIndex (n := d + 2) g))

lemma sum_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    ∑ g, endpointSpacing nodes g = B - A := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f (d + 1)
  rw [show f (d + 1) = nodes.point (endpointRightIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointRightIndex],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  calc
    (∑ i ∈ Finset.range (d + 1),
        if h : i < d + 1 then endpointSpacing nodes ⟨i, h⟩ else 0) =
        ∑ i ∈ Finset.range (d + 1), (f (i + 1) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < d + 1 := Finset.mem_range.mp hi
      rw [dif_pos hi']
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi'.le).symm
    _ = nodes.point (endpointRightIndex d) -
        nodes.point (endpointLeftIndex d) := htel
    _ = B - A := by rw [nodes.right_endpoint, nodes.left_endpoint]

lemma endpointSpacing_mem_positiveSpacingSimplex {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ positiveSpacingSimplex d (B - A) :=
  ⟨endpointSpacing_pos nodes, sum_endpointSpacing nodes⟩

/-- Cumulative full-node coordinate associated to a spacing vector. -/
def spacingPoint {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  A + ∑ i ∈ Finset.range k.val,
    if hi : i < d + 1 then s ⟨i, hi⟩ else 0

@[simp]
lemma spacingPoint_left {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ) :
    spacingPoint A s (endpointLeftIndex d) = A := by
  simp [spacingPoint, endpointLeftIndex]

lemma spacingPoint_strictMono {d : ℕ} (A : ℝ) {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) :
    StrictMono (spacingPoint A s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change A + ∑ r ∈ Finset.range i.val,
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
    A + ∑ r ∈ Finset.range (i.val + 1),
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)
  rw [Finset.sum_range_succ, dif_pos i.isLt]
  calc
    A + ∑ r ∈ Finset.range i.val,
        (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
        (A + ∑ r ∈ Finset.range i.val,
          (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)) + s i :=
      lt_add_of_pos_right _ (hs i)
    _ = A + ((∑ r ∈ Finset.range i.val,
          if hr : r < d + 1 then s ⟨r, hr⟩ else 0) + s i) := by ring

@[simp]
lemma spacingPoint_right {d : ℕ} {A B : ℝ}
    {s : Fin (d + 1) → ℝ} (hsum : ∑ g, s g = B - A) :
    spacingPoint A s (endpointRightIndex d) = B := by
  unfold spacingPoint
  simp only [endpointRightIndex_val]
  rw [← Finset.sum_fin_eq_sum_range, hsum]
  ring

/-- Construct an endpoint array from positive spacings with total `B-A`. -/
def endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    EndpointArray d A B where
  point := spacingPoint A s.1
  injective := (spacingPoint_strictMono A s.2.1).injective
  mem_Icc k := by
    have hmono := (spacingPoint_strictMono A s.2.1).monotone
    constructor
    · calc
        (-1 : ℝ) ≤ A := hAB.1
        _ = spacingPoint A s.1 (endpointLeftIndex d) :=
          (spacingPoint_left A s.1).symm
        _ ≤ spacingPoint A s.1 k :=
          hmono (by simp [Fin.le_iff_val_le_val])
    · calc
        spacingPoint A s.1 k ≤ spacingPoint A s.1 (endpointRightIndex d) :=
          hmono (by
            apply Fin.le_iff_val_le_val.mpr
            simp only [endpointRightIndex_val]
            omega)
        _ = B := spacingPoint_right s.2.2
        _ ≤ 1 := hAB.2.2
  strictMono := spacingPoint_strictMono A s.2.1
  left_endpoint := spacingPoint_left A s.1
  right_endpoint := spacingPoint_right s.2.2

@[simp]
lemma endpointSpacing_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    endpointSpacing (endpointArrayOfSpacings hAB s) = s.1 := by
  funext g
  unfold endpointSpacing endpointArrayOfSpacings spacingPoint
  simp only [gapRightIndex_val, gapLeftIndex_val]
  rw [Finset.sum_range_succ, dif_pos g.isLt]
  ring

lemma spacingPoint_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    spacingPoint A (endpointSpacing nodes) k = nodes.point k := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  have hk : k.val ≤ d + 1 := by omega
  have htel := Finset.sum_range_sub f k.val
  rw [show f k.val = nodes.point k by
      apply congrArg nodes.point
      apply Fin.ext
      simp [Nat.min_eq_left hk],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  unfold spacingPoint
  calc
    A + ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) =
      nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) := by
      exact congrArg (fun x ↦ x + ∑ i ∈ Finset.range k.val,
        if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0)
          nodes.left_endpoint.symm
    _ = nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val, (f (i + 1) - f i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hiMem
      have hiK : i < k.val := Finset.mem_range.mp hiMem
      have hi : i < d + 1 := lt_of_lt_of_le hiK hk
      rw [dif_pos hi]
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi.le).symm
    _ = nodes.point k := by rw [htel]; ring

@[simp]
lemma endpointArrayOfSpacings_endpointSpacing {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfSpacings hAB
      ⟨endpointSpacing nodes, endpointSpacing_mem_positiveSpacingSimplex nodes⟩ = nodes := by
  apply EndpointArray.ext
  exact spacingPoint_endpointSpacing nodes

/-- Exact equivalence between endpoint arrays and positive normalized
spacings. -/
def endpointArraySpacingEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toFun nodes := ⟨endpointSpacing nodes,
    endpointSpacing_mem_positiveSpacingSimplex nodes⟩
  invFun := endpointArrayOfSpacings hAB
  left_inv := endpointArrayOfSpacings_endpointSpacing hAB
  right_inv s := Subtype.ext (endpointSpacing_endpointArrayOfSpacings hAB s)

lemma continuous_endpointArray_point {d : ℕ} {A B : ℝ}
    (k : Fin (d + 2)) :
    Continuous (fun nodes : EndpointArray d A B ↦ nodes.point k) := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ A)) using 1
    funext nodes
    exact nodes.left_endpoint
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ B)) using 1
    funext nodes
    exact nodes.right_endpoint
  · subst k
    exact (continuous_apply i).comp
      (continuous_induced_dom : Continuous
        (fun nodes : EndpointArray d A B ↦ nodes.interior))

lemma continuous_endpointSpacing {d : ℕ} {A B : ℝ} :
    Continuous (endpointSpacing : EndpointArray d A B → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  exact (continuous_endpointArray_point (gapRightIndex g)).sub
    (continuous_endpointArray_point (gapLeftIndex g))

lemma continuous_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    Continuous (endpointArrayOfSpacings (d := d) hAB) := by
  rw [continuous_induced_rng]
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      (endpointArrayOfSpacings hAB s).interior)
  apply continuous_pi
  intro i
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      spacingPoint A s.1 (interiorNodeIndex i))
  unfold spacingPoint
  apply continuous_const.add
  apply continuous_finset_sum
  intro r hr
  split_ifs with h
  · let k : Fin (d + 1) := ⟨r, h⟩
    have hc : Continuous (fun s :
        {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
          s.1 k) :=
      (continuous_apply k).comp continuous_subtype_val
    exact hc
  · exact continuous_const

/-- Endpoint arrays are homeomorphic to positive normalized spacings. -/
def endpointArraySpacingHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toEquiv := endpointArraySpacingEquiv hAB
  continuous_toFun := Continuous.subtype_mk continuous_endpointSpacing _
  continuous_invFun := continuous_endpointArrayOfSpacings hAB

/-- Source-required global Euclidean homeomorphism, obtained by positive
spacings followed by log ratios against the final spacing. -/
def endpointArrayLogRatioHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
  (endpointArraySpacingHomeomorph hAB).trans
    (positiveSpacingLogRatioHomeomorph (sub_pos.mpr hAB.2.1)).symm

/-- Consequently, any two zero-dimensional endpoint arrays with the same
fixed endpoints are equal. -/
lemma endpointArray_zero_unique {A B : ℝ} (x y : EndpointArray 0 A B) :
    x = y := by
  apply EndpointArray.ext_interior
  exact Subsingleton.elim _ _

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Jacobian.lean` -/

/-!
# The endpoint-coordinate Jacobian

This file isolates the analytic and algebraic parts of the Jacobian argument
in de Boor--Pinkus.  The interpolation polynomial is first written on the
ambient space of interior coordinates.  The formula remains meaningful away
from the ordered simplex (it merely uses inverses of node differences), while
on the simplex it is definitionally the project's `gapPolynomial`.

The source's envelope calculation says that, at the unique critical point
`τ_g`, moving an interior node `t_j` changes the gap height by

`-F'_g(t_j) * l_j(τ_g)`.

The factorization `F'_g = (X - τ_g) Q_g` then rewrites this as a row factor,
the evaluation `Q_g(t_j)`, and a column factor.  Consequently every maximal
minor of the height Jacobian is the corresponding minor of the quotient
evaluation matrix times explicit nonzero diagonal factors.  Those algebraic
reductions are unconditional below.

The local implicit-function/envelope mechanism is also packaged without a
postulate: its hypotheses are ordinary Mathlib derivative judgments.  Thus a
later analytic proof can discharge exactly the two coordinate derivative
calculations without changing the downstream determinant argument.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Polynomial
open scoped BigOperators _root_.Topology

noncomputable section

/-! ## The interpolation polynomial in ambient interior coordinates -/

/-- The `k`th cardinal polynomial after adjoining the fixed endpoints `A,B`
to an arbitrary ambient interior vector `u`. -/
def coordinateLagrangePolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ[X] :=
  ∏ i ∈ Finset.univ.erase k,
    (X - C (endpointPoint A B u i)) *
      C (endpointPoint A B u k - endpointPoint A B u i)⁻¹

/-- The signed gap polynomial as a rational-polynomial expression in the
ambient interior coordinates. -/
def coordinateGapPolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) : ℝ[X] :=
  ∑ k : Fin (d + 2),
    C (gapCoefficient g k) * coordinateLagrangePolynomial A B u k

/-- Evaluation of the coordinate gap polynomial. -/
def coordinateGapValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).eval x

/-- The critical equation `F'_g(x)=0`, expressed in the same coordinates. -/
def coordinateCriticalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).derivative.eval x

lemma coordinateLagrangePolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    coordinateLagrangePolynomial A B u.1 k =
      lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily k := by
  rw [lagrangeBasis_eq_product]
  rfl

/-- On the ordered simplex the ambient coordinate formula is exactly the
committed signed gap polynomial, not merely an extension with the same nodal
values. -/
lemma coordinateGapPolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapPolynomial A B u.1 g =
      gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g := by
  classical
  simp only [coordinateGapPolynomial, gapPolynomial, Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coordinateLagrangePolynomial_eq hAB u]
  rfl

lemma coordinateGapValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateGapValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).eval x := by
  rw [coordinateGapValue, coordinateGapPolynomial_eq hAB u]

lemma coordinateCriticalValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval x := by
  rw [coordinateCriticalValue, coordinateGapPolynomial_eq hAB u]

/-- The gap height in the simplex chart. -/
def coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapHeight (endpointArrayOfInterior hAB u).toOrderedNodes g

/-- The selected unique critical point in the simplex chart. -/
def coordinateGapArgmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapArgmax (endpointArrayOfInterior hAB u).toOrderedNodes g

lemma coordinateGapHeight_eq_value_at_argmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapHeight hAB u g =
      coordinateGapValue A B u.1 g (coordinateGapArgmax hAB u g) := by
  rw [coordinateGapHeight, coordinateGapArgmax, coordinateGapValue_eq hAB u]
  exact gapHeight_eq_eval_gapArgmax _ _

/-! ## The source factorization of the height differential -/

/-- Product `ω_u(x)=∏_k (x-t_k)` of all endpoint-adjoined node factors,
written as a value because only its values enter the Jacobian. -/
def coordinateNodalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) (x : ℝ) : ℝ :=
  ∏ k : Fin (d + 2), (x - endpointPoint A B u k)

/-- Barycentric denominator `∏_{k≠j}(t_j-t_k)` at an interior node. -/
def coordinateBasisDenominator {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (j : Fin d) : ℝ :=
  ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
    (endpointPoint A B u (interiorNodeIndex j) - endpointPoint A B u k)

lemma coordinateNodalValue_eq_mul_erase {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (x : ℝ) :
    coordinateNodalValue A B u x =
      (x - endpointPoint A B u (interiorNodeIndex j)) *
        ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u k) := by
  classical
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 2)))
    (fun k => x - endpointPoint A B u k) (Finset.mem_univ _)).symm

lemma lagrangeFundamental_interior_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (x : ℝ) :
    lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
        (interiorNodeIndex j) x =
      (∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u.1 k)) *
        (coordinateBasisDenominator A B u.1 j)⁻¹ := by
  classical
  rw [lagrangeFundamental]
  simp only [endpointArrayOfInterior_point, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rfl

/-- The row factors in the source Jacobian reduction. -/
def gapJacobianRowFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  coordinateNodalValue A B nodes.interior (gapArgmax nodes.toOrderedNodes g)

/-- The column factors in the source Jacobian reduction. -/
def gapJacobianColumnFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) : ℝ :=
  (coordinateBasisDenominator A B nodes.interior j)⁻¹

/-- The quotient-evaluation matrix singled out in source Lemma 2.  It has
one row for every gap and one column for every moving interior node. -/
def gapQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => (gapDerivativeQuotient nodes.toOrderedNodes g).eval
    (nodes.point (interiorNodeIndex j))

/-- The factored matrix predicted for the differential of all gap heights. -/
def gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => gapJacobianRowFactor nodes g *
    gapQuotientEvaluationMatrix nodes g j * gapJacobianColumnFactor nodes j

lemma gapPolynomial_derivative_eval_interior_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    (gapPolynomial nodes.toOrderedNodes g).derivative.eval
        (nodes.point (interiorNodeIndex j)) =
      (nodes.point (interiorNodeIndex j) - gapArgmax nodes.toOrderedNodes g) *
        (gapDerivativeQuotient nodes.toOrderedNodes g).eval
          (nodes.point (interiorNodeIndex j)) := by
  have h := congrArg (Polynomial.eval (nodes.point (interiorNodeIndex j)))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes.toOrderedNodes
      (by have := j.isLt; omega) g)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using h.symm

/-- Entrywise envelope formula after removing the critical factor.  This is
the algebraic heart of the Jacobian calculation; it does not assume that the
height map has already been differentiated. -/
lemma gapHeightJacobianModel_apply_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    gapHeightJacobianModel nodes g j =
      -(gapPolynomial nodes.toOrderedNodes g).derivative.eval
          (nodes.point (interiorNodeIndex j)) *
        lagrangeFundamental nodes.toNodeFamily (interiorNodeIndex j)
          (gapArgmax nodes.toOrderedNodes g) := by
  let hAB := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have hnodes : endpointArrayOfInterior hAB u = nodes :=
    endpointArrayOfInterior_interior hAB nodes
  have hnodal := coordinateNodalValue_eq_mul_erase A B nodes.interior j
    (gapArgmax nodes.toOrderedNodes g)
  have hfund := lagrangeFundamental_interior_eq hAB u j
    (gapArgmax nodes.toOrderedNodes g)
  dsimp [u] at hfund
  rw [hnodes] at hfund
  rw [gapHeightJacobianModel, gapJacobianRowFactor,
    gapQuotientEvaluationMatrix, gapJacobianColumnFactor,
    gapPolynomial_derivative_eval_interior_eq, hfund, hnodal]
  simp only [endpointPoint_interior, EndpointArray.interior_apply]
  ring

/-! ## Maximal-minor reduction -/

/-- The maximal minor obtained by deleting row `omitted`. -/
def deletedRowMinor {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (omitted : Fin (d + 1)) : ℝ :=
  (M.submatrix omitted.succAbove id).det

/-- Every maximal height-Jacobian minor is the corresponding quotient-
evaluation minor times the explicit row and column products. -/
theorem deletedRowMinor_gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted =
      (∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
          ∏ j : Fin d, gapJacobianColumnFactor nodes j := by
  let R : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i => gapJacobianRowFactor nodes (omitted.succAbove i))
  let Q : Matrix (Fin d) (Fin d) ℝ :=
    (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id
  let C : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (gapJacobianColumnFactor nodes)
  have hmatrix :
      (gapHeightJacobianModel nodes).submatrix omitted.succAbove id = R * Q * C := by
    ext i j
    simp [R, Q, C, gapHeightJacobianModel, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  rw [deletedRowMinor, hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [R, Q, C, deletedRowMinor]

/-! ## The zero-dimensional/two-node exception -/

lemma coordinateCriticalValue_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B})
    (g : Fin 1) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x = 0 := by
  rw [coordinateCriticalValue_eq hAB u,
    gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp

lemma coordinateGapHeight_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B}) (g : Fin 1) :
    coordinateGapHeight hAB u g = 1 := by
  rw [coordinateGapHeight, gapHeight_eq_eval_gapArgmax,
    gapPolynomial_eq_one_of_two_nodes]
  simp

lemma gapHeightJacobianModel_zero_dim {A B : ℝ}
    (nodes : EndpointArray 0 A B) :
    gapHeightJacobianModel nodes = (0 : Matrix (Fin 1) (Fin 0) ℝ) := by
  ext g j
  exact Fin.elim0 j

lemma deletedRowMinor_zero_dim {A B : ℝ} (nodes : EndpointArray 0 A B)
    (omitted : Fin 1) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted = 1 := by
  rw [gapHeightJacobianModel_zero_dim]
  simp [deletedRowMinor]

/-! ## Checked implicit-function and envelope infrastructure

The analytic calculation is stated at the level at which Mathlib's Fréchet
calculus consumes it. `GapCoordinateDerivativesAt` records the two concrete
rational derivative computations for `coordinateGapPolynomial`. Everything
from that record through the implicit-function theorem, envelope cancellation,
and Jacobian entry formula is checked here; the final section constructs the
record directly from finite product differentiation and interpolation.
-/

/-- The coordinate value map on the product of ambient node coordinates and
the evaluation variable. -/
def coordinateGapValueMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateGapValue A B z.1 g z.2

/-- The coordinate critical equation on that product. -/
def coordinateCriticalMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateCriticalValue A B z.1 g z.2

/-- The vertical derivative of the critical equation at the chosen critical
point is `F''_g(τ_g)`. -/
def criticalVerticalCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  (gapPolynomial nodes.toOrderedNodes g).derivative.derivative.eval
    (gapArgmax nodes.toOrderedNodes g)

lemma criticalVerticalCoefficient_neg {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g < 0 := by
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes.toOrderedNodes
    (by omega) g

/-- In the one-coordinate/three-node case the second derivative need not use
the `n ≥ 4` logarithmic-concavity argument: the first derivative is a
nonzero polynomial of degree at most one with a root at the maximizer. -/
lemma criticalVerticalCoefficient_ne_zero_of_one_coordinate {A B : ℝ}
    (nodes : EndpointArray 1 A B) (g : Fin 2) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  let dp : ℝ[X] := (gapPolynomial nodes.toOrderedNodes g).derivative
  have hdegree : dp.natDegree ≤ 1 :=
    natDegree_gapPolynomial_derivative_le_one_of_three_nodes
      nodes.toOrderedNodes g
  obtain ⟨a, b, hab⟩ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdegree
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero
    nodes.toOrderedNodes (by norm_num) g
  have hcrit : dp.eval (gapArgmax nodes.toOrderedNodes g) = 0 :=
    gapPolynomial_derivative_eval_gapArgmax nodes.toOrderedNodes
      (by norm_num) g
  change dp.derivative.eval (gapArgmax nodes.toOrderedNodes g) ≠ 0
  intro hsecond
  rw [hab] at hdp hcrit hsecond
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one,
    zero_add] at hsecond
  have ha : a = 0 := by simpa using hsecond
  rw [ha] at hdp hcrit
  simp at hdp hcrit
  exact hdp hcrit

/-- The vertical derivative is nonzero in every nonexceptional dimension.
This combines the elementary three-node case with strict negativity for at
least four nodes. -/
lemma criticalVerticalCoefficient_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact criticalVerticalCoefficient_ne_zero_of_one_coordinate nodes g
  · exact ne_of_lt (criticalVerticalCoefficient_neg nodes (by omega) g)

lemma coordinateCriticalMap_eq_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    coordinateCriticalMap A B g (u.1, coordinateGapArgmax hAB u g) = 0 := by
  rw [coordinateCriticalMap, coordinateGapArgmax,
    coordinateCriticalValue_eq hAB u]
  exact gapPolynomial_derivative_eval_gapArgmax
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g

/-- The exact local coordinate-calculus obligations for one gap.  The
horizontal formula is the source's node-sensitivity identity; the vertical
formula for the value map is stationarity at `τ_g`. -/
structure GapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) where
  criticalDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  valueDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  hasFDerivAt_critical : HasFDerivAt (coordinateCriticalMap A B g)
    criticalDifferential (u.1, coordinateGapArgmax hAB u g)
  contDiffAt_critical : ContDiffAt ℝ 1 (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  critical_vertical :
    criticalDifferential.comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (criticalVerticalCoefficient (endpointArrayOfInterior hAB u) g)
  hasFDerivAt_value : HasFDerivAt (coordinateGapValueMap A B g)
    valueDifferential (u.1, coordinateGapArgmax hAB u g)
  value_vertical :
    valueDifferential.comp
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) = 0
  value_horizontal_sensitivity : ∀ j : Fin d,
    (valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) =
      -(gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval
          ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j)) *
        lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j) (coordinateGapArgmax hAB u g)

private lemma continuousLinearMap_bijective_of_apply_one_ne_zero
    (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : Function.Bijective L := by
  have hformula (x : ℝ) : L x = x * L 1 := by
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x • L 1 := map_smul L x 1
      _ = x * L 1 := by simp [smul_eq_mul]
  constructor
  · intro x y hxy
    have hx := hformula x
    have hy := hformula y
    exact mul_right_cancel₀ h (hx.symm.trans (hxy.trans hy))
  · intro y
    refine ⟨y / L 1, ?_⟩
    rw [hformula]
    exact div_mul_cancel₀ y h

/-- Negative second derivative turns the checked coordinate derivative data
into Mathlib's implicit-function predicate. -/
def gapCriticalIsContDiffImplicitAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    IsContDiffImplicitAt 1 (coordinateCriticalMap A B g)
      data.criticalDifferential (u.1, coordinateGapArgmax hAB u g) where
  hasFDerivAt := data.hasFDerivAt_critical
  contDiffAt := data.contDiffAt_critical
  bijective := by
    rw [data.critical_vertical]
    apply continuousLinearMap_bijective_of_apply_one_ne_zero
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      one_smul]
    exact criticalVerticalCoefficient_ne_zero
      (endpointArrayOfInterior hAB u) hd g
  ne_zero := by norm_num

/-- The local critical branch supplied by the implicit-function theorem. -/
def localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  (gapCriticalIsContDiffImplicitAt hAB u hd g data).implicitFunction

lemma localGapCriticalPoint_eq_at_base {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    localGapCriticalPoint hAB u hd g data u.1 = coordinateGapArgmax hAB u g := by
  let hIFT := gapCriticalIsContDiffImplicitAt hAB u hd g data
  exact (hIFT.eventually_implicitFunction_apply_eq.self_of_nhds
    (by rfl))

lemma contDiffAt_localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ContDiffAt ℝ 1 (localGapCriticalPoint hAB u hd g data) u.1 :=
  (gapCriticalIsContDiffImplicitAt hAB u hd g data).contDiffAt_implicitFunction

lemma eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      coordinateCriticalMap A B g
        (v, localGapCriticalPoint hAB u hd g data v) = 0 := by
  have hevent :=
    (gapCriticalIsContDiffImplicitAt hAB u hd g data).apply_implicitFunction
  rw [coordinateCriticalMap_eq_zero hAB u (by omega) g] at hevent
  exact hevent

/-- Pointwise identification of the IFT branch with the already-proved unique
own-gap critical point.  The explicit open-gap premise is the local geometric
condition used to select the source branch. -/
lemma localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g)
    (v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hcritical : coordinateCriticalMap A B g
      (v.1, localGapCriticalPoint hAB u hd g data v.1) = 0)
    (hgap : localGapCriticalPoint hAB u hd g data v.1 ∈
      openGap (endpointArrayOfInterior hAB v).toOrderedNodes g) :
    localGapCriticalPoint hAB u hd g data v.1 =
      coordinateGapArgmax hAB v g := by
  have hderiv :
      (gapPolynomial (endpointArrayOfInterior hAB v).toOrderedNodes g).derivative.eval
        (localGapCriticalPoint hAB u hd g data v.1) = 0 := by
    rw [← coordinateCriticalValue_eq hAB v]
    exact hcritical
  by_cases hd1 : d = 1
  · subst d
    exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
      (endpointArrayOfInterior hAB v).toOrderedNodes g hderiv
  · exact eq_gapArgmax_of_derivative_eval_eq_zero
      (endpointArrayOfInterior hAB v).toOrderedNodes (by omega) g hgap hderiv

/-- Abstract envelope cancellation: when the vertical derivative of the
value vanishes, the derivative of `u ↦ F(u,τ(u))` is just the horizontal
partial derivative, independently of `Dτ`. -/
lemma hasFDerivAt_envelope_of_vertical_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} {F' : E × ℝ →L[ℝ] ℝ} {τ : E → ℝ}
    {τ' : E →L[ℝ] ℝ} {u : E}
    (hF : HasFDerivAt F F' (u, τ u)) (hτ : HasFDerivAt τ τ' u)
    (hvertical : F'.comp (ContinuousLinearMap.inr ℝ E ℝ) = 0) :
    HasFDerivAt (fun v => F (v, τ v))
      (F'.comp (ContinuousLinearMap.inl ℝ E ℝ)) u := by
  have hpair : HasFDerivAt (fun v : E => (v, τ v))
      ((1 : E →L[ℝ] E).prod τ') u :=
    (hasFDerivAt_id u).prodMk hτ
  have hcomp := hF.comp u hpair
  have hmaps : F'.comp ((1 : E →L[ℝ] E).prod τ') =
      F'.comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    ext v
    have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L (τ' v)) hvertical
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply] at hv
    change F' (v, τ' v) = F' (v, 0)
    rw [show (v, τ' v) = (v, 0) + (0, τ' v) by ext <;> simp]
    rw [map_add, hv, add_zero]
  rw [hmaps] at hcomp
  simpa only [Function.comp_apply] using hcomp

/-- The local critical-value branch.  Near the base point it is the genuine
gap height once the preceding branch-identification lemma is applied. -/
def localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  fun v => coordinateGapValue A B v g
    (localGapCriticalPoint hAB u hd g data v)

private lemma continuous_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Continuous (fun v : Fin d → ℝ => endpointPoint A B v k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split
    · fun_prop
    · fun_prop

/-- The implicit branch remains in its owning moving gap near the base
array.  This supplies the geometric branch selection needed to use the
unique-critical-point theorem. -/
lemma eventually_localGapCriticalPoint_mem_coordinate_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      endpointPoint A B v (gapLeftIndex (n := d + 2) g) <
          localGapCriticalPoint hAB u hd g data v ∧
        localGapCriticalPoint hAB u hd g data v <
          endpointPoint A B v (gapRightIndex (n := d + 2) g) := by
  have hτcont : ContinuousAt (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).continuousAt
  have hopen := gapArgmax_mem_openGap
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g
  have hbaseLeft :
      endpointPoint A B u.1 (gapLeftIndex (n := d + 2) g) <
        localGapCriticalPoint hAB u hd g data u.1 := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.1
  have hbaseRight :
      localGapCriticalPoint hAB u hd g data u.1 <
        endpointPoint A B u.1 (gapRightIndex (n := d + 2) g) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.2
  exact ((continuous_endpointPoint_coordinate A B
      (gapLeftIndex (n := d + 2) g)).continuousAt.eventually_lt
        hτcont hbaseLeft).and
    (hτcont.eventually_lt
      (continuous_endpointPoint_coordinate A B
        (gapRightIndex (n := d + 2) g)).continuousAt hbaseRight)

/-- Near the base point, the local critical-value branch is exactly the
compactly defined gap height for every ordered coordinate vector. -/
lemma eventually_localGapCriticalHeight_eq_coordinateGapHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1, ∀ hv : v ∈ endpointNodeSpace d A B,
      localGapCriticalHeight hAB u hd g data v =
        coordinateGapHeight hAB ⟨v, hv⟩ g := by
  filter_upwards
      [eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
        hAB u hd g data,
       eventually_localGapCriticalPoint_mem_coordinate_openGap
        hAB u hd g data] with v hcritical hgap
  intro hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  have hgap' : localGapCriticalPoint hAB u hd g data v ∈
      openGap (endpointArrayOfInterior hAB v').toOrderedNodes g := hgap
  have harg := localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    hAB u hd g data v' hcritical hgap'
  rw [coordinateGapHeight_eq_value_at_argmax]
  change coordinateGapValue A B v g
      (localGapCriticalPoint hAB u hd g data v) =
    coordinateGapValue A B v g (coordinateGapArgmax hAB v' g)
  rw [harg]

/-- A total ambient extension of the genuine gap height.  Outside the open
simplex it uses the local critical-value expression; inside it is exactly
`gapHeight`. -/
def extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) (v : Fin d → ℝ) : ℝ := by
  classical
  exact if hv : v ∈ endpointNodeSpace d A B then
      coordinateGapHeight hAB ⟨v, hv⟩ g
    else localGapCriticalHeight hAB u hd g data v

lemma hasFDerivAt_localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (localGapCriticalHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  have hτdiff : DifferentiableAt ℝ
      (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).differentiableAt
      (by norm_num)
  have hτ := hτdiff.hasFDerivAt
  have hvalue : HasFDerivAt (coordinateGapValueMap A B g)
      data.valueDifferential
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact data.hasFDerivAt_value
  exact hasFDerivAt_envelope_of_vertical_eq_zero hvalue hτ data.value_vertical

/-- Conditional on the explicit coordinate derivative package, the actual
gap height has a differentiable ambient extension at every array with at
least one moving node. -/
lemma hasFDerivAt_extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (extendedCoordinateGapHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  apply (hasFDerivAt_localGapCriticalHeight hAB u hd g data).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [extendedCoordinateGapHeight, dif_pos hv]
  exact (heq hv).symm

/-! The only downstream sign input is named as a proposition.  Importantly,
this file does not construct an inhabitant of it. -/

/-- Cross-polynomial sign/interlacing must ultimately prove these quotient
evaluation minors nonzero. -/
def QuotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∀ omitted : Fin (d + 1),
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0

/-! ## Discharging the coordinate-calculus interface -/

/-- One normalized scalar factor of a coordinate cardinal polynomial. -/
def coordinateLagrangeFactorValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k i : Fin (d + 2)) (x : ℝ) : ℝ :=
  (x - endpointPoint A B u i) *
    (endpointPoint A B u k - endpointPoint A B u i)⁻¹

lemma coordinateLagrangePolynomial_eval_eq_prod_factor {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).eval x =
      ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i x := by
  simp only [coordinateLagrangePolynomial, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, coordinateLagrangeFactorValue]

@[fun_prop]
lemma differentiable_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Differentiable ℝ (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop

lemma endpointPoint_sub_ne_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) :
    endpointPoint A B u.1 k - endpointPoint A B u.1 i ≠ 0 := by
  exact sub_ne_zero.mpr
    ((endpointPoint_strictMono hAB.2.1 u.2).injective.ne hki)

lemma differentiableAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply DifferentiableAt.mul
  · exact differentiableAt_snd.sub
      ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
        _ differentiableAt_fst)
  · apply DifferentiableAt.inv
    · exact ((differentiable_endpointPoint_coordinate A B k).differentiableAt.comp
          _ differentiableAt_fst).sub
        ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
          _ differentiableAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki

lemma differentiableAt_coordinateLagrangePolynomial_eval {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      (coordinateLagrangePolynomial A B z.1 k).eval z.2) (u.1, x) := by
  simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
  let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
    fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
  have hfac : ∀ i ∈ Finset.univ.erase k,
      DifferentiableAt ℝ (fac i) (u.1, x) := by
    intro i hi
    exact differentiableAt_coordinateLagrangeFactorValue hAB u
      (Finset.mem_erase.mp hi).1.symm x
  have hprod := HasFDerivAt.finset_prod
    (g' := fun i => fderiv ℝ (fac i) (u.1, x))
    (fun i hi => (hfac i hi).hasFDerivAt)
  exact hprod.differentiableAt

lemma differentiableAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    DifferentiableAt ℝ (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := DifferentiableAt.sum (u := Finset.univ)
    (A := fun k (z : (Fin d → ℝ) × ℝ) => gapCoefficient g k *
      (coordinateLagrangePolynomial A B z.1 k).eval z.2)
    (fun k _ => (differentiableAt_const (c := gapCoefficient g k)).mul
      (differentiableAt_coordinateLagrangePolynomial_eval hAB u k x))
  convert hsum using 1
  funext z
  simp

/-- The derivative with respect to the evaluation variable of one cardinal
product, displayed as the product rule. -/
def coordinateLagrangeCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase k,
    (∏ m ∈ (Finset.univ.erase k).erase i,
      coordinateLagrangeFactorValue A B u k m x) *
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹

lemma hasDerivAt_coordinateLagrangeFactorValue_evaluation {d : ℕ}
    {A B : ℝ} {u : Fin d → ℝ} {k i : Fin (d + 2)} {x : ℝ} :
    HasDerivAt (fun y => coordinateLagrangeFactorValue A B u k i y)
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ x := by
  unfold coordinateLagrangeFactorValue
  convert ((hasDerivAt_id x).sub_const
    (endpointPoint A B u i)).mul_const
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ using 1
  all_goals ring

lemma coordinateLagrangeCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).derivative.eval x =
      coordinateLagrangeCriticalFormula A B u k x := by
  have hp := (coordinateLagrangePolynomial A B u k).hasDerivAt x
  have hprod := HasDerivAt.finset_prod (x := x)
    (u := Finset.univ.erase k)
    (f := fun i y => coordinateLagrangeFactorValue A B u k i y)
    (f' := fun i => (endpointPoint A B u k - endpointPoint A B u i)⁻¹)
    (fun _i _ => hasDerivAt_coordinateLagrangeFactorValue_evaluation)
  have hprod' : HasDerivAt
      (fun y => ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i y)
      (coordinateLagrangeCriticalFormula A B u k x) x := by
    convert hprod using 1
    funext y
    simp
  have heqfun :
      (fun y => (coordinateLagrangePolynomial A B u k).eval y) =
        fun y => ∏ i ∈ Finset.univ.erase k,
          coordinateLagrangeFactorValue A B u k i y := by
    funext y
    exact coordinateLagrangePolynomial_eval_eq_prod_factor A B u k y
  rw [heqfun] at hp
  exact hp.unique hprod'

def coordinateGapCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  ∑ k : Fin (d + 2), gapCoefficient g k *
    coordinateLagrangeCriticalFormula A B u k x

lemma coordinateGapCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u g x =
      coordinateGapCriticalFormula A B u g x := by
  simp only [coordinateCriticalValue, coordinateGapPolynomial,
    Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    coordinateGapCriticalFormula, coordinateLagrangeCriticalFormula_eq]

@[fun_prop]
lemma contDiff_endpointPoint_coordinate {d : ℕ} (n : WithTop ℕ∞)
    (A B : ℝ) (k : Fin (d + 2)) :
    ContDiff ℝ n (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop

private lemma contDiffAt_finset_prod_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (1 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

private lemma contDiffAt_finset_sum_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

lemma contDiffAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply ContDiffAt.mul
  · exact contDiffAt_snd.sub
      ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
        (u.1, x) contDiffAt_fst)
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki

lemma contDiffAt_coordinateLagrangeCriticalFormula {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeCriticalFormula A B z.1 k z.2) (u.1, x) := by
  unfold coordinateLagrangeCriticalFormula
  apply contDiffAt_finset_sum_scalar
  intro i hi
  apply ContDiffAt.mul
  · apply contDiffAt_finset_prod_scalar
    intro m hm
    exact contDiffAt_coordinateLagrangeFactorValue hAB u (by
      have hm' := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1
      exact hm'.symm) x n
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u
        (Finset.mem_erase.mp hi).1.symm

lemma contDiffAt_coordinateCriticalMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (coordinateCriticalMap A B g) (u.1, x) := by
  rw [show coordinateCriticalMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        coordinateLagrangeCriticalFormula A B z.1 k z.2 by
    funext z
    exact coordinateGapCriticalFormula_eq A B z.1 g z.2]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul
    (contDiffAt_coordinateLagrangeCriticalFormula hAB u k x n)

private lemma fderiv_comp_inr_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hx : HasDerivAt (fun y => f (u, y)) c x) :
    (fderiv ℝ f (u, x)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := by
  have hcurve : HasFDerivAt (fun y : ℝ => (u, y))
      (ContinuousLinearMap.inr ℝ E ℝ) x := by
    convert (hasFDerivAt_const (x := x) (c := u)).prodMk
      (hasFDerivAt_id x) using 1
  have hcomp := hf.hasFDerivAt.comp x hcurve
  exact hcomp.unique hx

lemma coordinateGapValueMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateCriticalValue A B u.1 g x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  change HasDerivAt (fun y => coordinateGapValue A B u.1 g y)
    (coordinateCriticalValue A B u.1 g x) x
  simpa only [coordinateGapValue, coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).hasDerivAt x

lemma coordinateCriticalMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateCriticalMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    ((contDiffAt_coordinateCriticalMap hAB u g x 1).differentiableAt
      (by norm_num))
  change HasDerivAt (fun y => coordinateCriticalValue A B u.1 g y)
    ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) x
  simpa only [coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).derivative.hasDerivAt x

/-! ### Moving one interior node -/

/-- Unit coordinate direction for the `j`th interior node. -/
def coordinateDirection {d : ℕ} (j : Fin d) : Fin d → ℝ := Pi.single j 1

/-- Affine line which moves only the `j`th interior node. -/
def coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) (s : ℝ) :
    Fin d → ℝ :=
  u + s • coordinateDirection j

@[simp]
lemma coordinateShift_zero {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    coordinateShift u j 0 = u := by
  ext i
  simp [coordinateShift]

lemma coordinateShift_apply_self {d : ℕ} (u : Fin d → ℝ)
    (j : Fin d) (s : ℝ) :
    coordinateShift u j s j = u j + s := by
  simp [coordinateShift, coordinateDirection]

lemma coordinateShift_apply_of_ne {d : ℕ} (u : Fin d → ℝ)
    {j i : Fin d} (hij : i ≠ j) (s : ℝ) :
    coordinateShift u j s i = u i := by
  simp [coordinateShift, coordinateDirection, hij]

/-- Velocity of a full endpoint-adjoined node under `coordinateShift`. -/
def coordinateNodeVelocity {d : ℕ} (j : Fin d) (k : Fin (d + 2)) : ℝ :=
  if k = interiorNodeIndex j then 1 else 0

lemma hasDerivAt_endpointPoint_coordinateShift {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    HasDerivAt (fun s => endpointPoint A B (coordinateShift u j s) k)
      (coordinateNodeVelocity j k) 0 := by
  rcases endpoint_index_cases k with rfl | rfl | ⟨i, rfl⟩
  · simp only [endpointPoint_left]
    have hne : endpointLeftIndex d ≠ interiorNodeIndex j :=
      (endpointLeftIndex_lt_interior j).ne
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := A))
  · simp only [endpointPoint_right]
    have hne : endpointRightIndex d ≠ interiorNodeIndex j :=
      (interior_lt_endpointRightIndex j).ne'
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := B))
  · simp only [endpointPoint_interior]
    by_cases hij : i = j
    · subst i
      simp only [coordinateShift_apply_self]
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := u j)).add
        (hasDerivAt_id 0) using 1
      simp [coordinateNodeVelocity]
    · have hfun : (fun s => coordinateShift u j s i) = fun _ => u i := by
        funext s
        exact coordinateShift_apply_of_ne u hij s
      have hnode : interiorNodeIndex i ≠ interiorNodeIndex j :=
        interiorNodeIndex_strictMono.injective.ne hij
      rw [hfun]
      simpa [coordinateNodeVelocity, hnode] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := u i))

lemma hasFDerivAt_coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    HasFDerivAt (coordinateShift u j)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateDirection j)) 0 := by
  let L : ℝ →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (coordinateDirection j)
  have h := (hasFDerivAt_const (x := (0 : ℝ)) (c := u)).add L.hasFDerivAt
  simpa [coordinateShift, L, smul_eq_mul, mul_comm] using h

/-- Polynomial form of one normalized factor. -/
def coordinateLagrangeFactorPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) : ℝ[X] :=
  (X - C (endpointPoint A B u i)) *
    C (endpointPoint A B u k - endpointPoint A B u i)⁻¹

/-- Directional derivative of one normalized factor when interior node `j`
moves.  This is the quotient rule written as a polynomial in `X`. -/
def coordinateLagrangeFactorPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k i : Fin (d + 2)) : ℝ[X] :=
  (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)) *
    C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹)

lemma coordinateLagrangeFactorPolynomial_eval {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangeFactorPolynomial A B u k i).eval x =
      coordinateLagrangeFactorValue A B u k i x := by
  simp [coordinateLagrangeFactorPolynomial,
    coordinateLagrangeFactorValue]

lemma hasDerivAt_coordinateLagrangeFactor_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    HasDerivAt (fun s => coordinateLagrangeFactorValue A B
      (coordinateShift u.1 j s) k i x)
      ((coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x) 0 := by
  have hti := hasDerivAt_endpointPoint_coordinateShift A B u.1 j i
  have htk := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hnum : HasDerivAt
      (fun s => x - endpointPoint A B (coordinateShift u.1 j s) i)
      (-(coordinateNodeVelocity j i)) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := x)).sub hti using 1
    all_goals simp [coordinateNodeVelocity]
  have hden : HasDerivAt
      (fun s => endpointPoint A B (coordinateShift u.1 j s) k -
        endpointPoint A B (coordinateShift u.1 j s) i)
      (coordinateNodeVelocity j k - coordinateNodeVelocity j i) 0 := by
    exact htk.sub hti
  have hne := endpointPoint_sub_ne_zero hAB u hki
  have hquot := hnum.div hden (by simpa using hne)
  convert hquot using 1
  simp only [coordinateLagrangeFactorPartialPolynomial,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, coordinateShift_zero]
  field_simp [hne]

/-- Product-rule directional derivative of a coordinate cardinal polynomial. -/
def coordinateLagrangePartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) : ℝ[X] :=
  ∑ i ∈ Finset.univ.erase k,
    coordinateLagrangeFactorPartialPolynomial A B u j k i *
      ∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m

/-- Directional derivative polynomial of the signed gap polynomial. -/
def coordinateGapPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) : ℝ[X] :=
  ∑ k : Fin (d + 2), C (gapCoefficient g k) *
    coordinateLagrangePartialPolynomial A B u j k

lemma hasDerivAt_coordinateLagrange_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (k : Fin (d + 2)) (x : ℝ) :
    HasDerivAt (fun s =>
      (coordinateLagrangePolynomial A B (coordinateShift u.1 j s) k).eval x)
      ((coordinateLagrangePartialPolynomial A B u.1 j k).eval x) 0 := by
  let fac : Fin (d + 2) → ℝ → ℝ := fun i s =>
    coordinateLagrangeFactorValue A B (coordinateShift u.1 j s) k i x
  have hprod := HasDerivAt.finset_prod (x := (0 : ℝ))
    (u := Finset.univ.erase k) (f := fac)
    (f' := fun i =>
      (coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x)
    (fun i hi => hasDerivAt_coordinateLagrangeFactor_coordinateShift
      hAB u j (Finset.mem_erase.mp hi).1.symm x)
  convert hprod using 1
  · funext s
    rw [coordinateLagrangePolynomial_eval_eq_prod_factor]
    simp [fac]
  · simp only [coordinateLagrangePartialPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod,
      fac, coordinateLagrangeFactorPolynomial_eval, smul_eq_mul,
      coordinateShift_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma hasDerivAt_finset_sum_scalar {ι : Type*} {s : Finset ι}
    {f : ι → ℝ → ℝ} {f' : ι → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (x := x) (c := (0 : ℝ))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      convert (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi]))) using 1

lemma hasDerivAt_coordinateGapValue_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    HasDerivAt (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x)
      ((coordinateGapPartialPolynomial A B u.1 g j).eval x) 0 := by
  rw [show (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x) =
      fun s => ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B
          (coordinateShift u.1 j s) k).eval x by
    funext s
    simp only [coordinateGapValue, coordinateGapPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := hasDerivAt_finset_sum_scalar (s := Finset.univ)
    (f := fun k s => gapCoefficient g k *
      (coordinateLagrangePolynomial A B
        (coordinateShift u.1 j s) k).eval x)
    (f' := fun k => gapCoefficient g k *
      (coordinateLagrangePartialPolynomial A B u.1 j k).eval x)
    (fun k _ => (hasDerivAt_coordinateLagrange_coordinateShift
      hAB u j k x).const_mul (gapCoefficient g k))
  convert hsum using 1
  simp only [coordinateGapPartialPolynomial,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]

private lemma fderiv_apply_inl_direction_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u v : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hv : HasFDerivAt (fun s : ℝ => u + s • v)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0)
    (hx : HasDerivAt (fun s : ℝ => f (u + s • v, x)) c 0) :
    fderiv ℝ f (u, x) (v, 0) = c := by
  have hcurve : HasFDerivAt (fun s : ℝ => (u + s • v, x))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).prod
        (0 : ℝ →L[ℝ] ℝ)) 0 :=
    hv.prodMk (hasFDerivAt_const (x := (0 : ℝ)) (c := x))
  have hfbase : HasFDerivAt f (fderiv ℝ f (u, x))
      (u + (0 : ℝ) • v, x) := by
    simpa using hf.hasFDerivAt
  have hcomp := hfbase.comp 0 hcurve
  have hvalue := hcomp.unique (by
    simpa only [Function.comp_apply] using hx)
  have happly := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hvalue
  simpa using happly

lemma coordinateGapValueMap_fderiv_horizontal_explicit {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval x := by
  apply fderiv_apply_inl_direction_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  · simpa only [coordinateShift] using hasFDerivAt_coordinateShift u.1 j
  · simpa only [coordinateGapValueMap, coordinateShift] using
      hasDerivAt_coordinateGapValue_coordinateShift hAB u g j x

/-! ### Identification of the moving-node derivative -/

lemma eventually_coordinateShift_mem_endpointNodeSpace {d : ℕ}
    {A B : ℝ}
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) (j : Fin d) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateShift u.1 j s ∈ endpointNodeSpace d A B := by
  have hmem : endpointNodeSpace d A B ∈ 𝓝 (coordinateShift u.1 j 0) := by
    simpa using (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  exact (hasFDerivAt_coordinateShift u.1 j).continuousAt.eventually hmem

lemma eventually_coordinateGapValue_shift_at_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateGapValue A B (coordinateShift u.1 j s) g
        (endpointPoint A B (coordinateShift u.1 j s) k) =
          gapCoefficient g k := by
  filter_upwards [eventually_coordinateShift_mem_endpointNodeSpace u j] with s hs
  let v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} :=
    ⟨coordinateShift u.1 j s, hs⟩
  rw [coordinateGapValue_eq hAB v]
  exact gapPolynomial_eval_node
    (endpointArrayOfInterior hAB v).toOrderedNodes g k

/-- The directional derivative polynomial has the values forced by
differentiating the interpolation equations: it vanishes at every stationary
node and equals `-F'_g(t_j)` at the moving node. -/
lemma coordinateGapPartialPolynomial_eval_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateGapPartialPolynomial A B u.1 g j).eval
        (endpointPoint A B u.1 k) =
      -(coordinateNodeVelocity j k) *
        (coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 k) := by
  let t : ℝ := endpointPoint A B u.1 k
  let L := fderiv ℝ (coordinateGapValueMap A B g) (u.1, t)
  have hdiff := differentiableAt_coordinateGapValueMap hAB u g t
  have hpoint := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hcurve : HasFDerivAt
      (fun s : ℝ => (coordinateShift u.1 j s,
        endpointPoint A B (coordinateShift u.1 j s) k))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateDirection j)).prod
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateNodeVelocity j k))) 0 :=
    (hasFDerivAt_coordinateShift u.1 j).prodMk hpoint.hasFDerivAt
  have hbase : (coordinateShift u.1 j 0,
      endpointPoint A B (coordinateShift u.1 j 0) k) = (u.1, t) := by
    simp [t]
  have hFbase : HasFDerivAt (coordinateGapValueMap A B g) L
      (coordinateShift u.1 j 0,
        endpointPoint A B (coordinateShift u.1 j 0) k) := by
    rw [hbase]
    exact hdiff.hasFDerivAt
  have hcomp := hFbase.comp 0 hcurve
  have hevent :
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k)) =ᶠ[𝓝 0]
      (fun _ => gapCoefficient g k) := by
    simpa only [coordinateGapValueMap] using
      eventually_coordinateGapValue_shift_at_node hAB u g j k
  have hzero : HasFDerivAt
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k))
      (0 : ℝ →L[ℝ] ℝ) 0 := by
    exact (hasFDerivAt_const (x := (0 : ℝ))
      (c := gapCoefficient g k)).congr_of_eventuallyEq hevent
  have hmaps := hcomp.unique hzero
  have happly := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hmaps
  have hhorizontal := coordinateGapValueMap_fderiv_horizontal_explicit
    hAB u g j t
  have hverticalMap := coordinateGapValueMap_fderiv_vertical hAB u g t
  have hvertical := congrArg (fun M : ℝ →L[ℝ] ℝ =>
    M (coordinateNodeVelocity j k)) hverticalMap
  change L (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval t at hhorizontal
  change L (0, coordinateNodeVelocity j k) =
      coordinateNodeVelocity j k *
        coordinateCriticalValue A B u.1 g t at hvertical
  have hsplit : L (coordinateDirection j, coordinateNodeVelocity j k) =
      L (coordinateDirection j, 0) +
        L (0, coordinateNodeVelocity j k) := by
    calc
      L (coordinateDirection j, coordinateNodeVelocity j k) =
          L ((coordinateDirection j, 0) +
            (0, coordinateNodeVelocity j k)) := by congr <;> simp
      _ = _ := map_add L _ _
  have happly' : L (coordinateDirection j, coordinateNodeVelocity j k) = 0 := by
    simpa using happly
  rw [hsplit, hhorizontal, hvertical] at happly'
  rw [coordinateCriticalValue] at happly'
  change (coordinateGapPartialPolynomial A B u.1 g j).eval t =
    -(coordinateNodeVelocity j k) *
      (coordinateGapPolynomial A B u.1 g).derivative.eval t
  linarith

lemma degree_coordinateLagrangeFactorPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPolynomial A B u k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPolynomial
  have hc : (C (endpointPoint A B u k - endpointPoint A B u i)⁻¹ :
      ℝ[X]).degree ≤ 0 := degree_C_le
  exact (degree_mul_le _ _).trans <| by
    simpa using add_le_add
      (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hc

lemma degree_coordinateLagrangeFactorPartialPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d)
    (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPartialPolynomial A B u j k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPartialPolynomial
  apply (degree_mul_le _ _).trans
  have hcvel : (C (coordinateNodeVelocity j k -
      coordinateNodeVelocity j i) : ℝ[X]).degree ≤ 0 := degree_C_le
  have hmul : ((X - C (endpointPoint A B u i)) *
      C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_mul_le _ _).trans <| by
      simpa using add_le_add
        (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hcvel
  have hcfirst : (C (-(coordinateNodeVelocity j i) *
      (endpointPoint A B u k - endpointPoint A B u i)) : ℝ[X]).degree ≤ 0 :=
    degree_C_le
  have hsub : (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_sub_le _ _).trans <| by
      exact max_le (hcfirst.trans (by simp)) hmul
  have hclast :
      (C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹) :
        ℝ[X]).degree ≤ 0 := degree_C_le
  simpa using add_le_add hsub hclast

lemma degree_coordinateLagrangePartialPolynomial_le {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
  classical
  unfold coordinateLagrangePartialPolynomial
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  apply (degree_mul_le _ _).trans
  have hcard : ((Finset.univ.erase k).erase i).card = d := by
    rw [Finset.card_erase_of_mem hi,
      Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hprod :
      (∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m).degree ≤ (d : ℕ) := by
    apply (degree_prod_le _ _).trans
    calc
      (∑ m ∈ (Finset.univ.erase k).erase i,
          (coordinateLagrangeFactorPolynomial A B u k m).degree) ≤
          ∑ _m ∈ (Finset.univ.erase k).erase i, (1 : WithBot ℕ) :=
        Finset.sum_le_sum fun m _ =>
          degree_coordinateLagrangeFactorPolynomial_le_one A B u k m
      _ = (d : ℕ) := by simp [hcard]
  simpa [Nat.cast_add, Nat.cast_one, add_comm] using
    add_le_add
      (degree_coordinateLagrangeFactorPartialPolynomial_le_one A B u j k i)
      hprod

lemma degree_coordinateGapPartialPolynomial_lt {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) :
    (coordinateGapPartialPolynomial A B u g j).degree < (d + 2 : ℕ) := by
  classical
  unfold coordinateGapPartialPolynomial
  have hle : (∑ k : Fin (d + 2), C (gapCoefficient g k) *
      coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
    apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro k _
    apply (degree_mul_le _ _).trans
    have hc : (C (gapCoefficient g k) : ℝ[X]).degree ≤ 0 := degree_C_le
    simpa using add_le_add hc
      (degree_coordinateLagrangePartialPolynomial_le A B u j k)
  exact hle.trans_lt (by
    rw [Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega)

/-- The moving-node derivative is the source sensitivity polynomial
`-F'_g(t_j) l_j`.  The proof uses its derived nodal values and the degree
budget, rather than assuming the formula. -/
lemma coordinateGapPartialPolynomial_eq_sourceSensitivity {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) :
    coordinateGapPartialPolynomial A B u.1 g j =
      C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
        (endpointPoint A B u.1 (interiorNodeIndex j))) *
        coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j) := by
  classical
  let rhs : ℝ[X] :=
    C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
      (endpointPoint A B u.1 (interiorNodeIndex j))) *
      coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j)
  have hdegLeft : (coordinateGapPartialPolynomial A B u.1 g j).degree <
      ((Finset.univ : Finset (Fin (d + 2))).card : ℕ) := by
    simpa using degree_coordinateGapPartialPolynomial_lt A B u.1 g j
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (endpointPoint_strictMono hAB.2.1 u.2).injective.injOn hdegLeft
  · have hbasis := Lagrange.degree_basis
      (s := Finset.univ) (v := (endpointArrayOfInterior hAB u).point)
      (endpointArrayOfInterior hAB u).injective.injOn
      (Finset.mem_univ (interiorNodeIndex j))
    have hcoord : (coordinateLagrangePolynomial A B u.1
        (interiorNodeIndex j)).degree = (d + 1 : ℕ) := by
      rw [coordinateLagrangePolynomial_eq hAB u, lagrangeBasis]
      simpa using hbasis
    have hright : rhs.degree < (d + 2 : ℕ) := by
      unfold rhs
      apply (degree_mul_le _ _).trans_lt
      have hc : (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j))) : ℝ[X]).degree ≤ 0 :=
        degree_C_le
      calc
        (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
              (endpointPoint A B u.1 (interiorNodeIndex j)))).degree +
            (coordinateLagrangePolynomial A B u.1
              (interiorNodeIndex j)).degree ≤
            0 + (d + 1 : ℕ) := add_le_add hc hcoord.le
        _ < (d + 2 : ℕ) := by
          rw [zero_add, Nat.cast_withBot, Nat.cast_withBot,
            WithBot.coe_lt_coe]
          omega
    simpa only [Finset.card_univ, Fintype.card_fin] using hright
  · intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      coordinateGapPartialPolynomial_eval_node hAB u g j k]
    by_cases hk : k = interiorNodeIndex j
    · subst k
      simp only [coordinateNodeVelocity]
      rw [coordinateLagrangePolynomial_eq hAB u]
      change _ = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j))
      rw [lagrangeBasis_eval_self, mul_one]
      norm_num
    · rw [show coordinateNodeVelocity j k = 0 by
        simp [coordinateNodeVelocity, hk]]
      simp only [neg_zero, zero_mul]
      rw [coordinateLagrangePolynomial_eq hAB u]
      have heval :
          (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
            (interiorNodeIndex j)).eval
              ((endpointArrayOfInterior hAB u).point k) = 0 :=
        lagrangeBasis_eval_of_ne _ hk
      change 0 = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point k)
      rw [heval, mul_zero]

lemma coordinateGapValueMap_fderiv_horizontal_source {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      -(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j)) *
        (coordinateLagrangePolynomial A B u.1
          (interiorNodeIndex j)).eval x := by
  rw [coordinateGapValueMap_fderiv_horizontal_explicit hAB u g j x,
    coordinateGapPartialPolynomial_eq_sourceSensitivity hAB u g j,
    Polynomial.eval_mul, Polynomial.eval_C]

/-! ### The concrete derivative package and unconditional height Jacobian -/

/-- The formerly abstract coordinate derivative package, now constructed
from the finite product and interpolation calculations above. -/
def concreteGapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : GapCoordinateDerivativesAt hAB u g where
  criticalDifferential := fderiv ℝ (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  valueDifferential := fderiv ℝ (coordinateGapValueMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  hasFDerivAt_critical :=
    ((contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1).differentiableAt
        (by norm_num)).hasFDerivAt
  contDiffAt_critical :=
    contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1
  critical_vertical := by
    rw [coordinateCriticalMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u]
    rfl
  hasFDerivAt_value :=
    (differentiableAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)).hasFDerivAt
  value_vertical := by
    rw [coordinateGapValueMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    have hcrit : coordinateCriticalValue A B u.1 g
        (coordinateGapArgmax hAB u g) = 0 := by
      by_cases hd : d = 0
      · subst d
        exact coordinateCriticalValue_zero_dim hAB u g _
      · exact coordinateCriticalMap_eq_zero hAB u
          (Nat.one_le_iff_ne_zero.mpr hd) g
    rw [hcrit]
    ext
    simp
  value_horizontal_sensitivity := by
    intro j
    change fderiv ℝ (coordinateGapValueMap A B g)
      (u.1, coordinateGapArgmax hAB u g) (Pi.single j 1, 0) = _
    rw [show Pi.single j 1 = coordinateDirection j by rfl,
      coordinateGapValueMap_fderiv_horizontal_source hAB u g j
        (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u,
      coordinateLagrangePolynomial_eq hAB u, lagrangeBasis_eval]
    rfl

/-- Canonical ambient extension of the genuine compact gap height.  On the
open simplex it is definitionally the compact height, while its off-simplex
values merely provide a total domain for Fréchet differentiation. -/
def canonicalExtendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) : (Fin d → ℝ) → ℝ :=
  extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)

/-- Unconditional differentiability of a local ambient extension of the
coordinate gap height. -/
theorem hasFDerivAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB u hd g)
      ((concreteGapCoordinateDerivativesAt hAB u g).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 :=
  hasFDerivAt_extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)

/-- Unconditional Jacobian-entry formula for genuine coordinate gap heights.
The right-hand side is the already-factored quotient-evaluation model. -/
theorem canonicalCoordinateGapHeight_fderiv_basis_eq_model {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) (j : Fin d) :
    fderiv ℝ (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1
        (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) g j := by
  rw [(hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).fderiv]
  exact ((concreteGapCoordinateDerivativesAt hAB u g).value_horizontal_sensitivity
    j).trans
      (gapHeightJacobianModel_apply_eq
        (endpointArrayOfInterior hAB u) g j).symm

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Minors.lean` -/

/-!
# Maximal quotient-evaluation minors

This file formalizes the last, genuinely linear-algebraic step in Lemma 2 of
de Boor--Pinkus.  The checkerboard signs of the critical quotients are not by
themselves a nonsingularity theorem.  The additional input used here is that
all quotient polynomials have degree at most `d - 1`: the source's alternating
sign construction would otherwise produce `d` distinct real zeros.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Polynomial
noncomputable section

/-! ## The alternating-zero-count kernel -/

/-- A polynomial of degree strictly below `d` cannot change sign across all
`d` consecutive intervals cut out by `d+1` strictly ordered points. -/
private theorem eq_zero_of_eval_mul_next_neg {d : ℕ} (p : ℝ[X])
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hdegree : p.natDegree < d)
    (hsign : ∀ j : Fin d,
      p.eval (τ j.castSucc) * p.eval (τ j.succ) < 0) :
    p = 0 := by
  classical
  have hexists (j : Fin d) :
      ∃ x ∈ Set.Ioo (τ j.castSucc) (τ j.succ), p.eval x = 0 := by
    have hab : τ j.castSucc ≤ τ j.succ :=
      (hτ Fin.castSucc_lt_succ).le
    have hcont : ContinuousOn (fun x => p.eval x)
        (Set.Icc (τ j.castSucc) (τ j.succ)) :=
      p.continuous.continuousOn
    rcases mul_neg_iff.mp (hsign j) with hj | hj
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.succ))
          (p.eval (τ j.castSucc)) := ⟨hj.2, hj.1⟩
      exact intermediate_value_Ioo' hab hcont hz
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.castSucc))
          (p.eval (τ j.succ)) := hj
      exact intermediate_value_Ioo hab hcont hz
  let r : Fin d → ℝ := fun j => Classical.choose (hexists j)
  have hr_mem (j : Fin d) : r j ∈ Set.Ioo (τ j.castSucc) (τ j.succ) :=
    (Classical.choose_spec (hexists j)).1
  have hr_eval (j : Fin d) : p.eval (r j) = 0 :=
    (Classical.choose_spec (hexists j)).2
  have hr_strictMono : StrictMono r := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hmiddle : τ i.succ ≤ τ j.castSucc := by
      apply hτ.monotone
      exact Fin.le_iff_val_le_val.mpr (by simpa using hij')
    exact ((hr_mem i).2.trans_le hmiddle).trans (hr_mem j).1
  let s : Finset ℝ := Finset.univ.image r
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hr_strictMono.injective,
      Finset.card_univ, Fintype.card_fin]
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    exact hr_eval j

/-! ## Signs of ordered nodal products -/

private lemma sq_negOnePow_v1 (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num

private lemma ordered_gap_nodalProduct_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (g : Fin (n - 1)) {x : ℝ}
    (hx : t (gapLeftIndex g) < x ∧ x < t (gapRightIndex g)) :
    0 < (-1 : ℝ) ^ (n - 1 - g.val) * ∏ k : Fin n, (x - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iic (gapLeftIndex g)
  let U : Finset (Fin n) := Finset.Ioi (gapLeftIndex g)
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hkL
    have hgk : gapLeftIndex g < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkle) hgk
  have hunion : L ∪ U = Finset.univ := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi,
      Finset.mem_univ, iff_true]
    exact le_or_gt k (gapLeftIndex g)
  have hleft : 0 < ∏ k ∈ L, (x - t k) := by
    apply Finset.prod_pos
    intro k hk
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hk
    exact sub_pos.mpr ((ht.monotone hkle).trans_lt hx.1)
  have hright : 0 < ∏ k ∈ U, (t k - x) := by
    apply Finset.prod_pos
    intro k hk
    have hgk : gapLeftIndex g < k := by simpa [U] using hk
    have hright_le : gapRightIndex g ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      change g.val + 1 ≤ k.val
      change g.val < k.val at hgk
      omega
    exact sub_pos.mpr (hx.2.trans_le (ht.monotone hright_le))
  have hprod : (∏ k : Fin n, (x - t k)) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (x - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (x - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - x) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - x))
  have hcard : U.card = n - 1 - g.val := by
    simp [U, gapLeftIndex_val]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - g.val)
  have hs : s ^ 2 = 1 := sq_negOnePow_v1 (n - 1 - g.val)
  have hboth : 0 <
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (x - t k)) *
    (s * ∏ k ∈ U, (t k - x)))
  rw [show s * ((∏ k ∈ L, (x - t k)) *
      (s * ∏ k ∈ U, (t k - x))) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) by
    calc
      s * ((∏ k ∈ L, (x - t k)) *
          (s * ∏ k ∈ U, (t k - x))) =
          s ^ 2 * ((∏ k ∈ L, (x - t k)) *
            ∏ k ∈ U, (t k - x)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth

private lemma ordered_basisDenominator_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (r : Fin n) :
    0 < (-1 : ℝ) ^ (n - 1 - r.val) *
      ∏ k ∈ Finset.univ.erase r, (t r - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iio r
  let U : Finset (Fin n) := Finset.Ioi r
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkr : k < r := by simpa [L] using hkL
    have hrk : r < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkr.le) hrk
  have hunion : L ∪ U = Finset.univ.erase r := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
    · intro h
      exact lt_or_gt_of_ne h
  have hleft : 0 < ∏ k ∈ L, (t r - t k) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [L] using hk))
  have hright : 0 < ∏ k ∈ U, (t k - t r) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [U] using hk))
  have hprod : (∏ k ∈ Finset.univ.erase r, (t r - t k)) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t r - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (t r - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - t r) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - t r))
  have hcard : U.card = n - 1 - r.val := by simp [U]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - r.val)
  have hs : s ^ 2 = 1 := sq_negOnePow_v1 (n - 1 - r.val)
  have hboth : 0 <
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (t r - t k)) *
    (s * ∏ k ∈ U, (t k - t r)))
  rw [show s * ((∏ k ∈ L, (t r - t k)) *
      (s * ∏ k ∈ U, (t k - t r))) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) by
    calc
      s * ((∏ k ∈ L, (t r - t k)) *
          (s * ∏ k ∈ U, (t k - t r))) =
          s ^ 2 * ((∏ k ∈ L, (t r - t k)) *
            ∏ k ∈ U, (t k - t r)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth

private lemma endpointPoint_eq_endpointArray_point {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    endpointPoint A B nodes.interior k = nodes.point k := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have harr := endpointArrayOfInterior_interior nodes.admissibleInterval nodes
  have hpoint := congrArg (fun z : EndpointArray d A B => z.point k) harr
  exact hpoint

/-- Exact row-factor sign: the nodal product at the `g`th gap maximum has
one negative factor for every node strictly to the right of that gap. -/
theorem gapJacobianRowFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ (d + 1 - g.val) * gapJacobianRowFactor nodes g := by
  rw [gapJacobianRowFactor, coordinateNodalValue]
  simp_rw [endpointPoint_eq_endpointArray_point nodes]
  have h := ordered_gap_nodalProduct_sign nodes.point nodes.strictMono g
    (gapArgmax_mem_openGap nodes.toOrderedNodes (by omega) g)
  simpa using h

/-- Exact column-factor sign.  The denominator at interior node `j` has one
negative factor for every node to its right, namely `d-j` factors; inversion
preserves that sign. -/
theorem gapJacobianColumnFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    0 < (-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j := by
  have hden := ordered_basisDenominator_sign nodes.point nodes.strictMono
    (interiorNodeIndex j)
  have hden' : 0 < (-1 : ℝ) ^ (d - j.val) *
      coordinateBasisDenominator A B nodes.interior j := by
    rw [coordinateBasisDenominator]
    simp_rw [endpointPoint_eq_endpointArray_point nodes]
    have hexp : d + 2 - 1 - (interiorNodeIndex j).val = d - j.val := by
      simp only [interiorNodeIndex_val]
      omega
    rw [hexp] at hden
    exact hden
  rw [gapJacobianColumnFactor]
  rcases neg_one_pow_eq_or ℝ (d - j.val) with hs | hs
  · rw [hs] at hden' ⊢
    simp only [one_mul] at hden' ⊢
    exact inv_pos.mpr hden'
  · rw [hs] at hden' ⊢
    simp only [neg_one_mul] at hden' ⊢
    have hneg : coordinateBasisDenominator A B nodes.interior j < 0 := by
      linarith
    exact neg_pos.mpr (inv_lt_zero.mpr hneg)

/-- The total sign contributed to a height-Jacobian minor by all retained row
factors and all column factors. -/
def heightMinorFactorParity (d : ℕ) (omitted : Fin (d + 1)) : ℝ :=
  (∏ i : Fin d, (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val)) *
    ∏ j : Fin d, (-1 : ℝ) ^ (d - j.val)

/-- The explicit row/column factor parity collapses to the ordinary
row-deletion parity `(-1)^omitted`.  Pairing the retained row indexed by
`omitted.succAbove i` with column `i` makes each factor `-1` exactly for
`i < omitted`. -/
lemma heightMinorFactorParity_eq_negOnePow (d : ℕ)
    (omitted : Fin (d + 1)) :
    heightMinorFactorParity d omitted = (-1 : ℝ) ^ omitted.val := by
  classical
  let S : Finset (Fin d) :=
    Finset.univ.filter fun i => i.castSucc < omitted
  have hcard : S.card = omitted.val := by
    calc
      S.card = (Finset.Iio omitted).card := by
        apply Finset.card_bij (fun i _hi => i.castSucc)
        · intro i hi
          simpa [S] using (Finset.mem_filter.mp hi).2
        · intro i _hi j _hj hij
          exact Fin.castSucc_inj.mp hij
        · intro k hk
          have hko : k < omitted := by simpa using hk
          let i : Fin d := ⟨k.val, by
            have ho : omitted.val ≤ d := by omega
            exact lt_of_lt_of_le (Fin.lt_def.mp hko) ho⟩
          refine ⟨i, ?_, ?_⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ i, by simpa [i] using hko⟩
          · ext
            rfl
      _ = omitted.val := Fin.card_Iio omitted
  rw [heightMinorFactorParity, ← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin d,
        (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
          (-1 : ℝ) ^ (d - i.val)) =
        ∏ i : Fin d, if i.castSucc < omitted then (-1 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hio : i.castSucc < omitted
      · rw [if_pos hio, Fin.succAbove_of_castSucc_lt omitted i hio]
        simp only [Fin.val_castSucc]
        have hexp : d + 1 - i.val = (d - i.val) + 1 := by omega
        rw [hexp, pow_succ]
        have hs := sq_negOnePow_v1 (d - i.val)
        nlinarith
      · have hoi : omitted ≤ i.castSucc := le_of_not_gt hio
        rw [if_neg hio, Fin.succAbove_of_le_castSucc omitted i hoi]
        simp only [Fin.val_succ]
        have hexp : d + 1 - (i.val + 1) = d - i.val := by omega
        rw [hexp]
        simpa only [pow_two] using sq_negOnePow_v1 (d - i.val)
    _ = (-1 : ℝ) ^ S.card := by
      rw [← Finset.prod_filter (s := Finset.univ)
        (fun i : Fin d => i.castSucc < omitted) (fun _ => (-1 : ℝ))]
      change (∏ _i ∈ S, (-1 : ℝ)) = (-1 : ℝ) ^ S.card
      simp
    _ = (-1 : ℝ) ^ omitted.val := by rw [hcard]

/-! ## The source normalization and its sign table -/

/-- Row normalization used in the proof following source equations (6)--(7).
The first quotient is negated; every later quotient receives its alternating
row sign.  Consequently all normalized quotients are positive at `τ₀`. -/
def sourceQuotientNormalizer {m : ℕ} (i : Fin (m + 1)) : ℝ :=
  if i = 0 then -1 else (-1 : ℝ) ^ i.val

lemma sourceQuotientNormalizer_ne_zero {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ≠ 0 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact pow_ne_zero _ (by norm_num)

lemma sourceQuotientNormalizer_sq {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ^ 2 = 1 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact sq_negOnePow_v1 i.val

/-- The normalized critical quotient polynomial. -/
def sourceNormalizedQuotient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ[X] :=
  C (sourceQuotientNormalizer i) *
    gapDerivativeQuotient nodes.toOrderedNodes i

lemma natDegree_sourceNormalizedQuotient_le {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (i : Fin (d + 1)) :
    (sourceNormalizedQuotient nodes i).natDegree ≤ d - 1 := by
  have hq := natDegree_gapDerivativeQuotient_le_sub_three
    (n := d + 2) nodes.toOrderedNodes (by omega) i
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)

lemma sourceNormalizedQuotient_eval_first_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    0 < (sourceNormalizedQuotient nodes i).eval
      (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  by_cases hi : i = 0
  · subst i
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer]
      using neg_pos.mpr (htable.1 ⟨0, by omega⟩)
  · have h := htable.2 i ⟨0, by omega⟩ hi
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
      Polynomial.eval_mul, Polynomial.eval_C] using h

lemma sourceNormalizedQuotient_first_eval_later_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (j : Fin (d + 1)) (hj : j ≠ 0) :
    0 < (-1 : ℝ) ^ (j.val + 1) *
      (sourceNormalizedQuotient nodes 0).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 ⟨0, by omega⟩ j hj.symm
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer,
    Polynomial.eval_mul, Polynomial.eval_C, pow_succ] using h

lemma sourceNormalizedQuotient_offDiagonal_eval_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (i j : Fin (d + 1)) (hi : i ≠ 0) (hij : i ≠ j) :
    0 < (-1 : ℝ) ^ j.val *
      (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 i j hij
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
    Polynomial.eval_mul, Polynomial.eval_C, pow_add, mul_assoc,
    mul_left_comm, mul_comm] using h

/-! ## The de Boor--Pinkus sign-variation relation argument -/

private def negativeLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => a i < 0

private def positiveLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => 0 < a i

private lemma sum_eq_first_add_negative_add_positive {d : ℕ}
    (a v : Fin (d + 1) → ℝ) :
    (∑ i, a i * v i) =
      a 0 * v 0 +
        ∑ i ∈ negativeLaterIndices a, a i * v i +
          ∑ i ∈ positiveLaterIndices a, a i * v i := by
  classical
  let I : Finset (Fin (d + 1)) := Finset.univ.erase 0
  let N := negativeLaterIndices a
  let P := positiveLaterIndices a
  have hNsub : N ⊆ I := Finset.filter_subset _ _
  have hPsub : P ⊆ I := Finset.filter_subset _ _
  have hdis : Disjoint N P := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiN hiP
    have hneg : a i < 0 := (Finset.mem_filter.mp hiN).2
    have hpos : 0 < a i := (Finset.mem_filter.mp hiP).2
    linarith
  have hcover :
      (∑ i ∈ N ∪ P, a i * v i) = ∑ i ∈ I, a i * v i := by
    apply Finset.sum_subset (Finset.union_subset hNsub hPsub)
    intro i hiI hiNP
    have hiN : i ∉ N := fun h => hiNP (Finset.mem_union_left P h)
    have hiP : i ∉ P := fun h => hiNP (Finset.mem_union_right N h)
    have hnneg : ¬a i < 0 := by
      intro h
      exact hiN (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hnpos : ¬0 < a i := by
      intro h
      exact hiP (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hai : a i = 0 := le_antisymm (le_of_not_gt hnpos) (le_of_not_gt hnneg)
    simp [hai]
  rw [Finset.sum_union hdis] at hcover
  have herase := Finset.sum_erase_add Finset.univ (fun i => a i * v i)
    (Finset.mem_univ (0 : Fin (d + 1)))
  change (∑ i ∈ I, a i * v i) + a 0 * v 0 = ∑ i, a i * v i at herase
  rw [← herase, ← hcover]
  dsimp only [N, P]
  ring

/-- In any nonzero polynomial relation among the normalized quotients, every
coefficient is nonzero.  This is the precise source conclusion needed for
all row-deleted families: a relation missing one row is therefore trivial. -/
theorem sourceNormalizedQuotient_relation_sign_pattern {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    (0 < a 0 ∧ ∀ i, i ≠ 0 → a i < 0) ∨
      (a 0 < 0 ∧ ∀ i, i ≠ 0 → 0 < a i) := by
  classical
  let orient : ℝ := if 0 ≤ a 0 then 1 else -1
  let b : Fin (d + 1) → ℝ := fun i => orient * a i
  have horient : orient = 1 ∨ orient = -1 := by
    dsimp [orient]
    split <;> simp
  have horient_ne : orient ≠ 0 := by
    rcases horient with h | h <;> rw [h] <;> norm_num
  have hbfirst : 0 ≤ b 0 := by
    dsimp [b, orient]
    split_ifs with h
    · simpa using h
    · have hlt : a 0 < 0 := lt_of_not_ge h
      simp only [neg_one_mul]
      exact neg_nonneg.mpr hlt.le
  have hbne : b ≠ 0 := by
    intro hb
    apply ha
    funext i
    have hi := congrFun hb i
    dsimp [b] at hi
    exact (mul_eq_zero.mp hi).resolve_left horient_ne
  have hbrel : (∑ i, C (b i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (b i) * sourceNormalizedQuotient nodes i) =
          C orient * (∑ i, C (a i) * sourceNormalizedQuotient nodes i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [b, map_mul]
            ring
      _ = 0 := by rw [hrel, mul_zero]
  have hbrel_eval (x : ℝ) :
      (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) = 0 := by
    have h := congrArg (Polynomial.eval x) hbrel
    simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero] using h
  let N := negativeLaterIndices b
  let P := positiveLaterIndices b
  have hN : N.Nonempty := by
    by_contra hNempty
    rw [Finset.not_nonempty_iff_eq_empty] at hNempty
    have hbnonneg (i : Fin (d + 1)) : 0 ≤ b i := by
      by_cases hi : i = 0
      · simpa [hi] using hbfirst
      · apply le_of_not_gt
        intro hneg
        have hiN : i ∈ N := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hneg⟩
        rw [hNempty] at hiN
        simp at hiN
    obtain ⟨i, hbi⟩ := Function.ne_iff.mp hbne
    have hbipos : 0 < b i := lt_of_le_of_ne (hbnonneg i) (Ne.symm hbi)
    have hterm_nonneg (k : Fin (d + 1)) :
        0 ≤ b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_nonneg (hbnonneg k)
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) k).le
    have hterm_pos :
        0 < b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_pos hbipos
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
    have hsumpos : 0 <
        ∑ k, b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      rw [Finset.sum_pos_iff_of_nonneg (fun k _hk => hterm_nonneg k)]
      exact ⟨i, Finset.mem_univ i, hterm_pos⟩
    rw [hbrel_eval] at hsumpos
    exact (lt_irrefl 0) hsumpos
  -- The source's auxiliary polynomial: first row plus all negatively
  -- weighted later rows.
  let f : ℝ[X] := C (b 0) * sourceNormalizedQuotient nodes 0 +
    ∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i
  have hf_eval (x : ℝ) : f.eval x =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x := by
    simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finset_sum]
  have hf_eval_eq_neg_pos (x : ℝ) : f.eval x =
      -∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x := by
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval x)
    have hzero := hbrel_eval x
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x +
          ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x at hsplit
    rw [hf_eval]
    linarith
  have hNmem {i : Fin (d + 1)} (hi : i ∈ N) : i ≠ 0 ∧ b i < 0 := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hPmem {i : Fin (d + 1)} (hi : i ∈ P) : i ≠ 0 ∧ 0 < b i := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hfzero : f = 0 := by
    by_cases hP : P.Nonempty
    · have hf_sign (j : Fin (d + 1)) :
          0 < (-1 : ℝ) ^ (j.val + 1) * f.eval
            (gapArgmax nodes.toOrderedNodes j) := by
        by_cases hj0 : j = 0
        · subst j
          have hsumpos : 0 < ∑ i ∈ P,
              b i * (sourceNormalizedQuotient nodes i).eval
                (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
            apply Finset.sum_pos
            · intro i hi
              exact mul_pos (hPmem hi).2
                (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
            · exact hP
          rw [hf_eval_eq_neg_pos]
          simpa using hsumpos
        · by_cases hjP : j ∈ P
          · have hfirst : 0 ≤
                b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                  (sourceNormalizedQuotient nodes 0).eval
                    (gapArgmax nodes.toOrderedNodes j)) :=
              mul_nonneg hbfirst
                (sourceNormalizedQuotient_first_eval_later_sign
                  nodes (by omega) j hj0).le
            have hNsum : 0 < ∑ i ∈ N,
                (-1 : ℝ) ^ (j.val + 1) *
                  (b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j)) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hNmem hi).1
                have hibneg := (hNmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  linarith [hibneg, (hPmem hjP).2]
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < (-b i) * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) :=
                    mul_pos (neg_pos.mpr hibneg) hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                    rw [pow_succ]
                    ring
              · exact hN
            rw [hf_eval]
            calc
              0 < b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                    (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j)) +
                  ∑ i ∈ N, (-1 : ℝ) ^ (j.val + 1) *
                    (b i * (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) :=
                add_pos_of_nonneg_of_pos hfirst hNsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (b 0 * (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j) +
                    ∑ i ∈ N, b i *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                ring
          · have hjnotpos : ¬0 < b j := by
              intro hjpos
              exact hjP (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩, hjpos⟩)
            have hPsum : 0 < ∑ i ∈ P,
                (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hPmem hi).1
                have hibpos := (hPmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  exact hjnotpos hibpos
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < b i * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := mul_pos hibpos hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (-(b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j))) := by
                    rw [pow_succ]
                    ring
              · exact hP
            rw [hf_eval_eq_neg_pos]
            calc
              0 < ∑ i ∈ P, (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := hPsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (-∑ i ∈ P, b i *
                    (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                congr 1
                rw [← Finset.sum_neg_distrib]
      apply eq_zero_of_eval_mul_next_neg f
          (gapArgmax nodes.toOrderedNodes)
          (gapArgmax_strictMono nodes.toOrderedNodes (by omega))
      · have hfirstDegree :
            (C (b 0) * sourceNormalizedQuotient nodes 0).natDegree ≤ d - 1 :=
          (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd 0)
        have hsumDegree :
            (∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i).natDegree ≤
              d - 1 := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i hi
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd i)
        exact (Polynomial.natDegree_add_le _ _).trans_lt (by omega)
      · intro j
        have hleft := hf_sign j.castSucc
        have hright := hf_sign j.succ
        simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
        rw [show j.val + 1 + 1 = (j.val + 1) + 1 by omega, pow_succ] at hright
        nlinarith [sq_negOnePow_v1 (j.val + 1)]
    · apply Polynomial.funext
      have heval : ∀ x : ℝ, f.eval x = 0 := by
        intro x
        rw [hf_eval_eq_neg_pos]
        rw [Finset.not_nonempty_iff_eq_empty.mp hP]
        simp
      intro x
      simpa using heval x
  have hPempty : P = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hP
    have hsumpos : 0 < ∑ i ∈ P,
        b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      apply Finset.sum_pos
      · intro i hi
        exact mul_pos (hPmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hP
    have hf0 := congrArg
      (fun p : ℝ[X] => p.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) hfzero
    have hf0' : f.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) = 0 := by
      simpa only [Polynomial.eval_zero] using hf0
    rw [hf_eval_eq_neg_pos] at hf0'
    linarith
  have hblater (i : Fin (d + 1)) (hi0 : i ≠ 0) : b i ≠ 0 := by
    intro hbi
    have hiP : i ∉ P := by rw [hPempty]; simp
    have hibnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hiP (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩, hpos⟩)
    have hiN : i ∉ N := by
      intro hiN
      exact (hNmem hiN).2.ne hbi
    have hfirst : 0 ≤ b 0 * ((-1 : ℝ) ^ (i.val + 1) *
        (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes i)) :=
      mul_nonneg hbfirst
        (sourceNormalizedQuotient_first_eval_later_sign
          nodes (by omega) i hi0).le
    have hNsum : 0 < ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
        (b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes i)) := by
      apply Finset.sum_pos
      · intro k hk
        have hk0 := (hNmem hk).1
        have hkbneg := (hNmem hk).2
        have hki : k ≠ i := by
          intro hki
          subst k
          exact hiN hk
        have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
          nodes (by omega) k i hk0 hki
        calc
          0 < (-b k) * ((-1 : ℝ) ^ i.val *
              (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
            mul_pos (neg_pos.mpr hkbneg) hq
          _ = (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
            rw [pow_succ]
            ring
      · exact hN
    have hfpos : 0 < (-1 : ℝ) ^ (i.val + 1) *
        f.eval (gapArgmax nodes.toOrderedNodes i) := by
      rw [hf_eval]
      calc
        0 < b 0 * ((-1 : ℝ) ^ (i.val + 1) *
              (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i)) +
            ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
          add_pos_of_nonneg_of_pos hfirst hNsum
        _ = (-1 : ℝ) ^ (i.val + 1) *
            (b 0 * (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i) +
              ∑ k ∈ N, b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
          rw [← Finset.mul_sum]
          ring
    rw [hfzero] at hfpos
    simp at hfpos
  have hbzero : b 0 ≠ 0 := by
    intro hb0
    have hNsumneg :
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) < 0 := by
      apply Finset.sum_neg
      · intro i hi
        exact mul_neg_of_neg_of_pos (hNmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hN
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩))
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) at hsplit
    rw [hbrel_eval, hb0, hPempty] at hsplit
    simp at hsplit
    exact (ne_of_lt hNsumneg) hsplit.symm
  have hbfirstpos : 0 < b 0 := lt_of_le_of_ne hbfirst (Ne.symm hbzero)
  have hblaterneg (i : Fin (d + 1)) (hi : i ≠ 0) : b i < 0 := by
    have hnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have hiP : i ∈ P := Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hpos⟩
      rw [hPempty] at hiP
      simp at hiP
    exact lt_of_le_of_ne hnonpos (hblater i hi)
  rcases horient with horient | horient
  · left
    constructor
    · simpa [b, horient] using hbfirstpos
    · intro i hi
      simpa [b, horient] using hblaterneg i hi
  · right
    constructor
    · have := hbfirstpos
      simp only [b, horient, neg_one_mul] at this
      linarith
    · intro i hi
      have := hblaterneg i hi
      simp only [b, horient, neg_one_mul] at this
      linarith

theorem sourceNormalizedQuotient_relation_coeff_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    ∀ i, a i ≠ 0 := by
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel ha with
    h | h
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_gt h.1
    · exact ne_of_lt (h.2 i hi)
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_lt h.1
    · exact ne_of_gt (h.2 i hi)

/-! ## From the relation theorem to maximal minors -/

/-- Transpose-oriented evaluation matrix for the normalized polynomials in
the row-deleted family.  Rows are interior nodes and columns are retained gap
quotients. -/
def normalizedDeletedQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j i => (sourceNormalizedQuotient nodes (omitted.succAbove i)).eval
    (nodes.point (interiorNodeIndex j))

theorem normalizedDeletedQuotientEvaluationMatrix_det_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : ℝ[X] := ∑ i : Fin d,
    C (c i) * sourceNormalizedQuotient nodes (omitted.succAbove i)
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (natDegree_sourceNormalizedQuotient_le nodes hd _)
    omega
  have hp_eval (j : Fin d) : p.eval (nodes.point (interiorNodeIndex j)) = 0 := by
    have hj := congrFun hc j
    simp only [normalizedDeletedQuotientEvaluationMatrix, Matrix.mulVec,
      dotProduct, p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Pi.zero_apply] at hj ⊢
    simpa only [mul_comm] using hj
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  have hpzero : p = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
    · rw [hs_card]
      exact Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr hpdegree)
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
      exact hp_eval j
  let a : Fin (d + 1) → ℝ :=
    Fin.succAboveCases (α := fun _ => ℝ) omitted 0 c
  have harel :
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    rw [Fin.sum_univ_succAbove
      (fun i => C (a i) * sourceNormalizedQuotient nodes i) omitted]
    simp [a]
    exact hpzero
  have hane : a ≠ 0 := by
    intro ha
    apply hcne
    funext i
    have hi := congrFun ha (omitted.succAbove i)
    simpa [a] using hi
  have hall := sourceNormalizedQuotient_relation_coeff_ne_zero
    nodes hd a harel hane omitted
  exact hall (by simp [a])

/-- Row normalization is exactly diagonal scaling of the transposed deleted
quotient-evaluation matrix. -/
lemma normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).transpose =
      Matrix.diagonal
        (fun i => sourceQuotientNormalizer (omitted.succAbove i)) *
      (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id := by
  ext i j
  simp [normalizedDeletedQuotientEvaluationMatrix, sourceNormalizedQuotient,
    gapQuotientEvaluationMatrix, Matrix.diagonal_mul]

theorem deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0 := by
  have hnormalized :=
    normalizedDeletedQuotientEvaluationMatrix_det_ne_zero nodes hd omitted
  have hfactor := congrArg Matrix.det
    (normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
      nodes omitted)
  rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal] at hfactor
  have hnormalizer :
      (∏ i : Fin d, sourceQuotientNormalizer (omitted.succAbove i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi => sourceQuotientNormalizer_ne_zero _
  rw [deletedRowMinor]
  intro hminor
  rw [hminor, mul_zero] at hfactor
  exact hnormalized hfactor

theorem quotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    QuotientEvaluationMaximalMinorsNonzero nodes := by
  intro omitted
  by_cases hd0 : d = 0
  · subst d
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    rw [deletedRowMinor]
    have hentry := gapDerivativeQuotient_eval_neg_of_three_nodes
      nodes.toOrderedNodes (omitted.succAbove 0)
        (nodes.point (interiorNodeIndex 0))
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      (ne_of_lt hentry)
  · exact deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
      nodes (by omega) omitted

/-! ## Coherent signs of all row-deleted minors -/

/-- The signed maximal minor which occurs in the usual left-kernel cofactor
vector of a `(d+1)×d` matrix. -/
def gapQuotientCofactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ :=
  (-1 : ℝ) ^ i.val *
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) i

/-- Square augmentation of the quotient matrix by a duplicate of column
`j`.  Its determinant vanishes, and expansion down column zero gives the
cofactor relation. -/
private def duplicateQuotientColumnMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases (gapQuotientEvaluationMatrix nodes i j)
    (fun k' => gapQuotientEvaluationMatrix nodes i k') k

lemma gapQuotientCofactor_evaluation_sum_eq_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    ∑ i : Fin (d + 1), gapQuotientCofactor nodes i *
      gapQuotientEvaluationMatrix nodes i j = 0 := by
  let M := duplicateQuotientColumnMatrix nodes j
  have hcols : ∀ i, M i 0 = M i j.succ := by
    intro i
    simp [M, duplicateQuotientColumnMatrix]
  have hne : (0 : Fin (d + 1)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hdet : M.det = 0 := Matrix.det_zero_of_column_eq hne hcols
  have hexpand := Matrix.det_succ_column M (0 : Fin (d + 1))
  rw [hdet] at hexpand
  have hminor (i : Fin (d + 1)) :
      (M.submatrix i.succAbove (0 : Fin (d + 1)).succAbove).det =
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) i := by
    rw [deletedRowMinor]
    congr 1
  simp only [Fin.val_zero, Nat.add_zero, M, duplicateQuotientColumnMatrix,
    Fin.cases_zero, hminor] at hexpand
  simpa [gapQuotientCofactor, mul_assoc, mul_left_comm, mul_comm] using
    hexpand.symm

theorem gapQuotientCofactor_polynomial_relation {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
      gapDerivativeQuotient nodes.toOrderedNodes i) = 0 := by
  let p : ℝ[X] := ∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
    gapDerivativeQuotient nodes.toOrderedNodes i
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (by
          have hq := natDegree_gapDerivativeQuotient_le_sub_three
            (n := d + 2) nodes.toOrderedNodes (by omega) i
          omega)
    omega
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  change p = 0
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hpdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact gapQuotientCofactor_evaluation_sum_eq_zero nodes j

/-- The source relation theorem applied to the cofactor relation.  In raw
row convention, the cofactor coefficients alternate strictly. -/
theorem gapQuotientCofactor_alternating_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∀ i : Fin (d + 1),
      (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i < 0) ∨
    (∀ i : Fin (d + 1),
      0 < (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i) := by
  let a : Fin (d + 1) → ℝ := fun i =>
    sourceQuotientNormalizer i * gapQuotientCofactor nodes i
  have hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) =
          ∑ i, C (gapQuotientCofactor nodes i) *
            gapDerivativeQuotient nodes.toOrderedNodes i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [sourceNormalizedQuotient]
        have hs := sourceQuotientNormalizer_sq i
        change C (sourceQuotientNormalizer i * gapQuotientCofactor nodes i) *
            (C (sourceQuotientNormalizer i) *
              gapDerivativeQuotient nodes.toOrderedNodes i) = _
        rw [← mul_assoc, ← map_mul]
        congr 2
        calc
          sourceQuotientNormalizer i * gapQuotientCofactor nodes i *
              sourceQuotientNormalizer i =
              gapQuotientCofactor nodes i *
                sourceQuotientNormalizer i ^ 2 := by ring
          _ = gapQuotientCofactor nodes i := by rw [hs, mul_one]
      _ = 0 := gapQuotientCofactor_polynomial_relation nodes hd
  have hane : a ≠ 0 := by
    intro ha
    have h0 := congrFun ha (0 : Fin (d + 1))
    have hc0 := quotientEvaluationMaximalMinorsNonzero nodes (0 : Fin (d + 1))
    have hcofactor0 : gapQuotientCofactor nodes 0 ≠ 0 := by
      simpa [gapQuotientCofactor] using hc0
    dsimp [a] at h0
    exact hcofactor0 ((mul_eq_zero.mp h0).resolve_left
      (sourceQuotientNormalizer_ne_zero 0))
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel hane with
    hneg | hpos
  · left
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hneg
      simpa using hneg.1
    · have hi' := hneg.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'
  · right
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hpos
      simpa using hpos.1
    · have hi' := hpos.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'

/-- All raw row-deleted quotient-evaluation minors have one coherent strict
sign.  This is stronger than pointwise nonvanishing and is the orientation
input needed by the consecutive-gap-difference Jacobian. -/
theorem gapQuotientEvaluation_deletedRowMinors_coherent_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) :
    (∀ omitted : Fin (d + 1),
      deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted < 0) ∨
    (∀ omitted : Fin (d + 1),
      0 < deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted) := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    left
    intro omitted
    rw [deletedRowMinor]
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      gapDerivativeQuotient_eval_neg_of_three_nodes nodes.toOrderedNodes
        (omitted.succAbove 0) (nodes.point (interiorNodeIndex 0))
  · rcases gapQuotientCofactor_alternating_sign nodes (by omega) with
      hneg | hpos
    · left
      intro omitted
      have h := hneg omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow_v1 omitted.val]
    · right
      intro omitted
      have h := hpos omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow_v1 omitted.val]

/-! ## Transfer to the height Jacobian and consecutive differences -/

/-- The explicit diagonal row/column factor multiplying a quotient minor has
the row-deletion sign `(-1)^omitted`. -/
theorem gapHeightMinor_diagonalFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (omitted : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ omitted.val *
      ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by
  have hrow : 0 < ∏ i : Fin d,
      ((-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
        gapJacobianRowFactor nodes (omitted.succAbove i)) := by
    apply Finset.prod_pos
    intro i _hi
    exact gapJacobianRowFactor_parity_pos nodes hd _
  have hcol : 0 < ∏ j : Fin d,
      ((-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j) := by
    apply Finset.prod_pos
    intro j _hj
    exact gapJacobianColumnFactor_parity_pos nodes j
  have hboth := mul_pos hrow hcol
  rw [← heightMinorFactorParity_eq_negOnePow d omitted]
  simpa [heightMinorFactorParity, Finset.prod_mul_distrib, mul_assoc,
    mul_left_comm, mul_comm] using hboth

/-- Coherent orientation of all height-Jacobian maximal minors.  The
row-deletion cofactor signs, rather than the bare minors, are equal: they are
all strictly negative or all strictly positive. -/
def AlternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  (∀ omitted : Fin (d + 1),
      (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted < 0) ∨
  (∀ omitted : Fin (d + 1),
      0 < (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted)

theorem alternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    AlternatingHeightMaximalMinorSigns nodes := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor_zero_dim]
  have hd : 1 ≤ d := by omega
  rcases gapQuotientEvaluation_deletedRowMinors_coherent_sign nodes with
    hqneg | hqpos
  · left
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqneg omitted
    calc
      (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) =
          ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted := by ring
      _ < 0 := mul_neg_of_pos_of_neg hfactor hq
  · right
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqpos omitted
    calc
      0 < ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted :=
        mul_pos hfactor hq
      _ = (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by ring

/-- Adjoin a leading column of ones to the rectangular height Jacobian.  Its
first-column cofactors are exactly the signed height maximal minors. -/
def augmentedGapHeightJacobianMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases 1 (fun j => gapHeightJacobianModel nodes i j) k

/-- The augmented determinant has the common strict cofactor sign. -/
theorem augmentedGapHeightJacobianMatrix_det_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det < 0 ∨
      0 < (augmentedGapHeightJacobianMatrix nodes).det := by
  have hexpand := Matrix.det_succ_column_zero
    (augmentedGapHeightJacobianMatrix nodes)
  simp only [augmentedGapHeightJacobianMatrix, Fin.cases_zero, mul_one] at hexpand
  rcases alternatingHeightMaximalMinorSigns nodes with hneg | hpos
  · left
    rw [hexpand]
    apply Finset.sum_neg
    · intro i _hi
      exact hneg i
    · exact Finset.univ_nonempty
  · right
    rw [hexpand]
    apply Finset.sum_pos
    · intro i _hi
      exact hpos i
    · exact Finset.univ_nonempty

theorem augmentedGapHeightJacobianMatrix_det_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det ≠ 0 := by
  rcases augmentedGapHeightJacobianMatrix_det_sign nodes with h | h
  · exact ne_of_lt h
  · exact ne_of_gt h

/-- The actual consecutive-row-difference matrix is nonsingular.  The proof
uses the augmented determinant: a kernel vector for all consecutive
differences would make all height-row evaluations equal, hence extend to a
nonzero kernel vector of the augmented matrix. -/
theorem gapHeightJacobianModel_consecutiveDifference_det_ne_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Matrix.det (fun i j : Fin d =>
      gapHeightJacobianModel nodes i.succ j -
        gapHeightJacobianModel nodes i.castSucc j) ≠ 0 := by
  classical
  intro hdet
  let D : Matrix (Fin d) (Fin d) ℝ := fun i j =>
    gapHeightJacobianModel nodes i.succ j -
      gapHeightJacobianModel nodes i.castSucc j
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (show D.det = 0 from hdet)
  let rowValue : Fin (d + 1) → ℝ := fun i =>
    ∑ j : Fin d, gapHeightJacobianModel nodes i j * v j
  have hadj (i : Fin d) : rowValue i.succ = rowValue i.castSucc := by
    have hi := congrFun hv i
    simp only [D, Matrix.mulVec, dotProduct, Pi.zero_apply, rowValue] at hi ⊢
    simp_rw [sub_mul] at hi
    rw [Finset.sum_sub_distrib] at hi
    linarith
  have hconst (i : Fin (d + 1)) : rowValue i = rowValue 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).trans ih
  let w : Fin (d + 1) → ℝ :=
    Fin.cases (-(rowValue 0)) v
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    funext j
    have hj := congrFun hw j.succ
    simpa [w] using hj
  have hAw : (augmentedGapHeightJacobianMatrix nodes).mulVec w = 0 := by
    funext i
    rw [show (augmentedGapHeightJacobianMatrix nodes).mulVec w i =
        -(rowValue 0) + rowValue i by
      simp [Matrix.mulVec, dotProduct, augmentedGapHeightJacobianMatrix,
        w, Fin.sum_univ_succ, rowValue]]
    rw [hconst i]
    simp
  have hA0 : (augmentedGapHeightJacobianMatrix nodes).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hAw⟩
  exact (augmentedGapHeightJacobianMatrix_det_ne_zero nodes) hA0

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Statement.lean` -/

/-!
# Exact de Boor--Pinkus theorem interfaces (unproved propositions)

This file fixes the statements that the later source formalization must
prove.  It does **not** assert them as theorems or axioms.  Each boss result is
a definition of a proposition; an eventual theorem must construct a term of
that proposition from the interlacing, Jacobian, boundary, and global
topology developed in subsequent modules.

With `d` interior nodes there are `d + 1` gap heights.  The source's map
`Γ` has `d` coordinates, formed by consecutive height differences.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Consecutive gap-height differences, the map called `Γ` in the plan and
`Γ`/`r` (depending on OCR) in source Theorem 1. -/
def gapDifference {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.height i.succ - nodes.height i.castSucc

/-- All gap heights of an endpoint-fixed array agree. -/
def Equioscillates {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Prop :=
  ∀ i j : Fin (d + 1), nodes.height i = nodes.height j

/-- Source Theorem 1 in the topology induced by the interior coordinates.

This is only a proposition definition.  In particular, no local-Jacobian
claim is being silently promoted to a global homeomorphism. -/
def GapDifferenceHomeomorphismStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    IsHomeomorph (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Exact coordinatewise comparison/rigidity statement from source Theorem 2.
The polarity is important: if every gap of `s` is no higher than the
corresponding gap of `t`, the arrays are equal. -/
def GapHeightLeRigidityStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ s t : EndpointArray d A B,
    (∀ i : Fin (d + 1), s.height i ≤ t.height i) → s = t

/-- Exact existence and uniqueness interface for the equioscillating
endpoint array. -/
def ExistsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    ∃! nodes : EndpointArray d A B, Equioscillates nodes

/-- The only source package consumed by the later block-collapse bridge.
Keeping it as a structure makes dependency status explicit: no inhabitant is
provided in this declaration file. -/
structure ComparisonPackage (d : ℕ) (A B : ℝ) : Prop where
  gapHeight_le_rigidity : GapHeightLeRigidityStatement d A B
  exists_unique_equioscillating : ExistsUniqueEquioscillatingStatement d A B

/-!
The eventual exported theorem surface, once proved, is deliberately reserved
to have the following shapes:

```lean
theorem gapDifference_homeomorph :
    GapDifferenceHomeomorphismStatement d A B

theorem gapHeight_le_rigidity :
    GapHeightLeRigidityStatement d A B

theorem exists_unique_equioscillating :
    ExistsUniqueEquioscillatingStatement d A B
```

No declaration with one of these theorem names appears here, so downstream
code cannot consume an unproved boss result.
-/

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Boundary.lean` -/

/-!
# The de Boor--Pinkus boundary kernel

Lemma 4 of de Boor--Pinkus (1978) considers two consecutive nodal gaps, the
upper of which collapses while the lower stays nondegenerate.  At the midpoint
of the lower gap, every cardinal function dominates its value throughout the
collapsing gap by one common factor tending to infinity.  Summing absolute
values compares the two gap heights and forces the corresponding coordinate
of `gapDifference` to tend to minus infinity.

This file isolates the exact, source-faithful implication from common-point
cardinal domination to gap-height divergence.  In particular, it does **not**
use the tempting but false shortcut that the ratio of the two cardinal
polynomials belonging to colliding nodes must diverge; that ratio can tend to
`-1`.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Filter

noncomputable section

/-! ## Transport and summation -/

/-- Exact product transport of a cardinal function between two nonnodal
points.  This is the algebraic identity used in the displayed estimate in
source Lemma 4; importantly, it transports one cardinal function between two
points, rather than comparing two cardinal functions at colliding nodes. -/
lemma lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    lagrangeFundamental nodes k y =
      lagrangeFundamental nodes k x *
        ∏ j ∈ Finset.univ.erase k,
          ((y - nodes.point j) / (x - nodes.point j)) := by
  classical
  unfold lagrangeFundamental
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hxj : x - nodes.point j ≠ 0 := sub_ne_zero.mpr (hx j hjk)
  field_simp

/-- Absolute-value form of `lagrangeFundamental_eval_transport`. -/
lemma abs_lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    |lagrangeFundamental nodes k y| =
      |lagrangeFundamental nodes k x| *
        ∏ j ∈ Finset.univ.erase k,
          |(y - nodes.point j) / (x - nodes.point j)| := by
  rw [lagrangeFundamental_eval_transport nodes k hx, abs_mul,
    Finset.abs_prod]

/-- A common pointwise cardinal amplification survives summation and hence
amplifies the whole Lebesgue function. -/
lemma mul_le_lebesgueFunction_of_cardinal_domination {n : ℕ}
    (nodes : NodeFamily n) {K x y : ℝ}
    (hdom : ∀ k : Fin n,
      K * |lagrangeFundamental nodes k x| ≤
        |lagrangeFundamental nodes k y|) :
    K * lebesgueFunction nodes x ≤ lebesgueFunction nodes y := by
  classical
  simp only [lebesgueFunction, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ hdom k

/-! ## Compact gap maxima -/

/-- Every endpoint-array Lebesgue function is at least one. -/
lemma one_le_lebesgueFunction_endpointArray {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (x : ℝ) :
    1 ≤ lebesgueFunction nodes.toNodeFamily x := by
  have hsum :
      ∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x = 1 :=
    sum_lagrangeFundamental_eq_one nodes.toOrderedNodes (by omega) x
  calc
    1 = |∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x| := by rw [hsum, abs_one]
    _ ≤ ∑ k : Fin (d + 2),
        |lagrangeFundamental nodes.toNodeFamily k x| := Finset.abs_sum_le_sum_abs _ _
    _ = lebesgueFunction nodes.toNodeFamily x := rfl

/-- A gap height bounds the Lebesgue function at every point of its closed
gap. -/
lemma lebesgueFunction_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) {x : ℝ}
    (hx : x ∈ closedGap nodes.toOrderedNodes g) :
    lebesgueFunction nodes.toNodeFamily x ≤ nodes.height g := by
  obtain ⟨t, ht, heq, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  exact (hmax x hx).trans_eq heq.symm

/-- Every compact gap height is at least one. -/
lemma one_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    1 ≤ nodes.height g := by
  exact (one_le_lebesgueFunction_endpointArray nodes
    (nodes.point (gapLeftIndex g))).trans
      (lebesgueFunction_le_height nodes g
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩)

/-- With at least three nodes, every gap height is strictly greater than one.
This ensures that a maximizer cannot be either nodal endpoint. -/
lemma one_lt_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    1 < nodes.height g := by
  obtain ⟨x, hx⟩ := openGap_nonempty nodes.toOrderedNodes g
  have hxClosed : x ∈ closedGap nodes.toOrderedNodes g := ⟨hx.1.le, hx.2.le⟩
  have hpoly := one_lt_eval_gapPolynomial_of_mem_openGap
    nodes.toOrderedNodes (by omega) g hx
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hxClosed] at hpoly
  exact hpoly.trans_le (lebesgueFunction_le_height nodes g hxClosed)

/-- For an endpoint array with an interior node, the compact maximum on each
gap is attained in its open interior. -/
lemma exists_height_eq_lebesgueFunction_mem_openGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ∃ x ∈ openGap nodes.toOrderedNodes g,
      nodes.height g = lebesgueFunction nodes.toNodeFamily x := by
  obtain ⟨x, hx, heq, _hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  have hheight : 1 < nodes.height g := one_lt_height nodes hd g
  have hleft : x ≠ nodes.point (gapLeftIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapLeftIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_left]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  have hright : x ≠ nodes.point (gapRightIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapRightIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨(gap_left_lt_right nodes.toOrderedNodes g).le, le_rfl⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_right]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 hleft.symm,
    lt_of_le_of_ne hx.2 hright⟩, heq⟩

/-! ## The finite-radius boundary estimate -/

/-- The exact cardinal-domination premise extracted from source Lemma 4 for
two consecutive gaps.  `y` is the source's fixed point `t-hat` in the lower
gap; the quantifier over `x` is uniform over the collapsing upper gap.

This is a definition, not an assertion that the source's product estimate has
already been discharged. -/
def AdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.castSucc,
    ∀ x ∈ openGap nodes.toOrderedNodes q.succ,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|

/-- Midpoint of the noncollapsing lower neighbor used in source Lemma 4. -/
def boundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.castSucc) +
    nodes.point (gapRightIndex q.castSucc)) / 2

/-- The explicit finite-radius amplification obtained from the source product
argument.  We use the fixed interval length `B - A` in the harmless bounded
factors, rather than the slightly sharper local two-gap length printed in the
paper. -/
def boundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.castSucc /
      (2 * endpointSpacing nodes q.succ)) *
    (endpointSpacing nodes q.castSucc / (2 * (B - A))) ^ d

lemma boundary_common_index {d : ℕ} (q : Fin d) :
    gapRightIndex (n := d + 2) q.castSucc =
      gapLeftIndex (n := d + 2) q.succ := by
  apply Fin.ext
  rfl

lemma boundaryMidpoint_mem_lowerGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    boundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.castSucc := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  constructor <;> unfold boundaryMidpoint <;> linarith

/-- A point in the open upper gap is not any interpolation node. -/
lemma upperGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val + 1
  · have hjCommon : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have := (nodes.strictMono.monotone hjCommon).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)

/-- Every node is at least half of the lower-gap length away from its
midpoint.  Adjacency is what makes this uniform in the node index. -/
lemma half_lowerSpacing_le_midpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / 2 ≤
      |boundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ boundaryMidpoint nodes q - nodes.point j := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing boundaryMidpoint
    linarith
  · have hcommonj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hcommonj
    have hnonpos : boundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing boundaryMidpoint
    linarith

/-- Distances between an upper-gap point and any endpoint-array node are
bounded by the fixed interval length. -/
lemma upperGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.succ) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.succ) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith

private lemma half_div_le_div_of_bounds {L D a b : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hb : 0 < b)
    (ha : L / 2 ≤ a) (hbD : b ≤ D) :
    L / (2 * D) ≤ a / b := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hD) hb]
  have h₁ : L * b ≤ L * D := mul_le_mul_of_nonneg_left hbD hL
  have h₂ : (2 * D) * (L / 2) ≤ (2 * D) * a :=
    mul_le_mul_of_nonneg_left ha (mul_pos (by norm_num) hD).le
  nlinarith

/-- Uniform bounded-factor estimate in the source product. -/
lemma boundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / (2 * (B - A)) ≤
      |(boundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (upperGap_point_ne_node nodes q hx j))
  · exact half_lowerSpacing_le_midpoint_distance nodes q j
  · exact upperGap_distance_le_intervalLength nodes q hx j

/-- The factor belonging to the common node contains the full reciprocal
collapsing-spacing growth. -/
lemma boundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [boundary_common_index q]
    rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]

/-- The factor belonging to the right endpoint of the collapsing gap has the
same reciprocal-spacing lower bound. -/
lemma boundary_ratio_le_upperRight_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q - nodes.point (gapRightIndex q.succ)) /
        (x - nodes.point (gapRightIndex q.succ))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.succ)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q (gapRightIndex q.succ)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]

/-- For every cardinal row, at least one of the two factors adjacent to the
collapsing gap survives deletion of that cardinal's own node. -/
lemma exists_boundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.castSucc /
          (2 * endpointSpacing nodes q.succ) ≤
        |(boundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapRightIndex q.succ, ?_,
      boundary_ratio_le_upperRight_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.succ).ne
    rw [← boundary_common_index q, hk, h]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      boundary_ratio_le_common_factor nodes q hx⟩

/-- Product form of the displayed estimate in source Lemma 4.  One of the
two collision factors supplies the reciprocal upper spacing; the other `d`
factors are bounded below using the fixed interval length. -/
lemma boundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    boundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(boundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(boundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.castSucc / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.castSucc /
    (2 * endpointSpacing nodes q.succ)
  obtain ⟨r, hrs, hrR⟩ := exists_boundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact boundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.castSucc).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by
    rwa [hcard] at hpow
  have hrR' : R ≤ f r := hrR
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR' (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [boundaryAmplification, s, f, c, R] using hprod

/-- The explicit source product estimate supplies the precise common
cardinal amplification premise needed by the finite-radius height lemma. -/
theorem adjacentCardinalAmplification_boundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    AdjacentCardinalAmplification nodes q (boundaryAmplification nodes q) := by
  refine ⟨boundaryMidpoint nodes q, boundaryMidpoint_mem_lowerGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact upperGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := boundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := boundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))

/-- Quantitative amplification tends to infinity when the upper spacing
collapses and its lower neighbor is eventually bounded below. -/
theorem tendsto_boundaryAmplification_atTop_of_upperSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ᶠ m in atTop,
      delta ≤ endpointSpacing (nodes m) q.castSucc) :
    Tendsto (fun m ↦ boundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.succ ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.succ
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto
      (fun m ↦ (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hlower] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.castSucc / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.castSucc / 2 := by
    linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [boundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.succ)⁻¹ ≤
      ((endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.succ)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hUpperPos.le)
    _ = (endpointSpacing (nodes m) q.castSucc *
          (2 * endpointSpacing (nodes m) q.succ)⁻¹) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
      field_simp

/-- Source Lemma 4's analytic heart in finite-radius form: a common cardinal
amplification `K ≥ 1` forces the upper-minus-lower gap-height coordinate to
be at most `1 - K`. -/
theorem gapDifference_le_one_sub_of_adjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : AdjacentCardinalAmplification nodes q K) :
    gapDifference nodes q ≤ 1 - K := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.succ
  have hsum :
      K * lebesgueFunction nodes.toNodeFamily x ≤
        lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily
      (hdom x hx)
  have hlower :
      lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.castSucc :=
    lebesgueFunction_le_height nodes q.castSucc hy
  have hupper : nodes.height q.succ = lebesgueFunction nodes.toNodeFamily x := by
    exact heq
  have hone : 1 ≤ nodes.height q.succ := one_le_height nodes q.succ
  unfold gapDifference
  rw [hupper] at hone ⊢
  nlinarith

/-- A sequence-level finite-radius form of the source boundary argument.
Once amplifications tend to infinity, the norm of the selected coordinate of
the gap-difference map tends to infinity. -/
theorem tendsto_norm_gapDifference_atTop_of_amplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, AdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_le_one_sub_of_adjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hneg : gapDifference (nodes m) q ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith

/-! ## The reflected, right-neighbor estimate -/

/-- Cardinal amplification when the lower gap collapses and the upper gap is
the surviving neighbor. -/
def RightAdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.succ,
    ∀ x ∈ openGap nodes.toOrderedNodes q.castSucc,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|

/-- Midpoint of the surviving upper neighbor. -/
def rightBoundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.succ) +
    nodes.point (gapRightIndex q.succ)) / 2

/-- Reflected amplification factor. -/
def rightBoundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.succ /
      (2 * endpointSpacing nodes q.castSucc)) *
    (endpointSpacing nodes q.succ / (2 * (B - A))) ^ d

lemma rightBoundaryMidpoint_mem_upperGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    rightBoundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.succ := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.succ
  constructor <;> unfold rightBoundaryMidpoint <;> linarith

lemma lowerGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have := (nodes.strictMono.monotone hjleft).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)

lemma half_upperSpacing_le_rightMidpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / 2 ≤
      |rightBoundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.succ
  by_cases hj : j.val ≤ q.val + 1
  · have hjleft : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ rightBoundaryMidpoint nodes q - nodes.point j := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hrightj
    have hnonpos : rightBoundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith

lemma lowerGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.castSucc) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.castSucc) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith

lemma rightBoundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / (2 * (B - A)) ≤
      |(rightBoundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (lowerGap_point_ne_node nodes q hx j))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q j
  · exact lowerGap_distance_le_intervalLength nodes q hx j

lemma rightBoundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]

lemma rightBoundary_ratio_le_lowerLeft_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapLeftIndex q.castSucc)) /
        (x - nodes.point (gapLeftIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapLeftIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapLeftIndex q.castSucc)
  · rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]

lemma exists_rightBoundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.succ /
          (2 * endpointSpacing nodes q.castSucc) ≤
        |(rightBoundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapLeftIndex q.castSucc, ?_,
      rightBoundary_ratio_le_lowerLeft_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.castSucc).ne
    rw [h, hk]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      rightBoundary_ratio_le_common_factor nodes q hx⟩

lemma rightBoundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    rightBoundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(rightBoundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(rightBoundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.succ / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.succ /
    (2 * endpointSpacing nodes q.castSucc)
  obtain ⟨r, hrs, hrR⟩ := exists_rightBoundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact rightBoundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.succ).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by rwa [hcard] at hpow
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [rightBoundaryAmplification, s, f, c, R] using hprod

theorem rightAdjacentCardinalAmplification_rightBoundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    RightAdjacentCardinalAmplification nodes q
      (rightBoundaryAmplification nodes q) := by
  refine ⟨rightBoundaryMidpoint nodes q, rightBoundaryMidpoint_mem_upperGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact lowerGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := rightBoundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := rightBoundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))

/-- Reflected finite-radius height separation. -/
theorem gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : RightAdjacentCardinalAmplification nodes q K) :
    K - 1 ≤ gapDifference nodes q := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.castSucc
  have hsum : K * lebesgueFunction nodes.toNodeFamily x ≤
      lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily (hdom x hx)
  have hupp : lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.succ :=
    lebesgueFunction_le_height nodes q.succ hy
  have hlower : nodes.height q.castSucc = lebesgueFunction nodes.toNodeFamily x := heq
  have hone : 1 ≤ nodes.height q.castSucc := one_le_height nodes q.castSucc
  unfold gapDifference
  rw [hlower] at hone ⊢
  nlinarith

theorem tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hupper : ∀ᶠ m in atTop, delta ≤ endpointSpacing (nodes m) q.succ) :
    Tendsto (fun m ↦ rightBoundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by dsimp [C]; positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.castSucc ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.castSucc
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto (fun m ↦ (endpointSpacing (nodes m) q.castSucc)⁻¹)
      atTop atTop := hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.castSucc)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hupper] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.succ / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.succ / 2 := by linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [rightBoundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.castSucc)⁻¹ ≤
      ((endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.castSucc)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hLowerPos.le)
    _ = (endpointSpacing (nodes m) q.succ *
          (2 * endpointSpacing (nodes m) q.castSucc)⁻¹) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
      field_simp

theorem tendsto_norm_gapDifference_atTop_of_rightAmplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, RightAdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hpos : 0 ≤ gapDifference (nodes m) q := by linarith
  rw [abs_of_nonneg hpos]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith

/-! ## Boundary/properness interfaces -/

/-- Sequential escape when an upper gap collapses while its immediate lower
neighbor remains nondegenerate. -/
def LeftNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.castSucc) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop

/-- Reflected sequential escape: the lower gap collapses while its immediate
upper neighbor remains nondegenerate.  This is deliberately a proposition,
not an asserted theorem; it is the exact remaining mirror estimate. -/
def RightNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.succ) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop

/-- The left-neighbor boundary escape statement is completely discharged by
the explicit product estimate.  This includes collapse of the right endpoint
gap; the reflected right-neighbor case is the remaining ingredient for an
all-faces properness theorem. -/
theorem boundaryEscape_leftNeighbor (d : ℕ) (A B : ℝ) :
    LeftNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hlower⟩
  have hK := tendsto_boundaryAmplification_atTop_of_upperSpacing
    nodes q hzero hdelta hlower
  exact tendsto_norm_gapDifference_atTop_of_amplification nodes q
    (fun m ↦ boundaryAmplification (nodes m) q) hK
    (fun m ↦ adjacentCardinalAmplification_boundaryAmplification (nodes m) q)

/-- Reflected right-neighbor escape, proved by transporting every cardinal
function from the collapsing lower gap to the midpoint of the surviving upper
gap. -/
theorem boundaryEscape_rightNeighbor (d : ℕ) (A B : ℝ) :
    RightNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hupper⟩
  have hK := tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    nodes q hzero hdelta hupper
  exact tendsto_norm_gapDifference_atTop_of_rightAmplification nodes q
    (fun m ↦ rightBoundaryAmplification (nodes m) q) hK
    (fun m ↦ rightAdjacentCardinalAmplification_rightBoundaryAmplification
      (nodes m) q)

/-! ## Selection from a limiting boundary spacing profile -/

/-- A nonnegative finite chain containing both a zero and a positive entry
has an adjacent zero/positive transition. -/
lemma exists_adjacent_zero_positive {d : ℕ} (s : Fin (d + 1) → ℝ)
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      (0 < s q.castSucc ∧ s q.succ = 0) ∨
        (s q.castSucc = 0 ∧ 0 < s q.succ) := by
  induction d with
  | zero =>
      obtain ⟨z, hz⟩ := hzero
      obtain ⟨p, hp⟩ := hpos
      have hz0 : z = 0 := Fin.eq_zero z
      have hp0 : p = 0 := Fin.eq_zero p
      rw [hz0] at hz
      rw [hp0, hz] at hp
      exact (lt_irrefl 0 hp).elim
  | succ d ih =>
      let tail : Fin (d + 1) → ℝ := fun i ↦ s i.succ
      by_cases h0 : s 0 = 0
      · by_cases h1 : s (Fin.succ 0) = 0
        · have htailZero : ∃ g, tail g = 0 := ⟨0, h1⟩
          obtain ⟨p, hp⟩ := hpos
          have hp0 : p ≠ 0 := by
            intro hpzero
            subst p
            rw [h0] at hp
            exact (lt_irrefl 0 hp)
          obtain ⟨p', rfl⟩ := Fin.exists_succ_eq.mpr hp0
          have htailPos : ∃ g, 0 < tail g := ⟨p', hp⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq
        · refine ⟨0, Or.inr ⟨h0, ?_⟩⟩
          exact lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)
      · have h0pos : 0 < s 0 := lt_of_le_of_ne (hs 0) (Ne.symm h0)
        by_cases h1 : s (Fin.succ 0) = 0
        · exact ⟨0, Or.inl ⟨h0pos, h1⟩⟩
        · have htailPos : ∃ g, 0 < tail g :=
            ⟨0, lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)⟩
          obtain ⟨z, hz⟩ := hzero
          have hz0 : z ≠ 0 := by
            intro hzzero
            subst z
            exact h0 hz
          obtain ⟨z', rfl⟩ := Fin.exists_succ_eq.mpr hz0
          have htailZero : ∃ g, tail g = 0 := ⟨z', hz⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq

/-- Coordinatewise convergence of the positive spacing vectors to a genuine
boundary profile forces one fixed adjacent coordinate of `gapDifference` to
escape.  This is a whole-sequence result because the boundary profile itself
is assumed to be the whole-sequence limit. -/
theorem exists_coordinate_escape_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_adjacent_zero_positive s hs hzero hpos
  refine ⟨q, ?_⟩
  rcases hq with hleft | hright
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
        atTop (nhds 0) := by simpa [hleft.2] using hconv q.succ
    have hevent : ∀ᶠ m in atTop,
        s q.castSucc / 2 ≤ endpointSpacing (nodes m) q.castSucc :=
      ((hconv q.castSucc).eventually_const_lt (half_lt_self hleft.1)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_leftNeighbor d A B nodes q hzero'
      ⟨s q.castSucc / 2, half_pos hleft.1, hevent⟩
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
        atTop (nhds 0) := by simpa [hright.1] using hconv q.castSucc
    have hevent : ∀ᶠ m in atTop,
        s q.succ / 2 ≤ endpointSpacing (nodes m) q.succ :=
      ((hconv q.succ).eventually_const_lt (half_lt_self hright.2)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_rightNeighbor d A B nodes q hzero'
      ⟨s q.succ / 2, half_pos hright.2, hevent⟩

/-- The norm of the full finite gap-difference vector escapes whenever one
fixed coordinate does. -/
theorem tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_coordinate_escape_of_boundarySpacingProfile
    nodes s hconv hs hzero hpos
  exact tendsto_atTop_mono
    (fun m ↦ norm_le_pi_norm (gapDifference (nodes m)) q) hq

/-! ## Compact spacing extraction and the precise sequential residue -/

/-- Closed coordinate box containing every spacing vector. -/
def closedSpacingBox (d : ℕ) (A B : ℝ) : Set (Fin (d + 1) → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Icc 0 (B - A)

lemma isCompact_closedSpacingBox (d : ℕ) (A B : ℝ) :
    IsCompact (closedSpacingBox d A B) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

lemma endpointSpacing_mem_closedSpacingBox {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ closedSpacingBox d A B := by
  intro g _hg
  constructor
  · exact (endpointSpacing_pos nodes g).le
  · calc
      endpointSpacing nodes g ≤ ∑ i, endpointSpacing nodes i :=
        Finset.single_le_sum
          (fun i _ ↦ (endpointSpacing_pos nodes i).le) (Finset.mem_univ g)
      _ = B - A := sum_endpointSpacing nodes

/-- Every endpoint-array sequence has a subsequence whose complete spacing
vector converges in the closed simplex. -/
theorem exists_convergent_spacing_subsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧
      ∑ g, s g = B - A := by
  obtain ⟨s, hsbox, φ, hφ, hlim⟩ :=
    (isCompact_closedSpacingBox d A B).tendsto_subseq
      (fun m ↦ endpointSpacing_mem_closedSpacingBox (nodes m))
  have hcoord : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
      atTop (nhds (s g)) := by
    intro g
    have h := (tendsto_pi_nhds.mp hlim) g
    simpa only [Function.comp_apply] using h
  have hsumlim : Tendsto
      (fun m ↦ ∑ g, endpointSpacing (nodes (φ m)) g)
      atTop (nhds (∑ g, s g)) :=
    tendsto_finset_sum Finset.univ fun g _ ↦ hcoord g
  have hsumlim' : Tendsto (fun _ : ℕ ↦ B - A)
      atTop (nhds (∑ g, s g)) := by
    simpa only [sum_endpointSpacing] using hsumlim
  have hsum : ∑ g, s g = B - A :=
    tendsto_nhds_unique hsumlim' tendsto_const_nhds
  exact ⟨s, φ, hφ, hcoord, fun g ↦ (hsbox g (Set.mem_univ g)).1, hsum⟩

/-- A sequence has no convergent subsequence in the open endpoint-array
space.  This is a sequential escape hypothesis, not yet a topological
properness assertion. -/
def HasNoConvergentEndpointSubsequence {d : ℕ} {A B : ℝ}
    (nodes : ℕ → EndpointArray d A B) : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ limit : EndpointArray d A B,
    ¬ Tendsto (fun m ↦ nodes (φ m)) atTop (nhds limit)

/-- Under sequential escape from the open simplex, compact spacing
extraction necessarily lands on its boundary.  If every limiting spacing
were positive, the committed spacing homeomorphism would reconstruct a
convergent endpoint-array subsequence. -/
theorem exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧ (∃ g, s g = 0) ∧ (∃ g, 0 < s g) := by
  obtain ⟨s, φ, hφ, hconv, hs, hsum⟩ := exists_convergent_spacing_subsequence nodes
  have hzero : ∃ g, s g = 0 := by
    by_contra h
    push_neg at h
    have hspos : ∀ g, 0 < s g := fun g ↦ lt_of_le_of_ne (hs g) (Ne.symm (h g))
    let σ : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} :=
      ⟨s, hspos, hsum⟩
    have hsub : Tendsto
        (fun m ↦ ⟨endpointSpacing (nodes (φ m)),
          endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds σ) := by
      apply tendsto_subtype_rng.mpr
      exact tendsto_pi_nhds.mpr hconv
    have hAB : AdmissibleInterval A B := (nodes 0).admissibleInterval
    have hnodes :=
      ((endpointArraySpacingHomeomorph hAB).continuous_invFun.tendsto σ).comp hsub
    have hnodes' : Tendsto (fun m ↦ nodes (φ m)) atTop
        (nhds (endpointArrayOfSpacings hAB σ)) := by
      change Tendsto
        (fun m ↦ endpointArrayOfSpacings hAB
          ⟨endpointSpacing (nodes (φ m)),
            endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds (endpointArrayOfSpacings hAB σ)) at hnodes
      simpa only [endpointArrayOfSpacings_endpointSpacing] using hnodes
    exact hno φ hφ (endpointArrayOfSpacings hAB σ) hnodes'
  have hpos : ∃ g, 0 < s g := by
    have hp := (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (fun g _ ↦ hs g)).mp (by
        rw [hsum]
        exact sub_pos.mpr (nodes 0).endpoints_lt)
    obtain ⟨g, _hgmem, hg⟩ := hp
    exact ⟨g, hg⟩
  exact ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩

/-- What the compactness reduction proves without any further uniformity
argument: every endpoint-array sequence with no convergent open-simplex
subsequence has a subsequence along which the full gap-difference norm tends
to infinity. -/
theorem exists_subsequence_tendsto_norm_gapDifference_atTop
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m ↦ ‖gapDifference (nodes (φ m))‖) atTop atTop := by
  obtain ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩ :=
    exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence nodes hno
  exact ⟨φ, hφ,
    tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
      (fun m ↦ nodes (φ m)) s hconv hs hzero hpos⟩

/-- Sequential properness kernel: if a sequence has no convergent subsequence
in the open endpoint-array simplex, then the norm of its full gap-difference
vector tends to infinity along the whole sequence.  The proof upgrades the
subsequential boundary result by applying it to any hypothetical frequently
bounded subsequence. -/
theorem tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  by_contra hR
  have hfreq : ∃ᶠ m in atTop, ¬ R ≤ ‖gapDifference (nodes m)‖ := by
    exact Filter.not_eventually.mp hR
  obtain ⟨φ, hφ, hbound⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hnoφ : HasNoConvergentEndpointSubsequence (fun m ↦ nodes (φ m)) := by
    intro ψ hψ limit hlim
    apply hno (φ ∘ ψ) (hφ.comp hψ) limit
    simpa only [Function.comp_apply] using hlim
  obtain ⟨ψ, _hψ, hescape⟩ :=
    exists_subsequence_tendsto_norm_gapDifference_atTop
      (fun m ↦ nodes (φ m)) hnoφ
  have hevent := hescape.eventually_ge_atTop R
  obtain ⟨m, hm⟩ := hevent.exists
  exact hbound (ψ m) hm

/-- The genuine topological properness target.  It is kept as a proposition:
upgrading the checked sequential escape theorem to `IsProperMap` additionally
requires the continuity of the gap-height map and the appropriate
metrizable/locally compact properness bridge. -/
def GapDifferenceTopologicalPropernessStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsProperMap (gapDifference : EndpointArray d A B → Fin d → ℝ)

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Properness.lean` -/

/-!
# From sequential boundary escape to properness

`Boundary` proves that every endpoint-array sequence with no convergent
subsequence has gap-difference norm tending to infinity.  This file supplies
the standard finite-dimensional topological bridge: conditional only on
continuity of `gapDifference`, compact target sets have compact preimages.

The proof does not identify sequential escape with properness by fiat.  It
uses the committed Euclidean homeomorphism of the endpoint-array simplex,
proves sequential compactness of the image of each compact preimage, and then
uses metrizability of the finite-dimensional function space.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Filter _root_.Topology

noncomputable section

/-- A compact set in the finite-dimensional target has a uniform norm
bound.  This small wrapper keeps the contradiction in the properness proof
explicit. -/
lemma exists_norm_bound_of_isCompact {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) :
    ∃ C : ℝ, ∀ y ∈ K, ‖y‖ ≤ C :=
  (isBounded_iff_forall_norm_le (s := K)).mp hK.isBounded

/-- Conditional compact-preimage bridge for `gapDifference`.

Continuity is used only to show that the limit of a convergent endpoint-array
subsequence remains in the preimage of the closed compact target set.  The
existence of the subsequence comes from the checked sequential boundary
escape theorem in `Boundary`. -/
theorem isCompact_preimage_gapDifference_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    IsCompact
      ((gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K) := by
  classical
  let S : Set (EndpointArray d A B) :=
    (gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K
  by_cases hSne : S.Nonempty
  · let base : EndpointArray d A B := hSne.some
    have hAB : AdmissibleInterval A B := base.admissibleInterval
    let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
      endpointArrayLogRatioHomeomorph hAB
    have himageSeq : IsSeqCompact (e '' S) := by
      intro z hz
      let nodes : ℕ → EndpointArray d A B := fun m ↦ e.symm (z m)
      have hnodesMem : ∀ m, nodes m ∈ S := by
        intro m
        obtain ⟨x, hxS, hx⟩ := hz m
        have hnodes : nodes m = x := by
          apply e.injective
          simp only [nodes, Homeomorph.apply_symm_apply, hx]
        simpa only [hnodes] using hxS
      have hnotNo : ¬ HasNoConvergentEndpointSubsequence nodes := by
        intro hno
        have hescape :=
          tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
            nodes hno
        obtain ⟨C, hC⟩ := exists_norm_bound_of_isCompact hK
        obtain ⟨m, hm⟩ := (hescape.eventually_ge_atTop (C + 1)).exists
        have hmem : gapDifference (nodes m) ∈ K := hnodesMem m
        linarith [hC (gapDifference (nodes m)) hmem]
      unfold HasNoConvergentEndpointSubsequence at hnotNo
      push_neg at hnotNo
      obtain ⟨φ, hφ, limit, hlim⟩ := hnotNo
      have hlimitS : limit ∈ S := by
        apply hK.isClosed.mem_of_tendsto
          ((hcont.tendsto limit).comp hlim)
        exact Eventually.of_forall fun m ↦ hnodesMem (φ m)
      refine ⟨e limit, ⟨limit, hlimitS, rfl⟩, φ, hφ, ?_⟩
      have heLim := (e.continuous.tendsto limit).comp hlim
      convert heLim using 1
      funext m
      exact (e.apply_symm_apply (z (φ m))).symm
    have himageCompact : IsCompact (e '' S) := himageSeq.isCompact
    have hSCompact : IsCompact S := e.isCompact_image.mp himageCompact
    exact hSCompact
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    change IsCompact S
    rw [hSempty]
    exact isCompact_empty

/-- The promised one-line packaging: once continuity of gap heights (and
hence of `gapDifference`) is available, the de Boor--Pinkus difference map is
proper. -/
theorem gapDifference_isProperMap_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, ?_⟩
  intro K hK
  exact isCompact_preimage_gapDifference_of_continuous hcont hK

/-- Ordinary proposition interface for the only remaining input.  No
inhabitant is asserted here; the active height/Jacobian lane may discharge it
without changing the properness proof. -/
def GapDifferenceContinuityStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Continuity-to-properness packaging in the exact project-level proposition
language reserved by `Boundary`. -/
theorem gapDifference_topologicalProperness_of_continuity
    {d : ℕ} {A B : ℝ} :
    GapDifferenceContinuityStatement d A B →
      GapDifferenceTopologicalPropernessStatement d A B :=
  gapDifference_isProperMap_of_continuous

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/GlobalHomeomorph.lean` -/

/-!
# The global-topology step in the de Boor--Pinkus argument

This file isolates the standard global inversion theorem needed after the
Jacobian and boundary arguments.  A proper local homeomorphism of a
finite-dimensional real vector space is a covering map.  Its image is both
open and closed, hence (because the target is connected) it is surjective.
A covering of a simply connected target by a connected total space has one
sheet, so the map is a homeomorphism.

The proof below spells out all three bridges.  In particular, it does not
replace properness by local injectivity or assume the desired global
bijectivity under another name.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Function _root_.Topology

noncomputable section

/-! ## Proper local homeomorphisms are covering maps -/

/-- A proper local homeomorphism between Hausdorff spaces is a covering map.

Properness makes the map closed and makes each point fiber compact.  The
local charts make the fiber discrete; a compact discrete subset is finite,
which is precisely the finite-fiber input to Mathlib's evenly-covered
neighborhood constructor. -/
theorem isCoveringMap_of_isLocalHomeomorph_of_isProperMap
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X] {f : E → X}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph
  · intro x hx
    have hdisc : IsDiscrete (f ⁻¹' {x}) :=
      IsDiscrete.of_openPartialHomeomorph f Set.Subset.rfl fun e he ↦ by
        obtain ⟨φ, heφ, hφ⟩ := hloc e
        exact ⟨φ, heφ, hφ.symm⟩
    exact (hproper.isCompact_preimage isCompact_singleton).finite hdisc
  · intro e he
    obtain ⟨φ, heφ, hφ⟩ := hloc e
    exact ⟨φ, heφ, hφ.symm⟩

/-! ## A connected covering of a simply connected space has one sheet -/

/-- A surjective covering map from a preconnected space to a nonempty,
simply connected, locally path-connected space is a homeomorphism.

The inverse is the unique lift of the identity map through the covering.  To
check the other inverse law, compare `s ∘ f` with the identity as two lifts
of `f`; connectedness of the total space and equality at the chosen basepoint
give equality everywhere. -/
theorem IsCoveringMap.isHomeomorph_of_surjective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty X]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    {f : E → X} (hcover : IsCoveringMap f) (hsurj : Surjective f) :
    IsHomeomorph f := by
  let x₀ : X := Classical.arbitrary X
  obtain ⟨e₀, he₀⟩ := hsurj x₀
  let fid : C(X, X) := ContinuousMap.id X
  obtain ⟨s, hs, _⟩ :=
    hcover.existsUnique_continuousMap_lifts fid x₀ e₀ (by simpa [fid] using he₀)
  obtain ⟨hs₀, hfs⟩ := hs
  have hsf : (s : X → E) ∘ f = id := by
    refine hcover.eq_of_comp_eq
      (s.continuous.comp hcover.continuous) continuous_id ?_ e₀ ?_
    · funext e
      have hright := congrFun hfs (f e)
      simpa [fid, Function.comp_def] using hright
    · simpa [he₀] using hs₀
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨hcover.continuous, s, ?_, ?_, s.continuous⟩
  · intro e
    exact congrFun hsf e
  · intro x
    have hright := congrFun hfs x
    simpa [fid, Function.comp_def] using hright

/-! ## Euclidean global inversion -/

/-- The zero-dimensional case is completely elementary: `Fin 0 → ℝ` is a
singleton, so every local homeomorphism from it to itself is bijective. -/
theorem fin_zero_isHomeomorph_of_isLocalHomeomorph
    {f : (Fin 0 → ℝ) → (Fin 0 → ℝ)}
    (hloc : IsLocalHomeomorph f) : IsHomeomorph f := by
  have hinj : Injective f := fun _ _ _ ↦ Subsingleton.elim _ _
  have hsurj : Surjective f := fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  exact (hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩).isHomeomorph

/-- A proper local homeomorphism of `Fin d → ℝ` is a global
homeomorphism.  The `d = 0` singleton case is dispatched explicitly; positive
dimensions use the covering-space argument. -/
theorem euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
    {d : ℕ} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsHomeomorph f := by
  cases d with
  | zero => exact fin_zero_isHomeomorph_of_isLocalHomeomorph hloc
  | succ d =>
    have hcover : IsCoveringMap f :=
      isCoveringMap_of_isLocalHomeomorph_of_isProperMap hloc hproper
    have hrangeOpen : IsOpen (Set.range f) := by
      simpa only [Set.image_univ] using hloc.isOpenMap Set.univ isOpen_univ
    have hrangeClosed : IsClosed (Set.range f) := hproper.isClosed_range
    have hrangeNonempty : (Set.range f).Nonempty :=
      ⟨f 0, 0, rfl⟩
    have hrange : Set.range f = Set.univ :=
      IsClopen.eq_univ ⟨hrangeClosed, hrangeOpen⟩ hrangeNonempty
    exact IsCoveringMap.isHomeomorph_of_surjective hcover
      (Set.range_eq_univ.mp hrange)

/-! ## Transporting the de Boor--Pinkus difference map -/

/-- The gap-difference map written in the global spacing/log-ratio chart. -/
def transportedGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  gapDifference ∘ (endpointArrayLogRatioHomeomorph hAB).symm

/-- Local-homeomorphism transport from endpoint arrays to the global
Euclidean chart. -/
theorem isLocalHomeomorph_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsLocalHomeomorph (transportedGapDifference (d := d) hAB) := by
  exact hloc.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isLocalHomeomorph

/-- Properness transport from endpoint arrays to the global Euclidean
chart. -/
theorem isProperMap_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap (transportedGapDifference (d := d) hAB) := by
  exact hproper.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isProperMap

/-- The exact global-topology packaging needed by the source theorem.  Once
the Jacobian lane supplies local homeomorphism and the boundary lane supplies
properness, no further global hypothesis is needed. -/
theorem gapDifference_isHomeomorph_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  have htransport : IsHomeomorph (transportedGapDifference (d := d) hAB) :=
    euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
      (isLocalHomeomorph_transportedGapDifference hAB hloc)
      (isProperMap_transportedGapDifference hAB hproper)
  have hchart : IsHomeomorph (endpointArrayLogRatioHomeomorph (d := d) hAB) :=
    (endpointArrayLogRatioHomeomorph (d := d) hAB).isHomeomorph
  have hcomp := htransport.comp hchart
  simpa only [transportedGapDifference, Function.comp_assoc,
    Homeomorph.symm_comp_self, Function.id_comp] using hcomp

/-- Ordinary proposition interface for the remaining local input.  No
inhabitant is asserted here. -/
def GapDifferenceLocalHomeomorphStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsLocalHomeomorph
    (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Project-level packaging into the reserved homeomorphism statement. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hproper : GapDifferenceTopologicalPropernessStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B := by
  intro hAB
  exact gapDifference_isHomeomorph_of_localHomeomorph_of_proper hAB hloc hproper

/-- Continuity plus the local-homeomorphism input suffices, using the checked
sequential boundary-escape-to-properness theorem. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hcont : GapDifferenceContinuityStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper hloc
    (gapDifference_topologicalProperness_of_continuity hcont)

/-- Final one-input topology interface.  A local homeomorphism is already
continuous, so the committed boundary-escape bridge supplies properness and
the global inversion theorem supplies the reserved source statement. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    hloc hloc.continuous

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Comparison.lean` -/

/-!
# Equioscillation and coordinatewise comparison

The first part of this file is unconditional: a global homeomorphism for the
gap-difference map has a unique zero, and zero consecutive differences are
exactly equioscillation.

The second part isolates the one source input not yet delivered by the
Jacobian/interlacing lane.  De Boor--Pinkus use the coherent signs of the
maximal height-Jacobian minors twice:

* lift the straight segment in the coordinates consisting of all heights
  except the first; the first height moves strictly in the opposite
  direction;
* lift the diagonal decreasing ray in those coordinates until the first
  gap difference crosses a prescribed lower value.

`GapHeightPathRayOrientationStatement` records exactly those two oriented
lift conclusions, including the actual continuous lifted paths.  It is an
ordinary proposition and no inhabitant is asserted here.  The full
coordinatewise rigidity theorem and the project `ComparisonPackage` are
proved below from that single orientation input and the already-checked
global homeomorphism.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Function _root_.Topology unitInterval

noncomputable section

/-! ## Consecutive differences and equioscillation -/

/-- The coordinates used by source Theorem 2: all gap heights except the
first one. -/
def tailGapHeight {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i ↦ nodes.height i.succ

/-- Vanishing consecutive height differences are equivalent to equality of
all gap heights. -/
theorem equioscillates_iff_gapDifference_eq_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Equioscillates nodes ↔
      gapDifference nodes = (0 : Fin d → ℝ) := by
  constructor
  · intro heq
    funext i
    simp only [gapDifference, Pi.zero_apply, sub_eq_zero]
    exact heq i.succ i.castSucc
  · intro hzero
    have hadj (i : Fin d) :
        nodes.height i.succ = nodes.height i.castSucc := by
      have hi := congrFun hzero i
      simpa only [gapDifference, Pi.zero_apply, sub_eq_zero] using hi
    have hbase (i : Fin (d + 1)) :
        nodes.height i = nodes.height (0 : Fin (d + 1)) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
          exact (hadj i).trans ih
    intro i j
    exact (hbase i).trans (hbase j).symm

/-- Source Theorem 1 immediately gives the unique equioscillating endpoint
array as the unique inverse image of the zero difference vector. -/
theorem existsUniqueEquioscillating_of_gapDifferenceHomeomorphism
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B) :
    ExistsUniqueEquioscillatingStatement d A B := by
  intro hAB
  let hglobal := hhomeomorph hAB
  obtain ⟨nodes, hnodes⟩ := hglobal.surjective (0 : Fin d → ℝ)
  refine ⟨nodes, (equioscillates_iff_gapDifference_eq_zero nodes).2 hnodes, ?_⟩
  intro other hother
  apply hglobal.injective
  rw [(equioscillates_iff_gapDifference_eq_zero other).1 hother, hnodes]

/-! ## The exact coherent-orientation continuation input -/

/-- The source-faithful output required from coherent maximal-minor signs.

For positive dimension, `lift_increasingSegment` is the lift of the affine
segment in `(height 1, ..., height d)` and records strict decrease of
`height 0`.  `lift_decreasingRay_to_firstDifference` is the finite initial
piece of the diagonal decreasing ray, stopped when its first consecutive
difference reaches the prescribed smaller value.  Both fields expose the
continuous lifted curve and its exact coordinate formula; neither assumes
coordinatewise rigidity or injectivity of a height-coordinate projection.
-/
structure GapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) : Prop where
  lift_increasingSegment :
    ∀ (_hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ),
      (∀ i, tailGapHeight s i ≤ y i) →
      y ≠ tailGapHeight s →
      ∃ g : C(I, EndpointArray d A B),
        g 0 = s ∧
        (∀ u i,
          tailGapHeight (g u) i =
            (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
        StrictAnti (fun u : I ↦ (g u).height (0 : Fin (d + 1)))
  lift_decreasingRay_to_firstDifference :
    ∀ (hd : 1 ≤ d) (r : EndpointArray d A B) (c : ℝ),
      c < gapDifference r ⟨0, hd⟩ →
      ∃ α : ℝ, 0 < α ∧
        ∃ g : C(I, EndpointArray d A B),
          g 0 = r ∧
          (∀ u i,
            tailGapHeight (g u) i =
              tailGapHeight r i - (u : ℝ) * α) ∧
          gapDifference (g 1) ⟨0, hd⟩ = c

/-- Endpoint form of the increasing-segment lift. -/
theorem exists_tail_eq_and_height_zero_lt_of_le_of_ne
    {d : ℕ} {A B : ℝ}
    (horient : GapHeightPathRayOrientationStatement d A B)
    (hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ r : EndpointArray d A B,
      tailGapHeight r = y ∧
        r.height (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) := by
  obtain ⟨g, hgzero, hgtail, hganti⟩ :=
    horient.lift_increasingSegment hd s y hle hne
  refine ⟨g 1, ?_, ?_⟩
  · funext i
    simpa using hgtail 1 i
  · have hzeroOne : (0 : I) < 1 := zero_lt_one
    have hstrict := hganti hzeroOne
    simpa only [hgzero] using hstrict

/-! ## Difference reconstruction after a diagonal tail shift -/

/-- If every noninitial height is shifted by the same amount and the first
height difference is fixed separately, then the entire consecutive-
difference vector is fixed. -/
lemma gapDifference_eq_of_tail_eq_sub_and_zero_eq
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    {q t : EndpointArray d A B} {α : ℝ}
    (htail : ∀ i, tailGapHeight q i = tailGapHeight t i - α)
    (hzero : gapDifference q ⟨0, hd⟩ =
      gapDifference t ⟨0, hd⟩) :
    gapDifference q = gapDifference t := by
  let i₀ : Fin d := ⟨0, hd⟩
  funext i
  by_cases hi : i = i₀
  · simpa only [hi] using hzero
  · have hiVal : i.val ≠ 0 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa only [i₀] using hval
    let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [gapDifference, gapDifference]
    have hright := htail i
    have hleft := htail j
    simp only [tailGapHeight] at hright hleft
    rw [hjsucc] at hleft
    linarith

/-! ## Coordinatewise rigidity -/

/-- De Boor--Pinkus Theorem 2 from the global difference homeomorphism and
the exact coherent-minor path/ray orientation input. -/
theorem gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    GapHeightLeRigidityStatement d A B := by
  intro s t hle
  by_cases hd : d = 0
  · subst d
    exact endpointArray_zero_unique s t
  have hdpos : 1 ≤ d := by omega
  let i₀ : Fin d := ⟨0, hdpos⟩
  by_contra hst
  have htailCases : tailGapHeight s = tailGapHeight t ∨
      tailGapHeight s ≠ tailGapHeight t := eq_or_ne _ _
  obtain ⟨r, hrtail, hrzero⟩ :
      ∃ r : EndpointArray d A B,
        tailGapHeight r = tailGapHeight t ∧
          r.height (0 : Fin (d + 1)) < t.height (0 : Fin (d + 1)) := by
    rcases htailCases with htailEq | htailNe
    · refine ⟨s, htailEq, ?_⟩
      have hzeroLe := hle (0 : Fin (d + 1))
      exact lt_of_le_of_ne hzeroLe fun heq ↦ by
        apply hst
        apply (hhomeomorph s.admissibleInterval).injective
        apply gapDifference_eq_of_tail_eq_sub_and_zero_eq
          (hd := hdpos) (α := 0)
        · intro i
          have htail := congrFun htailEq i
          simpa using htail
        · rw [gapDifference, gapDifference]
          have htail := congrFun htailEq i₀
          simp only [tailGapHeight] at htail
          change s.height i₀.succ - s.height i₀.castSucc =
            t.height i₀.succ - t.height i₀.castSucc
          have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
            apply Fin.ext
            rfl
          rw [hi₀cast, heq]
          exact congrArg (fun z ↦ z - t.height (0 : Fin (d + 1))) htail
    · have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight t i := by
        intro i
        exact hle i.succ
      obtain ⟨r, hrtail, hrs⟩ :=
        exists_tail_eq_and_height_zero_lt_of_le_of_ne
          horient hdpos s (tailGapHeight t) htailLe htailNe.symm
      exact ⟨r, hrtail, hrs.trans_le (hle (0 : Fin (d + 1)))⟩
  have hfirst : gapDifference t i₀ < gapDifference r i₀ := by
    rw [gapDifference, gapDifference]
    have htail0 := congrFun hrtail i₀
    simp only [tailGapHeight] at htail0
    have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      rfl
    rw [hi₀cast]
    linarith
  obtain ⟨α, hα, g, hgzero, hgtail, hgfirst⟩ :=
    horient.lift_decreasingRay_to_firstDifference hdpos r
      (gapDifference t i₀) hfirst
  let q : EndpointArray d A B := g 1
  have hqtail : ∀ i, tailGapHeight q i = tailGapHeight t i - α := by
    intro i
    have hpath := hgtail 1 i
    calc
      tailGapHeight q i = tailGapHeight r i - α := by simpa [q] using hpath
      _ = tailGapHeight t i - α := by rw [congrFun hrtail i]
  have hqzero : gapDifference q i₀ = gapDifference t i₀ := by
    simpa [q] using hgfirst
  have hqdiff : gapDifference q = gapDifference t :=
    gapDifference_eq_of_tail_eq_sub_and_zero_eq hdpos hqtail hqzero
  have hqt : q = t :=
    (hhomeomorph t.admissibleInterval).injective hqdiff
  have hshift := hqtail i₀
  rw [hqt] at hshift
  linarith

/-! ## Project packaging -/

/-- Construct the complete comparison package from source Theorem 1 and the
single remaining coherent-orientation continuation input. -/
theorem comparisonPackage_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    ComparisonPackage d A B where
  gapHeight_le_rigidity :=
    gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
      hhomeomorph horient
  exists_unique_equioscillating :=
    existsUniqueEquioscillating_of_gapDifferenceHomeomorphism hhomeomorph

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Orientation.lean` -/

/-!
# Local coherent orientation for the de Boor--Pinkus comparison paths

This file moves strictly below the path/ray contract in `Comparison`.
First it records coherent signs of the maximal height-Jacobian minors and
derives the source's Cramer-rule sign (equation (8)).  It then gives the
smallest continuation-ready local input: around every endpoint array, the
tail-height map has a convex local-homeomorphism chart and height zero is
strictly order-reversing in that chart.

From this genuinely local input we prove that the tail-height map is a local
homeomorphism and construct every chart-contained affine lift, including
strict opposite motion of height zero.  A generic compact-continuation
theorem then glues the unique local branches.  Compact height slabs handle
the increasing segment; for the decreasing ray, failure to cross a prescribed
first difference bounds height zero and gives the same compact continuation.
The resulting theorem inhabits the exact path/ray interface from `Comparison`.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Filter _root_.Function _root_.Topology unitInterval
noncomputable section

/-! ## Coherent deleted-minor signs and source equation (8) -/

/-- Cramer's-rule coefficient for height zero as a function of tail height
coordinate `k`.  With zero-based indices, source `J_{k+2}` is the minor
obtained by deleting row `k.succ`, while `J_1` deletes row zero. -/
def heightZeroCramerCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (k : Fin d) : ℝ :=
  (-1 : ℝ) ^ (k.val + 2) *
    deletedRowMinor (gapHeightJacobianModel nodes) k.succ /
      deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩

/-- Exact coherent orientation of all maximal height-Jacobian minors.

The extra exponent `omitted.val + 1` converts the project's zero-based gap
index to the source's one-based `J_k`.  The common sign is required to
be `±1`, so this proposition contains both nonvanishing and the coherent
relative signs used in equation (8). -/
def CoherentHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    ∀ omitted : Fin (d + 1),
      0 < sign * (-1 : ℝ) ^ (omitted.val + 1) *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted

/-- Coherent signs in particular make every maximal minor nonzero. -/
theorem deletedRowMinor_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (hsigns : CoherentHeightMaximalMinorSigns nodes)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  intro hzero
  have h := hsign omitted
  rw [hzero, mul_zero] at h
  linarith

/-- Source equation (8): every Cramer coefficient expressing the omitted
height as a function of the other heights is strictly negative. -/
theorem heightZeroCramerCoefficient_neg_of_coherentSigns
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns nodes) (k : Fin d) :
    heightZeroCramerCoefficient nodes hd k < 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  let D₀ : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩
  let Dk : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) k.succ
  let sk : ℝ := (-1 : ℝ) ^ (k.val + 2)
  have h₀ : 0 < sign * (-1 : ℝ) * D₀ := by
    simpa only [D₀, Fin.val_zero, zero_add, pow_one] using
      hsign (⟨0, by omega⟩ : Fin (d + 1))
  have hk : 0 < sign * sk * Dk := by
    simpa only [Dk, sk, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsign k.succ
  have hsignSq : sign * sign = 1 := by
    rcases hsignValue with rfl | rfl <;> norm_num
  have hsignD₀ : sign * D₀ < 0 := by nlinarith
  have hsignSkDk : 0 < sign * (sk * Dk) := by
    nlinarith
  have hprod : sk * Dk * D₀ < 0 := by
    have hmul := mul_neg_of_pos_of_neg hsignSkDk hsignD₀
    calc
      sk * Dk * D₀ = (sign * (sk * Dk)) * (sign * D₀) := by
        symm
        calc
          (sign * (sk * Dk)) * (sign * D₀) =
              (sign * sign) * (sk * Dk * D₀) := by ring
          _ = sk * Dk * D₀ := by rw [hsignSq, one_mul]
      _ < 0 := hmul
  have hD₀ : D₀ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at h₀
    linarith
  have hD₀sq : 0 < D₀ ^ 2 := sq_pos_of_ne_zero hD₀
  rw [heightZeroCramerCoefficient]
  change sk * Dk / D₀ < 0
  rw [show sk * Dk / D₀ = (sk * Dk * D₀) / D₀ ^ 2 by
    field_simp]
  exact div_neg_of_neg_of_pos hprod hD₀sq

/-! ## The smallest local analytic/orientation input -/

/-- One convex tail-height chart carrying the integrated form of equation
(8).  The strict order reversal is local: it is asserted only for comparable
points in this chart's convex target. -/
structure OrientedTailHeightChart {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) where
  chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ)
  mem_source : nodes ∈ chart.source
  chart_eq :
    (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart
  convex_target : Convex ℝ chart.target
  height_zero_strictAnti : ∀ {y z : Fin d → ℝ},
    y ∈ chart.target → z ∈ chart.target →
      (∀ i, y i ≤ z i) → y ≠ z →
        (chart.symm z).height (0 : Fin (d + 1)) <
          (chart.symm y).height (0 : Fin (d + 1))

/-- Ordinary proposition reserved for the exact remaining local analytic
input.  Continuity of height zero follows from the same envelope derivative
calculation as the Jacobian.  `oriented_chart` is the inverse-function
theorem plus coherent Cramer signs, shrunk to a convex target neighborhood.
-/
def TailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous
    (fun nodes : EndpointArray d A B ↦
      nodes.height (0 : Fin (d + 1))) ∧
    ∀ (_hd : 1 ≤ d) (nodes : EndpointArray d A B),
      Nonempty (OrientedTailHeightChart nodes)

/-- The local oriented charts make the tail-height map a genuine local
homeomorphism. -/
theorem tailGapHeight_isLocalHomeomorph_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    IsLocalHomeomorph
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) := by
  intro nodes
  let e := (hlocal.2 hd nodes).some
  exact ⟨e.chart, e.mem_source, e.chart_eq⟩

/-- Consequently all tail heights vary continuously. -/
theorem continuous_tailGapHeight_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    Continuous
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
  (tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd).continuous

lemma OrientedTailHeightChart.tail_mem_target
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    tailGapHeight nodes ∈ e.chart.target := by
  rw [e.chart_eq]
  exact e.chart.map_source e.mem_source

@[simp]
lemma OrientedTailHeightChart.symm_tail_eq
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    e.chart.symm (tailGapHeight nodes) = nodes := by
  rw [e.chart_eq]
  exact e.chart.left_inv e.mem_source

/-! ## Checked local affine lifting -/

/-! ## Source-oriented local steps based at an endpoint array -/

/-! ## Compactness kernel for maximal continuation -/

/-- Reconstruct consecutive differences from height zero and the tail-height
vector. -/
def differenceOfBaseTail {d : ℕ} (z : ℝ × (Fin d → ℝ)) : Fin d → ℝ :=
  fun i ↦ if hi : i.val = 0 then z.2 i - z.1
    else z.2 i - z.2 ⟨i.val - 1, by omega⟩

lemma continuous_differenceOfBaseTail {d : ℕ} :
    Continuous (differenceOfBaseTail :
      ℝ × (Fin d → ℝ) → Fin d → ℝ) := by
  apply continuous_pi
  intro i
  unfold differenceOfBaseTail
  split_ifs
  · fun_prop
  · fun_prop

lemma differenceOfBaseTail_height_eq_gapDifference
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    differenceOfBaseTail
      (nodes.height (0 : Fin (d + 1)), tailGapHeight nodes) =
        gapDifference nodes := by
  funext i
  unfold differenceOfBaseTail gapDifference
  split_ifs with hi
  · have hcast : i.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      exact hi
    rw [hcast]
    rfl
  · let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    simp only [tailGapHeight]
    rw [hjsucc]

/-- Endpoint arrays whose tail vector lies in `K` and whose first height lies
in `[a,b]`. -/
def tailHeightSlab {d : ℕ} {A B : ℝ}
    (K : Set (Fin d → ℝ)) (a b : ℝ) : Set (EndpointArray d A B) :=
  {nodes | tailGapHeight nodes ∈ K ∧
    nodes.height (0 : Fin (d + 1)) ∈ Set.Icc a b}

/-- The compactness fact used at every finite maximal-lift endpoint.

The proof is deliberately routed through the global difference
homeomorphism.  On the slab, `(height 0, tailHeight)` lies in the compact box
`[a,b] × K`; `differenceOfBaseTail` maps this box to a bounded set containing
all gap-difference vectors.  The slab is closed, so its image under the
homeomorphism is closed and bounded in finite-dimensional Euclidean space. -/
theorem isCompact_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ) :
    IsCompact (tailHeightSlab (A := A) (B := B) K a b) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    (hhomeomorph hAB).homeomorph gapDifference
  let box : Set (ℝ × (Fin d → ℝ)) := Set.Icc a b ×ˢ K
  have hbox : IsCompact box := isCompact_Icc.prod hK
  have hslabClosed :
      IsClosed (tailHeightSlab (A := A) (B := B) K a b) := by
    have htail : Continuous
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
      continuous_tailGapHeight_of_localOrientation hlocal hd
    exact (hK.isClosed.preimage htail).inter
      (isClosed_Icc.preimage hlocal.1)
  have himageClosed :
      IsClosed (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    e.isClosedMap _ hslabClosed
  have hboundContainer :=
    (hbox.image continuous_differenceOfBaseTail).isBounded
  have himageSubset :
      e '' tailHeightSlab (A := A) (B := B) K a b ⊆
        differenceOfBaseTail '' box := by
    rintro y ⟨nodes, hnodes, rfl⟩
    refine ⟨(nodes.height (0 : Fin (d + 1)), tailGapHeight nodes), ?_, ?_⟩
    · exact ⟨hnodes.2, hnodes.1⟩
    · exact differenceOfBaseTail_height_eq_gapDifference nodes
  have himageBounded :=
    hboundContainer.subset himageSubset
  have himageCompact :
      IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨himageClosed, himageBounded⟩
  exact e.isCompact_image.mp himageCompact

/-- Sequential form of the compact slab, ready for the endpoint step in a
maximal-lift argument. -/
theorem exists_convergent_subsequence_of_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ)
    (nodes : ℕ → EndpointArray d A B)
    (hnodes : ∀ n, nodes n ∈ tailHeightSlab K a b) :
    ∃ limit ∈ tailHeightSlab K a b, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (nodes ∘ phi) atTop (𝓝 limit) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    endpointArrayLogRatioHomeomorph hAB
  have hslab : IsCompact (tailHeightSlab (A := A) (B := B) K a b) :=
    isCompact_tailHeightSlab hd hAB hhomeomorph hlocal hK a b
  have himage : IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    hslab.image e.continuous
  obtain ⟨z, hz, phi, hphi, htend⟩ := himage.isSeqCompact
    (fun n ↦ ⟨nodes n, hnodes n, rfl⟩)
  refine ⟨e.symm z, ?_, phi, hphi, ?_⟩
  · obtain ⟨limit, hlimit, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hlimit
  · have hpull := (e.symm.continuous.tendsto z).comp htend
    convert hpull using 1
    funext n
    simp

/-! ## Generic compact continuation for a local homeomorphism -/

/-- A lift of the prefix `[0,u]` of a real-parameterized curve.  Keeping the
domain as an ambient real function makes restriction and chart-local gluing
literal, while continuity is required only on the relevant closed interval. -/
structure PrefixLift {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (gamma : ℝ → X) (e0 : E) (u : ℝ) where
  toFun : ℝ → E
  continuousOn : ContinuousOn toFun (Set.Icc 0 u)
  zero_eq : toFun 0 = e0
  map_eq : Set.EqOn (f ∘ toFun) gamma (Set.Icc 0 u)

namespace PrefixLift

instance {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u : ℝ} :
    CoeFun (PrefixLift f gamma e0 u) (fun _ ↦ ℝ → E) :=
  ⟨PrefixLift.toFun⟩

/-- The constant lift of a zero-length prefix. -/
def zero {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} (hzero : f e0 = gamma 0) :
    PrefixLift f gamma e0 0 where
  toFun := fun _ ↦ e0
  continuousOn := continuous_const.continuousOn
  zero_eq := rfl
  map_eq := by
    intro t ht
    have ht0 : t = 0 := by exact le_antisymm ht.2 ht.1
    subst t
    exact hzero

/-- Restricting a prefix lift to an earlier nonnegative endpoint. -/
def restrict {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (_hv : 0 ≤ v) (hvu : v ≤ u) :
    PrefixLift f gamma e0 v where
  toFun := L
  continuousOn := L.continuousOn.mono fun _ ht ↦
    ⟨ht.1, ht.2.trans hvu⟩
  zero_eq := L.zero_eq
  map_eq := by
    intro t ht
    exact L.map_eq ⟨ht.1, ht.2.trans hvu⟩

/-- Extend a prefix inside one local-homeomorphism chart.  On the overlap the
old lift and the chart inverse agree by the left inverse law, so this is an
actual continuous gluing rather than an independent choice of branch. -/
def appendChart {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (hu : 0 ≤ u) (_huv : u ≤ v)
    (chart : OpenPartialHomeomorph E X) (hsource : L u ∈ chart.source)
    (hchart : f = chart) (hgamma : Continuous gamma)
    (htarget : ∀ t ∈ Set.Icc u v, gamma t ∈ chart.target) :
    PrefixLift f gamma e0 v where
  toFun t := if t ≤ u then L t else chart.symm (gamma t)
  continuousOn := by
    apply ContinuousOn.if (p := fun t : ℝ ↦ t ≤ u)
    · intro t ht
      have htEq : t = u := by
        have htfront := ht.2
        change t ∈ frontier (Set.Iic u) at htfront
        simpa using htfront
      subst t
      have hmap : f (L u) = gamma u :=
        L.map_eq ⟨hu, le_rfl⟩
      calc
        L u = chart.symm (chart (L u)) := (chart.left_inv hsource).symm
        _ = chart.symm (f (L u)) :=
          congrArg chart.symm (congrFun hchart (L u)).symm
        _ = chart.symm (gamma u) := by rw [hmap]
    · apply L.continuousOn.mono
      rintro t ⟨ht, htclosure⟩
      have htu : t ≤ u := by
        change t ∈ closure (Set.Iic u) at htclosure
        rwa [closure_Iic] at htclosure
      exact ⟨ht.1, htu⟩
    · apply chart.continuousOn_invFun.comp hgamma.continuousOn
      rintro t ⟨ht, htclosure⟩
      have hut : u ≤ t := by
        rw [show {a : ℝ | ¬ a ≤ u} = Set.Ioi u by ext; simp] at htclosure
        rwa [closure_Ioi] at htclosure
      exact htarget t ⟨hut, ht.2⟩
  zero_eq := by
    simp only [if_pos hu, L.zero_eq]
  map_eq := by
    intro t ht
    by_cases htu : t ≤ u
    · simp only [Function.comp_apply, if_pos htu]
      exact L.map_eq ⟨ht.1, htu⟩
    · simp only [Function.comp_apply, if_neg htu]
      rw [hchart]
      exact chart.right_inv (htarget t ⟨le_of_not_ge htu, ht.2⟩)

end PrefixLift

/-- Compact-continuation theorem for local homeomorphisms.

Every finite prefix has a unique branch because the total space is
Hausdorff and the map is locally injective.  Reachable prefix lengths form
an open set by `PrefixLift.appendChart`.  Sequential compactness of the set
containing every reachable endpoint makes that set closed: endpoints along
a convergent sequence of prefix lengths have a convergent subsequence, and
one final chart glues in the limiting prefix.  Connectedness of `[0,T]` then
gives a lift of the entire curve. -/
theorem exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {T : ℝ}
    (hloc : IsLocalHomeomorph f) (hgamma : Continuous gamma)
    (hT : 0 ≤ T) (hzero : f e0 = gamma 0)
    {K : Set E} (hK : IsSeqCompact K)
    (hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift f gamma e0 u, L u ∈ K) :
    Nonempty (PrefixLift f gamma e0 T) := by
  let Q := {u : ℝ // u ∈ Set.Icc 0 T}
  let S : Set Q := {u | Nonempty (PrefixLift f gamma e0 u.1)}
  have hSseq : IsSeqClosed S := by
    intro q p hq hp
    let L : ∀ n, PrefixLift f gamma e0 (q n).1 :=
      fun n ↦ (hq n).some
    let endpoint : ℕ → E := fun n ↦ L n (q n).1
    have hendpointK : ∀ n, endpoint n ∈ K := by
      intro n
      exact hendpoint (q n).2 (L n)
    obtain ⟨e, heK, phi, hphi, hephi⟩ := hK hendpointK
    have hqphi : Tendsto (fun n ↦ (q (phi n)).1) atTop (𝓝 p.1) := by
      exact (continuous_subtype_val.tendsto p).comp (hp.comp hphi.tendsto_atTop)
    have hmapEndpoint : ∀ n, f (endpoint n) = gamma (q n).1 := by
      intro n
      exact (L n).map_eq ⟨(q n).2.1, le_rfl⟩
    have hfe : f e = gamma p.1 := by
      have hleft := (hloc.continuous.tendsto e).comp hephi
      have hright := (hgamma.tendsto p.1).comp hqphi
      have hright' : Tendsto (fun n ↦ f (endpoint (phi n))) atTop
          (𝓝 (gamma p.1)) := by
        convert hright using 1
        funext n
        exact hmapEndpoint (phi n)
      exact tendsto_nhds_unique hleft hright'
    obtain ⟨chart, hesource, hchart⟩ := hloc e
    have hgammaTarget : gamma p.1 ∈ chart.target := by
      rw [← hfe, hchart]
      exact chart.map_source hesource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      p.1 hgammaTarget
    by_cases habove : ∃ n, p.1 ≤ (q n).1
    · obtain ⟨n, hn⟩ := habove
      exact ⟨(L n).restrict p.2.1 hn⟩
    · have hbelow : ∀ n, (q n).1 < p.1 := by
        intro n
        exact lt_of_not_ge fun h ↦ habove ⟨n, h⟩
      have heventSource : ∀ᶠ n in atTop, endpoint (phi n) ∈ chart.source :=
        hephi.eventually (chart.open_source.mem_nhds hesource)
      have heventBall : ∀ᶠ n in atTop,
          (q (phi n)).1 ∈ Metric.ball p.1 eps :=
        hqphi.eventually (Metric.ball_mem_nhds p.1 heps)
      obtain ⟨n, hnsource, hnball⟩ :=
        (heventSource.and heventBall).exists
      have htarget : ∀ t ∈ Set.Icc (q (phi n)).1 p.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq] at hnball ⊢
        have hleft := hbelow (phi n)
        have habsLeft : |(q (phi n)).1 - p.1| = p.1 - (q (phi n)).1 := by
          rw [abs_of_nonpos (sub_nonpos.mpr hleft.le)]
          ring
        have habs : |t - p.1| = p.1 - t := by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          ring
        rw [habsLeft] at hnball
        rw [habs]
        have hqt := ht.1
        linarith
      exact ⟨(L (phi n)).appendChart (q (phi n)).2.1
        (hbelow (phi n)).le chart hnsource hchart hgamma htarget⟩
  have hSclosed : IsClosed S := hSseq.isClosed
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    let L : PrefixLift f gamma e0 q.1 := hq.some
    obtain ⟨chart, hsource, hchart⟩ := hloc (L q.1)
    have hmap : f (L q.1) = gamma q.1 :=
      L.map_eq ⟨q.2.1, le_rfl⟩
    have hgammaTarget : gamma q.1 ∈ chart.target := by
      exact hmap ▸ (congrFun hchart (L q.1)).symm ▸
        chart.map_source hsource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      q.1 hgammaTarget
    let V : Set Q := {r | r.1 < q.1 + eps}
    have hVopen : IsOpen V := by
      exact isOpen_lt continuous_subtype_val continuous_const
    have hqV : q ∈ V := by
      dsimp only [V]
      exact lt_add_of_pos_right q.1 heps
    apply Filter.mem_of_superset (hVopen.mem_nhds hqV)
    intro r hr
    by_cases hrq : r.1 ≤ q.1
    · exact ⟨L.restrict r.2.1 hrq⟩
    · have hqr : q.1 ≤ r.1 := le_of_not_ge hrq
      have htarget : ∀ t ∈ Set.Icc q.1 r.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |t - q.1| = t - q.1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        rw [habs]
        have hrv : r.1 < q.1 + eps := hr
        have htr := ht.2
        linarith
      exact ⟨L.appendChart q.2.1 hqr chart hsource hchart hgamma htarget⟩
  have hSnonempty : S.Nonempty := by
    let q0 : Q := ⟨0, ⟨le_rfl, hT⟩⟩
    exact ⟨q0, ⟨PrefixLift.zero hzero⟩⟩
  letI : PreconnectedSpace Q :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSnonempty
  let qT : Q := ⟨T, ⟨hT, le_rfl⟩⟩
  have hqT : qT ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hqT

/-! ## Applying compact continuation to the oriented tail-height map -/

/-- The real-parameter version of `tailLine`. -/
def realTailLine {d : ℕ} (y z : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ (1 - t) * y i + t * z i

lemma continuous_realTailLine {d : ℕ} (y z : Fin d → ℝ) :
    Continuous (realTailLine y z) := by
  unfold realTailLine
  fun_prop

/-- A lifted increasing affine tail prefix cannot finish above its initial
height zero.  The extreme-value proof is the formal version of the source's
monotonicity sentence: if a maximum occurred at positive time, a sufficiently
close point immediately to its left would lie in the same oriented chart and
have strictly larger height zero. -/
theorem PrefixLift.heightZero_endpoint_le_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) ≤
      s.height (0 : Fin (d + 1)) := by
  let H : ℝ → ℝ := fun t ↦ (L t).height (0 : Fin (d + 1))
  have hHcont : ContinuousOn H (Set.Icc 0 u) := by
    exact hlocal.1.comp_continuousOn L.continuousOn
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, ⟨le_rfl, hu.1⟩⟩ hHcont
  by_contra hnot
  have hendGt : H 0 < H u := by
    simpa only [H, L.zero_eq] using lt_of_not_ge hnot
  have htGt : H 0 < H t := hendGt.trans_le (hmax ⟨hu.1, le_rfl⟩)
  have htpos : 0 < t := by
    exact lt_of_le_of_ne ht.1 fun htzero ↦ by
      subst t
      exact (lt_irrefl _ htGt).elim
  let e := (hlocal.2 hd (L t)).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] t :=
    (L.continuousOn t ht).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds e.mem_source)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (t / 2) (eps / 2)
  let r : ℝ := t - delta
  have hdelta : 0 < delta := by
    exact lt_min (half_pos htpos) (half_pos heps)
  have hdeltat : delta < t :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self htpos)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hrlt : r < t := by dsimp only [r]; linarith
  have hrmem : r ∈ Set.Icc 0 u := by
    constructor
    · dsimp only [r]
      linarith
    · exact hrlt.le.trans ht.2
  have hrball : r ∈ Metric.ball t eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |r - t| = delta := by
      dsimp only [r]
      rw [show t - delta - t = -delta by ring, abs_neg,
        abs_of_pos hdelta]
    rw [habs]
    exact hdeltaeps
  have hrsource : L r ∈ e.chart.source :=
    hball ⟨hrball, hrmem⟩
  have htailR : tailGapHeight (L r) =
      realTailLine (tailGapHeight s) y r :=
    L.map_eq hrmem
  have htailT : tailGapHeight (L t) =
      realTailLine (tailGapHeight s) y t :=
    L.map_eq ht
  have htailLe : ∀ i, tailGapHeight (L r) i ≤
      tailGapHeight (L t) i := by
    intro i
    rw [htailR, htailT]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight (L r) ≠ tailGapHeight (L t) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailR, htailT] at hi
    unfold realTailLine at hi
    nlinarith
  have htailEqChartR : tailGapHeight (L r) = e.chart (L r) :=
    congrFun e.chart_eq (L r)
  have htailRtarget : tailGapHeight (L r) ∈ e.chart.target := by
    exact htailEqChartR.symm ▸ e.chart.map_source hrsource
  have hdecrease := e.height_zero_strictAnti
    htailRtarget e.tail_mem_target htailLe htailNe
  have hsymmR : e.chart.symm (tailGapHeight (L r)) = L r := by
    exact (congrArg e.chart.symm htailEqChartR).trans
      (e.chart.left_inv hrsource)
  rw [hsymmR, e.symm_tail_eq] at hdecrease
  exact (not_lt_of_ge (hmax hrmem) hdecrease).elim

/-- Reparameterize a subinterval of an affine-tail prefix back to `[0,1]`.
The new target curve is definitionally the affine segment between the two
actual endpoint tail vectors. -/
def PrefixLift.reparamRealTailLine
    {d : ℕ} {A B : ℝ} {s : EndpointArray d A B}
    {y : Fin d → ℝ} {u a b : ℝ}
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u)
    (ha : a ∈ Set.Icc 0 u) (hb : b ∈ Set.Icc 0 u) (hab : a ≤ b) :
    PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight (L a)) (tailGapHeight (L b)))
      (L a) 1 where
  toFun t := L ((1 - t) * a + t * b)
  continuousOn := by
    apply L.continuousOn.comp (by fun_prop)
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
  zero_eq := by simp
  map_eq := by
    intro t ht
    have hw : (1 - t) * a + t * b ∈ Set.Icc 0 u := by
      constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
    have hmain := L.map_eq hw
    have hleft := L.map_eq ha
    have hright := L.map_eq hb
    simp only [Function.comp_apply] at hmain hleft hright ⊢
    funext i
    have hmaini := congrFun hmain i
    have hlefti := congrFun hleft i
    have hrighti := congrFun hright i
    unfold realTailLine at hmaini hlefti hrighti ⊢
    rw [hmaini, hlefti, hrighti]
    ring

/-- Strict form of the endpoint estimate for a positive-length increasing
tail prefix.  A short first piece lies in the initial oriented chart and
strictly lowers height zero; the non-strict extreme-value estimate applied to
the remaining reparameterized suffix preserves that strict loss. -/
theorem PrefixLift.heightZero_endpoint_lt_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu0 : 0 < u) (_hu1 : u ≤ 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) <
      s.height (0 : Fin (d + 1)) := by
  let e := (hlocal.2 hd s).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] 0 :=
    (L.continuousOn 0 ⟨le_rfl, hu0.le⟩).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds (by simpa [L.zero_eq] using e.mem_source))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (u / 2) (eps / 2)
  have hdelta : 0 < delta :=
    lt_min (half_pos hu0) (half_pos heps)
  have hdeltau : delta < u :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hu0)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hdeltamem : delta ∈ Set.Icc 0 u := ⟨hdelta.le, hdeltau.le⟩
  have hdeltaball : delta ∈ Metric.ball (0 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact hdeltaeps
  have hdeltasource : L delta ∈ e.chart.source :=
    hball ⟨hdeltaball, hdeltamem⟩
  have htailZero : tailGapHeight (L 0) = tailGapHeight s := by
    rw [L.zero_eq]
  have htailDelta : tailGapHeight (L delta) =
      realTailLine (tailGapHeight s) y delta :=
    L.map_eq hdeltamem
  have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight (L delta) i := by
    intro i
    rw [htailDelta]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight s ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have htailDeltaTarget : tailGapHeight (L delta) ∈ e.chart.target := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact heq.symm ▸ e.chart.map_source hdeltasource
  have hfirst := e.height_zero_strictAnti e.tail_mem_target
    htailDeltaTarget htailLe htailNe
  have hsymmDelta : e.chart.symm (tailGapHeight (L delta)) = L delta := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact (congrArg e.chart.symm heq).trans
      (e.chart.left_inv hdeltasource)
  rw [e.symm_tail_eq, hsymmDelta] at hfirst
  let M := L.reparamRealTailLine hdeltamem ⟨hu0.le, le_rfl⟩ hdeltau.le
  have htailU : tailGapHeight (L u) =
      realTailLine (tailGapHeight s) y u :=
    L.map_eq ⟨hu0.le, le_rfl⟩
  have hsuffixLe : ∀ i, tailGapHeight (L delta) i ≤
      tailGapHeight (L u) i := by
    intro i
    rw [htailDelta, htailU]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hsuffixNe : tailGapHeight (L u) ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailU, htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have hsuffix := M.heightZero_endpoint_le_of_realTailLine hd hlocal
    (L delta) (tailGapHeight (L u)) hsuffixLe hsuffixNe
    (u := 1) ⟨zero_le_one, le_rfl⟩
  have hfinal := hsuffix.trans_lt hfirst
  change (L ((1 - (1 : ℝ)) * delta + (1 : ℝ) * u)).height
      (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) at hfinal
  simpa using hfinal

/-- The globally continued increasing affine-tail lift, including the
source-required strict antitonicity of height zero. -/
theorem exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ g : C(I, EndpointArray d A B),
      g 0 = s ∧
      (∀ u i, tailGapHeight (g u) i =
        (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
      StrictAnti (fun u : I ↦
        (g u).height (0 : Fin (d + 1))) := by
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph s.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := realTailLine (tailGapHeight s) y
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight s) y) 1
      (s.height (0 : Fin (d + 1)))
  have hsegment : IsCompact (segment ℝ (tailGapHeight s) y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      s.admissibleInterval hhomeomorph hlocal hsegment 1
        (s.height (0 : Fin (d + 1))) nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_realTailLine _ _
  have hzero : tailGapHeight s = gamma 0 := by
    funext i
    simp [gamma, realTailLine]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 1 →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma s u, L u ∈ K := by
    intro u hu L
    constructor
    · have htail : tailGapHeight (L u) = gamma u :=
        L.map_eq ⟨hu.1, le_rfl⟩
      rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u, hu, ?_⟩
      funext i
      simp only [gamma, realTailLine, AffineMap.lineMap_apply_module,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · exact L.heightZero_endpoint_le_of_realTailLine hd hlocal s y hle hne hu
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma (T := 1) zero_le_one hzero hKseq hendpoint
  let g : C(I, EndpointArray d A B) :=
    ⟨fun u ↦ L u, continuousOn_iff_continuous_restrict.mp L.continuousOn⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · exact L.zero_eq
  · intro u i
    have hmap := L.map_eq u.2
    have hi := congrFun hmap i
    simpa only [Function.comp_apply, gamma, realTailLine] using hi
  · intro u v huv
    have huMem : (u : ℝ) ∈ Set.Icc 0 1 := u.2
    have hvMem : (v : ℝ) ∈ Set.Icc 0 1 := v.2
    let M := L.reparamRealTailLine huMem hvMem huv.le
    have htailU : tailGapHeight (L (u : ℝ)) = gamma (u : ℝ) :=
      L.map_eq huMem
    have htailV : tailGapHeight (L (v : ℝ)) = gamma (v : ℝ) :=
      L.map_eq hvMem
    have htailLe : ∀ i, tailGapHeight (L (u : ℝ)) i ≤
        tailGapHeight (L (v : ℝ)) i := by
      intro i
      rw [htailU, htailV]
      dsimp only [gamma, realTailLine]
      have hi := hle i
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hex : ∃ i, tailGapHeight s i < y i := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      exact le_antisymm (h i) (hle i)
    obtain ⟨i0, hi0⟩ := hex
    have htailNe : tailGapHeight (L (v : ℝ)) ≠
        tailGapHeight (L (u : ℝ)) := by
      intro heq
      have hi := congrFun heq i0
      rw [htailU, htailV] at hi
      dsimp only [gamma, realTailLine] at hi
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hstrict := M.heightZero_endpoint_lt_of_realTailLine hd hlocal
      (L (u : ℝ)) (tailGapHeight (L (v : ℝ))) htailLe htailNe
      (u := 1) zero_lt_one (by rfl)
    change (L ((1 - (1 : ℝ)) * (u : ℝ) + (1 : ℝ) * (v : ℝ))).height
      (0 : Fin (d + 1)) <
        (L (u : ℝ)).height (0 : Fin (d + 1)) at hstrict
    norm_num at hstrict
    exact hstrict

/-- The source's diagonal decreasing tail ray, with real time parameter. -/
def decreasingTailRay {d : ℕ} (y : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ y i - t

lemma continuous_decreasingTailRay {d : ℕ} (y : Fin d → ℝ) :
    Continuous (decreasingTailRay y) := by
  unfold decreasingTailRay
  fun_prop

/-- Stop and reparameterize a decreasing-ray prefix once its first
consecutive difference has fallen to the prescribed level.  The intermediate
value theorem supplies the first required time; positivity follows because
the initial difference is strictly larger. -/
theorem exists_stopped_decreasingRay_of_prefix_endpoint_le
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩)
    {u : ℝ} (hu : 0 ≤ u)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (decreasingTailRay (tailGapHeight r)) r u)
    (hend : gapDifference (L u) ⟨0, hd⟩ ≤ c) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let F : ℝ → ℝ := fun t ↦ gapDifference (L t) ⟨0, hd⟩
  have hFcont : ContinuousOn F (Set.Icc 0 u) := by
    have hdiffCont :=
      (hhomeomorph r.admissibleInterval).continuous.comp_continuousOn
        L.continuousOn
    simpa only [F, Function.comp_def] using
      (continuous_apply ⟨0, hd⟩).comp_continuousOn hdiffCont
  have hFzero : F 0 = gapDifference r ⟨0, hd⟩ := by
    simp only [F, L.zero_eq]
  have hcIcc : c ∈ Set.Icc (F u) (F 0) := by
    exact ⟨hend, by simpa only [hFzero] using hc.le⟩
  obtain ⟨alpha, halphaMem, halphaEq⟩ :=
    intermediate_value_Icc' hu hFcont hcIcc
  have halpha : 0 < alpha := by
    exact lt_of_le_of_ne halphaMem.1 fun hzero ↦ by
      subst alpha
      rw [hFzero] at halphaEq
      exact (ne_of_gt hc) halphaEq
  let g : C(I, EndpointArray d A B) :=
    ⟨fun v ↦ L ((v : ℝ) * alpha), by
      apply L.continuousOn.comp_continuous
      · fun_prop
      · intro v
        exact ⟨mul_nonneg v.2.1 halpha.le,
          (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩⟩
  refine ⟨alpha, halpha, g, ?_, ?_, ?_⟩
  · change L ((0 : ℝ) * alpha) = r
    rw [zero_mul, L.zero_eq]
  · intro v i
    have htime : (v : ℝ) * alpha ∈ Set.Icc 0 u :=
      ⟨mul_nonneg v.2.1 halpha.le,
        (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩
    have hmap := L.map_eq htime
    have hi := congrFun hmap i
    simpa only [Function.comp_apply, decreasingTailRay, g] using hi
  · change gapDifference (L ((1 : ℝ) * alpha)) ⟨0, hd⟩ = c
    simpa only [one_mul, F] using halphaEq

/-- Global continuation of the decreasing diagonal ray until its first
difference reaches any prescribed lower value.  Under the negation of such a
stopped lift, every reachable prefix has first difference `> c`; hence height
zero is bounded above by `tail₀(r)-c`, while all tail vectors remain in a
fixed compact segment.  Compact continuation reaches a time at which the
elementary bound `height ≥ 1` forces the first difference below `c`, and the
preceding stopping lemma gives the contradiction. -/
theorem exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let i0 : Fin d := ⟨0, hd⟩
  let T : ℝ := tailGapHeight r i0 - c
  have hi0cast : i0.castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext
    rfl
  have honeR : 1 ≤ r.height (0 : Fin (d + 1)) :=
    one_le_height r (0 : Fin (d + 1))
  have hdiffR : gapDifference r i0 =
      tailGapHeight r i0 - r.height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have hT : 0 < T := by
    rw [hdiffR] at hc
    dsimp only [T]
    linarith
  by_contra hno
  push_neg at hno
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph r.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := decreasingTailRay (tailGapHeight r)
  let tailEnd : Fin d → ℝ := gamma T
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight r) tailEnd) 1 T
  have hsegment : IsCompact (segment ℝ (tailGapHeight r) tailEnd) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      r.admissibleInterval hhomeomorph hlocal hsegment 1 T nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_decreasingTailRay _
  have hzero : tailGapHeight r = gamma 0 := by
    funext i
    simp [gamma, decreasingTailRay]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma r u, L u ∈ K := by
    intro u hu L
    have htail : tailGapHeight (L u) = gamma u :=
      L.map_eq ⟨hu.1, le_rfl⟩
    have hdiff : gapDifference (L u) i0 =
        tailGapHeight (L u) i0 -
          (L u).height (0 : Fin (d + 1)) := by
      rw [gapDifference, tailGapHeight, hi0cast]
    have hdiffGt : c < gapDifference (L u) i0 := by
      by_contra hleDiff
      have hstopped := exists_stopped_decreasingRay_of_prefix_endpoint_le
        hd hhomeomorph r c hc hu.1 L (le_of_not_gt hleDiff)
      obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ := hstopped
      exact hno alpha halpha g hg0 hgtail hgend
    constructor
    · rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u / T, ?_, ?_⟩
      · constructor
        · exact div_nonneg hu.1 hT.le
        · exact (div_le_one hT).2 hu.2
      · funext i
        simp only [tailEnd, gamma, decreasingTailRay,
          AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        field_simp
        ring
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · rw [hdiff, htail] at hdiffGt
        have hgammaUi : gamma u i0 = tailGapHeight r i0 - u := rfl
        rw [hgammaUi] at hdiffGt
        dsimp only [T]
        have hu0 := hu.1
        linarith
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma hT.le hzero hKseq hendpoint
  have htailFinal : tailGapHeight (L T) = gamma T :=
    L.map_eq ⟨hT.le, le_rfl⟩
  have hdiffFinal : gapDifference (L T) i0 =
      tailGapHeight (L T) i0 -
        (L T).height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have honeFinal : 1 ≤ (L T).height (0 : Fin (d + 1)) :=
    one_le_height (L T) (0 : Fin (d + 1))
  have hfinalLe : gapDifference (L T) i0 ≤ c := by
    rw [hdiffFinal, htailFinal]
    dsimp only [gamma, decreasingTailRay, T]
    linarith
  obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ :=
    exists_stopped_decreasingRay_of_prefix_endpoint_le
      hd hhomeomorph r c hc hT.le L hfinalLe
  exact hno alpha halpha g hg0 hgtail hgend

/-- The complete source path/ray orientation interface, derived from the
global gap-difference homeomorphism and the single local coherent-orientation
input.  No global path or ray is included among the assumptions. -/
theorem gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B) :
    GapHeightPathRayOrientationStatement d A B where
  lift_increasingSegment hd s y hle hne :=
    exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal s y hle hne
  lift_decreasingRay_to_firstDifference hd r c hc :=
    exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal r c hc

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/SignBridge.lean` -/

/-!
# Sign-convention bridge for the height-Jacobian maximal minors

`Minors` proves that the zero-based row cofactors
`(-1)^omitted * deletedRowMinor` all have one strict sign.  `Orientation`
uses the source's one-based exponent `(-1)^(omitted+1)` and records the
remaining common sign explicitly as `±1`.  This file proves that these are
the same orientation statement, including dimension zero.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Convert the unconditional alternating-cofactor convention from
`Minors` to the explicit `±1`, one-based convention used by `Orientation`.

If all zero-based cofactors are negative, the witness is `+1`; if they are
positive, the witness is `-1`.  The proof is dimension-free, so the unique
minor in dimension zero is handled without a separate vacuous case. -/
theorem coherentHeightMaximalMinorSigns_of_alternating
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (h : AlternatingHeightMaximalMinorSigns nodes) :
    CoherentHeightMaximalMinorSigns nodes := by
  rcases h with hneg | hpos
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro omitted
    have hstrict := neg_pos.mpr (hneg omitted)
    calc
      0 < -((-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted) := hstrict
      _ = (1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro omitted
    calc
      0 < (-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted :=
        hpos omitted
      _ = (-1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring

/-- Unconditional coherent maximal-minor orientation in the canonical
`Orientation` convention. -/
theorem coherentHeightMaximalMinorSigns_unconditional
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    CoherentHeightMaximalMinorSigns nodes :=
  coherentHeightMaximalMinorSigns_of_alternating nodes
    (alternatingHeightMaximalMinorSigns nodes)

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/LocalHomeomorph.lean` -/

/-!
# The local homeomorphism of consecutive gap-height differences

This file passes from the checked coordinate derivative of each individual
gap height to the source map

`Γ_i = h_{i+1} - h_i`.

Continuity is unconditional.  The sole algebraic input to the inverse
function theorem is isolated as nonvanishing of the determinant of the
explicit consecutive-row-difference matrix.  No inhabitant of that
proposition is asserted here; it is the output expected from the coherent
maximal-minor sign argument.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Filter _root_.Function _root_.Topology

noncomputable section

/-! ## The explicit Jacobian model -/

/-- Consecutive row differences of the checked gap-height Jacobian. -/
def gapDifferenceJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => gapHeightJacobianModel nodes i.succ j -
    gapHeightJacobianModel nodes i.castSucc j

/-- The exact algebraic residue of the local-homeomorphism argument.
It is deliberately a proposition, not an assumed theorem. -/
def GapDifferenceJacobianDeterminantCondition (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : EndpointArray d A B,
    Matrix.det (gapDifferenceJacobianModel nodes) ≠ 0

/-! ## `C¹` regularity of the local critical-value extension -/

private lemma contDiffAt_finset_sum_scalar_v3 {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

private lemma contDiffAt_finset_prod_scalar_v2 {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (1 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

/-- The rational coordinate gap-value map is `C¹` at every simplex point
and every evaluation point. -/
lemma contDiffAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    ContDiffAt ℝ 1 (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  apply contDiffAt_finset_sum_scalar_v3
  intro k _
  exact contDiffAt_const.mul (by
    simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
    let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
      fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
    have hfac : ∀ i ∈ Finset.univ.erase k,
        ContDiffAt ℝ 1 (fac i) (u.1, x) := by
      intro i hi
      exact contDiffAt_coordinateLagrangeFactorValue hAB u
        (Finset.mem_erase.mp hi).1.symm x 1
    exact contDiffAt_finset_prod_scalar_v2 1 (Finset.univ.erase k) fac
      (u.1, x) hfac)

/-- The genuine local critical-value branch is `C¹` at its base point. -/
lemma contDiffAt_localGapCriticalHeight_concrete {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (localGapCriticalHeight hAB u hd g
        (concreteGapCoordinateDerivativesAt hAB u g)) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  have hpair : ContDiffAt ℝ 1
      (fun v : Fin d → ℝ =>
        (v, localGapCriticalPoint hAB u hd g data v)) u.1 :=
    contDiffAt_id.prodMk
      (contDiffAt_localGapCriticalPoint hAB u hd g data)
  have hvalue : ContDiffAt ℝ 1 (coordinateGapValueMap A B g)
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact contDiffAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)
  simpa only [localGapCriticalHeight, coordinateGapValueMap,
    Function.comp_def] using hvalue.comp u.1 hpair

/-- The canonical ambient extension used for differentiation is `C¹` at
its base point. -/
lemma contDiffAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  apply (contDiffAt_localGapCriticalHeight_concrete hAB u hd g).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos hv]
  exact (heq hv).symm

/-! ## Continuity of genuine gap heights -/

lemma continuous_coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun u : {v : Fin d → ℝ //
      v ∈ endpointNodeSpace d A B} => coordinateGapHeight hAB u g) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hd0 : d = 0
  · subst d
    have heq : (fun v : {w : Fin 0 → ℝ //
        w ∈ endpointNodeSpace 0 A B} => coordinateGapHeight hAB v g) =
        fun _ => (1 : ℝ) := by
      funext v
      exact coordinateGapHeight_zero_dim hAB v g
    rw [heq]
    exact continuousAt_const
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hamb :=
      (hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).continuousAt
    have hcomp := hamb.comp continuousAt_subtype_val
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with v
    change coordinateGapHeight hAB v g =
      canonicalExtendedCoordinateGapHeight hAB u hd g v.1
    rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
      dif_pos v.2]

/-- Each compactly defined gap height is continuous in the induced endpoint
array topology. -/
theorem continuous_endpointArray_height_of_admissible {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  let H : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → ℝ :=
    fun u => coordinateGapHeight hAB u g
  have hH : Continuous H := continuous_coordinateGapHeight hAB g
  have heq : (fun nodes : EndpointArray d A B => nodes.height g) =
      H ∘ endpointArrayHomeomorph hAB := by
    funext nodes
    change nodes.height g = coordinateGapHeight hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ g
    rw [coordinateGapHeight, endpointArrayOfInterior_interior]
    rfl
  rw [heq]
  exact hH.comp (endpointArrayHomeomorph hAB).continuous

/-- Each gap height is continuous for arbitrary endpoint parameters.  At a
point of the domain, the endpoint array itself supplies the required
admissible-interval witness; if the domain is empty there are no points to
check. -/
theorem continuous_endpointArray_height {d : ℕ} {A B : ℝ}
    (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  rw [continuous_iff_continuousAt]
  intro nodes
  exact (continuous_endpointArray_height_of_admissible
    nodes.admissibleInterval g).continuousAt

/-! ## The ambient derivative of consecutive differences -/

/-- A total ambient representative of `Γ` based at one simplex point. -/
def canonicalExtendedCoordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i =>
    canonicalExtendedCoordinateGapHeight hAB u hd i.succ v -
      canonicalExtendedCoordinateGapHeight hAB u hd i.castSucc v

/-- Its checked differential, formed before choosing any matrix
coordinates. -/
def gapDifferenceDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ) -
      (concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem hasFDerivAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (gapDifferenceDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)

theorem contDiffAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateGapDifference hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)

/-- Every coordinate entry of the differential is literally the difference
of the two consecutive rows of `gapHeightJacobianModel`. -/
theorem gapDifferenceDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    gapDifferenceDifferentialAt hAB u hd (Pi.single j 1) i =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) i j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) -
      ((concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).fderiv,
    ← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc).fderiv,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model]
  rfl

/-- Matrix form of the preceding entrywise derivative theorem. -/
theorem gapDifferenceDifferentialAt_toMatrix_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (gapDifferenceDifferentialAt hAB u hd).toLinearMap =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact gapDifferenceDifferentialAt_basis_eq_model hAB u hd i j

/-- Therefore the determinant condition is exactly invertibility of the
actual ambient differential consumed by the inverse function theorem. -/
theorem gapDifferenceDifferentialAt_det_ne_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hdet : Matrix.det
      (gapDifferenceJacobianModel (endpointArrayOfInterior hAB u)) ≠ 0) :
    (gapDifferenceDifferentialAt hAB u hd).det ≠ 0 := by
  change LinearMap.det (gapDifferenceDifferentialAt hAB u hd).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix',
    gapDifferenceDifferentialAt_toMatrix_eq_model hAB u hd]
  exact hdet

/-! ## Restriction to the open simplex and inverse function theorem -/

/-- The genuine source map in the open-simplex chart. -/
def coordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => gapDifference (endpointArrayOfInterior hAB v)

lemma canonicalExtendedCoordinateGapDifference_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateGapDifference hAB u hd v.1 =
      coordinateGapDifference hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateGapDifference,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateGapDifference, gapDifference,
    coordinateGapHeight]
  rfl

/-- On the positive-dimensional simplex, the determinant condition gives
a local homeomorphism by the finite-dimensional `C¹` inverse function
theorem. -/
theorem isLocalHomeomorph_coordinateGapDifference_of_determinant
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B) (hd : 1 ≤ d)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    IsLocalHomeomorph (coordinateGapDifference (d := d) hAB) := by
  apply IsLocalHomeomorph.mk
  intro u
  let F := canonicalExtendedCoordinateGapDifference hAB u hd
  let L := gapDifferenceDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    gapDifferenceDifferentialAt_det_ne_zero hAB u hd
      (hdet (endpointArrayOfInterior hAB u))
  let eL : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    L.toContinuousLinearEquivOfDetNeZero hLdet
  have hFderiv : HasFDerivAt F (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    change HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateGapDifference hAB u hd
  have hFcont : ContDiffAt ℝ 1 F u.1 :=
    contDiffAt_canonicalExtendedCoordinateGapDifference hAB u hd
  let e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
    hFcont.toOpenPartialHomeomorph F hFderiv (by norm_num)
  have hue : u.1 ∈ e.source :=
    hFcont.mem_toOpenPartialHomeomorph_source hFderiv (by norm_num)
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  have hS : Nonempty S := ⟨u⟩
  let es : OpenPartialHomeomorph S (Fin d → ℝ) := e.subtypeRestr hS
  refine ⟨es, ?_, ?_⟩
  · simpa only [es, OpenPartialHomeomorph.subtypeRestr_source,
      Set.mem_preimage] using hue
  · intro v _hv
    change coordinateGapDifference hAB v = F v.1
    exact (canonicalExtendedCoordinateGapDifference_eq_coordinate
      hAB u v hd).symm

/-! ## Endpoint arrays, including dimension zero -/

private theorem isLocalHomeomorph_gapDifference_zero
    {A B : ℝ} (hAB : AdmissibleInterval A B) :
    IsLocalHomeomorph
      (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) := by
  let u0 : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hu0 : u0 ∈ endpointNodeSpace 0 A B := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · exact fun i => Fin.elim0 i
  let S := {u : Fin 0 → ℝ // u ∈ endpointNodeSpace 0 A B}
  letI : Unique S := {
    default := ⟨u0, hu0⟩
    uniq := fun v => Subtype.ext (Subsingleton.elim _ _) }
  let e0 : S ≃ₜ (Fin 0 → ℝ) :=
    Homeomorph.homeomorphOfUnique S (Fin 0 → ℝ)
  let e : EndpointArray 0 A B ≃ₜ (Fin 0 → ℝ) :=
    (endpointArrayHomeomorph hAB).trans e0
  have heq : (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) = e := by
    funext nodes
    exact Subsingleton.elim _ _
  rw [heq]
  exact e.isLocalHomeomorph

/-- Shortest checked route from the explicit determinant condition to the
canonical unconditional local-homeomorphism statement.  At each array, that
array supplies its own admissible-interval witness.  Thus arbitrary `A,B`,
including an empty endpoint-array domain, are handled honestly.  The `d = 0`
branch is discharged without invoking a positive-dimensional critical-point
theorem. -/
theorem gapDifference_localHomeomorphStatement_of_determinant
    (d : ℕ) (A B : ℝ)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    GapDifferenceLocalHomeomorphStatement d A B := by
  intro nodes
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  by_cases hd0 : d = 0
  · subst d
    exact (isLocalHomeomorph_gapDifference_zero hAB) nodes
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hcoord :=
      isLocalHomeomorph_coordinateGapDifference_of_determinant hAB hd hdet
    have hchart := (endpointArrayHomeomorph (d := d) hAB).isLocalHomeomorph
    have hcomp := hcoord.comp hchart
    have heq :
        (gapDifference : EndpointArray d A B → Fin d → ℝ) =
          coordinateGapDifference hAB ∘ endpointArrayHomeomorph hAB := by
      funext r
      change gapDifference r = gapDifference
        (endpointArrayOfInterior hAB
          ⟨r.interior, r.interior_mem_endpointNodeSpace⟩)
      rw [endpointArrayOfInterior_interior]
    rw [heq]
    exact hcomp nodes

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/TopologyPackage.lean` -/

/-!
# Unconditional topology package for the gap-difference map

This file closes the de Boor--Pinkus topology chain.  The coherent-minor
argument proves the explicit Jacobian determinant condition; the committed
inverse-function and properness arguments then promote that condition first
to a local homeomorphism and finally to the canonical global homeomorphism
statement.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- The explicit consecutive-difference Jacobian is nonsingular at every
endpoint array. -/
theorem gapDifference_jacobianDeterminantCondition
    (d : ℕ) (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition d A B := by
  intro nodes
  simpa only [gapDifferenceJacobianModel] using
    gapHeightJacobianModel_consecutiveDifference_det_ne_zero nodes

/-- The gap-difference map is unconditionally a local homeomorphism. -/
theorem gapDifference_localHomeomorphStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceLocalHomeomorphStatement d A B :=
  gapDifference_localHomeomorphStatement_of_determinant d A B
    (gapDifference_jacobianDeterminantCondition d A B)

/-- The canonical global homeomorphism statement for the gap-difference
map, obtained from local inversion and the committed properness theorem. -/
theorem gapDifference_homeomorphismStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph
    (gapDifference_localHomeomorphStatement d A B)

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/OrientedCharts.lean` -/

/-!
# Oriented local charts for the tail-height map

This file supplies the analytic input isolated by `Orientation.lean`.  The
tail heights have the height-Jacobian with row zero deleted.  Coherent signs
make this square differential invertible; the inverse function theorem then
gives a chart.  Cramer's rule identifies every partial derivative of the
omitted height with the strictly negative coefficient recorded in
`heightZeroCramerCoefficient`.  Integrating those derivatives along a line
segment in a convex target proves the required strict order reversal.
-/

namespace Randy1153.DeBoorPinkus

open _root_.Filter _root_.Function _root_.Topology
open scoped BigOperators _root_.Matrix

noncomputable section

/-! ## The tail-height differential -/

/-- An ambient representative of all heights except height zero. -/
def canonicalExtendedCoordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i => canonicalExtendedCoordinateGapHeight hAB u hd i.succ v

/-- The differential of the ambient tail-height representative. -/
def tailHeightDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem hasFDerivAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB u hd)
      (tailHeightDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ

theorem contDiffAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateTailHeight hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact contDiffAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ

theorem tailHeightDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    tailHeightDifferentialAt hAB u hd (Pi.single j 1) i =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) i.succ j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd i.succ).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd i.succ j

theorem tailHeightDifferentialAt_toMatrix_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (tailHeightDifferentialAt hAB u hd).toLinearMap =
      (gapHeightJacobianModel (endpointArrayOfInterior hAB u)).submatrix
        (0 : Fin (d + 1)).succAbove id := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simpa using tailHeightDifferentialAt_basis_eq_model hAB u hd i j

theorem tailHeightDifferentialAt_det_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    (tailHeightDifferentialAt hAB u hd).det =
      deletedRowMinor (gapHeightJacobianModel
        (endpointArrayOfInterior hAB u)) (0 : Fin (d + 1)) := by
  change LinearMap.det (tailHeightDifferentialAt hAB u hd).toLinearMap = _
  rw [← LinearMap.det_toMatrix',
    tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd]
  rfl

theorem tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (tailHeightDifferentialAt hAB u hd).det ≠ 0 := by
  rw [tailHeightDifferentialAt_det_eq_deletedZero hAB u hd]
  exact deletedRowMinor_ne_zero_of_coherentSigns hsigns _

/-! ## The deleted-row Cramer identity -/

private lemma updateRow_tailMatrix_eq_permuted_deletedRow
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    (H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0) =
      (H.submatrix k.succ.succAbove id).submatrix k.cycleRange id := by
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  ext i j
  by_cases hik : i = k
  · subst i
    simp
  · by_cases hil : i < k
    · rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_lt hil]
      rw [Fin.succAbove_succ_of_le k (i + 1) (by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one_of_lt' (by omega)]
        omega)]
      apply congrArg (fun q => H q j)
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_succ,
        Fin.val_add_one_of_lt' (by omega)]
    · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hik)
      rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_gt hki]
      rw [Fin.succAbove_succ_of_lt k i hki]

/-- Replacing row `k` of the tail matrix by row zero is the deleted-`k+1`
minor, with exactly the row-cycle sign used in source equation (8). -/
theorem det_updateRow_tailMatrix
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    ((H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0)).det =
      (-1 : ℝ) ^ (k.val + 2) * deletedRowMinor H k.succ := by
  rw [updateRow_tailMatrix_eq_permuted_deletedRow H k, Matrix.det_permute]
  simp only [Fin.sign_cycleRange, deletedRowMinor]
  norm_num [pow_add]

/-! ## Cramer's rule for the omitted height -/

/-- The differential of height zero at an ordered coordinate vector. -/
def heightZeroDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  (concreteGapCoordinateDerivativesAt hAB u (0 : Fin (d + 1))).valueDifferential.comp
    (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem heightZeroDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (j : Fin d) :
    heightZeroDifferentialAt hAB u (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) 0 j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u 0).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd 0).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd 0 j

private lemma continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec
    {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) (hdet : L.det ≠ 0)
    (v : Fin d → ℝ) :
    (L.toContinuousLinearEquivOfDetNeZero hdet).symm v =
      ((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
  let eL := L.toContinuousLinearEquivOfDetNeZero hdet
  apply eL.injective
  change L (eL.symm v) = L
    (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v)
  rw [show L (eL.symm v) = v by
    change eL (eL.symm v) = v
    exact eL.apply_symm_apply v]
  symm
  calc
    L (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) =
        LinearMap.toMatrix' L.toLinearMap *ᵥ
          (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) :=
      (LinearMap.toMatrix'_mulVec L.toLinearMap _).symm
    _ = ((LinearMap.toMatrix' L.toLinearMap) *
          (LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    _ = v := by
      rw [Matrix.mul_nonsing_inv]
      · exact Matrix.one_mulVec v
      · exact isUnit_iff_ne_zero.mpr (by
          rw [LinearMap.det_toMatrix']
          exact hdet)

/-- The actual inverse-chart partial derivative of height zero is the
source's deleted-minor quotient. -/
theorem heightZeroDifferential_comp_tailInverse_basis
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (k : Fin d) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap
        (Pi.single k 1) =
      heightZeroCramerCoefficient (endpointArrayOfInterior hAB u) hd k := by
  let H := gapHeightJacobianModel (endpointArrayOfInterior hAB u)
  let T := H.submatrix (0 : Fin (d + 1)).succAbove id
  let L := tailHeightDifferentialAt hAB u hd
  let D := heightZeroDifferentialAt hAB u
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  have hT : LinearMap.toMatrix' L.toLinearMap = T := by
    exact tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd
  have hTdet : T.det ≠ 0 := by
    rw [← hT, LinearMap.det_toMatrix']
    exact hLdet
  have hTunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hTdet
  have hD : ∀ j : Fin d, D (Pi.single j 1) = H 0 j := by
    intro j
    exact heightZeroDifferentialAt_basis_eq_model hAB u hd j
  have hinv :
      (L.toContinuousLinearEquivOfDetNeZero hLdet).symm (Pi.single k 1) =
        (T⁻¹) *ᵥ Pi.single k 1 := by
    rw [continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec L hLdet]
    rw [hT]
  change D ((L.toContinuousLinearEquivOfDetNeZero hLdet).symm
    (Pi.single k 1)) = _
  rw [hinv]
  have hD_apply (v : Fin d → ℝ) : D v = H 0 ⬝ᵥ v := by
    have hv : v = ∑ i : Fin d,
        (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ) :=
      pi_eq_sum_univ' v
    calc
      D v = D (∑ i : Fin d,
          (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ)) := congrArg D hv
      _ = ∑ i, v i * H 0 i := by
        simp only [map_sum, map_smul, smul_eq_mul, hD]
      _ = H 0 ⬝ᵥ v := by
        simp only [dotProduct]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hD_apply, Matrix.dotProduct_mulVec, dotProduct_single_one]
  have hcramer := Matrix.det_smul_inv_vecMul_eq_cramer_transpose
    T (H 0) hTunit
  have hcramerK := congrFun hcramer k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_transpose_apply] at hcramerK
  rw [det_updateRow_tailMatrix H k] at hcramerK
  rw [heightZeroCramerCoefficient]
  change (H 0 ᵥ* T⁻¹) k =
    (-1) ^ (k.val + 2) * deletedRowMinor H k.succ /
      deletedRowMinor H 0
  have hTdetMinor : T.det = deletedRowMinor H 0 := rfl
  rw [← hTdetMinor]
  apply (eq_div_iff hTdet).2
  nlinarith

/-! ## The genuine tail map on the open simplex -/

/-- Tail gap heights in the interior-coordinate chart. -/
def coordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => tailGapHeight (endpointArrayOfInterior hAB v)

lemma canonicalExtendedCoordinateTailHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateTailHeight hAB u hd v.1 =
      coordinateTailHeight hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateTailHeight,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateTailHeight, tailGapHeight,
    coordinateGapHeight]
  rfl

lemma canonicalExtendedCoordinateGapHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    canonicalExtendedCoordinateGapHeight hAB u hd g v.1 =
      coordinateGapHeight hAB v g := by
  simp only [canonicalExtendedCoordinateGapHeight,
    extendedCoordinateGapHeight, dif_pos v.2]

/-- Although the inverse-function chart is constructed from an ambient
representative based at one point, at every other simplex point its
derivative is the point's own concrete tail differential. -/
theorem hasFDerivAt_canonicalTailHeight_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (tailHeightDifferentialAt hAB x hd) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateTailHeight
    hAB x hd).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateTailHeight_eq_coordinate
    hAB base v' hd).trans
      (canonicalExtendedCoordinateTailHeight_eq_coordinate hAB x v' hd).symm

/-- The analogous base-independence for the omitted height. -/
theorem hasFDerivAt_canonicalHeightZero_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB base hd 0)
      (heightZeroDifferentialAt hAB x) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB x hd 0).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
    hAB base v' hd 0).trans
      (canonicalExtendedCoordinateGapHeight_eq_coordinate hAB x v' hd 0).symm

theorem heightZeroDifferential_comp_tailInverse_apply
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (w : Fin d → ℝ) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w =
      ∑ k, w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k := by
  let C := (heightZeroDifferentialAt hAB u).comp
    ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
      (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
        hAB u hd hsigns)).symm.toContinuousLinearMap
  have hw : w = ∑ k : Fin d,
      (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ) := pi_eq_sum_univ' w
  change C w = _
  calc
    C w = C (∑ k : Fin d,
        (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ)) := congrArg C hw
    _ = ∑ k, w k * C (Pi.single k 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [heightZeroDifferential_comp_tailInverse_basis hAB u hd hsigns k]

theorem heightZeroDifferential_comp_tailInverse_neg
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u))
    {w : Fin d → ℝ} (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w < 0 := by
  rw [heightZeroDifferential_comp_tailInverse_apply hAB u hd hsigns w]
  have hex : ∃ k, 0 < w k := by
    by_contra hn
    push_neg at hn
    apply hw0
    funext k
    exact le_antisymm (hn k) (hw k)
  obtain ⟨k0, hk0⟩ := hex
  have hnonpos : ∀ k, w k * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    intro k
    exact mul_nonpos_of_nonneg_of_nonpos (hw k)
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k).le
  have hstrict : w k0 * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k0 < 0 :=
    mul_neg_of_pos_of_neg hk0
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k0)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k0)]
  have herase : ∑ k ∈ Finset.univ.erase k0,
      w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    exact Finset.sum_nonpos fun k _ => hnonpos k
  linarith

/-! ## Differential of height zero through an ambient inverse chart -/

private theorem hasFDerivAt_heightZero_through_ambientInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (he : (e : (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB base hd)
    {y : Fin d → ℝ} (hy : y ∈ e.target)
    (hyspace : e.symm y ∈ endpointNodeSpace d A B)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB ⟨e.symm y, hyspace⟩)) :
    HasFDerivAt
      (fun q => canonicalExtendedCoordinateGapHeight hAB
        ⟨e.symm y, hyspace⟩ hd 0 (e.symm q))
      ((heightZeroDifferentialAt hAB ⟨e.symm y, hyspace⟩).comp
        (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt hAB ⟨e.symm y, hyspace⟩ hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB ⟨e.symm y, hyspace⟩ hd hsigns)).symm.toContinuousLinearMap) y := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have heDeriv : HasFDerivAt e (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ)
      (e.symm y) := by
    rw [he]
    change HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalTailHeight_at_simplexPoint hAB base u hd
  have heInv : HasFDerivAt e.symm
      (eL.symm : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) y :=
    e.hasFDerivAt_symm hy heDeriv
  have hzero := hasFDerivAt_canonicalHeightZero_at_simplexPoint
    hAB u u hd
  exact hzero.comp y heInv

/-! ## The inverse-function chart and its simplex restriction -/

/-- The ambient inverse-function chart based at one endpoint array. -/
def ambientTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  exact ContDiffAt.toOpenPartialHomeomorph
    (canonicalExtendedCoordinateTailHeight hAB u hd)
    (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
    hderiv (by norm_num)

@[simp]
theorem ambientTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (ambientTailHeightChart hAB u hd hsigns :
      (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB u hd := by
  simp only [ambientTailHeightChart]
  apply ContDiffAt.toOpenPartialHomeomorph_coe

theorem mem_ambientTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u.1 ∈ (ambientTailHeightChart hAB u hd hsigns).source := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  simpa only [ambientTailHeightChart] using
    (ContDiffAt.mem_toOpenPartialHomeomorph_source
      (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
      hderiv (by norm_num))

/-- Restriction of the ambient IFT chart to the ordered open simplex. -/
def simplexTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  (ambientTailHeightChart hAB u hd hsigns).subtypeRestr
    (show Nonempty S from ⟨u⟩)

theorem mem_simplexTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u ∈ (simplexTailHeightChart hAB u hd hsigns).source := by
  simpa only [simplexTailHeightChart,
    OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using
      mem_ambientTailHeightChart_source hAB u hd hsigns

@[simp]
theorem simplexTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) =
      coordinateTailHeight hAB := by
  funext v
  rw [show (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) v =
      (ambientTailHeightChart hAB u hd hsigns) v.1 by rfl]
  rw [ambientTailHeightChart_coe]
  exact canonicalExtendedCoordinateTailHeight_eq_coordinate hAB u v hd

private theorem hasFDerivAt_coordinateHeightZero_through_simplexInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {y : Fin d → ℝ}
    (hy : y ∈ (simplexTailHeightChart hAB base hd hbase).target) :
    let uy := (simplexTailHeightChart hAB base hd hbase).symm y
    HasFDerivAt
      (fun q => coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm q) 0)
      ((heightZeroDifferentialAt hAB uy).comp
        (ContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
            (tailHeightDifferentialAt hAB uy hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB uy hd (hsignsAll (endpointArrayOfInterior hAB uy)))).symm)) y := by
  dsimp only
  let e := ambientTailHeightChart hAB base hd hbase
  let es := simplexTailHeightChart hAB base hd hbase
  let uy := es.symm y
  have hyAmbient : y ∈ e.target := by
    exact OpenPartialHomeomorph.subtypeRestr_target_subset e
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hval : uy.1 = e.symm y := by
    change (Subtype.val ∘ es.symm) y = e.symm y
    exact e.subtypeRestr_symm_apply
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hyspace : e.symm y ∈ endpointNodeSpace d A B := by
    rw [← hval]
    exact uy.2
  let ue : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  have hue : ue = uy := Subtype.ext hval.symm
  have hderiv := hasFDerivAt_heightZero_through_ambientInverse
    hAB base hd e (ambientTailHeightChart_coe hAB base hd hbase)
    hyAmbient hyspace (hsignsAll (endpointArrayOfInterior hAB ue))
  have hevent : ∀ᶠ q in 𝓝 y, q ∈ es.target :=
    es.open_target.mem_nhds hy
  have heq :
      (fun q => coordinateGapHeight hAB (es.symm q) 0) =ᶠ[𝓝 y]
        (fun q => canonicalExtendedCoordinateGapHeight hAB ue hd 0 (e.symm q)) := by
    filter_upwards [hevent] with q hq
    have hqval : (es.symm q).1 = e.symm q := by
      change (Subtype.val ∘ es.symm) q = e.symm q
      exact e.subtypeRestr_symm_apply
        (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hq
    rw [← hqval]
    exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
      hAB ue (es.symm q) hd 0).symm
  have hout := hderiv.congr_of_eventuallyEq heq
  convert hout using 1
  congr 3
  exact hue.symm
  congr 2
  exact hue.symm

/-! ## Integrating the negative Cramer partials -/

private theorem coordinateHeightZero_strictAntiOn_convexTarget
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {V : Set (Fin d → ℝ)}
    (hVconvex : Convex ℝ V)
    (hV : V ⊆ (simplexTailHeightChart hAB base hd hbase).target)
    {y z : Fin d → ℝ} (hy : y ∈ V) (hz : z ∈ V)
    (hyz : ∀ i, y i ≤ z i) (hyzNe : y ≠ z) :
    coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm z) 0 <
      coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm y) 0 := by
  let es := simplexTailHeightChart hAB base hd hbase
  let φ : ℝ → ℝ := fun t =>
    coordinateGapHeight hAB (es.symm (AffineMap.lineMap y z t)) 0
  let w : Fin d → ℝ := z - y
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact sub_nonneg.mpr (hyz i)
  have hw0 : w ≠ 0 := by
    intro hwzero
    apply hyzNe
    exact (sub_eq_zero.mp hwzero).symm
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AffineMap.lineMap y z t ∈ V :=
    hVconvex.lineMap_mem hy hz ht
  have hpathDeriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt φ
        (((heightZeroDifferentialAt hAB
            (es.symm (AffineMap.lineMap y z t))).comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
              (tailHeightDifferentialAt hAB
                (es.symm (AffineMap.lineMap y z t)) hd)
              (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB
                (es.symm (AffineMap.lineMap y z t)) hd
                (hsignsAll (endpointArrayOfInterior hAB
                  (es.symm (AffineMap.lineMap y z t)))))).symm)) w) t := by
    have houter :=
      hasFDerivAt_coordinateHeightZero_through_simplexInverse
        hAB base hd hsignsAll hbase
          (hV (hline t ht))
    have hcomp := houter.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := t))
    simpa only [φ, es, Function.comp_def, w] using hcomp
  have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hpathDeriv t ht).continuousAt.continuousWithinAt
  have hderivNeg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv φ t < 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hpathDeriv t htIcc).deriv]
    exact heightZeroDifferential_comp_tailInverse_neg hAB
      (es.symm (AffineMap.lineMap y z t)) hd
      (hsignsAll (endpointArrayOfInterior hAB
        (es.symm (AffineMap.lineMap y z t)))) hw hw0
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
    hcont hderivNeg
  have h01 := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_lt_one
  simpa only [φ, es, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h01

/-! ## Assembly of the canonical oriented chart -/

/-- Coherent maximal-minor signs construct the local oriented chart required
by `Orientation.lean`.  The target is explicitly shrunk to a norm ball, so
its convexity is kernel-visible. -/
theorem nonempty_orientedTailHeightChart_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (nodes : EndpointArray d A B) :
    Nonempty (OrientedTailHeightChart nodes) := by
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    (endpointArrayHomeomorph hAB) nodes
  have huNodes : endpointArrayOfInterior hAB u = nodes := by
    exact (endpointArrayHomeomorph hAB).symm_apply_apply nodes
  have hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u) := by
    rw [huNodes]
    exact hsignsAll nodes
  let es := simplexTailHeightChart hAB u hd hbase
  have huSource : u ∈ es.source :=
    mem_simplexTailHeightChart_source hAB u hd hbase
  let center : Fin d → ℝ := coordinateTailHeight hAB u
  have hcenter : center ∈ es.target := by
    have hmapped := es.map_source huSource
    change coordinateTailHeight hAB u ∈ es.target
    rw [← simplexTailHeightChart_coe hAB u hd hbase]
    exact hmapped
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp es.open_target center hcenter
  let ball : Set (Fin d → ℝ) := Metric.ball center r
  let esSmall : OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
    (es.symm.restrOpen ball Metric.isOpen_ball).symm
  have hesSmallTarget : esSmall.target = ball := by
    change es.target ∩ ball = ball
    exact Set.inter_eq_right.mpr hball
  have hcenterBall : center ∈ ball := Metric.mem_ball_self hr
  have hcenterSmallTarget : center ∈ esSmall.target := by
    rw [hesSmallTarget]
    exact hcenterBall
  have huSmallSource : u ∈ esSmall.source := by
    have hmapped := esSmall.map_target hcenterSmallTarget
    have hinv : esSmall.symm center = u := by
      change (es.symm.restrOpen ball Metric.isOpen_ball) center = u
      change es.symm center = u
      have hcenterEq : es u = center := by
        change es u = coordinateTailHeight hAB u
        exact congrFun (simplexTailHeightChart_coe hAB u hd hbase) u
      rw [← hcenterEq]
      exact es.left_inv huSource
    rwa [hinv] at hmapped
  let chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ) :=
    (endpointArrayHomeomorph hAB).transOpenPartialHomeomorph esSmall
  have hnodesSource : nodes ∈ chart.source := by
    change nodes ∈ (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).source
    rw [Homeomorph.transOpenPartialHomeomorph_source]
    change u ∈ esSmall.source
    exact huSmallSource
  have hchartEq :
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart := by
    funext x
    change tailGapHeight x = esSmall ((endpointArrayHomeomorph hAB) x)
    change tailGapHeight x = es ((endpointArrayHomeomorph hAB) x)
    rw [simplexTailHeightChart_coe]
    change tailGapHeight x = tailGapHeight
      (endpointArrayOfInterior hAB ((endpointArrayHomeomorph hAB) x))
    congr 1
    exact (endpointArrayHomeomorph hAB).symm_apply_apply x |>.symm
  have hchartTarget : chart.target = ball := by
    change (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).target = ball
    rw [Homeomorph.transOpenPartialHomeomorph_target, hesSmallTarget]
  have hconvex : Convex ℝ chart.target := by
    rw [hchartTarget]
    exact convex_ball center r
  refine ⟨{
    chart := chart
    mem_source := hnodesSource
    chart_eq := hchartEq
    convex_target := hconvex
    height_zero_strictAnti := ?_ }⟩
  intro y z hy hz hyz hyzNe
  have hyBall : y ∈ ball := by rwa [← hchartTarget]
  have hzBall : z ∈ ball := by rwa [← hchartTarget]
  have hstrict := coordinateHeightZero_strictAntiOn_convexTarget
    hAB u hd hsignsAll hbase (convex_ball center r) hball
      hyBall hzBall hyz hyzNe
  change (chart.symm z).height 0 < (chart.symm y).height 0
  change (endpointArrayOfInterior hAB (esSmall.symm z)).height 0 <
    (endpointArrayOfInterior hAB (esSmall.symm y)).height 0
  change coordinateGapHeight hAB (esSmall.symm z) 0 <
    coordinateGapHeight hAB (esSmall.symm y) 0
  change coordinateGapHeight hAB (es.symm z) 0 <
    coordinateGapHeight hAB (es.symm y) 0
  exact hstrict

/-- The local orientation proposition isolated by `Orientation.lean` is a
theorem of the ordinary coherent-sign input.  Height-zero continuity is
unconditional; for `d = 0` the chart clause is vacuous because it quantifies
an impossible witness `1 ≤ 0`. -/
theorem tailHeightLocalOrientationStatement_of_coherentSigns
    (d : ℕ) (A B : ℝ)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes) :
    TailHeightLocalOrientationStatement d A B := by
  refine ⟨continuous_endpointArray_height (0 : Fin (d + 1)), ?_⟩
  intro hd nodes
  exact nonempty_orientedTailHeightChart_of_coherentSigns hd hsignsAll nodes

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Randy1153/DeBoorPinkus/Package.lean` -/

/-!
# Unconditional de Boor--Pinkus package

This module is the final assembly layer for the endpoint-fixed comparison
theory.  The interlacing/minor computation supplies coherent orientation,
the topology package supplies the global gap-difference homeomorphism, and
the oriented local charts supply the path and ray lifts.  No additional
hypothesis is introduced here.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- The tail-height map has coherently oriented local charts at every
endpoint array. -/
theorem tailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) :
    TailHeightLocalOrientationStatement d A B :=
  tailHeightLocalOrientationStatement_of_coherentSigns d A B
    coherentHeightMaximalMinorSigns_unconditional

/-- The global increasing-segment and decreasing-ray lifts, with their
source-faithful height-zero orientation. -/
theorem gapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) :
    GapHeightPathRayOrientationStatement d A B :=
  gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    (gapDifference_homeomorphismStatement d A B)
    (tailHeightLocalOrientationStatement d A B)

/-- The unconditional comparison package used by the block-collapse
argument. -/
theorem comparisonPackage (d : ℕ) (A B : ℝ) :
    ComparisonPackage d A B :=
  comparisonPackage_of_homeomorphism_of_pathRayOrientation
    (gapDifference_homeomorphismStatement d A B)
    (gapHeightPathRayOrientationStatement d A B)

/-- Smoke theorem: the package contains the unique equioscillating endpoint
array asserted by source Theorem 1. -/
theorem existsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) :
    ExistsUniqueEquioscillatingStatement d A B :=
  (comparisonPackage d A B).exists_unique_equioscillating

end

end Randy1153.DeBoorPinkus

/-! ### Upstream module `Jsp936/CanonicalBounds.lean` -/

/-!
Canonical optimal values and their lower bound for all free-node competitors.
The first two comparison consequences follow the canonical JSP000936 adapter by
randyxian08 (MIT, upstream commit e1df51e950876056d8951f4a93fa7fef6863b422).
The de Boor–Pinkus theory itself is imported from the credited upstream core.
-/
namespace Jsp936
open Randy1153 Randy1153.DeBoorPinkus
noncomputable section

/-- A canonical equioscillator is rigid under coordinatewise upper bounds on its peaks. -/
theorem canonical_upper_threshold {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (s : EndpointArray d (-1) 1)
    (h : ∀ i, s.height i ≤ opt.height 0) : s = opt := by
  apply (comparisonPackage d (-1) 1).gapHeight_le_rigidity s opt
  intro i
  rw [hopt i 0]
  exact h i

/-- The canonical optimal peak bounds every simultaneous upper bound on another array. -/
theorem canonical_peak_le_upper_bound {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (s : EndpointArray d (-1) 1) (U : ℝ)
    (hU : ∀ i, s.height i ≤ U) : opt.height 0 ≤ U := by
  by_contra h
  have hlt : U < opt.height 0 := lt_of_not_ge h
  have heq : s = opt := canonical_upper_threshold opt hopt s
    (fun i ↦ (hU i).trans hlt.le)
  have hbad := hU 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- Each gap contains a node, where the Lebesgue function is one. -/
theorem one_le_gapHeight {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) : 1 ≤ gapHeight nodes g := by
  have h := lebesgueFunction_le_on nodes.toNodeFamily (gap_left_lt_right nodes g).le
    (show nodes.point (gapLeftIndex g) ∈
      Set.Icc (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g)) from
      ⟨le_rfl, (gap_left_lt_right nodes g).le⟩)
  simpa only [lebesgueFunction_at_node] using h

/-- The common canonical gap peak is exactly the full interval maximum. -/
theorem canonical_lebesgueOn_eq {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt) :
    lebesgueOn opt.toNodeFamily (-1) 1 = opt.height 0 := by
  apply le_antisymm
  · apply lebesgueOn_le_of_gapHeight_le opt.toOrderedNodes
    · intro g
      exact (hopt g 0).le
    · calc
        lebesgueFunction opt.toNodeFamily (-1) =
            lebesgueFunction opt.toNodeFamily (opt.point (endpointLeftIndex d)) :=
          congrArg (lebesgueFunction opt.toNodeFamily) opt.left_endpoint.symm
        _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointLeftIndex d)
        _ ≤ opt.height 0 := one_le_gapHeight opt.toOrderedNodes 0
    · calc
        lebesgueFunction opt.toNodeFamily 1 =
            lebesgueFunction opt.toNodeFamily (opt.point (endpointRightIndex d)) :=
          congrArg (lebesgueFunction opt.toNodeFamily) opt.right_endpoint.symm
        _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointRightIndex d)
        _ ≤ opt.height 0 := one_le_gapHeight opt.toOrderedNodes 0
  · exact gapHeight_le_lebesgueOn opt.toOrderedNodes 0

/-- The canonical optimum is a lower bound for every free-node configuration. -/
theorem canonical_peak_le_free_maximum {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    opt.height 0 ≤ lebesgueOn nodes (-1) 1 := by
  apply canonical_peak_le_upper_bound opt hopt (normalizedNodes nodes.sorted)
  intro i
  change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i ≤ _
  rw [gapHeight_normalized]
  calc
    gapHeight nodes.sorted i ≤ lebesgueOn nodes.sorted.toNodeFamily (-1) 1 :=
      gapHeight_le_lebesgueOn nodes.sorted i
    _ = lebesgueOn nodes (-1) 1 := nodes.lebesgueOn_sorted (-1) 1

end
end Jsp936

/-! ### Upstream module `Jsp936/Singleton.lean` -/

/-! The one-node case of the free-node optimization problem. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- A one-node family has constant Lebesgue function equal to one. -/
@[simp]
lemma lebesgueFunction_singleton (nodes : NodeFamily 1) (t : ℝ) :
    lebesgueFunction nodes t = 1 := by
  simp [lebesgueFunction, lagrangeFundamental]

/-- The Lebesgue maximum of a one-node family is one on `[-1, 1]`. -/
@[simp]
lemma lebesgueOn_singleton (nodes : NodeFamily 1) :
    lebesgueOn nodes (-1) 1 = 1 := by
  obtain ⟨t, _, ht, _⟩ := exists_lebesgueOn_eq_and_ge nodes (by norm_num : (-1 : ℝ) ≤ 1)
  rw [ht, lebesgueFunction_singleton]

/-- Every single interpolation node is optimal, with amplification exactly one. -/
theorem singleton_nodes_optimal (nodes : NodeFamily 1) :
    IsOptimal nodes ∧ lebesgueOn nodes (-1) 1 = 1 := by
  constructor
  · intro other
    rw [lebesgueOn_singleton nodes, lebesgueOn_singleton other]
  · exact lebesgueOn_singleton nodes

end
end Jsp936

/-! ### Upstream module `Jsp936/Main.lean` -/

/-! Complete characterization of all optimal free interpolation node families. -/
namespace Jsp936
open Randy1153 Randy1153.DeBoorPinkus
noncomputable section

/-- Complete characterization for every number of distinct nodes at least two. -/
theorem minimizer_iff_equioscillating_and_controlled_tails
    (d : ℕ) (nodes : NodeFamily (d + 2)) :
    IsOptimal nodes ↔ EquioscillatingWithControlledTails nodes := by
  obtain ⟨opt, hopt, hunique⟩ := existsUniqueEquioscillatingStatement d (-1) 1
    (by norm_num [AdmissibleInterval])
  constructor
  · intro hmin
    have hmax : lebesgueOn nodes (-1) 1 ≤ opt.height 0 := by
      rw [← canonical_lebesgueOn_eq opt hopt]
      exact hmin opt.toNodeFamily
    have hnormalized : normalizedNodes nodes.sorted = opt := by
      apply canonical_upper_threshold opt hopt
      intro i
      change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i ≤ _
      rw [gapHeight_normalized]
      exact (gapHeight_le_lebesgueOn nodes.sorted i).trans
        (by simpa only [NodeFamily.lebesgueOn_sorted] using hmax)
    have hpeak (i : Fin (d + 1)) : gapHeight nodes.sorted i = opt.height 0 := by
      rw [← gapHeight_normalized nodes.sorted i]
      change (normalizedNodes nodes.sorted).height i = opt.height 0
      rw [hnormalized, hopt i 0]
    refine ⟨fun i j ↦ (hpeak i).trans (hpeak j).symm, ?_, ?_⟩
    · rw [hpeak 0]
      exact (lebesgueFunction_le_on nodes (by norm_num) (by simp)).trans hmax
    · rw [hpeak 0]
      exact (lebesgueFunction_le_on nodes (by norm_num) (by simp)).trans hmax
  · rintro ⟨hequal, hleft, hright⟩
    have hnormalized : normalizedNodes nodes.sorted = opt := by
      apply hunique
      intro i j
      change gapHeight (normalizedNodes nodes.sorted).toOrderedNodes i =
        gapHeight (normalizedNodes nodes.sorted).toOrderedNodes j
      rw [gapHeight_normalized, gapHeight_normalized]
      exact hequal i j
    have hpeak : gapHeight nodes.sorted (0 : Fin (d + 1)) = opt.height 0 := by
      rw [← gapHeight_normalized nodes.sorted (0 : Fin (d + 1))]
      change (normalizedNodes nodes.sorted).height 0 = opt.height 0
      rw [hnormalized]
    have hmax : lebesgueOn nodes (-1) 1 ≤ opt.height 0 := by
      rw [← nodes.lebesgueOn_sorted (-1) 1, ← hpeak]
      apply lebesgueOn_le_of_gapHeight_le nodes.sorted
      · intro i
        exact (hequal i 0).le
      · simpa only [NodeFamily.lebesgueFunction_sorted] using hleft
      · simpa only [NodeFamily.lebesgueFunction_sorted] using hright
    intro other
    exact hmax.trans (canonical_peak_le_free_maximum opt hopt other)

end
end Jsp936

/-- Erdős Problem 1129: which distinct nodes in `[-1, 1]` minimise the Lebesgue constant. -/
theorem erdos_1129 :
    (∀ (d : ℕ) (nodes : Randy1153.NodeFamily (d + 2)),
      Jsp936.IsOptimal nodes ↔ Jsp936.EquioscillatingWithControlledTails nodes) ∧
    (∀ nodes : Randy1153.NodeFamily 1,
      Jsp936.IsOptimal nodes ∧ Randy1153.lebesgueOn nodes (-1) 1 = 1) :=
  ⟨Jsp936.minimizer_iff_equioscillating_and_controlled_tails, Jsp936.singleton_nodes_optimal⟩

#print axioms erdos_1129
-- 'Erdos1129.erdos_1129' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1129
