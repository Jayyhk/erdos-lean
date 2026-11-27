import Mathlib

namespace Erdos1019

/-
# Erdős Problem 1019

A planar graph on $n$ vertices with $3n-6$ edges (the maximum possible) is called saturated.
Does every graph on $n$ vertices with $\lfloor n^2/4\rfloor+\lfloor \frac{n+1}{2}\rfloor$ edges
contain a saturated planar graph with $>3$ vertices?

The answer is **yes**, proved by Simonovits: such a graph contains either $K_4$ or a bipyramid
$C_l + 2K_1$ for some $l \geq 3$ (`erdos_1019_sharp`). `erdos_1019` states the question with
planarity in its ordinary topological sense, `SimpleGraph.IsPlanar`: a plane drawing in
$\mathbb{R}^2$ by Jordan arcs. It is proved by explicit straight-line drawings of $K_4$ and of
every bipyramid. The hypothesis `Nonempty V` excludes only the empty graph, for which the
literal statement is false.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000849); the
ten modules forming the closure of `erdos_1019` are flattened here in dependency order. The
proof of Simonovits's theorem is vendored there from `plby/lean-proofs`
(`ErdosProblems/Erdos1019.lean`), whose own final theorem, stating planarity only as being
isomorphic to $K_4$ or a bipyramid, is not needed here and is removed. The final theorem is
renamed from upstream `erdos_1019_saturated_planar`, and the upstream corollary
`erdos_1019_saturated_planar_closed`, a restatement of it on `Fin (n + 1)` without
hypotheses, is omitted so that `erdos_1019` is the last declaration.

Declarations that `erdos_1019` does not depend on have been removed.
-/

/-! ### Upstream module `Erdos1019Planar/Planarity.lean` -/

section
/-!
# Plane drawings of simple graphs

A plane drawing of a simple graph places the vertices at distinct points of `ℝ × ℝ` and
represents every edge by a Jordan arc (the injective continuous image of `[0, 1]`) joining the
images of its two endpoints, subject to the two usual non-crossing conditions: no vertex lies on
the arc of an edge that is not incident to it, and two distinct arcs meet only in the images of
their common endpoints.  A graph is planar when it admits such a drawing.

This is the ordinary topological notion; no combinatorial certificate is used.  Straight-line
drawings are a special case, see `SimpleGraph.IsStraightLineDrawing`.
-/

open _root_.Set

/-- A plane drawing of `G`: an injective vertex placement and, for each edge, a Jordan arc
between the images of its endpoints, such that vertices avoid non-incident arcs and distinct
arcs meet only at images of shared endpoints. -/
structure _root_.SimpleGraph.PlaneDrawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex. -/
  pos : V → ℝ × ℝ
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set representing each edge. -/
  arc : Sym2 V → Set (ℝ × ℝ)
  /-- Every edge is drawn as a Jordan arc from the image of one endpoint to the other. -/
  arc_isArc : ∀ e ∈ G.edgeSet, ∃ u v : V, e = s(u, v) ∧ ∃ γ : ℝ → ℝ × ℝ,
    ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = pos u ∧ γ 1 = pos v ∧
      arc e = γ '' Icc 0 1
  /-- A vertex lies on the arc of an edge only if it is an endpoint of that edge. -/
  vertex_mem_arc : ∀ e ∈ G.edgeSet, ∀ w : V, pos w ∈ arc e → w ∈ e
  /-- Two distinct arcs meet only in images of common endpoints. -/
  arc_inter_arc : ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
    arc e ∩ arc f ⊆ pos '' {w : V | w ∈ e ∧ w ∈ f}

open _root_.SimpleGraph in
/-- A graph is planar when it admits a plane drawing. -/
def _root_.SimpleGraph.IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneDrawing G)

open _root_.SimpleGraph in
/-- The vertex placement `pos` is a straight-line plane drawing of `G`: positions are
distinct, no vertex lies on the closed segment of a non-incident edge, and the closed segments
of two distinct edges meet only in positions of common endpoints. -/
def _root_.SimpleGraph.IsStraightLineDrawing {V : Type*} (G : SimpleGraph V) (pos : V → ℝ × ℝ) : Prop :=
  Function.Injective pos ∧
    (∀ u v w : V, G.Adj u v → pos w ∈ segment ℝ (pos u) (pos v) → w = u ∨ w = v) ∧
    (∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
      segment ℝ (pos a) (pos b) ∩ segment ℝ (pos c) (pos d) ⊆
        pos '' {w : V | w ∈ s(a, b) ∧ w ∈ s(c, d)})

end

/-! ### Upstream module `Erdos1019Planar/Simonovits.lean` -/

section
/-
Vendored from plby/lean-proofs, src/latest/ErdosProblems/Erdos1019.lean at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e (Lean/Mathlib v4.33.0), Apache License 2.0.
Formal authors per the file header: Codex, GPT-5.6 Sol. Informal author: Miklós Simonovits.
Ported to Lean 4.34.0-rc1 / Mathlib 1fe0a51a for the JSP-000849 planarity bridge; modifications,
if any, are marked with `-- PORT:` comments. Original SHA-256: 476e39206d4d3ce3...
-/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1019.
https://www.erdosproblems.com/forum/thread/1019

Informal authors:
- Miklós Simonovits

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1019.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Erdős Problem 1019

Simonovits proved that an `n`-vertex graph with

`⌊n²/4⌋ + ⌊(n+1)/2⌋`

edges contains a saturated planar graph on more than three vertices.  We formalize the sharper
form recorded in the source discussion: the graph contains either `K₄` or a bipyramid
`C_l ∨ 2K₁` for some `l ≥ 3`.  These two graphs are planar triangulations and have respectively
`6 = 3*4-6` and `3*l = 3*(l+2)-6` edges.

The proof is the sharp Simonovits induction.  At one edge below the claimed threshold, every graph
without one of the two witnesses is the join of a tree and an independent set whose orders differ
by at most two.  Adding one edge to such a join produces one of the witnesses.
-/

open scoped _root_.SimpleGraph
open _root_.Finset

/-- The sharp one-edge-lower extremal value. -/
def lowerThreshold (n : ℕ) : ℕ := n * n / 4 + (n - 1) / 2

/-- The edge threshold in Erdős Problem 1019. -/
def problemThreshold (n : ℕ) : ℕ := n * n / 4 + (n + 1) / 2

/-- The degree removed in the sharp induction. -/
def stepDegree (n : ℕ) : ℕ := (n + 1) / 2

/-- The bipyramid over an `l`-cycle.  Its vertices are the equatorial vertices `Fin l` and two
apices indexed by `Bool`. -/
def bipyramidGraph (l : ℕ) : SimpleGraph (Fin l ⊕ Bool) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inl j => (SimpleGraph.cycleGraph l).Adj i j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro u v h
    rcases u with i | p <;> rcases v with j | q
    · exact ((SimpleGraph.cycleGraph l).adj_comm i j).mp h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

instance bipyramidGraph_decidableRel (l : ℕ) :
    DecidableRel (bipyramidGraph l).Adj := by
  intro u v
  rcases u with i | b <;> rcases v with j | c
  · change Decidable ((SimpleGraph.cycleGraph l).Adj i j)
    exact inferInstance
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id

/-- The stronger concrete conclusion in Simonovits's resolution. -/
def HasTarget {V : Type*} (G : SimpleGraph V) : Prop :=
  (⊤ : SimpleGraph (Fin 4)) ⊑ G ∨
    ∃ l : ℕ, 3 ≤ l ∧ bipyramidGraph l ⊑ G

/-- The number of edges of `G` whose two endpoints lie in the finite set `U`.  We use `ncard`
so that this mathematical quantity does not retain a choice of decidability instance. -/
noncomputable def edgeCountOn {V : Type*} [Fintype V] (G : SimpleGraph V)
    (U : Finset V) : ℕ :=
  (G.induce (U : Set V)).edgeSet.ncard

lemma edgeCountOn_eq_card_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    edgeCountOn G U = #(G.induce (U : Set V)).edgeFinset := by
  unfold edgeCountOn
  rw [Set.ncard_eq_toFinset_card']
  rfl

lemma edgeSet_ncard_eq_card_edgeFinset {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeSet.ncard = #G.edgeFinset := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (SimpleGraph.edgeFinset_card).symm

/-- When every non-isolated vertex lies in `U`, inducing on `U` does not change the number of
edges.  The proof is phrased with `ncard`, hence is independent of finite-instance choices. -/
lemma edgeCountOn_eq_edgeSet_ncard_of_support_subset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (hsupp : G.support ⊆ (U : Set V)) :
    edgeCountOn G U = G.edgeSet.ncard := by
  let inc : (U : Set V) ↪ V := Function.Embedding.subtype _
  let F : Sym2 (U : Set V) → Sym2 V := inc.sym2Map
  have himage : F '' (G.induce (U : Set V)).edgeSet = G.edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      obtain ⟨d, hd, rfl⟩ := he
      induction d using Sym2.inductionOn with
      | _ a b => exact hd
    · intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hab : G.Adj a b := he
        have ha : a ∈ G.support := ⟨b, hab⟩
        have hb : b ∈ G.support := ⟨a, hab.symm⟩
        refine ⟨s(⟨a, hsupp ha⟩, ⟨b, hsupp hb⟩), hab, ?_⟩
        rfl
  unfold edgeCountOn
  rw [← himage, Set.ncard_image_of_injective _ inc.sym2Map.injective]

/-- The target-free extremal configuration: on `U`, the graph is the join of a tree on `A`
and an independent set `B`, and the tree side is between zero and two vertices larger. -/
def IsBalancedTreeJoinOn {V : Type*} (G : SimpleGraph V)
    (U A B : Finset V) : Prop :=
  (A : Set V) ∪ (B : Set V) = (U : Set V) ∧
  Disjoint (A : Set V) (B : Set V) ∧
  (G.induce (A : Set V)).IsTree ∧
  (G.induce (B : Set V)) = ⊥ ∧
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
  B.card ≤ A.card ∧ A.card ≤ B.card + 2

@[simp] lemma bipyramidGraph_adj_left_right {l : ℕ} {i : Fin l} {b : Bool} :
    (bipyramidGraph l).Adj (.inl i) (.inr b) :=
  trivial

@[simp] lemma bipyramidGraph_adj_right_left {l : ℕ} {b : Bool} {i : Fin l} :
    (bipyramidGraph l).Adj (.inr b) (.inl i) :=
  trivial

lemma bipyramidGraph_degree_apex {l : ℕ} (b : Bool) :
    (bipyramidGraph l).degree (Sum.inr b) = l := by
  classical
  let e : (bipyramidGraph l).neighborSet (Sum.inr b) ≃ Fin l :=
    { toFun := fun y ↦ match h : y.1 with
        | .inl i => i
        | .inr c => False.elim (by
            have hy := y.2
            rw [h] at hy
            exact hy)
      invFun := fun i ↦ ⟨Sum.inl i, by simp⟩
      left_inv := by
        intro y
        rcases y with ⟨i | c, hi⟩
        · rfl
        · exact False.elim hi
      right_inv := by intro i; rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr e).trans (Fintype.card_fin l)

lemma bipyramidGraph_degree_equator {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    (bipyramidGraph l).degree (Sum.inl i) = 4 := by
  classical
  let e : (bipyramidGraph l).neighborSet (Sum.inl i) ≃
      (SimpleGraph.cycleGraph l).neighborSet i ⊕ Bool :=
    { toFun := fun y ↦ match h : y.1 with
        | .inl j => Sum.inl ⟨j, by
            have hy := y.2
            rw [h] at hy
            exact hy⟩
        | .inr b => Sum.inr b
      invFun := fun y ↦ match y with
        | .inl j => ⟨Sum.inl j.1, j.2⟩
        | .inr b => ⟨Sum.inr b, by simp⟩
      left_inv := by
        intro y
        rcases y with ⟨j | b, hj⟩ <;> rfl
      right_inv := by
        intro y
        rcases y with j | b <;> rfl }
  have hcycle : (SimpleGraph.cycleGraph l).degree i = 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 3 := by
      exact ⟨l - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e,
    Fintype.card_sum, Fintype.card_bool]
  rw [SimpleGraph.card_neighborSet_eq_degree, hcycle]

lemma bipyramidGraph_card_edges {l : ℕ} (hl : 3 ≤ l) :
    #(bipyramidGraph l).edgeFinset = 3 * l := by
  classical
  have hsum := (bipyramidGraph l).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, bipyramidGraph_degree_equator hl,
    bipyramidGraph_degree_apex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul] at hsum
  nlinarith

lemma HasTarget.mono {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H)
    (hG : HasTarget G) : HasTarget H := by
  rcases hG with h4 | ⟨l, hl, hb⟩
  · exact Or.inl (h4.trans_le hGH)
  · exact Or.inr ⟨l, hl, hb.trans_le hGH⟩

lemma HasTarget.of_four_clique {V : Type*} {G : SimpleGraph V}
    {a b c d : V} (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) : HasTarget G := by
  classical
  apply Or.inl
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained 4]
  apply SimpleGraph.IsNClique.not_cliqueFree (s := {a, b, c, d})
  rw [SimpleGraph.isNClique_iff]
  constructor
  · simp [hab, hac, had, hbc, hbd, hcd, hab.ne, hac.ne, had.ne,
      hbc.ne, hbd.ne, hcd.ne]
  · simp [hab.ne, hac.ne, had.ne, hbc.ne, hbd.ne, hcd.ne]

/-- Removing one vertex removes exactly its degree inside the induced graph.  This is the
finite-set form used by the induction. -/
lemma edgeCountOn_erase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {x : V} (hx : x ∈ U) :
    edgeCountOn G (U.erase x) =
      edgeCountOn G U - (G.induce (U : Set V)).degree ⟨x, hx⟩ := by
  classical
  let xu : (U : Set V) := ⟨x, hx⟩
  let e : {y : (U : Set V) // y ∈ ({xu}ᶜ : Set (U : Set V))} ≃
      (U.erase x : Set V) :=
    { toFun := fun y ↦ ⟨y.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          exact y.2 (Set.mem_singleton_iff.mpr (Subtype.ext h)), y.1.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact (Finset.ne_of_mem_erase y.2) (congrArg Subtype.val h)⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  let iso : (G.induce (U : Set V)).induce ({xu}ᶜ : Set (U : Set V)) ≃g
      G.induce (U.erase x : Set V) :=
    { toEquiv := e
      map_rel_iff' := by intro a b; rfl }
  have hi := iso.card_edgeFinset_eq
  have hd := (G.induce (U : Set V)).card_edgeFinset_induce_compl_singleton xu
  have hr := (G.induce (U : Set V)).card_edgeFinset_deleteIncidenceSet xu
  rw [edgeCountOn_eq_card_edgeFinset, edgeCountOn_eq_card_edgeFinset]
  simpa only [xu] using hi.symm.trans (hd.trans hr)

lemma degree_induce_eq_card_filter {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {x : V} (hx : x ∈ U) :
    (G.induce (U : Set V)).degree ⟨x, hx⟩ = #(U.filter (G.Adj x)) := by
  classical
  let e : (G.induce (U : Set V)).neighborSet (⟨x, hx⟩ : (U : Set V)) ≃
      (U.filter (G.Adj x) : Set V) :=
    { toFun := fun y ↦ ⟨y.1.1, Finset.mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩,
        (Finset.mem_filter.mp y.2).2⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  calc
    (G.induce (U : Set V)).degree ⟨x, hx⟩ =
        Fintype.card ((G.induce (U : Set V)).neighborSet ⟨x, hx⟩) :=
      (SimpleGraph.card_neighborSet_eq_degree _ _).symm
    _ = Fintype.card (U.filter (G.Adj x) : Set V) := Fintype.card_congr e
    _ = #(U.filter (G.Adj x)) := Fintype.card_coe _

/-- Extend a copied equatorial cycle by two external universal vertices. -/
lemma bipyramid_isContained_of_cycle_copy {V : Type*} {G : SimpleGraph V} {l : ℕ}
    (f : (SimpleGraph.cycleGraph l).Copy G) (north south : V)
    (hns : north ≠ south) (hn : north ∉ Set.range f) (hs : south ∉ Set.range f)
    (hun : ∀ i : Fin l, G.Adj north (f i) ∧ G.Adj south (f i)) :
    bipyramidGraph l ⊑ G := by
  let F : Fin l ⊕ Bool → V := fun z ↦ match z with
    | .inl i => f i
    | .inr false => north
    | .inr true => south
  let hFhom : bipyramidGraph l →g G := {
    toFun := F
    map_rel' := by
      intro u v huv
      rcases u with i | b <;> rcases v with j | c
      · change G.Adj (f i) (f j)
        exact f.toHom.map_rel huv
      · cases c
        · change G.Adj (f i) north
          exact (hun i).1.symm
        · change G.Adj (f i) south
          exact (hun i).2.symm
      · cases b
        · change G.Adj north (f j)
          exact (hun j).1
        · change G.Adj south (f j)
          exact (hun j).2
      · exact False.elim huv }
  have hFinj : Function.Injective F := by
    intro u v huv
    rcases u with i | b <;> rcases v with j | c
    · change f i = f j at huv
      exact congrArg Sum.inl (f.injective huv)
    · exfalso
      cases c
      · change f i = north at huv
        exact hn ⟨i, huv⟩
      · change f i = south at huv
        exact hs ⟨i, huv⟩
    · exfalso
      cases b
      · change north = f j at huv
        exact hn ⟨j, huv.symm⟩
      · change south = f j at huv
        exact hs ⟨j, huv.symm⟩
    · cases b <;> cases c
      · rfl
      · change north = south at huv
        exact (hns huv).elim
      · change south = north at huv
        exact (hns huv.symm).elim
      · rfl
  exact ⟨⟨hFhom, hFinj⟩⟩

/-- A tree together with a new vertex joined to two tree vertices contains a cycle. -/
lemma not_isAcyclic_tree_insert_two_neighbors {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x u v : V)
    (hT : (G.induce (A : Set V)).IsTree) (hxA : x ∉ A)
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    ¬(G.induce ((insert x A : Finset V) : Set V)).IsAcyclic := by
  classical
  let C := insert x A
  let HC := G.induce (C : Set V)
  let inc : G.induce (A : Set V) →g HC :=
    { toFun := fun y ↦ ⟨y.1, by simp [C, y.2]⟩
      map_rel' := by intro a b hab; exact hab }
  have hinc : Function.Injective inc := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : (C : Set V) ↦ z.1) h
  let uA : (A : Set V) := ⟨u, hu⟩
  let vA : (A : Set V) := ⟨v, hv⟩
  let uC : (C : Set V) := inc uA
  let vC : (C : Set V) := inc vA
  let xC : (C : Set V) := ⟨x, by simp [C]⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath uA vA
  let pC := p.map inc
  have hpC : pC.IsPath := hp.map hinc
  have hxuC : HC.Adj xC uC := hxu
  have hxvC : HC.Adj xC vC := hxv
  let q : HC.Walk uC vC := .cons hxuC.symm (.cons hxvC .nil)
  have hxv_ne : xC ≠ vC := by
    intro h
    apply hxA
    have : x = v := congrArg Subtype.val h
    simpa [this] using hv
  have huvC : uC ≠ vC := by
    intro h
    exact huv (congrArg Subtype.val h)
  have hux_ne : uC ≠ xC := by
    intro h
    apply hxA
    have : u = x := congrArg Subtype.val h
    simpa [← this] using hu
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons
    · apply SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil
      simp [hxv_ne]
    · simp [huvC, hux_ne]
  intro hac
  change HC.IsAcyclic at hac
  have heq := hac.subsingleton_path uC vC |>.elim
      (⟨pC, hpC⟩ : HC.Path uC vC) (⟨q, hq⟩ : HC.Path uC vC)
  have hwalk : pC = q := congrArg Subtype.val heq
  have hxq : xC ∈ q.support := by simp [q]
  rw [← hwalk, SimpleGraph.Walk.support_map] at hxq
  rcases List.mem_map.mp hxq with ⟨y, hy, hey⟩
  apply hxA
  have hval : y.1 = x := congrArg Subtype.val hey
  simpa [hval] using y.2

/-- Two external universal vertices turn any cycle in `C` into a bipyramid. -/
lemma hasTarget_of_not_isAcyclic_two_apices {V : Type*}
    (G : SimpleGraph V) (C : Finset V) (north south : V)
    (hacyc : ¬(G.induce (C : Set V)).IsAcyclic)
    (hnC : north ∉ C) (hsC : south ∉ C) (hns : north ≠ south)
    (hun : ∀ z ∈ C, G.Adj north z ∧ G.Adj south z) : HasTarget G := by
  classical
  have hcycle : ∃ l : ℕ, 3 ≤ l ∧
      SimpleGraph.cycleGraph l ⊑ G.induce (C : Set V) := by
    by_contra h
    apply hacyc
    rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
    intro l hl hcopy
    exact h ⟨l, hl, hcopy⟩
  obtain ⟨l, hl, ⟨f⟩⟩ := hcycle
  let fG : (SimpleGraph.cycleGraph l).Copy G :=
    (SimpleGraph.Copy.induce G (C : Set V)).comp f
  have hnrange : north ∉ Set.range fG := by
    rintro ⟨i, hi⟩
    apply hnC
    have : north = (f i).1 := hi.symm
    rw [this]
    exact (f i).2
  have hsrange : south ∉ Set.range fG := by
    rintro ⟨i, hi⟩
    apply hsC
    have : south = (f i).1 := hi.symm
    rw [this]
    exact (f i).2
  refine Or.inr ⟨l, hl, bipyramid_isContained_of_cycle_copy fG north south hns
    hnrange hsrange ?_⟩
  intro i
  exact hun (f i).1 (f i).2

/-- In the induction, two neighbours on each side immediately give a bipyramid. -/
lemma hasTarget_of_two_neighbors_on_both_sides {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (x : V)
    (hT : (G.induce (A : Set V)).IsTree)
    (hdisj : Disjoint (A : Set V) (B : Set V))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hxA : x ∉ A) (hxB : x ∉ B)
    (hSA : 2 ≤ #(A.filter (G.Adj x)))
    (hSB : 2 ≤ #(B.filter (G.Adj x))) : HasTarget G := by
  classical
  have hSA' : 1 < #(A.filter (G.Adj x)) := by omega
  obtain ⟨u, huS, v, hvS, huv⟩ := Finset.one_lt_card.mp hSA'
  have hSB' : 1 < #(B.filter (G.Adj x)) := by omega
  obtain ⟨north, hnS, south, hsS, hns⟩ := Finset.one_lt_card.mp hSB'
  have hu := (Finset.mem_filter.mp huS).1
  have hv := (Finset.mem_filter.mp hvS).1
  have hxu := (Finset.mem_filter.mp huS).2
  have hxv := (Finset.mem_filter.mp hvS).2
  have hnB := (Finset.mem_filter.mp hnS).1
  have hsB := (Finset.mem_filter.mp hsS).1
  have hxn := (Finset.mem_filter.mp hnS).2
  have hxs := (Finset.mem_filter.mp hsS).2
  have hacyc := not_isAcyclic_tree_insert_two_neighbors G A x u v hT hxA hu hv huv hxu hxv
  apply hasTarget_of_not_isAcyclic_two_apices G (insert x A) north south hacyc
  · simp only [Finset.mem_insert]
    intro h
    rcases h with rfl | hnA
    · exact hxB hnB
    · exact hdisj.le_bot ⟨hnA, hnB⟩
  · simp only [Finset.mem_insert]
    intro h
    rcases h with rfl | hsA
    · exact hxB hsB
    · exact hdisj.le_bot ⟨hsA, hsB⟩
  · exact hns
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzA
    · exact ⟨hxn.symm, hxs.symm⟩
    · exact ⟨(hcross z hzA north hnB).symm, (hcross z hzA south hsB).symm⟩

/-- Adding a new vertex with exactly one neighbour to a finite tree again gives a tree. -/
lemma isTree_induce_insert_of_one_neighbor {V : Type*} [Finite V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (x u : V) (hT : (G.induce (A : Set V)).IsTree)
    (hxA : x ∉ A) (hu : u ∈ A) (hxu : G.Adj x u)
    (hone : #(A.filter (G.Adj x)) = 1) :
    (G.induce ((insert x A : Finset V) : Set V)).IsTree := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let C : Finset V := insert x A
  let HC := G.induce (C : Set V)
  let inc : G.induce (A : Set V) →g HC :=
    { toFun := fun y ↦ ⟨y.1, by simp [C, y.2]⟩
      map_rel' := by intro a b hab; exact hab }
  let xC : (C : Set V) := ⟨x, by simp [C]⟩
  let uA : (A : Set V) := ⟨u, hu⟩
  let uC : (C : Set V) := inc uA
  have hxuC : HC.Adj xC uC := hxu
  have hconn : HC.Connected := by
    refine { preconnected := ?_, nonempty := ⟨xC⟩ }
    intro y z
    have hy : y.1 = x ∨ y.1 ∈ A := by simpa [C] using y.2
    have hz : z.1 = x ∨ z.1 ∈ A := by simpa [C] using z.2
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · have hy' : y = xC := Subtype.ext hy
      have hz' : z = xC := Subtype.ext hz
      rw [hy', hz']
    · have hy' : y = xC := Subtype.ext hy
      rw [hy']
      let zA : (A : Set V) := ⟨z.1, hz⟩
      have hz' : inc zA = z := Subtype.ext rfl
      rw [← hz']
      exact hxuC.reachable.trans (hT.connected uA zA |>.map inc)
    · have hz' : z = xC := Subtype.ext hz
      rw [hz']
      let yA : (A : Set V) := ⟨y.1, hy⟩
      have hy' : inc yA = y := Subtype.ext rfl
      rw [← hy']
      exact (hT.connected yA uA |>.map inc).trans hxuC.symm.reachable
    · let yA : (A : Set V) := ⟨y.1, hy⟩
      let zA : (A : Set V) := ⟨z.1, hz⟩
      have hy' : inc yA = y := Subtype.ext rfl
      have hz' : inc zA = z := Subtype.ext rfl
      rw [← hy', ← hz']
      exact hT.connected yA zA |>.map inc
  have hdeg : HC.degree xC = 1 := by
    rw [degree_induce_eq_card_filter]
    have hloop : ¬G.Adj x x := G.loopless.irrefl x
    -- PORT: `if_neg` is deprecated on Lean 4.34.0-rc1; discharge the `ite` with the hypothesis.
    simp only [C, Finset.filter_insert, hloop, ↓reduceIte]
    exact hone
  have herase := edgeCountOn_erase G C xC.2
  have hOld : edgeCountOn G A + 1 = A.card := by
    rw [edgeCountOn_eq_card_edgeFinset]
    simpa using hT.card_edgeFinset
  have hpos : 1 ≤ edgeCountOn G C := by
    have := HC.degree_le_card_edgeFinset xC
    rw [edgeCountOn_eq_card_edgeFinset]
    simpa [HC, hdeg] using this
  have hE : edgeCountOn G C + 1 = C.card := by
    have hEraseSet : C.erase x = A := by simp [C, hxA]
    rw [hEraseSet, hdeg] at herase
    have hCcard : C.card = A.card + 1 := by simp [C, hxA]
    omega
  change HC.IsTree
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card]
  rw [edgeCountOn_eq_card_edgeFinset] at hE
  simpa [HC] using hE

/-- A centre joined to every vertex of an independent set is a tree. -/
lemma isTree_induce_star {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (u : V)
    (huB : u ∉ B)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂)
    (hu : ∀ b ∈ B, G.Adj u b) :
    (G.induce ((insert u B : Finset V) : Set V)).IsTree := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      have hsingle : (G.induce (({u} : Finset V) : Set V)).IsTree := by
        let : Nonempty (({u} : Finset V) : Set V) := ⟨⟨u, by simp⟩⟩
        let : Subsingleton (({u} : Finset V) : Set V) := ⟨by
          intro a b
          apply Subtype.ext
          have ha : a.1 = u := by simpa using a.2
          have hb : b.1 = u := by simpa using b.2
          exact ha.trans hb.symm⟩
        exact SimpleGraph.IsTree.of_subsingleton
      simpa using hsingle
  | @insert b B hb ih =>
      have hub : u ≠ b := by
        intro h
        apply huB
        simp [h]
      have huB' : u ∉ B := by
        intro h
        exact huB (Finset.mem_insert_of_mem h)
      have hB' : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂
        exact hB b₁ (Finset.mem_insert_of_mem hb₁) b₂ (Finset.mem_insert_of_mem hb₂)
      have hu' : ∀ z ∈ B, G.Adj u z := by
        intro z hz
        exact hu z (Finset.mem_insert_of_mem hz)
      have ihT := ih huB' hB' hu'
      have hbA : b ∉ insert u B := by simp [hb, hub.symm]
      have hbu : G.Adj b u := (hu b (by simp)).symm
      have hone : #((insert u B).filter (G.Adj b)) = 1 := by
        have heq : (insert u B).filter (G.Adj b) = {u} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hz, hadj⟩
            · rfl
            · exact False.elim (hB b (by simp) z (by simp [hz]) hadj)
          · rintro rfl
            exact ⟨Or.inl rfl, hbu⟩
        rw [heq]
        simp
      have hleaf := isTree_induce_insert_of_one_neighbor G (insert u B) b u
        ihT hbA (by simp) hbu hone
      have heq : insert b (insert u B) = insert u (insert b B) := by
        ext z
        simp [or_left_comm]
      rw [← heq]
      exact hleaf

/-- The rearranged exceptional configuration is the broom-shaped tree used in the proof. -/
lemma isTree_induce_broom {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (u x p : V)
    (huB : u ∉ B) (hxB : x ∉ B) (hxu : x ≠ u) (hp : p ∈ B)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂)
    (hu : ∀ b ∈ B, G.Adj u b)
    (hxp : G.Adj x p) (hxu_not : ¬G.Adj x u)
    (hxonly : ∀ b ∈ B, G.Adj x b → b = p) :
    (G.induce ((insert x (insert u B) : Finset V) : Set V)).IsTree := by
  classical
  have hstar := isTree_induce_star G B u huB hB hu
  have hxD : x ∉ insert u B := by simp [hxB, hxu]
  have hone : #((insert u B).filter (G.Adj x)) = 1 := by
    have heq : (insert u B).filter (G.Adj x) = {p} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hz, hadj⟩
        · exact False.elim (hxu_not hadj)
        · exact hxonly z hz hadj
      · rintro rfl
        exact ⟨Or.inr hp, hxp⟩
    rw [heq]
    simp
  exact isTree_induce_insert_of_one_neighbor G (insert u B) x p hstar hxD
    (by simp [hp]) hxp hone

/-- If deleting `u` leaves no edges in a tree, then every other vertex is adjacent to `u`. -/
lemma tree_center_of_independent_erase {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (u : V)
    (hT : (G.induce (A : Set V)).IsTree) (hu : u ∈ A)
    (hno : ∀ y ∈ A.erase u, ∀ z ∈ A.erase u, ¬G.Adj y z) :
    ∀ z ∈ A.erase u, G.Adj u z := by
  classical
  intro z hz
  let uA : (A : Set V) := ⟨u, hu⟩
  let zA : (A : Set V) := ⟨z, Finset.mem_of_mem_erase hz⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath uA zA
  have huz : u ≠ z := (Finset.ne_of_mem_erase hz).symm
  have hnil : ¬p.Nil := by
    intro h
    exact huz (congrArg Subtype.val (hp.nil_iff_eq.mp h))
  have hadj := p.adj_penultimate hnil
  by_cases heq : p.penultimate = uA
  · simpa [heq] using hadj
  · exfalso
    have hpA : p.penultimate.1 ∈ A.erase u := Finset.mem_erase.mpr ⟨by
      intro h
      apply heq
      exact Subtype.ext h, p.penultimate.2⟩
    exact hno p.penultimate.1 hpA z hz hadj

/-- The extension step in Simonovits's sharp induction. -/
lemma extend_balanced_tree_join {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A B : Finset V) (x : V) (hxU : x ∉ U)
    (hjoin : IsBalancedTreeJoinOn G U A B)
    (hdeg : #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) =
      stepDegree (U.card + 1)) :
    HasTarget G ∨ ∃ A' B', IsBalancedTreeJoinOn G (insert x U) A' B' := by
  classical
  rcases hjoin with ⟨hpart, hdisj, hT, hBind, hcross, hBA, hAB⟩
  have hpartF : A ∪ B = U := by
    ext z
    have hz := Set.ext_iff.mp hpart z
    simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
  have hdisjF : Disjoint A B := by simpa only [Finset.disjoint_coe] using hdisj
  have hxA : x ∉ A := by
    intro hx
    apply hxU
    rw [← hpartF]
    exact Finset.mem_union_left B hx
  have hxB : x ∉ B := by
    intro hx
    apply hxU
    rw [← hpartF]
    exact Finset.mem_union_right A hx
  have hUcard : U.card = A.card + B.card := by
    rw [← hpartF, Finset.card_union_of_disjoint hdisjF]
  let SA := A.filter (G.Adj x)
  let SB := B.filter (G.Adj x)
  have hSAle : SA.card ≤ A.card := Finset.card_filter_le _ _
  have hSBle : SB.card ≤ B.card := Finset.card_filter_le _ _
  change SA.card + SB.card = stepDegree (U.card + 1) at hdeg
  by_cases htwo : 2 ≤ SA.card ∧ 2 ≤ SB.card
  · exact Or.inl (hasTarget_of_two_neighbors_on_both_sides G A B x hT hdisj
      hcross hxA hxB htwo.1 htwo.2)
  have hsmall : SA.card ≤ 1 ∨ SB.card ≤ 1 := by omega
  by_cases hleaf : SA.card = 1 ∧ SB.card = B.card
  · rcases hleaf with ⟨hSA1, hSBcard⟩
    obtain ⟨u, hSAeq⟩ := Finset.card_eq_one.mp hSA1
    have huS : u ∈ SA := by simp [hSAeq]
    have huA : u ∈ A := (Finset.mem_filter.mp huS).1
    have hxu : G.Adj x u := (Finset.mem_filter.mp huS).2
    have hSBeq : SB = B :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hnewT := isTree_induce_insert_of_one_neighbor G A x u hT hxA huA hxu hSA1
    refine Or.inr ⟨insert x A, B, ?_⟩
    refine ⟨?_, ?_, hnewT, hBind, ?_, ?_, ?_⟩
    · have heq : insert x A ∪ B = insert x U := by
        rw [insert_union, hpartF]
      simpa only [Finset.coe_union, Finset.coe_insert] using
        congrArg (fun s : Finset V ↦ (s : Set V)) heq
    · rw [Set.disjoint_left]
      intro z hz hzB
      rcases Finset.mem_insert.mp hz with rfl | hzA
      · exact hxB hzB
      · exact hdisj.le_bot ⟨hzA, hzB⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl | haA
      · have : b ∈ SB := by rw [hSBeq]; exact hb
        exact (Finset.mem_filter.mp this).2
      · exact hcross a haA b hb
    · simp [hxA]
      omega
    · simp [hxA]
      unfold stepDegree at hdeg
      omega
  by_cases hind : SB.card = 0 ∧ SA.card = A.card
  · rcases hind with ⟨hSB0, hSAcard⟩
    have hSAeq : SA = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hxBnone : ∀ b ∈ B, ¬G.Adj x b := by
      intro b hb hadj
      have : b ∈ SB := Finset.mem_filter.mpr ⟨hb, hadj⟩
      have : 0 < SB.card := Finset.card_pos.mpr ⟨b, this⟩
      omega
    have hBno : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
      intro b₁ hb₁ b₂ hb₂ hadj
      have h : (G.induce (B : Set V)).Adj ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ := hadj
      rw [hBind] at h
      exact h
    have hnewB : G.induce ((insert x B : Finset V) : Set V) = ⊥ := by
      ext y z
      simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
      intro hadj
      have hy : y.1 = x ∨ y.1 ∈ B := by simpa using y.2
      have hz : z.1 = x ∨ z.1 ∈ B := by simpa using z.2
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · simp [hy, hz] at hadj
      · exact hxBnone z hz (by simpa [hy] using hadj)
      · exact hxBnone y hy (by simpa [hz] using hadj.symm)
      · exact hBno y hy z hz hadj
    refine Or.inr ⟨A, insert x B, ?_⟩
    refine ⟨?_, ?_, hT, hnewB, ?_, ?_, ?_⟩
    · have heq : A ∪ insert x B = insert x U := by
        rw [Finset.union_insert, hpartF]
      simpa only [Finset.coe_union, Finset.coe_insert] using
        congrArg (fun s : Finset V ↦ (s : Set V)) heq
    · rw [Set.disjoint_left]
      intro z hzA hz
      rcases Finset.mem_insert.mp hz with rfl | hzB
      · exact hxA hzA
      · exact hdisj.le_bot ⟨hzA, hzB⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp hb with rfl | hbB
      · have : a ∈ SA := by rw [hSAeq]; exact ha
        exact (Finset.mem_filter.mp this).2.symm
      · exact hcross a ha b hbB
    · simp [hxB]
      unfold stepDegree at hdeg
      omega
    · simp [hxB]
      omega
  by_cases heqcard : A.card = B.card
  · have hSAcard : SA.card = A.card := by
      unfold stepDegree at hdeg
      omega
    have hSB1 : SB.card = 1 := by
      unfold stepDegree at hdeg
      omega
    have hAge2 : 2 ≤ A.card := by
      by_contra h
      have : A.card ≤ 1 := by omega
      have hleaf' : SA.card = 1 ∧ SB.card = B.card := by omega
      exact hleaf hleaf'
    have hSAeq : SA = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    obtain ⟨p, hSBeq⟩ := Finset.card_eq_one.mp hSB1
    have hpS : p ∈ SB := by simp [hSBeq]
    have hpB : p ∈ B := (Finset.mem_filter.mp hpS).1
    have hxp : G.Adj x p := (Finset.mem_filter.mp hpS).2
    have hEnonempty : (G.induce (A : Set V)).edgeFinset.Nonempty := by
      rw [← Finset.card_pos]
      have hcardT := hT.card_edgeFinset
      have hcardA : Fintype.card (A : Set V) = A.card := Fintype.card_coe _
      omega
    obtain ⟨e, he⟩ := hEnonempty
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ y z =>
      have hyS : y.1 ∈ SA := by rw [hSAeq]; exact y.2
      have hzS : z.1 ∈ SA := by rw [hSAeq]; exact z.2
      exact Or.inl (HasTarget.of_four_clique hxp (Finset.mem_filter.mp hyS).2
        (Finset.mem_filter.mp hzS).2 (hcross y y.2 p hpB).symm
        (hcross z z.2 p hpB).symm he)
  · have hdiff : A.card = B.card + 1 ∨ A.card = B.card + 2 := by omega
    have hSB1 : SB.card = 1 := by
      unfold stepDegree at hdeg
      omega
    have hSApred : SA.card + 1 = A.card := by
      unfold stepDegree at hdeg
      omega
    obtain ⟨p, hSBeq⟩ := Finset.card_eq_one.mp hSB1
    have hpS : p ∈ SB := by simp [hSBeq]
    have hpB : p ∈ B := (Finset.mem_filter.mp hpS).1
    have hxp : G.Adj x p := (Finset.mem_filter.mp hpS).2
    have hSAssub : SA ⊂ A := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨Finset.filter_subset _ _, fun h ↦ by
        have := congrArg Finset.card h
        omega⟩
    obtain ⟨u, huA, huS⟩ := Finset.exists_of_ssubset hSAssub
    have hSAerase : SA = A.erase u := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_erase.mpr ⟨fun h ↦ huS (h ▸ hz), (Finset.mem_filter.mp hz).1⟩
      · simp [huA]
        omega
    by_cases hedge : ∃ y ∈ A.erase u, ∃ z ∈ A.erase u, G.Adj y z
    · obtain ⟨y, hy, z, hz, hyz⟩ := hedge
      have hyS : y ∈ SA := by rw [hSAerase]; exact hy
      have hzS : z ∈ SA := by rw [hSAerase]; exact hz
      exact Or.inl (HasTarget.of_four_clique hxp (Finset.mem_filter.mp hyS).2
        (Finset.mem_filter.mp hzS).2
        (hcross y (Finset.mem_of_mem_erase hy) p hpB).symm
        (hcross z (Finset.mem_of_mem_erase hz) p hpB).symm hyz)
    · push Not at hedge
      have hBno : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂ hadj
        have h : (G.induce (B : Set V)).Adj ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ := hadj
        rw [hBind] at h
        exact h
      have huB : u ∉ B := by
        intro hu
        exact hdisj.le_bot ⟨huA, hu⟩
      have hxu_not : ¬G.Adj x u := by
        intro hadj
        exact huS (Finset.mem_filter.mpr ⟨huA, hadj⟩)
      have hxonly : ∀ b ∈ B, G.Adj x b → b = p := by
        intro b hb hadj
        have : b ∈ SB := Finset.mem_filter.mpr ⟨hb, hadj⟩
        rw [hSBeq] at this
        simpa using this
      have huall : ∀ b ∈ B, G.Adj u b := fun b hb ↦ hcross u huA b hb
      have hxu_ne : x ≠ u := fun h ↦ hxA (h ▸ huA)
      have hbroom := isTree_induce_broom G B u x p huB hxB
        hxu_ne hpB hBno huall hxp hxu_not hxonly
      have hcenter := tree_center_of_independent_erase G A u hT huA hedge
      have hnewInd : G.induce ((A.erase u : Finset V) : Set V) = ⊥ := by
        ext y z
        simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
        exact hedge y y.2 z z.2
      refine Or.inr ⟨insert x (insert u B), A.erase u, ?_⟩
      refine ⟨?_, ?_, hbroom, hnewInd, ?_, ?_, ?_⟩
      · have heq : insert x (insert u B) ∪ A.erase u = insert x U := by
          ext z
          rw [← hpartF]
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ((rfl | rfl | hzB) | ⟨_, hzA⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl huA)
            · exact Or.inr (Or.inr hzB)
            · exact Or.inr (Or.inl hzA)
          · rintro (rfl | hzA | hzB)
            · exact Or.inl (Or.inl rfl)
            · by_cases hzu : z = u
              · exact Or.inl (Or.inr (Or.inl hzu))
              · exact Or.inr ⟨hzu, hzA⟩
            · exact Or.inl (Or.inr (Or.inr hzB))
        simpa only [Finset.coe_union, Finset.coe_insert] using
          congrArg (fun s : Finset V ↦ (s : Set V)) heq
      · rw [Set.disjoint_left]
        intro z hz hze
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hxA (Finset.mem_of_mem_erase hze)
        · rcases Finset.mem_insert.mp hz with rfl | hzB
          · exact (Finset.ne_of_mem_erase hze) rfl
          · exact hdisj.le_bot ⟨Finset.mem_of_mem_erase hze, hzB⟩
      · intro a ha z hz
        rcases Finset.mem_insert.mp ha with rfl | ha
        · have : z ∈ SA := by rw [hSAerase]; exact hz
          exact (Finset.mem_filter.mp this).2
        · rcases Finset.mem_insert.mp ha with rfl | haB
          · exact hcenter z hz
          · exact (hcross z (Finset.mem_of_mem_erase hz) a haB).symm
      · have htreecard : #(insert x (insert u B)) = B.card + 2 := by
          simp [hxB, huB, hxu_ne]
        have hindcard : #(A.erase u) = A.card - 1 := by simp [huA]
        rw [htreecard, hindcard]
        omega
      · have htreecard : #(insert x (insert u B)) = B.card + 2 := by
          simp [hxB, huB, hxu_ne]
        have hindcard : #(A.erase u) = A.card - 1 := by simp [huA]
        rw [htreecard, hindcard]
        omega

/-- Adding a missing chord to a spanning tree creates a cycle. -/
lemma not_isAcyclic_of_tree_le_extra_edge {V : Type*}
    (H G : SimpleGraph V) (A : Finset V) (hHG : H ≤ G)
    (hT : (H.induce (A : Set V)).IsTree) {u v : V}
    (hu : u ∈ A) (hv : v ∈ A) (hGuv : G.Adj u v) (hHuv : ¬H.Adj u v) :
    ¬(G.induce (A : Set V)).IsAcyclic := by
  classical
  let uA : (A : Set V) := ⟨u, hu⟩
  let vA : (A : Set V) := ⟨v, hv⟩
  intro hacyc
  have hleTree : H.induce (A : Set V) ≤ G.induce (A : Set V) := fun _ _ h ↦ hHG h
  have hleEdge : SimpleGraph.edge uA vA ≤ G.induce (A : Set V) := by
    rw [SimpleGraph.edge_le_iff]
    exact Or.inr hGuv
  have hsup : H.induce (A : Set V) ⊔ SimpleGraph.edge uA vA ≤
      G.induce (A : Set V) := sup_le hleTree hleEdge
  have hs := hacyc.anti hsup
  rw [SimpleGraph.isAcyclic_sup_fromEdgeSet_iff] at hs
  rcases hs.2 (hT.connected uA vA) with huv | hadj
  · exact hGuv.ne (congrArg Subtype.val huv)
  · exact hHuv hadj

/-- One additional edge over a balanced tree join forces one of the two target graphs. -/
lemma augment_balanced_tree_join {V : Type*}
    (H G : SimpleGraph V)
    (U A B : Finset V) (hU4 : 4 ≤ U.card) (hHG : H ≤ G)
    (hjoin : IsBalancedTreeJoinOn H U A B)
    {u v : V} (huU : u ∈ U) (hvU : v ∈ U)
    (hGuv : G.Adj u v) (hHuv : ¬H.Adj u v) : HasTarget G := by
  classical
  rcases hjoin with ⟨hpart, hdisj, hT, hBind, hcross, hBA, hAB⟩
  have hpartF : A ∪ B = U := by
    ext z
    have hz := Set.ext_iff.mp hpart z
    simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
  have hdisjF : Disjoint A B := by simpa only [Finset.disjoint_coe] using hdisj
  have hUcard : U.card = A.card + B.card := by
    rw [← hpartF, Finset.card_union_of_disjoint hdisjF]
  have hu : u ∈ A ∨ u ∈ B := by
    rw [← Finset.mem_union, hpartF]
    exact huU
  have hv : v ∈ A ∨ v ∈ B := by
    rw [← Finset.mem_union, hpartF]
    exact hvU
  rcases hu with huA | huB <;> rcases hv with hvA | hvB
  · have hacyc := not_isAcyclic_of_tree_le_extra_edge H G A hHG hT huA hvA hGuv hHuv
    by_cases hB2 : 2 ≤ B.card
    · have hB1 : 1 < B.card := by omega
      obtain ⟨north, hnB, south, hsB, hns⟩ := Finset.one_lt_card.mp hB1
      apply hasTarget_of_not_isAcyclic_two_apices G A north south hacyc
      · intro hnA
        exact hdisj.le_bot ⟨hnA, hnB⟩
      · intro hsA
        exact hdisj.le_bot ⟨hsA, hsB⟩
      · exact hns
      · intro z hz
        exact ⟨hHG (hcross z hz north hnB).symm,
          hHG (hcross z hz south hsB).symm⟩
    · have hBcard : B.card = 1 := by omega
      have hAcard : A.card = 3 := by omega
      obtain ⟨b, hBeq⟩ := Finset.card_eq_one.mp hBcard
      have hbB : b ∈ B := by simp [hBeq]
      have hcycle : ∃ l : ℕ, 3 ≤ l ∧
          SimpleGraph.cycleGraph l ⊑ G.induce (A : Set V) := by
        by_contra h
        apply hacyc
        rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
        intro l hl hc
        exact h ⟨l, hl, hc⟩
      obtain ⟨l, hl, ⟨f⟩⟩ := hcycle
      have hle : l ≤ 3 := by
        rw [← hAcard, ← Fintype.card_coe, ← Fintype.card_fin l]
        exact Fintype.card_le_of_injective f f.injective
      have hl3 : l = 3 := by omega
      subst l
      let fG : (SimpleGraph.cycleGraph 3).Copy G :=
        (SimpleGraph.Copy.induce G (A : Set V)).comp f
      have h01 : G.Adj (fG 0) (fG 1) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      have h02 : G.Adj (fG 0) (fG 2) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      have h12 : G.Adj (fG 1) (fG 2) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      exact HasTarget.of_four_clique
        (hHG (hcross (f 0).1 (f 0).2 b hbB).symm)
        (hHG (hcross (f 1).1 (f 1).2 b hbB).symm)
        (hHG (hcross (f 2).1 (f 2).2 b hbB).symm) h01 h02 h12
  · exact False.elim (hHuv (hcross u huA v hvB))
  · exact False.elim (hHuv (hcross v hvA u huB).symm)
  · have huv : u ≠ v := hGuv.ne
    have hB2 : 2 ≤ B.card := by
      have : 1 < B.card := Finset.one_lt_card.mpr ⟨u, huB, v, hvB, huv⟩
      omega
    have hA2 : 2 ≤ A.card := by omega
    have hEnonempty : (H.induce (A : Set V)).edgeFinset.Nonempty := by
      rw [← Finset.card_pos]
      have hcardT := hT.card_edgeFinset
      have hcardA : Fintype.card (A : Set V) = A.card := Fintype.card_coe _
      omega
    obtain ⟨e, he⟩ := hEnonempty
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ y z =>
      exact HasTarget.of_four_clique hGuv
        (hHG (hcross y y.2 u huB).symm) (hHG (hcross z z.2 u huB).symm)
        (hHG (hcross y y.2 v hvB).symm) (hHG (hcross z z.2 v hvB).symm)
        (hHG he)

/-- Keep any prescribed number of the edges induced on `U`, and discard all other edges. -/
lemma exists_subgraph_edgeCountOn_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) {m : ℕ}
    (hm : m ≤ edgeCountOn G U) :
    ∃ H : SimpleGraph V, H ≤ G ∧ edgeCountOn H U = m := by
  classical
  let E := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ U
  have hEm : m ≤ E.card := by
    rw [edgeCountOn_eq_card_edgeFinset] at hm
    rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset]
    exact hm
  obtain ⟨K, hKE, hKcard⟩ := Finset.exists_subset_card_eq hEm
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (K : Set (Sym2 V))
  refine ⟨H, ?_, ?_⟩
  · rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    have heK : e ∈ K := he.1
    have heE : e ∈ E := hKE heK
    exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heE).1
  · have hsupp : H.support ⊆ (U : Set V) := by
      intro x hx
      rw [SimpleGraph.mem_support] at hx
      obtain ⟨y, hxy⟩ := hx
      have heK : s(x, y) ∈ K :=
        ((SimpleGraph.fromEdgeSet_adj (K : Set (Sym2 V))).mp hxy).1
      have heE : s(x, y) ∈ E := hKE heK
      have hsub := (Finset.mem_filter.mp heE).2
      exact hsub (by simp)
    have hKEdiag : Disjoint (K : Set (Sym2 V)) Sym2.diagSet := by
      rw [Set.disjoint_left]
      intro e heK hediag
      have heE : e ∈ E := hKE heK
      exact G.not_isDiag_of_mem_edgeFinset (Finset.mem_filter.mp heE).1 hediag
    have hedge : H.edgeSet = (K : Set (Sym2 V)) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
      exact hKEdiag
    let inc : (U : Set V) ↪ V := Function.Embedding.subtype _
    let F : Sym2 (U : Set V) → Sym2 V := inc.sym2Map
    have himage : F '' (H.induce (U : Set V)).edgeSet = H.edgeSet := by
      apply Set.Subset.antisymm
      · intro e he
        obtain ⟨d, hd, rfl⟩ := he
        induction d using Sym2.inductionOn with
        | _ a b => exact hd
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b =>
          have hab : H.Adj a b := he
          have ha : a ∈ H.support := ⟨b, hab⟩
          have hb : b ∈ H.support := ⟨a, hab.symm⟩
          refine ⟨s(⟨a, hsupp ha⟩, ⟨b, hsupp hb⟩), hab, ?_⟩
          rfl
    unfold edgeCountOn
    calc
      (H.induce (U : Set V)).edgeSet.ncard =
          (F '' (H.induce (U : Set V)).edgeSet).ncard :=
        (Set.ncard_image_of_injective _ inc.sym2Map.injective).symm
      _ = H.edgeSet.ncard := congrArg Set.ncard himage
      _ = (K : Set (Sym2 V)).ncard := by rw [hedge]
      _ = K.card := Set.ncard_coe_finset K
      _ = m := hKcard

/-- If `H ≤ G` and `G` has more edges on `U`, one of those induced edges is absent from `H`. -/
lemma exists_extra_adj_on {V : Type*} [Fintype V]
    {H G : SimpleGraph V} (U : Finset V) (hHG : H ≤ G)
    (hlt : edgeCountOn H U < edgeCountOn G U) :
    ∃ u ∈ U, ∃ v ∈ U, G.Adj u v ∧ ¬H.Adj u v := by
  by_contra hno
  have hall : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v := by
    intro u hu v hv huv
    by_contra hn
    exact hno ⟨u, hu, v, hv, huv, hn⟩
  have hGH : G.induce (U : Set V) ≤ H.induce (U : Set V) := by
    intro u v huv
    exact hall u.1 u.2 v.1 v.2 huv
  have hHG' : H.induce (U : Set V) ≤ G.induce (U : Set V) := by
    intro u v huv
    exact hHG huv
  have heq : G.induce (U : Set V) = H.induce (U : Set V) :=
    le_antisymm hGH hHG'
  unfold edgeCountOn at hlt
  rw [heq] at hlt
  exact (Nat.lt_irrefl _ hlt)

lemma lowerThreshold_even (s : ℕ) :
    lowerThreshold (2 * s) = s * s + s - 1 := by
  cases s with
  | zero => simp [lowerThreshold]
  | succ s =>
      unfold lowerThreshold
      rw [show (2 * (s + 1)) * (2 * (s + 1)) = 4 * ((s + 1) * (s + 1)) by ring]
      simp
      omega

lemma lowerThreshold_odd (s : ℕ) :
    lowerThreshold (2 * s + 1) = s * s + 2 * s := by
  unfold lowerThreshold
  rw [show (2 * s + 1) * (2 * s + 1) = 4 * (s * s + s) + 1 by ring]
  simp
  omega

lemma problemThreshold_eq_lowerThreshold_add_one {n : ℕ} (hn : 1 ≤ n) :
    problemThreshold n = lowerThreshold n + 1 := by
  simp [problemThreshold, lowerThreshold]
  omega

lemma lowerThreshold_succ (n : ℕ) (hn : 0 < n) :
    lowerThreshold (n + 1) = lowerThreshold n + stepDegree (n + 1) := by
  rcases n.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [← two_mul s] at hn ⊢
    have hs : 0 < s := by omega
    rw [lowerThreshold_even, lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    rw [hh]
    omega
  · rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega]
    rw [lowerThreshold_even, lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * (s + 1) + 1) / 2 = s + 1 := by omega
    rw [hh]
    have he : (s + 1) * (s + 1) + (s + 1) - 1 =
        (s + 1) * (s + 1) + s := by omega
    rw [he]
    ring

lemma twice_lowerThreshold_lt (n : ℕ) (hn : 0 < n) :
    2 * lowerThreshold n < n * (stepDegree n + 1) := by
  rcases n.even_or_odd with ⟨s, hs⟩ | ⟨s, hs⟩
  · subst n
    have hs0 : 0 < s := by omega
    rw [← two_mul s]
    rw [lowerThreshold_even]
    unfold stepDegree
    have hh : (2 * s + 1) / 2 = s := by omega
    rw [hh]
    have hsub : s * s + s - 1 + 1 = s * s + s := by omega
    nlinarith
  · subst n
    rw [lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    rw [hh]
    nlinarith

/-- At the one-edge-lower extremal value there is a vertex of at most the induction degree. -/
lemma exists_degree_le_stepDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (hU : U.Nonempty)
    (hcard : edgeCountOn G U = lowerThreshold U.card) :
    ∃ (x : V) (hx : x ∈ U),
      (G.induce (U : Set V)).degree ⟨x, hx⟩ ≤ stepDegree U.card := by
  classical
  let H := G.induce (U : Set V)
  let : Nonempty (U : Set V) := Set.nonempty_coe_sort.mpr (by simpa using hU)
  obtain ⟨x, hx⟩ := H.exists_minimal_degree_vertex
  by_cases hle : H.degree x ≤ stepDegree U.card
  · exact ⟨x.1, x.2, hle⟩
  · have hall : ∀ v : (U : Set V), stepDegree U.card + 1 ≤ H.degree v := by
      intro v
      have hmin := H.minDegree_le_degree v
      rw [hx] at hmin
      omega
    have hsum : U.card * (stepDegree U.card + 1) ≤ ∑ v, H.degree v := by
      calc
        U.card * (stepDegree U.card + 1) =
            ∑ _v : (U : Set V), (stepDegree U.card + 1) := by simp
        _ ≤ ∑ v, H.degree v := Finset.sum_le_sum fun v _ ↦ hall v
    rw [H.sum_degrees_eq_twice_card_edges] at hsum
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    have hlt := twice_lowerThreshold_lt U.card hpos
    have hedge : #H.edgeFinset = lowerThreshold U.card := by
      rw [edgeCountOn_eq_card_edgeFinset] at hcard
      simpa [H] using hcard
    rw [hedge] at hsum
    omega

/-- The simultaneous sharp induction.  Its first component classifies every target-free graph at
the one-edge-lower bound; its second component is Simonovits's forcing theorem. -/
theorem sharp_simonovits_induction {V : Type*} [Fintype V]
    (U : Finset V) (hU : U.Nonempty) :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      edgeCountOn G U = lowerThreshold U.card →
        HasTarget G ∨ ∃ A B, IsBalancedTreeJoinOn G U A B) ∧
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      lowerThreshold U.card + 1 ≤ edgeCountOn G U → HasTarget G) := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U with
  | h n ih =>
    have hnpos : 0 < n := by
      rw [← hn]
      exact Finset.card_pos.mpr hU
    have hp : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        edgeCountOn G U = lowerThreshold n →
          HasTarget G ∨ ∃ A B, IsBalancedTreeJoinOn G U A B := by
      intro G instG hcard
      by_cases hn1 : n = 1
      · have hUcard : U.card = 1 := hn.trans hn1
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hUcard
        refine Or.inr ⟨{a}, ∅, ?_⟩
        refine ⟨by simp, by simp, ?_, ?_, by simp, by simp, by simp⟩
        · exact isTree_induce_star G ∅ a (by simp) (by simp) (by simp)
        · ext x y
          simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
          intro _
          simpa using x.2
      · have hn2 : 2 ≤ n := by omega
        have hcardU : edgeCountOn G U = lowerThreshold U.card := by
          rw [hn]
          exact hcard
        obtain ⟨x, hxU, hxdeg⟩ := exists_degree_le_stepDegree G U hU hcardU
        let U' := U.erase x
        have hU'card : U'.card + 1 = U.card := by
          rw [show U' = U.erase x by rfl, Finset.card_erase_of_mem hxU]
          omega
        have hU'pos : 0 < U'.card := by omega
        have hU'nonempty : U'.Nonempty := Finset.card_pos.mp hU'pos
        have hU'lt : U'.card < n := by omega
        have hi := ih U'.card hU'lt U' hU'nonempty rfl
        have herase := edgeCountOn_erase G U hxU
        have hq : lowerThreshold U.card =
            lowerThreshold U'.card + stepDegree U.card := by
          have h := lowerThreshold_succ U'.card hU'pos
          rw [hU'card] at h
          exact h
        have hOldGe : lowerThreshold U'.card ≤ edgeCountOn G U' := by
          rw [show U.erase x = U' by rfl] at herase
          omega
        by_cases hOldHigh : lowerThreshold U'.card + 1 ≤ edgeCountOn G U'
        · exact Or.inl (hi.2 G hOldHigh)
        · have hOldEq : edgeCountOn G U' = lowerThreshold U'.card := by omega
          rcases hi.1 G hOldEq with htarget | ⟨A, B, hjoin⟩
          · exact Or.inl htarget
          · have hdegree :
                (G.induce (U : Set V)).degree ⟨x, hxU⟩ = stepDegree U.card := by
              rw [show U.erase x = U' by rfl] at herase
              omega
            have hpartF : A ∪ B = U' := by
              ext z
              have hz := Set.ext_iff.mp hjoin.1 z
              simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
            have hdisjF : Disjoint A B := by
              simpa only [Finset.disjoint_coe] using hjoin.2.1
            have hfilterErase : U.filter (G.Adj x) = U'.filter (G.Adj x) := by
              ext z
              simp only [U', Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨hzU, hxz⟩
                exact ⟨⟨fun hzx ↦ G.loopless.irrefl x (hzx ▸ hxz), hzU⟩, hxz⟩
              · rintro ⟨⟨_, hzU⟩, hxz⟩
                exact ⟨hzU, hxz⟩
            have hfilterCard : #(U.filter (G.Adj x)) =
                #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) := by
              rw [hfilterErase, ← hpartF, Finset.filter_union]
              rw [Finset.card_union_of_disjoint
                (hdisjF.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
            have hdegFilters : #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) =
                stepDegree (U'.card + 1) := by
              have hdcard := degree_induce_eq_card_filter G U hxU
              rw [hdegree, hfilterCard] at hdcard
              rw [hU'card]
              exact hdcard.symm
            rcases extend_balanced_tree_join G U' A B x (by simp [U']) hjoin hdegFilters with
              htarget | ⟨A', B', hjoin'⟩
            · exact Or.inl htarget
            · refine Or.inr ⟨A', B', ?_⟩
              simpa [U', hxU] using hjoin'
    refine ⟨hp, ?_⟩
    intro G instG hcard
    by_cases hn4 : 4 ≤ n
    · have hm : lowerThreshold n ≤ edgeCountOn G U := by omega
      obtain ⟨H, hHG, hHcard⟩ := exists_subgraph_edgeCountOn_eq G U hm
      let : DecidableRel H.Adj := Classical.decRel H.Adj
      rcases hp H hHcard with htarget | ⟨A, B, hjoin⟩
      · exact htarget.mono hHG
      · have hlt : edgeCountOn H U < edgeCountOn G U := by omega
        obtain ⟨u, hu, v, hv, hGuv, hHuv⟩ := exists_extra_adj_on U hHG hlt
        apply augment_balanced_tree_join H G U A B
        · omega
        · exact hHG
        · exact hjoin
        · exact hu
        · exact hv
        · exact hGuv
        · exact hHuv
    · have hmax : edgeCountOn G U ≤ U.card.choose 2 := by
        rw [edgeCountOn_eq_card_edgeFinset, ← Fintype.card_coe U]
        exact SimpleGraph.card_edgeFinset_le_card_choose_two
      rw [hn] at hmax
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl <;>
        norm_num [lowerThreshold] at hcard hmax hn <;> omega

/-- Simonovits's stronger resolution of Erdős Problem 1019: at the stated threshold, the host
contains either `K₄` or a bipyramid over a cycle. -/
theorem erdos_1019_sharp {V : Type*} [Fintype V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : #G.edgeFinset = problemThreshold (Fintype.card V)) :
    HasTarget G := by
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (Fintype.card_pos)
  apply (sharp_simonovits_induction (Finset.univ : Finset V) hne).2 G
  have hthreshold := problemThreshold_eq_lowerThreshold_add_one (n := Fintype.card V)
    (Fintype.card_pos)
  rw [hthreshold] at hE
  have hcount : edgeCountOn G (Finset.univ : Finset V) = #G.edgeFinset := by
    rw [edgeCountOn_eq_edgeSet_ncard_of_support_subset G Finset.univ (by simp),
      edgeSet_ncard_eq_card_edgeFinset]
  simpa [hcount] using hE.ge

end

/-! ### Upstream module `Erdos1019Planar/StraightLine.lean` -/

/-!
# Straight-line drawings are plane drawings

A straight-line drawing (`SimpleGraph.IsStraightLineDrawing`) yields a plane drawing whose
arcs are the closed segments between the endpoint positions.  The Jordan arc of an edge is the
affine parametrization `t ↦ (1 - t) • pos u + t • pos v` of `[0, 1]`, which is continuous and
injective because `pos u ≠ pos v`.
-/

open _root_.SimpleGraph in
/-- A straight-line drawing gives a plane drawing, hence planarity. -/
theorem _root_.SimpleGraph.IsPlanar.of_isStraightLineDrawing {V : Type*} {G : SimpleGraph V} {pos : V → ℝ × ℝ}
    (h : G.IsStraightLineDrawing pos) : G.IsPlanar := by
  obtain ⟨hinj, hvert, hcross⟩ := h
  refine ⟨⟨pos, hinj, Sym2.lift ⟨fun u v ↦ segment ℝ (pos u) (pos v),
    fun u v ↦ segment_symm ℝ (pos u) (pos v)⟩, ?_, ?_, ?_⟩⟩
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [mem_edgeSet] at he
      refine ⟨u, v, rfl, fun t ↦ (1 - t) • pos u + t • pos v, ?_, ?_, by simp, by simp, ?_⟩
      · exact (by fun_prop : Continuous fun t : ℝ ↦ (1 - t) • pos u + t • pos v).continuousOn
      · intro s _ t _ hst
        have hne : pos v - pos u ≠ 0 := sub_ne_zero.mpr fun h' ↦ he.ne (hinj h').symm
        have hzero : (s - t) • (pos v - pos u) = 0 := by
          linear_combination (norm := module) hst
        rcases smul_eq_zero.mp hzero with hst' | hst'
        · exact sub_eq_zero.mp hst'
        · exact absurd hst' hne
      · exact segment_eq_image ℝ (pos u) (pos v)
  · intro e he w hw
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [mem_edgeSet] at he
      exact Sym2.mem_iff.mpr (hvert u v w he hw)
  · intro e he f hf hef
    induction e, f using Sym2.inductionOn₂ with
    | hf a b c d =>
      rw [mem_edgeSet] at he hf
      exact hcross a b c d he hf hef

/-! ### Upstream module `Erdos1019Planar/Separation.lean` -/

/-!
# Separating closed segments in the plane by affine functionals

Every non-crossing claim in the straight-line drawings of `K₄` and of the bipyramids is
reduced to the sign of an affine functional `lineFun a b c : ℝ × ℝ → ℝ` on the endpoints of the
segments involved.  This file records the few general facts needed.
-/

/-- The affine functional `p ↦ a * p.1 + b * p.2 + c` on the plane. -/
def lineFun (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  a * p.1 + b * p.2 + c

/-- On a segment, an affine functional is a convex combination of its endpoint values. -/
theorem lineFun_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hz : z ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      lineFun a b c z = (1 - t) * lineFun a b c p + t * lineFun a b c q ∧
      z = (1 - t) • p + t • q := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  refine ⟨t, ht0, ht1, ?_, rfl⟩
  simp only [lineFun, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- If both endpoint values are nonnegative, so is every value on the segment. -/
theorem lineFun_nonneg_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : 0 ≤ lineFun a b c p)
    (hq : 0 ≤ lineFun a b c q) (hz : z ∈ segment ℝ p q) : 0 ≤ lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  exact add_nonneg (mul_nonneg (sub_nonneg.2 ht1) hp) (mul_nonneg ht0 hq)

/-- If both endpoint values are nonpositive, so is every value on the segment. -/
theorem lineFun_nonpos_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p ≤ 0)
    (hq : lineFun a b c q ≤ 0) (hz : z ∈ segment ℝ p q) : lineFun a b c z ≤ 0 := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ht1) hp)
    (mul_nonpos_of_nonneg_of_nonpos ht0 hq)

/-- If both endpoint values are positive, so is every value on the segment. -/
theorem lineFun_pos_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : 0 < lineFun a b c p)
    (hq : 0 < lineFun a b c q) (hz : z ∈ segment ℝ p q) : 0 < lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt]
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simpa using hp
  · have h1 := mul_nonneg (sub_nonneg.2 ht1) hp.le
    have h2 := mul_pos htpos hq
    linarith

/-- If both endpoint values vanish, the functional vanishes on the segment. -/
theorem lineFun_eq_zero_of_mem_segment {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p = 0)
    (hq : lineFun a b c q = 0) (hz : z ∈ segment ℝ p q) : lineFun a b c z = 0 := by
  obtain ⟨t, ht0, ht1, hzt, -⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  rw [hzt, hp, hq, mul_zero, mul_zero, add_zero]

/-- If the functional vanishes at `p` and is positive at `q`, it is positive on the segment
away from `p`. -/
theorem lineFun_pos_of_mem_segment_of_ne {a b c : ℝ} {p q z : ℝ × ℝ} (hp : lineFun a b c p = 0)
    (hq : 0 < lineFun a b c q) (hz : z ∈ segment ℝ p q) (hzp : z ≠ p) : 0 < lineFun a b c z := by
  obtain ⟨t, ht0, ht1, hzt, hzeq⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  have ht : t ≠ 0 := by
    rintro rfl
    apply hzp
    rw [hzeq]
    simp
  rw [hzt, hp, mul_zero, zero_add]
  exact mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hq

/-- If the functional vanishes at `p` and is nonzero at `q`, it is nonzero on the segment
away from `p`. -/
theorem lineFun_ne_zero_of_mem_segment_of_ne {a b c : ℝ} {p q z : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q ≠ 0) (hz : z ∈ segment ℝ p q) (hzp : z ≠ p) :
    lineFun a b c z ≠ 0 := by
  obtain ⟨t, ht0, ht1, hzt, hzeq⟩ := lineFun_mem_segment (a := a) (b := b) (c := c) hz
  have ht : t ≠ 0 := by
    rintro rfl
    apply hzp
    rw [hzeq]
    simp
  rw [hzt, hp, mul_zero, zero_add]
  exact mul_ne_zero ht hq

/-- Two segments are disjoint when a functional is positive on one and nonpositive on the
other. -/
theorem segment_disjoint_of_pos_of_nonpos {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : 0 < lineFun a b c p) (hq : 0 < lineFun a b c q) (hr : lineFun a b c r ≤ 0)
    (hs : lineFun a b c s ≤ 0) : Disjoint (segment ℝ p q) (segment ℝ r s) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have h1 := lineFun_pos_of_mem_segment hp hq hz1
  have h2 := lineFun_nonpos_of_mem_segment hr hs hz2
  exact absurd h1 (not_lt.2 h2)

/-- If a functional vanishes at `p`, is positive at `q`, and is nonpositive on the segment
`[r, s]`, then `[p, q]` meets `[r, s]` at most in `p`. -/
theorem segment_inter_segment_subset_singleton {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : 0 < lineFun a b c q) (hr : lineFun a b c r ≤ 0)
    (hs : lineFun a b c s ≤ 0) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} := by
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_singleton_iff]
  by_contra hzp
  have h1 := lineFun_pos_of_mem_segment_of_ne hp hq hz1 hzp
  have h2 := lineFun_nonpos_of_mem_segment hr hs hz2
  exact absurd h1 (not_lt.2 h2)

/-- If a functional vanishes at `p`, is nonzero at `q`, and vanishes on the segment `[r, s]`,
then `[p, q]` meets `[r, s]` at most in `p`. -/
theorem segment_inter_segment_subset_singleton_of_ne_zero {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q ≠ 0) (hr : lineFun a b c r = 0)
    (hs : lineFun a b c s = 0) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} := by
  intro z ⟨hz1, hz2⟩
  rw [Set.mem_singleton_iff]
  by_contra hzp
  have h1 := lineFun_ne_zero_of_mem_segment_of_ne hp hq hz1 hzp
  exact h1 (lineFun_eq_zero_of_mem_segment hr hs hz2)

/-- A point where a functional is positive does not lie on a segment where it is nonpositive. -/
theorem notMem_segment_of_pos_of_nonpos {a b c : ℝ} {p q z : ℝ × ℝ} (hz : 0 < lineFun a b c z)
    (hp : lineFun a b c p ≤ 0) (hq : lineFun a b c q ≤ 0) : z ∉ segment ℝ p q := by
  intro h
  exact absurd (lineFun_nonpos_of_mem_segment hp hq h) (not_le.2 hz)

/-- A point where a functional is nonzero does not lie on a segment where it vanishes. -/
theorem notMem_segment_of_ne_zero {a b c : ℝ} {p q z : ℝ × ℝ} (hz : lineFun a b c z ≠ 0)
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q = 0) : z ∉ segment ℝ p q := by
  intro h
  exact hz (lineFun_eq_zero_of_mem_segment hp hq h)

/-! ### Upstream module `Erdos1019Planar/K4.lean` -/

section
/-!
# A straight-line drawing of `K₄`

Vertices `0, 1, 2, 3` of `K₄` are placed at `(0,0)`, `(4,0)`, `(0,4)` and `(1,1)`: an outer
triangle with the fourth vertex inside.  Every pair of disjoint edges is separated by one of the
functionals `y`, `x`, `4 - x - y`, and every two adjacent edges are non-collinear, so they
meet only at their common endpoint.
-/

open _root_.Set

/-- The positions of the four vertices of `K₄`. -/
def k4Pos : Fin 4 → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => (4, 0)
  | 2 => (0, 4)
  | 3 => (1, 1)

/-- Every edge `{u, v}` of the drawing lies on an affine line missing the two other vertices:
`y`, `x`, `4 - x - y` for the sides of the outer triangle and `x - y`, `x + 3y - 4`,
`3x + y - 4` for the edges through the inner vertex. -/
private lemma exists_lineFun_edge (u v : Fin 4) (huv : u ≠ v) :
    ∃ a b c : ℝ, lineFun a b c (k4Pos u) = 0 ∧ lineFun a b c (k4Pos v) = 0 ∧
      ∀ w : Fin 4, w ≠ u → w ≠ v → lineFun a b c (k4Pos w) ≠ 0 := by
  fin_cases u <;> fin_cases v <;>
    first
    | exact absurd rfl huv
    | (refine ⟨0, 1, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, 0, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨-1, -1, 4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, -1, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, 3, -4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨3, 1, -4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos])

/-- Two vertex-disjoint edges of the drawing have disjoint segments: one of `y`, `x`,
`4 - x - y` vanishes on one of them and is positive on the other. -/
private lemma disjoint_segment_k4Pos {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint (segment ℝ (k4Pos a) (k4Pos b)) (segment ℝ (k4Pos c) (k4Pos d)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hcd
    | exact absurd rfl hac
    | exact absurd rfl had
    | exact absurd rfl hbc
    | exact absurd rfl hbd
    | (refine segment_disjoint_of_pos_of_nonpos (a := 0) (b := 1) (c := 0) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := 0) (b := 1) (c := 0) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine segment_disjoint_of_pos_of_nonpos (a := 1) (b := 0) (c := 0) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := 1) (b := 0) (c := 0) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine segment_disjoint_of_pos_of_nonpos (a := -1) (b := -1) (c := 4) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := -1) (b := -1) (c := 4) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos])

/-- If `z` lies on the segments of the edges `{v, u}` and `{c, d}`, where `v` is an endpoint of
`{c, d}` and `u` is not, then `z` is the position of the common vertex `v`. -/
private lemma eq_k4Pos_of_mem_segment {v u c d : Fin 4} {z : ℝ × ℝ} (hcd : c ≠ d)
    (hv : v = c ∨ v = d) (huc : u ≠ c) (hud : u ≠ d) (hz1 : z ∈ segment ℝ (k4Pos v) (k4Pos u))
    (hz2 : z ∈ segment ℝ (k4Pos c) (k4Pos d)) : z = k4Pos v := by
  obtain ⟨a, b, e, hc, hd, hoff⟩ := exists_lineFun_edge c d hcd
  have hv0 : lineFun a b e (k4Pos v) = 0 := by rcases hv with rfl | rfl <;> assumption
  exact segment_inter_segment_subset_singleton_of_ne_zero hv0 (hoff u huc hud) hc hd ⟨hz1, hz2⟩

/-- The complete graph on four vertices has a straight-line plane drawing. -/
theorem top_four_isStraightLineDrawing :
    (⊤ : SimpleGraph (Fin 4)).IsStraightLineDrawing k4Pos := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    fin_cases u <;> fin_cases v <;> first | rfl | norm_num [k4Pos, Prod.ext_iff] at h
  · intro u v w huv hw
    rw [SimpleGraph.top_adj] at huv
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨a, b, c, hu, hv, hoff⟩ := exists_lineFun_edge u v huv
    exact notMem_segment_of_ne_zero (hoff w hne.1 hne.2) hu hv hw
  · intro a b c d hab hcd hne z ⟨hz1, hz2⟩
    rw [SimpleGraph.top_adj] at hab hcd
    by_cases h : a = c ∨ a = d ∨ b = c ∨ b = d
    · rcases h with rfl | rfl | rfl | rfl
      · have hbd : b ≠ d := fun h ↦ hne (by rw [h])
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inl rfl) hab.symm hbd hz1 hz2).symm⟩
        simp
      · have hbc : b ≠ c := fun h ↦ hne (by rw [h]; exact Sym2.eq_swap)
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inr rfl) hbc hab.symm hz1 hz2).symm⟩
        simp
      · rw [segment_symm] at hz1
        have had : a ≠ d := fun h ↦ hne (by rw [h]; exact Sym2.eq_swap)
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inl rfl) hab had hz1 hz2).symm⟩
        simp
      · rw [segment_symm] at hz1
        have hac : a ≠ c := fun h ↦ hne (by rw [h])
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inr rfl) hac hab hz1 hz2).symm⟩
        simp
    · simp only [not_or] at h
      obtain ⟨hac, had, hbc, hbd⟩ := h
      exact absurd hz2 (disjoint_left.1 (disjoint_segment_k4Pos hab hcd hac had hbc hbd) hz1)

end

/-! ### Upstream module `Erdos1019Planar/BipyramidLines.lean` -/

/-!
# Coordinates for the bipyramid drawing

The bipyramid over the `l`-cycle (`l ≥ 3`) has equatorial vertices `0, …, l-1` and two apices.
We draw equatorial vertex `i` at `(i, i²)` on the parabola `y = x²`, the inner apex at
`(1, 3/2)` (strictly inside the convex polygon spanned by the equator) and the outer apex at
`(0, -l²)` far below the parabola.  All non-crossing claims follow from the signs of a few
affine functionals at these points, recorded in this file:

* `chordFun i`: the line through `(i, i²)` and `(i+1, (i+1)²)`;
* `longFun l`: the line through `(0, 0)` and `(l-1, (l-1)²)`;
* `tangentFun i`: the tangent to the parabola at `(i, i²)`;
* `innerSpokeFun i`: the line through the inner apex and `(i, i²)`;
* `outerSpokeFun l i`: the line through the outer apex and `(i, i²)`.
-/

noncomputable section

namespace Bipyramid

/-- Equatorial vertex `i`, on the parabola `y = x²`. -/
def equator (i : ℕ) : ℝ × ℝ :=
  ((i : ℝ), (i : ℝ) ^ 2)

/-- The inner apex `(1, 3/2)`. -/
def innerApex : ℝ × ℝ :=
  (1, 3 / 2)

/-- The outer apex `(0, -l²)`. -/
def outerApex (l : ℕ) : ℝ × ℝ :=
  (0, -((l : ℝ) ^ 2))

/-- Positions of the vertices of the bipyramid `bipyramidGraph l` on `Fin l ⊕ Bool`:
equatorial vertices on the parabola, `inr false` the inner apex, `inr true` the outer apex. -/
def pos (l : ℕ) : Fin l ⊕ Bool → ℝ × ℝ
  | Sum.inl i => equator i
  | Sum.inr false => innerApex
  | Sum.inr true => outerApex l

/-- `y - (2i+1) x + i(i+1)`: vanishes at `(i, i²)` and `(i+1, (i+1)²)`. -/
abbrev chordFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun (-(2 * (i : ℝ) + 1)) 1 ((i : ℝ) * ((i : ℝ) + 1))

/-- `(l-1) x - y`: vanishes at `(0, 0)` and `(l-1, (l-1)²)`. -/
abbrev longFun (l : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((l : ℝ) - 1) (-1) 0

/-- `y - 2i x + i²`: the tangent line to the parabola at `(i, i²)`. -/
abbrev tangentFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun (-(2 * (i : ℝ))) 1 ((i : ℝ) ^ 2)

/-- The line through the inner apex `(1, 3/2)` and `(i, i²)`. -/
abbrev innerSpokeFun (i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((i : ℝ) ^ 2 - 3 / 2) (-((i : ℝ) - 1)) (-(i : ℝ) ^ 2 + 3 / 2 * (i : ℝ))

/-- The line through the outer apex `(0, -l²)` and `(i, i²)`. -/
abbrev outerSpokeFun (l i : ℕ) : ℝ × ℝ → ℝ :=
  lineFun ((i : ℝ) ^ 2 + (l : ℝ) ^ 2) (-(i : ℝ)) (-((i : ℝ) * (l : ℝ) ^ 2))

/-- The vertex positions are pairwise distinct. -/
theorem pos_injective (l : ℕ) (hl : 1 ≤ l) : Function.Injective (pos l) := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  intro x y hxy
  rcases x with i | b <;> rcases y with j | c
  · simp only [pos, equator, Prod.mk.injEq] at hxy
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hxy.1))
  · exfalso
    cases c <;> simp only [pos, equator, innerApex, outerApex, Prod.mk.injEq] at hxy
    · obtain ⟨h1, h2⟩ := hxy
      rw [h1] at h2
      norm_num at h2
    · obtain ⟨h1, h2⟩ := hxy
      rw [h1] at h2
      nlinarith
  · exfalso
    cases b <;> simp only [pos, equator, innerApex, outerApex, Prod.mk.injEq] at hxy
    · obtain ⟨h1, h2⟩ := hxy
      rw [← h1] at h2
      norm_num at h2
    · obtain ⟨h1, h2⟩ := hxy
      rw [← h1] at h2
      nlinarith
  · cases b <;> cases c <;> simp only [pos, innerApex, outerApex, Prod.mk.injEq] at hxy ⊢
    · norm_num at hxy
    · norm_num at hxy

/-! ### The chord line -/

/-- Value of the chord functional at an equatorial vertex. -/
theorem chordFun_equator (i j : ℕ) :
    chordFun i (equator j) = ((j : ℝ) - i) * ((j : ℝ) - i - 1) := by
  simp only [chordFun, lineFun, equator]
  ring

/-- The chord functional is nonnegative on the equator. -/
theorem chordFun_equator_nonneg (i j : ℕ) : 0 ≤ chordFun i (equator j) := by
  rw [chordFun_equator]
  rcases le_or_gt j i with h | h
  · have h' : (j : ℝ) ≤ i := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

/-- The chord functional is positive on the equator away from its two endpoints. -/
theorem chordFun_equator_pos (i j : ℕ) (hj : j ≠ i) (hj' : j ≠ i + 1) :
    0 < chordFun i (equator j) := by
  rw [chordFun_equator]
  rcases hj.lt_or_gt with h | h
  · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h2 : i + 2 ≤ j := by omega
    have h' : (i : ℝ) + 2 ≤ j := by exact_mod_cast h2
    exact mul_pos (by linarith) (by linarith)

/-- The chord functional vanishes at its first endpoint. -/
theorem chordFun_equator_self (i : ℕ) : chordFun i (equator i) = 0 := by
  simp only [chordFun, lineFun, equator]
  ring

/-- The chord functional vanishes at its second endpoint. -/
theorem chordFun_equator_succ (i : ℕ) : chordFun i (equator (i + 1)) = 0 := by
  simp only [chordFun, lineFun, equator]
  push_cast
  ring

/-- The chord functional is positive at the inner apex. -/
theorem chordFun_innerApex_pos (i : ℕ) : 0 < chordFun i innerApex := by
  simp only [chordFun, lineFun, innerApex]
  nlinarith [sq_nonneg ((i : ℝ) - 1 / 2)]

/-- The chord functional is negative at the outer apex. -/
theorem chordFun_outerApex_neg (i l : ℕ) (h : i + 1 < l) : chordFun i (outerApex l) < 0 := by
  simp only [chordFun, lineFun, outerApex]
  have h' : (i : ℝ) + 1 ≤ l := by exact_mod_cast h.le
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-! ### The long chord line -/

/-- Value of the long chord functional at an equatorial vertex. -/
theorem longFun_equator (l j : ℕ) :
    longFun l (equator j) = (j : ℝ) * ((l : ℝ) - 1 - j) := by
  simp only [longFun, lineFun, equator]
  ring

/-- The long chord functional is nonnegative on the equator. -/
theorem longFun_equator_nonneg (l j : ℕ) (hj : j < l) : 0 ≤ longFun l (equator j) := by
  rw [longFun_equator]
  have h' : (j : ℝ) + 1 ≤ l := by exact_mod_cast hj
  exact mul_nonneg (Nat.cast_nonneg j) (by linarith)

/-- The long chord functional is positive on the equator away from its two endpoints. -/
theorem longFun_equator_pos (l j : ℕ) (hj : j < l) (h0 : j ≠ 0) (h1 : j + 1 ≠ l) :
    0 < longFun l (equator j) := by
  rw [longFun_equator]
  have h2 : j + 2 ≤ l := by omega
  have h' : (j : ℝ) + 2 ≤ l := by exact_mod_cast h2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
  exact mul_pos hj0 (by linarith)

/-- The long chord functional vanishes at vertex `0`. -/
theorem longFun_equator_zero (l : ℕ) : longFun l (equator 0) = 0 := by
  simp [longFun, lineFun, equator]

/-- The long chord functional vanishes at vertex `l - 1`. -/
theorem longFun_equator_last (l : ℕ) (hl : 1 ≤ l) : longFun l (equator (l - 1)) = 0 := by
  rw [longFun_equator, Nat.cast_pred hl]
  ring

/-- The long chord functional is positive at the inner apex. -/
theorem longFun_innerApex_pos (l : ℕ) (hl : 3 ≤ l) : 0 < longFun l innerApex := by
  simp only [longFun, lineFun, innerApex]
  have h' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  linarith

/-- The long chord functional is positive at the outer apex. -/
theorem longFun_outerApex_pos (l : ℕ) (hl : 1 ≤ l) : 0 < longFun l (outerApex l) := by
  simp only [longFun, lineFun, outerApex]
  have h' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

/-! ### The tangent line -/

/-- Value of the tangent functional at an equatorial vertex. -/
theorem tangentFun_equator (i j : ℕ) : tangentFun i (equator j) = ((j : ℝ) - i) ^ 2 := by
  simp only [tangentFun, lineFun, equator]
  ring

/-- The tangent functional vanishes at its point of tangency. -/
theorem tangentFun_equator_self (i : ℕ) : tangentFun i (equator i) = 0 := by
  simp only [tangentFun, lineFun, equator]
  ring

/-- The tangent functional is positive at every other equatorial vertex. -/
theorem tangentFun_equator_pos (i j : ℕ) (h : j ≠ i) : 0 < tangentFun i (equator j) := by
  rw [tangentFun_equator]
  have h' : (j : ℝ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  positivity

/-- The tangent functional is positive at the inner apex. -/
theorem tangentFun_innerApex_pos (i : ℕ) : 0 < tangentFun i innerApex := by
  simp only [tangentFun, lineFun, innerApex]
  nlinarith [sq_nonneg ((i : ℝ) - 1)]

/-- The tangent functional is negative at the outer apex. -/
theorem tangentFun_outerApex_neg (i l : ℕ) (h : i < l) : tangentFun i (outerApex l) < 0 := by
  simp only [tangentFun, lineFun, outerApex]
  have h' : (i : ℝ) < l := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-! ### The inner spoke line -/

/-- The inner spoke functional vanishes at the inner apex. -/
theorem innerSpokeFun_innerApex (i : ℕ) : innerSpokeFun i innerApex = 0 := by
  simp only [innerSpokeFun, lineFun, innerApex]
  ring

/-- The inner spoke functional vanishes at its equatorial endpoint. -/
theorem innerSpokeFun_equator_self (i : ℕ) : innerSpokeFun i (equator i) = 0 := by
  simp only [innerSpokeFun, lineFun, equator]
  ring

/-- Value of the inner spoke functional at an equatorial vertex. -/
theorem innerSpokeFun_equator (i j : ℕ) :
    innerSpokeFun i (equator j) = ((i : ℝ) - j) * (((i : ℝ) - 1) * ((j : ℝ) - 1) + 1 / 2) := by
  simp only [innerSpokeFun, lineFun, equator]
  ring

/-- The inner spoke functional does not vanish at any other equatorial vertex. -/
theorem innerSpokeFun_equator_ne_zero (i j : ℕ) (h : j ≠ i) :
    innerSpokeFun i (equator j) ≠ 0 := by
  rw [innerSpokeFun_equator]
  have h1 : (i : ℝ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.symm)
  have h2 : ((i : ℝ) - 1) * ((j : ℝ) - 1) + 1 / 2 ≠ 0 := by
    intro hc
    have h3 : ((2 * (((i : ℤ) - 1) * ((j : ℤ) - 1)) + 1 : ℤ) : ℝ) = 0 := by
      push_cast
      linarith
    have h4 : (2 * (((i : ℤ) - 1) * ((j : ℤ) - 1)) + 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  exact mul_ne_zero h1 h2

/-! ### The outer spoke line -/

/-- The outer spoke functional vanishes at the outer apex. -/
theorem outerSpokeFun_outerApex (l i : ℕ) : outerSpokeFun l i (outerApex l) = 0 := by
  simp only [outerSpokeFun, lineFun, outerApex]
  ring

/-- The outer spoke functional vanishes at its equatorial endpoint. -/
theorem outerSpokeFun_equator_self (l i : ℕ) : outerSpokeFun l i (equator i) = 0 := by
  simp only [outerSpokeFun, lineFun, equator]
  ring

/-- Value of the outer spoke functional at an equatorial vertex. -/
theorem outerSpokeFun_equator (l i j : ℕ) :
    outerSpokeFun l i (equator j) = ((j : ℝ) - i) * ((l : ℝ) ^ 2 - (i : ℝ) * j) := by
  simp only [outerSpokeFun, lineFun, equator]
  ring

/-- The outer spoke functional is positive at equatorial vertices to the right of `i`. -/
theorem outerSpokeFun_equator_pos (l i j : ℕ) (hi : i < l) (hj : j < l) (h : i < j) :
    0 < outerSpokeFun l i (equator j) := by
  rw [outerSpokeFun_equator]
  have hi' : (i : ℝ) < l := by exact_mod_cast hi
  have hj' : (j : ℝ) < l := by exact_mod_cast hj
  have h' : (i : ℝ) < j := by exact_mod_cast h
  have hij : (i : ℝ) * j < (l : ℝ) ^ 2 := by
    rw [sq]
    exact mul_lt_mul'' hi' hj' (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  exact mul_pos (by linarith) (by linarith)

/-- The outer spoke functional is negative at equatorial vertices to the left of `i`. -/
theorem outerSpokeFun_equator_neg (l i j : ℕ) (hi : i < l) (hj : j < l) (h : j < i) :
    outerSpokeFun l i (equator j) < 0 := by
  rw [outerSpokeFun_equator]
  have hi' : (i : ℝ) < l := by exact_mod_cast hi
  have hj' : (j : ℝ) < l := by exact_mod_cast hj
  have h' : (j : ℝ) < i := by exact_mod_cast h
  have hij : (i : ℝ) * j < (l : ℝ) ^ 2 := by
    rw [sq]
    exact mul_lt_mul'' hi' hj' (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

end Bipyramid

end

/-! ### Upstream module `Erdos1019Planar/BipyramidChords.lean` -/

section
/-!
# Chords of the bipyramid drawing

The equatorial edges of `bipyramidGraph l` are the edges of `cycleGraph l`: the short chords
`{i, i+1}` (`i + 1 < l`) and the long chord `{l-1, 0}`.  In the drawing of `BipyramidLines`
every short chord lies on the line `chordFun i = 0`, with all other vertices strictly above it
except the outer apex, which is strictly below; the long chord lies on `longFun l = 0` with all
other vertices strictly on one side.  Hence no vertex lies on a non-incident chord and two
distinct chords meet only in a common endpoint.
-/

open _root_.Set
namespace Bipyramid

/-- Adjacent vertices of `cycleGraph l` differ by one, cyclically. -/
private theorem cycle_adj_cases {l : ℕ} {i j : Fin l} (h : (SimpleGraph.cycleGraph l).Adj i j) :
    (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = l) ∨
      ((j : ℕ) = 0 ∧ (i : ℕ) + 1 = l) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [SimpleGraph.cycleGraph_adj'] at h
  rcases h with h | h
  · rcases le_or_gt j i with hle | hlt
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.2 hlt] at h
      have := Fin.lt_def.1 hlt
      omega
  · rcases le_or_gt i j with hle | hlt
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.2 hlt] at h
      have := Fin.lt_def.1 hlt
      omega

/-- The short chord `{i, i+1}` lies on `chordFun i = 0`, and no other vertex does. -/
private theorem short_chord_zero {l : ℕ} {i j : Fin l} (hij : (j : ℕ) = i + 1) :
    chordFun i (pos l (Sum.inl i)) = 0 ∧ chordFun i (pos l (Sum.inl j)) = 0 ∧
      ∀ w : Fin l ⊕ Bool, chordFun i (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j := by
  have hj := j.isLt
  refine ⟨chordFun_equator_self i, ?_, ?_⟩
  · show chordFun i (equator j) = 0
    rw [hij]
    exact chordFun_equator_succ i
  · rintro (n | b) hn
    · by_contra hne
      rw [not_or] at hne
      refine (chordFun_equator_pos i n ?_ ?_).ne' hn
      · exact fun h ↦ hne.1 (congrArg Sum.inl (Fin.ext h))
      · exact fun h ↦ hne.2 (congrArg Sum.inl (Fin.ext (by omega)))
    · cases b
      · exact absurd hn (chordFun_innerApex_pos i).ne'
      · exact absurd hn (chordFun_outerApex_neg i l (by omega)).ne

/-- The long chord `{0, l-1}` lies on `longFun l = 0`, and no other vertex does. -/
private theorem long_chord_zero {l : ℕ} (hl : 3 ≤ l) {i j : Fin l} (hi : (i : ℕ) = 0)
    (hj : (j : ℕ) + 1 = l) :
    longFun l (pos l (Sum.inl i)) = 0 ∧ longFun l (pos l (Sum.inl j)) = 0 ∧
      ∀ w : Fin l ⊕ Bool, longFun l (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j := by
  refine ⟨?_, ?_, ?_⟩
  · show longFun l (equator i) = 0
    rw [hi]
    exact longFun_equator_zero l
  · show longFun l (equator j) = 0
    rw [show (j : ℕ) = l - 1 by omega]
    exact longFun_equator_last l (by omega)
  · rintro (n | b) hn
    · by_contra hne
      rw [not_or] at hne
      refine (longFun_equator_pos l n n.isLt ?_ ?_).ne' hn
      · exact fun h ↦ hne.1 (congrArg Sum.inl (Fin.ext (by omega)))
      · exact fun h ↦ hne.2 (congrArg Sum.inl (Fin.ext (by omega)))
    · cases b
      · exact absurd hn (longFun_innerApex_pos l hl).ne'
      · exact absurd hn (longFun_outerApex_pos l (by omega)).ne'

/-- If a functional vanishes on the chord `{i, j}`, and `{k, m}` has `k` a common endpoint
while the functional is positive at `m`, the chords meet only in `pos l (inl k)`. -/
private theorem chord_inter_of_shared {l : ℕ} {a b c : ℝ} {i j k m : Fin l}
    (hi : lineFun a b c (pos l (Sum.inl i)) = 0) (hj : lineFun a b c (pos l (Sum.inl j)) = 0)
    (hk : k = i ∨ k = j) (hm : 0 < lineFun a b c (pos l (Sum.inl m))) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have hk0 : lineFun a b c (pos l (Sum.inl k)) = 0 := by
    rcases hk with h | h <;> rw [h] <;> assumption
  rw [Set.inter_comm]
  refine (segment_inter_segment_subset_singleton hk0 hm hi.le hj.le).trans ?_
  rw [Set.singleton_subset_iff]
  refine ⟨Sum.inl k, ⟨?_, Sym2.mem_mk_left _ _⟩, rfl⟩
  exact Sym2.mem_iff.2 (hk.imp (congrArg Sum.inl) (congrArg Sum.inl))

/-- Core of `chord_inter_chord`: a functional vanishing exactly on the endpoints of the chord
`{i, j}` among all vertices, and nonnegative on the equator, separates this chord from every
other chord `{k, m}` except at common endpoints. -/
private theorem chord_inter_of_lineFun {l : ℕ} {a b c : ℝ} {i j k m : Fin l}
    (hi : lineFun a b c (pos l (Sum.inl i)) = 0) (hj : lineFun a b c (pos l (Sum.inl j)) = 0)
    (hnn : ∀ n : Fin l, 0 ≤ lineFun a b c (pos l (Sum.inl n)))
    (hzero : ∀ w : Fin l ⊕ Bool, lineFun a b c (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j)
    (hkm : k ≠ m) (hne : s(i, j) ≠ s(k, m)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have key : ∀ n : Fin l, ¬(n = i ∨ n = j) → 0 < lineFun a b c (pos l (Sum.inl n)) :=
    fun n hn ↦ lt_of_le_of_ne (hnn n)
      fun h ↦ hn ((hzero _ h.symm).imp Sum.inl.inj Sum.inl.inj)
  by_cases hk : k = i ∨ k = j
  · by_cases hm : m = i ∨ m = j
    · exfalso
      apply hne
      rcases hk with rfl | rfl <;> rcases hm with rfl | rfl
      · exact absurd rfl hkm
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hkm
    · exact chord_inter_of_shared hi hj hk (key m hm)
  · by_cases hm : m = i ∨ m = j
    · rw [segment_symm ℝ (pos l (Sum.inl k)), Sym2.eq_swap (a := Sum.inl k)]
      exact chord_inter_of_shared hi hj hm (key k hk)
    · have hd := segment_disjoint_of_pos_of_nonpos (key k hk) (key m hm) hi.le hj.le
      rw [Set.inter_comm, Set.disjoint_iff_inter_eq_empty.1 hd]
      exact Set.empty_subset _

/-- A vertex on the segment of an equatorial edge is one of its endpoints. -/
theorem vertex_mem_chord (l : ℕ) (hl : 3 ≤ l) (i j : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (w : Fin l ⊕ Bool)
    (hw : pos l w ∈ segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j))) :
    w = Sum.inl i ∨ w = Sum.inl j := by
  rcases cycle_adj_cases hij with h | h | h | h
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    exact h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    rw [segment_symm] at hw
    exact (h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)).symm
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    exact h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    rw [segment_symm] at hw
    exact (h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)).symm

/-- Two distinct equatorial edges meet only in positions of common endpoints. -/
theorem chord_inter_chord (l : ℕ) (hl : 3 ≤ l) (i j k m : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (hkm : (SimpleGraph.cycleGraph l).Adj k m)
    (hne : s(i, j) ≠ s(k, m)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have hne' : s(j, i) ≠ s(k, m) := by rwa [Sym2.eq_swap (a := j)]
  rcases cycle_adj_cases hij with h | h | h | h
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ chordFun_equator_nonneg _ _) h3 hkm.ne hne
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    rw [segment_symm ℝ (pos l (Sum.inl i)), Sym2.eq_swap (a := Sum.inl i)]
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ chordFun_equator_nonneg _ _) h3 hkm.ne hne'
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ longFun_equator_nonneg _ _ n.isLt) h3 hkm.ne hne
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    rw [segment_symm ℝ (pos l (Sum.inl i)), Sym2.eq_swap (a := Sum.inl i)]
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ longFun_equator_nonneg _ _ n.isLt) h3 hkm.ne hne'

end Bipyramid

end

/-! ### Upstream module `Erdos1019Planar/BipyramidSpokes.lean` -/

section
/-!
# Spokes of the bipyramid drawing

The spokes of `bipyramidGraph l` join an equatorial vertex `i` to an apex.  In the drawing of
`BipyramidLines` the inner spoke to `(i, i²)` lies in the closed region `tangentFun i ≥ 0`,
touching the tangent line only at `(i, i²)`, and on the line `innerSpokeFun i = 0`; the outer
spoke lies in `tangentFun i ≤ 0`, touching only at `(i, i²)`, and on `outerSpokeFun l i = 0`.
Chords lie on `chordFun`/`longFun` lines on which the apices have strict signs.  These signs
give every required non-crossing statement involving a spoke.
-/

open _root_.Set
namespace Bipyramid

/-! ### Sign-flipped separation lemmas -/

/-- Negating the coefficients negates the affine functional. -/
private theorem lineFun_neg (a b c : ℝ) (z : ℝ × ℝ) :
    lineFun (-a) (-b) (-c) z = -lineFun a b c z := by
  simp only [lineFun]
  ring

/-- Two segments are disjoint when a functional is negative on one and nonnegative on the
other. -/
private theorem segment_disjoint_of_neg_of_nonneg {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p < 0) (hq : lineFun a b c q < 0) (hr : 0 ≤ lineFun a b c r)
    (hs : 0 ≤ lineFun a b c s) : Disjoint (segment ℝ p q) (segment ℝ r s) :=
  segment_disjoint_of_pos_of_nonpos (a := -a) (b := -b) (c := -c)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)

/-- If a functional vanishes at `p`, is negative at `q`, and is nonnegative on `[r, s]`, then
`[p, q]` meets `[r, s]` at most in `p`. -/
private theorem segment_inter_segment_subset_singleton_of_neg {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q < 0) (hr : 0 ≤ lineFun a b c r)
    (hs : 0 ≤ lineFun a b c s) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} :=
  segment_inter_segment_subset_singleton (a := -a) (b := -b) (c := -c)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)

/-! ### From separation statements to the image form -/

/-- Disjoint segments trivially meet inside any image. -/
private theorem subset_image_of_disjoint {l : ℕ} {S T : Set (ℝ × ℝ)} {P : Set (Fin l ⊕ Bool)}
    (h : Disjoint S T) : S ∩ T ⊆ pos l '' P := by
  rw [Set.disjoint_iff_inter_eq_empty.1 h]
  exact Set.empty_subset _

/-- An intersection contained in the position of a vertex of `P` lies in the image of `P`. -/
private theorem subset_image_of_subset_singleton {l : ℕ} {S T : Set (ℝ × ℝ)}
    {P : Set (Fin l ⊕ Bool)} {w : Fin l ⊕ Bool} (hw : w ∈ P) (h : S ∩ T ⊆ {pos l w}) :
    S ∩ T ⊆ pos l '' P :=
  h.trans (Set.singleton_subset_iff.2 ⟨w, hw, rfl⟩)

/-! ### Vertices on spokes -/

/-- A vertex on the segment of a spoke is one of its endpoints. -/
theorem vertex_mem_spoke (l : ℕ) (hl : 3 ≤ l) (i : Fin l) (b : Bool) (w : Fin l ⊕ Bool)
    (hw : pos l w ∈ segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr b))) :
    w = Sum.inl i ∨ w = Sum.inr b := by
  have _ := hl
  rcases w with j | c
  · by_cases hji : j = i
    · exact Or.inl (congrArg Sum.inl hji)
    exfalso
    have hji' : (j : ℕ) ≠ i := Fin.val_ne_of_ne hji
    cases b
    · exact notMem_segment_of_ne_zero (innerSpokeFun_equator_ne_zero i j hji')
        (innerSpokeFun_equator_self i) (innerSpokeFun_innerApex i) hw
    · exact notMem_segment_of_pos_of_nonpos (tangentFun_equator_pos i j hji')
        (tangentFun_equator_self i).le (tangentFun_outerApex_neg i l i.isLt).le hw
  · cases b <;> cases c
    · exact Or.inr rfl
    · exact absurd (lineFun_nonneg_of_mem_segment (tangentFun_equator_self i).ge
        (tangentFun_innerApex_pos i).le hw) (not_le.2 (tangentFun_outerApex_neg i l i.isLt))
    · exact absurd (lineFun_nonpos_of_mem_segment (tangentFun_equator_self i).le
        (tangentFun_outerApex_neg i l i.isLt).le hw) (not_le.2 (tangentFun_innerApex_pos i))
    · exact Or.inr rfl

/-! ### Chords against spokes -/

/-- Adjacency in the cycle graph, in terms of the underlying naturals. -/
private theorem cycle_adj_cases_v1 {l : ℕ} {i j : Fin l} (h : (SimpleGraph.cycleGraph l).Adj i j) :
    (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = l) ∨
      ((j : ℕ) = 0 ∧ (i : ℕ) + 1 = l) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub] at h
  rcases h with h | h
  · rcases lt_or_ge (l - (j : ℕ) + i) l with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rcases lt_or_ge (l - (i : ℕ) + j) l with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- A chord `{i, j}` on the zero set of a functional that is positive at the apex, and a spoke
from `k` to that apex: if the functional is positive at `equator k` whenever `k ∉ {i, j}`,
the two segments meet only in positions of common endpoints. -/
private theorem chord_inter_spoke_of_fun (l : ℕ) (i j k : Fin l) (b : Bool) {a₁ a₂ a₃ : ℝ}
    (hi : lineFun a₁ a₂ a₃ (equator i) = 0) (hj : lineFun a₁ a₂ a₃ (equator j) = 0)
    (hb : 0 < lineFun a₁ a₂ a₃ (pos l (Sum.inr b)))
    (hk : k ≠ i → k ≠ j → 0 < lineFun a₁ a₂ a₃ (equator k)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  by_cases hki : k = i
  · subst hki
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton hi hb hi.le hj.le
  by_cases hkj : k = j
  · subst hkj
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton hj hb hi.le hj.le
  · exact subset_image_of_disjoint
      (segment_disjoint_of_pos_of_nonpos (hk hki hkj) hb hi.le hj.le).symm

/-- The short chord `{i, i+1}` against a spoke. -/
private theorem chord_inter_spoke_succ (l : ℕ) (i j k : Fin l) (b : Bool)
    (hj : (j : ℕ) = i + 1) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  have hkl := k.isLt
  have hil := i.isLt
  have hjl := j.isLt
  cases b
  · refine chord_inter_spoke_of_fun l i j k false (chordFun_equator_self i) ?_
      (chordFun_innerApex_pos i) ?_
    · rw [hj]
      exact chordFun_equator_succ i
    · intro hki hkj
      exact chordFun_equator_pos i k (Fin.val_ne_of_ne hki) (hj ▸ Fin.val_ne_of_ne hkj)
  · by_cases hki : k = i
    · subst hki
      refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
      exact segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_equator_self l _)
        (outerSpokeFun_equator_pos l _ _ (Fin.isLt _) (Fin.isLt _) (by omega)).ne'
        (outerSpokeFun_equator_self l _) (outerSpokeFun_outerApex l _)
    by_cases hkj : k = j
    · subst hkj
      refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩ ?_
      rw [segment_symm ℝ (pos l (Sum.inl i))]
      exact segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_equator_self l _)
        (outerSpokeFun_equator_neg l _ _ (Fin.isLt _) (Fin.isLt _) (by omega)).ne
        (outerSpokeFun_equator_self l _) (outerSpokeFun_outerApex l _)
    have hki' : (k : ℕ) ≠ i := Fin.val_ne_of_ne hki
    have hkj' : (k : ℕ) ≠ j := Fin.val_ne_of_ne hkj
    refine subset_image_of_disjoint ?_
    rcases lt_or_gt_of_ne hki' with h | h
    · exact segment_disjoint_of_pos_of_nonpos (outerSpokeFun_equator_pos l k i hkl hil h)
        (outerSpokeFun_equator_pos l k j hkl hjl (by omega)) (outerSpokeFun_equator_self l k).le
        (outerSpokeFun_outerApex l k).le
    · exact segment_disjoint_of_neg_of_nonneg (outerSpokeFun_equator_neg l k i hkl hil h)
        (outerSpokeFun_equator_neg l k j hkl hjl (by omega)) (outerSpokeFun_equator_self l k).ge
        (outerSpokeFun_outerApex l k).ge

/-- The long chord `{0, l-1}` against a spoke. -/
private theorem chord_inter_spoke_long (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hi : (i : ℕ) = 0) (hj : (j : ℕ) + 1 = l) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  have hi0 : longFun l (equator i) = 0 := by
    rw [hi]
    exact longFun_equator_zero l
  have hj0 : longFun l (equator j) = 0 := by
    have hj' : (j : ℕ) = l - 1 := by omega
    rw [hj']
    exact longFun_equator_last l (by omega)
  have hk : k ≠ i → k ≠ j → 0 < longFun l (equator k) := fun hki hkj ↦
    longFun_equator_pos l k k.isLt (fun h ↦ Fin.val_ne_of_ne hki (h.trans hi.symm))
      (fun h ↦ Fin.val_ne_of_ne hkj (by omega))
  cases b
  · exact chord_inter_spoke_of_fun l i j k false hi0 hj0 (longFun_innerApex_pos l hl) hk
  · exact chord_inter_spoke_of_fun l i j k true hi0 hj0 (longFun_outerApex_pos l (by omega)) hk

/-- An equatorial edge and a spoke meet only in positions of common endpoints. -/
theorem chord_inter_spoke (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  rcases cycle_adj_cases_v1 hij with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact chord_inter_spoke_succ l i j k b h
  · have := chord_inter_spoke_succ l j i k b h
    rwa [segment_symm ℝ (pos l (Sum.inl j)), Sym2.eq_swap (a := Sum.inl j)] at this
  · exact chord_inter_spoke_long l hl i j k b h1 h2
  · have := chord_inter_spoke_long l hl j i k b h1 h2
    rwa [segment_symm ℝ (pos l (Sum.inl j)), Sym2.eq_swap (a := Sum.inl j)] at this

/-! ### Spokes against spokes -/

/-- An inner spoke and an outer spoke meet only in positions of common endpoints. -/
private theorem inner_inter_outer (l : ℕ) (i k : Fin l) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr false)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr true)) ⊆
      pos l '' {w : Fin l ⊕ Bool |
        w ∈ s(Sum.inl i, Sum.inr false) ∧ w ∈ s(Sum.inl k, Sum.inr true)} := by
  have hB := tangentFun_outerApex_neg k l k.isLt
  have hA := tangentFun_innerApex_pos k
  by_cases hki : k = i
  · subst hki
    have hv : 0 ≤ tangentFun k (equator k) := (tangentFun_equator_self k).ge
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton_of_neg (tangentFun_equator_self k) hB hv hA.le
  · exact subset_image_of_disjoint (segment_disjoint_of_pos_of_nonpos
      (tangentFun_equator_pos k i (Fin.val_ne_of_ne (Ne.symm hki))) hA
      (tangentFun_equator_self k).le hB.le)

/-- Two distinct spokes meet only in positions of common endpoints. -/
theorem spoke_inter_spoke (l : ℕ) (hl : 3 ≤ l) (i k : Fin l) (b c : Bool)
    (hne : s(Sum.inl i, Sum.inr b) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inr c)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr b)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr c)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inr b) ∧ w ∈ s(Sum.inl k, Sum.inr c)} := by
  have _ := hl
  cases b <;> cases c
  · have hik : (i : ℕ) ≠ k := fun h ↦ hne (by rw [Fin.ext h])
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩ ?_
    rw [Set.inter_comm, segment_symm ℝ (pos l (Sum.inl k))]
    exact segment_inter_segment_subset_singleton_of_ne_zero (innerSpokeFun_innerApex i)
      (innerSpokeFun_equator_ne_zero i k (Ne.symm hik)) (innerSpokeFun_equator_self i)
      (innerSpokeFun_innerApex i)
  · exact inner_inter_outer l i k
  · have := inner_inter_outer l k i
    rw [Set.inter_comm] at this
    exact this.trans (Set.image_mono fun w hw ↦ ⟨hw.2, hw.1⟩)
  · have hik : (i : ℕ) ≠ k := fun h ↦ hne (by rw [Fin.ext h])
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩ ?_
    rw [Set.inter_comm, segment_symm ℝ (pos l (Sum.inl k))]
    refine segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_outerApex l i) ?_
      (outerSpokeFun_equator_self l i) (outerSpokeFun_outerApex l i)
    rcases lt_or_gt_of_ne hik with h | h
    · exact (outerSpokeFun_equator_pos l i k i.isLt k.isLt h).ne'
    · exact (outerSpokeFun_equator_neg l i k i.isLt k.isLt h).ne

end Bipyramid

end

/-! ### Upstream module `Erdos1019Planar/Bipyramid.lean` -/

section
/-!
# The bipyramid has a straight-line plane drawing

Assembling the chord and spoke lemmas: every edge of `Erdos1019.bipyramidGraph l` is either an
equatorial edge (an edge of `cycleGraph l`) or a spoke, and the segment conditions of
`SimpleGraph.IsStraightLineDrawing` follow by case analysis, using the symmetry of segments and
of unordered pairs.
-/

open _root_.Set
namespace Bipyramid

/-- The crossing condition of `SimpleGraph.IsStraightLineDrawing` for one pair of edges. -/
def CrossOk (l : ℕ) (a b c d : Fin l ⊕ Bool) : Prop :=
  segment ℝ (pos l a) (pos l b) ∩ segment ℝ (pos l c) (pos l d) ⊆
    pos l '' {w : Fin l ⊕ Bool | w ∈ s(a, b) ∧ w ∈ s(c, d)}

theorem CrossOk.swap_left {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l b a c d := by
  unfold CrossOk at h ⊢
  rw [segment_symm, Sym2.eq_swap]
  exact h

theorem CrossOk.swap_right {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l a b d c := by
  unfold CrossOk at h ⊢
  rw [segment_symm ℝ (pos l d), Sym2.eq_swap (a := d)]
  exact h

theorem CrossOk.comm {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l c d a b := by
  unfold CrossOk at h ⊢
  rw [Set.inter_comm]
  refine h.trans (Set.image_mono ?_)
  intro w hw
  exact ⟨hw.2, hw.1⟩

/-- The two apices are not adjacent. -/
theorem not_adj_inr_inr {l : ℕ} {b c : Bool}
    (h : (Erdos1019.bipyramidGraph l).Adj (Sum.inr b) (Sum.inr c)) : False := h

theorem crossOk_chord_chord (l : ℕ) (hl : 3 ≤ l) (i j k m : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (hkm : (SimpleGraph.cycleGraph l).Adj k m)
    (hne : s((Sum.inl i : Fin l ⊕ Bool), Sum.inl j) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inl m)) :
    CrossOk l (Sum.inl i) (Sum.inl j) (Sum.inl k) (Sum.inl m) := by
  refine chord_inter_chord l hl i j k m hij hkm ?_
  intro h
  apply hne
  have := congrArg (Sym2.map (Sum.inl : Fin l → Fin l ⊕ Bool)) h
  simpa using this

theorem crossOk_chord_spoke (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) :
    CrossOk l (Sum.inl i) (Sum.inl j) (Sum.inl k) (Sum.inr b) :=
  chord_inter_spoke l hl i j k b hij

theorem crossOk_spoke_spoke (l : ℕ) (hl : 3 ≤ l) (i k : Fin l) (b c : Bool)
    (hne : s((Sum.inl i : Fin l ⊕ Bool), Sum.inr b) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inr c)) :
    CrossOk l (Sum.inl i) (Sum.inr b) (Sum.inl k) (Sum.inr c) :=
  spoke_inter_spoke l hl i k b c hne

/-- The crossing condition for every pair of distinct edges of the bipyramid. -/
theorem crossOk_of_adj (l : ℕ) (hl : 3 ≤ l) (a b c d : Fin l ⊕ Bool)
    (hab : (Erdos1019.bipyramidGraph l).Adj a b) (hcd : (Erdos1019.bipyramidGraph l).Adj c d)
    (hne : s(a, b) ≠ s(c, d)) : CrossOk l a b c d := by
  rcases a with i | p <;> rcases b with j | q
  · -- first edge is a chord
    rcases c with k | r <;> rcases d with m | s
    · exact crossOk_chord_chord l hl i j k m hab hcd hne
    · exact crossOk_chord_spoke l hl i j k s hab
    · exact (crossOk_chord_spoke l hl i j m r hab).swap_right
    · exact (not_adj_inr_inr hcd).elim
  · -- first edge is a spoke `inl i — inr q`
    rcases c with k | r <;> rcases d with m | s
    · exact (crossOk_chord_spoke l hl k m i q hcd).comm
    · exact crossOk_spoke_spoke l hl i k q s hne
    · refine (crossOk_spoke_spoke l hl i m q r ?_).swap_right
      rwa [Sym2.eq_swap (a := (Sum.inr r : Fin l ⊕ Bool))] at hne
    · exact (not_adj_inr_inr hcd).elim
  · -- first edge is a spoke `inr p — inl j`
    rcases c with k | r <;> rcases d with m | s
    · exact ((crossOk_chord_spoke l hl k m j p hcd).comm).swap_left
    · refine (crossOk_spoke_spoke l hl j k p s ?_).swap_left
      rwa [Sym2.eq_swap (a := (Sum.inr p : Fin l ⊕ Bool))] at hne
    · refine ((crossOk_spoke_spoke l hl j m p r ?_).swap_left).swap_right
      rwa [Sym2.eq_swap (a := (Sum.inr p : Fin l ⊕ Bool)),
        Sym2.eq_swap (a := (Sum.inr r : Fin l ⊕ Bool))] at hne
    · exact (not_adj_inr_inr hcd).elim
  · exact (not_adj_inr_inr hab).elim

/-- No vertex lies on the segment of a non-incident edge of the bipyramid. -/
theorem vertex_mem_of_adj (l : ℕ) (hl : 3 ≤ l) (u v w : Fin l ⊕ Bool)
    (huv : (Erdos1019.bipyramidGraph l).Adj u v)
    (hw : pos l w ∈ segment ℝ (pos l u) (pos l v)) : w = u ∨ w = v := by
  rcases u with i | p <;> rcases v with j | q
  · exact vertex_mem_chord l hl i j huv w hw
  · exact vertex_mem_spoke l hl i q w hw
  · rw [segment_symm] at hw
    exact (vertex_mem_spoke l hl j p w hw).symm
  · exact (not_adj_inr_inr huv).elim

/-- For `l ≥ 3`, the bipyramid over the `l`-cycle has a straight-line plane drawing. -/
theorem bipyramidGraph_isStraightLineDrawing (l : ℕ) (hl : 3 ≤ l) :
    (Erdos1019.bipyramidGraph l).IsStraightLineDrawing (pos l) :=
  ⟨pos_injective l (by omega), fun u v w huv hw ↦ vertex_mem_of_adj l hl u v w huv hw,
    fun a b c d hab hcd hne ↦ crossOk_of_adj l hl a b c d hab hcd hne⟩

end Bipyramid

end

/-! ### Upstream module `Erdos1019Planar/Main.lean` -/

section
/-!
# Erdős Problem #1019 with genuine planarity

Erdős asked whether every graph on `n` vertices with `⌊n²/4⌋ + ⌊(n+1)/2⌋` edges contains a
saturated planar graph on more than three vertices, a saturated planar graph on `m` vertices
being a planar graph with `3m - 6` edges.  Simonovits proved that such a graph contains `K₄`
or a bipyramid `C_l + 2K₁`; that combinatorial theorem is `Erdos1019.erdos_1019_sharp`.  Here
planarity is the topological notion `SimpleGraph.IsPlanar` (a plane drawing by Jordan arcs).
-/

open _root_.Finset
open scoped _root_.SimpleGraph

/-- **Erdős Problem #1019** (Simonovits).  Every graph on `n ≥ 1` vertices with exactly
`⌊n²/4⌋ + ⌊(n+1)/2⌋` edges contains a saturated planar graph on more than three vertices: a
planar graph `H` on `m > 3` vertices with `3m - 6` edges, together with a copy of `H` in `G`.
The edge count of `G` is its `edgeSet.ncard`, so no decidability instance appears on the theorem
face; `n = Fintype.card V ≥ 1`. -/
theorem erdos_1019 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hE : G.edgeSet.ncard = Fintype.card V * Fintype.card V / 4 + (Fintype.card V + 1) / 2) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      H.IsPlanar ∧ 3 < Fintype.card W ∧ H.edgeSet.ncard = 3 * Fintype.card W - 6 ∧ H ⊑ G := by
  classical
  have hE' : #G.edgeFinset = Erdos1019.problemThreshold (Fintype.card V) := by
    rw [← Erdos1019.edgeSet_ncard_eq_card_edgeFinset]
    exact hE
  rcases Erdos1019.erdos_1019_sharp G hE' with h4 | ⟨l, hl, hb⟩
  · refine ⟨Fin 4, inferInstance, ⊤,
      SimpleGraph.IsPlanar.of_isStraightLineDrawing top_four_isStraightLineDrawing, by simp, ?_, h4⟩
    rw [Erdos1019.edgeSet_ncard_eq_card_edgeFinset,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp [Nat.choose]
  · refine ⟨Fin l ⊕ Bool, inferInstance, Erdos1019.bipyramidGraph l,
      SimpleGraph.IsPlanar.of_isStraightLineDrawing
        (Bipyramid.bipyramidGraph_isStraightLineDrawing l hl), ?_, ?_, hb⟩
    · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
      omega
    · rw [Erdos1019.edgeSet_ncard_eq_card_edgeFinset, Erdos1019.bipyramidGraph_card_edges hl]
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
      omega

end

#print axioms erdos_1019
-- 'Erdos1019.erdos_1019' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1019
