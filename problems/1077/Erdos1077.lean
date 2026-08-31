import Mathlib

namespace Erdos1077

/-
# Problem Description

Erdős Problem 1077. Call a graph `D`-balanced if its maximum degree is at most `D` times its minimum degree. For `ε, α > 0` and `D`, `n` sufficiently large, must every `n`-vertex graph with at least `n^(1+α)` edges contain a `D`-balanced subgraph on `m > n^(1-α)` vertices with at least `ε m^(1+α)` edges? `erdos_1077` disproves this.

The inequalities below are strict, matching the original source. Erdős and Simonovits state
this as the first of two open problems on pp. 388--389 of [ErSi70]: "Is it true that for every
`ε` and `α` if `n > n₀(ε,α)` and `d > d₀(ε,α)` every `Gⁿ`, `e(Gⁿ) > n^(1+α)` contains a
`d`-regular subgraph `Gᵐ`, `m > n^(1-α)`, `e(Gᵐ) > ε m^(1+α)`?" All three inequalities are `>`
in the paper; erdosproblems.com paraphrases them as "at least", but the non-strict form
appears in [ErSi70] only in Theorem 1, the proved result, which gives `e(Gᵐ) ≥ (2/5) m^(1+α)`
with `m ≥ n^(α(1-α)/(1+α))`. Their Definition 1, "`Gₙ` is `d`-regular if
`d · min σ(x) ≥ max σ(x)`", is the `IsBalanced` predicate used below. The restriction to
`ε < 1` and `α < 1` only strengthens the disproof, since a counterexample in that range is a
counterexample to the unrestricted question.

The site further notes that the [ErSi70] question "does not really make sense" as literally
stated -- the use of `ε > 0` suggests a small constant while the statement suggests taking `ε`
arbitrarily large -- and discusses what the intended question probably was.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos1077.lean`, a single self-contained file whose only import is
`Mathlib`. It is reproduced here with the file-level comment header, the upstream trust-base
print lines and the trailing `alias` removed, wrapped once in `namespace Erdos1077`, and with the
final theorem named `erdos_1077` (upstream `not_erdos_1077`). The upstream `namespace SimpleGraph` block declares into Mathlib's own namespace and is emitted with explicit `_root_.SimpleGraph.` prefixes. No mathematical content is changed.
-/

/-!
# Erdős Problem 1077

The literal upstream statement has a negative answer.  The complete bipartite
graph `K_{2k, k^4 - 2k}` has more than `(k^4)^(5/4)` edges, while every
nonempty `D`-balanced subgraph has at most `2 * (D + 1) * k` vertices.

The detailed mathematical proof and Leanization map are in `tex/1077.tex`.
-/

section
open SimpleGraph

/-- A finite graph is `D`-balanced when its maximum degree is at most `D`
times its minimum degree.  This is the definition used by the upstream
Formal Conjectures statement. -/
def IsBalanced {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℝ)
    [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end



open Finset Filter SimpleGraph

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The real-power identity used for the edge threshold. -/
lemma rpow_four_five (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 4) ^ (5 / 4 : ℝ) = x ^ 5 := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  norm_num

/-- The real-power identity used for the vertex threshold. -/
lemma rpow_four_three (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 4) ^ (3 / 4 : ℝ) = x ^ 3 := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  norm_num

/-- In a balanced bipartite graph of positive minimum degree, the right part
has at most `D` times as many vertices as the left part. -/
lemma right_part_card_le {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (D : ℝ)
    (L R : Finset V) (hBip : F.IsBipartiteWith L R)
    (hBal : IsBalanced F D) (hmin : 0 < F.minDegree) :
    (R.card : ℝ) ≤ D * (L.card : ℝ) := by
  have hnat : R.card * F.minDegree ≤ L.card * F.maxDegree := by
    calc
      R.card * F.minDegree = ∑ v ∈ R, F.minDegree := by simp
      _ ≤ ∑ v ∈ R, F.degree v := by
        exact Finset.sum_le_sum fun v _ ↦ F.minDegree_le_degree v
      _ = F.edgeFinset.card :=
        SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hBip
      _ = ∑ v ∈ L, F.degree v :=
        (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hBip).symm
      _ ≤ ∑ v ∈ L, F.maxDegree := by
        exact Finset.sum_le_sum fun v _ ↦ F.degree_le_maxDegree v
      _ = L.card * F.maxDegree := by simp
  have hreal :
      (R.card : ℝ) * (F.minDegree : ℝ) ≤
        (L.card : ℝ) * (F.maxDegree : ℝ) := by
    exact_mod_cast hnat
  have hchain :
      (R.card : ℝ) * (F.minDegree : ℝ) ≤
        (D * (L.card : ℝ)) * (F.minDegree : ℝ) := by
    calc
      (R.card : ℝ) * (F.minDegree : ℝ)
          ≤ (L.card : ℝ) * (F.maxDegree : ℝ) := hreal
      _ ≤ (L.card : ℝ) * (D * (F.minDegree : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hBal (by positivity)
      _ = (D * (L.card : ℝ)) * (F.minDegree : ℝ) := by ring
  exact (mul_le_mul_iff_left₀ (mod_cast hmin : (0 : ℝ) < F.minDegree)).mp hchain

/-- The smaller side of the explicit complete bipartite counterexample. -/
def smallSide (k : ℕ) : Finset (Fin (k ^ 4)) :=
  {i | i < 2 * k}

/-- The complete bipartite graph between the first `2k` vertices and their
complement in `Fin (k^4)`. -/
def counterexampleGraph (k : ℕ) : SimpleGraph (Fin (k ^ 4)) :=
  (⊤ : SimpleGraph (Fin (k ^ 4))).between (smallSide k) (smallSide k)ᶜ

lemma two_mul_le_fourth {k : ℕ} (hk : 3 ≤ k) : 2 * k ≤ k ^ 4 := by
  calc
    2 * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
    _ = k ^ 2 := by ring
    _ ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

@[simp]
lemma card_smallSide {k : ℕ} (hk : 3 ≤ k) : (smallSide k).card = 2 * k := by
  rw [smallSide, Fin.card_filter_val_lt, min_eq_right (two_mul_le_fourth hk)]

lemma counterexampleGraph_isBipartiteWith (k : ℕ) :
    (counterexampleGraph k).IsBipartiteWith
      (smallSide k : Set (Fin (k ^ 4))) (smallSide k : Set (Fin (k ^ 4)))ᶜ := by
  rw [counterexampleGraph]
  exact SimpleGraph.between_isBipartiteWith disjoint_compl_right

lemma neighborFinset_counterexampleGraph {k : ℕ} {v : Fin (k ^ 4)}
    (hv : v ∈ smallSide k) :
    (counterexampleGraph k).neighborFinset v = (smallSide k)ᶜ := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, counterexampleGraph,
    SimpleGraph.between_adj]
  simp [hv]
  intro hw hvw
  subst w
  exact hw hv

@[simp]
lemma degree_counterexampleGraph {k : ℕ} {v : Fin (k ^ 4)}
    (hv : v ∈ smallSide k) :
    (counterexampleGraph k).degree v = ((smallSide k)ᶜ).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_counterexampleGraph hv]

lemma card_edgeFinset_counterexampleGraph {k : ℕ} (hk : 3 ≤ k) :
    (counterexampleGraph k).edgeFinset.card = 2 * k * (k ^ 4 - 2 * k) := by
  have hBip : (counterexampleGraph k).IsBipartiteWith
      (↑(smallSide k) : Set (Fin (k ^ 4)))
      (↑((smallSide k)ᶜ) : Set (Fin (k ^ 4))) := by
    simpa only [Finset.coe_compl] using counterexampleGraph_isBipartiteWith k
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (s := smallSide k) (t := (smallSide k)ᶜ) hBip]
  calc
    ∑ v ∈ smallSide k, (counterexampleGraph k).degree v =
        ∑ _v ∈ smallSide k, ((smallSide k)ᶜ).card := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [degree_counterexampleGraph hv]
    _ = 2 * k * (k ^ 4 - 2 * k) := by
      simp [card_smallSide hk, Finset.card_compl]

lemma ncard_edgeSet_counterexampleGraph {k : ℕ} (hk : 3 ≤ k) :
    (counterexampleGraph k).edgeSet.ncard = 2 * k * (k ^ 4 - 2 * k) := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
    card_edgeFinset_counterexampleGraph hk]

lemma four_lt_cube {k : ℕ} (hk : 3 ≤ k) : 4 < k ^ 3 := by
  exact lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hk 3)

/-- The counterexample graph meets the strict edge-density hypothesis for
`α = 1/4`. -/
lemma counterexampleGraph_many_edges {k : ℕ} (hk : 3 ≤ k) :
    ((counterexampleGraph k).edgeSet.ncard : ℝ) >
      ((k ^ 4 : ℕ) : ℝ) ^ (5 / 4 : ℝ) := by
  have hpow : (((k ^ 4 : ℕ) : ℝ) ^ (5 / 4 : ℝ)) = (k : ℝ) ^ 5 := by
    rw [Nat.cast_pow]
    exact rpow_four_five (k : ℝ) (by positivity)
  rw [hpow, ncard_edgeSet_counterexampleGraph hk, Nat.cast_mul,
    Nat.cast_mul, Nat.cast_sub (two_mul_le_fourth hk), Nat.cast_pow]
  have hkpos : (0 : ℝ) < k := by positivity
  have hcube : (4 : ℝ) < (k : ℝ) ^ 3 := by
    exact_mod_cast four_lt_cube hk
  have hfactor : 0 < (k : ℝ) ^ 2 * ((k : ℝ) ^ 3 - 4) :=
    mul_pos (sq_pos_of_pos hkpos) (sub_pos.mpr hcube)
  norm_num only [Nat.cast_ofNat, Nat.cast_mul] at *
  nlinarith

/-- A balanced subgraph containing an edge cannot have minimum degree zero. -/
lemma minDegree_pos_of_balanced_of_edge {V : Type*} [Fintype V]
    {G : SimpleGraph V} (H : G.Subgraph) [DecidableRel H.Adj] (D : ℝ)
    (hBal : IsBalanced H.coe D) (hEdge : H.edgeSet.Nonempty) :
    0 < H.coe.minDegree := by
  obtain ⟨e, he⟩ := hEdge
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : H.Adj u v := by
        simpa only [Subgraph.mem_edgeSet] using he
      let u' : H.verts := ⟨u, H.edge_vert huv⟩
      let v' : H.verts := ⟨v, H.edge_vert huv.symm⟩
      have hadj : H.coe.Adj u' v' := huv
      have hne : H.coe ≠ ⊥ := by
        intro hbot
        rw [hbot] at hadj
        exact hadj
      have hmaxne : H.coe.maxDegree ≠ 0 := by
        intro hzero
        exact hne (SimpleGraph.maxDegree_eq_zero_iff.mp hzero)
      have hmaxpos : 0 < H.coe.maxDegree := Nat.pos_of_ne_zero hmaxne
      rw [IsBalanced] at hBal
      by_contra hmin
      have hminzero : H.coe.minDegree = 0 := Nat.eq_zero_of_not_pos hmin
      rw [hminzero, Nat.cast_zero, mul_zero] at hBal
      exact (not_le_of_gt (mod_cast hmaxpos : (0 : ℝ) < H.coe.maxDegree)) hBal

/-- If a graph is bipartite across `s` and its complement, then every
nonempty `D`-balanced subgraph has at most `(D + 1) * |s|` vertices. -/
lemma balanced_subgraph_vertex_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : Finset V)
    (hBip : G.IsBipartiteWith (s : Set V) (s : Set V)ᶜ)
    (H : G.Subgraph) [DecidableRel H.Adj] (D : ℝ) (hD : 0 ≤ D)
    (hBal : IsBalanced H.coe D) (hEdge : H.edgeSet.Nonempty) :
    (H.verts.ncard : ℝ) ≤ (D + 1) * (s.card : ℝ) := by
  let L : Finset H.verts := Finset.univ.filter fun x ↦ (x : V) ∈ s
  let R : Finset H.verts := Lᶜ
  have hBH : H.coe.IsBipartiteWith
      (↑L : Set H.verts) (↑R : Set H.verts) := by
    simpa [L, R] using hBip.subgraph H
  have hmin : 0 < H.coe.minDegree :=
    minDegree_pos_of_balanced_of_edge H D hBal hEdge
  have hR : (R.card : ℝ) ≤ D * (L.card : ℝ) :=
    right_part_card_le H.coe D L R hBH hBal hmin
  let f : H.verts ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : L.map f ⊆ s := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [L, f] using hy
  have hLnat : L.card ≤ s.card := by
    rw [← Finset.card_map f]
    exact Finset.card_le_card hmap
  have hL : (L.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hLnat
  have hmnat : H.verts.ncard = L.card + R.card := by
    change H.verts.ncard = L.card + Lᶜ.card
    rw [← H.verts.fintypeCard_eq_ncard, Finset.card_compl]
    exact (Nat.add_sub_of_le (Finset.card_le_univ L)).symm
  calc
    (H.verts.ncard : ℝ) = (L.card : ℝ) + (R.card : ℝ) := by
      exact_mod_cast hmnat
    _ ≤ (L.card : ℝ) + D * (L.card : ℝ) := add_le_add_right hR _
    _ = (D + 1) * (L.card : ℝ) := by ring
    _ ≤ (D + 1) * (s.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hL (by linarith)

/-- The literal Formal Conjectures statement of Erdős Problem 1077 is false.
The witnesses `ε = 1/2`, `α = 1/4` and the family
`K_{2k, k^4 - 2k}` refute its eventual assertion. -/
theorem erdos_1077 :
    ¬ ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 →
      ∀ᶠ D in atTop, ∀ᶠ n in atTop,
        ∀ G : SimpleGraph (Fin n),
          G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
            ∃ (H : Subgraph G),
              letI m := H.verts.ncard
              IsBalanced H.coe D ∧
                m > (n : ℝ) ^ (1 - α) ∧
                  H.edgeSet.ncard > ε * m ^ (1 + α) := by
  intro hstatement
  have hfixed := hstatement (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (1 / 4 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.1 hfixed
  obtain ⟨d, hd⟩ := exists_nat_ge D₀
  have hDst := hD₀ (d : ℝ) hd
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hDst
  let k : ℕ := n₀ + d + 4
  have hk : 3 ≤ k := by
    dsimp [k]
    omega
  have hn₀k : n₀ ≤ k := by
    dsimp [k]
    omega
  have hn₀pow : n₀ ≤ k ^ 4 := by
    calc
      n₀ ≤ k := hn₀k
      _ = k ^ 1 := by simp
      _ ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hdkNat : d + 4 ≤ k := by
    dsimp [k]
    omega
  have hdk : (d : ℝ) + 4 ≤ (k : ℝ) := by exact_mod_cast hdkNat
  have hkpos : (0 : ℝ) < k := by positivity
  have hdiff : 0 ≤ (k : ℝ) - ((d : ℝ) + 4) := sub_nonneg.mpr hdk
  have hsum : 0 ≤ (k : ℝ) + ((d : ℝ) + 4) := by positivity
  have hsquares : 0 ≤
      ((k : ℝ) + ((d : ℝ) + 4)) * ((k : ℝ) - ((d : ℝ) + 4)) :=
    mul_nonneg hsum hdiff
  have hquad : 2 * ((d : ℝ) + 1) < (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (d : ℝ)]
  have hsize : ((d : ℝ) + 1) * (2 * (k : ℝ)) < (k : ℝ) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hquad hkpos
    nlinarith
  have hmany : ((counterexampleGraph k).edgeSet.ncard : ℝ) >
      ((k ^ 4 : ℕ) : ℝ) ^ (1 + (1 / 4 : ℝ)) := by
    norm_num
    simpa only [Nat.cast_pow] using counterexampleGraph_many_edges hk
  obtain ⟨H, hBal, hm, hEdges⟩ :=
    hn₀ (k ^ 4) hn₀pow (counterexampleGraph k) hmany
  norm_num at hm hEdges
  have hEdgeReal : 0 < (H.edgeSet.ncard : ℝ) := by
    have hnonneg : 0 ≤ (1 / 2 : ℝ) *
        (H.verts.ncard : ℝ) ^ (5 / 4 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
    exact hnonneg.trans_lt hEdges
  have hEdgeNat : 0 < H.edgeSet.ncard := by exact_mod_cast hEdgeReal
  have hEdge : H.edgeSet.Nonempty :=
    (Set.ncard_pos (s := H.edgeSet)).mp hEdgeNat
  have hbound := balanced_subgraph_vertex_bound (smallSide k)
    (counterexampleGraph_isBipartiteWith k) H (d : ℝ) (by positivity) hBal hEdge
  rw [card_smallSide hk] at hbound
  rw [rpow_four_three (k : ℝ) (by positivity)] at hm
  norm_num only [Nat.cast_ofNat, Nat.cast_mul] at hbound
  linarith

#print axioms erdos_1077
-- 'Erdos1077.erdos_1077' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1077
