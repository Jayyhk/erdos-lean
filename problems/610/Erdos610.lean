import Mathlib

namespace Erdos610

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Formalization of "A note on the clique-transversal number"

This file formalizes the paper resolving Erdős Problem #610, showing that
`T(n) = n - Θ(√(n log n))`, where `T(n)` is the maximum clique-transversal number
over all n-vertex graphs.

Let `τ(G)` denote the minimum size of a set of vertices meeting every maximal clique
of size at least 2 in a graph `G`. The paper proves:

- **Upper bound** (via clique colourings): `τ(G) ≤ n - c√(n log n)` for some `c > 0`
  and all sufficiently large `n`, using the JMRS bound on the clique chromatic number.
- **Lower bound** (from triangle-free graphs): `T(n) ≥ n - C√(n log n)` for some `C > 0`,
  using Kim's Ramsey-theoretic construction.

## References

* P. Erdős, T. Gallai, Zs. Tuza, "Covering the cliques of a graph with vertices" (1992)
* G. Joret, P. Micek, B. Reed, M. Smid, "Tight bounds on the clique chromatic number" (2021)
* J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t" (1995)
-/

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

/-- A finset `S` is a **maximal clique of size ≥ 2** in graph `G`:
it is a clique, has at least 2 vertices, and no strict superset is a clique. -/
def IsMaxClique2 (G : SimpleGraph V) (S : Finset V) : Prop :=
  G.IsClique (↑S) ∧ 2 ≤ S.card ∧ ∀ T : Finset V, S ⊆ T → G.IsClique (↑T) → S = T

/-- A **clique transversal**: a set of vertices that meets every maximal clique of size ≥ 2. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ S, IsMaxClique2 G S → (T ∩ S).Nonempty

/-- A **clique coloring** with `q` colors: no maximal clique of size ≥ 2 is monochromatic. -/
def IsCliqueColoring (G : SimpleGraph V) {q : ℕ} (c : V → Fin q) : Prop :=
  ∀ S, IsMaxClique2 G S → ∃ u ∈ S, ∃ v ∈ S, c u ≠ c v

/-- A **vertex cover**: a set of vertices that meets every edge. -/
def IsVertexCover (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T

/-! ## Section 2: The upper bound via clique colourings -/

/-
The complement of a color class in a clique coloring is a clique transversal.
If `c` is a clique coloring and `Vᵢ = {v | c v = i}`, then `V \ Vᵢ` meets every
maximal clique of size ≥ 2 (since no such clique is monochromatic).
-/
lemma color_class_compl_isTransversal (G : SimpleGraph V) {q : ℕ}
    (c : V → Fin q) (hc : IsCliqueColoring G c) (i : Fin q) :
    IsCliqueTransversal G (univ.filter (fun v => c v ≠ i)) := by
  intro S hS;
  -- Since $S$ is a maximal clique of size ≥ 2, there must be at least two vertices in $S$ with different colors.
  obtain ⟨u, v, huS, hvS, huv⟩ : ∃ u v, u ∈ S ∧ v ∈ S ∧ c u ≠ c v := by
    exact Exists.elim ( hc S hS ) fun u hu => Exists.elim hu.2 fun v hv => ⟨ u, v, hu.1, hv.1, hv.2 ⟩;
  exact if hi : c u = i then ⟨ v, by aesop ⟩ else ⟨ u, by aesop ⟩

/-
The filter complement cardinality identity:
`|{v | c v ≠ i}| = |V| - |{v | c v = i}|`.
-/
lemma card_filter_ne_eq {q : ℕ} (c : V → Fin q) (i : Fin q) :
    (univ.filter (fun v => c v ≠ i)).card =
      Fintype.card V - (univ.filter (fun v => c v = i)).card := by
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num

/-
**Pigeonhole principle** for color classes: if `V` is colored with `q > 0` colors,
some color class has size ≥ `|V| / q`.
-/
lemma exists_large_color_class {q : ℕ} (hq : 0 < q) (c : V → Fin q) :
    ∃ i : Fin q, Fintype.card V / q ≤ (univ.filter (fun v => c v = i)).card := by
  have h_pigeonhole : ∑ i : Fin q, Finset.card (Finset.filter (fun v => c v = i) Finset.univ) = Fintype.card V := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; simp +decide;
  contrapose! h_pigeonhole;
  exact ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hq ⟩, Finset.mem_univ _ ⟩ fun i _ => h_pigeonhole i ) ( by simp +decide [ mul_comm ] ; nlinarith [ Nat.div_mul_le_self ( Fintype.card V ) q ] ) )

/-
**Lemma 2** (Transversal bound from coloring):
If `G` has a clique coloring with `q > 0` colors, then `G` has a clique transversal
of size at most `n - n/q`, where `n = |V|`.
-/
theorem transversal_bound_of_coloring (G : SimpleGraph V) {q : ℕ} (hq : 0 < q)
    (c : V → Fin q) (hc : IsCliqueColoring G c) :
    ∃ T : Finset V, IsCliqueTransversal G T ∧
      T.card ≤ Fintype.card V - Fintype.card V / q := by
  obtain ⟨ i, hi ⟩ := exists_large_color_class hq c;
  refine' ⟨ _, color_class_compl_isTransversal G c hc i, _ ⟩;
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num;
  omega

/-! ## Section 3: The lower bound from triangle-free graphs -/

/-
In a triangle-free graph, if `u` and `v` are adjacent, then `{u, v}` is a maximal
clique of size 2. No third vertex can be adjacent to both (that would create a triangle).
-/
lemma triangleFree_edge_isMaxClique2 (G : SimpleGraph V)
    (hG : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
    IsMaxClique2 G {u, v} := by
  refine' ⟨ _, _, _ ⟩;
  · simp +decide [ *, Set.Pairwise ];
  · rw [ Finset.card_pair huv.ne ];
  · intro T hT₁ hT₂; ext w; simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
    contrapose! hG;
    simp +decide [ SimpleGraph.CliqueFree ];
    use {u, v, w};
    rw [ SimpleGraph.isNClique_iff ];
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop

/-
In a triangle-free graph, every maximal clique of size ≥ 2 is a pair of adjacent vertices.
-/
lemma triangleFree_maxClique2_isEdge (G : SimpleGraph V)
    (hG : G.CliqueFree 3) {S : Finset V} (hS : IsMaxClique2 G S) :
    ∃ u v, u ≠ v ∧ G.Adj u v ∧ S = {u, v} := by
  obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 hS.2.1; use u, v; simp_all +decide ;
  refine' ⟨ hS.1 hu hv huv, _ ⟩;
  refine' Finset.eq_of_subset_of_card_le ( fun w hw => _ ) _;
  · contrapose! hG;
    have := hS.1 hu hw; have := hS.1 hv hw;
    simp_all +decide [ SimpleGraph.CliqueFree ];
    use {u, v, w};
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    exact ⟨ hS.1 hu hv huv, by rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop ⟩;
  · exact Finset.card_le_card ( Finset.insert_subset hu ( Finset.singleton_subset_iff.mpr hv ) )

/-
In a triangle-free graph, every clique transversal is a vertex cover.
-/
lemma triangleFree_transversal_isVertexCover (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) (hT : IsCliqueTransversal G T) :
    IsVertexCover G T := by
  intro u v huv;
  exact hT { u, v } (( triangleFree_edge_isMaxClique2 G hG ) huv) |> fun ⟨ x, hx ⟩ => by aesop;

/-
In a triangle-free graph, every vertex cover is a clique transversal.
-/
lemma triangleFree_vertexCover_isTransversal (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) (hT : IsVertexCover G T) :
    IsCliqueTransversal G T := by
  intro S hS;
  rcases triangleFree_maxClique2_isEdge G hG hS with ⟨ u, v, hne, hadj, rfl ⟩;
  cases hT u v hadj <;> simp_all +decide [ Finset.Nonempty ];
  aesop

/-- **Lemma 4a** (Triangle-free, clique transversal ↔ vertex cover):
In a triangle-free graph, clique transversals and vertex covers coincide. -/
theorem triangleFree_transversal_iff_vertexCover (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) :
    IsCliqueTransversal G T ↔ IsVertexCover G T :=
  ⟨triangleFree_transversal_isVertexCover G hG T,
   triangleFree_vertexCover_isTransversal G hG T⟩

/-
The complement of an independent set is a vertex cover.
-/
lemma indepSet_compl_isVertexCover (G : SimpleGraph V)
    (I : Finset V) (hI : G.IsIndepSet (↑I)) :
    IsVertexCover G (univ \ I) := by
  intro u v huv; by_cases hu : u ∈ I <;> by_cases hv : v ∈ I <;> simp_all +decide [ SimpleGraph.isIndepSet_iff ] ;
  exact hI hu hv ( by aesop ) huv

/-
The complement of a vertex cover is an independent set.
-/
lemma vertexCover_compl_isIndepSet (G : SimpleGraph V)
    (T : Finset V) (hT : IsVertexCover G T) :
    G.IsIndepSet (↑(univ \ T)) := by
  intro v hv w hw hvw; specialize hT v w; aesop;

/-
**Lemma 4b** (Triangle-free, independent set → transversal):
In a triangle-free graph, the complement of any independent set is a clique transversal
of size `n - |I|`.
-/
theorem triangleFree_indep_gives_transversal (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (I : Finset V) (hI : G.IsIndepSet (↑I)) :
    IsCliqueTransversal G (univ \ I) ∧ (univ \ I).card = Fintype.card V - I.card := by
  refine' ⟨ _, _ ⟩;
  · exact triangleFree_vertexCover_isTransversal G hG _ ( indepSet_compl_isVertexCover G I hI );
  · simp +decide [ Finset.card_sdiff ]

/-
**Lemma 4c** (Triangle-free, transversal → independent set):
In a triangle-free graph, the complement of any clique transversal is an independent set.
-/
theorem triangleFree_transversal_gives_indep (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (T : Finset V) (hT : IsCliqueTransversal G T) :
    G.IsIndepSet (↑(univ \ T)) := by
  exact vertexCover_compl_isIndepSet G T ( triangleFree_transversal_isVertexCover G hG T hT )

/-! ## External theorems (stated without proof)

The following two results are deep theorems from the literature.
Their proofs are beyond the scope of this formalization. -/

/-- **Theorem (Joret–Micek–Reed–Smid, 2021)**: There exists `A > 0` such that for all
sufficiently large `n`, every `n`-vertex graph admits a clique coloring with at most
`A √(n / log n)` colors.

Reference: Joret, Micek, Reed, Smid, "Tight Bounds on the Clique Chromatic Number",
Electronic J. Combinatorics 28(3) (2021). -/
axiom jmrs_theorem : ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n),
      ∃ q : ℕ, 0 < q ∧ (∃ c : Fin n → Fin q, IsCliqueColoring G c) ∧
        (q : ℝ) ≤ A * Real.sqrt (↑n / Real.log ↑n)

/-- **Theorem (Kim, 1995)**: There exists `B > 0` such that for all sufficiently large `n`,
there exists a triangle-free graph on `n` vertices where every independent set has size at
most `B √(n log n)`. This follows from Kim's lower bound `R(3,t) ≥ a · t² / log t`.

Reference: J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t",
Random Structures & Algorithms 7(3) (1995), 173–207. -/
axiom kim_theorem : ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ ∀ I : Finset (Fin n), G.IsIndepSet (↑I) →
        (I.card : ℝ) ≤ B * Real.sqrt (↑n * Real.log ↑n)

/-! ## Corollaries and main theorem -/

/-
**Corollary 3** (Upper bound): There exists `c > 0` such that for all sufficiently large `n`,
every `n`-vertex graph has a clique transversal of size at most `n - c√(n log n)`.
This follows from Lemma 2 and the JMRS theorem.

*Proof sketch*: By JMRS, `G` has a clique coloring with `q ≤ A√(n/log n)` colors.
By Lemma 2, `G` has a transversal of size `≤ n - n/q ≤ n - √(n log n)/A`.
-/
theorem upper_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n),
      ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧
        (T.card : ℝ) ≤ ↑n - c * Real.sqrt (↑n * Real.log ↑n) := by
  -- By jmrs_theorem, we obtain A > 0 and N₀ such that for n ≥ N₀, every graph G has a clique coloring with q ≤ A√(n/log n) colors.
  obtain ⟨A, hA_pos, N₀, h_coloring⟩ : ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), ∃ q : ℕ, 0 < q ∧
    (∃ c : Fin n → Fin q, IsCliqueColoring G c) ∧ (q : ℝ) ≤ A * Real.sqrt (n / Real.log n) := by
      exact jmrs_theorem;
  refine' ⟨ 1 / ( 2 * A ), by positivity, N₀ + ⌈ ( 4 * A ^ 2 ) ⌉₊ + 1, fun n hn G => _ ⟩;
  obtain ⟨ q, hq_pos, ⟨ c, hc ⟩, hq_bound ⟩ := h_coloring n ( by linarith ) G
  obtain ⟨ T, hT_transversal, hT_card ⟩ := transversal_bound_of_coloring G hq_pos c hc
  use T
  constructor
  · exact hT_transversal
  ·
    -- We need to show that $(n/q : ℕ) \geq \sqrt{n \log n}/A - 1$.
    have h_floor : (n / q : ℕ) ≥ Real.sqrt (n * Real.log n) / A - 1 := by
      have h_floor : (n / q : ℝ) ≥ Real.sqrt (n * Real.log n) / A := by
        field_simp;
        convert mul_le_mul_of_nonneg_left hq_bound ( Real.sqrt_nonneg ( n * Real.log n ) ) using 1 ; ring;
        rw [ mul_assoc, ← Real.sqrt_mul ( by positivity ) ] ; ring_nf ; norm_num [ show n ≠ 0 by linarith, show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.ceil_pos.mpr <| show 0 < 4 * A ^ 2 by positivity ] ] ; ring;
      exact le_trans ( sub_le_iff_le_add.mpr <| by linarith [ Nat.lt_floor_add_one <| ( n : ℝ ) / q, show ( n : ℝ ) / q ≤ ↑ ( n / q ) + 1 from by rw [ div_le_iff₀ <| Nat.cast_pos.mpr hq_pos ] ; norm_cast ; linarith [ Nat.div_add_mod n q, Nat.mod_lt n hq_pos ] ] ) le_rfl;
    -- We need to show that $1 \leq \sqrt{n \log n}/(2A)$.
    have h_one_le : 1 ≤ Real.sqrt (n * Real.log n) / (2 * A) := by
      rw [ le_div_iff₀ ( by positivity ) ];
      refine' Real.le_sqrt_of_sq_le _;
      nlinarith [ Nat.le_ceil ( 4 * A ^ 2 ), show ( n : ℝ ) ≥ N₀ + ⌈4 * A ^ 2⌉₊ + 1 by exact_mod_cast hn, Real.log_inv ( n : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show ( n : ℝ ) > 0 by norm_cast; linarith ) ), mul_inv_cancel₀ ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
    norm_num +zetaDelta at *;
    refine' le_trans ( Nat.cast_le.mpr hT_card ) _;
    rw [ Nat.cast_sub ( Nat.div_le_self _ _ ) ] ; ring_nf at * ; linarith

/-
**Corollary 5** (Lower bound): There exists `C > 0` such that for all sufficiently large `n`,
there exists an `n`-vertex graph where every clique transversal has size ≥ `n - C√(n log n)`.
This follows from Lemma 4 and Kim's theorem.

*Proof sketch*: By Kim, there exists a triangle-free graph `G` with `α(G) ≤ B√(n log n)`.
For any transversal `T`, `V \ T` is independent (Lemma 4c), so `|V \ T| ≤ B√(n log n)`,
hence `|T| ≥ n - B√(n log n)`.
-/
theorem lower_bound : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∃ G : SimpleGraph (Fin n),
      ∀ T : Finset (Fin n), IsCliqueTransversal G T →
        (n : ℝ) - C * Real.sqrt (↑n * Real.log ↑n) ≤ ↑T.card := by
  obtain ⟨ B, hB₀, N, hN ⟩ := kim_theorem;
  use B, hB₀, N;
  intro n hn; obtain ⟨ G, hG₁, hG₂ ⟩ := hN n hn; use G; intro T hT; have := hG₂ ( Finset.univ \ T ) ; simp_all +decide [ Finset.card_sdiff ] ;
  rw [ Nat.cast_sub ] at this;
  · linarith [ this ( by simpa [ Set.diff_eq ] using triangleFree_transversal_gives_indep G hG₁ T hT ) ];
  · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num )

/-- **Erdős Problem 610** ([EGT92; Er94; Er99], resolved). The clique-transversal
number `τ(G)` is the minimum size of a vertex set meeting every maximal clique of
`G` (excluding isolated vertices). Erdős asked whether every `n`-vertex graph
satisfies `τ(G) ≤ n − c√(n log n)` for some absolute `c > 0`; the answer is
**yes** and the rate is tight. This theorem proves both directions —
`T(n) = n − Θ(√(n log n))` — assuming Joret–Micek–Reed–Smid's clique-coloring
bound (`jmrs_theorem`) and Kim's lower bound on `R(3,t)` (`kim_theorem`). -/
theorem erdos_610 :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n),
        ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧
          (T.card : ℝ) ≤ ↑n - c * Real.sqrt (↑n * Real.log ↑n)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : SimpleGraph (Fin n),
        ∀ T : Finset (Fin n), IsCliqueTransversal G T →
          (n : ℝ) - C * Real.sqrt (↑n * Real.log ↑n) ≤ ↑T.card) :=
  ⟨upper_bound, lower_bound⟩

#print axioms erdos_610
-- 'Erdos610.erdos_610' depends on axioms: [propext, Classical.choice, Erdos610.jmrs_theorem, Erdos610.kim_theorem, Quot.sound]

end Erdos610
