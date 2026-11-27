import Mathlib

namespace Erdos803

/-
# Erdős Problem 803

We call a graph $H$ $D$-balanced (or $D$-almost-regular) if the maximum degree of $H$ is at most
$D$ times the minimum degree of $H$. Is it true that for every $m \geq 1$, if $n$ is sufficiently
large, any graph on $n$ vertices with $\geq n \log n$ edges contains a $O(1)$-balanced subgraph
with $m$ vertices and $\gg m \log m$ edges (where the implied constants are absolute)?

The answer is **no**, by a construction of Alon [Al08]: for every $D \geq 1$ and all large $N$
there is a graph on $N$ vertices with at least $N \log_2 N$ edges in which every $D$-balanced
subgraph on $m$ vertices has at most $18 m (4\sqrt{\log_2 m} + \log_2(64D) + 26)$ edges
(`alon_construction`). `erdos_803` refutes the question as posed, with a balanced subgraph on
exactly $m$ vertices; `not_erdosSimonovitsUniform` refutes the weaker requirement of a subgraph
on at least $m$ vertices. Logarithms are to base $2$, which only strengthens the refutation: the
counterexample graphs have at least $N \log_2 N \geq N \ln N$ edges, and the base of $\log m$ is
absorbed into the implied constant.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000660); the eight
modules forming the closure of `erdos_803` are flattened here in dependency order, with the
final theorem renamed from upstream `not_erdosSimonovitsLiteral`.

Declarations that `erdos_803` does not depend on have been removed.
-/

/-! ### Upstream module `Proof/Defs.lean` -/

section
/-!
# Erdős Problem 803: definitions

A subgraph `H` of a graph `G` is `D`-balanced when every vertex degree inside `H` is at most `D`
times every other vertex degree inside `H` (equivalently, maximum degree ≤ `D` · minimum degree).
Erdős and Simonovits asked whether there are absolute constants `ε > 0` and `D` such that every
graph on `n` vertices with at least `n log₂ n` edges (for `n` large in terms of `m`) contains a
`D`-balanced subgraph on `m` vertices with at least `ε m log₂ m` edges.  Alon (2008) answered
this negatively.  We record the question in its uniform form (a balanced subgraph on at least `m₀`
vertices) and in its literal form (exactly `m` vertices); the literal form implies the uniform one.
-/

open _root_.SimpleGraph

variable {V : Type*}

/-- The degree of `v` inside the subgraph `H` (number of `H`-neighbours). -/
noncomputable def sdeg {G : SimpleGraph V} (H : G.Subgraph) (v : V) : ℕ :=
  (H.neighborSet v).ncard

/-- `H` is `D`-balanced: every degree inside `H` is at most `D` times every other degree. -/
def Balanced {G : SimpleGraph V} (D : ℝ) (H : G.Subgraph) : Prop :=
  ∀ v ∈ H.verts, ∀ w ∈ H.verts, (sdeg H v : ℝ) ≤ D * sdeg H w

theorem Balanced.mono {G : SimpleGraph V} {D D' : ℝ} (h : D ≤ D') {H : G.Subgraph}
    (hH : Balanced D H) : Balanced D' H := by
  intro v hv w hw
  exact (hH v hv w hw).trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))

/-- A balanced subgraph containing a vertex of degree `0` has no edges. -/
theorem Balanced.edgeSet_eq_empty_of_sdeg_eq_zero [Finite V] {G : SimpleGraph V} {D : ℝ}
    {H : G.Subgraph} (hH : Balanced D H) {v : V} (hv : v ∈ H.verts) (h0 : sdeg H v = 0) :
    H.edgeSet = ∅ := by
  have hzero : ∀ w ∈ H.verts, H.neighborSet w = ∅ := by
    intro w hw
    have h1 : (sdeg H w : ℝ) ≤ D * (sdeg H v : ℝ) := hH w hw v hv
    rw [h0, Nat.cast_zero, mul_zero] at h1
    have h2 : sdeg H w = 0 := Nat.le_zero.mp (by exact_mod_cast h1)
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp h2
  rw [Set.eq_empty_iff_forall_notMem]
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    rw [Subgraph.mem_edgeSet]
    intro he
    have hy : y ∈ H.neighborSet x := he
    rw [hzero x (H.edge_vert he)] at hy
    exact hy

/-- Inside a subgraph with finitely many neighbours, `sdeg` agrees with `Subgraph.degree`. -/
private theorem sdeg_eq_degree {G : SimpleGraph V} (H : G.Subgraph) (v : V)
    [Fintype (H.neighborSet v)] : sdeg H v = H.degree v :=
  (Set.ncard_eq_toFinset_card' _).trans (Set.toFinset_card _)

/-- Handshake identity inside a subgraph of a graph on a finite vertex type. -/
theorem sum_sdeg [Fintype V] [DecidableEq V] {G : SimpleGraph V} (H : G.Subgraph) :
    ∑ v ∈ H.verts.toFinite.toFinset, sdeg H v = 2 * H.edgeSet.ncard := by
  classical
  have hfv : Fintype H.verts := Fintype.ofFinite _
  have hdec : DecidableRel H.coe.Adj := Classical.decRel _
  have key := H.coe.sum_degrees_eq_twice_card_edges
  simp only [Subgraph.coe_degree, ← sdeg_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at key
  have himg : H.coe.edgeSet.ncard = H.edgeSet.ncard := by
    rw [← H.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  rw [Finset.sum_subtype (F := hfv) _ (fun x => H.verts.toFinite.mem_toFinset) (sdeg H), key,
    himg]

/-- The uniform form of the Erdős–Simonovits question with constants `ε`, `D`: for every `m₀`,
all sufficiently large graphs with `n log₂ n` edges contain a `D`-balanced subgraph on at least
`m₀` vertices with at least `ε m log₂ m` edges. -/
def ErdosSimonovitsUniform (ε D : ℝ) : Prop :=
  ∀ m₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, m₀ ≤ H.verts.ncard ∧ Balanced D H ∧
        ε * H.verts.ncard * Real.logb 2 H.verts.ncard ≤ H.edgeSet.ncard

/-- The literal form: a `D`-balanced subgraph on exactly `m` vertices. -/
def ErdosSimonovitsLiteral (ε D : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, H.verts.ncard = m ∧ Balanced D H ∧
        ε * m * Real.logb 2 m ≤ H.edgeSet.ncard

theorem ErdosSimonovitsLiteral.uniform {ε D : ℝ} (h : ErdosSimonovitsLiteral ε D) :
    ErdosSimonovitsUniform ε D := by
  intro m₀
  obtain ⟨n₀, hn₀⟩ := h (max m₀ 1) (le_max_right _ _)
  refine ⟨n₀, fun n hn G hG => ?_⟩
  obtain ⟨H, hcard, hbal, hedge⟩ := hn₀ n hn G hG
  refine ⟨H, ?_, hbal, ?_⟩
  · rw [hcard]
    exact le_max_left _ _
  · rw [hcard]
    exact hedge

end

/-! ### Upstream module `Proof/Model.lean` -/

section
/-!
# Alon's random bipartite model

For `n` vertices `A = Fin n` and block indices `i ∈ [4, top n]`, `j ∈ Fin 8` (with
`top n = ⌊log₂ n⌋ / 2`), block `(i, j)` has `bsize n (i, j) = n / 2 ^ i` vertices.  A choice
function `f : Choice n` assigns to every `a ∈ A` and every block one vertex of that block; the
graph `graphOf f` joins `a` to each of its chosen vertices.  Every `a` has degree
`8 * (top n - 3)`, the graph is bipartite between `A` and the blocks, and between a fixed set
`A'` of `A`-vertices and a fixed block there are at most `|A'|` edges.
-/

open _root_.SimpleGraph _root_.Finset

/-- The largest block index: `⌊log₂ n⌋ / 2`. -/
def top (n : ℕ) : ℕ := Nat.log 2 n / 2

/-- Block indices `(i, j)` with `4 ≤ i ≤ top n` and `j < 8`. -/
abbrev BlockIdx (n : ℕ) := ↥(Finset.Icc 4 (top n)) × Fin 8

/-- The size `n / 2 ^ i` of block `(i, j)`. -/
def bsize (n : ℕ) (p : BlockIdx n) : ℕ := n / 2 ^ p.1.1

/-- The block vertices: a block index together with a position in the block. -/
abbrev BVertex (n : ℕ) := Σ p : BlockIdx n, Fin (bsize n p)

/-- The vertex type: `A = Fin n` plus the block vertices. -/
abbrev Vtx (n : ℕ) := Fin n ⊕ BVertex n

/-- A choice function: for every `a ∈ A` and every block, one vertex of that block. -/
abbrev Choice (n : ℕ) := Fin n → (p : BlockIdx n) → Fin (bsize n p)

/-- The adjacency relation of the random graph: `a` is joined to its chosen vertex in each block. -/
def adj {n : ℕ} (f : Choice n) : Vtx n → Vtx n → Prop
  | Sum.inl a, Sum.inr ⟨p, b⟩ => f a p = b
  | Sum.inr ⟨p, b⟩, Sum.inl a => f a p = b
  | _, _ => False

theorem adj_symm {n : ℕ} (f : Choice n) : ∀ ⦃u v : Vtx n⦄, adj f u v → adj f v u := by
  rintro (a | ⟨p, b⟩) (a' | ⟨p', b'⟩) h
  · exact h
  · exact h
  · exact h
  · exact h

theorem adj_irrefl {n : ℕ} (f : Choice n) : ∀ u : Vtx n, ¬ adj f u u := by
  rintro (a | ⟨p, b⟩) h
  · exact h
  · exact h

/-- The graph determined by a choice function. -/
def graphOf {n : ℕ} (f : Choice n) : SimpleGraph (Vtx n) where
  Adj := adj f
  symm := ⟨fun _ _ h => adj_symm f h⟩
  loopless := ⟨fun u h => adj_irrefl f u h⟩

theorem graphOf_adj_inl_inr {n : ℕ} (f : Choice n) (a : Fin n) (p : BlockIdx n)
    (b : Fin (bsize n p)) : (graphOf f).Adj (Sum.inl a) (Sum.inr ⟨p, b⟩) ↔ f a p = b :=
  Iff.rfl

theorem graphOf_not_adj_inl_inl {n : ℕ} (f : Choice n) (a a' : Fin n) :
    ¬ (graphOf f).Adj (Sum.inl a) (Sum.inl a') := fun h ↦ h

theorem graphOf_not_adj_inr_inr {n : ℕ} (f : Choice n) (b b' : BVertex n) :
    ¬ (graphOf f).Adj (Sum.inr b) (Sum.inr b') := by
  obtain ⟨p, c⟩ := b
  obtain ⟨p', c'⟩ := b'
  exact fun h ↦ h

/-- The number of block indices. -/
theorem card_blockIdx (n : ℕ) : Fintype.card (BlockIdx n) = 8 * (top n + 1 - 4) := by
  rw [Fintype.card_prod, Fintype.card_coe, Nat.card_Icc, Fintype.card_fin, mul_comm]

/-- The number of edges of `graphOf f`: every `a ∈ A` contributes one edge per block. -/
theorem edgeSet_ncard_graphOf {n : ℕ} (f : Choice n) :
    (graphOf f).edgeSet.ncard = n * Fintype.card (BlockIdx n) := by
  set g : Fin n × BlockIdx n → Sym2 (Vtx n) :=
    fun ap ↦ s(Sum.inl ap.1, Sum.inr ⟨ap.2, f ap.1 ap.2⟩) with hg
  have hinj : Function.Injective g := by
    rintro ⟨a, p⟩ ⟨a', p'⟩ h
    simp only [hg, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · obtain ⟨h3, -⟩ := h2
      exact Prod.ext h1 h3
    · exact absurd h1 (by simp)
  have hset : (graphOf f).edgeSet = Set.range g := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro h
        rw [SimpleGraph.mem_edgeSet] at h
        rcases u with a | ⟨p, b⟩ <;> rcases v with a' | ⟨p', b'⟩
        · exact absurd h (graphOf_not_adj_inl_inl f a a')
        · rw [graphOf_adj_inl_inr] at h
          subst h
          exact ⟨(a, p'), rfl⟩
        · have h' := h.symm
          rw [graphOf_adj_inl_inr] at h'
          subst h'
          exact ⟨(a', p), Sym2.eq_swap⟩
        · exact absurd h (graphOf_not_adj_inr_inr f ⟨p, b⟩ ⟨p', b'⟩)
    · rintro e ⟨⟨a, p⟩, rfl⟩
      rw [hg, SimpleGraph.mem_edgeSet]
      exact (graphOf_adj_inl_inr f a p _).mpr rfl
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin]

/-- A geometric bound in `ℕ`: `∑_{k < K} ⌊m / 2 ^ k⌋ ≤ 2 * m`. -/
private lemma sum_range_div_two_pow_le (K m : ℕ) :
    ∑ k ∈ Finset.range K, m / 2 ^ k ≤ 2 * m := by
  induction K generalizing m with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ k : ℕ, m / 2 ^ (k + 1) = m / 2 / 2 ^ k := by
      intro k
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    simp only [h, pow_zero, Nat.div_one]
    have := ih (m / 2)
    omega

/-- The tail bound `8 * ∑_{i ∈ [4, T]} ⌊n / 2 ^ i⌋ ≤ n`. -/
private lemma eight_mul_sum_Icc_div_le (n T : ℕ) :
    8 * ∑ i ∈ Finset.Icc 4 T, n / 2 ^ i ≤ n := by
  have h : ∑ i ∈ Finset.Icc 4 T, n / 2 ^ i
      = ∑ k ∈ Finset.range (T + 1 - 4), n / 16 / 2 ^ k := by
    have hIco : Finset.Icc 4 T = Finset.Ico 4 (T + 1) := by
      ext i
      simp
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.div_div_eq_div_mul, pow_add]
    norm_num
  rw [h]
  calc 8 * ∑ k ∈ Finset.range (T + 1 - 4), n / 16 / 2 ^ k
      ≤ 8 * (2 * (n / 16)) := Nat.mul_le_mul_left _ (sum_range_div_two_pow_le _ _)
    _ ≤ n := by omega

/-- There are at most `n` block vertices (`8 ∑_{i ≥ 4} n / 2 ^ i ≤ n`). -/
theorem card_bVertex_le (n : ℕ) : Fintype.card (BVertex n) ≤ n := by
  have hcard : Fintype.card (BVertex n) = 8 * ∑ i ∈ Finset.Icc 4 (top n), n / 2 ^ i := by
    rw [Fintype.card_sigma, Fintype.sum_prod_type, Finset.mul_sum, Finset.univ_eq_attach,
      ← Finset.sum_attach (Finset.Icc 4 (top n)) fun i ↦ 8 * (n / 2 ^ i)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [Fintype.card_fin]
    simp [bsize]
  rw [hcard]
  exact eight_mul_sum_Icc_div_le n (top n)

theorem card_vtx_le (n : ℕ) : Fintype.card (Vtx n) ≤ 2 * n := by
  rw [Fintype.card_sum, Fintype.card_fin]
  have := card_bVertex_le n
  omega

/-- Every block has at least `√n / 2` vertices: `n ≤ 4 * bsize n p ^ 2` (for `4 ≤ n`). -/
theorem le_four_mul_bsize_sq {n : ℕ} (hn : 4 ≤ n) (p : BlockIdx n) : n ≤ 4 * bsize n p ^ 2 := by
  have hi : (p.1 : ℕ) ≤ top n := (Finset.mem_Icc.mp p.1.2).2
  have hq : 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) ≤ n := by
    have h2 : 2 * (p.1 : ℕ) ≤ Nat.log 2 n := by
      have : (p.1 : ℕ) ≤ Nat.log 2 n / 2 := hi
      omega
    calc 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) = 2 ^ (2 * (p.1 : ℕ)) := by ring
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hqpos : 0 < 2 ^ (p.1 : ℕ) := pow_pos (by norm_num) _
  have hd : 1 ≤ bsize n p := by
    rw [bsize, Nat.one_le_div_iff hqpos]
    calc 2 ^ (p.1 : ℕ) = 1 * 2 ^ (p.1 : ℕ) := (one_mul _).symm
      _ ≤ 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) := Nat.mul_le_mul_right _ hqpos
      _ ≤ n := hq
  have hlt : n < (bsize n p + 1) * 2 ^ (p.1 : ℕ) := by
    rw [bsize, add_mul, one_mul]
    exact Nat.lt_div_mul_add hqpos
  have key : n * n < (bsize n p + 1) ^ 2 * n := by
    calc n * n < ((bsize n p + 1) * 2 ^ (p.1 : ℕ)) * ((bsize n p + 1) * 2 ^ (p.1 : ℕ)) :=
          Nat.mul_lt_mul_of_lt_of_lt hlt hlt
      _ = (bsize n p + 1) ^ 2 * (2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ)) := by ring
      _ ≤ (bsize n p + 1) ^ 2 * n := Nat.mul_le_mul_left _ hq
  have hn2 : n < (bsize n p + 1) ^ 2 := Nat.lt_of_mul_lt_mul_right key
  nlinarith [hd, hn2]

end

/-! ### Upstream module `Proof/Counting.lean` -/

/-!
# The union-bound claim

For `m ≥ 1` put `rpar m = 4 (⌊√⌊log₂ m⌋⌋ + 1) + 16` (an integer with
`4 √(log₂ m) + 16 ≤ rpar m ≤ 4 √(log₂ m) + 24`).  The large blocks for `m` are the blocks of
size at least `m · 2 ^ rpar m`.  A choice function `f` is *good* when for every `m ∈ [1, n]`, every
`A' ⊆ A` with `|A'| ≤ m` and every set `B'` of at most `m` vertices in large blocks, fewer than
`m · rpar m` edges of `graphOf f` join `A'` to `B'`.

Counting: the number of choice functions realising a prescribed set `E` of `A`-block-vertex
pairs is at most `|Choice n| / ∏_{e ∈ E} bsize(e)` (`card_forced_le`), and a union bound over
`m`, `A'`, `B'` and `E` bounds the number of bad choice functions by
`|Choice n| · ∑_m badBound n m` (`card_bad_le`), where every large block has at least
`max (m · 2 ^ rpar m, √n / 2)` vertices.
-/

/-- The threshold parameter `r = r(m)`. -/
def rpar (m : ℕ) : ℕ := 4 * (Nat.sqrt (Nat.log 2 m) + 1) + 16

/-- Block vertices lying in blocks of size at least `m · 2 ^ rpar m`. -/
def largeB (n m : ℕ) : Finset (BVertex n) :=
  Finset.univ.filter fun b ↦ m * 2 ^ rpar m ≤ bsize n b.1

/-- The edges of `graphOf f` joining `A'` to `B'`, as pairs. -/
def crossEdges {n : ℕ} (f : Choice n) (A' : Finset (Fin n)) (B' : Finset (BVertex n)) :
    Finset (Fin n × BVertex n) :=
  (A' ×ˢ B').filter fun ab ↦ f ab.1 ab.2.1 = ab.2.2

/-- A choice function is good when the union-bound claim holds for it. -/
def Good {n : ℕ} (f : Choice n) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ A' : Finset (Fin n), A'.card ≤ m →
    ∀ B' : Finset (BVertex n), B' ⊆ largeB n m → B'.card ≤ m →
      (crossEdges f A' B').card < m * rpar m

/-- Choice functions realising every pair in `E`: at most `|Choice n| / ∏ bsize`. -/
theorem card_forced_le (n : ℕ) (E : Finset (Fin n × BVertex n)) :
    {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2}.ncard * ∏ e ∈ E, bsize n e.2.1 ≤
      Fintype.card (Choice n) := by
  classical
  set S : Finset (Choice n) := Finset.univ.filter (fun f ↦ ∀ e ∈ E, f e.1 e.2.1 = e.2.2) with hS
  have hset : {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2} = (S : Set (Choice n)) := by
    ext f
    simp [hS]
  rw [hset, Set.ncard_coe_finset]
  by_cases hSe : S = ∅
  · rw [hSe]
    simp
  · obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have hinj : ∀ x ∈ E, ∀ y ∈ E, ((x.1, x.2.1) : Fin n × BlockIdx n) = (y.1, y.2.1) → x = y := by
      intro x hx y hy hxy
      rw [hS, Finset.mem_filter] at hf₀
      obtain ⟨a, p, b⟩ := x
      obtain ⟨a', p', b'⟩ := y
      have h1 := hf₀.2 _ hx
      have h2 := hf₀.2 _ hy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      simp only at h1 h2
      rw [← h1, ← h2]
    set K : Finset (Fin n × BlockIdx n) := E.image (fun e ↦ (e.1, e.2.1)) with hK
    have hprod : ∏ e ∈ E, bsize n e.2.1 = ∏ k ∈ K, bsize n k.2 := by
      rw [hK, Finset.prod_image hinj]
    have hdet : ∀ f₁ ∈ S, ∀ f₂ ∈ S, ∀ a : Fin n, ∀ p : BlockIdx n, (a, p) ∈ K →
        f₁ a p = f₂ a p := by
      intro f₁ h₁ f₂ h₂ a p hap
      rw [hS, Finset.mem_filter] at h₁ h₂
      rw [hK, Finset.mem_image] at hap
      obtain ⟨e, he, hep⟩ := hap
      obtain ⟨a', p', b'⟩ := e
      simp only [Prod.mk.injEq] at hep
      obtain ⟨rfl, rfl⟩ := hep
      rw [h₁.2 _ he, h₂.2 _ he]
    have key : (S ×ˢ (Finset.univ :
        Finset ((k : {x : Fin n × BlockIdx n // x ∈ K}) → Fin (bsize n k.1.2)))).card ≤
          Fintype.card (Choice n) := by
      rw [← Finset.card_univ (α := Choice n)]
      refine Finset.card_le_card_of_injOn
        (fun fg ↦ fun a p ↦ if h : (a, p) ∈ K then fg.2 ⟨(a, p), h⟩ else fg.1 a p)
        (fun _ _ ↦ Finset.mem_univ _) ?_
      rintro ⟨f₁, g₁⟩ hm₁ ⟨f₂, g₂⟩ hm₂ heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hm₁ hm₂
      have hfun : ∀ (a : Fin n) (p : BlockIdx n),
          (if h : (a, p) ∈ K then g₁ ⟨(a, p), h⟩ else f₁ a p) =
            (if h : (a, p) ∈ K then g₂ ⟨(a, p), h⟩ else f₂ a p) :=
        fun a p ↦ congrFun (congrFun heq a) p
      have hg : g₁ = g₂ := by
        funext k
        obtain ⟨⟨a, p⟩, hk⟩ := k
        have hk' := hfun a p
        simpa only [hk, dite_true, reduceDIte] using hk'
      have hf : f₁ = f₂ := by
        funext a p
        by_cases hk : (a, p) ∈ K
        · exact hdet f₁ hm₁.1 f₂ hm₂.1 a p hk
        · have hk' := hfun a p
          simpa only [hk, dite_false, reduceDIte] using hk'
      simp [hf, hg]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_pi] at key
    simp only [Fintype.card_fin] at key
    rw [Finset.prod_coe_sort K (fun k ↦ bsize n k.2)] at key
    rw [hprod]
    exact key

/-- The choice functions realising every pair in `E`. -/
private def forced {n : ℕ} (E : Finset (Fin n × BVertex n)) : Finset (Choice n) :=
  Finset.univ.filter fun f ↦ ∀ e ∈ E, f e.1 e.2.1 = e.2.2

/-- `card_forced_le` in `Finset` form. -/
private theorem card_forced_mul_le {n : ℕ} (E : Finset (Fin n × BVertex n)) :
    (forced E).card * ∏ e ∈ E, bsize n e.2.1 ≤ Fintype.card (Choice n) := by
  have h := card_forced_le n E
  have hcoe : {f : Choice n | ∀ e ∈ E, f e.1 e.2.1 = e.2.2} = (forced E : Set (Choice n)) := by
    ext f
    simp [forced]
  rwa [hcoe, Set.ncard_coe_finset] at h

/-- Each forced edge into a large block costs a factor `min (1 / (m · 2 ^ rpar m)) (2 / √n)`. -/
private theorem card_forced_le_real {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m)
    (E : Finset (Fin n × BVertex n)) (hE : ∀ e ∈ E, e.2 ∈ largeB n m) :
    ((forced E).card : ℝ) ≤ (Fintype.card (Choice n) : ℝ) *
      (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ E.card := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hmR : (0 : ℝ) < (m : ℝ) * 2 ^ rpar m := by positivity
  have hbig : ∀ e ∈ E, m * 2 ^ rpar m ≤ bsize n e.2.1 := by
    intro e he
    have h := hE e he
    rw [largeB, Finset.mem_filter] at h
    exact h.2
  have hbpos : ∀ e ∈ E, 0 < bsize n e.2.1 := by
    intro e he
    have h1 := hbig e he
    have h2 : 0 < m * 2 ^ rpar m := Nat.mul_pos hm (Nat.two_pow_pos _)
    omega
  have hble : ∀ e ∈ E, ((bsize n e.2.1 : ℝ))⁻¹ ≤
      min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) := by
    intro e he
    have hb : (0 : ℝ) < (bsize n e.2.1 : ℝ) := by exact_mod_cast hbpos e he
    rw [← one_div]
    refine le_min (one_div_le_one_div_of_le hmR ?_) ?_
    · have h := hbig e he
      have hcast : ((m * 2 ^ rpar m : ℕ) : ℝ) ≤ ((bsize n e.2.1 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at hcast
      exact hcast
    · rw [le_div_iff₀ hsq, div_mul_eq_mul_div, one_mul, div_le_iff₀ hb]
      have h4 := le_four_mul_bsize_sq hn e.2.1
      have h4R : (n : ℝ) ≤ (2 * (bsize n e.2.1 : ℝ)) ^ 2 := by
        have hcast : ((n : ℕ) : ℝ) ≤ ((4 * bsize n e.2.1 ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
        push_cast at hcast
        nlinarith [hcast]
      calc Real.sqrt n ≤ Real.sqrt ((2 * (bsize n e.2.1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt h4R
        _ = 2 * (bsize n e.2.1 : ℝ) := Real.sqrt_sq (by positivity)
  have hP : (0 : ℝ) < ∏ e ∈ E, (bsize n e.2.1 : ℝ) :=
    Finset.prod_pos fun e he ↦ by exact_mod_cast hbpos e he
  have hkey : ((forced E).card : ℝ) * ∏ e ∈ E, (bsize n e.2.1 : ℝ) ≤
      (Fintype.card (Choice n) : ℝ) := by
    have h := card_forced_mul_le E
    have hcast : (((forced E).card * ∏ e ∈ E, bsize n e.2.1 : ℕ) : ℝ) ≤
        (Fintype.card (Choice n) : ℝ) := by exact_mod_cast h
    push_cast at hcast
    exact hcast
  rw [← le_div_iff₀ hP] at hkey
  refine hkey.trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [← Finset.prod_inv_distrib]
  calc ∏ e ∈ E, ((bsize n e.2.1 : ℝ))⁻¹
      ≤ ∏ _e ∈ E, min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
        Finset.prod_le_prod (fun e _ ↦ by positivity) hble
    _ = (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ E.card := Finset.prod_const _

/-- There are at most `(m + 1) (2 N) ^ m` subsets of a set of size at most `N` with at most
`m` elements. -/
private theorem card_powerset_filter_le {α : Type*} [DecidableEq α] (s : Finset α) (m N : ℕ)
    (hs : s.card ≤ N) (hN : 1 ≤ N) :
    (s.powerset.filter fun t ↦ t.card ≤ m).card ≤ (m + 1) * (2 * N) ^ m := by
  have hsub : s.powerset.filter (fun t ↦ t.card ≤ m) ⊆
      (Finset.range (m + 1)).biUnion fun a ↦ s.powersetCard a := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Finset.mem_biUnion.mpr ⟨t.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨ht.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ a ∈ Finset.range (m + 1), (s.powersetCard a).card
      ≤ ∑ _a ∈ Finset.range (m + 1), (2 * N) ^ m := by
        refine Finset.sum_le_sum fun a ha ↦ ?_
        rw [Finset.card_powersetCard]
        have h1 : s.card.choose a ≤ N.choose a := Nat.choose_le_choose a hs
        have h2 : N.choose a ≤ N ^ a := Nat.choose_le_pow N a
        have h3 : N ^ a ≤ N ^ m :=
          Nat.pow_le_pow_right hN (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
        have h4 : N ^ m ≤ (2 * N) ^ m := Nat.pow_le_pow_left (by omega) m
        omega
    _ = (m + 1) * (2 * N) ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The subsets of `Fin n` with at most `m` elements. -/
private def smallA (n m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter fun A' ↦ A'.card ≤ m

/-- The subsets of `largeB n m` with at most `m` elements. -/
private def smallB (n m : ℕ) : Finset (Finset (BVertex n)) :=
  (largeB n m).powerset.filter fun B' ↦ B'.card ≤ m

/-- There are at most `(m + 1) (2 n) ^ m` sets in `smallA n m`. -/
private theorem card_smallA_le {n m : ℕ} (hn : 1 ≤ n) :
    (smallA n m).card ≤ (m + 1) * (2 * n) ^ m := by
  refine card_powerset_filter_le _ m n ?_ hn
  simp

/-- There are at most `(m + 1) (2 n) ^ m` sets in `smallB n m`. -/
private theorem card_smallB_le {n m : ℕ} (hn : 1 ≤ n) :
    (smallB n m).card ≤ (m + 1) * (2 * n) ^ m := by
  refine card_powerset_filter_le _ m n ?_ hn
  exact (Finset.card_le_univ _).trans (card_bVertex_le n)

/-- The per-`m` term of the union bound. -/
noncomputable def badBound (n m : ℕ) : ℝ :=
  ((m + 1 : ℝ) ^ 2 * (2 * n : ℝ) ^ (2 * m) * ((m ^ 2).choose (m * rpar m) : ℝ)) *
    (min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)

/-- The choice functions covered by the union bound with parameter `m`. -/
private def badCoverAt (n m : ℕ) : Finset (Choice n) :=
  (smallA n m).biUnion fun A' ↦ (smallB n m).biUnion fun B' ↦
    ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E

/-- The union bound for a single value of `m`. -/
private theorem card_badCoverAt_le {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m) :
    ((badCoverAt n m).card : ℝ) ≤ (Fintype.card (Choice n) : ℝ) * badBound n m := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set c : ℝ := min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) with hc
  set C : ℝ := (Fintype.card (Choice n) : ℝ) with hC
  set κ : ℝ := ((m ^ 2).choose (m * rpar m) : ℝ) with hκ
  set β : ℝ := ((m : ℝ) + 1) * (2 * n : ℝ) ^ m with hβ
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    refine le_min ?_ ?_ <;> positivity
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
  have hβ0 : (0 : ℝ) ≤ β := by
    rw [hβ]
    positivity
  have hcp0 : (0 : ℝ) ≤ C * c ^ (m * rpar m) := mul_nonneg hC0 (pow_nonneg hc0 _)
  have hEbound : ∀ A' ∈ smallA n m, ∀ B' ∈ smallB n m,
      (((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ)) ≤
        κ * (C * c ^ (m * rpar m)) := by
    intro A' hA' B' hB'
    rw [smallA, Finset.mem_filter] at hA'
    rw [smallB, Finset.mem_filter, Finset.mem_powerset] at hB'
    have hstep : ∀ E ∈ (A' ×ˢ B').powersetCard (m * rpar m),
        ((forced E).card : ℝ) ≤ C * c ^ (m * rpar m) := by
      intro E hEmem
      rw [Finset.mem_powersetCard] at hEmem
      have h := card_forced_le_real hn hm E fun e he ↦
        hB'.1 (Finset.mem_product.mp (hEmem.1 he)).2
      rw [hEmem.2] at h
      exact h
    calc (((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ))
        ≤ ∑ E ∈ (A' ×ˢ B').powersetCard (m * rpar m), ((forced E).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ (A' ×ˢ B').powersetCard (m * rpar m), C * c ^ (m * rpar m) :=
          Finset.sum_le_sum hstep
      _ = (((A' ×ˢ B').powersetCard (m * rpar m)).card : ℝ) * (C * c ^ (m * rpar m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ κ * (C * c ^ (m * rpar m)) := by
          refine mul_le_mul_of_nonneg_right ?_ hcp0
          rw [hκ]
          refine Nat.cast_le.mpr ?_
          rw [Finset.card_powersetCard, Finset.card_product]
          refine Nat.choose_le_choose _ ?_
          calc A'.card * B'.card ≤ m * m := Nat.mul_le_mul hA'.2 hB'.2
            _ = m ^ 2 := (sq m).symm
  have hBbound : ∀ A' ∈ smallA n m,
      ((((smallB n m).biUnion fun B' ↦ ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion
        fun E ↦ forced E).card : ℝ)) ≤ β * (κ * (C * c ^ (m * rpar m))) := by
    intro A' hA'
    calc ((((smallB n m).biUnion fun B' ↦ ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion
          fun E ↦ forced E).card : ℝ))
        ≤ ∑ B' ∈ smallB n m,
            ((((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _B' ∈ smallB n m, κ * (C * c ^ (m * rpar m)) :=
          Finset.sum_le_sum (hEbound A' hA')
      _ = ((smallB n m).card : ℝ) * (κ * (C * c ^ (m * rpar m))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ β * (κ * (C * c ^ (m * rpar m))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hκ0 hcp0)
          have h := card_smallB_le (n := n) (m := m) hn1
          have hcast : (((smallB n m).card : ℕ) : ℝ) ≤ (((m + 1) * (2 * n) ^ m : ℕ) : ℝ) := by
            exact_mod_cast h
          rw [hβ]
          push_cast at hcast ⊢
          exact hcast
  have hpow : (2 * (n : ℝ)) ^ (2 * m) = ((2 * (n : ℝ)) ^ m) ^ 2 := by
    rw [show 2 * m = m * 2 from Nat.mul_comm 2 m, pow_mul]
  have hfinal : β * (β * (κ * (C * c ^ (m * rpar m)))) = C * badBound n m := by
    rw [badBound, ← hc, ← hκ, hβ, hpow]
    ring
  rw [badCoverAt, ← hfinal]
  calc (((smallA n m).biUnion fun A' ↦ (smallB n m).biUnion fun B' ↦
        ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ)
      ≤ ∑ A' ∈ smallA n m, (((smallB n m).biUnion fun B' ↦
          ((A' ×ˢ B').powersetCard (m * rpar m)).biUnion fun E ↦ forced E).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _A' ∈ smallA n m, β * (κ * (C * c ^ (m * rpar m))) := Finset.sum_le_sum hBbound
    _ = ((smallA n m).card : ℝ) * (β * (κ * (C * c ^ (m * rpar m)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ β * (β * (κ * (C * c ^ (m * rpar m)))) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hβ0 (mul_nonneg hκ0 hcp0))
        have h := card_smallA_le (n := n) (m := m) hn1
        have hcast : (((smallA n m).card : ℕ) : ℝ) ≤ (((m + 1) * (2 * n) ^ m : ℕ) : ℝ) := by
          exact_mod_cast h
        rw [hβ]
        push_cast at hcast ⊢
        exact hcast

/-- Union bound: the number of bad choice functions is at most `|Choice n| · ∑_m badBound n m`. -/
theorem card_bad_le (n : ℕ) (hn : 4 ≤ n) :
    ({f : Choice n | ¬ Good f}.ncard : ℝ) ≤
      (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m := by
  classical
  set Bad : Finset (Choice n) := Finset.univ.filter (fun f ↦ ¬ Good f) with hBad
  have hcoe : {f : Choice n | ¬ Good f} = (Bad : Set (Choice n)) := by
    ext f
    simp [hBad]
  rw [hcoe, Set.ncard_coe_finset]
  have hsub : Bad ⊆ (Finset.Icc 1 n).biUnion fun m ↦ badCoverAt n m := by
    intro f hf
    rw [hBad, Finset.mem_filter] at hf
    by_contra hc
    refine hf.2 ?_
    intro m hm1 hmn A' hA' B' hB'sub hB'card
    by_contra hlt
    obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (Nat.not_lt.mp hlt)
    refine hc (Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmn⟩, ?_⟩)
    rw [badCoverAt]
    refine Finset.mem_biUnion.mpr ⟨A', ?_, Finset.mem_biUnion.mpr ⟨B', ?_,
      Finset.mem_biUnion.mpr ⟨E, ?_, ?_⟩⟩⟩
    · rw [smallA, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA'⟩
    · rw [smallB, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hB'sub, hB'card⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, hEcard⟩
      intro e he
      exact (Finset.mem_filter.mp (hEsub he)).1
    · rw [forced, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun e he ↦ (Finset.mem_filter.mp (hEsub he)).2⟩
  calc (Bad.card : ℝ)
      ≤ (((Finset.Icc 1 n).biUnion fun m ↦ badCoverAt n m).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ m ∈ Finset.Icc 1 n, ((badCoverAt n m).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ m ∈ Finset.Icc 1 n, (Fintype.card (Choice n) : ℝ) * badBound n m := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        exact card_badCoverAt_le hn (Finset.mem_Icc.mp hm).1
    _ = (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m :=
        (Finset.mul_sum _ _ _).symm

/-! ### Upstream module `Proof/Estimates.lean` -/

/-!
# Real-number estimates

For `n ≥ 2 ^ 40` and `1 ≤ m ≤ n` the union-bound term satisfies `badBound n m ≤ 2⁻ᵐ`, so the
sum over `m` is below `1`.  The two regimes are `m ≤ n ^ (1/4)` (use the block-size lower bound
`√n / 2`) and `m > n ^ (1/4)` (use `m · 2 ^ rpar m`), following Alon.  Also
`rpar m ≤ 4 √(log₂ m) + 24` and `4 √(log₂ m) + 16 ≤ rpar m`.
-/

/-- `Nat.log 2 m` is the floor of `Real.logb 2 m`, so it is at most `Real.logb 2 m`. -/
private lemma natLog_le_logb (m : ℕ) (hm : 1 ≤ m) : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  have hfloor : ⌊Real.logb 2 m⌋₊ = Nat.log 2 m := by
    have h := Real.natFloor_logb_natCast 2 m
    norm_num at h
    exact h
  have hnn : (0 : ℝ) ≤ Real.logb 2 m :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  rw [← hfloor]
  exact Nat.floor_le hnn

/-- `⌊√⌊log₂ m⌋⌋ ≤ √(log₂ m)` for `m ≥ 1`. -/
private lemma natSqrt_le_sqrt_logb (m : ℕ) (hm : 1 ≤ m) :
    (Nat.sqrt (Nat.log 2 m) : ℝ) ≤ Real.sqrt (Real.logb 2 m) := by
  refine le_trans Real.nat_sqrt_le_real_sqrt ?_
  exact Real.sqrt_le_sqrt (natLog_le_logb m hm)

theorem rpar_le (m : ℕ) (hm : 1 ≤ m) : (rpar m : ℝ) ≤ 4 * Real.sqrt (Real.logb 2 m) + 24 := by
  have h := natSqrt_le_sqrt_logb m hm
  have hr : (rpar m : ℝ) = 4 * ((Nat.sqrt (Nat.log 2 m) : ℝ) + 1) + 16 := by
    unfold rpar
    push_cast
    ring
  rw [hr]
  linarith

theorem sixteen_le_rpar (m : ℕ) : 16 ≤ rpar m := by
  unfold rpar
  omega

/-- `k! ≥ (k / 3) ^ k`. -/
theorem pow_div_three_le_factorial (k : ℕ) : ((k : ℝ) / 3) ^ k ≤ k.factorial := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k := by
    gcongr
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    have hle : Real.sqrt 1 ≤ Real.sqrt (2 * Real.pi * k) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    simpa using hle
  calc ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k := h1
    _ ≤ Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k :=
        le_mul_of_one_le_left (by positivity) h2
    _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k

/-- `C(a, k) ≤ (3 a / k) ^ k` for `k ≥ 1`. -/
theorem choose_le_pow_three_mul_div (a k : ℕ) (hk : 1 ≤ k) :
    (a.choose k : ℝ) ≤ (3 * a / k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((k : ℝ) / 3) ^ k := by positivity
  calc (a.choose k : ℝ) ≤ (a : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k a
    _ ≤ (a : ℝ) ^ k / ((k : ℝ) / 3) ^ k :=
        div_le_div_of_nonneg_left (by positivity) hpos (pow_div_three_le_factorial k)
    _ = (3 * a / k : ℝ) ^ k := by
        have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
        rw [div_pow, div_pow]
        field_simp
        ring

/-- `(m + 1) ^ 2 ≤ 4 ^ m` over the reals. -/
private lemma sq_add_one_le_four_pow (m : ℕ) : ((m : ℝ) + 1) ^ 2 ≤ 4 ^ m := by
  have h1 : m + 1 ≤ 2 ^ m := m.lt_two_pow_self
  have h2 : (m + 1) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : ((2 : ℕ) ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h3] at h2
  exact_mod_cast h2

/-- Reduction step shared by the two regimes of `badBound_le`. -/
private lemma badBound_le_of (n m : ℕ) (D : ℝ) (hm : 1 ≤ m) (hn : 0 < n) (hD0 : 0 ≤ D)
    (hpow : ((3 * (m : ℝ) / rpar m) *
        min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m) ≤ D ^ m)
    (hfin : 4 * (4 * (n : ℝ) ^ 2) * D ≤ 1 / 2) :
    badBound n m ≤ (1 / 2 : ℝ) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 16 ≤ rpar m := sixteen_le_rpar m
  have hr0 : (0 : ℝ) < rpar m := by
    have h : (0 : ℕ) < rpar m := by omega
    exact_mod_cast h
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hXpos : 0 < min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
    lt_min (by positivity) (by positivity)
  set X : ℝ := min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) with hXdef
  have hk : 1 ≤ m * rpar m := by
    have h : 0 < m * rpar m := Nat.mul_pos hm (by omega)
    omega
  have hchoose : (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ)
      ≤ (3 * (m : ℝ) / rpar m) ^ (m * rpar m) := by
    have h := choose_le_pow_three_mul_div (m ^ 2) (m * rpar m) hk
    have he : (3 * ((m ^ 2 : ℕ) : ℝ) / ((m * rpar m : ℕ) : ℝ))
        = 3 * (m : ℝ) / (rpar m : ℝ) := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rwa [he] at h
  have e1 : (2 * (n : ℝ)) ^ (2 * m) = (4 * (n : ℝ) ^ 2) ^ m := by
    rw [pow_mul]
    congr 1
    ring
  have hc : (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m) ≤ D ^ m := by
    calc (((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m)
        ≤ (3 * (m : ℝ) / rpar m) ^ (m * rpar m) * X ^ (m * rpar m) := by gcongr
      _ = ((3 * (m : ℝ) / rpar m) * X) ^ (m * rpar m) := (mul_pow _ _ _).symm
      _ ≤ D ^ m := hpow
  calc badBound n m
      = (((m : ℝ) + 1) ^ 2 * (2 * (n : ℝ)) ^ (2 * m)) *
          ((((m ^ 2).choose (m * rpar m) : ℕ) : ℝ) * X ^ (m * rpar m)) := by
        rw [badBound, hXdef]
        ring
    _ ≤ ((4 : ℝ) ^ m * (4 * (n : ℝ) ^ 2) ^ m) * D ^ m := by
        rw [e1]
        refine mul_le_mul ?_ hc (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (sq_add_one_le_four_pow m) (by positivity)
    _ = (4 * (4 * (n : ℝ) ^ 2) * D) ^ m := by
        rw [← mul_pow, ← mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hfin m

/-- In the large-`m` regime `32 n ^ 2 ≤ 2 ^ (rpar m) ^ 2`. -/
private lemma thirtytwo_mul_sq_le (n m : ℕ) (h : n < m ^ 4) :
    32 * n ^ 2 ≤ 2 ^ (rpar m * rpar m) := by
  have hLs : Nat.log 2 m + 1 ≤ (Nat.sqrt (Nat.log 2 m) + 1) * (Nat.sqrt (Nat.log 2 m) + 1) :=
    Nat.lt_succ_sqrt (Nat.log 2 m)
  have h6 : 8 * Nat.log 2 m + 13 ≤ rpar m * rpar m := by
    unfold rpar
    nlinarith [hLs, Nat.zero_le (Nat.sqrt (Nat.log 2 m)), Nat.zero_le (Nat.log 2 m)]
  have hmlog : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h1 : n ^ 2 < (m ^ 4) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  have h3 : (m ^ 4) ^ 2 < (2 ^ (Nat.log 2 m + 1)) ^ 8 := by
    have hrw : (m ^ 4) ^ 2 = m ^ 8 := by ring
    rw [hrw]
    exact Nat.pow_lt_pow_left hmlog (by norm_num)
  have h4 : ((2 : ℕ) ^ (Nat.log 2 m + 1)) ^ 8 = 2 ^ (8 * Nat.log 2 m + 8) := by
    rw [← pow_mul]
    congr 1
    ring
  have h5 : 32 * n ^ 2 ≤ 2 ^ (8 * Nat.log 2 m + 13) := by
    have hlt : n ^ 2 < 2 ^ (8 * Nat.log 2 m + 8) := by
      rw [← h4]
      exact lt_trans h1 h3
    calc 32 * n ^ 2 ≤ 32 * 2 ^ (8 * Nat.log 2 m + 8) := by omega
      _ = 2 ^ (8 * Nat.log 2 m + 13) := by
          rw [show 8 * Nat.log 2 m + 13 = 8 * Nat.log 2 m + 8 + 5 by ring, pow_add]
          ring
  exact h5.trans (Nat.pow_le_pow_right (by norm_num) h6)

theorem badBound_le (n m : ℕ) (hn : 2 ^ 40 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
    badBound n m ≤ (1 / 2 : ℝ) ^ m := by
  have hn' : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 16 ≤ rpar m := sixteen_le_rpar m
  have hr0 : (0 : ℝ) < rpar m := by
    have h : (0 : ℕ) < rpar m := by omega
    exact_mod_cast h
  have hr16 : (16 : ℝ) ≤ rpar m := by exact_mod_cast hr
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsqsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hnbig : (2 : ℝ) ^ 40 ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn1 : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hm1 hmn1
  have hXpos : 0 < min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) :=
    lt_min (by positivity) (by positivity)
  rcases le_or_gt (m ^ 4) n with hcase | hcase
  · -- Small `m`: use the `2 / √n` block bound.
    refine badBound_le_of n m (1 / (2 ^ 16 * (n : ℝ) ^ 4)) hm hn' (by positivity) ?_ ?_
    · have hm4 : ((m : ℝ) ^ 2) ^ 2 ≤ (n : ℝ) := by
        have h' : ((m : ℝ) ^ 4) ≤ (n : ℝ) := by exact_mod_cast hcase
        calc ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 := by ring
          _ ≤ (n : ℝ) := h'
      have hms : (m : ℝ) ^ 2 ≤ Real.sqrt n := by
        calc (m : ℝ) ^ 2 = Real.sqrt (((m : ℝ) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hm4
      have hbase : (3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ (m : ℝ) / (2 * Real.sqrt n) := by
        have h1 : min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ 2 / Real.sqrt n :=
          min_le_right _ _
        have h2 : 3 * (m : ℝ) / rpar m ≤ 3 * (m : ℝ) / 16 := by gcongr
        have h3 : (3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ (3 * (m : ℝ) / 16) *
              (2 / Real.sqrt n) :=
          mul_le_mul h2 h1 hXpos.le (by positivity)
        refine h3.trans ?_
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hsq, hm0]
      have hu0 : (0 : ℝ) ≤ (m : ℝ) / (2 * Real.sqrt n) := by positivity
      have hu1 : (m : ℝ) / (2 * Real.sqrt n) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [hms, hm1, hsq]
      have hstep : ((3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (m * rpar m) :=
        pow_le_pow_left₀ (by positivity) hbase _
      have hexp : 16 * m ≤ m * rpar m := by
        calc 16 * m = m * 16 := by ring
          _ ≤ m * rpar m := Nat.mul_le_mul_left m hr
      have hstep2 : ((m : ℝ) / (2 * Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (16 * m) :=
        pow_le_pow_of_le_one hu0 hu1 hexp
      have hm16 : ((m : ℝ) ^ 16) ≤ (n : ℝ) ^ 4 := by
        have hnat : (m ^ 4) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hcase 4
        have h' : ((m : ℝ) ^ 4) ^ 4 ≤ (n : ℝ) ^ 4 := by exact_mod_cast hnat
        calc (m : ℝ) ^ 16 = ((m : ℝ) ^ 4) ^ 4 := by ring
          _ ≤ (n : ℝ) ^ 4 := h'
      have hsqrt16 : Real.sqrt n ^ 16 = (n : ℝ) ^ 8 := by
        rw [show (16 : ℕ) = 2 * 8 by norm_num, pow_mul, hsqsq]
      have hD : ((m : ℝ) / (2 * Real.sqrt n)) ^ 16 ≤ 1 / (2 ^ 16 * (n : ℝ) ^ 4) := by
        rw [div_pow, mul_pow, hsqrt16, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hm16 (le_of_lt (pow_pos hn0 4))]
      calc ((3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ ((m : ℝ) / (2 * Real.sqrt n)) ^ (16 * m) := hstep.trans hstep2
        _ = (((m : ℝ) / (2 * Real.sqrt n)) ^ 16) ^ m := by rw [pow_mul]
        _ ≤ (1 / (2 ^ 16 * (n : ℝ) ^ 4)) ^ m := pow_le_pow_left₀ (by positivity) hD m
    · have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hn1]
      have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
        nlinarith [hn2, sq_nonneg ((n : ℝ) ^ 2 - 1)]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hn24, pow_pos hn0 2]
  · -- Large `m`: use the `1 / (m 2 ^ r)` block bound.
    refine badBound_le_of n m (1 / (2 : ℝ) ^ (rpar m * rpar m)) hm hn' (by positivity) ?_ ?_
    · have hbase : (3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n) ≤ 1 / (2 : ℝ) ^ rpar m := by
        have h1 : min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)
            ≤ 1 / (m * 2 ^ rpar m : ℝ) := min_le_left _ _
        have h2 : (3 * (m : ℝ) / rpar m) * (1 / (m * 2 ^ rpar m : ℝ))
            = 3 / ((rpar m : ℝ) * 2 ^ rpar m) := by
          rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
          ring
        have h3 : (3 * (m : ℝ) / rpar m) *
            min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)
            ≤ (3 * (m : ℝ) / rpar m) * (1 / (m * 2 ^ rpar m : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [h2] at h3
        refine h3.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hr16
          (le_of_lt (pow_pos (show (0 : ℝ) < 2 by norm_num) (rpar m))),
          pow_pos (show (0 : ℝ) < 2 by norm_num) (rpar m)]
      have hstep : ((3 * (m : ℝ) / rpar m) *
          min (1 / (m * 2 ^ rpar m : ℝ)) (2 / Real.sqrt n)) ^ (m * rpar m)
          ≤ (1 / (2 : ℝ) ^ rpar m) ^ (m * rpar m) :=
        pow_le_pow_left₀ (by positivity) hbase _
      refine hstep.trans_eq ?_
      rw [mul_comm m (rpar m), pow_mul, div_pow, one_pow, ← pow_mul]
    · have hkey : (32 : ℝ) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (rpar m * rpar m) := by
        have h := thirtytwo_mul_sq_le n m hcase
        exact_mod_cast h
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]

/-- The geometric sum `∑_{m=1}^{n} 2⁻ᵐ` equals `1 - 2⁻ⁿ`. -/
private lemma sum_geom_Icc (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ m = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem sum_badBound_lt_one (n : ℕ) (hn : 2 ^ 40 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, badBound n m < 1 := by
  have h1 : ∑ m ∈ Finset.Icc 1 n, badBound n m
      ≤ ∑ m ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ m := by
    refine Finset.sum_le_sum fun m hm ↦ ?_
    rw [Finset.mem_Icc] at hm
    exact badBound_le n m hn hm.1 hm.2
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  rw [sum_geom_Icc n] at h1
  linarith

/-! ### Upstream module `Proof/Existence.lean` -/

/-!
# Existence of a good choice function

For `n ≥ 2 ^ 40` the union bound shows that fewer than `|Choice n|` choice functions are bad,
so a good one exists.
-/

/-- For `n ≥ 2 ^ 40` a good choice function exists: the union bound makes the number of bad
choice functions strictly smaller than `|Choice n|`. -/
theorem exists_good (n : ℕ) (hn : 2 ^ 40 ≤ n) : ∃ f : Choice n, Good f := by
  have hn4 : 4 ≤ n := le_trans (by norm_num) hn
  have hne : Nonempty (Choice n) := by
    refine ⟨fun _ p ↦ ⟨0, ?_⟩⟩
    have h := le_four_mul_bsize_sq hn4 p
    rcases Nat.eq_zero_or_pos (bsize n p) with h0 | h0
    · rw [h0] at h
      norm_num at h
      omega
    · exact h0
  have hcardpos : (0 : ℝ) < (Fintype.card (Choice n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Choice n)
  have hlt : ({f : Choice n | ¬ Good f}.ncard : ℝ) < (Fintype.card (Choice n) : ℝ) :=
    calc ({f : Choice n | ¬ Good f}.ncard : ℝ)
        ≤ (Fintype.card (Choice n) : ℝ) * ∑ m ∈ Finset.Icc 1 n, badBound n m :=
          card_bad_le n hn4
      _ < (Fintype.card (Choice n) : ℝ) * 1 :=
          mul_lt_mul_of_pos_left (sum_badBound_lt_one n hn) hcardpos
      _ = (Fintype.card (Choice n) : ℝ) := mul_one _
  by_contra hcon
  simp only [not_exists] at hcon
  have huniv : {f : Choice n | ¬ Good f} = Set.univ := by
    ext f
    simp [hcon f]
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card] at hlt
  exact lt_irrefl _ hlt

/-! ### Upstream module `Proof/Deterministic.lean` -/

section
/-!
# The deterministic counting argument

Fix a good choice function `f`, `D ≥ 1`, and a `D`-balanced subgraph `H` of `graphOf f` with
`m` vertices, `d` = minimum degree inside `H` (so every degree is at most `D d`).  Every edge of
`H` joins an `A`-vertex to a block vertex; split the edges by the size of that block:

* small blocks (`bsize ≤ m / (64 D)`): at most `m / (4 D)` vertices in total, hence at most
  `m d / 4` incident edges;
* middle blocks (`m / (64 D) < bsize < m · 2 ^ rpar m`): at most `8 (rpar m + log₂(64 D) + 1)`
  blocks, each meeting at most `|A ∩ V(H)| ≤ m` edges of `H`;
* large blocks: fewer than `m · rpar m` edges, by goodness.

Since `2 e(H) = ∑ deg ≥ m d`, this yields `e(H) ≤ 18 m (rpar m + log₂(64 D) + 2)`.
-/

open _root_.SimpleGraph _root_.Finset

/-- A geometric bound in `ℕ`: `∑_{k < K} ⌊M / 2 ^ k⌋ ≤ 2 M`. -/
private lemma sum_range_div_two_pow_le_aux (K M : ℕ) :
    ∑ k ∈ Finset.range K, M / 2 ^ k ≤ 2 * M := by
  induction K generalizing M with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ k : ℕ, M / 2 ^ (k + 1) = M / 2 / 2 ^ k := by
      intro k
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    simp only [h, pow_zero, Nat.div_one]
    have := ih (M / 2)
    omega

/-- The tail bound `∑_{i ∈ [a, b]} ⌊N / 2 ^ i⌋ ≤ 2 ⌊N / 2 ^ a⌋`. -/
private lemma sum_Icc_div_two_pow_le (N a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, N / 2 ^ i ≤ 2 * (N / 2 ^ a) := by
  have hIco : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (b + 1 - a), N / 2 ^ (a + k) = N / 2 ^ a / 2 ^ k := by
    intro k _
    rw [pow_add, Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl hterm]
  exact sum_range_div_two_pow_le_aux _ _

/-- At most `R + log₂(64 D) + 1` indices `i` satisfy `m / (64 D) < n / 2 ^ i < m · 2 ^ R`. -/
private lemma card_mid_le (n m R : ℕ) {D : ℝ} (hD : 1 ≤ D) (hm : 1 ≤ m) (I : Finset ℕ)
    (hI : ∀ i ∈ I, (m : ℝ) / (64 * D) < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) :
    (I.card : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) + 1 := by
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  have hcnn : 0 ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by nlinarith)
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have h0 : I.min' hne ∈ I := I.min'_mem hne
    have h1 : I.max' hne ∈ I := I.max'_mem hne
    set i₀ : ℕ := I.min' hne with hi₀
    set i₁ : ℕ := I.max' hne with hi₁
    have hsub : I ⊆ Finset.Icc i₀ i₁ := fun i hi =>
      Finset.mem_Icc.mpr ⟨I.min'_le i hi, I.le_max' i hi⟩
    have hle : i₀ ≤ i₁ := I.min'_le _ h1
    have hcard : I.card ≤ i₁ - i₀ + 1 := by
      have h := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h
      omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hup : (m : ℝ) * 2 ^ i₁ < 64 * D * n := by
      have h := (hI i₁ h1).1
      have hcast : ((n / 2 ^ i₁ : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ i₁ : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at hcast
      have h2 : (m : ℝ) / (64 * D) < (n : ℝ) / 2 ^ i₁ := lt_of_lt_of_le h hcast
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h2
      linarith
    have hlow : (n : ℝ) < (m : ℝ) * 2 ^ R * 2 ^ i₀ := by
      have h := (hI i₀ h0).2
      have hq : 0 < 2 ^ i₀ := Nat.two_pow_pos i₀
      have hnat : n < m * 2 ^ R * 2 ^ i₀ := by
        calc n < n / 2 ^ i₀ * 2 ^ i₀ + 2 ^ i₀ := Nat.lt_div_mul_add hq
          _ = (n / 2 ^ i₀ + 1) * 2 ^ i₀ := by ring
          _ ≤ m * 2 ^ R * 2 ^ i₀ := Nat.mul_le_mul_right _ (by omega)
      exact_mod_cast hnat
    have hkey : (2 : ℝ) ^ (i₁ - i₀) < 64 * D * 2 ^ R := by
      have hpow : (2 : ℝ) ^ i₁ = 2 ^ (i₁ - i₀) * 2 ^ i₀ := by
        rw [← pow_add]
        congr 1
        omega
      have hp0 : (0 : ℝ) < (2 : ℝ) ^ i₀ := by positivity
      have h2 : (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) < 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) := by
        calc (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) = (m : ℝ) * 2 ^ i₁ := by rw [hpow]
          _ < 64 * D * n := hup
          _ < 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) := by nlinarith
      have hmul : (0 : ℝ) < (m : ℝ) * 2 ^ i₀ := by positivity
      rw [show (m : ℝ) * (2 ^ (i₁ - i₀) * 2 ^ i₀) = 2 ^ (i₁ - i₀) * ((m : ℝ) * 2 ^ i₀) by ring,
        show 64 * D * ((m : ℝ) * 2 ^ R * 2 ^ i₀) = 64 * D * 2 ^ R * ((m : ℝ) * 2 ^ i₀) by
          ring] at h2
      exact lt_of_mul_lt_mul_right h2 hmul.le
    have hlog : ((i₁ - i₀ : ℕ) : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) := by
      have hmono : Real.logb 2 ((2 : ℝ) ^ (i₁ - i₀)) ≤ Real.logb 2 (64 * D * 2 ^ R) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hkey.le
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
        Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one] at hmono
      linarith
    have hcastI : (I.card : ℝ) ≤ ((i₁ - i₀ : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    linarith

/-- Block vertices in blocks of size at most `m / (64 D)` number at most `m / (4 D)`. -/
private lemma card_small_le {n m : ℕ} {D : ℝ} (hD : 1 ≤ D) (Bs : Finset (BVertex n))
    (hBs : ∀ b ∈ Bs, ((bsize n b.1 : ℕ) : ℝ) ≤ (m : ℝ) / (64 * D)) :
    (Bs.card : ℝ) ≤ (m : ℝ) / (4 * D) := by
  classical
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  set S : ℝ := (m : ℝ) / (64 * D) with hS
  have hSnn : 0 ≤ S := by positivity
  set SI : Finset ℕ := (Finset.Icc 4 (top n)).filter (fun i => ((n / 2 ^ i : ℕ) : ℝ) ≤ S) with hSI
  have hSImem : ∀ i : ℕ, i ∈ SI ↔ i ∈ Finset.Icc 4 (top n) ∧ ((n / 2 ^ i : ℕ) : ℝ) ≤ S := by
    intro i
    rw [hSI, Finset.mem_filter]
  set SmallIdx : Finset (BlockIdx n) := Finset.univ.filter (fun p => (p.1 : ℕ) ∈ SI) with hSmall
  have hsub : Bs ⊆ SmallIdx.sigma (fun p => (Finset.univ : Finset (Fin (bsize n p)))) := by
    intro b hb
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hSmall, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hSImem _).mpr ⟨b.1.1.2, hBs b hb⟩⟩
  have hcard : Bs.card ≤ ∑ p ∈ SmallIdx, bsize n p := by
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sigma]
    simp
  have hmaps : ∀ p ∈ SmallIdx, (p.1 : ℕ) ∈ SI := by
    intro p hp
    rw [hSmall, Finset.mem_filter] at hp
    exact hp.2
  have hfib8 : ∀ i : ℕ, (SmallIdx.filter fun p => (p.1 : ℕ) = i).card ≤ 8 := by
    intro i
    have hb : (SmallIdx.filter fun p => (p.1 : ℕ) = i).card
        ≤ (Finset.univ : Finset (Fin 8)).card := by
      refine Finset.card_le_card_of_injOn Prod.snd
        (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun p hp p' hp' h => ?_)
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      exact Prod.ext (Subtype.ext (hp.2.trans hp'.2.symm)) h
    simpa using hb
  have hsum : ∑ p ∈ SmallIdx, bsize n p ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => bsize n p), Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hbody : ∀ p ∈ SmallIdx.filter (fun p => (p.1 : ℕ) = i), bsize n p = n / 2 ^ i := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [bsize, hp.2]
    rw [Finset.sum_congr rfl hbody, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hfib8 i)
  have hcard2 : Bs.card ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := le_trans hcard hsum
  rcases SI.eq_empty_or_nonempty with hempty | hne
  · rw [hempty] at hcard2
    simp only [Finset.sum_empty, Nat.mul_zero, Nat.le_zero] at hcard2
    rw [hcard2, Nat.cast_zero]
    positivity
  · have h0 : SI.min' hne ∈ SI := SI.min'_mem hne
    set i₀ : ℕ := SI.min' hne with hi₀
    have h0' : ((n / 2 ^ i₀ : ℕ) : ℝ) ≤ S := ((hSImem i₀).mp h0).2
    have hsubI : SI ⊆ Finset.Icc i₀ (top n) := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨SI.min'_le i hi, (Finset.mem_Icc.mp ((hSImem i).mp hi).1).2⟩
    have hgeom : ∑ i ∈ SI, n / 2 ^ i ≤ 2 * (n / 2 ^ i₀) :=
      le_trans (Finset.sum_le_sum_of_subset hsubI) (sum_Icc_div_two_pow_le _ _ _)
    have hfin : Bs.card ≤ 16 * (n / 2 ^ i₀) :=
      calc Bs.card ≤ 8 * ∑ i ∈ SI, n / 2 ^ i := hcard2
        _ ≤ 8 * (2 * (n / 2 ^ i₀)) := Nat.mul_le_mul_left 8 hgeom
        _ = 16 * (n / 2 ^ i₀) := by ring
    have hfinR : (Bs.card : ℝ) ≤ 16 * ((n / 2 ^ i₀ : ℕ) : ℝ) := by exact_mod_cast hfin
    have hgoal : (16 : ℝ) * S = (m : ℝ) / (4 * D) := by
      rw [hS]
      field_simp
      ring
    linarith

/-- Alon's counting bound: a `D`-balanced subgraph `H` of the graph of a good choice function
has at most `18 m (rpar m + log₂ (64 D) + 2)` edges, where `m` is its number of vertices. -/
theorem edges_le_of_good {n : ℕ} {f : Choice n} (hf : Good f) (_hn : 2 ^ 40 ≤ n) {D : ℝ}
    (hD : 1 ≤ D) (H : (graphOf f).Subgraph) (hH : Balanced D H) :
    (H.edgeSet.ncard : ℝ) ≤
      18 * H.verts.ncard * (rpar H.verts.ncard + Real.logb 2 (64 * D) + 2) := by
  classical
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  have hcnn : 0 ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by nlinarith)
  set m : ℕ := H.verts.ncard with hm_def
  set R : ℕ := rpar m with hR_def
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · have hV : H.verts = ∅ := by
      refine (Set.ncard_eq_zero (Set.toFinite _)).mp ?_
      rw [← hm_def]
      exact hm0
    have hE : H.edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        rw [Subgraph.mem_edgeSet] at he
        have hu : u ∈ H.verts := H.edge_vert he
        rw [hV] at hu
        exact hu
    rw [hE, Set.ncard_empty, hm0]
    norm_num
  -- the two sides of the bipartition, inside `H`
  set VH : Finset (Vtx n) := H.verts.toFinite.toFinset with hVH_def
  have hVHcard : VH.card = m := by
    rw [hm_def, hVH_def]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  set A' : Finset (Fin n) := Finset.univ.filter (fun a => Sum.inl a ∈ H.verts) with hA'_def
  set BH : Finset (BVertex n) := Finset.univ.filter (fun b => Sum.inr b ∈ H.verts) with hBH_def
  have hA'mem : ∀ a : Fin n, a ∈ A' ↔ Sum.inl a ∈ H.verts := by
    intro a
    rw [hA'_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hBHmem : ∀ b : BVertex n, b ∈ BH ↔ Sum.inr b ∈ H.verts := by
    intro b
    rw [hBH_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hA'card : A'.card ≤ m := by
    rw [← hVHcard]
    refine Finset.card_le_card_of_injOn Sum.inl (fun a ha => ?_) (fun _ _ _ _ h => by simpa using h)
    rw [Finset.mem_coe, hVH_def, Set.Finite.mem_toFinset]
    exact (hA'mem a).1 (Finset.mem_coe.mp ha)
  have hBHcard : BH.card ≤ m := by
    rw [← hVHcard]
    refine Finset.card_le_card_of_injOn Sum.inr (fun b hb => ?_) (fun _ _ _ _ h => by simpa using h)
    rw [Finset.mem_coe, hVH_def, Set.Finite.mem_toFinset]
    exact (hBHmem b).1 (Finset.mem_coe.mp hb)
  -- the edges of `H`, presented as pairs
  set P : Finset (Fin n × BVertex n) :=
    (A' ×ˢ BH).filter (fun ab => H.Adj (Sum.inl ab.1) (Sum.inr ab.2)) with hP_def
  have hPmem : ∀ ab : Fin n × BVertex n,
      ab ∈ P ↔ ab.1 ∈ A' ∧ ab.2 ∈ BH ∧ H.Adj (Sum.inl ab.1) (Sum.inr ab.2) := by
    intro ab
    rw [hP_def, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hedges : H.edgeSet.ncard = P.card := by
    have hinj : Function.Injective
        (fun ab : Fin n × BVertex n => s(Sum.inl ab.1, Sum.inr ab.2)) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
        exact Prod.ext h1 h2
      · exact absurd h1 (by simp)
    have himg : H.edgeSet
        = (fun ab : Fin n × BVertex n => s(Sum.inl ab.1, Sum.inr ab.2)) '' (P : Set _) := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        constructor
        · intro he
          rw [Subgraph.mem_edgeSet] at he
          have hs := H.adj_sub he
          rcases u with a | b <;> rcases v with a' | b'
          · exact absurd hs (graphOf_not_adj_inl_inl f a a')
          · refine ⟨(a, b'), ?_, rfl⟩
            rw [Finset.mem_coe, hPmem]
            exact ⟨(hA'mem a).2 (H.edge_vert he), (hBHmem b').2 (H.edge_vert he.symm), he⟩
          · refine ⟨(a', b), ?_, Sym2.eq_swap⟩
            rw [Finset.mem_coe, hPmem]
            exact ⟨(hA'mem a').2 (H.edge_vert he.symm), (hBHmem b).2 (H.edge_vert he), he.symm⟩
          · exact absurd hs (graphOf_not_adj_inr_inr f b b')
        · rintro ⟨ab, hab, heq⟩
          rw [← heq]
          exact ((hPmem ab).1 (Finset.mem_coe.mp hab)).2.2
    rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  -- split the pairs according to the size of the block
  set S : ℝ := (m : ℝ) / (64 * D) with hS_def
  set Bs : Finset (BVertex n) := BH.filter (fun b => ((bsize n b.1 : ℕ) : ℝ) ≤ S) with hBs_def
  set Bl : Finset (BVertex n) := BH.filter (fun b => m * 2 ^ R ≤ bsize n b.1) with hBl_def
  set Ps : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) with hPs_def
  set Pl : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => m * 2 ^ R ≤ bsize n ab.2.1) with hPl_def
  set Pm : Finset (Fin n × BVertex n) :=
    P.filter (fun ab => ¬ (((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) ∧ ¬ (m * 2 ^ R ≤ bsize n ab.2.1))
    with hPm_def
  have hBsmem : ∀ b : BVertex n, b ∈ Bs ↔ b ∈ BH ∧ ((bsize n b.1 : ℕ) : ℝ) ≤ S := by
    intro b
    rw [hBs_def, Finset.mem_filter]
  have hBlmem : ∀ b : BVertex n, b ∈ Bl ↔ b ∈ BH ∧ m * 2 ^ R ≤ bsize n b.1 := by
    intro b
    rw [hBl_def, Finset.mem_filter]
  have hPsmem : ∀ ab : Fin n × BVertex n,
      ab ∈ Ps ↔ ab ∈ P ∧ ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S := by
    intro ab
    rw [hPs_def, Finset.mem_filter]
  have hPlmem : ∀ ab : Fin n × BVertex n,
      ab ∈ Pl ↔ ab ∈ P ∧ m * 2 ^ R ≤ bsize n ab.2.1 := by
    intro ab
    rw [hPl_def, Finset.mem_filter]
  have hPmmem : ∀ ab : Fin n × BVertex n, ab ∈ Pm ↔ ab ∈ P ∧
      ¬ (((bsize n ab.2.1 : ℕ) : ℝ) ≤ S) ∧ ¬ (m * 2 ^ R ≤ bsize n ab.2.1) := by
    intro ab
    rw [hPm_def, Finset.mem_filter]
  have hsplit : P.card ≤ Ps.card + Pm.card + Pl.card := by
    have hsub : P ⊆ Ps ∪ Pm ∪ Pl := by
      intro ab hab
      by_cases h1 : ((bsize n ab.2.1 : ℕ) : ℝ) ≤ S
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hPsmem ab).mpr ⟨hab, h1⟩))
      · by_cases h2 : m * 2 ^ R ≤ bsize n ab.2.1
        · exact Finset.mem_union_right _ ((hPlmem ab).mpr ⟨hab, h2⟩)
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ ((hPmmem ab).mpr ⟨hab, h1, h2⟩))
    calc P.card ≤ (Ps ∪ Pm ∪ Pl).card := Finset.card_le_card hsub
      _ ≤ (Ps ∪ Pm).card + Pl.card := Finset.card_union_le _ _
      _ ≤ Ps.card + Pm.card + Pl.card := by
          have := Finset.card_union_le Ps Pm
          omega
  -- (1) large blocks: goodness of `f`
  have hcrossmem : ∀ (B' : Finset (BVertex n)) (ab : Fin n × BVertex n),
      ab ∈ crossEdges f A' B' ↔ (ab.1 ∈ A' ∧ ab.2 ∈ B') ∧ f ab.1 ab.2.1 = ab.2.2 := by
    intro B' ab
    simp only [crossEdges, Finset.mem_filter, Finset.mem_product]
  have hPlcard : Pl.card ≤ m * R := by
    have hBlcard : Bl.card ≤ m := by
      refine le_trans (Finset.card_le_card ?_) hBHcard
      intro b hb
      exact ((hBlmem b).mp hb).1
    have hBlsub : Bl ⊆ largeB n m := by
      intro b hb
      simp only [largeB, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hR_def]
      exact ((hBlmem b).mp hb).2
    have hPlsub : Pl ⊆ crossEdges f A' Bl := by
      intro ab hab
      obtain ⟨habP, hlarge⟩ := (hPlmem ab).mp hab
      obtain ⟨h1, h2, h3⟩ := (hPmem ab).1 habP
      refine (hcrossmem Bl ab).mpr ⟨⟨h1, (hBlmem ab.2).mpr ⟨h2, hlarge⟩⟩, ?_⟩
      obtain ⟨a, p, c⟩ := ab
      exact (graphOf_adj_inl_inr f a p c).mp (H.adj_sub h3)
    by_cases hmn : m ≤ n
    · exact le_of_lt (lt_of_le_of_lt (Finset.card_le_card hPlsub)
        (hf m hm1 hmn A' hA'card Bl hBlsub hBlcard))
    · have hBlempty : Bl = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        obtain ⟨-, hlarge⟩ := (hBlmem b).mp hb
        have h1 : bsize n b.1 ≤ n := Nat.div_le_self _ _
        have h2 : m * 1 ≤ m * 2 ^ R := Nat.mul_le_mul_left m Nat.one_le_two_pow
        rw [mul_one] at h2
        exact hmn (le_trans (le_trans h2 hlarge) h1)
      have hPlempty : Pl = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ab hab
        have h := (hcrossmem Bl ab).mp (hPlsub hab)
        rw [hBlempty] at h
        exact absurd h.1.2 (Finset.notMem_empty _)
      simp [hPlempty]
  -- (2) middle blocks: few indices, each meeting at most `|A'|` pairs
  set MI : Finset ℕ := (Finset.Icc 4 (top n)).filter
    (fun i => S < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) with hMI_def
  have hMImem : ∀ i : ℕ, i ∈ MI ↔ i ∈ Finset.Icc 4 (top n) ∧
      (S < ((n / 2 ^ i : ℕ) : ℝ) ∧ (n / 2 ^ i : ℕ) < m * 2 ^ R) := by
    intro i
    rw [hMI_def, Finset.mem_filter]
  set MidIdx : Finset (BlockIdx n) :=
    Finset.univ.filter (fun p => (p.1 : ℕ) ∈ MI) with hMid_def
  have hMidmem : ∀ p : BlockIdx n, p ∈ MidIdx ↔ (p.1 : ℕ) ∈ MI := by
    intro p
    rw [hMid_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hPmfib : ∀ ab ∈ Pm, ab.2.1 ∈ MidIdx := by
    intro ab hab
    obtain ⟨-, h1, h2⟩ := (hPmmem ab).mp hab
    exact (hMidmem _).mpr ((hMImem _).mpr ⟨ab.2.1.1.2, not_le.mp h1, not_le.mp h2⟩)
  have hPmcard : Pm.card ≤ MidIdx.card * A'.card := by
    rw [Finset.card_eq_sum_card_fiberwise hPmfib]
    calc ∑ p ∈ MidIdx, (Pm.filter fun ab => ab.2.1 = p).card
        ≤ ∑ _p ∈ MidIdx, A'.card := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          refine Finset.card_le_card_of_injOn Prod.fst (fun ab hab => ?_)
            (fun ab hab ab' hab' hfst => ?_)
          · rw [Finset.mem_coe, Finset.mem_filter] at hab
            exact Finset.mem_coe.mpr ((hPmem ab).1 ((hPmmem ab).mp hab.1).1).1
          · rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
            obtain ⟨habP, hq⟩ := hab
            obtain ⟨habP', hq'⟩ := hab'
            obtain ⟨a, q, c⟩ := ab
            obtain ⟨a', q', c'⟩ := ab'
            have hcc : c = f a q :=
              ((graphOf_adj_inl_inr f a q c).mp
                (H.adj_sub ((hPmem _).1 ((hPmmem _).mp habP).1).2.2)).symm
            have hcc' : c' = f a' q' :=
              ((graphOf_adj_inl_inr f a' q' c').mp
                (H.adj_sub ((hPmem _).1 ((hPmmem _).mp habP').1).2.2)).symm
            have haa : a = a' := hfst
            have hqq : q = q' := hq.trans hq'.symm
            subst hcc
            subst hcc'
            subst haa
            subst hqq
            rfl
      _ = MidIdx.card * A'.card := by rw [Finset.sum_const, smul_eq_mul]
  have hMidcard : MidIdx.card ≤ 8 * MI.card := by
    have hfib : ∀ p ∈ MidIdx, (p.1 : ℕ) ∈ MI := fun p hp => (hMidmem p).mp hp
    rw [Finset.card_eq_sum_card_fiberwise hfib]
    calc ∑ i ∈ MI, (MidIdx.filter fun p => (p.1 : ℕ) = i).card
        ≤ ∑ _i ∈ MI, 8 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hb : (MidIdx.filter fun p => (p.1 : ℕ) = i).card
              ≤ (Finset.univ : Finset (Fin 8)).card := by
            refine Finset.card_le_card_of_injOn Prod.snd
              (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun p hp p' hp' h => ?_)
            rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
            exact Prod.ext (Subtype.ext (hp.2.trans hp'.2.symm)) h
          simpa using hb
      _ = 8 * MI.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hMIcard : (MI.card : ℝ) ≤ (R : ℝ) + Real.logb 2 (64 * D) + 1 := by
    refine card_mid_le n m R hD hm1 MI (fun i hi => ?_)
    obtain ⟨-, h1, h2⟩ := (hMImem i).mp hi
    exact ⟨hS_def ▸ h1, h2⟩
  -- (3) small blocks: few vertices, each of controlled degree
  have hVHne : VH.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := Finset.exists_min_image VH (sdeg H) hVHne
  have hPsfib : ∀ ab ∈ Ps, ab.2 ∈ Bs := by
    intro ab hab
    obtain ⟨habP, hsmall⟩ := (hPsmem ab).mp hab
    exact (hBsmem ab.2).mpr ⟨((hPmem ab).1 habP).2.1, hsmall⟩
  have hPscard : Ps.card ≤ ∑ b ∈ Bs, sdeg H (Sum.inr b) := by
    rw [Finset.card_eq_sum_card_fiberwise hPsfib]
    refine Finset.sum_le_sum (fun b _ => ?_)
    have hfin : (H.neighborSet (Sum.inr b)).Finite := Set.toFinite _
    have hcardeq : sdeg H (Sum.inr b) = hfin.toFinset.card := by
      rw [sdeg, Set.ncard_eq_toFinset_card _ hfin]
    rw [hcardeq]
    refine Finset.card_le_card_of_injOn (fun ab => Sum.inl ab.1) (fun ab hab => ?_)
      (fun ab hab ab' hab' hEq => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hab
      obtain ⟨habPs, habb⟩ := hab
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Subgraph.mem_neighborSet, ← habb]
      exact (((hPmem ab).1 ((hPsmem ab).mp habPs).1).2.2).symm
    · rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
      simp only [Sum.inl.injEq] at hEq
      exact Prod.ext hEq (hab.2.trans hab'.2.symm)
  have hBscard : (Bs.card : ℝ) ≤ (m : ℝ) / (4 * D) := by
    refine card_small_le hD Bs (fun b hb => ?_)
    rw [← hS_def]
    exact ((hBsmem b).mp hb).2
  have hPssmall : (Ps.card : ℝ) ≤ (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ)) := by
    have h1 : (Ps.card : ℝ) ≤ ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := by
      calc (Ps.card : ℝ) ≤ ((∑ b ∈ Bs, sdeg H (Sum.inr b) : ℕ) : ℝ) := by exact_mod_cast hPscard
        _ = ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := by push_cast; rfl
    have h2 : ∀ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) ≤ D * (sdeg H v₀ : ℝ) := by
      intro b hb
      refine hH _ ((hBHmem b).1 ((hBsmem b).mp hb).1) v₀ ?_
      rw [hVH_def, Set.Finite.mem_toFinset] at hv₀mem
      exact hv₀mem
    calc (Ps.card : ℝ) ≤ ∑ b ∈ Bs, ((sdeg H (Sum.inr b) : ℕ) : ℝ) := h1
      _ ≤ ∑ _b ∈ Bs, D * (sdeg H v₀ : ℝ) := Finset.sum_le_sum h2
      _ = (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- (4) the handshake bound
  have hdeg : m * sdeg H v₀ ≤ 2 * H.edgeSet.ncard := by
    have h := Finset.card_nsmul_le_sum VH (sdeg H) (sdeg H v₀) hv₀min
    rw [smul_eq_mul, hVHcard, hVH_def, sum_sdeg H] at h
    exact h
  -- assembly
  have hMnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have he : (H.edgeSet.ncard : ℝ) = (P.card : ℝ) := by rw [hedges]
  have hsplitR : (P.card : ℝ) ≤ (Ps.card : ℝ) + (Pm.card : ℝ) + (Pl.card : ℝ) := by
    exact_mod_cast hsplit
  have hPsR : (Ps.card : ℝ) ≤ (m : ℝ) * (sdeg H v₀ : ℝ) / 4 := by
    have h1 : (Bs.card : ℝ) * (D * (sdeg H v₀ : ℝ))
        ≤ ((m : ℝ) / (4 * D)) * (D * (sdeg H v₀ : ℝ)) :=
      mul_le_mul_of_nonneg_right hBscard (by positivity)
    have h2 : ((m : ℝ) / (4 * D)) * (D * (sdeg H v₀ : ℝ)) = (m : ℝ) * (sdeg H v₀ : ℝ) / 4 := by
      field_simp
    linarith
  have hPmR : (Pm.card : ℝ) ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) * (m : ℝ) := by
    have h1 : (Pm.card : ℝ) ≤ (MidIdx.card : ℝ) * (A'.card : ℝ) := by exact_mod_cast hPmcard
    have h3 : (MidIdx.card : ℝ) ≤ 8 * (MI.card : ℝ) := by exact_mod_cast hMidcard
    have h2 : (MidIdx.card : ℝ) ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) := by linarith
    have h4 : (A'.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hA'card
    have h5 : (MidIdx.card : ℝ) * (A'.card : ℝ)
        ≤ 8 * ((R : ℝ) + Real.logb 2 (64 * D) + 1) * (m : ℝ) :=
      mul_le_mul h2 h4 (Nat.cast_nonneg _) (by positivity)
    linarith
  have hPlR : (Pl.card : ℝ) ≤ (m : ℝ) * (R : ℝ) := by exact_mod_cast hPlcard
  have hdegR : (m : ℝ) * (sdeg H v₀ : ℝ) ≤ 2 * (H.edgeSet.ncard : ℝ) := by exact_mod_cast hdeg
  have hMc : (0 : ℝ) ≤ (m : ℝ) * Real.logb 2 (64 * D) := mul_nonneg hMnn hcnn
  nlinarith [he, hsplitR, hPsR, hPmR, hPlR, hdegR, hMnn, hMc, hRnn]

end

/-! ### Upstream module `Proof/Transfer.lean` -/

section
/-!
# Transfer to `Fin N`

Embedding the vertex type `Vtx n` into `Fin N` (for `N ≥ |Vtx n|`) and mapping the graph along
the embedding gives a graph on `Fin N` with the same number of edges whose extra vertices are
isolated.  A `D`-balanced subgraph `H` of the mapped graph is therefore either edgeless (as soon
as it uses one of the extra, isolated vertices), or it lives inside the image of the embedding and
pulls back to a `D`-balanced subgraph `H'` of the original graph with the same numbers of vertices
and edges.
-/

open _root_.SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {e : V ↪ W} {H : (G.map e).Subgraph}

/-- The pullback of a subgraph of `G.map e` along the embedding `e`. -/
private def pullback (e : V ↪ W) (H : (G.map e).Subgraph) : G.Subgraph where
  verts := e ⁻¹' H.verts
  Adj u v := H.Adj (e u) (e v)
  adj_sub {u v} h := by
    obtain ⟨u', v', hadj, hu, hv⟩ := (SimpleGraph.map_adj e G _ _).mp (H.adj_sub h)
    rwa [e.injective hu, e.injective hv] at hadj
  edge_vert {_ _} h := H.edge_vert h
  symm.symm _ _ h := H.adj_symm h

/-- The `pullback` neighbourhoods are the preimages of the original ones. -/
private theorem pullback_neighborSet (u : V) :
    (pullback e H).neighborSet u = e ⁻¹' H.neighborSet (e u) := rfl

/-- If `H` only uses vertices in the range of `e`, its edge set is the image of the edge set of
the pullback. -/
private theorem pullback_edgeSet (hsub : H.verts ⊆ Set.range e) :
    H.edgeSet = e.sym2Map '' (pullback e H).edgeSet := by
  refine Set.Subset.antisymm (fun s hs ↦ ?_) ?_
  · induction s using Sym2.ind with
    | _ a b =>
      rw [Subgraph.mem_edgeSet] at hs
      obtain ⟨u, rfl⟩ := hsub (H.edge_vert hs)
      obtain ⟨v, rfl⟩ := hsub (H.edge_vert (H.adj_symm hs))
      exact ⟨s(u, v), hs, rfl⟩
  · rintro s ⟨t, ht, rfl⟩
    induction t using Sym2.ind with
    | _ u v => exact ht

/-- If `H` only uses vertices in the range of `e`, degrees are preserved by the pullback. -/
private theorem sdeg_pullback (hsub : H.verts ⊆ Set.range e) (u : V) :
    sdeg (pullback e H) u = sdeg H (e u) := by
  rw [sdeg, sdeg, pullback_neighborSet, Set.ncard_preimage_of_injective_subset_range e.injective
    ((H.neighborSet_subset_verts _).trans hsub)]

/-- A vertex outside the range of `e` is isolated in `G.map e`, hence in every subgraph. -/
private theorem sdeg_eq_zero_of_notMem_range {w : W} (hw : w ∉ Set.range e) : sdeg H w = 0 := by
  have hempty : H.neighborSet w = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨u', _, _, hu', _⟩ := (SimpleGraph.map_adj e G _ _).mp (H.adj_sub hx)
    exact hw ⟨u', hu'⟩
  rw [sdeg, hempty, Set.ncard_empty]

/-- Mapping `graphOf f` along an embedding of `Vtx n` into `Fin N` gives a graph on `Fin N` with
the same number of edges, each of whose `D`-balanced subgraphs is either edgeless or comes from a
`D`-balanced subgraph of `graphOf f` with the same numbers of vertices and edges. -/
theorem exists_graph_fin (n N : ℕ) (hN : Fintype.card (Vtx n) ≤ N) (f : Choice n) :
    ∃ G : SimpleGraph (Fin N), G.edgeSet.ncard = (graphOf f).edgeSet.ncard ∧
      ∀ H : G.Subgraph, ∀ D : ℝ, Balanced D H → H.edgeSet = ∅ ∨
        ∃ H' : (graphOf f).Subgraph, H'.edgeSet.ncard = H.edgeSet.ncard ∧
          H'.verts.ncard = H.verts.ncard ∧ Balanced D H' := by
  classical
  obtain ⟨e⟩ : Nonempty (Vtx n ↪ Fin N) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hN)
  refine ⟨(graphOf f).map e, ?_, fun H D hD ↦ ?_⟩
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ e.sym2Map.injective]
  by_cases hsub : H.verts ⊆ Set.range e
  · refine Or.inr ⟨pullback e H, ?_, ?_, ?_⟩
    · rw [pullback_edgeSet hsub, Set.ncard_image_of_injective _ e.sym2Map.injective]
    · exact Set.ncard_preimage_of_injective_subset_range e.injective hsub
    · intro u hu v hv
      rw [sdeg_pullback hsub, sdeg_pullback hsub]
      exact hD _ hu _ hv
  · obtain ⟨w, hw, hwr⟩ := Set.not_subset.mp hsub
    exact Or.inl (hD.edgeSet_eq_empty_of_sdeg_eq_zero hw (sdeg_eq_zero_of_notMem_range hwr))

end

/-! ### Upstream module `Proof/Main.lean` -/

section
/-!
# Erdős Problem 803: Alon's construction and the negative answer

**Alon (2008), Proposition 2.1.** For every `D ≥ 1` and every sufficiently large `N` there is a
graph on `N` vertices with at least `N log₂ N` edges in which every `D`-balanced subgraph on `m`
vertices has at most `18 m (4 √(log₂ m) + log₂(64 D) + 26)` edges.  (Alon states the average
degree bound `36 (4 √log₂ m + log₂(64 D) + 18)`; our integer threshold `rpar` costs a slightly
larger additive constant.)

Consequently the Erdős–Simonovits question has a negative answer: there are no absolute constants
`ε > 0`, `D` such that all large graphs with `n log₂ n` edges contain a `D`-balanced subgraph on
`m` (or at least `m₀`) vertices with `ε m log₂ m` edges.
-/

open _root_.SimpleGraph

/-- The construction on `Vtx n` has enough edges: `N log₂ N ≤ n · 8 (top n + 1 - 4)` whenever
`2 ^ 40 ≤ n` and `N ≤ 2 n + 1`. -/
private theorem le_edge_count (n N : ℕ) (hn : 2 ^ 40 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 2 * n + 1) :
    (N : ℝ) * Real.logb 2 N ≤ ((n * (8 * (top n + 1 - 4)) : ℕ) : ℝ) := by
  have hn' : (1099511627776 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (1099511627776 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
  have hL40 : 40 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) hn0).2 hn
  have htop : top n = Nat.log 2 n / 2 := rfl
  obtain ⟨t, ht⟩ : ∃ t : ℕ, top n = t + 4 := ⟨top n - 4, by rw [htop] at *; omega⟩
  have hLt : Nat.log 2 n ≤ 2 * t + 9 := by rw [htop] at ht; omega
  have hLtR : (Nat.log 2 n : ℝ) ≤ 2 * (t : ℝ) + 9 := by exact_mod_cast hLt
  have hLnR : (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.log_le_self 2 n
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx_lt : Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1 := by
    have hfl : ⌊Real.logb ((2 : ℕ) : ℝ) ((n : ℕ) : ℝ)⌋₊ = Nat.log 2 n :=
      Real.natFloor_logb_natCast 2 n
    have hlt := Nat.lt_floor_add_one (Real.logb ((2 : ℕ) : ℝ) ((n : ℕ) : ℝ))
    rw [hfl] at hlt
    simpa using hlt
  have hx40 : (40 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos,
      show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hn
  have hlog4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.logb_mul two_ne_zero two_ne_zero,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hNR : (N : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogN : Real.logb 2 (N : ℝ) ≤ Real.logb 2 (n : ℝ) + 2 := by
    calc Real.logb 2 (N : ℝ) ≤ Real.logb 2 (4 * (n : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) hNpos (by linarith)
      _ = Real.logb 2 4 + Real.logb 2 (n : ℝ) :=
          Real.logb_mul (by norm_num) (ne_of_gt hnpos)
      _ = Real.logb 2 (n : ℝ) + 2 := by rw [hlog4]; ring
  have hlogNnn : (0 : ℝ) ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hN1)
  have hstep : (N : ℝ) * Real.logb 2 (N : ℝ) ≤ (2 * (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 2) :=
    mul_le_mul hNR hlogN hlogNnn (by linarith)
  have hgoal : (2 * (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 2) ≤ (n : ℝ) * (8 * ((t : ℝ) + 1)) := by
    nlinarith [mul_nonneg hnpos.le (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ) + 10 - Real.logb 2 (n : ℝ)),
      mul_nonneg hnpos.le (by linarith : (0 : ℝ) ≤ Real.logb 2 (n : ℝ) - 40)]
  have hcast : ((n * (8 * (top n + 1 - 4)) : ℕ) : ℝ) = (n : ℝ) * (8 * ((t : ℝ) + 1)) := by
    rw [show n * (8 * (top n + 1 - 4)) = n * (8 * (t + 1)) by
      rw [ht, show t + 4 + 1 - 4 = t + 1 from by omega]]
    push_cast
    ring
  rw [hcast]
  linarith

/-- For a fixed constant `C ≥ 0` the bound `72 √T + 18 C + 468` is eventually beaten by `ε T`. -/
private theorem exists_threshold (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → 72 * Real.sqrt T + 18 * C + 468 < ε * T := by
  refine ⟨((540 + 18 * C) / ε + 1) ^ 2 + 1, fun T hT ↦ ?_⟩
  have hq : 0 ≤ (540 + 18 * C) / ε := by positivity
  have hb : (0 : ℝ) ≤ (540 + 18 * C) / ε + 1 := by linarith
  have hTpos : (0 : ℝ) < T := by nlinarith [sq_nonneg ((540 + 18 * C) / ε + 1)]
  have hs : (540 + 18 * C) / ε + 1 ≤ Real.sqrt T := by
    calc (540 + 18 * C) / ε + 1 = Real.sqrt (((540 + 18 * C) / ε + 1) ^ 2) :=
          (Real.sqrt_sq hb).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  have hs1 : (1 : ℝ) ≤ Real.sqrt T := by linarith
  have hKs : 540 + 18 * C + ε ≤ ε * Real.sqrt T := by
    have h := mul_le_mul_of_nonneg_left hs hε.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hε)] at h
    linarith
  have hTT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
  nlinarith [mul_le_mul_of_nonneg_right hKs (by linarith : (0 : ℝ) ≤ Real.sqrt T),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 468 + 18 * C) (by linarith : (0 : ℝ) ≤ Real.sqrt T - 1),
    mul_pos hε (lt_of_lt_of_le zero_lt_one hs1)]

/-- **Alon's construction** (Erdős Problem 803, negative direction). -/
theorem alon_construction (D : ℝ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ G : SimpleGraph (Fin N),
      (N : ℝ) * Real.logb 2 N ≤ G.edgeSet.ncard ∧
        ∀ H : G.Subgraph, Balanced D H →
          (H.edgeSet.ncard : ℝ) ≤ 18 * H.verts.ncard *
            (4 * Real.sqrt (Real.logb 2 H.verts.ncard) + Real.logb 2 (64 * D) + 26) := by
  have hlogD : (0 : ℝ) ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by linarith)
  refine ⟨2 ^ 41, fun N hN ↦ ?_⟩
  have hN' : (2199023255552 : ℕ) ≤ N := le_trans (by norm_num) hN
  have hn : 2 ^ 40 ≤ N / 2 := le_trans (by norm_num) (by omega : (1099511627776 : ℕ) ≤ N / 2)
  obtain ⟨f, hf⟩ := exists_good (N / 2) hn
  have hcard : Fintype.card (Vtx (N / 2)) ≤ N := le_trans (card_vtx_le (N / 2)) (by omega)
  obtain ⟨G, hG, hsub⟩ := exists_graph_fin (N / 2) N hcard f
  refine ⟨G, ?_, fun H hH ↦ ?_⟩
  · rw [hG, edgeSet_ncard_graphOf, card_blockIdx]
    exact le_edge_count (N / 2) N hn (by omega) (by omega)
  · rcases hsub H D hH with hemp | ⟨H', he, hv, hH'⟩
    · rw [hemp, Set.ncard_empty]
      have h2 : (0 : ℝ) ≤ Real.sqrt (Real.logb 2 H.verts.ncard) := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) ≤ (H.verts.ncard : ℝ) := Nat.cast_nonneg _
      simp only [Nat.cast_zero]
      nlinarith
    · rw [← he, ← hv]
      have hmain := edges_le_of_good hf hn hD H' hH'
      rcases Nat.eq_zero_or_pos H'.verts.ncard with h0 | h0
      · rw [h0] at hmain ⊢
        simp only [Nat.cast_zero, mul_zero, zero_mul] at hmain ⊢
        exact hmain
      · have hr := rpar_le H'.verts.ncard h0
        have hmR : (0 : ℝ) ≤ (H'.verts.ncard : ℝ) := Nat.cast_nonneg _
        nlinarith

/-- The uniform Erdős–Simonovits statement is false for every choice of constants. -/
theorem not_erdosSimonovitsUniform :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsUniform ε D := by
  rintro ⟨ε, D, hε, hD, h⟩
  have hD'1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have hDD' : D ≤ max D 1 := le_max_left _ _
  have hC : (0 : ℝ) ≤ Real.logb 2 (64 * max D 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  obtain ⟨T₀, hT₀⟩ := exists_threshold ε (Real.logb 2 (64 * max D 1)) hε hC
  obtain ⟨N₀, hN₀⟩ := alon_construction (max D 1) hD'1
  obtain ⟨n₀, hn₀⟩ := h (⌈(2 : ℝ) ^ T₀⌉₊ + 2)
  obtain ⟨G, hGedge, hGsub⟩ := hN₀ (max N₀ n₀) (le_max_left _ _)
  obtain ⟨H, hHcard, hHbal, hHedge⟩ := hn₀ (max N₀ n₀) (le_max_right _ _) G hGedge
  have hmpos : (0 : ℝ) < (H.verts.ncard : ℝ) := by
    have : 0 < H.verts.ncard := by omega
    exact_mod_cast this
  have hTm : T₀ ≤ Real.logb 2 H.verts.ncard := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hmpos]
    calc (2 : ℝ) ^ T₀ ≤ (⌈(2 : ℝ) ^ T₀⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (H.verts.ncard : ℝ) := by exact_mod_cast (by omega : ⌈(2 : ℝ) ^ T₀⌉₊ ≤ H.verts.ncard)
  have hthr := hT₀ (Real.logb 2 H.verts.ncard) hTm
  have hbnd := hGsub H (Balanced.mono hDD' hHbal)
  nlinarith [mul_lt_mul_of_pos_left hthr hmpos]

/-- The literal Erdős–Simonovits statement is false for every choice of constants. -/
theorem erdos_803 :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsLiteral ε D := by
  rintro ⟨ε, D, hε, hD, h⟩
  exact not_erdosSimonovitsUniform ⟨ε, D, hε, hD, h.uniform⟩

end

#print axioms erdos_803
-- 'Erdos803.erdos_803' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos803
