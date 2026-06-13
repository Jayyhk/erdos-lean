import Mathlib

namespace Erdos426

noncomputable section

/-! ==================================================================
    Core Definitions and Burnside Machinery
    (originally MainDefs.lean)
    ================================================================== -/

open Finset Function SimpleGraph
open scoped Classical

/-!
# Core Definitions and Burnside Machinery for Unique Subgraphs

Extracted from Main.lean to break the circular dependency with PolyaWright.lean.
Contains all definitions, basic properties, the group action, and Burnside-related
theorems needed by both Main.lean and PolyaWright.lean.
-/


open Finset Function SimpleGraph
open scoped Classical

namespace UniqueSubgraphs

/-! ## Core Definitions -/

/-! ### Isomorphism of graphs -/

/-- The isomorphism equivalence relation on SimpleGraph (Fin n). -/
instance graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G₁ G₂ := Nonempty (G₁.Iso G₂)
  iseqv := {
    refl := fun _ => ⟨Iso.refl⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

/-- The number of isomorphism classes of graphs on Fin n. -/
def numIsoClasses (n : ℕ) : ℕ :=
  Fintype.card (Quotient (graphIsoSetoid n))

/-! ### Paper's normalization constant -/

/-- The normalization constant 2^{n choose 2} / n! from the paper.
    This is the asymptotic count of unlabeled graphs on n vertices (Pólya's theorem). -/
def paperDenom (n : ℕ) : ℝ :=
  (2 ^ n.choose 2 : ℝ) / (Nat.factorial n : ℝ)

def IsUniqueSubgraph {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃! S : H.Subgraph, S.IsSpanning ∧ Nonempty (S.spanningCoe.Iso G)

def uniqueSubgraphClasses {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Quotient (graphIsoSetoid n)) :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsUniqueSubgraph G H)).image
    (Quotient.mk (graphIsoSetoid n))

/-- f(H): the fraction of isomorphism classes that appear as unique subgraphs of H,
    normalized by the paper's denominator 2^{n choose 2} / n!. -/
def fH {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  ((uniqueSubgraphClasses H).card : ℝ) / paperDenom n

/-- f(n): the maximum of f(H) over all n-vertex graphs H. -/
def fSeq (n : ℕ) : ℝ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup' ⟨⊥, mem_univ _⟩ fH

/-! ### Embeddings (auxiliary, used in proofs) -/

/-- An embedding of G into H is a permutation φ of Fin n
    such that every edge of G maps to an edge of H under φ. -/
def IsEmbedding {n : ℕ} (G H : SimpleGraph (Fin n)) (φ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → H.Adj (φ u) (φ v)

/-- The set of all embeddings of G into H. -/
def embeddingFinset {n : ℕ} (G H : SimpleGraph (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (IsEmbedding G H)

/-- The number of embeddings of G into H. -/
def numEmbeddings {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ :=
  (embeddingFinset G H).card

/-- G uniquely embeds into H: there is exactly one embedding (permutation). -/
def UniquelyEmbeds {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  numEmbeddings G H = 1

/-- The automorphism set of G. -/
def autFinset {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun φ => ∀ u v : Fin n, G.Adj u v ↔ G.Adj (φ u) (φ v))

/-- The number of labelled graphs G on Fin n that uniquely embed into H. -/
def numUniquelyEmbedding {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H)).card

/-- The probability that a uniformly random labelled graph uniquely embeds into H. -/
def probUniqueEmb {n : ℕ} (H : SimpleGraph (Fin n)) : ℝ :=
  (numUniquelyEmbedding H : ℝ) / (2 ^ (n.choose 2) : ℝ)

/-! ## Basic Properties -/

theorem id_mem_autFinset {n : ℕ} (G : SimpleGraph (Fin n)) :
    (1 : Equiv.Perm (Fin n)) ∈ autFinset G := by
  simp [autFinset]


theorem autFinset_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    (autFinset G).Nonempty :=
  ⟨_, id_mem_autFinset G⟩


theorem probUniqueEmb_le_one {n : ℕ} (H : SimpleGraph (Fin n)) :
    probUniqueEmb H ≤ 1 := by
  have h_card_le : numUniquelyEmbedding H ≤ 2 ^ (n.choose 2) := by
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun s : Finset ( Sym2 ( Fin n ) ) => SimpleGraph.fromEdgeSet ( s.filter fun e => ¬e.IsDiag ) ) ( Finset.powerset ( Finset.univ.filter fun e => ¬e.IsDiag ) );
    · intro G hG;
      simp +zetaDelta at *;
      refine' ⟨ Finset.filter ( fun e => e ∈ G.edgeSet ) ( Finset.univ.filter fun e => ¬e.IsDiag ), _, _ ⟩ <;> aesop;
    · refine' Finset.card_image_le.trans _;
      rw [ show Finset.filter ( fun e => ¬e.IsDiag ) Finset.univ = Finset.univ \ Finset.image ( fun i => Sym2.mk ( i, i ) ) Finset.univ from ?_, Finset.card_powerset, Finset.card_sdiff ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
      · rw [ Sym2.card ];
        simp +arith +decide [ Nat.choose_succ_succ ];
      · ext ⟨ i, j ⟩ ; aesop;
  exact div_le_one_of_le₀ ( mod_cast h_card_le ) ( by positivity )


theorem every_perm_embeds_into_top {n : ℕ} (G : SimpleGraph (Fin n))
    (φ : Equiv.Perm (Fin n)) : IsEmbedding G ⊤ φ := by
  intro u v huv
  rw [SimpleGraph.top_adj]
  exact fun h => (G.ne_of_adj huv) (φ.injective h)

theorem embeddingFinset_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    embeddingFinset G ⊤ = Finset.univ := by
  ext φ
  simp [embeddingFinset, every_perm_embeds_into_top G φ]

theorem numEmbeddings_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    numEmbeddings G ⊤ = Nat.factorial n := by
  simp [numEmbeddings, embeddingFinset_top, Fintype.card_perm]

instance permGraphMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  smul σ G := {
    Adj := fun u v => G.Adj (σ⁻¹ u) (σ⁻¹ v)
    symm := fun {_} {_} h => G.symm h
    loopless := ⟨fun v h => G.loopless.irrefl (σ⁻¹ v) h⟩
  }
  one_smul G := by
    ext u v
    change G.Adj ((1 : Equiv.Perm (Fin n))⁻¹ u) ((1 : Equiv.Perm (Fin n))⁻¹ v) ↔ _
    simp
  mul_smul σ τ G := by
    ext u v
    change G.Adj ((σ * τ)⁻¹ u) ((σ * τ)⁻¹ v) ↔ G.Adj (τ⁻¹ (σ⁻¹ u)) (τ⁻¹ (σ⁻¹ v))
    simp [mul_inv_rev, Equiv.Perm.mul_apply]

@[simp] theorem smul_adj {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (u v : Fin n) : (σ • G).Adj u v ↔ G.Adj (σ⁻¹ u) (σ⁻¹ v) := Iff.rfl



/-! ### Connecting MulAction to autFinset and graphIsoSetoid -/

/-
The orbit relation for the Perm action on SimpleGraph equals
    the graph isomorphism equivalence relation.
-/
theorem orbitRel_eq_graphIsoSetoid (n : ℕ) :
    MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) = graphIsoSetoid n := by
  ext G H;
  constructor;
  · rintro ⟨ σ, rfl ⟩;
    refine' ⟨ _, _ ⟩;
    exacts [ σ⁻¹, by simp +decide [ SimpleGraph.adj_comm ] ];
  · rintro ⟨ f ⟩;
    use f.toEquiv.symm;
    ext u v; simp +decide [ f.map_adj_iff ] ;

/-
σ fixes G under the action iff σ⁻¹ is an automorphism of G.
-/
theorem mem_fixedBy_iff_inv_mem_autFinset {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) :
    G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ ↔ σ⁻¹ ∈ autFinset G := by
  simp +decide [ MulAction.mem_fixedBy, autFinset ];
  constructor;
  · intro h u v; replace h := congr_arg ( fun G => G.Adj u v ) h; aesop;
  · intro h; ext u v; simp +decide [ h u v, SimpleGraph.adj_comm ] ;

/-
autFinset is closed under inversion.
-/
theorem autFinset_inv_mem {n : ℕ} {G : SimpleGraph (Fin n)} {σ : Equiv.Perm (Fin n)}
    (h : σ ∈ autFinset G) : σ⁻¹ ∈ autFinset G := by
  unfold autFinset at *;
  simp +zetaDelta at *;
  grind

/-
σ fixes G iff σ is an automorphism.
-/
theorem mem_fixedBy_iff_mem_autFinset {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) :
    G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ ↔ σ ∈ autFinset G := by
  constructor;
  · intro h;
    convert autFinset_inv_mem _;
    exact inv_eq_iff_eq_inv.mp rfl;
    exact (mem_fixedBy_iff_inv_mem_autFinset σ G).mp h;
  · grind +suggestions

/-
The number of orbits of Perm on SimpleGraph equals numIsoClasses.
-/
theorem card_orbits_eq_numIsoClasses (n : ℕ) :
    Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)))) =
    numIsoClasses n := by
  have h_orbitRel_eq_graphIsoSetoid : MulAction.orbitRel (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) = graphIsoSetoid n := by
    exact orbitRel_eq_graphIsoSetoid n;
  rw [ h_orbitRel_eq_graphIsoSetoid ];
  rfl

/-
Burnside's lemma applied to this action:
    Σ_σ |Fix(σ)| = numIsoClasses(n) * n!
-/
theorem burnside_applied (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) =
    numIsoClasses n * Nat.factorial n := by
  convert MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ( Equiv.Perm ( Fin n ) ) ( SimpleGraph ( Fin n ) ) using 1;
  rw [ card_orbits_eq_numIsoClasses, Fintype.card_perm ];
  norm_num

/-
Double counting: Σ_σ |Fix(σ)| = Σ_G |Aut(G)|
-/
theorem sum_fixedBy_eq_sum_autFinset (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        G ∈ MulAction.fixedBy (SimpleGraph (Fin n)) σ)).card =
    ∑ G : SimpleGraph (Fin n), (autFinset G).card := by
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ];
  congr! 2;
  convert Finset.card_filter ( fun σ : Equiv.Perm ( Fin n ) => σ ∈ autFinset _ ) Finset.univ using 2;
  any_goals exact ‹SimpleGraph ( Fin n ) ›;
  · rw [ Finset.card_filter ];
    congr! 2;
    exact?;
  · simp +decide [ Fintype.card_subtype ]

/-
Combined: Σ_G |Aut(G)| = numIsoClasses(n) * n!
-/
theorem sum_autFinset_eq (n : ℕ) :
    (∑ G : SimpleGraph (Fin n), (autFinset G).card : ℕ) =
    numIsoClasses n * Nat.factorial n := by
  convert burnside_applied n;
  convert sum_fixedBy_eq_sum_autFinset n |> Eq.symm using 1;
  simp +decide [ Fintype.card_subtype ]

theorem card_simpleGraph (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  have h_bij : Fintype.card (SimpleGraph (Fin n)) = Fintype.card {s : Finset (Fin n × Fin n) | ∀ x y, (x, y) ∈ s → x < y} := by
    refine' Fintype.card_congr _;
    refine' Equiv.ofBijective ( fun G => ⟨ Finset.filter ( fun p => G.Adj p.1 p.2 ) ( Finset.univ.filter fun p => p.1 < p.2 ), _ ⟩ ) ⟨ _, _ ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    · aesop;
    · intro G₁ G₂ h; ext u v; by_cases hu : u < v <;> by_cases hv : v < u <;> simp_all +decide [ Finset.ext_iff, SimpleGraph.adj_comm ] ;
      · simpa [ SimpleGraph.adj_comm ] using h v u hv;
      · simp_all +decide [ le_antisymm hv hu ];
    · intro a ha;
      refine' ⟨ SimpleGraph.mk fun x y => x < y ∧ ( x, y ) ∈ a ∨ y < x ∧ ( y, x ) ∈ a, _ ⟩;
      grind;
  -- The number of subsets of the set of pairs (x, y) with x < y is 2^(n choose 2).
  have h_subsets : Fintype.card {s : Finset (Fin n × Fin n) | ∀ x y, (x, y) ∈ s → x < y} = 2 ^ (Finset.card (Finset.filter (fun p => p.1 < p.2) (Finset.univ : Finset (Fin n × Fin n)))) := by
    rw [ Fintype.card_of_subtype ];
    case s => exact Finset.powerset ( Finset.filter ( fun p => p.1 < p.2 ) ( Finset.univ : Finset ( Fin n × Fin n ) ) );
    · rw [ Finset.card_powerset ];
    · grind;
  convert h_bij.trans h_subsets using 2;
  rw [ Nat.choose_two_right, Finset.card_filter ];
  erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite ];
  rw [ ← Finset.sum_range_id ];
  simp +decide [ Finset.filter_lt_eq_Ioi ];
  rw [ ← Finset.sum_range_reflect, Finset.sum_range ]

end UniqueSubgraphs

/-! ==================================================================
    Helper Lemmas (EdgeSlot, graph encoding, low-degree set)
    (originally Helpers.lean)
    ================================================================== -/

/-!
# Helper Lemmas for Unique Subgraphs Are Rare

Sorry-free infrastructure supporting the proof of `per_perm_switch_bound`
and `reduction_to_dense` in the main formalization.
-/

open Finset Function SimpleGraph
open scoped Classical

namespace UniqueSubgraphs

/-! ## Graph ↔ Bool Bijection

The canonical bijection `SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool)`,
encoding each graph by its edge indicator function on ordered pairs `(i,j)` with `i < j`.
-/

/-- The set of "edge slots": pairs (i,j) with i < j in Fin n.
    These represent potential edges in a simple graph on Fin n. -/
def EdgeSlot (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

instance edgeSlotFintype (n : ℕ) : Fintype (EdgeSlot n) := Subtype.fintype _
instance edgeSlotDecidableEq (n : ℕ) : DecidableEq (EdgeSlot n) := Subtype.instDecidableEq

/-- The cardinality of edge slots equals n choose 2. -/
theorem card_edgeSlot (n : ℕ) : Fintype.card (EdgeSlot n) = n.choose 2 := by
  have h_comb : Finset.card (Finset.filter (fun p => p.1 < p.2) (Finset.univ : Finset (Fin n × Fin n))) = Nat.choose n 2 := by
    rw [ Nat.choose_two_right, Finset.card_filter ]
    convert Finset.sum_range_id n using 1
    erw [ Finset.sum_product ]
    simp +decide [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ]
    rw [ ← Finset.sum_range_reflect, Finset.sum_range ]
  convert h_comb using 1
  convert Fintype.card_subtype _
  infer_instance

/-- Encode a simple graph as a Boolean function on edge slots. -/
def graphEncode {n : ℕ} (G : SimpleGraph (Fin n)) : EdgeSlot n → Bool :=
  fun ⟨⟨i, j⟩, _⟩ => decide (G.Adj i j)

/-- Decode a Boolean function on edge slots into a simple graph. -/
def graphDecode {n : ℕ} (f : EdgeSlot n → Bool) : SimpleGraph (Fin n) where
  Adj i j :=
    if h : i < j then f ⟨⟨i, j⟩, h⟩ = true
    else if h' : j < i then f ⟨⟨j, i⟩, h'⟩ = true
    else False
  symm := by
    intro i j hij
    show (if h : j < i then _ else if h' : i < j then _ else _)
    by_cases h1 : i < j <;> by_cases h2 : j < i <;> simp_all; omega
  loopless := by
    constructor; intro i
    show ¬ (if h : i < i then _ else if h' : i < i then _ else _)
    simp

/-- The graph encoding is a bijection between SimpleGraph (Fin n) and (EdgeSlot n → Bool). -/
def graphEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool) where
  toFun := graphEncode
  invFun := graphDecode
  left_inv G := by
    ext i j
    simp only [graphEncode, graphDecode]
    by_cases h1 : i < j
    · simp [h1, decide_eq_true_eq]
    · by_cases h2 : j < i
      · simp [h1, h2, decide_eq_true_eq, G.adj_comm]
      · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hij; simp [SimpleGraph.irrefl]
  right_inv f := by
    ext ⟨⟨i, j⟩, h⟩
    simp only [graphEncode, graphDecode, h, dite_true]
    simp

/-- Key property: the encoding preserves the uniform counting measure.
    Since graphEquiv is a bijection, #{G : P(G)} = #{x : P(graphDecode x)}. -/
theorem graphEquiv_card_filter {n : ℕ} (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
    (Finset.univ.filter (fun x : EdgeSlot n → Bool => P (graphDecode x))).card := by
  apply Finset.card_bij (fun G _ => graphEncode G)
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    have : graphDecode (graphEncode G) = G := (graphEquiv n).left_inv G
    rw [this]; exact hG
  · intro _ _ _ _ h; exact (graphEquiv n).injective h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact ⟨graphDecode f, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hf,
      (graphEquiv n).right_inv f⟩

/-! ## Low-Degree Set Infrastructure -/

/-
In a graph with at most C*n edges, at least n/2 vertices have degree ≤ 4*C.
    Proof: by the handshaking lemma, Σ deg(v) = 2*e ≤ 2*C*n. At most n/2 vertices
    can have degree > 4*C (otherwise the sum exceeds n/2 * 4*C + 0 = 2*C*n).
-/
lemma low_degree_set_large {n : ℕ} (C : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.edgeFinset.card ≤ C * n) :
    n / 2 ≤ (Finset.univ.filter (fun v : Fin n => G.degree v ≤ 4 * C)).card := by
  have h_sum_degrees : ∑ v : Fin n, G.degree v ≤ 2 * C * n := by
    rw [ SimpleGraph.sum_degrees_eq_twice_card_edges ] ; linarith;
  -- Let $H$ be the set of high-degree vertices, i.e., vertices with degree greater than $4C$.
  set H := Finset.filter (fun v => G.degree v > 4 * C) (Finset.univ : Finset (Fin n)) with hH_def;
  -- Then $|H| * (4C + 1) \leq \sum_{v \in H} \deg(v) \leq \sum_{v} \deg(v) \leq 2Cn$.
  have h_card_H : H.card * (4 * C + 1) ≤ 2 * C * n := by
    exact le_trans ( by simpa using Finset.sum_le_sum fun v ( hv : v ∈ H ) => Nat.succ_le_of_lt <| Finset.mem_filter.mp hv |>.2 ) ( h_sum_degrees.trans' <| Finset.sum_le_sum_of_subset <| Finset.filter_subset _ _ );
  rw [ show ( Finset.filter ( fun v => G.degree v ≤ 4 * C ) Finset.univ ) = Finset.univ \ H by ext; aesop, Finset.card_sdiff ] ; norm_num;
  exact Nat.le_sub_of_add_le ( by nlinarith [ Nat.div_mul_le_self n 2 ] )

/-! ## Switch Condition Properties -/

def IsIdSwitch {n : ℕ} (Hc G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  (∀ w : Fin n, Hc.Adj u w → ¬Hc.Adj v w → G.Adj v w) ∧
  (∀ w : Fin n, Hc.Adj v w → ¬Hc.Adj u w → G.Adj u w)

instance isIdSwitchDecidable {n : ℕ} (Hc G : SimpleGraph (Fin n)) (u v : Fin n) :
    Decidable (IsIdSwitch Hc G u v) := by
  unfold IsIdSwitch; infer_instance

/-- The asymmetric neighbourhood of u relative to v. -/
def asymNbhd {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w)

lemma asymNbhd_card_le_degree {n : ℕ} (Hc : SimpleGraph (Fin n))
    (u v : Fin n) :
    (asymNbhd Hc u v).card ≤ Hc.degree u := by
  apply Finset.card_le_card
  intro w hw
  simp [asymNbhd, SimpleGraph.degree, SimpleGraph.neighborFinset] at hw ⊢
  exact hw.1

/-! ## Switch Probability for a Pair -/

set_option maxHeartbeats 800000 in
/-- For non-adjacent vertices u,v with degree ≤ d in Hc,
    the number of graphs G satisfying IsIdSwitch Hc G u v
    is at least 2^(n.choose 2 - 2*d). -/
lemma switch_pair_count_lower {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : u ≠ v) (hnadj : ¬Hc.Adj u v) (d : ℕ)
    (hdu : Hc.degree u ≤ d) (hdv : Hc.degree v ≤ d)
    (hdn : 2 * d ≤ n.choose 2) :
    2 ^ (n.choose 2 - 2 * d) ≤
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G u v)).card := by
  have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => (∀ w : Fin n, Hc.Adj u w → ¬Hc.Adj v w → G.Adj v w) ∧ (∀ w : Fin n, Hc.Adj v w → ¬Hc.Adj u w → G.Adj u w)) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ))) := by
    have h_edges : ∀ (S : Finset (Sym2 (Fin n))), S ⊆ Finset.univ.filter (fun e => e.IsDiag = false) → Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - S.card) := by
      intros S hS
      have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) = 2 ^ (Finset.card (Finset.univ.filter (fun e => e.IsDiag = false) \ S)) := by
        have h_edges : Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ S, e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n))) = Finset.image (fun T : Finset (Sym2 (Fin n)) => SimpleGraph.fromEdgeSet (S ∪ T)) (Finset.powerset (Finset.univ.filter (fun e => e.IsDiag = false) \ S)) := by
          ext G; simp [Finset.mem_image];
          constructor;
          · intro hG; use Finset.filter ( fun e => e ∈ G.edgeSet ) ( Finset.univ.filter ( fun e => ¬e.IsDiag ) \ S ) ; simp_all +decide [ Finset.subset_iff ] ;
            ext v w; simp +decide [ SimpleGraph.fromEdgeSet ] ;
            by_cases hvw : v = w <;> by_cases h : s(v, w) ∈ S <;> simp_all +decide [ SimpleGraph.adj_comm ];
            exact?;
          · rintro ⟨ T, hT, rfl ⟩ e he; simp_all +decide [ Finset.subset_iff ] ;
        rw [ h_edges, Finset.card_image_of_injOn, Finset.card_powerset ];
        · simp +decide [ Finset.ext_iff ];
        · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
          intro e; replace h_eq := congr_arg ( fun f => f.edgeSet ) h_eq; simp_all +decide [ Set.ext_iff ] ;
          specialize h_eq e; replace hT := @hT e; replace hT' := @hT' e; aesop;
      rw [ h_edges, Finset.card_sdiff ];
      gcongr;
      · norm_num;
      · have h_card : Finset.card (Finset.filter (fun e => e.IsDiag = false) (Finset.univ : Finset (Sym2 (Fin n)))) = Finset.card (Finset.powersetCard 2 (Finset.univ : Finset (Fin n))) := by
          refine' Finset.card_bij ( fun e he => Finset.filter ( fun x => x ∈ e ) Finset.univ ) _ _ _ <;> simp +decide [ Finset.mem_powersetCard ];
          · intro a ha; rw [ Finset.card_eq_two ] ;
            rcases a with ⟨ x, y ⟩ ; use x, y ; aesop;
          · simp +contextual [ Finset.ext_iff, Sym2.ext_iff ];
          · intro b hb; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb; use Sym2.mk ( x, y ) ; aesop;
        aesop;
      · exact Finset.inter_subset_left;
    have h_edges : Finset.card (Finset.filter (fun G : SimpleGraph (Fin n) => ∀ e ∈ Finset.image (fun w => Sym2.mk (v, w)) (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) ∪ Finset.image (fun w => Sym2.mk (u, w)) (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ), e ∈ G.edgeSet) (Finset.univ : Finset (SimpleGraph (Fin n)))) ≥ 2 ^ (Nat.choose n 2 - (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ))) := by
      refine le_trans ?_ ( h_edges _ ?_ );
      · rw [ Finset.card_union_of_disjoint ];
        · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          · grind;
          · grind;
        · simp +decide [ Finset.disjoint_left, Sym2.eq ];
          rintro _ x hx₁ hx₂ rfl y hy₁ hy₂; contrapose! hnadj; aesop;
      · simp +decide [ Finset.subset_iff ];
        rintro _ ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp +decide [ *, Sym2.eq_swap ];
        · grind;
        · rintro rfl; tauto;
    refine le_trans h_edges ?_;
    refine Finset.card_mono ?_;
    simp +contextual [ Finset.subset_iff, Sym2.forall ];
    exact fun G hG => ⟨ fun w hw₁ hw₂ => hG _ _ <| Or.inl ⟨ w, ⟨ hw₁, hw₂ ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩, fun w hw₁ hw₂ => hG _ _ <| Or.inr ⟨ w, ⟨ hw₁, hw₂ ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩ ⟩;
  have h_constrained_edges : (Finset.card (Finset.filter (fun w => Hc.Adj u w ∧ ¬Hc.Adj v w) Finset.univ) + Finset.card (Finset.filter (fun w => Hc.Adj v w ∧ ¬Hc.Adj u w) Finset.univ)) ≤ 2 * d := by
    linarith [ asymNbhd_card_le_degree Hc u v, asymNbhd_card_le_degree Hc v u, show Finset.card ( Finset.filter ( fun w => Hc.Adj u w ∧ ¬Hc.Adj v w ) Finset.univ ) ≤ Hc.degree u from by simpa [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] using Finset.card_le_card fun x hx => by aesop, show Finset.card ( Finset.filter ( fun w => Hc.Adj v w ∧ ¬Hc.Adj u w ) Finset.univ ) ≤ Hc.degree v from by simpa [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] using Finset.card_le_card fun x hx => by aesop ];
  exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_left h_constrained_edges _ ) ) h_edges

/-! ## Greedy Independent Set -/

/-- In a graph where a set S of vertices all have degree ≤ d,
    there exists an independent set of size ≥ |S| / (d+1). -/
lemma greedy_independent_set {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (d : ℕ)
    (hdeg : ∀ v ∈ S, G.degree v ≤ d) :
    ∃ I : Finset (Fin n), I ⊆ S ∧
    (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v) ∧
    S.card ≤ I.card * (d + 1) := by
  induction' S using Finset.strongInduction with S ih;
  by_cases hS : S = ∅;
  · aesop;
  · obtain ⟨v, hv⟩ : ∃ v ∈ S, True := by
      exact Exists.elim ( Finset.nonempty_of_ne_empty hS ) fun v hv => ⟨ v, hv, trivial ⟩;
    have := ih ( S \ ( { v } ∪ G.neighborFinset v ) ) ?_ ?_;
    · obtain ⟨ I, hI₁, hI₂, hI₃ ⟩ := this; use Insert.insert v I; simp_all +decide [ Finset.subset_iff ] ;
      rw [ Finset.card_sdiff ] at hI₃ ; simp_all +decide [ Finset.subset_iff ];
      exact ⟨ fun u hu => by have := hI₁ hu; tauto, by rw [ Finset.card_insert_of_notMem fun h => by have := hI₁ h; tauto ] ; nlinarith [ show # ( G.neighborFinset v ∩ S ) ≤ d by exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( hdeg v hv ) ] ⟩;
    · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
      exact ⟨ v, hv, by tauto ⟩;
    · grind +qlia

/-! ## Switch Count Infrastructure -/

/-- The switch indicator for a fixed pair (u,v). -/
def switchIndicator {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n)
    (G : SimpleGraph (Fin n)) : ℝ :=
  if IsIdSwitch Hc G u v then 1 else 0

/-- The switch count function: sum of switch indicators over all pairs in a set T. -/
def switchCount {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ p ∈ T.offDiag, switchIndicator Hc p.1 p.2 G

/-- switchCount is nonneg -/
lemma switchCount_nonneg {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : 0 ≤ switchCount Hc T G := by
  apply Finset.sum_nonneg
  intro p _
  unfold switchIndicator
  split <;> norm_num

/-- If the switchCount is 0, then no pair in T has a switch. -/
lemma switchCount_zero_iff_no_switch {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (G : SimpleGraph (Fin n)) :
    switchCount Hc T G = 0 ↔
    ∀ p ∈ T.offDiag, ¬IsIdSwitch Hc G p.1 p.2 := by
  unfold switchCount
  constructor
  · intro h p hp
    have hsm := Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
      unfold switchIndicator; split <;> norm_num : ∀ p ∈ T.offDiag, (0 : ℝ) ≤ switchIndicator Hc p.1 p.2 G)
    rw [hsm] at h
    have := h p hp
    unfold switchIndicator at this
    split at this <;> simp_all
  · intro h
    apply Finset.sum_eq_zero
    intro p hp
    unfold switchIndicator
    simp [h p hp]

/-- No-switch monotonicity: if all pairs fail the switch condition,
    then pairs in any subset T also fail. -/
lemma no_switch_implies_switchCount_zero {n : ℕ} (Hc G : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (h : ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v) :
    switchCount Hc T G = 0 := by
  rw [switchCount_zero_iff_no_switch]
  intro p hp
  exact h p.1 p.2 (Finset.mem_offDiag.mp hp).2.2

/-- The set of graphs with no switch for all pairs is a subset of
    the set with switchCount = 0. -/
lemma no_switch_subset_switchCount_zero {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)) ⊆
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)) := by
  intro G hG
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact no_switch_implies_switchCount_zero Hc G T hG

/-! ## Mean Switch Count Lower Bound -/

/-- Sum of switch indicators over all graphs equals the number of
    graphs satisfying the switch condition. -/
lemma sum_switchIndicator_eq_card {n : ℕ} (Hc : SimpleGraph (Fin n)) (u v : Fin n) :
    ∑ G : SimpleGraph (Fin n), switchIndicator Hc u v G =
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G u v)).card : ℝ) := by
  unfold switchIndicator
  rw [← Finset.sum_boole]

/-- The total switch count summed over all graphs G equals
    the sum over pairs of the number of satisfying graphs. -/
lemma sum_switchCount_eq {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    ∑ G : SimpleGraph (Fin n), switchCount Hc T G =
    ∑ p ∈ T.offDiag,
      ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        IsIdSwitch Hc G p.1 p.2)).card : ℝ) := by
  unfold switchCount
  rw [Finset.sum_comm]
  congr 1
  ext p
  exact sum_switchIndicator_eq_card Hc p.1 p.2

/-
The mean value of the switch count over all graphs G is at least
    |T.offDiag| * 2^(N - 8C), assuming T is independent in Hc and
    all vertices of T have degree ≤ 4C in Hc.
-/
set_option maxHeartbeats 800000 in
lemma mean_switchCount_lower {n : ℕ} (Hc : SimpleGraph (Fin n)) (C : ℕ)
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hn : 8 * C ≤ n.choose 2) :
    (T.offDiag.card : ℝ) * (2 : ℝ) ^ (n.choose 2 - 8 * C) ≤
    ∑ G : SimpleGraph (Fin n), switchCount Hc T G := by
  rw [ sum_switchCount_eq, mul_comm ];
  -- Apply the lemma `switch_pair_count_lower` to each pair in $T.offDiag$.
  have h_pair_count : ∀ p ∈ T.offDiag, ((Finset.univ.filter (fun G => IsIdSwitch Hc G p.1 p.2)).card : ℝ) ≥ 2 ^ (n.choose 2 - 8 * C) := by
    intros p hp
    have h_pair_count : ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsIdSwitch Hc G p.1 p.2)).card : ℝ) ≥ 2 ^ (n.choose 2 - 2 * (4 * C)) := by
      norm_num +zetaDelta at *;
      exact_mod_cast switch_pair_count_lower Hc p.1 p.2 hp.2.2 ( hT_indep p.1 hp.1 p.2 hp.2.1 hp.2.2 ) ( 4 * C ) ( hT_deg p.1 hp.1 ) ( hT_deg p.2 hp.2.1 ) ( by linarith );
    grind;
  simpa [ mul_comm ] using Finset.sum_le_sum h_pair_count

/-! ## Bounded Differences for switchCount through graphEquiv -/

/-- The bounded-differences constant for switchCount at edge slot e.
    For T independent in Hc:
    - If exactly one endpoint of e is in T: bound = 2·dT(non-T endpoint)
    - Otherwise (both in T or both outside T): bound = 0 -/
def switchBound {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (e : EdgeSlot n) : ℝ :=
  if e.val.1 ∈ T ∧ e.val.2 ∉ T then
    (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.2)).card)
  else if e.val.2 ∈ T ∧ e.val.1 ∉ T then
    (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.1)).card)
  else 0

set_option maxHeartbeats 800000 in
lemma switchCount_bounded_diff_edgeSlot {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (e : EdgeSlot n)
    (x y : EdgeSlot n → Bool)
    (hxy : ∀ e' : EdgeSlot n, e' ≠ e → x e' = y e') :
    |switchCount Hc T (graphDecode x) -
     switchCount Hc T (graphDecode y)| ≤
    switchBound Hc T e := by
  unfold switchBound;
  split_ifs <;> simp_all +decide [ switchCount ];
  · -- Let's simplify the expression inside the absolute value.
    suffices h_simp : ∀ p ∈ T.offDiag, |switchIndicator Hc p.1 p.2 (graphDecode x) - switchIndicator Hc p.1 p.2 (graphDecode y)| ≤ if p.1 = e.val.1 ∧ Hc.Adj p.2 e.val.2 then 1 else if p.2 = e.val.1 ∧ Hc.Adj p.1 e.val.2 then 1 else 0 by
      refine' le_trans ( by simpa only [ ← Finset.sum_sub_distrib ] using Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_simp ) _ );
      simp +decide [ Finset.sum_ite, Finset.filter_and ];
      rw [ two_mul ];
      gcongr;
      · refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.image ( fun v => ( e.val.1, v ) ) ( Finset.filter ( fun v => Hc.Adj v e.val.2 ) T );
        · intro p hp; aesop;
        · exact Finset.card_image_le;
      · refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.image ( fun v => ( v, e.val.1 ) ) ( Finset.filter ( fun v => Hc.Adj v e.val.2 ) T );
        · grind;
        · exact Finset.card_image_le;
    intro p hp; split_ifs <;> simp_all +decide [ switchIndicator ] ;
    · split_ifs <;> norm_num;
    · split_ifs <;> norm_num;
    · unfold IsIdSwitch; simp_all +decide [ graphDecode ] ;
      grind +revert;
  · -- The difference in switch counts is bounded by the number of pairs affected by the edge slot e.
    have h_diff_bound : |∑ p ∈ T.offDiag, (switchIndicator Hc p.1 p.2 (graphDecode x) - switchIndicator Hc p.1 p.2 (graphDecode y))| ≤ ∑ p ∈ T.offDiag, (if p.1 = e.val.2 ∧ Hc.Adj p.2 (e.val.1) then 1 else 0) + ∑ p ∈ T.offDiag, (if p.2 = e.val.2 ∧ Hc.Adj p.1 (e.val.1) then 1 else 0) := by
      rw [ ← Finset.sum_add_distrib ];
      refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum _ );
      intro p hp; split_ifs <;> simp_all +decide [ switchIndicator ] ;
      · split_ifs <;> norm_num;
      · split_ifs <;> norm_num;
      · unfold IsIdSwitch; simp_all +decide [ graphDecode ] ;
        grind;
    simp_all +decide [ Finset.sum_ite ];
    refine le_trans h_diff_bound ?_;
    rw [ two_mul ];
    gcongr;
    · have h_card_filter : Finset.card (Finset.image (fun p => p.2) (Finset.filter (fun p => p.1 = e.val.2 ∧ Hc.Adj p.2 (e.val.1)) (T.offDiag))) ≤ Finset.card (Finset.filter (fun v => Hc.Adj v (e.val.1)) T) := by
        exact Finset.card_le_card fun x hx => by aesop;
      rwa [ Finset.card_image_of_injOn ] at h_card_filter ; intro p hp q hq ; aesop;
    · refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun v => ( v, e.val.2 ) ) ( Finset.filter ( fun v => Hc.Adj v e.val.1 ) T );
      · intro x hx; aesop;
      · exact Finset.card_image_le;
  · rw [ sub_eq_zero, Finset.sum_congr rfl ];
    intro p hp; unfold switchIndicator; simp +decide [ graphDecode ] ;
    unfold IsIdSwitch; simp +decide [ hxy ] ;
    congr! 3;
    · congr! 3;
      · rw [ hxy ] ; aesop;
      · congr! 2;
        rw [ hxy ] ; aesop;
    · congr! 3;
      · grind +suggestions;
      · congr! 2;
        rw [ hxy ];
        rintro rfl; simp_all +decide [ SimpleGraph.adj_comm ];
        exact hT_indep _ ‹_› _ hp.2.1 ( by aesop ) ‹_›

/-! ## Tight Bounded Differences (excluding Hc-edges) -/

/-- Tight bounded-differences constant for switchCount at edge slot e.
    This refines `switchBound` by giving 0 when all of T is adjacent to
    the non-T endpoint (because flipping an Hc-edge doesn't change
    any switch indicator). -/
def switchBoundTight {n : ℕ} (Hc : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (e : EdgeSlot n) : ℝ :=
  if e.val.1 ∈ T ∧ e.val.2 ∉ T then
    if Hc.Adj e.val.1 e.val.2 then 0
    else (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.2)).card)
  else if e.val.2 ∈ T ∧ e.val.1 ∉ T then
    if Hc.Adj e.val.2 e.val.1 then 0
    else (2 : ℝ) * ↑((T.filter (fun v => Hc.Adj v e.val.1)).card)
  else 0

lemma switchBoundTight_nonneg {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (e : EdgeSlot n) :
    0 ≤ switchBoundTight Hc T e := by
  unfold switchBoundTight; split_ifs <;> positivity

/-
The tight bounded-differences result: for T independent in Hc,
    flipping one edge slot changes switchCount by at most switchBoundTight.
    This is tighter than switchBound because when Hc.Adj u w (with u ∈ T, w ∉ T),
    the switch indicators for pairs in T don't depend on G.Adj u w at all.
-/
lemma switchCount_bounded_diff_tight {n : ℕ} (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (e : EdgeSlot n)
    (x y : EdgeSlot n → Bool)
    (hxy : ∀ e' : EdgeSlot n, e' ≠ e → x e' = y e') :
    |switchCount Hc T (graphDecode x) -
     switchCount Hc T (graphDecode y)| ≤
    switchBoundTight Hc T e := by
  revert e;
  intro e he; by_cases he' : Hc.Adj e.val.1 e.val.2 <;> by_cases he'' : Hc.Adj e.val.2 e.val.1 <;> simp +decide [ he', he'', switchBoundTight ] ;
  · -- Since $Hc.Adj (e.val.1) (e.val.2)$, the switch indicators for pairs in $T$ do not depend on $G.Adj (e.val.1) (e.val.2)$.
    have h_switch_indicator_indep : ∀ u v : Fin n, u ∈ T → v ∈ T → u ≠ v → (IsIdSwitch Hc (graphDecode x) u v ↔ IsIdSwitch Hc (graphDecode y) u v) := by
      intros u v hu hv huv
      simp [IsIdSwitch, graphDecode];
      grind;
    simp +decide [ switchCount, h_switch_indicator_indep ];
    rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_eq_zero fun p hp => by unfold switchIndicator; specialize h_switch_indicator_indep p.1 p.2; aesop;
  · exact False.elim <| he'' <| he'.symm;
  · exact False.elim <| he' <| he''.symm;
  · convert switchCount_bounded_diff_edgeSlot Hc T hT_indep e x y he using 1

end UniqueSubgraphs
/-! ==================================================================
    Pruning Chain Infrastructure
    (originally PruningChain.lean)
    ================================================================== -/

/-!
# Pruning Chain Infrastructure for Claim 2.4
-/

open Finset Function SimpleGraph
open scoped Classical

namespace UniqueSubgraphs

/-- For any M > 0 and k : ℕ, eventually (n : ℝ) ≥ M * (log n)^k for natural n. -/
lemma eventually_ge_mul_log_pow (M : ℝ) (k : ℕ) (hM : M > 0) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) ≥ M * (Real.log n) ^ k := by
  have h : Filter.Tendsto (fun x : ℝ => M * (Real.log x) ^ k / x) Filter.atTop (nhds 0) := by
    have := @Real.isLittleO_pow_log_id_atTop k
    simpa [mul_div_assoc] using this.const_mul_left M |>.tendsto_div_nhds_zero
  exact Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds zero_lt_one)) |> fun ⟨N, hN⟩ ↦
    ⟨⌈N⌉₊ + 1, fun n hn ↦ by
      have := hN n (Nat.le_of_ceil_le (by linarith))
      rw [div_lt_one (by norm_cast; linarith)] at this
      exact_mod_cast this.le⟩

def pruningThresh (n : ℕ) (i : ℕ) : ℕ :=
  ⌊(n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))⌋₊

/-! ### Threshold properties -/

/-- All pruning thresholds at levels ≤ 4C are ≥ 2 for large n. -/
lemma pruningThresh_ge_two (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ i : ℕ, i ≤ 4 * C → pruningThresh n i ≥ 2 := by
  -- Use `eventually_ge_mul_log_pow` with $M = 2$ and $k = 6^{4C+1}$ to get $n₀$ such that $n \geq 2 * (\log n)^{6^{4C+1}}$ for $n \geq n₀$.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) ≥ 2 * (Real.log n) ^ (6 ^ (4 * C + 1)) := by
    convert eventually_ge_mul_log_pow 2 ( 6 ^ ( 4 * C + 1 ) ) ( by norm_num ) using 1;
  refine' ⟨ n₀ + 3, fun n hn i hi => Nat.le_floor _ ⟩;
  rw [ le_div_iff₀ ] <;> norm_num;
  · refine le_trans ?_ ( hn₀ n ( by linarith ) );
    exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) <| pow_le_pow_right₀ ( by norm_num ) <| by linarith ) zero_le_two;
  · exact pow_pos ( Real.log_pos <| by norm_cast; linarith ) _

/-
For large n, the level-0 threshold is ≤ n/(8C+2).
-/
lemma pruningThresh_zero_le_B'_card (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ B'_card : ℕ, B'_card ≥ n / (8 * C + 2) →
    pruningThresh n 0 ≤ B'_card := by
  -- Use the lemma `eventually_ge_mul_log_pow` to find such an $n₀$.
  have h_eventually_ge_mul_log_pow : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (n : ℝ) / (Real.log n) ^ 6 ≤ n / (8 * C + 2) := by
    have h_eventually_ge_mul_log_pow : ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (Real.log n) ^ 6 ≥ 8 * C + 2 := by
      have h_log_bound : Filter.Tendsto (fun n : ℕ => (Real.log n)^6) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      exact Filter.eventually_atTop.mp ( h_log_bound.eventually_ge_atTop _ );
    exact ⟨ h_eventually_ge_mul_log_pow.choose + 1, fun n hn => by gcongr ; exact h_eventually_ge_mul_log_pow.choose_spec n ( by linarith ) ⟩;
  cases' h_eventually_ge_mul_log_pow with n₀ hn₀;
  refine' ⟨ n₀ + 2, fun n hn B'_card hB'_card => _ ⟩ ; norm_num [ pruningThresh ] at *;
  refine' Nat.le_trans ( Nat.floor_mono <| hn₀ n <| by linarith ) _;
  exact Nat.le_trans ( Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by linarith : 0 < ( 8 * C + 2 ) ) ] ) hB'_card

/-
Pruning thresholds are non-increasing for large n (where log n > 1).
-/
lemma pruningThresh_mono {n : ℕ} (hn : n ≥ 3) (i : ℕ) :
    pruningThresh n (i + 1) ≤ pruningThresh n i := by
  refine Nat.floor_mono ?_;
  gcongr <;> norm_num;
  · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  · exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) )

/-! ### The one-step pruning alternative -/

/-
If T ⊆ B' is not controlled with threshold τ ≥ 1, then there exists a "bad" vertex
    w outside B' that can be used to prune T.
-/
lemma not_controlled_exists_bad {n : ℕ}
    (Hc : SimpleGraph (Fin n))
    (B' T : Finset (Fin n)) (τ : ℕ) (hτ : τ ≥ 1)
    (hTB : T ⊆ B')
    (hIndep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (h_not : ¬(∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < τ)) :
    ∃ w, w ∉ B' ∧ w ∉ T ∧
    (T.filter (fun v => Hc.Adj v w)).card ≥ τ ∧
    ¬(∀ v ∈ T, Hc.Adj v w) ∧
    T.filter (fun v => Hc.Adj v w) ⊆ B' ∧
    T.filter (fun v => Hc.Adj v w) ⊂ T := by
  simp +zetaDelta at *;
  obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_not;
  refine' ⟨ x, _, _, hx₃, hx₂, _, _ ⟩;
  · contrapose! hx₂;
    intro y hy; have := Finset.card_pos.mp ( by linarith ) ; obtain ⟨ z, hz ⟩ := this; specialize hIndep _ ( hTB <| Finset.mem_filter.mp hz |>.1 ) _ hx₂; aesop;
  · grind +qlia;
  · exact fun y hy => hTB <| Finset.mem_filter.mp hy |>.1;
  · grind

/-! ### The multi-level chain argument -/

/-
The multi-level pruning chain terminates within 4C levels, producing
    a controlled T with a size guarantee from the threshold sequence.
-/
set_option maxHeartbeats 800000 in
lemma pruning_chain_produces_controlled {n : ℕ} (C : ℕ) (hC : C ≥ 1)
    (Hc : SimpleGraph (Fin n))
    (B' : Finset (Fin n))
    (hIndep : ∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v)
    (hDeg : ∀ v ∈ B', Hc.degree v ≤ 4 * C)
    (τ : ℕ → ℕ)
    (hτ_ge : ∀ i, i ≤ 4 * C → τ i ≥ 2)
    (hτ_le : τ 0 ≤ B'.card)
    (hτ_mono : ∀ i, i < 4 * C → τ (i + 1) ≤ τ i) :
    ∃ (i : ℕ) (T : Finset (Fin n)),
    i ≤ 4 * C ∧
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    T.card ≥ (if i = 0 then B'.card else τ (i - 1)) ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < τ i) := by
  by_contra! h_contra;
  -- Define a recursive construction: at level ℓ (starting from 0), we have T_ℓ ⊆ B' with |T_ℓ| ≥ (if ℓ=0 then |B'| else τ(ℓ-1)), and a set W_ℓ of ℓ distinct vertices outside B', all adjacent to all of T_ℓ.
  have h_rec : ∀ k ≤ 4 * C + 1, ∃ T : Finset (Fin n), ∃ W : Finset (Fin n), T ⊆ B' ∧ W.card = k ∧ (∀ w ∈ W, w ∉ B') ∧ (∀ w ∈ W, ∀ v ∈ T, Hc.Adj v w) ∧ T.card ≥ (if k = 0 then B'.card else τ (k - 1)) := by
    intro k hk
    induction' k with k ih;
    · exact ⟨ B', ∅, Finset.Subset.refl _, rfl, by norm_num, by norm_num, by norm_num ⟩;
    · obtain ⟨ T, W, hT₁, hT₂, hT₃, hT₄, hT₅ ⟩ := ih ( Nat.le_of_succ_le hk );
      -- By the induction hypothesis, T is not controlled with threshold τ k.
      have h_not_controlled : ¬(∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨ (T.filter (fun v => Hc.Adj v w)).card < τ k) := by
        specialize h_contra k T ( by linarith ) hT₁ ( by
          grind ) hT₅;
        grind;
      obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := not_controlled_exists_bad Hc B' T ( τ k ) ( by linarith [ hτ_ge k ( by linarith ) ] ) hT₁ hIndep h_not_controlled;
      use T.filter (fun v => Hc.Adj v w), Insert.insert w W;
      grind;
  obtain ⟨ T, W, hT₁, hW₁, hW₂, hW₃, hT₂ ⟩ := h_rec ( 4 * C + 1 ) le_rfl;
  -- Since $W$ consists of $4C + 1$ distinct vertices outside $B'$ and each vertex in $W$ is adjacent to all vertices in $T$, the degree of any vertex in $T$ must be at least $4C + 1$.
  have h_deg_T : ∀ v ∈ T, Hc.degree v ≥ 4 * C + 1 := by
    intros v hv; exact (by
    exact hW₁ ▸ Finset.card_le_card ( show W ⊆ Hc.neighborFinset v from fun w hw => by aesop ));
  rcases T.eq_empty_or_nonempty with ( rfl | ⟨ v, hv ⟩ ) <;> simp_all +decide;
  · linarith [ hτ_ge ( 4 * C ) le_rfl ];
  · linarith [ h_deg_T v hv, hDeg v ( hT₁ hv ) ]

/-! ### Ratio bound at each level -/

/-
For large n (depending on C), at any level i ≤ 4C, the ratio
    (a - 1)² / τᵢ ≥ K · n · log n whenever a ≥ the lower bound for that level.
-/
set_option maxHeartbeats 1600000 in
lemma pruning_ratio_bound (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ i : ℕ, i ≤ 4 * C →
    ∀ a : ℕ, a ≥ (if i = 0 then n / (8 * C + 2) else pruningThresh n (i - 1)) →
    ((a : ℝ) - 1) ^ 2 / ((pruningThresh n i : ℝ)) ≥
      2 ^ (16 * C + 4) * (C : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  have := @UniqueSubgraphs.pruningThresh_ge_two C hC; simp_all +decide [ UniqueSubgraphs.pruningThresh ] ; (
  -- Choose n₀ so that for n ≥ n₀: (1) pruningThresh is ≥ 2, (2) a ≥ a/2 ≥ 2, (3) (log n)^3 ≥ 16·K, and (4) (log n)^5 ≥ 4·(8C+2)²·K.
  obtain ⟨n₀₁, hn₀₁⟩ := this
  obtain ⟨n₀₂, hn₀₂⟩ : ∃ n₀₂ : ℕ, ∀ n ≥ n₀₂, Real.log n ^ 3 ≥ 16 * 2 ^ (16 * C + 4) * C := by
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n ^ 3) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop _ ) |> fun ⟨ n₀₂, hn₀₂ ⟩ => ⟨ n₀₂, fun n hn => hn₀₂ n hn ⟩ ;
  obtain ⟨n₀₃, hn₀₃⟩ : ∃ n₀₃ : ℕ, ∀ n ≥ n₀₃, Real.log n ^ 5 ≥ 4 * (8 * C + 2) ^ 2 * 2 ^ (16 * C + 4) * C := by
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log n ^ 5) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by norm_num ) ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop _ ) |> fun ⟨ n₀₃, hn₀₃ ⟩ => ⟨ n₀₃, fun n hn => hn₀₃ n hn ⟩ ;
  obtain ⟨n₀₄, hn₀₄⟩ : ∃ n₀₄ : ℕ, ∀ n ≥ n₀₄, ∀ i ≤ 4 * C, n / (8 * C + 2) ≥ 4 := by
    exact ⟨ 4 * ( 8 * C + 2 ) + 1, fun n hn i hi => Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by linarith ⟩ ;
  use max n₀₁ (max n₀₂ (max n₀₃ n₀₄)) + 1; intros n hn i hi a ha; split_ifs at ha <;> simp_all +decide [ Nat.succ_div ] ;
  · -- For i = 0, we have a ≥ n / (8C + 2). We need to show that (a - 1)² / τ₀ ≥ K·n·log n.
    have h_case0 : (a - 1 : ℝ) ^ 2 / (n / (Real.log n) ^ 6) ≥ 2 ^ (16 * C + 4) * C * (n * Real.log n) := by
      have h_case0 : (a - 1 : ℝ) ≥ n / (2 * (8 * C + 2)) := by
        rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> try linarith;
        rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by linarith : 0 < ( 8 * C + 2 ) ), hn₀₄ n ( by linarith ) 0 ( by linarith ) ] ;
      have h_case0 : (a - 1 : ℝ) ^ 2 ≥ (n / (2 * (8 * C + 2))) ^ 2 := by
        exact pow_le_pow_left₀ ( by positivity ) h_case0 2
      have h_case0 : (n / (2 * (8 * C + 2))) ^ 2 / (n / (Real.log n) ^ 6) ≥ 2 ^ (16 * C + 4) * C * (n * Real.log n) := by
        field_simp;
        convert mul_le_mul_of_nonneg_left ( hn₀₃ n ( by linarith ) ) ( show ( 0 :ℝ ) ≤ n * Real.log n by exact mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) using 1 <;> ring
      exact le_trans h_case0 (by
      gcongr);
    refine le_trans h_case0 ?_;
    by_cases h : ⌊ ( n : ℝ ) / Real.log n ^ 6⌋₊ = 0 <;> simp_all +decide [ div_eq_mul_inv ];
    · contrapose! hn₀₁;
      exact ⟨ n, by linarith, 0, by linarith, Nat.floor_lt' ( by norm_num ) |>.2 <| by simpa using h.trans_le <| by norm_num ⟩;
    · gcongr;
      exact le_trans ( by norm_num [ mul_comm ] ) ( inv_anti₀ ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr h ) <| Nat.floor_le <| by positivity );
  · -- For i ≥ 1, a ≥ pruningThresh n (i-1) = ⌊n/(log n)^(6^i)⌋₊ ≥ n/(log n)^(6^i) - 1.
    have ha_ge : (a : ℝ) ≥ (n : ℝ) / (Real.log n) ^ (6 ^ i) - 1 := by
      rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ‹_› ) ] at ha;
      exact le_trans ( sub_le_iff_le_add.mpr <| Nat.lt_floor_add_one _ |> le_of_lt ) <| mod_cast ha
    -- Thus, a ≥ n/(2·(log n)^(6^i)).
    have ha_ge_half : (a : ℝ) ≥ (n : ℝ) / (2 * (Real.log n) ^ (6 ^ i)) := by
      have ha_ge_half : (n : ℝ) / (Real.log n) ^ (6 ^ i) ≥ 2 := by
        have := hn₀₁ n ( by linarith ) ( i - 1 ) ( by omega ) ; rcases i <;> simp_all +decide [ Nat.pow_succ' ] ;
        exact le_trans ( mod_cast this ) ( Nat.floor_le ( by positivity ) )
      generalize_proofs at *; (
      ring_nf at *; linarith;)
    -- The ratio: (a-1)²/(pruningThresh n i) ≥ (a/2)²/(n/(log n)^(6^(i+1))) (for a ≥ 2).
    have h_ratio_ge : ((a - 1 : ℝ) ^ 2) / (pruningThresh n i) ≥ ((n : ℝ) / (4 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) := by
      gcongr <;> norm_num [ UniqueSubgraphs.pruningThresh ] at *;
      · grind +splitImp;
      · rcases a with ( _ | _ | a ) <;> norm_num at *;
        · grind +suggestions;
        · exact absurd ha ( not_le_of_gt ( Nat.lt_of_lt_of_le ( by norm_num ) ( hn₀₁ n ( by linarith ) ( i - 1 ) ( Nat.sub_le_of_le_add ( by linarith ) ) ) ) );
        · ring_nf at *; linarith;
      · exact Nat.floor_le ( by positivity ) |> le_trans <| by norm_num;
    generalize_proofs at *; (
    -- Simplify the right-hand side of the inequality.
    have h_simplify : ((n : ℝ) / (4 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) = (n : ℝ) * (Real.log n) ^ (4 * 6 ^ i) / 16 := by
      field_simp
      ring
      generalize_proofs at *; (
      by_cases h : Real.log n = 0 <;> simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ] ; ring;
      · norm_cast at * ; aesop ( simp_config := { decide := true } ) ;
      · exact div_eq_iff ( pow_ne_zero _ <| pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| lt_of_le_of_ne ( Nat.succ_le_of_lt <| Nat.pos_of_ne_zero h.1 ) <| Ne.symm h.2.1 ) |>.2 <| by ring;)
    generalize_proofs at *; (
    -- Since $4 \cdot 6^i \geq 4$ for $i \geq 1$, we have $(\log n)^{4 \cdot 6^i} \geq (\log n)^4$.
    have h_log_ge : (Real.log n) ^ (4 * 6 ^ i) ≥ (Real.log n) ^ 4 := by
      exact pow_le_pow_right₀ ( show 1 ≤ Real.log n from by have := hn₀₂ n ( by linarith ) ; nlinarith [ show ( 1 :ℝ ) ≤ 2 ^ ( 16 * C + 4 ) * C by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( mod_cast hC ), pow_two_nonneg ( Real.log n ^ 2 - 1 ) ] ) ( show 4 ≤ 4 * 6 ^ i by linarith [ pow_pos ( by decide : 0 < 6 ) i ] ) ;
    generalize_proofs at *; (
    -- Since $(\log n)^3 \geq 16 \cdot 2^{16C+4} \cdot C$, we have $(\log n)^4 \geq 16 \cdot 2^{16C+4} \cdot C \cdot \log n$.
    have h_log_fourth_ge : (Real.log n) ^ 4 ≥ 16 * 2 ^ (16 * C + 4) * C * Real.log n := by
      nlinarith only [ hn₀₂ n hn.2.1.le, Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ]
    generalize_proofs at *; (
    exact le_trans ( by nlinarith [ show ( 0 :ℝ ) ≤ n * Real.log n by positivity ] ) ( h_ratio_ge.trans' ( h_simplify.ge.trans' ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left h_log_ge <| Nat.cast_nonneg _ ) <| by positivity ) ) ) |> le_trans <| le_rfl;)))));

/-! ### Main result: combining chain and ratio -/

/-
**Claim 2.4 (C ≥ 1)**: the multi-level pruning produces a controlled (T, threshold)
    pair with a good ratio bound.
-/
theorem claim_2_4_pruning_pos_result (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) := by
  obtain ⟨ n₁, hn₁ ⟩ := pruningThresh_ge_two C hC;
  obtain ⟨ n₂, hn₂ ⟩ := pruningThresh_zero_le_B'_card C hC;
  obtain ⟨ n₃, hn₃ ⟩ := pruning_ratio_bound C hC;
  refine' ⟨ n₁ + n₂ + n₃ + 3, fun n hn Hc hHc B' hB' hB'' hB''' => _ ⟩;
  -- Apply the multi-level pruning chain to obtain the controlled set T and threshold.
  obtain ⟨ i, T, hi₁, hi₂, hi₃, hi₄, hi₅ ⟩ := pruning_chain_produces_controlled C hC Hc B' hB' hB'' (fun i => pruningThresh n i) (fun i hi => hn₁ n (by linarith) i hi) (by
  exact hn₂ n ( by linarith ) _ hB''') (fun i hi => pruningThresh_mono (by linarith) i);
  refine' ⟨ T, pruningThresh n i, hi₂, hi₃, hi₅, _, _ ⟩;
  · exact sub_pos_of_lt ( mod_cast hi₃ );
  · grind

end UniqueSubgraphs
/-! ==================================================================
    Edge Ordering Argument
    (originally EdgeOrdering.lean)
    ================================================================== -/

section EdgeOrderingSection

/-!
# Edge Ordering Argument for the z-process Sum Bound

This file proves the abstract transition bound needed for `sum_z_refined_le_one`.
-/


open Finset Function
open scoped Classical

namespace EdgeOrderingCount

variable {N : ℕ}

/-! ## Chain prefix from a permutation -/

/-- The prefix of a permutation: the set {σ(i) : i.val < m}. -/
def chainPrefix (σ : Equiv.Perm (Fin N)) (m : ℕ) : Finset (Fin N) :=
  (Finset.univ.filter (fun i : Fin N => i.val < m)).image σ

@[simp]
lemma chainPrefix_zero (σ : Equiv.Perm (Fin N)) : chainPrefix σ 0 = ∅ := by
  simp [chainPrefix]

lemma chainPrefix_card (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m ≤ N) :
    (chainPrefix σ m).card = m := by
  rw [ chainPrefix, Finset.card_image_of_injective _ σ.injective ];
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i, by linarith ⟩;
  · grind;
  · aesop;
  · aesop

lemma chainPrefix_mono (σ : Equiv.Perm (Fin N)) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    chainPrefix σ m₁ ⊆ chainPrefix σ m₂ := by
  intro x hx
  simp only [chainPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, by omega, rfl⟩


lemma chainPrefix_succ (σ : Equiv.Perm (Fin N)) {m : ℕ} (hm : m < N) :
    chainPrefix σ (m + 1) = insert (σ ⟨m, hm⟩) (chainPrefix σ m) := by
  ext x
  simp only [chainPrefix, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i.val = m
    · left; congr 1; exact Fin.ext h
    · right; exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨m, hm⟩, by simp, rfl⟩
    · exact ⟨i, by omega, rfl⟩

lemma chainPrefix_new_not_mem (σ : Equiv.Perm (Fin N)) {m : ℕ} (hm : m < N) :
    σ ⟨m, hm⟩ ∉ chainPrefix σ m := by
  simp only [chainPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨i, hi, h⟩
  have := σ.injective h
  subst this; simp at hi

/-! ## Counting permutations with a given prefix -/

set_option maxHeartbeats 800000 in
lemma perm_prefix_fiber_card (m : ℕ) (S : Finset (Fin N)) (hS : S.card = m) (hm : m ≤ N) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S)).card =
    Nat.factorial m * Nat.factorial (N - m) := by
  revert S hS hm;
  induction' m with m ih generalizing N;
  · simp +decide [ Fintype.card_perm ];
  · intro S hS hN
    have h_count_succ : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ (m + 1) = S} = ∑ x ∈ S, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} := by
      have h_count_succ : Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = S) Finset.univ = Finset.biUnion S (fun x => Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x) Finset.univ) := by
        ext σ; simp [chainPrefix_succ];
        constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, chainPrefix ];
        · refine' ⟨ h _ |>.1 ⟨ _, le_rfl, rfl ⟩, fun a => ⟨ fun ⟨ i, hi, hi' ⟩ => ⟨ _, h _ |>.1 ⟨ i, hi.le, hi' ⟩ ⟩, fun ⟨ hi, hi' ⟩ => _ ⟩ ⟩;
          · intro H; have := σ.injective ( H.symm ▸ hi' ) ; aesop;
          · exact h a |>.2 hi' |> fun ⟨ i, hi, hi' ⟩ => ⟨ i, lt_of_le_of_ne hi ( by aesop ), hi' ⟩;
        · grind;
      rw [ h_count_succ, Finset.card_biUnion ];
      exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσx hσy => hxy <| by aesop;
    have h_count_erase : ∀ x ∈ S, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} = m.factorial * (N - m - 1).factorial := by
      intro x hx
      have h_count_erase : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} = Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x} / (N - m) := by
        have h_ind_step : ∀ y ∈ Finset.univ \ S.erase x, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y} = Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x} := by
          intro y hy
          have h_bij : Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y) Finset.univ = Finset.image (fun σ : Equiv.Perm (Fin N) => Equiv.swap x y * σ) (Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = x) Finset.univ) := by
            ext σ; simp [chainPrefix];
            constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, Equiv.swap_apply_def ];
            · grind;
            · grind;
          rw [ h_bij, Finset.card_image_of_injective _ fun σ τ h => by simpa using h ];
        have h_ind_step : Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x} = ∑ y ∈ Finset.univ \ S.erase x, Finset.card {σ : Equiv.Perm (Fin N) | chainPrefix σ m = S.erase x ∧ σ ⟨m, by linarith⟩ = y} := by
          rw [ ← Finset.card_biUnion ];
          · congr with σ ; simp +decide [ Finset.mem_biUnion ];
            intro hσ hxσ; contrapose! hxσ; simp_all +decide [ chainPrefix ] ;
            replace hσ := Finset.ext_iff.mp hσ ( σ ⟨ m, by linarith ⟩ ) ; aesop;
          · exact fun y hy z hz hyz => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hyz <| by aesop;
        rw [ h_ind_step, Finset.sum_congr rfl ‹_› ] ; simp +decide [ Finset.card_sdiff, * ];
        rw [ Nat.mul_div_cancel_left _ ( Nat.sub_pos_of_lt hN ) ];
      rw [ h_count_erase, ih ];
      · exact Nat.div_eq_of_eq_mul_left ( Nat.sub_pos_of_lt hN ) ( by rw [ mul_assoc, ← Nat.succ_pred_eq_of_pos ( Nat.sub_pos_of_lt hN ) ] ; simp +decide [ Nat.factorial_succ, mul_comm, mul_assoc, mul_left_comm ] );
      · grind;
      · grind +qlia;
    simp_all +decide [ Nat.sub_sub, Nat.factorial_succ ];
    ring

/-! ## Transition count and interval property -/

set_option maxHeartbeats 800000 in
lemma transition_count_le_one
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (σ : Equiv.Perm (Fin N)) :
    ((Finset.range (N + 1)).filter (fun m =>
      P (chainPrefix σ m) ∧ (m = 0 ∨ ¬ P (chainPrefix σ (m - 1))))).card ≤ 1 := by
  rw [ Finset.card_le_one_iff ];
  grind +suggestions

/-! ## Counting identities -/

def countP (P : Finset (Fin N) → Prop) [DecidablePred P] (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin N) => S.card = m ∧ P S)).card

lemma count_perm_with_P (P : Finset (Fin N) → Prop) [DecidablePred P] (m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card =
    countP P m * Nat.factorial m * Nat.factorial (N - m) := by
  have h_card : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card = Finset.sum (Finset.univ.filter (fun S : Finset (Fin N) => S.card = m ∧ P S)) (fun S => (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S)).card) := by
    rw [ ← Finset.card_biUnion ];
    · congr with σ;
      simp +zetaDelta at *;
      exact fun _ => chainPrefix_card σ m hm;
    · exact fun x hx y hy hxy => Finset.disjoint_filter.2 fun z => by aesop;
  rw [ h_card, Finset.sum_congr rfl fun S hS ↦ perm_prefix_fiber_card m S ( by aesop ) hm ];
  simp +decide [ mul_assoc, countP ]

set_option maxHeartbeats 3200000 in
lemma count_perm_with_P_pair (P : Finset (Fin N) → Prop) [DecidablePred P]
    (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ N)
    (ext_val : ℕ → ℕ)
    (h_ext : ∀ (S : Finset (Fin N)), P S → S.card < N →
      ((Finset.univ : Finset (Fin N)).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
      P (chainPrefix σ m) ∧ P (chainPrefix σ (m - 1)))).card =
    countP P (m - 1) * ext_val (m - 1) * Nat.factorial (m - 1) * Nat.factorial (N - m) := by
  rcases m with ( _ | m ) <;> simp_all +decide;
  have h_fiber_size : ∀ S₀ : Finset (Fin N), S₀.card = m → P S₀ → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card = Nat.factorial m * Nat.factorial (N - m) := by
    exact fun S₀ hS₀ hP₀ => perm_prefix_fiber_card m S₀ hS₀ ( by linarith );
  have h_fiber_size_succ : ∀ S₀ : Finset (Fin N), S₀.card = m → P S₀ → ∀ e : Fin N, e ∉ S₀ → P (insert e S₀) → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card = Nat.factorial m * Nat.factorial (N - m - 1) := by
    intros S₀ hS₀ hP₀ e he hP₁
    have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
      congr 1 with σ ; simp +decide [ chainPrefix_succ, he ];
      intro hσ; rw [ chainPrefix_succ ] ; simp +decide [ hσ, he ] ;
      · constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff ];
        intro a; specialize h a; by_cases ha : a = e <;> simp_all +decide ;
        exact fun h => he <| by obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp h; aesop;
      · grind +revert;
    have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card / (N - m) := by
      have h_fiber_size_succ : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀)).card = ∑ e ∈ Finset.univ \ S₀, (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
        rw [ ← Finset.card_biUnion ];
        · congr with σ ; simp +decide [ chainPrefix ];
          intro h; replace h := Finset.ext_iff.mp h ( σ ⟨ m, hm' ⟩ ) ; aesop;
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hxy <| by aesop;
      have h_fiber_size_succ : ∀ e₁ e₂ : Fin N, e₁ ∉ S₀ → e₂ ∉ S₀ → (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e₁)).card = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ m = S₀ ∧ σ ⟨m, hm'⟩ = e₂)).card := by
        intros e₁ e₂ he₁ he₂;
        refine' Finset.card_bij ( fun σ hσ => Equiv.swap e₁ e₂ * σ ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_univ, Equiv.swap_apply_def ];
        · intro σ hσ₁ hσ₂; simp_all +decide [ chainPrefix ] ;
          ext x; simp +decide [ Equiv.swap_apply_def, hσ₁, hσ₂ ] ;
          constructor;
          · grind;
          · intro hx;
            obtain ⟨ a, ha₁, ha₂ ⟩ := Finset.mem_image.mp ( hσ₁.symm ▸ hx ) ; use a; aesop;
        · intro b hb hb'; use Equiv.swap e₁ e₂ * b; simp_all +decide [ Equiv.swap_apply_def ] ;
          convert hb using 1;
          ext x; simp +decide [ chainPrefix ] ;
          constructor <;> rintro ⟨ a, ha, rfl ⟩ <;> use a <;> simp_all +decide [ Equiv.swap_apply_def ];
          · split_ifs <;> simp_all +decide [ chainPrefix ];
            · replace hb := Finset.ext_iff.mp hb e₁; aesop;
            · have := b.injective ( by aesop : b a = b ⟨ m, hm' ⟩ ) ; aesop;
          · split_ifs <;> simp_all +decide [ chainPrefix ];
            · replace hb := Finset.ext_iff.mp hb e₁; aesop;
            · have := b.injective ( by aesop : b a = b ⟨ m, hm' ⟩ ) ; aesop;
      rw [ ‹# { σ | chainPrefix σ m = S₀ } = ∑ e ∈ Finset.univ \ S₀, _›, Finset.sum_congr rfl fun x hx => h_fiber_size_succ x e ( by aesop ) he ] ; simp +decide [ Finset.card_sdiff, * ];
    rcases k : N - m with ( _ | k ) <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm ];
    · omega;
    · exact Nat.div_eq_of_eq_mul_left ( Nat.succ_pos _ ) ( by ring );
  have h_count : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ (m + 1)) ∧ P (chainPrefix σ m))).card = ∑ S₀ ∈ Finset.filter (fun S => S.card = m ∧ P S) (Finset.univ : Finset (Finset (Fin N))), ∑ e ∈ Finset.filter (fun e => e ∉ S₀ ∧ P (insert e S₀)) (Finset.univ : Finset (Fin N)), (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e)).card := by
    have h_count : Finset.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ (m + 1)) ∧ P (chainPrefix σ m)) Finset.univ = Finset.biUnion (Finset.filter (fun S => S.card = m ∧ P S) (Finset.univ : Finset (Finset (Fin N)))) (fun S₀ => Finset.biUnion (Finset.filter (fun e => e ∉ S₀ ∧ P (insert e S₀)) (Finset.univ : Finset (Fin N))) (fun e => Finset.filter (fun σ : Equiv.Perm (Fin N) => chainPrefix σ (m + 1) = insert e S₀ ∧ σ ⟨m, hm'⟩ = e) Finset.univ)) := by
      ext σ; simp [chainPrefix_succ];
      constructor;
      · intro hσ
        use chainPrefix σ m;
        exact ⟨ ⟨ chainPrefix_card σ m hm'.le, hσ.2 ⟩, ⟨ chainPrefix_new_not_mem σ hm', by simpa [ chainPrefix_succ σ hm' ] using hσ.1 ⟩, chainPrefix_succ σ hm' ⟩;
      · rintro ⟨ S₀, ⟨ hS₀₁, hS₀₂ ⟩, ⟨ hS₀₃, hS₀₄ ⟩, hS₀₅ ⟩;
        have h_chainPrefix_m : chainPrefix σ m = S₀ := by
          have h_chainPrefix_m : chainPrefix σ (m + 1) = insert (σ ⟨m, hm'⟩) (chainPrefix σ m) := by
            exact?;
          rw [ Finset.ext_iff ] at h_chainPrefix_m;
          ext x; specialize h_chainPrefix_m x; by_cases hx : x = σ ⟨ m, hm' ⟩ <;> simp_all +decide ;
          exact?;
        grind;
    rw [ h_count, Finset.card_biUnion, Finset.sum_congr rfl ];
    · intro S₀ hS₀;
      rw [ Finset.card_biUnion ];
      intro e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
    · intros S₀ hS₀ S₁ hS₁ h_inter;
      simp_all +decide [ Finset.disjoint_left ];
      intro σ hσ₀ hσ₁ hσ₂ hσ₃ hσ₄; contrapose! h_inter; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_inter a; aesop;
  rw [ h_count ];
  rw [ Finset.sum_congr rfl fun S₀ hS₀ => Finset.sum_congr rfl fun e he => h_fiber_size_succ S₀ ( Finset.mem_filter.mp hS₀ |>.2.1 ) ( Finset.mem_filter.mp hS₀ |>.2.2 ) e ( Finset.mem_filter.mp he |>.2.1 ) ( Finset.mem_filter.mp he |>.2.2 ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul _ _ _ ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ h_ext x ( Finset.mem_filter.mp hx |>.2.2 ) ( by linarith [ Finset.mem_filter.mp hx |>.2.1, Nat.sub_add_cancel hm'.le ] ) ] ] ; simp +decide [ Nat.sub_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2.1 ] ] ; simp +decide [ countP, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

/-! ## Transition bound -/

lemma total_transitions_le_factorial
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅) :
    ∑ m ∈ Finset.range (N + 1),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
        P (chainPrefix σ m) ∧ ¬ P (chainPrefix σ (m - 1)))).card ≤
    Nat.factorial N := by
  have h_perm_bound : ∀ σ : Equiv.Perm (Fin N), (∑ m ∈ Finset.range (N + 1), if P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)) then 1 else 0) ≤ 1 := by
    intro σ;
    convert transition_count_le_one P h_interval h_empty σ using 1;
    rw [ Finset.card_filter, Finset.sum_congr rfl ] ; aesop;
  convert Finset.sum_le_sum fun σ _ => h_perm_bound σ using 1;
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.card_filter _ _ ];
  norm_num [ Finset.card_univ, Fintype.card_perm ]

/-! ## Main theorem -/

set_option maxHeartbeats 1600000 in
theorem transition_sum_le_one
    (R : ℕ → ℕ) (ext_val : ℕ → ℕ)
    (P : Finset (Fin N) → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset (Fin N)),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (h_ext : ∀ (S : Finset (Fin N)), P S → S.card < N →
      ((Finset.univ : Finset (Fin N)).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card)
    (hR : ∀ m, R m = countP P m) :
    ∑ m ∈ Finset.range (N + 1),
      ((R m : ℝ) / (N.choose m : ℝ) -
       (ext_val (m - 1) : ℝ) / ((N : ℝ) - ↑m + 1) *
       ((R (m - 1) : ℝ) / (N.choose (m - 1) : ℝ))) ≤ 1 := by
  have h_total_transitions_le_factorial : ∑ m ∈ Finset.range (N + 1), ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) ≤ Nat.factorial N := by
    exact_mod_cast total_transitions_le_factorial P h_interval h_empty;
  have h_sum_eq : ∀ m ∈ Finset.range (N + 1), ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = (Nat.factorial N : ℝ) * ((R m : ℝ) / (Nat.choose N m : ℝ) - (ext_val (m - 1) : ℝ) / ((N - m + 1) : ℝ) * ((R (m - 1) : ℝ) / (Nat.choose N (m - 1) : ℝ))) := by
    intro m hm
    have h_card : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = (Nat.factorial m * Nat.factorial (N - m) : ℝ) * (R m : ℝ) - (if m = 0 then 0 else (Nat.factorial (m - 1) * Nat.factorial (N - m) : ℝ) * (ext_val (m - 1) : ℝ) * (R (m - 1) : ℝ)) := by
      have h_card : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ ¬P (chainPrefix σ (m - 1)))).card : ℝ) = ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m))).card : ℝ) - (if m = 0 then 0 else ((Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => P (chainPrefix σ m) ∧ P (chainPrefix σ (m - 1)))).card : ℝ)) := by
        rcases m with ( _ | m ) <;> simp_all +decide [ Finset.filter_and ];
        rw [ eq_sub_iff_add_eq', ← Nat.cast_add ];
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with x ; by_cases hx : P ( chainPrefix x m ) <;> aesop;
        · exact Finset.disjoint_left.mpr ( by aesop );
      convert h_card using 2;
      · convert count_perm_with_P P m ( Finset.mem_range_succ_iff.mp hm ) |> Eq.symm using 1;
        rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; rw [ hR ] ; ring;
      · split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        have := count_perm_with_P_pair P m ( Nat.pos_of_ne_zero ‹_› ) hm ext_val h_ext; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    split_ifs at * <;> simp_all +decide [ Nat.cast_choose, mul_sub ];
    · cases h_card <;> simp_all +decide [ Nat.factorial_ne_zero ];
    · rw [ Nat.cast_choose ];
      · field_simp;
        rw [ show N - ( m - 1 ) = N - m + 1 by omega ] ; norm_num [ Nat.factorial_succ ] ; ring;
        rw [ show ( 1 + ( N - m : ℝ ) ) = ( N - m + 1 : ℝ ) by ring ] ; norm_num [ Nat.cast_sub hm ] ; ring;
        nlinarith only [ inv_mul_cancel_left₀ ( show ( 1 + ( N - m : ℝ ) ) ≠ 0 by linarith [ show ( m : ℝ ) ≤ N by norm_cast ] ) ( ( N - m ).factorial * ( m - 1 ).factorial * ext_val ( m - 1 ) * countP P ( m - 1 ) ) ];
      · exact Nat.sub_le_of_le_add <| by linarith;
  rw [ Finset.sum_congr rfl h_sum_eq, ← Finset.mul_sum _ _ _ ] at h_total_transitions_le_factorial ; nlinarith [ show ( N.factorial : ℝ ) > 0 by positivity ]

/-! ## Generalized version for arbitrary finite types -/

set_option maxHeartbeats 1600000 in
/-- Generalized transition sum bound for arbitrary finite types. -/
theorem transition_sum_le_one_gen
    {α : Type} [Fintype α] [DecidableEq α]
    (R : ℕ → ℕ) (ext_val : ℕ → ℕ)
    (P : Finset α → Prop) [DecidablePred P]
    (h_interval : ∀ (S₁ S₂ S₃ : Finset α),
      S₁ ⊆ S₂ → S₂ ⊆ S₃ → P S₁ → P S₃ → P S₂)
    (h_empty : ¬ P ∅)
    (h_ext : ∀ (S : Finset α), P S → S.card < Fintype.card α →
      ((Finset.univ : Finset α).filter (fun e => e ∉ S ∧ P (insert e S))).card =
        ext_val S.card)
    (hR : ∀ m, R m = (Finset.univ.filter (fun S : Finset α => S.card = m ∧ P S)).card) :
    let N := Fintype.card α
    ∑ m ∈ Finset.range (N + 1),
      ((R m : ℝ) / (N.choose m : ℝ) -
       (ext_val (m - 1) : ℝ) / ((N : ℝ) - ↑m + 1) *
       ((R (m - 1) : ℝ) / (N.choose (m - 1) : ℝ))) ≤ 1 := by
  -- Define P' : Finset (Fin N) → Prop by P'(S) = P(S.map e.symm.toEmbedding).
  set N := Fintype.card α
  obtain ⟨e, he⟩ : ∃ e : α ≃ Fin N, True := by
    exact ⟨ Fintype.equivFin α, trivial ⟩;
  convert transition_sum_le_one R ext_val ( fun S => P ( S.map e.symm.toEmbedding ) ) _ _ _ _ using 1;
  · aesop;
  · aesop;
  · intro S hS hS'; specialize h_ext ( S.map e.symm.toEmbedding ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
    convert h_ext using 1;
    rw [ Finset.card_filter, Finset.card_filter ];
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;
    grind;
  · intro m; rw [ hR ] ; unfold countP; simp +decide [ Finset.card_map ] ;
    refine' Finset.card_bij ( fun S hS => S.map e.toEmbedding ) _ _ _ <;> simp +decide [ Finset.card_map ];
    · simp +contextual [ Finset.map_map, Equiv.symm_apply_apply ];
    · exact fun b hb hb' => ⟨ _, ⟨ by simpa [ Finset.card_map ] using hb, hb' ⟩, by ext x; simp +decide ⟩

end EdgeOrderingCount
end EdgeOrderingSection

/-! ==================================================================
    Pólya-Wright Theorem
    (originally PolyaWright.lean)
    ================================================================== -/

section PolyaWrightSection

/-!
# Proof of the Pólya–Wright Theorem

The proof uses Burnside's lemma and bounds the contributions from
non-identity permutations using an orbit-size argument on edges.
-/


open Finset Function SimpleGraph Filter
open scoped Classical

namespace PolyaWright

open UniqueSubgraphs

/-! ## Auxiliary: Graph ↔ Bool function on edges -/

/-- Encode a graph as a Boolean function on non-diagonal Sym2 elements. -/
def graphToFun {n : ℕ} (G : SimpleGraph (Fin n)) :
    {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool :=
  fun ⟨e, _⟩ => e.lift ⟨fun a b => decide (G.Adj a b),
    fun a b => by simp [G.adj_comm]⟩

/-- Decode a Boolean function on edges back to a graph. -/
def funToGraph {n : ℕ}
    (f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ (h : u ≠ v), f ⟨s(u, v), by rwa [Sym2.isDiag_iff_proj_eq]⟩ = true
  symm u v := by
    rintro ⟨h1, h2⟩; refine ⟨h1.symm, ?_⟩
    convert h2 using 2; exact Subtype.ext (Sym2.eq_swap)
  loopless := ⟨fun v h => h.1 rfl⟩

/-- Graphs on `Fin n` are equivalent to Boolean functions on non-diagonal Sym2. -/
def graphEquivFun (n : ℕ) :
    SimpleGraph (Fin n) ≃ ({e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool) where
  toFun := graphToFun
  invFun := funToGraph
  left_inv G := by
    ext u v; simp only [funToGraph, graphToFun, Sym2.lift_mk, decide_eq_true_eq]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨G.ne_of_adj h, h⟩⟩
  right_inv f := by
    ext ⟨e, he⟩; induction e using Sym2.ind with
    | h u v =>
      simp only [graphToFun, Sym2.lift_mk, funToGraph]
      have hne : u ≠ v := by rwa [Sym2.isDiag_iff_proj_eq] at he
      simp [hne]

/-- The action of σ on non-diagonal Sym2 elements (edges). -/
def edgePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm {e : Sym2 (Fin n) // ¬ e.IsDiag} where
  toFun e := ⟨e.val.map σ, by rw [Sym2.isDiag_map σ.injective]; exact e.prop⟩
  invFun e := ⟨e.val.map σ.symm, by rw [Sym2.isDiag_map σ.symm.injective]; exact e.prop⟩
  left_inv := by intro ⟨e, he⟩; simp [Sym2.map_map]
  right_inv := by intro ⟨e, he⟩; simp [Sym2.map_map]

/-- `σ • G = G` iff `graphToFun G` is invariant under `edgePerm σ`. -/
theorem fixed_iff_invariant {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    σ • G = G ↔ ∀ e, graphToFun G (edgePerm σ e) = graphToFun G e := by
  constructor
  · intro h ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v =>
      change decide (G.Adj (σ u) (σ v)) = decide (G.Adj u v)
      congr 1; exact propext (by
        have : (σ • G).Adj (σ u) (σ v) = G.Adj (σ u) (σ v) := by rw [h]
        simp [smul_adj] at this; exact this.symm)
  · intro h
    ext u v
    simp only [smul_adj]
    by_cases huv : u = v
    · subst huv; simp
    · have hne' : σ.symm u ≠ σ.symm v := fun heq => huv (σ.symm.injective heq)
      have h' := h ⟨s(σ.symm u, σ.symm v), by rwa [Sym2.isDiag_iff_proj_eq]⟩
      change decide (G.Adj (σ (σ.symm u)) (σ (σ.symm v))) = _ at h'
      simp only [Equiv.apply_symm_apply] at h'
      rw [Equiv.Perm.inv_def]
      exact (decide_eq_decide.mp h'.symm)

/-- A σ-fixed graph corresponds to a σ-invariant Boolean edge function. -/
def fixedBy_equiv_invariant {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) ≃
    {f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool //
      ∀ e, f (edgePerm σ e) = f e} :=
  (graphEquivFun n).subtypeEquiv (fun G => by
    simp only [graphEquivFun, MulAction.mem_fixedBy]
    exact fixed_iff_invariant σ G)

/-! ## Step 1: Cardinality of SimpleGraph (Fin n) -/

/-- The number of simple graphs on `Fin n` equals `2^{n choose 2}`. -/
theorem card_simpleGraph_fin (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [card_simpleGraph]

theorem card_invariant_bool_le {S : Type*} [Fintype S] [DecidableEq S]
    (σ : Equiv.Perm S) :
    Fintype.card {f : S → Bool // ∀ s, f (σ s) = f s} ≤
    2 ^ ((Fintype.card S + Fintype.card (Function.fixedPoints σ)) / 2) := by
  -- The number of orbits of σ on S is at most the number of fixed points plus half the number of non-fixed points.
  have h_orbits : (Fintype.card (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S))) ≤ (Fintype.card (fixedPoints σ)) + ((Fintype.card S) - (Fintype.card (fixedPoints σ))) / 2 := by
    -- Let's count the number of orbits.
    have h_orbits_card : ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) = Fintype.card S := by
      simp +decide only [card_filter, Fintype.card_eq_sum_ones];
      rw [ Finset.sum_comm ] ; aesop;
    -- Each orbit is either a fixed point or a cycle of length at least 2.
    have h_orbit_length : ∀ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) ≥ if x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S)) then 1 else 2 := by
      intro x
      by_cases hx : x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S));
      · obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact if_pos hx ▸ Finset.card_pos.mpr ⟨ y, by aesop ⟩ ;
      · obtain ⟨ y, hy ⟩ := Quotient.exists_rep x; simp_all +decide [ Quotient.eq ] ;
        refine' le_trans _ ( Finset.card_mono <| show { y, σ y } ⊆ Finset.filter ( fun z => ⟦z⟧ = x ) Finset.univ from _ );
        · grind;
        · simp +decide [ ← hy, Finset.insert_subset_iff ];
          exact Quotient.sound ⟨ ⟨ σ, Subgroup.mem_zpowers σ ⟩, rfl ⟩;
    have h_orbit_length_sum : ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), (Finset.card (Finset.filter (fun y => ⟦y⟧ = x) (Finset.univ : Finset S))) ≥ ∑ x : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S), if x ∈ Finset.image (fun y => ⟦y⟧) (Finset.filter (fun y => σ y = y) (Finset.univ : Finset S)) then 1 else 2 := by
      exact Finset.sum_le_sum fun x _ => h_orbit_length x;
    simp_all +decide [ Finset.sum_ite ];
    rw [ show ( Finset.filter ( fun x => ∃ a, σ a = a ∧ ⟦a⟧ = x ) Finset.univ : Finset ( Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) ) = Finset.image ( fun y => ⟦y⟧ ) ( Finset.filter ( fun y => σ y = y ) Finset.univ ) from ?_ ] at h_orbit_length_sum;
    · rw [ show ( Finset.filter ( fun x => ∀ y, σ y = y → ¬⟦y⟧ = x ) Finset.univ : Finset ( Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) ) = Finset.univ \ Finset.image ( fun y => ⟦y⟧ ) ( Finset.filter ( fun y => σ y = y ) Finset.univ ) from ?_, Finset.card_sdiff ] at h_orbit_length_sum <;> norm_num at *;
      · grind;
      · grind;
    · grind;
  -- Each σ-invariant function corresponds to a function on the orbits of σ.
  have h_invariant : { f : S → Bool // ∀ s, f (σ s) = f s } ≃ (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) S) → Bool) := by
    refine' Equiv.ofBijective ( fun f => fun q => f.val ( Classical.choose ( Quotient.exists_rep q ) ) ) ⟨ _, _ ⟩;
    · intro f g hfg;
      ext s;
      have := Classical.choose_spec ( Quotient.exists_rep ( ⟦s⟧ : Quotient ( MulAction.orbitRel ( Subgroup.zpowers σ ) S ) ) );
      rw [ Quotient.eq ] at this;
      obtain ⟨ k, hk ⟩ := this;
      have h_eq : ∀ m : ℕ, f.val (σ^[m] s) = f.val s ∧ g.val (σ^[m] s) = g.val s := by
        intro m; induction m <;> simp_all +decide [ Function.iterate_succ_apply', Equiv.Perm.smul_def ] ;
        exact ⟨ by rw [ f.2, ‹ ( f : S → Bool ) ( ( σ ^ _ ) s ) = ( f : S → Bool ) s ∧ ( g : S → Bool ) ( ( σ ^ _ ) s ) = ( g : S → Bool ) s ›.1 ], by rw [ g.2, ‹ ( f : S → Bool ) ( ( σ ^ _ ) s ) = ( f : S → Bool ) s ∧ ( g : S → Bool ) ( ( σ ^ _ ) s ) = ( g : S → Bool ) s ›.2 ] ⟩;
      obtain ⟨ m, hm ⟩ := k.2;
      have := h_eq ( Int.toNat ( m % orderOf σ ) ) ; simp_all +decide [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr ( ne_of_gt ( orderOf_pos σ ) ) ) ) ] ;
      replace hm := congr_arg ( fun x => x s ) hm ; simp_all +decide [ zpow_mod_orderOf ] ;
      replace hfg := congr_fun hfg ⟦s⟧; aesop;
    · intro g
      use ⟨fun s => g (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) S) s), by
        simp +decide [ Quotient.eq ];
        congr! 1;
        exact Quotient.sound ⟨ ⟨ σ, Subgroup.mem_zpowers σ ⟩, rfl ⟩⟩
      generalize_proofs at *;
      ext q; have := Classical.choose_spec ( Quotient.exists_rep q ) ; aesop;
  have := Fintype.card_congr h_invariant;
  simp_all +decide [ Fintype.card_pi ];
  refine' pow_le_pow_right₀ ( by decide ) _;
  grind

/-
proved by subagent (long proof)

Bound on the number of edges fixed by σ: at most `s.choose 2 + (n-s)/2`
    where s is the number of vertex fixed points.
-/
set_option maxHeartbeats 800000 in
theorem card_fixedPoints_edgePerm_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (Function.fixedPoints (edgePerm σ)) ≤
    (Fintype.card (Function.fixedPoints σ)).choose 2 +
    (n - Fintype.card (Function.fixedPoints σ)) / 2 := by
  -- An edge e = s(u,v) is a fixed point of edgePerm σ iff {σ(u), σ(v)} = {u, v} (as an unordered pair). This happens in two cases:
  -- 1. Both u and v are fixed points of σ (σ(u) = u and σ(v) = v). There are (s choose 2) such edges where s = Fintype.card (fixedPoints σ).
  -- 2. σ swaps u and v: σ(u) = v and σ(v) = u, i.e., (u,v) form a 2-cycle of σ. The number of 2-cycles is at most (n-s)/2 since each 2-cycle uses 2 non-fixed points.

  have card_fixed_edges : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e)).card ≤ (Fintype.card (fixedPoints σ)).choose 2 + (n - Fintype.card (fixedPoints σ)) / 2 := by
    have h_fixed_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk (u, v) ∧ u ∈ fixedPoints σ ∧ v ∈ fixedPoints σ)).card ≤ (Fintype.card (fixedPoints σ)).choose 2 := by
      have h_fixed_edges : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ e ∈ Finset.image (fun (uv : Fin n × Fin n) => Sym2.mk uv) (Finset.offDiag (Finset.univ.filter (fun u => u ∈ fixedPoints σ))))).card ≤ (Finset.univ.filter (fun u => u ∈ fixedPoints σ)).card.choose 2 := by
        rw [ ← Finset.card_powersetCard ];
        refine' le_of_eq _;
        refine' Finset.card_bij ( fun e he => Finset.filter ( fun u => u ∈ e ) Finset.univ ) _ _ _ <;> simp +decide [ Finset.subset_iff ];
        · rintro a ha x y hx hy hxy rfl; simp_all +decide [ IsFixedPt ] ;
          exact Finset.card_eq_two.mpr ⟨ x, y, by aesop ⟩;
        · intro a₁ ha₁ x y hx hy hxy h₁ a₂ ha₂ u v hu hv huv h₂ h₃; ext w; replace h₃ := Finset.ext_iff.mp h₃ w; aesop;
        · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; use a, b; aesop;
      refine le_trans ?_ ( h_fixed_edges.trans ?_ );
      · refine Finset.card_le_card ?_;
        simp +contextual [ Finset.subset_iff ];
        intro e he hσ u v hu hv hv'; use u, v; aesop;
      · rw [ Fintype.card_subtype ]
    have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk (u, v) ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card ≤ (n - Fintype.card (fixedPoints σ)) / 2 := by
      have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk (u, v) ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card / 2 := by
        have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk (u, v) ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).card * 2 ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card := by
          have h_swap_points : (Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ Sym2.map σ e = e ∧ ∃ u v : Fin n, e = Sym2.mk (u, v) ∧ u ∉ fixedPoints σ ∧ v ∉ fixedPoints σ ∧ σ u = v ∧ σ v = u)).sum (fun e => (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ ∧ e = Sym2.mk (u, σ u))).card) ≤ (Finset.univ.filter (fun u : Fin n => u ∉ fixedPoints σ)).card := by
            rw [ ← Finset.card_biUnion ];
            · exact Finset.card_le_card fun x hx => by aesop;
            · intros e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
              grind;
          refine le_trans ?_ h_swap_points;
          rw [ Finset.sum_const_nat ];
          simp +contextual [ Finset.card_eq_two ];
          intro e he₁ he₂ u hu₁ hu₂ hu₃ hu₄; use σ u, u; simp_all +decide [ IsFixedPt ] ;
          grind;
        rwa [ Nat.le_div_iff_mul_le zero_lt_two ];
      simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
      convert h_swap_points using 1
    refine le_trans ?_ ( add_le_add h_fixed_points h_swap_points );
    rw [ ← Finset.card_union_add_card_inter ];
    refine' le_add_right ( Finset.card_le_card _ );
    intro e he; simp_all +decide [ Sym2.forall ] ;
    rcases e with ⟨ u, v ⟩ ; simp_all +decide [ IsFixedPt, Sym2.eq_swap ] ;
    grind +ring;
  convert card_fixed_edges using 1;
  refine' Finset.card_bij ( fun x hx => x.val ) _ _ _ <;> simp +decide [ edgePerm ];
  · grind +suggestions;
  · exact fun b hb hb' => ⟨ hb, Subtype.ext hb' ⟩

/-- The main combinatorial bound: |Fix(σ)| ≤ 2^{(N + f) / 2}. -/
theorem card_fixedBy_le_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) ≤
    2 ^ ((n.choose 2 +
      Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
  calc Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ)
      = Fintype.card {f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool //
          ∀ e, f (edgePerm σ e) = f e} := by
        exact Fintype.card_congr (fixedBy_equiv_invariant σ)
    _ ≤ 2 ^ ((Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag} +
          Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
        exact card_invariant_bool_le (edgePerm σ)
    _ = 2 ^ ((n.choose 2 +
          Fintype.card (Function.fixedPoints (edgePerm σ))) / 2) := by
        congr 1; congr 1; congr 1
        rw [@Sym2.card_subtype_not_diag (Fin n) _ _, Fintype.card_fin]

/-! ## Step 3: From Burnside to the ratio -/

/-
Burnside gives: `numIsoClasses n / paperDenom n` equals the Burnside sum
    divided by `2^N`.
-/
theorem ratio_eq_burnside_over_two_pow (n : ℕ) :
    (numIsoClasses n : ℝ) / paperDenom n =
    (∑ σ : Equiv.Perm (Fin n),
      (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) /
    (2 ^ n.choose 2 : ℝ) := by
  unfold paperDenom;
  field_simp;
  exact_mod_cast UniqueSubgraphs.burnside_applied n |> Eq.symm

/-
|Fix(1)| = 2^(n choose 2) since every graph is fixed by the identity.
-/
theorem card_fixedBy_one (n : ℕ) :
    Fintype.card (MulAction.fixedBy (SimpleGraph (Fin n))
      (1 : Equiv.Perm (Fin n))) =
    2 ^ n.choose 2 := by
      convert UniqueSubgraphs.card_simpleGraph n using 1;
      simp +decide [ MulAction.fixedBy ]

theorem ratio_eq_one_plus_remainder (n : ℕ) :
    (numIsoClasses n : ℝ) / paperDenom n = 1 +
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (· ≠ 1),
      (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) /
    (2 ^ n.choose 2 : ℝ) := by
  rw [ ratio_eq_burnside_over_two_pow ];
  rw [ Finset.sum_eq_add_sum_diff_singleton <| Finset.mem_univ ( 1 : Equiv.Perm ( Fin n ) ) ];
  rw [ add_div' ] <;> norm_num [ Finset.filter_ne', card_fixedBy_one ];
  exact_mod_cast card_simpleGraph_fin n

/-! ## Step 4: The remainder tends to 0 -/

/-
The exponent bound: for σ ≠ 1, `(N + f)/2 - N ≤ -m(n-2)/4`
    where `m = n - s`, `s` = fixed points. This means `|Fix(σ)|/2^N ≤ 2^{-m(n-2)/4}`.
-/
theorem saving_lower_bound {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    let s := Fintype.card (Function.fixedPoints σ)
    let m := n - s
    (Fintype.card ↑(MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) ≤
    (2 : ℝ) ^ (n.choose 2 : ℤ) / (2 : ℝ) ^ ((m * (n - 2) / 4 : ℕ) : ℤ) := by
  rw [ le_div_iff₀ ] <;> norm_cast;
  · refine' le_trans ( Nat.mul_le_mul_right _ ( card_fixedBy_le_pow σ ) ) _;
    rw [ ← pow_add ];
    refine' pow_le_pow_right₀ ( by decide ) _;
    have h_exp_bound : Fintype.card (Function.fixedPoints (edgePerm σ)) ≤ (Fintype.card (Function.fixedPoints σ)).choose 2 + (n - Fintype.card (Function.fixedPoints σ)) / 2 := by
      convert card_fixedPoints_edgePerm_le σ using 1;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
    have h_exp_bound : (n + 1 + 1) * (n + 1) + #(filter (Membership.mem (fixedPoints ⇑σ)) univ) * (#(filter (Membership.mem (fixedPoints ⇑σ)) univ) - 1) + (n + 1 + 1 - #(filter (Membership.mem (fixedPoints ⇑σ)) univ)) + (n + 1 + 1 - #(filter (Membership.mem (fixedPoints ⇑σ)) univ)) * n ≤ 2 * (n + 1 + 1) * (n + 1) := by
      have h_exp_bound : #(filter (Membership.mem (fixedPoints ⇑σ)) univ) ≤ n + 1 + 1 := by
        exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      cases h : #(filter (Membership.mem (fixedPoints ⇑σ)) univ) <;> simp_all +decide [ Nat.mul_succ ] ; nlinarith [ Nat.sub_add_cancel h_exp_bound ];
      nlinarith only [ Nat.sub_add_cancel h_exp_bound ];
    grind;
  · positivity

/-
The number of permutations on Fin n that move exactly m elements
    is at most n^m.
-/
theorem count_perms_moving_m_le {n m : ℕ} :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun σ : Equiv.Perm (Fin n) => n - Fintype.card (Function.fixedPoints σ) = m)).card ≤ n ^ m := by
  -- The number of permutations fixing at least $n - m$ points is at most $n^m$.
  have h_count_fix : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => n - Fintype.card (Function.fixedPoints σ) = m)).card ≤ Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => σ) (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => Finset.card (Finset.filter (fun x => x∉(Function.fixedPoints σ)) (Finset.univ : Finset (Fin n))) = m))) := by
    simp +decide [ Fintype.card_subtype, Finset.filter_not, Finset.card_sdiff ];
  -- Each permutation with exactly $m$ non-fixed points can be constructed by choosing $m$ elements to permute and then permuting them.
  have h_construction : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => Finset.card (Finset.filter (fun x => x∉(Function.fixedPoints σ)) (Finset.univ : Finset (Fin n))) = m) ⊆ Finset.biUnion (Finset.powersetCard m (Finset.univ : Finset (Fin n))) (fun t => Finset.image (fun σ : Equiv.Perm {x // x ∈ t} => Equiv.Perm.ofSubtype σ) (Finset.univ : Finset (Equiv.Perm {x // x ∈ t}))) := by
    intro σ hσ; simp_all +decide [ Finset.subset_iff ] ;
    refine' ⟨ Finset.filter ( fun x => ¬IsFixedPt σ x ) Finset.univ, hσ, _ ⟩;
    refine' ⟨ Equiv.Perm.subtypePerm σ _, _ ⟩;
    all_goals simp +decide [ Equiv.Perm.ext_iff, Equiv.Perm.ofSubtype ];
    all_goals simp +decide [ IsFixedPt, Equiv.Perm.extendDomain ];
    intro x; by_cases hx : σ x = x <;> simp +decide [ hx, Equiv.Perm.subtypePerm ] ;
  refine le_trans h_count_fix <| le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun σ hσ => h_construction hσ ) <| le_trans ( Finset.card_biUnion_le ) ?_;
  refine' le_trans ( Finset.sum_le_sum fun _ _ => Finset.card_image_le ) _;
  simp +decide [ Finset.card_univ, Fintype.card_perm ];
  refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.factorial_le <| Finset.mem_powersetCard.mp hx |>.2.le ) _ ; norm_num [ Finset.card_univ ];
  rw [ Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _

end PolyaWright
end PolyaWrightSection

section ChernoffBoundSection
namespace ChernoffBound

/-- Count of true values in a Boolean vector. -/
abbrev boolCount {N : ℕ} (f : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

/-! ## Step 1: MGF factorization -/

/-
Key identity: the sum of exp(λ · count) over all Boolean vectors equals (1 + exp λ)^N.
    This is the product factorization of the moment generating function.
-/
lemma mgf_factorization (N : ℕ) (lam : ℝ) :
    ∑ f : Fin N → Bool, Real.exp (lam * (boolCount f : ℝ)) =
    (1 + Real.exp lam) ^ N := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ f : Fin N → Bool, ∏ i, Real.exp (lam * (if f i then 1 else 0)) = ∏ i : Fin N, (∑ b : Bool, Real.exp (lam * (if b then 1 else 0))) := by
        exact Eq.symm (Fintype.prod_sum fun i j => Real.exp (lam * if j = true then 1 else 0));
      convert h_fubini using 1;
      · simp +decide [ ← Real.exp_sum, mul_comm, Finset.sum_ite ];
      · norm_num [ add_comm, Finset.prod_pow ]

/-! ## Step 2: Exponential Markov inequality (counting version) -/

/-
Exponential Markov inequality: for λ ≥ 0, the number of Boolean vectors with
    count ≥ m is at most exp(-λm) times the MGF sum.
-/
lemma exp_markov_count (N : ℕ) (lam : ℝ) (m : ℝ) (hlam : lam ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ m)).card : ℝ) ≤
    Real.exp (-lam * m) *
    ∑ f : Fin N → Bool, Real.exp (lam * (boolCount f : ℝ)) := by
      have h_exp_markov : ∀ f : Fin N → Bool, (if (boolCount f : ℝ) ≥ m then 1 else 0) ≤ Real.exp (-lam * m) * Real.exp (lam * (boolCount f : ℝ)) := by
        intro f; split_ifs <;> simp_all +decide [ ← Real.exp_add ] ; nlinarith;
        positivity;
      simpa [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun f ( hf : f ∈ Finset.univ ) => h_exp_markov f

/-! ## Step 3: Bounding (1 + exp λ) -/

/-
The key analytical bound: (1 + exp λ) / 2 ≤ exp(λ/2 + λ²/8).
    This follows from (1+exp λ)/2 = exp(λ/2)·cosh(λ/2) and cosh(x) ≤ exp(x²/2).
-/
lemma one_plus_exp_half_bound (lam : ℝ) :
    (1 + Real.exp lam) / 2 ≤ Real.exp (lam / 2 + lam ^ 2 / 8) := by
      -- We'll use the exponential property to simplify the expression. Note that $(1 + \exp \lambda) / 2$ can be bounded above.
      have h_exp : (1 + Real.exp lam) / 2 ≤ Real.exp (lam / 2) * Real.cosh (lam / 2) := by
        rw [ Real.cosh_eq ] ; ring_nf ; norm_num [ ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf; norm_num;
      exact h_exp.trans ( by rw [ Real.exp_add ] ; exact mul_le_mul_of_nonneg_left ( by simpa using Real.cosh_le_exp_half_sq ( lam / 2 ) ) ( by positivity ) |> le_trans <| by ring_nf; norm_num )

/-! ## Step 4: Upper tail bound -/

/-
Upper tail Chernoff bound: the number of Boolean vectors with count ≥ N/2 + t
    is at most 2^N · exp(-2t²/N).
-/
lemma upper_tail_bound (N : ℕ) (t : ℝ) (ht : t ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
      by_cases hN : N = 0 <;> simp_all +decide [ neg_div, neg_mul ];
      · exact Finset.card_le_one.mpr ( by aesop );
      · -- Use exp_markov_count with lam₀ = 4*t/N, which is ≥ 0 since t ≥ 0 and N > 0.
        have h_exp_markov : ((Finset.univ.filter (fun f : Fin N → Bool => (boolCount f : ℝ) ≥ N / 2 + t)).card : ℝ) ≤
            Real.exp (-4 * t / N * (N / 2 + t)) * (∑ f : Fin N → Bool, Real.exp (4 * t / N * (boolCount f : ℝ))) := by
              convert exp_markov_count N ( 4 * t / N ) ( N / 2 + t ) ( by positivity ) using 1 ; ring;
        -- Now bound (1 + exp lam₀)^N: (1 + exp lam₀) = 2 * ((1 + exp lam₀)/2) ≤ 2 * exp(lam₀/2 + lam₀²/8) (by one_plus_exp_half_bound)
        have h_bound : (∑ f : Fin N → Bool, Real.exp (4 * t / N * (boolCount f : ℝ))) ≤ 2 ^ N * Real.exp (N * (4 * t / N / 2 + (4 * t / N) ^ 2 / 8)) := by
          rw [ mgf_factorization ];
          have := one_plus_exp_half_bound ( 4 * t / N );
          rw [ ← div_le_iff₀' ( by positivity ) ];
          simpa only [ ← div_pow, ← Real.exp_nat_mul ] using pow_le_pow_left₀ ( by positivity ) this _;
        convert h_exp_markov.trans ( mul_le_mul_of_nonneg_left h_bound <| Real.exp_nonneg _ ) using 1 ; ring;
        rw [ ← Real.exp_add ] ; norm_num [ sq, mul_assoc, hN ] ; ring;

/-! ## Step 5: Bit-flipping symmetry -/

/-
Flipping all bits sends count k to N - k.
-/
lemma boolCount_not {N : ℕ} (f : Fin N → Bool) :
    boolCount (fun i => !(f i)) = N - boolCount f := by
      unfold boolCount;
      simpa using Finset.card_compl ( Finset.filter ( fun i => f i = Bool.true ) Finset.univ )

/-
The bit-flip map is a bijection on `Fin N → Bool`.
-/
lemma boolFlip_bijective (N : ℕ) :
    Bijective (fun (f : Fin N → Bool) (i : Fin N) => !(f i)) := by
      exact ⟨ fun f g h => by ext i; simpa using congr_fun h i, fun f => ⟨ fun i => !f i, by aesop ⟩ ⟩

/-! ## Step 6: Lower tail bound -/

/-
Lower tail Chernoff bound via bit-flipping symmetry.
-/
lemma lower_tail_bound (N : ℕ) (t : ℝ) (_ht : t ≥ 0) :
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
      convert ChernoffBound.upper_tail_bound N t _ht using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ ← Equiv.sum_comp ( show ( Fin N → Bool ) ≃ ( Fin N → Bool ) from Equiv.ofBijective ( fun f => fun i => !f i ) ( by exact ChernoffBound.boolFlip_bijective N ) ) ];
      norm_num [ ChernoffBound.boolCount_not ];
      refine' congr_arg _ ( Finset.filter_congr fun x hx => _ );
      rw [ Nat.cast_sub ( show boolCount x ≤ N from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; constructor <;> intro <;> linarith

/-! ## Step 7: Combining tails -/

/-
The absolute deviation filter is contained in the union of upper and lower tails.
-/
lemma abs_deviation_card_le (N : ℕ) (t : ℝ) (_ht : t ≥ 0) :
    (Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card ≤
    (Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card +
    (Finset.univ.filter (fun f : Fin N → Bool =>
      (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        -- Let's simplify the set on the right-hand side.
        apply le_add_right; apply Finset.card_mono; intro f hf; simp_all +decide [ abs_eq_max_neg ] ;
        exact Or.imp ( fun h => by linarith! ) ( fun h => by linarith! ) hf

/-! ## Main Theorem -/

/-- **Chernoff bound** (Hoeffding's inequality for fair coin flips):
    For N independent fair coin flips, the number of Boolean vectors with sum deviating
    from N/2 by at least t is at most 2·2^N·exp(-2t²/N). -/
theorem chernoff_bound_prime :
    ∀ (N : ℕ) (t : ℝ), t ≥ 0 →
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ) ≤
    2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by
  intro N t ht
  have h1 := abs_deviation_card_le N t ht
  have h2 := upper_tail_bound N t ht
  have h3 := lower_tail_bound N t ht
  calc ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ)
      ≤ ((Finset.univ.filter (fun f : Fin N → Bool =>
        (boolCount f : ℝ) ≥ (N : ℝ) / 2 + t)).card : ℝ) +
        ((Finset.univ.filter (fun f : Fin N → Bool =>
        (boolCount f : ℝ) ≤ (N : ℝ) / 2 - t)).card : ℝ) := by exact_mod_cast h1
      _ ≤ (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) +
          (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by linarith
      _ = 2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) := by ring

end ChernoffBound
end ChernoffBoundSection

/-! ==================================================================
    Azuma-Hoeffding Inequality
    (originally AzumaHoeffding.lean)
    ================================================================== -/

section AzumaHoeffdingSection

/-!
# Azuma–Hoeffding Inequality (Bounded Differences)

This file proves the Azuma–Hoeffding inequality for functions of independent
fair coin flips with bounded differences. The statement is copied exactly from
`RequestProject/Main.lean`.

## Main result

`azuma_hoeffding_prime` — identical statement to `azuma_hoeffding` in Main.lean.

## Proof strategy

We use the exponential moment method:

1. **Exponential moment bound** (`exp_moment_bound`): For any λ ∈ ℝ,
   `∑ x, exp(λ(μ - f(x))) ≤ 2^n * exp(λ²/8 * ∑ bᵢ²)`.
   Proved by induction on n, using `avg_exp_le` (which follows from
   `Real.cosh_le_exp_half_sq`) and averaging over coordinates.

2. **Markov's inequality** (`markov_counting`): combinatorial counting form.

3. **Optimization**: Choose λ = 4t/∑bᵢ² (when ∑bᵢ² > 0) to get the
   optimal bound `exp(-2t²/∑bᵢ²)`.
-/


open Finset Real

namespace AzumaHoeffding

/-! ## Part 1: Analytic helper -/

/-
Key analytic inequality: exp(a+d) + exp(a-d) ≤ 2·exp(a + d²/2).
    Follows from cosh(d) ≤ exp(d²/2).
-/
lemma avg_exp_le (a d : ℝ) :
    exp (a + d) + exp (a - d) ≤ 2 * exp (a + d ^ 2 / 2) := by
  -- By dividing both sides of the inequality by $e^a$, we get $e^d + e^{-d} \leq 2e^{d^2/2}$.
  have h_div : Real.exp d + Real.exp (-d) ≤ 2 * Real.exp (d^2 / 2) := by
    have := @Real.cosh_le_exp_half_sq;
    have := this d; rw [ Real.cosh_eq ] at this; linarith;
  convert mul_le_mul_of_nonneg_left h_div ( Real.exp_nonneg a ) using 1 <;> push_cast [ sub_eq_add_neg, Real.exp_add ] <;> ring

/-! ## Part 2: Combinatorial infrastructure -/

/-
Decomposition of sums over `Fin (n+1) → Bool` into sums over
    the first coordinate and the remaining coordinates.
-/
lemma sum_fin_succ_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → Bool, f x =
    ∑ b : Bool, ∑ y : Fin n → Bool, f (Fin.cons b y) := by
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( x 0, x ∘ Fin.succ ) ) _ _ _ _ <;> simp +decide;
  · exact fun a₁ a₂ h₁ h₂ => funext fun i => by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
  · exact ⟨ fun b => ⟨ Fin.cons false b, rfl, rfl ⟩, fun b => ⟨ Fin.cons true b, rfl, rfl ⟩ ⟩;
  · exact fun x => by congr; ext i; induction i using Fin.inductionOn <;> aesop;

/-- The averaging function: average f over the first coordinate. -/
def avgFn {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun y => (f (Fin.cons false y) + f (Fin.cons true y)) / 2

/-! ## Part 3: Properties of avgFn -/

/-
The mean of avgFn equals the mean of f.
-/
lemma avgFn_mean {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ y : Fin n → Bool, avgFn f y) / ((2 : ℝ) ^ n) =
    (∑ x : Fin (n + 1) → Bool, f x) / ((2 : ℝ) ^ (n + 1)) := by
  simp +decide [ sum_fin_succ_eq, avgFn ];
  simpa only [ ← Finset.sum_div _ _ _, Finset.sum_add_distrib, add_comm ] using by ring;

/-
avgFn inherits bounded differences from f (with bounds shifted by Fin.succ).
-/
lemma avgFn_bounded_diff {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) (b : Fin (n + 1) → ℝ)
    (hbd : ∀ i : Fin (n + 1), ∀ x y : Fin (n + 1) → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) :
    ∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |avgFn f x - avgFn f y| ≤ b (Fin.succ i) := by
  -- By definition of `avgFn`, we have:
  intros i x y hxy
  simp [avgFn];
  rw [ abs_le ];
  constructor <;> linarith [ abs_le.mp ( hbd i.succ ( Fin.cons false x ) ( Fin.cons false y ) fun j hj => by cases j using Fin.inductionOn <;> aesop ), abs_le.mp ( hbd i.succ ( Fin.cons true x ) ( Fin.cons true y ) fun j hj => by cases j using Fin.inductionOn <;> aesop ) ]

theorem exp_moment_bound (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ)
    (hbd : ∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (lam : ℝ) :
    ∑ x : Fin n → Bool, exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≤
    ((2 : ℝ) ^ n) * exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2) := by
  revert n f b hbd;
  refine fun n => Nat.recOn n ?_ ?_;
  · aesop;
  · intro n ih f b hbd;
    -- Let μ = (∑ x, f x) / 2^(n+1) and g = avgFn f, μ_g = (∑ y, g y) / 2^n.
    set μ : ℝ := (∑ x, f x) / 2 ^ (n + 1)
    set g : (Fin n → Bool) → ℝ := avgFn f
    set μ_g : ℝ := (∑ y, g y) / 2 ^ n;
    -- By avgFn_mean, μ_g = μ.
    have hμ_g : μ_g = μ := by
      exact avgFn_mean f;
    -- Now f(cons false y) = g(y) - d(y) and f(cons true y) = g(y) + d(y) where d(y) = (f(cons true y) - f(cons false y))/2.
    have h_decomp : ∀ y : Fin n → Bool, Real.exp (lam * (μ - f (Fin.cons false y))) + Real.exp (lam * (μ - f (Fin.cons true y))) ≤ 2 * Real.exp (lam * (μ_g - g y) + lam ^ 2 * (b 0) ^ 2 / 8) := by
      intro y
      set d := (f (Fin.cons true y) - f (Fin.cons false y)) / 2
      have h_exp : Real.exp (lam * (μ - f (Fin.cons false y))) + Real.exp (lam * (μ - f (Fin.cons true y))) ≤ 2 * Real.exp (lam * (μ_g - g y) + lam ^ 2 * d ^ 2 / 2) := by
        convert avg_exp_le ( lam * ( μ_g - g y ) ) ( lam * d ) using 1 <;> ring;
        simp +zetaDelta at *;
        rw [ hμ_g ] ; ring;
        unfold avgFn; ring;
      -- By cons_diff_bound, |f(cons true y) - f(cons false y)| ≤ b 0, so d² ≤ (b 0)² / 4.
      have h_d_bound : d ^ 2 ≤ (b 0) ^ 2 / 4 := by
        simp +zetaDelta at *;
        nlinarith only [ abs_le.mp ( hbd 0 ( Fin.cons true y ) ( Fin.cons false y ) fun j hj => by cases j using Fin.inductionOn <;> tauto ) ];
      exact h_exp.trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith ) zero_le_two );
    -- By the induction hypothesis applied to g with bounds (b ∘ Fin.succ) using avgFn_bounded_diff:
    have h_ind : ∑ y : Fin n → Bool, Real.exp (lam * (μ_g - g y)) ≤ 2 ^ n * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b (Fin.succ i)) ^ 2) := by
      exact ih g (fun i => b (Fin.succ i)) (avgFn_bounded_diff f b hbd);
    -- Combining the decomposition and induction hypothesis:
    have h_combined : ∑ x : Fin (n + 1) → Bool, Real.exp (lam * (μ - f x)) ≤ 2 * Real.exp (lam ^ 2 * (b 0) ^ 2 / 8) * ∑ y : Fin n → Bool, Real.exp (lam * (μ_g - g y)) := by
      convert Finset.sum_le_sum fun y _ => h_decomp y using 1;
      any_goals exact Finset.univ;
      · rw [ sum_fin_succ_eq ];
        rw [ Finset.sum_comm ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_eq_add ( false ) ( true ) ] <;> simp +decide ;
      · norm_num [ Real.exp_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    convert h_combined.trans ( mul_le_mul_of_nonneg_left h_ind <| by positivity ) using 1 ; ring;
    rw [ ← Real.exp_add ] ; norm_num [ Fin.sum_univ_succ ] ; ring

/-! ## Part 5: Counting Markov's inequality -/

/-
Counting form of Markov's inequality.
-/
lemma markov_counting {α : Type*} [Fintype α] (g : α → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, 0 ≤ g x) :
    ((Finset.univ.filter (fun x => g x ≥ c)).card : ℝ) * c ≤ ∑ x, g x := by
  have := Finset.sum_le_sum fun x ( hx : x ∈ Finset.univ ) => show g x ≥ if g x ≥ c then c else 0 by split_ifs <;> linarith [ hg x ];
  simpa [ Finset.sum_ite ] using this

/-! ## Part 6: Main theorem -/

/-
**Azuma–Hoeffding inequality** (bounded differences / McDiarmid's inequality).
    Exact copy of the statement from `Main.lean`.
-/
theorem azuma_hoeffding_prime :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i : Fin n, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let μ := (∑ x : (Fin n → Bool), f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter (fun x : Fin n → Bool => f x ≤ μ - t)).card : ℝ) ≤
    (2 ^ n : ℝ) * exp (-2 * t ^ 2 / ∑ i : Fin n, (b i) ^ 2) := by
  intros n f b hbd hb t ht;
  -- Use exp_moment_bound with lam = 4*t/S.
  set lam := 4 * t / (∑ i, b i ^ 2)
  have h_exp_moment : ∑ x : Fin n → Bool, Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≤ ((2 : ℝ) ^ n) * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2) := by
    exact exp_moment_bound n f b hbd lam;
  -- Apply Markov's inequality to the exponential moment bound.
  have h_markov : ((Finset.univ.filter (fun x => Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≥ Real.exp (lam * t))).card : ℝ) ≤ ((2 : ℝ) ^ n) * Real.exp (lam ^ 2 / 8 * ∑ i : Fin n, (b i) ^ 2 - lam * t) := by
    have h_markov : ((Finset.univ.filter (fun x => Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) ≥ Real.exp (lam * t))).card : ℝ) * Real.exp (lam * t) ≤ ∑ x : Fin n → Bool, Real.exp (lam * ((∑ z : Fin n → Bool, f z) / ((2 : ℝ) ^ n) - f x)) := by
      have := markov_counting ( fun x => Real.exp ( lam * ( ( ∑ z, f z ) / 2 ^ n - f x ) ) ) ( Real.exp ( lam * t ) ) ( Real.exp_pos _ ) ( fun x => Real.exp_nonneg _ ) ; aesop;
    rw [ Real.exp_sub ];
    rw [ ← mul_div_assoc, le_div_iff₀ ( Real.exp_pos _ ) ] ; linarith;
  refine le_trans ?_ ( h_markov.trans ?_ );
  · norm_num;
    exact Finset.card_mono fun x hx => by exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by nlinarith [ Finset.mem_filter.mp hx, show 0 ≤ lam by exact div_nonneg ( mul_nonneg zero_le_four ht ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ⟩ ;
  · grind

end AzumaHoeffding
end AzumaHoeffdingSection

/-! ==================================================================
    Main Theorem — Unique Subgraphs Are Rare
    ================================================================== -/

/-!
# Unique Subgraphs Are Rare

Formalization of the paper "Unique subgraphs are rare" by Domagoj Bradač and Micha Christoph.

## Overview

A folklore result attributed to Pólya states that there are (1 + o(1))·2^{n choose 2}/n!
non-isomorphic graphs on n vertices. Given two graphs G and H on n vertices, we say that
G is a *unique subgraph* of H if H contains exactly one subgraph isomorphic to G.

For an n-vertex graph H, let f(H) be the number of non-isomorphic unique subgraphs of H
divided by 2^{n choose 2}/n!, and let f(n) denote the maximum of f(H) over all n-vertex
graphs H. Erdős asked (1975) whether there exists δ > 0 such that f(n) > δ for all n.

The paper shows that f(n) → 0, confirming Erdős' intuition that no graph on n vertices
contains a constant proportion of all graphs as unique subgraphs.

## Structure

The proof proceeds in three steps:
1. **Lemma 2.1** reduces f(H) to Pr_{G ∼ G(n,1/2)}[G has a unique embedding into H] + o(1).
2. **Lemma 2.2** shows that if this probability is ≥ δ, then H must be very dense:
   e(H) ≥ C(n,2) - Cn.
3. **Lemma 2.3** shows that for very dense H, the probability is o(1).

The main theorem follows from the composition of Lemmas 2.2 and 2.3.

## Black-box theorems (now fully proved)

Three standard results were previously taken as black boxes and are now
proved in separate files:
1. **Pólya–Wright theorem** — proved in `PolyaWright.lean`
2. **Chernoff bound** — proved in `ChernoffBound.lean`
3. **Azuma–Hoeffding inequality** — proved in `AzumaHoeffding.lean`

Core definitions and Burnside machinery are in `MainDefs.lean`.

## References

- Bradač, D., Christoph, M. "Unique subgraphs are rare" (2024)
- Erdős, P. "Problems and results in graph theory and combinatorial analysis" (1975)
-/


open Finset Function SimpleGraph
open scoped Classical

namespace UniqueSubgraphs

/-! ## Black-Box Theorems (proved via standalone files) -/

theorem chernoff_bound :
    ∀ (N : ℕ) (t : ℝ), t ≥ 0 →
    ((Finset.univ.filter (fun f : Fin N → Bool =>
      |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (N : ℝ) / 2| ≥ t)).card : ℝ) ≤
    2 * (2 ^ N : ℝ) * Real.exp (-2 * t ^ 2 / ↑N) :=
  ChernoffBound.chernoff_bound_prime

/-- **Azuma–Hoeffding inequality** (bounded differences / McDiarmid's inequality).
    Proved in `AzumaHoeffding.lean`. -/
theorem azuma_hoeffding :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i : Fin n, ∀ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i : Fin n, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let μ := (∑ x : (Fin n → Bool), f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter (fun x : Fin n → Bool => f x ≤ μ - t)).card : ℝ) ≤
    (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / ∑ i : Fin n, (b i) ^ 2) :=
  AzumaHoeffding.azuma_hoeffding_prime

/-! ## Derivation of Key Lemmas -/

/-! ### Derivation of almost_all_trivial_aut -/

theorem uniquelyEmbeds_iff_uniqueSub_trivialAut {n : ℕ} (G H : SimpleGraph (Fin n)) :
    UniquelyEmbeds G H ↔ IsUniqueSubgraph G H ∧ (autFinset G).card = 1 := by
  constructor;
  · intro h;
    constructor;
    · obtain ⟨φ, hφ⟩ : ∃! φ : Equiv.Perm (Fin n), IsEmbedding G H φ := by
        exact?;
      use ⟨ Set.univ, fun u v => G.Adj ( φ⁻¹ u ) ( φ⁻¹ v ), by
        exact fun { v w } h => by simpa using hφ.1 ( φ⁻¹ v ) ( φ⁻¹ w ) h;, by
        exact fun _ => Set.mem_univ _, by
        exact fun u v huv => G.symm huv ⟩
      generalize_proofs at *;
      constructor;
      · refine' ⟨ _, _ ⟩;
        · exact?;
        · refine' ⟨ _, _ ⟩;
          exacts [ φ⁻¹, by simp +decide [ SimpleGraph.spanningCoe ] ];
      · rintro ⟨ S, hS ⟩ ⟨ hS₁, ⟨ f ⟩ ⟩;
        have h_iso : ∃ ψ : Equiv.Perm (Fin n), ∀ u v, G.Adj u v ↔ hS (ψ u) (ψ v) := by
          use f.symm.toEquiv;
          exact fun u v => by simpa using f.symm.map_adj_iff.symm;
        obtain ⟨ ψ, hψ ⟩ := h_iso;
        have h_iso : ψ = φ := by
          apply hφ.right;
          intro u v huv; specialize hψ u v; aesop;
        congr! 1;
        · exact?;
        · ext u v; specialize hψ ( φ⁻¹ u ) ( φ⁻¹ v ) ; aesop;
    · rw [ Finset.card_eq_one ];
      obtain ⟨ φ, hφ ⟩ := Finset.card_eq_one.mp h;
      use 1; ext σ; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      constructor <;> intro hσ <;> simp_all +decide [ embeddingFinset, autFinset ];
      have := hφ.2 ( φ * σ ) ?_;
      · simpa using this;
      · intro u v huv; specialize hσ u v; aesop;
  · intro h
    obtain ⟨h_unique_subgraph, h_aut⟩ := h
    have h_embedding : ∀ φ₁ φ₂ : Equiv.Perm (Fin n), (IsEmbedding G H φ₁) → (IsEmbedding G H φ₂) → ∃ σ : Equiv.Perm (Fin n), σ ∈ autFinset G ∧ φ₂ = φ₁ * σ := by
      intros φ₁ φ₂ hφ₁ hφ₂
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ = φ₁⁻¹ * φ₂ ∧ ∀ u v : Fin n, G.Adj u v ↔ G.Adj (σ u) (σ v) := by
        obtain ⟨ S, hS₁, hS₂ ⟩ := h_unique_subgraph;
        have h_subgraph : ∀ φ : Equiv.Perm (Fin n), IsEmbedding G H φ → ∃ S' : H.Subgraph, S'.IsSpanning ∧ Nonempty (S'.spanningCoe.Iso G) ∧ ∀ u v : Fin n, G.Adj u v ↔ S'.Adj (φ u) (φ v) := by
          intro φ hφ
          use ⟨Set.univ, fun u v => G.Adj (φ⁻¹ u) (φ⁻¹ v), by
            exact fun { v w } hvw => by simpa using hφ ( φ⁻¹ v ) ( φ⁻¹ w ) hvw;, by
            exact fun _ => Set.mem_univ _, by
            exact fun u v h => G.symm h⟩
          generalize_proofs at *;
          refine' ⟨ _, _, _ ⟩;
          · exact?;
          · refine' ⟨ _, _ ⟩;
            exact φ⁻¹;
            aesop;
          · simp +decide [ Equiv.Perm.inv_eq_iff_eq ];
        obtain ⟨ S₁, hS₁₁, hS₁₂, hS₁₃ ⟩ := h_subgraph φ₁ hφ₁
        obtain ⟨ S₂, hS₂₁, hS₂₂, hS₂₃ ⟩ := h_subgraph φ₂ hφ₂
        have hS₁₂_eq : S₁ = S₂ := by
          rw [ hS₂ S₁ ⟨ hS₁₁, hS₁₂ ⟩, hS₂ S₂ ⟨ hS₂₁, hS₂₂ ⟩ ];
        simp_all +decide [ Equiv.Perm.inv_eq_iff_eq ];
      exact ⟨ σ, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ.2 ⟩, by simp +decide [ hσ.1, mul_assoc ] ⟩;
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Equiv.Perm (Fin n), IsEmbedding G H φ₁ := by
      obtain ⟨ S, hS₁, hS₂ ⟩ := h_unique_subgraph;
      obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Equiv.Perm (Fin n), ∀ u v, G.Adj u v ↔ S.Adj (φ₁ u) (φ₁ v) := by
        obtain ⟨ φ₁, hφ₁ ⟩ := hS₁.2;
        use φ₁.symm;
        intro u v; specialize @hφ₁ ( φ₁.symm u ) ( φ₁.symm v ) ; aesop;
      use φ₁;
      exact fun u v huv => S.adj_sub ( hφ₁ u v |>.1 huv );
    have h_unique_embedding : ∀ φ₂ : Equiv.Perm (Fin n), IsEmbedding G H φ₂ → φ₂ = φ₁ := by
      have := Finset.card_eq_one.mp h_aut;
      obtain ⟨ a, ha ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      have := ha.2 1 ( id_mem_autFinset G ) ; aesop;
    exact Finset.card_eq_one.mpr ⟨ φ₁, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hφ₁ ⟩, fun φ₂ hφ₂ => h_unique_embedding φ₂ <| Finset.mem_filter.mp hφ₂ |>.2 ⟩ ⟩

lemma orbit_card_mul_aut (n : ℕ) (G : SimpleGraph (Fin n)) :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) * (autFinset G).card =
    Nat.factorial n := by
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group ( Equiv.Perm ( Fin n ) ) G using 1;
  · rw [ Fintype.card_subtype ];
    rw [ Fintype.card_of_subtype ];
    intro x; erw [ mem_fixedBy_iff_mem_autFinset ] ;
  · simp +decide [ Fintype.card_perm ]

/-- For G with |aut|=1, the orbit has exactly n! elements. -/
lemma orbit_card_of_trivial_aut {n : ℕ} (G : SimpleGraph (Fin n))
    (h : (autFinset G).card = 1) :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) = Nat.factorial n := by
  have := orbit_card_mul_aut n G; rw [h] at this; omega

lemma aut_card_iso_invariant {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    (h : Nonempty (G₁.Iso G₂)) : (autFinset G₁).card = (autFinset G₂).card := by
  obtain ⟨ f ⟩ := h;
  refine' Finset.card_bij _ _ _ _;
  use fun a ha => f.toEquiv * a * f.symm.toEquiv;
  · unfold autFinset;
    simp +decide [ SimpleGraph.Iso.map_adj_iff ];
    intro a ha u v; rw [ ← ha ] ;
    exact Iff.symm (Iso.map_adj_iff f.symm);
  · simp +contextual [ funext_iff, Equiv.Perm.ext_iff ];
  · intro b hb;
    refine' ⟨ f.symm.toEquiv * b * f.toEquiv, _, _ ⟩ <;> simp_all +decide [ autFinset ];
    · exact fun u v => by simpa [ ← f.map_adj_iff ] using hb ( f u ) ( f v ) ;
    · ext x; simp +decide [ Equiv.Perm.mul_apply ] ;

/-
UniquelyEmbeds is invariant under the Perm action on graphs.
-/
lemma uniquelyEmbeds_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (G H : SimpleGraph (Fin n)) :
    UniquelyEmbeds (σ • G) H ↔ UniquelyEmbeds G H := by
  have h_embedding_equiv : ∀ τ : Equiv.Perm (Fin n), IsEmbedding (σ • G) H τ ↔ IsEmbedding G H (τ * σ) := by
    intro τ
    simp [IsEmbedding, smul_adj];
    grind;
  simp +decide only [UniquelyEmbeds, numEmbeddings, embeddingFinset];
  rw [ show ( filter ( IsEmbedding ( σ • G ) H ) univ ) = Finset.image ( fun τ => τ * σ⁻¹ ) ( filter ( IsEmbedding G H ) univ ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
  ext τ; aesop

/-
The number of iso classes with nontrivial aut times n! is bounded by the
    Burnside excess. This is used to bound the error term in fH_le_probUniqueEmb_plus_error.
    Key idea: each nontrivial-aut iso class contributes ≥ n!/2 to ∑(|aut|-1).
-/
lemma nontrivial_aut_classes_bound (n : ℕ) :
    (((Finset.univ : Finset (SimpleGraph (Fin n))).image
      (@Quotient.mk _ (graphIsoSetoid n))).filter (fun q =>
      ∀ G : SimpleGraph (Fin n), @Quotient.mk _ (graphIsoSetoid n) G = q →
        (autFinset G).card ≠ 1)).card * (Nat.factorial n) ≤
    2 * (numIsoClasses n * Nat.factorial n - 2 ^ n.choose 2) := by
  -- Let's denote the set of iso classes with nontrivial aut as `S`.
  set S := Finset.filter (fun q => ∀ G : SimpleGraph (Fin n), ⟦G⟧ = q → (autFinset G).card ≠ 1) (Finset.univ.image (Quotient.mk (graphIsoSetoid n)));
  -- Each element in S corresponds to an iso class with nontrivial aut.
  have hS_card : S.card * n.factorial ≤ ∑ q ∈ S, ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) * 2 := by
    have hS_card : ∀ q ∈ S, ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) * 2 ≥ n.factorial := by
      intro q hq
      obtain ⟨G₀, hG₀⟩ : ∃ G₀ : SimpleGraph (Fin n), ⟦G₀⟧ = q ∧ (autFinset G₀).card ≠ 1 := by
        grind;
      -- Since $G₀$ has nontrivial automorphisms, the orbit of $G₀$ under the action of $S_n$ has size $n! / |Aut(G₀)|$.
      have h_orbit_size : (Finset.univ.filter (fun G => ⟦G⟧ = q)).card = n.factorial / (autFinset G₀).card := by
        have h_orbit_size : (Finset.univ.filter (fun G => ⟦G⟧ = q)).card = Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G₀) := by
          rw [ Fintype.card_of_subtype ];
          simp +decide [ ← hG₀.1, MulAction.orbitRel_apply ];
          intro x; rw [ Quotient.eq ] ;
          constructor <;> intro h;
          · obtain ⟨ σ, hσ ⟩ := h;
            use σ⁻¹;
            ext a b; simp +decide [ hσ ] ;
          · obtain ⟨ σ, rfl ⟩ := h;
            refine' ⟨ _, _ ⟩;
            exact σ⁻¹;
            aesop;
        have := orbit_card_mul_aut n G₀;
        rw [ h_orbit_size, ← this, Nat.mul_div_cancel _ ( Finset.card_pos.mpr ⟨ 1, id_mem_autFinset G₀ ⟩ ) ];
      -- Since $G₀$ has nontrivial automorphisms, each element in the orbit of $G₀$ has the same automorphism group size as $G₀$.
      have h_orbit_aut_size : ∀ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), (autFinset G).card = (autFinset G₀).card := by
        intros G hG
        have h_iso : Nonempty (G.Iso G₀) := by
          simp +zetaDelta at *;
          exact Quotient.exact ( hG.trans hG₀.1.symm );
        exact aut_card_iso_invariant h_iso;
      rw [ Finset.sum_congr rfl fun x hx => by rw [ h_orbit_aut_size x hx ] ] ; simp_all +decide [ Nat.mul_div_cancel' ];
      have h_aut_size : (autFinset G₀).card ≥ 2 := by
        exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ 1, id_mem_autFinset G₀ ⟩ ) ( Ne.symm hG₀.2 );
      nlinarith [ Nat.div_mul_cancel ( show #(autFinset G₀) ∣ n.factorial from orbit_card_mul_aut n G₀ ▸ dvd_mul_left _ _ ), Nat.sub_add_cancel ( show 1 ≤ #(autFinset G₀) from by linarith ) ];
    simpa using Finset.sum_le_sum hS_card;
  -- The sum over all iso classes of (|aut(G)| - 1) is equal to the excess.
  have h_sum_excess : ∑ q : Quotient (graphIsoSetoid n), ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) = numIsoClasses n * n.factorial - 2 ^ n.choose 2 := by
    have h_sum_excess : ∑ q : Quotient (graphIsoSetoid n), ∑ G ∈ Finset.univ.filter (fun G => ⟦G⟧ = q), ((autFinset G).card - 1) = ∑ G : SimpleGraph (Fin n), ((autFinset G).card - 1) := by
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun G _ => G.2 ) _ _ _ _ <;> aesop;
    rw [ h_sum_excess, ← sum_autFinset_eq ];
    rw [ Nat.sub_eq_of_eq_add ];
    zify [ ← card_simpleGraph ];
    rw [ Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Finset.card_pos.mpr <| autFinset_nonempty _ ] ; norm_num;
  simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  rw [ ← h_sum_excess, mul_comm ];
  rw [ mul_comm ];
  exact hS_card.trans ( by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset <| Finset.filter_subset _ _ ) zero_le_two )

/-
Burnside gives: numIsoClasses * n! ≥ 2^(n choose 2).
-/
lemma numIsoClasses_factorial_ge (n : ℕ) :
    2 ^ n.choose 2 ≤ numIsoClasses n * Nat.factorial n := by
  rw [ ← card_simpleGraph, ← sum_autFinset_eq ];
  exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => Finset.card_pos.mpr ( autFinset_nonempty _ ) )

/-
The number of trivial-aut unique-subgraph iso classes times n! equals
    numUniquelyEmbedding.
-/
lemma numUniquelyEmbedding_eq_factorial_mul {n : ℕ} (H : SimpleGraph (Fin n)) :
    (numUniquelyEmbedding H : ℝ) =
    (Nat.factorial n : ℝ) *
    (((uniqueSubgraphClasses H).filter (fun q =>
      ∃ G : SimpleGraph (Fin n), (autFinset G).card = 1 ∧
      @Quotient.mk _ (graphIsoSetoid n) G = q)).card : ℝ) := by
  -- The set S = {G : UniquelyEmbeds G H} is a union of complete orbits under the Perm action (each orbit has all its elements in S, by uniquelyEmbeds_smul).
  let S := Finset.univ.filter (fun G : SimpleGraph (Fin n) => UniquelyEmbeds G H)
  have h_orbits : Finset.card S = (Finset.image (Quotient.mk (graphIsoSetoid n)) S).card * Nat.factorial n := by
    have h_orbits : ∀ q ∈ S.image (Quotient.mk (graphIsoSetoid n)), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ⟦G⟧ = q ∧ G ∈ S)).card = Nat.factorial n := by
      intros q hq
      obtain ⟨G, hG⟩ : ∃ G ∈ S, ⟦G⟧ = q := by
        grind;
      have h_orbit : (Finset.univ.filter (fun G' : SimpleGraph (Fin n) => G' ∈ MulAction.orbit (Equiv.Perm (Fin n)) G)).card = Nat.factorial n := by
        convert orbit_card_of_trivial_aut G _;
        · rw [ Fintype.card_of_subtype ] ; aesop;
        · exact uniquelyEmbeds_iff_uniqueSub_trivialAut G H |>.1 ( Finset.mem_filter.mp hG.1 |>.2 ) |>.2;
      convert h_orbit using 2;
      ext G'; simp [hG];
      rw [ ← hG.2, Quotient.eq ];
      constructor;
      · -- If G' is in the set S and is equivalent to G under the graphIsoSetoid n, then there exists a permutation σ such that G' = σ • G.
        intro h
        obtain ⟨σ, hσ⟩ := h.left;
        use σ⁻¹;
        ext a b; simp +decide [ hσ ] ;
      · rintro ⟨ σ, rfl ⟩;
        simp +zetaDelta at *;
        exact ⟨ ⟨ σ.symm, by aesop ⟩, by simpa using uniquelyEmbeds_smul σ G H |>.2 hG.1 ⟩
    have h_orbits : Finset.card S = Finset.sum (Finset.image (Quotient.mk (graphIsoSetoid n)) S) (fun q => (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ⟦G⟧ = q ∧ G ∈ S)).card) := by
      rw [ ← Finset.card_biUnion ];
      · congr with G ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    rw [ h_orbits, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
  convert congr_arg ( ( ↑ ) : ℕ → ℝ ) h_orbits using 1 ; norm_num [ mul_comm ];
  refine Or.inl <| congr_arg Finset.card <| Finset.ext fun x => ?_;
  constructor;
  · simp +zetaDelta at *;
    rintro hx G hG rfl;
    obtain ⟨ G', hG', hG'' ⟩ := Finset.mem_image.mp hx;
    use G';
    rw [ Quotient.eq ] at hG'';
    exact ⟨ uniquelyEmbeds_iff_uniqueSub_trivialAut _ _ |>.2 ⟨ Finset.mem_filter.mp hG' |>.2, by simpa [ hG ] using aut_card_iso_invariant hG'' ⟩, Quotient.sound hG'' ⟩;
  · simp +zetaDelta at *;
    rintro G hG rfl; exact ⟨ Finset.mem_image.mpr ⟨ G, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simpa using uniquelyEmbeds_iff_uniqueSub_trivialAut G H |>.1 hG |>.1 ⟩, rfl ⟩, G, by simpa using uniquelyEmbeds_iff_uniqueSub_trivialAut G H |>.1 hG |>.2, rfl ⟩ ;

/-
fH ≤ probUniqueEmb + 2*(numIsoClasses * n! / 2^N - 1).
    Uses orbit-stabilizer. The second term tends to 0 by Pólya-Wright.
-/
lemma fH_le_probUniqueEmb_plus_error {n : ℕ} (H : SimpleGraph (Fin n)) :
    fH H ≤ probUniqueEmb H +
    2 * ((numIsoClasses n : ℝ) * (Nat.factorial n : ℝ) / (2 ^ n.choose 2 : ℝ) - 1) := by
  field_simp;
  unfold fH probUniqueEmb paperDenom;
  field_simp;
  have h_card_filter : ((uniqueSubgraphClasses H).card : ℝ) ≤
    (numUniquelyEmbedding H : ℝ) / (Nat.factorial n : ℝ) +
    (((Finset.univ : Finset (SimpleGraph (Fin n))).image
      (@Quotient.mk _ (graphIsoSetoid n))).filter (fun q =>
        ∀ G : SimpleGraph (Fin n), @Quotient.mk _ (graphIsoSetoid n) G = q →
          (autFinset G).card ≠ 1)).card := by
            rw [ numUniquelyEmbedding_eq_factorial_mul ];
            rw [ mul_div_cancel_left₀ _ ( by positivity ) ];
            rw_mod_cast [ ← Finset.card_union_add_card_inter ];
            refine' le_add_right ( Finset.card_le_card _ );
            intro q hq;
            by_cases h : ∃ G : SimpleGraph (Fin n), (autFinset G).card = 1 ∧ ⟦G⟧ = q;
            · grind +extAll;
            · simp +zetaDelta at *;
              exact Or.inr ⟨ by rcases Quotient.exists_rep q with ⟨ G, rfl ⟩ ; exact ⟨ G, rfl ⟩, fun G hG hG' => h G hG' hG ⟩
  rw [ div_add', le_div_iff₀ ] at h_card_filter <;> norm_cast at *;
  · rw [ Int.subNatNat_of_le ] <;> norm_cast;
    · have := nontrivial_aut_classes_bound n;
      lia;
    · linarith [ numIsoClasses_factorial_ge n ];
  · positivity;
  · positivity

lemma count_graphs_with_embedding {n : ℕ} (H : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      IsEmbedding G H σ)).card = 2 ^ H.edgeFinset.card := by
  -- The number of subgraphs of a graph G is 2^(e(G)), where e(G) is the number of edges in G.
  have h_subgraph_count (G : SimpleGraph (Fin n)) : (Finset.univ.filter (fun H : SimpleGraph (Fin n) => H ≤ G)).card = 2 ^ G.edgeFinset.card := by
    -- Each subgraph of $G$ corresponds to a subset of the edge set of $G$.
    have h_subgraph_subset : Finset.univ.filter (fun H : SimpleGraph (Fin n) => H ≤ G) = Finset.image (fun s : Finset (Sym2 (Fin n)) => SimpleGraph.fromEdgeSet (s.filter (fun e => e ∈ G.edgeFinset))) (Finset.powerset G.edgeFinset) := by
      ext H;
      simp +zetaDelta at *;
      constructor;
      · intro hH;
        use H.edgeFinset;
        aesop;
      · rintro ⟨ a, ha, rfl ⟩ ; intro u v; simp +decide [ SimpleGraph.fromEdgeSet ] ; aesop;
    rw [ h_subgraph_subset, Finset.card_image_of_injOn, Finset.card_powerset ];
    intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    intro x; replace h_eq := congr_arg ( fun f => f.edgeSet ) h_eq; simp_all +decide [ Set.subset_def ] ;
    replace h_eq := Set.ext_iff.mp h_eq x; by_cases hx : x ∈ G.edgeSet <;> simp_all +decide [ Sym2.diagSet ] ;
    · cases x ; aesop;
    · exact ⟨ fun hx' => False.elim <| hx <| hs x hx', fun hx' => False.elim <| hx <| ht x hx' ⟩;
  convert h_subgraph_count ( SimpleGraph.comap σ H ) using 1;
  refine' congr_arg _ ( Finset.card_bij ( fun e he => Sym2.map σ.symm e ) _ _ _ ) <;> simp +decide [ SimpleGraph.comap ];
  · rintro ⟨ u, v ⟩ huv; simp_all +decide [ SimpleGraph.adj_comm ] ;
  · intro a₁ ha₁ a₂ ha₂ h; rcases a₁ with ⟨ u₁, v₁ ⟩ ; rcases a₂ with ⟨ u₂, v₂ ⟩ ; aesop;
  · rintro ⟨ u, v ⟩ huv; use Sym2.mk ( σ u, σ v ) ; aesop;

/-
First moment bound: the number of uniquely-embedding graphs is at most
    n! * 2^{e(H)}. This follows from the union bound over all permutations.
-/
lemma first_moment_embedding_bound {n : ℕ} (H : SimpleGraph (Fin n)) :
    numUniquelyEmbedding H ≤ Nat.factorial n * 2 ^ H.edgeFinset.card := by
  have h_first_moment : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0)).card ≤ (Nat.factorial n) * 2 ^ H.edgeFinset.card := by
    have h_first_moment : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0)).card ≤ ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding G H σ)).card := by
      have h_union_bound : Finset.univ.filter (fun G : SimpleGraph (Fin n) => numEmbeddings G H > 0) ⊆ Finset.biUnion Finset.univ (fun σ : Equiv.Perm (Fin n) => Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding G H σ)) := by
        intro G hG; contrapose! hG; simp_all +decide [ numEmbeddings ] ;
        exact Finset.eq_empty_of_forall_notMem fun σ hσ => hG σ <| Finset.mem_filter.mp hσ |>.2;
      exact le_trans ( Finset.card_le_card h_union_bound ) ( Finset.card_biUnion_le );
    exact h_first_moment.trans ( by rw [ Finset.sum_congr rfl fun σ _ => count_graphs_with_embedding H σ ] ; simp +decide [ Finset.card_univ, Fintype.card_perm ] );
  refine le_trans ?_ h_first_moment;
  exact Finset.card_mono (fun G hG => by unfold UniquelyEmbeds at hG; aesop);

/-
From first_moment_embedding_bound: probUniqueEmb H ≤ n! / 2^{C(n,2) - e(H)}.
-/
lemma probUniqueEmb_le_factorial_div {n : ℕ} (H : SimpleGraph (Fin n)) :
    probUniqueEmb H ≤ (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - H.edgeFinset.card) := by
  -- Using the first moment embedding bound, we have:
  have h_bound : numUniquelyEmbedding H ≤ Nat.factorial n * 2 ^ H.edgeFinset.card :=
    first_moment_embedding_bound H
  simp [probUniqueEmb] at *;
  rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num;
  convert Nat.mul_le_mul_right _ h_bound using 1;
  rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ];
  convert H.card_edgeFinset_le_card_choose_two;
  norm_num

/-! ### Universal Vertices and Twin Argument -/

lemma small_n_vacuity (C n : ℕ) (hn : n ≤ 2 * C + 1) :
    n.choose 2 ≤ C * n := by
  rw [Nat.choose_two_right]
  have h2 : n * (n - 1) ≤ 2 * (C * n) := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one]
      have : n ≤ 2 * C := by omega
      nlinarith
  exact Nat.div_le_of_le_mul h2

/-- First moment bound: probUniqueEmb H ≤ n! · 2^{e(H)} / 2^N ≤ n!/2^m
    where m = N - e(H) is the number of non-edges. Combined with the
    edge-count concentration from the Chernoff bound, this implies
    that graphs with too many non-edges have small probUniqueEmb. -/

/-
For G₀ with UniquelyEmbeds G₀ H, any supergraph G' ≥ G₀ that embeds into H
    must use the same unique embedding σ.
-/
lemma UE_supergraph_same_embedding {n : ℕ} {G₀ G' H : SimpleGraph (Fin n)}
    (hle : G₀ ≤ G') (hUE₀ : UniquelyEmbeds G₀ H)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ embeddingFinset G' H) :
    embeddingFinset G₀ H = {σ} := by
  -- Since σ is in embeddingFinset G' H and G₀ ≤ G', σ is also in embeddingFinset G₀ H.
  have hσ_G₀ : σ ∈ embeddingFinset G₀ H := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => Finset.mem_filter.mp hσ |>.2 u v ( hle huv ) ⟩;
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨ hσ_G₀, fun τ hτ => by have := Finset.card_eq_one.mp hUE₀; aesop ⟩

/-
Supergraph UE characterization: if G₀ UE via σ, then G' ≥ G₀ UE iff
    G' ≤ σ • H (every edge of G' maps to an edge of H under σ).
-/
lemma UE_supergraph_iff {n : ℕ} {G₀ G' H : SimpleGraph (Fin n)}
    (hle : G₀ ≤ G') (hUE₀ : UniquelyEmbeds G₀ H)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ embeddingFinset G₀ H) :
    UniquelyEmbeds G' H ↔ IsEmbedding G' H σ := by
  constructor;
  · intro h;
    -- By definition of UniquelyEmbeds, G' has exactly one embedding into H.
    obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), embeddingFinset G' H = {τ} := by
      exact Finset.card_eq_one.mp h;
    -- Since τ is the unique embedding of G' into H, and σ is an embedding of G₀ into H, we must have τ = σ.
    have hτ_eq_σ : τ = σ := by
      have hτ_eq_σ : τ ∈ embeddingFinset G₀ H := by
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hτ.1; exact this.2 u v ( hle huv ) ⟩;
      have := Finset.card_eq_one.mp hUE₀;
      aesop;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact Finset.mem_filter.mp hτ.1 |>.2;
  · intro hσ';
    -- By definition of UniquelyEmbeds, we know that embeddingFinset G₀ H = {σ}.
    have h_embeddingFinset_G₀ : embeddingFinset G₀ H = {σ} := by
      apply_rules [ UE_supergraph_same_embedding ];
      exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ' ⟩;
    -- Since σ is in embeddingFinset G' H and G₀ ≤ G', we have that embeddingFinset G' H is a subset of embeddingFinset G₀ H.
    have h_embeddingFinset_G'_subset_G₀ : embeddingFinset G' H ⊆ embeddingFinset G₀ H := by
      intro τ hτ;
      exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => Finset.mem_filter.mp hτ |>.2 u v ( hle huv ) ⟩;
    rw [ h_embeddingFinset_G₀ ] at h_embeddingFinset_G'_subset_G₀;
    exact Finset.card_eq_one.mpr ⟨ σ, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hσ' ⟩, fun x hx => Finset.mem_singleton.mp ( h_embeddingFinset_G'_subset_G₀ hx ) ⟩ ⟩

/-
The number of (m+k)-edge supergraphs of G₀ that embed via σ
    equals C(e(H) - m, k), where m = e(G₀).
-/
set_option maxHeartbeats 800000 in
lemma supergraph_UE_count {n : ℕ} (G₀ H : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hUE : UniquelyEmbeds G₀ H) (hσ : σ ∈ embeddingFinset G₀ H)
    (hk : k ≤ H.edgeFinset.card - G₀.edgeFinset.card) :
    (Finset.univ.filter (fun G' : SimpleGraph (Fin n) =>
      G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k ∧
      UniquelyEmbeds G' H)).card =
    (H.edgeFinset.card - G₀.edgeFinset.card).choose k := by
  have h_bij : {G' : SimpleGraph (Fin n) | G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k ∧ UniquelyEmbeds G' H} = {G' : SimpleGraph (Fin n) | G₀ ≤ G' ∧ G' ≤ σ⁻¹ • H ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k} := by
    apply Set.ext
    intro G'
    simp [hUE, hσ];
    intro hG';
    constructor <;> intro h;
    · have := UE_supergraph_iff hG' hUE σ (by
      exact hσ)
      generalize_proofs at *;
      exact ⟨ fun u v huv => by simpa using this.mp h.2 u v huv, h.1 ⟩;
    · have h_unique_embedding : IsEmbedding G' H σ := by
        intro u v huv; have := h.1 huv; aesop;
      have h_unique_embedding : UniquelyEmbeds G' H ↔ IsEmbedding G' H σ := by
        apply_rules [ UE_supergraph_iff ];
      aesop;
  -- The set of valid G' corresponds to choosing k edges from a set of e(H) - m₀ available edges, which has C(e(H) - m₀, k) elements.
  have h_card : Finset.card (Finset.filter (fun G' : SimpleGraph (Fin n) => G₀ ≤ G' ∧ G' ≤ σ⁻¹ • H ∧ G'.edgeFinset.card = G₀.edgeFinset.card + k) Finset.univ) = Finset.card (Finset.powersetCard k (Finset.filter (fun e => e ∈ (σ⁻¹ • H).edgeFinset ∧ e ∉ G₀.edgeFinset) (Finset.univ : Finset (Sym2 (Fin n)))) ) := by
    refine' Finset.card_bij ( fun G' _ => G'.edgeFinset \ G₀.edgeFinset ) _ _ _;
    · simp +contextual [ Finset.mem_powersetCard, Finset.card_sdiff ];
      intro G' hG'₁ hG'₂ hG'₃; rw [ Finset.inter_comm ] ; simp_all +decide [ Finset.subset_iff ] ;
      refine' ⟨ fun x hx₁ hx₂ => _, _ ⟩;
      · cases x ; aesop;
      · rw [ Finset.inter_eq_right.mpr ] <;> aesop;
    · simp +contextual [ Finset.ext_iff ];
      intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ h; ext u v; specialize h ( Sym2.mk ( u, v ) ) ; by_cases hu : G₀.Adj u v <;> aesop;
    · intro b hb; use SimpleGraph.fromEdgeSet ( G₀.edgeFinset ∪ b ) ; simp_all +decide [ Finset.subset_iff ] ;
      refine' ⟨ ⟨ ⟨ _, _ ⟩, _ ⟩, _ ⟩;
      · intro u v; simp_all +decide [ embeddingFinset ] ;
        exact hσ u v;
      · grind;
      · rw [ Finset.card_union_of_disjoint ] <;> simp_all +decide [ Finset.disjoint_left ];
        · convert hb.2 using 1;
          refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ SimpleGraph.edgeSet ];
          · grind;
          · intro x hx; specialize hb; have := hb.1 hx; simp_all +decide [ SimpleGraph.edgeSet ] ;
            exact fun h => by have := hb.1 hx; exact this.1 |> fun h' => by cases x; aesop;
        · intro x hx₁ hx₂; specialize hb; have := hb.1 hx₂; aesop;
      · ext; simp [hb];
        by_cases h : ‹Sym2 ( Fin n ) › ∈ G₀.edgeSet <;> simp_all +decide [ SimpleGraph.edgeSet ];
        · exact fun h' => hb.1 h' |>.2 h;
        · intro hx; specialize hb; have := hb.1 hx; simp_all +decide [ edgeSetEmbedding ] ;
          cases ‹Sym2 ( Fin n ) › ; simp_all +decide [ Sym2.fromRel ];
          intro h; have := hb.1 hx; simp_all +decide [ Sym2.lift ] ;
  convert h_card using 1;
  · congr! 1;
    convert h_bij using 1;
    simp +decide [ Finset.ext_iff, Set.ext_iff ];
  · rw [ Finset.card_powersetCard, show Finset.filter ( fun e => e ∈ ( σ⁻¹ • H ).edgeFinset ∧ e∉G₀.edgeFinset ) Finset.univ = ( σ⁻¹ • H ).edgeFinset \ G₀.edgeFinset by ext; aesop ];
    -- Since σ is a permutation, the number of edges in σ⁻¹ • H is the same as in H.
    have h_edge_card : (σ⁻¹ • H).edgeFinset.card = H.edgeFinset.card := by
      refine' Finset.card_bij ( fun e he => Sym2.map σ e ) _ _ _ <;> simp +decide [ Sym2.map ];
      · intro e he; rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact he;
      · intro a₁ ha₁ a₂ ha₂ h; rcases a₁ with ⟨ u₁, v₁ ⟩ ; rcases a₂ with ⟨ u₂, v₂ ⟩ ; simp_all +decide [ Quot.map ] ;
      · rintro ⟨ u, v ⟩ huv;
        refine' ⟨ Quot.mk _ ( σ⁻¹ u, σ⁻¹ v ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.edgeSetEmbedding ];
        exact Quot.sound ( by aesop );
    rw [ Finset.card_sdiff ];
    rw [ h_edge_card, Finset.inter_eq_left.mpr ];
    intro e he; simp_all +decide [ SimpleGraph.edgeFinset ] ;
    rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.edgeSetEmbedding ] ;
    exact Finset.mem_filter.mp hσ |>.2 u v he

/-
Anti-concentration: for N = C(n,2) with n ≥ 4, C(N,m)/2^N ≤ 4/n.
-/
lemma binomial_anticoncentration {n : ℕ} (hn : 4 ≤ n) (m : ℕ) :
    ((n.choose 2).choose m : ℝ) / 2 ^ (n.choose 2) ≤ 4 / n := by
  field_simp;
  -- By the properties of binomial coefficients, we know that $\binom{N}{m} \leq \binom{N}{\lfloor N/2 \rfloor}$.
  have h_binom_le : (Nat.choose (Nat.choose n 2) m : ℝ) ≤ (Nat.choose (Nat.choose n 2) (Nat.choose n 2 / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle _ _;
  -- By the properties of binomial coefficients, we know that $\binom{N}{\lfloor N/2 \rfloor} \leq 2^N / \sqrt{N/2 + 1}$.
  have h_binom_bound : (Nat.choose (Nat.choose n 2) (Nat.choose n 2 / 2) : ℝ) ≤ 2 ^ (Nat.choose n 2) / Real.sqrt ((Nat.choose n 2) / 2 + 1) := by
    -- By the properties of binomial coefficients, we know that $\binom{2k}{k} \leq \frac{4^k}{\sqrt{k+1}}$ for any $k$.
    have h_binom_bound : ∀ k : ℕ, (Nat.choose (2 * k) k : ℝ) ≤ 4 ^ k / Real.sqrt (k + 1) := by
      intro k
      induction' k with k ih;
      · norm_num;
      · -- For the inductive step, we use the identity $\binom{2(k+1)}{k+1} = \frac{2(2k+1)}{k+1} \binom{2k}{k}$.
        have h_identity : (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) = (2 * (2 * k + 1) / (k + 1)) * (Nat.choose (2 * k) k : ℝ) := by
          rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
          norm_num [ two_mul, Nat.factorial ];
          rw [ div_mul_div_comm, div_eq_div_iff ] <;> first | positivity | ring;
          rw [ show 1 + k * 2 = k * 2 + 1 by ring, Nat.factorial_succ ] ; push_cast ; ring;
        rw [ h_identity, pow_succ' ];
        refine le_trans ( mul_le_mul_of_nonneg_left ih <| by positivity ) ?_;
        field_simp;
        norm_num ; nlinarith [ sq_nonneg ( Real.sqrt ( k + 1 ) - Real.sqrt ( k + 1 + 1 ) ), Real.mul_self_sqrt ( show ( k:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( k:ℝ ) + 1 + 1 ≥ 0 by positivity ), Real.sqrt_nonneg ( k + 1 ), Real.sqrt_nonneg ( k + 1 + 1 ) ];
    rcases Nat.even_or_odd' ( Nat.choose n 2 ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk ];
    · convert h_binom_bound k using 2 ; norm_num [ pow_mul ];
    · have := h_binom_bound ( k + 1 ) ; norm_num [ Nat.add_div, Nat.mul_succ, pow_succ', pow_mul ] at *;
      rw [ show ( 2 * k + 2 : ℕ ) = 2 * k + 1 + 1 by ring, Nat.choose_succ_succ ] at this;
      rw [ le_div_iff₀ ( by positivity ) ] at *;
      rw [ show ( 2 * k + 1 : ℕ ).choose k.succ = ( 2 * k + 1 : ℕ ).choose k from by rw [ Nat.choose_symm_of_eq_add ] ; linarith ] at this ; ring_nf at * ; norm_num at *;
      nlinarith [ Real.sqrt_nonneg ( 2 + k : ℝ ), Real.sqrt_nonneg ( 3 / 2 + k : ℝ ), Real.mul_self_sqrt ( show ( 0 : ℝ ) ≤ 2 + k by positivity ), Real.mul_self_sqrt ( show ( 0 : ℝ ) ≤ 3 / 2 + k by positivity ), Real.sqrt_le_sqrt ( show ( 2 + k : ℝ ) ≥ 3 / 2 + k by linarith ) ];
  -- We'll use that $n \leq 4 \sqrt{\frac{n(n-1)}{4} + 1}$ for $n \geq 4$.
  have h_sqrt_bound : (n : ℝ) ≤ 4 * Real.sqrt ((Nat.choose n 2) / 2 + 1) := by
    rw [ Nat.choose_two_right ];
    rcases n with ( _ | _ | _ | _ | n ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
    nlinarith only [ Real.sqrt_nonneg ( ( n + 1 + 1 + 1 + 1 : ℝ ) * ( n + 1 + 1 + 1 ) / 2 / 2 + 1 ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( n + 1 + 1 + 1 + 1 : ℝ ) * ( n + 1 + 1 + 1 ) / 2 / 2 + 1 ) ];
  rw [ le_div_iff₀ ] at h_binom_bound <;> first | positivity | nlinarith [ Real.sqrt_nonneg ( ( n.choose 2 : ℝ ) / 2 + 1 ), Real.mul_self_sqrt ( show 0 ≤ ( n.choose 2 : ℝ ) / 2 + 1 by positivity ) ] ;

/-
Chernoff tail bound for edge counts: given ε > 0, there exists L such that
    for all n, the number of graphs on n vertices with edge count deviating
    from N/2 by at least L*n is at most ε * 2^N.
-/
lemma chernoff_edge_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, 4 ≤ n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤
    ε * 2 ^ (n.choose 2) := by
  -- Apply the Chernoff bound with $t = L * n$.
  have h_chernoff : ∀ L : ℝ, 0 < L → ∀ n : ℕ, 4 ≤ n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => |((G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2)| ≥ (L : ℝ) * n)).card : ℝ) ≤
    2 * (2 ^ n.choose 2 : ℝ) * Real.exp (-2 * (L * (n : ℝ)) ^ 2 / n.choose 2) := by
      intros L hL n hn
      have h_chernoff : ((Finset.univ.filter (fun f : Fin (n.choose 2) → Bool => |((Finset.univ.filter (fun i => f i = true)).card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤ 2 * (2 ^ n.choose 2 : ℝ) * Real.exp (-2 * (L * (n : ℝ)) ^ 2 / n.choose 2) := by
        convert chernoff_bound ( n.choose 2 ) ( L * n ) ( by positivity ) using 1;
      have h_bij : ∃ f : SimpleGraph (Fin n) ≃ (Fin (n.choose 2) → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
        -- Define the bijection between SimpleGraph (Fin n) and (Fin (n.choose 2) → Bool) using the edgeSlot structure.
        have h_bij : ∃ f : SimpleGraph (Fin n) ≃ (Fin (n.choose 2) → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
          have h_edgeSlot : ∃ f : SimpleGraph (Fin n) ≃ (EdgeSlot n → Bool), ∀ G : SimpleGraph (Fin n), (Finset.univ.filter (fun i => f G i = true)).card = G.edgeFinset.card := by
            use UniqueSubgraphs.graphEquiv n;
            intro G; exact (by
            refine' Finset.card_bij _ _ _ _;
            use fun a ha => Sym2.mk ( a.val.1, a.val.2 );
            · simp +decide [ graphEquiv ];
              unfold graphEncode; aesop;
            · simp +decide [ Sym2.eq_iff ];
              rintro ⟨ ⟨ i, j ⟩, hij ⟩ hi ⟨ ⟨ k, l ⟩, hkl ⟩ hj ( h | h ) <;> simp_all +decide [ Fin.ext_iff, Prod.ext_iff ];
              · exact Subtype.ext <| Prod.ext ( Fin.ext h.1 ) ( Fin.ext h.2 );
              · grind;
            · intro b hb; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
              cases lt_trichotomy u v <;> simp_all +decide [ graphEquiv ];
              · exact ⟨ ⟨ ⟨ u, v ⟩, by assumption ⟩, by unfold graphEncode; aesop ⟩;
              · cases ‹_› <;> simp_all +decide [ graphEncode ];
                exact ⟨ ⟨ ( v, u ), by assumption ⟩, by simpa [ SimpleGraph.adj_comm ] using hb, Or.inr rfl ⟩)
          obtain ⟨ f, hf ⟩ := h_edgeSlot;
          have h_bij : ∃ g : EdgeSlot n ≃ Fin (n.choose 2), True := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ card_edgeSlot ], trivial ⟩;
          obtain ⟨ g, hg ⟩ := h_bij;
          use f.trans (Equiv.arrowCongr g (Equiv.refl Bool));
          intro G; specialize hf G; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
          rw [ ← hf, Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp g.symm ] ;
        exact h_bij;
      obtain ⟨ f, hf ⟩ := h_bij;
      convert h_chernoff using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ ← Equiv.sum_comp f ] ; aesop;
  -- Choose $L$ such that $2 * \exp(-4L^2) \leq \epsilon$.
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 0 < L ∧ 2 * Real.exp (-4 * (L : ℝ) ^ 2) ≤ ε := by
    have h_exp_bound : Filter.Tendsto (fun L : ℕ => 2 * Real.exp (-4 * (L : ℝ) ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.const_mul_atTop ( by norm_num ) <| Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_exp_bound.eventually ( ge_mem_nhds hε ) ) |> fun ⟨ L, hL ⟩ => ⟨ L + 1, Nat.succ_pos _, hL _ ( Nat.le_succ _ ) ⟩;
  refine' ⟨ L, hL.1, fun n hn => le_trans ( h_chernoff L ( Nat.cast_pos.mpr hL.1 ) n hn ) _ ⟩;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_right hL.2 <| by positivity );
  rw [ show ( n.choose 2 : ℝ ) = n * ( n - 1 ) / 2 by rw [ Nat.choose_two_right ] ; induction n <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] at * ] ; ring_nf ; norm_num;
  field_simp;
  rw [ le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 4 by norm_cast, show ( L : ℝ ) ^ 2 ≥ 0 by positivity ]

/-! ### Process bound infrastructure -/

/-- Number of graphs with exactly m edges that uniquely embed into H. -/
def numUEWithEdges {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
    G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).card

/-
Chain interval property: if G₁ ≤ G₂ ≤ G₃ and G₁, G₃ both UE into H,
    then G₂ also UE into H.
-/
lemma ue_chain_interval {n : ℕ} {G₁ G₂ G₃ H : SimpleGraph (Fin n)}
    (h12 : G₁ ≤ G₂) (h23 : G₂ ≤ G₃)
    (hUE1 : UniquelyEmbeds G₁ H) (hUE3 : UniquelyEmbeds G₃ H) :
    UniquelyEmbeds G₂ H := by
  obtain ⟨ σ₁, hσ₁ ⟩ := Finset.card_eq_one.mp hUE1;
  have hσ₂ : σ₁ ∈ embeddingFinset G₂ H := by
    obtain ⟨ σ₃, hσ₃ ⟩ := Finset.card_eq_one.mp hUE3;
    have hσ₂ : σ₁ = σ₃ := by
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      exact hσ₁.2 σ₃ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => hσ₃.1 |> Finset.mem_filter.mp |>.2 u v ( h12 huv |> h23 ) ⟩ ) ▸ rfl;
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hσ₃.1; exact this.2 u v ( h23 huv ) ⟩;
  have hσ₃ : numEmbeddings G₂ H ≤ numEmbeddings G₁ H := by
    exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun u v huv => by have := Finset.mem_filter.mp hx; exact this.2 u v ( h12 huv ) ⟩;
  exact le_antisymm ( le_trans hσ₃ hUE1.le ) ( Finset.card_pos.mpr ⟨ σ₁, hσ₂ ⟩ )

/-
The empty graph does not uniquely embed for n ≥ 2 (it has n! ≥ 2 embeddings).
-/
lemma numUEWithEdges_zero {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    numUEWithEdges H 0 = 0 := by
  rw [ numUEWithEdges ];
  simp [UniquelyEmbeds, numEmbeddings, embeddingFinset];
  rw [ Finset.card_eq_sum_ones, Finset.sum_filter ];
  rw [ Finset.sum_congr rfl fun x hx => if_pos <| by unfold IsEmbedding; aesop ] ; norm_num [ Finset.card_univ, Fintype.card_perm ] ; linarith [ Nat.self_le_factorial n ]

/-
Abstract algebraic process bound.
    Given f : ℕ → ℝ with f(0) = 0, f ≥ 0, satisfying
    f(m) ≤ p · f(m-1) + z(m) for z ≥ 0 with Σ z ≤ 1,
    we get Σ_{m∈S} f(m) ≤ k + |S| · p^{k-1}.
-/
lemma abstract_process_bound (N : ℕ) (f z : ℕ → ℝ) (p : ℝ) (k : ℕ) (S : Finset ℕ)
    (hf0 : f 0 = 0) (hf_nonneg : ∀ m, 0 ≤ f m) (hz_nonneg : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, 1 ≤ m → m ≤ N → f m ≤ p * f (m - 1) + z m)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hk : 1 ≤ k)
    (hS : ∀ m ∈ S, m ≤ N)
    (hz_sum : ∑ m ∈ Finset.range (N + 1), z m ≤ 1)
    (hf_large : ∀ m, N < m → f m = 0) :
    ∑ m ∈ S, f m ≤ ↑k + ↑S.card * p ^ (k - 1) := by
  -- For each $j$, $\sum_{m \in S, m \geq j} p^{m-j} \leq \# \{m \in S : m-j < k-1\} \cdot 1 + \# \{m \in S : m-j \geq k-1\} \cdot p^{k-1}$.
  have h_sum_bound : ∀ j ∈ Finset.range (N + 1), ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) ≤ (min k (Finset.card (S.filter (fun m => j ≤ m)))) + (Finset.card (S.filter (fun m => j ≤ m))) * p ^ (k - 1) := by
    intros j hj
    have h_split : ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) ≤ ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j < k), p ^ (m - j) + ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j ≥ k), p ^ (m - j) := by
      rw [ ← Finset.sum_union ];
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by by_cases h : x - j < k <;> aesop ) fun _ _ _ => pow_nonneg hp _;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    have h_bound : ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j < k), p ^ (m - j) ≤ (min k (Finset.card (S.filter (fun m => j ≤ m)))) ∧ ∑ m ∈ S.filter (fun m => j ≤ m ∧ m - j ≥ k), p ^ (m - j) ≤ (Finset.card (S.filter (fun m => j ≤ m ∧ m - j ≥ k))) * p ^ (k - 1) := by
      constructor;
      · refine' le_trans ( Finset.sum_le_sum fun x hx => pow_le_one₀ hp hp1 ) _ ; norm_num;
        exact ⟨ le_trans ( Finset.card_le_card ( show { m ∈ S | j ≤ m ∧ m - j < k } ⊆ Finset.Ico j ( j + k ) from fun x hx => Finset.mem_Ico.mpr ⟨ by aesop, by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel ( show j ≤ x from by aesop ) ] ⟩ ) ) ( by simp +arith +decide ), Finset.card_mono ( fun x hx => by aesop ) ⟩;
      · exact le_trans ( Finset.sum_le_sum fun x hx => show p ^ ( x - j ) ≤ p ^ ( k - 1 ) by exact pow_le_pow_of_le_one hp hp1 ( by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel ( show 1 ≤ k from hk ) ] ) ) ( by norm_num );
    exact h_split.trans ( add_le_add h_bound.1 ( h_bound.2.trans ( mul_le_mul_of_nonneg_right ( mod_cast Finset.card_mono <| fun x hx => by aesop ) <| pow_nonneg hp _ ) ) );
  -- By interchanging the order of summation, we can rewrite the left-hand side of the inequality.
  have h_interchange : ∑ m ∈ S, f m ≤ ∑ j ∈ Finset.range (N + 1), z j * ∑ m ∈ S.filter (fun m => j ≤ m), p ^ (m - j) := by
    have h_interchange : ∀ m ∈ S, f m ≤ ∑ j ∈ Finset.range (m + 1), z j * p ^ (m - j) := by
      intro m hm
      have h_induction : ∀ m ≤ N, f m ≤ ∑ j ∈ Finset.range (m + 1), z j * p ^ (m - j) := by
        intro m hm; induction' m with m ih <;> simp_all +decide [ Finset.sum_range_succ ] ;
        refine le_trans ( hrec _ ( Nat.succ_pos _ ) ( by linarith ) ) ?_;
        norm_num [ Nat.succ_eq_add_one, pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] at *;
        exact le_trans ( mul_le_mul_of_nonneg_left ( ih hm.le ) hp ) ( by rw [ show ∑ j ∈ Finset.range m, z j * p ^ ( m + 1 - j ) = p * ∑ j ∈ Finset.range m, z j * p ^ ( m - j ) by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.sub_add_comm ( by linarith [ Finset.mem_range.mp ‹_› ] ) ] ; ring ] ; linarith );
      exact h_induction m <| hS m hm;
    refine le_trans ( Finset.sum_le_sum h_interchange ) ?_;
    simp +decide only [Finset.mul_sum _ _ _];
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    refine' le_of_eq _;
    refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst ⟩ ) _ _ _ _ <;> simp +decide;
    · exact fun a ha₁ ha₂ => ⟨ le_trans ha₂ ( hS _ ha₁ ), ha₁, ha₂ ⟩;
    · bound;
    · exact fun b hb₁ hb₂ hb₃ => ⟨ b.snd, b.fst, ⟨ hb₂, hb₃ ⟩, rfl ⟩;
  refine le_trans h_interchange <| le_trans ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( h_sum_bound j hj ) <| hz_nonneg j ) ?_;
  refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( add_le_add ( Nat.cast_le.mpr <| min_le_left _ _ ) <| mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| pow_nonneg hp _ ) <| hz_nonneg _ ) _;
  rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ show 0 ≤ ( k : ℝ ) + ( S.card : ℝ ) * p ^ ( k - 1 ) by positivity ] ;

/-
Double counting lower bound: R(m-1)·(eH-m+1) ≤ m·R(m).
-/
lemma double_count_ue_pairs {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hm_le : m ≤ n.choose 2) :
    (numUEWithEdges H (m - 1) : ℝ) * ((H.edgeFinset.card : ℝ) - ↑m + 1) ≤
    ↑m * (numUEWithEdges H m : ℝ) := by
  rcases m with ( _ | m ) <;> simp_all +decide [ numUEWithEdges ];
  -- Let's count the number of pairs (G₀, G) where G₀ has m edges and G is a supergraph of G₀ with m+1 edges.
  have h_pairs : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).sum (fun G => (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card) ≥ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).sum (fun G => (H.edgeFinset.card - G.edgeFinset.card : ℕ)) := by
    have h_pairs : ∀ G₀ : SimpleGraph (Fin n), G₀.edgeFinset.card = m → UniquelyEmbeds G₀ H → (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ G₀ ≤ G ∧ UniquelyEmbeds G H)).card ≥ (H.edgeFinset.card - G₀.edgeFinset.card : ℕ) := by
      intro G₀ hG₀ hUE₀
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ ∈ embeddingFinset G₀ H := by
        contrapose! hUE₀; simp_all +decide [ UniquelyEmbeds ] ;
        exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_eq_zero.mpr ( by aesop ) |> le_of_eq ) ( by norm_num ) );
      have := supergraph_UE_count G₀ H σ 1 hUE₀ hσ;
      by_cases h : 1 ≤ #H.edgeFinset - #G₀.edgeFinset <;> simp_all +decide [ and_comm, and_left_comm, and_assoc ];
    refine' le_trans ( Finset.sum_le_sum fun G₀ hG₀ => h_pairs G₀ ( Finset.mem_filter.mp hG₀ |>.2.1 ) ( Finset.mem_filter.mp hG₀ |>.2.2 ) ) _;
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
    any_goals exact Finset.univ.filter fun G => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H;
    · exact Finset.sum_le_sum fun x hx => Finset.card_mono fun y hy => by aesop;
    · aesop;
  -- Since each graph $G$ with $m+1$ edges has at most $m+1$ subgraphs with $m$ edges, we have:
  have h_bound : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).sum (fun G => (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card) ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m + 1 ∧ UniquelyEmbeds G H)).card * (m + 1) := by
    have h_bound : ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = m + 1 → (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G ∧ UniquelyEmbeds G₀ H)).card ≤ m + 1 := by
      intros G hG_card
      have h_subgraphs : (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)).card ≤ m + 1 := by
        have h_subgraphs : (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)).card ≤ Finset.card (Finset.powersetCard m G.edgeFinset) := by
          have h_subgraphs : Finset.image (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset) (Finset.univ.filter (fun G₀ : SimpleGraph (Fin n) => G₀.edgeFinset.card = m ∧ G₀ ≤ G)) ⊆ Finset.powersetCard m G.edgeFinset := by
            grind +suggestions;
          have := Finset.card_le_card h_subgraphs;
          rwa [ Finset.card_image_of_injOn ] at this ; intro a ha b hb ; aesop;
        simp_all +decide [ Finset.card_powersetCard ];
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_subgraphs;
    exact Finset.sum_le_card_nsmul _ _ _ fun x hx => h_bound x <| Finset.mem_filter.mp hx |>.2.1;
  norm_cast;
  rw [ Int.subNatNat_eq_coe ] ; push_cast ; norm_num [ mul_comm ] at *;
  have h_sum_bound : ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H), (H.edgeFinset.card - G.edgeFinset.card : ℕ) ≥ (H.edgeFinset.card - m) * (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧ UniquelyEmbeds G H)).card := by
    rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_filter.mp hx |>.2.1 ] ] ; norm_num [ mul_comm ];
  by_cases h : #H.edgeFinset ≤ m <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
  · exact le_trans ( mul_nonpos_of_nonpos_of_nonneg ( by linarith ) ( Nat.cast_nonneg _ ) ) ( by positivity );
  · grind +locals

/-- The UE fraction: f(m) = R(m)/C(N,m). -/
noncomputable def fUE {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) : ℝ :=
  (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)

/-! ### Edge-subset bridge for the transition sum bound -/

/-- Graph constructed from a set of non-diagonal Sym2 elements. -/
private noncomputable def graphOfEdges {n : ℕ}
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (S.image Subtype.val : Set (Sym2 (Fin n)))

/-- The UE predicate on edge subsets. -/
private def UEPred {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}) : Prop :=
  UniquelyEmbeds (graphOfEdges S) H

private instance UEPred_decidable {n : ℕ} (H : SimpleGraph (Fin n)) :
    DecidablePred (UEPred H) := fun S => inferInstance

/-
Interval property for UEPred.
-/
private lemma UEPred_interval {n : ℕ} (H : SimpleGraph (Fin n))
    (S₁ S₂ S₃ : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag})
    (h12 : S₁ ⊆ S₂) (h23 : S₂ ⊆ S₃)
    (hP1 : UEPred H S₁) (hP3 : UEPred H S₃) :
    UEPred H S₂ := by
  apply ue_chain_interval;
  rotate_left;
  rotate_left;
  exact hP1;
  exact hP3;
  · intro u v; simp +decide [ graphOfEdges ] ;
    exact fun _ h => ⟨ ‹_›, h12 h ⟩;
  · rw [ graphOfEdges, graphOfEdges ] ; exact SimpleGraph.fromEdgeSet_mono <| by aesop_cat;

/-
UEPred on the empty set is false for n ≥ 2.
-/
private lemma UEPred_empty {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    ¬ UEPred H ∅ := by
  -- The empty Finset gives graphOfEdges ∅ = fromEdgeSet ∅ = ⊥ (the empty graph).
  simp [UEPred, graphOfEdges];
  -- The empty graph has n! embeddings into any graph H, so it cannot be uniquely embeddable.
  simp [UniquelyEmbeds];
  -- The number of embeddings of the empty graph into any graph H is the number of permutations of the vertices of H, which is n!.
  have h_empty_embeddings : numEmbeddings ⊥ H = Nat.factorial n := by
    convert numEmbeddings_top ⊥ using 1;
    unfold numEmbeddings;
    unfold embeddingFinset;
    unfold IsEmbedding; aesop;
  exact h_empty_embeddings.symm ▸ Nat.ne_of_gt ( Nat.lt_of_lt_of_le ( by decide ) ( Nat.factorial_le hn ) )

/-
Extension count: for S with UEPred H S, the number of extensions is eH - |S|.
-/
set_option maxHeartbeats 1600000 in
private lemma UEPred_ext_count {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag})
    (hPS : UEPred H S) (hScard : S.card < Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag}) :
    ((Finset.univ : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag}).filter
      (fun e => e ∉ S ∧ UEPred H (insert e S))).card =
    H.edgeFinset.card - S.card := by
  -- By definition of `UEPred`, there exists a unique embedding `σ` such that `σ ∈ embeddingFinset (graphOfEdges S) H`.
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : SimpleGraph (Fin n), graphOfEdges S = G₀ ∧ UniquelyEmbeds G₀ H := by
    exact ⟨ _, rfl, hPS ⟩;
  -- Since `σ` is in `embeddingFinset G₀ H`, by `supergraph_UE_count`, the number of supergraphs `G'` of `G₀` with `G'.edgeFinset.card = G₀.edgeFinset.card + 1` and `UniquelyEmbeds G' H` is `(H.edgeFinset.card - G₀.edgeFinset.card).choose 1`.
  have h_card_supergraphs : (Finset.univ.filter (fun G' : SimpleGraph (Fin n) => G₀ ≤ G' ∧ G'.edgeFinset.card = G₀.edgeFinset.card + 1 ∧ UniquelyEmbeds G' H)).card = (H.edgeFinset.card - G₀.edgeFinset.card) := by
    have := supergraph_UE_count G₀ H;
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ ∈ embeddingFinset G₀ H := by
      have := hG₀.2;
      have := Finset.card_pos.mp ( show 0 < Finset.card ( embeddingFinset G₀ H ) from ?_ ) ; aesop;
      exact?;
    by_cases h : 1 ≤ H.edgeFinset.card - G₀.edgeFinset.card <;> simp_all +decide [ Nat.choose ];
    · simpa using this σ 1 hσ h;
    · intro G' hG' hG'_card hG'_UE
      have hG'_edgeFinset : G'.edgeFinset.card ≤ H.edgeFinset.card := by
        obtain ⟨ σ, hσ ⟩ := Finset.card_pos.mp ( show 0 < Finset.card ( Finset.filter ( fun σ : Equiv.Perm ( Fin n ) => IsEmbedding G' H σ ) Finset.univ ) from by
                                                  exact? );
        have hG'_edgeFinset : G'.edgeFinset.image (fun e => Sym2.map (fun v => σ v) e) ⊆ H.edgeFinset := by
          simp_all +decide [ Finset.subset_iff, IsEmbedding ];
          rintro ⟨ u, v ⟩ huv; specialize hσ u v; aesop;
        have := Finset.card_le_card hG'_edgeFinset; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
        rw [ Finset.card_image_of_injective ] at this <;> norm_num [ Function.Injective ] at * ; linarith;
        rintro ⟨ a, b ⟩ ⟨ c, d ⟩ h; simp_all +decide [ Sym2.eq_iff ] ;
      omega;
  -- By definition of `graphOfEdges`, the edge set of `G₀` is exactly `S`.
  have h_edge_set : G₀.edgeFinset = S.image Subtype.val := by
    unfold graphOfEdges at hG₀; aesop;
  convert h_card_supergraphs using 1;
  · refine' Finset.card_bij ( fun e he => graphOfEdges ( insert e S ) ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
    · intro a ha hS hUE
      have hG₀_le : G₀ ≤ graphOfEdges (insert ⟨a, ha⟩ S) := by
        intro u v; simp_all +decide [ graphOfEdges ] ;
        replace h_edge_set := Finset.ext_iff.mp h_edge_set ( s(u, v) ) ; aesop;
      have hG₀_card : (graphOfEdges (insert ⟨a, ha⟩ S)).edgeFinset.card = (image Subtype.val S).card + 1 := by
        have hG₀_card : (graphOfEdges (insert ⟨a, ha⟩ S)).edgeFinset = (image Subtype.val S) ∪ {a} := by
          unfold graphOfEdges; aesop;
        rw [ hG₀_card, Finset.card_union ] ; aesop
      have hG₀_uniquelyEmbeds : UniquelyEmbeds (graphOfEdges (insert ⟨a, ha⟩ S)) H := by
        exact hUE
      exact ⟨hG₀_le, hG₀_card, hG₀_uniquelyEmbeds⟩;
    · intro a ha ha' ha'' b hb hb' hb'' hab; replace hab := congr_arg ( fun G => G.edgeFinset ) hab; simp_all +decide [ Finset.ext_iff, SimpleGraph.edgeSet ] ;
      specialize hab a ; simp_all +decide [ graphOfEdges ];
    · intro G' hG' hG'_card hG'_UE
      obtain ⟨e, he⟩ : ∃ e : {e : Sym2 (Fin n) // ¬e.IsDiag}, e ∉ S ∧ G'.edgeFinset = S.image Subtype.val ∪ {e.val} := by
        have h_edge_set : G'.edgeFinset ⊇ S.image Subtype.val := by
          exact h_edge_set ▸ SimpleGraph.edgeFinset_mono hG';
        have h_edge_set : ∃ e ∈ G'.edgeFinset, e ∉ S.image Subtype.val := by
          exact Finset.not_subset.mp fun h => by have := Finset.card_le_card h; linarith;
        obtain ⟨ e, he₁, he₂ ⟩ := h_edge_set; use ⟨ e, by
          cases e ; aesop ⟩ ; simp_all +decide [ Finset.ext_iff ] ;
        all_goals generalize_proofs at *;
        have := Finset.eq_of_subset_of_card_le ( show image Subtype.val S ∪ { e } ⊆ G'.edgeFinset from Finset.union_subset h_edge_set ( Finset.singleton_subset_iff.mpr <| by aesop ) ) ; simp_all +decide [ Finset.card_union ] ;
        intro a; replace this := Finset.ext_iff.mp this a; aesop;
      refine' ⟨ e.val, e.property, ⟨ he.1, _ ⟩, _ ⟩ <;> simp_all +decide [ UEPred ];
      · convert hG'_UE using 1;
        ext u v; simp [graphOfEdges, he];
        replace he := Finset.ext_iff.mp he.2 ( s(u, v) ) ; aesop;
      · ext u v; simp +decide [ graphOfEdges, he ] ;
        replace he := Finset.ext_iff.mp he.2 ( s(u, v) ) ; aesop;
  · rw [ h_edge_set, Finset.card_image_of_injective _ Subtype.coe_injective ]

/-
Counting equivalence: numUEWithEdges matches the edge-subset count.
-/
set_option maxHeartbeats 800000 in
private lemma UEPred_countP {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) :
    numUEWithEdges H m =
    (Finset.univ.filter (fun S : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag} =>
      S.card = m ∧ UEPred H S)).card := by
  refine' Finset.card_bij _ _ _ _;
  use fun G hG => Finset.univ.filter (fun e => e.val ∈ G.edgeFinset);
  · simp +contextual [ UEPred ];
    intro G hG hUE
    constructor
    ·
      convert hG using 1;
      refine' Finset.card_bij ( fun e he => e.val ) _ _ _ <;> simp +decide;
      exact fun e he => ⟨ he, by cases e; aesop ⟩
    ·
      convert hUE using 1;
      ext u v; simp +decide [ graphOfEdges ] ;
      exact fun h => h.ne;
  · simp +contextual [ Finset.ext_iff, Set.ext_iff ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; ext u v; specialize h ( Sym2.mk ( u, v ) ) ; aesop;
  · intro S hS;
    refine' ⟨ graphOfEdges S, _, _ ⟩ <;> simp_all +decide [ UEPred ];
    · convert hS.1 using 1;
      refine' Finset.card_bij ( fun e he => ⟨ e, _ ⟩ ) _ _ _ <;> simp_all +decide [ graphOfEdges ];
      tauto;
    · ext e; simp [graphOfEdges];
      grind

/-
The z-process sum ≤ 1: key process bound.
    Proved by applying the abstract transition sum bound with the UE predicate
    on edge subsets, using ue_chain_interval for the interval property and
    supergraph_UE_count for the extension count.
-/
set_option maxHeartbeats 1600000 in
lemma sum_z_refined_le_one {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) :
    ∑ m ∈ Finset.range (n.choose 2 + 1),
      (fUE H m - ((H.edgeFinset.card : ℝ) - ↑m + 1) / (↑(n.choose 2) - ↑m + 1) *
       fUE H (m - 1)) ≤ 1 := by
  have := @EdgeOrderingCount.transition_sum_le_one_gen;
  convert this ( fun m => numUEWithEdges H m ) ( fun m => H.edgeFinset.card - m ) ( fun S => UEPred H S ) _ _ _ _ using 1;
  · rw [ Sym2.card_subtype_not_diag ];
    norm_num [ fUE ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rcases x with ( _ | x ) <;> norm_num;
    · exact Or.inr ( numUEWithEdges_zero hn H );
    · by_cases h : x ≤ H.edgeFinset.card;
      · exact Or.inl ( by rw [ Nat.cast_sub h ] ; ring );
      · exact Or.inr <| Or.inl <| by rw [ numUEWithEdges ] ; exact Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun G hG => by intro h; linarith [ show G.edgeFinset.card ≤ H.edgeFinset.card from by
                                                                                                                                                                  exact h.2 |> fun h => by
                                                                                                                                                                    obtain ⟨ σ, hσ ⟩ := Finset.card_eq_one.mp h;
                                                                                                                                                                    rw [ Finset.eq_singleton_iff_unique_mem ] at hσ;
                                                                                                                                                                    have h_card_le : G.edgeFinset.card ≤ (Finset.image (fun e => Sym2.map σ e) G.edgeFinset).card := by
                                                                                                                                                                      rw [ Finset.card_image_of_injective ];
                                                                                                                                                                      intro e₁ e₂ h; induction e₁ using Sym2.inductionOn ; induction e₂ using Sym2.inductionOn ; aesop;
                                                                                                                                                                    refine le_trans h_card_le <| Finset.card_le_card ?_;
                                                                                                                                                                    simp +decide [ Finset.subset_iff, SimpleGraph.edgeSet ];
                                                                                                                                                                    rintro ⟨ u, v ⟩ huv; simp_all +decide [ edgeSetEmbedding ] ;
                                                                                                                                                                    exact hσ.1 |> fun h => by simpa using Finset.mem_filter.mp h |>.2 u v huv; ] ;
  · exact?;
  · exact?;
  · convert UEPred_ext_count hn H using 1;
  · exact?

/-
**Process inequality** (key combinatorial bound from the random graph process).

    For any set S of edge counts, the sum of UE fractions f(m) = R(m)/C(N,m)
    is bounded by k + |S| · (eH/N)^{k-1}.

    Proved by combining abstract_process_bound with sum_z_refined_le_one.
-/
lemma process_inequality {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin n))
    (k : ℕ) (hk : 1 ≤ k) (hk_le : k ≤ H.edgeFinset.card)
    (S : Finset ℕ) (hS : ∀ m ∈ S, m ≤ n.choose 2) :
    (∑ m ∈ S,
      (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≤
    ↑k + ↑S.card * ((H.edgeFinset.card : ℝ) / ↑(n.choose 2)) ^ (k - 1) := by
  have := @abstract_process_bound;
  contrapose! this;
  refine' ⟨ n.choose 2, fun m => if m ≤ n.choose 2 then ( numUEWithEdges H m : ℝ ) / ( Nat.choose ( n.choose 2 ) m : ℝ ) else 0, fun m => if m ≤ n.choose 2 then Max.max 0 ( ( numUEWithEdges H m : ℝ ) / ( Nat.choose ( n.choose 2 ) m : ℝ ) - ( ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ) ) * ( if m = 0 then 0 else ( numUEWithEdges H ( m - 1 ) : ℝ ) / ( Nat.choose ( n.choose 2 ) ( m - 1 ) : ℝ ) ) ) else 0, ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ), k, S, _, _, _, _, _ ⟩ <;> norm_num;
  · exact numUEWithEdges_zero hn H;
  · intro m; split_ifs <;> positivity;
  · intro m; split_ifs <;> positivity;
  · grind +locals;
  · refine' ⟨ div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ _ ( Nat.cast_nonneg _ ), hk, hS, _, _, _ ⟩;
    · convert H.card_edgeFinset_le_card_choose_two;
      norm_num;
    · refine' le_trans _ ( sum_z_refined_le_one hn H );
      refine' Finset.sum_le_sum fun m hm => _;
      split_ifs <;> norm_num [ fUE ];
      · simp_all +decide [ numUEWithEdges_zero hn ];
      · constructor;
        · have := double_count_ue_pairs hn H m ( Nat.pos_of_ne_zero ‹_› ) ‹_›;
          rw [ div_mul_div_comm, div_le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ Nat.choose_succ_succ ];
          · rcases m <;> simp_all +decide [ Nat.add_one_mul_choose_eq, mul_assoc, mul_comm, mul_left_comm ];
            refine' le_trans ( mul_le_mul_of_nonneg_left this ( Nat.cast_nonneg _ ) ) _;
            rw [ ← mul_assoc, ← mul_assoc ];
            exact mul_le_mul_of_nonneg_right ( by nlinarith [ Nat.add_one_mul_choose_eq ( Nat.choose n 2 ) ‹_›, Nat.choose_succ_succ ( Nat.choose n 2 ) ‹_› ] ) ( Nat.cast_nonneg _ );
          · exact Nat.choose_pos ( Nat.sub_le_of_le_add <| by linarith );
          · exact Nat.choose_pos ‹_›;
        · have h_frac_le : ((H.edgeFinset.card : ℝ) - m + 1) / (n.choose 2 - m + 1) ≤ (H.edgeFinset.card : ℝ) / (n.choose 2) := by
            rw [ div_le_div_iff₀ ] <;> norm_num;
            · have h_frac_le : (H.edgeFinset.card : ℝ) ≤ n.choose 2 := by
                have := H.card_edgeFinset_le_card_choose_two;
                aesop;
              nlinarith [ show ( m : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ‹_› ];
            · exact add_pos_of_nonneg_of_pos ( sub_nonneg_of_le ( mod_cast by linarith ) ) zero_lt_one;
            · exact Nat.choose_pos ( by linarith );
          nlinarith [ show 0 ≤ ( numUEWithEdges H ( m - 1 ) : ℝ ) / ( Nat.choose ( n.choose 2 ) ( m - 1 ) : ℝ ) by positivity ];
      · linarith [ Finset.mem_range.mp hm ];
    · intros; linarith;
    · exact this.trans_le ( Finset.sum_le_sum fun x hx => by rw [ if_pos ( hS x hx ) ] )

/-
Restricted sum lower bound: from probUniqueEmb H ≥ δ, Chernoff concentration,
    and the binomial anticoncentration bound, we get a large restricted sum of
    UE fractions over edge counts near N/2.
-/
set_option maxHeartbeats 800000 in
lemma restricted_sum_lower_bound {n : ℕ} (hn : 4 ≤ n) (H : SimpleGraph (Fin n))
    (δ : ℝ) (hδ : 0 < δ) (hH : probUniqueEmb H ≥ δ)
    (L : ℕ) (hL : 0 < L)
    (hchern : ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (L : ℝ) * n)).card : ℝ) ≤
      (δ / 4) * 2 ^ (n.choose 2)) :
    ∃ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) ∧
      S.card ≤ 2 * L * n + 1 ∧
      (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≥
        3 * δ * ↑n / 16 := by
  -- By definition of $probUniqueEmb$, we know that
  have h_prob_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ)) ≥ δ * 2 ^ (n.choose 2) := by
    refine' le_trans ( mul_le_mul_of_nonneg_right hH ( by positivity ) ) _;
    unfold probUniqueEmb numUEWithEdges; norm_num;
    rw_mod_cast [ ← Finset.card_biUnion ];
    · refine Finset.card_mono ?_;
      intro G hG; simp_all +decide [ Finset.subset_iff ] ;
      convert G.card_edgeFinset_le_card_choose_two using 1;
      norm_num;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
  -- By definition of $numUEWithEdges$, we know that
  have h_numUE_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ)) ≤ (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ) * (if |((m : ℝ) - (n.choose 2 : ℝ) / 2)| < L * n then 1 else 0)) + (δ / 4) * 2 ^ (n.choose 2) := by
    have h_numUE_def : (∑ m ∈ Finset.range (n.choose 2 + 1), (numUEWithEdges H m : ℝ) * (if |((m : ℝ) - (n.choose 2 : ℝ) / 2)| ≥ L * n then 1 else 0)) ≤ (δ / 4) * 2 ^ (n.choose 2) := by
      refine le_trans ?_ hchern;
      simp +decide [ numUEWithEdges ];
      norm_num [ Finset.sum_ite ];
      rw_mod_cast [ ← Finset.card_biUnion ];
      · exact Finset.card_le_card fun x hx => by aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    convert add_le_add_left h_numUE_def _ using 1;
    all_goals rw [ add_comm ];
    rw [ add_comm, ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> linarith;
  -- Let's choose the set $S$ of edge counts $m$ such that $|m - N/2| < Ln$.
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) ∧ S.card ≤ 2 * L * n + 1 ∧ (∑ m ∈ S, (numUEWithEdges H m : ℝ)) ≥ (3 * δ / 4) * 2 ^ (n.choose 2) := by
    refine' ⟨ Finset.filter ( fun m : ℕ => |( m : ℝ ) - n.choose 2 / 2| < L * n ) ( Finset.range ( n.choose 2 + 1 ) ), _, _, _ ⟩ <;> norm_num at *;
    · grind +revert;
    · refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.Ico ( Nat.ceil ( ( n.choose 2 : ℝ ) / 2 - L * n ) ) ( Nat.ceil ( ( n.choose 2 : ℝ ) / 2 + L * n ) );
      · intro m hm; simp_all +decide [ abs_lt ] ;
        exact ⟨ by linarith, Nat.lt_ceil.mpr <| by linarith ⟩;
      · norm_num [ Nat.card_Ico ];
        linarith [ Nat.le_ceil ( ( n.choose 2 : ℝ ) / 2 - L * n ) ];
    · norm_num [ Finset.sum_ite ] at * ; linarith;
  -- Apply the binomial anticoncentration bound to each term in the sum.
  have h_binom_anticoncentration : ∀ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ) ≥ (numUEWithEdges H m : ℝ) * (n / (4 * 2 ^ (n.choose 2))) := by
    intros m hm
    have h_binom_anticoncentration : ((n.choose 2).choose m : ℝ) / 2 ^ (n.choose 2) ≤ 4 / n := by
      exact binomial_anticoncentration hn m;
    rw [ ge_iff_le, mul_div, div_le_div_iff₀ ] <;> try positivity;
    · rw [ div_le_div_iff₀ ] at h_binom_anticoncentration <;> first | positivity | nlinarith [ show ( 0 : ℝ ) ≤ numUEWithEdges H m by positivity ] ;
    · exact Nat.cast_pos.mpr ( Nat.choose_pos ( hS.1 m hm ) );
  refine' ⟨ S, hS.1, hS.2.1, le_trans _ ( Finset.sum_le_sum h_binom_anticoncentration ) ⟩;
  rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast, show ( 2 ^ n.choose 2 : ℝ ) > 0 by positivity, mul_div_cancel₀ ( n : ℝ ) ( by positivity : ( 4 * 2 ^ n.choose 2 : ℝ ) ≠ 0 ) ] ;

/-
For large n and probUniqueEmb H ≥ δ, H has at least n edges.
    Uses the union bound: probUniqueEmb H ≤ n! · 2^{eH} / 2^N,
    and for eH < n this is exponentially small for large n.
-/
lemma ue_implies_many_edges (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ → n ≤ H.edgeFinset.card := by
  -- Use probUniqueEmb_le_factorial_div which gives probUniqueEmb H ≤ n!/2^{N-eH}.
  have h_prob_le : ∀ n : ℕ, ∀ H : SimpleGraph (Fin n), probUniqueEmb H ≤ (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - H.edgeFinset.card) := by
    exact?;
  -- For n large enough: n!/2^{n(n-3)/2} < δ. This gives a contradiction with probUniqueEmb H ≥ δ.
  have h_contradiction : ∃ n₀ : ℕ, ∀ n ≥ n₀, (Nat.factorial n : ℝ) / 2 ^ (n.choose 2 - n) < δ := by
    -- We'll use that $n! / 2^{n(n-3)/2}$ tends to $0$ as $n$ tends to infinity.
    have h_lim : Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ) / 2 ^ (n * (n - 3) / 2)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $n! \leq n^n$ and $2^{n(n-3)/2}$ grows much faster than $n^n$.
      have h_bound : ∀ n : ℕ, n ≥ 10 → (n.factorial : ℝ) / 2 ^ (n * (n - 3) / 2) ≤ (n / 2 ^ ((n - 3) / 2 : ℝ)) ^ n := by
        intros n hn
        have h_factorial_bound : (n.factorial : ℝ) ≤ n ^ n := by
          exact mod_cast Nat.recOn n ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ih ) ( by gcongr ; linarith ) ;
        have h_exp_bound : (2 : ℝ) ^ (n * (n - 3) / 2) = (2 ^ ((n - 3) / 2 : ℝ)) ^ n := by
          rw [ ← Real.rpow_natCast _ n, ← Real.rpow_natCast _ ( n * ( n - 3 ) / 2 ), ← Real.rpow_mul ] <;> norm_num;
          rw [ ← Real.rpow_natCast ] ; rw [ Nat.cast_div ] <;> norm_num ; ring;
          · rw [ Nat.cast_sub ( by linarith ) ] ; ring;
          · rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ ← even_iff_two_dvd, mul_add, parity_simps ]
        rw [div_pow]
        field_simp [h_exp_bound];
        rw [ h_exp_bound, mul_comm ] ; gcongr;
      -- For $n \geq 10$, we have $n / 2^{(n-3)/2} < 1$, thus $(n / 2^{(n-3)/2})^n \to 0$ as $n \to \infty$.
      have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n / 2 ^ ((n - 3) / 2 : ℝ)) : ℕ → ℝ) Filter.atTop (nhds 0) := by
        -- We can use the fact that $2^{(n-3)/2}$ grows much faster than $n$.
        have h_exp_growth : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.exp ((n - 3) / 2 * Real.log 2)) Filter.atTop (nhds 0) := by
          -- We can use the fact that $n / e^{(n-3)/2 \ln 2}$ tends to $0$ as $n$ tends to infinity.
          have h_lim_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.exp (n * Real.log 2 / 4)) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{n \ln 2}{4}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{4y}{e^y}$.
            suffices h_lim_y : Filter.Tendsto (fun y : ℝ => 4 * y / Real.exp y) Filter.atTop (nhds 0) by
              have h_subst : Filter.Tendsto (fun n : ℕ => 4 * (n * Real.log 2 / 4) / Real.exp (n * Real.log 2 / 4)) Filter.atTop (nhds 0) := by
                exact h_lim_y.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| tendsto_natCast_atTop_atTop.atTop_mul_const ( by positivity );
              convert h_subst.div_const ( Real.log 2 ) using 2 <;> ring;
              norm_num [ mul_assoc, mul_comm, mul_left_comm ];
            simpa [ mul_div_assoc, Real.exp_neg ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
          refine' squeeze_zero_norm' _ h_lim_zero;
          filter_upwards [ Filter.eventually_gt_atTop 12 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) ≥ 13 by exact_mod_cast hn ] ;
        convert h_exp_growth using 2 ; norm_num [ Real.rpow_def_of_pos, mul_comm ];
      refine' squeeze_zero_norm' _ _;
      use fun n => ( n / 2 ^ ( ( n - 3 ) / 2 : ℝ ) ) ^ n;
      · filter_upwards [ Filter.eventually_ge_atTop 10 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_bound n hn;
      · rw [ Metric.tendsto_nhds ] at *;
        intro ε hε; filter_upwards [ h_lim_zero ( Min.min ε 1 ) ( lt_min hε zero_lt_one ), Filter.eventually_ge_atTop 10 ] with n hn hn'; simp_all +decide [ abs_div, abs_of_nonneg, Real.rpow_nonneg ] ;
        exact lt_of_le_of_lt ( pow_le_of_le_one ( by positivity ) hn.2.le ( by positivity ) ) hn.1;
    have := h_lim.eventually ( gt_mem_nhds hδ );
    obtain ⟨ n₀, hn₀ ⟩ := Filter.eventually_atTop.mp this; use n₀ + 4; intros n hn; specialize hn₀ n ( by linarith ) ; rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ] ;
    grind;
  contrapose! h_contradiction;
  intro n₀; obtain ⟨ n, hn₁, H, hn₂, hn₃ ⟩ := h_contradiction n₀; use n, hn₁; refine le_trans hn₂ ?_; refine le_trans ( h_prob_le n H ) ?_; gcongr ; linarith;

/-
**Process bound** (core of Lemma 2.2).
-/
lemma process_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ (α : ℝ), α > 0 ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    0 < n.choose 2 ∧
    ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ ⌊δ * ↑n / 32⌋₊ ≥ α := by
  -- Set α = (δ/(20*L))², n₀ = max(n₁, 4*L + ⌈64/δ⌉₊ + 1).
  obtain ⟨L, hL⟩ := chernoff_edge_tail (δ / 4) (by linarith)
  obtain ⟨n₁, hn₁⟩ := ue_implies_many_edges δ hδ
  set α := (δ / (20 * L)) ^ 2
  set n₀ := max n₁ (4 * L + Nat.ceil (64 / δ) + 1);
  refine' ⟨ α, _, n₀, _ ⟩;
  · exact sq_pos_of_pos ( div_pos hδ ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr hL.1 ) ) );
  · intro n hn H hH
    have hn_ge_4 : 4 ≤ n := by
      grind
    have hn_ge_n₁ : n₁ ≤ n := by
      exact le_trans ( le_max_left _ _ ) hn
    have hn_ge_4L : 4 * L ≤ n := by
      grind
    have hn_ge_ceil : Nat.ceil (64 / δ) ≤ n := by
      grind
    have hn_ge_1 : 1 ≤ ⌊δ * n / 32⌋₊ := by
      exact Nat.floor_pos.mpr ( by nlinarith [ Nat.ceil_le.mp hn_ge_ceil, mul_div_cancel₀ 64 hδ.ne' ] );
    obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := restricted_sum_lower_bound hn_ge_4 H δ hδ hH L hL.1 ( hL.2 n hn_ge_4 );
    -- Apply process_inequality to get Σf ≤ k + |S|·(eH/N)^{k-1}.
    have h_process : (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≤ ⌊δ * n / 32⌋₊ + (2 * L * n + 1) * ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊δ * n / 32⌋₊ - 1) := by
      refine le_trans ( process_inequality ( by linarith ) H ⌊δ * n / 32⌋₊ hn_ge_1 ?_ S hS₁ ) ?_;
      · refine le_trans ?_ ( hn₁ n hn_ge_n₁ H hH );
        refine Nat.floor_le_of_le ?_;
        have := hH.trans ( show probUniqueEmb H ≤ 1 from probUniqueEmb_le_one H ) ; rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast, Nat.le_ceil ( 64 / δ ), mul_div_cancel₀ ( 64 : ℝ ) hδ.ne' ] ;
      · gcongr ; norm_cast;
    -- Combine the inequalities to get $(eH/N)^{k-1} \geq \delta/(20L)$.
    have h_combined : ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊δ * n / 32⌋₊ - 1) ≥ δ / (20 * L) := by
      rw [ ge_iff_le, div_le_iff₀ ] <;> try norm_num ; linarith;
      have := Nat.floor_le ( show 0 ≤ δ * n / 32 by positivity );
      nlinarith [ show ( L : ℝ ) ≥ 1 by norm_cast; linarith, show ( n : ℝ ) ≥ 4 by norm_cast, show ( ⌊δ * n / 32⌋₊ : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left ( show ( L : ℝ ) ≥ 1 by norm_cast; linarith ) ( show ( 0 : ℝ ) ≤ n by positivity ) ];
    refine' ⟨ Nat.choose_pos ( by linarith ), _ ⟩;
    refine' le_trans ( pow_le_pow_left₀ ( by positivity ) h_combined 2 ) _;
    rw [ ← pow_mul ];
    refine' pow_le_pow_of_le_one _ _ _;
    · positivity;
    · refine' div_le_one_of_le₀ _ _ <;> norm_cast;
      · convert H.card_edgeFinset_le_card_choose_two using 1;
        norm_num;
      · positivity;
    · rcases k : ⌊δ * n / 32⌋₊ with ( _ | _ | k ) <;> simp_all +decide;
      rw [ Nat.floor_eq_iff ] at k <;> norm_num at * <;> nlinarith [ show ( L : ℝ ) ≥ 1 by norm_cast; linarith, mul_div_cancel₀ ( 64 : ℝ ) hδ.ne' ]

/-
From x^k ≥ α > 0 and x ≤ 1, deduce x ≥ α^(1/k). Equivalently, 1 - x ≤ 1 - α^(1/k).
    For k large enough, 1 - α^(1/k) ≤ 2|ln α|/k.
-/
lemma pow_ge_implies_close_to_one {x α : ℝ} {k : ℕ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k) (h : x ^ k ≥ α) :
    1 - x ≤ -Real.log α / k := by
  by_cases hx_eq_zero : x = 0;
  · rw [ le_div_iff₀ ] <;> norm_num [ hk.ne', hx_eq_zero ] at * <;> linarith;
  · rw [ le_div_iff₀ ( by positivity ) ];
    nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < x by positivity ), Real.log_pow x k, Real.log_le_log ( by positivity ) h ]

lemma reduction_to_dense_large_n :
    ∀ δ : ℝ, δ > 0 →
    ∃ C₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    H.edgeFinset.card + C₀ * n ≥ n.choose 2 := by
  -- Use `process_bound` to get α > 0 and n₀ such that for n ≥ n₀ and probUniqueEmb H ≥ δ:
  intro δ hδ
  obtain ⟨α, hα_pos, n₀, hn₀⟩ := process_bound δ hδ;
  -- Choose C₀ = ⌈32 * (-log α) / δ⌉ + 1.
  use Nat.ceil (32 * (-Real.log α) / δ) + 1;
  -- Choose n₀ such that for n ≥ n₀, ⌊δn/32⌋₊ > 0 and the N/k bound holds.
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ n ≥ n₁, ⌊δ * (n : ℝ) / 32⌋₊ > 0 ∧ (n.choose 2 : ℝ) / ⌊δ * (n : ℝ) / 32⌋₊ ≤ 32 * (n : ℝ) / δ := by
    refine' ⟨ ⌈32 / δ⌉₊ + 1, fun n hn => ⟨ _, _ ⟩ ⟩ <;> norm_num [ Nat.choose_two_right ] at *;
    · exact Nat.floor_pos.mpr ( by nlinarith [ Nat.lt_of_ceil_lt hn, mul_div_cancel₀ 32 hδ.ne' ] );
    · rw [ div_le_div_iff₀ ] <;> try positivity;
      · rcases n with ( _ | _ | n ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
        have := Nat.lt_floor_add_one ( δ * ( n + 1 + 1 ) / 32 );
        rw [ div_le_iff₀ ] at hn <;> nlinarith [ show ( ⌊δ * ( n + 1 + 1 ) / 32⌋₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.floor_pos.mpr ( by nlinarith [ mul_div_cancel₀ 32 hδ.ne' ] ) ) ];
      · exact Nat.cast_pos.mpr ( Nat.floor_pos.mpr ( by nlinarith [ Nat.le_ceil ( 32 / δ ), show ( n : ℝ ) ≥ ⌈32 / δ⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ 32 hδ.ne' ] ) );
  use Max.max n₀ n₁;
  intros n hn H hH
  have h_bound : (n.choose 2 : ℝ) - H.edgeFinset.card ≤ (n.choose 2 : ℝ) * (-Real.log α) / ⌊δ * (n : ℝ) / 32⌋₊ := by
    have h_bound : 1 - (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) ≤ -Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
      have h_bound : ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ ⌊δ * (n : ℝ) / 32⌋₊ ≥ α := by
        exact hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.2;
      have h_bound : 1 - (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) ≤ -Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
        have h_log : Real.log ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ≥ Real.log α / ⌊δ * (n : ℝ) / 32⌋₊ := by
          rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num;
          · simpa [ mul_comm ] using Real.log_le_log ( by positivity ) h_bound;
          · exact hn₁ n ( le_trans ( le_max_right _ _ ) hn ) |>.1
        have h_log : Real.log ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ≤ (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ) - 1 := by
          by_cases h : ( H.edgeFinset.card : ℝ ) / ( n.choose 2 : ℝ ) = 0 <;> simp_all +decide [ Real.log_le_iff_le_exp ];
          · exact absurd h_bound ( not_le_of_gt ( by rw [ zero_pow ( Nat.ne_of_gt ( hn₁ n hn.2 |>.1 ) ) ] ; linarith ) );
          · exact Real.log_le_sub_one_of_pos ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero h.2 ) ) );
        grind;
      exact h_bound;
    rw [ mul_div_assoc ];
    rwa [ one_sub_div ( Nat.cast_ne_zero.mpr <| ne_of_gt <| hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.1 ), div_le_iff₀' <| Nat.cast_pos.mpr <| hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.1 ] at h_bound;
  have h_bound : (n.choose 2 : ℝ) - H.edgeFinset.card ≤ 32 * (n : ℝ) * (-Real.log α) / δ := by
    refine le_trans h_bound ?_;
    convert mul_le_mul_of_nonneg_right ( hn₁ n ( le_trans ( le_max_right _ _ ) hn ) |>.2 ) ( neg_nonneg.mpr ( Real.log_nonpos hα_pos.le ( show α ≤ 1 from _ ) ) ) using 1 <;> ring;
    exact le_trans ( hn₀ n ( le_trans ( le_max_left _ _ ) hn ) H hH |>.2 ) ( pow_le_one₀ ( by positivity ) ( div_le_one_of_le₀ ( mod_cast by
      convert H.card_edgeFinset_le_card_choose_two using 1;
      norm_num ) ( by positivity ) ) );
  have := Nat.le_ceil ( 32 * -Real.log α / δ );
  rw [ div_le_iff₀ ] at this <;> norm_num at * <;> try linarith;
  exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ ( - ( 32 * n * Real.log α ) ) hδ.ne' ] ;

/-- **Lemma 2.2** (Reduction to the very dense case).
    Derived from the Chernoff bound. -/
theorem reduction_to_dense :
    ∀ δ : ℝ, δ > 0 →
    ∃ C : ℕ, ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ δ →
    H.edgeFinset.card + C * n ≥ n.choose 2 := by
  intro δ hδ
  obtain ⟨C₀, n₀, h₀⟩ := reduction_to_dense_large_n δ hδ
  use max C₀ (n₀ / 2 + 1)
  intro n H hH
  by_cases hn : n₀ ≤ n
  · -- Large n: use reduction_to_dense_large_n
    have h1 := h₀ n hn H hH
    calc H.edgeFinset.card + max C₀ (n₀ / 2 + 1) * n
        ≥ H.edgeFinset.card + C₀ * n := by
          apply Nat.add_le_add_left
          exact Nat.mul_le_mul_right n (le_max_left C₀ (n₀ / 2 + 1))
      _ ≥ n.choose 2 := h1
  · -- Small n: use vacuity
    push_neg at hn
    have hn' : n ≤ 2 * (n₀ / 2 + 1) + 1 := by omega
    calc H.edgeFinset.card + max C₀ (n₀ / 2 + 1) * n
        ≥ (max C₀ (n₀ / 2 + 1)) * n := Nat.le_add_left _ _
      _ ≥ (n₀ / 2 + 1) * n := Nat.mul_le_mul_right n (le_max_right C₀ (n₀ / 2 + 1))
      _ ≥ n.choose 2 := small_n_vacuity (n₀ / 2 + 1) n hn'

/-! ### Switch-based infrastructure for Lemma 2.3 -/

lemma embedding_iff_compl {n : ℕ} {G H : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    IsEmbedding G H σ ↔ IsEmbedding Hᶜ Gᶜ σ⁻¹ := by
  -- By contrapositive on each direction.
  constructor <;> intro h <;> simp_all +decide [ IsEmbedding, SimpleGraph.compl_adj ];
  · exact fun u v huv huv' => fun huv'' => huv' <| by simpa [ huv ] using h _ _ huv'';
  · contrapose! h;
    obtain ⟨ u, v, huv, h ⟩ := h; use σ u, σ v; aesop;

/-
The number of embeddings of G into H equals the number of embeddings
    of Hᶜ into Gᶜ (via the bijection σ ↦ σ⁻¹).
-/
lemma numEmbeddings_compl {n : ℕ} (G H : SimpleGraph (Fin n)) :
    numEmbeddings G H = numEmbeddings Hᶜ Gᶜ := by
  refine' Finset.card_bij ( fun σ hσ => σ⁻¹ ) _ _ _ <;> simp_all +decide [ IsEmbedding ];
  · exact fun σ hσ => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simpa using embedding_iff_compl.mp <| Finset.mem_filter.mp hσ |>.2 ⟩;
  · intro b hb
    use b⁻¹
    simp [embeddingFinset] at hb ⊢;
    exact embedding_iff_compl.mpr hb

/-
**Complement duality**: The number of graphs G that uniquely embed
    into H equals the number of graphs G' such that Hᶜ uniquely embeds into G'.
-/
lemma complement_duality {n : ℕ} (H : SimpleGraph (Fin n)) :
    numUniquelyEmbedding H =
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      numEmbeddings Hᶜ G = 1)).card := by
  apply Finset.card_bij (fun G _ => Gᶜ);
  · norm_num +zetaDelta at *;
    exact fun G hG => numEmbeddings_compl G H ▸ hG;
  · aesop;
  · intro b hb; use bᶜ; simp_all +decide [ UniquelyEmbeds ] ;
    rw [ numEmbeddings_compl ] ; aesop

/-
The original `no_switch_exponential_bound` counted *all* graphs G where no
   transposition is an embedding of G into H. That statement is false: for
   H = Kₙ minus one edge the set has size ~2^{C(n−2,2)}, which exceeds
   2^N · exp(−n log n) for large n.

   The paper (Lemma 2.3) instead uses a complement trick: σ embeds G into H iff
   σ⁻¹ embeds Hᶜ into Gᶜ, and since G(n,1/2) is self-complementary in law,
   Pr[G ↪_unique H] = Pr[Hᶜ ↪_unique G]. The switch argument is then applied to
   the sparse graph Hᶜ embedded into a random G, where Azuma–Hoeffding gives the
   needed concentration.

   The resulting bound (combining complement duality, union bound over n!
   bijections, and the Azuma-based switch probability) is:
     probUniqueEmb H ≤ n! · exp(−n log n)
   which tends to 0. We state this as the corrected replacement.

**Corrected Azuma-based bound (Lemma 2.3 core)**:
    For H with ≤ C·n non-edges, `probUniqueEmb H ≤ n! · exp(−n · log n)`.

    **Proof sketch (from the paper)**:
    1. *Complement duality*: σ embeds G into H iff σ⁻¹ embeds Hᶜ into Gᶜ.
       Since G ∼ G(n,1/2) is self-complementary in distribution,
       Pr_G[G ↪_unique H] = Pr_G[Hᶜ ↪_unique G].
    2. *Switch definition*: For a bijection π and distinct u,v ∈ V(G),
       {u,v} is a π-switch if N_G(v) ⊇ π(N_{Hᶜ}(π⁻¹(u)) \ N_{Hᶜ}(π⁻¹(v)))
       and symmetrically. If π embeds Hᶜ into G and {u,v} is a π-switch,
       then swapping yields a second embedding.
    3. *Claim 2.4 (iterative pruning)*: Find T ⊆ V(H) with |T| ≥ n/log^D(n),
       low-degree in Hᶜ, independent, with controlled high-degree interaction.
    4. *Azuma*: S = Σ_{u,v ∈ T} 𝟙[{u,v} is π-switch]. E[S] ≥ 2^{−8C}C(|T|,2)
       and Σ b_e² ≤ 2Cn³/log^{6D}(n). By `azuma_hoeffding`: Pr[S = 0] ≤ e^{−n log n}.
    5. *Union bound*: Pr[∃ π without switch] ≤ n! · e^{−n log n}.

    Derived from the `azuma_hoeffding` black box + Claim 2.4 pruning.

    The proof uses the paper's **switch condition**: for distinct u,v ∈ V(G),
    {u,v} is an id-switch for Hᶜ in G if
      N_G(v) ⊇ N_{Hᶜ}(u) \ N_{Hᶜ}(v) and N_G(u) ⊇ N_{Hᶜ}(v) \ N_{Hᶜ}(u).
    This is weaker than `IsEmbedding Hᶜ G (swap u v)`, but sufficient to
    produce a second embedding when composed with any embedding of Hᶜ into G.
-/

/-  The paper's switch condition IsIdSwitch is defined in SwitchHelpers.lean.
    {u,v} is an id-switch for a sparse graph Hc in G if the asymmetric
    neighborhoods of u and v in Hc are contained in the neighborhoods of
    v and u (respectively) in G. -/

/-
If π embeds Hc into G and {u,v} is an id-switch, then swap(u,v)*π
    also embeds Hc into G.
-/
set_option maxHeartbeats 800000 in
lemma switch_gives_second_embedding {n : ℕ}
    {Hc G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {u v : Fin n}
    (huv : u ≠ v)
    (hπ : IsEmbedding Hc G π)
    (hswitch : IsIdSwitch Hc (π⁻¹ • G) (π⁻¹ u) (π⁻¹ v)) :
    IsEmbedding Hc G (Equiv.swap u v * π) := by
  unfold IsEmbedding at *; simp_all +decide [ IsIdSwitch, Equiv.swap_apply_def ];
  intro a b hab;
  by_cases ha : π a = u <;> by_cases hb : π b = u <;> by_cases ha' : π a = v <;> by_cases hb' : π b = v <;> simp_all +decide [ SimpleGraph.adj_comm ];
  all_goals have := hπ a b hab; simp_all +decide [ SimpleGraph.adj_comm ] ;
  · grind +suggestions;
  · grind +suggestions;
  · grind +suggestions;
  · grind +suggestions

/-
If Hc uniquely embeds into G via π, then there is no id-switch
    in π⁻¹•G for any pair of vertices.
-/
lemma unique_implies_no_switch {n : ℕ}
    {Hc G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    (hπ : IsEmbedding Hc G π)
    (huniq : ∀ τ : Equiv.Perm (Fin n), IsEmbedding Hc G τ → τ = π)
    (u v : Fin n) (huv : u ≠ v) :
    ¬IsIdSwitch Hc (π⁻¹ • G) (π⁻¹ u) (π⁻¹ v) := by
  contrapose! huniq;
  refine' ⟨ Equiv.swap u v * π, switch_gives_second_embedding huv hπ huniq, _ ⟩;
  simp +decide [ Equiv.swap_apply_def, huv ]

/-
The number of G such that Hc uniquely embeds into G is at most
    n! times the number of G with no id-switch for Hc (using the switch condition).
-/
lemma complement_unique_le_factorial_mul_no_switch {n : ℕ} (Hc : SimpleGraph (Fin n)) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      numEmbeddings Hc G = 1)).card ≤
    n.factorial * (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
  -- Let π be the unique embedding of Hc into G.
  have h_unique_embedding : ∀ G : SimpleGraph (Fin n), numEmbeddings Hc G = 1 → ∃ σ : Equiv.Perm (Fin n), IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v) := by
    intro G hG
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), IsEmbedding Hc G σ ∧ ∀ τ : Equiv.Perm (Fin n), IsEmbedding Hc G τ → τ = σ := by
      obtain ⟨ σ, hσ ⟩ := Finset.card_eq_one.mp hG;
      rw [ Finset.eq_singleton_iff_unique_mem ] at hσ;
      exact ⟨ σ, Finset.mem_filter.mp hσ.1 |>.2, fun τ hτ => hσ.2 τ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hτ ⟩ ) ⟩;
    exact ⟨ σ, hσ.1, fun u v huv => unique_implies_no_switch hσ.1 hσ.2 u v huv ⟩;
  -- For each permutation σ, the set of graphs G with a unique embedding π such that π⁻¹ • G is in the no-switch set for σ is at most the number of graphs with no switch for σ.
  have h_card_bound : ∀ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))).card ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
    intro σ
    have h_card_bound : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))).card ≤ (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card := by
      have : Finset.image (fun G => σ⁻¹ • G) (Finset.univ.filter (fun G : SimpleGraph (Fin n) => IsEmbedding Hc G σ ∧ ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc (σ⁻¹ • G) (σ⁻¹ u) (σ⁻¹ v))) ⊆ Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v) := by
        simp +contextual [ Finset.subset_iff ];
        rintro _ G hG hG' rfl u v huv; specialize hG' ( σ u ) ( σ v ) ; aesop;
      exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ) ( Finset.card_mono this );
    convert h_card_bound using 1;
  refine' le_trans _ ( le_trans ( Finset.sum_le_sum fun σ _ => h_card_bound σ ) _ );
  any_goals exact Finset.univ;
  · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
  · norm_num [ Finset.card_univ, Fintype.card_perm ]

/-! ### Azuma infrastructure for per_perm_switch_bound -/

lemma azuma_for_zero_count (N : ℕ) (f : (Fin N → Bool) → ℝ)
    (b : Fin N → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hbd : ∀ i : Fin N, ∀ x y : Fin N → Bool,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (hb_nonneg : ∀ i : Fin N, 0 ≤ b i)
    (hb_pos : 0 < ∑ i : Fin N, (b i) ^ 2)
    (c : ℝ) (hc : c ≥ 0)
    (hexp : c ≤ 2 * ((∑ x : Fin N → Bool, f x) / (2 ^ N : ℝ)) ^ 2 /
      (∑ i : Fin N, (b i) ^ 2)) :
    ((Finset.univ.filter (fun x : Fin N → Bool => f x = 0)).card : ℝ) ≤
    (2 ^ N : ℝ) * Real.exp (-c) := by
  set μ := (∑ x : Fin N → Bool, f x) / (2 ^ N : ℝ) with hμ_def
  have hμ_nonneg : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun _ _ => hf_nonneg _) (by positivity)
  have h_azuma := azuma_hoeffding N f b hbd hb_nonneg μ hμ_nonneg
  dsimp only at h_azuma
  simp only [hμ_def, sub_self] at h_azuma
  have h_eq : (Finset.univ.filter (fun x => f x = 0)) =
      (Finset.univ.filter (fun x => f x ≤ 0)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => le_of_eq h, fun h => le_antisymm h (hf_nonneg x)⟩
  rw [h_eq]
  apply le_trans h_azuma
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 ^ N)
  apply Real.exp_le_exp.mpr
  rw [show (∑ x : Fin N → Bool, f x) / (2 : ℝ) ^ N = μ from hμ_def.symm]
  have h_neg : -(2 * μ ^ 2 / ∑ i, b i ^ 2) ≤ -c := neg_le_neg hexp
  have h_eq2 : -2 * μ ^ 2 / ∑ i, b i ^ 2 = -(2 * μ ^ 2 / ∑ i, b i ^ 2) := by ring
  linarith

/-- Combining low_degree_set_large and greedy_independent_set:
    for Hc with ≤ Cn edges and n ≥ 2, there exists an independent set T
    with |T| ≥ n/(8C+2) and all vertices having degree ≤ 4C in Hc. -/
lemma find_good_independent_set {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (hCn : Hc.edgeFinset.card ≤ C * n) (hn : n ≥ 2) :
    ∃ T : Finset (Fin n),
    (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v) ∧
    (∀ v ∈ T, Hc.degree v ≤ 4 * C) ∧
    T.card ≥ n / (8 * C + 2) ∧
    T.card ≥ 1 := by
  set B := Finset.univ.filter (fun v => Hc.degree v ≤ 4 * C);
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin n), I ⊆ B ∧ (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬Hc.Adj u v) ∧ B.card ≤ I.card * (4 * C + 1) := by
    convert greedy_independent_set Hc B ( 4 * C ) ( fun v hv => Finset.mem_filter.mp hv |>.2 ) using 1;
  refine' ⟨ I, hI.2.1, fun v hv => Finset.mem_filter.mp ( hI.1 hv ) |>.2, _, _ ⟩;
  · have hB_card : B.card ≥ n / 2 := by
      convert low_degree_set_large C Hc hCn using 1;
    rw [ ge_iff_le, Nat.div_le_iff_le_mul_add_pred ];
    · grind;
    · linarith;
  · have := low_degree_set_large C Hc hCn;
    grind +locals


/-
The sum of squared bounded-differences constants for switchCount
    through the edge-slot encoding.
    Σ switchBound(e)² ≤ 4·|T|·Σ_w dT(w)².

    Proof: for each w ∉ T, there are exactly |T| edge slots with
    one endpoint w and the other in T. Each contributes (2·dT(w))² = 4·dT(w)².
    For w ∈ T, dT(w) = 0 (T independent), so these contribute 0.
    Total: Σ_e switchBound(e)² = Σ_{w∉T} |T| · 4·dT(w)² = 4|T|·Σ_w dT(w)².
-/
set_option maxHeartbeats 1600000 in
private lemma claim_2_4_pruning_zero :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ 0 * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * 0) →
    B'.card ≥ n / (8 * 0 + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * 0 + 4) * 0 * (↑n * Real.log ↑n) := by
  use 4; norm_num;
  intro n hn B' hB' hB''; use B'; norm_num at *;
  exact ⟨ by omega, 1, fun w hw => Or.inr zero_lt_one, by omega, by positivity ⟩

/-- C ≥ 1 case of claim_2_4_pruning: the main iterative pruning chain. -/
private lemma claim_2_4_pruning_pos (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) :=
  claim_2_4_pruning_pos_result C hC

lemma claim_2_4_pruning (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) := by
  -- The proof follows the iterative pruning from the paper.
  -- For C = 0: K = 0, so RHS = 0. Use T = B', threshold = B'.card.
  -- For C ≥ 1: use the paper's multi-level pruning chain.
  rcases Nat.eq_zero_or_pos C with rfl | hC_pos
  · -- C = 0: RHS = 0, use T = B', threshold = B'.card
    convert claim_2_4_pruning_zero using 6; all_goals simp
  · -- C ≥ 1: the main case
    exact claim_2_4_pruning_pos C (by omega)

/-! ### Sum of squares with tight bound and pruning -/

/-
Sum of squares of switchBoundTight, restricted to controlled neighborhoods.
    After pruning: for w ∉ T with dT(w) < threshold, the contribution is bounded.
    For w with T ⊆ N_Hc(w), switchBoundTight gives 0 for all edge slots involving w.
-/
set_option maxHeartbeats 3200000 in
lemma switchCount_sum_sq_tight {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (threshold : ℕ)
    (hcontrol : ∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) :
    ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤
    (16 : ℝ) * C * ↑(T.card) ^ 2 * ↑threshold := by
  have h_sum_bound : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w ∉ T, (T.card - (T.filter (fun v => Hc.Adj v w)).card) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) ^ 2 := by
    have h_sum_bound : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w∉T, ∑ v ∈ T, (if Hc.Adj v w then 0 else 4 * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2) := by
      have h_sum_bound : ∀ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 ≤ ∑ w∉T, ∑ v ∈ T, (if e.val.1 = v ∧ e.val.2 = w ∨ e.val.1 = w ∧ e.val.2 = v then (if Hc.Adj v w then 0 else 4 * ((T.filter (fun u => Hc.Adj u w)).card : ℝ) ^ 2) else 0) := by
        intro e
        simp [switchBoundTight];
        split_ifs <;> norm_num [ mul_pow ];
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
        · rw [ Finset.sum_eq_single ( e.val.2 ) ] <;> simp_all +decide [ Finset.sum_ite ];
          · exact le_mul_of_one_le_left ( by positivity ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ by tauto, by tauto ⟩, by tauto ⟩ ⟩ );
          · grind +ring;
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
        · rw [ Finset.sum_eq_single ( e.val.1 ) ] <;> simp_all +decide [ Finset.sum_ite ];
          · exact le_mul_of_one_le_left ( by positivity ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ by tauto, by tauto ⟩, by tauto ⟩ ⟩ );
          · grind;
        · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
      refine' le_trans ( Finset.sum_le_sum fun e _ => h_sum_bound e ) _;
      rw [ Finset.sum_comm ];
      refine' Finset.sum_le_sum fun w hw => _;
      rw [ Finset.sum_comm ];
      refine' Finset.sum_le_sum fun v hv => _;
      split_ifs <;> simp_all +decide [ Finset.sum_ite ];
      refine' mul_le_of_le_one_left ( by positivity ) _;
      refine' mod_cast Finset.card_le_one.mpr _;
      simp +contextual [ EdgeSlot ];
      grind;
    simp_all +decide [ Finset.sum_ite, mul_assoc ];
    refine le_trans h_sum_bound ?_;
    gcongr;
    rw [ le_sub_iff_add_le ] ; norm_cast ; rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr <| by aesop ) ] ; exact Finset.card_mono <| by aesop_cat;
  have h_sum_bound : ∑ w ∉ T, (T.card - (T.filter (fun v => Hc.Adj v w)).card) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) ^ 2 ≤ ∑ w ∉ T, (T.card : ℝ) * 4 * ((T.filter (fun v => Hc.Adj v w)).card : ℝ) * threshold := by
    refine Finset.sum_le_sum fun w hw => ?_;
    cases hcontrol w ( by aesop ) <;> simp_all +decide [ mul_assoc ];
    · rw [ Finset.filter_true_of_mem ‹_› ] ; nlinarith [ show ( 0 : ℝ ) ≤ #T * threshold by positivity ];
    · nlinarith only [ show ( Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) : ℝ ) ≤ threshold by exact_mod_cast le_of_lt ‹_›, show ( Finset.card T : ℝ ) ≥ 0 by positivity, show ( Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) : ℝ ) ^ 2 ≤ threshold * Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) by exact_mod_cast by nlinarith only [ ‹Finset.card ( Finset.filter ( fun v => Hc.Adj v w ) T ) < threshold› ] ];
  have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card ≤ ∑ v ∈ T, Hc.degree v := by
    have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card = ∑ v ∈ T, ∑ w ∉ T, (if Hc.Adj v w then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
    exact Finset.sum_le_sum fun x hx => Finset.card_mono fun y hy => by aesop;
  have h_sum_bound : ∑ w ∉ T, (T.filter (fun v => Hc.Adj v w)).card ≤ 4 * C * T.card := by
    exact h_sum_bound.trans ( by simpa [ mul_comm ] using Finset.sum_le_sum hT_deg );
  refine le_trans ‹_› <| le_trans ‹_› ?_;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  exact mul_le_mul_of_nonneg_right ( by norm_cast; nlinarith ) ( Nat.cast_nonneg _ )

/-! ### Graph↔Bool transfer for Azuma -/

/-
Transfer lemma: apply azuma_for_zero_count through graphEquiv.
    Given bounds b on switchCount through graphDecode and sufficient
    Azuma exponent, derive the zero-count bound for SimpleGraph.
-/
lemma azuma_for_switchCount_zero {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n))
    (b : EdgeSlot n → ℝ)
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hC8 : 8 * C ≤ n.choose 2)
    (hT_card : T.card ≥ 2)
    (hbd : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool,
      (∀ e', e' ≠ e → x e' = y e') →
      |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode y)| ≤ b e)
    (hb_nonneg : ∀ e, 0 ≤ b e)
    (hb_pos : 0 < ∑ e : EdgeSlot n, (b e) ^ 2)
    (hexp : ↑n * Real.log ↑n ≤
      2 * ((∑ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x)) /
           (2 ^ Fintype.card (EdgeSlot n) : ℝ)) ^ 2 /
      (∑ e : EdgeSlot n, (b e) ^ 2)) :
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  have := @azuma_for_zero_count;
  contrapose! this;
  refine' ⟨ Fintype.card ( EdgeSlot n ), _, _, _, _, _, _ ⟩;
  use fun x => switchCount Hc T ( graphDecode ( fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) );
  use fun i => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm i );
  · exact fun x => switchCount_nonneg _ _ _;
  · intro i x y hxy; specialize hbd ( Fintype.equivFin ( EdgeSlot n ) |>.symm i ) ( fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) ( fun e => y ( Fintype.equivFin ( EdgeSlot n ) e ) ) ; aesop;
  · exact fun i => hb_nonneg _;
  · refine' ⟨ _, n * Real.log n, _, _, _ ⟩;
    · convert hb_pos using 1;
      conv_rhs => rw [ ← Equiv.sum_comp ( Fintype.equivFin ( EdgeSlot n ) |> Equiv.symm ) ] ;
    · positivity;
    · convert hexp using 1;
      refine' congrArg₂ _ ( congrArg₂ _ rfl ( congrArg₂ _ ( congr_arg ( fun x : ℝ => x / _ ) ( Finset.sum_bij ( fun x _ => fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) _ _ _ _ ) ) rfl ) ) ( Finset.sum_bij ( fun x _ => ( Fintype.equivFin ( EdgeSlot n ) ).symm x ) _ _ _ _ ) <;> simp +decide;
      · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( Fintype.equivFin ( EdgeSlot n ) |>.symm x ) ;
      · exact fun b => ⟨ fun e => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm e ), by ext; simp +decide ⟩;
      · exact fun e => ⟨ _, Equiv.apply_symm_apply _ _ ⟩;
    · convert this using 1;
      · rw [ card_edgeSlot ];
      · convert rfl;
        convert graphEquiv_card_filter _;
        refine' Finset.card_bij ( fun x hx => fun e => x ( Fintype.equivFin ( EdgeSlot n ) e ) ) _ _ _ <;> simp +decide;
        · exact fun a₁ ha₁ a₂ ha₂ h => funext fun i => by simpa using congr_fun h ( Fintype.equivFin ( EdgeSlot n ) |>.symm i ) ;
        · exact fun b hb => ⟨ fun e => b ( Fintype.equivFin ( EdgeSlot n ) |>.symm e ), by simpa using hb, by ext; simp +decide ⟩

/-! ### Azuma exponent calculation -/

/-
The Azuma exponent is sufficient: given the mean lower bound and sum-of-squares
    upper bound and the ratio from claim 2.4, we have 2μ²/Σb² ≥ n·log n.
-/
set_option maxHeartbeats 6400000 in
lemma azuma_exponent_sufficient {n : ℕ} (C : ℕ) (Hc : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (threshold : ℕ)
    (hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v)
    (hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C)
    (hC8 : 8 * C ≤ n.choose 2)
    (hT_card : T.card ≥ 2)
    (hT_control : ∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold)
    (hT_pos : (T.card : ℝ) - 1 > 0)
    (hT_ratio : ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n))
    (h_sum_pos : 0 < ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2) :
    ↑n * Real.log ↑n ≤
    2 * ((∑ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x)) /
         (2 ^ Fintype.card (EdgeSlot n) : ℝ)) ^ 2 /
    (∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2) := by
  -- By combining the results from the mean switch count lower bound and the sum of squares upper bound, we can derive the required inequality for the Azuma exponent.
  have h_combined : 2 * ((T.offDiag.card : ℝ) * (2 : ℝ) ^ (n.choose 2 - 8 * C)) ^ 2 / (2 ^ n.choose 2) ^ 2 / (16 * C * (T.card : ℝ) ^ 2 * threshold) ≥ n * Real.log n := by
    rw [ div_div, ge_iff_le, le_div_iff₀ ];
    · rcases eq_or_ne threshold 0 <;> simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ];
      rw [ Nat.cast_sub ( by nlinarith ) ] ; push_cast ; ring_nf at *;
      rw [ show n.choose 2 * 2 = ( n.choose 2 - C * 8 ) * 2 + C * 16 by linarith [ Nat.sub_add_cancel hC8 ] ] ; norm_num [ pow_add, pow_mul ] ; ring_nf at *;
      field_simp at *;
      nlinarith [ show ( T.card : ℝ ) ≥ 2 by norm_cast ];
    · cases eq_or_ne C 0 <;> cases eq_or_ne threshold 0 <;> simp_all +decide;
      · contrapose! h_sum_pos; simp_all +decide [ switchBoundTight ] ;
      · unfold switchBoundTight at h_sum_pos ; simp_all +decide;
        contrapose! h_sum_pos; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
        refine' Finset.sum_nonpos fun x hx => _ ; aesop;
      · contrapose! hT_ratio;
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        · contradiction;
        · contradiction;
        · exact mul_pos ( mul_pos ( by positivity ) ( by positivity ) ) ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) );
      · positivity;
  -- Substitute the bounds from mean_switchCount_lower and switchCount_sum_sq_tight into the expression.
  have h_subst : 2 * ((∑ G : SimpleGraph (Fin n), switchCount Hc T G) / (2 ^ n.choose 2 : ℝ)) ^ 2 / (16 * C * (T.card : ℝ) ^ 2 * threshold) ≥ n * Real.log n := by
    refine le_trans h_combined ?_;
    rw [ div_pow, mul_div_assoc' ];
    gcongr;
    convert mean_switchCount_lower Hc C T hT_indep hT_deg hC8 using 1;
  refine le_trans ?_ ( h_subst.trans ?_ );
  · norm_num;
  · rw [ show ( ∑ x : SimpleGraph ( Fin n ), switchCount Hc T x ) = ( ∑ x : EdgeSlot n → Bool, switchCount Hc T ( graphDecode x ) ) from ?_ ];
    · rw [ card_edgeSlot ];
      gcongr;
      convert switchCount_sum_sq_tight C Hc T hT_indep hT_deg threshold hT_control using 1;
    · apply Finset.sum_bij (fun G _ => graphEncode G);
      · simp;
      · exact fun G₁ _ G₂ _ h => by simpa using graphEquiv n |>.injective h;
      · exact fun b _ => ⟨ graphDecode b, Finset.mem_univ _, graphEquiv n |>.right_inv b ⟩;
      · exact fun G _ => congr_arg ( fun f => switchCount Hc T f ) ( graphEquiv n |>.left_inv G ) ▸ rfl

/-! ### Assembly: switchCount_zero_bound -/

set_option maxHeartbeats 6400000 in
/-- **Azuma bound for switchCount = 0**.
    Combines Claim 2.4 pruning, tight bounded differences, and
    Azuma-Hoeffding to show: for large n, for Hc with ≤ Cn edges,
    ∃ T such that #{switchCount = 0} ≤ 2^N · exp(-n log n). -/
lemma switchCount_zero_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∃ T : Finset (Fin n),
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  -- Get n₀ from claim_2_4_pruning
  obtain ⟨n₁, hn₁⟩ := claim_2_4_pruning C
  use max (max n₁ 2) (8 * C + 3)
  intro n hn Hc hCn
  have hn2 : n ≥ 2 := le_trans (le_max_of_le_left (le_max_right _ _)) hn
  have hn1 : n ≥ n₁ := le_trans (le_max_of_le_left (le_max_left _ _)) hn
  -- Get independent set B'
  obtain ⟨B', hB'_indep, hB'_deg, hB'_card, _⟩ := find_good_independent_set C Hc hCn hn2
  -- Apply pruning
  obtain ⟨T, threshold, hTB, hT_card, hT_control, hT_pos, hT_ratio⟩ :=
    hn₁ n hn1 Hc hCn B' hB'_indep hB'_deg hB'_card
  -- T inherits properties from B'
  have hT_indep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬Hc.Adj u v :=
    fun u hu v hv huv => hB'_indep u (hTB hu) v (hTB hv) huv
  have hT_deg : ∀ v ∈ T, Hc.degree v ≤ 4 * C :=
    fun v hv => hB'_deg v (hTB hv)
  have hC8 : 8 * C ≤ n.choose 2 := by
    have hnn : n ≥ 8 * C + 3 := le_trans (le_max_right _ _) hn
    rw [Nat.choose_two_right]
    have h1 : n ≥ 1 := by linarith
    have h2 : n - 1 ≥ 8 * C + 2 := by omega
    have : n * (n - 1) ≥ (8 * C + 3) * (8 * C + 2) :=
      Nat.mul_le_mul hnn h2
    have : (8 * C + 3) * (8 * C + 2) ≥ 16 * C := by nlinarith
    omega
  -- Case split on whether switchBoundTight sum is positive
  by_cases h_sum_pos : 0 < ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2
  · -- Case B: Σb² > 0, apply Azuma
    use T
    apply azuma_for_switchCount_zero C Hc T (fun e => switchBoundTight Hc T e)
      hT_indep hT_deg hC8 hT_card
    · -- bounded differences
      exact fun e x y hxy => switchCount_bounded_diff_tight Hc T hT_indep e x y hxy
    · -- b nonneg
      exact fun e => switchBoundTight_nonneg Hc T e
    · -- Σb² > 0
      exact h_sum_pos
    · -- Azuma exponent sufficient
      exact azuma_exponent_sufficient C Hc T threshold hT_indep hT_deg hC8 hT_card
        hT_control hT_pos hT_ratio h_sum_pos
  · -- Case A: Σb² = 0, switchCount is constant
    push_neg at h_sum_pos
    have h_sum_zero : ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2 = 0 :=
      le_antisymm h_sum_pos (Finset.sum_nonneg fun e _ => sq_nonneg _)
    -- All switchBoundTight are 0
    have hb_zero : ∀ e : EdgeSlot n, switchBoundTight Hc T e = 0 := by
      intro e
      have := Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (switchBoundTight Hc T e))
        |>.mp h_sum_zero e (Finset.mem_univ _)
      exact sq_eq_zero_iff.mp this
    -- switchCount is constant
    have hconst : ∀ x y : EdgeSlot n → Bool,
        switchCount Hc T (graphDecode x) = switchCount Hc T (graphDecode y) := by
      intros x y
      have h_diff_zero : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool, (∀ e', e' ≠ e → x e' = y e') → |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode y)| ≤ switchBoundTight Hc T e := by
        exact fun e x y a ↦ switchCount_bounded_diff_tight Hc T hT_indep e x y a;
      induction' s : Finset.univ.filter (fun e => x e ≠ y e) using Finset.induction with e s ih generalizing x y;
      · simp_all +decide [ Finset.ext_iff ];
        rw [ show x = y from funext s ];
      · rename_i s' hs';
        have h_diff_zero : |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode (fun e' => if e' = e then y e else x e'))| ≤ switchBoundTight Hc T e := by
          grind;
        specialize hs' ( fun e' => if e' = e then y e else x e' ) y ; simp_all +decide [ Finset.ext_iff ];
        grind +ring
    -- The constant must be > 0 (from mean_switchCount_lower)
    have hmean_pos : ∑ G : SimpleGraph (Fin n), switchCount Hc T G > 0 := by
      have hmean := mean_switchCount_lower Hc C T hT_indep hT_deg hC8
      have hoff : (T.offDiag.card : ℝ) > 0 := by
        have : T.offDiag.card > 0 := by
          have : T.card ≥ 2 := hT_card
          simp [Finset.offDiag_card]; omega
        exact Nat.cast_pos.mpr this
      have hpow : (0:ℝ) < 2 ^ (n.choose 2 - 8 * C) := by positivity
      calc (∑ G : SimpleGraph (Fin n), switchCount Hc T G)
          ≥ (T.offDiag.card : ℝ) * 2 ^ (n.choose 2 - 8 * C) := hmean
        _ > 0 := mul_pos hoff hpow
    -- So switchCount > 0 for all G, hence #{switchCount = 0} = 0
    use T
    -- switchCount is constant on SimpleGraph too
    have hconst' : ∀ G₁ G₂ : SimpleGraph (Fin n), switchCount Hc T G₁ = switchCount Hc T G₂ := by
      intro G₁ G₂
      have := hconst (graphEncode G₁) (graphEncode G₂)
      have h1 : graphDecode (graphEncode G₁) = G₁ := (graphEquiv n).left_inv G₁
      have h2 : graphDecode (graphEncode G₂) = G₂ := (graphEquiv n).left_inv G₂
      rw [h1, h2] at this; exact this
    -- All switchCount values equal some constant c > 0
    have hne : switchCount Hc T ⊥ > 0 := by
      by_contra h
      push_neg at h
      have h0 : switchCount Hc T ⊥ = 0 := le_antisymm h (switchCount_nonneg _ _ _)
      have : ∀ G, switchCount Hc T G = 0 := fun G => by rw [hconst' G ⊥, h0]
      have : ∑ G : SimpleGraph (Fin n), switchCount Hc T G = 0 :=
        Finset.sum_eq_zero fun G _ => this G
      linarith
    have : (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        switchCount Hc T G = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro G _; exact ne_of_gt (hconst' G ⊥ ▸ hne)
    simp [this]; positivity

lemma per_perm_switch_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      ∀ u v : Fin n, u ≠ v → ¬IsIdSwitch Hc G u v)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  obtain ⟨n₀, hn₀⟩ := switchCount_zero_bound C
  exact ⟨n₀, fun n hn Hc hCn => by
    obtain ⟨T, hT⟩ := hn₀ n hn Hc hCn
    exact le_trans (by exact_mod_cast Finset.card_le_card (no_switch_subset_switchCount_zero Hc T)) hT⟩

lemma complement_switch_bound (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ H : SimpleGraph (Fin n),
    H.edgeFinset.card + C * n ≥ n.choose 2 →
    probUniqueEmb H ≤ (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) := by
  have := @per_perm_switch_bound C;
  obtain ⟨ n₀, hn₀ ⟩ := this; use n₀ + 2; intros n hn H hH; rw [ probUniqueEmb ] ; specialize hn₀ n ( by linarith ) ( Hᶜ ) ; simp_all +decide;
  have h_card : (numUniquelyEmbedding H : ℝ) ≤ (n.factorial : ℝ) * (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, ¬u = v → ¬IsIdSwitch Hᶜ G u v)).card := by
    convert complement_unique_le_factorial_mul_no_switch Hᶜ using 1;
    rw [ complement_duality ] ; norm_cast;
  rw [ div_le_iff₀ ( by positivity ) ];
  convert h_card.trans ( mul_le_mul_of_nonneg_left ( hn₀ _ ) ( Nat.cast_nonneg _ ) ) using 1 ; ring;
  have h_card : H.edgeFinset.card + Hᶜ.edgeFinset.card = n.choose 2 := by
    have h_card : H.edgeFinset ∪ Hᶜ.edgeFinset = Finset.univ.filter (fun e => e ∈ SimpleGraph.edgeFinset (⊤ : SimpleGraph (Fin n))) := by
      ext e; simp [SimpleGraph.edgeFinset];
      rcases e with ⟨ u, v ⟩ ; by_cases hu : u = v <;> simp +decide [ hu ] ; tauto;
    rw [ ← Finset.card_union_of_disjoint, h_card ];
    · simp +decide [ SimpleGraph.edgeFinset ];
      rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ Finset.card_univ, Sym2.card ];
      rw [ show ( Finset.univ.filter fun x : Sym2 ( Fin n ) => x.IsDiag ) = Finset.image ( fun x : Fin n => Sym2.mk ( x, x ) ) Finset.univ from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · exact Nat.sub_eq_of_eq_add <| by induction n <;> simp +decide [ Nat.choose ] at * ; linarith;
      · ext ⟨ x, y ⟩ ; aesop;
    · simp +decide [ Finset.disjoint_left ];
      rintro ⟨ u, v ⟩ huv; simp_all +decide [ SimpleGraph.compl_adj ] ;
  grind

/-! ### Derivation of dense_case -/

def ExplicitRateStatement : Prop :=
  ∃ (C : ℝ), C > 0 ∧ ∃ (n₀ : ℕ), ∀ n ≥ n₀,
    fSeq n ≤ C * Real.log (Real.log (Real.log (↑n))) / Real.log (Real.log (↑n))


lemma floor_div_log_mul_log_le {x : ℝ} (hx : x > 0) (hlx : Real.log x ≥ 1) :
    (⌊x / Real.log x⌋₊ : ℝ) * Real.log (⌊x / Real.log x⌋₊ : ℝ) ≤ x := by
  set k := ⌊x / Real.log x⌋₊ with hk_def
  by_cases hk0 : k = 0
  · simp [hk0]; exact le_of_lt hx
  have hlx_pos : Real.log x > 0 := lt_of_lt_of_le zero_lt_one hlx
  have hx_div_pos : x / Real.log x > 0 := div_pos hx hlx_pos
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hk_le_div : (k : ℝ) ≤ x / Real.log x := Nat.floor_le (le_of_lt hx_div_pos)
  have hk_le_x : (k : ℝ) ≤ x :=
    le_trans hk_le_div (div_le_self (le_of_lt hx) hlx)
  have hk_ge_one : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hlk_nonneg : Real.log (k : ℝ) ≥ 0 := Real.log_nonneg hk_ge_one
  have hlk_le : Real.log (k : ℝ) ≤ Real.log x :=
    Real.log_le_log hk_pos hk_le_x
  calc (k : ℝ) * Real.log k
      ≤ (x / Real.log x) * Real.log k :=
        mul_le_mul_of_nonneg_right hk_le_div hlk_nonneg.le
    _ ≤ (x / Real.log x) * Real.log x :=
        mul_le_mul_of_nonneg_left hlk_le (le_of_lt hx_div_pos)
    _ = x := div_mul_cancel₀ x (ne_of_gt hlx_pos)

/-- The bounding function: rateF(k) = ⌈exp(exp(k·ln k))⌉₊ for k ≥ 2, and 3 otherwise. -/
def rateF (k : ℕ) : ℕ :=
  if k ≤ 1 then 3 else ⌈Real.exp (Real.exp (↑k * Real.log ↑k))⌉₊

/-! ## Growth bound: rateF(⌊loglogn/logloglogn⌋) ≤ n for large n -/

/-- Auxiliary: log(log(log(n))) is eventually ≥ 1. -/
private lemma eventually_logloglog_ge_one :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → Real.log (Real.log (Real.log (↑n))) ≥ 1 := by
  have : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (↑n))))
      Filter.atTop Filter.atTop := by
    exact (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))
  exact Filter.eventually_atTop.mp (this.eventually_ge_atTop 1)

/-- For sufficiently large n, the bounding function rateF evaluated at
    ⌊log(log(n))/log(log(log(n)))⌋ is at most n.

    This is the **growth compatibility** condition: rateF grows slowly
    enough that rateF(⌊log log n / log log log n⌋) ≤ n. -/
theorem rateF_growth_bound :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.log (Real.log (↑n)) > 1 →
    rateF (⌊Real.log (Real.log (↑n)) / Real.log (Real.log (Real.log (↑n)))⌋₊) ≤ n := by
  obtain ⟨n₁, hn₁⟩ := eventually_logloglog_ge_one
  use max n₁ 3
  intro n hn hloglogn
  have hn₁' : Real.log (Real.log (Real.log (↑n))) ≥ 1 := hn₁ n (le_of_max_le_left hn)
  have hn_ge_3 : (n : ℕ) ≥ 3 := le_of_max_le_right hn
  set x := Real.log (Real.log (↑n)) with hx_def
  set lx := Real.log x with hlx_def
  have hx_pos : x > 0 := by linarith
  have hlx_ge_one : lx ≥ 1 := by rw [hlx_def, hx_def]; exact hn₁'
  have hlx_pos : lx > 0 := lt_of_lt_of_le zero_lt_one hlx_ge_one
  set k := ⌊x / lx⌋₊ with hk_def
  -- The key bound: k * log(k) ≤ x = log(log(n))
  have hkey : (k : ℝ) * Real.log (k : ℝ) ≤ x :=
    floor_div_log_mul_log_le hx_pos hlx_ge_one
  -- Therefore exp(exp(k*logk)) ≤ exp(exp(loglogn)) = exp(logn) = n
  have hexp_le : Real.exp (Real.exp ((k : ℝ) * Real.log (k : ℝ))) ≤ ↑n := by
    calc Real.exp (Real.exp ((k : ℝ) * Real.log (k : ℝ)))
        ≤ Real.exp (Real.exp x) := by
          exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hkey)
      _ = Real.exp (Real.log (↑n)) := by
          rw [hx_def]; congr 1
          exact Real.exp_log (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
      _ = ↑n := Real.exp_log (by positivity : (↑n : ℝ) > 0)
  -- Now bound rateF(k)
  show rateF k ≤ n
  unfold rateF
  split_ifs with hk1
  · -- k ≤ 1: rateF(k) = 3 ≤ n
    exact hn_ge_3
  · -- k ≥ 2: rateF(k) = ⌈exp(exp(k*logk))⌉₊ ≤ n
    exact Nat.ceil_le.mpr (by exact_mod_cast hexp_le)

/-! ## Reduction to the quantitative threshold bound -/

lemma factorial_div_pow_self_le (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ 1 / (n : ℝ) := by
  rw [ div_le_div_iff₀ ] <;> norm_cast;
  · induction hn <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
    rename_i k hk ih;
    rw [ mul_assoc ];
    refine' Nat.le_induction _ _ k hk <;> intros <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
    nlinarith [ pow_le_pow_left' ( by linarith : ‹_› + 1 + 1 ≥ ‹_› + 1 ) ‹_› ];
  · positivity

theorem factorial_exp_at_rateF (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ≥ rateF k, (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) <
    1 / (2 * ↑k) := by
  intro n hn
  have h_n_ge_2k : (n : ℝ) ≥ 2 * k + 1 := by
    -- Since $rateF(k) \geq 2k + 1$, we have $n \geq 2k + 1$.
    have h_rateF_ge_two_k_plus_one : rateF k ≥ 2 * k + 1 := by
      unfold rateF; split_ifs <;> norm_num at *;
      · grind +splitIndPred;
      · refine' Nat.lt_ceil.mpr _;
        rw [ ← Real.log_lt_iff_lt_exp ( by positivity ) ];
        rw [ Nat.cast_mul, Real.log_mul ( by positivity ) ( by positivity ) ];
        have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.add_one_le_exp ( k * Real.log k ), ( by norm_cast : ( 2 :ℝ ) ≤ k ), Real.log_pos ( by norm_cast : ( 1 :ℝ ) < k ) ];
    exact_mod_cast h_rateF_ge_two_k_plus_one.trans hn;
  -- Use the factorial bound: n! ≤ n^n / n
  have h_factorial_bound : (n.factorial : ℝ) / (n : ℝ) ^ n ≤ 1 / (n : ℝ) := by
    convert factorial_div_pow_self_le n ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at h_n_ge_2k; linarith ) ) using 1;
  rw [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log ] at *;
  · exact h_factorial_bound.trans_lt ( one_div_lt_one_div_of_lt ( by positivity ) ( by linarith ) );
  · linarith

/-! ## Decomposition of the frontier -/

set_option maxHeartbeats 800000 in
lemma pw_error_le_geom_sum (n : ℕ) (hn : 4 ≤ n) :
    (numIsoClasses n : ℝ) * (n.factorial : ℝ) / (2 ^ n.choose 2 : ℝ) - 1 ≤
    ∑ m ∈ Finset.Icc 2 n, ((n : ℝ) / 2 ^ ((n - 2) / 4 : ℕ)) ^ m := by
  have := @PolyaWright.ratio_eq_one_plus_remainder;
  specialize this n; simp_all +decide [ paperDenom ] ;
  -- Applying the bound from `saving_lower_bound` and `count_perms_moving_m_le`.
  have h_bound : (∑ σ : Equiv.Perm (Fin n) with ¬σ = 1, (Fintype.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) / 2 ^ (Nat.choose n 2 : ℕ) ≤ ∑ m ∈ Finset.Icc 2 n, (n : ℝ) ^ m / 2 ^ ((m * (n - 2)) / 4 : ℕ) := by
    have h_bound : ∀ m ∈ Finset.Icc 2 n, (∑ σ : Equiv.Perm (Fin n) with ¬σ = 1 ∧ (Finset.univ.filter (fun v => σ v = v)).card = n - m, (Fintype.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ)) / 2 ^ (Nat.choose n 2 : ℕ) ≤ (n : ℝ) ^ m / 2 ^ ((m * (n - 2)) / 4 : ℕ) := by
      intros m hm
      have h_bound : ∀ σ : Equiv.Perm (Fin n), ¬σ = 1 → (Finset.univ.filter (fun v => σ v = v)).card = n - m → (Fintype.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) ≤ 2 ^ (Nat.choose n 2 : ℕ) / 2 ^ ((m * (n - 2)) / 4 : ℕ) := by
        intros σ hσ_ne_one hσ_fixed_points
        have h_bound : (Fintype.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) : ℝ) ≤ (2 : ℝ) ^ (Nat.choose n 2 : ℤ) / (2 : ℝ) ^ ((m * (n - 2)) / 4 : ℕ) := by
          have := @PolyaWright.saving_lower_bound n ( by linarith ) σ;
          simp_all +decide [ fixedPoints ];
          convert this using 2;
          rw [ Fintype.card_subtype ];
          rw [ show ( Finset.univ.filter fun x => IsFixedPt σ x ) = Finset.univ.filter fun x => σ x = x from Finset.filter_congr fun x _ => by simp +decide [ IsFixedPt ] ] ; aesop;
        exact_mod_cast h_bound;
      have h_card : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ¬σ = 1 ∧ (Finset.univ.filter (fun v => σ v = v)).card = n - m)).card ≤ n ^ m := by
        have := @PolyaWright.count_perms_moving_m_le n m;
        refine le_trans ?_ this;
        refine Finset.card_mono ?_;
        simp +contextual [ Finset.subset_iff, fixedPoints ];
        simp +contextual [ Fintype.card_subtype, IsFixedPt ];
        exact fun _ _ _ => Nat.sub_sub_self ( by linarith [ Finset.mem_Icc.mp hm ] );
      rw [ div_le_div_iff₀ ] <;> try positivity;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum fun x hx => h_bound x ( by aesop ) ( by aesop ) ) ( by positivity ) ) _ ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul _ _ _ ];
      rw [ ← mul_assoc, mul_div_cancel₀ _ ( by positivity ) ] ; norm_cast ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( Nat.choose n 2 ) ] ;
    refine' le_trans _ ( Finset.sum_le_sum h_bound );
    rw [ ← Finset.sum_div _ _ _ ];
    rw [ ← Finset.sum_biUnion ];
    · gcongr;
      intro σ hσ; simp_all +decide [ Finset.subset_iff ] ;
      refine' ⟨ n - Finset.card ( Finset.filter ( fun v => σ v = v ) Finset.univ ), _, _ ⟩ <;> norm_num;
      · -- Since σ is not the identity, there are at least two elements that are not fixed points.
        have h_not_fixed : ∃ v w : Fin n, v ≠ w ∧ σ v ≠ v ∧ σ w ≠ w := by
          obtain ⟨v, hv⟩ : ∃ v : Fin n, σ v ≠ v := by
            exact not_forall.mp fun h => hσ <| Equiv.Perm.ext h;
          by_cases h_fixed : ∀ w : Fin n, w ≠ v → σ w = w;
          · have := σ.injective ( show σ ( σ v ) = σ v from by aesop ) ; aesop;
          · grind +ring;
        obtain ⟨ v, w, hvw, hv, hw ⟩ := h_not_fixed; have := Finset.card_le_card ( show Finset.filter ( fun x => σ x = x ) Finset.univ ⊆ Finset.univ \ { v, w } from fun x hx => by aesop ) ; simp_all +decide [ Finset.card_sdiff, Finset.card_singleton ] ;
        omega;
      · rw [ Nat.sub_sub_self ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by linarith [ Finset.mem_filter.mp hx₁, Finset.mem_filter.mp hx₂, Nat.sub_add_cancel ( show i ≤ n from Finset.mem_Icc.mp hi |>.2 ), Nat.sub_add_cancel ( show j ≤ n from Finset.mem_Icc.mp hj |>.2 ) ] ;
  simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  rw [ add_comm ] ; gcongr;
  refine le_trans h_bound ?_;
  refine Finset.sum_le_sum fun x hx => ?_ ; ring_nf ; norm_num;
  exact mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( Nat.mul_div_le_mul_div_assoc _ _ _ ) ) ( by positivity )

/-
n/2^{(n-2)/4} < 1/2 for n ≥ 26.
-/
lemma rateR_lt_half (n : ℕ) (hn : 26 ≤ n) :
    (n : ℝ) / 2 ^ ((n - 2) / 4 : ℕ) < 1 / 2 := by
  rw [ div_lt_div_iff₀ ] <;> norm_cast;
  · induction' n using Nat.strong_induction_on with n ih;
    rcases hn with ( _ | _ | _ | _ | n ) <;> simp +arith +decide at *;
    rename_i k;
    specialize ih k ( by linarith ) ( by linarith );
    rw [ show ( k + 2 ) / 4 = ( k - 2 ) / 4 + 1 by omega ] ; norm_num [ pow_succ' ] at * ; omega;
  · positivity

/-
Geometric sum bound: Σ_{m∈Icc 2 n} x^m ≤ 2x² for 0 ≤ x < 1/2 and n ≥ 2.
-/
lemma geom_sum_Icc_le_two_sq (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Icc 2 n, x ^ m ≤ 2 * x ^ 2 := by
  erw [ Finset.sum_Ico_eq_sum_range ];
  norm_num [ pow_add ];
  rw [ ← Finset.mul_sum _ _ _, geom_sum_eq ];
  · rw [ mul_div, div_le_iff_of_neg ] <;> nlinarith [ pow_nonneg hx0 ( n + 1 - 2 ) ];
  · linarith

/-
rateF(k) ≥ 4k for k ≥ 2.
-/
lemma rateF_ge_four_mul (k : ℕ) (hk : 2 ≤ k) : 4 * k ≤ rateF k := by
  unfold rateF;
  split_ifs <;> norm_num at *;
  · grind;
  · refine Nat.le_of_lt_succ ?_;
    refine' Nat.lt_succ_of_le ( Nat.le_of_lt <| Nat.lt_ceil.mpr _ );
    rw [ Real.exp_nat_mul, Real.exp_log ( by positivity ) ];
    induction hk <;> norm_num [ pow_succ' ] at *;
    · have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 4 ];
    · rename_i k hk₁ hk₂ hk₃;
      refine' lt_of_lt_of_le _ ( Real.add_one_le_exp _ );
      nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, pow_le_pow_right₀ ( by linarith : 1 ≤ ( k : ℝ ) + 1 ) hk₁ ]

/-
For n ≥ 55 and k ≤ n/4: 2(n/2^{(n-2)/4})² < 1/(4k).
    Equivalently: 8kn² < 4^{(n-2)/4}.
-/
lemma pw_bound_at_large_n (n k : ℕ) (hn : 55 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n / 4) :
    2 * ((n : ℝ) / 2 ^ ((n - 2) / 4 : ℕ)) ^ 2 < 1 / (4 * (k : ℝ)) := by
  field_simp;
  -- We'll use that $8kn^2 < 4^{(n-2)/4}$ to conclude the proof.
  have h_ineq : 8 * k * n ^ 2 < 4 ^ ((n - 2) / 4 : ℕ) := by
    -- We'll use that $8kn^2 < 4^{(n-2)/4}$ to conclude the proof. Since $k \leq n/4$, we have $8kn^2 \leq 8(n/4)n^2 = 2n^3$.
    have h_ineq : 8 * k * n ^ 2 ≤ 2 * n ^ 3 := by
      nlinarith [ Nat.div_mul_le_self n 4 ];
    refine lt_of_le_of_lt h_ineq ?_;
    -- We'll use that $2n^3 < 4^{(n-2)/4}$ for $n \geq 55$.
    have h_exp : ∀ n ≥ 55, 2 * n ^ 3 < 4 ^ ((n - 2) / 4 : ℕ) := by
      intro n hn
      induction' n using Nat.strong_induction_on with n ih
      by_cases hn' : n < 59
      generalize_proofs at *; (
      interval_cases n <;> trivial);
      have := ih ( n - 4 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ( Nat.le_sub_of_add_le ( by linarith ) ) ; rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ Nat.pow_succ' ] ;
      rw [ show ( n + 2 ) / 4 = ( n - 2 ) / 4 + 1 by omega ] ; norm_num [ pow_succ' ] at * ; nlinarith [ Nat.sub_add_cancel ( by linarith : 2 ≤ n ) ] ;
    exact h_exp n hn;
  norm_cast ; rw [ pow_right_comm ] ; ring_nf at * ; aesop

/-
rateF(k) ≥ 55 for k ≥ 2. Uses exp(4) > 54 from exp_one_gt_d9.
-/
lemma rateF_ge_55 (k : ℕ) (hk : 2 ≤ k) : 55 ≤ rateF k := by
  unfold rateF; split_ifs;
  · linarith;
  · -- Since $k \geq 2$, we have $k * \log k \geq 2 * \log 2$.
    have h_klogk_ge_2log2 : (k : ℝ) * Real.log k ≥ 2 * Real.log 2 := by
      gcongr <;> norm_cast;
    -- Since $Real.exp (2 * Real.log 2) = 4$, we have $Real.exp (k * Real.log k) ≥ 4$.
    have h_exp_klogk_ge_4 : Real.exp (k * Real.log k) ≥ 4 := by
      exact le_trans ( by norm_num [ ← Real.log_rpow, Real.exp_log ] ) ( Real.exp_le_exp.mpr h_klogk_ge_2log2 );
    -- Since $Real.exp (4) > 54$, we have $Real.exp (Real.exp (k * Real.log k)) > 54$.
    have h_exp_exp_klogk_gt_54 : Real.exp (Real.exp (k * Real.log k)) > 54 := by
      have h_exp_exp_klogk_gt_54 : Real.exp 4 > 54 := by
        have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 4 ];
      exact h_exp_exp_klogk_gt_54.trans_le ( Real.exp_le_exp.mpr h_exp_klogk_ge_4 );
    exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( mod_cast h_exp_exp_klogk_gt_54 ) )

/-
PW convergence rate: for k ≥ 2 and n ≥ rateF(k), PW error < 1/(4k).
-/
theorem pw_convergence_at_rateF (k : ℕ) (hk : 2 ≤ k) :
    ∀ n ≥ rateF k,
    (numIsoClasses n : ℝ) * (n.factorial : ℝ) / (2 ^ n.choose 2 : ℝ) - 1 <
    1 / (4 * ↑k) := by
  intro n hn;
  -- Apply the lemma pw_error_le_geom_sum to bound the error term.
  have h_pw_error : (numIsoClasses n : ℝ) * (n.factorial : ℝ) / 2 ^ n.choose 2 - 1 ≤ ∑ m ∈ Finset.Icc 2 n, ((n : ℝ) / 2 ^ ((n - 2) / 4 : ℕ)) ^ m := by
    convert pw_error_le_geom_sum n ( show 4 ≤ n by
                                      linarith [ rateF_ge_four_mul k hk ] ) using 1;
  refine lt_of_le_of_lt h_pw_error ?_;
  refine' lt_of_le_of_lt ( geom_sum_Icc_le_two_sq _ _ _ _ _ ) _;
  · positivity;
  · exact rateR_lt_half n ( by linarith [ rateF_ge_55 k hk ] );
  · linarith [ show rateF k ≥ 55 by exact rateF_ge_55 k hk ];
  · convert pw_bound_at_large_n n k _ _ _ using 1;
    · exact le_trans ( rateF_ge_55 k hk ) hn;
    · linarith;
    · rw [ Nat.le_div_iff_mul_le ] <;> linarith [ rateF_ge_four_mul k hk ]

/-! ## Reduction to Dense Threshold Only -/

lemma probUniqueEmb_le_inv_of_clog_nonedges {n : ℕ} (hn : 1 ≤ n)
    (H : SimpleGraph (Fin n))
    (h_nonedges : Nat.clog 2 (n * n.factorial) ≤ n.choose 2 - H.edgeFinset.card) :
    probUniqueEmb H ≤ 1 / (n : ℝ) := by
  refine le_trans (probUniqueEmb_le_factorial_div H) ?_
  suffices h : ∀ m : ℕ, Nat.clog 2 (n * n.factorial) ≤ m →
      (n.factorial : ℝ) / 2 ^ m ≤ 1 / n by
    convert h _ h_nonedges
  intro m hm
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ m) (by positivity : (0:ℝ) < (n:ℝ))]
  rw [one_mul]
  have key : n * n.factorial ≤ 2 ^ m := by
    calc n * n.factorial
        ≤ 2 ^ Nat.clog 2 (n * n.factorial) := Nat.le_pow_clog (by norm_num) _
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : n.factorial * n = n * n.factorial := by ring
  exact_mod_cast this ▸ key

/-! ## The adjacent-twin-free reduction -/

lemma probUniqueEmb_lt_inv_2k_of_clog_k_nonedges {n : ℕ} {k : ℕ} (hk : 2 ≤ k) (hn : 3 ≤ n)
    (H : SimpleGraph (Fin n))
    (h_nonedges : Nat.clog 2 (2 * k * n.factorial) ≤ n.choose 2 - H.edgeFinset.card) :
    probUniqueEmb H < 1 / (2 * (k : ℝ)) := by
  refine lt_of_le_of_lt (probUniqueEmb_le_factorial_div H) ?_
  rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 ^ (n.choose 2 - H.edgeFinset.card))
    (by positivity : (0:ℝ) < 2 * (k : ℝ))]
  rw [one_mul]
  -- 2*k*n! is not a power of 2 (has odd factor 3 from n! for n ≥ 3)
  have h_not_pow : ¬ ∃ j, 2 ^ j = 2 * k * n.factorial := by
    intro ⟨j, hj⟩
    have h3 : 3 ∣ n.factorial := (Nat.Prime.dvd_factorial Nat.prime_three).mpr hn
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three
      (hj ▸ dvd_mul_of_dvd_right h3 _)) (by omega)
  -- Hence 2^{clog} > 2*k*n!, and 2^m ≥ 2^{clog} > 2*k*n!
  have h_strict : 2 * k * n.factorial < 2 ^ Nat.clog 2 (2 * k * n.factorial) :=
    lt_of_le_of_ne (Nat.le_pow_clog (by norm_num) _) (fun h => h_not_pow ⟨_, h.symm⟩)
  have h_key : 2 * k * n.factorial < 2 ^ (n.choose 2 - H.edgeFinset.card) :=
    lt_of_lt_of_le h_strict (Nat.pow_le_pow_right (by norm_num) h_nonedges)
  have : (n.factorial * (2 * k) : ℕ) = 2 * k * n.factorial := by ring
  exact_mod_cast this ▸ h_key

private lemma rateF_le_rateF_max (k : ℕ) : rateF k ≤ rateF (max k 2) := by
  by_cases h : k ≤ 1
  · have : max k 2 = 2 := by omega
    calc rateF k = 3 := by simp [rateF, h]
      _ ≤ 55 := by norm_num
      _ ≤ rateF 2 := rateF_ge_55 2 le_rfl
      _ = rateF (max k 2) := by rw [this]
  · push_neg at h
    have : max k 2 = k := by omega
    rw [this]

def densityPred (k : ℕ) (C : ℕ) : Prop :=
  ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
  probUniqueEmb H ≥ 1 / (2 * (k : ℝ)) →
  H.edgeFinset.card + C * n ≥ n.choose 2

lemma densityPred_exists (k : ℕ) (hk : 1 ≤ k) : ∃ C, densityPred k C :=
  reduction_to_dense (1 / (2 * (k : ℝ)))
    (div_pos one_pos (mul_pos two_pos (Nat.cast_pos.mpr (by linarith))))

/-- The MINIMUM density constant for `reduction_to_dense (1/(2k))`.
    Uses `Nat.find` to return the smallest C satisfying:
      ∀ n H, probUniqueEmb H ≥ 1/(2k) → H.edgeFinset.card + C * n ≥ n.choose 2

    - `densityCMin k ≤ densityC k` (since densityC satisfies the predicate)
    - Boundable from above via `Nat.find_min'` by constructing an explicit witness. -/
noncomputable def densityCMin (k : ℕ) : ℕ :=
  if h : 1 ≤ k then
    Nat.find (densityPred_exists k h)
  else 0

lemma densityCMin_spec (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ 1 / (2 * (k : ℝ)) →
    H.edgeFinset.card + (densityCMin k) * n ≥ n.choose 2 := by
  unfold densityCMin; rw [dif_pos hk]
  exact Nat.find_spec (densityPred_exists k hk)


/-- The minimum n₀ threshold (via Nat.find). -/
noncomputable def denseN₀Min (C : ℕ) : ℕ :=
  Nat.find (complement_switch_bound C)

lemma denseN₀Min_spec (C : ℕ) :
    ∀ n ≥ denseN₀Min C, ∀ H : SimpleGraph (Fin n),
    H.edgeFinset.card + C * n ≥ n.choose 2 →
    probUniqueEmb H ≤ (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) :=
  Nat.find_spec (complement_switch_bound C)

lemma denseN₀Min_mono {C₁ C₂ : ℕ} (h : C₁ ≤ C₂) :
    denseN₀Min C₁ ≤ denseN₀Min C₂ := by
  apply Nat.find_mono
  intro n₀ hn₀ n hn H hH
  exact hn₀ n hn H (le_trans hH (by gcongr))

/-- For n above both thresholds (rateF and denseN₀Min(densityCMin k)),
    probUniqueEmb H < 1/(2k). -/
theorem ue_above_min_thresholds (k : ℕ) (hk : 1 ≤ k) :
    ∀ n, n ≥ denseN₀Min (densityCMin k) → n ≥ rateF k →
    ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H < 1 / (2 * (k : ℝ)) := by
  intro n hn_dense hn_rate H
  by_contra habs; push_neg at habs
  have hH_dense := densityCMin_spec k hk n H habs
  have hH_bound := denseN₀Min_spec (densityCMin k) n hn_dense H hH_dense
  exact absurd (lt_of_le_of_lt hH_bound (factorial_exp_at_rateF k hk n hn_rate))
    (not_lt.mpr habs)

/-! ## Refined rate function using Nat.find minimums -/

/-- Rate function using `Nat.find`-based minimums.
    `rateGMin k = max(rateF(max k 2), denseN₀Min(densityCMin k))`.
    This is ≤ rateG k since both components are ≤. -/
noncomputable def rateGMin (k : ℕ) : ℕ :=
  max (rateF (max k 2)) (denseN₀Min (densityCMin k))


lemma rateGMin_ge_rateF (k : ℕ) : rateF k ≤ rateGMin k :=
  le_trans (rateF_le_rateF_max k) (le_max_left _ _)


theorem probUE_lt_at_rateGMin (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ≥ rateGMin k, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H < 1 / (2 * (k : ℝ)) := by
  intro n hn H
  exact ue_above_min_thresholds k hk n
    (le_trans (le_max_right _ _) hn)
    (le_trans (rateGMin_ge_rateF k) hn) H

theorem fH_lt_at_rateGMin (k : ℕ) (hk : 2 ≤ k) :
    ∀ n ≥ rateGMin k, ∀ H : SimpleGraph (Fin n), fH H < 1 / (k : ℝ) := by
  intro n hn H
  have h_pw := pw_convergence_at_rateF k hk n
    (le_trans (rateGMin_ge_rateF k) hn)
  have h_ue := probUE_lt_at_rateGMin k (by linarith) n hn H
  have h_fH := fH_le_probUniqueEmb_plus_error H
  ring_nf at *; linarith

theorem fH_lt_one_at_rateGMin :
    ∀ n ≥ rateGMin 1, ∀ H : SimpleGraph (Fin n), fH H < 1 := by
  intro n hn H
  have h_pw := pw_convergence_at_rateF 2 (by norm_num) n
    (le_trans (le_max_left _ _) hn)
  have h_ue := probUE_lt_at_rateGMin 1 (by norm_num) n hn H
  have h_fH := fH_le_probUniqueEmb_plus_error H
  simp only [Nat.cast_ofNat] at h_pw
  linarith

theorem fH_lt_at_rateGMin_general (k : ℕ) (hk : 0 < k) :
    ∀ n ≥ rateGMin k, ∀ H : SimpleGraph (Fin n), fH H < 1 / (k : ℝ) := by
  rcases k with _ | _ | k
  · omega
  · intro n hn H
    have := fH_lt_one_at_rateGMin n hn H
    simp; linarith
  · exact fH_lt_at_rateGMin (k + 2) (by omega)

/-! ## Growth-bound frontier via rateGMin (strictly smaller) -/

theorem explicit_ge_mul_log_pow (M : ℝ) (k : ℕ) (hM : M > 0) :
    ∀ n : ℕ, n ≥ max (⌈M ^ 2⌉₊ + 1) (⌈Real.exp ((2 * ↑k + 1) ^ 2)⌉₊ + 1) →
    (n : ℝ) ≥ M * (Real.log n) ^ k := by
  intros n hn
  have h_log_n : (Real.log n) ^ k ≤ Real.sqrt n := by
    have h_log_n_ge : Real.log n ≥ (2 * k + 1) ^ 2 := by
      exact Real.le_log_iff_exp_le ( Nat.cast_pos.mpr <| by linarith [ Nat.le_max_left ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ) ] ) |>.2 <| by exact le_trans ( Nat.le_ceil _ ) <| mod_cast by linarith [ Nat.le_max_right ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ) ] ;
    have h_log_u_le_u : 2 * k * Real.log (Real.log n) ≤ Real.log n := by
      have h_log_log_n_le_sqrt : Real.log (Real.log n) ≤ Real.sqrt (Real.log n) := by
        have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt ( Real.log n ) / 2 by exact div_pos ( Real.sqrt_pos.mpr ( lt_of_lt_of_le ( by positivity ) h_log_n_ge ) ) zero_lt_two );
        rw [ Real.log_div ( by exact ne_of_gt <| Real.sqrt_pos.mpr <| lt_of_lt_of_le ( by positivity ) h_log_n_ge ) ( by positivity ), Real.log_sqrt <| by exact le_trans ( by positivity ) h_log_n_ge ] at this ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
      nlinarith [ Real.mul_self_sqrt ( show 0 ≤ Real.log n by nlinarith ), Real.sqrt_nonneg ( Real.log n ), pow_two ( Real.sqrt ( Real.log n ) - ( 2 * k : ℝ ) ) ];
    rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ];
    · rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.ceil_pos.mpr <| show 0 < M ^ 2 by positivity, Nat.ceil_pos.mpr <| show 0 < Real.exp ( ( 2 * k + 1 ) ^ 2 ) by positivity, le_max_left ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ), le_max_right ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ) ] ) ] ; norm_num ; linarith;
    · exact Nat.cast_pos.mpr ( by linarith [ Nat.le_max_left ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ), Nat.le_max_right ( ⌈M ^ 2⌉₊ + 1 ) ( ⌈Real.exp ( ( 2 * k + 1 ) ^ 2 ) ⌉₊ + 1 ) ] );
  nlinarith [ show ( n : ℝ ) ≥ ⌈M ^ 2⌉₊ + 1 by exact_mod_cast le_trans ( le_max_left _ _ ) hn, Real.sqrt_nonneg n, Real.mul_self_sqrt ( Nat.cast_nonneg n ), Nat.le_ceil ( M ^ 2 ), pow_two_nonneg ( M - Real.sqrt n ) ]

/-! ## Graph-level Chernoff bound -/

/-- **Graph-level Chernoff bound**: direct transfer of the raw Chernoff bound
    to SimpleGraph (Fin n) via the graph-Bool bijection.
    For any t ≥ 0: #{G : |edges - N/2| ≥ t} ≤ 2 * 2^N * exp(-2t²/N)
    where N = n.choose 2. -/
theorem graph_chernoff_bound (n : ℕ) (hn : 4 ≤ n) (t : ℝ) (ht : t ≥ 0) :
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ t)).card : ℝ) ≤
    2 * (2 ^ n.choose 2 : ℝ) * Real.exp (-2 * t ^ 2 / ↑(n.choose 2)) := by
  have h_chernoff : ∀ (f : EdgeSlot n → Bool), (Finset.univ.filter (fun f : EdgeSlot n → Bool => |((Finset.univ.filter (fun e => f e = true)).card : ℝ) - (n.choose 2) / 2| ≥ t)).card ≤ 2 * 2 ^ (n.choose 2) * Real.exp (-2 * t ^ 2 / (n.choose 2)) := by
    intros f
    have := chernoff_bound (n.choose 2) t ht
    norm_num at *;
    have h_equiv : Nonempty (EdgeSlot n ≃ Fin (n.choose 2)) := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ card_edgeSlot ] ⟩;
    obtain ⟨ e ⟩ := h_equiv;
    convert this using 1;
    rw [ Finset.card_filter, Finset.card_filter ];
    refine' congr_arg _ ( Finset.sum_bij ( fun x _ => x ∘ e.symm ) _ _ _ _ ) <;> simp +decide;
    · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( e x ) ;
    · exact fun b => ⟨ b ∘ e, by ext; simp +decide ⟩;
    · intro a; rw [ show ( Finset.univ.filter fun e => a e = true ) = Finset.image ( fun i => e.symm i ) ( Finset.univ.filter fun i => a ( e.symm i ) = true ) from ?_, Finset.card_image_of_injective _ e.symm.injective ] ;
      ext; simp +decide [ e.symm_apply_eq ] ;
  refine' le_trans _ ( h_chernoff 0 );
  have h_bij : Finset.card (Finset.univ.filter (fun G : SimpleGraph (Fin n) => |((G.edgeFinset.card : ℝ) - (n.choose 2) / 2)| ≥ t)) = Finset.card (Finset.image graphEncode (Finset.univ.filter (fun G : SimpleGraph (Fin n) => |((G.edgeFinset.card : ℝ) - (n.choose 2) / 2)| ≥ t))) := by
    rw [ Finset.card_image_of_injective _ ( show Function.Injective graphEncode from _ ) ];
    exact ( Equiv.injective ( graphEquiv n ) );
  refine' mod_cast h_bij.le.trans ( Finset.card_le_card _ );
  intro f hf; obtain ⟨ G, hG, rfl ⟩ := Finset.mem_image.mp hf; exact (by
  convert hG using 1;
  simp +decide [ graphEncode ];
  rw [ show G.edgeFinset = Finset.image ( fun e : EdgeSlot n => Sym2.mk ( e.val.1, e.val.2 ) ) ( Finset.filter ( fun e : EdgeSlot n => G.Adj e.val.1 e.val.2 ) Finset.univ ) from ?_, Finset.card_image_of_injective ];
  · convert Iff.rfl;
    rename_i e; rcases e with ⟨ ⟨ i, j ⟩, hij ⟩ ; simp +decide [ hij ] ;
  · intro e₁ e₂ h; rcases e₁ with ⟨ ⟨ u₁, v₁ ⟩, h₁ ⟩ ; rcases e₂ with ⟨ ⟨ u₂, v₂ ⟩, h₂ ⟩ ; simp_all +decide [ Sym2.eq_iff ] ;
    grind;
  · ext ⟨ u, v ⟩ ; simp +decide [ SimpleGraph.adj_comm ] ;
    constructor <;> intro huv;
    · cases lt_or_gt_of_ne huv.ne <;> [ exact ⟨ ⟨ ⟨ u, v ⟩, by aesop ⟩, huv, Or.inl rfl ⟩ ; exact ⟨ ⟨ ⟨ v, u ⟩, by aesop ⟩, huv.symm, Or.inr rfl ⟩ ];
    · rcases huv with ⟨ a, ha, ha' | ha' ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ]);

/-! ## Explicit Chernoff L parameter -/

/-- The explicit Chernoff parameter for edge tail concentration.
    L = max(1, ⌈sqrt(log(16k))⌉₊) ensures that the Chernoff bound gives
    #{G : |edges - N/2| ≥ L*n} ≤ (1/(8k)) * 2^N for n ≥ 4. -/
def chernoffL (k : ℕ) : ℕ :=
  max 1 (⌈Real.sqrt (Real.log (16 * ↑k))⌉₊)

lemma chernoffL_pos (k : ℕ) : 0 < chernoffL k := by
  simp [chernoffL]

/-- For k ≥ 1, chernoffL(k)² ≥ log(16k). -/
lemma chernoffL_sq_ge_log (k : ℕ) (hk : 1 ≤ k) :
    (chernoffL k : ℝ) ^ 2 ≥ Real.log (16 * ↑k) := by
  have h_sqrt : (chernoffL k : ℝ) ≥ Real.sqrt (Real.log (16 * k)) := by
    unfold chernoffL;
    exact le_trans ( Nat.le_ceil _ ) ( mod_cast le_max_right _ _ );
  exact le_trans ( by rw [ Real.sq_sqrt ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ) ( pow_le_pow_left₀ ( Real.sqrt_nonneg _ ) h_sqrt 2 )

/-- **Analysis bound**: for n ≥ 4 and k ≥ 1,
    2 * exp(-2 * (chernoffL(k) * n)² / (n choose 2)) ≤ 1/(8k). -/
lemma chernoff_exp_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4 ≤ n) :
    2 * Real.exp (-2 * (↑(chernoffL k) * ↑n) ^ 2 / ↑(n.choose 2)) ≤
    1 / (8 * ↑k) := by
  have h_exp : -2 * (chernoffL k * n : ℝ) ^ 2 / (Nat.choose n 2) ≤ -Real.log (16 * k) := by
    have h_simplified : 4 * (chernoffL k : ℝ) ^ 2 * n / (n - 1) ≥ Real.log (16 * k) := by
      field_simp;
      rw [ le_div_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast, show ( chernoffL k : ℝ ) ^ 2 ≥ Real.log ( 16 * k ) by exact_mod_cast chernoffL_sq_ge_log k hk, Real.log_nonneg ( show ( 16 * k : ℝ ) ≥ 1 by norm_cast; linarith ) ];
    convert neg_le_neg h_simplified using 1;
    rw [ Nat.choose_two_right ];
    rw [ Nat.cast_div ] <;> norm_num;
    · rw [ Nat.cast_sub ( by linarith ) ] ; ring;
      grind;
    · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ );
  exact le_trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr h_exp ) zero_le_two ) ( by rw [ Real.exp_neg, Real.exp_log ( by positivity ) ] ; ring_nf; nlinarith [ inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ) ] )

/-- **Explicit Chernoff edge tail for chernoffL**.
    Combines graph_chernoff_bound with chernoff_exp_bound. -/
theorem chernoff_edge_tail_at_chernoffL (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, 4 ≤ n →
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      |(G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ) / 2| ≥ (chernoffL k : ℝ) * n)).card : ℝ) ≤
    1 / (8 * (k : ℝ)) * 2 ^ (n.choose 2) := by
  intro n hn;
  refine le_trans ( ?_ ) ( mul_le_mul_of_nonneg_right ( chernoff_exp_bound k hk n hn ) ( by positivity ) );
  convert graph_chernoff_bound n hn ( chernoffL k * n ) ( by positivity ) using 1 ; ring

/-! ## Explicit density constant from Chernoff -/

/-- The explicit density constant: C₀ from the process bound analysis.
    C₀ = ⌈128 * k * log(40 * k * chernoffL(k))⌉₊ + 1.

    This is the density constant from `reduction_to_dense_large_n` with
    explicit Chernoff parameters. -/
def densityC₀ (k : ℕ) : ℕ :=
  ⌈128 * (k : ℝ) * Real.log (40 * k * chernoffL k)⌉₊ + 1

/-! ## Step 2: Explicit ue_implies_many_edges -/

/-
For n ≥ 5, (n+1)² ≤ n · 2^(n-1). This is the induction step for
    `mul_factorial_le_two_pow_choose`.
-/
lemma sq_succ_le_mul_two_pow (n : ℕ) (hn : 5 ≤ n) :
    (n + 1) ^ 2 ≤ n * 2 ^ (n - 1) := by
      rcases n with ( _ | _ | _ | _ | _ | n ) <;> norm_num [ Nat.pow_succ' ] at *;
      exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith

/-
For n ≥ 20, n · n! ≤ 2^((n-1).choose 2).
    Proof by strong induction:
    - Base: n=20 by computation.
    - Step: (n+1)·(n+1)! = (n+1)²·n! ≤ n·2^(n-1)·n! (by sq_succ_le_mul_two_pow)
                         ≤ 2^(n-1) · 2^((n-1).choose 2) (by IH: n·n! ≤ 2^((n-1).choose 2))
                         = 2^(n.choose 2)    (since (n-1).choose 2 + (n-1) = n.choose 2).
-/
lemma mul_factorial_le_two_pow_choose (n : ℕ) (hn : 20 ≤ n) :
    n * n.factorial ≤ 2 ^ (n - 1).choose 2 := by
      induction' n using Nat.case_strong_induction_on with n ih;
      · contradiction;
      · by_cases hn : n ≥ 20;
        · have h_step : (n + 1) ^ 2 ≤ n * 2 ^ (n - 1) := by
            exact sq_succ_le_mul_two_pow n ( by linarith );
          have h_step : (n + 1) * (n + 1).factorial ≤ 2 ^ (n - 1) * (n * n.factorial) := by
            convert Nat.mul_le_mul_right ( n.factorial ) h_step using 1 <;> push_cast [ Nat.factorial_succ ] <;> ring;
          have h_step : (n + 1) * (n + 1).factorial ≤ 2 ^ (n - 1) * 2 ^ Nat.choose (n - 1) 2 := by
            exact h_step.trans ( Nat.mul_le_mul_left _ ( ih n le_rfl hn ) );
          convert h_step using 1 ; cases n <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ' ] ; ring;
        · interval_cases n <;> trivial

/-
For n ≥ 20, Nat.clog 2 (n · n!) ≤ n.choose 2 - (n - 1).
    Follows from `mul_factorial_le_two_pow_choose` via `Nat.clog_le_of_le_pow`,
    noting that (n-1).choose 2 = n.choose 2 - (n-1).
-/
lemma clog_mul_factorial_le (n : ℕ) (hn : 20 ≤ n) :
    Nat.clog 2 (n * n.factorial) ≤ n.choose 2 - (n - 1) := by
      have h_log_factorial : n * Nat.factorial n ≤ 2 ^ ((n - 1).choose 2) := by
        exact?;
      refine' le_trans _ ( show n.choose 2 - ( n - 1 ) ≥ ( n - 1 ).choose 2 from _ );
      · exact?;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
        grind

/-- Explicit threshold for `ue_implies_many_edges` at δ = 1/(2k).
    For n ≥ ueEdgeThresh(k), if probUE ≥ 1/(2k), then edges ≥ n. -/
def ueEdgeThresh (k : ℕ) : ℕ := max 20 (2 * k)

/-
**Explicit version of ue_implies_many_edges for δ = 1/(2k).**
    For k ≥ 1 and n ≥ max(20, 2k), if probUniqueEmb H ≥ 1/(2k), then H has ≥ n edges.

    Proof: By contradiction. If edges < n, then non-edges ≥ n.choose 2 - (n-1).
    Since n ≥ 20, by `clog_mul_factorial_le`, Nat.clog 2 (n·n!) ≤ n.choose 2 - (n-1).
    Since n ≥ 2k, Nat.clog 2 (2k·n!) ≤ Nat.clog 2 (n·n!) (monotonicity).
    For k ≥ 2: by `probUniqueEmb_lt_inv_2k_of_clog_k_nonedges`, probUE < 1/(2k). Contradiction.
    For k = 1: by `probUniqueEmb_le_inv_of_clog_nonedges`, probUE ≤ 1/n ≤ 1/20 < 1/2.
-/
theorem ue_implies_many_edges_explicit (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ≥ ueEdgeThresh k, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ 1 / (2 * (k : ℝ)) → n ≤ H.edgeFinset.card := by
      intro n hn H hH;
      contrapose! hH;
      by_cases hk2 : 2 ≤ k;
      · apply probUniqueEmb_lt_inv_2k_of_clog_k_nonedges hk2 (by
        unfold ueEdgeThresh at hn; linarith [ Nat.le_max_left 20 ( 2 * k ), Nat.le_max_right 20 ( 2 * k ) ] ;) H (by
        -- Since $n \geq 2k$, we have $2k \leq n$, thus $2k \cdot n! \leq n \cdot n!$.
        have h_factorial : 2 * k * n.factorial ≤ n * n.factorial := by
          exact Nat.mul_le_mul_right _ ( by linarith [ show n ≥ 2 * k from hn.trans' ( by unfold ueEdgeThresh; aesop ) ] );
        have h_log : Nat.clog 2 (n * n.factorial) ≤ n.choose 2 - (n - 1) := by
          apply clog_mul_factorial_le;
          exact le_trans ( by norm_num [ ueEdgeThresh ] ) hn;
        exact le_trans ( Nat.clog_mono_right _ h_factorial ) ( h_log.trans ( Nat.sub_le_sub_left ( Nat.le_sub_one_of_lt hH ) _ ) ));
      · interval_cases k;
        have h_prob : probUniqueEmb H ≤ 1 / (n : ℝ) := by
          apply probUniqueEmb_le_inv_of_clog_nonedges;
          · grind;
          · have h_nonedges : Nat.clog 2 (n * n.factorial) ≤ n.choose 2 - (n - 1) := by
              exact?;
            exact le_trans h_nonedges ( Nat.sub_le_sub_left ( Nat.le_sub_one_of_lt hH ) _ );
        exact h_prob.trans_lt ( by rw [ div_lt_div_iff₀ ] <;> norm_cast <;> linarith [ show n ≥ 20 by exact le_trans ( by decide ) hn ] )

/-! ## Step 3-6: Explicit density constant and densityCMin bound -/

/-- Explicit process bound threshold at δ = 1/(2k).
    n₀ = max(ueEdgeThresh(k), 4*chernoffL(k) + ⌈128k⌉ + 1). -/
def processN₀ (k : ℕ) : ℕ :=
  max (ueEdgeThresh k) (4 * chernoffL k + 128 * k + 1)

/-- Explicit upper bound on densityCMin.
    C = max(densityC₀(k), processN₀(k)/2 + 1). -/
def densityCBound (k : ℕ) : ℕ :=
  max (densityC₀ k) (processN₀ k / 2 + 1)

lemma processN₀_ge_4 (k : ℕ) (hk : 1 ≤ k) : 4 ≤ processN₀ k := by
  unfold processN₀ ueEdgeThresh chernoffL; omega

lemma processN₀_ge_ueEdgeThresh (k : ℕ) : ueEdgeThresh k ≤ processN₀ k :=
  le_max_left _ _

lemma processN₀_ge_4L (k : ℕ) : 4 * chernoffL k ≤ processN₀ k := by
  unfold processN₀; omega

lemma processN₀_ge_128k (k : ℕ) : 128 * k ≤ processN₀ k := by
  unfold processN₀; omega

/-
For n ≥ processN₀(k) and k ≥ 1, ⌊δn/32⌋ ≥ 1 where δ = 1/(2k).
-/
lemma floor_div_ge_one (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : processN₀ k ≤ n) :
    1 ≤ ⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ := by
      refine Nat.floor_pos.mpr ?_;
      rw [ div_mul_eq_mul_div, div_div, le_div_iff₀ ] <;> norm_cast <;> try linarith;
      linarith [ processN₀_ge_128k k ]

/-
**Explicit process bound at δ = 1/(2k).**
    For n ≥ processN₀(k), probUE ≥ 1/(2k) implies (eH/N)^k ≥ α
    where k = ⌊n/(64k)⌋ and α = (1/(40k·chernoffL(k)))^2.
-/
theorem process_bound_at_half_k (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ≥ processN₀ k, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ 1 / (2 * (k : ℝ)) →
    0 < n.choose 2 ∧
    ((H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ^ ⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ ≥
      (1 / (40 * k * chernoffL k)) ^ 2 := by
        intro n hn H hH;
        refine' ⟨ Nat.choose_pos ( show 2 ≤ n by linarith [ processN₀_ge_4 k hk ] ), _ ⟩;
        have h_exp : (↑H.edgeFinset.card / ↑(n.choose 2)) ^ (⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ - 1) ≥ (1 / (2 * (k : ℝ))) / (20 * chernoffL k) := by
          have h_step4 : 3 * (1 / (2 * (k : ℝ))) * n / 16 ≤ (⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ : ℝ) + (2 * chernoffL k * n + 1) * ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ - 1) := by
            have h_restricted_sum : ∃ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) ∧ S.card ≤ 2 * chernoffL k * n + 1 ∧ (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≥ 3 * (1 / (2 * k : ℝ)) * n / 16 := by
              apply restricted_sum_lower_bound;
              · exact le_trans ( processN₀_ge_4 k hk ) hn;
              · positivity;
              · exact hH;
              · exact?;
              · convert chernoff_edge_tail_at_chernoffL k hk n ( by linarith [ processN₀_ge_4 k ( by linarith ) ] ) using 1 ; ring;
            have h_process_inequality : ∀ S : Finset ℕ, (∀ m ∈ S, m ≤ n.choose 2) → (∑ m ∈ S, (numUEWithEdges H m : ℝ) / ((n.choose 2).choose m : ℝ)) ≤ ⌊(1 / (2 * k : ℝ)) * n / 32⌋₊ + S.card * ((H.edgeFinset.card : ℝ) / (n.choose 2)) ^ (⌊(1 / (2 * k : ℝ)) * n / 32⌋₊ - 1) := by
              intros S hS
              apply process_inequality;
              · linarith [ show n ≥ 4 by linarith [ processN₀_ge_4 k hk ] ];
              · exact floor_div_ge_one k hk n hn;
              · have := ue_implies_many_edges_explicit k hk n ( by
                  exact le_trans ( processN₀_ge_ueEdgeThresh k ) hn ) H hH;
                refine' le_trans _ this;
                exact Nat.floor_le_of_le ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( n : ℝ ) ≥ 0 by positivity, div_mul_cancel₀ ( 1 : ℝ ) ( by positivity : ( 2 * k : ℝ ) ≠ 0 ) ] );
              · assumption;
            obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_restricted_sum;
            refine le_trans hS₃ <| le_trans ( h_process_inequality S hS₁ ) ?_;
            gcongr ; norm_cast;
          have h_step5 : (⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ : ℝ) ≤ (1 / (2 * (k : ℝ))) * n / 32 := by
            exact Nat.floor_le ( by positivity );
          have h_step6 : (2 * chernoffL k * n + 1 : ℝ) ≤ 5 / 2 * chernoffL k * n := by
            have h_step6 : (n : ℝ) ≥ 4 * chernoffL k := by
              exact_mod_cast hn.trans' ( processN₀_ge_4L k );
            nlinarith [ show ( chernoffL k : ℝ ) ≥ 1 by exact_mod_cast chernoffL_pos k ];
          field_simp at *;
          rw [ div_le_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( chernoffL k : ℝ ) ≥ 1 by exact_mod_cast chernoffL_pos k ];
        have h_exp : (↑H.edgeFinset.card / ↑(n.choose 2)) ^ (2 * (⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ - 1)) ≥ (1 / (40 * (k : ℝ) * chernoffL k)) ^ 2 := by
          rw [ pow_mul' ] ; exact le_trans ( by ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) h_exp 2 ) ;
        refine le_trans h_exp ?_;
        refine' pow_le_pow_of_le_one _ _ _ <;> norm_num;
        · positivity;
        · refine' div_le_one_of_le₀ _ _;
          · convert H.card_edgeFinset_le_card_choose_two using 1;
            norm_cast;
            rw [ Fintype.card_fin ];
          · positivity;
        · rcases x : ⌊ ( k : ℝ ) ⁻¹ * ( 1 / 2 ) * n / 32⌋₊ with ( _ | _ | m ) <;> simp_all +decide;
          rw [ Nat.floor_eq_iff ] at x <;> norm_num at * <;> try positivity;
          unfold processN₀ at hn ; norm_num at hn;
          nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ), show ( chernoffL k : ℝ ) ≥ 1 by exact_mod_cast chernoffL_pos k, show ( n : ℝ ) ≥ 4 * chernoffL k + 128 * k + 1 by exact_mod_cast hn.2 ]

/-
**Explicit reduction_to_dense_large_n at δ = 1/(2k).**
    For n ≥ processN₀(k), probUE ≥ 1/(2k) implies the graph is dense
    with density constant densityC₀(k).
-/
theorem reduction_to_dense_at_half_k (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ≥ processN₀ k, ∀ H : SimpleGraph (Fin n),
    probUniqueEmb H ≥ 1 / (2 * (k : ℝ)) →
    H.edgeFinset.card + densityC₀ k * n ≥ n.choose 2 := by
      intros n hn H h_prob
      have h_bound : (n.choose 2 - H.edgeFinset.card : ℝ) ≤ 128 * k * n * Real.log (40 * k * chernoffL k) := by
        have h_bound : (1 - (H.edgeFinset.card : ℝ) / (n.choose 2 : ℝ)) ≤ -Real.log ((1 / (40 * k * chernoffL k)) ^ 2) / ⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ := by
          apply pow_ge_implies_close_to_one;
          any_goals positivity;
          · refine' div_le_one_of_le₀ _ _;
            · have := H.card_edgeFinset_le_card_choose_two;
              aesop;
            · positivity;
          · exact sq_pos_of_pos ( one_div_pos.mpr ( mul_pos ( mul_pos ( by positivity ) ( by positivity ) ) ( Nat.cast_pos.mpr ( chernoffL_pos k ) ) ) );
          · exact pow_le_one₀ ( by positivity ) ( div_le_one_of_le₀ ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( chernoffL k : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( chernoffL_pos k ) ] ) ( by positivity ) );
          · exact floor_div_ge_one k hk n hn;
          · apply (process_bound_at_half_k k hk n hn H h_prob).right;
        have h_bound : (n.choose 2 - H.edgeFinset.card : ℝ) ≤ (n.choose 2 : ℝ) * (-Real.log ((1 / (40 * k * chernoffL k)) ^ 2)) / ⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ := by
          rw [ sub_div', div_le_iff₀ ] at * <;> ring_nf at * <;> norm_num at *;
          · convert h_bound using 1;
          · exact Nat.choose_pos ( by linarith [ show n ≥ 2 by linarith [ show processN₀ k ≥ 2 by exact le_trans ( by norm_num [ processN₀, ueEdgeThresh ] ) ( Nat.le_max_left _ _ ) ] ] );
          · exact ne_of_gt <| Nat.choose_pos <| by linarith [ show n ≥ 2 by linarith [ show n ≥ 2 by exact le_trans ( by norm_num [ processN₀, ueEdgeThresh ] ) hn ] ] ;
        have h_bound : (n.choose 2 : ℝ) / ⌊(1 / (2 * (k : ℝ))) * n / 32⌋₊ ≤ 32 * n / (1 / (2 * (k : ℝ))) := by
          rw [ div_le_div_iff₀ ] <;> norm_num;
          · have := Nat.lt_floor_add_one ( ( k : ℝ ) ⁻¹ * ( 1 / 2 ) * n / 32 );
            rw [ Nat.choose_two_right ];
            rcases n with ( _ | _ | n ) <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
            field_simp at *;
            norm_cast at *;
            nlinarith [ show ⌊ ( n + 1 + 1 : ℝ ) / ( 2 * k * 32 ) ⌋₊ ≥ 1 from Nat.floor_pos.mpr ( by rw [ le_div_iff₀ ] <;> norm_cast <;> nlinarith [ show processN₀ k ≥ 4 * chernoffL k + 128 * k + 1 from by exact le_trans ( by norm_num ) ( Nat.le_max_right _ _ ) ] ) ];
          · refine' Nat.floor_pos.mpr _;
            field_simp;
            norm_cast;
            unfold processN₀ at hn; norm_num at hn; linarith;
          · linarith;
        refine le_trans ‹_› ?_;
        convert mul_le_mul_of_nonneg_right h_bound ( show ( 0 :ℝ ) ≤ -Real.log ( ( 1 / ( 40 * k * chernoffL k ) ) ^ 2 ) by exact neg_nonneg_of_nonpos <| Real.log_nonpos ( by positivity ) <| by exact pow_le_one₀ ( by positivity ) <| div_le_one_of_le₀ ( by nlinarith [ show ( k :ℝ ) ≥ 1 by norm_cast, show ( chernoffL k :ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| chernoffL_pos k ] ) <| by positivity ) using 1 <;> ring;
        norm_num [ Real.log_mul, show k ≠ 0 by linarith, show chernoffL k ≠ 0 by exact ne_of_gt <| chernoffL_pos k ] ; ring;
        rw [ show ( 1 : ℝ ) / 1600 = ( 40 ^ 2 ) ⁻¹ by norm_num, Real.log_inv, Real.log_pow ] ; ring;
      unfold densityC₀;
      exact_mod_cast ( by nlinarith [ Nat.le_ceil ( 128 * ( k : ℝ ) * Real.log ( 40 * k * chernoffL k ) ) ] : ( H.edgeFinset.card : ℝ ) + ( ⌈128 * ( k : ℝ ) * Real.log ( 40 * k * chernoffL k ) ⌉₊ + 1 ) * n ≥ n.choose 2 )

/-
densityCBound(k) satisfies the density predicate.
-/
theorem densityPred_of_bound (k : ℕ) (hk : 1 ≤ k) :
    densityPred k (densityCBound k) := by
      intro n H hH
      by_cases h_n_ge_processN₀ : n ≥ processN₀ k;
      · exact le_trans ( reduction_to_dense_at_half_k k hk n h_n_ge_processN₀ H hH ) ( by gcongr ; exact le_max_left _ _ );
      · refine' le_trans _ ( Nat.le_add_left _ _ );
        refine' small_n_vacuity _ _ _ |> le_trans <| mul_le_mul_of_nonneg_right _ <| Nat.zero_le _;
        rotate_left;
        exacts [ processN₀ k / 2 + 1, le_max_right _ _, by omega ]

/-- **Explicit upper bound on densityCMin.**
    densityCMin(k) ≤ densityCBound(k) for k ≥ 1. -/
theorem densityCMin_le_bound (k : ℕ) (hk : 1 ≤ k) :
    densityCMin k ≤ densityCBound k := by
  unfold densityCMin; rw [dif_pos hk]
  exact Nat.find_min' _ (densityPred_of_bound k hk)


/-! ==================================================================
    Explicit Dense N₀
    (originally ExplicitDenseN0.lean)
    ================================================================== -/


/-! ## Explicit threshold definitions -/

/-- The explicit threshold for `n ≥ M * (log n)^k` from `explicit_ge_mul_log_pow`.
    Wrapper that avoids definitional unfolding issues. -/
def explicitMLogPowThresh (M : ℝ) (k : ℕ) : ℕ :=
  max (⌈M ^ 2⌉₊ + 1) (⌈Real.exp ((2 * ↑k + 1) ^ 2)⌉₊ + 1)

lemma ge_of_ge_explicitMLogPowThresh (M : ℝ) (k : ℕ) (hM : M > 0) :
    ∀ n : ℕ, n ≥ explicitMLogPowThresh M k →
    (n : ℝ) ≥ M * (Real.log n) ^ k := by
  intro n hn
  exact explicit_ge_mul_log_pow M k hM n hn

/-- The explicit threshold for `n ≥ 2 * (log n)^{6^{4C+1}}`.
    Equals `explicitMLogPowThresh 2 (6^(4C+1))`. -/
def pruningExpThresh (C : ℕ) : ℕ :=
  explicitMLogPowThresh 2 (6 ^ (4 * C + 1))

lemma ge_two_mul_log_pow_of_ge_pruningExpThresh (C : ℕ) :
    ∀ n : ℕ, n ≥ pruningExpThresh C →
    (n : ℝ) ≥ 2 * (Real.log n) ^ (6 ^ (4 * C + 1)) := by
  exact ge_of_ge_explicitMLogPowThresh 2 (6 ^ (4 * C + 1)) (by norm_num)

/-
Explicit version of `pruningThresh_ge_two`.
    For n ≥ pruningExpThresh(C) + 3 and C ≥ 1, all pruning thresholds
    at levels ≤ 4C are ≥ 2.
-/
lemma pruningThresh_ge_two_explicit (C : ℕ) (hC : C ≥ 1) :
    ∀ n : ℕ, n ≥ pruningExpThresh C + 3 →
    ∀ i : ℕ, i ≤ 4 * C → pruningThresh n i ≥ 2 := by
  intros n hn i hi
  have h_n_ge_2 : (n : ℝ) ≥ 2 * (Real.log n) ^ (6 ^ (4 * C + 1)) := by
    exact ge_two_mul_log_pow_of_ge_pruningExpThresh C n ( by linarith );
  -- Since $i \leq 4C$, we have $6^{i+1} \leq 6^{4C+1}$.
  have h_exp_le : (6 : ℕ) ^ (i + 1) ≤ (6 : ℕ) ^ (4 * C + 1) := by
    exact pow_le_pow_right₀ ( by norm_num ) ( by linarith );
  refine Nat.le_floor ?_;
  rw [ le_div_iff₀ ( pow_pos ( Real.log_pos <| by norm_cast; linarith ) _ ) ];
  refine le_trans ?_ h_n_ge_2;
  gcongr;
  · norm_num;
  · exact Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ;

/-
For n ≥ pruningExpThresh(C) + 3 and C ≥ 1,
    the level-0 pruning threshold ≤ B'_card for any B' with
    |B'| ≥ n/(8C+2).
-/
lemma pruningThresh_zero_le_B'_card_explicit (C : ℕ) (hC : C ≥ 1) :
    ∀ n : ℕ, n ≥ pruningExpThresh C + 3 →
    ∀ B'_card : ℕ, B'_card ≥ n / (8 * C + 2) →
    pruningThresh n 0 ≤ B'_card := by
  unfold pruningThresh;
  intros n hn B'_card hB'_card
  have h_log : (Real.log n) ≥ 8 * C + 2 := by
    have h_log : Real.log n ≥ (2 * 6 ^ (4 * C + 1) + 1) ^ 2 := by
      refine' le_trans _ ( Real.log_le_log _ <| Nat.cast_le.mpr hn );
      · unfold pruningExpThresh at *;
        unfold explicitMLogPowThresh at * ; norm_num at *;
        rw [ Real.le_log_iff_exp_le ] <;> norm_cast <;> norm_num;
        exact le_add_of_le_of_nonneg ( le_max_of_le_right ( by linarith [ Nat.le_ceil ( Real.exp ( ( 2 * 6 ^ ( 4 * C + 1 ) + 1 ) ^ 2 ) ) ] ) ) zero_le_three;
      · positivity;
    refine le_trans ?_ h_log ; norm_cast ; ring;
    nlinarith only [ hC, show 6 ^ ( C * 4 ) ≥ C + 1 by exact Nat.recOn C ( by norm_num ) fun n ihn => by rw [ Nat.succ_mul, pow_add ] ; nlinarith only [ ihn, pow_pos ( show 0 < 6 by norm_num ) ( n * 4 ) ], show 6 ^ ( C * 8 ) ≥ 1 by exact Nat.one_le_pow _ _ ( by norm_num ) ];
  refine' le_trans ( Nat.floor_mono _ ) _;
  exact ( n : ℝ ) / ( 8 * C + 2 );
  · gcongr;
    exact le_trans h_log ( le_self_pow₀ ( by linarith ) ( by norm_num ) );
  · exact Nat.le_trans ( Nat.le_of_lt_succ <| by rw [ Nat.floor_lt' <| by positivity ] ; rw [ div_lt_iff₀ <| by positivity ] ; norm_cast ; linarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by positivity : 0 < ( 8 * C + 2 ) ) ] ) hB'_card

/-
For n ≥ pruningExpThresh(C) + 3 and C ≥ 1, the ratio bound
    (a-1)²/τᵢ ≥ 2^{16C+4} · C · n · log n holds at every level.
-/
set_option maxHeartbeats 1600000 in
lemma pruning_ratio_bound_explicit (C : ℕ) (hC : C ≥ 1) :
    ∀ n : ℕ, n ≥ pruningExpThresh C + 3 →
    ∀ i : ℕ, i ≤ 4 * C →
    ∀ a : ℕ, a ≥ (if i = 0 then n / (8 * C + 2) else pruningThresh n (i - 1)) →
    ((a : ℝ) - 1) ^ 2 / ((pruningThresh n i : ℝ)) ≥
      2 ^ (16 * C + 4) * (C : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  intro n hn i hi a ha
  by_cases hi_zero : i = 0;
  · -- For i = 0, a ≥ n/(8C+2), so a-1 ≥ n/(2*(8C+2)), and the bound follows from (log n)^5 being large.
    have h_log_bound : (Real.log n) ^ 5 ≥ 4 * (8 * C + 2) ^ 2 * 2 ^ (16 * C + 4) * C := by
      -- Since $n \geq \exp((2 \cdot 6^{4C+1} + 1)^2)$, we have $\log n \geq (2 \cdot 6^{4C+1} + 1)^2$.
      have h_log_n_ge : Real.log n ≥ (2 * 6 ^ (4 * C + 1) + 1) ^ 2 := by
        have h_log_n_ge : n ≥ Nat.ceil (Real.exp ((2 * 6 ^ (4 * C + 1) + 1) ^ 2)) + 1 := by
          refine le_trans ?_ hn;
          refine' le_trans _ ( Nat.le_add_right _ _ );
          refine' le_max_right _ _ |> le_trans _ ; norm_num [ Real.exp_pos ];
        exact Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 ( by exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith ) );
      refine le_trans ?_ ( pow_le_pow_left₀ ( by positivity ) h_log_n_ge 5 );
      refine' le_trans _ ( pow_le_pow_left₀ ( by positivity ) ( pow_le_pow_left₀ ( by positivity ) ( show ( 2 * 6 ^ ( 4 * C + 1 ) + 1 : ℝ ) ≥ 6 ^ ( 4 * C + 1 ) by linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 6 ) ( 4 * C + 1 ) ] ) 2 ) 5 ) ; ring_nf;
      norm_num [ pow_mul' ];
      refine' Nat.recOn C _ _ <;> norm_num [ pow_succ' ] at *;
      intro n hn; nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 65536 ) n, pow_le_pow_left₀ ( by norm_num ) ( by norm_num : ( 13367494538843734067838845976576 : ℝ ) ≥ 65536 ) n ] ;
    -- Since $a \geq n / (8 * C + 2)$, we have $a - 1 \geq n / (2 * (8 * C + 2))$.
    have h_a_minus_one : (a - 1 : ℝ) ≥ n / (2 * (8 * C + 2)) := by
      rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast;
      · rw [ Int.subNatNat_eq_coe ] ; norm_num [ hi_zero ] at *;
        have h_a_minus_one : n ≥ 4 * (8 * C + 2) := by
          have h_a_minus_one : n ≥ ⌈Real.exp ((2 * 6 ^ (4 * C + 1) + 1) ^ 2)⌉₊ + 3 := by
            refine le_trans ?_ hn;
            unfold pruningExpThresh;
            unfold explicitMLogPowThresh; norm_num;
          refine le_trans ?_ h_a_minus_one;
          refine' le_trans _ ( Nat.le_add_right _ _ );
          refine' Nat.le_of_lt_succ _;
          refine' Nat.lt_succ_of_le ( Nat.le_trans _ <| Nat.ceil_mono <| Real.add_one_le_exp _ );
          exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith only [ show ( 6 : ℝ ) ^ ( 4 * C + 1 ) ≥ 4 * C + 1 by exact mod_cast Nat.recOn ( 4 * C + 1 ) ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith only [ ihn, pow_pos ( by norm_num : ( 0 : ℕ ) < 6 ) n ], Nat.le_ceil ( ( 2 * 6 ^ ( 4 * C + 1 ) + 1 ) ^ 2 + 1 : ℝ ) ] ;
        nlinarith [ Nat.div_add_mod n ( 8 * C + 2 ), Nat.mod_lt n ( by linarith : 0 < 8 * C + 2 ) ];
      · positivity;
    -- Substitute the bounds into the inequality.
    have h_subst : ((a - 1 : ℝ) ^ 2) / (n / (Real.log n) ^ 6) ≥ (n ^ 2 / (4 * (8 * C + 2) ^ 2)) / (n / (Real.log n) ^ 6) := by
      gcongr;
      exact le_trans ( by rw [ div_pow ] ; ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) h_a_minus_one 2 );
    refine le_trans ?_ ( h_subst.trans ?_ );
    · field_simp;
      nlinarith [ show 0 ≤ ( n : ℝ ) * Real.log n by positivity ];
    · gcongr;
      · refine Nat.cast_pos.mpr <| Nat.floor_pos.mpr ?_;
        rw [ one_le_div ] <;> norm_cast;
        · have := ge_of_ge_explicitMLogPowThresh 1 6 ( by norm_num ) n ( by linarith [ show pruningExpThresh C ≥ explicitMLogPowThresh 1 6 from by
                                                                                        refine' max_le_max _ _ <;> norm_num [ explicitMLogPowThresh ];
                                                                                        exact le_trans ( Real.exp_le_exp.mpr ( by nlinarith only [ show ( 6 : ℝ ) ^ ( 4 * C + 1 ) ≥ 6 by exact le_self_pow₀ ( by norm_num ) ( by linarith ) ] ) ) ( Nat.le_ceil _ ) ] ) ; aesop;
        · exact pow_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ show pruningExpThresh C ≥ 1 from Nat.succ_le_of_lt <| Nat.lt_of_lt_of_le ( by norm_num ) <| Nat.le_max_left _ _ ] ) _;
      · rw [ le_div_iff₀ ] <;> norm_cast <;> norm_num [ hi_zero ];
        · refine le_trans ( mul_le_mul_of_nonneg_right ( Nat.floor_le <| by positivity ) <| by positivity ) ?_;
          norm_num +zetaDelta at *;
          rw [ div_mul_cancel₀ _ ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ show n ≥ 2 by linarith [ show pruningExpThresh C ≥ 1 by exact le_max_of_le_left <| Nat.succ_pos _ ] ] ) ];
        · exact pow_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.zero_le ( pruningExpThresh C ) ] ) _;
  · -- Since $i \neq 0$, we have $a \geq \text{pruningThresh } n (i - 1)$.
    have ha_ge_pruningThresh : (a : ℝ) ≥ (n : ℝ) / (Real.log n) ^ (6 ^ i) - 1 := by
      rcases i <;> simp_all +decide [ pruningThresh ];
      exact le_of_lt ( Nat.lt_floor_add_one _ |> LT.lt.trans_le <| mod_cast Nat.succ_le_succ ha )
    generalize_proofs at *; (
    -- Since $n \geq \text{pruningExpThresh } C + 3$, we have $\log n \geq (2 * 6^{4C+1} + 1)^2$.
    have h_log_n_ge : Real.log n ≥ (2 * 6 ^ (4 * C + 1) + 1) ^ 2 := by
      have h_log_n_ge : (n : ℝ) ≥ Real.exp ((2 * 6 ^ (4 * C + 1) + 1) ^ 2) := by
        refine' le_trans _ ( Nat.cast_le.mpr hn ) ; norm_num [ pruningExpThresh ];
        norm_num [ explicitMLogPowThresh ];
        exact le_add_of_le_of_nonneg ( le_max_of_le_right ( by linarith [ Nat.le_ceil ( Real.exp ( ( 2 * 6 ^ ( 4 * C + 1 ) + 1 ) ^ 2 ) ) ] ) ) zero_le_three
      generalize_proofs at *; (
      simpa using Real.log_le_log ( by positivity ) h_log_n_ge)
    generalize_proofs at *; (
    -- Since $a \geq \frac{n}{(\log n)^{6^i}} - 1$, we have $a - 1 \geq \frac{n}{2(\log n)^{6^i}}$.
    have ha_minus_one_ge : (a - 1 : ℝ) ≥ (n : ℝ) / (2 * (Real.log n) ^ (6 ^ i)) := by
      have h_a_minus_one_sq_ge : (n : ℝ) / (Real.log n) ^ (6 ^ i) ≥ (n : ℝ) / (2 * (Real.log n) ^ (6 ^ i)) + 2 := by
        have h_a_minus_one_sq_ge : (Real.log n) ^ (6 ^ i) ≥ 2 := by
          exact le_trans ( by nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 6 ) ( show 4 * C + 1 ≥ 1 by linarith ) ] ) ( pow_le_pow_left₀ ( by positivity ) h_log_n_ge _ ) |> le_trans <| pow_le_pow_right₀ ( by nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 6 ) ( show 4 * C + 1 ≥ 1 by linarith ) ] ) <| Nat.one_le_pow _ _ <| by positivity;
        generalize_proofs at *; (
        field_simp;
        have h_n_ge_log_pow : (n : ℝ) ≥ 2 * (Real.log n) ^ (6 ^ (4 * C + 1)) := by
          apply ge_two_mul_log_pow_of_ge_pruningExpThresh C n (by
          linarith [ Nat.zero_le ( pruningExpThresh C ) ])
        generalize_proofs at *; (
        have h_log_pow_ge : (Real.log n) ^ (6 ^ (4 * C + 1)) ≥ (Real.log n) ^ (6 ^ i) * (Real.log n) ^ (6 ^ i) := by
          rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by nlinarith [ show ( 1 :ℝ ) ≤ 6 ^ ( 4 * C + 1 ) by exact one_le_pow₀ ( by norm_num ) ] ) ( by linarith [ show 6 ^ ( 4 * C + 1 ) ≥ 6 ^ i + 6 ^ i by exact le_trans ( add_le_add ( pow_le_pow_right₀ ( by norm_num ) ( show i ≤ 4 * C by linarith ) ) ( pow_le_pow_right₀ ( by norm_num ) ( show i ≤ 4 * C by linarith ) ) ) ( by ring_nf; norm_num ) ] ) ;
        generalize_proofs at *; (
        nlinarith [ show ( 6 : ℝ ) ^ ( 4 * C + 1 ) ≥ 6 by exact le_self_pow₀ ( by norm_num ) ( by linarith ) ])))
      generalize_proofs at *; (
      grobner)
    generalize_proofs at *; (
    -- Substitute $a - 1 \geq \frac{n}{2(\log n)^{6^i}}$ into the ratio.
    have h_ratio_ge : ((a - 1 : ℝ) ^ 2) / (pruningThresh n i) ≥ ((n : ℝ) / (2 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) := by
      gcongr
      generalize_proofs at *; (
      refine' Nat.cast_pos.mpr ( Nat.floor_pos.mpr _ );
      rw [ one_le_div ] <;> norm_cast at * <;> norm_num at *;
      · have := ge_of_ge_explicitMLogPowThresh 1 ( 6 ^ ( i + 1 ) ) one_pos n ( by
          refine' le_trans _ hn;
          refine' le_add_of_le_of_nonneg ( max_le _ _ ) zero_le_three <;> norm_num [ explicitMLogPowThresh, pruningExpThresh ];
          exact Or.inr ( le_trans ( Real.exp_le_exp.mpr <| by gcongr ; linarith ) <| Nat.le_ceil _ ) ) ; aesop;
      · exact pow_pos ( lt_of_lt_of_le ( by positivity ) h_log_n_ge ) _);
      exact Nat.floor_le ( div_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) |> le_trans <| by norm_num;
    generalize_proofs at *; (
    -- Simplify the right-hand side of the inequality.
    have h_simplify : ((n : ℝ) / (2 * (Real.log n) ^ (6 ^ i))) ^ 2 / ((n : ℝ) / (Real.log n) ^ (6 ^ (i + 1))) = (n : ℝ) * (Real.log n) ^ (4 * 6 ^ i) / 4 := by
      field_simp
      ring;
      by_cases h : Real.log n = 0 <;> simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ];
      · norm_cast at *;
      · exact div_eq_iff ( pow_ne_zero _ <| pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ h.1, h.2.1 ⟩ ) |>.2 <| by ring;
    generalize_proofs at *; (
    -- Since $4 * 6^i \geq 3$, we have $(\log n)^{4 * 6^i} \geq (\log n)^3$.
    have h_log_pow_ge : (Real.log n) ^ (4 * 6 ^ i) ≥ (Real.log n) ^ 3 := by
      exact pow_le_pow_right₀ ( by nlinarith [ show ( 6 : ℝ ) ^ ( 4 * C + 1 ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) ] ) ( by linarith [ Nat.pow_le_pow_right ( by norm_num : 1 ≤ 6 ) ( Nat.pos_of_ne_zero hi_zero ) ] )
    generalize_proofs at *; (
    -- Since $C \geq 1$, we have $2^{16C+4} * C \leq 2^{16C+4} * C$.
    have h_exp_bound : (2 : ℝ) ^ (16 * C + 4) * C ≤ (Real.log n) ^ 2 / 4 := by
      refine le_trans ?_ ( div_le_div_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) h_log_n_ge 2 ) zero_le_four ) ; ring_nf ; norm_cast ; norm_num [ Nat.pow_succ', Nat.pow_mul ] at *; (
      refine' le_add_of_nonneg_of_le ( by positivity ) _ ; norm_cast ; induction' C with C ih <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] at * ; ring_nf at * ; (
      norm_num [ pow_mul' ] at * ; ring_nf at * ; (
      exact Nat.recOn C ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith [ pow_pos ( show 0 < 65536 by norm_num ) n, pow_le_pow_left' ( show 2821109907456 ≥ 65536 by norm_num ) n ] ;)))
    generalize_proofs at *; (
    refine le_trans ?_ h_ratio_ge ; rw [ h_simplify ] ; nlinarith [ show ( 0 :ℝ ) ≤ n * Real.log n by positivity ] ;)))))))

/-
Explicit version of `claim_2_4_pruning` for C ≥ 1.
    Combines the three explicit threshold lemmas.
-/
theorem claim_2_4_pruning_explicit (C : ℕ) (hC : C ≥ 1) :
    ∀ n : ℕ, n ≥ pruningExpThresh C + 3 →
    ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∀ B' : Finset (Fin n),
    (∀ u ∈ B', ∀ v ∈ B', u ≠ v → ¬Hc.Adj u v) →
    (∀ v ∈ B', Hc.degree v ≤ 4 * C) →
    B'.card ≥ n / (8 * C + 2) →
    ∃ (T : Finset (Fin n)) (threshold : ℕ),
    T ⊆ B' ∧
    T.card ≥ 2 ∧
    (∀ w, w ∉ T → (∀ v ∈ T, Hc.Adj v w) ∨
      (T.filter (fun v => Hc.Adj v w)).card < threshold) ∧
    (T.card : ℝ) - 1 > 0 ∧
    ((T.card : ℝ) - 1) ^ 2 / (threshold : ℝ) ≥
      2 ^ (16 * C + 4) * C * (↑n * Real.log ↑n) := by
  intro n hn Hc hHc B' hB' hB'' hB''';
  obtain ⟨ i, T, hi₁, hi₂, hi₃, hi₄, hi₅ ⟩ := pruning_chain_produces_controlled C hC Hc B' hB' hB'' (fun i => pruningThresh n i) (fun i hi => pruningThresh_ge_two_explicit C hC n (by linarith) i hi) (pruningThresh_zero_le_B'_card_explicit C hC n (by linarith) _ hB''') (fun i hi => pruningThresh_mono (by linarith) i);
  refine' ⟨ T, pruningThresh n i, hi₂, hi₃, hi₅, _, _ ⟩;
  · exact sub_pos_of_lt ( mod_cast hi₃ );
  · have := pruning_ratio_bound_explicit C hC n ( by linarith ) i hi₁;
    grind

/-! ## Explicit denseN₀Bound -/

/-- The explicit upper bound on `denseN₀Min(C)`.
    For C = 0, the bound is 2 (trivial case).
    For C ≥ 1, the bound is dominated by the pruning threshold
    `pruningExpThresh(C)` ≈ exp(6^{4C+1}). -/
def denseN₀Bound (C : ℕ) : ℕ :=
  if C = 0 then 2
  else max (pruningExpThresh C + 5) (8 * C + 5)

/-
Explicit version of `switchCount_zero_bound`.
    For n ≥ denseN₀Bound(C), the Azuma switchCount zero bound holds.
-/
set_option maxHeartbeats 800000 in
theorem switchCount_zero_bound_explicit (C : ℕ) :
    ∀ n : ℕ, n ≥ denseN₀Bound C → ∀ Hc : SimpleGraph (Fin n),
    Hc.edgeFinset.card ≤ C * n →
    ∃ T : Finset (Fin n),
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hc T G = 0)).card : ℝ) ≤
    (2 : ℝ) ^ n.choose 2 * Real.exp (-(↑n * Real.log ↑n)) := by
  by_cases hC : C = 0 <;> simp_all +decide [ denseN₀Bound ];
  · intro n hn;
    use Finset.univ;
    unfold switchCount;
    unfold switchIndicator; norm_num [ Finset.sum_eq_zero_iff_of_nonneg ] ;
    unfold IsIdSwitch; norm_num [ Finset.card_univ ] ;
    split_ifs <;> norm_num;
    · exact absurd ( ‹∀ a b : Fin n, a = b› ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ) ( by norm_num );
    · positivity;
  · intros n hn Hc hCn
    obtain ⟨B', hB'_indep, hB'_deg, hB'_card, _⟩ := find_good_independent_set C Hc hCn (by
    grind);
    have := claim_2_4_pruning_explicit C ( Nat.pos_of_ne_zero hC ) n ( by linarith [ Nat.le_max_left ( pruningExpThresh C ) ( 8 * C ), Nat.le_max_right ( pruningExpThresh C ) ( 8 * C ) ] ) Hc hCn B' hB'_indep hB'_deg hB'_card;
    obtain ⟨ T, threshold, hT₁, hT₂, hT₃, hT₄, hT₅ ⟩ := this;
    by_cases h_sum_pos : 0 < ∑ e : EdgeSlot n, switchBoundTight Hc T e ^ 2;
    · use T;
      apply azuma_for_switchCount_zero C Hc T (fun e => switchBoundTight Hc T e) (by
      exact fun u hu v hv huv => hB'_indep u ( hT₁ hu ) v ( hT₁ hv ) huv) (by
      exact fun v hv => hB'_deg v ( hT₁ hv )) (by
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose ];
      linarith [ Nat.le_max_right ( pruningExpThresh C ) ( 8 * C ) ]) hT₂ (by
      exact fun e x y hxy => switchCount_bounded_diff_tight Hc T (fun u hu v hv huv => hB'_indep u (hT₁ hu) v (hT₁ hv) huv) e x y hxy) (by
      exact fun e => switchBoundTight_nonneg _ _ _) (by
      convert h_sum_pos using 1);
      apply azuma_exponent_sufficient C Hc T threshold (by
      exact fun u hu v hv huv => hB'_indep u ( hT₁ hu ) v ( hT₁ hv ) huv) (by
      exact fun v hv => hB'_deg v ( hT₁ hv )) (by
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose ];
      linarith [ Nat.le_max_right ( pruningExpThresh C ) ( 8 * C ) ]) hT₂ hT₃ hT₄ hT₅ h_sum_pos;
    · have h_const : ∀ x y : EdgeSlot n → Bool, switchCount Hc T (graphDecode x) = switchCount Hc T (graphDecode y) := by
        have h_const : ∀ e : EdgeSlot n, switchBoundTight Hc T e = 0 := by
          exact fun e => sq_eq_zero_iff.mp ( le_antisymm ( le_of_not_gt fun h => h_sum_pos <| lt_of_lt_of_le ( by positivity ) <| Finset.single_le_sum ( fun x _ => sq_nonneg <| switchBoundTight Hc T x ) <| Finset.mem_univ e ) <| sq_nonneg _ );
        intros x y; exact (by
        have h_const : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool, (∀ e', e' ≠ e → x e' = y e') → |switchCount Hc T (graphDecode x) - switchCount Hc T (graphDecode y)| ≤ switchBoundTight Hc T e := by
          intros e x y hxy; exact (by
          apply switchCount_bounded_diff_tight;
          · exact fun u hu v hv huv => hB'_indep u ( hT₁ hu ) v ( hT₁ hv ) huv;
          · exact hxy);
        have h_const : ∀ e : EdgeSlot n, ∀ x y : EdgeSlot n → Bool, (∀ e', e' ≠ e → x e' = y e') → switchCount Hc T (graphDecode x) = switchCount Hc T (graphDecode y) := by
          intros e x y hxy; specialize h_const e x y hxy; simp_all +decide [ abs_le ] ;
          linarith;
        have h_const : ∀ s : Finset (EdgeSlot n), ∀ x y : EdgeSlot n → Bool, (∀ e ∈ s, x e ≠ y e) → (∀ e ∉ s, x e = y e) → switchCount Hc T (graphDecode x) = switchCount Hc T (graphDecode y) := by
          intros s x y hs hy; induction' s using Finset.induction with e s ih generalizing x y; simp_all +decide ;
          · rw [ show x = y from funext hy ];
          · convert h_const e x ( fun f => if f = e then y e else x f ) _ using 1;
            · grind +splitIndPred;
            · grind +ring;
        exact h_const ( Finset.univ.filter fun e => x e ≠ y e ) x y ( by simp +contextual ) ( by simp +contextual ));
      have h_const_pos : 0 < ∑ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x) := by
        refine' Finset.sum_pos _ _;
        · intro x hx; specialize h_const x ( fun _ => Bool.true ) ; simp_all +decide [ switchCount ] ;
          refine' Finset.sum_pos _ _ <;> simp_all +decide [ switchIndicator ];
          · intro a b ha hb hab; split_ifs <;> simp_all +decide [ IsIdSwitch ] ;
            simp_all +decide [ graphDecode ];
            grind;
          · exact Finset.card_pos.mp ( by simpa [ Finset.offDiag_card ] using by linarith );
        · exact ⟨ fun _ => Bool.true, Finset.mem_univ _ ⟩;
      have h_const_pos : ∀ x : EdgeSlot n → Bool, switchCount Hc T (graphDecode x) > 0 := by
        exact fun x => by rw [ Finset.sum_congr rfl fun y hy => h_const y x ] at h_const_pos; simpa using h_const_pos;
      have h_const_pos : ∀ G : SimpleGraph (Fin n), switchCount Hc T G > 0 := by
        intro G
        obtain ⟨x, hx⟩ : ∃ x : EdgeSlot n → Bool, G = graphDecode x := by
          use fun e => graphEncode G e;
          ext u v; simp +decide [ graphEncode, graphDecode ] ;
          exact fun h => ⟨ fun h' => ⟨ lt_of_le_of_ne h ( by aesop ), by simpa [ SimpleGraph.adj_comm ] using h' ⟩, fun h' => by simpa [ SimpleGraph.adj_comm ] using h'.2 ⟩;
        rw [hx]
        apply h_const_pos;
      exact ⟨ T, by rw [ Finset.card_eq_zero.mpr <| Finset.eq_empty_of_forall_notMem fun G hG => by linarith [ h_const_pos G, Finset.mem_filter.mp hG ] ] ; norm_num; positivity ⟩

/-
Explicit version of `complement_switch_bound`.
    For n ≥ denseN₀Bound(C) + 2, the complement switch bound holds.
-/
set_option maxHeartbeats 800000 in
theorem complement_switch_bound_explicit (C : ℕ) :
    ∀ n : ℕ, n ≥ denseN₀Bound C + 2 → ∀ H : SimpleGraph (Fin n),
    H.edgeFinset.card + C * n ≥ n.choose 2 →
    probUniqueEmb H ≤ (n.factorial : ℝ) * Real.exp (-(↑n * Real.log ↑n)) := by
  intro n hn H hH;
  -- By `switchCount_zero_bound_explicit`, we get T such that #{switchCount = 0} ≤ 2^N * exp(-n*log n).
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n),
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
      switchCount Hᶜ T G = 0)).card : ℝ) ≤ 2 ^ (n.choose 2) * Real.exp (-(n * Real.log n)) := by
        convert switchCount_zero_bound_explicit C n ( by linarith ) Hᶜ _;
        have h_complement_edges : (Hᶜ.edgeFinset.card : ℕ) = n.choose 2 - H.edgeFinset.card := by
          rw [ eq_tsub_iff_add_eq_of_le ];
          · have h_complement_edges : H.edgeFinset.card + Hᶜ.edgeFinset.card = n.choose 2 := by
              have h_complement : H.edgeFinset ∪ Hᶜ.edgeFinset = (SimpleGraph.completeGraph (Fin n)).edgeFinset := by
                ext ⟨ u, v ⟩ ; by_cases h : H.Adj u v <;> aesop;
              rw [ ← Finset.card_union_of_disjoint, h_complement ];
              · simp +decide [ SimpleGraph.edgeFinset ];
                rw [ Finset.card_compl ] ; simp +decide [ Sym2.card, Nat.choose_two_right ];
                rw [ show ( Finset.filter ( Membership.mem Sym2.diagSet ) Finset.univ : Finset ( Sym2 ( Fin n ) ) ) = Finset.image ( fun x : Fin n => Sym2.mk ( x, x ) ) Finset.univ from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
                · exact Nat.sub_eq_of_eq_add <| by nlinarith only [ Nat.sub_add_cancel ( show 1 ≤ n from by linarith [ show 0 < n from Nat.pos_of_ne_zero ( by rintro rfl; contradiction ) ] ), Nat.div_mul_cancel ( show 2 ∣ ( n + 1 ) * n from Nat.dvd_of_mod_eq_zero <| by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ), Nat.div_mul_cancel ( show 2 ∣ n * ( n - 1 ) from Nat.dvd_of_mod_eq_zero <| by rw [ Nat.mod_two_of_bodd ] ; induction n <;> simp +arith +decide [ * ] ) ] ;
                · ext ⟨ x, y ⟩ ; aesop;
              · simp +decide [ SimpleGraph.edgeSet, Finset.disjoint_left ];
                rintro ⟨ u, v ⟩ ; simp +decide [ SimpleGraph.compl_adj ] ;
                tauto;
            linarith;
          · convert H.card_edgeFinset_le_card_choose_two using 1;
            norm_num;
        grind +splitImp;
  have h_complement : (numUniquelyEmbedding H : ℝ) ≤ n.factorial * (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, ¬u = v → ¬IsIdSwitch Hᶜ G u v)).card := by
    convert complement_unique_le_factorial_mul_no_switch Hᶜ using 1;
    norm_cast;
    convert Iff.rfl;
    exact Eq.symm (complement_duality H);
  have h_complement_subset : Finset.filter (fun G : SimpleGraph (Fin n) => ∀ u v : Fin n, ¬u = v → ¬IsIdSwitch Hᶜ G u v) Finset.univ ⊆ Finset.filter (fun G : SimpleGraph (Fin n) => switchCount Hᶜ T G = 0) Finset.univ := by
    apply no_switch_subset_switchCount_zero;
  refine' div_le_of_le_mul₀ _ _ _ <;> try positivity;
  exact h_complement.trans ( mul_le_mul_of_nonneg_left ( le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_complement_subset ) hT ) <| by positivity ) |> le_trans <| by ring_nf; norm_num;

/-- **Step 7: Explicit upper bound on denseN₀Min.**
    denseN₀Min(C) ≤ denseN₀Bound(C) + 2 for all C. -/
theorem denseN₀Min_le_denseN₀Bound (C : ℕ) :
    denseN₀Min C ≤ denseN₀Bound C + 2 := by
  unfold denseN₀Min
  exact Nat.find_min' _ (complement_switch_bound_explicit C)

/-! ## Composed frontier -/

/-- The composed explicit bound function G(C) = denseN₀Bound(C) + 2. -/
def denseN₀G (C : ℕ) : ℕ := denseN₀Bound C + 2

theorem explicitRate_of_adjusted_k (A₀ : ℕ) (hA₀ : 2 ≤ A₀)
    (hGrowth : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.log (Real.log (↑n)) > 1 →
      rateGMin (⌊Real.log (Real.log (↑n)) /
        (↑A₀ * Real.log (Real.log (Real.log (↑n))))⌋₊) ≤ n) :
    ∃ (C : ℝ), C > 0 ∧ ∃ (n₀ : ℕ), ∀ n ≥ n₀, Real.log (Real.log (↑n)) > 1 → fSeq n ≤ C * Real.log (Real.log (Real.log (↑n))) / Real.log (Real.log (↑n)) := by
  refine' ⟨ 2 * A₀, _, _ ⟩;
  · positivity;
  · obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.log (Real.log n) > 1 → ∀ k : ℕ, 2 ≤ k → ⌊(Real.log (Real.log n)) / (A₀ * (Real.log (Real.log (Real.log n))))⌋₊ ≥ k → fSeq n ≤ 1 / (k : ℝ) := by
      obtain ⟨ n₀, hn₀ ⟩ := hGrowth;
      use n₀ + 55;
      intros n hn hn' k hk hk';
      have := fH_lt_at_rateGMin_general ( ⌊Real.log ( Real.log n ) / ( A₀ * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ ) ?_;
      · refine' Finset.sup'_le _ _ _;
        exact fun H _ => le_trans ( le_of_lt ( this n ( hn₀ n ( by linarith ) hn' ) H ) ) ( one_div_le_one_div_of_le ( by positivity ) ( mod_cast hk' ) );
      · linarith;
    obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ n ≥ n₁, Real.log (Real.log n) > 1 → ⌊(Real.log (Real.log n)) / (A₀ * (Real.log (Real.log (Real.log n))))⌋₊ ≥ 2 := by
      have h_log_log_log : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n)) / (A₀ * (Real.log (Real.log (Real.log n)))) ) Filter.atTop Filter.atTop := by
        suffices h_log_log : Filter.Tendsto (fun u : ℝ => u / (A₀ * Real.log u)) Filter.atTop Filter.atTop by
          exact h_log_log.comp ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
        suffices h_log : Filter.Tendsto (fun v : ℝ => Real.exp v / (A₀ * v)) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        have := Real.tendsto_exp_div_pow_atTop 1;
        convert this.const_mul_atTop ( show ( 0 : ℝ ) < 1 / A₀ by positivity ) using 2 ; ring;
      exact Filter.eventually_atTop.mp ( h_log_log_log.eventually_ge_atTop 2 ) |> fun ⟨ n₁, hn₁ ⟩ => ⟨ n₁, fun n hn hn' => Nat.le_floor <| hn₁ n hn ⟩;
    refine' ⟨ n₁ + n₀ + 1, fun n hn hn' => le_trans ( hn₀ n ( by linarith ) hn' ⌊ ( Real.log ( Real.log n ) ) / ( A₀ * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ ( hn₁ n ( by linarith ) hn' ) le_rfl ) _ ⟩;
    rw [ div_le_div_iff₀ ];
    · have := Nat.lt_floor_add_one ( Real.log ( Real.log n ) / ( A₀ * Real.log ( Real.log ( Real.log n ) ) ) );
      rw [ div_lt_iff₀ ] at this;
      · nlinarith [ show ( A₀ : ℝ ) ≥ 2 by norm_cast, show ( ⌊Real.log ( Real.log n ) / ( A₀ * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ : ℝ ) ≥ 2 by exact_mod_cast hn₁ n ( by linarith ) hn', show ( Real.log ( Real.log ( Real.log n ) ) : ℝ ) ≥ 0 by exact Real.log_nonneg <| by linarith ];
      · exact mul_pos ( by positivity ) ( Real.log_pos <| by linarith );
    · exact Nat.cast_pos.mpr ( hn₁ n ( by linarith ) hn' |> le_trans ( by norm_num ) );
    · linarith

/-! ## Part 2: Real analysis core -/

/-- For `0 < α < 1` and `c > 0`, eventually `c · x^α ≤ x`. -/
lemma eventually_pow_dominates (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (c : ℝ) (hc : 0 < c) :
    ∃ x₀ : ℝ, x₀ > 0 ∧ ∀ x ≥ x₀, c * x ^ α ≤ x := by
  have h_exp : ∃ x₀ > 0, ∀ x ≥ x₀, c ≤ x ^ (1 - α) := by
    exact ⟨ c ^ ( 1 / ( 1 - α ) ), by positivity, fun x hx => by exact le_trans ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by linarith ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) hx ( by linarith ) ) ⟩;
  obtain ⟨ x₀, hx₀₁, hx₀₂ ⟩ := h_exp; exact ⟨ x₀, hx₀₁, fun x hx => by convert mul_le_mul_of_nonneg_right ( hx₀₂ x hx ) ( Real.rpow_nonneg ( le_trans hx₀₁.le hx ) α ) using 1 ; rw [ ← Real.rpow_add ( by linarith ) ] ; norm_num ⟩ ;

/-- For `0 < α < 1` and `c > 0`, eventually `exp(c · (log n)^α) ≤ n`. -/
lemma eventually_sublinear_exp (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → n ≥ 2 →
    Real.exp (c * (Real.log (↑n)) ^ α) ≤ (↑n : ℝ) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ > 0 ∧ ∀ x ≥ x₀, c * x ^ α ≤ x := by
    exact eventually_pow_dominates α hα0 hα1 c hc;
  use Nat.ceil (Real.exp x₀) + 1;
  intro n hn hn'; have := hx₀.2 ( Real.log n ) ( by rw [ ge_iff_le ] at *; rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact le_trans ( Nat.le_ceil _ ) ( by norm_cast; linarith ) ) ; rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; linarith;

/-! ## Part 3: Upper bound on denseN₀G -/

/-- For `C ≥ 1`: `denseN₀G(C) ≤ ⌈exp((2·6^{4C+1}+1)²)⌉₊ + 8`. -/
lemma denseN₀G_le_exp_tower (C : ℕ) (hC : 1 ≤ C) :
    denseN₀G C ≤ ⌈Real.exp ((2 * (6 : ℝ) ^ (4 * ↑C + 1) + 1) ^ 2)⌉₊ + 8 := by
  unfold denseN₀G denseN₀Bound;
  unfold pruningExpThresh; norm_num;
  unfold explicitMLogPowThresh; norm_num; split_ifs <;> simp_all +arith +decide;
  constructor;
  · exact Nat.succ_le_of_lt ( Nat.lt_ceil.mpr ( by norm_num; nlinarith [ Real.add_one_le_exp ( ( 2 * 6 ^ ( 4 * C + 1 ) + 1 ) ^ 2 ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 6 ) ( show 4 * C + 1 ≥ 1 by linarith ) ] ) );
  · have := Nat.le_ceil ( Real.exp ( ( 2 * 6 ^ ( 4 * C + 1 ) + 1 ) ^ 2 ) );
    contrapose! this;
    refine' lt_of_lt_of_le ( Nat.cast_lt.mpr ( Nat.lt_of_succ_lt this ) ) _;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
    refine' le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) _;
    norm_num [ pow_succ', pow_mul ];
    norm_cast ; nlinarith only [ show 1296 ^ C ≥ C by exact le_of_lt ( Nat.recOn C ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith only [ ihn ] ) ]

/-! ## Part 4: Bounding densityCBound -/

/-- For `k ≥ 1`, `chernoffL(k) ≤ k + 1`. -/
lemma chernoffL_le_add_one (k : ℕ) (hk : 1 ≤ k) : chernoffL k ≤ k + 1 := by
  unfold chernoffL;
  by_cases hk4 : k ≥ 4;
  · norm_num;
    rw [ Real.sqrt_le_left ] <;> try positivity;
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 16 * k : ℝ ) / 4 );
    rw [ Real.log_div ] at this <;> norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_four, ( by norm_cast : ( 4 :ℝ ) ≤ k ) ];
    linarith;
  · interval_cases k <;> norm_num [ Real.sqrt_le_iff ];
    · rw [ show ( 16 : ℝ ) = 2 ^ 4 by norm_num, Real.log_pow ] ; norm_num ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
    · rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] ; norm_num ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
    · rw [ Real.log_le_iff_le_exp ] <;> norm_num;
      have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 16 = ( Real.exp 1 ) ^ 16 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ )

/-
For `k ≥ 100`, `(densityCBound k : ℝ) ≤ 400 * k * Real.log k`.

    Proof: chernoffL(k) ≤ k+1, so 40k·L ≤ 80k². For k ≥ 100,
    log(80k²) = log80+2logk ≤ 3logk (since log80 ≈ 4.38 ≤ logk).
    So densityC₀(k) ≤ 128k·3logk+2 = 384k·logk+2 ≤ 400k·logk.
    And processN₀(k)/2+1 ≤ 67k ≤ 400k·logk.
-/
lemma densityCBound_le_mul_logk (k : ℕ) (hk : 100 ≤ k) :
    (densityCBound k : ℝ) ≤ 400 * ↑k * Real.log ↑k := by
  simp [densityCBound, densityC₀, processN₀];
  refine' add_le_of_le_sub_right _;
  refine' max_le _ _;
  · -- We'll use that $Real.log (40 * k * chernoffL k) \leq 3 * Real.log k$ for $k \geq 100$.
    have h_log_bound : Real.log (40 * k * chernoffL k) ≤ 3 * Real.log k := by
      erw [ ← Real.log_pow ] ; gcongr ; norm_cast ; ring;
      · exact mul_pos ( mul_pos ( by linarith ) ( Nat.pos_of_ne_zero ( by unfold chernoffL; aesop ) ) ) ( by norm_num );
      · -- Since $k \geq 100$, we have $chernoffL k \leq k + 1$.
        have h_chernoffL_le : chernoffL k ≤ k + 1 := by
          exact chernoffL_le_add_one k ( by linarith );
        norm_cast ; nlinarith [ Nat.pow_le_pow_left hk 2 ];
    nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 128 : ℝ ) * k * Real.log ( 40 * k * chernoffL k ) by exact mul_nonneg ( by positivity ) ( Real.log_nonneg ( by nlinarith [ show ( k : ℝ ) ≥ 100 by norm_cast, show ( chernoffL k : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( chernoffL_pos k ) ] ) ) ), show ( k : ℝ ) ≥ 100 by norm_cast, Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( k : ℝ ) ≥ 2 by norm_cast; linarith ) ];
  · refine' le_trans ( Nat.cast_div_le .. ) _;
    rw [ div_le_iff₀ ] <;> norm_num;
    constructor <;> nlinarith [ show ( k : ℝ ) ≥ 100 by norm_cast, Real.le_log_iff_exp_le ( by positivity : 0 < ( k : ℝ ) ) |>.2 <| show ( Real.exp 1 : ℝ ) ≤ k by exact le_trans ( Real.exp_one_lt_d9.le ) <| by norm_num; linarith [ show ( k : ℝ ) ≥ 100 by norm_cast ], show ( chernoffL k : ℝ ) ≤ k + 1 by exact_mod_cast chernoffL_le_add_one k <| by linarith, show ( ueEdgeThresh k : ℝ ) ≤ 2 * k by exact_mod_cast max_le ( by linarith ) ( by linarith ) ]

/-! ## Part 5: k·logk bound via floor_div_log_mul_log_le -/

lemma rateF_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : rateF k₁ ≤ rateF k₂ := by
  unfold rateF; split_ifs <;> norm_num at *;
  · exact Nat.lt_ceil.mpr ( by norm_num; nlinarith [ Real.add_one_le_exp ( Real.exp ( k₂ * Real.log k₂ ) ), Real.add_one_le_exp ( k₂ * Real.log k₂ ), show ( k₂ : ℝ ) ≥ 2 by norm_cast, Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show ( k₂ : ℝ ) ≥ 2 by norm_cast ) ] );
  · linarith;
  · exact le_trans ( Real.exp_le_exp.mpr <| Real.exp_le_exp.mpr <| mul_le_mul ( Nat.cast_le.mpr h ) ( Real.log_le_log ( by positivity ) <| Nat.cast_le.mpr h ) ( Real.log_nonneg <| by norm_cast; linarith ) <| by positivity ) <| Nat.le_ceil _

/-
Part 1 of growth bound: rateF part. Since our k is ≤ the standard
    ⌊loglogn/logloglogn⌋, monotonicity of rateF gives the bound.
-/
lemma rateF_part_of_growth_bound :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.log (Real.log (↑n)) > 1 →
    rateF (max (⌊Real.log (Real.log (↑n)) /
      (5800 * Real.log (Real.log (Real.log (↑n))))⌋₊) 2) ≤ n := by
  obtain ⟨ n₀, hn₀ ⟩ := rateF_growth_bound;
  refine' ⟨ n₀ + 3, fun n hn hn' => le_trans _ ( hn₀ n ( by linarith ) hn' ) ⟩;
  refine' rateF_mono _;
  refine' max_le _ _;
  · gcongr;
    · exact Real.log_pos hn';
    · linarith [ Real.log_nonneg ( show 1 ≤ Real.log ( Real.log n ) by linarith ) ];
  · refine' Nat.le_floor _;
    rw [ le_div_iff₀ ( Real.log_pos <| by linarith ) ];
    have := Real.log_le_sub_one_of_pos ( show 0 < Real.log ( Real.log n ) / 2 by linarith );
    rw [ Real.log_div ( by linarith ) ( by linarith ) ] at this ; norm_num at * ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ]

lemma k_logk_bound (n : ℕ) (hn : Real.log (Real.log (↑n)) > 5800) :
    (⌊Real.log (Real.log (↑n)) /
      (5800 * Real.log (Real.log (Real.log (↑n))))⌋₊ : ℝ) *
    Real.log (⌊Real.log (Real.log (↑n)) /
      (5800 * Real.log (Real.log (Real.log (↑n))))⌋₊ : ℝ) ≤
    Real.log (Real.log (↑n)) / 5800 := by
  have h_floor : (⌊Real.log (Real.log n) / (5800 * Real.log (Real.log (Real.log n)))⌋₊ : ℝ) ≤ Real.log (Real.log n) / (5800 * Real.log (Real.log (Real.log n))) := by
    exact Nat.floor_le ( div_nonneg ( le_of_lt ( by linarith ) ) ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( by linarith ) ) ) );
  by_cases h₂ : ⌊Real.log (Real.log n) / (5800 * Real.log (Real.log (Real.log n)))⌋₊ ≥ 1;
  · have h_log_floor : Real.log (⌊Real.log (Real.log n) / (5800 * Real.log (Real.log (Real.log n)))⌋₊ : ℝ) ≤ Real.log (Real.log (Real.log n)) := by
      gcongr;
      refine le_trans h_floor ?_;
      refine' div_le_self ( by linarith ) _;
      linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) ( show Real.log ( Real.log n ) ≥ Real.exp 1 by linarith [ Real.exp_one_lt_d9.le ] ) ];
    rw [ le_div_iff₀ ( mul_pos ( by norm_num ) ( Real.log_pos ( show 1 < Real.log ( Real.log n ) from by linarith ) ) ) ] at *;
    nlinarith [ show ( ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ : ℝ ) ≥ 1 by exact_mod_cast h₂, Real.log_nonneg ( show ( ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ : ℝ ) ≥ 1 by exact_mod_cast h₂ ) ];
  · norm_num [ show ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ = 0 by linarith ] at *;
    linarith

/-
Sub-lemma: for large n, exp(c*(logn)^{α}) + 9 ≤ n when α < 1.
-/
lemma eventually_exp_plus_const_le (c : ℝ) (hc : 0 < c) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.exp (c * (Real.log (↑n)) ^ α) + 9 ≤ (↑n : ℝ) := by
  -- By eventually_sublinear_exp with 2c, we get exp(2c*(logn)^α) ≤ n for n ≥ n₀.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 → Real.exp (2 * c * (Real.log n) ^ α) ≤ n := by
    convert eventually_sublinear_exp α hα0 hα1 ( 2 * c ) ( mul_pos zero_lt_two hc ) using 1;
  use Max.max n₀ 18; intro n hn; specialize hn₀ n ( le_trans ( le_max_left _ _ ) hn ) ( by linarith [ le_max_right n₀ 18 ] ) ; (
  rw [ show 2 * c * Real.log n ^ α = c * Real.log n ^ α + c * Real.log n ^ α by ring, Real.exp_add ] at hn₀ ; nlinarith [ Real.add_one_le_exp ( c * Real.log n ^ α ), show ( n : ℝ ) ≥ 18 by norm_cast; linarith [ le_max_right n₀ 18 ] ] ;);

/-
Part 2 of growth bound: denseN₀ part.
-/
lemma denseN0_part_of_growth_bound :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.log (Real.log (↑n)) > 1 →
    denseN₀Min (densityCMin (⌊Real.log (Real.log (↑n)) /
      (5800 * Real.log (Real.log (Real.log (↑n))))⌋₊)) ≤ n := by
  -- Apply the `eventually_exp_plus_const_le` lemma to find an $n₀$.
  have := eventually_exp_plus_const_le 180 (by norm_num) (16 * Real.log 6 / 29) (by
  positivity) (by
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ];
  rw [ Real.log_lt_iff_lt_exp ] <;> norm_num;
  have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 29 = ( Real.exp 1 ) ^ 29 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ ));
  -- Apply the `eventually_exp_plus_const_le` lemma to find an $n₀$ for the denseN₀ part.
  obtain ⟨n₀_denseN₀, hn₀_denseN₀⟩ : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
    ⌈Real.exp ((2 * (6 : ℝ) ^ (4 * (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊) + 1) + 1) ^ 2)⌉₊ + 8 ≤ n := by
      -- Use the bound on densityCBound to relate it to loglogn.
      have h_densityCBound_le : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
        (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) ≤ 2 * Real.log (Real.log (n : ℝ)) / 29 := by
          have h_densityCBound_le : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
            ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ ≥ 100 := by
              have h_floor_ge_100 : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))) Filter.atTop Filter.atTop := by
                -- We can use the change of variables $u = \log \log n$ to transform the limit expression.
                suffices h_change : Filter.Tendsto (fun u : ℝ => u / (5800 * Real.log u)) Filter.atTop Filter.atTop by
                  exact h_change.comp ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
                -- We can use the change of variables $v = \log u$ to transform the limit expression.
                suffices h_change : Filter.Tendsto (fun v : ℝ => Real.exp v / (5800 * v)) Filter.atTop Filter.atTop by
                  have := h_change.comp Real.tendsto_log_atTop;
                  exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
                have := Real.tendsto_exp_div_pow_atTop 1;
                convert this.const_mul_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 5800 ) using 2 ; ring;
              exact Filter.eventually_atTop.mp ( h_floor_ge_100.eventually_ge_atTop 100 ) |> fun ⟨ n₀_denseN₀, hn₀_denseN₀ ⟩ ↦ ⟨ n₀_denseN₀, fun n hn hn' ↦ Nat.le_floor <| hn₀_denseN₀ n hn ⟩;
          have h_densityCBound_le : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
            (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) ≤ 400 * (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) * Real.log (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) := by
              exact ⟨ h_densityCBound_le.choose, fun n hn hn' => densityCBound_le_mul_logk _ ( h_densityCBound_le.choose_spec n hn hn' ) ⟩;
          have h_densityCBound_le : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
            (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) * Real.log (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) ≤ Real.log (Real.log (n : ℝ)) / 5800 := by
              have h_densityCBound_le : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 5800 →
                (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) * Real.log (⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ : ℝ) ≤ Real.log (Real.log (n : ℝ)) / 5800 := by
                  exact ⟨ 0, fun n hn hn' => k_logk_bound n hn' ⟩;
              obtain ⟨ n₀_denseN₀, hn₀_denseN₀ ⟩ := h_densityCBound_le;
              have h_log_log_n_gt_5800 : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 5800 := by
                have h_log_log_n_gt_5800 : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) Filter.atTop Filter.atTop := by
                  exact Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop;
                exact Filter.eventually_atTop.mp ( h_log_log_n_gt_5800.eventually_gt_atTop 5800 );
              exact ⟨ Max.max n₀_denseN₀ h_log_log_n_gt_5800.choose, fun n hn hn' => hn₀_denseN₀ n ( le_trans ( le_max_left _ _ ) hn ) ( h_log_log_n_gt_5800.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ) ⟩;
          obtain ⟨ n₀_denseN₀, hn₀_denseN₀ ⟩ := h_densityCBound_le; obtain ⟨ n₀_denseN₀', hn₀_denseN₀' ⟩ := ‹∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log ( Real.log n ) > 1 → ( densityCBound ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ : ℝ ) ≤ 400 * ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ * Real.log ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊›; use Max.max n₀_denseN₀ n₀_denseN₀'; intros n hn hn'; specialize hn₀_denseN₀ n ( le_trans ( le_max_left _ _ ) hn ) hn'; specialize hn₀_denseN₀' n ( le_trans ( le_max_right _ _ ) hn ) hn'; linarith;
      -- Use the bound on densityCBound to relate it to loglogn and apply the exponential bound.
      have h_exp_bound : ∃ n₀_denseN₀ : ℕ, ∀ n ≥ n₀_denseN₀, Real.log (Real.log (n : ℝ)) > 1 →
        Real.exp ((2 * (6 : ℝ) ^ (4 * (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊) + 1) + 1) ^ 2) ≤ Real.exp (180 * (Real.log (n : ℝ)) ^ (16 * Real.log 6 / 29)) := by
          obtain ⟨n₀_denseN₀, hn₀_denseN₀⟩ := h_densityCBound_le
          use max n₀_denseN₀ 1000000
          intro n hn hn_log
          have h_exp : (6 : ℝ) ^ (4 * (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊) + 1) ≤ 6 * (Real.log (n : ℝ)) ^ (8 * Real.log 6 / 29) := by
            have h_exp : (6 : ℝ) ^ (4 * (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊)) ≤ (Real.log (n : ℝ)) ^ (8 * Real.log 6 / 29) := by
              have h_exp : (6 : ℝ) ^ (4 * (densityCBound ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊)) ≤ (6 : ℝ) ^ (8 * Real.log (Real.log (n : ℝ)) * Real.log 6 / 29 / Real.log 6) := by
                have := hn₀_denseN₀ n ( le_trans ( le_max_left _ _ ) hn ) hn_log;
                rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ];
                rw [ div_mul_cancel₀ _ ( by positivity ) ] ; norm_num ; nlinarith [ Real.log_pos ( show ( 6 : ℝ ) > 1 by norm_num ) ];
              convert h_exp using 1 ; norm_num [ Real.rpow_def_of_pos ] ; ring;
              rw [ Real.rpow_def_of_pos ( Real.log_pos <| by norm_cast; linarith [ le_max_right n₀_denseN₀ 1000000 ] ) ] ; norm_num [ sq, mul_assoc, mul_comm, mul_left_comm ];
            simpa only [ pow_succ' ] using mul_le_mul_of_nonneg_left h_exp <| by norm_num;
          have h_exp : (2 * 6 * (Real.log (n : ℝ)) ^ (8 * Real.log 6 / 29) + 1) ^ 2 ≤ 180 * (Real.log (n : ℝ)) ^ (16 * Real.log 6 / 29) := by
            have h_exp : (Real.log (n : ℝ)) ^ (8 * Real.log 6 / 29) ≥ 1 := by
              exact Real.one_le_rpow ( by linarith [ Real.log_exp 1, Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ Real.exp 1 by exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ show ( n : ℝ ) ≥ 1000000 by exact_mod_cast le_trans ( le_max_right _ _ ) hn ] ) ) ] ) ( by positivity );
            rw [ show ( 16 * Real.log 6 / 29 : ℝ ) = 8 * Real.log 6 / 29 + 8 * Real.log 6 / 29 by ring, Real.rpow_add ] <;> nlinarith [ Real.log_pos <| show ( n :ℝ ) > 1 by norm_cast; linarith [ le_max_right n₀_denseN₀ 1000000 ] ];
          exact Real.exp_le_exp.mpr ( by nlinarith [ show ( 6 : ℝ ) ^ ( 4 * densityCBound ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ + 1 ) ≥ 0 by positivity ] );
      obtain ⟨ n₀_denseN₀, hn₀_denseN₀ ⟩ := h_exp_bound;
      obtain ⟨ n₀_denseN₀', hn₀_denseN₀' ⟩ := this;
      exact ⟨ Max.max n₀_denseN₀ n₀_denseN₀', fun n hn hn' => by have := hn₀_denseN₀' n ( le_trans ( le_max_right _ _ ) hn ) ; have := hn₀_denseN₀ n ( le_trans ( le_max_left _ _ ) hn ) hn'; exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.ceil_lt_add_one <| show 0 ≤ Real.exp ( ( 2 * 6 ^ ( 4 * densityCBound ⌊Real.log ( Real.log n ) / ( 5800 * Real.log ( Real.log ( Real.log n ) ) ) ⌋₊ + 1 ) + 1 ) ^ 2 ) from Real.exp_nonneg _ ] ⟩;
  obtain ⟨n₀_denseN₀', hn₀_denseN₀'⟩ : ∃ n₀_denseN₀' : ℕ, ∀ n ≥ n₀_denseN₀', Real.log (Real.log (n : ℝ)) > 1 →
    ⌊Real.log (Real.log (n : ℝ)) / (5800 * Real.log (Real.log (Real.log (n : ℝ))))⌋₊ ≥ 100 := by
      have h_log_log_log : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / (5800 * Real.log (Real.log (Real.log n)))) Filter.atTop Filter.atTop := by
        -- We can use the change of variables $u = \log \log n$ to transform the limit expression.
        suffices h_change : Filter.Tendsto (fun u : ℝ => u / (5800 * Real.log u)) Filter.atTop Filter.atTop by
          exact h_change.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) );
        -- We can use the change of variables $v = \log u$ to transform the limit expression.
        suffices h_change : Filter.Tendsto (fun v : ℝ => Real.exp v / (5800 * v)) Filter.atTop Filter.atTop by
          have := h_change.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        have := Real.tendsto_exp_div_pow_atTop 1;
        convert this.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 5800 by norm_num ) using 2 ; ring;
      exact Filter.eventually_atTop.mp ( h_log_log_log.eventually_ge_atTop 100 ) |> fun ⟨ n₀_denseN₀', hn₀_denseN₀' ⟩ => ⟨ n₀_denseN₀', fun n hn hn' => Nat.le_floor <| hn₀_denseN₀' n hn ⟩;
  refine' ⟨ n₀_denseN₀ + n₀_denseN₀', fun n hn hn' => le_trans _ ( hn₀_denseN₀ n ( by linarith ) hn' ) ⟩;
  refine' le_trans _ ( denseN₀G_le_exp_tower _ _ );
  · refine' le_trans _ ( denseN₀Min_le_denseN₀Bound _ );
    exact denseN₀Min_mono ( densityCMin_le_bound _ ( by linarith [ hn₀_denseN₀' n ( by linarith ) hn' ] ) );
  · unfold densityCBound; aesop;

/-- **The growth bound closes for `A₀ = 5800`.** -/
theorem adjusted_growth_bound :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
    Real.log (Real.log (↑n)) > 1 →
    rateGMin (⌊Real.log (Real.log (↑n)) /
      (5800 * Real.log (Real.log (Real.log (↑n))))⌋₊) ≤ n := by
  obtain ⟨n₁, hn₁⟩ := rateF_part_of_growth_bound
  obtain ⟨n₂, hn₂⟩ := denseN0_part_of_growth_bound
  exact ⟨max n₁ n₂, fun n hn h => max_le
    (hn₁ n (le_trans (le_max_left _ _) hn) h)
    (hn₂ n (le_trans (le_max_right _ _) hn) h)⟩

/-! ## Part 7: Final theorem -/

/-- log(log(n)) is eventually > 1. -/
private lemma eventually_loglog_gt_one :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.log (Real.log (↑n : ℝ)) > 1 := by
  have : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (↑n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact Filter.eventually_atTop.mp (this.eventually_gt_atTop 1)

/-- **ExplicitRateStatement is true.**
    `f(n) = O(log log log n / log log n)` with constant `C = 11600`. -/
theorem explicitRateStatement_proved : ExplicitRateStatement := by
  obtain ⟨C, hC, n₀, hn₀⟩ := explicitRate_of_adjusted_k 5800 (by norm_num) adjusted_growth_bound
  obtain ⟨n₁, hn₁⟩ := eventually_loglog_gt_one
  exact ⟨C, hC, max n₀ n₁, fun n hn =>
    hn₀ n (le_trans (le_max_left _ _) hn) (hn₁ n (le_trans (le_max_right _ _) hn))⟩

end UniqueSubgraphs

/-- **Erdős Problem 426.** The answer is *no*: if `f(n)` denotes the maximum number of
distinct unique subgraphs of a graph on `n` vertices, then `f(n) = o(2^{C(n,2)}/n!)`.
Here `fSeq n = f(n) / (2^{C(n,2)}/n!)` is the normalized ratio, so the statement is
`fSeq n → 0` (derived from the quantitative rate `explicitRateStatement_proved`). -/
theorem erdos_426 :
    Filter.Tendsto UniqueSubgraphs.fSeq Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, n₀, hn₀⟩ := UniqueSubgraphs.explicitRateStatement_proved
  have h_div : Filter.Tendsto (fun m : ℝ => Real.log m / m) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h_loglog : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h_base : Filter.Tendsto
      (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp] using h_div.comp h_loglog
  have h_rhs : Filter.Tendsto
      (fun n : ℕ => C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using h_base.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rhs ?_ ?_
  · filter_upwards with n
    refine le_trans ?_
      (Finset.le_sup' UniqueSubgraphs.fH (Finset.mem_univ (⊥ : SimpleGraph (Fin n))))
    unfold UniqueSubgraphs.fH UniqueSubgraphs.paperDenom
    positivity
  · filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    exact hn₀ n hn

end

#print axioms erdos_426
-- 'Erdos426.erdos_426' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos426
