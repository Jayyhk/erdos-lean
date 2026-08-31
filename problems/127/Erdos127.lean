import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos127

/-
# Problem Description

Erdős Problem 127, conjectured by Erdős, Kohayakawa and Gyárfás. Let `f(m)` be maximal such
that every graph with `m` edges contains a bipartite subgraph with at least

  `m/2 + (√(8m+1) - 1)/8 + f(m)`

edges. Is there an infinite sequence `mᵢ` with `f(mᵢ) → ∞`? `erdos_127` proves that there
is. Solved by Alon, who showed `f(n²/2) ≫ n^(1/2)`; Edwards had earlier shown `f(m) ≥ 0`
always, and `f` cannot grow faster than `m^(1/4)`.

`baseline m` is the Edwards baseline `m/2 + (√(8m+1) - 1)/8`. `Guarantees m k` says every
finite simple graph with `m` edges has a bipartite subgraph with at least `baseline m + k`
edges, and `correction m = Nat.findGreatest (Guarantees m) m` is the integral version of
`f(m)`. Since `f(mᵢ) → ∞` iff its floor does, the integral form is equivalent for the
question asked. The subgraph lives on the same vertex type with unused vertices isolated,
and quantifying over all finite types is the same as over all finite unlabelled graphs.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/BalancedCut.lean` -/

section
open scoped Sym2
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` crossing the vertex cut given by `S`. -/
private def _root_.SimpleGraph.cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦
    e ∈ Sym2.fromRel (r := fun u v : V ↦ (u ∈ S) ≠ (v ∈ S)) ⟨fun _ _ ↦ ne_comm.mp⟩

@[simp] private lemma _root_.SimpleGraph.mem_cutEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) :
    s(u, v) ∈ G.cutEdgeFinset S ↔ G.Adj u v ∧ ((u ∈ S) ≠ (v ∈ S)) := by
  simp [cutEdgeFinset]

private lemma _root_.SimpleGraph.edgeFinset_between_compl_eq_cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (G.between (S : Set V) (S : Set V)ᶜ).edgeFinset = G.cutEdgeFinset S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, between_adj, mem_coe, Set.mem_compl_iff,
        mem_cutEdgeFinset_mk]
      tauto

private lemma _root_.SimpleGraph.between_compl_isBipartite (G : SimpleGraph V) (S : Finset V) :
    (G.between (S : Set V) (S : Set V)ᶜ).IsBipartite :=
  G.between_isBipartite disjoint_compl_right

private def _root_.SimpleGraph.colorCrosses {q : ℕ} (c : V → Fin q) (A : Finset (Fin q))
    (e : Sym2 V) : Prop :=
  e ∈ Sym2.fromRel (r := fun u v : V ↦ (c u ∈ A) ≠ (c v ∈ A))
    ⟨fun _ _ ↦ ne_comm.mp⟩

@[simp] private lemma _root_.SimpleGraph.colorCrosses_mk {q : ℕ} (c : V → Fin q)
    (A : Finset (Fin q)) (u v : V) :
    colorCrosses c A s(u, v) ↔ ((c u ∈ A) ≠ (c v ∈ A)) := by
  simp [colorCrosses]

private instance _root_.SimpleGraph.colorCrosses_decidablePred {q : ℕ} (c : V → Fin q)
    (A : Finset (Fin q)) : DecidablePred (colorCrosses c A) := fun e ↦ by
  unfold colorCrosses
  infer_instance

private lemma _root_.SimpleGraph.card_powersetCard_filter_mem_notMem {q k : ℕ} (hk : 1 ≤ k)
    {a b : Fin q} (hab : a ≠ b) :
    #((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A) =
      (q - 2).choose (k - 1) := by
  have hab' : a ∈ (Finset.univ.erase b : Finset (Fin q)) := by simp [hab]
  have hsingle : ({a} : Finset (Fin q)) ⊆ Finset.univ.erase b := by simpa
  have hcard_single : #({a} : Finset (Fin q)) ≤ k := by simpa using hk
  have heq :
      ((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A) =
        (((Finset.univ.erase b).powersetCard k).filter fun A ↦ ({a} : Finset (Fin q)) ⊆ A) := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, singleton_subset_iff]
    constructor
    · rintro ⟨hcard, ha, hb⟩
      refine ⟨⟨?_, hcard⟩, ha⟩
      intro x hx
      simp only [mem_erase, mem_univ, and_true]
      rintro rfl
      exact hb hx
    · rintro ⟨⟨hsub, hcard⟩, ha⟩
      refine ⟨hcard, ha, ?_⟩
      intro hb
      have := hsub hb
      simpa using this
  rw [heq, Finset.card_filter_powersetCard_subset _ _ _ hsingle hcard_single]
  simp [Nat.sub_sub]

private lemma _root_.SimpleGraph.card_powersetCard_filter_separates {q k : ℕ} (hk : 1 ≤ k)
    {a b : Fin q} (hab : a ≠ b) :
    #((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦
        (a ∈ A) ≠ (b ∈ A)) = 2 * (q - 2).choose (k - 1) := by
  let L := (Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A
  let R := (Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ b ∈ A ∧ a ∉ A
  have hsep :
      ((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦
          (a ∈ A) ≠ (b ∈ A)) = L ∪ R := by
    ext A
    simp only [mem_filter, mem_powersetCard_univ, mem_union, L, R]
    tauto
  have hdisj : Disjoint L R := by
    simp only [Finset.disjoint_left, mem_filter, mem_powersetCard_univ, L, R]
    aesop
  rw [hsep, card_union_of_disjoint hdisj,
    card_powersetCard_filter_mem_notMem hk hab,
    card_powersetCard_filter_mem_notMem hk hab.symm]
  omega

private lemma _root_.SimpleGraph.sum_balanced_colorCuts {G : SimpleGraph V} [DecidableRel G.Adj]
    {q k : ℕ} (hk : 1 ≤ k) (c : G.Coloring (Fin q)) :
    ∑ A ∈ (Finset.univ.powersetCard k),
        #(G.edgeFinset.filter (colorCrosses c A)) =
      (2 * (q - 2).choose (k - 1)) * #G.edgeFinset := by
  classical
  calc
    ∑ A ∈ (Finset.univ.powersetCard k),
        #(G.edgeFinset.filter (colorCrosses c A)) =
        ∑ A ∈ (Finset.univ.powersetCard k), ∑ e ∈ G.edgeFinset,
          if colorCrosses c A e then 1 else 0 := by
            apply sum_congr rfl
            intro A hA
            exact (Finset.sum_boole (colorCrosses c A) G.edgeFinset).symm
    _ = ∑ e ∈ G.edgeFinset, ∑ A ∈ (Finset.univ.powersetCard k),
          if colorCrosses c A e then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, (2 * (q - 2).choose (k - 1)) := by
          apply sum_congr rfl
          intro e he
          induction e using Sym2.inductionOn with
          | _ u v =>
              have huv : c u ≠ c v := c.valid (by simpa using he)
              rw [← card_filter]
              exact card_powersetCard_filter_separates hk huv
    _ = (2 * (q - 2).choose (k - 1)) * #G.edgeFinset := by simp [mul_comm]

private lemma _root_.SimpleGraph.central_choose_step (n : ℕ) (hn : 1 ≤ n) :
    (2 * n).choose n = 2 * (2 * n - 1).choose (n - 1) := by
  have hrec :
      (2 * n).choose n =
        (2 * n - 1).choose (n - 1) + (2 * n - 1).choose n := by
    have htop : 2 * n - 1 + 1 = 2 * n := by omega
    have hidx : n - 1 + 1 = n := by omega
    simpa only [htop, hidx] using Nat.choose_succ_succ' (2 * n - 1) (n - 1)
  have hsym : (2 * n - 1).choose (n - 1) = (2 * n - 1).choose n := by
    exact Nat.choose_symm_of_eq_add (by omega)
  omega

private lemma _root_.SimpleGraph.odd_middle_step_le (n : ℕ) (hn : 1 ≤ n) :
    (2 * n - 1).choose (n - 1) ≤ 2 * (2 * n - 2).choose (n - 1) := by
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have hn2 : 2 ≤ n := by omega
  have hrec :
      (2 * n - 1).choose (n - 1) =
        (2 * n - 2).choose (n - 2) + (2 * n - 2).choose (n - 1) := by
    have htop : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    have hidx : n - 2 + 1 = n - 1 := by omega
    simpa only [htop, hidx] using Nat.choose_succ_succ' (2 * n - 2) (n - 2)
  have hmono :
      (2 * n - 2).choose (n - 2) ≤ (2 * n - 2).choose (n - 1) := by
    have hlt : n - 2 < (2 * n - 2) / 2 := by omega
    have h := Nat.choose_le_succ_of_lt_half_left hlt
    simpa only [show n - 2 + 1 = n - 1 by omega] using h
  omega

private lemma _root_.SimpleGraph.balanced_choose_ineq {q : ℕ} (hq : 2 ≤ q) :
    (q + 1) * q.choose (q / 2) ≤
      2 * q * (2 * (q - 2).choose (q / 2 - 1)) := by
  rcases q.even_or_odd' with ⟨n, hqeven | hqodd⟩
  · subst q
    have hn : 1 ≤ n := by omega
    have hdiv : 2 * n / 2 = n := by omega
    rw [hdiv, central_choose_step n hn]
    have hratio := Nat.choose_mul_succ_eq (2 * n - 2) (n - 1)
    have hsub : 2 * n - 2 + 1 - (n - 1) = n := by omega
    have htop : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [hsub, htop] at hratio
    apply Nat.le_of_mul_le_mul_left ?_ hn
    calc
      n * ((2 * n + 1) * (2 * (2 * n - 1).choose (n - 1))) =
          2 * (2 * n + 1) * ((2 * n - 1).choose (n - 1) * n) := by ring
      _ = 2 * (2 * n + 1) * ((2 * n - 2).choose (n - 1) * (2 * n - 1)) := by
            rw [← hratio]
      _ ≤ n * (2 * (2 * n) * (2 * (2 * n - 2).choose (n - 1))) := by
            have hsquare :
                (2 * n + 1) * (2 * n - 1) ≤ (2 * n) * (2 * n) := by
              calc
                (2 * n + 1) * (2 * n - 1) =
                    ((2 * n - 1) + 2) * (2 * n - 1) := by congr 1 <;> omega
                _ ≤ ((2 * n - 1) + 1) * ((2 * n - 1) + 1) := by nlinarith
                _ = (2 * n) * (2 * n) := by congr 1 <;> omega
            have hpoly : 2 * (2 * n + 1) * (2 * n - 1) ≤ 8 * n * n := by
              have h := Nat.mul_le_mul_left 2 hsquare
              convert h using 1 <;> ring
            have hmul := Nat.mul_le_mul_right ((2 * n - 2).choose (n - 1)) hpoly
            convert hmul using 1 <;> ring
  · subst q
    have hn : 1 ≤ n := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hdiv]
    have hcentral := central_choose_step n hn
    have hratio := Nat.choose_mul_succ_eq (2 * n) n
    have hsub : 2 * n + 1 - n = n + 1 := by omega
    rw [hsub] at hratio
    calc
      (2 * n + 1 + 1) * (2 * n + 1).choose n =
          2 * ((2 * n + 1).choose n * (n + 1)) := by ring
      _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [← hratio]
      _ = 2 * ((2 * (2 * n - 1).choose (n - 1)) * (2 * n + 1)) := by
            rw [hcentral]
      _ ≤ 2 * (2 * n + 1) * (2 * (2 * n + 1 - 2).choose (n - 1)) := by
            apply Eq.le
            rw [show 2 * n + 1 - 2 = 2 * n - 1 by omega]
            ring

/-- A proper coloring by at least two colors has a vertex cut containing at least
`(q + 1) / (2q)` of all edges, stated without division.  Surjectivity is included
to match the usual formulation but is not needed for the estimate. -/
private theorem _root_.SimpleGraph.exists_cutEdgeFinset_mul_bound {G : SimpleGraph V} [DecidableRel G.Adj]
    {q : ℕ} (hq : 2 ≤ q) (c : G.Coloring (Fin q))
    (_hc : Function.Surjective c) :
    ∃ S : Finset V,
      (q + 1) * #G.edgeFinset ≤ 2 * q * #(G.cutEdgeFinset S) := by
  classical
  let k := q / 2
  let F := (Finset.univ : Finset (Fin q)).powersetCard k
  have hk : 1 ≤ k := by simp only [k]; omega
  have hkq : k ≤ q := by simp only [k]; omega
  have hF : F.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa only [card_univ, Fintype.card_fin] using hkq
  have hcoeff := Nat.mul_le_mul_right (#G.edgeFinset) (balanced_choose_ineq hq)
  have hsum := sum_balanced_colorCuts (G := G) hk c
  have htotal :
      #F * ((q + 1) * #G.edgeFinset) ≤
        2 * q * ∑ A ∈ F, #(G.edgeFinset.filter (colorCrosses c A)) := by
    simp only [F, card_powersetCard, card_univ, Fintype.card_fin]
    rw [hsum]
    convert hcoeff using 1 <;> ring
  have havg :
      (∑ A ∈ F, (q + 1) * #G.edgeFinset) ≤
        ∑ A ∈ F, 2 * q * #(G.edgeFinset.filter (colorCrosses c A)) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    exact htotal
  obtain ⟨A, hAF, hA⟩ := Finset.exists_le_of_sum_le hF havg
  let S : Finset V := Finset.univ.filter fun v ↦ c v ∈ A
  have hcut :
      G.cutEdgeFinset S = G.edgeFinset.filter (colorCrosses c A) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v => simp [cutEdgeFinset, colorCrosses, S]
  refine ⟨S, ?_⟩
  rw [hcut]
  exact hA

/-- Graph-valued form of `exists_cutEdgeFinset_mul_bound`: the selected edges are the
standard bipartite `between S Sᶜ` subgraph of `G`. -/
private theorem _root_.SimpleGraph.exists_bipartite_cut_mul_bound {G : SimpleGraph V} [DecidableRel G.Adj]
    {q : ℕ} (hq : 2 ≤ q) (c : G.Coloring (Fin q))
    (hc : Function.Surjective c) :
    ∃ S : Finset V,
      G.between (S : Set V) (S : Set V)ᶜ ≤ G ∧
      (G.between (S : Set V) (S : Set V)ᶜ).IsBipartite ∧
      (q + 1) * #G.edgeFinset ≤
        2 * q * #(G.between (S : Set V) (S : Set V)ᶜ).edgeFinset := by
  obtain ⟨S, hS⟩ := exists_cutEdgeFinset_mul_bound hq c hc
  refine ⟨S, G.between_le, G.between_compl_isBipartite S, ?_⟩
  rw [edgeFinset_between_compl_eq_cutEdgeFinset]
  exact hS


end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/CriticalClique.lean` -/

section
open scoped ENat
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V]

/-- The degree-sum consequence needed for a finite critical graph. -/
private lemma _root_.SimpleGraph.card_mul_le_twice_edges_of_degree_ge (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hdeg : ∀ v, d ≤ G.degree v) :
    Fintype.card V * d ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    Fintype.card V * d = ∑ _v : V, d := by simp [mul_comm]
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ ↦ hdeg v
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A finite graph of positive finite chromatic number has an induced subgraph
which is vertex-critical for that chromatic number. -/
private lemma _root_.SimpleGraph.exists_induced_vertex_critical (G : SimpleGraph V) [DecidableEq V]
    (q : ℕ) (hq : 0 < q)
    (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      (G.induce (s : Set V)).chromaticNumber = q ∧
      ∀ v : s, ((G.induce (s : Set V)).induce ({v}ᶜ : Set s)).Colorable (q - 1) := by
  classical
  let bad : Finset (Finset V) :=
    Finset.univ.powerset.filter fun s ↦
      ¬(G.induce (s : Set V)).Colorable (q - 1)
  have hGq : G.Colorable q := by
    rw [← chromaticNumber_le_iff_colorable, hχ]
  have hGbad : ¬G.Colorable (q - 1) := by
    intro hc
    have := hc.chromaticNumber_le
    rw [hχ, ENat.natCast_le_natCast] at this
    omega
  have hbad : bad.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [bad, mem_filter, mem_powerset, subset_refl, true_and]
    rw [show (↑(Finset.univ : Finset V) : Set V) = Set.univ by ext; simp]
    exact ((colorable_congr (G.induceUnivIso)).not).mpr hGbad
  obtain ⟨s, hsbad, hsmin⟩ := bad.exists_min_image Finset.card hbad
  have hsnot : ¬(G.induce (s : Set V)).Colorable (q - 1) :=
    (Finset.mem_filter.mp hsbad).2
  have hsq : (G.induce (s : Set V)).Colorable q :=
    hGq.of_hom (Embedding.induce (G := G) (s : Set V)).toHom
  refine ⟨s, ?_, ?_⟩
  · apply le_antisymm hsq.chromaticNumber_le
    rw [le_chromaticNumber_iff_colorable]
    intro m hm
    by_contra! hmq
    exact hsnot (hm.mono (by omega))
  · intro v
    have herase : (G.induce ((s.erase v : Finset V) : Set V)).Colorable (q - 1) := by
      by_contra! hnot
      have herase_bad : s.erase v ∈ bad := by
        simp only [bad, mem_filter, mem_powerset, subset_univ, true_and]
        exact hnot
      have hcard := hsmin (s.erase v) herase_bad
      exact (Nat.not_lt_of_ge hcard) (Finset.card_erase_lt_of_mem v.property)
    obtain ⟨C⟩ := herase
    refine ⟨Coloring.mk (fun w ↦ C ⟨w.1.1, ?_⟩) ?_⟩
    · rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun heq ↦ w.property (Subtype.ext heq), w.1.property⟩
    · intro a b hab
      apply C.valid
      simpa using hab

/-- Extend a coloring over one omitted vertex when fewer than `q` colors occur
among its neighbors. -/
private lemma _root_.SimpleGraph.colorable_of_induce_compl_singleton_colorable_of_degree_lt
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (v : V) (q : ℕ)
    (hc : (G.induce ({v}ᶜ : Set V)).Colorable q)
    (hdeg : G.degree v < q) : G.Colorable q := by
  classical
  let C : (G.induce ({v}ᶜ : Set V)).Coloring (Fin q) := hc.some
  let N : Finset (Fin q) := (G.neighborFinset v).attach.image fun
      w : {x // x ∈ G.neighborFinset v} ↦
    C ⟨w.1, by
      have hwadj : G.Adj v w.1 := (G.mem_neighborFinset v w.1).mp w.property
      simpa using (G.ne_of_adj hwadj).symm⟩
  have hNcard : N.card < Fintype.card (Fin q) := by
    calc
      N.card ≤ (G.neighborFinset v).attach.card := Finset.card_image_le
      _ = G.degree v := by simp [SimpleGraph.card_neighborFinset_eq_degree]
      _ < q := hdeg
      _ = Fintype.card (Fin q) := by simp
  obtain ⟨c, -, hcN⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := N) (t := Finset.univ) hNcard
  refine ⟨Coloring.mk (fun w ↦ if hw : w = v then c else C ⟨w, by simpa [hw]⟩) ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := (G.ne_of_adj hab).symm
    simp only [dite_true, hb, dite_false]
    intro hcb
    apply hcN
    simp only [N, Finset.mem_image]
    refine ⟨⟨b, by simpa using hab⟩, ?_⟩
    exact ⟨by simp, hcb.symm⟩
  · by_cases hb : b = v
    · subst b
      have hva : a ≠ v := G.ne_of_adj hab
      simp only [ha, dite_false, dite_true]
      intro hac
      apply hcN
      simp only [N, Finset.mem_image]
      refine ⟨⟨a, by simpa [G.adj_comm] using hab⟩, ?_⟩
      exact ⟨by simp, hac⟩
    · simp only [ha, hb, dite_false]
      apply C.valid
      simpa using hab

/-- Vertex-criticality forces the usual lower bound on minimum degree. -/
private lemma _root_.SimpleGraph.le_minDegree_of_delete_vertex_colorable
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (q : ℕ) (hnot : ¬G.Colorable q)
    (hdel : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Colorable q) :
    q ≤ G.minDegree := by
  apply G.le_minDegree_of_forall_le_degree
  intro v
  by_contra! hdeg
  exact hnot (colorable_of_induce_compl_singleton_colorable_of_degree_lt G v q (hdel v) hdeg)

/-- Packaged structural consequence: a finite `q`-chromatic graph has an
induced `q`-critical subgraph of minimum degree at least `q - 1`. -/
private lemma _root_.SimpleGraph.exists_induced_critical_minDegree
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      (G.induce (s : Set V)).chromaticNumber = q ∧
      q - 1 ≤ (G.induce (s : Set V)).minDegree := by
  obtain ⟨s, hsχ, hsdel⟩ := exists_induced_vertex_critical G q hq hχ
  have hcard : q ≤ Fintype.card s := by
    have h := (G.induce (s : Set V)).chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hsne : s.Nonempty := Finset.card_pos.mp (by simpa using hq.trans_le hcard)
  letI : Nonempty s := hsne.to_subtype
  refine ⟨s, hsχ, ?_⟩
  apply le_minDegree_of_delete_vertex_colorable
  · intro hc
    have := hc.chromaticNumber_le
    rw [hsχ, ENat.natCast_le_natCast] at this
    omega
  · exact hsdel

/-- If a `q`-coloring cannot be improved to `q-1` colors, representatives of
two singleton color classes must be adjacent. -/
private lemma _root_.SimpleGraph.adj_of_singleton_color_classes
    (G : SimpleGraph V) [DecidableEq V] (q : ℕ)
    (C : G.Coloring (Fin q)) (hnot : ¬G.Colorable (q - 1))
    {u v : V} (huv : u ≠ v)
    (hu : ∀ w, C w = C u → w = u)
    (hv : ∀ w, C w = C v → w = v) : G.Adj u v := by
  classical
  by_contra hadj
  let col : V → Fin q := fun w ↦ if w = u then C v else C w
  have hcu : C v ≠ C u := by
    intro h
    exact huv (hu v h).symm
  have havoid (w : V) : col w ≠ C u := by
    by_cases hw : w = u
    · simp [col, hw, hcu]
    · simp only [col, hw, if_false]
      intro h
      exact hw (hu w h)
  have hproper {a b : V} (hab : G.Adj a b) : col a ≠ col b := by
    by_cases ha : a = u
    · subst a
      have hb : b ≠ u := (G.ne_of_adj hab).symm
      simp only [col, if_pos, hb, if_false]
      intro heq
      have hbv : b = v := hv b heq.symm
      subst b
      exact hadj hab
    · by_cases hb : b = u
      · subst b
        simp only [col, ha, if_false, if_pos]
        intro heq
        have hav : a = v := hv a heq
        subst a
        exact hadj (G.adj_symm hab)
      · simp only [col, ha, hb, if_false]
        exact C.valid hab
  let D : G.Coloring {i : Fin q // i ≠ C u} :=
    Coloring.mk (fun w ↦ ⟨col w, havoid w⟩) (by
      intro a b hab heq
      exact hproper hab (congrArg Subtype.val heq))
  apply hnot
  simpa using D.colorable

/-- In any surjective map to `q` colors, the number of singleton fibers is
at least `2*q - |V|`, in subtraction-free form. -/
private lemma _root_.SimpleGraph.twice_card_le_card_add_singleton_fibers
    (q : ℕ) (C : V → Fin q) (hsurj : Function.Surjective C) :
    2 * q ≤ Fintype.card V +
      (Finset.univ.filter fun i : Fin q ↦
        (Finset.univ.filter fun v : V ↦ C v = i).card = 1).card := by
  classical
  let F : Fin q → Finset V := fun i ↦ Finset.univ.filter fun v ↦ C v = i
  let T : Finset (Fin q) := Finset.univ.filter fun i ↦ (F i).card = 1
  have hFpos (i : Fin q) : 0 < (F i).card := by
    obtain ⟨v, hv⟩ := hsurj i
    exact Finset.card_pos.mpr ⟨v, by simp [F, hv]⟩
  have hpoint (i : Fin q) : 2 ≤ (F i).card + if i ∈ T then 1 else 0 := by
    by_cases hi : i ∈ T
    · have hFi : (F i).card = 1 := (Finset.mem_filter.mp hi).2
      simp [hi, hFi]
    · have hFi : (F i).card ≠ 1 := by
        intro heq
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)
      simp only [hi, if_false, add_zero]
      have hp := hFpos i
      omega
  change 2 * q ≤ Fintype.card V + T.card
  calc
    2 * q = ∑ _i : Fin q, 2 := by simp [mul_comm]
    _ ≤ ∑ i : Fin q, ((F i).card + if i ∈ T then 1 else 0) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = (∑ i : Fin q, (F i).card) + ∑ i : Fin q, (if i ∈ T then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = Fintype.card V + T.card := by
      congr 1
      · symm
        apply Finset.card_eq_sum_card_fiberwise
        intro v _
        simp
      · simp

/-- The singleton classes of an optimal coloring yield the desired large
clique.  The bound `2*q ≤ |V| + |S|` is equivalent to `2*q-|V| ≤ |S|`. -/
private lemma _root_.SimpleGraph.exists_clique_twice_chromatic_le_card_add_card
    (G : SimpleGraph V) [DecidableEq V] (q : ℕ) (hq : 0 < q)
    (C : G.Coloring (Fin q)) (hχ : G.chromaticNumber = q) :
    ∃ S : Finset V, G.IsClique (S : Set V) ∧
      2 * q ≤ Fintype.card V + S.card := by
  classical
  have hqχ : Fintype.card (Fin q) ≤ G.chromaticNumber := by simp [hχ]
  have hsurj : Function.Surjective C :=
    card_le_chromaticNumber_iff_forall_surjective.mp hqχ C
  have hnot : ¬G.Colorable (q - 1) := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hχ, ENat.natCast_le_natCast] at hle
    omega
  let F : Fin q → Finset V := fun i ↦ Finset.univ.filter fun v ↦ C v = i
  let T : Finset (Fin q) := Finset.univ.filter fun i ↦ (F i).card = 1
  let rep : Fin q → V := fun i ↦ (hsurj i).choose
  have hrep (i : Fin q) : C (rep i) = i := (hsurj i).choose_spec
  have hsingle (i : T) : ∀ w, C w = C (rep i) → w = rep i := by
    intro w hw
    have hiCard : (F i).card = 1 := (Finset.mem_filter.mp i.property).2
    exact (Finset.card_le_one_iff.mp hiCard.le)
      (by simp [F, hw, hrep]) (by simp [F, hrep])
  have hrep_inj : Function.Injective (fun i : T ↦ rep i) := by
    intro i j hij
    apply Subtype.ext
    have hcij := congrArg C hij
    simpa [hrep] using hcij
  let S : Finset V := T.attach.image fun i : T ↦ rep i
  have hScard : S.card = T.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hrep_inj]
    simp
  have hSclique : G.IsClique (S : Set V) := by
    rintro a ha b hb hab
    change a ∈ S at ha
    change b ∈ S at hb
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, _, rfl⟩
    exact adj_of_singleton_color_classes G q C hnot hab (hsingle i) (hsingle j)
  refine ⟨S, hSclique, ?_⟩
  rw [hScard]
  simpa [F, T] using twice_card_le_card_add_singleton_fibers q C hsurj

/-- One-stop finite structural lemma collecting criticality, the handshake
bound, and the singleton-class clique bound. -/
private lemma _root_.SimpleGraph.exists_induced_critical_with_handshake_and_clique
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hχ : G.chromaticNumber = q) :
    ∃ s : Finset V,
      let H := G.induce (s : Set V)
      H.chromaticNumber = q ∧
      (∀ v : s, (H.induce ({v}ᶜ : Set s)).Colorable (q - 1)) ∧
      q - 1 ≤ H.minDegree ∧
      Fintype.card s * (q - 1) ≤ 2 * H.edgeFinset.card ∧
      ∃ K : Finset s, H.IsClique (K : Set s) ∧
        2 * q ≤ Fintype.card s + K.card := by
  classical
  obtain ⟨s, hsχ, hsdel⟩ := exists_induced_vertex_critical G q hq hχ
  let H := G.induce (s : Set V)
  have hcard : q ≤ Fintype.card s := by
    have h := H.chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hsne : s.Nonempty := Finset.card_pos.mp (by simpa using hq.trans_le hcard)
  letI : Nonempty s := hsne.to_subtype
  have hnot : ¬H.Colorable (q - 1) := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [hsχ, ENat.natCast_le_natCast] at hle
    omega
  have hmin : q - 1 ≤ H.minDegree :=
    le_minDegree_of_delete_vertex_colorable H (q - 1) hnot hsdel
  have hhand : Fintype.card s * (q - 1) ≤ 2 * H.edgeFinset.card :=
    card_mul_le_twice_edges_of_degree_ge H (q - 1) fun v ↦
      hmin.trans (H.minDegree_le_degree v)
  have hcol : H.Colorable q := by
    rw [← chromaticNumber_le_iff_colorable, hsχ]
  obtain ⟨K, hK, hKcard⟩ :=
    exists_clique_twice_chromatic_le_card_add_card H q hq hcol.some hsχ
  exact ⟨s, hsχ, hsdel, hmin, hhand, K, hK, hKcard⟩

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/Chromatic.lean` -/

section
open scoped ENat
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V]

/-- For a finite graph, `chromaticNumber.toNat` is its actual chromatic
number and admits a surjective optimal coloring. -/
private lemma _root_.SimpleGraph.exists_optimal_coloring_toNat (G : SimpleGraph V) :
    let q := ENat.toNat G.chromaticNumber
    ∃ C : G.Coloring (Fin q), G.chromaticNumber = q ∧ Function.Surjective C := by
  let q := ENat.toNat G.chromaticNumber
  have hcol : G.Colorable q := colorable_chromaticNumber_of_fintype G
  have hne : G.chromaticNumber ≠ ⊤ :=
    (hcol.chromaticNumber_le.trans_lt (ENat.natCast_lt_top q)).ne
  have hχ : G.chromaticNumber = q :=
    (ENat.natCast_toNat_eq_self.mpr hne).symm
  let C : G.Coloring (Fin q) := hcol.some
  have hqχ : Fintype.card (Fin q) ≤ G.chromaticNumber := by simp [hχ]
  exact ⟨C, hχ, card_le_chromaticNumber_iff_forall_surjective.mp hqχ C⟩

/-- An induced subgraph has no more edges than the original graph. -/
private lemma _root_.SimpleGraph.card_edgeFinset_induce_le (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)] :
    (G.induce s).edgeFinset.card ≤ G.edgeFinset.card := by
  have h := congrArg Finset.card (G.map_edgeFinset_induce (s := s))
  rw [Finset.card_map] at h
  rw [h]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Instance-independent edge-count monotonicity for induced subgraphs. -/
private lemma _root_.SimpleGraph.ncard_edgeSet_induce_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).edgeSet.ncard ≤ G.edgeSet.ncard := by
  let f : Sym2 s ↪ Sym2 V := (Function.Embedding.subtype (· ∈ s)).sym2Map
  have hmaps : f '' (G.induce s).edgeSet ⊆ G.edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.inductionOn with
    | _ u v => simpa [f, SimpleGraph.mem_edgeSet] using he
  calc
    (G.induce s).edgeSet.ncard = (f '' (G.induce s).edgeSet).ncard :=
      (Set.ncard_image_of_injective _ f.injective).symm
    _ ≤ G.edgeSet.ncard := Set.ncard_le_ncard hmaps

/-- The standard critical-subgraph argument gives the quadratic lower bound
on the edge count in terms of the finite chromatic number. -/
private lemma _root_.SimpleGraph.chromatic_toNat_mul_pred_le_twice_card_edges
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hedge : G.edgeFinset.Nonempty) :
    let q := ENat.toNat G.chromaticNumber
    q * (q - 1) ≤ 2 * G.edgeFinset.card := by
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, -⟩ := exists_optimal_coloring_toNat G
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2q : 2 ≤ q := by
    have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
      two_le_chromaticNumber_iff_ne_bot.mpr hnebot
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  obtain ⟨s, hsχ, _, _, hhand, _⟩ :=
    exists_induced_critical_with_handshake_and_clique G q (by omega) hχ
  have hqcard : q ≤ Fintype.card s := by
    have h := (G.induce (s : Set V)).chromaticNumber_le_card
    rw [hsχ, ENat.natCast_le_natCast] at h
    exact h
  have hhand' : Fintype.card s * (q - 1) ≤
      2 * (G.induce (s : Set V)).edgeSet.ncard := by
    simpa [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] using hhand
  have hHedge : (G.induce (s : Set V)).edgeSet.ncard ≤ G.edgeSet.ncard :=
    ncard_edgeSet_induce_le G (s : Set V)
  have hGcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  calc
    q * (q - 1) ≤ Fintype.card s * (q - 1) :=
      Nat.mul_le_mul_right (q - 1) hqcard
    _ ≤ 2 * (G.induce (s : Set V)).edgeSet.ncard := hhand'
    _ ≤ 2 * G.edgeSet.ncard := Nat.mul_le_mul_left 2 hHedge
    _ = 2 * G.edgeFinset.card := by rw [hGcard]

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/CutComposition.lean` -/

section
open scoped Sym2
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of `G` with both endpoints in `U`. -/
private def _root_.SimpleGraph.insideEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset ∩ U.sym2

/-- The induced graph on `U`, regarded as a spanning graph on the original
vertex type (all vertices outside `U` are isolated). -/
private def _root_.SimpleGraph.insideGraph (G : SimpleGraph V) (U : Finset V) : SimpleGraph V :=
  (G.induce (U : Set V)).spanningCoe

@[simp] private lemma _root_.SimpleGraph.insideGraph_adj (G : SimpleGraph V) (U : Finset V) (u v : V) :
    (G.insideGraph U).Adj u v ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  constructor
  · rw [insideGraph, SimpleGraph.map_adj]
    rintro ⟨u', v', huv, rfl, rfl⟩
    exact ⟨huv, u'.property, v'.property⟩
  · rintro ⟨huv, hu, hv⟩
    rw [insideGraph, SimpleGraph.map_adj]
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩

private instance _root_.SimpleGraph.insideGraph.instDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : DecidableRel (G.insideGraph U).Adj := fun u v ↦
  decidable_of_iff (G.Adj u v ∧ u ∈ U ∧ v ∈ U) (insideGraph_adj G U u v).symm

private theorem _root_.SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    (G.insideGraph U).edgeFinset = G.insideEdgeFinset U := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [insideGraph_adj, insideEdgeFinset]

@[simp] private lemma _root_.SimpleGraph.mem_insideEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (u v : V) :
    s(u, v) ∈ G.insideEdgeFinset U ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  simp [insideEdgeFinset]

/-- Edges internal to `U` which cross the cut `S`. -/
private def _root_.SimpleGraph.localCutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) : Finset (Sym2 V) :=
  G.insideEdgeFinset U ∩ G.cutEdgeFinset S

@[simp] private lemma _root_.SimpleGraph.mem_localCutEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) (u v : V) :
    s(u, v) ∈ G.localCutEdgeFinset U S ↔
      G.Adj u v ∧ u ∈ U ∧ v ∈ U ∧ ((u ∈ S) ≠ (v ∈ S)) := by
  simp [localCutEdgeFinset]
  tauto

private theorem _root_.SimpleGraph.cutEdgeFinset_insideGraph_eq_localCutEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    (G.insideGraph U).cutEdgeFinset S = G.localCutEdgeFinset U S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [insideGraph_adj, localCutEdgeFinset, insideEdgeFinset] <;> tauto

private lemma _root_.SimpleGraph.edgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    (G.insideEdgeFinset U ∪ G.cutEdgeFinset U) ∪ G.insideEdgeFinset Uᶜ = G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_insideEdgeFinset_mk, mem_cutEdgeFinset_mk,
        mem_compl, mem_edgeFinset]
      tauto

private lemma _root_.SimpleGraph.inside_disjoint_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : Disjoint (G.insideEdgeFinset U) (G.cutEdgeFinset U) := by
  rw [Finset.disjoint_left]
  intro e heI heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at heI heC
      tauto

private lemma _root_.SimpleGraph.inside_union_cut_disjoint_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    Disjoint (G.insideEdgeFinset U ∪ G.cutEdgeFinset U) (G.insideEdgeFinset Uᶜ) := by
  rw [Finset.disjoint_left]
  intro e he heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at he heC
      tauto

/-- Every edge is uniquely internal to `U`, crosses from `U` to its complement,
or is internal to the complement. -/
private theorem _root_.SimpleGraph.card_edgeFinset_eq_inside_add_cut_add_inside_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    #G.edgeFinset =
      #(G.insideEdgeFinset U) + #(G.cutEdgeFinset U) + #(G.insideEdgeFinset Uᶜ) := by
  rw [← edgeFinset_partition G U,
    card_union_of_disjoint (inside_union_cut_disjoint_compl G U),
    card_union_of_disjoint (inside_disjoint_cut G U)]

private lemma _root_.SimpleGraph.cutEdgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) :
    (G.localCutEdgeFinset U S ∪
        (G.cutEdgeFinset U ∩ G.cutEdgeFinset S)) ∪
      G.localCutEdgeFinset Uᶜ S = G.cutEdgeFinset S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_inter, mem_localCutEdgeFinset_mk,
        mem_cutEdgeFinset_mk, mem_compl]
      tauto

private lemma _root_.SimpleGraph.local_disjoint_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) :
    Disjoint (G.localCutEdgeFinset U S)
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset S) := by
  rw [Finset.disjoint_left]
  intro e heI heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at heI heC
      tauto

private lemma _root_.SimpleGraph.local_union_cross_disjoint_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    Disjoint
      (G.localCutEdgeFinset U S ∪ (G.cutEdgeFinset U ∩ G.cutEdgeFinset S))
      (G.localCutEdgeFinset Uᶜ S) := by
  rw [Finset.disjoint_left]
  intro e he heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at he heC
      tauto

private theorem _root_.SimpleGraph.card_cutEdgeFinset_eq_local_add_cross_add_local_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    #(G.cutEdgeFinset S) =
      #(G.localCutEdgeFinset U S) +
        #(G.cutEdgeFinset U ∩ G.cutEdgeFinset S) +
          #(G.localCutEdgeFinset Uᶜ S) := by
  have h := congrArg Finset.card (cutEdgeFinset_partition G U S)
  rw [card_union_of_disjoint (local_union_cross_disjoint_compl G U S),
    card_union_of_disjoint (local_disjoint_cross G U S)] at h
  exact h.symm

private lemma _root_.SimpleGraph.localCutEdgeFinset_union_left
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hT : T ⊆ Uᶜ) :
    G.localCutEdgeFinset U (A ∪ T) = G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union]
      have hu : u ∈ T → u ∉ U := fun huT ↦ by simpa using hT huT
      have hv : v ∈ T → v ∉ U := fun hvT ↦ by simpa using hT hvT
      tauto

private lemma _root_.SimpleGraph.localCutEdgeFinset_union_right
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) :
    G.localCutEdgeFinset Uᶜ (A ∪ T) = G.localCutEdgeFinset Uᶜ T := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_compl]
      have hu : u ∈ A → u ∈ U := fun huA ↦ hA huA
      have hv : v ∈ A → v ∈ U := fun hvA ↦ hA hvA
      tauto

private lemma _root_.SimpleGraph.localCutEdgeFinset_union_compl_sdiff_left
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V} :
    G.localCutEdgeFinset U (A ∪ (Uᶜ \ T)) = G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl]
      tauto

private lemma _root_.SimpleGraph.localCutEdgeFinset_union_compl_sdiff_right
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) :
    G.localCutEdgeFinset Uᶜ (A ∪ (Uᶜ \ T)) =
      G.localCutEdgeFinset Uᶜ T := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl]
      have hu : u ∈ A → u ∈ U := fun huA ↦ hA huA
      have hv : v ∈ A → v ∈ U := fun hvA ↦ hA hvA
      tauto

private lemma _root_.SimpleGraph.oriented_cross_union
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ T)) ∪
        (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ (Uᶜ \ T))) =
      G.cutEdgeFinset U := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_inter, mem_cutEdgeFinset_mk, mem_sdiff, mem_compl]
      have huA : u ∈ A → u ∈ U := fun h ↦ hA h
      have hvA : v ∈ A → v ∈ U := fun h ↦ hA h
      have huT : u ∈ T → u ∉ U := fun hT' ↦ by simpa using hT hT'
      have hvT : v ∈ T → v ∉ U := fun hT' ↦ by simpa using hT hT'
      tauto

private lemma _root_.SimpleGraph.oriented_cross_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    Disjoint
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ T))
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ (Uᶜ \ T))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_inter, mem_cutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl] at he₁ he₂
      have huA : u ∈ A → u ∈ U := fun h ↦ hA h
      have hvA : v ∈ A → v ∈ U := fun h ↦ hA h
      have huT : u ∈ T → u ∉ U := fun hT' ↦ by simpa using hT hT'
      have hvT : v ∈ T → v ∉ U := fun hT' ↦ by simpa using hT hT'
      tauto

/-- Reversing a cut of `Uᶜ` preserves all edges internal to `U` and `Uᶜ`,
while the two orientations partition the `U`--`Uᶜ` edges. -/
private theorem _root_.SimpleGraph.card_oriented_cut_add_card_oriented_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    #(G.cutEdgeFinset (A ∪ T)) +
        #(G.cutEdgeFinset (A ∪ (Uᶜ \ T))) =
      2 * #(G.localCutEdgeFinset U A) +
        2 * #(G.localCutEdgeFinset Uᶜ T) + #(G.cutEdgeFinset U) := by
  rw [card_cutEdgeFinset_eq_local_add_cross_add_local_compl G U (A ∪ T),
    card_cutEdgeFinset_eq_local_add_cross_add_local_compl G U (A ∪ (Uᶜ \ T)),
    localCutEdgeFinset_union_left G hT,
    localCutEdgeFinset_union_right G hA,
    localCutEdgeFinset_union_compl_sdiff_left G,
    localCutEdgeFinset_union_compl_sdiff_right G hA]
  have h := congrArg Finset.card (oriented_cross_union G hA hT)
  rw [card_union_of_disjoint (oriented_cross_disjoint G hA hT)] at h
  omega

/-- One of the two orientations captures at least half the `U`--`Uᶜ` edges,
in addition to both prescribed internal cut contributions. -/
private theorem _root_.SimpleGraph.exists_oriented_cut_mul_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    ∃ S : Finset V,
      (S = A ∪ T ∨ S = A ∪ (Uᶜ \ T)) ∧
        2 * (#(G.localCutEdgeFinset U A) + #(G.localCutEdgeFinset Uᶜ T)) +
            #(G.cutEdgeFinset U) ≤
          2 * #(G.cutEdgeFinset S) := by
  have hsum := card_oriented_cut_add_card_oriented_cut G hA hT
  rcases le_total (#(G.cutEdgeFinset (A ∪ T)))
      (#(G.cutEdgeFinset (A ∪ (Uᶜ \ T)))) with hle | hle
  · refine ⟨A ∪ (Uᶜ \ T), Or.inr rfl, ?_⟩
    omega
  · refine ⟨A ∪ T, Or.inl rfl, ?_⟩
    omega

private lemma _root_.SimpleGraph.image_interedges_eq_localCutEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V} (hA : A ⊆ U) :
    (G.interedges A (U \ A)).image (fun p : V × V ↦ s(p.1, p.2)) =
      G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      constructor
      · intro he
        rcases Finset.mem_image.mp he with ⟨p, hp, hep⟩
        rw [SimpleGraph.mem_interedges_iff] at hp
        rcases hp with ⟨hpA, hpUA, hpAdj⟩
        have hpU : p.1 ∈ U := hA hpA
        have hpU' : p.2 ∈ U := (Finset.mem_sdiff.mp hpUA).1
        have hpnotA : p.2 ∉ A := (Finset.mem_sdiff.mp hpUA).2
        have hpLocal : s(p.1, p.2) ∈ G.localCutEdgeFinset U A := by
          rw [mem_localCutEdgeFinset_mk]
          exact ⟨hpAdj, hpU, hpU', by simp [hpA, hpnotA]⟩
        rwa [hep] at hpLocal
      · intro he
        rw [mem_localCutEdgeFinset_mk] at he
        rcases he with ⟨huv, huU, hvU, hsplit⟩
        by_cases huA : u ∈ A
        · have hvA : v ∉ A := by tauto
          apply Finset.mem_image.mpr
          refine ⟨(u, v), ?_, rfl⟩
          rw [SimpleGraph.mk_mem_interedges_iff]
          exact ⟨huA, Finset.mem_sdiff.mpr ⟨hvU, hvA⟩, huv⟩
        · have hvA : v ∈ A := by tauto
          apply Finset.mem_image.mpr
          refine ⟨(v, u), ?_, by simp⟩
          rw [SimpleGraph.mk_mem_interedges_iff]
          exact ⟨hvA, Finset.mem_sdiff.mpr ⟨huU, huA⟩, (G.adj_comm _ _).mp huv⟩

private lemma _root_.SimpleGraph.sym2OfProd_injOn_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] (U A : Finset V) :
    Set.InjOn (fun p : V × V ↦ s(p.1, p.2)) (G.interedges A (U \ A)) := by
  intro p hp q hq hpq
  rw [Sym2.mk_eq_mk_iff] at hpq
  rcases hpq with hpq | hpq
  · exact hpq
  · change p ∈ G.interedges A (U \ A) at hp
    change q ∈ G.interedges A (U \ A) at hq
    rw [SimpleGraph.mem_interedges_iff] at hp hq
    exfalso
    have hpA : p.1 ∈ A := hp.1
    have hqnotA : q.2 ∉ A := (Finset.mem_sdiff.mp hq.2.1).2
    have : q.2 ∈ A := by simpa [hpq] using hpA
    exact hqnotA this

/-- A cut internal to `U` is counted by the ordered edges from its `A` side to
its `U \ A` side; disjointness makes the unordered-pair quotient injective. -/
private theorem _root_.SimpleGraph.card_localCutEdgeFinset_eq_card_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V} (hA : A ⊆ U) :
    #(G.localCutEdgeFinset U A) = #(G.interedges A (U \ A)) := by
  rw [← image_interedges_eq_localCutEdgeFinset G hA,
    Finset.card_image_of_injOn (sym2OfProd_injOn_interedges G U A)]

private lemma _root_.SimpleGraph.interedges_eq_product_of_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hA : A ⊆ U) (hU : G.IsClique (U : Set V)) :
    G.interedges A (U \ A) = A ×ˢ (U \ A) := by
  ext p
  rw [SimpleGraph.mem_interedges_iff, Finset.mem_product]
  constructor
  · rintro ⟨hpA, hpUA, -⟩
    exact ⟨hpA, hpUA⟩
  · rintro ⟨hpA, hpUA⟩
    refine ⟨hpA, hpUA, ?_⟩
    apply hU
    · exact hA hpA
    · exact (Finset.mem_sdiff.mp hpUA).1
    · intro heq
      exact (Finset.mem_sdiff.mp hpUA).2 (heq ▸ hpA)

/-- In a clique, an internal split into parts of sizes `a` and `b` cuts
exactly `a*b` edges. -/
private theorem _root_.SimpleGraph.card_localCutEdgeFinset_of_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hA : A ⊆ U) (hU : G.IsClique (U : Set V)) :
    #(G.localCutEdgeFinset U A) = #A * #(U \ A) := by
  rw [card_localCutEdgeFinset_eq_card_interedges G hA,
    interedges_eq_product_of_isClique G hA hU, Finset.card_product]

/-- An even clique of size `2*r` admits an equal split cutting exactly `r^2`
of its internal edges (`u^2/4`, stated without division). -/
private theorem _root_.SimpleGraph.exists_half_clique_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U : Finset V} (r : ℕ)
    (hcard : #U = 2 * r) (hU : G.IsClique (U : Set V)) :
    ∃ A ⊆ U, #A = r ∧ #(U \ A) = r ∧
      #(G.localCutEdgeFinset U A) = r * r := by
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq (s := U) (n := r) (by omega)
  refine ⟨A, hA, hAcard, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hA, hcard, hAcard]
    omega
  · rw [card_localCutEdgeFinset_of_isClique G hA hU, hAcard,
      Finset.card_sdiff_of_subset hA, hcard, hAcard]
    have hr : 2 * r - r = r := by omega
    rw [hr]

/-- Combined division-free form used in the clique-composition argument. -/
private theorem _root_.SimpleGraph.exists_cut_of_even_clique_and_compl_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U T : Finset V} (r : ℕ)
    (hcard : #U = 2 * r) (hU : G.IsClique (U : Set V)) (hT : T ⊆ Uᶜ) :
    ∃ A S : Finset V,
      A ⊆ U ∧ #A = r ∧ #(U \ A) = r ∧
        #(G.localCutEdgeFinset U A) = r * r ∧
        (S = A ∪ T ∨ S = A ∪ (Uᶜ \ T)) ∧
        2 * (r * r + #(G.localCutEdgeFinset Uᶜ T)) + #(G.cutEdgeFinset U) ≤
          2 * #(G.cutEdgeFinset S) := by
  obtain ⟨A, hA, hAcard, hAcocard, hAlocal⟩ := exists_half_clique_cut G r hcard hU
  obtain ⟨S, hS, hbound⟩ := exists_oriented_cut_mul_bound G hA hT
  refine ⟨A, S, hA, hAcard, hAcocard, hAlocal, hS, ?_⟩
  rwa [hAlocal] at hbound

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/HeavyHalf.lean` -/

section
open Finset

section
open Finset

variable {α : Type*} [DecidableEq α]

/-- Among an even number of nonnegative integer weights, one can choose half the
indices with the sharp remainder improvement over half the total weight. -/
private theorem _root_.Finset.exists_half_sum_two_ge_add_min
    (U : Finset α) (d : α → ℕ) {x Q s : ℕ}
    (hU : U.Nonempty) (heven : Even #U)
    (hs : s < #U) (hsum : ∑ i ∈ U, d i = x)
    (hx : x = Q * #U + s) :
    ∃ A : Finset α, A ⊆ U ∧ #A = #U / 2 ∧
      x + min s (#U - s) ≤ 2 * ∑ i ∈ A, d i := by
  let u := #U
  let k := u / 2
  let H := U.filter fun i ↦ Q < d i
  have hu : u = #U := rfl
  have hu_pos : 0 < u := by simpa only [u] using hU.card_pos
  have huk : 2 * k = u := by
    simpa only [k] using Nat.two_mul_div_two_of_even heven
  have hkU : k ≤ #U := by omega
  have hrem : s + min s (u - s) ≤ u := by
    rcases le_total s (u - s) with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      omega
  by_cases hH : k ≤ #H
  · obtain ⟨A, hAH, hAcard⟩ := H.exists_subset_card_eq hH
    have hAU : A ⊆ U := hAH.trans (filter_subset _ _)
    have hlarge : (Q + 1) * #A ≤ ∑ i ∈ A, d i := by
      have hlarge' := A.card_nsmul_le_sum d (Q + 1) fun i hi ↦ by
        have hiH := hAH hi
        have hiQ : Q < d i := (mem_filter.mp hiH).2
        omega
      simpa only [Nat.nsmul_eq_mul, mul_comm] using hlarge'
    refine ⟨A, hAU, ?_, ?_⟩
    · simpa only [u, k] using hAcard
    · have htarget : x + min s (u - s) ≤ 2 * ((Q + 1) * k) := by
        have hrem' := hrem
        rw [← huk] at hrem'
        rw [hx, ← hu, ← huk]
        nlinarith
      calc
        x + min s (#U - s) = x + min s (u - s) := by rw [hu]
        _ ≤ 2 * ((Q + 1) * k) := htarget
        _ = 2 * ((Q + 1) * #A) := by rw [hAcard]
        _ ≤ 2 * ∑ i ∈ A, d i := Nat.mul_le_mul_left 2 hlarge
  · have hHk : #H ≤ k := by omega
    obtain ⟨A, hHA, hAU, hAcard⟩ :=
      exists_subsuperset_card_eq (s := H) (t := U) (n := k)
        (filter_subset _ _) hHk hkU
    let B := U \ A
    have hBcard : #B = k := by
      simp only [B, card_sdiff_of_subset hAU, hAcard]
      omega
    have hsmall : ∑ i ∈ B, d i ≤ Q * #B := by
      have hsmall' := B.sum_le_card_nsmul d Q fun i hi ↦ by
        have hiU : i ∈ U := (mem_sdiff.mp hi).1
        have hiA : i ∉ A := (mem_sdiff.mp hi).2
        by_contra hQi
        have hiH : i ∈ H := by
          simp only [H, mem_filter, hiU, true_and]
          omega
        exact hiA (hHA hiH)
      simpa only [Nat.nsmul_eq_mul, mul_comm] using hsmall'
    have hsplit : (∑ i ∈ A, d i) + ∑ i ∈ B, d i = x := by
      change (∑ i ∈ A, d i) + ∑ i ∈ U \ A, d i = x
      rw [add_comm, sum_sdiff hAU, hsum]
    refine ⟨A, hAU, ?_, ?_⟩
    · simpa only [u, k] using hAcard
    · have htarget : x + min s (u - s) ≤ 2 * ∑ i ∈ A, d i := by
        have hsmall' : (∑ i ∈ B, d i) ≤ Q * k := by simpa only [hBcard] using hsmall
        rw [hx, ← hu, ← huk] at hsplit ⊢
        have hmins : min s (2 * k - s) ≤ s := min_le_left _ _
        nlinarith
      simpa only [hu] using htarget

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/DenseSubcase.lean` -/

section
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dense-remainder subcase: split an even clique in half, putting all vertices
outside the clique opposite the heavier half.  The assumptions on `s` are stated
without division, so they express the real interval `u/4 ≤ s ≤ 3u/4` exactly. -/
private theorem _root_.SimpleGraph.exists_bipartite_cut_of_clique_dense_remainder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.Nonempty) (heven : Even #U)
    (hclique : G.IsClique (U : Set V))
    (R s : ℕ) (hs_lo : #U ≤ 4 * s) (hs_hi : 4 * s ≤ 3 * #U)
    (hx : #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = R * #U + s) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ H.IsBipartite ∧
      #U * #U + 2 * #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset + #U / 2 ≤
        4 * #H.edgeFinset := by
  classical
  let W : Finset V := Uᶜ
  let K : SimpleGraph V := G.between (U : Set V) (W : Set V)
  let x : ℕ := #K.edgeFinset
  let d : V → ℕ := fun v ↦ K.degree v
  have hUW : Disjoint U W := by
    simpa only [W] using (disjoint_compl_right : Disjoint U Uᶜ)
  have hK : K.IsBipartiteWith U W := by
    simpa only [K, W, coe_compl] using
      (G.between_isBipartiteWith
        (s := (U : Set V)) (t := (U : Set V)ᶜ) disjoint_compl_right)
  have hsumd : ∑ v ∈ U, d v = x := by
    simpa only [d, x] using K.isBipartiteWith_sum_degrees_eq_card_edges hK
  have hx' : x = R * #U + s := by simpa only [x, K, W] using hx
  have hs_lt : s < #U := by
    have hu_pos := hU.card_pos
    omega
  obtain ⟨A, hAU, hAcard, hheavy⟩ :=
    Finset.exists_half_sum_two_ge_add_min U d hU heven hs_lt hsumd hx'
  let H : SimpleGraph V := G.between (A : Set V) (Aᶜ : Finset V)
  have hHbip : H.IsBipartite := by
    simpa only [H, coe_compl] using
      (G.between_isBipartite (s := (A : Set V)) (t := (A : Set V)ᶜ) disjoint_compl_right)
  have hHA : H.IsBipartiteWith A (Aᶜ : Finset V) := by
    simpa only [H, coe_compl] using
      (G.between_isBipartiteWith
        (s := (A : Set V)) (t := (A : Set V)ᶜ) disjoint_compl_right)
  have hmin : #U / 2 ≤ 2 * min s (#U - s) := by
    have hsU : s ≤ #U := hs_lt.le
    rcases le_total s (#U - s) with hle | hle
    · rw [min_eq_left hle]
      omega
    · rw [min_eq_right hle]
      omega
  have hdeg (a : V) (ha : a ∈ A) :
      #(U \ A) + d a ≤ H.degree a := by
    have haU : a ∈ U := hAU ha
    have hKsub : K.neighborFinset a ⊆ W :=
      K.isBipartiteWith_neighborFinset_subset hK haU
    have hdisj : Disjoint (U \ A) (K.neighborFinset a) := by
      apply Finset.disjoint_left.mpr
      intro v hvU hvK
      have hvW := hKsub hvK
      exact (Finset.disjoint_left.mp hUW (mem_sdiff.mp hvU).1 hvW)
    have hsub : (U \ A) ∪ K.neighborFinset a ⊆ H.neighborFinset a := by
      intro v hv
      rw [mem_union] at hv
      rw [mem_neighborFinset]
      change G.Adj a v ∧
        (a ∈ (A : Set V) ∧ v ∈ (Aᶜ : Finset V) ∨
          a ∈ (Aᶜ : Finset V) ∧ v ∈ (A : Set V))
      rcases hv with hv | hv
      · have hvU : v ∈ U := (mem_sdiff.mp hv).1
        have hvA : v ∉ A := (mem_sdiff.mp hv).2
        have hav : a ≠ v := fun hav ↦ hvA (hav ▸ ha)
        exact ⟨hclique haU hvU hav, Or.inl ⟨ha, by simpa using hvA⟩⟩
      · have hKav : K.Adj a v := by simpa only [mem_neighborFinset] using hv
        have hvW : v ∈ W := hKsub hv
        have hvU : v ∉ U := by simpa only [W, mem_compl] using hvW
        have hvA : v ∉ A := fun hvA ↦ hvU (hAU hvA)
        have hGav : G.Adj a v := by
          change G.Adj a v ∧ _ at hKav
          exact hKav.1
        exact ⟨hGav, Or.inl ⟨ha, by simpa using hvA⟩⟩
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree] at hcard
    exact hcard
  have hcut_lower : #A * #(U \ A) + (∑ a ∈ A, d a) ≤ #H.edgeFinset := by
    calc
      #A * #(U \ A) + (∑ a ∈ A, d a) =
          ∑ a ∈ A, (#(U \ A) + d a) := by
            simp [sum_add_distrib]
      _ ≤ ∑ a ∈ A, H.degree a := by
            exact sum_le_sum fun a ha ↦ hdeg a ha
      _ = #H.edgeFinset := H.isBipartiteWith_sum_degrees_eq_card_edges hHA
  have hUtwo : 2 * (#U / 2) = #U := Nat.two_mul_div_two_of_even heven
  have hdiffcard : #(U \ A) = #U / 2 := by
    rw [card_sdiff_of_subset hAU, hAcard]
    omega
  refine ⟨H, inferInstance, G.between_le, hHbip, ?_⟩
  have hheavy' : x + min s (#U - s) ≤ 2 * ∑ a ∈ A, d a := hheavy
  rw [hAcard, hdiffcard] at hcut_lower
  have hxdef : x = #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset := by
    simp only [x, K, W]
  rw [← hxdef]
  nlinarith

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127/HighChromClique.lean` -/

section
open scoped ENat
open Finset

section
open SimpleGraph

variable {V : Type*} [Fintype V]

/-- High chromatic number at the square edge scale forces an explicitly sized
clique.  The edge hypothesis is the division-free form `|E(G)| = N^2 / 2`.
The witness `s` records the critical induced graph used in the proof. -/
private lemma _root_.SimpleGraph.exists_exact_clique_of_high_chromatic
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (N L : ℕ) (hN : 0 < N) (hNL : 2 * L ≤ N)
    (hedges : 2 * G.edgeFinset.card = N ^ 2)
    (hhigh : N - L < ENat.toNat G.chromaticNumber) :
    let q := ENat.toNat G.chromaticNumber
    q ≤ N ∧
      ∃ s : Finset V,
        (G.induce (s : Set V)).chromaticNumber = q ∧
        Fintype.card s ≤ N + 2 * L ∧
        ∃ U : Finset V, G.IsClique (U : Set V) ∧ U.card = N - 4 * L := by
  classical
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, -⟩ := exists_optimal_coloring_toNat G
  have hedge : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    nlinarith [sq_pos_of_pos hN]
  have hquad := chromatic_toNat_mul_pred_le_twice_card_edges G hedge
  change q * (q - 1) ≤ 2 * G.edgeFinset.card at hquad
  rw [hedges] at hquad
  have hqN : q ≤ N := by
    by_contra! hNq
    have hpred : N ≤ q - 1 := by omega
    nlinarith
  have hNLpos : 0 < N - L := by omega
  have hqpos : 0 < q := by omega
  obtain ⟨s, hsχ, -, -, hhand, K, hK, hKcard⟩ :=
    exists_induced_critical_with_handshake_and_clique G q hqpos hχ
  let H := G.induce (s : Set V)
  have hHedge : H.edgeFinset.card ≤ G.edgeFinset.card := by
    simpa only [edgeFinset, Set.toFinset_card] using
      Fintype.card_le_of_embedding (Copy.induce G (s : Set V)).mapEdgeSet
  have hhand' : Fintype.card s * (q - 1) ≤ N ^ 2 :=
    hhand.trans ((Nat.mul_le_mul_left 2 hHedge).trans_eq hedges)
  have hqpred : N - L ≤ q - 1 := by omega
  have hsub : N - L + L = N := by omega
  have hsBound : Fintype.card s ≤ N + 2 * L := by
    by_contra! hsLarge
    have hprod : N ^ 2 < Fintype.card s * (q - 1) := by
      nlinarith
    exact (Nat.not_lt_of_ge hhand') hprod
  have hKlarge : N - 4 * L ≤ K.card := by omega
  let W : Finset V := K.map (Function.Embedding.subtype (· ∈ (s : Set V)))
  have hWcard : W.card = K.card := by simp [W]
  have hWclique : G.IsClique (W : Set V) := by
    have himage := (isClique_induce_iff.mp hK)
    simpa [W] using himage
  have htarget : N - 4 * L ≤ W.card := by rw [hWcard]; exact hKlarge
  obtain ⟨U, hUW, hUcard⟩ := W.exists_subset_card_eq htarget
  have hUclique : G.IsClique (U : Set V) :=
    hWclique.subset (by simpa using hUW)
  exact ⟨hqN, s, hsχ, hsBound, U, hUclique, hUcard⟩

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos127.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 127.
https://www.erdosproblems.com/forum/thread/127

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos127.md
-/

/-!
# Erdős Problem 127

Alon's affirmative resolution of the problem on the largest bipartite subgraph
of a graph with a prescribed number of edges.
-/

open Filter Finset Set
open scoped ENNReal Topology



/-- The Edwards baseline in Problem 127. -/
noncomputable def baseline (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/-- `Guarantees m k` says that every finite simple graph with `m` edges has a
bipartite subgraph whose number of edges is at least the Edwards baseline plus
the integral correction `k`.

The subgraph is represented on the same vertex type; unused vertices are
isolated.  Quantifying over all finite types is equivalent to quantifying over
all finite (unlabelled) simple graphs. -/
def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
        baseline m + k ≤ (H.edgeSet.ncard : ℝ)

/-- The integral correction function from Problem 127.  The a priori bound
`k ≤ m` is proved below, so this bounded maximum is the genuine maximum. -/
noncomputable def correction (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

private lemma ncard_edgeSet_completeBipartiteGraph (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard = a * b := by
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Set.Finite.cast_ncard_eq (Set.toFinite _)]
  simp [SimpleGraph.encard_edgeSet_completeBipartiteGraph]

lemma guarantees_le_edges {m k : ℕ} (h : Guarantees m k) : k ≤ m := by
  let G := completeBipartiteGraph (Fin 1) (Fin m)
  obtain ⟨H, hHG, -, hk⟩ := h (Fin 1 ⊕ Fin m) G (by
    simpa [G] using ncard_edgeSet_completeBipartiteGraph 1 m)
  have hcard : H.edgeSet.ncard ≤ m := by
    have hsub : H.edgeSet ⊆ G.edgeSet := SimpleGraph.edgeSet_mono hHG
    simpa [G, ncard_edgeSet_completeBipartiteGraph] using Set.ncard_le_ncard hsub
  have hbase : 0 ≤ baseline m := by
    unfold baseline
    have hsqrt : 1 ≤ Real.sqrt (8 * (m : ℝ) + 1) := by
      have hm : 0 ≤ (m : ℝ) := by positivity
      calc
        1 = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (8 * (m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    positivity
  exact_mod_cast (show (k : ℝ) ≤ m by
    exact (le_add_of_nonneg_left hbase).trans (hk.trans (by exact_mod_cast hcard)))

lemma le_correction_of_guarantees {m k : ℕ} (h : Guarantees m k) :
    k ≤ correction m := by
  classical
  unfold correction
  exact Nat.le_findGreatest (guarantees_le_edges h) h

/-- Edwards' theorem in the exact form used in Problem 127. -/
theorem exists_edwards_bipartite_subgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      baseline G.edgeSet.ncard ≤ (H.edgeSet.ncard : ℝ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases hedge : G.edgeFinset.Nonempty
  · let q := ENat.toNat G.chromaticNumber
    obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
    have hnebot : G ≠ ⊥ := by
      intro hbot
      subst G
      simpa using hedge
    have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
      SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
    have hq : 2 ≤ q := by
      rw [hχ] at h2χ
      exact_mod_cast h2χ
    obtain ⟨S, hle, hbip, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
    let H := G.between (S : Set V) (S : Set V)ᶜ
    let m := G.edgeFinset.card
    let c := H.edgeFinset.card
    have hchrom : q * (q - 1) ≤ 2 * m := by
      simpa only [m] using G.chromatic_toNat_mul_pred_le_twice_card_edges hedge
    have hm : G.edgeSet.ncard = m := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hc : H.edgeSet.ncard = c := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hqR : (0 : ℝ) < q := by positivity
    have hmR : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
    have hchromR' : (q : ℝ) * ((q - 1 : ℕ) : ℝ) ≤ 2 * m := by
      exact_mod_cast hchrom
    have hchromR : (q : ℝ) * (q - 1) ≤ 2 * m := by
      simpa [Nat.cast_sub (by omega : 1 ≤ q)] using hchromR'
    have hcutR : ((q + 1) * m : ℕ) ≤ 2 * q * c := by
      simpa only [H, m, c] using hcut
    have hcutR' : ((q : ℝ) + 1) * m ≤ 2 * q * c := by exact_mod_cast hcutR
    have hsqrt : Real.sqrt (8 * (m : ℝ) + 1) ≤ 4 * m / q + 1 := by
      have hright : 0 ≤ (4 : ℝ) * m / q + 1 := by
        have : 0 ≤ (4 : ℝ) * m / q := div_nonneg (mul_nonneg (by norm_num) hmR) hqR.le
        linarith
      rw [Real.sqrt_le_left hright]
      have hcore : 0 ≤ (2 : ℝ) * m - q * (q - 1) := by linarith
      have hprod : 0 ≤ (8 : ℝ) * m * ((2 : ℝ) * m - q * (q - 1)) :=
        mul_nonneg (mul_nonneg (by positivity) hmR) hcore
      field_simp
      nlinarith
    have hbonus : (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8 ≤ m / (2 * q) := by
      have hsub := sub_le_sub_right hsqrt 1
      have hdiv := div_le_div_of_nonneg_right hsub (by norm_num : (0 : ℝ) ≤ 8)
      calc
        (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8 ≤ (4 * m / q) / 8 := by
          simpa only [add_sub_cancel_right] using hdiv
        _ = m / (2 * q) := by
          field_simp
          ring
    have hbalanced : (m : ℝ) / 2 + m / (2 * q) ≤ c := by
      have hid : (m : ℝ) / 2 + m / (2 * q) = ((q + 1) * m) / (2 * q) := by
        field_simp
      rw [hid, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcutR'
    refine ⟨H, hle, hbip, ?_⟩
    rw [hm, hc]
    unfold baseline
    linarith
  · have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hedge
    have hm : G.edgeSet.ncard = 0 := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hempty]
      simp
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · exact ⟨SimpleGraph.Coloring.mk (fun _ ↦ 0) (by simp)⟩
    simp [baseline, hm]

theorem guarantees_zero (m : ℕ) : Guarantees m 0 := by
  intro V _ G hm
  obtain ⟨H, hle, hbip, hbound⟩ := exists_edwards_bipartite_subgraph G
  exact ⟨H, hle, hbip, by simpa [hm] using hbound⟩

lemma correction_spec (m : ℕ) : Guarantees m (correction m) := by
  classical
  unfold correction
  exact Nat.findGreatest_spec (Nat.zero_le m) (guarantees_zero m)

lemma correction_isGreatest (m : ℕ) :
    IsGreatest {k : ℕ | Guarantees m k} (correction m) :=
  ⟨correction_spec m, fun _ hk ↦ le_correction_of_guarantees hk⟩

/-- A division-free coarse consequence of Edwards' coloring argument. -/
theorem exists_coarse_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℕ) (ha : 1 ≤ a) (hedges : 8 * a ^ 2 ≤ G.edgeSet.ncard) :
  ∃ S : Finset V,
      G.edgeSet.ncard + 2 * a ≤ 2 * #(G.cutEdgeFinset S) := by
  classical
  let w := G.edgeFinset.card
  have hw : G.edgeSet.ncard = w := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hwpos : 0 < w := by
    rw [hw] at hedges
    nlinarith
  have hedge : G.edgeFinset.Nonempty := Finset.card_pos.mp hwpos
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
  have hq : 2 ≤ q := by
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  have hchrom : q * (q - 1) ≤ 2 * w := by
    simpa only [w] using G.chromatic_toNat_mul_pred_le_twice_card_edges hedge
  obtain ⟨S, -, -, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
  rw [G.edgeFinset_between_compl_eq_cutEdgeFinset S] at hcut
  change (q + 1) * w ≤ 2 * q * #(G.cutEdgeFinset S) at hcut
  refine ⟨S, ?_⟩
  rw [hw]
  by_contra! hsmall
  have hwa : w < 2 * q * a := by nlinarith
  have hqbound : q ≤ 4 * a := by
    have hpred : q - 1 + 1 = q := by omega
    nlinarith
  rw [hw] at hedges
  nlinarith

lemma card_insideEdgeFinset_of_isClique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU : G.IsClique (U : Set V)) :
    #(G.insideEdgeFinset U) = U.card.choose 2 := by
  have htop : G.induce (U : Set V) = ⊤ := G.induce_eq_top.mpr hU
  calc
    #(G.insideEdgeFinset U) = #(G.induce (U : Set V)).edgeFinset := by
      rw [SimpleGraph.insideEdgeFinset, ← G.filter_edgeFinset_toFinset_subset U]
      exact G.card_filter_edgeFinset_toFinset_subset U
    _ = (G.induce (U : Set V)).edgeSet.ncard := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ = (⊤ : SimpleGraph (U : Set V)).edgeSet.ncard := by rw [htop]
    _ = #(⊤ : SimpleGraph (U : Set V)).edgeFinset := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ = U.card.choose 2 := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

lemma localCutEdgeFinset_inter_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    G.localCutEdgeFinset U (S ∩ U) = G.localCutEdgeFinset U S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [SimpleGraph.mem_localCutEdgeFinset_mk] <;> tauto

private theorem thresholdQuarterArithmetic (t : ℕ) (ht : 1 ≤ t) :
    4 * (8 * (128 * t) ^ 2) + 4 * (64 * t) ≤ 2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

private theorem squareRemainderArithmetic (t : ℕ) (ht : 1 ≤ t) :
    2 * ((4 * (64 * t)) * (4 * (64 * t))) + 4 * (64 * t) ≤
      2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

private theorem smallBonusArithmetic (t : ℕ) (ht : 1 ≤ t) :
    4 * (8 * (128 * t) ^ 2) + 2 * (4 * (64 * t)) + 8 * t + 4 * (64 * t) ≤
      2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

/-- Explicit specialization of Alon's theorem at `N = 2^20 t^2`.  The
conclusion is the desired cut estimate with all divisions cleared. -/
theorem explicit_alon_cut {t : ℕ} (ht : 1 ≤ t) {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : 2 * #G.edgeFinset = (2 ^ 20 * t ^ 2) ^ 2) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧ H.IsBipartite ∧
        2 * #G.edgeFinset + (2 ^ 20 * t ^ 2) + 4 * t ≤ 4 * #H.edgeFinset := by
  classical
  let N := 2 ^ 20 * t ^ 2
  let L := 64 * t
  let R := 4 * L
  let y := 128 * t
  let m := #G.edgeFinset
  let q := ENat.toNat G.chromaticNumber
  have htPos : 0 < t := by omega
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hedge : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcard
    have hcard0 : #G.edgeFinset = 0 := Nat.eq_zero_of_not_pos hcard
    have hright : 0 < (2 ^ 20 * t ^ 2) ^ 2 := by positivity
    rw [hcard0] at hedges
    simp only [Nat.reduceMul] at hedges
    omega
  obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
  have hq : 2 ≤ q := by
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  have hedges' : 2 * m = N ^ 2 := by simpa only [m, N] using hedges
  by_cases hlow : q ≤ N - L
  · obtain ⟨S, hle, hbip, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
    let H := G.between (S : Set V) (S : Set V)ᶜ
    let c := #H.edgeFinset
    have hLle : L ≤ N := by
      dsimp [N, L]
      nlinarith [show t ≤ t ^ 2 by nlinarith]
    have hsubL : N - L + L = N := Nat.sub_add_cancel hLle
    have hconst : (N - L) * (N + 4 * t) ≤ N ^ 2 := by
      have hfour : 4 * t ≤ L := by
        dsimp [L]
        omega
      have hmul : (N - L) * (4 * t) ≤ N * L :=
        Nat.mul_le_mul (Nat.sub_le N L) hfour
      calc
        (N - L) * (N + 4 * t) = (N - L) * N + (N - L) * (4 * t) := by ring
        _ ≤ (N - L) * N + N * L := Nat.add_le_add_left hmul _
        _ = N * ((N - L) + L) := by ring
        _ = N ^ 2 := by rw [hsubL]; ring
    have hqm : q * (N + 4 * t) ≤ 2 * m := by
      calc
        q * (N + 4 * t) ≤ (N - L) * (N + 4 * t) :=
          Nat.mul_le_mul_right (N + 4 * t) hlow
        _ ≤ N ^ 2 := hconst
        _ = 2 * m := hedges'.symm
    have hcut' : (q + 1) * m ≤ 2 * q * c := by
      simpa only [m, H, c] using hcut
    have htarget : 2 * m + N + 4 * t ≤ 4 * c := by
      nlinarith
    exact ⟨H, inferInstance, hle, hbip, by simpa only [m, N, H, c] using htarget⟩
  · have hhigh : N - L < q := by omega
    have hNL : 2 * L ≤ N := by
      dsimp [N, L]
      norm_num
      nlinarith
    obtain ⟨-, sCrit, -, -, U, hUclique, hUcard⟩ :=
      G.exists_exact_clique_of_high_chromatic N L hN hNL hedges' hhigh
    let u := #U
    let eU := #(G.insideEdgeFinset U)
    let x := #(G.cutEdgeFinset U)
    let eW := #(G.insideEdgeFinset Uᶜ)
    have hR : R = 4 * L := rfl
    have hu : u = N - R := by simpa only [u, R] using hUcard
    have hRle : R ≤ N := by
      dsimp [N, L, R]
      norm_num
      nlinarith
    have hNuR : u + R = N := by omega
    have huPos : 0 < u := by
      rw [hu]
      dsimp [N, L, R]
      norm_num
      nlinarith
    have hUne : U.Nonempty := Finset.card_pos.mp (by simpa only [u] using huPos)
    have hNeven : Even N := by
      refine ⟨2 ^ 19 * t ^ 2, ?_⟩
      dsimp [N]
      ring
    have hReven : Even R := by
      refine ⟨128 * t, ?_⟩
      dsimp [R, L]
      ring
    rcases hNeven with ⟨nN, hnN⟩
    rcases hReven with ⟨nR, hnR⟩
    have hnRle : nR ≤ nN := by nlinarith [hRle]
    have huEven : Even u := by
      refine ⟨nN - nR, ?_⟩
      omega
    have huHalf : 2 * (u / 2) = u := Nat.two_mul_div_two_of_even huEven
    have hEU : eU = u * (u - 1) / 2 := by
      rw [show eU = u.choose 2 by
        simpa only [eU, u] using card_insideEdgeFinset_of_isClique G U hUclique]
      exact Nat.choose_two_right u
    have hprodEven : Even (u * (u - 1)) := huEven.mul_right (u - 1)
    have hEUtwo : 2 * eU = u * (u - 1) := by
      rw [hEU]
      exact Nat.two_mul_div_two_of_even hprodEven
    have hpart : m = eU + x + eW := by
      simpa only [m, eU, x, eW] using
        G.card_edgeFinset_eq_inside_add_cut_add_inside_compl U
    by_cases hlarge : 8 * y ^ 2 ≤ eW
    · let GW := G.insideGraph Uᶜ
      have hGWcard : GW.edgeSet.ncard = eW := by
        calc
          GW.edgeSet.ncard = #GW.edgeFinset := by
            rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = eW := by
            rw [G.edgeFinset_insideGraph_eq_insideEdgeFinset]
      have hy : 1 ≤ y := by
        dsimp [y]
        omega
      have hGWlarge : 8 * y ^ 2 ≤ GW.edgeSet.ncard := by
        rw [hGWcard]
        exact hlarge
      obtain ⟨T, hTcut⟩ := exists_coarse_cut GW y hy hGWlarge
      let T' := T ∩ Uᶜ
      have hTsub : T' ⊆ Uᶜ := Finset.inter_subset_right
      have hlocal : eW + 2 * y ≤ 2 * #(G.localCutEdgeFinset Uᶜ T') := by
        rw [localCutEdgeFinset_inter_self G Uᶜ T,
          ← G.cutEdgeFinset_insideGraph_eq_localCutEdgeFinset]
        simpa only [hGWcard] using hTcut
      let r := u / 2
      have hUcard2 : #U = 2 * r := by simpa only [u, r] using huHalf.symm
      obtain ⟨A, S, -, -, -, -, -, hcomp⟩ :=
        G.exists_cut_of_even_clique_and_compl_cut r hUcard2 hUclique hTsub
      let H := G.between (S : Set V) (S : Set V)ᶜ
      have hrr : 4 * (r * r) = u * u := by
        calc
          4 * (r * r) = (2 * r) * (2 * r) := by ring
          _ = u * u := by rw [show 2 * r = u by simpa only [r] using huHalf]
      have hlocal2 : 2 * eW + 4 * y ≤
          4 * #(G.localCutEdgeFinset Uᶜ T') := by omega
      have hcomp2 : 4 * (r * r) + 2 * x +
          4 * #(G.localCutEdgeFinset Uᶜ T') ≤
          4 * #(G.cutEdgeFinset S) := by omega
      have hcutBonus : u * u + 2 * x + 2 * eW + 4 * y ≤
          4 * #(G.cutEdgeFinset S) := by omega
      have hpred : u - 1 + 1 = u := Nat.sub_add_cancel (by omega : 1 ≤ u)
      have hsq : u * (u - 1) + u = u * u := by
        simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun z => u * z) hpred
      have hm2 : 2 * m = u * (u - 1) + 2 * x + 2 * eW := by omega
      have hRbonus : N + 4 * t ≤ u + 4 * y := by
        dsimp [R, L, y] at hNuR
        omega
      have htarget : 2 * m + N + 4 * t ≤ 4 * #(G.cutEdgeFinset S) := by
        omega
      refine ⟨H, inferInstance, G.between_le, G.between_compl_isBipartite S, ?_⟩
      rw [G.edgeFinset_between_compl_eq_cutEdgeFinset]
      simpa only [m, N, H] using htarget
    · have hsmall : eW < 8 * y ^ 2 := by omega
      have hR2Even : Even (R * R) := by
        refine ⟨2 * L * R, ?_⟩
        dsimp [R]
        ring
      have hR2half : 2 * ((R * R) / 2) = R * R :=
        Nat.two_mul_div_two_of_even hR2Even
      let a0 := u / 2 + (R * R) / 2
      have ha0two : 2 * a0 = u + R * R := by
        dsimp [a0]
        omega
      have hpred : u - 1 + 1 = u := Nat.sub_add_cancel (by omega : 1 ≤ u)
      have hsq : u * (u - 1) + u = u * u := by
        simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun z => u * z) hpred
      have hm2 : 2 * m = u * (u - 1) + 2 * x + 2 * eW := by omega
      have hN2 : N ^ 2 = u * u + 2 * R * u + R * R := by
        rw [← hNuR]
        ring
      have hDtwo : 2 * (x + eW) = 2 * R * u + u + R * R := by
        omega
      have hrighttwo : 2 * (R * u + a0) = 2 * R * u + u + R * R := by
        calc
          2 * (R * u + a0) = 2 * R * u + 2 * a0 := by ring
          _ = 2 * R * u + u + R * R := by rw [ha0two]; omega
      have hD : x + eW = R * u + a0 :=
        Nat.mul_left_cancel (by norm_num) (hDtwo.trans hrighttwo.symm)
      have hthresholdQuarter : 4 * (8 * y ^ 2) ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R, y] using thresholdQuarterArithmetic t ht
      have heWa0 : eW ≤ a0 := by omega
      let rem := a0 - eW
      have hremadd : rem + eW = a0 := by omega
      have hx : x = R * u + rem := by omega
      have hremlo : u ≤ 4 * rem := by omega
      have hR2u : 2 * (R * R) ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R] using squareRemainderArithmetic t ht
      have hremhi : 4 * rem ≤ 3 * u := by omega
      have hxcut :
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = x := by
        have hgraphs : G.between (U : Set V) (Uᶜ : Finset V) =
            G.between (U : Set V) (U : Set V)ᶜ := by
          ext v w
          simp only [SimpleGraph.between_adj, Finset.coe_compl]
        calc
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset =
              (G.between (U : Set V) (Uᶜ : Finset V)).edgeSet.ncard := by
                rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = (G.between (U : Set V) (U : Set V)ᶜ).edgeSet.ncard := by rw [hgraphs]
          _ = #(G.between (U : Set V) (U : Set V)ᶜ).edgeFinset := by
                rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = #(G.cutEdgeFinset U) :=
            congrArg Finset.card (G.edgeFinset_between_compl_eq_cutEdgeFinset U)
          _ = x := rfl
      have hxBetween :
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = R * #U + rem := by
        rw [hxcut]
        simpa only [u] using hx
      obtain ⟨H, instH, hHG, hHbip, hbound⟩ :=
        G.exists_bipartite_cut_of_clique_dense_remainder U hUne huEven hUclique
          R rem (by simpa only [u] using hremlo) (by simpa only [u] using hremhi) hxBetween
      letI : DecidableRel H.Adj := instH
      have hbound' : u * u + 2 * x + u / 2 ≤ 4 * #H.edgeFinset := by
        rw [hxcut] at hbound
        simpa only [u, x] using hbound
      have hbonusRaw : 4 * (8 * y ^ 2) + 2 * R + 8 * t ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R, y] using smallBonusArithmetic t ht
      have hhalfBonus : 2 * eW + R + 4 * t ≤ u / 2 := by omega
      have hpretarget : 2 * m + N + 4 * t ≤ u * u + 2 * x + u / 2 := by
        omega
      have htarget : 2 * m + N + 4 * t ≤ 4 * #H.edgeFinset := by
        exact hpretarget.trans hbound'
      exact ⟨H, instH, hHG, hHbip, by simpa only [m, N] using htarget⟩

/-- The vertex scale in the explicit family used for Alon's lower bound. -/
def alonParameter (t : ℕ) : ℕ := 2 ^ 20 * t ^ 2

/-- The edge count `N² / 2` at the scale `N = 2²⁰t²`. -/
def alonEdgeCount (t : ℕ) : ℕ := alonParameter t ^ 2 / 2

lemma two_mul_alonEdgeCount (t : ℕ) :
    2 * alonEdgeCount t = alonParameter t ^ 2 := by
  unfold alonEdgeCount alonParameter
  apply Nat.two_mul_div_two_of_even
  refine ⟨(2 ^ 19 * t ^ 2) * (2 ^ 20 * t ^ 2), ?_⟩
  ring

private lemma parameter_le_edgeCount (t : ℕ) (ht : 1 ≤ t) :
    t ≤ alonEdgeCount t := by
  have htwo := two_mul_alonEdgeCount t
  have hbound : 2 * t ≤ alonParameter t ^ 2 := by
    have htt : t ≤ t ^ 2 := by nlinarith
    have h2t : 2 * t ≤ alonParameter t := by
      dsimp [alonParameter]
      omega
    have hN1 : 1 ≤ alonParameter t := by omega
    have hNsq : alonParameter t ≤ alonParameter t ^ 2 := by nlinarith
    exact h2t.trans hNsq
  omega

/-- Every graph with `alonEdgeCount t` edges has an integral excess of at
least `t` above the exact Edwards baseline. -/
theorem guarantees_alonEdgeCount (t : ℕ) (ht : 1 ≤ t) :
    Guarantees (alonEdgeCount t) t := by
  intro V _ G hG
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hGcard : #G.edgeFinset = alonEdgeCount t := by
    calc
      #G.edgeFinset = G.edgeSet.ncard := by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
      _ = alonEdgeCount t := hG
  have hedges : 2 * #G.edgeFinset = (2 ^ 20 * t ^ 2) ^ 2 := by
    rw [hGcard, two_mul_alonEdgeCount]
    rfl
  obtain ⟨H, instH, hHG, hHbip, hcut⟩ := explicit_alon_cut ht G hedges
  letI : DecidableRel H.Adj := instH
  have hHcard : H.edgeSet.ncard = #H.edgeFinset := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcutNat :
      2 * alonEdgeCount t + alonParameter t + 4 * t ≤ 4 * #H.edgeFinset := by
    simpa only [hGcard, alonParameter] using hcut
  have hcutReal :
      2 * (alonEdgeCount t : ℝ) + (alonParameter t : ℝ) + 4 * (t : ℝ) ≤
        4 * (#H.edgeFinset : ℝ) := by
    exact_mod_cast hcutNat
  have hexplicit :
      (alonEdgeCount t : ℝ) / 2 + (alonParameter t : ℝ) / 4 + t ≤
        (#H.edgeFinset : ℝ) := by
    linarith
  have hmEq :
      2 * (alonEdgeCount t : ℝ) = (alonParameter t : ℝ) ^ 2 := by
    exact_mod_cast two_mul_alonEdgeCount t
  have hsqrt :
      Real.sqrt (8 * (alonEdgeCount t : ℝ) + 1) ≤ 2 * alonParameter t + 1 := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 2 * alonParameter t + 1)]
    nlinarith
  have hbaseline :
      baseline (alonEdgeCount t) + t ≤
        (alonEdgeCount t : ℝ) / 2 + (alonParameter t : ℝ) / 4 + t := by
    unfold baseline
    linarith
  refine ⟨H, hHG, hHbip, ?_⟩
  rw [hHcard]
  exact hbaseline.trans hexplicit

/-- Alon's explicit quantitative lower bound for the correction function. -/
theorem alon_correction_lower_bound (t : ℕ) (ht : 1 ≤ t) :
    t ≤ correction (alonEdgeCount t) :=
  le_correction_of_guarantees (guarantees_alonEdgeCount t ht)

/-- **Erdős Problem 127 (Alon).** There is a sequence of edge counts tending
to infinity along which the integral correction above the Edwards baseline
also tends to infinity. -/
theorem erdos_127 :
    ∃ mseq : ℕ → ℕ, Tendsto mseq atTop atTop ∧
      Tendsto (fun i ↦ correction (mseq i)) atTop atTop := by
  let mseq : ℕ → ℕ := fun i ↦ alonEdgeCount (i + 1)
  refine ⟨mseq, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro i hi
    have him : i + 1 ≤ mseq i := by
      exact parameter_le_edgeCount (i + 1) (by omega)
    omega
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro i hi
    have hic : i + 1 ≤ correction (mseq i) := by
      exact alon_correction_lower_bound (i + 1) (by omega)
    omega

end

#print axioms erdos_127
-- 'Erdos127.erdos_127' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos127
