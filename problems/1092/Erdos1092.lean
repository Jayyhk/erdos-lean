import Mathlib

namespace Erdos1092

/-
# Erdős Problem 1092

Let $f_r(n)$ be maximal such that, if a graph $G$ has the property that every subgraph $H$ on $m$
vertices is the union of a graph with chromatic number $\leq r$ and a graph with $\leq f_r(m)$
edges, then $G$ has chromatic number $\leq r+1$. Is it true that $f_2(n) \gg n$? More generally,
is $f_r(n)\gg_r n$?

The answer is **no**, for every $r \geq 2$: Rödl [Ro82] constructed graphs of arbitrarily large
chromatic number in which every subgraph on $m$ vertices becomes bipartite after deleting at most
$\epsilon m$ edges, and joining a clique on $r - 2$ vertices extends this to every $r$.
`IsAdmissible r g` is the hypothesis of the problem with budget $g$, imposed on every subgraph $H$
at its own vertex count, as in `formal-conjectures`; since a function below an admissible one is
admissible, $f_r(n) \gg n$ says that some admissible $g$ has $n = O(g(n))$, and `erdos_1092`
shows that none does.

Formalised by `Wang060919` in `Wang060919/erdos1092-lean`, with a self-contained finite
construction; the seven modules forming the closure of `erdos_1092` are flattened here in
dependency order, and the three corollaries after it upstream (`erdos_1092_all`,
`f_asymptotic_2`, `f_asymptotic_general`) are omitted so that `erdos_1092` is the last
declaration.

Declarations that `erdos_1092` does not depend on have been removed.
-/

/-! ### Upstream module `Erdos1092/Basic.lean` -/

/-- Ordinary vertices have a layer and a cyclic coordinate; the right summand is the apex. -/
abbrev Vertex (R t : ℕ) := (Fin R × ZMod t) ⊕ Unit

def cycleAdj {t : ℕ} (a b : ZMod t) : Prop :=
  a ≠ b ∧ (b = a + 1 ∨ a = b + 1)

lemma cycleAdj_symm {t : ℕ} {a b : ZMod t} (h : cycleAdj a b) : cycleAdj b a :=
  ⟨h.1.symm, h.2.symm⟩

def MycAdj (R t : ℕ) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i, a), Sum.inl (j, b) =>
      cycleAdj a b ∧ ((i.val = 0 ∧ j.val = 0) ∨
        j.val = i.val + 1 ∨ i.val = j.val + 1)
  | Sum.inl (i, _), Sum.inr _ => i.val + 1 = R
  | Sum.inr _, Sum.inl (i, _) => i.val + 1 = R
  | Sum.inr _, Sum.inr _ => False

def mycGraph (R t : ℕ) : SimpleGraph (Vertex R t) where
  Adj := MycAdj R t
  symm := by
    constructor
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact ⟨cycleAdj_symm h.1, h.2.elim
          (fun h0 => Or.inl ⟨h0.2, h0.1⟩)
          (fun hs => Or.inr hs.symm)⟩
      | inr b => exact h
    | inr a =>
      cases b with
      | inl b => exact h
      | inr b => exact h
  loopless := by
    constructor
    intro a h
    cases a with
    | inl a => exact h.1.1 rfl
    | inr a => exact h

open scoped Classical in
/-- A budget bound for every missing-edge subgraph whose incident vertices lie in `S`.
This support formulation avoids losing non-induced subgraphs or charging isolated vertices
outside `S`; it will be bridged to the original `Subgraph` formulation. -/
def LocalCutBound {V : Type*} [Fintype V] [DecidableEq V]
    (ε : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ (H : SimpleGraph V), H ≤ G → ∀ S : Finset V,
    (∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) →
    ∃ E : Finset (Sym2 V), E ⊆ H.edgeFinset ∧
      (E.card : ℝ) ≤ ε * S.card ∧ (H.deleteEdges E).Colorable 2

/-! ### Upstream module `Erdos1092/Winding.lean` -/

section
open _root_.SimpleGraph
def colorDelta (a b : Fin 3) : ℤ :=
  if b.val = (a.val + 1) % 3 then 1 else -1

lemma colorDelta_reverse {a b : Fin 3} (h : a ≠ b) :
    colorDelta b a = -colorDelta a b := by
  fin_cases a <;> fin_cases b <;> norm_num [colorDelta] at *

lemma colorDelta_mod_two (a b : Fin 3) : colorDelta a b % 2 = 1 := by
  unfold colorDelta
  split <;> norm_num

/-- This concerns closed walks, so no distinctness of opposite vertices is needed. -/
lemma colorDelta_closed_four {a b c d : Fin 3}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    colorDelta a b + colorDelta b c + colorDelta c d + colorDelta d a = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [colorDelta] at *

section Cyclic

variable {t : ℕ} [NeZero t]

lemma cyclic_sum_add_one (f : ZMod t → ℤ) :
    (∑ i, f (i + 1)) = ∑ i, f i := by
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod t)) _ f (fun _ => rfl)

lemma cyclic_sum_sub_one (f : ZMod t → ℤ) :
    (∑ i, f (i - 1)) = ∑ i, f i := by
  simpa [sub_eq_add_neg] using
    Fintype.sum_equiv (Equiv.addRight (-1 : ZMod t)) (fun i => f (i + -1)) f (fun _ => rfl)

def forwardDelta (c : ℕ → ZMod t → Fin 3) (j : ℕ) (i : ZMod t) : ℤ :=
  colorDelta (c j i) (c (j + 1) (i + 1))

def backwardDelta (c : ℕ → ZMod t → Fin 3) (j : ℕ) (i : ZMod t) : ℤ :=
  colorDelta (c j i) (c (j + 1) (i - 1))

def layerWinding (c : ℕ → ZMod t → Fin 3) (j : ℕ) : ℤ :=
  ∑ i, (forwardDelta c j i - backwardDelta c j i)

def baseWinding (c : ℕ → ZMod t → Fin 3) : ℤ :=
  ∑ i, colorDelta (c 0 i) (c 0 (i + 1))

lemma baseWinding_odd (c : ℕ → ZMod t → Fin 3) (ht : Odd t) :
    Odd (baseWinding c) := by
  apply Int.odd_iff.mpr
  unfold baseWinding
  rw [Finset.sum_int_mod]
  simp only [colorDelta_mod_two]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rcases ht with ⟨k, hk⟩
  omega

lemma base_layer_winding (c : ℕ → ZMod t → Fin 3)
    (hbase : ∀ i, c 0 i ≠ c 0 (i + 1))
    (hfwd : ∀ i, c 0 i ≠ c 1 (i + 1))
    (hbwd : ∀ i, c 0 i ≠ c 1 (i - 1)) :
    layerWinding c 0 = 2 * baseWinding c := by
  have hpoint (i : ZMod t) :
      colorDelta (c 0 i) (c 0 (i + 1)) +
        colorDelta (c 0 (i - 1)) (c 0 i) +
        backwardDelta c 0 (i + 1) - forwardDelta c 0 (i - 1) = 0 := by
    have h := colorDelta_closed_four (hbase i) (by simpa using hbwd (i + 1))
      (by simpa using (hfwd (i - 1)).symm) (by simpa using hbase (i - 1))
    have hrev : colorDelta (c 1 i) (c 0 (i - 1)) =
        -colorDelta (c 0 (i - 1)) (c 1 i) :=
      colorDelta_reverse (by simpa using hfwd (i - 1))
    rw [hrev] at h
    simpa [forwardDelta, backwardDelta, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one, cyclic_sum_sub_one] at hsum
  have hshift : (∑ i : ZMod t, colorDelta (c 0 (i - 1)) (c 0 i)) = baseWinding c := by
    simpa [baseWinding] using
      cyclic_sum_sub_one (fun i : ZMod t => colorDelta (c 0 i) (c 0 (i + 1)))
  rw [hshift] at hsum
  unfold baseWinding at hsum
  unfold layerWinding baseWinding
  rw [Finset.sum_sub_distrib]
  linarith

lemma successive_layer_winding (c : ℕ → ZMod t → Fin 3) (j : ℕ)
    (hfwd : ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ i, c j i ≠ c (j + 1) (i - 1))
    (hfwd' : ∀ i, c (j + 1) i ≠ c (j + 2) (i + 1))
    (hbwd' : ∀ i, c (j + 1) i ≠ c (j + 2) (i - 1)) :
    layerWinding c j = layerWinding c (j + 1) := by
  have hpoint (i : ZMod t) :
      forwardDelta c j i + backwardDelta c (j + 1) (i + 1) -
        forwardDelta c (j + 1) (i - 1) - backwardDelta c j i = 0 := by
    have h := colorDelta_closed_four (hfwd i) (by simpa using hbwd' (i + 1))
      (by simpa using (hfwd' (i - 1)).symm) (hbwd i).symm
    have hrev : colorDelta (c (j + 2) i) (c (j + 1) (i - 1)) =
        -colorDelta (c (j + 1) (i - 1)) (c (j + 2) i) :=
      colorDelta_reverse (by simpa using hfwd' (i - 1))
    rw [hrev, colorDelta_reverse (hbwd i)] at h
    simpa [forwardDelta, backwardDelta, Nat.add_assoc, sub_eq_add_neg] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one, cyclic_sum_sub_one] at hsum
  simp only [layerWinding, Finset.sum_sub_distrib]
  linarith

lemma top_layer_winding (c : ℕ → ZMod t → Fin 3) (j : ℕ) (apex : Fin 3)
    (hfwd : ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ i, c j i ≠ c (j + 1) (i - 1))
    (htop : ∀ i, c (j + 1) i ≠ apex) :
    layerWinding c j = 0 := by
  have hpoint (i : ZMod t) :
      forwardDelta c j i + colorDelta (c (j + 1) (i + 1)) apex -
        colorDelta (c (j + 1) (i - 1)) apex - backwardDelta c j i = 0 := by
    have h := colorDelta_closed_four (hfwd i) (htop (i + 1))
      (htop (i - 1)).symm (hbwd i).symm
    rw [colorDelta_reverse (htop (i - 1)), colorDelta_reverse (hbwd i)] at h
    simpa [forwardDelta, backwardDelta, sub_eq_add_neg] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one (fun i => colorDelta (c (j + 1) i) apex),
    cyclic_sum_sub_one (fun i => colorDelta (c (j + 1) i) apex)] at hsum
  simp only [layerWinding, Finset.sum_sub_distrib]
  linarith

lemma winding_contradiction (R : ℕ) (hR : 2 ≤ R) (htOdd : Odd t)
    (c : ℕ → ZMod t → Fin 3) (apex : Fin 3)
    (hbase : ∀ i, c 0 i ≠ c 0 (i + 1))
    (hfwd : ∀ j, j + 1 < R → ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ j, j + 1 < R → ∀ i, c j i ≠ c (j + 1) (i - 1))
    (htop : ∀ i, c (R - 1) i ≠ apex) : False := by
  have heq (j : ℕ) (hj : j + 1 < R) : layerWinding c j = layerWinding c 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj' : j + 1 < R := by omega
      exact (successive_layer_winding c j (hfwd j hj') (hbwd j hj')
        (hfwd (j + 1) hj) (hbwd (j + 1) hj)).symm.trans (ih hj')
  have hj : R - 2 + 1 < R := by omega
  have htop' : ∀ i, c (R - 2 + 1) i ≠ apex := by
    simpa only [show R - 2 + 1 = R - 1 by omega] using htop
  have hzero := top_layer_winding c (R - 2) apex (hfwd _ hj) (hbwd _ hj) htop'
  rw [heq _ hj, base_layer_winding c hbase (hfwd 0 (by omega))
    (hbwd 0 (by omega))] at hzero
  have hwzero : baseWinding c = 0 := by omega
  have hodd := baseWinding_odd c htOdd
  rw [hwzero] at hodd
  norm_num at hodd

end Cyclic

lemma cycleAdj_next {t : ℕ} (ht : 3 ≤ t) (i : ZMod t) :
    cycleAdj i (i + 1) := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  have h' : i + 0 = i + (1 : ZMod t) := by simpa using h
  have hone : (1 : ZMod t) = 0 := (add_left_cancel h').symm
  have := ZMod.one_eq_zero_iff.mp hone
  omega

lemma cycleAdj_prev {t : ℕ} (ht : 3 ≤ t) (i : ZMod t) :
    cycleAdj i (i - 1) := by
  refine ⟨?_, Or.inr (sub_add_cancel i 1).symm⟩
  intro h
  have h' : i + 0 = i + (-1 : ZMod t) := by simpa [sub_eq_add_neg] using h
  have hone : (1 : ZMod t) = 0 := neg_eq_zero.mp (add_left_cancel h').symm
  have := ZMod.one_eq_zero_iff.mp hone
  omega

/-- The actual generalized Mycielski graph of an odd cycle needs four colors.
All hypotheses are the construction's original integer parameter conditions. -/
theorem mycGraph_not_colorable_three (R t : ℕ) [NeZero t]
    (hR : 2 ≤ R) (ht : 3 ≤ t) (htOdd : Odd t) :
    ¬(mycGraph R t).Colorable 3 := by
  rintro ⟨C⟩
  let c (j : ℕ) (i : ZMod t) : Fin 3 :=
    if hj : j < R then C (Sum.inl (⟨j, hj⟩, i)) else 0
  have hbase (i : ZMod t) : c 0 i ≠ c 0 (i + 1) := by
    have h0 : 0 < R := by omega
    dsimp only [c]
    simp only [dif_pos h0]
    apply C.valid
    exact ⟨cycleAdj_next ht i, Or.inl ⟨rfl, rfl⟩⟩
  have hfwd (j : ℕ) (hj : j + 1 < R) (i : ZMod t) :
      c j i ≠ c (j + 1) (i + 1) := by
    have hj0 : j < R := by omega
    dsimp only [c]
    simp only [dif_pos hj0, dif_pos hj]
    apply C.valid
    exact ⟨cycleAdj_next ht i, Or.inr (Or.inl rfl)⟩
  have hbwd (j : ℕ) (hj : j + 1 < R) (i : ZMod t) :
      c j i ≠ c (j + 1) (i - 1) := by
    have hj0 : j < R := by omega
    dsimp only [c]
    simp only [dif_pos hj0, dif_pos hj]
    apply C.valid
    exact ⟨cycleAdj_prev ht i, Or.inr (Or.inl rfl)⟩
  have htop (i : ZMod t) : c (R - 1) i ≠ C (Sum.inr ()) := by
    have hj : R - 1 < R := by omega
    dsimp only [c]
    simp only [dif_pos hj]
    apply C.valid
    show R - 1 + 1 = R
    omega
  exact winding_contradiction R hR htOdd c (C (Sum.inr ())) hbase hfwd hbwd htop

end

/-! ### Upstream module `Erdos1092/Cuts.lean` -/

section
open _root_.SimpleGraph _root_.Finset
open scoped BigOperators Classical

/-- The ordinary part of an arbitrary missing-edge subgraph. -/
def ordinaryPart {R t : ℕ} (H : SimpleGraph (Vertex R t)) : SimpleGraph (Vertex R t) where
  Adj u v := H.Adj u v ∧ u.isLeft ∧ v.isLeft
  symm := by constructor; intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by constructor; intro u h; exact H.irrefl h.1

/-- At most two levels can supply an ordinary neighbor. -/
lemma neighborLevel_count {R : ℕ} (i : Fin R) :
    (univ.filter fun j : Fin R =>
      (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1).card ≤ 2 := by
  classical
  let A := univ.filter fun j : Fin R =>
    (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1
  have hinj : Set.InjOn (fun j : Fin R => j.val) A := by
    intro a ha b hb hab
    exact Fin.ext hab
  have hsub : A.image (fun j => j.val) ⊆ {if i.val = 0 then 0 else i.val - 1, i.val + 1} := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hh := (mem_filter.mp hj).2
    rcases hh with hh | hh | hh
    · simp [hh.1, hh.2]
    · simp [hh]
    · have hi : i.val ≠ 0 := by omega
      simp [hi, show j.val = i.val - 1 by omega]
  have hc : (A.image (fun j => j.val)).card ≤ 2 :=
    (card_le_card hsub).trans card_le_two
  rwa [card_image_of_injOn hinj] at hc

lemma ordinaryPart_degree_le_four {R t : ℕ} [NeZero t]
    (H : SimpleGraph (Vertex R t)) (hH : H ≤ mycGraph R t) (u : Vertex R t) :
    (ordinaryPart H).degree u ≤ 4 := by
  classical
  cases u with
  | inr z =>
      have hzero : (ordinaryPart H).neighborFinset (Sum.inr z) = ∅ := by
        ext v
        rw [mem_neighborFinset]
        simp [ordinaryPart]
      rw [← card_neighborFinset_eq_degree, hzero]
      simp
  | inl p =>
      rcases p with ⟨i, a⟩
      let L := univ.filter fun j : Fin R =>
        (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1
      let C : Finset (ZMod t) := {a + 1, a - 1}
      have hsub : (ordinaryPart H).neighborFinset (Sum.inl (i,a)) ⊆
          (L ×ˢ C).image Sum.inl := by
        intro v hv
        have hh : H.Adj (Sum.inl (i,a)) v ∧ (Sum.inl (i,a) : Vertex R t).isLeft ∧ v.isLeft :=
          ((mem_neighborFinset _ _ _).mp hv)
        cases v with
        | inr z => simp at hh
        | inl p =>
          rcases p with ⟨j,b⟩
          have hg : cycleAdj a b ∧
              ((i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1) := hH hh.1
          apply mem_image.mpr
          refine ⟨(j,b), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hg.2⟩, ?_⟩,rfl⟩
          rcases hg.1.2 with hb | hb
          · simp [C,hb]
          · have hb' : b = a - 1 := by rw [hb]; abel
            simp [C,hb']
      have hL : L.card ≤ 2 := neighborLevel_count i
      have hC : C.card ≤ 2 := card_le_two
      rw [← card_neighborFinset_eq_degree]
      calc
        _ ≤ ((L ×ˢ C).image Sum.inl).card := card_le_card hsub
        _ ≤ (L ×ˢ C).card := card_image_le
        _ = L.card * C.card := card_product _ _
        _ ≤ 4 := by nlinarith

lemma ordinaryPart_card_edges_le {R t : ℕ} [NeZero t]
    (H : SimpleGraph (Vertex R t)) (hH : H ≤ mycGraph R t)
    (S : Finset (Vertex R t))
    (hS : ∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) :
    (ordinaryPart H).edgeFinset.card ≤ 2 * S.card := by
  classical
  have hs : ∑ u, (ordinaryPart H).degree u = ∑ u ∈ S, (ordinaryPart H).degree u := by
    symm
    apply sum_subset (subset_univ S)
    intro u hu hnot
    rw [degree_eq_zero]
    intro v hv
    exact hnot (hS hv.1).1
  have hd : ∑ u ∈ S, (ordinaryPart H).degree u ≤ S.card * 4 := by
    calc
      _ ≤ ∑ _u ∈ S, 4 := sum_le_sum fun u hu => ordinaryPart_degree_le_four H hH u
      _ = S.card * 4 := by simp
  rw [← hs, sum_degrees_eq_twice_card_edges] at hd
  omega

/-- Averaging in its division-free form, usable for an arbitrary finite partition of edges. -/
lemma exists_small_fiber {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    (E : Finset β) (p : α → β → Prop) [∀ a, DecidablePred (p a)]
    (huniq : ∀ e ∈ E, ∀ a b, p a e → p b e → a = b) :
    ∃ a, Fintype.card α * (E.filter (p a)).card ≤ E.card := by
  classical
  have hsum : ∑ a : α, (E.filter (p a)).card ≤ E.card := by
    have heq : ∀ a : α, (E.filter (p a)).card = ∑ e ∈ E, if p a e then 1 else 0 := by
      intro a
      simp only [card_eq_sum_ones, sum_filter]
    simp_rw [heq]
    rw [sum_comm]
    calc
      _ ≤ ∑ _e ∈ E, 1 := by
        apply sum_le_sum
        intro e he
        by_cases hex : ∃ a, p a e
        · obtain ⟨a, ha⟩ := hex
          have hp : ∀ b, p b e ↔ b = a := by
            intro b
            exact ⟨fun hb => huniq e he b a hb ha, fun hb => hb ▸ ha⟩
          simp [hp]
        · simp only [not_exists] at hex
          simp [hex]
      _ = E.card := by simp
  by_contra hnot
  push Not at hnot
  have hgt : E.card * Fintype.card α <
      (∑ a : α, (E.filter (p a)).card) * Fintype.card α := by
    calc
      _ = ∑ _a : α, E.card := by simp [mul_comm]
      _ < ∑ a : α, Fintype.card α * (E.filter (p a)).card :=
        sum_lt_sum_of_nonempty univ_nonempty fun a _ => hnot a
      _ = _ := by rw [← mul_sum, mul_comm]
  have hc : 0 < Fintype.card α := Fintype.card_pos
  nlinarith

/-- Successive positions on a cut-open modular cycle have opposite parity. -/
lemma zmod_parity_next {t : ℕ} [NeZero t] (ht : 3 ≤ t) (a : ZMod t)
    (ha : a + 1 ≠ 0) : a.val % 2 ≠ (a + 1).val % 2 := by
  have hone : (1 : ZMod t).val = 1 := ZMod.val_one'' (by omega)
  have hav := ZMod.val_lt a
  have hlt : a.val + 1 < t := by
    by_contra hn
    have he : a.val + 1 = t := by omega
    have hz : (a + 1).val = 0 := by rw [ZMod.val_add, hone, he]; simp
    exact ha ((ZMod.val_eq_zero _).mp hz)
  rw [ZMod.val_add, hone, Nat.mod_eq_of_lt hlt]
  omega

/-- Cut edges crossing a specified positive height. -/
def heightRel {R t : ℕ} (h : ℕ) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i,_), Sum.inl (j,_) =>
      (i.val < h ∧ h ≤ j.val) ∨ (j.val < h ∧ h ≤ i.val)
  | _, _ => False

lemma heightRel_symm {R t : ℕ} (h : ℕ) (u v : Vertex R t) :
    heightRel h u v ↔ heightRel h v u := by
  cases u <;> cases v <;> simp [heightRel, or_comm]

def heightEdge {R t : ℕ} (h : ℕ) : Sym2 (Vertex R t) → Prop :=
  Sym2.lift ⟨heightRel h, fun u v => propext (heightRel_symm h u v)⟩

lemma heightEdge_unique {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (hH : H ≤ mycGraph R t) (e : Sym2 (Vertex R t)) (he : e ∈ H.edgeFinset)
    (a b : Fin (R-1)) (ha : heightEdge (a.val+1) e) (hb : heightEdge (b.val+1) e) : a = b := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hh : (mycGraph R t).Adj u v := hH (by simpa only [mem_edgeFinset,mem_edgeSet] using he)
      cases u with
      | inr z => cases v <;> simp [heightEdge,heightRel,Sym2.lift_mk] at ha
      | inl p =>
          cases v with
          | inr z => simp [heightEdge,heightRel,Sym2.lift_mk] at ha
          | inl q =>
              rcases p with ⟨i,x⟩
              rcases q with ⟨j,y⟩
              change cycleAdj x y ∧ ((i.val = 0 ∧ j.val = 0) ∨ j.val = i.val+1 ∨ i.val = j.val+1) at hh
              change (i.val < a.val+1 ∧ a.val+1 ≤ j.val) ∨ (j.val < a.val+1 ∧ a.val+1 ≤ i.val) at ha
              change (i.val < b.val+1 ∧ b.val+1 ≤ j.val) ∨ (j.val < b.val+1 ∧ b.val+1 ≤ i.val) at hb
              apply Fin.ext
              rcases hh.2 with hh | hh | hh <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- Below-height edges at the chosen seam of the index cycle. -/
def seamRel {R t : ℕ} (h : ℕ) (s : ZMod t) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i,a), Sum.inl (j,b) =>
      i.val < h ∧ j.val < h ∧ ((a = s ∧ b = s+1) ∨ (b = s ∧ a = s+1))
  | _, _ => False

lemma seamRel_symm {R t : ℕ} (h : ℕ) (s : ZMod t) (u v : Vertex R t) :
    seamRel h s u v ↔ seamRel h s v u := by
  cases u <;> cases v <;> simp [seamRel, and_left_comm, or_comm]

def seamEdge {R t : ℕ} (h : ℕ) (s : ZMod t) : Sym2 (Vertex R t) → Prop :=
  Sym2.lift ⟨seamRel h s, fun u v => propext (seamRel_symm h s u v)⟩

lemma two_ne_zero {t : ℕ} (ht : 3 ≤ t) : (2 : ZMod t) ≠ 0 := by
  intro hz
  have hd : t ∣ 2 := (ZMod.natCast_eq_zero_iff 2 t).mp hz
  have := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

lemma seamEdge_unique {R t : ℕ} (ht : 3 ≤ t)
    (e : Sym2 (Vertex R t)) (h : ℕ) (a b : ZMod t)
    (ha : seamEdge h a e) (hb : seamEdge h b e) : a = b := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      cases u with
      | inr z => cases v <;> simp [seamEdge,seamRel,Sym2.lift_mk] at ha
      | inl p =>
          cases v with
          | inr z => simp [seamEdge,seamRel,Sym2.lift_mk] at ha
          | inl q =>
              rcases p with ⟨i,x⟩
              rcases q with ⟨j,y⟩
              change i.val < h ∧ j.val < h ∧ ((x=a ∧ y=a+1) ∨ (y=a ∧ x=a+1)) at ha
              change i.val < h ∧ j.val < h ∧ ((x=b ∧ y=b+1) ∨ (y=b ∧ x=b+1)) at hb
              rcases ha.2.2 with ha | ha <;> rcases hb.2.2 with hb | hb
              · exact ha.1.symm.trans hb.1
              · have hz : (2 : ZMod t) = 0 := by
                  linear_combination ha.1 - ha.2 - hb.2 + hb.1
                exact False.elim (two_ne_zero ht hz)
              · have hz : (2 : ZMod t) = 0 := by
                  linear_combination ha.1 - ha.2 - hb.2 + hb.1
                exact False.elim (two_ne_zero ht hz)
              · exact ha.1.symm.trans hb.1

/-- Two colors, using index parity below the height and layer parity above it. -/
def cutColor {R t : ℕ} [NeZero t] (h : ℕ) (s : ZMod t) : Vertex R t → Fin 2
  | Sum.inl (i,a) => if i.val < h then ⟨(a-(s+1)).val % 2, Nat.mod_lt _ (by omega)⟩
      else ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
  | Sum.inr _ => ⟨R % 2, Nat.mod_lt _ (by omega)⟩

lemma cycle_parity {t : ℕ} [NeZero t] (ht : 3 ≤ t) (s a b : ZMod t)
    (hab : cycleAdj a b)
    (hseam : ¬ ((a=s ∧ b=s+1) ∨ (b=s ∧ a=s+1))) :
    (a-(s+1)).val % 2 ≠ (b-(s+1)).val % 2 := by
  rcases hab.2 with hb | ha
  · have hne : (a-(s+1))+1 ≠ 0 := by
      intro hz
      have he : a=s := by linear_combination hz
      exact hseam (Or.inl ⟨he, by simpa [he] using hb⟩)
    have hh := zmod_parity_next ht (a-(s+1)) hne
    have he : b-(s+1) = (a-(s+1))+1 := by rw [hb]; abel
    rw [he]
    exact hh
  · have hne : (b-(s+1))+1 ≠ 0 := by
      intro hz
      have he : b=s := by linear_combination hz
      exact hseam (Or.inr ⟨he, by simpa [he] using ha⟩)
    have hh := zmod_parity_next ht (b-(s+1)) hne
    have he : a-(s+1) = (b-(s+1))+1 := by rw [ha]; abel
    rw [he]
    exact hh.symm

lemma cutColor_valid {R t : ℕ} [NeZero t] (ht : 3 ≤ t)
    (h : ℕ) (hpos : 1 ≤ h) (hR : h < R) (s : ZMod t)
    (u v : Vertex R t) (huv : (mycGraph R t).Adj u v)
    (hh : ¬heightRel h u v) (hs : ¬seamRel h s u v) :
    cutColor h s u ≠ cutColor h s v := by
  cases u with
  | inl p =>
      rcases p with ⟨i,a⟩
      cases v with
      | inl q =>
          rcases q with ⟨j,b⟩
          change cycleAdj a b ∧ ((i.val=0 ∧ j.val=0) ∨ j.val=i.val+1 ∨ i.val=j.val+1) at huv
          by_cases hi : i.val < h
          · have hj : j.val < h := by
              by_contra hj
              exact hh (Or.inl ⟨hi, by omega⟩)
            have hp := cycle_parity ht s a b huv.1 (fun hn => hs ⟨hi,hj,hn⟩)
            simpa [cutColor,hi,hj,Fin.ext_iff] using hp
          · have hj : ¬j.val < h := by
              intro hj
              exact hh (Or.inr ⟨hj, by omega⟩)
            have hp : i.val % 2 ≠ j.val % 2 := by
              rcases huv.2 with hb | hb | hb <;> omega
            simpa [cutColor,hi,hj,Fin.ext_iff] using hp
      | inr z =>
          change i.val+1=R at huv
          have hi : ¬i.val < h := by omega
          have hp : i.val % 2 ≠ R % 2 := by omega
          simpa [cutColor,hi,Fin.ext_iff] using hp
  | inr z =>
      cases v with
      | inr w => exact False.elim huv
      | inl p =>
          rcases p with ⟨i,a⟩
          change i.val+1=R at huv
          have hi : ¬i.val < h := by omega
          have hp : R % 2 ≠ i.val % 2 := by omega
          simpa [cutColor,hi,Fin.ext_iff] using hp

lemma mem_ordinary_height {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (h : ℕ) (u v : Vertex R t) (huv : H.Adj u v) (hh : heightRel h u v) :
    s(u,v) ∈ (ordinaryPart H).edgeFinset := by
  classical
  rw [mem_edgeFinset, mem_edgeSet]
  cases u <;> cases v <;> simp_all [heightRel, ordinaryPart]

lemma mem_ordinary_seam {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (h : ℕ) (a : ZMod t) (u v : Vertex R t) (huv : H.Adj u v) (hh : seamRel h a u v) :
    s(u,v) ∈ (ordinaryPart H).edgeFinset := by
  classical
  rw [mem_edgeFinset, mem_edgeSet]
  cases u <;> cases v <;> simp_all [seamRel, ordinaryPart]

/-- All non-induced subgraphs admit the two-cut budget, uniformly in their support size. -/
theorem mycGraph_localCutBound (R t : ℕ) [NeZero t] (hR : 2 ≤ R) (ht : 3 ≤ t) :
    LocalCutBound (2/(R-1 : ℝ) + 2/(t : ℝ)) (mycGraph R t) := by
  classical
  intro H hH S hS
  let O := (ordinaryPart H).edgeFinset
  have ho : O.card ≤ 2*S.card := ordinaryPart_card_edges_le H hH S hS
  have hO : ordinaryPart H ≤ mycGraph R t := fun u v huv => hH huv.1
  let : Nonempty (Fin (R-1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a,ha⟩ := exists_small_fiber O
    (fun a : Fin (R-1) => heightEdge (a.val+1))
    (fun e he a b h1 h2 => heightEdge_unique (ordinaryPart H) hO e he a b h1 h2)
  let h := a.val+1
  have hpos : 1 ≤ h := by omega
  have hlt : h < R := by have := a.isLt; omega
  let A := O.filter (heightEdge h)
  have hAc : (R-1)*A.card ≤ 2*S.card := by
    simpa [A,h,Fintype.card_fin] using ha.trans ho
  obtain ⟨b,hb⟩ := exists_small_fiber O (fun b : ZMod t => seamEdge h b)
    (fun e _ a b h1 h2 => seamEdge_unique ht e h a b h1 h2)
  let B := O.filter (seamEdge h b)
  have hBc : t*B.card ≤ 2*S.card := by
    simpa [B,ZMod.card] using hb.trans ho
  have hsubO : O ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hh : (ordinaryPart H).Adj u v := by simpa [O,mem_edgeFinset,mem_edgeSet] using he
        simpa [mem_edgeFinset,mem_edgeSet] using hh.1
  refine ⟨A ∪ B, union_subset (Subset.trans (filter_subset _ _) hsubO)
    (Subset.trans (filter_subset _ _) hsubO), ?_, ?_⟩
  · have hr : (0 : ℝ) < (R-1 : ℕ) := by exact_mod_cast (show 0 < R-1 by omega)
    have htr : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hac : (A.card : ℝ) ≤ 2/(R-1 : ℝ)*S.card := by
      have hc : ((R-1 : ℕ) : ℝ)*A.card ≤ 2*S.card := by exact_mod_cast hAc
      have he : ((R-1 : ℕ) : ℝ) = (R-1 : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [he] at hc hr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hr).mpr
      nlinarith
    have hbc : (B.card : ℝ) ≤ 2/(t : ℝ)*S.card := by
      have hc : (t : ℝ)*B.card ≤ 2*S.card := by exact_mod_cast hBc
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ htr).mpr
      nlinarith
    have hcard : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ)+B.card := by exact_mod_cast card_union_le A B
    nlinarith
  · refine ⟨⟨cutColor h b, ?_⟩⟩
    intro u v huv
    have hdel := deleteEdges_adj.mp huv
    apply cutColor_valid ht h hpos hlt b u v (hH hdel.1)
    · intro hh
      apply hdel.2
      apply mem_union_left
      apply mem_filter.mpr
      exact ⟨mem_ordinary_height H h u v hdel.1 hh,hh⟩
    · intro hh
      apply hdel.2
      apply mem_union_right
      apply mem_filter.mpr
      exact ⟨mem_ordinary_seam H h b u v hdel.1 hh,hh⟩

end

/-! ### Upstream module `Erdos1092/Outer.lean` -/

section
open _root_.SimpleGraph _root_.Filter _root_.Asymptotics

open scoped Classical in
/-- The original assertion, including every non-induced subgraph and every vertex count. -/
def IsAdmissible (r : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ H : G.Subgraph,
      ∃ E : Finset (Sym2 H.verts),
        E ⊆ H.coe.edgeFinset ∧ E.card ≤ g (Fintype.card H.verts) ∧
        chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
    chromaticNumber G ≤ (r + 1 : ℕ∞)

/-- Join with a complete graph: all cross edges are present. -/
def cliqueJoin {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (V ⊕ Fin k) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inr v => u ≠ v
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> first | exact G.symm h | exact h.symm | trivial
  loopless := by
    constructor
    intro u h
    cases u
    · exact G.irrefl h
    · exact h rfl

/-- A clique uses `k` different colors, leaving only three for the original graph. -/
theorem cliqueJoin_not_colorable {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hG : ¬G.Colorable 3) : ¬(cliqueJoin G k).Colorable (3 + k) := by
  classical
  rintro ⟨C⟩
  let used : Finset (Fin (3 + k)) := Finset.univ.image (fun v : Fin k => C (.inr v))
  have hi : Function.Injective (fun v : Fin k => C (.inr v)) := by
    intro u v huv
    by_contra hne
    exact C.valid (show (cliqueJoin G k).Adj (.inr u) (.inr v) from hne) huv
  have hcard : used.card = k := by
    simp [used, Finset.card_image_of_injective _ hi]
  have havail : Fintype.card ↥usedᶜ ≤ 3 := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hcard]
    omega
  let D : G.Coloring ↥usedᶜ := Coloring.mk
    (fun v => ⟨C (.inl v), by
      simp only [Finset.mem_compl, used, Finset.mem_image, Finset.mem_univ, true_and,
        not_exists]
      intro u hu
      exact C.valid (show (cliqueJoin G k).Adj (.inl v) (.inr u) from True.intro) hu.symm⟩)
    (fun {u v} huv h => C.valid (show (cliqueJoin G k).Adj (.inl u) (.inl v) from huv)
      (congrArg Subtype.val h))
  exact hG (D.colorable.mono havail)

open scoped Classical in
/-- A support-sensitive deletion bound, allowing an arbitrary number of remaining colors. -/
def LocalColorCutBound {V : Type*} [Fintype V] [DecidableEq V]
    (ε : ℝ) (q : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ (H : SimpleGraph V), H ≤ G → ∀ S : Finset V,
    (∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) →
    ∃ E : Finset (Sym2 V), E ⊆ H.edgeFinset ∧
      (E.card : ℝ) ≤ ε * S.card ∧ (H.deleteEdges E).Colorable q

/-- The join requires only deleting edges in the original graph. -/
theorem cliqueJoin_localCut {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε : ℝ} (hε : 0 ≤ ε) (hG : LocalCutBound ε G) (k : ℕ) :
    LocalColorCutBound ε (2 + k) (cliqueJoin G k) := by
  classical
  intro H hH S hS
  let J := H.comap (Sum.inl : V → V ⊕ Fin k)
  let T := S.preimage (Sum.inl : V → V ⊕ Fin k) Sum.inl_injective.injOn
  have hJ : J ≤ G := fun u v huv => hH huv
  have hT : ∀ ⦃u v⦄, J.Adj u v → u ∈ T ∧ v ∈ T := by
    intro u v huv
    simpa [T, J] using hS huv
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG J hJ T hT
  let f : V ↪ V ⊕ Fin k := ⟨Sum.inl, Sum.inl_injective⟩
  let F := E.map f.sym2Map
  have hF : F ⊆ H.edgeFinset := by
    have hmap : ∀ a : Sym2 V, a ∈ E → f.sym2Map a ∈ H.edgeFinset := by
      refine Sym2.ind ?_
      intro u v ha
      have huv : J.Adj u v := by simpa using hE ha
      simpa [f, J] using huv
    intro a ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
    exact hba ▸ hmap b hb
  have hsize : T.card ≤ S.card := by
    dsimp [T]
    rw [Finset.card_preimage]
    exact Finset.card_filter_le _ _
  have hbound : (F.card : ℝ) ≤ ε * S.card := by
    calc
      (F.card : ℝ) = E.card := by simp [F]
      _ ≤ ε * T.card := hcard
      _ ≤ ε * S.card := mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) hε
  let D : (H.deleteEdges F).Coloring (Fin 2 ⊕ Fin k) := Coloring.mk
    (Sum.elim (fun v => Sum.inl (C v)) Sum.inr)
    (by
      intro u v huv
      obtain ⟨huv, hnot⟩ := (deleteEdges_adj).mp huv
      cases u with
      | inl u =>
        cases v with
        | inl v =>
          intro heq
          apply C.valid
            (show (J.deleteEdges E).Adj u v from deleteEdges_adj.mpr ⟨huv, by
              intro he
              apply hnot
              exact Finset.mem_map.mpr ⟨s(u,v), he, rfl⟩⟩)
          exact Sum.inl.inj heq
        | inr v => exact Sum.inl_ne_inr
      | inr u =>
        cases v with
        | inl v => exact Sum.inr_ne_inl
        | inr v =>
          intro heq
          exact (hH huv) (Sum.inr.inj heq))
  refine ⟨F, hF, hbound, ?_⟩
  simpa using D.colorable

/-- Relabeling vertices preserves the support-sensitive bound. -/
theorem localColorCut_comap_equiv {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {ε : ℝ} {q : ℕ}
    (hG : LocalColorCutBound ε q G) (e : W ≃ V) :
    LocalColorCutBound ε q (G.comap e) := by
  classical
  intro H hH S hS
  let J := H.comap e.symm
  have hJ : J ≤ G := by
    intro u v huv
    simpa using hH huv
  have hT : ∀ ⦃u v⦄, J.Adj u v → u ∈ S.image e ∧ v ∈ S.image e := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hS huv
    exact ⟨Finset.mem_image.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩,
      Finset.mem_image.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩⟩
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG J hJ (S.image e) hT
  let F := E.map e.symm.toEmbedding.sym2Map
  have hF : F ⊆ H.edgeFinset := by
    have hmap : ∀ a : Sym2 V, a ∈ E → e.symm.toEmbedding.sym2Map a ∈ H.edgeFinset := by
      refine Sym2.ind ?_
      intro u v ha
      simpa [J] using hE ha
    intro a ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
    exact hba ▸ hmap b hb
  refine ⟨F, hF, ?_, ?_⟩
  · simpa [F, Finset.card_image_of_injective _ e.injective] using hcard
  · refine ⟨Coloring.mk (fun v => C (e v)) ?_⟩
    intro u v huv
    apply C.valid
    obtain ⟨huv, hn⟩ := deleteEdges_adj.mp huv
    apply deleteEdges_adj.mpr
    refine ⟨by simpa [J] using huv, ?_⟩
    intro he
    apply hn
    apply Finset.mem_map.mpr
    refine ⟨s(e u, e v), he, ?_⟩
    simp

open scoped Classical in
/-- Restrict an ambient deletion set to the original subgraph's vertex subtype.
Isolated vertices stay in the vertex count, and edges need not be induced. -/
theorem localColorCut_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε : ℝ} {q : ℕ} (hG : LocalColorCutBound ε q G)
    (H : G.Subgraph) :
    ∃ E : Finset (Sym2 H.verts), E ⊆ H.coe.edgeFinset ∧
      (E.card : ℝ) ≤ ε * Fintype.card H.verts ∧ (H.coe.deleteEdges E).Colorable q := by
  classical
  have hs : ∀ ⦃u v⦄, H.spanningCoe.Adj u v →
      u ∈ H.verts.toFinset ∧ v ∈ H.verts.toFinset := by
    intro u v huv
    exact ⟨by simpa using H.edge_vert huv, by simpa using H.edge_vert (H.adj_symm huv)⟩
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG H.spanningCoe H.spanningCoe_le H.verts.toFinset hs
  let f : H.verts ↪ V := Function.Embedding.subtype _
  let F := E.preimage f.sym2Map f.sym2Map.injective.injOn
  have hF : F ⊆ H.coe.edgeFinset := by
    intro a ha
    have he : f.sym2Map a ∈ E := Finset.mem_preimage.mp ha
    have he' := hE he
    induction a using Sym2.ind with
    | _ u v => simpa [f] using he'
  have hle : F.card ≤ E.card := by
    simpa [F, Finset.card_preimage] using
      (Finset.card_filter_le E (fun v => v ∈ Set.range f.sym2Map))
  refine ⟨F, hF, ?_, ?_⟩
  · calc
      (F.card : ℝ) ≤ E.card := by exact_mod_cast hle
      _ ≤ ε * Fintype.card H.verts := by simpa using hcard
  · refine ⟨Coloring.mk (fun v => C v) ?_⟩
    intro u v huv
    apply C.valid
    obtain ⟨huv, hn⟩ := deleteEdges_adj.mp huv
    exact deleteEdges_adj.mpr ⟨huv, fun he => hn (Finset.mem_preimage.mpr he)⟩

/-- An eventually linear lower bound also absorbs the cuts at the finitely many small sizes:
their edge counts are integers and the chosen real bound is below one. -/
theorem exists_small_cut_budget {g : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hlinear : ∃ M : ℕ, ∀ m ≥ M, c * m ≤ (g m : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m a : ℕ, (a : ℝ) ≤ ε * m → a ≤ g m := by
  obtain ⟨M, hM⟩ := hlinear
  let ε : ℝ := min c (1 / ((M : ℝ) + 1))
  have hden : 0 < (M : ℝ) + 1 := by positivity
  have hε : 0 < ε := lt_min hc (one_div_pos.mpr hden)
  have hεc : ε ≤ c := min_le_left _ _
  have hεM : ε * ((M : ℝ) + 1) ≤ 1 := by
    calc
      ε * ((M : ℝ) + 1) ≤ (1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hden.le
      _ = 1 := by field_simp
  refine ⟨ε, hε, ?_⟩
  intro m a ha
  by_cases hm : M ≤ m
  · have := ha.trans ((mul_le_mul_of_nonneg_right hεc (Nat.cast_nonneg m)).trans (hM m hm))
    exact_mod_cast this
  · have hm' : (m : ℝ) < (M : ℝ) + 1 := by exact_mod_cast (show m < M + 1 by omega)
    have ha1 : (a : ℝ) < 1 := lt_of_le_of_lt ha
      ((mul_lt_mul_of_pos_left hm' hε).trans_le hεM)
    have : a < 1 := by exact_mod_cast ha1
    have : a = 0 := by omega
    simp [this]

/-- The outer argument uses the actual finite core only through this interface.
The final theorem supplies this interface from the explicit graph construction. -/
theorem no_admissible_eventual_linear
    (coreExists : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X)
    {r : ℕ} (hr : 2 ≤ r) {g : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hlinear : ∃ M : ℕ, ∀ m ≥ M, c * m ≤ (g m : ℝ)) : ¬IsAdmissible r g := by
  classical
  obtain ⟨ε, hε, hbudget⟩ := exists_small_cut_budget hc hlinear
  obtain ⟨n, X, hX, hcut⟩ := coreExists ε hε
  let k := r - 2
  have hrk : 2 + k = r := by dsimp [k]; omega
  let Y := cliqueJoin X k
  let N := Fintype.card (Fin n ⊕ Fin k)
  let e : Fin N ≃ (Fin n ⊕ Fin k) := (Fintype.equivFin _).symm
  let G := Y.comap e
  have hlocal : LocalColorCutBound ε r G := by
    rw [← hrk]
    exact localColorCut_comap_equiv (cliqueJoin_localCut hε.le hcut k) e
  intro hadm
  have hchrom := hadm N G (by
    intro H
    obtain ⟨E, hE, hb, hcolor⟩ := localColorCut_subgraph hlocal H
    exact ⟨E, hE, hbudget _ _ hb, hcolor.chromaticNumber_le⟩)
  obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp hchrom
  have hY : Y.Colorable (r + 1) := by
    refine ⟨Coloring.mk (fun v => C (e.symm v)) ?_⟩
    intro u v huv
    apply C.valid
    simpa [G] using huv
  have hnum : r + 1 = 3 + k := by omega
  exact cliqueJoin_not_colorable X k hX (hnum ▸ hY)

/-- The analytic notation in the canonical problem yields the exact eventual lower bound. -/
theorem no_admissible_bigO
    (coreExists : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X)
    {r : ℕ} (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) := by
  rintro ⟨g, hadm, hbig⟩
  obtain ⟨C, hC, hbound⟩ := hbig.exists_pos
  have hevent : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ C * (g n : ℝ) := by
    filter_upwards [hbound.bound] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n),
      abs_of_nonneg (show (0 : ℝ) ≤ g n from Nat.cast_nonneg (g n))] using hn
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  apply no_admissible_eventual_linear coreExists hr (one_div_pos.mpr hC) _ hadm
  refine ⟨M, fun m hm => ?_⟩
  have := hM m hm
  change (1 / C) * (m : ℝ) ≤ (g m : ℝ)
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hC).mpr
  simpa [mul_comm] using this

end

/-! ### Upstream module `Erdos1092/Transport.lean` -/

section
open _root_.SimpleGraph

theorem localCutBound_comap_equiv {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {ε : ℝ} {G : SimpleGraph V} (e : W ≃ V)
    (h : LocalCutBound ε G) : LocalCutBound ε (G.comap e) := by
  classical
  intro H hH S hS
  let H' := H.comap e.symm
  let S' := S.map e.toEmbedding
  have hH' : H' ≤ G := by
    intro u v huv
    have hh := hH huv
    simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hh
  have hS' : ∀ ⦃u v⦄, H'.Adj u v → u ∈ S' ∧ v ∈ S' := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hS huv
    constructor
    · exact Finset.mem_map.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩
    · exact Finset.mem_map.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩
  obtain ⟨E, hE, hcard, ⟨c⟩⟩ := h H' hH' S' hS'
  let E' := E.map e.symm.toEmbedding.sym2Map
  refine ⟨E', ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ E.map e.symm.toEmbedding.sym2Map at hq
    obtain ⟨q0, hq0, heq⟩ := Finset.mem_map.mp hq
    rw [← heq]
    have he := hE hq0
    revert he
    refine Sym2.inductionOn q0 (fun u v he => ?_)
    simpa only [Function.Embedding.sym2Map_apply, Sym2.map_mk,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      H', SimpleGraph.comap_adj, Equiv.toEmbedding_apply] using he
  · simpa only [E', S', Finset.card_map] using hcard
  · refine ⟨Coloring.mk (fun w => c (e w)) ?_⟩
    intro u v huv
    apply c.valid
    rw [SimpleGraph.deleteEdges_adj] at huv ⊢
    refine ⟨?_, ?_⟩
    · simpa only [H', SimpleGraph.comap_adj, Equiv.symm_apply_apply] using huv.1
    · intro hmem
      apply huv.2
      apply Finset.mem_map.mpr
      refine ⟨s(e u, e v), hmem, ?_⟩
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk,
        Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

theorem not_colorable_comap_equiv {V W : Type*}
    {G : SimpleGraph V} {n : ℕ} (e : W ≃ V)
    (h : ¬ G.Colorable n) : ¬ (G.comap e).Colorable n := by
  rintro ⟨c⟩
  apply h
  refine ⟨Coloring.mk (fun v => c (e.symm v)) ?_⟩
  intro u v huv
  apply c.valid
  simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using huv

end

/-! ### Upstream module `Erdos1092/Parameters.lean` -/

/-- The construction parameters are chosen before any subgraph is given. -/
theorem exists_cut_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 2 ≤ M ∧
      2 / (M : ℝ) + 2 / ((2 * M + 1 : ℕ) : ℝ) ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (4 / ε) (2 : ℝ))
  have hM2 : (2 : ℝ) < M := (le_max_right _ _).trans_lt hM
  have hMlarge : 4 / ε < (M : ℝ) := (le_max_left _ _).trans_lt hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hMnat : 2 ≤ M := by exact_mod_cast hM2.le
  have hden : (M : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hratio : 2 / ((2 * M + 1 : ℕ) : ℝ) ≤ 2 / (M : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hMpos hden
  have hfour : 4 / (M : ℝ) ≤ ε := by
    apply (div_le_iff₀ hMpos).mpr
    have := (div_lt_iff₀ hε).mp hMlarge
    nlinarith
  refine ⟨M, hMnat, ?_⟩
  calc
    2 / (M : ℝ) + 2 / ((2 * M + 1 : ℕ) : ℝ) ≤
        2 / (M : ℝ) + 2 / (M : ℝ) := by linarith
    _ = 4 / (M : ℝ) := by ring
    _ ≤ ε := hfour

lemma parameter_layer_ge_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ M + 1 := by omega

lemma parameter_cycle_ge_three {M : ℕ} (hM : 2 ≤ M) : 3 ≤ 2 * M + 1 := by omega

lemma parameter_cycle_odd (M : ℕ) : Odd (2 * M + 1) := by
  exact ⟨M, by omega⟩

lemma parameter_cycle_ne_zero (M : ℕ) : NeZero (2 * M + 1) := by
  exact ⟨by omega⟩

/-! ### Upstream module `Erdos1092/Main.lean` -/

section
open _root_.SimpleGraph _root_.Filter _root_.Asymptotics

theorem localCutBound_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε δ : ℝ} (hεδ : ε ≤ δ)
    (h : LocalCutBound ε G) : LocalCutBound δ G := by
  classical
  intro H hH S hS
  obtain ⟨E, hE, hcard, hcolor⟩ := h H hH S hS
  exact ⟨E, hE, hcard.trans
    (mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg S.card)), hcolor⟩

/-- The actual finite construction supplies every premise of the outer argument. -/
theorem exists_finite_hereditary_counterexample (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X := by
  classical
  obtain ⟨M, hM, hbound⟩ := exists_cut_parameter ε hε
  have : NeZero (2 * M + 1) := parameter_cycle_ne_zero M
  let V := Vertex (M + 1) (2 * M + 1)
  let G := mycGraph (M + 1) (2 * M + 1)
  have hG : ¬G.Colorable 3 := mycGraph_not_colorable_three
    (M + 1) (2 * M + 1) (parameter_layer_ge_two hM)
    (parameter_cycle_ge_three hM) (parameter_cycle_odd M)
  have hcut : LocalCutBound ε G := by
    apply localCutBound_mono _ (mycGraph_localCutBound
      (M + 1) (2 * M + 1) (parameter_layer_ge_two hM) (parameter_cycle_ge_three hM))
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hbound
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  exact ⟨n, G.comap e, not_colorable_comap_equiv e hG,
    localCutBound_comap_equiv e hcut⟩

/-- Complete resolution at every fixed color parameter: no admissible budget is
eventually at least linear. Admissibility retains all subgraph sizes simultaneously. -/
theorem erdos_1092 (r : ℕ) (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  no_admissible_bigO exists_finite_hereditary_counterexample hr

end

#print axioms erdos_1092
-- 'Erdos1092.erdos_1092' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1092
