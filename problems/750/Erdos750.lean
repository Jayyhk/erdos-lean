import Mathlib

namespace Erdos750

/-
# Problem Description

Erdős Problem 750. Let `f(m) → ∞`. Does there exist a graph `G` of infinite chromatic
number such that every subgraph on `m` vertices contains an independent set of size at
least `m / 2 - f(m)`? `erdos_750` answers this in the affirmative.

`erdos_750` is proved unconditionally here: Stiebitz's lower bound on the chromatic number
of recursively built generalized Mycielski graphs, previously assumed in this repository
as `stiebitz_lower_bound`, is proved rather than assumed. The proof is by integral
signed-biclique chains: cylinder contraction extends the chain invariant at each step, and
cyclic-resolution exactness obstructs colourings with too few colours.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos750.lean`, whose `ErdosProblems.Erdos750.Stiebitz` replaces
the assumed bound. The conditional development it builds on is by paws (Shashi456),
`Erdos/P750/Proof.lean`, following the construction of Chojecki and GPT-5.5 Pro
(https://www.ulam.ai/research/erdos750.pdf).

Flattened single-file vendoring of the 30-module import closure, in dependency order, with
project-internal imports removed so that `Mathlib` is the only import, each module wrapped
in its own `section`. Declarations keep their upstream names. The outer `Erdos750`
namespace is stripped from the modules that carry it, since the whole file is wrapped in
it once; `Erdos750.Chains` and `Erdos750.Conditional` become `Chains` and `Conditional`
accordingly. One module, `Erdos780/External/FinsetOrientation.lean`, declares into
Mathlib's own `Finset` namespace — its `Finset.imageSign` and `Finset.imagePerm` are used
through dot notation in five other modules — so it is emitted with an explicit `_root_.`
prefix rather than nested. Two thirds of the closure is the `Erdos780.External.*`
signed-sphere and Tucker-lemma development, shared with problem 780. No mathematical
content is changed.
-/

/-! ### Upstream module `ErdosProblems/Erdos750/Basic.lean` -/

section
/-
Adapted from Shashi456/erdos-formalizations, Erdos/P750/Proof.lean:
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean
Original formalization posted by paws on 4 May 2026:
https://www.erdosproblems.com/forum/thread/750#post-6255
-/

open SimpleGraph Filter
open scoped NNReal

universe u v

/-! ## §2. Generalized Mycielski operation -/

/-- The vertex type of `genMyc s G`: `Fin s` levels of `V`, plus one apex vertex. -/
abbrev MycVerts (s : ℕ) (V : Type u) : Type u := (Fin s × V) ⊕ Unit

/-- The apex vertex of `genMyc s G`. -/
@[reducible] def apex (s : ℕ) (V : Type u) : MycVerts s V := Sum.inr ()

/-- The "level i" vertex `(i, v)` in `genMyc s G`. -/
@[reducible] def lvl (s : ℕ) {V : Type u} (i : Fin s) (v : V) : MycVerts s V :=
  Sum.inl (i, v)

/-- Raw adjacency relation of `genMyc s G`, before symmetry/irreflexivity packaging. -/
def MycAdj (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    MycVerts s V → MycVerts s V → Prop
  | Sum.inl (i, u), Sum.inl (j, v) =>
      (i.val = 0 ∧ j.val = 0 ∧ G.Adj u v)
      ∨ (j.val = i.val + 1 ∧ G.Adj u v)
      ∨ (i.val = j.val + 1 ∧ G.Adj u v)
  | Sum.inl (i, _), Sum.inr () => i.val + 1 = s
  | Sum.inr (), Sum.inl (i, _) => i.val + 1 = s
  | Sum.inr (), Sum.inr () => False

lemma MycAdj_symm (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    Std.Symm (MycAdj s G) := by
  constructor
  intro a b h
  match a, b, h with
  | Sum.inl (i, u), Sum.inl (j, v), h =>
      simp only [MycAdj] at h ⊢
      rcases h with ⟨hi, hj, h⟩ | ⟨hji, h⟩ | ⟨hij, h⟩
      · exact Or.inl ⟨hj, hi, h.symm⟩
      · exact Or.inr (Or.inr ⟨hji, h.symm⟩)
      · exact Or.inr (Or.inl ⟨hij, h.symm⟩)
  | Sum.inl (i, _), Sum.inr (), h =>
      simp only [MycAdj] at h ⊢; exact h
  | Sum.inr (), Sum.inl (i, _), h =>
      simp only [MycAdj] at h ⊢; exact h
  | Sum.inr (), Sum.inr (), h =>
      simp only [MycAdj] at h

lemma MycAdj_irrefl (s : ℕ) {V : Type u} (G : SimpleGraph V) :
    Std.Irrefl (MycAdj s G) := by
  constructor
  intro a h
  match a, h with
  | Sum.inl (i, v), h =>
      simp only [MycAdj] at h
      rcases h with ⟨_, _, h⟩ | ⟨hii, _⟩ | ⟨hii, _⟩
      · exact G.irrefl ‹_›
      · omega
      · omega
  | Sum.inr (), h =>
      simp only [MycAdj] at h

/--
The **generalized Mycielski graph** `Mₛ(G)` of a graph `G` (PDF Definition 2.1):
* level-0 internal edges `(0,u)-(0,v)` for each edge `uv ∈ E(G)`;
* cross-level edges `(i,u)-(i+1,v)` for each edge `uv` and `0 ≤ i < s-1`;
* the apex `z` is adjacent to every top-level vertex `(s-1,v)`.

`M₂(G)` is the classical Mycielskian; `M₁(G)` adds a universal vertex.
-/
def genMyc (s : ℕ) {V : Type u} (G : SimpleGraph V) : SimpleGraph (MycVerts s V) where
  Adj := MycAdj s G
  symm := MycAdj_symm s G
  loopless := MycAdj_irrefl s G

/-! ## §3. Odd-cycle transversal number `oct` -/

/--
The **odd-cycle transversal number** of an induced subgraph `G[X]`: the minimum size
of `T ⊆ X` such that `G` restricted to `X \ T` is bipartite.

Defined for any `G : SimpleGraph V` (possibly infinite) and any `X : Finset V`.
Since `T = X` always works (the empty graph is bipartite), the set of valid `t` is
nonempty and `sInf` returns a natural number.
-/
noncomputable def oct {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) : ℕ :=
  sInf { t : ℕ | ∃ T : Finset V, T ⊆ X ∧ T.card = t ∧
    (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite }

/-! ### OCT API — extraction / introduction lemmas -/

/-- Empty induced subgraph is bipartite (works on any vertex type). -/
private lemma induce_empty_isBipartite {V : Type u} (G : SimpleGraph V) :
    (G.induce (∅ : Set V)).IsBipartite := by
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  rintro ⟨_, hv⟩ _ _; exact absurd hv (Set.notMem_empty _)

/-- The witness set defining `oct G X` is nonempty (`T = X` always works). -/
private lemma oct_nonempty_witness {V : Type u}
    (G : SimpleGraph V) (X : Finset V) :
    ({ t : ℕ | ∃ T : Finset V, T ⊆ X ∧ T.card = t ∧
        (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite }).Nonempty := by
  refine ⟨X.card, X, subset_refl _, rfl, ?_⟩
  rw [show ((↑X : Set V) \ (↑X : Set V)) = (∅ : Set V) from Set.sdiff_self]
  exact induce_empty_isBipartite G

/-- **Introduction.** If a `T ⊆ X` of size `≤ k` makes `G[X \ T]` bipartite, then
`oct G X ≤ k`. -/
lemma oct_le_of_delete {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {X T : Finset V} (hT : T ⊆ X) {k : ℕ} (hcard : T.card ≤ k)
    (hbip : (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite) :
    oct G X ≤ k :=
  le_trans (Nat.sInf_le ⟨T, hT, rfl, hbip⟩) hcard

/-- **Extraction.** `oct G X` is realised by some witness `T ⊆ X`. -/
lemma oct_witness {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    ∃ T : Finset V, T ⊆ X ∧ T.card = oct G X ∧
      (G.induce ((↑X : Set V) \ (↑T : Set V))).IsBipartite := by
  have hmem := Nat.sInf_mem (oct_nonempty_witness G X)
  exact hmem

/-- `oct G X = 0` iff `G[X]` is already bipartite. -/
lemma oct_eq_zero_iff {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) :
    oct G X = 0 ↔ (G.induce ((↑X : Set V))).IsBipartite := by
  refine ⟨fun h => ?_, fun hbip => ?_⟩
  · obtain ⟨T, hT, hcard, hbip⟩ := oct_witness G X
    rw [h, Finset.card_eq_zero] at hcard
    subst hcard
    rw [Finset.coe_empty, Set.sdiff_empty] at hbip
    exact hbip
  · refine le_antisymm ?_ (Nat.zero_le _)
    refine oct_le_of_delete (Finset.empty_subset X) (by simp) ?_
    rw [Finset.coe_empty, Set.sdiff_empty]
    exact hbip

/-- `oct G ∅ = 0` (empty graph is bipartite). -/
@[simp] lemma oct_empty {V : Type u} [DecidableEq V] (G : SimpleGraph V) :
    oct G ∅ = 0 := by
  rw [oct_eq_zero_iff]
  rw [Finset.coe_empty]
  exact induce_empty_isBipartite G

/-! ## Recursive generalized Mycielski graphs -/

/--
Predicate that a graph `G` was assembled from `K₂` by iterated `Mₛ`-cones.
Stiebitz's theorem applies *only* to graphs in this recursively built class; it is
**not** true that `χ(Mₛ(H)) = χ(H) + 1` for every graph `H` and every `s ≥ 3`.

`IsRecursivelyBuiltMr r G` says: `G ≃g K₂` if `r = 2`, otherwise there exists some
graph `H` in `Mᵣ₋₁` and some `s ≥ 1` such that `G ≃g genMyc s H`.
-/
def IsRecursivelyBuiltMr : ∀ (_r : ℕ) {_V : Type u} (_G : SimpleGraph _V), Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | 2, _, G => Nonempty (G ≃g (completeGraph (Fin 2)))
  | r + 3, _, G => ∃ (W : Type u) (H : SimpleGraph W) (s : ℕ),
      1 ≤ s ∧ IsRecursivelyBuiltMr (r + 2) H ∧ Nonempty (G ≃g genMyc s H)

end

/-! ### Upstream module `ErdosProblems/Erdos750/Conditional.lean` -/

section
/-
Adapted from Shashi456/erdos-formalizations, Erdos/P750/Proof.lean:
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean
Original formalization posted by paws on 4 May 2026:
https://www.erdosproblems.com/forum/thread/750#post-6255
-/

namespace Conditional

open SimpleGraph Filter
open scoped NNReal

universe u v

/-- Stiebitz's chromatic lower bound, isolated as an explicit hypothesis. -/
def StiebitzLowerBound : Prop :=
  ∀ {V : Type} (G : SimpleGraph V) (r : ℕ),
    IsRecursivelyBuiltMr r G → (r : ℕ∞) ≤ G.chromaticNumber

/-! ## §3. Key combinatorial lemmas -/

/-- Easy direction of Stiebitz: a `k`-colouring of `G` lifts to a `(k+1)`-colouring of
`Mₛ(G)` by reusing the colours on every level and giving the apex a fresh colour. -/
theorem genMyc_colorable_succ {V : Type u} (s : ℕ) (G : SimpleGraph V) (k : ℕ)
    (hG : G.Colorable k) : (genMyc s G).Colorable (k + 1) := by
  classical
  obtain ⟨c⟩ := hG
  refine ⟨Coloring.mk
    (fun a => Sum.elim (fun p : Fin s × V => (c p.2).castSucc) (fun _ : Unit => Fin.last k) a)
    ?_⟩
  intro a b hab
  match a, b, hab with
  | Sum.inl (i, u), Sum.inl (j, v), h =>
      simp only [Sum.elim_inl]
      have huv : G.Adj u v := by
        rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
      have hcuv : c u ≠ c v := c.valid huv
      intro heq
      exact hcuv (Fin.castSucc_injective _ heq)
  | Sum.inl (i, u), Sum.inr (), _ =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      intro heq
      have hh : ((c u).castSucc).val = k := by rw [heq]; rfl
      rw [Fin.val_castSucc] at hh
      have := (c u).isLt
      omega
  | Sum.inr (), Sum.inl (i, v), _ =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      intro heq
      have hh : (Fin.last k).val = ((c v).castSucc).val := by rw [heq]
      rw [Fin.val_castSucc] at hh
      have := (c v).isLt
      simp at hh
      omega
  | Sum.inr (), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h

/-- Easy direction of Stiebitz: `χ(Mₛ(G)) ≤ χ(G) + 1`. -/
theorem genMyc_chromaticNumber_le_succ {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    (genMyc s G).chromaticNumber ≤ G.chromaticNumber + 1 := by
  by_cases hG : G.chromaticNumber = ⊤
  · rw [hG]; simp
  · -- finite case: take k = G.chromaticNumber.toNat
    set n := G.chromaticNumber.toNat with hn_def
    have hcoe : (n : ℕ∞) = G.chromaticNumber := by
      rw [hn_def]; exact ENat.natCast_toNat hG
    have hGc : G.Colorable n := by
      rw [← chromaticNumber_le_iff_colorable, hcoe]
    have h1 : (genMyc s G).Colorable (n + 1) := genMyc_colorable_succ s G n hGc
    have h2 : (genMyc s G).chromaticNumber ≤ ((n + 1 : ℕ) : ℕ∞) := h1.chromaticNumber_le
    have h3 : ((n + 1 : ℕ) : ℕ∞) = G.chromaticNumber + 1 := by
      push_cast; rw [hcoe]
    rw [h3] at h2; exact h2

/--
The projection of a finite vertex set in `Mₛ(G)` to a `Finset` of `V`. Apex vertices
contribute nothing.
-/
def projFinset {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) : Finset V :=
  X.biUnion fun a => match a with | Sum.inl (_, v) => {v} | Sum.inr () => ∅

/-- The "lifted deletion set" used in Lemma 3.1's proof: from a transversal `T` of
`G[projFinset X]`, lift to a deletion set of `(genMyc s G)[X]` that includes every
copy `(i, v)` with `v ∈ T` *and* the apex if it appears in `X`.

Equivalently `(image of (Fin s) × T into MycVerts) ∪ {apex if in X}`, intersected
with `X`. -/
private noncomputable def liftedDeletion {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) : Finset (MycVerts s V) :=
  X ∩ (((Finset.univ : Finset (Fin s)) ×ˢ T).image (fun p => Sum.inl p) ∪
       ({apex s V} : Finset (MycVerts s V)))

private lemma liftedDeletion_subset {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) :
    liftedDeletion X T ⊆ X :=
  Finset.inter_subset_left

private lemma mem_liftedDeletion {V : Type u} [DecidableEq V] {s : ℕ}
    {X : Finset (MycVerts s V)} {T : Finset V} {a : MycVerts s V} :
    a ∈ liftedDeletion X T ↔
      a ∈ X ∧ ((∃ i : Fin s, ∃ v ∈ T, a = Sum.inl (i, v)) ∨ a = apex s V) := by
  classical
  unfold liftedDeletion
  rw [Finset.mem_inter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with ⟨⟨i, v⟩, hv, heq⟩ | hap
    · left
      rw [Finset.mem_product] at hv
      exact ⟨i, v, hv.2, heq.symm⟩
    · right; exact hap
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with ⟨i, v, hv, heq⟩ | hap
    · left
      refine ⟨(i, v), ?_, heq.symm⟩
      rw [Finset.mem_product]
      exact ⟨Finset.mem_univ _, hv⟩
    · right; exact hap

/-- Cardinality bound for the lifted deletion set. -/
private lemma liftedDeletion_card_le {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) (T : Finset V) :
    (liftedDeletion X T).card ≤ s * T.card +
      (if apex s V ∈ X then 1 else 0) := by
  classical
  -- liftedDeletion ⊆ levelLifts ∪ apexSet (with the apex set conditional on X)
  set levelLifts : Finset (MycVerts s V) :=
    ((Finset.univ : Finset (Fin s)) ×ˢ T).image (fun p => Sum.inl p) with h_lL
  set apexSet : Finset (MycVerts s V) :=
    if apex s V ∈ X then ({apex s V} : Finset _) else ∅ with h_aS
  have h_sub : liftedDeletion X T ⊆ levelLifts ∪ apexSet := by
    intro a ha
    rw [mem_liftedDeletion] at ha
    obtain ⟨ha_X, ha_or⟩ := ha
    rw [Finset.mem_union]
    rcases ha_or with ⟨i, v, hv, heq⟩ | hap
    · left; rw [h_lL, Finset.mem_image]
      refine ⟨(i, v), ?_, heq.symm⟩
      simp [Finset.mem_product, hv]
    · right; rw [h_aS]
      rw [hap] at ha_X
      simp [ha_X, hap]
  refine le_trans (Finset.card_le_card h_sub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  · rw [h_aS]; split_ifs <;> simp

/-- Bipartiteness of the survivor `(genMyc s G)[X \ liftedDeletion X T]`, given that
`G[projFinset X \ T]` is bipartite. The bipartition is "vertical": each level vertex
inherits the side of its projection in `G`. -/
private lemma liftedDeletion_survivor_isBipartite {V : Type u} [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (X : Finset (MycVerts s V)) (T : Finset V)
    (_hT : T ⊆ projFinset X)
    (hbip : (G.induce ((↑(projFinset X) : Set V) \ (↑T : Set V))).IsBipartite) :
    ((genMyc s G).induce
        ((↑X : Set (MycVerts s V)) \
          (↑(liftedDeletion X T) : Set (MycVerts s V)))).IsBipartite := by
  classical
  obtain ⟨c⟩ := hbip
  -- For a survivor a, extract its underlying V-vertex and properties: a = Sum.inl (i, v),
  -- v ∈ projFinset X, v ∉ T. The apex is excluded by `liftedDeletion`.
  -- We use a `match` term to define the coloring directly, taking the survivor's proof
  -- as input to discharge the apex case via `False.elim`.
  have hAux : ∀ a : MycVerts s V,
      a ∈ X → a ∉ liftedDeletion X T →
      Σ' (v : V), v ∈ projFinset X ∧ v ∉ T ∧ ∃ i : Fin s, a = Sum.inl (i, v) := by
    intro a haX haND
    match a, haX, haND with
    | Sum.inl (i, v), hX', hND' =>
        refine ⟨v, ?_, ?_, i, rfl⟩
        · unfold projFinset
          rw [Finset.mem_biUnion]
          exact ⟨Sum.inl (i, v), hX', by simp⟩
        · intro hvT
          apply hND'
          rw [mem_liftedDeletion]
          exact ⟨hX', Or.inl ⟨i, v, hvT, rfl⟩⟩
    | Sum.inr (), hX', hND' =>
        exfalso
        apply hND'
        rw [mem_liftedDeletion]
        exact ⟨hX', Or.inr rfl⟩
  -- Define the coloring on survivors by projecting and applying c.
  let colorFn : ((↑X : Set (MycVerts s V)) \
      (↑(liftedDeletion X T) : Set (MycVerts s V)) : Set _) → Fin 2 :=
    fun a =>
      let info := hAux a.val a.prop.1 a.prop.2
      c ⟨info.1, info.2.1, info.2.2.1⟩
  refine ⟨Coloring.mk colorFn ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : (genMyc s G).Adj a b := hab
  simp only [colorFn]
  -- Compute `hAux` outputs for a and b
  set ainfo := hAux a ha.1 ha.2 with h_ainfo
  set binfo := hAux b hb.1 hb.2 with h_binfo
  -- Show `Sum.inl (i, ainfo.1) = a` and `Sum.inl (j, binfo.1) = b` for some i, j.
  obtain ⟨i, hai⟩ := ainfo.2.2.2
  obtain ⟨j, hbj⟩ := binfo.2.2.2
  -- From hab' : (genMyc s G).Adj a b and the substitutions a = inl(i, ainfo.1), b = inl(j,
  -- binfo.1),
  -- conclude G.Adj ainfo.1 binfo.1.
  have huv : G.Adj ainfo.1 binfo.1 := by
    have : (genMyc s G).Adj (Sum.inl (i, ainfo.1)) (Sum.inl (j, binfo.1)) := by
      rw [← hai, ← hbj]; exact hab'
    -- Unfold MycAdj on inl-inl
    have hM : MycAdj s G (Sum.inl (i, ainfo.1)) (Sum.inl (j, binfo.1)) := this
    simp only [MycAdj] at hM
    rcases hM with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  -- Apply c.valid
  exact c.valid huv

/--
**Lemma 3.1 (Projection inequality).** For every `X ⊆ V(Mₛ(G))` with projection
`P = projFinset X`, the induced subgraph satisfies
`oct(Mₛ(G)[X]) ≤ s · oct(G[P]) + 1{apex ∈ X}`.

Proof: take an OCT witness `T` of `G[projFinset X]`. Lift to `T' := liftedDeletion X T`.
Then `T' ⊆ X`, `|T'| ≤ s * |T| + 1{apex ∈ X}` (`liftedDeletion_card_le`), and the
survivor `(genMyc s G)[X \ T']` is bipartite (`liftedDeletion_survivor_isBipartite`).
Apply `oct_le_of_delete`.
-/
theorem oct_genMyc_le {V : Type u} [DecidableEq V]
    (s : ℕ) (G : SimpleGraph V) (X : Finset (MycVerts s V)) :
    oct (genMyc s G) X ≤ s * oct G (projFinset X) +
      (if apex s V ∈ X then 1 else 0) := by
  classical
  obtain ⟨T, hTsub, hTcard, hTbip⟩ := oct_witness G (projFinset X)
  have hcard := liftedDeletion_card_le X T
  rw [hTcard] at hcard
  refine oct_le_of_delete (liftedDeletion_subset X T) hcard ?_
  exact liftedDeletion_survivor_isBipartite G X T hTsub hTbip

/-- **Height** of a vertex in `Mₛ(G)`: the apex sits at height `s`, every level-`i`
vertex sits at height `i.val < s`. Each edge changes height by at most `1`, with edges
that *preserve* height existing only at height `0` (level-0 internal edges). -/
def height {V : Type u} (s : ℕ) : MycVerts s V → ℕ
  | Sum.inl (i, _) => i.val
  | Sum.inr () => s

/-- Edges of `genMyc s G` change height by at most 1. -/
lemma height_diff_le_one {V : Type u} {s : ℕ} {G : SimpleGraph V}
    {a b : MycVerts s V} (h : (genMyc s G).Adj a b) :
    height s a ≤ height s b + 1 ∧ height s b ≤ height s a + 1 := by
  match a, b, h with
  | Sum.inl (i, _), Sum.inl (j, _), h =>
      simp only [height]
      rcases h with ⟨hi, hj, _⟩ | ⟨hji, _⟩ | ⟨hij, _⟩ <;> omega
  | Sum.inl (i, _), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height]; omega
  | Sum.inr (), Sum.inl (i, _), h =>
      simp only [genMyc, MycAdj] at h
      simp only [height]; omega
  | Sum.inr (), Sum.inr (), h =>
      simp only [genMyc, MycAdj] at h

/-- Walks are 1-Lipschitz with respect to `height`: a walk of length `ℓ` from `a` to `b`
satisfies `|height a − height b| ≤ ℓ`. -/
lemma height_diff_le_walk_length {V : Type u} {s : ℕ} {G : SimpleGraph V}
    {a b : MycVerts s V} (w : (genMyc s G).Walk a b) :
    height s a ≤ height s b + w.length ∧ height s b ≤ height s a + w.length := by
  induction w with
  | nil => simp
  | @cons a c b hac w ih =>
      have hed := height_diff_le_one hac
      simp only [Walk.length_cons]
      omega

/-! ### Towards Lemma 3.2: parity coloring of `Mₛ(G)` minus level-0 internal edges -/

/-- The "level-0 internal" edges of `Mₛ(G)`: both endpoints at height 0. For `s ≥ 1`
this is exactly the level-0 internal edges of the PDF. -/
def IsLevelZeroEdge {V : Type u} {s : ℕ} (a b : MycVerts s V) : Prop :=
  height s a = 0 ∧ height s b = 0

lemma IsLevelZeroEdge.symm {V : Type u} {s : ℕ} {a b : MycVerts s V}
    (h : IsLevelZeroEdge a b) : IsLevelZeroEdge b a := ⟨h.2, h.1⟩

/-- The graph `Mₛ(G)` with level-0 internal edges removed. Closed walks here are
even-length: a height-parity coloring witnesses bipartiteness. -/
def genMycMinusZero {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    SimpleGraph (MycVerts s V) where
  Adj a b := (genMyc s G).Adj a b ∧ ¬ IsLevelZeroEdge a b
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, fun hz => h2 hz.symm⟩⟩
  loopless := ⟨fun _ ⟨h1, _⟩ => (genMyc s G).irrefl h1⟩

/-- The height parity is a 2-coloring of `Mₛ(G)` minus level-0 internal edges. -/
private lemma genMycMinusZero_isBipartite {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    (genMycMinusZero s G).IsBipartite := by
  refine ⟨Coloring.mk
    (fun a => (⟨(height s a) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  intro a b ⟨hab, hnot0⟩
  -- Heights differ by exactly 1; height parities differ.
  have hheight : height s a + 1 = height s b ∨ height s b + 1 = height s a := by
    match a, b, hab with
    | Sum.inl (i, _), Sum.inl (j, _), h =>
        simp only [height]
        rcases h with ⟨hi, hj, _⟩ | ⟨hji, _⟩ | ⟨hij, _⟩
        · exact absurd ⟨by simpa [height] using hi, by simpa [height] using hj⟩ hnot0
        · left; omega
        · right; omega
    | Sum.inl (i, _), Sum.inr (), h =>
        have h' : i.val + 1 = s := h
        simp only [height]; left; omega
    | Sum.inr (), Sum.inl (i, _), h =>
        have h' : i.val + 1 = s := h
        simp only [height]; right; omega
    | Sum.inr (), Sum.inr (), h =>
        exact (h : False).elim
  -- From either case, parities differ
  intro heq
  have heq' : (height s a) % 2 = (height s b) % 2 := by
    have := congrArg Fin.val heq
    simpa using this
  rcases hheight with hh | hh
  · omega
  · omega

/--
**Generalized helper.** Any walk in `Mₛ(G)` containing a level-0 edge has length at
least `height a + height b + 1`, where `a, b` are the walk's endpoints.

Proof by induction on the walk. Base case (nil walk) is vacuous. For `cons hab rest`:
either the first edge is the level-0 edge (so `height a = height c = 0`, and
Lipschitz on `rest` gives `rest.length ≥ height b`); or the level-0 edge is in
`rest.edges`, in which case the induction hypothesis plus the height bound
`|height a − height c| ≤ 1` gives the result.
-/
private lemma walk_zero_edge_implies_long {V : Type u} {s : ℕ} {G : SimpleGraph V} :
    ∀ {a b : MycVerts s V} (w : (genMyc s G).Walk a b),
      (∃ e ∈ w.edges, ∀ v ∈ e, height s v = 0) →
      height s a + height s b + 1 ≤ w.length := by
  intro a b w hex
  induction w with
  | nil =>
      obtain ⟨e, he, _⟩ := hex
      simp at he
  | @cons a c b hab rest ih =>
      obtain ⟨e, he_in, he_zero⟩ := hex
      rw [Walk.edges_cons] at he_in
      rcases List.mem_cons.mp he_in with heq | hin
      · -- The first edge is the level-0 edge
        subst heq
        have h_a_zero : height s a = 0 := he_zero a (Sym2.mem_mk_left a c)
        have h_c_zero : height s c = 0 := he_zero c (Sym2.mem_mk_right a c)
        have hLip := (height_diff_le_walk_length rest).2
        -- hLip : height s b ≤ height s c + rest.length = rest.length
        simp only [Walk.length_cons]
        omega
      · -- Level-0 edge is inside `rest`
        have ih_appl : height s c + height s b + 1 ≤ rest.length :=
          ih ⟨e, hin, he_zero⟩
        have hedge := height_diff_le_one hab
        simp only [Walk.length_cons]
        omega

/-- An edge in `(genMyc s G).edgeSet` but not in `(genMycMinusZero s G).edgeSet` is a
level-0 edge: both endpoints have height 0. -/
private lemma sym2_zero_of_in_genMyc_not_minus {V : Type u} {s : ℕ}
    {G : SimpleGraph V} :
    ∀ (e : Sym2 (MycVerts s V)),
      e ∈ (genMyc s G).edgeSet → e ∉ (genMycMinusZero s G).edgeSet →
      ∀ v ∈ e, height s v = 0 := by
  refine Sym2.ind ?_
  intro a b hG hne v hv
  rw [SimpleGraph.mem_edgeSet] at hG
  have h_iszero : IsLevelZeroEdge a b := by
    by_contra h
    apply hne
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hG, h⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact h_iszero.1
  · exact h_iszero.2

/--
**Apex-to-apex closed walks with a non-`genMycMinusZero` edge are long.** If `w` is
a closed walk from `apex` to `apex` containing some edge not in `genMycMinusZero`,
then `w.length ≥ 2 s + 1`.
-/
private lemma walk_apex_long_of_zero_edge {V : Type u} {s : ℕ} {G : SimpleGraph V}
    (w : (genMyc s G).Walk (apex s V) (apex s V))
    (hex : ∃ e ∈ w.edges, e ∉ (genMycMinusZero s G).edgeSet) :
    2 * s + 1 ≤ w.length := by
  obtain ⟨e, he, hne⟩ := hex
  have hG : e ∈ (genMyc s G).edgeSet := w.edges_subset_edgeSet he
  have hzero : ∀ v ∈ e, height s v = 0 :=
    sym2_zero_of_in_genMyc_not_minus e hG hne
  have hlen := walk_zero_edge_implies_long w ⟨e, he, hzero⟩
  simp only [height] at hlen
  omega

/--
**Helper sub-lemma for Lemma 3.2.** Contrapositive of the above: if a closed apex
walk has length `< 2s + 1`, all its edges are in `genMycMinusZero s G`.
-/
private lemma walk_short_no_zero_edge {V : Type u} {s : ℕ} (G : SimpleGraph V)
    (w : (genMyc s G).Walk (apex s V) (apex s V))
    (hlen : w.length < 2 * s + 1) :
    ∀ e ∈ w.edges, e ∈ (genMycMinusZero s G).edgeSet := by
  intro e he
  by_contra hcon
  exact absurd hlen (not_lt.mpr (walk_apex_long_of_zero_edge w ⟨e, he, hcon⟩))

/--
**Lemma 3.2 (Apex closed walks of odd length are long).**

For every `s ≥ 1` and every closed walk in `Mₛ(G)` from the apex back to itself, if the
walk has odd length, the length is at least `2 * s + 1`.

This statement does **not** require `G` to be bipartite (audit #4). The argument is
purely a height/parity invariant: every edge changes `height` by 0 (only at height 0)
or ±1, so on a closed walk the count of `±1`-edges is even, meaning odd parity forces
at least one `0`-edge. A `0`-edge exists only at height 0, so the walk descends from
height `s` to `0` and re-ascends. Each leg costs at least `s` edges by Lipschitz, plus
the `0`-edge itself, giving total length at least `2 * s + 1`.

This proof is structured into two pieces: the parity coloring of
`genMycMinusZero` (proved above), and the helper `walk_short_no_zero_edge`
(the walk-decomposition + Lipschitz step). Given the helper, this theorem is
fully proved by `Walk.transfer` + `Coloring.even_length_iff_congr`.
-/
theorem genMyc_oddClosedWalk_through_apex_long {V : Type u} {s : ℕ} (_hs : 1 ≤ s)
    (G : SimpleGraph V) :
    ∀ (w : (genMyc s G).Walk (apex s V) (apex s V)),
      Odd w.length → 2 * s + 1 ≤ w.length := by
  intro w hodd
  by_contra hcon
  push Not at hcon
  -- hcon : w.length < 2 * s + 1.  Lift w to genMycMinusZero (no 0-edges).
  have hedges : ∀ e ∈ w.edges, e ∈ (genMycMinusZero s G).edgeSet :=
    walk_short_no_zero_edge G w hcon
  let w' : (genMycMinusZero s G).Walk (apex s V) (apex s V) := w.transfer _ hedges
  have hlen : w'.length = w.length := Walk.length_transfer w hedges
  -- Use bipartite parity to force even length.
  obtain ⟨c⟩ := genMycMinusZero_isBipartite s G
  let c' : (genMycMinusZero s G).Coloring Bool := SimpleGraph.recolorOfEquiv _ finTwoEquiv c
  have heven : Even w'.length := (c'.even_length_iff_congr w').mpr ⟨id, id⟩
  rw [hlen] at heven
  exact Nat.not_odd_iff_even.mpr heven hodd

/-! ## §4. Finite local-oct profile -/

/--
**Helper.** In a simple graph, if `p : G.Walk v u` is a path of length at least 2,
then there is no edge between its endpoints `s(u, v)` lying within `p.edges`.
Reason: any such edge corresponds to a dart at some position `k < p.length` with
endpoints `{u, v}`. By `IsPath.getVert_eq_start_iff` and `getVert_eq_end_iff`,
the only positions giving `u` and `v` are `p.length` and `0` respectively. So
the dart spans `(0, 1) = (v, u)`, giving `1 = p.length`, contradicting `length ≥ 2`.
-/
private lemma noEndpointEdge_of_isPath_length_ge_two {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk v u) (hpath : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  intro hmem
  -- Get a dart witnessing the edge.
  rw [Walk.edges, List.mem_map] at hmem
  obtain ⟨d, hd_mem, hd_edge⟩ := hmem
  -- d is at some position k in p.darts.
  obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hd_mem
  rw [Walk.length_darts] at hk_lt
  -- d = ⟨(getVert k, getVert (k+1)), _⟩.
  have hk_lt' : k < p.darts.length := by rw [Walk.length_darts]; exact hk_lt
  have hd_eq := Walk.darts_getElem_eq_getVert (p := p) k hk_lt'
  rw [hk_eq] at hd_eq
  -- d.edge = s(u, v), so {d.fst, d.snd} = {u, v}.
  rcases d with ⟨⟨a, b⟩, hadj⟩
  simp only [Dart.mk.injEq] at hd_eq
  injection hd_eq with hfst hsnd
  -- now hfst : a = p.getVert k, hsnd : b = p.getVert (k + 1).
  -- d.edge = s(a, b) = s(u, v). So (a, b) = (u, v) or (a, b) = (v, u).
  simp only [Dart.edge, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk] at hd_edge
  rcases hd_edge with ⟨ha_u, hb_v⟩ | ⟨ha_v, hb_u⟩
  · -- a = u, b = v: p.getVert k = u, so k = p.length (by getVert_eq_end_iff). But k < p.length.
    have hgvk : p.getVert k = u := hfst.symm.trans ha_u
    rw [hpath.getVert_eq_end_iff (Nat.le_of_lt hk_lt)] at hgvk
    omega
  · -- a = v, b = u: p.getVert k = v, so k = 0. Then p.getVert 1 = u, so 1 = p.length.
    have h_a : p.getVert k = v := hfst.symm.trans ha_v
    have h_b : p.getVert (k + 1) = u := hsnd.symm.trans hb_u
    rw [hpath.getVert_eq_start_iff (Nat.le_of_lt hk_lt)] at h_a
    rw [h_a] at h_b
    -- now h_b : p.getVert 1 = u
    rw [hpath.getVert_eq_end_iff (by omega : (0 + 1 : ℕ) ≤ p.length)] at h_b
    omega

/--
**Helper.** A closed walk in a simple graph with `support.tail.Nodup` and length at
least three is automatically a cycle. The only obstruction to a nodup-tail closed
walk being a cycle is having length 2 — a walk `u → v → u` whose two edges coincide.
Odd closed walks have length ≠ 2, so for them tail-nodup suffices.
-/
private lemma isCycle_of_tail_nodup_three_le {V : Type*} {G : SimpleGraph V} :
    ∀ {u : V} (w : G.Walk u u), w.support.tail.Nodup → 3 ≤ w.length → w.IsCycle := by
  intro u w htail hlen
  match w, htail, hlen with
  | .nil, _, hlen => simp at hlen
  | .cons (v := v) h₀ p, htail, hlen =>
    have hpath : p.IsPath := by
      rw [Walk.isPath_def]
      simpa using htail
    have hlen_p : 2 ≤ p.length := by
      simp [Walk.length_cons] at hlen
      omega
    rw [Walk.cons_isCycle_iff]
    exact ⟨hpath, noEndpointEdge_of_isPath_length_ge_two p hpath hlen_p⟩

/--
**Helper.** From any odd closed walk in a simple graph, extract an odd cycle whose
length is at most the original walk's length and whose support is contained in the
walk's support. The proof is by strong induction on length: a non-cycle odd closed
walk admits a vertex repetition; rotating to that vertex and splitting via takeUntil
yields two strictly-shorter closed sub-walks summing to the original odd length, one
of which is therefore odd; recurse on it.
-/
private lemma exists_isCycle_of_odd_closedWalk
    {V : Type*} {G : SimpleGraph V} :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length = n → Odd w.length →
      ∃ (v : V) (c : G.Walk v v),
        c.IsCycle ∧ Odd c.length ∧ c.length ≤ n ∧ ∀ x ∈ c.support, x ∈ w.support := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hwn hodd
    -- Case 1: w is already a cycle. Done.
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, hodd, hwn ▸ Nat.le_refl _, fun _ hx => hx⟩
    -- w not a cycle: derive length ≥ 3, then ¬ tail.Nodup, then splice.
    have hodd_ne_zero : w.length ≠ 0 := by
      rcases hodd with ⟨k, hk⟩; omega
    have hlen_ne_one : w.length ≠ 1 := by
      intro h1
      match w, h1 with
      | .cons (v := v) h₀ p, h1 =>
        simp [Walk.length_cons] at h1
        -- h1 : p.length = 0, p : Walk v u, so v = u, contradicting Adj u v.
        rcases p with _ | _
        · exact G.irrefl h₀
        · simp at h1
    have hlen_ne_two : w.length ≠ 2 := by
      intro h2; rw [h2] at hodd; exact (by decide : ¬ Odd 2) hodd
    have hlen_ge_three : 3 ≤ w.length := by
      rcases hodd with ⟨k, hk⟩; omega
    -- ¬ tail.Nodup (else cycle).
    have hnotnodup : ¬ w.support.tail.Nodup :=
      fun htail => hcyc (isCycle_of_tail_nodup_three_le w htail hlen_ge_three)
    -- Find a duplicate y in support.tail.
    rw [← List.exists_duplicate_iff_not_nodup] at hnotnodup
    obtain ⟨y, hy_dup⟩ := hnotnodup
    have hy_mem : y ∈ w.support :=
      (Walk.mem_support_iff w).mpr (Or.inr hy_dup.mem)
    -- Rotate to start at y.
    let w' := w.rotate y hy_mem
    have hw'_len : w'.length = w.length := by
      change ((w.dropUntil y hy_mem).append (w.takeUntil y hy_mem)).length = w.length
      rw [Walk.length_append, add_comm]
      have := congr_arg Walk.length (w.take_spec hy_mem)
      rw [Walk.length_append] at this
      exact this
    have hw'_odd : Odd w'.length := hw'_len ▸ hodd
    -- y has count ≥ 2 in w.support.tail (from the Duplicate).
    have hy_count_w : 2 ≤ List.count y w.support.tail :=
      List.duplicate_iff_two_le_count.mp hy_dup
    -- And in w'.support.tail (rotation preserves count).
    have hperm : List.Perm w'.support.tail w.support.tail :=
      (Walk.support_rotate w y hy_mem).perm
    have hy_count_w' : 2 ≤ List.count y w'.support.tail := by
      rw [hperm.count_eq]; exact hy_count_w
    -- w' is non-nil (odd length).
    have hw'_pos : 0 < w'.length := by rw [hw'_len]; omega
    -- Decompose w' = cons h_b q (q : Walk y' y for some y').
    match hw'_eq : w', hw'_pos, hy_count_w' with
    | .nil, h0, _ => simp at h0
    | .cons (v := y') h_b q, _, hy_count_w'_cons =>
      -- support.tail of cons = q.support.
      have hy_count_q : 2 ≤ List.count y q.support := by
        have : (Walk.cons h_b q).support.tail = q.support := by simp
        rwa [this] at hy_count_w'_cons
      have hy_in_q : y ∈ q.support := List.count_pos_iff.mp (by omega)
      -- q = q.takeUntil y hy_in_q ++ q.dropUntil y hy_in_q.
      let q_first := q.takeUntil y hy_in_q
      let q_rest := q.dropUntil y hy_in_q
      have hq_split : q_first.append q_rest = q := q.take_spec hy_in_q
      have hq_len : q_first.length + q_rest.length = q.length := by
        have := congr_arg Walk.length hq_split
        rwa [Walk.length_append] at this
      -- α = cons h_b q_first : Walk y y, length 1 + q_first.length.
      -- β = q_rest : Walk y y, length q_rest.length.
      -- α.length + β.length = 1 + q.length = (Walk.cons h_b q).length = w'.length = n.
      let α : G.Walk y y := Walk.cons h_b q_first
      let β : G.Walk y y := q_rest
      have hα_len : α.length = 1 + q_first.length := by
        change (Walk.cons h_b q_first).length = 1 + q_first.length
        rw [Walk.length_cons]; omega
      have hβ_len : β.length = q_rest.length := rfl
      have hsum : α.length + β.length = n := by
        rw [hα_len, hβ_len]
        -- (1 + q_first.length) + q_rest.length = n
        -- = 1 + q.length (from hq_len) = (cons h_b q).length = w.length = n
        have : (Walk.cons h_b q).length = n := hw'_len.trans hwn
        rw [Walk.length_cons] at this
        omega
      -- q_rest.length ≥ 1 (because y has count ≥ 2 in q.support, the takeUntil count is 1,
      -- so the rest contributes ≥ 1).
      have hq_rest_pos : 0 < q_rest.length := by
        -- count y in q.support = count y in q_first.support + count y in q_rest.support.tail.
        -- count y in q_first.support = 1.
        -- So count y in q_rest.support.tail = (count in q.support) - 1 ≥ 1.
        -- q_rest.support.tail.length = q_rest.length, and tail has y, so non-empty.
        have hsplit_supp : q.support = q_first.support ++ q_rest.support.tail := by
          have := congr_arg Walk.support hq_split
          rw [Walk.support_append] at this
          exact this.symm
        have hcount_first : List.count y q_first.support = 1 :=
          q.count_support_takeUntil_eq_one hy_in_q
        have hcount_split : List.count y q.support =
            List.count y q_first.support + List.count y q_rest.support.tail := by
          rw [hsplit_supp, List.count_append]
        have hcount_tail : 1 ≤ List.count y q_rest.support.tail := by omega
        have hmem_tail : y ∈ q_rest.support.tail := List.count_pos_iff.mp (by omega)
        have hpos : 0 < q_rest.support.tail.length :=
          List.length_pos_of_mem hmem_tail
        have hsl : q_rest.support.length = q_rest.length + 1 := q_rest.length_support
        have htl : q_rest.support.tail.length = q_rest.length := by
          rw [List.length_tail, hsl]; omega
        omega
      -- Both α.length, β.length < n.
      have hβ_lt : β.length < n := by
        -- α.length ≥ 1, so β.length ≤ n - 1 < n.
        have : α.length ≥ 1 := by rw [hα_len]; omega
        omega
      have hα_lt : α.length < n := by
        -- β.length ≥ 1, so α.length ≤ n - 1 < n.
        rw [hβ_len] at hq_rest_pos
        omega
      -- One of α, β is odd. Since α.length + β.length = n is odd:
      have hodd_n : Odd n := hwn ▸ hodd
      have hodd_split : Odd α.length ∨ Odd β.length := by
        rcases Nat.even_or_odd α.length with hα_even | hα_odd
        · right
          have hodd_sum : Odd (α.length + β.length) := hsum ▸ hodd_n
          rcases hodd_sum with ⟨k, hk⟩
          rcases hα_even with ⟨m, hm⟩
          refine ⟨k - m, ?_⟩; omega
        · left; exact hα_odd
      -- Apply IH to whichever is odd.
      have hsupp_α : ∀ x ∈ α.support, x ∈ w.support := by
        intro x hx
        -- α.support = y :: q_first.support, q_first ⊆ q.support.
        -- q.support ⊆ w'.support. w'.support has same elements as w.support (rotation perm).
        have h1 : x ∈ (Walk.cons h_b q_first).support := hx
        rw [Walk.support_cons, List.mem_cons] at h1
        rcases h1 with rfl | h2
        · -- x = y
          exact hy_mem
        · have : x ∈ q.support := q.support_takeUntil_subset_support hy_in_q h2
          have : x ∈ (Walk.cons h_b q).support := by
            rw [Walk.support_cons]; exact List.mem_cons.mpr (Or.inr this)
          have hxw' : x ∈ w'.support := by rw [hw'_eq]; exact this
          rw [Walk.mem_support_rotate_iff] at hxw'
          exact hxw'
      have hsupp_β : ∀ x ∈ β.support, x ∈ w.support := by
        intro x hx
        have h1 : x ∈ q_rest.support := hx
        have h2 : x ∈ q.support := q.support_dropUntil_subset_support hy_in_q h1
        have : x ∈ (Walk.cons h_b q).support := by
          rw [Walk.support_cons]; exact List.mem_cons.mpr (Or.inr h2)
        have hxw' : x ∈ w'.support := by rw [hw'_eq]; exact this
        rw [Walk.mem_support_rotate_iff] at hxw'
        exact hxw'
      rcases hodd_split with hα_odd | hβ_odd
      · obtain ⟨v', c', hc', hc'_odd, hc'_len, hc'_supp⟩ :=
          ih α.length hα_lt α rfl hα_odd
        refine ⟨v', c', hc', hc'_odd, hc'_len.trans hα_lt.le, ?_⟩
        intro x hx
        exact hsupp_α _ (hc'_supp x hx)
      · obtain ⟨v', c', hc', hc'_odd, hc'_len, hc'_supp⟩ :=
          ih β.length hβ_lt β rfl hβ_odd
        refine ⟨v', c', hc', hc'_odd, hc'_len.trans hβ_lt.le, ?_⟩
        intro x hx
        exact hsupp_β _ (hc'_supp x hx)

/--
For finite induced subgraphs, non-bipartite implies the existence of a short odd cycle
(length at most the number of vertices). The proof: bipartite ↔ all closed walks even
(`two_colorable_iff_forall_loop_even`), so non-bipartite gives an odd closed walk;
then `exists_isCycle_of_odd_closedWalk` extracts an odd cycle of length ≤ walk length;
the cycle's support has nodup tail of size = cycle length, all in `↑X`, hence bounded
by `X.card`.
-/
theorem finite_nonbipartite_induce_has_short_odd_cycle
    {V : Type u}
    (G : SimpleGraph V) (X : Finset V)
    (h : ¬ (G.induce ((↑X : Set V))).IsBipartite) :
    ∃ (v : ((↑X : Set V) : Type u))
      (w : (G.induce ((↑X : Set V))).Walk v v),
        w.IsCycle ∧ Odd w.length ∧ w.length ≤ X.card := by
  classical
  -- Get an odd closed walk in (G.induce ↑X).
  have h2 : ¬ (G.induce ((↑X : Set V))).Colorable 2 := h
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at h2
  push Not at h2
  obtain ⟨u, w, hw_not_even⟩ := h2
  rw [Nat.not_even_iff_odd] at hw_not_even
  -- Apply helper to get an odd cycle.
  obtain ⟨v, c, hcyc, hodd, hlen, hsupp⟩ :=
    exists_isCycle_of_odd_closedWalk w.length w rfl hw_not_even
  refine ⟨v, c, hcyc, hodd, ?_⟩
  -- Bound the length by X.card. The cycle's support tail is nodup of length = c.length,
  -- all elements in ↑X (a Finset of size X.card). So c.length ≤ X.card.
  have htail_nodup : c.support.tail.Nodup := hcyc.support_nodup
  -- c.support.tail has length = c.length.
  have htail_len : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]; omega
  -- The tail elements are all in ↑X.
  -- Map to V via Subtype.val.
  -- We can show the tail.toFinset has size = c.length, embedded in X (as Finset).
  -- toFinset card = length when nodup. And toFinset ⊆ X (the underlying Finset).
  have hsub : (c.support.tail.map (·.val) : List V).toFinset ⊆ X := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact a.property
  have hmap_nodup : (c.support.tail.map (·.val) : List V).Nodup := by
    rw [List.nodup_map_iff_inj_on htail_nodup]
    intros _ _ _ _ heq; exact Subtype.ext heq
  have hcard : (c.support.tail.map (·.val) : List V).toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hmap_nodup, List.length_map, htail_len]
  have : (c.support.tail.map (·.val) : List V).toFinset.card ≤ X.card :=
    Finset.card_le_card hsub
  omega

/-- **Helper.** `(genMyc s G).induce (↑X \ {apex})` is bipartite when
`(G.induce ↑(projFinset X))` is bipartite. This is the `T = ∅` case of
`liftedDeletion_survivor_isBipartite`. -/
private lemma genMyc_induce_diff_apex_isBipartite {V : Type u} [DecidableEq V] {s : ℕ}
    (G : SimpleGraph V) (X : Finset (MycVerts s V))
    (hbip : (G.induce ((↑(projFinset X) : Set V))).IsBipartite) :
    ((genMyc s G).induce
        ((↑X : Set (MycVerts s V)) \ ({apex s V} : Set (MycVerts s V)))).IsBipartite := by
  classical
  have key := liftedDeletion_survivor_isBipartite G X ∅ (Finset.empty_subset _) (by
    rw [Finset.coe_empty, Set.sdiff_empty]; exact hbip)
  -- Show ↑X \ ↑(liftedDeletion X ∅) = ↑X \ {apex s V}
  have hset : ((↑X : Set (MycVerts s V)) \ (↑(liftedDeletion X ∅) : Set (MycVerts s V)))
      = ((↑X : Set (MycVerts s V)) \ ({apex s V} : Set (MycVerts s V))) := by
    ext a
    simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hX, hND⟩
      refine ⟨hX, ?_⟩
      intro hap
      apply hND
      rw [mem_liftedDeletion]
      exact ⟨hX, Or.inr hap⟩
    · rintro ⟨hX, hap⟩
      refine ⟨hX, ?_⟩
      intro hin
      rw [mem_liftedDeletion] at hin
      obtain ⟨_, h⟩ := hin
      rcases h with ⟨_, _, hT, _⟩ | hap'
      · exact (Finset.notMem_empty _ hT).elim
      · exact hap hap'
  rw [hset] at key
  exact key

/-! ### Helpers used by `finite_oct_profile` -/

/-- The function `m ↦ (g m - 1) / s` is monotone whenever `g` is. -/
private lemma h_monotone {g : ℕ → ℕ} (hg : Monotone g) (s : ℕ) :
    Monotone (fun m => (g m - 1) / s) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.sub_le_sub_right (hg hab) 1)

/-- The function `m ↦ (g m - 1) / s` tends to infinity whenever `g` does. -/
private lemma h_tendsto {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) {s : ℕ} (hs : 0 < s) :
    Tendsto (fun m => (g m - 1) / s) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro K
  rw [Filter.tendsto_atTop_atTop] at hg
  obtain ⟨N, hN⟩ := hg (s * K + 1)
  refine ⟨N, fun m hm => ?_⟩
  have h := hN m hm
  have h1 : s * K ≤ g m - 1 := by omega
  exact (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; exact h1)

/-- For `r ≥ 2`, the recursive class predicate at `r + 1` follows from a witness at `r`. -/
private lemma IsRecursivelyBuiltMr_succ_of_genMyc {V : Type u} {W : Type u}
    {r : ℕ} (hr : 2 ≤ r)
    {H_inner : SimpleGraph W} {s : ℕ} (hs : 1 ≤ s)
    (h_inner : IsRecursivelyBuiltMr r H_inner)
    {G : SimpleGraph V} (hG_iso : Nonempty (G ≃g genMyc s H_inner)) :
    IsRecursivelyBuiltMr (r + 1) G := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  -- Now `r + 1 = (k + 2) + 1 = k + 3`.
  change IsRecursivelyBuiltMr (k + 3) G
  exact ⟨W, H_inner, s, hs, h_inner, hG_iso⟩

/-- `K₂ = completeGraph (Fin 2)` is bipartite. -/
private lemma completeGraphFin2_isBipartite :
    (completeGraph (Fin 2)).IsBipartite := by
  refine ⟨Coloring.mk id ?_⟩
  intro v w h
  exact h

/-- `(projFinset X).card ≤ X.card`. -/
private lemma projFinset_card_le {V : Type u} [DecidableEq V] {s : ℕ}
    (X : Finset (MycVerts s V)) :
    (projFinset X).card ≤ X.card := by
  classical
  unfold projFinset
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum (s := X) (f := fun a =>
      (match a with | Sum.inl (_, v) => ({v} : Finset V) | Sum.inr () => (∅ : Finset V)).card)
    (g := fun _ => 1) (h := fun a _ => ?_)) ?_
  · match a with
    | Sum.inl (_, v) => simp
    | Sum.inr () => simp
  · simp

/-- **Theorem 4.1 (Finite local oct profile).** For every nondecreasing unbounded
`g : ℕ → ℕ` and every `r ≥ 2`, there exists a finite graph `H` in the recursively
built class `Mᵣ` such that every nonempty induced subgraph `H[X]` satisfies
`oct(H[X]) ≤ g(|X|)`.

In particular `χ(H) = r` (combine `stiebitz_lower_bound` with `genMyc_chromaticNumber_le_succ`).
-/
theorem finite_oct_profile (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := by
  classical
  -- Induction on `r ≥ 2`. The induction motive is parameterized over `g` so the IH
  -- can be applied to a different (rescaled) function in the inductive step.
  induction r, hr using Nat.le_induction generalizing g with
  | base =>
      -- Base: r = 2. Take H := completeGraph (Fin 2).
      refine ⟨Fin 2, inferInstance, inferInstance, completeGraph (Fin 2), ?_, ?_⟩
      · -- IsRecursivelyBuiltMr 2 (completeGraph (Fin 2))
        change Nonempty ((completeGraph (Fin 2)) ≃g (completeGraph (Fin 2)))
        exact ⟨(SimpleGraph.Iso.refl : completeGraph (Fin 2) ≃g completeGraph (Fin 2))⟩
      · -- For every nonempty X, oct K₂ X = 0 ≤ g X.card.
        intro X _hX
        have hK2 : (completeGraph (Fin 2)).IsBipartite := completeGraphFin2_isBipartite
        obtain ⟨c⟩ := hK2
        have hbip : ((completeGraph (Fin 2)).induce
            ((↑X : Set (Fin 2)))).IsBipartite := by
          refine ⟨Coloring.mk (fun a => c a.val) ?_⟩
          intro a b hab
          exact c.valid hab
        have hoct0 : oct (completeGraph (Fin 2)) X = 0 := by
          rw [oct_eq_zero_iff]; exact hbip
        rw [hoct0]; exact Nat.zero_le _
  | succ r hr IH =>
      -- Inductive step: given hypothesis at r, produce a witness at r + 1.
      -- Step 1: choose a threshold N₀ with g m ≥ 1 for m ≥ N₀.
      have hg_top' := hg_top
      rw [Filter.tendsto_atTop_atTop] at hg_top'
      obtain ⟨N₀, hN₀⟩ := hg_top' 1
      -- Step 2: set s := N₀ + 2 (so 2s+1 > N₀ and s ≥ 1).
      set s : ℕ := N₀ + 2 with hs_def
      have hs_pos : 0 < s := by omega
      have hs_ge_one : 1 ≤ s := by omega
      -- Step 3: define h := fun m => (g m - 1) / s.
      set h : ℕ → ℕ := fun m => (g m - 1) / s with hh_def
      have hh_mono : Monotone h := h_monotone hg_mono s
      have hh_top : Tendsto h atTop atTop := h_tendsto hg_top hs_pos
      -- Step 4: apply IH at (h, r).
      obtain ⟨V_inner, _Vfin, _Vdec, G_inner, hRec, hOct_inner⟩ :=
        IH h hh_mono hh_top
      -- Step 5: set H := genMyc s G_inner.
      let H : SimpleGraph (MycVerts s V_inner) := genMyc s G_inner
      refine ⟨MycVerts s V_inner, inferInstance, inferInstance, H, ?_, ?_⟩
      · -- IsRecursivelyBuiltMr (r + 1) H.
        exact IsRecursivelyBuiltMr_succ_of_genMyc hr hs_ge_one hRec
          ⟨(SimpleGraph.Iso.refl : H ≃g H)⟩
      · -- The OCT bound.
        intro X hXne
        set P : Finset V_inner := projFinset X with hP_def
        -- Bound `oct G_inner P` by `h X.card`.
        have hCardP_le : P.card ≤ X.card := projFinset_card_le X
        have hOctP_le_hX : oct G_inner P ≤ h X.card := by
          by_cases hPne : P.Nonempty
          · exact le_trans (hOct_inner P hPne) (hh_mono hCardP_le)
          · -- P = ∅, so oct G_inner P = 0 ≤ h X.card.
            rw [Finset.not_nonempty_iff_eq_empty] at hPne
            rw [hPne]
            simp
        -- Apply Lemma 3.1.
        have hL31 : oct H X ≤ s * oct G_inner P + (if apex s V_inner ∈ X then 1 else 0) :=
          oct_genMyc_le s G_inner X
        by_cases hCase : 1 ≤ g X.card
        · -- Case 1: g X.card ≥ 1.
          -- s * h X.card + 1 ≤ g X.card.
          have hKey : s * h X.card + 1 ≤ g X.card := by
            have : h X.card * s ≤ g X.card - 1 := Nat.div_mul_le_self _ _
            have hge : g X.card ≥ 1 := hCase
            calc s * h X.card + 1 = h X.card * s + 1 := by ring
              _ ≤ (g X.card - 1) + 1 := by omega
              _ = g X.card := by omega
          have hifle : (if apex s V_inner ∈ X then 1 else 0) ≤ 1 := by
            split_ifs <;> simp
          calc oct H X ≤ s * oct G_inner P + (if apex s V_inner ∈ X then 1 else 0) := hL31
            _ ≤ s * h X.card + 1 := by
                refine add_le_add (Nat.mul_le_mul_left s hOctP_le_hX) hifle
            _ ≤ g X.card := hKey
        · -- Case 2: g X.card = 0.
          push Not at hCase
          have hg0 : g X.card = 0 := by omega
          -- From g X.card = 0, deduce X.card < N₀ (else g X.card ≥ 1 would hold).
          have hCardLt : X.card < N₀ := by
            by_contra hcontra
            push Not at hcontra
            have := hN₀ X.card hcontra
            omega
          have hCardLt2s : X.card < 2 * s + 1 := by omega
          -- h X.card = 0 since g X.card = 0.
          have hhX0 : h X.card = 0 := by
            simp [hh_def, hg0]
          -- oct G_inner P ≤ h X.card = 0.
          have hOctP0 : oct G_inner P = 0 := by
            have := hOctP_le_hX
            rw [hhX0] at this
            omega
          -- (G_inner).induce ↑P is bipartite.
          have hPbip : (G_inner.induce ((↑P : Set V_inner))).IsBipartite := by
            rw [← oct_eq_zero_iff]
            exact hOctP0
          -- (genMyc s G_inner).induce (↑X \ {apex}) is bipartite.
          have hHdiffBip :
              (H.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))).IsBipartite :=
            genMyc_induce_diff_apex_isBipartite G_inner X hPbip
          -- Show H.induce ↑X is bipartite.
          suffices hbip : (H.induce ((↑X : Set (MycVerts s V_inner)))).IsBipartite by
            have hoctH0 : oct H X = 0 := by
              rw [oct_eq_zero_iff]; exact hbip
            rw [hoctH0]; exact Nat.zero_le _
          -- Suppose not. Get an odd cycle of length ≤ X.card.
          by_contra hnotbip
          obtain ⟨v, w, hwcycle, hwodd, hwlen⟩ :=
            finite_nonbipartite_induce_has_short_odd_cycle H X hnotbip
          have hwlen2s : w.length < 2 * s + 1 := lt_of_le_of_lt hwlen hCardLt2s
          -- Step A: apex s V_inner ∈ X.
          have hApexInX : apex s V_inner ∈ X := by
            by_contra hapex
            -- If apex ∉ X, then ↑X \ {apex} = ↑X, so the whole induce is bipartite.
            have hsetEq : ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))
                = (↑X : Set (MycVerts s V_inner)) := by
              ext a
              simp only [Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
              refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
              intro hap; subst hap
              exact hapex h
            rw [hsetEq] at hHdiffBip
            exact hnotbip hHdiffBip
          -- Map w through the embedding induce ↑X ↪ H.
          set f : H.induce (↑X : Set (MycVerts s V_inner)) ↪g H := Embedding.induce _ with hf_def
          set wH : H.Walk v.val v.val := Walk.map f.toHom w with hwH_def
          have hwHlen : wH.length = w.length := Walk.length_map f.toHom w
          have hwHsupp : wH.support = w.support.map f := Walk.support_map f.toHom w
          -- Step B: apex must lie on the support of wH (the lifted walk).
          have hApexInSupport : apex s V_inner ∈ wH.support := by
            by_contra hnot
            -- All vertices of wH are in (↑X \ {apex}).
            have hsupp_in : ∀ x ∈ wH.support, x ∈ ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner))) := by
              intro x hx
              rw [hwHsupp, List.mem_map] at hx
              obtain ⟨y, hy_supp, hxy⟩ := hx
              refine ⟨?_, ?_⟩
              · rw [← hxy]
                show f y ∈ (↑X : Set (MycVerts s V_inner))
                exact y.prop
              · intro hap
                apply hnot
                rw [hwHsupp, List.mem_map]
                exact ⟨y, hy_supp, hxy.trans hap⟩
            -- Use Walk.induce to lift wH to a walk in H.induce (↑X \ {apex}).
            let wDiff := wH.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner))) hsupp_in
            -- wDiff has the same length as wH via `map_induce` + `length_map`.
            have hwDifflen : wDiff.length = wH.length := by
              have hmap := Walk.map_induce (s := ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))) wH hsupp_in
              have := congrArg Walk.length hmap
              simp only [Walk.length_map] at this
              exact this
            have hwDifflen' : wDiff.length = w.length := by rw [hwDifflen, hwHlen]
            -- wDiff is a closed walk in a bipartite graph, so it has even length.
            obtain ⟨c⟩ := hHdiffBip
            let c' : (H.induce ((↑X : Set (MycVerts s V_inner))
                \ ({apex s V_inner} : Set (MycVerts s V_inner)))).Coloring Bool :=
              SimpleGraph.recolorOfEquiv _ finTwoEquiv c
            have heven : Even wDiff.length := (c'.even_length_iff_congr wDiff).mpr Iff.rfl
            rw [hwDifflen'] at heven
            exact (Nat.not_odd_iff_even.mpr heven) hwodd
          -- Step C: rotate wH to start/end at apex.
          set wApex : H.Walk (apex s V_inner) (apex s V_inner) :=
            wH.rotate (apex s V_inner) hApexInSupport with hwApex_def
          -- Length-rotate via the dart-rotation lemma.
          have hwApexlen : wApex.length = wH.length := by
            have hd : wApex.darts ~r wH.darts :=
              Walk.rotate_darts wH (apex s V_inner) hApexInSupport
            have := hd.perm.length_eq
            rw [Walk.length_darts, Walk.length_darts] at this
            exact this
          have hwApexLen2 : wApex.length = w.length := by rw [hwApexlen, hwHlen]
          have hwApexOdd : Odd wApex.length := by rw [hwApexLen2]; exact hwodd
          have hwApexLt : wApex.length < 2 * s + 1 := by rw [hwApexLen2]; exact hwlen2s
          -- Apply Lemma 3.2.
          have := genMyc_oddClosedWalk_through_apex_long hs_ge_one G_inner wApex hwApexOdd
          omega

/-! ## §5. Infinite construction -/

/-! ### Helpers for `infinite_chromatic_local_oct` -/

/-- The rescaled function `gᵣ(m) := g(m) / 2^(r+2)` is monotone whenever `g` is. -/
private lemma g_div_pow_monotone {g : ℕ → ℕ} (hg : Monotone g) (r : ℕ) :
    Monotone (fun m => g m / 2 ^ (r + 2)) := fun _ _ hab =>
  Nat.div_le_div_right (hg hab)

/-- The rescaled function `gᵣ(m) := g(m) / 2^(r+2)` tends to infinity whenever `g` does. -/
private lemma g_div_pow_tendsto {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) (r : ℕ) :
    Tendsto (fun m => g m / 2 ^ (r + 2)) atTop atTop := by
  have hpos : 0 < 2 ^ (r + 2) := Nat.two_pow_pos _
  rw [Filter.tendsto_atTop_atTop]
  intro K
  rw [Filter.tendsto_atTop_atTop] at hg
  obtain ⟨N, hN⟩ := hg (2 ^ (r + 2) * K)
  refine ⟨N, fun m hm => ?_⟩
  have hbig : 2 ^ (r + 2) * K ≤ g m := hN m hm
  exact (Nat.le_div_iff_mul_le hpos).mpr (by rw [Nat.mul_comm]; exact hbig)

/-- Geometric sum bound: `∑_{r ∈ R} n / 2^(r+2) ≤ n`. The total tail of the series
`1/4 + 1/8 + ...` is `1/2 ≤ 1`. -/
private lemma sum_div_two_pow_le (R : Finset ℕ) (n : ℕ) :
    ∑ r ∈ R, n / 2 ^ (r + 2) ≤ n := by
  -- Auxiliary: stronger bound over `Finset.range N`.
  have key : ∀ N : ℕ,
      (∑ r ∈ Finset.range N, n / 2 ^ (r + 2)) + n / 2 ^ (N + 1) ≤ n := by
    intro N
    induction N with
    | zero => simpa using Nat.div_le_self n 2
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hkey : 2 * (n / 2 ^ (k + 2)) ≤ n / 2 ^ (k + 1) := by
          have h2 : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
          rw [show (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) from by ring]
          rw [Nat.mul_comm, Nat.le_div_iff_mul_le h2, Nat.mul_assoc]
          exact Nat.div_mul_le_self _ _
        have h_sum_add : n / 2 ^ (k + 2) + n / 2 ^ ((k + 1) + 1)
            = 2 * (n / 2 ^ (k + 2)) := by
          have : (k + 1) + 1 = k + 2 := by ring
          rw [this]; ring
        calc (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + n / 2 ^ (k + 2)
              + n / 2 ^ ((k + 1) + 1)
            = (∑ r ∈ Finset.range k, n / 2 ^ (r + 2))
                + (n / 2 ^ (k + 2) + n / 2 ^ ((k + 1) + 1)) := by ring
          _ = (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + 2 * (n / 2 ^ (k + 2)) := by
                rw [h_sum_add]
          _ ≤ (∑ r ∈ Finset.range k, n / 2 ^ (r + 2)) + n / 2 ^ (k + 1) :=
                Nat.add_le_add_left hkey _
          _ ≤ n := ih
  by_cases hR : R = ∅
  · simp [hR]
  have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hR
  have hsub : R ⊆ Finset.range (R.max' hRne + 1) := by
    intro r hr
    simp only [Finset.mem_range]
    have : r ≤ R.max' hRne := Finset.le_max' R r hr
    omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _)).trans
    (Nat.le_of_add_right_le (key (R.max' hRne + 1)))

/--
**Theorem 1.1 (PDF / paper).** For every nondecreasing unbounded `g : ℕ → ℕ`, there
exists a graph `G` with infinite chromatic number such that every finite induced
subgraph `F` has `oct(F) ≤ g(|V(F)|)`.

The witness is a disjoint union of finite `Hᵣ` from `finite_oct_profile`, each
calibrated against `gᵣ(m) := ⌊g(m) / 2^(r+2)⌋`. The global vertex type is `ℕ × ℕ`,
where component `r` lives at `{r} × Fin (Fintype.card Vᵣ)` (lifted to `ℕ × ℕ`),
and remaining vertices `(r, i)` with `i ≥ card Vᵣ` are isolated.
-/
theorem infinite_chromatic_local_oct (stiebitz_lower_bound : StiebitzLowerBound)
    (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := by
  classical
  -- Step 1. For each `r : ℕ`, extract a per-component graph from `finite_oct_profile`.
  -- We choose data uniformly via `Classical.choose`.
  have mk : ∀ r : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), IsRecursivelyBuiltMr (r + 2) G ∧
        ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card / 2 ^ (r + 2) := by
    intro r
    exact finite_oct_profile (fun m => g m / 2 ^ (r + 2))
      (g_div_pow_monotone hg_mono r) (g_div_pow_tendsto hg_top r) (r + 2) (by omega)
  choose Vᵣ Vᵣ_fintype Vᵣ_deceq Hᵣ Hᵣ_rec Hᵣ_oct using mk
  -- Equivalence Vᵣ ≃ Fin (card Vᵣ)
  let eᵣ : ∀ r, Vᵣ r ≃ Fin (Fintype.card (Vᵣ r)) := fun r =>
    @Fintype.equivFin (Vᵣ r) (Vᵣ_fintype r)
  -- Step 2. Define the global graph G on ℕ × ℕ.
  let G : SimpleGraph (ℕ × ℕ) := {
    Adj := fun p q => ∃ (r : ℕ) (u v : Vᵣ r),
      p = (r, (eᵣ r u).val) ∧ q = (r, (eᵣ r v).val) ∧ (Hᵣ r).Adj u v
    symm := ⟨by
      rintro p q ⟨r, u, v, hp, hq, hadj⟩
      exact ⟨r, v, u, hq, hp, hadj.symm⟩⟩
    loopless := ⟨by
      rintro p ⟨r, u, v, hp, hq, hadj⟩
      rw [hp] at hq
      have hval : (eᵣ r u).val = (eᵣ r v).val := ((Prod.mk.injEq _ _ _ _).mp hq).2
      have huv : eᵣ r u = eᵣ r v := Fin.eq_of_val_eq hval
      rw [(eᵣ r).injective huv] at hadj
      exact (Hᵣ r).irrefl hadj⟩
  }
  -- Component homomorphism Hᵣ →g G.
  let φᵣ : ∀ r, (Hᵣ r) →g G := fun r => ⟨fun u => (r, (eᵣ r u).val),
    fun {u v} huv => ⟨r, u, v, rfl, rfl, huv⟩⟩
  -- We will use both directions: we also need the inverse of (eᵣ r) restricted to
  -- "vertices at component r in X". For (r, i) with i < card (Vᵣ r), the corresponding
  -- vertex is `(eᵣ r).symm ⟨i, hi⟩`.
  refine ⟨ℕ × ℕ, inferInstance, G, ?_, ?_⟩
  · -- Step 3: prove G.chromaticNumber = ⊤.
    by_contra hne
    have hne' : G.chromaticNumber ≠ ⊤ := hne
    rw [SimpleGraph.chromaticNumber_ne_top_iff_exists] at hne'
    obtain ⟨n, hcol⟩ := hne'
    -- The component Hₙ is colorable with n colors via φₙ.
    have hcolHn : (Hᵣ n).Colorable n := SimpleGraph.Colorable.of_hom (φᵣ n) hcol
    have hbound : ((n + 2 : ℕ) : ℕ∞) ≤ (Hᵣ n).chromaticNumber :=
      stiebitz_lower_bound (Hᵣ n) (n + 2) (Hᵣ_rec n)
    have hcolBound : (Hᵣ n).chromaticNumber ≤ (n : ℕ∞) :=
      hcolHn.chromaticNumber_le
    have habs : ((n + 2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := hbound.trans hcolBound
    -- Contradiction since n + 2 > n.
    have h_lt : (n : ℕ∞) < ((n + 2 : ℕ) : ℕ∞) := by
      have h : n < n + 2 := by omega
      exact_mod_cast h
    exact absurd (lt_of_lt_of_le h_lt habs) (lt_irrefl _)
  · -- Step 4: prove the local OCT bound.
    intro X hXne
    -- For each r ∈ ℕ, define the per-component vertex set and transversal.
    -- Yᵣ r is the set of u : Vᵣ r such that (r, (eᵣ r u).val) ∈ X.
    set Y : ∀ r, Finset (Vᵣ r) := fun r =>
      (Finset.univ : Finset (Vᵣ r)).filter (fun u => (r, (eᵣ r u).val) ∈ X)
      with hY_def
    -- Witness Tᵣ : Finset (Vᵣ r) from oct_witness on Hᵣ.
    let Tdata : ∀ r, { T : Finset (Vᵣ r) // T ⊆ Y r ∧ T.card = oct (Hᵣ r) (Y r) ∧
        ((Hᵣ r).induce ((↑(Y r) : Set (Vᵣ r)) \ ↑T)).IsBipartite } := fun r =>
      ⟨(oct_witness (Hᵣ r) (Y r)).choose,
        ((oct_witness (Hᵣ r) (Y r)).choose_spec)⟩
    set T : ∀ r, Finset (Vᵣ r) := fun r => (Tdata r).1 with hT_def
    have hTsub : ∀ r, T r ⊆ Y r := fun r => (Tdata r).2.1
    have hTcard : ∀ r, (T r).card = oct (Hᵣ r) (Y r) := fun r => (Tdata r).2.2.1
    have hTbip : ∀ r, ((Hᵣ r).induce
        ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).IsBipartite := fun r => (Tdata r).2.2.2
    -- The global deletion set: union of liftings of Tᵣ for r ∈ R.
    let R : Finset ℕ := X.image Prod.fst
    let lift : ∀ r, Vᵣ r → ℕ × ℕ := fun r u => (r, (eᵣ r u).val)
    set Tglob : Finset (ℕ × ℕ) :=
      R.biUnion (fun r => (T r).image (lift r))
      with hTglob_def
    -- Tglob ⊆ X.
    have hTglob_sub : Tglob ⊆ X := by
      intro a ha
      rw [hTglob_def, Finset.mem_biUnion] at ha
      obtain ⟨r, _hrR, ha'⟩ := ha
      rw [Finset.mem_image] at ha'
      obtain ⟨u, huT, hu_eq⟩ := ha'
      have huY : u ∈ Y r := hTsub r huT
      rw [hY_def, Finset.mem_filter] at huY
      rw [← hu_eq]; exact huY.2
    -- Tglob.card bounded: each lift fiber is injective, so the biUnion gives the sum.
    have hlift_inj : ∀ r, Function.Injective (lift r) := by
      intro r u v huv
      have hval : (eᵣ r u).val = (eᵣ r v).val := ((Prod.mk.injEq _ _ _ _).mp huv).2
      exact (eᵣ r).injective (Fin.eq_of_val_eq hval)
    have h_lift_disj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ →
        Disjoint ((T r₁).image (lift r₁)) ((T r₂).image (lift r₂)) := by
      intro r₁ _ r₂ _ hne
      rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      rw [Finset.mem_image] at ha₁ ha₂
      obtain ⟨u, _, hu⟩ := ha₁
      obtain ⟨v, _, hv⟩ := ha₂
      rw [← hu] at hv
      exact hne (((Prod.mk.injEq _ _ _ _).mp hv).1).symm
    have hTglob_card : Tglob.card = ∑ r ∈ R, (T r).card := by
      rw [hTglob_def]
      rw [Finset.card_biUnion (fun r₁ hr₁ r₂ hr₂ hne => h_lift_disj r₁ hr₁ r₂ hr₂ hne)]
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.card_image_of_injective _ (hlift_inj r)
    -- Each (T r).card ≤ g X.card / 2^(r+2).
    have hYcard_le_X : ∀ r, (Y r).card ≤ X.card := by
      intro r
      -- The map u ↦ (r, (eᵣ r u).val) sends Y r injectively into X.
      have hinj_card : (Y r).card = ((Y r).image (lift r)).card :=
        (Finset.card_image_of_injective (Y r) (hlift_inj r)).symm
      rw [hinj_card]
      apply Finset.card_le_card
      · intro a ha
        rw [Finset.mem_image] at ha
        obtain ⟨u, huY, huEq⟩ := ha
        rw [hY_def, Finset.mem_filter] at huY
        rw [← huEq]; exact huY.2
    have hTr_le : ∀ r, (T r).card ≤ g X.card / 2 ^ (r + 2) := by
      intro r
      rw [hTcard]
      by_cases hYne : (Y r).Nonempty
      · refine le_trans (Hᵣ_oct r (Y r) hYne) ?_
        exact g_div_pow_monotone hg_mono r (hYcard_le_X r)
      · rw [Finset.not_nonempty_iff_eq_empty] at hYne
        rw [hYne]; simp
    -- Sum bound: ∑ r ∈ R, (T r).card ≤ g X.card.
    have hsum_le : ∑ r ∈ R, (T r).card ≤ g X.card := by
      refine le_trans (Finset.sum_le_sum (fun r _ => hTr_le r)) ?_
      exact sum_div_two_pow_le R (g X.card)
    have hTglob_card_le : Tglob.card ≤ g X.card := by
      rw [hTglob_card]; exact hsum_le
    -- Show survivor (G.induce (↑X \ ↑Tglob)) is bipartite.
    have hsurv_bip :
        (G.induce ((↑X : Set (ℕ × ℕ)) \ (↑Tglob : Set (ℕ × ℕ)))).IsBipartite := by
      classical
      -- Per-component bipartite colorings from `hTbip`.
      let cᵣ : ∀ r, ((Hᵣ r).induce
          ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).Coloring (Fin 2) :=
        fun r => Classical.choice (hTbip r)
      -- A "compute" function for a vertex (r, i) ∈ ℕ × ℕ. Returns a Fin 2 if `(r,i)` is in
      -- `X` and `i < card (Vᵣ r)` and the corresponding `Vᵣ r` element is in `Y r \ T r`;
      -- returns 0 otherwise.
      let getColor : ℕ × ℕ → Fin 2 := fun p =>
        if hi : p.2 < Fintype.card (Vᵣ p.1) then
          let u := (eᵣ p.1).symm ⟨p.2, hi⟩
          if hYT : u ∈ Y p.1 ∧ u ∉ T p.1 then
            cᵣ p.1 ⟨u, ⟨hYT.1, hYT.2⟩⟩
          else 0
        else 0
      -- Key fact: getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, _⟩ when u ∈ Y r \ T r.
      have hget_eq : ∀ r (u : Vᵣ r) (huY : u ∈ Y r) (huT : u ∉ T r),
          getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, ⟨huY, huT⟩⟩ := by
        intro r u huY huT
        show getColor (r, (eᵣ r u).val) = cᵣ r ⟨u, ⟨huY, huT⟩⟩
        have hlt : (eᵣ r u).val < Fintype.card (Vᵣ r) := (eᵣ r u).isLt
        -- Compute (eᵣ r).symm at this index — equals u.
        have hsymm : (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ = u := by
          conv_rhs => rw [← (eᵣ r).symm_apply_apply u]
        -- Unfold getColor
        change (if hi : (eᵣ r u).val < Fintype.card (Vᵣ r) then
              if hYT : (eᵣ r).symm ⟨(eᵣ r u).val, hi⟩ ∈ Y r ∧
                       (eᵣ r).symm ⟨(eᵣ r u).val, hi⟩ ∉ T r then
                cᵣ r ⟨(eᵣ r).symm ⟨(eᵣ r u).val, hi⟩, ⟨hYT.1, hYT.2⟩⟩
              else 0
            else 0) = cᵣ r ⟨u, ⟨huY, huT⟩⟩
        rw [dif_pos hlt]
        rw [dif_pos (show (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ ∈ Y r ∧
                          (eᵣ r).symm ⟨(eᵣ r u).val, hlt⟩ ∉ T r by
                       rw [hsymm]; exact ⟨huY, huT⟩)]
        congr
      let color : ((↑X : Set (ℕ × ℕ)) \ ↑Tglob : Set _) → Fin 2 :=
        fun a => getColor a.val
      refine ⟨Coloring.mk color ?_⟩
      rintro ⟨a, haX, haT⟩ ⟨b, hbX, hbT⟩ hab
      have hGab : G.Adj a b := hab
      obtain ⟨r, u, v, hau, hbv, huv⟩ := hGab
      have ha_eq : a = (r, (eᵣ r u).val) := hau
      have hb_eq : b = (r, (eᵣ r v).val) := hbv
      have huY : u ∈ Y r := by
        rw [hY_def, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← ha_eq]; exact haX
      have hvY : v ∈ Y r := by
        rw [hY_def, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hb_eq]; exact hbX
      have hr_in_R : r ∈ R := by
        change r ∈ X.image Prod.fst
        rw [Finset.mem_image]
        exact ⟨a, haX, by rw [ha_eq]⟩
      have huT : u ∉ T r := by
        intro huT
        apply haT
        rw [hTglob_def]
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨r, hr_in_R, ?_⟩
        rw [Finset.mem_image]
        exact ⟨u, huT, ha_eq.symm⟩
      have hvT : v ∉ T r := by
        intro hvT
        apply hbT
        rw [hTglob_def]
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨r, hr_in_R, ?_⟩
        rw [Finset.mem_image]
        exact ⟨v, hvT, hb_eq.symm⟩
      -- Compute the colors.
      change getColor a ≠ getColor b
      rw [ha_eq, hb_eq, hget_eq r u huY huT, hget_eq r v hvY hvT]
      exact (cᵣ r).valid (show ((Hᵣ r).induce ((↑(Y r) : Set (Vᵣ r)) \ ↑(T r))).Adj
        ⟨u, ⟨huY, huT⟩⟩ ⟨v, ⟨hvY, hvT⟩⟩ from huv)
    -- Apply oct_le_of_delete.
    exact oct_le_of_delete hTglob_sub hTglob_card_le hsurv_bip

/-! ### Helpers for `erdos_750_independence` -/

/-- A choice of threshold function: for each `k`, picks an `n` such that for every
`m ≥ n`, `(k : NNReal) ≤ f m`.  Existence is guaranteed by `Tendsto f atTop atTop`. -/
private noncomputable def thresholdSeq (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (k : ℕ) : ℕ :=
  (show ∃ n, ∀ m, n ≤ m → (k : NNReal) ≤ f m from
    (Filter.tendsto_atTop_atTop.mp hf) (k : NNReal)).choose

private lemma thresholdSeq_spec (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) (k : ℕ) :
    ∀ m, thresholdSeq f hf k ≤ m → (k : NNReal) ≤ f m :=
  (show ∃ n, ∀ m, n ≤ m → (k : NNReal) ≤ f m from
    (Filter.tendsto_atTop_atTop.mp hf) (k : NNReal)).choose_spec

/-- The minorant: the largest `k ≤ m` for which the threshold `thresholdSeq f hf k`
is already `≤ m`.  By construction, `(g f hf m : NNReal) ≤ f m`, hence
`(g f hf m : ℝ) ≤ 2 * (f m : ℝ)`. -/
private noncomputable def gMinorant (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => thresholdSeq f hf k ≤ m) m

private lemma gMinorant_le_self (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : gMinorant f hf m ≤ m := by
  classical
  unfold gMinorant
  exact Nat.findGreatest_le m

private lemma gMinorant_le_f (f : ℕ → NNReal) (hf : Tendsto f atTop atTop)
    (m : ℕ) : ((gMinorant f hf m : ℕ) : NNReal) ≤ f m := by
  classical
  set k := gMinorant f hf m with hk_def
  by_cases hk : k = 0
  · rw [hk]
    have : ((0 : ℕ) : NNReal) = 0 := by norm_cast
    rw [this]
    exact zero_le
  · have h : thresholdSeq f hf k ≤ m := by
      unfold gMinorant at hk_def
      have := Nat.findGreatest_of_ne_zero (P := fun k => thresholdSeq f hf k ≤ m)
        (n := m) hk_def.symm hk
      exact this
    exact thresholdSeq_spec f hf k m h

private lemma gMinorant_monotone (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) :
    Monotone (gMinorant f hf) := by
  classical
  intro m m' hmm'
  unfold gMinorant
  -- We need: gMinorant m ≤ gMinorant m'.
  set k := Nat.findGreatest (fun k => thresholdSeq f hf k ≤ m) m with hk_def
  by_cases hk : k = 0
  · rw [hk]; exact Nat.zero_le _
  · have hP : thresholdSeq f hf k ≤ m :=
      Nat.findGreatest_of_ne_zero (P := fun k => thresholdSeq f hf k ≤ m)
        (n := m) hk_def.symm hk
    have hkm : k ≤ m := by rw [hk_def]; exact Nat.findGreatest_le m
    have hkm' : k ≤ m' := hkm.trans hmm'
    have hP' : thresholdSeq f hf k ≤ m' := hP.trans hmm'
    exact Nat.le_findGreatest hkm' hP'

private lemma gMinorant_tendsto (f : ℕ → NNReal) (hf : Tendsto f atTop atTop) :
    Tendsto (gMinorant f hf) atTop atTop := by
  classical
  rw [Filter.tendsto_atTop_atTop]
  intro K
  refine ⟨max K (thresholdSeq f hf K), ?_⟩
  intro m hm
  have hKm : K ≤ m := (le_max_left _ _).trans hm
  have hTm : thresholdSeq f hf K ≤ m := (le_max_right _ _).trans hm
  unfold gMinorant
  exact Nat.le_findGreatest hKm hTm

/--
**Corollary 1.2 / The Erdős problem (#750).** For every `f : ℕ → ℝ≥0` with
`f(m) → ∞`, there exists a graph `G` of infinite chromatic number such that every
finite induced subgraph `F` on `m` vertices has an independent set of size at least
`m / 2 - f(m)`.

This is the right-hand side of `formal-conjectures`'
`FormalConjectures/ErdosProblems/750.lean`.
-/
theorem erdos_750_independence (stiebitz_lower_bound : StiebitzLowerBound) :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m / 2 : ℝ) - f m ≤ I.ncard := by
  classical
  intro f hf
  -- Build the integer minorant `g` of `f` and apply `infinite_chromatic_local_oct`.
  obtain ⟨V, _decV, G, hChrom, hOct⟩ :=
    infinite_chromatic_local_oct stiebitz_lower_bound (gMinorant f hf) (gMinorant_monotone f hf)
      (gMinorant_tendsto f hf)
  refine ⟨V, G, hChrom, ?_⟩
  intro m S hm hScard
  -- `S` is finite since `S.ncard = m` with `0 < m`.
  have hSfin : S.Finite := by
    by_contra hSinf
    rw [Set.not_finite] at hSinf
    rw [hSinf.ncard] at hScard
    omega
  -- Convert to Finset.
  set Sfin : Finset V := hSfin.toFinset with hSfin_def
  have hSfin_card : Sfin.card = m := by
    rw [hSfin_def, ← Set.ncard_eq_toFinset_card S hSfin]
    exact hScard
  have hSfin_coe : (↑Sfin : Set V) = S := by
    rw [hSfin_def]; exact hSfin.coe_toFinset
  -- Apply oct_witness on `G` and `Sfin`.
  obtain ⟨T, hTsub, hTcard, hTbip⟩ := oct_witness G Sfin
  -- The OCT bound from Theorem 1.1.
  have hSfin_ne : Sfin.Nonempty := by
    rw [← Finset.card_pos, hSfin_card]; exact hm
  have hOctBound : oct G Sfin ≤ gMinorant f hf m :=
    by have := hOct Sfin hSfin_ne; rw [hSfin_card] at this; exact this
  -- Pick a 2-coloring of the survivor and define the two color classes.
  obtain ⟨c⟩ := hTbip
  -- Survivor vertex set as Finset.
  set Surv : Finset V := Sfin \ T with hSurv_def
  -- Sanity: ↑Surv = (↑Sfin : Set V) \ ↑T
  have hSurv_coe : (↑Surv : Set V) = (↑Sfin : Set V) \ (↑T : Set V) := by
    rw [hSurv_def, Finset.coe_sdiff]
  -- The coloring `c` is on the subtype `(↑Sfin : Set V) \ (↑T : Set V)`. For `v ∈ Surv`,
  -- we need to compute `c ⟨v, _⟩ : Fin 2`.
  -- Define the two color-class Finsets inside `Surv`.
  let class0 : Finset V := Surv.filter (fun v =>
    if h : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) then c ⟨v, h⟩ = 0 else False)
  let class1 : Finset V := Surv.filter (fun v =>
    if h : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) then c ⟨v, h⟩ = 1 else False)
  -- Each vertex of Surv is in exactly one of class0, class1.
  have hclass_partition : class0 ∪ class1 = Surv := by
    apply Finset.ext
    intro v
    simp only [Finset.mem_union, Finset.mem_filter, class0, class1]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      have hvSurv : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
        rw [← hSurv_coe]; exact hv
      -- c ⟨v, hvSurv⟩ : Fin 2 takes value 0 or 1.
      have h2 : c ⟨v, hvSurv⟩ = 0 ∨ c ⟨v, hvSurv⟩ = 1 := by
        have hlt : (c ⟨v, hvSurv⟩).val < 2 := (c ⟨v, hvSurv⟩).isLt
        have : (c ⟨v, hvSurv⟩).val = 0 ∨ (c ⟨v, hvSurv⟩).val = 1 := by
          have := hlt
          omega
        rcases this with hv | hv
        · left
          apply Fin.ext
          show (c ⟨v, hvSurv⟩).val = (0 : Fin 2).val
          rw [hv]; rfl
        · right
          apply Fin.ext
          show (c ⟨v, hvSurv⟩).val = (1 : Fin 2).val
          rw [hv]; rfl
      rcases h2 with h2 | h2
      · left
        refine ⟨hv, ?_⟩
        rw [dif_pos hvSurv]; exact h2
      · right
        refine ⟨hv, ?_⟩
        rw [dif_pos hvSurv]; exact h2
  have hclass_disj : Disjoint class0 class1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    simp only [Finset.mem_filter, class0, class1] at hv0 hv1
    obtain ⟨hv, hc0⟩ := hv0
    obtain ⟨_, hc1⟩ := hv1
    have hvSurv : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hv
    rw [dif_pos hvSurv] at hc0 hc1
    have : (0 : Fin 2) = 1 := hc0.symm.trans hc1
    exact absurd this (by decide)
  -- |class0| + |class1| = |Surv|.
  have hclass_card : class0.card + class1.card = Surv.card := by
    rw [← Finset.card_union_of_disjoint hclass_disj, hclass_partition]
  -- One of class0, class1 has size ≥ Surv.card / 2 (and ≥ ⌈Surv.card/2⌉ ≥ Surv.card - Surv.card/2).
  -- Specifically, max(class0.card, class1.card) ≥ Surv.card / 2 (real divide).
  -- Using ℕ-arithmetic: 2 * max(a,b) ≥ a + b, so max ≥ (a+b)/2 (in ℕ, max ≥ (a+b)/2 — and a+b -
  -- max ≥ ... )
  -- Pick the larger one.
  let I_finset : Finset V := if class0.card ≥ class1.card then class0 else class1
  have hI_subset_surv : I_finset ⊆ Surv := by
    by_cases hge : class0.card ≥ class1.card
    · simp only [I_finset, hge, if_true]
      intro v hv
      simp only [Finset.mem_filter, class0] at hv
      exact hv.1
    · simp only [I_finset, hge, if_false]
      intro v hv
      simp only [Finset.mem_filter, class1] at hv
      exact hv.1
  -- I.ncard ≥ Surv.card / 2  (where Surv.card = m - oct G Sfin).
  have hSurv_card : Surv.card = Sfin.card - T.card := by
    rw [hSurv_def, Finset.card_sdiff_of_subset hTsub]
  have hI_card_lb : 2 * I_finset.card ≥ Surv.card := by
    by_cases hge : class0.card ≥ class1.card
    · simp only [I_finset, hge, if_true]
      have : 2 * class0.card ≥ class0.card + class1.card := by
        have h1 : class1.card ≤ class0.card := hge
        omega
      rw [hclass_card] at this
      exact this
    · simp only [I_finset, hge, if_false]
      push Not at hge
      have : 2 * class1.card ≥ class0.card + class1.card := by
        have h1 : class0.card ≤ class1.card := le_of_lt hge
        omega
      rw [hclass_card] at this
      exact this
  -- Define the resulting independent set.
  let I : Set V := (↑I_finset : Set V)
  refine ⟨I, ?_, ?_, ?_⟩
  · -- I ⊆ S
    have hI_sub_Sfin : I_finset ⊆ Sfin := hI_subset_surv.trans Finset.sdiff_subset
    intro v hv
    rw [← hSfin_coe]
    exact hI_sub_Sfin hv
  · -- G.IsIndepSet I
    intro v hv w hw hvw
    simp only [I, Finset.mem_coe] at hv hw
    have hvSurv : v ∈ Surv := hI_subset_surv hv
    have hwSurv : w ∈ Surv := hI_subset_surv hw
    have hvSurvSet : v ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hvSurv
    have hwSurvSet : w ∈ ((↑Sfin : Set V) \ (↑T : Set V)) := by
      rw [← hSurv_coe]; exact hwSurv
    intro hadj
    -- Same color → not adjacent in G.induce.
    have hadj_induce : (G.induce ((↑Sfin : Set V) \ (↑T : Set V))).Adj
        ⟨v, hvSurvSet⟩ ⟨w, hwSurvSet⟩ := hadj
    -- Both have the same color (call it `i`).
    have hsame_color : c ⟨v, hvSurvSet⟩ = c ⟨w, hwSurvSet⟩ := by
      by_cases hge : class0.card ≥ class1.card
      · -- I = class0, both colored 0
        have hv' : v ∈ class0 := by simp only [I_finset, hge, if_true] at hv; exact hv
        have hw' : w ∈ class0 := by simp only [I_finset, hge, if_true] at hw; exact hw
        simp only [Finset.mem_filter, class0] at hv' hw'
        have hvc : c ⟨v, hvSurvSet⟩ = 0 := by
          have := hv'.2; rw [dif_pos hvSurvSet] at this; exact this
        have hwc : c ⟨w, hwSurvSet⟩ = 0 := by
          have := hw'.2; rw [dif_pos hwSurvSet] at this; exact this
        rw [hvc, hwc]
      · -- I = class1, both colored 1
        have hv' : v ∈ class1 := by simp only [I_finset, hge, if_false] at hv; exact hv
        have hw' : w ∈ class1 := by simp only [I_finset, hge, if_false] at hw; exact hw
        simp only [Finset.mem_filter, class1] at hv' hw'
        have hvc : c ⟨v, hvSurvSet⟩ = 1 := by
          have := hv'.2; rw [dif_pos hvSurvSet] at this; exact this
        have hwc : c ⟨w, hwSurvSet⟩ = 1 := by
          have := hw'.2; rw [dif_pos hwSurvSet] at this; exact this
        rw [hvc, hwc]
    exact c.valid hadj_induce hsame_color
  · -- (m / 2 : ℝ) - f m ≤ I.ncard
    have hI_ncard : (I.ncard : ℝ) = (I_finset.card : ℝ) := by
      simp [I, Set.ncard_coe_finset]
    rw [hI_ncard]
    -- I.card ≥ Surv.card / 2 = (m - oct) / 2 ≥ (m - g m) / 2 ≥ (m - 2 f m) / 2 = m/2 - f m.
    have h_surv : (Surv.card : ℝ) ≤ 2 * (I_finset.card : ℝ) := by
      have h := hI_card_lb
      exact_mod_cast h
    have h_card_eq : Surv.card = m - T.card := by
      rw [hSurv_card, hSfin_card]
    have h_T_le : T.card ≤ gMinorant f hf m := by
      rw [hTcard]; exact hOctBound
    have h_T_le' : T.card ≤ m := h_T_le.trans (gMinorant_le_self f hf m)
    have h_surv_real : (Surv.card : ℝ) = (m : ℝ) - (T.card : ℝ) := by
      rw [h_card_eq]
      push_cast [Nat.cast_sub h_T_le']
      ring
    -- The real bound `gMinorant f hf m ≤ f m`
    have h_gM_le_f : ((gMinorant f hf m : ℕ) : ℝ) ≤ (f m : ℝ) := by
      have h := gMinorant_le_f f hf m
      exact_mod_cast (NNReal.coe_le_coe.mpr h)
    have h_T_real_le : (T.card : ℝ) ≤ (f m : ℝ) := by
      have : (T.card : ℝ) ≤ ((gMinorant f hf m : ℕ) : ℝ) := by exact_mod_cast h_T_le
      exact this.trans h_gM_le_f
    -- Now: 2 * I.card ≥ Surv.card = m - T.card ≥ m - f m, so I.card ≥ (m - f m)/2 = m/2 - f m / 2
    -- ≥ m/2 - f m.
    -- We want (m/2 : ℝ) - f m ≤ I.card.
    -- From 2 I.card ≥ Surv.card = m - T.card ≥ m - f m,
    -- so I.card ≥ (m - f m)/2 = m/2 - f m/2 ≥ m/2 - f m.
    have h_chain : (m : ℝ) - (f m : ℝ) ≤ 2 * (I_finset.card : ℝ) := by
      calc (m : ℝ) - (f m : ℝ)
          ≤ (m : ℝ) - (T.card : ℝ) := by linarith
        _ = (Surv.card : ℝ) := h_surv_real.symm
        _ ≤ 2 * (I_finset.card : ℝ) := h_surv
    -- Now derive m/2 - f m ≤ I_finset.card.
    have h_NN : (0 : ℝ) ≤ (f m : ℝ) := (f m).coe_nonneg
    linarith

/--
**Upstream-shape wrapper** matching `formal-conjectures`'s
[`FormalConjectures/ErdosProblems/750.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/750.lean)
exact syntax: `m / 2 - f m ≤ I.ncard`. With Lean's default elaboration, `f m : ℝ≥0`
forces the subtraction into NNReal, which makes `m / 2` *real division* in NNReal
(`(↑m : ℝ≥0) / 2`), and the subtraction is NNReal-truncated. Implied by the
real-valued form `erdos_750_independence` proved above. -/
theorem erdos_750_independence_FC_form (stiebitz_lower_bound : StiebitzLowerBound) :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : NNReal) / 2 - f m ≤ (I.ncard : NNReal) := by
  intro f hf
  obtain ⟨V, G, hChrom, hWit⟩ := erdos_750_independence stiebitz_lower_bound f hf
  refine ⟨V, G, hChrom, ?_⟩
  intro m S hm hScard
  obtain ⟨I, hI_sub, hI_indep, hI_real⟩ := hWit m S hm hScard
  refine ⟨I, hI_sub, hI_indep, ?_⟩
  -- `hI_real : (m / 2 : ℝ) - f m ≤ I.ncard`. Translate to NNReal-truncated form.
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_sub_def]
  -- Goal: max (((m : NNReal) / 2 : ℝ) - ((f m : NNReal) : ℝ)) 0 ≤ ((I.ncard : NNReal) : ℝ)
  push_cast
  refine max_le ?_ ?_
  · -- (m : ℝ) / 2 - (f m : ℝ) ≤ (I.ncard : ℝ)
    linarith
  · -- 0 ≤ (I.ncard : ℝ)
    exact_mod_cast Nat.zero_le _

end Conditional

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/SourceFlags.lean` -/

section
/-!
A small, self-contained chain model for order-complex flags.

The empty list is the augmented (-1)-simplex.  A nonempty list has the
usual alternating deletion boundary.  We deliberately work first in the
free module on all lists: strict flags form a boundary-stable submodule,
while the algebraic cone/prism identities are simplest in the ambient
module.
-/

namespace SourceFlags

open scoped BigOperators

noncomputable section

variable {α β γ : Type*}

abbrev Chain (α : Type*) := List α →₀ ℤ

def basis (l : List α) : Chain α := Finsupp.single l 1

def linearOfBasis (f : List α → Chain β) : Chain α →ₗ[ℤ] Chain β :=
  (Finsupp.lift (Chain β) ℤ (List α)) f

@[simp] theorem linearOfBasis_basis (f : List α → Chain β) (l : List α) :
    linearOfBasis f (basis l) = f l := by
  simp [linearOfBasis, basis]

def mapLists (f : List α → List β) : Chain α →ₗ[ℤ] Chain β :=
  linearOfBasis fun l => basis (f l)

@[simp] theorem mapLists_basis (f : List α → List β) (l : List α) :
    mapLists f (basis l) = basis (f l) := by
  simp [mapLists]

def mapVertices (f : α → β) : Chain α →ₗ[ℤ] Chain β :=
  mapLists (List.map f)

@[simp] theorem mapVertices_basis (f : α → β) (l : List α) :
    mapVertices f (basis l) = basis (l.map f) := by
  simp [mapVertices]

@[simp] theorem mapVertices_id_apply (c : Chain α) :
    mapVertices id c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp

def prepend (x : α) : Chain α →ₗ[ℤ] Chain α :=
  mapLists (List.cons x)

@[simp] theorem prepend_basis (x : α) (l : List α) :
    prepend x (basis l) = basis (x :: l) := by
  simp [prepend]

/- The recursive formula is exactly
   d[x0,...,xq] = [x1,...,xq] - x0 * d[x1,...,xq]. -/
def boundaryBasis : List α → Chain α
  | [] => 0
  | x :: xs => basis xs - prepend x (boundaryBasis xs)

def boundary : Chain α →ₗ[ℤ] Chain α :=
  linearOfBasis boundaryBasis

@[simp] theorem boundary_basis (l : List α) :
    boundary (basis l) = boundaryBasis l := by
  simp [boundary]

@[simp] theorem boundaryBasis_nil : boundaryBasis ([] : List α) = 0 := rfl

@[simp] theorem boundaryBasis_cons (x : α) (xs : List α) :
    boundaryBasis (x :: xs) = basis xs - prepend x (boundaryBasis xs) := rfl

theorem boundary_prepend (x : α) (c : Chain α) :
    boundary (prepend x c) = c - prepend x (boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      rw [hc, hd]
      module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [boundaryBasis_cons, smul_sub]

theorem mapVertices_prepend (f : α → β) (x : α) (c : Chain α) :
    mapVertices f (prepend x c) = prepend (f x) (mapVertices f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp

theorem boundary_mapVertices_basis (f : α → β) (l : List α) :
    boundary (mapVertices f (basis l)) = mapVertices f (boundary (basis l)) := by
  induction l with
  | nil => simp [boundaryBasis]
  | cons x xs ih =>
      simp only [mapVertices_basis, List.map_cons, boundary_basis, boundaryBasis_cons,
        map_sub, mapVertices_basis, mapVertices_prepend]
      rw [show boundaryBasis (List.map f xs) = boundary (basis (List.map f xs)) by simp]
      rw [show mapVertices f (boundaryBasis xs) =
          mapVertices f (boundary (basis xs)) by simp]
      have ih' : boundary (basis (List.map f xs)) =
          mapVertices f (boundary (basis xs)) := by simpa using ih
      rw [ih']

theorem boundary_mapVertices (f : α → β) (c : Chain α) :
    boundary (mapVertices f c) = mapVertices f (boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp only [map_smul]
      rw [boundary_mapVertices_basis]

theorem boundary_boundary_basis (l : List α) : boundary (boundary (basis l)) = 0 := by
  induction l with
  | nil => simp [boundaryBasis]
  | cons x xs ih =>
      simp only [boundary_basis, boundaryBasis_cons, map_sub, boundary_prepend]
      rw [show boundaryBasis xs = boundary (basis xs) by simp]
      rw [ih]
      simp

theorem boundary_boundary (c : Chain α) : boundary (boundary c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp only [map_smul]
    rw [boundary_boundary_basis]
    simp

/- Cone on the image of a vertex map. -/
def cone (v : β) (J : α → β) : Chain α →ₗ[ℤ] Chain β :=
  (prepend v).comp (mapVertices J)

theorem boundary_cone (v : β) (J : α → β) (c : Chain α) :
    boundary (cone v J c) + cone v J (boundary c) = mapVertices J c := by
  simp [cone, boundary_prepend, boundary_mapVertices]

/- The usual prism for the pointwise-comparable maps f and g.  The order
assumptions are needed only to know that its terms are flags; the chain
identity itself is purely algebraic. -/
def prismBasis (f g : α → β) : List α → Chain β
  | [] => 0
  | x :: xs =>
      basis (f x :: g x :: xs.map g) - prepend (f x) (prismBasis f g xs)

def prism (f g : α → β) : Chain α →ₗ[ℤ] Chain β :=
  linearOfBasis (prismBasis f g)

@[simp] theorem prism_basis (f g : α → β) (l : List α) :
    prism f g (basis l) = prismBasis f g l := by
  simp [prism]

@[simp] theorem prismBasis_nil (f g : α → β) :
    prismBasis f g [] = 0 := rfl

@[simp] theorem prismBasis_cons (f g : α → β) (x : α) (xs : List α) :
    prismBasis f g (x :: xs) =
      basis (f x :: g x :: xs.map g) - prepend (f x) (prismBasis f g xs) := rfl

theorem prism_prepend (f g : α → β) (x : α) (c : Chain α) :
    prism f g (prepend x c) =
      prepend (f x) (prepend (g x) (mapVertices g c)) -
        prepend (f x) (prism f g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      rw [hc, hd]
      module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [prism, prismBasis_cons, sub_eq_add_neg]

theorem boundary_prism_add_prism_boundary_basis
    (f g : α → β) (l : List α) :
    boundary (prism f g (basis l)) + prism f g (boundary (basis l)) =
      mapVertices g (basis l) - mapVertices f (basis l) := by
  induction l with
  | nil => simp [prismBasis, boundaryBasis]
  | cons x xs ih =>
      simp only [prism_basis, prismBasis_cons, map_sub, boundary_prepend,
        boundary_basis, boundaryBasis_cons, prism_prepend, mapVertices_basis,
        List.map_cons]
      have hmap := boundary_mapVertices_basis g xs
      simp only [mapVertices_basis, boundary_basis] at hmap
      have ih' := ih
      simp only [prism_basis, boundary_basis, mapVertices_basis] at ih'
      rw [hmap]
      have ih'' := congrArg (prepend (f x)) ih'
      simp only [map_add, map_sub] at ih''
      rw [show basis (f x :: List.map f xs) =
        prepend (f x) (basis (List.map f xs)) by simp]
      calc
        basis (g x :: List.map g xs) -
              (prepend (f x) (basis (List.map g xs)) -
                prepend (f x) (prepend (g x) (mapVertices g (boundaryBasis xs)))) -
              (prismBasis f g xs - prepend (f x) (boundary (prismBasis f g xs))) +
              (prismBasis f g xs -
                (prepend (f x) (prepend (g x) (mapVertices g (boundaryBasis xs))) -
                  prepend (f x) (prism f g (boundaryBasis xs)))) =
            basis (g x :: List.map g xs) - prepend (f x) (basis (List.map g xs)) +
              (prepend (f x) (boundary (prismBasis f g xs)) +
                prepend (f x) (prism f g (boundaryBasis xs))) := by module
        _ = basis (g x :: List.map g xs) - prepend (f x) (basis (List.map g xs)) +
              (prepend (f x) (basis (List.map g xs)) -
                prepend (f x) (basis (List.map f xs))) := by rw [ih'']
        _ = basis (g x :: List.map g xs) - prepend (f x) (basis (List.map f xs)) := by
          module

theorem boundary_prism_add_prism_boundary (f g : α → β) (c : Chain α) :
    boundary (prism f g c) + prism f g (boundary c) =
      mapVertices g c - mapVertices f c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      calc
        boundary (prism f g c) + boundary (prism f g d) +
              (prism f g (boundary c) + prism f g (boundary d)) =
            (boundary (prism f g c) + prism f g (boundary c)) +
              (boundary (prism f g d) + prism f g (boundary d)) := by module
        _ = (mapVertices g c - mapVertices f c) +
              (mapVertices g d - mapVertices f d) := by rw [hc, hd]
        _ = mapVertices g c + mapVertices g d -
              (mapVertices f c + mapVertices f d) := by module
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp only [map_smul]
    have h := boundary_prism_add_prism_boundary_basis f g l
    calc
      z • boundary (prism f g (basis l)) +
          z • prism f g (boundary (basis l)) =
        z • (boundary (prism f g (basis l)) +
          prism f g (boundary (basis l))) := by module
      _ = z • (mapVertices g (basis l) - mapVertices f (basis l)) := by rw [h]
      _ = z • mapVertices g (basis l) - z • mapVertices f (basis l) := by module

/- Fresh-join contraction: J is the operation A |-> A union {fresh}; v is
the fresh singleton. -/
def freshFill (v : α) (J : α → α) : Chain α →ₗ[ℤ] Chain α :=
  cone v J - prism id J

/- Strict order-complex flags. -/

/- The group action on chains is just pointwise action on flag vertices. -/
section Action

variable (G : Type*) [Group G] [MulAction G α]

def act (g : G) : Chain α →ₗ[ℤ] Chain α :=
  mapVertices (g • ·)

@[simp] theorem act_basis (g : G) (l : List α) :
    act G g (basis l) = basis (l.map (g • ·)) := by
  simp [act]

end Action

/- Abstract recursion underlying the generalized-sphere chains.  It is
stated for arbitrary alternating operators; the concrete operators are
tau and norm on cyclic group chains. -/
section Recursion

variable (A B F : Chain α →ₗ[ℤ] Chain α)

end Recursion

end

end SourceFlags

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/ZpTuckerDefs.lean` -/

section
open scoped BigOperators

namespace ZpTuckerScratch

abbrev SignedVector (p n : ℕ) := Fin n → Option (ZMod p)

def SignedVector.Nonzero {p n : ℕ} (x : SignedVector p n) : Prop :=
  ∃ i, x i ≠ none

def SignedVector.LE {p n : ℕ} (x y : SignedVector p n) : Prop :=
  ∀ i g, x i = some g → y i = some g

instance {p n : ℕ} : LE (SignedVector p n) := ⟨SignedVector.LE⟩

@[simp] theorem SignedVector.le_def {p n : ℕ} {x y : SignedVector p n} :
    x ≤ y ↔ ∀ i g, x i = some g → y i = some g := Iff.rfl

theorem SignedVector.le_refl {p n : ℕ} (x : SignedVector p n) : x ≤ x := by
  intro i g h
  exact h

theorem SignedVector.le_trans {p n : ℕ} {x y z : SignedVector p n}
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro i g h
  exact hyz i g (hxy i g h)

theorem SignedVector.le_antisymm {p n : ℕ} {x y : SignedVector p n}
    (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  funext i
  cases hxi : x i with
  | none =>
      cases hyi : y i with
      | none => rfl
      | some g =>
          have h := hyx i g hyi
          rw [hxi] at h
          contradiction
  | some g =>
      cases hyi : y i with
      | none =>
          have h := hxy i g hxi
          rw [hyi] at h
          contradiction
      | some g' =>
          have h := hxy i g hxi
          rw [hyi] at h
          cases h
          rfl

instance {p n : ℕ} : PartialOrder (SignedVector p n) where
  le_refl := SignedVector.le_refl
  le_trans _ _ _ := SignedVector.le_trans
  le_antisymm _ _ := SignedVector.le_antisymm

def SignedVector.shift {p n : ℕ} (a : ZMod p) (x : SignedVector p n) :
    SignedVector p n := fun i => (x i).map (a + ·)

@[simp] theorem SignedVector.shift_apply {p n : ℕ} (a : ZMod p)
    (x : SignedVector p n) (i : Fin n) :
    x.shift a i = (x i).map (a + ·) := rfl

@[simp] theorem SignedVector.shift_zero {p n : ℕ} (x : SignedVector p n) :
    x.shift 0 = x := by
  funext i
  cases h : x i <;> simp [SignedVector.shift, h]

@[simp] theorem SignedVector.shift_add {p n : ℕ} (a b : ZMod p)
    (x : SignedVector p n) :
    (x.shift b).shift a = x.shift (a + b) := by
  funext i
  cases x i <;> simp [SignedVector.shift, add_assoc]

theorem SignedVector.Nonzero.shift {p n : ℕ} {x : SignedVector p n}
    (hx : x.Nonzero) (a : ZMod p) : (x.shift a).Nonzero := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  rcases h : x i with _ | g
  · exact (hi h).elim
  · simp [SignedVector.shift, h]

abbrev NonzeroSignedVector (p n : ℕ) :=
  {x : SignedVector p n // x.Nonzero}

def NonzeroSignedVector.shift {p n : ℕ} (a : ZMod p)
    (x : NonzeroSignedVector p n) : NonzeroSignedVector p n :=
  ⟨x.1.shift a, x.2.shift a⟩

instance {p n : ℕ} : LE (NonzeroSignedVector p n) :=
  ⟨fun x y => x.1 ≤ y.1⟩

instance {p n : ℕ} : PartialOrder (NonzeroSignedVector p n) :=
  PartialOrder.lift Subtype.val Subtype.val_injective

@[simp] theorem NonzeroSignedVector.coe_shift {p n : ℕ} (a : ZMod p)
    (x : NonzeroSignedVector p n) :
    (x.shift a : SignedVector p n) = x.1.shift a := rfl

end ZpTuckerScratch

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/SignedSphere.lean` -/

section
/-!
A concrete finite-chain model of the free `ZMod p`-sphere carried by the
order complex of nonzero signed vectors.  The chains constructed below are
the standard chains for the periodic cyclic resolution: their boundaries
alternate between `tau = sigma - 1` and the group norm.
-/

namespace SignedSphere

open scoped BigOperators
open SourceFlags ZpTuckerScratch

noncomputable section

variable {α β : Type*}

/-- A chain is supported on `P` when every basis list with nonzero
coefficient satisfies `P`. -/
def Supported (P : List α → Prop) (c : Chain α) : Prop :=
  ∀ l, c l ≠ 0 → P l

theorem Supported.mono {P Q : List α → Prop} {c : Chain α}
    (hc : Supported P c) (hPQ : ∀ l, P l → Q l) : Supported Q c := by
  intro l hl
  exact hPQ l (hc l hl)

theorem supported_zero (P : List α → Prop) : Supported P (0 : Chain α) := by
  intro l hl
  simp at hl

theorem supported_basis {P : List α → Prop} {l : List α} (hl : P l) :
    Supported P (basis l) := by
  intro k hk
  by_cases hkl : k = l
  · simpa [hkl] using hl
  · simp [basis, Finsupp.single_apply, hkl] at hk

theorem supported_add {P : List α → Prop} {c d : Chain α}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c + d) := by
  intro l hl
  by_cases hcl : c l = 0
  · apply hd l
    intro hdl
    apply hl
    simp [hcl, hdl]
  · exact hc l hcl

theorem supported_neg {P : List α → Prop} {c : Chain α}
    (hc : Supported P c) : Supported P (-c) := by
  intro l hl
  apply hc l
  intro h
  apply hl
  simp [h]

theorem supported_sub {P : List α → Prop} {c d : Chain α}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c - d) := by
  exact supported_add hc (supported_neg hd)

theorem supported_sum {ι : Type*} {P : List α → Prop} {s : Finset ι}
    {c : ι → Chain α} (hc : ∀ i ∈ s, Supported P (c i)) :
    Supported P (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supported_zero P
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact supported_add (hc a (by simp)) (ih (fun i hi => hc i (by simp [hi])))

/-- Support propagation through a linear map specified on the list basis. -/
theorem supported_linearOfBasis {P : List α → Prop} {Q : List β → Prop}
    (f : List α → Chain β)
    (hf : ∀ l, P l → Supported Q (f l)) {c : Chain α}
    (hc : Supported P c) : Supported Q (linearOfBasis f c) := by
  classical
  intro k hk
  have hkmem : k ∈ (linearOfBasis f c).support := Finsupp.mem_support_iff.mpr hk
  rw [linearOfBasis, Finsupp.lift_apply] at hkmem
  have hsub := Finsupp.support_sum (f := c)
      (g := fun l z => z • f l)
  have hkU := hsub hkmem
  simp only [Finset.mem_biUnion] at hkU
  obtain ⟨l, hlc, hkl⟩ := hkU
  have hlP : P l := hc l (Finsupp.mem_support_iff.mp hlc)
  apply hf l hlP k
  have hz : c l • f l k ≠ 0 := Finsupp.mem_support_iff.mp hkl
  intro hzero
  apply hz
  simp [hzero]

theorem supported_mapVertices {P : List α → Prop} {Q : List β → Prop}
    (f : α → β) (hf : ∀ l, P l → Q (l.map f)) {c : Chain α}
    (hc : Supported P c) : Supported Q (mapVertices f c) := by
  simpa [mapVertices, mapLists] using
    (supported_linearOfBasis (fun l => basis (l.map f))
      (fun l hl => supported_basis (hf l hl)) hc)

theorem supported_prepend {P Q : List α → Prop} (x : α)
    (hx : ∀ l, P l → Q (x :: l)) {c : Chain α} (hc : Supported P c) :
    Supported Q (prepend x c) := by
  simpa [prepend, mapLists] using
    (supported_linearOfBasis (fun l => basis (x :: l))
      (fun l hl => supported_basis (hx l hl)) hc)

/-! ## Signed vertices and a fresh-coordinate join -/

abbrev Vertex (p n : ℕ) := NonzeroSignedVector p n
abbrev SChain (p n : ℕ) := Chain (Vertex p n)

def rawUnit {p n : ℕ} (q : Fin n) (a : ZMod p) : SignedVector p n :=
  fun j => if j = q then some a else none

@[simp] theorem rawUnit_same {p n : ℕ} (q : Fin n) (a : ZMod p) :
    rawUnit q a q = some a := by simp [rawUnit]

@[simp] theorem rawUnit_ne {p n : ℕ} {q j : Fin n} (h : j ≠ q) (a : ZMod p) :
    rawUnit q a j = none := by simp [rawUnit, h]

def unit {p n : ℕ} (q : Fin n) (a : ZMod p) : Vertex p n :=
  ⟨rawUnit q a, ⟨q, by simp⟩⟩

def rawAdjoin {p n : ℕ} (q : Fin n) (a : ZMod p)
    (x : SignedVector p n) : SignedVector p n :=
  fun j => if j = q then some a else x j

@[simp] theorem rawAdjoin_same {p n : ℕ} (q : Fin n) (a : ZMod p)
    (x : SignedVector p n) : rawAdjoin q a x q = some a := by
  simp [rawAdjoin]

@[simp] theorem rawAdjoin_ne {p n : ℕ} {q j : Fin n} (h : j ≠ q)
    (a : ZMod p) (x : SignedVector p n) : rawAdjoin q a x j = x j := by
  simp [rawAdjoin, h]

def adjoin {p n : ℕ} (q : Fin n) (a : ZMod p) (x : Vertex p n) : Vertex p n :=
  ⟨rawAdjoin q a x.1, ⟨q, by simp⟩⟩

theorem supported_linearMap {P : List α → Prop} {Q : List β → Prop}
    (L : Chain α →ₗ[ℤ] Chain β)
    (hL : ∀ l, P l → Supported Q (L (basis l))) {c : Chain α}
    (hc : Supported P c) : Supported Q (L c) := by
  have heq_all : ∀ d : Chain α, linearOfBasis (fun l => L (basis l)) d = L d := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single l z =>
        rw [show Finsupp.single l z = z • basis l by simp [basis]]
        simp
  rw [← heq_all c]
  exact supported_linearOfBasis (fun l => L (basis l)) hL hc

/-! ## The cyclic operators -/

@[simp] theorem vertex_shift_zero {p n : ℕ} (x : Vertex p n) : x.shift 0 = x := by
  apply Subtype.ext
  exact SignedVector.shift_zero x.1

@[simp] theorem vertex_shift_add {p n : ℕ} (a b : ZMod p) (x : Vertex p n) :
    (x.shift b).shift a = x.shift (a + b) := by
  apply Subtype.ext
  exact SignedVector.shift_add a b x.1

def shiftChain {p n : ℕ} (a : ZMod p) : SChain p n →ₗ[ℤ] SChain p n :=
  mapVertices (NonzeroSignedVector.shift a)

@[simp] theorem shiftChain_zero {p n : ℕ} (c : SChain p n) : shiftChain 0 c = c := by
  have hshift : (NonzeroSignedVector.shift (0 : ZMod p) : Vertex p n → Vertex p n) = id := by
    funext x
    exact vertex_shift_zero x
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp [shiftChain, hshift]

def tau {p n : ℕ} : SChain p n →ₗ[ℤ] SChain p n :=
  shiftChain 1 - LinearMap.id

def norm {p n : ℕ} [NeZero p] : SChain p n →ₗ[ℤ] SChain p n :=
  ∑ a : ZMod p, shiftChain a

theorem boundary_shiftChain {p n : ℕ} (a : ZMod p) (c : SChain p n) :
    boundary (shiftChain a c) = shiftChain a (boundary c) :=
  boundary_mapVertices _ _

theorem boundary_tau {p n : ℕ} (c : SChain p n) :
    boundary (tau c) = tau (boundary c) := by
  simp [tau, boundary_shiftChain]

theorem boundary_norm {p n : ℕ} [NeZero p] (c : SChain p n) :
    boundary (norm c) = norm (boundary c) := by
  simp [norm, boundary_shiftChain]

/-! ## Recursive sphere chains -/

/-- The differential used at positive degree in the periodic cyclic
resolution: `tau` in odd degree and the norm in even degree. -/
def periodicOp {p n : ℕ} [NeZero p] (i : ℕ) : SChain p n →ₗ[ℤ] SChain p n :=
  if i % 2 = 1 then tau else norm

@[simp] theorem shiftChain_empty {p n : ℕ} (a : ZMod p) :
    shiftChain a (basis ([] : List (Vertex p n))) = basis [] := by
  simp [shiftChain]

@[simp] theorem tau_empty {p n : ℕ} :
    tau (basis ([] : List (Vertex p n))) = 0 := by
  simp [tau]

/-- The chain `y i`, defined for all naturals but equal to zero beyond the
ambient dimension.  At a valid successor degree it fills the alternating
cyclic boundary using coordinate `i+1`. -/
def y (p n : ℕ) [NeZero p] : ℕ → SChain p n
  | 0 => if h : 0 < n then basis [unit ⟨0, h⟩ 0] else 0
  | i + 1 => if h : i + 1 < n then
      freshFill (unit ⟨i + 1, h⟩ 0) (adjoin ⟨i + 1, h⟩ 0)
        (periodicOp (i + 1) (y p n i))
    else 0

end

end SignedSphere

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/SignedSphereLength.lean` -/

section
namespace SignedSphere

open SourceFlags ZpTuckerScratch

noncomputable section

variable {α β : Type*}

def BoundaryTerm (l q : List α) : Prop :=
  q.Sublist l ∧ q.length + 1 = l.length

theorem boundaryBasis_supported_terms (l : List α) :
    Supported (BoundaryTerm l) (boundaryBasis l) := by
  induction l with
  | nil => exact supported_zero _
  | cons x xs ih =>
      apply supported_sub
      · exact supported_basis
          ⟨List.Sublist.cons _ (List.Sublist.refl xs), by simp⟩
      · apply supported_linearOfBasis
          (P := BoundaryTerm xs) (Q := BoundaryTerm (x :: xs))
          (fun q => basis (x :: q))
        · intro q hq
          exact supported_basis
            ⟨hq.1.cons_cons x, by simp [hq.2]⟩
        · exact ih

theorem prismBasis_supported_length (f : α → β) (g : α → β) (l : List α) :
    Supported (fun q : List β => q.length = l.length + 1)
      (prism f g (basis l)) := by
  induction l with
  | nil => simp [prismBasis, supported_zero]
  | cons x xs ih =>
      rw [prism_basis, prismBasis_cons]
      apply supported_sub
      · exact supported_basis (by simp)
      · rw [show prismBasis f g xs = prism f g (basis xs) by simp]
        apply supported_prepend
            (P := fun q : List β => q.length = xs.length + 1)
            (Q := fun q : List β => q.length = (x :: xs).length + 1) (f x)
        · intro q hq
          simp [hq]
        · exact ih

theorem supported_and {P Q : List α → Prop} {c : Chain α}
    (hP : Supported P c) (hQ : Supported Q c) :
    Supported (fun l => P l ∧ Q l) c := by
  intro l hl
  exact ⟨hP l hl, hQ l hl⟩

end

end SignedSphere

end

/-! ### Upstream module `ErdosProblems/Erdos750/Chains.lean` -/

section
/-!
# Chains in the signed biclique complex

A face is a list of signed vertices whose opposite shores span a complete
bipartite graph. Repeated vertices are allowed in this intermediate chain
model; the coloring obstruction will normalize them in an exterior algebra.
-/

namespace Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section

universe u v
variable {V : Type u} {W : Type v}

abbrev Signed (V : Type u) := ZMod 2 × V

def flip (x : Signed V) : Signed V := (x.1 + 1, x.2)

@[simp] lemma flip_flip (x : Signed V) : flip (flip x) = x := by
  ext
  · change x.1 + 1 + 1 = x.1
    have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [add_assoc, this, add_zero]
  · rfl

def Face (G : SimpleGraph V) (l : List (Signed V)) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.1 ≠ b.1 → G.Adj a.2 b.2

def Good (G : SimpleGraph V) (k : ℕ) (l : List (Signed V)) : Prop :=
  Face G l ∧ l.length = k

lemma Face.map_flip {G : SimpleGraph V} {l : List (Signed V)}
    (hl : Face G l) : Face G (l.map flip) := by
  rintro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact hl x hx y hy (by simpa [flip] using hab)

lemma mapVertices_comp (f : V → W) {U : Type*} (g : W → U) (c : Chain V) :
    mapVertices g (mapVertices f c) = mapVertices (g ∘ f) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
    rw [show Finsupp.single l z = z • basis l by simp [basis]]
    simp [List.map_map]

def swap : Chain (Signed V) →ₗ[ℤ] Chain (Signed V) := mapVertices flip

@[simp] lemma swap_swap (c : Chain (Signed V)) : swap (swap c) = c := by
  change mapVertices flip (mapVertices flip c) = c
  rw [mapVertices_comp]
  have hf : flip ∘ flip = (id : Signed V → Signed V) := funext flip_flip
  rw [hf]
  exact mapVertices_id_apply c

def op (i : ℕ) : Chain (Signed V) →ₗ[ℤ] Chain (Signed V) :=
  if Odd i then swap - LinearMap.id else swap + LinearMap.id

lemma boundary_op (i : ℕ) (c : Chain (Signed V)) :
    boundary (op i c) = op i (boundary c) := by
  by_cases hi : Odd i <;>
    simp [op, hi, swap, boundary_mapVertices]

lemma op_succ_op (i : ℕ) (c : Chain (Signed V)) : op (i + 1) (op i c) = 0 := by
  rcases Nat.even_or_odd i with hi | hi
  · have hn := Nat.not_odd_iff_even.mpr hi
    simp [op, hn, hi.add_one, map_add]
  · have hn := Nat.not_odd_iff_even.mpr hi.add_one
    simp [op, hi, hn, map_sub]
    abel

lemma supported_op {G : SimpleGraph V} {k : ℕ} {c : Chain (Signed V)}
    (hc : Supported (Good G k) c) (i : ℕ) : Supported (Good G k) (op i c) := by
  have hs : Supported (Good G k) (swap c) :=
    supported_mapVertices flip (fun l hl => ⟨hl.1.map_flip, by simpa using hl.2⟩) hc
  by_cases hi : Odd i
  · simpa only [op, if_pos hi, LinearMap.sub_apply, LinearMap.id_apply] using
      supported_sub hs hc
  · simpa only [op, if_neg hi, LinearMap.add_apply, LinearMap.id_apply] using
      supported_add hs hc

/-- A finite initial segment of the integral periodic resolution in a graph. -/
def HasResolution (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ c : ℕ → Chain (Signed V),
    (∀ i ≤ d, Supported (Good G (i + 1)) (c i)) ∧
    boundary (c 0) = basis [] ∧
    ∀ i < d, boundary (c (i + 1)) = op (i + 1) (c i)

lemma resolution_cycle {d : ℕ}
    {c : ℕ → Chain (Signed V)} (hzero : boundary (c 0) = basis [])
    (hrel : ∀ i < d, boundary (c (i + 1)) = op (i + 1) (c i)) :
    boundary (op (d + 1) (c d)) = 0 := by
  rw [boundary_op]
  cases d with
  | zero => simp [hzero, op, swap]
  | succ i => rw [hrel i (by omega), op_succ_op]

def signedMap (f : V → W) (x : Signed V) : Signed W := (x.1, f x.2)

lemma map_op (f : V → W) (i : ℕ) (c : Chain (Signed V)) :
    mapVertices (signedMap f) (op i c) = op i (mapVertices (signedMap f) c) := by
  have hs : mapVertices (signedMap f) (swap c) =
      swap (mapVertices (signedMap f) c) := by
    simp only [swap, mapVertices_comp]
    rfl
  by_cases hi : Odd i <;> simp [op, hi, hs]

lemma HasResolution.map {G : SimpleGraph V} {H : SimpleGraph W}
    {d : ℕ} (h : HasResolution G d) (f : G →g H) : HasResolution H d := by
  obtain ⟨c, hc, hzero, hrel⟩ := h
  refine ⟨fun i => mapVertices (signedMap f) (c i), ?_, ?_, ?_⟩
  · intro i hi
    refine supported_mapVertices (signedMap f) (P := Good G (i + 1))
      (Q := Good H (i + 1)) ?_ (hc i hi)
    intro l hl
    refine ⟨?_, by simpa using hl.2⟩
    rintro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact f.map_adj (hl.1 x hx y hy hab)
  · rw [boundary_mapVertices, hzero, mapVertices_basis]
    rfl
  · intro i hi
    rw [boundary_mapVertices, hrel i hi, map_op]

lemma hasResolution_complete_two : HasResolution (SimpleGraph.completeGraph (Fin 2)) 1 := by
  let a : Signed (Fin 2) := (0, 0)
  let b : Signed (Fin 2) := (0, 1)
  let c : ℕ → Chain (Signed (Fin 2)) := fun i =>
    if i = 0 then basis [a] else basis [a, b] + basis [b, flip a]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · apply supported_basis
      constructor
      · simp [Face]
      · rfl
    · apply supported_add <;> apply supported_basis
      · constructor
        · simp [Face, a, b]
        · rfl
      · constructor
        · simp [Face, a, b, flip, SimpleGraph.completeGraph]
        · rfl
  · simp [c, boundaryBasis]
  · intro i hi
    have : i = 0 := by omega
    subst i
    simp [c, boundaryBasis, op, swap, map_add]

end
end Chains

end

/-! ### Upstream module `ErdosProblems/Erdos750/MycielskiChains.lean` -/

section
/-!
# A chain contraction across the generalized Mycielski cylinder

At stage `t`, one shore is at height `t` and the other at height `t-1`.
Consecutive stages are contiguous maps of biclique complexes. At the final
stage one shore is the apex, so its image can be coned off.
-/

namespace Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section
universe u v
variable {V : Type u} {W : Type v}

lemma zmod_two_eq_add_one {a b : ZMod 2} (h : a ≠ b) : b = a + 1 := by
  exact (by decide : ∀ a b : ZMod 2, a ≠ b → b = a + 1) a b h

def stageLevel (t : ℕ) (a : ZMod 2) : ℕ := if (t : ZMod 2) = a then t else t - 1

lemma stageLevel_le (t : ℕ) (a : ZMod 2) : stageLevel t a ≤ t := by
  unfold stageLevel
  split <;> omega

def atHeight (s i : ℕ) (v : V) : MycVerts s V :=
  if h : i < s then lvl s ⟨i, h⟩ v else apex s V

def stage (s t : ℕ) (x : Signed V) : Signed (MycVerts s V) :=
  (x.1, atHeight s (stageLevel t x.1) x.2)

lemma atHeight_adj {G : SimpleGraph V} {s i j : ℕ} (hs : 0 < s)
    (hi : i ≤ s) (hj : j ≤ s)
    (hij : (i = 0 ∧ j = 0) ∨ i + 1 = j ∨ j + 1 = i)
    {a b : V} (hab : G.Adj a b) :
    (genMyc s G).Adj (atHeight s i a) (atHeight s j b) := by
  by_cases his : i < s <;> by_cases hjs : j < s
  · change MycAdj s G _ _
    simp only [atHeight, dif_pos his, dif_pos hjs, lvl, MycAdj]
    rcases hij with ⟨hi0, hj0⟩ | hij | hji
    · exact Or.inl ⟨hi0, hj0, hab⟩
    · exact Or.inr (Or.inl ⟨hij.symm, hab⟩)
    · exact Or.inr (Or.inr ⟨hji.symm, hab⟩)
  · change MycAdj s G _ _
    simp only [atHeight, dif_pos his, dif_neg hjs, lvl, apex, MycAdj]
    rcases hij with h | h | h <;> omega
  · change MycAdj s G _ _
    simp only [atHeight, dif_neg his, dif_pos hjs, lvl, apex, MycAdj]
    rcases hij with h | h | h <;> omega
  · rcases hij with h | h | h <;> omega

lemma stageLevel_same {t : ℕ} {a b : ZMod 2} (hab : a ≠ b) :
    (stageLevel t a = 0 ∧ stageLevel t b = 0) ∨
      stageLevel t a + 1 = stageLevel t b ∨
      stageLevel t b + 1 = stageLevel t a := by
  by_cases ha : (t : ZMod 2) = a
  · have hb : (t : ZMod 2) ≠ b := by simpa [ha] using hab
    simp only [stageLevel, if_pos ha, if_neg hb]
    by_cases ht : t = 0
    · exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr (Or.inr (by omega))
  · have hb : (t : ZMod 2) = b := by
      have h1 := zmod_two_eq_add_one ha
      have h2 := zmod_two_eq_add_one hab
      rw [h1] at h2
      have : (1 + 1 : ZMod 2) = 0 := by decide
      simpa [add_assoc, this] using h2.symm
    simp only [stageLevel, if_neg ha, if_pos hb]
    by_cases ht : t = 0
    · exact Or.inl ⟨by omega, ht⟩
    · exact Or.inr (Or.inl (by omega))

lemma stageLevel_cross {t : ℕ} {a b : ZMod 2} (hab : a ≠ b) :
    (stageLevel t a = 0 ∧ stageLevel (t + 1) b = 0) ∨
      stageLevel t a + 1 = stageLevel (t + 1) b ∨
      stageLevel (t + 1) b + 1 = stageLevel t a := by
  by_cases ha : (t : ZMod 2) = a
  · have hb : ((t + 1 : ℕ) : ZMod 2) = b := by
      simpa [ha] using (zmod_two_eq_add_one hab).symm
    simp [stageLevel, ha, hb]
  · have hb : ((t + 1 : ℕ) : ZMod 2) ≠ b := by
      have h1 := zmod_two_eq_add_one ha
      have : ((t + 1 : ℕ) : ZMod 2) = a := by simpa using h1.symm
      simpa [this] using hab
    simp only [stageLevel, if_neg ha, if_neg hb, Nat.add_sub_cancel]
    by_cases ht : t = 0
    · exact Or.inl ⟨by omega, ht⟩
    · exact Or.inr (Or.inl (by omega))

lemma stage_adj_same {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t ≤ s)
    {a b : Signed V} (hab : a.1 ≠ b.1) (he : G.Adj a.2 b.2) :
    (genMyc s G).Adj (stage s t a).2 (stage s t b).2 :=
  atHeight_adj hs ((stageLevel_le t a.1).trans ht)
    ((stageLevel_le t b.1).trans ht) (stageLevel_same hab) he

lemma stage_adj_cross {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t < s)
    {a b : Signed V} (hab : a.1 ≠ b.1) (he : G.Adj a.2 b.2) :
    (genMyc s G).Adj (stage s t a).2 (stage s (t + 1) b).2 :=
  atHeight_adj hs ((stageLevel_le t a.1).trans (by omega))
    ((stageLevel_le (t + 1) b.1).trans (by omega)) (stageLevel_cross hab) he

def PrismSupported {A B : Type*} (f g : A → B) (l : List A) (q : List B) : Prop :=
  ∀ y ∈ q, ∃ x ∈ l, y = f x ∨ y = g x

lemma prism_supported {A B : Type*} (f g : A → B) (l : List A) :
    Supported (PrismSupported f g l) (prism f g (basis l)) := by
  induction l with
  | nil => simpa using supported_zero (PrismSupported f g [])
  | cons x xs ih =>
    rw [prism_basis, prismBasis_cons]
    apply supported_sub
    · apply supported_basis
      intro y hy
      simp only [List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | rfl | ⟨z, hz, rfl⟩
      · exact ⟨x, by simp, Or.inl rfl⟩
      · exact ⟨x, by simp, Or.inr rfl⟩
      · exact ⟨z, by simp [hz], Or.inr rfl⟩
    · rw [← prism_basis]
      refine supported_prepend (P := PrismSupported f g xs)
        (Q := PrismSupported f g (x :: xs)) (f x) ?_ ih
      intro q hq y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨x, by simp, Or.inl rfl⟩
      · obtain ⟨z, hz, h⟩ := hq y hy
        exact ⟨z, by simp [hz], h⟩

lemma prism_stage_good {G : SimpleGraph V} {s t k : ℕ} (hs : 0 < s) (ht : t < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (prism (stage s t) (stage s (t + 1)) c) := by
  refine supported_linearMap (P := Good G k) (Q := Good (genMyc s G) (k + 1))
    (prism (stage s t) (stage s (t + 1))) ?_ hc
  intro l hl
  refine (supported_and (prism_supported (stage s t) (stage s (t + 1)) l)
    (prismBasis_supported_length (stage s t) (stage s (t + 1)) l)).mono
      (Q := Good (genMyc s G) (k + 1)) ?_
  intro q hq
  refine ⟨?_, by have hk := hl.2; omega⟩
  intro a ha b hb hab
  obtain ⟨x, hx, hx'⟩ := hq.1 a ha
  obtain ⟨y, hy, hy'⟩ := hq.1 b hb
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact stage_adj_same hs (by omega) hab (hl.1 x hx y hy hab)
  · exact stage_adj_cross hs ht hab (hl.1 x hx y hy hab)
  · exact (stage_adj_cross (G := G) (a := y) (b := x) hs ht hab.symm
      (hl.1 y hy x hx hab.symm)).symm
  · exact stage_adj_same hs (by omega) hab (hl.1 x hx y hy hab)

lemma Face.cons {G : SimpleGraph V} {l : List (Signed V)} {a : Signed V}
    (hl : Face G l)
    (ha : ∀ b ∈ l, a.1 ≠ b.1 → G.Adj a.2 b.2) : Face G (a :: l) := by
  intro x hx y hy hxy
  rcases List.mem_cons.mp hx with rfl | hx' <;>
    rcases List.mem_cons.mp hy with rfl | hy'
  · exact (hxy rfl).elim
  · exact ha y hy' hxy
  · exact (ha x hx' hxy.symm).symm
  · exact hl x hx' y hy' hxy

lemma stage_face {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t ≤ s)
    {l : List (Signed V)} (hl : Face G l) : Face (genMyc s G) (l.map (stage s t)) := by
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact stage_adj_same hs ht hab (hl x hx y hy hab)

def top (s : ℕ) : Signed (MycVerts s V) := ((s : ZMod 2), apex s V)

lemma top_adj_stage {G : SimpleGraph V} {s : ℕ} (hs : 0 < s) {x : Signed V}
    (hx : (top s (V := V)).1 ≠ (stage s s x).1) :
    (genMyc s G).Adj (top s (V := V)).2 (stage s s x).2 := by
  have hx' : (s : ZMod 2) ≠ x.1 := hx
  change MycAdj s G (apex s V) (atHeight s (stageLevel s x.1) x.2)
  simp only [stageLevel, if_neg hx', atHeight, dif_pos (show s - 1 < s by omega),
    apex, lvl, MycAdj]
  omega

lemma cone_stage_good {G : SimpleGraph V} {s k : ℕ} (hs : 0 < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (cone (top s) (stage s s) c) := by
  refine supported_linearMap (P := Good G k) (Q := Good (genMyc s G) (k + 1))
    (cone (top s) (stage s s)) ?_ hc
  intro l hl
  change Supported _ (prepend (top s) (mapVertices (stage s s) (basis l)))
  rw [mapVertices_basis, prepend_basis]
  apply supported_basis
  refine ⟨(stage_face hs le_rfl hl.1).cons ?_, by simpa using hl.2⟩
  intro b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact top_adj_stage hs hab

lemma boundary_prisms {A B : Type*} (f : ℕ → A → B) (n : ℕ) (c : Chain A) :
    boundary ((∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) c) +
      (∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) (boundary c) =
        mapVertices (f n) c - mapVertices (f 0) c := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, LinearMap.add_apply, map_add]
    have h := boundary_prism_add_prism_boundary (f n) (f (n + 1)) c
    calc
      _ = (boundary ((∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) c) +
            (∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) (boundary c)) +
          (boundary (prism (f n) (f (n + 1)) c) +
            prism (f n) (f (n + 1)) (boundary c)) := by abel
      _ = _ := by rw [ih, h]; abel

def cylinderFill (s : ℕ) : Chain (Signed V) →ₗ[ℤ] Chain (Signed (MycVerts s V)) :=
  cone (top s) (stage s s) - ∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))

lemma boundary_cylinderFill (s : ℕ) (c : Chain (Signed V)) :
    boundary (cylinderFill s c) + cylinderFill s (boundary c) =
      mapVertices (stage s 0) c := by
  have hc := boundary_cone (top s) (stage s s) c
  have hp := boundary_prisms (stage s (V := V)) s c
  simp only [cylinderFill, LinearMap.sub_apply, map_sub]
  calc
    _ = (boundary (cone (top s) (stage s s) c) +
          cone (top s) (stage s s) (boundary c)) -
        (boundary ((∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))) c) +
          (∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))) (boundary c)) := by abel
    _ = _ := by rw [hc, hp]; abel

lemma cylinderFill_good {G : SimpleGraph V} {s k : ℕ} (hs : 0 < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (cylinderFill s c) := by
  apply supported_sub (cone_stage_good hs hc)
  simp only [LinearMap.sum_apply]
  exact supported_sum fun t ht => prism_stage_good hs (Finset.mem_range.mp ht) hc

def baseEmbedding (s : ℕ) (hs : 0 < s) (G : SimpleGraph V) : G →g genMyc s G where
  toFun v := lvl s ⟨0, hs⟩ v
  map_rel' h := Or.inl ⟨rfl, rfl, h⟩

lemma stage_zero (s : ℕ) (hs : 0 < s) (G : SimpleGraph V) :
    stage s 0 = signedMap (baseEmbedding s hs G) := by
  funext x
  have hzero : stageLevel 0 x.1 = 0 := by simp [stageLevel]
  simp [stage, hzero, atHeight, hs, signedMap, baseEmbedding]
  rfl

lemma hasResolution_genMyc {G : SimpleGraph V} {d s : ℕ}
    (h : HasResolution G d) (hs : 0 < s) : HasResolution (genMyc s G) (d + 1) := by
  obtain ⟨c, hc, hzero, hrel⟩ := h
  let f := baseEmbedding s hs G
  let e : ℕ → Chain (Signed (MycVerts s V)) := fun i =>
    if i ≤ d then mapVertices (signedMap f) (c i)
    else cylinderFill s (op (d + 1) (c d))
  have he (i : ℕ) (hi : i ≤ d) : e i = mapVertices (signedMap f) (c i) := if_pos hi
  have hetop : e (d + 1) = cylinderFill s (op (d + 1) (c d)) := if_neg (by omega)
  have hmap (i : ℕ) (hi : i ≤ d) :
      Supported (Good (genMyc s G) (i + 1)) (mapVertices (signedMap f) (c i)) := by
    rw [← stage_zero s hs G]
    refine supported_mapVertices _ (P := Good G (i + 1)) ?_ (hc i hi)
    intro l hl
    exact ⟨stage_face hs (by omega) hl.1, by simpa using hl.2⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hid : i ≤ d
    · rw [he i hid]
      exact hmap i hid
    · have hitop : i = d + 1 := by omega
      subst i
      rw [hetop]
      exact cylinderFill_good hs (supported_op (hc d le_rfl) (d + 1))
  · rw [he 0 (Nat.zero_le _), boundary_mapVertices, hzero, mapVertices_basis]
    rfl
  · intro i hi
    by_cases hid : i < d
    · rw [he (i + 1) (by omega), he i (by omega), boundary_mapVertices,
        hrel i hid, map_op]
    · have hid' : i = d := by omega
      subst i
      rw [hetop, he d le_rfl]
      have hcycle := resolution_cycle hzero hrel
      have hfill := boundary_cylinderFill s (op (d + 1) (c d))
      rw [hcycle, map_zero, add_zero, stage_zero s hs G, map_op] at hfill
      exact hfill

end
end Chains

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/TargetChains.lean` -/

section
/-!
Finite oriented simplex chains, implemented as the exterior algebra of the
free module on the vertices.  The exterior-algebra basis is indexed by
`Finset V`; its coordinate module is literally `Finset V →₀ R`.
-/

namespace TargetChains

open scoped BigOperators

universe u v

section Contraction

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

theorem contraction_natural (εM : M →ₗ[R] R) (εN : N →ₗ[R] R)
    (f : M →ₗ[R] N) (hε : εN.comp f = εM) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft εN (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft εM x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp [hx, hy]
  | ι_mul x m hx =>
      rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, hx]
      have hm := LinearMap.congr_fun hε m
      simp only [LinearMap.comp_apply] at hm
      rw [hm]
      simp

end Contraction

section FiniteVertices

variable (R : Type*) [CommRing R]
variable (V : Type u) [Fintype V] [LinearOrder V]

abbrev OrientedSimplex (q : ℕ) := Set.powersetCard V (q + 1)
abbrev Chain (q : ℕ) := OrientedSimplex V q →₀ R
abbrev FullChain := Finset V →₀ R

noncomputable def vertexBasis : Module.Basis V R (V →₀ R) := Finsupp.basisSingleOne

noncomputable def exteriorBasis :
    Module.Basis (Finset V) R (ExteriorAlgebra R (V →₀ R)) :=
  (vertexBasis R V).ExteriorAlgebra

noncomputable def toExterior :
    FullChain R V ≃ₗ[R] ExteriorAlgebra R (V →₀ R) :=
  (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_single (s : Finset V) (r : R) :
    toExterior R V (Finsupp.single s r) = r • exteriorBasis R V s := by
  simp [toExterior]

noncomputable def augmentation : (V →₀ R) →ₗ[R] R :=
  Finsupp.lsum R (fun _ => LinearMap.id)

noncomputable def exteriorContraction :
    ExteriorAlgebra R (V →₀ R) →ₗ[R] ExteriorAlgebra R (V →₀ R) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (V →₀ R)))
    (augmentation R V)

@[simp]
theorem augmentation_single (v : V) (r : R) :
    augmentation R V (Finsupp.single v r) = r := by
  simp [augmentation]

noncomputable def boundary : FullChain R V →ₗ[R] FullChain R V :=
  (exteriorBasis R V).repr ∘ₗ
    exteriorContraction R V ∘ₗ
      (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_boundary (c : FullChain R V) :
    toExterior R V (boundary R V c) =
      exteriorContraction R V (toExterior R V c) := by
  simp [boundary, toExterior]

theorem boundary_boundary (c : FullChain R V) :
    boundary R V (boundary R V c) = 0 := by
  apply (toExterior R V).injective
  rw [map_zero, toExterior_boundary, toExterior_boundary]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (CliffordAlgebra.contractLeft (augmentation R V) (toExterior R V c)) = 0
  exact CliffordAlgebra.contractLeft_contractLeft _ _

/-! Ordinary (non-augmented) chains exclude the empty face.  We realize
them as the kernel of the empty-face coordinate, and explicitly project
away that coordinate after applying the augmented boundary. -/

noncomputable def positiveSubmodule : Submodule R (FullChain R V) :=
  LinearMap.ker (Finsupp.lapply ∅)

noncomputable abbrev PositiveChain := positiveSubmodule R V

noncomputable def positiveInclusion : PositiveChain R V →ₗ[R] FullChain R V :=
  (positiveSubmodule R V).subtype

noncomputable def projectPositive : FullChain R V →ₗ[R] PositiveChain R V where
  toFun c := ⟨c - Finsupp.single ∅ (c ∅), by
    change c ∅ - (Finsupp.single ∅ (c ∅)) ∅ = 0
    simp⟩
  map_add' c d := by
    apply Subtype.ext
    ext s
    by_cases hs : s = ∅
    · subst s; simp
    · simp [hs, Ne.symm hs]
  map_smul' r c := by
    apply Subtype.ext
    ext s
    by_cases hs : s = ∅
    · subst s; simp
    · simp [hs, Ne.symm hs]

@[simp]
theorem projectPositive_coe (c : FullChain R V) :
    (projectPositive R V c : FullChain R V) =
      c - Finsupp.single ∅ (c ∅) := rfl

@[simp]
theorem positiveInclusion_projectPositive (c : FullChain R V) :
    positiveInclusion R V (projectPositive R V c) =
      c - Finsupp.single ∅ (c ∅) := rfl

@[simp]
theorem projectPositive_apply_empty (c : FullChain R V) :
    (projectPositive R V c : FullChain R V) ∅ = 0 := by simp

@[simp]
theorem projectPositive_inclusion (c : PositiveChain R V) :
    projectPositive R V (positiveInclusion R V c) = c := by
  apply Subtype.ext
  rw [projectPositive_coe]
  have hc : (c : FullChain R V) ∅ = 0 := by
    have hc' := c.property
    change Finsupp.lapply ∅ (c : FullChain R V) = 0 at hc'
    simpa using hc'
  change (c : FullChain R V) -
      Finsupp.single (∅ : Finset V) ((c : FullChain R V) ∅) = (c : FullChain R V)
  rw [hc]
  simp

@[simp]
theorem projectPositive_single_empty (r : R) :
    projectPositive R V (Finsupp.single ∅ r) = 0 := by
  apply Subtype.ext
  ext s
  by_cases hs : s = ∅ <;> simp [projectPositive_coe, hs]

theorem boundary_single_empty (r : R) :
    boundary R V (Finsupp.single ∅ r) = 0 := by
  apply (toExterior R V).injective
  rw [map_zero, toExterior_boundary, toExterior_single]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (r • exteriorBasis R V ∅) = 0
  rw [map_smul]
  suffices exteriorBasis R V ∅ = 1 by
    rw [this, CliffordAlgebra.contractLeft_one, smul_zero]
  change (vertexBasis R V).ExteriorAlgebra ∅ = 1
  simp [ExteriorAlgebra.basis_apply]

theorem boundary_projectPositive (c : FullChain R V) :
    boundary R V (positiveInclusion R V (projectPositive R V c)) =
      boundary R V c := by
  rw [positiveInclusion_projectPositive]
  rw [map_sub, boundary_single_empty, sub_zero]

noncomputable def reducedBoundary : PositiveChain R V →ₗ[R] PositiveChain R V :=
  projectPositive R V ∘ₗ boundary R V ∘ₗ positiveInclusion R V

theorem reducedBoundary_reducedBoundary (c : PositiveChain R V) :
    reducedBoundary R V (reducedBoundary R V c) = 0 := by
  apply Subtype.ext
  change (projectPositive R V
    (boundary R V (positiveInclusion R V (projectPositive R V
      (boundary R V (positiveInclusion R V c))))) : FullChain R V) = 0
  rw [boundary_projectPositive, boundary_boundary]
  simp

variable {R V}

noncomputable def vertexMap {W : Type v} [Fintype W] [LinearOrder W] (f : V → W) :
    (V →₀ R) →ₗ[R] (W →₀ R) :=
  Finsupp.lmapDomain R R f

@[simp]
theorem vertexMap_single {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (v : V) (r : R) :
    vertexMap f (Finsupp.single v r) = Finsupp.single (f v) r := by
  simp [vertexMap]

theorem augmentation_vertexMap {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) :
    (augmentation R W).comp (vertexMap f) = augmentation R V := by
  ext v r
  simp

noncomputable def map {W : Type v} [Fintype W] [LinearOrder W] (f : V → W) :
    FullChain R V →ₗ[R] FullChain R W :=
  (exteriorBasis R W).repr ∘ₗ
    (ExteriorAlgebra.map (vertexMap f)).toLinearMap ∘ₗ
      (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_map {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    toExterior R W (map f c) =
      ExteriorAlgebra.map (vertexMap f) (toExterior R V c) := by
  simp [map, toExterior]

theorem map_boundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    map f (boundary R V c) = boundary R W (map f c) := by
  apply (toExterior R W).injective
  simp only [toExterior_map, toExterior_boundary]
  exact (contraction_natural (augmentation R V) (augmentation R W)
    (vertexMap f) (augmentation_vertexMap f) (toExterior R V c)).symm

theorem map_single_empty {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (r : R) :
    map f (Finsupp.single ∅ r) = Finsupp.single ∅ r := by
  apply (toExterior R W).injective
  rw [toExterior_map, toExterior_single, toExterior_single, map_smul]
  suffices exteriorBasis R V ∅ = 1 ∧ exteriorBasis R W ∅ = 1 by
    rw [this.1, this.2, map_one]
  constructor <;> change (vertexBasis R _).ExteriorAlgebra ∅ = 1 <;>
    simp [ExteriorAlgebra.basis_apply]

theorem projectPositive_map_projectPositive {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    projectPositive R W
        (map f (positiveInclusion R V (projectPositive R V c))) =
      projectPositive R W (map f c) := by
  rw [positiveInclusion_projectPositive]
  rw [map_sub, map_single_empty, map_sub, projectPositive_single_empty]
  exact sub_zero (projectPositive R W (map f c))

noncomputable def reducedMap {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) : PositiveChain R V →ₗ[R] PositiveChain R W :=
  projectPositive R W ∘ₗ map f ∘ₗ positiveInclusion R V

theorem reducedMap_reducedBoundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : PositiveChain R V) :
    reducedMap f (reducedBoundary R V c) =
      reducedBoundary R W (reducedMap f c) := by
  apply Subtype.ext
  change (projectPositive R W
      (map f (positiveInclusion R V (projectPositive R V
        (boundary R V (positiveInclusion R V c))))) : FullChain R W) =
    projectPositive R W
      (boundary R W (positiveInclusion R W (projectPositive R W
        (map f (positiveInclusion R V c)))))
  rw [projectPositive_map_projectPositive, boundary_projectPositive, map_boundary]

/-! On a basis simplex, `map` is the exterior product of the vertex images.
This is the normalized simplicial map: alternation supplies the sorting sign,
and a repeated image vertex makes the result zero. -/

theorem toExterior_map_single {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (s : Finset V) :
    toExterior R W (map f (Finsupp.single s 1)) =
      ExteriorAlgebra.map (vertexMap f) (exteriorBasis R V s) := by
  simp

end FiniteVertices

end TargetChains

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/TargetBridge.lean` -/

section
namespace TargetBridge

open TargetChains

noncomputable section

variable {X V : Type*} [Fintype V] [LinearOrder V]

def wedgePrepend (v : V) : FullChain ℤ V →ₗ[ℤ] FullChain ℤ V :=
  (toExterior ℤ V).symm.toLinearMap ∘ₗ
    (LinearMap.mulLeft ℤ (ExteriorAlgebra.ι ℤ (Finsupp.single v 1))) ∘ₗ
      (toExterior ℤ V).toLinearMap

@[simp]
theorem toExterior_wedgePrepend (v : V) (c : FullChain ℤ V) :
    toExterior ℤ V (wedgePrepend v c) =
      ExteriorAlgebra.ι ℤ (Finsupp.single v 1) * toExterior ℤ V c := by
  simp [wedgePrepend]

def labelList (lab : X → V) : List X → FullChain ℤ V
  | [] => (toExterior ℤ V).symm 1
  | x :: xs => wedgePrepend (lab x) (labelList lab xs)

@[simp]
theorem toExterior_labelList_nil (lab : X → V) :
    toExterior ℤ V (labelList lab []) = 1 := by
  simp [labelList]

@[simp]
theorem toExterior_labelList_cons (lab : X → V) (x : X) (xs : List X) :
    toExterior ℤ V (labelList lab (x :: xs)) =
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) *
        toExterior ℤ V (labelList lab xs) := by
  simp [labelList]

def labelLists (lab : X → V) : SourceFlags.Chain X →ₗ[ℤ] FullChain ℤ V :=
  (Finsupp.lift (FullChain ℤ V) ℤ (List X)) (labelList lab)

@[simp]
theorem labelLists_basis (lab : X → V) (l : List X) :
    labelLists lab (SourceFlags.basis l) = labelList lab l := by
  simp [labelLists, SourceFlags.basis]

theorem labelLists_prepend (lab : X → V) (x : X) (c : SourceFlags.Chain X) :
    labelLists lab (SourceFlags.prepend x c) =
      wedgePrepend (lab x) (labelLists lab c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp [labelList]

theorem boundary_labelList (lab : X → V) (l : List X) :
    boundary ℤ V (labelList lab l) =
      labelLists lab (SourceFlags.boundaryBasis l) := by
  induction l with
  | nil =>
      apply (toExterior ℤ V).injective
      simp [labelList, SourceFlags.boundaryBasis, exteriorContraction,
        CliffordAlgebra.contractLeft_one]
  | cons x xs ih =>
      rw [SourceFlags.boundaryBasis_cons, map_sub, labelLists_basis,
        labelLists_prepend]
      apply (toExterior ℤ V).injective
      rw [map_sub, toExterior_boundary, toExterior_labelList_cons,
        toExterior_wedgePrepend]
      change CliffordAlgebra.contractLeft (augmentation ℤ V)
          (ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) *
            toExterior ℤ V (labelList lab xs)) = _
      rw [CliffordAlgebra.contractLeft_ι_mul, augmentation_single, one_smul]
      have ihE := congrArg (toExterior ℤ V) ih
      rw [show CliffordAlgebra.contractLeft (augmentation ℤ V)
          (toExterior ℤ V (labelList lab xs)) =
          toExterior ℤ V (labelLists lab (SourceFlags.boundaryBasis xs)) by
        simpa [exteriorContraction] using ihE]

theorem labelLists_boundary (lab : X → V) (c : SourceFlags.Chain X) :
    boundary ℤ V (labelLists lab c) =
      labelLists lab (SourceFlags.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp only [map_smul, labelLists_basis, SourceFlags.boundary_basis]
      rw [boundary_labelList]

/-! The direct tuple formula requested by the target-chain construction. -/
theorem labelList_eq_ιMulti (lab : X → V) (l : List X) :
    toExterior ℤ V (labelList lab l) =
      ExteriorAlgebra.ιMulti ℤ l.length
        (fun i => Finsupp.single (lab (l.get i)) 1) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [toExterior_labelList_cons]
      change _ = ExteriorAlgebra.ιMulti ℤ xs.length.succ
        (fun i : Fin xs.length.succ =>
          Finsupp.single (lab ((x :: xs).get i)) 1)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 1

theorem labelList_eq_zero_of_repeated (lab : X → V) (l : List X)
    (h : ¬ Function.Injective (fun i => lab (l.get i))) :
    labelList lab l = 0 := by
  apply (toExterior ℤ V).injective
  rw [map_zero, labelList_eq_ιMulti]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hinj
  apply h
  intro i j hij
  apply hinj
  exact congrArg (fun v : V => Finsupp.single v (1 : ℤ)) hij

end

end TargetBridge

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/PositiveTarget.lean` -/

section
/-!
The positive-dimensional target complex.  The empty finset is deliberately
removed: it is fixed by every vertex permutation and therefore cannot occur
in the free-orbit argument.
-/

namespace PositiveTarget

open TargetChains TargetBridge

noncomputable section

universe u v

variable (R : Type*) [CommRing R]
variable (V : Type u) [Fintype V] [LinearOrder V]

abbrev Chain := PositiveChain R V

abbrev boundary : Chain R V →ₗ[R] Chain R V := reducedBoundary R V

theorem boundary_boundary (c : Chain R V) :
    boundary R V (boundary R V c) = 0 :=
  reducedBoundary_reducedBoundary R V c

/-! A vertex is a genuine positive chain, and the truncated boundary drops
its augmented empty-face boundary. -/
theorem iota_single_eq_exteriorBasis_singleton (v : V) :
    ExteriorAlgebra.ι R (Finsupp.single v 1) =
      exteriorBasis R V {v} := by
  change ExteriorAlgebra.ι R (Finsupp.single v 1) =
    (vertexBasis R V).ExteriorAlgebra {v}
  have hb := ExteriorAlgebra.basis_apply_ofCard (vertexBasis R V)
    (s := ({v} : Finset V)) (n := 1) (by simp)
  rw [hb]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp [vertexBasis, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_singleton]

theorem fullBoundary_singleton (v : V) :
    TargetChains.boundary R V (Finsupp.single {v} 1) =
      Finsupp.single ∅ 1 := by
  apply (toExterior R V).injective
  rw [toExterior_boundary, toExterior_single, toExterior_single]
  rw [← iota_single_eq_exteriorBasis_singleton]
  rw [one_smul]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (ExteriorAlgebra.ι R (Finsupp.single v 1)) =
    (1 : R) • exteriorBasis R V ∅
  rw [show exteriorBasis R V ∅ = 1 by
    change (vertexBasis R V).ExteriorAlgebra ∅ = 1
    simp [ExteriorAlgebra.basis_apply]]
  simp [CliffordAlgebra.contractLeft_ι, augmentation_single]

noncomputable def vertex (v : V) : Chain R V :=
  projectPositive R V (Finsupp.single {v} 1)

@[simp]
theorem boundary_vertex (v : V) :
    boundary R V (vertex R V v) = 0 := by
  apply Subtype.ext
  change (projectPositive R V
    (TargetChains.boundary R V
      (positiveInclusion R V (projectPositive R V
        (Finsupp.single {v} 1)))) : FullChain R V) = 0
  rw [TargetChains.boundary_projectPositive, fullBoundary_singleton,
    projectPositive_single_empty]
  rfl

/-! This is the ordinary augmentation on 0-chains.  Algebraically it is
the empty-face coefficient of the augmented boundary before that coordinate
is discarded. -/
noncomputable def augmentation : Chain R V →ₗ[R] R :=
  Finsupp.lapply ∅ ∘ₗ TargetChains.boundary R V ∘ₗ positiveInclusion R V

theorem augmentation_boundary (c : Chain R V) :
    augmentation R V (boundary R V c) = 0 := by
  change TargetChains.boundary R V
      (positiveInclusion R V (projectPositive R V
        (TargetChains.boundary R V (positiveInclusion R V c)))) ∅ = 0
  rw [TargetChains.boundary_projectPositive, TargetChains.boundary_boundary]
  rfl

variable {R V}

noncomputable def map {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) : Chain R V →ₗ[R] Chain R W :=
  reducedMap f

theorem map_boundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : Chain R V) :
    map f (boundary R V c) = boundary R W (map f c) :=
  reducedMap_reducedBoundary f c

section Labels

variable {X : Type*}

noncomputable def labelLists (lab : X → V) :
    SourceFlags.Chain X →ₗ[ℤ] Chain ℤ V :=
  projectPositive ℤ V ∘ₗ TargetBridge.labelLists lab

theorem labelList_nil_eq_single_empty (lab : X → V) :
    TargetBridge.labelList lab [] = Finsupp.single ∅ 1 := by
  apply (toExterior ℤ V).injective
  rw [toExterior_labelList_nil, toExterior_single]
  rw [one_smul]
  change (1 : ExteriorAlgebra ℤ (V →₀ ℤ)) =
    (vertexBasis ℤ V).ExteriorAlgebra ∅
  simp [ExteriorAlgebra.basis_apply]

@[simp]
theorem labelLists_empty (lab : X → V) :
    labelLists lab (SourceFlags.basis []) = 0 := by
  simp only [labelLists, LinearMap.comp_apply, TargetBridge.labelLists_basis]
  rw [labelList_nil_eq_single_empty, projectPositive_single_empty]

theorem labelLists_basis (lab : X → V) (l : List X) :
    labelLists lab (SourceFlags.basis l) =
      projectPositive ℤ V (TargetBridge.labelList lab l) := by
  simp [labelLists]

/- On every actual (nonempty) source flag, projection does nothing: the
reduced label map is literally the pre-existing exterior-algebra label. -/

theorem labelLists_boundary (lab : X → V) (c : SourceFlags.Chain X) :
    boundary ℤ V (labelLists lab c) =
      labelLists lab (SourceFlags.boundary c) := by
  apply Subtype.ext
  change (projectPositive ℤ V
      (TargetChains.boundary ℤ V
        (positiveInclusion ℤ V (projectPositive ℤ V
          (TargetBridge.labelLists lab c)))) : FullChain ℤ V) =
    projectPositive ℤ V
      (TargetBridge.labelLists lab (SourceFlags.boundary c))
  rw [boundary_projectPositive, TargetBridge.labelLists_boundary]

end Labels

end

end PositiveTarget

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/AllowedFaces.lean` -/

section
/-!
The alpha-split target complex for the cyclic Tucker labeling.

A vertex is a sign together with a label index.  At a low index there may be
at most one sign in a face; at a high index there may be at most `p - 1`
signs.  The resulting faces form a downward-closed complex of maximum face
cardinality `alpha + (m - alpha) * (p - 1)`.
-/

namespace AllowedFaces

open scoped BigOperators

abbrev Label (p m : ℕ) := ZMod p × Fin m

/-- Vertices of `s` whose second coordinate is `j`. -/
def fiber {p m : ℕ} (s : Finset (Label p m)) (j : Fin m) :
    Finset (Label p m) :=
  s.filter fun v ↦ v.2 = j

/-- Capacity of the `j`th label coordinate. -/
def capacity (p alpha : ℕ) {m : ℕ} (j : Fin m) : ℕ :=
  if j.val < alpha then 1 else p - 1

/-- The alpha-split faces: one sign at a low index, and at most `p - 1`
signs at a high index. -/
def IsAllowed {p m : ℕ} (alpha : ℕ) (s : Finset (Label p m)) : Prop :=
  ∀ j : Fin m, (fiber s j).card ≤ capacity p alpha j

/-- Allowed faces are closed downward. -/
theorem IsAllowed.mono {p m alpha : ℕ} {s t : Finset (Label p m)}
    (hs : IsAllowed alpha s) (hts : t ⊆ s) : IsAllowed alpha t := by
  intro j
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hts)).trans (hs j)

@[simp] theorem isAllowed_empty (p m alpha : ℕ) :
    IsAllowed (p := p) (m := m) alpha ∅ := by
  intro j
  simp [fiber]

/-- The set of allowed exterior-basis indices. -/
def allowedFaceSet (p m alpha : ℕ) : Set (Finset (Label p m)) :=
  {s | IsAllowed alpha s}

/-- The span of allowed basis faces in the full exterior-chain coordinate
module `Finset (Label p m) →₀ R`. -/
def allowedChains (R : Type*) [CommRing R] (p m alpha : ℕ) :
    Submodule R (TargetChains.FullChain R (Label p m)) :=
  Finsupp.supported R R (allowedFaceSet p m alpha)

theorem mem_allowedChains {R : Type*} [CommRing R] {p m alpha : ℕ}
    (c : TargetChains.FullChain R (Label p m)) :
    c ∈ allowedChains R p m alpha ↔
      ∀ s ∈ c.support, IsAllowed alpha s := by
  rw [allowedChains, Finsupp.mem_supported]
  rfl

/-- The allowed submodule is exactly the span of its standard basis faces. -/
theorem allowedChains_eq_span {R : Type*} [CommRing R] (p m alpha : ℕ) :
    allowedChains R p m alpha =
      Submodule.span R
        ((fun s : Finset (Label p m) ↦ Finsupp.single s (1 : R)) ''
          allowedFaceSet p m alpha) := by
  exact Finsupp.supported_eq_span_single R (allowedFaceSet p m alpha)

end AllowedFaces

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/LabelAllowed.lean` -/

section
namespace LabelAllowed

open ZpTuckerScratch
open SignedSphere
open AllowedFaces

noncomputable section

variable {p n m alpha : ℕ}

abbrev Vertex := NonzeroSignedVector p n
abbrev Label := ZMod p × Fin m

end

end LabelAllowed

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/FinsetOrientation.lean` -/

section
open Finset

open Function

section ImageOrientation

variable {V W U R : Type*}

/-- Compare an equivalence of two `n`-element finsets with their increasing enumerations. -/
private noncomputable def _root_.Finset.orientationPerm [LinearOrder V] [LinearOrder W] {n : ℕ}
    (s : Finset V) (t : Finset W) (hs : s.card = n) (ht : t.card = n)
    (e : s ≃ t) : Equiv.Perm (Fin n) :=
  (s.orderIsoOfFin hs).toEquiv |>.trans e |>.trans (t.orderIsoOfFin ht).symm.toEquiv

/-- An injective map on a finset is an equivalence with its finset image. -/
private noncomputable def _root_.Finset.imageEquiv [DecidableEq W] (s : Finset V) (f : V → W)
    (hf : Set.InjOn f s) : s ≃ s.image f :=
  Equiv.ofBijective
    (fun x : s ↦ ⟨f x, mem_image_of_mem f x.2⟩)
    ⟨fun x y h ↦ Subtype.ext (hf x.2 y.2 (Subtype.ext_iff.mp h)),
      fun y ↦ by
        rcases mem_image.mp y.2 with ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp] theorem coe_imageEquiv_apply [DecidableEq W] (s : Finset V) (f : V → W)
    (hf : Set.InjOn f s) (x : s) :
    ((imageEquiv s f hf x : s.image f) : W) = f x := rfl

/-- The permutation comparing the increasing enumeration of `s`, transported by `f`,
with the increasing enumeration of `s.image f`. -/
private noncomputable def _root_.Finset.imagePerm [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) : Equiv.Perm (Fin s.card) :=
  orientationPerm s (s.image f) rfl (card_image_of_injOn hf) (imageEquiv s f hf)

@[simp] theorem imagePerm_apply [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) (i : Fin s.card) :
    imagePerm s f hf i =
      ((s.image f).orderIsoOfFin (card_image_of_injOn hf)).symm
        ⟨f (s.orderIsoOfFin rfl i), mem_image_of_mem f (s.orderIsoOfFin rfl i).2⟩ :=
  rfl

/-- Canonical orientation sign of an injective finite image. -/
private noncomputable def _root_.Finset.imageSign [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) : ℤˣ :=
  Equiv.Perm.sign (imagePerm s f hf)

/-- The normalized coefficient for the image of an ordered finite set: it is its canonical
orientation sign if `f` is injective on `s`, and zero otherwise. -/
private noncomputable def _root_.Finset.imageCoeff [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) : R :=
  if hf : Set.InjOn f s then (((imageSign s f hf : ℤˣ) : ℤ) : R) else 0

@[simp] theorem imageCoeff_of_injOn [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) :
    imageCoeff (R := R) s f = (((imageSign s f hf : ℤˣ) : ℤ) : R) := by
  simp [imageCoeff, hf]

@[simp] theorem imageCoeff_of_not_injOn [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) (hf : ¬ Set.InjOn f s) :
    imageCoeff (R := R) s f = 0 := by
  simp [imageCoeff, hf]

end ImageOrientation

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/SignedMap.lean` -/

section
open Function

namespace TargetChains

universe u v

variable {V : Type u} [Fintype V] [LinearOrder V]
variable {W : Type v} [Fintype W] [LinearOrder W]

theorem map_single_of_injOn (f : V → W) (s : Finset V)
    (hf : Set.InjOn f s) :
    map (R := ℤ) f (Finsupp.single s 1) =
      Finsupp.single (s.image f)
        ((Finset.imageSign s f hf : ℤˣ) : ℤ) := by
  apply (toExterior ℤ W).injective
  rw [toExterior_map_single, toExterior_single]
  change ExteriorAlgebra.map (vertexMap f)
      ((vertexBasis ℤ V).ExteriorAlgebra s) =
    ((Finset.imageSign s f hf : ℤˣ) : ℤ) •
      (vertexBasis ℤ W).ExteriorAlgebra (s.image f)
  rw [ExteriorAlgebra.basis_apply (vertexBasis ℤ V) s,
    ExteriorAlgebra.basis_apply_ofCard (vertexBasis ℤ W)
      (Finset.card_image_of_injOn hf),
    ExteriorAlgebra.map_apply_ιMulti]
  simp only [Set.powersetCard.prodEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_family, Finset.imageSign]
  let v : Fin s.card → (W →₀ ℤ) :=
    (vertexBasis ℤ W) ∘
      Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard (Finset.card_image_of_injOn hf))
  let σ : Equiv.Perm (Fin s.card) := Finset.imagePerm s f hf
  have hfamily :
      (vertexMap f) ∘ (vertexBasis ℤ V) ∘
          Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofCard rfl) =
        v ∘ σ := by
    funext i
    simp only [Function.comp_apply, vertexBasis, v, σ,
      Finsupp.coe_basisSingleOne, vertexMap_single]
    congr 1
    exact congrArg Subtype.val
      ((s.image f).orderIsoOfFin (Finset.card_image_of_injOn hf) |>.apply_symm_apply
        ⟨f (s.orderIsoOfFin rfl i), Finset.mem_image_of_mem f
          (s.orderIsoOfFin rfl i).2⟩) |>.symm
  rw [hfamily]
  exact AlternatingMap.map_perm (ExteriorAlgebra.ιMulti ℤ s.card) v σ

end TargetChains

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/LabelChainMap.lean` -/

section
/-!
The normalized simplicial chain map induced by a `Z_p`-Tucker labeling.

Source simplices are strict flags, represented by lists in their flag order.
The target is the exterior-algebra chain model: repeated labels therefore
normalize to zero, while a permutation of labels contributes its usual sign.
-/

namespace LabelChainMap

open scoped BigOperators

open ZpTuckerScratch

noncomputable section

abbrev SourceVertex (p n : ℕ) := NonzeroSignedVector p n
abbrev TargetVertex (p m : ℕ) := ZMod p × Fin m
abbrev TargetChain (p m : ℕ) := TargetChains.FullChain ℤ (TargetVertex p m)
abbrev TargetExterior (p m : ℕ) :=
  ExteriorAlgebra ℤ (TargetVertex p m →₀ ℤ)

variable {p n m alpha : ℕ} [NeZero p]

noncomputable local instance targetMax : Max (TargetVertex p m) where
  max x y :=
    let e := Fintype.equivFin (TargetVertex p m)
    e.symm (max (e x) (e y))

noncomputable local instance targetMin : Min (TargetVertex p m) where
  min x y :=
    let e := Fintype.equivFin (TargetVertex p m)
    e.symm (min (e x) (e y))

noncomputable local instance targetLinearOrder :
    LinearOrder (TargetVertex p m) :=
  let e := Fintype.equivFin (TargetVertex p m)
  LinearOrder.lift e e.injective
    (by
      intro x y
      change e (e.symm (max (e x) (e y))) = _
      exact e.apply_symm_apply _)
    (by
      intro x y
      change e (e.symm (min (e x) (e y))) = _
      exact e.apply_symm_apply _)

/-- Exterior product of the labeled vertices, in source-flag order. -/
def exteriorFlag
    {ι : Type*} (lab : ι → TargetVertex p m) :
    List ι → TargetExterior p m
  | [] => 1
  | x :: xs =>
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) * exteriorFlag lab xs

@[simp] theorem exteriorFlag_nil
    (lab : SourceVertex p n → TargetVertex p m) :
    exteriorFlag lab [] = 1 := rfl

@[simp] theorem exteriorFlag_cons
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) (xs : List (SourceVertex p n)) :
    exteriorFlag lab (x :: xs) =
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) * exteriorFlag lab xs := rfl

/-- A source flag list, normalized in the target exterior basis. -/
def normalizedBasis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) : TargetChain p m :=
  (TargetChains.toExterior ℤ (TargetVertex p m)).symm (exteriorFlag lab l)

/-- The exterior-normalized linear map induced by `lab`. -/
def normalizedMap
    (lab : SourceVertex p n → TargetVertex p m) :
    SourceFlags.Chain (SourceVertex p n) →ₗ[ℤ] TargetChain p m :=
  Finsupp.lift (TargetChain p m) ℤ (List (SourceVertex p n))
    (normalizedBasis lab)

@[simp] theorem normalizedMap_basis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) :
    normalizedMap lab (SourceFlags.basis l) = normalizedBasis lab l := by
  simp [normalizedMap, SourceFlags.basis]

@[simp] theorem toExterior_normalizedBasis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) :
    TargetChains.toExterior ℤ (TargetVertex p m) (normalizedBasis lab l) =
      exteriorFlag lab l := by
  simp [normalizedBasis]

/-- Left exterior multiplication by a target vertex. -/
def leftWedge (v : TargetVertex p m) : TargetChain p m →ₗ[ℤ] TargetChain p m :=
  (TargetChains.toExterior ℤ (TargetVertex p m)).symm.toLinearMap.comp
    ((LinearMap.mulLeft ℤ
      (ExteriorAlgebra.ι ℤ (Finsupp.single v 1))).comp
      (TargetChains.toExterior ℤ (TargetVertex p m)).toLinearMap)

@[simp] theorem toExterior_leftWedge
    (v : TargetVertex p m) (c : TargetChain p m) :
    TargetChains.toExterior ℤ (TargetVertex p m) (leftWedge v c) =
      ExteriorAlgebra.ι ℤ (Finsupp.single v 1) *
        TargetChains.toExterior ℤ (TargetVertex p m) c := by
  simp [leftWedge]

/-- The target cyclic shift on vertices. -/
def targetShift (a : ZMod p) (v : TargetVertex p m) : TargetVertex p m :=
  (a + v.1, v.2)

/-- The normalized action of a target vertex map on target chains. -/
def targetAct (a : ZMod p) : TargetChain p m →ₗ[ℤ] TargetChain p m :=
  TargetChains.map (targetShift a)

/-! ## The alpha-split target subcomplex -/

end

end LabelChainMap

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/PositiveAllowed.lean` -/

section
/-!
Allowed positive target chains and the reduced labeling map.
-/

namespace PositiveAllowed

open TargetChains PositiveTarget AllowedFaces LabelAllowed SignedSphere
open ZpTuckerScratch

noncomputable section

variable {p n m alpha k : ℕ} [NeZero p]

abbrev SourceVertex := NonzeroSignedVector p n
abbrev TargetVertex := AllowedFaces.Label p m

noncomputable local instance targetOrder :
    LinearOrder (TargetVertex (p := p) (m := m)) :=
  LabelChainMap.targetLinearOrder

def listAt {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X)
    (i : Fin l.length) : TargetVertex (p := p) (m := m) :=
  lab (l.get i)

def listFace {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X) :
    Finset (TargetVertex (p := p) (m := m)) :=
  Finset.univ.image (listAt lab l)

theorem labelList_eq_map_univ_general {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X) :
    TargetBridge.labelList lab l =
      TargetChains.map (listAt lab l)
        (Finsupp.single (Finset.univ : Finset (Fin l.length)) 1) := by
  apply (TargetChains.toExterior ℤ (TargetVertex (p := p) (m := m))).injective
  rw [TargetBridge.labelList_eq_ιMulti,
    TargetChains.toExterior_map_single]
  change ExteriorAlgebra.ιMulti ℤ l.length
      (fun i ↦ Finsupp.single (lab (l.get i)) 1) =
    ExteriorAlgebra.map (TargetChains.vertexMap (listAt lab l))
      ((TargetChains.vertexBasis ℤ (Fin l.length)).ExteriorAlgebra Finset.univ)
  have hcard : (Finset.univ : Finset (Fin l.length)).card = l.length := by simp
  rw [ExteriorAlgebra.basis_apply_ofCard
      (TargetChains.vertexBasis ℤ (Fin l.length)) hcard,
    ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, TargetChains.vertexBasis,
    Finsupp.coe_basisSingleOne, TargetChains.vertexMap_single, listAt]
  congr 1
  apply congrArg lab
  apply congrArg l.get
  apply Fin.ext
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, Fin.sort_univ]

theorem labelList_eq_signed_single_general {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X)
    (hinj : Function.Injective (listAt lab l)) :
    TargetBridge.labelList lab l =
      Finsupp.single (listFace lab l)
        ((Finset.imageSign (Finset.univ : Finset (Fin l.length))
          (listAt lab l) hinj.injOn : ℤˣ) : ℤ) := by
  rw [labelList_eq_map_univ_general]
  let img : Finset (TargetVertex (p := p) (m := m)) :=
    @Finset.image (Fin l.length) (TargetVertex (p := p) (m := m))
      (@LinearOrder.toDecidableEq _ targetOrder)
      (listAt lab l) Finset.univ
  have himg : img = listFace lab l := by
    ext v
    simp [img, listFace]
  rw [← himg]
  exact TargetChains.map_single_of_injOn (listAt lab l)
    (Finset.univ : Finset (Fin l.length)) hinj.injOn

/- The exterior label of a list is the normalized finite-image map from
the canonically ordered `Fin l.length` simplex. -/

/- A repeated target label kills the exterior simplex. -/

/- In the injective case the exterior label is one oriented copy of its
finite label image. -/

/-! ## The positive allowed submodules -/

def allowedPositiveChains (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ
      (PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) :=
  (AllowedFaces.allowedChains ℤ p m alpha).comap
    (TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m)))

abbrev Chain (p m alpha : ℕ) [NeZero p] :=
  allowedPositiveChains p m alpha

/-! ## Boundary closure of the allowed target complex -/

theorem labelList_id_mem_allowed_of_subset
    {s : Finset (TargetVertex (p := p) (m := m))}
    (hs : IsAllowed alpha s)
    (l : List (TargetVertex (p := p) (m := m)))
    (hl : l.toFinset ⊆ s) :
    TargetBridge.labelList id l ∈ AllowedFaces.allowedChains ℤ p m alpha := by
  by_cases hinj : Function.Injective (listAt id l)
  · rw [labelList_eq_signed_single_general id l hinj]
    rw [AllowedFaces.mem_allowedChains]
    intro t ht
    by_cases htf : t = listFace id l
    · subst t
      apply hs.mono
      intro v hv
      have hv' : ∃ i : Fin l.length, l.get i = v := by
        simpa [listFace, listAt] using hv
      have hvl : v ∈ l := by
        have h := (List.exists_mem_iff_get
          (l := l) (p := fun x ↦ x = v)).2 hv'
        simpa using h
      exact hl (by simpa using hvl)
    · exfalso
      apply (Finsupp.mem_support_iff.mp ht)
      simp [htf]
  · rw [TargetBridge.labelList_eq_zero_of_repeated id l hinj]
    exact (AllowedFaces.allowedChains ℤ p m alpha).zero_mem

theorem labelLists_id_mem_allowed_of_supported_subset
    {s : Finset (TargetVertex (p := p) (m := m))}
    (hs : IsAllowed alpha s)
    {c : SourceFlags.Chain (TargetVertex (p := p) (m := m))}
    (hc : SignedSphere.Supported (fun l ↦ l.toFinset ⊆ s) c) :
    TargetBridge.labelLists id c ∈ AllowedFaces.allowedChains ℤ p m alpha := by
  have hc' : c ∈ Finsupp.supported ℤ ℤ {l | l.toFinset ⊆ s} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact hc l (Finsupp.mem_support_iff.mp hl)
  have hle : Finsupp.supported ℤ ℤ {l | l.toFinset ⊆ s} ≤
      (AllowedFaces.allowedChains ℤ p m alpha).comap
        (TargetBridge.labelLists id) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    change TargetBridge.labelLists id (SourceFlags.basis l) ∈
      AllowedFaces.allowedChains ℤ p m alpha
    rw [TargetBridge.labelLists_basis]
    exact labelList_id_mem_allowed_of_subset hs l hl
  exact hle hc'

theorem boundary_single_mem_allowed
    (s : Finset (TargetVertex (p := p) (m := m)))
    (hs : IsAllowed alpha s) :
    TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
        (Finsupp.single s 1) ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  let l : List (TargetVertex (p := p) (m := m)) := s.sort (· ≤ ·)
  have hlfin : l.toFinset = s := by
    exact Finset.sort_toFinset s (· ≤ ·)
  have hlinj : Function.Injective (listAt id l) := by
    have hget :=
      List.nodup_iff_injective_get.mp (Finset.sort_nodup s (· ≤ ·))
    intro i j hij
    apply hget
    simpa [listAt] using hij
  let u : ℤˣ := Finset.imageSign (Finset.univ : Finset (Fin l.length))
    (listAt id l) hlinj.injOn
  have hface : listFace id l = s := by
    unfold listFace
    rw [← hlfin]
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, listAt, id_eq,
      List.mem_toFinset]
    constructor
    · rintro ⟨i, rfl⟩
      exact List.get_mem l i
    · intro hv
      let i : Fin l.length :=
        ⟨l.idxOf v, List.idxOf_lt_length_iff.mpr hv⟩
      refine ⟨i, ?_⟩
      simpa only [List.get_eq_getElem, i] using
        (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv))
  have hlabel : TargetBridge.labelList id l =
      (u : ℤ) • Finsupp.single s (1 : ℤ) := by
    rw [labelList_eq_signed_single_general id l hlinj, hface]
    simp [u]
  have hsupport : SignedSphere.Supported (fun q ↦ q.toFinset ⊆ s)
      (SourceFlags.boundaryBasis l) := by
    refine SignedSphere.Supported.mono
      (SignedSphere.boundaryBasis_supported_terms l) ?_
    intro q hq
    rw [← hlfin]
    intro v hv
    simp only [List.mem_toFinset] at hv ⊢
    exact hq.1.subset hv
  have hb : TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
      (TargetBridge.labelList id l) ∈
        AllowedFaces.allowedChains ℤ p m alpha := by
    rw [TargetBridge.boundary_labelList]
    exact labelLists_id_mem_allowed_of_supported_subset hs hsupport
  rw [hlabel, map_smul] at hb
  have hbinv := (AllowedFaces.allowedChains ℤ p m alpha).smul_mem
    ((↑(u⁻¹) : ℤ)) hb
  simpa [smul_smul] using hbinv

theorem boundary_mem_allowed
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.boundary ℤ (TargetVertex (p := p) (m := m)) c ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.allowedChains_eq_span] at hc
  let M : Submodule ℤ (TargetChains.FullChain ℤ
      (TargetVertex (p := p) (m := m))) :=
    (AllowedFaces.allowedChains ℤ p m alpha).comap
      (TargetChains.boundary ℤ (TargetVertex (p := p) (m := m)))
  have hle : Submodule.span ℤ
      ((fun s : Finset (TargetVertex (p := p) (m := m)) ↦
          Finsupp.single s (1 : ℤ)) '' AllowedFaces.allowedFaceSet p m alpha) ≤ M := by
    apply Submodule.span_le.2
    rintro _ ⟨s, hs, rfl⟩
    exact boundary_single_mem_allowed s hs
  exact hle hc

theorem projectPositive_mem_allowed
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m)) c) ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [TargetChains.positiveInclusion_projectPositive]
  apply (AllowedFaces.allowedChains ℤ p m alpha).sub_mem hc
  rw [AllowedFaces.mem_allowedChains]
  intro s hs
  by_cases hsempty : s = ∅
  · subst s
    exact AllowedFaces.isAllowed_empty p m alpha
  · exfalso
    apply (Finsupp.mem_support_iff.mp hs)
    simp [hsempty]

theorem reducedBoundary_mem_allowed
    {c : PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ allowedPositiveChains p m alpha) :
    PositiveTarget.boundary ℤ (TargetVertex (p := p) (m := m)) c ∈
      allowedPositiveChains p m alpha := by
  change TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
      (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
          (TargetChains.positiveInclusion ℤ
            (TargetVertex (p := p) (m := m)) c))) ∈
    AllowedFaces.allowedChains ℤ p m alpha
  apply projectPositive_mem_allowed
  apply boundary_mem_allowed
  exact hc

noncomputable def boundary (p m alpha : ℕ) [NeZero p] :
    Chain p m alpha →ₗ[ℤ] Chain p m alpha where
  toFun c := ⟨PositiveTarget.boundary ℤ
    (TargetVertex (p := p) (m := m)) c.1,
    reducedBoundary_mem_allowed c.2⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' z c := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem boundary_coe (c : Chain p m alpha) :
    ((boundary p m alpha c : Chain p m alpha) :
      PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) =
      PositiveTarget.boundary ℤ (TargetVertex (p := p) (m := m)) c :=
  rfl

theorem boundary_boundary (c : Chain p m alpha) :
    boundary p m alpha (boundary p m alpha c) = 0 := by
  apply Subtype.ext
  exact PositiveTarget.boundary_boundary ℤ
    (TargetVertex (p := p) (m := m)) c

/-! ## The target cyclic action on the restricted complex -/

def targetShift (a : ZMod p) (v : TargetVertex (p := p) (m := m)) :
    TargetVertex (p := p) (m := m) :=
  (a + v.1, v.2)

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · exact add_left_cancel (congrArg Prod.fst h)
  · simpa [targetShift] using congrArg Prod.snd h

theorem fiber_image_targetShift (a : ZMod p)
    (s : Finset (TargetVertex (p := p) (m := m))) (j : Fin m) :
    AllowedFaces.fiber (s.image (targetShift a)) j =
      (AllowedFaces.fiber s j).image (targetShift a) := by
  ext v
  simp only [AllowedFaces.fiber, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hwv⟩, hvj⟩
    refine ⟨w, ⟨hw, ?_⟩, hwv⟩
    simpa [← hwv, targetShift] using hvj
  · rintro ⟨w, ⟨hw, hwj⟩, hwv⟩
    refine ⟨⟨w, hw, hwv⟩, ?_⟩
    simpa [← hwv, targetShift] using hwj

theorem IsAllowed.image_targetShift (hs : IsAllowed alpha s) (a : ZMod p) :
    IsAllowed alpha (s.image (targetShift (m := m) a)) := by
  intro j
  rw [fiber_image_targetShift,
    Finset.card_image_of_injective _ (targetShift_injective a)]
  exact hs j

theorem targetMap_mem_allowed (a : ZMod p)
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.map (targetShift (m := m) a) c ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.allowedChains_eq_span] at hc
  let M : Submodule ℤ (TargetChains.FullChain ℤ
      (TargetVertex (p := p) (m := m))) :=
    (AllowedFaces.allowedChains ℤ p m alpha).comap
      (TargetChains.map (targetShift (m := m) a))
  have hle : Submodule.span ℤ
      ((fun s : Finset (TargetVertex (p := p) (m := m)) ↦
          Finsupp.single s (1 : ℤ)) '' AllowedFaces.allowedFaceSet p m alpha) ≤ M := by
    apply Submodule.span_le.2
    rintro _ ⟨s, hs, rfl⟩
    change TargetChains.map (targetShift (m := m) a)
      (Finsupp.single s (1 : ℤ)) ∈
        AllowedFaces.allowedChains ℤ p m alpha
    rw [TargetChains.map_single_of_injOn (targetShift a) s
      (targetShift_injective a).injOn]
    rw [AllowedFaces.mem_allowedChains]
    intro t ht
    by_cases hteq : t =
        @Finset.image _ _ (@LinearOrder.toDecidableEq _ targetOrder)
          (targetShift a) s
    · subst t
      change IsAllowed alpha s at hs
      have himg :
          @Finset.image _ _ (@LinearOrder.toDecidableEq _ targetOrder)
              (targetShift a) s =
            s.image (targetShift a) := by
        ext v
        simp
      rw [himg]
      exact PositiveAllowed.IsAllowed.image_targetShift hs a
    · exfalso
      apply (Finsupp.mem_support_iff.mp ht)
      rw [Finsupp.single_apply]
      split
      · rename_i h
        exact (hteq h.symm).elim
      · rfl
  exact hle hc

theorem reducedTargetMap_mem_allowed (a : ZMod p)
    {c : PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ allowedPositiveChains p m alpha) :
    PositiveTarget.map (targetShift (m := m) a) c ∈
      allowedPositiveChains p m alpha := by
  change TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
      (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.map (targetShift (m := m) a)
          (TargetChains.positiveInclusion ℤ
            (TargetVertex (p := p) (m := m)) c))) ∈
    AllowedFaces.allowedChains ℤ p m alpha
  apply projectPositive_mem_allowed
  apply targetMap_mem_allowed
  exact hc

noncomputable def targetAct (a : ZMod p) :
    Chain p m alpha →ₗ[ℤ] Chain p m alpha where
  toFun c := ⟨PositiveTarget.map (targetShift (m := m) a) c.1,
    reducedTargetMap_mem_allowed a c.2⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' z c := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem targetAct_coe (a : ZMod p) (c : Chain p m alpha) :
    ((targetAct (alpha := alpha) a c : Chain p m alpha) :
      PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) =
      PositiveTarget.map (targetShift (m := m) a) c :=
  rfl

end

end PositiveAllowed

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/CyclicAlgebra.lean` -/

section
open scoped BigOperators

namespace CyclicAlgebra

abbrev FreeCyclic (p : ℕ) (ι : Type*) := ι → ZMod p → ℤ

variable {p : ℕ} {ι κ : Type*}

def g [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι where
  toFun x i a := x i (a + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

def D [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι := g - AddMonoidHom.id _

def N [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι where
  toFun x i _ := ∑ a : ZMod p, x i a
  map_zero' := by ext i a; simp
  map_add' _ _ := by ext i a; simp [Finset.sum_add_distrib]

def op [NeZero p] (degree : ℕ) : FreeCyclic p ι →+ FreeCyclic p ι :=
  if Odd degree then D else N

def augmentation [NeZero p] [Fintype ι] : FreeCyclic p ι →+ ℤ where
  toFun x := ∑ i, ∑ a : ZMod p, x i a
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

@[simp] theorem g_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    g x i a = x i (a + 1) := rfl

@[simp] theorem D_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    D x i a = x i (a + 1) - x i a := rfl

@[simp] theorem N_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    N x i a = ∑ b : ZMod p, x i b := rfl

@[simp] theorem augmentation_N [NeZero p] [Fintype ι] (x : FreeCyclic p ι) :
    augmentation (N x) = (p : ℤ) * augmentation x := by
  simp only [augmentation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, N_apply]
  simp [ZMod.card, ← Finset.mul_sum]

theorem D_eq_zero_iff [NeZero p] (x : FreeCyclic p ι) :
    D x = 0 ↔ ∀ i a, x i (a + 1) = x i a := by
  constructor
  · intro h i a
    have ha := congrFun (congrFun h i) a
    exact sub_eq_zero.mp (by simpa [D_apply] using ha)
  · intro h
    funext i a
    simp [D_apply, h]

theorem constant_of_D_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : D x = 0) :
    ∀ i a, x i a = x i 0 := by
  intro i a
  have hstep : ∀ z : ZMod p, x i (z + 1) = x i z := (D_eq_zero_iff x).mp hx i
  have hnat : ∀ n : ℕ, x i (n : ZMod p) = x i 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (hstep (n : ZMod p)).trans ih
  rw [← ZMod.natCast_zmod_val a]
  exact hnat a.val

theorem exists_N_of_D_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : D x = 0) :
    ∃ y, N y = x := by
  let y : FreeCyclic p ι := fun i a => if a = 0 then x i 0 else 0
  refine ⟨y, ?_⟩
  funext i a
  rw [N_apply, constant_of_D_eq_zero hx i a]
  simp [y]

/-- On every free cyclic orbit, a vector whose coordinate sum is zero is a cyclic
difference.  This is the second exactness direction of the two-periodic resolution. -/
theorem exists_D_of_N_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : N x = 0) :
    ∃ y, D y = x := by
  by_cases hp1 : p = 1
  · let _ : Unique (ZMod p) := hp1 ▸ inferInstance
    have hNx : N x = x := by
      funext i a
      rw [N_apply]
      calc
        (∑ b : ZMod p, x i b) = ∑ _b : ZMod p, x i a := by
          apply Finset.sum_congr rfl
          intro b _
          exact congrArg (x i) (Subsingleton.elim b a)
        _ = x i a := by simp
    have hx0 : x = 0 := by simpa [hNx] using hx
    exact ⟨0, by simp [hx0]⟩
  · have hp : 1 < p := (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne p, hp1⟩
    let _ : Fact (1 < p) := ⟨hp⟩
    let y : FreeCyclic p ι := fun i a => ∑ k ∈ Finset.range a.val, x i (k : ZMod p)
    refine ⟨y, ?_⟩
    funext i a
    rw [D_apply]
    change (∑ k ∈ Finset.range (a + 1).val, x i (k : ZMod p)) -
      (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) = x i a
    have hsum_univ : (∑ b : ZMod p, x i b) = 0 := by
      have h := congrFun (congrFun hx i) 0
      simpa [N_apply] using h
    have hsum_range : (∑ k ∈ Finset.range p, x i (k : ZMod p)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have hconvert :
          (∑ k : Fin p, x i (k.val : ZMod p)) = ∑ b : ZMod p, x i b := by
        apply Fintype.sum_equiv (ZMod.finEquiv p)
        intro k
        congr 2
        have hv : (ZMod.finEquiv p k).val = k.val := by
          cases p with
          | zero => exact (NeZero.ne 0 rfl).elim
          | succ p => rfl
        exact (congrArg (fun n : ℕ => (n : ZMod p)) hv.symm).trans
          (ZMod.natCast_zmod_val (ZMod.finEquiv p k))
      exact hconvert.trans hsum_univ
    by_cases ha : a.val + 1 < p
    · have hval : (a + 1).val = a.val + 1 := by
        have hlt : a.val + (1 : ZMod p).val < p := by
          simpa [ZMod.val_one p] using ha
        simpa [ZMod.val_one p] using ZMod.val_add_of_lt hlt
      rw [hval, Finset.sum_range_succ, ZMod.natCast_zmod_val, add_sub_cancel_left]
    · have hap : a.val + 1 = p := by
        have hva := a.val_lt
        omega
      have hval : (a + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one p, hap, Nat.mod_self]
      have hsum_last :
          (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) + x i a = 0 := by
        rw [← ZMod.natCast_zmod_val a]
        simpa [← hap, Finset.sum_range_succ] using hsum_range
      rw [hval]
      simp only [Finset.sum_range_zero, zero_sub]
      omega

end CyclicAlgebra

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/TargetOrbits.lean` -/

section
open scoped BigOperators

namespace TargetOrbits

abbrev Label (p m : ℕ) := ZMod p × Fin m

def labelShift {p m : ℕ} (a : ZMod p) : Label p m ≃ Label p m :=
  Equiv.prodCongr (Equiv.addLeft a) (Equiv.refl (Fin m))

@[simp] theorem labelShift_apply {p m : ℕ} (a : ZMod p) (v : Label p m) :
    labelShift a v = (a + v.1, v.2) := rfl

def shiftFinset {p m : ℕ} (a : ZMod p) (s : Finset (Label p m)) :
    Finset (Label p m) := s.map (labelShift a).toEmbedding

@[simp] theorem mem_shiftFinset {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} {v : Label p m} :
    v ∈ shiftFinset a s ↔ (-a + v.1, v.2) ∈ s := by
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    change (a + w.1, w.2) = v at heq
    have h1 : v.1 = a + w.1 := congrArg Prod.fst heq.symm
    have h2 : v.2 = w.2 :=
      (congrArg (fun z : Label p m ↦ z.2) heq).symm
    simpa [h1, h2] using hw
  · intro hv
    refine Finset.mem_map.mpr ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp <;> abel

@[simp] theorem shiftFinset_zero {p m : ℕ} (s : Finset (Label p m)) :
    shiftFinset 0 s = s := by ext v; simp

@[simp] theorem shiftFinset_add {p m : ℕ} (a b : ZMod p)
    (s : Finset (Label p m)) :
    shiftFinset a (shiftFinset b s) = shiftFinset (a + b) s := by
  ext v
  simp [neg_add_rev, add_assoc]

def fiber {p m : ℕ} (s : Finset (Label p m)) (j : Fin m) :
    Finset (Label p m) := s.filter fun v ↦ v.2 = j

def Allowed {p m : ℕ} (alpha : ℕ) (s : Finset (Label p m)) : Prop :=
  ∀ j : Fin m, (fiber s j).card ≤ if j.val < alpha then 1 else p - 1

@[simp] theorem fiber_shiftFinset {p m : ℕ} (a : ZMod p)
    (s : Finset (Label p m)) (j : Fin m) :
    fiber (shiftFinset a s) j = shiftFinset a (fiber s j) := by
  ext v
  simp [fiber]

theorem card_shiftFinset {p m : ℕ} (a : ZMod p) (s : Finset (Label p m)) :
    (shiftFinset a s).card = s.card := by simp [shiftFinset]

@[simp] theorem allowed_shiftFinset_iff {p m alpha : ℕ} (a : ZMod p)
    (s : Finset (Label p m)) :
    Allowed alpha (shiftFinset a s) ↔ Allowed alpha s := by
  constructor <;> intro h j
  · have hj := h j
    rw [fiber_shiftFinset, card_shiftFinset] at hj
    exact hj
  · simpa only [fiber_shiftFinset, card_shiftFinset] using h j

theorem mem_shiftFinset_of_mem {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) : (a + v.1, v.2) ∈ s := by
  rw [← hfix]
  exact Finset.mem_map.mpr ⟨v, hv, rfl⟩

theorem orbit_mem_of_fixed {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) :
    ∀ n : ℕ, ((n : ZMod p) * a + v.1, v.2) ∈ s := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      have hs := mem_shiftFinset_of_mem hfix ih
      convert hs using 1 <;> simp [Nat.cast_succ] <;> ring

def signFiberEmbedding {p m : ℕ} (j : Fin m) : ZMod p ↪ Label p m where
  toFun b := (b, j)
  inj' := fun _ _ h ↦ congrArg Prod.fst h

theorem full_fiber_of_fixed {p m : ℕ} [NeZero p] (hp : p.Prime) {a : ZMod p}
    (ha : a ≠ 0) {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) :
    Finset.univ.map (signFiberEmbedding v.2) ⊆ fiber s v.2 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro w hw
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hw
  obtain ⟨b, rfl⟩ := hw
  simp only [fiber, Finset.mem_filter, and_true]
  let z : ZMod p := (b - v.1) * a⁻¹
  have hz := orbit_mem_of_fixed hfix hv z.val
  have hza : (z.val : ZMod p) * a + v.1 = b := by
    rw [ZMod.natCast_zmod_val]
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
    abel
  change (b, v.2) ∈ s ∧ v.2 = v.2
  exact ⟨by simpa only [hza] using hz, rfl⟩

theorem shiftFinset_ne_of_nonzero {p m alpha : ℕ} (hp : p.Prime)
    {a : ZMod p} (ha : a ≠ 0) {s : Finset (Label p m)}
    (hsne : s.Nonempty) (hallowed : Allowed alpha s) :
    shiftFinset a s ≠ s := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro hfix
  obtain ⟨v, hv⟩ := hsne
  have hsub := full_fiber_of_fixed hp ha hfix hv
  have hlower := Finset.card_le_card hsub
  have hcardMap :
      (Finset.univ.map (signFiberEmbedding (p := p) (m := m) v.2)).card = p := by
    simp [ZMod.card]
  rw [hcardMap] at hlower
  have hupper := hallowed v.2
  have hp2 := hp.two_le
  split at hupper
  · omega
  · omega

def AllowedFace (p m alpha q : ℕ) :=
  {s : Finset (Label p m) // s.card = q + 1 ∧ Allowed alpha s}

noncomputable instance (p m alpha q : ℕ) [NeZero p] : Fintype (AllowedFace p m alpha q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def shiftFace {p m alpha q : ℕ} (a : ZMod p)
    (s : AllowedFace p m alpha q) : AllowedFace p m alpha q :=
  ⟨shiftFinset a s.1,
    by rw [card_shiftFinset, s.2.1]; exact ⟨rfl, (allowed_shiftFinset_iff a s.1).2 s.2.2⟩⟩

@[simp] theorem shiftFace_zero {p m alpha q : ℕ} (s : AllowedFace p m alpha q) :
    shiftFace 0 s = s := by apply Subtype.ext; simp [shiftFace]

@[simp] theorem shiftFace_add {p m alpha q : ℕ} (a b : ZMod p)
    (s : AllowedFace p m alpha q) :
    shiftFace a (shiftFace b s) = shiftFace (a + b) s := by
  apply Subtype.ext
  simp [shiftFace]

theorem allowedFace_nonempty {p m alpha q : ℕ} (s : AllowedFace p m alpha q) :
    s.1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hc := s.2.1
  rw [h] at hc
  simp at hc

theorem shiftFace_eq_self_iff {p m alpha q : ℕ} (hp : p.Prime)
    (a : ZMod p) (s : AllowedFace p m alpha q) :
    shiftFace a s = s ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    apply shiftFinset_ne_of_nonzero hp ha (allowedFace_nonempty s) s.2.2
    exact congrArg Subtype.val h
  · rintro rfl
    simp

def OrbitRel {p m alpha q : ℕ}
    (x y : AllowedFace p m alpha q) : Prop :=
  ∃ a : ZMod p, shiftFace a x = y

theorem orbitRel_refl {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    OrbitRel x x := ⟨0, by simp⟩

theorem orbitRel_symm {p m alpha q : ℕ} {x y : AllowedFace p m alpha q} :
    OrbitRel x y → OrbitRel y x := by
  rintro ⟨a, rfl⟩
  refine ⟨-a, ?_⟩
  simpa only [shiftFace_add, neg_add_cancel, shiftFace_zero]

theorem orbitRel_trans {p m alpha q : ℕ} {x y z : AllowedFace p m alpha q} :
    OrbitRel x y → OrbitRel y z → OrbitRel x z := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨b + a, by simp [add_comm]⟩

def orbitSetoid (p m alpha q : ℕ) : Setoid (AllowedFace p m alpha q) where
  r := OrbitRel
  iseqv := ⟨orbitRel_refl, orbitRel_symm, orbitRel_trans⟩

abbrev FaceOrbit (p m alpha q : ℕ) := Quotient (orbitSetoid p m alpha q)

noncomputable instance (p m alpha q : ℕ) [NeZero p] :
    Fintype (FaceOrbit p m alpha q) := Fintype.ofFinite _

def orbitMk {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    FaceOrbit p m alpha q := Quotient.mk (orbitSetoid p m alpha q) x

noncomputable def orbitRep {p m alpha q : ℕ} (O : FaceOrbit p m alpha q) :
    AllowedFace p m alpha q := Quotient.out O

@[simp] theorem orbitMk_rep {p m alpha q : ℕ} (O : FaceOrbit p m alpha q) :
    orbitMk (orbitRep O) = O := by
  change Quotient.mk (orbitSetoid p m alpha q) (Quotient.out O) = O
  exact Quotient.out_eq O

theorem orbitMk_shiftFace {p m alpha q : ℕ} (a : ZMod p)
    (x : AllowedFace p m alpha q) : orbitMk (shiftFace a x) = orbitMk x := by
  change Quotient.mk (orbitSetoid p m alpha q) (shiftFace a x) =
    Quotient.mk (orbitSetoid p m alpha q) x
  exact Quotient.sound ⟨-a, by simp⟩

theorem exists_orbitCoord {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    ∃ a : ZMod p, shiftFace a (orbitRep (orbitMk x)) = x := by
  have hq : orbitMk (orbitRep (orbitMk x)) = orbitMk x := orbitMk_rep _
  change Quotient.mk (orbitSetoid p m alpha q) (orbitRep (orbitMk x)) =
    Quotient.mk (orbitSetoid p m alpha q) x at hq
  exact Quotient.exact hq

noncomputable def orbitCoord {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    ZMod p := Classical.choose (exists_orbitCoord x)

theorem orbitCoord_spec {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    shiftFace (orbitCoord x) (orbitRep (orbitMk x)) = x :=
  Classical.choose_spec (exists_orbitCoord x)

theorem shiftFace_left_cancel {p m alpha q : ℕ} (hp : p.Prime)
    {a b : ZMod p} {x : AllowedFace p m alpha q}
    (h : shiftFace a x = shiftFace b x) : a = b := by
  have h' := congrArg (shiftFace (-b)) h
  simp only [shiftFace_add] at h'
  have hz : shiftFace (a - b) x = x := by
    simpa only [add_comm (-b) a, sub_eq_add_neg, neg_add_cancel, shiftFace_zero] using h'
  have hz0 := (shiftFace_eq_self_iff hp (a - b) x).1 hz
  exact sub_eq_zero.mp hz0

@[simp] theorem orbitCoord_shiftFace {p m alpha q : ℕ} (hp : p.Prime)
    (b : ZMod p) (x : AllowedFace p m alpha q) :
    orbitCoord (shiftFace b x) = b + orbitCoord x := by
  apply shiftFace_left_cancel hp (x := orbitRep (orbitMk x))
  have hs := orbitCoord_spec (shiftFace b x)
  rw [orbitMk_shiftFace] at hs
  rw [hs]
  calc
    shiftFace b x = shiftFace b
        (shiftFace (orbitCoord x) (orbitRep (orbitMk x))) := by
          rw [orbitCoord_spec]
    _ = shiftFace (b + orbitCoord x) (orbitRep (orbitMk x)) :=
      shiftFace_add _ _ _

theorem orbitCoord_rep {p m alpha q : ℕ} (hp : p.Prime)
    (O : FaceOrbit p m alpha q) : orbitCoord (orbitRep O) = 0 := by
  apply shiftFace_left_cancel hp (x := orbitRep O)
  have hs := orbitCoord_spec (orbitRep O)
  rw [orbitMk_rep] at hs
  simpa using hs

noncomputable def faceOrbitEquiv {p m alpha q : ℕ} (hp : p.Prime) :
    FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q where
  toFun z := shiftFace z.2 (orbitRep z.1)
  invFun x := (orbitMk x, orbitCoord x)
  left_inv z := by
    change (orbitMk (shiftFace z.2 (orbitRep z.1)),
      orbitCoord (shiftFace z.2 (orbitRep z.1))) = z
    apply Prod.ext
    · rw [orbitMk_shiftFace, orbitMk_rep]
    · rw [orbitCoord_shiftFace hp, orbitCoord_rep hp, add_zero]
  right_inv x := orbitCoord_spec x

abbrev FaceChain (p m alpha q : ℕ) := AllowedFace p m alpha q →₀ ℤ

noncomputable def chainCoords {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q ≃ₗ[ℤ] CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    { toFun := fun c O a ↦ c (faceOrbitEquiv hp (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
          (fun s ↦ x (orbitMk s) (orbitCoord s))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        change c (faceOrbitEquiv hp (orbitMk s, orbitCoord s)) = c s
        exact congrArg c ((faceOrbitEquiv hp).apply_symm_apply s)
      right_inv := by
        intro x
        funext O a
        change x (orbitMk (faceOrbitEquiv hp (O, a)))
            (orbitCoord (faceOrbitEquiv hp (O, a))) = x O a
        exact congrArg (fun z ↦ x z.1 z.2)
          ((faceOrbitEquiv hp).symm_apply_apply (O, a)) }

@[simp] theorem chainCoords_apply {p m alpha q : ℕ} (hp : p.Prime)
    (c : FaceChain p m alpha q) (O : FaceOrbit p m alpha q) (a : ZMod p) :
    chainCoords hp c O a = c (shiftFace a (orbitRep O)) := rfl

/-- The generator in the orbitwise reoriented basis.  Thus translation has
coefficient `+1` along every chosen oriented orbit. -/
noncomputable def reorientedShift {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (chainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.g.comp (chainCoords hp).toAddEquiv.toAddMonoidHom)

/-- `tau = g - 1` in the reoriented orbit basis. -/
noncomputable def tau {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  reorientedShift hp - AddMonoidHom.id _

/-- The orbit norm `1 + g + ⋯ + g^(p-1)` in the reoriented orbit basis. -/
noncomputable def normOp {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (chainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp (chainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem chainCoords_reorientedShift {p m alpha q : ℕ} [NeZero p]
    (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (reorientedShift hp c) =
      CyclicAlgebra.g (chainCoords hp c) := by
  change chainCoords hp ((chainCoords hp).symm
      (CyclicAlgebra.g (chainCoords hp c))) = _
  rw [(chainCoords hp).apply_symm_apply]

@[simp] theorem chainCoords_tau {p m alpha q : ℕ} [NeZero p] (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (tau hp c) = CyclicAlgebra.D (chainCoords hp c) := by
  rw [show tau hp c = reorientedShift hp c - c by rfl, map_sub,
    chainCoords_reorientedShift]
  rfl

@[simp] theorem chainCoords_normOp {p m alpha q : ℕ} [NeZero p] (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (normOp hp c) = CyclicAlgebra.N (chainCoords hp c) := by
  change chainCoords hp ((chainCoords hp).symm
      (CyclicAlgebra.N (chainCoords hp c))) = _
  rw [(chainCoords hp).apply_symm_apply]

/-! ## One positive allowed module containing every degree

The sigma index excludes the empty face because every `AllowedFace ... q` has
cardinality `q + 1`.  This is the ambient module used by periodic descent: the
boundary can change `q`, while cyclic translation preserves it. -/

abbrev TotalFace (p m alpha : ℕ) := Σ q : ℕ, AllowedFace p m alpha q

abbrev PositiveAllowedFinset (p m alpha : ℕ) :=
  {s : Finset (Label p m) // s.Nonempty ∧ Allowed alpha s}

/-- Forgetting degree identifies the sigma of homogeneous nonempty faces with
all nonempty allowed finsets. -/
noncomputable def totalFaceEquivPositive (p m alpha : ℕ) :
    TotalFace p m alpha ≃ PositiveAllowedFinset p m alpha := by
  let f : TotalFace p m alpha → PositiveAllowedFinset p m alpha :=
    fun z ↦ ⟨z.2.1, allowedFace_nonempty z.2, z.2.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨q, s⟩ ⟨r, t⟩ h
    have hst : s.1 = t.1 := congrArg Subtype.val h
    have hq : q = r := by
      have hs := s.2.1
      have ht := t.2.1
      rw [hst] at hs
      omega
    apply Sigma.ext hq
    cases hq
    exact heq_of_eq (Subtype.ext hst)
  · intro s
    have hs : 0 < s.1.card := Finset.card_pos.mpr s.2.1
    refine ⟨⟨s.1.card - 1, ⟨s.1, by omega, s.2.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable instance (p m alpha : ℕ) [NeZero p] :
    Fintype (PositiveAllowedFinset p m alpha) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance (p m alpha : ℕ) [NeZero p] :
    Fintype (TotalFace p m alpha) :=
  Fintype.ofEquiv (PositiveAllowedFinset p m alpha)
    (totalFaceEquivPositive p m alpha).symm

abbrev TotalOrbit (p m alpha : ℕ) := Σ q : ℕ, FaceOrbit p m alpha q

/-- Orbit/coordinate parametrization simultaneously in every positive degree. -/
noncomputable def totalOrbitEquiv {p m alpha : ℕ} (hp : p.Prime) :
    TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha where
  toFun z := ⟨z.1.1, faceOrbitEquiv hp (z.1.2, z.2)⟩
  invFun s := ⟨⟨s.1, orbitMk s.2⟩, orbitCoord s.2⟩
  left_inv z := by
    rcases z with ⟨⟨q, O⟩, a⟩
    change (⟨⟨q, orbitMk (faceOrbitEquiv hp (O, a))⟩,
      orbitCoord (faceOrbitEquiv hp (O, a))⟩ :
        TotalOrbit p m alpha × ZMod p) = ⟨⟨q, O⟩, a⟩
    have h := (faceOrbitEquiv hp).symm_apply_apply (O, a)
    exact congrArg (fun z : FaceOrbit p m alpha q × ZMod p ↦
      (⟨⟨q, z.1⟩, z.2⟩ : TotalOrbit p m alpha × ZMod p)) h
  right_inv s := by
    rcases s with ⟨q, s⟩
    change (⟨q, faceOrbitEquiv hp (orbitMk s, orbitCoord s)⟩ :
      TotalFace p m alpha) = ⟨q, s⟩
    exact Sigma.ext rfl (heq_of_eq ((faceOrbitEquiv hp).apply_symm_apply s))

abbrev TotalChain (p m alpha : ℕ) := TotalFace p m alpha →₀ ℤ

/-- The total positive allowed chain module is a direct union of free cyclic
orbits, with one chosen transported orientation on each orbit. -/
noncomputable def totalChainCoords {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    { toFun := fun c O a ↦ c (totalOrbitEquiv hp (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
          (fun s ↦ x ⟨s.1, orbitMk s.2⟩ (orbitCoord s.2))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        change c (totalOrbitEquiv hp
          (⟨s.1, orbitMk s.2⟩, orbitCoord s.2)) = c s
        exact congrArg c ((totalOrbitEquiv hp).apply_symm_apply s)
      right_inv := by
        intro x
        funext O a
        change x ⟨(totalOrbitEquiv hp (O, a)).1,
            orbitMk (totalOrbitEquiv hp (O, a)).2⟩
            (orbitCoord (totalOrbitEquiv hp (O, a)).2) = x O a
        exact congrArg (fun z ↦ x z.1 z.2)
          ((totalOrbitEquiv hp).symm_apply_apply (O, a)) }

@[simp] theorem totalChainCoords_apply {p m alpha : ℕ} (hp : p.Prime)
    (c : TotalChain p m alpha) (O : TotalOrbit p m alpha) (a : ZMod p) :
    totalChainCoords hp c O a = c (totalOrbitEquiv hp (O, a)) := rfl

noncomputable def totalTau {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (totalChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.D.comp (totalChainCoords hp).toAddEquiv.toAddMonoidHom)

noncomputable def totalNorm {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (totalChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp (totalChainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem totalChainCoords_tau {p m alpha : ℕ} [NeZero p]
    (hp : p.Prime) (c : TotalChain p m alpha) :
    totalChainCoords hp (totalTau hp c) =
      CyclicAlgebra.D (totalChainCoords hp c) := by
  change totalChainCoords hp ((totalChainCoords hp).symm
    (CyclicAlgebra.D (totalChainCoords hp c))) = _
  rw [(totalChainCoords hp).apply_symm_apply]

@[simp] theorem totalChainCoords_norm {p m alpha : ℕ} [NeZero p]
    (hp : p.Prime) (c : TotalChain p m alpha) :
    totalChainCoords hp (totalNorm hp c) =
      CyclicAlgebra.N (totalChainCoords hp c) := by
  change totalChainCoords hp ((totalChainCoords hp).symm
    (CyclicAlgebra.N (totalChainCoords hp c))) = _
  rw [(totalChainCoords hp).apply_symm_apply]

end TargetOrbits

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/TargetOrientation.lean` -/

section
open scoped BigOperators

namespace TargetOrientation

open TargetChains TargetOrbits LabelChainMap

variable {p m : ℕ} [NeZero p]

noncomputable local instance : LinearOrder (Label p m) :=
  LabelChainMap.targetLinearOrder

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    dsimp [targetShift] at h1
    exact add_left_cancel h1
  · simpa [targetShift] using congrArg Prod.snd h

@[simp] theorem image_targetShift (a : ZMod p) (s : Finset (Label p m)) :
    s.image (targetShift a) = shiftFinset a s := by
  ext v
  simp only [Finset.mem_image, mem_shiftFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [targetShift]
  · intro hv
    refine ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp [targetShift]

noncomputable def targetOrientation (a : ZMod p) (s : Finset (Label p m)) : ℤˣ :=
  Finset.imageSign s (targetShift a) (targetShift_injective a).injOn

theorem targetAct_single_one (a : ZMod p) (s : Finset (Label p m)) :
    targetAct a (Finsupp.single s 1) =
      Finsupp.single (shiftFinset a s) (targetOrientation a s : ℤ) := by
  change TargetChains.map (targetShift a) (Finsupp.single s 1) = _
  have h := TargetChains.map_single_of_injOn (targetShift a) s
    (targetShift_injective a).injOn
  have himage :
      @Finset.image _ _ LabelChainMap.targetLinearOrder.toDecidableEq
        (targetShift a) s = shiftFinset a s := by
    ext v
    simp only [Finset.mem_image, mem_shiftFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [targetShift]
    · intro hv
      refine ⟨(-a + v.1, v.2), hv, ?_⟩
      ext <;> simp [targetShift]
  rw [himage] at h
  exact h

theorem targetAct_add (a b : ZMod p) (c : TargetChain p m) :
    targetAct a (targetAct b c) = targetAct (a + b) c := by
  change TargetChains.map (targetShift a) (TargetChains.map (targetShift b) c) =
    TargetChains.map (targetShift (a + b)) c
  apply (TargetChains.toExterior ℤ (Label p m)).injective
  rw [TargetChains.toExterior_map, TargetChains.toExterior_map,
    TargetChains.toExterior_map]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  congr 2
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) x) =
        TargetChains.vertexMap (targetShift (a + b)) x at hx
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) y) =
        TargetChains.vertexMap (targetShift (a + b)) y at hy
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) (x + y)) =
        TargetChains.vertexMap (targetShift (a + b)) (x + y)
      rw [map_add, map_add, map_add, hx, hy]
  | single v z =>
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) (Finsupp.single v z)) =
        TargetChains.vertexMap (targetShift (a + b)) (Finsupp.single v z)
      rw [TargetChains.vertexMap_single, TargetChains.vertexMap_single,
        TargetChains.vertexMap_single]
      congr 1
      ext <;> simp [targetShift, add_assoc]

theorem targetOrientation_add (a b : ZMod p) (s : Finset (Label p m)) :
    targetOrientation (a + b) s =
      targetOrientation a (shiftFinset b s) * targetOrientation b s := by
  have h := targetAct_add a b (Finsupp.single s 1)
  rw [targetAct_single_one, targetAct_single_one] at h
  have hone :
      Finsupp.single (shiftFinset b s) (targetOrientation b s : ℤ) =
        (targetOrientation b s : ℤ) •
          Finsupp.single (shiftFinset b s) 1 := by
    ext t
    by_cases ht : t = shiftFinset b s <;> simp [ht]
  rw [hone, map_smul, targetAct_single_one, shiftFinset_add] at h
  have hc := congrArg (fun c : TargetChain p m ↦ c (shiftFinset (a + b) s)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same] at hc
  apply Units.ext
  change (targetOrientation (a + b) s : ℤ) = _
  simpa [mul_comm] using hc.symm

@[simp] theorem targetOrientation_zero (s : Finset (Label p m)) :
    targetOrientation 0 s = 1 := by
  have h := targetOrientation_add 0 0 s
  simp only [zero_add, shiftFinset_zero] at h
  have h' := congrArg (fun z : ℤˣ ↦ (targetOrientation 0 s)⁻¹ * z) h
  simpa using h'.symm

section FixedDegree

variable {alpha q : ℕ}

/-- Orbit coordinates with the cyclic parameter reversed.  In this convention
actual target translation by `+1` becomes `x(a) ↦ x(a+1)`. -/
noncomputable def negFaceOrbitEquiv (hp : p.Prime) :
    FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.neg (ZMod p))).trans (faceOrbitEquiv hp)

@[simp] theorem negFaceOrbitEquiv_apply (hp : p.Prime)
    (O : FaceOrbit p m alpha q) (a : ZMod p) :
    negFaceOrbitEquiv hp (O, a) = shiftFace (-a) (orbitRep O) := rfl

/-- The unit by which the transported exterior orientation differs from the
canonical increasing orientation of its underlying finset. -/
noncomputable def orbitWeight (hp : p.Prime)
    (z : FaceOrbit p m alpha q × ZMod p) : ℤˣ :=
  targetOrientation (-z.2) (orbitRep z.1).1

/-- Coefficients in the genuinely transported exterior basis
`targetAct (-a) [orbitRep O]`. -/
noncomputable def orientedChainCoords (hp : p.Prime) :
    FaceChain p m alpha q ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) := by
  let e : FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q :=
    negFaceOrbitEquiv (m := m) (alpha := alpha) (q := q) hp
  let w : FaceOrbit p m alpha q × ZMod p → ℤˣ :=
    orbitWeight (m := m) (alpha := alpha) (q := q) hp
  exact
    { toFun := fun c O a ↦ (↑((w (O, a))⁻¹) : ℤ) * c (e (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
          (fun s ↦ (w (e.symm s) : ℤ) * x (e.symm s).1 (e.symm s).2)
      map_add' := by intros; funext O a; simp [mul_add]
      map_smul' := by
        intro z c
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            (z * c (e (O, a))) =
          z * ((↑((w (O, a))⁻¹) : ℤ) * c (e (O, a)))
        ring
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        rw [Finsupp.linearEquivFunOnFinite_symm_apply]
        change (w (e.symm s) : ℤ) *
            ((↑((w (e.symm s))⁻¹) : ℤ) * c (e (e.symm s))) = c s
        rw [e.apply_symm_apply]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      right_inv := by
        intro x
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            ((w (e.symm (e (O, a))) : ℤ) *
              x (e.symm (e (O, a))).1 (e.symm (e (O, a))).2) = x O a
        rw [e.symm_apply_apply]
        rw [← mul_assoc, Units.inv_mul, one_mul] }

@[simp] theorem orientedChainCoords_apply (hp : p.Prime)
    (c : FaceChain p m alpha q) (O : FaceOrbit p m alpha q) (a : ZMod p) :
    orientedChainCoords hp c O a =
      (↑((targetOrientation (-a) (orbitRep O).1)⁻¹) : ℤ) *
        c (shiftFace (-a) (orbitRep O)) := rfl

/-- The restriction of the *actual exterior action* `targetAct 1` to a
homogeneous allowed-face module, written coefficientwise. -/
noncomputable def actualFaceAct :
    FaceChain p m alpha q →ₗ[ℤ] FaceChain p m alpha q where
  toFun c :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
      (fun t ↦ (targetOrientation 1 (shiftFace (-1) t).1 : ℤ) *
        c (shiftFace (-1) t))
  map_add' c d := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (AllowedFace p m alpha q)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply, map_add,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply]
    funext t
    simp [mul_add]
  map_smul' z c := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (AllowedFace p m alpha q)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply, map_smul,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply]
    funext t
    change _ * (z * _) = z * (_ * _)
    ring

@[simp] theorem actualFaceAct_apply (c : FaceChain p m alpha q)
    (t : AllowedFace p m alpha q) :
    actualFaceAct c t =
      (targetOrientation 1 (shiftFace (-1) t).1 : ℤ) *
        c (shiftFace (-1) t) := by
  let f : AllowedFace p m alpha q → ℤ := fun u ↦
    (targetOrientation 1 (shiftFace (-1) u).1 : ℤ) *
      c (shiftFace (-1) u)
  change ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (AllowedFace p m alpha q)).symm f) t = f t
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (AllowedFace p m alpha q)).apply_symm_apply f) t

/-- Forget the cardinality/allowedness witness and regard a fixed-degree
allowed-face chain as an ordinary exterior target chain. -/
noncomputable def faceInclusion :
    FaceChain p m alpha q →ₗ[ℤ] TargetChain p m :=
  Finsupp.lmapDomain ℤ ℤ (fun s : AllowedFace p m alpha q ↦ s.1)

@[simp] theorem faceInclusion_single (s : AllowedFace p m alpha q) (z : ℤ) :
    faceInclusion (p := p) (m := m) (alpha := alpha) (q := q)
        (Finsupp.single s z) = Finsupp.single s.1 z := by
  simp [faceInclusion]

/-- **Actual-action conjugacy.**  With orbit parameter reversed and each
canonical face reoriented by its exterior permutation sign, the concrete
`targetAct (+1)` restriction is exactly `CyclicAlgebra.g`. -/
theorem orientedChainCoords_actualFaceAct (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualFaceAct c) =
      CyclicAlgebra.g (orientedChainCoords hp c) := by
  funext O a
  rw [orientedChainCoords_apply, actualFaceAct_apply,
    CyclicAlgebra.g_apply, orientedChainCoords_apply]
  have hshift :
      shiftFace (-1) (shiftFace (-a) (orbitRep O)) =
        shiftFace (-(a + 1)) (orbitRep O) := by
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := targetOrientation_add (p := p) (m := m)
    1 (-(a + 1)) (orbitRep O).1
  have hadd : (1 : ZMod p) + -(a + 1) = -a := by abel
  rw [hadd] at hw
  rw [hw]
  let u := targetOrientation 1 (shiftFace (-(a + 1)) (orbitRep O)).1
  let v := targetOrientation (-(a + 1)) (orbitRep O).1
  have huv : (u * v)⁻¹ * u = v⁻¹ := by
    calc
      (u * v)⁻¹ * u = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev]
      _ = v⁻¹ * (u⁻¹ * u) := by rw [mul_assoc]
      _ = v⁻¹ := by simp
  have huvZ := congrArg (fun z : ℤˣ ↦ (z : ℤ)) huv
  simp only [Units.val_mul] at huvZ
  change (↑((u * v)⁻¹) : ℤ) * ((u : ℤ) * _) =
    (↑(v⁻¹) : ℤ) * _
  rw [← mul_assoc, huvZ]

/-- The concrete exterior translation difference `targetAct (+1) - id`,
restricted to a fixed allowed degree. -/
noncomputable def actualTau :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  actualFaceAct.toAddMonoidHom - AddMonoidHom.id _

/-- The orbit norm transported through the sign-corrected coordinates. -/
noncomputable def actualNorm (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  (orientedChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp
      (orientedChainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem orientedChainCoords_actualTau (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualTau c) =
      CyclicAlgebra.D (orientedChainCoords hp c) := by
  rw [show actualTau c = actualFaceAct c - c by rfl, map_sub,
    orientedChainCoords_actualFaceAct]
  rfl

@[simp] theorem orientedChainCoords_actualNorm (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualNorm hp c) =
      CyclicAlgebra.N (orientedChainCoords hp c) := by
  change orientedChainCoords hp ((orientedChainCoords hp).symm
      (CyclicAlgebra.N (orientedChainCoords hp c))) = _
  rw [(orientedChainCoords hp).apply_symm_apply]

end FixedDegree

end TargetOrientation

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/SignedTargetOrbits.lean` -/

section
open scoped BigOperators

namespace SignedTargetOrbits

open TargetChains TargetOrbits

variable {p m alpha : ℕ} [NeZero p]

noncomputable local instance : LinearOrder (Label p m) :=
  LabelChainMap.targetLinearOrder

noncomputable abbrev PChain (p m : ℕ) := PositiveTarget.Chain ℤ (Label p m)

/-- The actual exterior-algebra action induced by translation of target vertices. -/
noncomputable def targetAct (a : ZMod p) : PChain p m →ₗ[ℤ] PChain p m :=
  PositiveTarget.map (LabelChainMap.targetShift (m := m) a)

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (LabelChainMap.targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · exact add_left_cancel (congrArg Prod.fst h)
  · simpa [LabelChainMap.targetShift] using congrArg Prod.snd h

@[simp] theorem image_targetShift (a : ZMod p) (s : Finset (Label p m)) :
    s.image (LabelChainMap.targetShift a) = shiftFinset a s := by
  ext v
  simp only [Finset.mem_image, mem_shiftFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [LabelChainMap.targetShift]
  · intro hv
    refine ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp [LabelChainMap.targetShift]

noncomputable def orientation (a : ZMod p) (s : Finset (Label p m)) : ℤˣ :=
  Finset.imageSign s (LabelChainMap.targetShift a)
    (targetShift_injective a).injOn

theorem shiftFinset_nonempty (a : ZMod p) {s : Finset (Label p m)}
    (hs : s.Nonempty) : (shiftFinset a s).Nonempty := by
  rcases hs with ⟨v, hv⟩
  exact ⟨labelShift a v, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩

noncomputable def positiveSingle (s : Finset (Label p m))
    (hs : s.Nonempty) : PChain p m :=
  ⟨Finsupp.single s 1, by
    change (Finsupp.single s (1 : ℤ)) ∅ = 0
    simp [Finset.nonempty_iff_ne_empty.mp hs]⟩

@[simp] theorem positiveSingle_coe (s : Finset (Label p m)) (hs : s.Nonempty) :
    (positiveSingle s hs : TargetChains.FullChain ℤ (Label p m)) =
      Finsupp.single s 1 := rfl

@[simp] theorem targetAct_positiveSingle (a : ZMod p)
    (s : Finset (Label p m)) (hs : s.Nonempty) :
    targetAct a (positiveSingle s hs) =
      (orientation a s : ℤ) •
        positiveSingle (shiftFinset a s)
          (shiftFinset_nonempty a hs) := by
  apply Subtype.ext
  simp only [targetAct, PositiveTarget.map, TargetChains.reducedMap,
    LinearMap.comp_apply]
  rw [show TargetChains.positiveInclusion ℤ (Label p m)
      (positiveSingle s hs) = Finsupp.single s 1 by rfl]
  have hmap : TargetChains.map (LabelChainMap.targetShift a)
      (Finsupp.single s 1) =
      Finsupp.single (shiftFinset a s) (orientation a s : ℤ) := by
    have h := TargetChains.map_single_of_injOn
      (LabelChainMap.targetShift a) s (targetShift_injective a).injOn
    have himage :
        @Finset.image _ _ LabelChainMap.targetLinearOrder.toDecidableEq
          (LabelChainMap.targetShift a) s = shiftFinset a s := by
      ext v
      simp only [Finset.mem_image, mem_shiftFinset]
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [LabelChainMap.targetShift]
      · intro hv
        refine ⟨(-a + v.1, v.2), hv, ?_⟩
        ext <;> simp [LabelChainMap.targetShift]
    rw [himage] at h
    exact h
  rw [hmap]
  have hne : shiftFinset a s ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp (shiftFinset_nonempty a hs)
  change (Finsupp.single (shiftFinset a s) (orientation a s : ℤ) -
      Finsupp.single ∅
        ((Finsupp.single (shiftFinset a s) (orientation a s : ℤ)) ∅)) = _
  ext t
  by_cases ht : t = ∅ <;> simp [ht, hne, positiveSingle]

/-- Translation on the sigma-indexed positive allowed faces. -/
noncomputable def shiftTotalFace (a : ZMod p)
    (s : TotalFace p m alpha) : TotalFace p m alpha :=
  ⟨s.1, shiftFace a s.2⟩

@[simp] theorem shiftTotalFace_zero (s : TotalFace p m alpha) :
    shiftTotalFace 0 s = s := by
  rcases s with ⟨q, s⟩
  simp [shiftTotalFace]

@[simp] theorem shiftTotalFace_add (a b : ZMod p)
    (s : TotalFace p m alpha) :
    shiftTotalFace a (shiftTotalFace b s) = shiftTotalFace (a + b) s := by
  rcases s with ⟨q, s⟩
  simp [shiftTotalFace]

def totalFaceVal (s : TotalFace p m alpha) : Finset (Label p m) := s.2.1

theorem totalFaceVal_injective :
    Function.Injective (totalFaceVal (p := p) (m := m) (alpha := alpha)) := by
  rintro ⟨q, s⟩ ⟨r, t⟩ h
  have hq : q = r := by
    have hs := s.2.1
    have ht := t.2.1
    change s.1 = t.1 at h
    rw [h] at hs
    omega
  apply Sigma.ext hq
  cases hq
  exact heq_of_eq (Subtype.ext h)

theorem totalFaceVal_ne_empty (s : TotalFace p m alpha) :
    totalFaceVal s ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (allowedFace_nonempty s.2)

/-- Include allowed total chains into the actual positive exterior target. -/
noncomputable def totalInclusion : TotalChain p m alpha →ₗ[ℤ] PChain p m where
  toFun c := ⟨Finsupp.mapDomain totalFaceVal c, by
    change Finsupp.mapDomain totalFaceVal c ∅ = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨s, hs⟩
    exact totalFaceVal_ne_empty s hs⟩
  map_add' c d := by
    apply Subtype.ext
    exact Finsupp.mapDomain_add
  map_smul' r c := by
    apply Subtype.ext
    change Finsupp.mapDomain totalFaceVal (r • c) =
      r • Finsupp.mapDomain totalFaceVal c
    exact Finsupp.mapDomain_smul
      (f := totalFaceVal (p := p) (m := m) (alpha := alpha)) r c

theorem totalInclusion_injective :
    Function.Injective
      (totalInclusion (p := p) (m := m) (alpha := alpha)) := by
  intro c d h
  apply Finsupp.mapDomain_injective totalFaceVal_injective
  exact congrArg Subtype.val h

@[simp] theorem totalInclusion_single (s : TotalFace p m alpha) (r : ℤ) :
    totalInclusion (Finsupp.single s r) =
      r • positiveSingle s.2.1 (allowedFace_nonempty s.2) := by
  apply Subtype.ext
  simp [totalInclusion, positiveSingle, totalFaceVal]

/-- The restriction of the actual exterior action to allowed total chains,
written on the canonical Finset basis with its genuine permutation sign. -/
noncomputable def totalTargetAct (a : ZMod p) :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha :=
  Finsupp.linearCombination ℤ fun s ↦
    (orientation a s.2.1 : ℤ) •
      Finsupp.single (shiftTotalFace a s) 1

@[simp] theorem totalTargetAct_single (a : ZMod p)
    (s : TotalFace p m alpha) (r : ℤ) :
    totalTargetAct a (Finsupp.single s r) =
      (r * (orientation a s.2.1 : ℤ)) •
        Finsupp.single (shiftTotalFace a s) 1 := by
  rw [totalTargetAct, Finsupp.linearCombination_single]
  simp [smul_smul, mul_comm]

@[simp] theorem totalTargetAct_apply (a : ZMod p)
    (c : TotalChain p m alpha) (t : TotalFace p m alpha) :
    totalTargetAct a c t =
      (orientation a (shiftTotalFace (-a) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-a) t) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd, mul_add]
  | single s r =>
      rw [totalTargetAct_single]
      by_cases h : t = shiftTotalFace a s
      · subst t
        have hs : shiftTotalFace (-a) (shiftTotalFace a s) = s := by
          rw [shiftTotalFace_add]
          simp
        rw [hs]
        simp [mul_comm]
      · have hne : shiftTotalFace (-a) t ≠ s := by
          intro he
          apply h
          rw [← he, shiftTotalFace_add]
          simp
        simp [h, hne]

/-- This is the key geometric certification: the signed action above is not
defined by conjugation; its inclusion is literally `PositiveTarget.map`. -/
theorem totalInclusion_targetAct (a : ZMod p) (c : TotalChain p m alpha) :
    totalInclusion (totalTargetAct a c) = targetAct a (totalInclusion c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, hc, hd]
  | single s r =>
      rw [totalTargetAct_single]
      calc
        totalInclusion
            ((r * (orientation a s.2.1 : ℤ)) •
              Finsupp.single (shiftTotalFace a s) 1) =
            (r * (orientation a s.2.1 : ℤ)) •
              positiveSingle (shiftFinset a s.2.1)
                (shiftFinset_nonempty a (allowedFace_nonempty s.2)) := by
              rw [map_smul, totalInclusion_single]
              simp [shiftTotalFace, shiftFace]
        _ = targetAct a
            (r • positiveSingle s.2.1 (allowedFace_nonempty s.2)) := by
              rw [map_smul, targetAct_positiveSingle]
              simp [smul_smul]
        _ = targetAct a (totalInclusion (Finsupp.single s r)) := by
              rw [totalInclusion_single]

/-! ## Orientation-correct coordinates on all positive degrees -/

/-- Reverse the orbit parameter so that actual translation by `+1` acts on
coordinates by reading at `a + 1`, exactly `CyclicAlgebra.g`. -/
noncomputable def negTotalOrbitEquiv (hp : p.Prime) :
    TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.neg (ZMod p))).trans
    (totalOrbitEquiv hp)

@[simp] theorem negTotalOrbitEquiv_apply (hp : p.Prime)
    (O : TotalOrbit p m alpha) (a : ZMod p) :
    negTotalOrbitEquiv hp (O, a) =
      ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ := rfl

noncomputable def totalOrbitWeight (hp : p.Prime)
    (z : TotalOrbit p m alpha × ZMod p) : ℤˣ :=
  orientation (-z.2) (orbitRep z.1.2).1

/-- The total positive allowed chain module in genuinely transported wedge
orientations `targetAct (-a) [orbitRep O]`. -/
noncomputable def orientedTotalCoords (hp : p.Prime) :
    TotalChain p m alpha ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) := by
  let e : TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha :=
    negTotalOrbitEquiv hp
  let w : TotalOrbit p m alpha × ZMod p → ℤˣ := totalOrbitWeight hp
  exact
    { toFun := fun c O a ↦ (↑((w (O, a))⁻¹) : ℤ) * c (e (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
          (fun s ↦ (w (e.symm s) : ℤ) * x (e.symm s).1 (e.symm s).2)
      map_add' := by intros; funext O a; simp [mul_add]
      map_smul' := by
        intro z c
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) * (z * c (e (O, a))) =
          z * ((↑((w (O, a))⁻¹) : ℤ) * c (e (O, a)))
        ring
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        rw [Finsupp.linearEquivFunOnFinite_symm_apply]
        change (w (e.symm s) : ℤ) *
            ((↑((w (e.symm s))⁻¹) : ℤ) * c (e (e.symm s))) = c s
        rw [e.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul]
      right_inv := by
        intro x
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            ((w (e.symm (e (O, a))) : ℤ) *
              x (e.symm (e (O, a))).1 (e.symm (e (O, a))).2) = x O a
        rw [e.symm_apply_apply, ← mul_assoc, Units.inv_mul, one_mul] }

@[simp] theorem orientedTotalCoords_apply (hp : p.Prime)
    (c : TotalChain p m alpha) (O : TotalOrbit p m alpha) (a : ZMod p) :
    orientedTotalCoords hp c O a =
      (↑((orientation (-a) (orbitRep O.2).1)⁻¹) : ℤ) *
        c ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ := rfl

/-- Coefficient form of the actual restricted `targetAct 1`. -/
noncomputable def actualTotalAct :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha where
  toFun c :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
      (fun t ↦ (orientation 1 (shiftTotalFace (-1) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-1) t))
  map_add' c d := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (TotalFace p m alpha)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply, map_add,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply]
    funext t
    simp [mul_add]
  map_smul' z c := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (TotalFace p m alpha)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply, map_smul,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply]
    funext t
    change _ * (z * _) = z * (_ * _)
    ring

@[simp] theorem actualTotalAct_apply (c : TotalChain p m alpha)
    (t : TotalFace p m alpha) :
    actualTotalAct c t =
      (orientation 1 (shiftTotalFace (-1) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-1) t) := by
  let f : TotalFace p m alpha → ℤ := fun u ↦
    (orientation 1 (shiftTotalFace (-1) u |>.2.1) : ℤ) *
      c (shiftTotalFace (-1) u)
  change ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (TotalFace p m alpha)).symm f) t = f t
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (TotalFace p m alpha)).apply_symm_apply f) t

/-- The coordinate action is the same signed restriction whose positive
inclusion is literally `PositiveTarget.map`. -/
theorem actualTotalAct_eq_totalTargetAct :
    actualTotalAct (p := p) (m := m) (alpha := alpha) = totalTargetAct 1 := by
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, hc, hd]
  | single s r =>
      apply Finsupp.ext
      intro t
      rw [actualTotalAct_apply, totalTargetAct_single]
      by_cases h : t = shiftTotalFace 1 s
      · subst t
        have hs : shiftTotalFace (-1) (shiftTotalFace 1 s) = s := by simp
        rw [hs]
        simp [mul_comm]
      · have hne : shiftTotalFace (-1) t ≠ s := by
          intro he
          apply h
          rw [← he]
          simp
        simp [h, hne]

theorem totalInclusion_actualTotalAct (c : TotalChain p m alpha) :
    totalInclusion (actualTotalAct c) = targetAct 1 (totalInclusion c) := by
  rw [actualTotalAct_eq_totalTargetAct, totalInclusion_targetAct]

/-- **Total actual-action conjugacy.**  This is the positive-degree ambient
statement used by periodic descent; no empty face occurs in either index. -/
theorem orientedTotalCoords_actualTotalAct (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalAct c) =
      CyclicAlgebra.g (orientedTotalCoords hp c) := by
  funext O a
  rw [orientedTotalCoords_apply, actualTotalAct_apply,
    CyclicAlgebra.g_apply, orientedTotalCoords_apply]
  have hshift :
      shiftTotalFace (-1)
          ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ =
        ⟨O.1, shiftFace (-(a + 1)) (orbitRep O.2)⟩ := by
    rcases O with ⟨q, O⟩
    change (⟨q, shiftFace (-1) (shiftFace (-a) (orbitRep O))⟩ :
      TotalFace p m alpha) = ⟨q, shiftFace (-(a + 1)) (orbitRep O)⟩
    apply congrArg (fun s : AllowedFace p m alpha q ↦
      (⟨q, s⟩ : TotalFace p m alpha))
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := TargetOrientation.targetOrientation_add (p := p) (m := m)
    1 (-(a + 1)) (orbitRep O.2).1
  have hadd : (1 : ZMod p) + -(a + 1) = -a := by abel
  rw [hadd] at hw
  change orientation (-a) (orbitRep O.2).1 =
    orientation 1 (shiftFinset (-(a + 1)) (orbitRep O.2).1) *
      orientation (-(a + 1)) (orbitRep O.2).1 at hw
  rw [hw]
  let u := orientation 1 (shiftFace (-(a + 1)) (orbitRep O.2)).1
  let v := orientation (-(a + 1)) (orbitRep O.2).1
  have huv : (u * v)⁻¹ * u = v⁻¹ := by
    calc
      (u * v)⁻¹ * u = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev]
      _ = v⁻¹ * (u⁻¹ * u) := by rw [mul_assoc]
      _ = v⁻¹ := by simp
  have huvZ := congrArg (fun z : ℤˣ ↦ (z : ℤ)) huv
  simp only [Units.val_mul] at huvZ
  change (↑((u * v)⁻¹) : ℤ) * ((u : ℤ) * _) =
    (↑(v⁻¹) : ℤ) * _
  rw [← mul_assoc, huvZ]

/-- General geometric translation formula.  In transported coordinates,
translation by `a` reads the old coordinate at `b + a`. -/
theorem orientedTotalCoords_totalTargetAct (hp : p.Prime)
    (a : ZMod p) (c : TotalChain p m alpha)
    (O : TotalOrbit p m alpha) (b : ZMod p) :
    orientedTotalCoords hp (totalTargetAct a c) O b =
      orientedTotalCoords hp c O (b + a) := by
  rw [orientedTotalCoords_apply, totalTargetAct_apply,
    orientedTotalCoords_apply]
  have hshift :
      shiftTotalFace (-a)
          ⟨O.1, shiftFace (-b) (orbitRep O.2)⟩ =
        ⟨O.1, shiftFace (-(b + a)) (orbitRep O.2)⟩ := by
    rcases O with ⟨q, O⟩
    change (⟨q, shiftFace (-a) (shiftFace (-b) (orbitRep O))⟩ :
      TotalFace p m alpha) = ⟨q, shiftFace (-(b + a)) (orbitRep O)⟩
    apply congrArg (fun s : AllowedFace p m alpha q ↦
      (⟨q, s⟩ : TotalFace p m alpha))
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := TargetOrientation.targetOrientation_add (p := p) (m := m)
    a (-(b + a)) (orbitRep O.2).1
  have hadd : a + -(b + a) = -b := by abel
  rw [hadd] at hw
  change orientation (-b) (orbitRep O.2).1 =
    orientation a (shiftFinset (-(b + a)) (orbitRep O.2).1) *
      orientation (-(b + a)) (orbitRep O.2).1 at hw
  rw [hw]
  let u := orientation a (shiftFace (-(b + a)) (orbitRep O.2)).1
  let v := orientation (-(b + a)) (orbitRep O.2).1
  have huv : (u * v)⁻¹ * u = v⁻¹ := by
    calc
      (u * v)⁻¹ * u = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev]
      _ = v⁻¹ * (u⁻¹ * u) := by rw [mul_assoc]
      _ = v⁻¹ := by simp
  have huvZ := congrArg (fun z : ℤˣ ↦ (z : ℤ)) huv
  simp only [Units.val_mul] at huvZ
  change (↑((u * v)⁻¹) : ℤ) * ((u : ℤ) * _) =
    (↑(v⁻¹) : ℤ) * _
  rw [← mul_assoc, huvZ]

/-- The literal geometric orbit sum of all target translations. -/
noncomputable def geometricTotalNorm :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha :=
  ∑ a : ZMod p, totalTargetAct a

@[simp] theorem orientedTotalCoords_geometricTotalNorm (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (geometricTotalNorm c) =
      CyclicAlgebra.N (orientedTotalCoords hp c) := by
  funext O b
  change orientedTotalCoords hp
      ((∑ a : ZMod p, totalTargetAct a) c) O b = _
  rw [LinearMap.sum_apply, map_sum]
  simp only [Finset.sum_apply, orientedTotalCoords_totalTargetAct,
    CyclicAlgebra.N_apply]
  exact Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun _ ↦ rfl)

/-! ## The actual two-periodic operators on the total positive module -/

/-- The actual geometric translation difference on all positive allowed
degrees at once. -/
noncomputable def actualTotalTau :
    TotalChain p m alpha →+ TotalChain p m alpha :=
  actualTotalAct.toAddMonoidHom - AddMonoidHom.id _

/-- The cyclic norm transported through the sign-corrected total
coordinates. -/
noncomputable def actualTotalNorm (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha :=
  (orientedTotalCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp
      (orientedTotalCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem orientedTotalCoords_actualTotalTau (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalTau c) =
      CyclicAlgebra.D (orientedTotalCoords hp c) := by
  rw [show actualTotalTau c = actualTotalAct c - c by rfl, map_sub,
    orientedTotalCoords_actualTotalAct]
  rfl

@[simp] theorem orientedTotalCoords_actualTotalNorm (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalNorm hp c) =
      CyclicAlgebra.N (orientedTotalCoords hp c) := by
  change orientedTotalCoords hp ((orientedTotalCoords hp).symm
      (CyclicAlgebra.N (orientedTotalCoords hp c))) = _
  rw [(orientedTotalCoords hp).apply_symm_apply]

/-- The transported norm is the literal sum of all geometric target
translations. -/
theorem actualTotalNorm_eq_geometricTotalNorm (hp : p.Prime) :
    actualTotalNorm (m := m) (alpha := alpha) hp =
      (geometricTotalNorm (p := p) (m := m) (alpha := alpha)).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro c
  apply (orientedTotalCoords hp).injective
  change orientedTotalCoords hp (actualTotalNorm hp c) =
    orientedTotalCoords hp (geometricTotalNorm c)
  rw [orientedTotalCoords_actualTotalNorm,
    orientedTotalCoords_geometricTotalNorm]

theorem exists_actualTotalNorm_of_actualTotalTau_eq_zero (hp : p.Prime)
    {c : TotalChain p m alpha} (hc : actualTotalTau c = 0) :
    ∃ d, actualTotalNorm hp d = c := by
  have hD : CyclicAlgebra.D (orientedTotalCoords hp c) = 0 := by
    rw [← orientedTotalCoords_actualTotalTau]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_N_of_D_eq_zero hD
  refine ⟨(orientedTotalCoords hp).symm y, ?_⟩
  apply (orientedTotalCoords hp).injective
  rw [orientedTotalCoords_actualTotalNorm,
    (orientedTotalCoords hp).apply_symm_apply, hy]

theorem exists_actualTotalTau_of_actualTotalNorm_eq_zero (hp : p.Prime)
    {c : TotalChain p m alpha} (hc : actualTotalNorm hp c = 0) :
    ∃ d, actualTotalTau d = c := by
  have hN : CyclicAlgebra.N (orientedTotalCoords hp c) = 0 := by
    rw [← orientedTotalCoords_actualTotalNorm]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_D_of_N_eq_zero hN
  refine ⟨(orientedTotalCoords hp).symm y, ?_⟩
  apply (orientedTotalCoords hp).injective
  rw [orientedTotalCoords_actualTotalTau,
    (orientedTotalCoords hp).apply_symm_apply, hy]

end SignedTargetOrbits

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/ReducedLabelEquivariance.lean` -/

section
namespace ReducedLabelEquivariance

open TargetChains
open ZpTuckerScratch

variable {p n m : ℕ} [NeZero p]

noncomputable local instance : LinearOrder (LabelChainMap.TargetVertex p m) :=
  LabelChainMap.targetLinearOrder

end ReducedLabelEquivariance

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/AllowedComplex.lean` -/

section
/-!
The normalized (nonempty) simplicial chain complex on the allowed target
faces.  `TargetOrbits.TotalChain` is the coefficient model used by the orbit
calculation; `PositiveAllowed` is the same module inside the exterior-algebra
positive target chains.
-/

namespace AllowedComplex

open TargetChains

noncomputable section

variable {p m alpha : ℕ} [NeZero p]

abbrev Vertex (p m : ℕ) := ZMod p × Fin m

noncomputable local instance targetOrder : LinearOrder (Vertex p m) :=
  LabelChainMap.targetLinearOrder

theorem targetAllowed_iff (s : Finset (Vertex p m)) :
    TargetOrbits.Allowed alpha s ↔ AllowedFaces.IsAllowed alpha s := by
  rfl

/-! ## Basis faces and downward closure -/

/-- Increasing enumeration of a finite target face.  The `List.ofFn` form
keeps its length definitionally tied to `s.card`, which is convenient for the
exterior basis. -/
noncomputable def faceList (s : Finset (Vertex p m)) : List (Vertex p m) :=
  List.ofFn (fun i : Fin s.card ↦ s.orderEmbOfFin rfl i)

@[simp] theorem faceList_length (s : Finset (Vertex p m)) :
    (faceList s).length = s.card := by simp [faceList]

@[simp] theorem faceList_toFinset (s : Finset (Vertex p m)) :
    (faceList s).toFinset = s := by
  ext v
  simp only [faceList, List.mem_toFinset, List.mem_ofFn]
  change v ∈ Set.range (s.orderEmbOfFin rfl) ↔ v ∈ (s : Set (Vertex p m))
  rw [Finset.range_orderEmbOfFin]

/-- Left exterior multiplication by one vertex sends a basis face to an
integer multiple of the basis of the inserted face. -/
theorem wedgePrepend_single_exists
    {V : Type*} [Fintype V] [LinearOrder V]
    (v : V) (s : Finset V) :
    ∃ z : ℤ, TargetBridge.wedgePrepend v
        (Finsupp.single s (1 : ℤ)) =
      z • Finsupp.single (insert v s) (1 : ℤ) := by
  by_cases hvs : v ∈ s
  · refine ⟨0, ?_⟩
    have hprod :
        TargetChains.exteriorBasis ℤ V {v} *
          TargetChains.exteriorBasis ℤ V s = 0 := by
      let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
      let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
      apply ExteriorAlgebra.basis_mul_of_not_disjoint
        (TargetChains.vertexBasis ℤ V) sv ss
      simpa [sv, ss, Finset.disjoint_singleton_left]
    simp only [zero_smul]
    apply (TargetChains.toExterior ℤ V).injective
    rw [map_zero, TargetBridge.toExterior_wedgePrepend,
      TargetChains.toExterior_single, one_smul,
      PositiveTarget.iota_single_eq_exteriorBasis_singleton, hprod]
  · let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
    let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
    have hd : Disjoint sv.val ss.val := by
      simpa [sv, ss, Finset.disjoint_singleton_left]
    refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
    apply (TargetChains.toExterior ℤ V).injective
    rw [TargetBridge.toExterior_wedgePrepend,
      TargetChains.toExterior_single, one_smul,
      PositiveTarget.iota_single_eq_exteriorBasis_singleton]
    change (TargetChains.vertexBasis ℤ V).ExteriorAlgebra sv.val *
        (TargetChains.vertexBasis ℤ V).ExteriorAlgebra ss.val = _
    rw [ExteriorAlgebra.basis_mul_of_disjoint
      (TargetChains.vertexBasis ℤ V) sv ss hd]
    simp [sv, ss, TargetChains.exteriorBasis,
      Set.powersetCard.disjUnion, Units.smul_def, Algebra.smul_def]

/-- A list label has a single possible exterior coordinate, namely the
unordered set of labels.  Repetitions are absorbed by the integer coefficient
being zero. -/
theorem labelList_eq_smul_single_toFinset
    {X V : Type*} [Fintype V] [LinearOrder V]
    (lab : X → V) (l : List X) :
    ∃ z : ℤ, TargetBridge.labelList lab l =
      z • Finsupp.single (l.map lab).toFinset (1 : ℤ) := by
  induction l with
  | nil =>
      refine ⟨1, ?_⟩
      rw [PositiveTarget.labelList_nil_eq_single_empty]
      simp
  | cons x xs ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨w, hw⟩ := wedgePrepend_single_exists (lab x)
        (xs.map lab).toFinset
      refine ⟨z * w, ?_⟩
      rw [TargetBridge.labelList, hz, map_smul, hw]
      simp [smul_smul]

/-- Positive target chains whose nonzero faces satisfy the capacity bounds. -/
noncomputable def PositiveAllowed (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ (PositiveTarget.Chain ℤ (Vertex p m)) :=
  (AllowedFaces.allowedChains ℤ p m alpha).comap
    (TargetChains.positiveInclusion ℤ (Vertex p m))

theorem mem_positiveAllowed
    (c : PositiveTarget.Chain ℤ (Vertex p m)) :
    c ∈ PositiveAllowed p m alpha ↔
      ∀ s ∈ (c : TargetChains.FullChain ℤ (Vertex p m)).support,
        AllowedFaces.IsAllowed alpha s := by
  rw [PositiveAllowed, Submodule.mem_comap,
    AllowedFaces.mem_allowedChains]
  rfl

/-- The corresponding supported submodule of the full coefficient module.
The predicate includes nonemptiness, so no augmentation coordinate occurs. -/
noncomputable def NonemptyAllowed (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ (TargetChains.FullChain ℤ (Vertex p m)) :=
  Finsupp.supported ℤ ℤ
    {s | s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}

theorem mem_nonemptyAllowed
    (c : TargetChains.FullChain ℤ (Vertex p m)) :
    c ∈ NonemptyAllowed p m alpha ↔
      ∀ s ∈ c.support,
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s := by
  rw [NonemptyAllowed, Finsupp.mem_supported]
  constructor
  · intro h s hs
    exact h hs
  · intro h s hs
    exact h s hs

/-- Forgetting the positive-chain subtype identifies positive allowed chains
with full chains supported on nonempty allowed faces. -/
noncomputable def positiveAllowedEquivSupported :
    PositiveAllowed p m alpha ≃ₗ[ℤ] NonemptyAllowed p m alpha := by
  let f : PositiveAllowed p m alpha →ₗ[ℤ]
      TargetChains.FullChain ℤ (Vertex p m) :=
    (TargetChains.positiveInclusion ℤ (Vertex p m)).comp
      (PositiveAllowed p m alpha).subtype
  let g : PositiveAllowed p m alpha →ₗ[ℤ] NonemptyAllowed p m alpha :=
    f.codRestrict (NonemptyAllowed p m alpha) (by
      intro c
      rw [mem_nonemptyAllowed]
      intro s hs
      constructor
      · rw [Finset.nonempty_iff_ne_empty]
        intro hse
        subst s
        have hc0 : ((c.1 : PositiveTarget.Chain ℤ (Vertex p m)) :
            TargetChains.FullChain ℤ (Vertex p m)) ∅ = 0 := by
          have hker := c.1.property
          change Finsupp.lapply ∅
            ((c.1 : PositiveTarget.Chain ℤ (Vertex p m)) :
              TargetChains.FullChain ℤ (Vertex p m)) = 0 at hker
          simpa using hker
        exact (Finsupp.mem_support_iff.mp hs) hc0
      · exact (mem_positiveAllowed c.1).1 c.2 s hs)
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y h
    have hfull :
        (g x : TargetChains.FullChain ℤ (Vertex p m)) = g y :=
      congrArg (fun z : NonemptyAllowed p m alpha ↦
        (z.1 : TargetChains.FullChain ℤ (Vertex p m))) h
    exact Subtype.ext (Subtype.ext hfull)
  · intro c
    have hc0 : (c.1 : TargetChains.FullChain ℤ (Vertex p m)) ∅ = 0 := by
      by_contra h
      have hempty : (∅ : Finset (Vertex p m)) ∈ c.1.support :=
        Finsupp.mem_support_iff.mpr h
      exact ((mem_nonemptyAllowed c.1).1 c.2 ∅ hempty).1.ne_empty rfl
    let pc : PositiveTarget.Chain ℤ (Vertex p m) :=
      ⟨c.1, by
        change Finsupp.lapply ∅
          (c.1 : TargetChains.FullChain ℤ (Vertex p m)) = 0
        simpa using hc0⟩
    have hpa : pc ∈ PositiveAllowed p m alpha := by
      rw [mem_positiveAllowed]
      intro s hs
      exact ((mem_nonemptyAllowed c.1).1 c.2 s hs).2
    refine ⟨⟨pc, hpa⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- The two files' definitionally equivalent allowed-face predicates induce
an equivalence of their nonempty face subtypes. -/
noncomputable def positivePredicateEquiv :
    TargetOrbits.PositiveAllowedFinset p m alpha ≃
      {s : Finset (Vertex p m) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} where
  toFun s := ⟨s.1, s.2.1, (targetAllowed_iff s.1).1 s.2.2⟩
  invFun s := ⟨s.1, s.2.1, (targetAllowed_iff s.1).2 s.2.2⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

/-- The orbit-indexed total face basis, with the duplicate target predicate
replaced by `AllowedFaces.IsAllowed`. -/
noncomputable def totalFaceEquivNonemptyAllowed :
    TargetOrbits.TotalFace p m alpha ≃
      {s : Finset (Vertex p m) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} :=
  (TargetOrbits.totalFaceEquivPositive p m alpha).trans
    (positivePredicateEquiv (p := p) (m := m) (alpha := alpha))

/-- Canonical coefficient equivalence between orbit/descent total chains and
the positive allowed submodule of the normalized target complex. -/
noncomputable def totalChainEquivPositiveAllowed :
    TargetOrbits.TotalChain p m alpha ≃ₗ[ℤ] PositiveAllowed p m alpha :=
  (Finsupp.lcongr (totalFaceEquivNonemptyAllowed (p := p) (m := m)
      (alpha := alpha)) (LinearEquiv.refl ℤ ℤ)).trans
    ((Finsupp.supportedEquivFinsupp
      {s : Finset (Vertex p m) |
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}).symm.trans
      (positiveAllowedEquivSupported (p := p) (m := m)
        (alpha := alpha)).symm)

end

end AllowedComplex

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/PeriodicDescent.lean` -/

section
/-!
The algebraic downward step in the periodic-resolution proof.  All degrees
may live in one ambient chain module; homogeneity is needed only to establish
that the chosen top chain is zero.
-/

namespace PeriodicDescent

variable {A : Type*} [AddCommGroup A]

structure Datum (A : Type*) [AddCommGroup A] where
  boundary : A →+ A
  tau : A →+ A
  normOp : A →+ A
  boundary_sq : ∀ x, boundary (boundary x) = 0
  boundary_tau : ∀ x, boundary (tau x) = tau (boundary x)
  boundary_norm : ∀ x, boundary (normOp x) = normOp (boundary x)
  ker_tau : ∀ {x}, tau x = 0 → ∃ y, normOp y = x
  ker_norm : ∀ {x}, normOp x = 0 → ∃ y, tau y = x

namespace Datum

variable (P : Datum A)

def op (i : ℕ) : A →+ A := if Odd i then P.tau else P.normOp

@[simp] theorem op_zero : P.op 0 = P.normOp := by simp [op]

theorem boundary_op (i : ℕ) (x : A) :
    P.boundary (P.op i x) = P.op i (P.boundary x) := by
  by_cases hi : Odd i
  · simp [op, hi, P.boundary_tau]
  · simp [op, hi, P.boundary_norm]

theorem exact_op_succ (i : ℕ) {x : A} (hx : P.op (i + 1) x = 0) :
    ∃ y, P.op i y = x := by
  rcases Nat.even_or_odd i with hi | hi
  · have hni : ¬ Odd i := Nat.not_odd_iff_even.mpr hi
    have his : Odd (i + 1) := hi.add_one
    simpa [op, hni] using P.ker_tau (by simpa [op, his] using hx)
  · have his : ¬ Odd (i + 1) := Nat.not_odd_iff_even.mpr hi.add_one
    simpa [op, hi] using P.ker_norm (by simpa [op, his] using hx)

/-- Starting from a decomposition in degree `i`, descend to degree zero.
The `next` argument is the degree-`i+1` correction and `same` is the
degree-`i` correction.
-/
theorem descend_from
    (y : ℕ → A)
    (hrel : ∀ i, P.boundary (y (i + 1)) = P.op (i + 1) (y i)) :
    ∀ (i : ℕ) (next same : A),
      y i = P.boundary next + P.op i same →
      ∃ z₁ z₀ : A, y 0 = P.boundary z₁ + P.normOp z₀ := by
  intro i
  induction i with
  | zero =>
      intro next same h
      exact ⟨next, same, by simpa using h⟩
  | succ i ih =>
      intro next same h
      have hk : P.op (i + 1) (y i - P.boundary same) = 0 := by
        rw [map_sub, ← hrel i]
        have hb := congrArg P.boundary h
        simp only [map_add, P.boundary_op, P.boundary_sq, zero_add] at hb
        exact sub_eq_zero.mpr hb
      obtain ⟨previous, hp⟩ := P.exact_op_succ i hk
      apply ih same previous
      rw [hp]
      abel

/-- If a resolution chain has zero top component, its bottom component is a
boundary plus a norm. -/
theorem bottom_decomposition
    (y : ℕ → A)
    (hrel : ∀ i, P.boundary (y (i + 1)) = P.op (i + 1) (y i))
    (Q : ℕ) (htop : y Q = 0) :
    ∃ z₁ z₀ : A, y 0 = P.boundary z₁ + P.normOp z₀ := by
  apply P.descend_from y hrel Q 0 0
  simp [htop]

end Datum
end PeriodicDescent

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/CyclicExactness.lean` -/

section
open scoped BigOperators

namespace CyclicAlgebra

variable {p : ℕ} {ι : Type*}

/-! ## The two exactness identities -/

/-- The canonical partial-sum primitive on each cyclic orbit.  At coordinate
`a`, it is the sum of the coordinates strictly before `a` in the standard
representative interval `[0,p)`.
-/
def cyclicPrimitive [NeZero p] (x : FreeCyclic p ι) : FreeCyclic p ι :=
  fun i a => ∑ k ∈ Finset.range a.val, x i (k : ZMod p)

/-- The partial-sum primitive differentiates to `x` whenever the cyclic
coordinate sum of `x` is zero.  The wraparound coordinate is exactly where
the hypothesis `N x = 0` is used.
-/
theorem D_cyclicPrimitive_of_N_eq_zero [NeZero p]
    {x : FreeCyclic p ι} (hx : N x = 0) : D (cyclicPrimitive x) = x := by
  by_cases hp1 : p = 1
  · letI : Unique (ZMod p) := hp1 ▸ inferInstance
    have hx0 : x = 0 := by
      funext i a
      have h := congrFun (congrFun hx i) (0 : ZMod p)
      have hsum : (∑ b : ZMod p, x i b) = 0 := by
        simpa only [N_apply, Pi.zero_apply] using h
      calc
        x i a = ∑ b : ZMod p, x i b := by
          simp only [Fintype.sum_unique]
          congr 1
          exact Subsingleton.elim _ _
        _ = 0 := hsum
    rw [hx0]
    funext i a
    simp [D_apply, cyclicPrimitive]
  · have hp : 1 < p :=
      (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne p, hp1⟩
    letI : Fact (1 < p) := ⟨hp⟩
    funext i a
    rw [D_apply]
    change (∑ k ∈ Finset.range (a + 1).val, x i (k : ZMod p)) -
      (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) = x i a
    have hsum_univ : (∑ b : ZMod p, x i b) = 0 := by
      have h := congrFun (congrFun hx i) 0
      simpa [N_apply] using h
    have hsum_range : (∑ k ∈ Finset.range p, x i (k : ZMod p)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have hconvert :
          (∑ k : Fin p, x i (k.val : ZMod p)) = ∑ b : ZMod p, x i b := by
        apply Fintype.sum_equiv (ZMod.finEquiv p)
        intro k
        congr 2
        have hv : (ZMod.finEquiv p k).val = k.val := by
          cases p with
          | zero => exact (NeZero.ne 0 rfl).elim
          | succ p => rfl
        exact (congrArg (fun n : ℕ => (n : ZMod p)) hv.symm).trans
          (ZMod.natCast_zmod_val (ZMod.finEquiv p k))
      exact hconvert.trans hsum_univ
    by_cases ha : a.val + 1 < p
    · have hval : (a + 1).val = a.val + 1 := by
        have hlt : a.val + (1 : ZMod p).val < p := by
          simpa [ZMod.val_one p] using ha
        simpa [ZMod.val_one p] using ZMod.val_add_of_lt hlt
      rw [hval, Finset.sum_range_succ, ZMod.natCast_zmod_val,
        add_sub_cancel_left]
    · have hap : a.val + 1 = p := by
        have hva := a.val_lt
        omega
      have hval : (a + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one p, hap, Nat.mod_self]
      have hsum_last :
          (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) + x i a = 0 := by
        rw [← ZMod.natCast_zmod_val a]
        simpa [← hap, Finset.sum_range_succ] using hsum_range
      rw [hval]
      simp only [Finset.sum_range_zero, zero_sub]
      omega

/-- Explicit range witness for the kernel of `N`. -/
theorem exists_cyclicPrimitive_of_N_eq_zero [NeZero p]
    {x : FreeCyclic p ι} (hx : N x = 0) :
    ∃ y, D y = x :=
  ⟨cyclicPrimitive x, D_cyclicPrimitive_of_N_eq_zero hx⟩

/-! ## Augmentation -/

/-! ## Packaging for `PeriodicDescent` -/

end CyclicAlgebra

/-! ## Transport to an ambient free-orbit module -/

namespace CyclicExactness

open CyclicAlgebra

variable {p : ℕ} {ι A : Type*}
variable [NeZero p] [Fintype ι]
variable [AddCommGroup A] [Module ℤ A]

/-- Coordinate data identifying an ambient module with a union of free cyclic
orbits.  These three compatibility equations are precisely what an orbit
decomposition must establish. -/
structure Transport (p : ℕ) (ι A : Type*) [NeZero p] [Fintype ι]
    [AddCommGroup A] [Module ℤ A] where
  equiv : A ≃ₗ[ℤ] FreeCyclic p ι
  tau : A →+ A
  normOp : A →+ A
  augmentation : A →+ ℤ
  equiv_tau : ∀ x, equiv (tau x) = D (equiv x)
  equiv_norm : ∀ x, equiv (normOp x) = N (equiv x)
  augmentation_equiv : ∀ x, augmentation x = CyclicAlgebra.augmentation (equiv x)

namespace Transport

variable (T : Transport p ι A)

/-- Exactness at the difference operator, transported through free-orbit
coordinates. -/
theorem ker_tau {x : A} (hx : T.tau x = 0) : ∃ y, T.normOp y = x := by
  have hx' : D (T.equiv x) = 0 := by
    rw [← T.equiv_tau x, hx, map_zero]
  obtain ⟨z, hz⟩ := exists_N_of_D_eq_zero hx'
  refine ⟨T.equiv.symm z, T.equiv.injective ?_⟩
  rw [T.equiv_norm, T.equiv.apply_symm_apply, hz]

/-- Exactness at the norm operator, transported through free-orbit
coordinates. -/
theorem ker_norm {x : A} (hx : T.normOp x = 0) : ∃ y, T.tau y = x := by
  have hx' : N (T.equiv x) = 0 := by
    rw [← T.equiv_norm x, hx, map_zero]
  obtain ⟨z, hz⟩ := exists_cyclicPrimitive_of_N_eq_zero hx'
  refine ⟨T.equiv.symm z, T.equiv.injective ?_⟩
  rw [T.equiv_tau, T.equiv.apply_symm_apply, hz]

end Transport
end CyclicExactness

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/AllowedDescent.lean` -/

section
namespace AllowedDescent

open TargetChains

noncomputable section

variable {p m alpha : ℕ} [NeZero p]

abbrev Vertex := ZMod p × Fin m
abbrev Total := TargetOrbits.TotalChain p m alpha
abbrev PA := AllowedComplex.PositiveAllowed p m alpha

noncomputable local instance targetOrder : LinearOrder (Vertex (p := p) (m := m)) :=
  LabelChainMap.targetLinearOrder

theorem single_empty_mem_allowed (r : ℤ) :
    Finsupp.single (∅ : Finset (Vertex (p := p) (m := m))) r ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.mem_allowedChains]
  intro s hs
  by_cases h : s = ∅
  · subst s
    exact AllowedFaces.isAllowed_empty p m alpha
  · exact ((Finsupp.mem_support_iff.mp hs) (by simp [h])).elim

noncomputable def positiveBoundary : PA (p := p) (m := m) (alpha := alpha) →ₗ[ℤ]
    PA (p := p) (m := m) (alpha := alpha) :=
  (PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))).domRestrict
      (AllowedComplex.PositiveAllowed p m alpha) |>.codRestrict
    (AllowedComplex.PositiveAllowed p m alpha) (by
      intro c
      change TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m))
          (PositiveTarget.boundary ℤ (Vertex (p := p) (m := m)) c.1) ∈
        AllowedFaces.allowedChains ℤ p m alpha
      change TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m))
          (TargetChains.projectPositive ℤ (Vertex (p := p) (m := m))
            (TargetChains.boundary ℤ (Vertex (p := p) (m := m))
              (TargetChains.positiveInclusion ℤ (Vertex (p := p) (m := m)) c.1))) ∈ _
      rw [TargetChains.positiveInclusion_projectPositive]
      apply Submodule.sub_mem
      · exact PositiveAllowed.boundary_mem_allowed c.2
      · exact single_empty_mem_allowed _)

noncomputable def totalBoundary : Total (p := p) (m := m) (alpha := alpha) →ₗ[ℤ]
    Total (p := p) (m := m) (alpha := alpha) :=
  (AllowedComplex.totalChainEquivPositiveAllowed (p := p) (m := m)
      (alpha := alpha)).symm.toLinearMap.comp
    ((positiveBoundary (p := p) (m := m) (alpha := alpha)).comp
      (AllowedComplex.totalChainEquivPositiveAllowed (p := p) (m := m)
        (alpha := alpha)).toLinearMap)

theorem equiv_coe_eq_totalInclusion
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    (AllowedComplex.totalChainEquivPositiveAllowed c).1 =
      SignedTargetOrbits.totalInclusion c := by
  apply Subtype.ext
  let P := AllowedComplex.positiveAllowedEquivSupported
    (p := p) (m := m) (alpha := alpha)
  let S := Finsupp.supportedEquivFinsupp
    (R := ℤ) (M := ℤ)
    {s : Finset (Vertex (p := p) (m := m)) |
      s.Nonempty ∧ AllowedFaces.IsAllowed alpha s}
  let L := Finsupp.lcongr
    (AllowedComplex.totalFaceEquivNonemptyAllowed
      (p := p) (m := m) (alpha := alpha))
    (LinearEquiv.refl ℤ ℤ)
  have hc : P (AllowedComplex.totalChainEquivPositiveAllowed c) =
      S.symm (L c) := by
    change P (P.symm (S.symm (L c))) = S.symm (L c)
    exact P.apply_symm_apply _
  change
    ((P (AllowedComplex.totalChainEquivPositiveAllowed c)).1 :
        TargetChains.FullChain ℤ (Vertex (p := p) (m := m))) =
      (SignedTargetOrbits.totalInclusion c).1
  rw [hc]
  ext t
  change (S.symm (L c)).1 t =
    Finsupp.mapDomain SignedTargetOrbits.totalFaceVal c t
  by_cases h : t.Nonempty ∧ AllowedFaces.IsAllowed alpha t
  · let st : {s : Finset (Vertex (p := p) (m := m)) //
        s.Nonempty ∧ AllowedFaces.IsAllowed alpha s} := ⟨t, h⟩
    let s : TargetOrbits.TotalFace p m alpha :=
      (AllowedComplex.totalFaceEquivNonemptyAllowed
        (p := p) (m := m) (alpha := alpha)).symm st
    have hs : SignedTargetOrbits.totalFaceVal s = t := by
      change s.2.1 = t
      exact congrArg Subtype.val
        ((AllowedComplex.totalFaceEquivNonemptyAllowed
          (p := p) (m := m) (alpha := alpha)).apply_symm_apply st)
    rw [← hs, Finsupp.mapDomain_apply
      SignedTargetOrbits.totalFaceVal_injective]
    have hsallowed :
        (SignedTargetOrbits.totalFaceVal s).Nonempty ∧
          AllowedFaces.IsAllowed alpha
            (SignedTargetOrbits.totalFaceVal s) :=
      ⟨TargetOrbits.allowedFace_nonempty s.2,
        (AllowedComplex.targetAllowed_iff s.2.1).1 s.2.2.2⟩
    let u : TargetOrbits.PositiveAllowedFinset p m alpha :=
      ⟨t, h.1, (AllowedComplex.targetAllowed_iff t).2 h.2⟩
    have hu : SignedTargetOrbits.totalFaceVal
        ((TargetOrbits.totalFaceEquivPositive p m alpha).symm u) = t := by
      exact congrArg Subtype.val
        ((TargetOrbits.totalFaceEquivPositive p m alpha).apply_symm_apply u)
    simp [S, L, s, st, hsallowed, u, hu, h,
      AllowedComplex.totalFaceEquivNonemptyAllowed,
      AllowedComplex.positivePredicateEquiv]
  · have ht : t ∉ Set.range
        (SignedTargetOrbits.totalFaceVal
          (p := p) (m := m) (alpha := alpha)) := by
      rintro ⟨s, rfl⟩
      apply h
      exact ⟨TargetOrbits.allowedFace_nonempty s.2,
        (AllowedComplex.targetAllowed_iff s.2.1).1 s.2.2.2⟩
    rw [Finsupp.mapDomain_of_notMem_range c t ht]
    simp [S, L, h]

theorem totalInclusion_boundary
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    SignedTargetOrbits.totalInclusion (totalBoundary c) =
      PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))
        (SignedTargetOrbits.totalInclusion c) := by
  rw [← equiv_coe_eq_totalInclusion (c := totalBoundary c),
    ← equiv_coe_eq_totalInclusion (c := c)]
  change (AllowedComplex.totalChainEquivPositiveAllowed
    ((AllowedComplex.totalChainEquivPositiveAllowed).symm
      (positiveBoundary (AllowedComplex.totalChainEquivPositiveAllowed c)))).1 =
        PositiveTarget.boundary ℤ (Vertex (p := p) (m := m))
          (AllowedComplex.totalChainEquivPositiveAllowed c).1
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem totalBoundary_sq (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (totalBoundary c) = 0 := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [totalInclusion_boundary, totalInclusion_boundary,
    PositiveTarget.boundary_boundary]
  simp

theorem totalBoundary_targetAct (a : ZMod p)
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.totalTargetAct a c) =
      SignedTargetOrbits.totalTargetAct a (totalBoundary c) := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [totalInclusion_boundary,
    SignedTargetOrbits.totalInclusion_targetAct,
    SignedTargetOrbits.totalInclusion_targetAct,
    totalInclusion_boundary]
  exact (PositiveTarget.map_boundary
    (LabelChainMap.targetShift (m := m) a)
    (SignedTargetOrbits.totalInclusion c)).symm

theorem totalBoundary_actualTotalAct
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalAct c) =
      SignedTargetOrbits.actualTotalAct (totalBoundary c) := by
  rw [SignedTargetOrbits.actualTotalAct_eq_totalTargetAct]
  exact totalBoundary_targetAct 1 c

theorem totalBoundary_actualTotalTau
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalTau c) =
      SignedTargetOrbits.actualTotalTau (totalBoundary c) := by
  change totalBoundary (SignedTargetOrbits.actualTotalAct c - c) =
    SignedTargetOrbits.actualTotalAct (totalBoundary c) - totalBoundary c
  rw [map_sub, totalBoundary_actualTotalAct]

theorem totalBoundary_geometricTotalNorm
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.geometricTotalNorm c) =
      SignedTargetOrbits.geometricTotalNorm (totalBoundary c) := by
  simp only [SignedTargetOrbits.geometricTotalNorm,
    LinearMap.sum_apply, map_sum, totalBoundary_targetAct]

theorem totalBoundary_actualTotalNorm (hp : p.Prime)
    (c : Total (p := p) (m := m) (alpha := alpha)) :
    totalBoundary (SignedTargetOrbits.actualTotalNorm hp c) =
      SignedTargetOrbits.actualTotalNorm hp (totalBoundary c) := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm hp]
  exact totalBoundary_geometricTotalNorm c

noncomputable def datum (hp : p.Prime) :
    PeriodicDescent.Datum (Total (p := p) (m := m) (alpha := alpha)) where
  boundary := totalBoundary.toAddMonoidHom
  tau := SignedTargetOrbits.actualTotalTau
  normOp := SignedTargetOrbits.actualTotalNorm hp
  boundary_sq := totalBoundary_sq
  boundary_tau := totalBoundary_actualTotalTau
  boundary_norm := totalBoundary_actualTotalNorm hp
  ker_tau := SignedTargetOrbits.exists_actualTotalNorm_of_actualTotalTau_eq_zero hp
  ker_norm := SignedTargetOrbits.exists_actualTotalTau_of_actualTotalNorm_eq_zero hp

end

end AllowedDescent

end

/-! ### Upstream module `ErdosProblems/Erdos780/External/Erdos780Core.lean` -/

section
open scoped BigOperators

namespace Erdos780Core

open ZpTuckerScratch

noncomputable section

variable {p n m alpha : ℕ}

abbrev Vertex (p m : ℕ) := ZMod p × Fin m
abbrev Total (p m alpha : ℕ) := TargetOrbits.TotalChain p m alpha

noncomputable local instance targetOrder [NeZero p] : LinearOrder (Vertex p m) :=
  LabelChainMap.targetLinearOrder

theorem map_apply_empty
    {V W : Type*} [Fintype V] [Fintype W]
    [LinearOrder V] [LinearOrder W]
    (f : V → W) (hf : Function.Injective f)
    (c : TargetChains.FullChain ℤ V) :
    TargetChains.map f c ∅ = c ∅ := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, Finsupp.add_apply, hc, hd]
  | single s z =>
      by_cases hs : s = ∅
      · subst s
        rw [TargetChains.map_single_empty]
        simp
      · have himage : (s.image f).Nonempty :=
          Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        rw [show Finsupp.single s z = z • Finsupp.single s (1 : ℤ) by simp,
          map_smul, TargetChains.map_single_of_injOn f s hf.injOn]
        simp [hs, Finset.nonempty_iff_ne_empty.mp himage]

theorem augmentation_map
    {V W : Type*} [Fintype V] [Fintype W]
    [LinearOrder V] [LinearOrder W]
    (f : V → W) (hf : Function.Injective f)
    (c : PositiveTarget.Chain ℤ V) :
    PositiveTarget.augmentation ℤ W (PositiveTarget.map f c) =
      PositiveTarget.augmentation ℤ V c := by
  change TargetChains.boundary ℤ W
      (TargetChains.positiveInclusion ℤ W
        (TargetChains.projectPositive ℤ W
          (TargetChains.map f
            (TargetChains.positiveInclusion ℤ V c)))) ∅ =
    TargetChains.boundary ℤ V
      (TargetChains.positiveInclusion ℤ V c) ∅
  rw [TargetChains.boundary_projectPositive, ← TargetChains.map_boundary]
  exact map_apply_empty f hf _

theorem augmentation_targetAct [NeZero p] (a : ZMod p)
    (c : PositiveTarget.Chain ℤ (Vertex p m)) :
    PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.targetAct a c) =
      PositiveTarget.augmentation ℤ (Vertex p m) c :=
  augmentation_map (LabelChainMap.targetShift a)
    (SignedTargetOrbits.targetShift_injective a) c

theorem augmentation_totalNorm [NeZero p] (hp : p.Prime)
    (c : Total p m alpha) :
    PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion
          (SignedTargetOrbits.actualTotalNorm hp c)) =
      (p : ℤ) * PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion c) := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm hp]
  change PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion
        (SignedTargetOrbits.geometricTotalNorm c)) = _
  change PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion
        ((∑ a : ZMod p, SignedTargetOrbits.totalTargetAct a) c)) = _
  rw [LinearMap.sum_apply, map_sum, map_sum]
  simp_rw [SignedTargetOrbits.totalInclusion_targetAct,
    augmentation_targetAct]
  simp

end

end Erdos780Core

end

/-! ### Upstream module `ErdosProblems/Erdos750/ColorObstruction.lean` -/

section
/-!
# The coloring obstruction for signed biclique chains

A proper `k`-coloring maps signed biclique faces to the crosspolytope on
`k` colors. The existing integral cyclic-resolution descent applies to its
free antipodal action. Normalization kills every simplex of length `k+1`.
-/

namespace Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section
universe u
variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

local instance : LinearOrder (ZMod 2 × Fin k) := LabelChainMap.targetLinearOrder

lemma linearMap_mem {A M : Type*} [AddCommGroup M]
    (L : Chain A →ₗ[ℤ] M) (S : Submodule ℤ M) {P : List A → Prop}
    (hL : ∀ l, P l → L (basis l) ∈ S) {c : Chain A} (hc : Supported P c) :
    L c ∈ S := by
  have he : L c = ∑ l ∈ c.support, c l • L (basis l) := by
    calc
      L c = L (c.sum Finsupp.single) := congrArg L (Finsupp.sum_single c).symm
      _ = _ := by
        simp only [Finsupp.sum, map_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [show Finsupp.single l (c l) = c l • basis l by simp [basis], map_smul]
  rw [he]
  exact S.sum_mem fun l hl => S.smul_mem _ (hL l (hc l (Finsupp.mem_support_iff.mp hl)))

def colorLabel (C : G.Coloring (Fin k)) : Signed V → ZMod 2 × Fin k :=
  fun x => (x.1, C x.2)

lemma face_same_color {C : G.Coloring (Fin k)} {l : List (Signed V)} (hl : Face G l)
    {a b : Signed V} (ha : a ∈ l) (hb : b ∈ l) (hc : C a.2 = C b.2) : a.1 = b.1 := by
  by_contra hn
  exact C.valid (hl a ha b hb hn) hc

lemma colorFace_allowed (C : G.Coloring (Fin k)) {l : List (Signed V)} (hl : Face G l) :
    AllowedFaces.IsAllowed k (l.map (colorLabel C)).toFinset := by
  intro j
  simp only [AllowedFaces.capacity, if_pos j.isLt]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, haj⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbj⟩ := Finset.mem_filter.mp hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have hcol : C x.2 = C y.2 := haj.trans hbj.symm
  exact Prod.ext (face_same_color hl hx hy hcol) hcol

lemma colorList_allowed (C : G.Coloring (Fin k)) {l : List (Signed V)} (hl : Face G l) :
    PositiveTarget.labelLists (colorLabel C) (basis l) ∈ AllowedComplex.PositiveAllowed 2 k k := by
  rw [PositiveTarget.labelLists_basis]
  obtain ⟨z, hz⟩ := AllowedComplex.labelList_eq_smul_single_toFinset (colorLabel C) l
  rw [hz]
  change TargetChains.positiveInclusion ℤ _
    (TargetChains.projectPositive ℤ _ (z • Finsupp.single _ 1)) ∈
      AllowedFaces.allowedChains ℤ 2 k k
  rw [TargetChains.positiveInclusion_projectPositive]
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    rw [AllowedFaces.mem_allowedChains]
    intro s hs
    have he := ((Finsupp.mem_support_single _ _ _).mp hs).1
    rw [he]
    convert colorFace_allowed C hl using 1
    ext x
    simp only [List.mem_toFinset]
  · exact AllowedDescent.single_empty_mem_allowed _

lemma colorChain_allowed (C : G.Coloring (Fin k)) {c : Chain (Signed V)}
    (hc : Supported (Face G) c) :
    PositiveTarget.labelLists (colorLabel C) c ∈ AllowedComplex.PositiveAllowed 2 k k :=
  linearMap_mem _ _ (fun _ hl => colorList_allowed C hl) hc

def colorLift (C : G.Coloring (Fin k)) (c : Chain (Signed V)) (hc : Supported (Face G) c) :
    TargetOrbits.TotalChain 2 k k :=
  AllowedComplex.totalChainEquivPositiveAllowed.symm
    ⟨PositiveTarget.labelLists (colorLabel C) c, colorChain_allowed C hc⟩

lemma colorLift_inclusion (C : G.Coloring (Fin k)) (c : Chain (Signed V))
    (hc : Supported (Face G) c) :
    SignedTargetOrbits.totalInclusion (colorLift C c hc) =
      PositiveTarget.labelLists (colorLabel C) c := by
  rw [← AllowedDescent.equiv_coe_eq_totalInclusion]
  simp [colorLift]

lemma colorList_eq_zero (C : G.Coloring (Fin k)) {l : List (Signed V)}
    (hl : Face G l) (hk : k < l.length) : TargetBridge.labelList (colorLabel C) l = 0 := by
  apply TargetBridge.labelList_eq_zero_of_repeated
  intro hinj
  have hcinj : Function.Injective (fun i : Fin l.length => C (l.get i).2) := by
    intro i j hij
    apply hinj
    exact Prod.ext (face_same_color hl (List.get_mem ..) (List.get_mem ..) hij) hij
  have hcard := Fintype.card_le_of_injective _ hcinj
  simp only [Fintype.card_fin] at hcard
  omega

lemma colorChain_eq_zero (C : G.Coloring (Fin k)) {n : ℕ} {c : Chain (Signed V)}
    (hc : Supported (Good G n) c) (hn : k < n) :
    PositiveTarget.labelLists (colorLabel C) c = 0 := by
  apply (Submodule.mem_bot ℤ).mp
  refine linearMap_mem _ ⊥ (P := Good G n) ?_ hc
  intro l hl
  rw [PositiveTarget.labelLists_basis,
    colorList_eq_zero C hl.1 (by have he := hl.2; omega), map_zero]
  exact Submodule.zero_mem _

lemma colorList_flip (C : G.Coloring (Fin k)) (l : List (Signed V)) :
    TargetBridge.labelList (colorLabel C) (l.map flip) =
      TargetChains.map (LabelChainMap.targetShift 1) (TargetBridge.labelList (colorLabel C) l) := by
  apply (TargetChains.toExterior ℤ (ZMod 2 × Fin k)).injective
  rw [TargetChains.toExterior_map]
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, TargetBridge.toExterior_labelList_cons, map_mul,
      ExteriorAlgebra.map_apply_ι, TargetChains.vertexMap_single, ih]
    congr 3
    simp [colorLabel, flip, LabelChainMap.targetShift, add_comm]

lemma colorChain_flip (C : G.Coloring (Fin k)) (c : Chain (Signed V)) :
    PositiveTarget.labelLists (colorLabel C) (swap c) =
      SignedTargetOrbits.targetAct 1 (PositiveTarget.labelLists (colorLabel C) c) := by
  have he : TargetBridge.labelLists (colorLabel C) (swap c) =
      TargetChains.map (LabelChainMap.targetShift 1)
        (TargetBridge.labelLists (colorLabel C) c) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp only [swap, map_smul, mapVertices_basis, TargetBridge.labelLists_basis, colorList_flip]
  change TargetChains.projectPositive ℤ _ (TargetBridge.labelLists (colorLabel C) (swap c)) = _
  rw [he]
  exact (TargetChains.projectPositive_map_projectPositive
    (LabelChainMap.targetShift 1) (TargetBridge.labelLists (colorLabel C) c)).symm

lemma colorChain_augmentation (C : G.Coloring (Fin k)) {c : Chain (Signed V)}
    (hc : boundary c = basis []) :
    PositiveTarget.augmentation ℤ _ (PositiveTarget.labelLists (colorLabel C) c) = 1 := by
  change TargetChains.boundary ℤ _ (TargetChains.positiveInclusion ℤ _
    (TargetChains.projectPositive ℤ _ (TargetBridge.labelLists (colorLabel C) c))) ∅ = 1
  rw [TargetChains.boundary_projectPositive, TargetBridge.labelLists_boundary, hc,
    TargetBridge.labelLists_basis, PositiveTarget.labelList_nil_eq_single_empty]
  simp

lemma targetAct_zero (y : PositiveTarget.Chain ℤ (ZMod 2 × Fin k)) :
    SignedTargetOrbits.targetAct 0 y = y := by
  have hf : LabelChainMap.targetShift (p := 2) (m := k) 0 = id := by
    funext x
    simp [LabelChainMap.targetShift]
  have hm (z : TargetChains.FullChain ℤ (ZMod 2 × Fin k)) :
      TargetChains.map (id : ZMod 2 × Fin k → _) z = z := by
    apply (TargetChains.toExterior ℤ (ZMod 2 × Fin k)).injective
    rw [TargetChains.toExterior_map]
    have hv : TargetChains.vertexMap (R := ℤ) (id : ZMod 2 × Fin k → _) = LinearMap.id := by
      ext x
      simp [TargetChains.vertexMap]
    rw [hv]
    simp
  change TargetChains.projectPositive ℤ _
    (TargetChains.map (LabelChainMap.targetShift 0) (TargetChains.positiveInclusion ℤ _ y)) = y
  rw [hf, hm, TargetChains.projectPositive_inclusion]

lemma totalInclusion_norm_two (x : TargetOrbits.TotalChain 2 k k) :
    SignedTargetOrbits.totalInclusion (SignedTargetOrbits.actualTotalNorm (by decide) x) =
      SignedTargetOrbits.targetAct 1 (SignedTargetOrbits.totalInclusion x) +
        SignedTargetOrbits.totalInclusion x := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm]
  change SignedTargetOrbits.totalInclusion
    ((∑ a : ZMod 2, SignedTargetOrbits.totalTargetAct a) x) = _
  rw [LinearMap.sum_apply, map_sum]
  simp_rw [SignedTargetOrbits.totalInclusion_targetAct]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  simp [targetAct_zero, add_comm]

lemma colorLift_op_inclusion (C : G.Coloring (Fin k)) (c : Chain (Signed V))
    (hc : Supported (Face G) c) (i : ℕ) :
    SignedTargetOrbits.totalInclusion
        ((AllowedDescent.datum (p := 2) (m := k) (alpha := k) (by decide)).op i
          (colorLift C c hc)) =
      PositiveTarget.labelLists (colorLabel C) (op i c) := by
  by_cases hi : Odd i
  · change SignedTargetOrbits.totalInclusion
      ((if Odd i then SignedTargetOrbits.actualTotalTau
        else SignedTargetOrbits.actualTotalNorm (by decide)) (colorLift C c hc)) = _
    rw [if_pos hi]
    change SignedTargetOrbits.totalInclusion
      (SignedTargetOrbits.actualTotalAct (colorLift C c hc) - colorLift C c hc) = _
    rw [map_sub, SignedTargetOrbits.totalInclusion_actualTotalAct, colorLift_inclusion]
    simp [op, hi, ← colorChain_flip]
  · change SignedTargetOrbits.totalInclusion
      ((if Odd i then SignedTargetOrbits.actualTotalTau
        else SignedTargetOrbits.actualTotalNorm (by decide)) (colorLift C c hc)) = _
    rw [if_neg hi, totalInclusion_norm_two, colorLift_inclusion]
    simp [op, hi, ← colorChain_flip]

lemma hasResolution_not_colorable {d : ℕ} (h : HasResolution G d) (hkd : k ≤ d) :
    ¬G.Colorable k := by
  rintro ⟨C⟩
  obtain ⟨c, hc, hzero, hrel⟩ := h
  let lift (i : ℕ) (hi : i ≤ d) := colorLift C (c i)
    ((hc i hi).mono (fun _ h => h.1))
  let y : ℕ → TargetOrbits.TotalChain 2 k k := fun i =>
    if hi : i ≤ k then lift i (hi.trans hkd) else 0
  let P := AllowedDescent.datum (p := 2) (m := k) (alpha := k) (by decide)
  have hy (i : ℕ) (hi : i ≤ k) : y i = lift i (hi.trans hkd) := dif_pos hi
  have htop : y k = 0 := by
    rw [hy k le_rfl]
    apply SignedTargetOrbits.totalInclusion_injective
    rw [map_zero, colorLift_inclusion]
    exact colorChain_eq_zero C (hc k hkd) (by omega)
  have hyzero {i : ℕ} (hi : k ≤ i) : y i = 0 := by
    rcases hi.eq_or_lt with rfl | hi
    · exact htop
    · simp [y, show ¬i ≤ k by omega]
  have hyrel (i : ℕ) : P.boundary (y (i + 1)) = P.op (i + 1) (y i) := by
    by_cases hik : i < k
    · rw [hy (i + 1) (by omega), hy i (by omega)]
      apply SignedTargetOrbits.totalInclusion_injective
      change SignedTargetOrbits.totalInclusion
        (AllowedDescent.totalBoundary (lift (i + 1) (by omega))) = _
      rw [AllowedDescent.totalInclusion_boundary, colorLift_inclusion,
        PositiveTarget.labelLists_boundary, hrel i (by omega), colorLift_op_inclusion]
    · rw [hyzero (by omega : k ≤ i + 1), hyzero (by omega : k ≤ i)]
      simp
  obtain ⟨z₁, z₀, hz⟩ := P.bottom_decomposition y hyrel k htop
  have haug : PositiveTarget.augmentation ℤ _
      (SignedTargetOrbits.totalInclusion (y 0)) = 1 := by
    rw [hy 0 (Nat.zero_le _), colorLift_inclusion]
    exact colorChain_augmentation C hzero
  have heq : (1 : ℤ) = 2 * PositiveTarget.augmentation ℤ _
      (SignedTargetOrbits.totalInclusion z₀) := by
    change y 0 = AllowedDescent.totalBoundary z₁ +
      SignedTargetOrbits.actualTotalNorm (by decide) z₀ at hz
    rw [← haug, hz, map_add, map_add, AllowedDescent.totalInclusion_boundary,
      PositiveTarget.augmentation_boundary, zero_add, Erdos780Core.augmentation_totalNorm]
    rfl
  omega

end
end Chains

end

/-! ### Upstream module `ErdosProblems/Erdos750/Stiebitz.lean` -/

section
/-!
# Stiebitz's theorem for recursively constructed generalized Mycielski graphs

The lower bound is proved by integral signed-biclique chains. The cylinder
contraction extends the chain invariant at each step, and cyclic-resolution
exactness gives the obstruction to a coloring with too few colors.
-/

open SimpleGraph Chains

universe u

lemma recursivelyBuilt_hasResolution : ∀ (r : ℕ) {V : Type u} (G : SimpleGraph V),
    IsRecursivelyBuiltMr r G → ∃ d, r = d + 1 ∧ HasResolution G d := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro V G hG
    cases r with
    | zero => exact hG.elim
    | succ r =>
      cases r with
      | zero => exact hG.elim
      | succ r =>
        cases r with
        | zero =>
          obtain ⟨e⟩ := hG
          exact ⟨1, rfl, hasResolution_complete_two.map e.symm.toHom⟩
        | succ r =>
          obtain ⟨W, H, s, hs, hH, ⟨e⟩⟩ := hG
          obtain ⟨d, hd, hc⟩ := ih (r + 2) (by omega) H hH
          refine ⟨d + 1, by omega, ?_⟩
          exact (hasResolution_genMyc hc (by omega)).map e.symm.toHom

/-- **Stiebitz's lower bound**, with no mathematical assumptions. -/
theorem stiebitz_lower_bound {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (hG : IsRecursivelyBuiltMr r G) : (r : ℕ∞) ≤ G.chromaticNumber := by
  obtain ⟨d, rfl, hd⟩ := recursivelyBuilt_hasResolution r G hG
  by_contra h
  have hle : G.chromaticNumber ≤ (d : ℕ∞) := by
    have hlt := lt_of_not_ge h
    exact ENat.lt_natCast_add_one_iff.mp (by simpa using hlt)
  exact hasResolution_not_colorable hd le_rfl (chromaticNumber_le_iff_colorable.mp hle)

end

/-! ### Upstream module `ErdosProblems/Erdos750.lean` -/

section
/-
Erdős Problem 750: almost-half independent sets at infinite chromatic number.

The local odd-cycle-transversal construction follows Chojecki and GPT-5.5 Pro,
https://www.ulam.ai/research/erdos750.pdf.
Its conditional Lean formalization was posted by paws (Shashi456):
https://www.erdosproblems.com/forum/thread/750#post-6255
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean

The originally assumed Stiebitz bound is replaced here by the theorem proved in
the `Stiebitz` module above. No computational limits are increased.
-/

open SimpleGraph Filter
open scoped NNReal

/-- The stronger OCT form: every nondecreasing unbounded profile occurs in
a graph of infinite chromatic number. -/
theorem infinite_chromatic_local_oct (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card :=
  Conditional.infinite_chromatic_local_oct stiebitz_lower_bound g hg_mono hg_top

/-- **Erdős Problem 750**, in the real-valued independence-bound form. -/
theorem erdos_750_independence :
    ∀ (f : ℕ → ℝ≥0), Tendsto f atTop atTop →
      ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 - (f m : ℝ) ≤ (I.ncard : ℝ) :=
  Conditional.erdos_750_independence stiebitz_lower_bound

end

/-! ### Final statement -/

section

open SimpleGraph Filter

/-- **Erdős Problem 750.** For every `f : ℕ → ℝ≥0` tending to infinity there is a graph of
infinite chromatic number in which every `m`-vertex subgraph contains an independent set
of size at least `m / 2 - f m`. -/
theorem erdos_750 :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : NNReal) / 2 - f m ≤ (I.ncard : NNReal) :=
  Conditional.erdos_750_independence_FC_form stiebitz_lower_bound

end

#print axioms erdos_750
-- 'Erdos750.erdos_750' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos750
