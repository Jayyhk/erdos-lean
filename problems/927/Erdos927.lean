/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/

/-
# Erdős Problem 927 — Disproof

Erdős Problem 927 asks whether
  g(n) = n − ⌊log₂ n⌋ − log*(n) + O(1),
where g(n) is the maximum number of different sizes of maximal cliques in a
graph on n vertices.

Spencer (1971) answered this negatively by constructing, for each sufficiently
large N, a graph on N vertices with at least N − ⌊log₂ N⌋ − 4 different
maximal clique sizes. Since log*(n) → ∞, this contradicts the conjectured
formula.

Reference: J. H. Spencer, "On cliques in graphs", Israel J. Math. 9 (1971),
419–421.
-/

import Mathlib

namespace Erdos927

open Classical Finset SimpleGraph

/-
# Erdős Problem 927 — Definitions

This file contains the basic definitions needed for the formalization of
Spencer's disproof of Erdős Problem 927.

## Main definitions

* `IsMaximalClique` — A maximal clique in a simple graph (a complete subgraph
  that cannot be extended).
* `maximalCliqueSizes` — The set of sizes of maximal clique sizes in a graph.
* `g` — The maximum number of different maximal clique sizes in a graph on n vertices.
* `logStar` — The iterated logarithm function.
-/


open Classical Finset SimpleGraph


/-! ## Maximal Cliques -/

/-- A finset `s` is a maximal clique of `G` if `s` is a clique and no proper superset
  of `s` (as a finset) is a clique. -/
def IsMaximalClique {α : Type*} [DecidableEq α] (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique (↑s : Set α) ∧ ∀ t : Finset α, G.IsClique (↑t : Set α) → s ⊆ t → t = s

/-- The set of sizes of maximal cliques in a graph. -/
noncomputable def maximalCliqueSizes {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Finset ℕ :=
  ((Finset.univ (α := Finset α)).filter (fun s => IsMaximalClique G s)).image Finset.card

/-- `g n` is the maximum number of different sizes of maximal cliques
  that can occur in a graph on `n` vertices. -/
noncomputable def g (n : ℕ) : ℕ :=
  Finset.sup (Finset.univ (α := SimpleGraph (Fin n)))
    (fun G => (maximalCliqueSizes G).card)

/-- Any specific graph on `Fin n` gives a lower bound on `g n`. -/
lemma le_g_of_graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    (maximalCliqueSizes G).card ≤ g n :=
  Finset.le_sup (f := fun G => (maximalCliqueSizes G).card) (Finset.mem_univ G)

/-
A graph on any type with cardinality `n` gives a lower bound on `g n`.
  This lets us work with convenient vertex types rather than `Fin n`.
-/
set_option maxHeartbeats 800000 in
lemma g_ge_of_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {n : ℕ} (hn : Fintype.card α = n) :
    (maximalCliqueSizes G).card ≤ g n := by
  obtain ⟨e⟩ : ∃ e : α ≃ Fin n, True := ⟨Fintype.equivFinOfCardEq hn, trivial⟩;
  convert le_g_of_graph ( SimpleGraph.comap e.symm G ) using 1;
  fapply Finset.card_bij;
  use fun a ha => a;
  · simp +decide [ maximalCliqueSizes ];
    intro a ha;
    refine' ⟨ Finset.image e a, _, _ ⟩;
    · constructor;
      · intro x hx y hy hxy;
        obtain ⟨ u, hu, rfl ⟩ := Finset.mem_image.mp hx; obtain ⟨ v, hv, rfl ⟩ :=
          Finset.mem_image.mp hy; have := ha.1 hu hv; aesop;
      · intro t ht ht'; have := ha.2 ( Finset.image e.symm t ) ;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
        rw [ ← this ];
        · simp +decide [ Finset.ext_iff ];
        · exact Set.Pairwise.image ht;
        · exact fun x hx => ⟨ e x, ht' x hx, e.symm_apply_apply x ⟩;
    · rw [ Finset.card_image_of_injective _ e.injective ];
  · grind;
  · unfold maximalCliqueSizes;
    simp +decide [ IsMaximalClique ];
    rintro b x hx₁ hx₂ rfl;
    refine' ⟨ Finset.image e.symm x, _, _ ⟩ <;>
      simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
    refine' ⟨ _, _ ⟩;
    · intro a ha b hb hab;
      specialize hx₁ ( show e a ∈ x from by aesop ) ( show e b ∈ x from by aesop ) ; aesop;
    · intro t ht ht'; specialize hx₂ ( Finset.image e t ) ;
      simp_all +decide [ Finset.subset_iff, SimpleGraph.IsClique ] ;
      rw [ ← hx₂ ];
      · simp +decide [ Finset.ext_iff ];
      · intro a ha b hb hab; aesop;
      · exact fun a ha => ⟨ e.symm a, ht' a ha, e.apply_symm_apply a ⟩

/-- If for each `k ∈ sizes` there is a maximal clique of size `k`,
  then `sizes ⊆ maximalCliqueSizes G`. -/
lemma maximalCliqueSizes_card_ge {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {sizes : Finset ℕ}
    (h : ∀ k ∈ sizes, ∃ s : Finset α, IsMaximalClique G s ∧ s.card = k) :
    sizes ⊆ maximalCliqueSizes G := by
  intro k hk
  obtain ⟨s, hs, rfl⟩ := h k hk
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)

/-! ## Iterated Logarithm -/

/-- The iterated logarithm (log-star) function. `logStar n` is the number of times
  one must take `Nat.log 2` before reaching a value ≤ 1. -/
def logStar : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => logStar (Nat.log 2 (n + 2)) + 1
termination_by n => n
decreasing_by
  simp_wf
  have : Nat.log 2 (n + 2) < n + 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    exact Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2)
  omega

@[simp] lemma logStar_zero : logStar 0 = 0 := by unfold logStar; rfl
@[simp] lemma logStar_one : logStar 1 = 0 := by unfold logStar; rfl

lemma logStar_eq_succ {n : ℕ} (hn : n ≥ 2) :
    logStar n = logStar (Nat.log 2 n) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [logStar]

/-
`logStar` is monotone.
-/
lemma logStar_mono {m n : ℕ} (h : m ≤ n) : logStar m ≤ logStar n := by
  induction' n using Nat.strongRecOn with n ih generalizing m;
  rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m );
  all_goals norm_num [ logStar_eq_succ ] at *;
  convert ih _ _ _ using 1;
  · refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ ) <;> norm_num;
    exact Nat.lt_two_pow_self;
  · exact Nat.log_mono_right ( by linarith )

/-
`logStar` is unbounded: for any `C`, there exists `n` with `logStar n > C`.
-/
lemma logStar_unbounded : ∀ C : ℕ, ∃ n : ℕ, C < logStar n := by
  intro C;
  induction' C with C ih;
  · exact ⟨ 2, by rw [logStar_eq_succ (by norm_num)]; simp ⟩;
  · obtain ⟨ n, hn ⟩ := ih;
    use 2^(n+1);
    rw [ logStar_eq_succ ] <;> norm_num [ Nat.log_pow ];
    · exact hn.trans_le ( logStar_mono ( Nat.le_succ _ ) );
    · exact le_self_pow ( by norm_num ) ( Nat.succ_ne_zero _ )

/-
# Binary Expansion Helper

For any α < 2^m, there exists a subset S of Fin m whose sum of 2^i equals α.
-/

open Finset


/-
Every natural number less than 2^m can be expressed as a sum of distinct
powers of 2 with exponents in {0, ..., m-1}.
-/
lemma binary_expansion (m α : ℕ) (h : α < 2 ^ m) :
    ∃ S : Finset (Fin m), ∑ i ∈ S, 2 ^ (i : ℕ) = α := by
  induction' m with m ih generalizing α;
  · aesop;
  · by_cases h_case : α < 2 ^ m;
    · exact Exists.elim ( ih α h_case ) fun S hS => ⟨ S.image ( Fin.castSucc ),
        by simpa [ Finset.sum_image ] using hS ⟩;
    · -- Since α ≥ 2^m, we can write α as 2^m + β for some β < 2^m.
      obtain ⟨β, hβ⟩ : ∃ β, α = 2 ^ m + β ∧ β < 2 ^ m := by
        exact ⟨ α - 2 ^ m, by rw [ Nat.add_sub_cancel' ( le_of_not_gt h_case ) ],
          by rw [ tsub_lt_iff_left ( le_of_not_gt h_case ) ] ; rw [ pow_succ' ] at h; linarith ⟩;
      obtain ⟨ S, hS ⟩ := ih β hβ.2;
      use Finset.image ( fun i : Fin m => Fin.castSucc i ) S ∪ { Fin.last m } ;
      simp_all +decide [ Finset.sum_image ]

/-
The sum of all 2^i for i in Fin m equals 2^m - 1.
-/
lemma sum_pow_two_Fin (m : ℕ) :
    ∑ i : Fin m, 2 ^ (i : ℕ) = 2 ^ m - 1 := by
  induction' m with m ih;
  · rfl;
  · norm_num [ Fin.sum_univ_castSucc, pow_succ', ih ];
    grind +qlia

/-
The sum of (2^i + 1) for i in Fin m equals 2^m - 1 + m.
-/
lemma sum_cSize_Fin (m : ℕ) :
    ∑ i : Fin m, (2 ^ (i : ℕ) + 1) = 2 ^ m - 1 + m := by
  simp +arith +decide [ Finset.sum_add_distrib, sum_pow_two_Fin ]

/-
# Spencer's Graph — Definition and Key Properties

This file defines the vertex type, edge relation, and key parameters
for Spencer's graph construction.

The graph has five types of vertices:
- `y i` : selector vertices (i < n)
- `yStar` : special selector
- `c i j` : elements of C_i (position sets)
- `cStar j` : elements of C* (recursive structure)
- `z` : root for small cliques
-/


open Classical Finset SimpleGraph


/-! ## Key Parameters -/

/-- Auxiliary function computing the total size of C*.
  For parameter `m`, computes the total from the recursive sequence starting at `m`. -/
def spAux : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | (m + 3) =>
    let next := Nat.log 2 (m + 2) + 1
    if next ≤ 2 then 2 ^ next + next - 1 + 1
    else 2 ^ next + next - 1 + spAux next
termination_by m => m
decreasing_by
  simp_wf
  have : Nat.log 2 (m + 2) < m + 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    exact Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2)
  omega

/-- The size of C* for parameter `n`. -/
def spA (n : ℕ) : ℕ := spAux n

/-- Total vertex count. -/
def spN (n : ℕ) : ℕ := n + 1 + (2 ^ n + n - 1) + spA n + 1

/-- B = size of the largest clique. -/
def spB (n : ℕ) : ℕ := 2 ^ n + n - 1 + spA n

/-- spA n ≥ 1 for all n. -/
lemma spAux_pos : ∀ m, 1 ≤ spAux m := by
  intro m
  induction' m using Nat.strongRecOn with m ih
  match m with
  | 0 | 1 | 2 => simp [spAux]
  | m + 3 =>
    simp only [spAux]
    have hlog : Nat.log 2 (m + 2) + 1 < m + 3 := by
      have := Nat.log_lt_of_lt_pow (show m + 2 ≠ 0 by omega)
        (Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2))
      omega
    split
    · have : 2 ^ (Nat.log 2 (m + 2) + 1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
      omega
    · have := ih _ hlog; omega

lemma spA_pos (n : ℕ) : 1 ≤ spA n := spAux_pos n

/-- Explicit evaluation of `spA 16 = 25`, used to discharge a small case in
`spencer_log`. -/
lemma spA_16_eq : spA 16 = 25 := by
  show spAux 16 = 25
  have h15 : Nat.log 2 15 = 3 := by
    rw [Nat.log_eq_iff] <;> norm_num
  have h3 : Nat.log 2 3 = 1 := by
    rw [Nat.log_eq_iff] <;> norm_num
  have h_spAux_4 : spAux 4 = 6 := by
    show spAux (1 + 3) = 6
    unfold spAux
    simp [h3]
  show spAux (13 + 3) = 25
  unfold spAux
  simp [h15, h_spAux_4]

/-- The vertex count satisfies N ≥ 2 for n ≥ 2. -/
lemma spN_ge_two (n : ℕ) (hn : n ≥ 2) : spN n ≥ 2 := by
  unfold spN; omega

/-- n ≤ spN n. -/
lemma le_spN (n : ℕ) : n ≤ spN n := by
  unfold spN; omega

/-- The waste equation: spN n = n + 4 + (spB n - 2) for n ≥ 2. -/
lemma spN_eq (n : ℕ) (hn : n ≥ 2) : spN n = n + 4 + (spB n - 2) := by
  unfold spN spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-- spB n ≥ 3 for n ≥ 2. -/
lemma spB_ge_three (n : ℕ) (hn : n ≥ 2) : spB n ≥ 3 := by
  unfold spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-! ## Vertex Type -/

/-- Size of C_i (0-indexed): |C_i| = 2^i + 1. -/
def cSize (i : ℕ) : ℕ := 2 ^ i + 1

/-- The vertex type for Spencer's graph. -/
inductive SpVtx (n A : ℕ) where
  | y (i : Fin n)
  | yStar
  | c (i : Fin n) (j : Fin (cSize i))
  | cStar (j : Fin A)
  | z
  deriving DecidableEq

instance SpVtx.instFintype {n A : ℕ} : Fintype (SpVtx n A) := by
  have equiv : SpVtx n A ≃
      (Fin n ⊕ Unit ⊕ (Σ i : Fin n, Fin (cSize i)) ⊕ Fin A ⊕ Unit) := {
    toFun := fun v => match v with
      | .y i => Sum.inl i
      | .yStar => Sum.inr (Sum.inl ())
      | .c i j => Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩))
      | .cStar j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
      | .z => Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))
    invFun := fun v => match v with
      | Sum.inl i => .y i
      | Sum.inr (Sum.inl ()) => .yStar
      | Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩)) => .c i j
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => .cStar j
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) => .z
    left_inv := by intro v; cases v <;> simp
    right_inv := by intro v; rcases v with _ | _ | ⟨⟨_, _⟩⟩ | _ | _ <;> simp
  }
  exact Fintype.ofEquiv _ equiv.symm

/-! ## Edge Relation -/

/-- Whether y-vertex `i` is a "generic" selector (i < n/2). -/
def isGeneric (n : ℕ) (i : Fin n) : Bool := decide ((i : ℕ) < n / 2)

/-- The recursive sequence for the w/v structure.
  `recSeq n 0 = n`, subsequent values are roughly `log₂` of previous. -/
def recSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if recSeq n k ≤ 2 then 2 else Nat.log 2 (recSeq n k - 1) + 1

/-- Find (level, position) for a w-vertex given its offset from n/2. -/
def wLookup (n offset level fuel : ℕ) : Option (ℕ × ℕ) :=
  match fuel with
  | 0 => if offset = 0 then some (level, 0) else none
  | fuel + 1 =>
    let nℓ := recSeq n (level + 1)
    if offset < nℓ then some (level, offset)
    else wLookup n (offset - nℓ) (level + 1) fuel

/-- Find (position, sub-index) within a v-level. -/
def findVPos (offset pos fuel : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (pos, offset)
  | fuel + 1 =>
    let sz := 2 ^ pos + 1
    if offset < sz then (pos, offset)
    else findVPos (offset - sz) (pos + 1) fuel

/-- Size of v-vertices at a given level. -/
def levelVSize (n level : ℕ) : ℕ :=
  let nℓ := recSeq n (level + 1)
  2 ^ nℓ + nℓ - 1

/-- Find (level, position, sub-index) for a C*-vertex given its index. -/
def vLookup (n offset level fuel : ℕ) : ℕ × ℕ × ℕ :=
  match fuel with
  | 0 =>
    let nℓ := recSeq n (level + 1)
    let (p, q) := findVPos offset 0 nℓ
    (level, p, q)
  | fuel + 1 =>
    let lvlSz := levelVSize n level
    if offset < lvlSz then
      let nℓ := recSeq n (level + 1)
      let (p, q) := findVPos offset 0 nℓ
      (level, p, q)
    else
      vLookup n (offset - lvlSz) (level + 1) fuel

/-- Whether a non-generic y-vertex (w-vertex) `i` is adjacent to C* vertex `j`.
  This encodes the recursive w/v structure:
  w at (level, pos) is adjacent to v at (level', pos', _) iff level = level' and pos ≠ pos'. -/
def wvAdj (n : ℕ) (i : Fin n) (j : Fin (spA n)) : Bool :=
  let wOffset := (i : ℕ) - n / 2
  match wLookup n wOffset 0 n with
  | none => false
  | some (wl, wp) =>
    let (vl, vp, _) := vLookup n (j : ℕ) 0 n
    wl == vl && wp != vp

/-- Spencer's graph adjacency relation. -/
def spAdj (n : ℕ) : SpVtx n (spA n) → SpVtx n (spA n) → Prop := fun u v =>
  u ≠ v ∧ match u, v with
  -- y-y and y-yStar: all pairwise adjacent
  | .y _, .y _ | .y _, .yStar | .yStar, .y _ => True
  -- C-C, C-C*, C*-C*: all pairwise adjacent
  | .c _ _, .c _ _ | .c _ _, .cStar _ | .cStar _, .c _ _ | .cStar _, .cStar _ => True
  -- C_i ~ y_k iff k ≠ i
  | .c i _, .y k | .y k, .c i _ => k ≠ i
  -- C ~ yStar: adjacent
  | .c _ _, .yStar | .yStar, .c _ _ => True
  -- y_i ~ cStar_j: generic selectors always; w-vertices via wvAdj
  | .y i, .cStar j | .cStar j, .y i =>
    if isGeneric n i then True else wvAdj n i j = true
  -- yStar is NOT adjacent to C*
  | .yStar, .cStar _ | .cStar _, .yStar => False
  -- z ~ y_i: only if i is a w-vertex (not generic)
  | .z, .y i | .y i, .z => !(isGeneric n i)
  -- z is NOT adjacent to yStar or C
  | .z, .yStar | .yStar, .z | .z, .c _ _ | .c _ _, .z => False
  -- z IS adjacent to all C*
  | .z, .cStar _ | .cStar _, .z => True
  -- Self
  | .yStar, .yStar | .z, .z => False

/-- Spencer's adjacency is symmetric. -/
lemma spAdj_symm (n : ℕ) : Symmetric (spAdj n) := by
  intro u v ⟨hne, hadj⟩
  refine ⟨hne.symm, ?_⟩
  cases u <;> cases v <;> simp_all

/-- Spencer's graph as a SimpleGraph. -/
def spGraph (n : ℕ) : SimpleGraph (SpVtx n (spA n)) where
  Adj := spAdj n
  symm := spAdj_symm n
  loopless := ⟨fun v => by intro ⟨h, _⟩; exact h rfl⟩

/-! ## Key Properties -/

/-
The cardinality of the Spencer vertex type equals spN n.
-/
lemma spVtx_card (n : ℕ) (_hn : n ≥ 2) :
    Fintype.card (SpVtx n (spA n)) = spN n := by
  unfold spN;
  rw [ show Fintype.card ( SpVtx n ( spA n ) ) =
      Fintype.card ( Fin n ⊕ Unit ⊕ ( Σ i : Fin n, Fin ( cSize i ) ) ⊕ Fin ( spA n ) ⊕ Unit ) by
        convert Fintype.card_congr ( Equiv.ofBijective _ ⟨ _, _ ⟩ );
        exact fun v => match v with
          | .y i => Sum.inl i | .yStar => Sum.inr ( Sum.inl () )
          | .c i j => Sum.inr ( Sum.inr ( Sum.inl ⟨ i, j ⟩ ) )
          | .cStar j => Sum.inr ( Sum.inr ( Sum.inr ( Sum.inl j ) ) )
          | .z => Sum.inr ( Sum.inr ( Sum.inr ( Sum.inr () ) ) );
        · intro v w; aesop;
        · intro x;
          rcases x with ( x | x | x | x | x ) <;> [ exact ⟨ SpVtx.y x, rfl ⟩ ;
            exact ⟨ SpVtx.yStar, rfl ⟩ ; exact ⟨ SpVtx.c x.1 x.2, rfl ⟩ ;
            exact ⟨ SpVtx.cStar x, rfl ⟩ ; exact ⟨ SpVtx.z, rfl ⟩ ] ];
  simp +arith +decide [ Fintype.card_sigma, cSize ];
  exact eq_tsub_of_add_eq ( by
  exact Nat.recOn n ( by norm_num )
    fun n ih => by norm_num [ Fin.sum_univ_castSucc, pow_succ' ] at * ; linarith )

/-
Nat.log 2 (spN n) = n for n ≥ 16.
-/
set_option maxHeartbeats 1600000 in
theorem spencer_log (n : ℕ) (hn : n ≥ 16) : Nat.log 2 (spN n) = n := by
  rw [ Nat.log_eq_iff ] <;> norm_num [ spN ];
  have h_upper : ∀ m ≥ 16, spAux m ≤ 4 * m := by
    intro m hm
    induction' m using Nat.strong_induction_on with m ih;
    rcases m with ( _ | _ | _ | m ) <;> simp +arith +decide [ * ] at hm ⊢;
    unfold spAux; simp +arith +decide [ * ];
    by_cases h₂ : Nat.log 2 (m + 2) + 1 ≥ 16;
    · have := ih ( Nat.log 2 ( m + 2 ) + 1 )
        ( by linarith [ Nat.log_lt_of_lt_pow ( by linarith ) ( show m + 2 < 2 ^ ( m + 2 ) by
                exact Nat.recOn m ( by norm_num ) fun n ihn => by
                  norm_num [ Nat.pow_succ' ] at * ;
                  linarith
              )
            ] ) h₂;
      have := Nat.pow_log_le_self 2 ( by linarith : m + 2 ≠ 0 );
      rcases k : Nat.log 2 ( m + 2 ) with
          ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;>
            simp_all +arith +decide [ Nat.pow_succ' ];
      · grind +splitImp;
      · rename_i k' hk';
        linarith [ Nat.one_le_pow k' 2 zero_lt_two, show k' ≤ 2 ^ k' by
            exact Nat.recOn k' ( by norm_num ) fun n ihn => by
              rw [ pow_succ' ] ;
              linarith [ Nat.one_le_pow n 2 zero_lt_two ]
          ];
    · interval_cases _ : Nat.log 2 ( m + 2 ) + 1 <;> simp_all +decide;
      all_goals rw [ Nat.log_eq_iff ] at * <;> norm_num at *;
      all_goals unfold spAux; simp +arith +decide at *;
      all_goals norm_num [ Nat.log_of_lt ] at *;
      any_goals omega;
      all_goals unfold spAux; simp +arith +decide at *;
      all_goals norm_num [ Nat.log_of_lt ] at * ; omega;
  rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;>
      simp +arith +decide [ Nat.pow_succ' ] at *;
  · rw [spA_16_eq]; decide;
  · linarith! [ h_upper ( n + 17 ) ( by linarith ), show 2 ^ n ≥ n + 1 from Nat.recOn n ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith ]

/-
# Small Clique — Lookup Properties

Properties of wLookup, vLookup, and findVPos needed for the small clique construction.
-/

open Finset SimpleGraph


/-! ## Offset definitions -/

/-- w-vertex offset at level ℓ: sum of recSeq n (i+1) for i = 0,...,ℓ-1. -/
def wOff (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => wOff n ℓ + recSeq n (ℓ + 1)

/-- v-vertex offset at level ℓ: sum of levelVSize n i for i = 0,...,ℓ-1. -/
def vOff (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => vOff n ℓ + levelVSize n ℓ

/-- Position offset within a level: sum of (2^i + 1) for i = 0,...,q-1. -/
def cPosOff : ℕ → ℕ
  | 0 => 0
  | q + 1 => cPosOff q + (2 ^ q + 1)

/-! ## Basic properties -/

@[simp] lemma wOff_zero (n : ℕ) : wOff n 0 = 0 := rfl
@[simp] lemma wOff_succ (n ℓ : ℕ) : wOff n (ℓ + 1) = wOff n ℓ + recSeq n (ℓ + 1) := rfl
@[simp] lemma vOff_zero (n : ℕ) : vOff n 0 = 0 := rfl
@[simp] lemma vOff_succ (n ℓ : ℕ) : vOff n (ℓ + 1) = vOff n ℓ + levelVSize n ℓ := rfl
@[simp] lemma cPosOff_zero_val : cPosOff 0 = 0 := rfl
@[simp] lemma cPosOff_succ_val (q : ℕ) : cPosOff (q + 1) = cPosOff q + (2 ^ q + 1) := rfl

lemma wOff_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : wOff n a ≤ wOff n b := by
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

lemma vOff_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : vOff n a ≤ vOff n b := by
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

lemma cPosOff_mono {a b : ℕ} (h : a ≤ b) : cPosOff a ≤ cPosOff b := by
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

/-- cPosOff k = 2^k - 1 + k -/
lemma cPosOff_eq (k : ℕ) : cPosOff k = 2 ^ k - 1 + k := by
  induction k with
  | zero => simp [cPosOff]
  | succ k ih =>
    simp only [cPosOff_succ_val, ih]
    have h : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    omega

/-- cPosOff (recSeq n (ℓ+1)) = levelVSize n ℓ -/
lemma cPosOff_eq_levelVSize (n ℓ : ℕ) :
    cPosOff (recSeq n (ℓ + 1)) = levelVSize n ℓ := by
  simp only [cPosOff_eq, levelVSize]
  have : 1 ≤ 2 ^ recSeq n (ℓ + 1) := Nat.one_le_pow _ 2 (by norm_num)
  omega

/-- cPosOff is strictly monotone -/
lemma cPosOff_strict_mono {a b : ℕ} (h : a < b) : cPosOff a < cPosOff b := by
  have h1 : cPosOff a + (2^a + 1) ≤ cPosOff b := by
    calc cPosOff a + (2^a + 1) = cPosOff (a + 1) := by simp [cPosOff]
      _ ≤ cPosOff b := cPosOff_mono (by omega)
  have h2 : 2 ^ a + 1 ≥ 2 := by
    have := Nat.one_le_pow a 2 (by norm_num); omega
  omega

/-! ## wLookup correctness -/

/-- wLookup correctness at arbitrary level.
  Starting from `level` with offset = wOff n ℓ - wOff n level + p,
  returns (ℓ, p) if level ≤ ℓ and fuel is sufficient. -/
lemma wLookup_wOff (n ℓ p level fuel : ℕ)
    (hp : p < recSeq n (ℓ + 1))
    (hℓ : level ≤ ℓ)
    (hfuel : ℓ - level < fuel)
    (hwoff_le : wOff n level ≤ wOff n ℓ) :
    wLookup n (wOff n ℓ - wOff n level + p) level fuel = some (ℓ, p) := by
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    simp only [wLookup]
    by_cases h_done : level = ℓ
    · subst h_done; simp [hp]
    · have h_lt : level < ℓ := Nat.lt_of_le_of_ne hℓ h_done
      have hwoff_succ : wOff n (level + 1) ≤ wOff n ℓ :=
        wOff_mono n (by omega)
      have h_ge : ¬ (wOff n ℓ - wOff n level + p < recSeq n (level + 1)) := by
        have : wOff n level + recSeq n (level + 1) = wOff n (level + 1) := rfl
        omega
      simp [h_ge]
      have h_off : wOff n ℓ - wOff n level + p - recSeq n (level + 1)
                 = wOff n ℓ - wOff n (level + 1) + p := by
        have : wOff n level + recSeq n (level + 1) = wOff n (level + 1) := rfl
        omega
      rw [h_off]
      exact ih (level + 1) (by omega) (by omega) hwoff_succ

/-- Main wLookup correctness lemma starting from level 0. -/
theorem wLookup_at_level (n ℓ p : ℕ)
    (hp : p < recSeq n (ℓ + 1))
    (hℓ : ℓ < n)
    (_ : wOff n (ℓ + 1) ≤ n) :
    wLookup n (wOff n ℓ + p) 0 n = some (ℓ, p) := by
  have h1 : wOff n ℓ + p = wOff n ℓ - wOff n 0 + p := by simp
  rw [h1]
  exact wLookup_wOff n ℓ p 0 n hp (Nat.zero_le _) (by omega) (by simp)

/-! ## findVPos correctness -/

/-- findVPos correctness: given offset = cPosOff q - cPosOff pos₀ + s
  with s < 2^q + 1 and pos₀ ≤ q, returns (q, s). -/
lemma findVPos_cPosOff (q s pos₀ fuel : ℕ)
    (hs : s < 2 ^ q + 1)
    (hq : pos₀ ≤ q)
    (hfuel : q - pos₀ < fuel)
    (hcpos : cPosOff pos₀ ≤ cPosOff q) :
    findVPos (cPosOff q - cPosOff pos₀ + s) pos₀ fuel = (q, s) := by
  induction fuel generalizing pos₀ with
  | zero => omega
  | succ f ih =>
    simp only [findVPos]
    by_cases h_done : pos₀ = q
    · subst h_done; simp [hs]
    · have h_lt : pos₀ < q := Nat.lt_of_le_of_ne hq h_done
      have hcpos_succ : cPosOff (pos₀ + 1) ≤ cPosOff q :=
        cPosOff_mono (by omega)
      have h_ge : ¬ (cPosOff q - cPosOff pos₀ + s < 2 ^ pos₀ + 1) := by
        have : cPosOff pos₀ + (2 ^ pos₀ + 1) = cPosOff (pos₀ + 1) := by simp [cPosOff]
        omega
      simp [h_ge]
      have h_off : cPosOff q - cPosOff pos₀ + s - (2 ^ pos₀ + 1)
                 = cPosOff q - cPosOff (pos₀ + 1) + s := by
        have : cPosOff pos₀ + (2 ^ pos₀ + 1) = cPosOff (pos₀ + 1) := by simp [cPosOff]
        omega
      rw [h_off]
      exact ih (pos₀ + 1) (by omega) (by omega) hcpos_succ

/-- findVPos starting from position 0. -/
theorem findVPos_at_pos (q s fuel : ℕ)
    (hs : s < 2 ^ q + 1) (hfuel : q < fuel) :
    findVPos (cPosOff q + s) 0 fuel = (q, s) := by
  have h : cPosOff q + s = cPosOff q - cPosOff 0 + s := by simp
  rw [h]
  exact findVPos_cPosOff q s 0 fuel hs (Nat.zero_le _) (by omega) (by simp)

/-! ## vLookup correctness -/

/-- vLookup correctness at arbitrary level. -/
lemma vLookup_vOff (n ℓ localOff level fuel : ℕ)
    (hloc : localOff < levelVSize n ℓ)
    (hℓ : level ≤ ℓ)
    (hfuel : ℓ - level < fuel)
    (hvoff_le : vOff n level ≤ vOff n ℓ) :
    vLookup n (vOff n ℓ - vOff n level + localOff) level fuel =
    (ℓ, (findVPos localOff 0 (recSeq n (ℓ + 1))).1,
     (findVPos localOff 0 (recSeq n (ℓ + 1))).2) := by
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    simp only [vLookup]
    by_cases h_done : level = ℓ
    · subst h_done
      simp [hloc]
    · have h_lt : level < ℓ := Nat.lt_of_le_of_ne hℓ h_done
      have hvoff_succ : vOff n (level + 1) ≤ vOff n ℓ :=
        vOff_mono n (by omega)
      have h_ge : ¬ (vOff n ℓ - vOff n level + localOff < levelVSize n level) := by
        have : vOff n level + levelVSize n level = vOff n (level + 1) := rfl
        omega
      simp [h_ge]
      have h_off : vOff n ℓ - vOff n level + localOff - levelVSize n level
                 = vOff n ℓ - vOff n (level + 1) + localOff := by
        have : vOff n level + levelVSize n level = vOff n (level + 1) := rfl
        omega
      rw [h_off]
      exact ih (level + 1) (by omega) (by omega) hvoff_succ

/-- Main vLookup correctness lemma: vLookup at level ℓ, position q, sub-index s. -/
theorem vLookup_at_level (n ℓ q s : ℕ)
    (hq : q < recSeq n (ℓ + 1))
    (hs : s < 2 ^ q + 1)
    (hℓ : ℓ < n)
    (_ : vOff n (ℓ + 1) ≤ spA n) :
    vLookup n (vOff n ℓ + cPosOff q + s) 0 n = (ℓ, q, s) := by
  have hloc : cPosOff q + s < levelVSize n ℓ := by
    have h1 : cPosOff q + s < cPosOff (q + 1) := by simp [cPosOff]; omega
    have h2 : cPosOff (q + 1) ≤ cPosOff (recSeq n (ℓ + 1)) := cPosOff_mono (by omega)
    rw [cPosOff_eq_levelVSize] at h2; omega
  have h1 : vOff n ℓ + cPosOff q + s = vOff n ℓ + (cPosOff q + s) := by omega
  rw [h1, show vOff n ℓ + (cPosOff q + s) = vOff n ℓ - vOff n 0 + (cPosOff q + s) by simp]
  have hvl := vLookup_vOff n ℓ (cPosOff q + s) 0 n hloc (Nat.zero_le _) (by omega) (by simp)
  rw [hvl]
  have hvp := findVPos_at_pos q s (recSeq n (ℓ + 1)) hs hq
  simp [hvp]

/-! ## wvAdj characterization -/

/-- wvAdj is true when wLookup and vLookup give same level, different position. -/
lemma wvAdj_true_of_ne (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ p q s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ, q, s))
    (hpq : p ≠ q) :
    wvAdj n i j = true := by
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [Bool.true_and, bne, hpq]

/-- wvAdj is false when wLookup and vLookup give same level, same position. -/
lemma wvAdj_false_of_eq (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ p s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ, p, s)) :
    wvAdj n i j = false := by
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [bne]

/-- wvAdj result when wLookup and vLookup give different levels. -/
lemma wvAdj_diff_level (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ₁ p ℓ₂ q s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ₁, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ₂, q, s))
    (hne : ℓ₁ ≠ ℓ₂) :
    wvAdj n i j = false := by
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [beq_iff_eq, hne]

/-- wvAdj is false when wLookup returns none. -/
lemma wvAdj_none (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = none) :
    wvAdj n i j = false := by
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl]

/-! ## isGeneric characterization -/

/-- A y-vertex at index ≥ n/2 is non-generic. -/
lemma isGeneric_false_of_ge (n : ℕ) (i : Fin n) (h : n / 2 ≤ (i : ℕ)) :
    isGeneric n i = false := by
  unfold isGeneric; simp [Nat.not_lt.mpr h]

/-- A y-vertex at index < n/2 is generic. -/
lemma isGeneric_true_of_lt (n : ℕ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    isGeneric n i = true := by
  unfold isGeneric; simp [h]

/-! ## recSeq properties -/

/-- recSeq n (k+1) < recSeq n k for recSeq n k ≥ 3. -/
lemma recSeq_decreasing (n k : ℕ) (h : recSeq n k ≥ 3) :
    recSeq n (k + 1) < recSeq n k := by
  simp only [recSeq]
  split_ifs with h'
  · omega
  · have := Nat.log_lt_of_lt_pow (show recSeq n k - 1 ≠ 0 by omega)
      (Nat.lt_pow_self (show 1 < 2 by norm_num))
    omega

/-- recSeq n (k+1) ≥ 2 when recSeq n k ≥ 2. -/
lemma recSeq_ge_two (n k : ℕ) (_ : recSeq n k ≥ 2) :
    recSeq n (k + 1) ≥ 2 := by
  simp only [recSeq]
  split_ifs with h' <;> [exact le_refl _; skip]
  have : Nat.log 2 (recSeq n k - 1) ≥ 1 := by
    apply Nat.le_log_of_pow_le (by norm_num)
    omega
  omega

/-- 2^(recSeq n (k+1)) > recSeq n k - 1 when recSeq n k ≥ 3.
  This ensures level overlap in the recursive construction. -/
lemma pow_recSeq_gt (n k : ℕ) (h : recSeq n k ≥ 3) :
    2 ^ recSeq n (k + 1) > recSeq n k - 1 := by
  have hge : recSeq n k ≥ 3 := h
  simp only [recSeq]
  split_ifs with h'
  · omega
  · have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (recSeq n k - 1)
    simp only [Nat.succ_eq_add_one] at this
    exact this

/-- Level overlap: the max size at level k+1 is ≥ min size at level k. -/
lemma level_overlap (n k : ℕ) (h : recSeq n k ≥ 3) :
    2 ^ recSeq n (k + 1) + recSeq n (k + 1) ≥ recSeq n k + 2 := by
  have h1 := pow_recSeq_gt n k h
  have h2 := recSeq_ge_two n k (by omega)
  omega

/-
wLookup returns position < recSeq.
-/
lemma wLookup_pos_bound (n offset level fuel ℓ p : ℕ)
    (h : wLookup n offset level fuel = some (ℓ, p)) :
    p < recSeq n (ℓ + 1) := by
  induction' fuel with fuel ih generalizing level offset;
  · unfold wLookup at h;
    unfold recSeq; aesop;
  · unfold wLookup at h;
    grind

/-
wLookup offset reconstruction.
-/
lemma wLookup_offset_eq (n offset level fuel ℓ p : ℕ)
    (h : wLookup n offset level fuel = some (ℓ, p))
    (hlev : level ≤ ℓ) :
    offset = wOff n ℓ - wOff n level + p := by
  induction' fuel with fuel fuel_ih generalizing offset level ℓ p <;> simp_all +decide [ wLookup ];
  split_ifs at h <;> simp_all +decide;
  specialize fuel_ih ( offset - recSeq n ( level + 1 ) ) ( level + 1 ) ℓ p h;
  cases hlev.eq_or_lt <;> simp_all +decide [ add_comm ];
  · have h_wLookup_pos : ∀ {offset level fuel ℓ p}, wLookup n offset level fuel = some (ℓ, p) → level ≤ ℓ := by
      intros offset level fuel ℓ p h; induction' fuel with fuel fuel_ih generalizing offset level ℓ p <;> simp_all +decide [ wLookup ] ;
      grind;
    grind;
  · rw [ Nat.sub_eq_iff_eq_add ] at fuel_ih;
    · rw [ fuel_ih, add_assoc, tsub_add_eq_add_tsub ];
      · rw [ Nat.add_sub_add_right ];
      · exact Nat.le_induction ( by simp +decide [ wOff ] ) ( fun k hk ih => by simp +decide [ wOff ] at * ; linarith ) _ ‹level < ℓ›;
    · linarith

/-
findVPos returns sub < 2^pos + 1 when offset fits within fuel positions.
-/
lemma findVPos_sub_bound (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    (findVPos offset pos fuel).2 < 2 ^ (findVPos offset pos fuel).1 + 1 := by
  contrapose! h;
  induction' fuel with fuel ih generalizing offset pos;
  · aesop;
  · unfold findVPos at h;
    have := ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ?_;
    · simp_all +decide [ Nat.add_comm, Nat.add_left_comm, Nat.add_assoc ];
      grind;
    · grind

/-
findVPos returns pos within bounds.
-/
lemma findVPos_pos_bound (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    (findVPos offset pos fuel).1 < pos + fuel := by
  contrapose! h;
  induction' fuel with fuel ih generalizing pos offset;
  · aesop;
  · by_cases h₂ : offset < 2 ^ pos + 1;
    · unfold findVPos at h; aesop;
    · specialize ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ; simp_all +decide [ ];
      rw [ show findVPos offset pos ( fuel + 1 ) = findVPos ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) fuel from ?_ ] at h;
      · grind;
      · exact if_neg ( by linarith )

/-
findVPos offset reconstruction.
-/
lemma findVPos_offset_eq (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    offset = cPosOff (findVPos offset pos fuel).1 - cPosOff pos + (findVPos offset pos fuel).2 := by
  induction' fuel with fuel ih generalizing offset pos;
  · grind;
  · unfold findVPos;
    specialize ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ; simp_all +decide [ ];
    split_ifs <;> simp_all +decide [ add_comm, add_left_comm ];
    convert congr_arg ( · + ( 1 + 2 ^ pos ) ) ( ih _ ) using 1;
    · rw [ Nat.sub_add_cancel ( by linarith ) ];
    · rw [ add_assoc, tsub_add_eq_add_tsub ];
      · rw [ Nat.add_sub_add_right ];
      · have h_findVPos_pos : (findVPos (offset - (1 + 2 ^ pos)) (pos + 1) fuel).1 ≥ pos + 1 := by
          have h_findVPos_pos : ∀ (offset pos fuel : ℕ), (findVPos offset pos fuel).1 ≥ pos := by
            intros offset pos fuel; induction' fuel with fuel ih generalizing offset pos <;> unfold findVPos <;> simp +arith +decide [ * ] ;
            grind;
          exact h_findVPos_pos _ _ _;
        refine' le_trans _ ( cPosOff_mono h_findVPos_pos );
        simp +arith +decide [ cPosOff ];
    · omega

/-! ## vLookup offset reconstruction -/

/-- If vLookup returns level ℓ, then the input offset equals vOff n ℓ - vOff n level + local offset. -/
lemma vLookup_level_ge (n offset level fuel : ℕ) :
    (vLookup n offset level fuel).1 ≥ level := by
  induction fuel generalizing offset level with
  | zero => simp [vLookup]
  | succ f ih =>
    simp only [vLookup]
    split_ifs with h
    · simp
    · exact le_trans (Nat.le_succ _) (ih _ _)

set_option maxHeartbeats 3200000 in
private lemma vLookup_offset_eq_step (n offset level fuel ℓ q s : ℕ)
    (ih : ∀ (offset level : ℕ),
      vLookup n offset level fuel = (ℓ, q, s) → level ≤ ℓ →
      offset = vOff n ℓ - vOff n level + cPosOff q + s)
    (h : vLookup n offset level (fuel + 1) = (ℓ, q, s))
    (_ : level ≤ ℓ) :
    offset = vOff n ℓ - vOff n level + cPosOff q + s := by
  unfold vLookup at h;
  by_cases h' : offset < levelVSize n level <;> simp +decide [ h' ] at h ⊢;
  · convert findVPos_offset_eq offset 0 ( recSeq n ( level + 1 ) ) _ using 1;
    · aesop;
    · convert h' using 1;
      convert cPosOff_eq_levelVSize n level using 1;
      norm_num;
  · have hlev' : level + 1 ≤ ℓ := by
      have := vLookup_level_ge n (offset - levelVSize n level) (level + 1) fuel
      simp only [h, ge_iff_le] at this; omega
    have h_ih := ih _ _ h hlev'
    have hvoff : vOff n (level + 1) = vOff n level + levelVSize n level := rfl
    have hvoff_le : vOff n (level + 1) ≤ vOff n ℓ := vOff_mono n hlev'
    have hoff_ge : offset ≥ levelVSize n level := Nat.le_of_not_lt h'
    rw [hvoff] at hvoff_le h_ih
    zify [hoff_ge, hvoff_le] at h_ih ⊢; omega

set_option maxHeartbeats 3200000 in
lemma vLookup_offset_eq (n offset level fuel ℓ q s : ℕ)
    (h : vLookup n offset level fuel = (ℓ, q, s))
    (hlev : level ≤ ℓ) :
    offset = vOff n ℓ - vOff n level + cPosOff q + s := by
  induction' fuel with fuel ih generalizing offset level;
  · cases h;
    by_cases h : offset < cPosOff ( 0 + ( recSeq n ( ℓ + 1 ) ) ) - cPosOff 0 <;> simp_all +decide [ cPosOff_eq ];
    · convert findVPos_offset_eq offset 0 ( recSeq n ( ℓ + 1 ) ) _ using 1;
      · rw [ cPosOff_eq ] ; norm_num;
      · convert h using 1;
        simp +decide [ cPosOff_eq ];
    · have h_findVPos : ∀ (offset pos fuel : ℕ), offset ≥ cPosOff (pos + fuel) - cPosOff pos → findVPos offset pos fuel
          = (pos + fuel, offset - (cPosOff (pos + fuel) - cPosOff pos)) := by
        intros offset pos fuel h; induction' fuel with fuel ih generalizing offset pos <;> simp_all +decide [ cPosOff_eq ] ;
        · rfl;
        · rw [ show findVPos offset pos ( fuel + 1 ) = findVPos ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) fuel from ?_ ];
          · convert ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) _ using 1;
            · simp +arith +decide [ Nat.pow_succ' ];
              rw [ Nat.sub_sub ] ; ring_nf;
              rw [ show 2 ^ pos * 2 - 1 = 2 ^ pos - 1 + 2 ^ pos by zify ; norm_num ; ring ] ; ring_nf;
              rw [ show 1 + fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) - ( pos + ( 2 ^ pos - 1 ) )
                          = 1 + ( fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) - ( pos + ( 2 ^ pos - 1 ) + 2 ^ pos ) ) + 2 ^ pos from ?_ ];
              rw [ Nat.sub_eq_of_eq_add ] ;
              linarith [ Nat.sub_add_cancel ( show pos + ( 2 ^ pos - 1 ) + 2 ^ pos ≤ fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) from by
                                                rcases fuel with ( _ | fuel ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ];
                                                · grind;
                                                · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ pos from Nat.one_le_pow _ _ ( by decide ) ),
                                                      Nat.sub_add_cancel ( show 1 ≤ 2 * ( 2 ^ fuel * ( 2 ^ pos * 2 ) ) from Nat.one_le_iff_ne_zero.mpr <| by positivity ),
                                                      Nat.one_le_pow fuel 2 ( by decide ), Nat.one_le_pow pos 2 ( by decide )
                                                    ]
                                              ) ];
            · grind;
          · exact if_neg ( by
              contrapose! h;
              rw [ pow_add ];
              nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow pos 2 zero_lt_two ),
                Nat.pow_le_pow_right two_pos ( show fuel + 1 ≥ 1 by linarith ),
                Nat.sub_add_cancel ( show 1 ≤ 2 ^ pos * 2 ^ ( fuel + 1 ) from Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] );
      rw [ h_findVPos ] <;> norm_num [ cPosOff_eq ];
      · rw [ Nat.add_sub_of_le h ];
      · grobner;
  · exact vLookup_offset_eq_step n offset level fuel ℓ q s ih h hlev

lemma vLookup_pos_bound (n offset level fuel ℓ q s : ℕ)
    (h : vLookup n offset level fuel = (ℓ, q, s))
    (hfuel : ℓ - level < fuel) :
    q < recSeq n (ℓ + 1) ∧ s < 2 ^ q + 1 := by
  induction' fuel with fuel ih generalizing offset level;
  · omega;
  · unfold vLookup at h;
    by_cases h : offset < levelVSize n level <;> simp_all +decide;
    · have := findVPos_pos_bound offset 0 ( recSeq n ( ℓ + 1 ) ) ?_ <;> simp_all +decide [ cPosOff_eq_levelVSize ];
      have := findVPos_sub_bound offset 0 ( recSeq n ( ℓ + 1 ) ) ?_ <;> simp_all +decide [ cPosOff_eq_levelVSize ];
      grind;
    · apply ih;
      expose_names; exact Prod.ext (congrArg Prod.fst h_1) (congrArg Prod.snd h_1)
      have := vLookup_level_ge n ( offset - levelVSize n level ) ( level + 1 ) fuel; simp_all +decide ; omega;

/-
# Medium Clique Construction

For each d with n+1 ≤ d ≤ 2^n + n, we construct a maximal clique of size d
in Spencer's graph. The clique consists of yStar, a subset of y-vertices,
and all C_i for i not in the selected subset.
-/

open Finset SimpleGraph


/-- The medium clique for selector set S:
  {yStar} ∪ {y_i : i ∈ S} ∪ ⋃_{i ∉ S} C_i -/
noncomputable def medClique (n : ℕ) (S : Finset (Fin n)) : Finset (SpVtx n (spA n)) :=
  {.yStar} ∪
  S.biUnion (fun i => {.y i}) ∪
  (Finset.univ \ S).biUnion (fun i => Finset.univ.image fun j => SpVtx.c i j)

/-- yStar is in the medium clique. -/
lemma yStar_mem_medClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.yStar ∈ medClique n S := by
  simp [medClique]

/-- y_i is in the medium clique iff i ∈ S. -/
lemma y_mem_medClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    SpVtx.y i ∈ medClique n S ↔ i ∈ S := by
  simp [medClique, SpVtx.y.injEq]

/-- c_i_j is in the medium clique iff i ∉ S. -/
lemma c_mem_medClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) (j : Fin (cSize i)) :
    SpVtx.c i j ∈ medClique n S ↔ i ∉ S := by
  simp [medClique, SpVtx.c.injEq]

/-- cStar vertices are NOT in the medium clique. -/
lemma cStar_not_mem_medClique (n : ℕ) (S : Finset (Fin n)) (j : Fin (spA n)) :
    SpVtx.cStar j ∉ medClique n S := by
  simp [medClique]

/-- z is NOT in the medium clique. -/
lemma z_not_mem_medClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.z ∉ medClique n S := by
  simp [medClique]

/-
The medium clique is a clique.
-/
lemma medClique_isClique (n : ℕ) (S : Finset (Fin n)) :
    (spGraph n).IsClique (↑(medClique n S) : Set _) := by
  intro x hx y hy hxy; unfold medClique at hx hy; simp_all +decide [ ] ;
  unfold spGraph; unfold spAdj; aesop;

/-
The medium clique is maximal.
-/
lemma medClique_isMaximal (n : ℕ) (S : Finset (Fin n)) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → medClique n S ⊆ t → t = medClique n S := by
  intro t ht ht_sub
  have ht_eq : ∀ v ∈ t, v ∈ medClique n S := by
    intro v hv;
    rcases v with ( _ | _ | _ | _ | _ );
    · rename_i i;
      by_cases hi : i ∈ S <;> simp_all +decide [ medClique ];
      have := ht hv ( ht_sub <| show SpVtx.c i ⟨ 0, by simp +decide [ cSize ] ⟩ ∈ _ from by aesop ) ;
      simp_all +decide [ spGraph ] ;
      unfold spAdj at this; aesop;
    · exact yStar_mem_medClique n S;
    · rename_i i j;
      by_cases hi : i ∈ S <;> simp_all +decide [ medClique ];
      have := ht ( ht_sub ( Finset.mem_insert_of_mem ( Finset.mem_union_left _
        ( Finset.mem_biUnion.mpr ⟨ i, hi, Finset.mem_singleton_self _ ⟩ ) ) ) ) hv;
      simp_all +decide [ spGraph ] ;
      unfold spAdj at this; aesop;
    · have := ht ( show SpVtx.yStar ∈ t from ht_sub <| by simp +decide [ medClique ] ) hv;
      simp_all +decide [ spGraph ] ;
      cases this ; tauto;
    · have := ht ( show SpVtx.yStar ∈ t from ht_sub ( by simp +decide [ medClique ] ) ) hv;
      simp +decide [ ] at this;
      cases this ; contradiction;
  exact subset_antisymm ht_eq ht_sub

/-- The medium clique is a maximal clique. -/
lemma medClique_isMaximalClique (n : ℕ) (S : Finset (Fin n)) :
    IsMaximalClique (spGraph n) (medClique n S) :=
  ⟨medClique_isClique n S, medClique_isMaximal n S⟩

/-
The card of the medium clique.
-/
lemma medClique_card (n : ℕ) (S : Finset (Fin n)) :
    (medClique n S).card = 2 ^ n + n - ∑ i ∈ S, 2 ^ (i : ℕ) := by
  unfold medClique;
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num;
  · rw [ Finset.card_biUnion, Finset.card_biUnion ] <;> norm_num;
    · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ fun x y hxy => by injection hxy ];
      simp +arith +decide [ Finset.card_univ, cSize ];
      have h_sum : ∑ i : Fin n, (2 ^ (i : ℕ) + 1) = 2 ^ n - 1 + n := by
        exact sum_cSize_Fin n;
      rw [ ← Finset.sum_sdiff ( Finset.subset_univ S ) ] at *;
      exact eq_tsub_of_add_eq ( by
          norm_num [ Finset.sum_add_distrib ] at *;
          linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ) ]
        );
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
  · aesop;
  · simp +contextual [ Finset.disjoint_left ]

/-
For each d with n+1 ≤ d ≤ 2^n + n, there exists a maximal clique of size d.
-/
theorem medium_clique_exists (n : ℕ) (hn : n ≥ 2) (d : ℕ)
    (hd1 : n + 1 ≤ d) (hd2 : d ≤ 2 ^ n + n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  -- Let α = 2^n + n - d. Then 0 ≤ α ≤ 2^n - 1.
  set α := 2 ^ n + n - d
  have hα_nonneg : 0 ≤ α := by
    exact Nat.zero_le _
  have hα_lt : α < 2 ^ n := by
    omega;
  obtain ⟨ S, hS ⟩ := binary_expansion n α hα_lt;
  exact ⟨ medClique n S, medClique_isMaximalClique n S, by rw [ medClique_card ] ; omega ⟩

/-
# Big Clique Construction

For each d with 2^n + n < d ≤ spB n, we construct a maximal clique of size d
in Spencer's graph. The clique consists of generic y-vertices (from a selected
subset), ALL C* vertices, and C_i for i not in the selected subset.
-/

open Finset SimpleGraph


/-- The big clique for selector set S ⊆ {generic selectors}:
  {y_i : i ∈ S} ∪ {cStar j : all j} ∪ ⋃_{i ∉ S} C_i

  S should only contain generic selectors (i < n/2) for the clique property. -/
noncomputable def bigClique (n : ℕ) (S : Finset (Fin n)) : Finset (SpVtx n (spA n)) :=
  S.biUnion (fun i => {.y i}) ∪
  Finset.univ.image SpVtx.cStar ∪
  (Finset.univ \ S).biUnion (fun i => Finset.univ.image fun j => SpVtx.c i j)

/-- y_i is in the big clique iff i ∈ S. -/
lemma y_mem_bigClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    SpVtx.y i ∈ bigClique n S ↔ i ∈ S := by
  simp [bigClique, SpVtx.y.injEq]

/-- cStar_j is in the big clique. -/
lemma cStar_mem_bigClique (n : ℕ) (S : Finset (Fin n)) (j : Fin (spA n)) :
    SpVtx.cStar j ∈ bigClique n S := by
  simp [bigClique]

/-- c_i_j is in the big clique iff i ∉ S. -/
lemma c_mem_bigClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) (j : Fin (cSize i)) :
    SpVtx.c i j ∈ bigClique n S ↔ i ∉ S := by
  simp [bigClique, SpVtx.c.injEq]

/-- yStar is NOT in the big clique. -/
lemma yStar_not_mem_bigClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.yStar ∉ bigClique n S := by
  simp [bigClique]

/-- z is NOT in the big clique. -/
lemma z_not_mem_bigClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.z ∉ bigClique n S := by
  simp [bigClique]

/-
The big clique is a clique when S only contains generic selectors.
-/
set_option maxHeartbeats 800000 in
lemma bigClique_isClique (n : ℕ) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, isGeneric n i = true) :
    (spGraph n).IsClique (↑(bigClique n S) : Set _) := by
  push_cast [ SimpleGraph.isClique_iff, bigClique ];
  simp +decide [ Set.Pairwise, spGraph ];
  unfold spAdj; aesop;

/-
The big clique is maximal when n ≥ 2.
-/
set_option maxHeartbeats 800000 in
lemma bigClique_isMaximal (n : ℕ) (hn : n ≥ 2) (S : Finset (Fin n)) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → bigClique n S ⊆ t → t = bigClique n S := by
  intro t ht ht';
  refine' le_antisymm _ ht';
  intro v hv;
  rcases v with ( _ | _ | _ | _ | _ ) <;> simp_all +decide [ Finset.subset_iff ];
  · rename_i i;
    by_cases hi : i ∈ S <;> simp_all +decide [ bigClique ];
    have := ht hv ( ht' <| Or.inr <| Or.inr <| ⟨ i, hi, ⟨ 0, by
      exact Nat.succ_pos _ ⟩, rfl ⟩ ) ; simp_all +decide [ spGraph ];
    unfold spAdj at this; aesop;
  · have := ht hv ( ht' ( cStar_mem_bigClique n S ⟨ 0, spA_pos n ⟩ ) ) ; simp_all +decide [ spGraph ] ;
    cases this ; tauto;
  · contrapose! hv;
    intro h;
    have := ht h ( ht' <| show SpVtx.y ‹_› ∈ bigClique n S from ?_ ) ; simp_all +decide [ spGraph ];
    · unfold spAdj at this; aesop;
    · unfold bigClique at *; aesop;
  · exact Finset.mem_union_left _ ( Finset.mem_union_right _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) );
  · by_cases h : ⟨ 0, by linarith ⟩ ∈ S <;> simp_all +decide [ bigClique ];
    · have := ht hv ( ht' <| Or.inl ⟨ _, h, rfl ⟩ ) ; simp_all +decide [ spGraph ] ;
      unfold spAdj at this; simp_all +decide [ isGeneric ] ;
    · have := ht hv ( ht' <| Or.inr <| Or.inr <| ⟨ ⟨ 0, by linarith ⟩, h, ⟨ 0, by simp +decide [ cSize ] ⟩, rfl ⟩ ) ; simp_all +decide [ spGraph ] ;
      cases this ; contradiction

/-- The big clique is a maximal clique when S contains only generic selectors. -/
lemma bigClique_isMaximalClique (n : ℕ) (hn : n ≥ 2) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, isGeneric n i = true) :
    IsMaximalClique (spGraph n) (bigClique n S) :=
  ⟨bigClique_isClique n S hS, bigClique_isMaximal n hn S⟩

/-
The card of the big clique.
-/
lemma bigClique_card (n : ℕ) (S : Finset (Fin n)) :
    (bigClique n S).card = spB n - ∑ i ∈ S, 2 ^ (i : ℕ) := by
  unfold bigClique;
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;>
    norm_num [ Finset.card_image_of_injective, Function.Injective ];
  · rw [ Finset.card_biUnion, Finset.card_biUnion ];
    · simp +decide [ Finset.card_image_of_injective, Function.Injective, spB ];
      have h_sum_cSize : ∑ i : Fin n, cSize i = 2 ^ n - 1 + n := by
        convert sum_cSize_Fin n using 1;
      rw [ ← Finset.sum_sdiff ( Finset.subset_univ S ) ] at *;
      simp_all +decide [ cSize ];
      simp_all +decide [ Finset.sum_add_distrib ];
      grind;
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
    · exact fun i hi j hj hij => Finset.disjoint_singleton.2 <| by simpa [ Fin.ext_iff ] using hij;
  · simp +decide [ Finset.disjoint_right ];
  · constructor <;> rw [ Finset.disjoint_left ] <;> aesop

/-
spA n ≤ 2^(n/2) for n ≥ 16.
-/
lemma spA_le_pow_half (n : ℕ) (hn : n ≥ 16) : spA n ≤ 2 ^ (n / 2) := by
  -- By induction on $n$, we can show that $spAux n \leq 4n$ for all $n \geq 16$.
  have h_spAux_le_4n (n : ℕ) (hn : n ≥ 16) : spAux n ≤ 4 * n := by
    induction' n using Nat.strong_induction_on with n ih;
    unfold spAux;
    rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;>
      simp +arith +decide [ * ] at *;
    by_cases h₂ : 16 ≤ Nat.log 2 (n + 15) + 1;
    · have := ih ( Nat.log 2 ( n + 15 ) + 1 ) ( by
        linarith [Nat.log_lt_of_lt_pow ( by linarith ) ( show n + 15 < 2 ^ ( n + 15 ) by
            exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith )
          ]
        ) ( by linarith );
      have := Nat.pow_log_le_self 2 ( by linarith : n + 15 ≠ 0 );
      rcases k : Nat.log 2 ( n + 15 ) with
        ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;>
          simp_all +arith +decide [ Nat.pow_succ' ];
      · linarith;
      · rename_i k' hk';
        linarith [ show 2 ^ k' ≥ k' + 1 from
          Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith ];
    · split_ifs <;> simp_all +arith +decide;
      · interval_cases Nat.log 2 ( n + 15 ) <;> norm_num at *;
      · interval_cases _ : Nat.log 2 ( n + 15 ) <;> simp +arith +decide at *;
        all_goals rw [ Nat.log_eq_iff ] at * <;> norm_num at *;
        all_goals unfold spAux; simp +arith +decide at *;
        all_goals norm_num [ Nat.log_of_lt ] at *;
        all_goals unfold spAux; simp +arith +decide at *;
        all_goals norm_num [ Nat.log_of_lt ] at *;
        all_goals omega;
  refine le_trans ( h_spAux_le_4n n hn ) ?_;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul ] at *;
  · exact Nat.le_induction ( by norm_num )
      ( fun n hn ih => by norm_num [ Nat.pow_succ ] at * ; linarith ) k ( show k ≥ 8 by linarith );
  · norm_num [ Nat.add_div ];
    exact Nat.le_induction ( by norm_num )
      ( fun n hn ih => by norm_num [ Nat.pow_succ' ] at * ; linarith ) _ ( show k ≥ 8 by linarith )

/-
For each d with 2^n + n < d ≤ spB n, there exists a maximal clique of size d.
-/
theorem big_clique_exists (n : ℕ) (hn : n ≥ 16) (d : ℕ)
    (hd1 : 2 ^ n + n < d) (hd2 : d ≤ spB n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (n / 2)), ∑ i ∈ S, 2 ^ (i : ℕ) = spB n - d := by
    apply binary_expansion;
    rw [ tsub_lt_iff_left ] <;> try linarith;
    unfold spB at *;
    linarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ n + n from by linarith [ Nat.one_le_pow n 2 zero_lt_two ] ), spA_le_pow_half n hn ];
  refine' ⟨ bigClique n ( Finset.image ( fun i ↦ ⟨ i.val, lt_of_lt_of_le i.2 ( Nat.div_le_self _ _ ) ⟩ ) S ), _, _ ⟩;
  · apply bigClique_isMaximalClique;
    · grind;
    · unfold isGeneric; aesop;
  · rw [ bigClique_card, Finset.sum_image ];
    · exact Nat.sub_eq_of_eq_add <| by linarith! [ Nat.sub_add_cancel hd2 ] ;
    · exact fun x hx y hy hxy => Fin.ext <| by simpa using congr_arg Fin.val hxy;

/-
# Small Clique Construction

For each d with 5 ≤ d ≤ n, we construct a maximal clique of size d
in Spencer's graph using z, w-vertices, and C*-vertices.
-/

open Finset SimpleGraph


/-! ## Level validity -/

/-- A level ℓ is "valid" for graph parameter n. -/
structure LevelValid (n ℓ : ℕ) : Prop where
  recSeq_ge : recSeq n (ℓ + 1) ≥ 2
  wfit : n / 2 + wOff n (ℓ + 1) ≤ n
  vfit : vOff n (ℓ + 1) ≤ spA n
  fuel : ℓ < n

/-! ## Clique at a level (filtering approach) -/

/-- Whether a w-vertex y_i belongs to level ℓ with position in S. -/
def wInLevel (n ℓ : ℕ) (S : Finset ℕ) (i : Fin n) : Bool :=
  decide (n / 2 ≤ (i : ℕ)) &&
  match wLookup n ((i : ℕ) - n / 2) 0 n with
  | some (wl, wp) => wl == ℓ && decide (wp ∈ S)
  | none => false

/-- Whether a C*-vertex cStar_j belongs to level ℓ with position NOT in S. -/
def vNotInLevel (n ℓ : ℕ) (S : Finset ℕ) (j : Fin (spA n)) : Bool :=
  let (vl, vp, _) := vLookup n (j : ℕ) 0 n
  vl == ℓ && !decide (vp ∈ S)

/-- The small clique at level ℓ with w-position set S.
  Includes z, w-vertices at positions in S, C*-vertices at positions NOT in S. -/
noncomputable def smallCl (n ℓ : ℕ) (S : Finset ℕ) :
    Finset (SpVtx n (spA n)) :=
  {.z} ∪
  (Finset.univ.filter fun i : Fin n => wInLevel n ℓ S i).image .y ∪
  (Finset.univ.filter fun j : Fin (spA n) => vNotInLevel n ℓ S j).image .cStar

/-! ## Membership helpers -/

/-- z is in the small clique. -/
lemma z_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) :
    SpVtx.z ∈ smallCl n ℓ S := by
  simp [smallCl]

/-
The w-vertex at position p is in smallCl when p ∈ S and the level is valid.
-/
lemma wVertex_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) (p : ℕ)
    (hv : LevelValid n ℓ) (hp : p < recSeq n (ℓ + 1)) (hpS : p ∈ S) :
    SpVtx.y ⟨n / 2 + wOff n ℓ + p, by
      have := hv.wfit; have : wOff n (ℓ + 1) = wOff n ℓ + recSeq n (ℓ + 1) := rfl; omega⟩
    ∈ smallCl n ℓ S := by
  unfold smallCl; simp +decide [ *, wInLevel ] ;
  rw [ show n / 2 + wOff n ℓ + p - n / 2 = wOff n ℓ + p by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
  rw [ wLookup_at_level ] <;> norm_num [ hp, hpS ];
  · exact le_add_of_le_of_nonneg ( Nat.le_add_right _ _ ) ( Nat.zero_le _ );
  · exact hv.fuel;
  · have := hv.wfit; norm_num [ Nat.add_assoc ] at *; omega;

/-
The C*-vertex at position q, sub-index s, is in smallCl when q ∉ S.
-/
lemma cStarVertex_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) (q s : ℕ)
    (hv : LevelValid n ℓ) (hq : q < recSeq n (ℓ + 1)) (hs : s < 2 ^ q + 1)
    (hqS : q ∉ S) :
    SpVtx.cStar ⟨vOff n ℓ + cPosOff q + s, by
      have := hv.vfit
      have h1 : cPosOff q + s < cPosOff (q + 1) := by simp [cPosOff]; omega
      have h2 : cPosOff (q + 1) ≤ cPosOff (recSeq n (ℓ + 1)) := cPosOff_mono (by omega)
      rw [cPosOff_eq_levelVSize] at h2
      have : vOff n ℓ + levelVSize n ℓ = vOff n (ℓ + 1) := rfl; omega⟩
    ∈ smallCl n ℓ S := by
  unfold smallCl; simp +decide [ *, vNotInLevel ] ;
  have := vLookup_at_level n ℓ q s hq hs hv.fuel hv.vfit; aesop;

/-! ## Clique property -/

/-- The small clique is a clique in Spencer's graph. -/
lemma smallCl_isClique (n ℓ : ℕ) (S : Finset ℕ) :
    (spGraph n).IsClique (↑(smallCl n ℓ S) : Set _) := by
  intro u hu v hv huv;
  unfold smallCl at hu hv;
  unfold wInLevel vNotInLevel at *;
  unfold spGraph at *;
  unfold spAdj; simp +decide [ huv ] ;
  rcases u with ( _ | _ | _ | _ | _ ) <;> rcases v with ( _ | _ | _ | _ | _ ) <;> simp +decide at hu hv huv ⊢;
  · unfold wvAdj;
    cases h : wLookup n ( ↑‹Fin n› - n / 2 ) 0 n <;> simp_all +decide;
    grind;
  · exact isGeneric_false_of_ge n _ hu.1;
  · unfold wvAdj; simp +decide [ ] ;
    cases h : wLookup n ( ↑‹Fin n› - n / 2 ) 0 n <;> simp_all +decide;
    grind;
  · exact isGeneric_false_of_ge n _ hv.1

/-! ## Maximality helpers -/

/-
If y_i is non-generic and not in smallCl, then wLookup gives a result
  that allows finding a blocking cStar in smallCl.
-/
lemma y_blocked_by_cStar (n ℓ : ℕ) (S : Finset ℕ) (i : Fin n)
    (hv : LevelValid n ℓ)
    (hge : n / 2 ≤ (i : ℕ))
    (hnotW : wInLevel n ℓ S i = false)
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    ∃ j : Fin (spA n), SpVtx.cStar j ∈ smallCl n ℓ S ∧
      wvAdj n i j = false := by
  by_cases h : wLookup n ( i - n / 2 ) 0 n = none <;> simp_all +decide [ wInLevel ];
  · obtain ⟨ q, hq₁, hq₂ ⟩ := hS_prop;
    refine' ⟨ ⟨ vOff n ℓ + cPosOff q + 0, _ ⟩, _, _ ⟩;
    any_goals exact cStarVertex_mem_smallCl n ℓ S q 0 hv hq₁ ( by norm_num ) hq₂;
    exact?;
  · rcases h' : wLookup n ( i - n / 2 ) 0 n with ( _ | ⟨ wl, wp ⟩ ) <;> simp_all +decide [ ];
    by_cases hwl : wl = ℓ <;> simp_all +decide [ ];
    · -- Since wp < recSeq n (ℓ + 1), we can use cStarVertex_mem_smallCl with (wp, 0).
      have hwp_lt : wp < recSeq n (ℓ + 1) := by
        have hwp_lt_recSeq : ∀ {offset level fuel : ℕ}, wLookup n offset level fuel = some (ℓ, wp) → wp < recSeq n (ℓ + 1) := by
          intros offset level fuel h; induction' fuel with fuel ih generalizing offset level <;> simp_all +decide [ wLookup ] ;
          · linarith [ hv.recSeq_ge ];
          · grind;
        exact hwp_lt_recSeq h';
      refine' ⟨ ⟨ vOff n ℓ + cPosOff wp + 0, _ ⟩, _, _ ⟩;
      any_goals exact cStarVertex_mem_smallCl n ℓ S wp 0 hv hwp_lt ( by norm_num ) hnotW;
      apply wvAdj_false_of_eq;
      exact h';
      convert vLookup_at_level n ℓ wp 0 _ _ _ _ using 1;
      · assumption;
      · positivity;
      · exact hv.fuel;
      · exact hv.vfit;
    · obtain ⟨ q, hq₁, hq₂ ⟩ := hS_prop;
      refine' ⟨ ⟨ vOff n ℓ + cPosOff q + 0, _ ⟩, _, _ ⟩;
      any_goals exact cStarVertex_mem_smallCl n ℓ S q 0 hv hq₁ ( by norm_num ) hq₂;
      apply wvAdj_diff_level;
      exact h';
      exact vLookup_at_level n ℓ q 0 hq₁ ( by norm_num ) hv.fuel hv.vfit;
      assumption

/-
If cStar_j is not in smallCl, then there exists a w-vertex in smallCl
  that is not adjacent to cStar_j.
-/
lemma cStar_blocked_by_y (n ℓ : ℕ) (S : Finset ℕ) (j : Fin (spA n))
    (hv : LevelValid n ℓ)
    (hnotV : vNotInLevel n ℓ S j = false)
    (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    ∃ i : Fin n, SpVtx.y i ∈ smallCl n ℓ S ∧
      isGeneric n i = false ∧ wvAdj n i j = false := by
  by_cases h_case2 : (vLookup n j 0 n).1 = ℓ ∧ (vLookup n j 0 n).2.1 ∈ S;
  · refine' ⟨ ⟨ n / 2 + wOff n ℓ + ( vLookup n j 0 n ).2.1, _ ⟩, _, _, _ ⟩;
    any_goals linarith [ hv.wfit, hS_sub _ h_case2.2, show wOff n ( ℓ + 1 ) = wOff n ℓ + recSeq n ( ℓ + 1 ) from rfl ];
    · convert wVertex_mem_smallCl n ℓ S ( vLookup n j 0 n |>.2.1 ) hv ( hS_sub _ h_case2.2 ) h_case2.2 using 1;
    · exact isGeneric_false_of_ge _ _ ( by simp +arith +decide );
    · apply wvAdj_false_of_eq;
      convert wLookup_at_level n ℓ ( vLookup n j 0 n |>.2.1 ) _ _ _ using 1;
      any_goals exact ( vLookup n j 0 n ).2.2;
      · grind;
      · exact hS_sub _ h_case2.2;
      · exact hv.fuel;
      · exact hv.wfit.trans' ( Nat.le_add_left _ _ );
      · grind;
  · obtain ⟨p, hp⟩ : ∃ p ∈ S, p < recSeq n (ℓ + 1) := by
      exact ⟨ _, hS_ne.choose_spec, hS_sub _ hS_ne.choose_spec ⟩;
    refine' ⟨ ⟨ n / 2 + wOff n ℓ + p, _ ⟩, _, _, _ ⟩;
    any_goals exact wVertex_mem_smallCl n ℓ S p hv hp.2 hp.1;
    · unfold isGeneric; simp +decide [ ] ;
      exact le_add_of_le_of_nonneg ( Nat.le_add_right _ _ ) ( Nat.zero_le _ );
    · apply wvAdj_diff_level;
      convert wLookup_at_level n ℓ p hp.2 hv.fuel _ using 1;
      grind;
      exact hv.wfit.trans' ( Nat.le_add_left _ _ );
      exact Prod.ext rfl rfl;
      unfold vNotInLevel at hnotV; aesop;

/-! ## Maximality -/

/-
The small clique is maximal.
-/
lemma smallCl_isMaximal (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ)
    (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1))
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → smallCl n ℓ S ⊆ t →
      t = smallCl n ℓ S := by
  intros t ht ht_sub
  apply Finset.Subset.antisymm;
  · intro v hv;
    rcases v with ( _ | _ | _ | _ | _ ) <;> simp_all +decide [ SimpleGraph.IsClique ];
    · rename_i i;
      by_cases hi : n / 2 ≤ (i : ℕ);
      · by_cases hi' : wInLevel n ℓ S i = true;
        · grind +locals;
        · obtain ⟨ j, hj₁, hj₂ ⟩ := y_blocked_by_cStar n ℓ S i ‹_› hi ( by simpa using hi' ) hS_prop;
          have := ht ( ht_sub hj₁ ) hv; simp_all +decide [ spGraph ] ;
          unfold spAdj at this; simp_all +decide [ isGeneric ] ;
          grind;
      · have := ht ( show SpVtx.z ∈ t from ht_sub ( z_mem_smallCl n ℓ S ) ) hv; simp_all +decide [ spGraph ] ;
        unfold spAdj at this; simp_all +decide [ isGeneric ] ;
    · have := ht ( z_mem_smallCl n ℓ S |> fun h => ht_sub h ) hv; simp_all +decide [ spGraph ] ;
      cases this ; contradiction;
    · have := ht ( show SpVtx.z ∈ t from ht_sub ( z_mem_smallCl n ℓ S ) ) hv; simp_all +decide [ spGraph, spAdj ] ;
    · by_cases h : vNotInLevel n ℓ S ‹_› <;> simp_all +decide [ smallCl ];
      obtain ⟨ i, hi, hi' ⟩ := cStar_blocked_by_y n ℓ S _ ‹_› h hS_ne hS_sub;
      have := ht ( show SpVtx.y i ∈ t from ?_ ) hv ?_ <;> simp_all +decide [ spGraph ];
      · unfold spAdj at this; aesop;
      · unfold smallCl at hi; aesop;
    · exact z_mem_smallCl n ℓ S;
  · assumption

/-! ## IsMaximalClique combined -/

/-- Combined: the small clique is a maximal clique. -/
lemma smallCl_isMaximalClique (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ) (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1))
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    IsMaximalClique (spGraph n) (smallCl n ℓ S) :=
  ⟨smallCl_isClique n ℓ S, smallCl_isMaximal n ℓ S hv hS_ne hS_sub hS_prop⟩

/-! ## Card calculation -/

/-
Card of the w-filter.
-/
lemma wFilter_card (n ℓ : ℕ) (S : Finset ℕ) (hv : LevelValid n ℓ)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    (Finset.univ.filter fun i : Fin n => wInLevel n ℓ S i).card = S.card := by
  fapply Finset.card_bij;
  use fun a ha => (wLookup n ((a : ℕ) - n / 2) 0 n).get!.2;
  · unfold wInLevel at *; aesop;
  · simp +decide [ wInLevel ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h;
    rcases h₁ : wLookup n ( a₁ - n / 2 ) 0 n with ( _ | ⟨ wl₁, wp₁ ⟩ ) <;> rcases h₂ : wLookup n ( a₂ - n / 2 ) 0 n with ( _ | ⟨ wl₂, wp₂ ⟩ ) <;> simp_all +decide ;
    have := wLookup_offset_eq n ( a₁ - n / 2 ) 0 n ℓ wp₂ h₁; have := wLookup_offset_eq n ( a₂ - n / 2 ) 0 n ℓ wp₂ h₂; simp_all +decide [ Fin.ext_iff ] ;
    omega;
  · intro b hb;
    refine' ⟨ ⟨ n / 2 + wOff n ℓ + b, _ ⟩, _, _ ⟩ <;> norm_num [ wInLevel ];
    · have := hv.wfit; have := hS_sub b hb; have := wOff_succ n ℓ; norm_num at *; omega;
    · rw [ show n / 2 + wOff n ℓ + b - n / 2 = wOff n ℓ + b by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      rw [ wLookup_at_level ];
      · grind;
      · exact hS_sub b hb;
      · exact hv.fuel;
      · exact hv.wfit.trans' ( Nat.le_add_left _ _ );
    · rw [ show n / 2 + wOff n ℓ + b - n / 2 = wOff n ℓ + b by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      rw [ wLookup_at_level ] <;> norm_num [ hS_sub b hb, hv.fuel ];
      have := hv.wfit; norm_num [ wOff ] at *; omega;

/-
Card of the v-filter.
-/
lemma vFilter_card (n ℓ : ℕ) (S : Finset ℕ) (hv : LevelValid n ℓ) :
    (Finset.univ.filter fun j : Fin (spA n) => vNotInLevel n ℓ S j).card =
    (Finset.range (recSeq n (ℓ + 1)) \ S).sum (fun q => 2 ^ q + 1) := by
  -- To prove the equality of the cardinalities, we can use the fact that the function mapping j to (q, s)
  -- is a bijection between the filter and the sigma type.
  have h_bij : Finset.image (fun j : Fin (spA n) => ((vLookup n j 0 n).2.1, (vLookup n j 0 n).2.2))
        (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true)) =
      Finset.biUnion (Finset.range (recSeq n (ℓ + 1)) \ S)
        (fun q => Finset.image (fun s => (q, s)) (Finset.range (2 ^ q + 1))) := by
    ext ⟨q, s⟩;
    constructor;
    · simp [vNotInLevel];
      intro x hx₁ hx₂ hx₃; have := vLookup_pos_bound n x 0 n ℓ q s; simp_all +decide ;
      exact this ( Prod.ext hx₁ hx₃ ) hv.fuel;
    · simp +zetaDelta at *;
      intro hq hqS hs
      use ⟨vOff n ℓ + cPosOff q + s, by
        have h_bound : cPosOff q + s < cPosOff (recSeq n (ℓ + 1)) := by
          refine' lt_of_lt_of_le _ ( cPosOff_mono hq );
          simp +arith +decide [ cPosOff ];
          grind;
        linarith [ hv.vfit, show vOff n ( ℓ + 1 ) = vOff n ℓ + levelVSize n ℓ from rfl, cPosOff_eq_levelVSize n ℓ ]⟩
      generalize_proofs at *;
      have h_vLookup : vLookup n (vOff n ℓ + cPosOff q + s) 0 n = (ℓ, q, s) := by
        apply vLookup_at_level;
        · assumption;
        · linarith;
        · exact hv.fuel;
        · exact hv.vfit;
      unfold vNotInLevel; aesop;
  have h_card_eq : Finset.card (Finset.image (fun j : Fin (spA n) => ((vLookup n j 0 n).2.1, (vLookup n j 0 n).2.2))
        (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true))) =
      Finset.card (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true)) := by
    apply Finset.card_image_of_injOn;
    intro j hj j' hj' h_eq;
    have h_eq_vLookup : (vLookup n j 0 n).1 = (vLookup n j' 0 n).1 := by
      unfold vNotInLevel at hj hj'; aesop;
    have h_eq_vLookup : j.val = vOff n (vLookup n j 0 n).1 + cPosOff (vLookup n j 0 n).2.1 + (vLookup n j 0 n).2.2 := by
      have := vLookup_offset_eq n j.val 0 n (vLookup n j.val 0 n).1 (vLookup n j.val 0 n).2.1 (vLookup n j.val 0 n).2.2 rfl (by
      exact Nat.zero_le _);
      convert this using 1
    have h_eq_vLookup' : j'.val = vOff n (vLookup n j' 0 n).1 + cPosOff (vLookup n j' 0 n).2.1 + (vLookup n j' 0 n).2.2 := by
      convert vLookup_offset_eq n j'.val 0 n ( vLookup n j'.val 0 n |> Prod.fst ) ( vLookup n j'.val 0 n |> Prod.snd |> Prod.fst )
        ( vLookup n j'.val 0 n |> Prod.snd |> Prod.snd ) rfl ( by linarith [ hv.fuel ] ) using 1;
    grind;
  rw [ ← h_card_eq, h_bij, Finset.card_biUnion ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_image_of_injective ] <;> aesop_cat;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

/-
The card of the small clique.
-/
lemma smallCl_card (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    (smallCl n ℓ S).card =
    1 + recSeq n (ℓ + 1) + (Finset.range (recSeq n (ℓ + 1)) \ S).sum (2 ^ ·) := by
  rw [ smallCl ];
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    rw [ wFilter_card n ℓ S hv hS_sub, vFilter_card n ℓ S hv ];
    simp +arith +decide [ Finset.sum_add_distrib, Finset.card_sdiff, * ];
    rw [ Finset.inter_eq_left.mpr fun x hx => Finset.mem_range.mpr ( hS_sub x hx ),
      add_tsub_cancel_of_le ( le_trans ( Finset.card_le_card
        ( show S ⊆ Finset.range ( recSeq n ( ℓ + 1 ) ) from fun x hx => Finset.mem_range.mpr ( hS_sub x hx ) ) ) ( by simp ) ) ];
  · aesop;
  · simp +decide [ Finset.disjoint_left ]

/-! ## Level validity lemmas -/

lemma recSeq1_le_half (n : ℕ) (hn : n ≥ 16) : recSeq n 1 ≤ n / 2 := by
  have h_log_lt : Nat.log 2 (n - 1) < n / 2 := by
    refine' Nat.log_lt_of_lt_pow _ _; · omega
    · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num
      · exact Nat.le_induction (by decide) (fun m hm ih => by rw [pow_succ']; omega) k (show k ≥ 8 by linarith)
      · norm_num [Nat.add_div]
        exact Nat.le_induction (by decide) (fun n hn ih => by rw [pow_succ']; linarith) k (show k ≥ 8 by linarith)
  unfold recSeq; unfold recSeq; split_ifs <;> omega

lemma level0_valid (n : ℕ) (hn : n ≥ 16) : LevelValid n 0 := by
  constructor
  · unfold recSeq; split_ifs <;> norm_num
    exact Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) (Nat.le_sub_one_of_lt (by linarith)))
  · simp +arith +decide [wOff]
    linarith [Nat.div_mul_le_self n 2, recSeq1_le_half n hn]
  · rcases n with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;> simp +arith +decide [spA] at *
    unfold spAux; simp +arith +decide [levelVSize]
    split_ifs <;> simp_all +arith +decide [recSeq]
  · linarith

set_option maxHeartbeats 3200000 in
lemma level1_valid (n : ℕ) (hn : n ≥ 16) : LevelValid n 1 := by
  constructor;
  · exact recSeq_ge_two n 1 (recSeq_ge_two n 0 (show n ≥ 2 by omega));
  · rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp +arith +decide [ ] at *;
    simp +arith +decide [ recSeq ];
    rcases k : Nat.log 2 ( n + 15 ) with ( _ | _ | k ) <;> simp_all +arith +decide;
    · omega;
    · rw [ Nat.log_eq_iff ] at k <;> norm_num at *;
      rename_i k';
      rcases k' with ( _ | _ | k' ) <;> simp +arith +decide [ Nat.pow_succ' ] at *;
      · norm_num [ k ];
      · have h_log : Nat.log 2 (k' + 4) ≤ k' + 2 := by
          refine Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ?_ ?_ ) <;> norm_num;
          exact Nat.recOn k' ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith;
        linarith [ Nat.div_mul_le_self ( n + 16 ) 2,
          show 2 ^ k' ≥ k' + 1 from Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn ] ];
  · unfold vOff; simp +arith +decide [ spA ] ;
    rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ levelVSize ] at *;
    unfold recSeq; simp +arith +decide [ spAux ] ;
    split_ifs <;> norm_num [ recSeq ] at *;
    any_goals split_ifs at * <;> linarith;
    · exact absurd ‹Nat.log 2 ( n + 2 ) ≤ 1› ( not_le_of_gt ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) );
    · unfold spAux; simp +arith +decide [ Nat.pow_succ' ] ;
      rcases k : Nat.log 2 ( n + 2 ) with ( _ | _ | _ | k ) <;> simp_all +arith +decide [ ];
      split_ifs <;> simp_all +arith +decide [ ];
  · grind

lemma recSeq1_ge_four' (n : ℕ) (hn : n ≥ 16) : recSeq n 1 ≥ 4 := by
  rw [show recSeq n 1 = if n ≤ 2 then 2 else Nat.log 2 (n - 1) + 1 from rfl]
  split_ifs <;> linarith [Nat.le_log_of_pow_le (by decide) (by omega : n - 1 ≥ 2 ^ 3)]

lemma level0_max_ge_n' (n : ℕ) (hn : n ≥ 3) :
    2 ^ (recSeq n 1) + recSeq n 1 ≥ n := by
  rw [show recSeq n 1 = Nat.log 2 (n - 1) + 1 from ?_]
  · exact le_add_of_le_of_nonneg (Nat.le_of_pred_lt (Nat.lt_pow_succ_log_self (by decide) _)) (Nat.zero_le _)
  · rcases n with (_ | _ | _ | n) <;> simp +arith +decide [recSeq] at *

lemma level0_strict_bound (n : ℕ) (hn : n ≥ 3) :
    n < 2 ^ (recSeq n 1) + recSeq n 1 := by
  have h : 2 ^ (recSeq n 1) ≥ n := by
    rcases n with (_ | _ | _ | _ | _ | _ | _ | n) <;> simp_all +arith +decide []
    exact Nat.lt_pow_succ_log_self (by decide) _
  linarith [show recSeq n 1 > 0 from Nat.recOn n (by trivial) fun n ihn => by (unfold recSeq; aesop)]

/-! ## Maximal clique at a level -/

/-
For any d in [k+2, 2^k+k-1], ∃ maximal clique of size d at level ℓ.
-/
lemma small_clique_at_level (n ℓ d : ℕ) (hv : LevelValid n ℓ)
    (hd_lo : recSeq n (ℓ + 1) + 2 ≤ d)
    (hd_hi : d ≤ 2 ^ recSeq n (ℓ + 1) + recSeq n (ℓ + 1) - 1) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  refine' ⟨ _, _, _ ⟩;
  exact smallCl n ℓ ( Finset.range ( recSeq n ( ℓ + 1 ) ) \ ( Finset.image ( fun i : Fin ( recSeq n ( ℓ + 1 ) ) => i.val )
    ( Classical.choose ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) ) ) ) );
  · refine' smallCl_isMaximalClique n ℓ _ hv _ _ _;
    · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
      contrapose! this; simp_all +decide [ Finset.ext_iff ] ;
      have h_sum_eq : ∑ i ∈ Classical.choose (binary_expansion (recSeq n (ℓ + 1))
          (d - (recSeq n (ℓ + 1) + 1)) (by omega)), 2 ^ (i : ℕ)
          = ∑ i ∈ Finset.range (recSeq n (ℓ + 1)), 2 ^ i := by
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> aesop;
      rw [ h_sum_eq, Nat.geomSum_eq ] <;> norm_num;
      omega;
    · aesop;
    · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
      contrapose! this;
      rw [ Finset.sum_eq_zero ] <;> norm_num;
      · omega;
      · grind;
  · convert smallCl_card n ℓ _ hv _ using 1;
    · rw [ Finset.sdiff_sdiff_eq_self ];
      · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
        rw [ Finset.sum_image ];
        · omega;
        · exact fun x hx y hy hxy => Fin.ext hxy;
      · exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr i.2;
    · aesop

/-! ## Coverage -/

/-
When ℓ ≥ 1 and recSeq n (ℓ+1) ≥ 4, n must be at least 257.
-/
lemma n_ge_257_of_deep (n ℓ : ℕ) (hn : n ≥ 16)
    (hv : LevelValid n ℓ) (hℓ : ℓ ≥ 1) (h4 : recSeq n (ℓ + 1) ≥ 4) :
    n ≥ 257 := by
  -- By definition of recSeq, we know that recSeq n 2 ≥ 4.
  have h_recSeq2 : recSeq n 2 ≥ 4 := by
    have h_recSeq2 : ∀ k ≥ 2, recSeq n k ≥ 4 → recSeq n 2 ≥ 4 := by
      intros k hk h4k
      induction' hk with k hk ih;
      · assumption;
      · apply ih;
        contrapose! h4k;
        interval_cases _ : recSeq n k <;> simp_all +decide [ recSeq ];
    grind;
  contrapose! h_recSeq2;
  interval_cases n <;> decide

/-
The sum of iterated logs is bounded: wOff n k ≤ 2 * recSeq n 1
    when all intermediate recSeq values are ≥ 4.
-/
lemma wOff_bound_ge4 (n k : ℕ)
    (hk : ∀ i, 1 ≤ i → i ≤ k → recSeq n i ≥ 4) :
    wOff n k ≤ 2 * recSeq n 1 := by
  rcases k with ( _ | _ | k ) <;> simp +arith +decide [ * ];
  have h_ineq : ∀ i, 1 ≤ i → i ≤ k + 1 → recSeq n (i + 1) ≤ recSeq n i - 1 := by
    intros i hi1 hi2;
    rw [ recSeq ];
    split_ifs <;> norm_num;
    · linarith [ hk i hi1 ( by linarith ) ];
    · exact Nat.log_lt_of_lt_pow ( Nat.sub_ne_zero_of_lt ( by linarith ) )
        ( by exact Nat.recOn ( recSeq n i - 1 ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; linarith );
  have h_ineq_sum : ∀ i, 1 ≤ i → i ≤ k + 1 → recSeq n i + ∑ j ∈ Finset.Icc 1 i, recSeq n j ≤ 2 * recSeq n 1 := by
    intro i hi₁ hi₂; induction hi₁ <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
    · linarith;
    · rename_i m hm ih;
      have h_subst : 2 * recSeq n (m + 1) ≤ recSeq n m := by
        have h_subst : recSeq n (m + 1) ≤ Nat.log 2 (recSeq n m - 1) + 1 := by
          rw [ recSeq ];
          grind +splitImp;
        have h_subst : 2 ^ (Nat.log 2 (recSeq n m - 1)) ≤ recSeq n m - 1 := by
          exact Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith [ hk m hm ( by linarith ) ] ) );
        have h_subst : 2 * (Nat.log 2 (recSeq n m - 1) + 1) ≤ recSeq n m := by
          rcases x : Nat.log 2 ( recSeq n m - 1 ) with ( _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ ];
          · exact le_of_not_gt fun h => by have := hk m hm ( by linarith ) ; interval_cases recSeq n m ;
          · exact hk m hm ( by linarith );
          · grind;
          · omega;
          · have h_subst : 2 ^ k ≥ k + 1 := by
              exact Nat.recOn k ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith;
            omega;
        linarith;
      linarith [ ih ( by linarith ) ];
  specialize h_ineq_sum ( k + 1 ) ; simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
  rw [ show wOff n k = ∑ i ∈ Finset.Icc 1 k, recSeq n i from ?_ ];
  · linarith! [ h_ineq ( k + 1 ) ( by linarith ) ( by linarith ),
      Nat.sub_add_cancel ( show 1 ≤ recSeq n ( k + 1 ) from by linarith [ hk ( k + 1 ) ( by linarith ) ( by linarith ) ] ) ];
  · refine' Nat.recOn k _ _ <;> simp +arith +decide [ *, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

/-
For n ≥ 257, 4 * (recSeq n 1) ≤ n.
-/
lemma four_recSeq_le (n : ℕ) (hn : n ≥ 257) : 4 * recSeq n 1 ≤ n := by
  rw [ show recSeq n 1 = Nat.log 2 ( n - 1 ) + 1 from ?_ ];
  · -- We'll use that $2^{Nat.log 2 (n - 1)} \leq n - 1$ and $Nat.log 2 (n - 1) \leq \frac{n}{4} - 1$ for $n \geq 257$.
    have h_log : 2 ^ (Nat.log 2 (n - 1)) ≤ n - 1 := by
      exact Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith ) )
    have h_log_bound : Nat.log 2 (n - 1) ≤ n / 4 - 1 := by
      have h_log_bound : ∀ k ≥ 8, 2 ^ k > 4 * k + 3 := by
        exact fun k hk => by induction hk <;> norm_num [ Nat.pow_succ ] at * ; linarith;
      grind +locals;
    omega;
  · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ recSeq ] at *;
    aesop

/-
vOff is bounded by spA when the recursive branch is taken at each level.
-/
set_option maxHeartbeats 400000 in
lemma vOff_le_spA (n ℓ : ℕ) (hn : n ≥ 3)
    (hall : ∀ i, 0 ≤ i → i ≤ ℓ → recSeq n (i + 1) ≥ 3) :
    vOff n (ℓ + 1) ≤ spA n := by
  induction' ℓ with ℓ ih generalizing n;
  · unfold vOff; simp +arith +decide [ spA ] ;
    rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ levelVSize, spAux ] at *;
    split_ifs <;> simp_all +arith +decide [ recSeq ];
  · -- By definition of $vOff$, we have $vOff n (ℓ + 2) = levelVSize n 0 + vOff (recSeq n 1) (ℓ + 1)$.
    have hvOff_succ : vOff n (ℓ + 2) = levelVSize n 0 + vOff (recSeq n 1) (ℓ + 1) := by
      have hvOff_succ : ∀ k ≥ 1, vOff n (k + 1) = levelVSize n 0 + vOff (recSeq n 1) k := by
        intro k hk;
        induction hk <;> simp_all +arith +decide [ vOff ];
        · unfold levelVSize; aesop;
        · rename_i k hk ih;
          rw [ show levelVSize n ( k + 1 ) = levelVSize ( recSeq n 1 ) k from ?_ ];
          · grind;
          · have h_recSeq_shift : ∀ k ≥ 1, recSeq n (k + 1) = recSeq (recSeq n 1) k := by
              intro k hk; induction hk <;> simp_all +arith +decide [ recSeq ] ;
            unfold levelVSize; aesop;
      exact hvOff_succ _ le_add_self;
    -- By definition of $spA$, we have $spA n = levelVSize n 0 + spA (recSeq n 1)$.
    have hspA_succ : spA n = levelVSize n 0 + spA (recSeq n 1) := by
      unfold spA; rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ * ] at *;
      rw [ spAux ];
      unfold levelVSize; simp +arith +decide [ recSeq ] ;
      intro h; have := hall 0; simp_all +arith +decide [ recSeq ] ;
      linarith;
    specialize ih ( recSeq n 1 ) ?_ ?_ <;> simp_all +decide;
    intro i hi; convert hall ( i + 1 ) ( by linarith ) using 1;
    induction i <;> simp_all +decide [ recSeq ];
    grind

/-
Level validity propagates: from level ℓ to ℓ+1 when recSeq ≥ 4.

spAux m ≥ 2^(recSeq m 1) + recSeq m 1 for m ≥ 3.
-/
lemma spAux_ge_levelVSize (m : ℕ) (hm : m ≥ 3) :
    spAux m ≥ 2 ^ (recSeq m 1) + recSeq m 1 := by
  unfold spAux recSeq;
  rcases m with ( _ | _ | _ | m ) <;> simp +arith +decide [ recSeq ] at *;
  split_ifs <;> simp_all +arith +decide [ Nat.pow_succ' ];
  exact spAux_pos _

/-
The recSeq sequence is non-increasing for values ≥ 4:
    if recSeq n j ≥ 4, then recSeq n i ≥ 4 for all i ≤ j.
-/
lemma recSeq_mono_ge4 (n i j : ℕ) (hij : i ≤ j) (hj : recSeq n j ≥ 4) :
    recSeq n i ≥ 4 := by
  contrapose! hj;
  induction hij <;> simp_all +decide [ recSeq ];
  interval_cases recSeq n ‹_› <;> decide

/-
For n ≥ 257, 6 * recSeq n 1 ≤ n.
-/
lemma six_recSeq_le (n : ℕ) (hn : n ≥ 257) : 6 * recSeq n 1 ≤ n := by
  rw [ show recSeq n 1 = Nat.log 2 ( n - 1 ) + 1 from ?_ ];
  · have := Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith : 1 < n ) );
    rcases k : Nat.log 2 ( n - 1 ) with ( _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ ];
    any_goals omega;
    rename_i k';
    exact le_trans ( by
      { exact Nat.recOn k' ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith } )
      ( Nat.le_trans this ( Nat.sub_le _ _ ) );
  · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ recSeq ] at *;
    aesop

/-
Level validity propagates: from level ℓ to ℓ+1 when recSeq ≥ 4.
-/
set_option maxHeartbeats 1200000 in
lemma next_level_valid (n ℓ : ℕ) (hn : n ≥ 16)
    (hv : LevelValid n ℓ) (h4 : recSeq n (ℓ + 1) ≥ 4) :
    LevelValid n (ℓ + 1) := by
  constructor;
  · exact recSeq_ge_two _ _ ( by linarith );
  · -- Using the bound $wOff n (ℓ + 1) ≤ 2 * recSeq n 1$ and $recSeq n (ℓ + 2) ≤ recSeq n 1$, we get:
    have h_wOff_bound : wOff n (ℓ + 1 + 1) ≤ 2 * recSeq n 1 + recSeq n 1 := by
      have h_wOff_bound : wOff n (ℓ + 1) ≤ 2 * recSeq n 1 := by
        apply wOff_bound_ge4;
        exact fun i a a_1 ↦ recSeq_mono_ge4 n i (ℓ + 1) a_1 h4;
      have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n (i + 1) ≤ recSeq n i := by
        intros i hi1 hi2;
        have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n i ≥ 3 := by
          have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n i ≥ 4 := by
            intros i hi1 hi2;
            apply recSeq_mono_ge4 n i (ℓ + 1) hi2 h4;
          grind +splitImp;
        exact Nat.le_of_lt ( recSeq_decreasing n i ( h_recSeq_bound i hi1 hi2 ) );
      have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n (i + 1) ≤ recSeq n 1 := by
        intro i hi₁ hi₂; induction hi₁ <;> simp_all +arith +decide;
        grind;
      exact add_le_add h_wOff_bound ( h_recSeq_bound _ ( by linarith ) ( by linarith ) );
    by_cases h₂ : n ≥ 257;
    · linarith [ Nat.div_mul_le_self n 2, six_recSeq_le n h₂ ];
    · -- Since $n < 257$, we can check each value of $n$ individually.
      have h_check : ∀ n ∈ Finset.Icc 16 256, ∀ ℓ ∈ Finset.range n, (recSeq n (ℓ + 1) ≥ 4) → (n / 2 + wOff n (ℓ + 1 + 1) ≤ n) := by
        set_option maxRecDepth 100000 in decide +revert;
      exact h_check n ( Finset.mem_Icc.mpr ⟨ hn, by linarith ⟩ ) ℓ ( Finset.mem_range.mpr ( by linarith [ hv.fuel ] ) ) h4;
  · by_cases h_recSeq_ge_3 : recSeq n (ℓ + 2) ≥ 3;
    · apply vOff_le_spA n (ℓ + 1) (by omega);
      intros i hi_nonneg hi_le_ℓ_plus_1
      by_cases hi : i ≤ ℓ;
      · have := recSeq_mono_ge4 n ( i + 1 ) ( ℓ + 1 ) ( by linarith ) h4; linarith;
      · grind;
    · interval_cases _ : recSeq n ( ℓ + 2 ) <;> simp_all +decide [ vOff ];
      · exact absurd ‹_› ( by linarith [ recSeq_ge_two n ( ℓ + 1 ) ( by linarith ) ] );
      · exact absurd ‹_› ( by exact ne_of_gt ( Nat.le_trans ( by decide ) ( recSeq_ge_two _ _ ( by linarith ) ) ) );
      · have h_vOff_le_spA : spA n = vOff n (ℓ + 1) + spAux (recSeq n (ℓ + 1)) := by
          have h_vOff_le_spA : ∀ ℓ, (∀ i, 0 ≤ i → i ≤ ℓ → recSeq n (i + 1) ≥ 3) → spA n
              = vOff n (ℓ + 1) + spAux (recSeq n (ℓ + 1)) := by
            intro ℓ hℓ; induction' ℓ with ℓ ih <;> simp_all +decide [ vOff ] ;
            · unfold spA levelVSize; simp +decide [ recSeq ] ;
              rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ ];
              rw [ spAux ] ; simp +arith +decide [ ];
              exact fun h => absurd h ( by exact not_le_of_gt ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) );
            · rw [ ih fun i hi => hℓ i ( by linarith ) ];
              unfold levelVSize; simp +arith +decide [ * ] ;
              rw [ show recSeq n ( ℓ + 2 ) = Nat.log 2 ( recSeq n ( ℓ + 1 ) - 1 ) + 1 from ?_ ];
              · rcases k : recSeq n ( ℓ + 1 ) with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
                · grind +revert;
                · linarith [ hℓ ℓ ( by linarith ) ];
                · linarith [ hℓ ℓ ( by linarith ) ];
                · rw [ spAux ] ; simp +arith +decide [ ];
                  intro h; interval_cases _ : Nat.log 2 ( _ + 2 ) <;> simp_all +decide ;
                  decide +kernel;
              · exact if_neg ( by linarith [ hℓ ℓ ( by linarith ) ] );
          apply h_vOff_le_spA;
          intros i hi_nonneg hi_le_ℓ
          have h_recSeq_ge_3 : recSeq n (i + 1) ≥ 4 := by
            apply recSeq_mono_ge4 n (i + 1) (ℓ + 1) (by linarith) h4
          linarith [h_recSeq_ge_3];
        have h_spAux_ge_levelVSize : spAux (recSeq n (ℓ + 1))
            ≥ levelVSize (recSeq n (ℓ + 1)) 0 + 1 := by
          convert spAux_ge_levelVSize ( recSeq n ( ℓ + 1 ) ) ( by linarith ) using 1;
          unfold levelVSize; simp +arith +decide [ * ] ;
          rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ];
        unfold levelVSize at * ; simp_all +decide [ Nat.pow_succ' ];
        unfold levelVSize at * ; simp_all +decide [ ];
        unfold recSeq at * ; simp_all +decide [ Nat.pow_succ' ];
        split_ifs at * <;> simp_all +arith +decide [ ];
        · exact Nat.le_of_add_left_le h_spAux_ge_levelVSize;
        · grind +suggestions;
  · have := hv.recSeq_ge; (
      have := hv.wfit; ( have := hv.vfit; ( have := hv.fuel; ( norm_num at *; ) ) ) );
    -- By definition of $wOff$, we know that $wOff n ℓ \geq 4 * ℓ$.
    have hwOff_ge : wOff n ℓ ≥ 4 * ℓ := by
      have hwOff_ge : ∀ i ≤ ℓ, recSeq n (i + 1) ≥ 4 := by
        intros i hi;
        apply recSeq_mono_ge4 n (i + 1) (ℓ + 1) (by linarith) h4;
      have hwOff_ge : ∀ i ≤ ℓ, wOff n i ≥ 4 * i := by
        intro i hi; induction' i with i ih <;> simp_all +decide [ Nat.mul_succ, wOff ] ;
        linarith [ ih ( Nat.le_of_lt hi ), hwOff_ge i ( Nat.le_of_lt hi ) ];
      exact hwOff_ge ℓ le_rfl;
    omega

/-- Recursive coverage with n ≥ 16 hypothesis. -/
lemma recursive_coverage (n ℓ d : ℕ)
    (hn : n ≥ 16)
    (hv : LevelValid n ℓ)
    (hd_lo : 5 ≤ d)
    (hd_hi : d ≤ 2 ^ recSeq n (ℓ + 1) + recSeq n (ℓ + 1) - 1) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  -- By strong induction on recSeq n (ℓ+1)
  suffices h : ∀ k l, k = recSeq n (l + 1) → LevelValid n l →
      5 ≤ d → d ≤ 2 ^ k + k - 1 →
      ∃ s : Finset (SpVtx n (spA n)), IsMaximalClique (spGraph n) s ∧ s.card = d from
    h _ ℓ rfl hv hd_lo hd_hi
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro l hk_eq hv' hd1' hd2'
    by_cases hbig : d ≥ k + 2
    · exact small_clique_at_level n l d hv' (by omega) (by subst hk_eq; omega)
    · -- d < k + 2, so k ≥ 4 (since d ≥ 5)
      push_neg at hbig
      have hk4 : k ≥ 4 := by omega
      -- Level overlap gives the range at next level covers d
      have h_overlap := level_overlap n (l + 1) (by rw [← hk_eq]; omega)
      set k' := recSeq n (l + 2) with hk'_def
      have h_lt : k' < k := by
        rw [hk_eq]; exact recSeq_decreasing n (l + 1) (by rw [← hk_eq]; omega)
      have hd_next : d ≤ 2 ^ k' + k' - 1 := by omega
      -- Need LevelValid n (l+1)
      have hv'' : LevelValid n (l + 1) :=
        next_level_valid n l hn hv' (by rw [← hk_eq]; omega)
      exact ih k' h_lt (l + 1) rfl hv'' hd1' hd_next

/-
For each d with 5 ≤ d ≤ n, there exists a maximal clique of size d.
-/
theorem small_clique_exists (n : ℕ) (hn : n ≥ 16) (d : ℕ)
    (hd1 : 5 ≤ d) (hd2 : d ≤ n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  apply recursive_coverage n 0 d hn (level0_valid n hn) hd1 (by
    exact le_trans hd2 ( Nat.le_sub_one_of_lt ( level0_strict_bound n ( by linarith ) ) ))

/-
# Spencer's Lower Bound — Main Theorem

This file connects Spencer's graph construction to the disproof
of Erdős Problem 927.
-/


/-! ## Core combinatorial claim -/

/-- For each size d with 5 ≤ d ≤ spB n, there exists a maximal clique of size d
  in Spencer's graph. This is the core combinatorial claim. -/
theorem spencer_clique_sizes (n : ℕ) (hn : n ≥ 16) :
    ∀ d : ℕ, 5 ≤ d → d ≤ spB n →
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  intro d hd1 hd2
  by_cases hmed : d ≤ 2 ^ n + n
  · by_cases hsmall : d ≤ n
    · exact small_clique_exists n hn d hd1 hsmall
    · exact medium_clique_exists n (by omega) d (by omega) hmed
  · exact big_clique_exists n hn d (by omega) hd2

/-! ## Main bound -/

/-- spB n ≥ 5 for n ≥ 2. -/
lemma spB_ge_five (n : ℕ) (hn : n ≥ 2) : spB n ≥ 5 := by
  unfold spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-- For each n ≥ 16, Spencer's construction gives
  g(spN n) ≥ spB n - 4. -/
theorem spencer_construction (n : ℕ) (hn : n ≥ 16) :
    spN n ≤ n + 6 + g (spN n) := by
  have hcliques := spencer_clique_sizes n hn
  have hcard := spVtx_card n (by omega : n ≥ 2)
  have hge : spB n - 4 ≤ g (spN n) := by
    have hsub : Finset.Icc 5 (spB n) ⊆ maximalCliqueSizes (spGraph n) := by
      apply maximalCliqueSizes_card_ge
      intro k hk
      simp [Finset.mem_Icc] at hk
      exact hcliques k hk.1 hk.2
    have hcard_icc : (Finset.Icc 5 (spB n)).card = spB n - 4 := by
      rw [Nat.card_Icc]
      have := spB_ge_five n (by omega : n ≥ 2)
      omega
    calc spB n - 4 = (Finset.Icc 5 (spB n)).card := hcard_icc.symm
      _ ≤ (maximalCliqueSizes (spGraph n)).card :=
          Finset.card_le_card hsub
      _ ≤ g (Fintype.card (SpVtx n (spA n))) :=
          g_ge_of_card (spGraph n) rfl
      _ = g (spN n) := by rw [hcard]
  have heq := spN_eq n (by omega : n ≥ 2)
  omega

/-- Spencer's lower bound with log: for n ≥ 16,
  g(spN n) ≥ spN n - Nat.log 2 (spN n) - 6. -/
theorem spencer_lower_bound (n : ℕ) (hn : n ≥ 16) :
    spN n ≤ g (spN n) + Nat.log 2 (spN n) + 6 := by
  rw [spencer_log n hn]
  linarith [spencer_construction n hn]

/-- The disproof: for any C, there exists N ≥ 2 with
  g(N) + log₂(N) + logStar(N) > N + C. -/
theorem spencer_disproof_key (C : ℕ) :
    ∃ N : ℕ, N ≥ 2 ∧ N + C < g N + Nat.log 2 N + logStar N := by
  obtain ⟨m, hm⟩ := logStar_unbounded (C + 6)
  set n := max m 16 with hn_def
  have hn16 : n ≥ 16 := le_max_right _ _
  have hnm : n ≥ m := le_max_left _ _
  use spN n
  refine ⟨spN_ge_two n (by omega), ?_⟩
  have hsp := spencer_lower_bound n hn16
  have hls : C + 6 < logStar (spN n) :=
    lt_of_lt_of_le hm (logStar_mono (le_trans hnm (le_spN n)))
  omega

/-! ## The Disproof -/

/-- **Erdős Problem 927** ([Er66b; Er71, p.101; Er69b], disproved by Spencer
[Sp71]). Erdős conjectured `g(n) = n − ⌊log₂ n⌋ − log*(n) + O(1)`, where `g(n)`
is the maximum number of distinct sizes of maximal cliques in a graph on `n`
vertices and `log*` is the iterated logarithm. The upper-bound direction of
the conjecture states that there is some `C` with
`g(n) + ⌊log₂ n⌋ + log*(n) ≤ n + C` for all `n ≥ 2`. Spencer's construction
gives graphs whose maximal-clique sizes span an interval of length
`n − ⌊log₂ n⌋ − O(1)`, refuting this upper bound. -/
theorem erdos_927 :
    ¬ (∃ C : ℕ, ∀ n : ℕ, n ≥ 2 → g n + Nat.log 2 n + logStar n ≤ n + C) := by
  intro ⟨C, hC⟩
  obtain ⟨N, hN2, hN⟩ := spencer_disproof_key C
  have := hC N hN2
  omega

#print axioms erdos_927
-- 'Erdos927.erdos_927' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos927
