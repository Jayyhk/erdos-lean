import Mathlib

namespace Erdos651

/-
# Erdős Problem 651

Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in general position in
$\mathbb{R}^k$ contain $n$ which determine a convex polyhedron. Is it true that
$$f_k(n) > (1+c_k)^n$$
for some constant $c_k>0$?

The answer is **no** for every $k \geq 3$: Pohoata and Zakharov [PoZa22] proved
$f_3(n)\leq 2^{o(n)}$ (`PohoataZakharov.erdos_651_subexponential`), and the bound transfers to
every higher dimension by a generic projection. `erdos_651` states the negative answer for all
$k \geq 3$, with `erdosSzekeresNumber k n` the least number of points in general position in
$\mathbb{R}^k$ (every $k+1$ of them affinely independent) that forces $n$ in convex position
(none in the convex hull of the others). For $k = 2$ the answer is yes, by Erdős--Szekeres.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000527), proving
Pohoata and Zakharov's extraction theorem and reusing the definitions and the supporting
development of `plby/lean-proofs` (`ErdosProblems/Erdos651.lean` and its modules), whose own
headline assumes the subexponential bound as a hypothesis. The 24 modules forming the closure are
flattened here in dependency order. `erdos_651` is added here: it restates upstream's
`erdos_651_disproved_all_dimensions`, indexed by $k = d + 3$, and adds no mathematical content.

Declarations that `erdos_651` does not depend on have been removed.
-/

/-! ### Upstream module `JSP527/External/Erdos651/Definitions.lean` -/

/-! Exact geometric and asymptotic definitions for Erdős Problem 651. -/

noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def InGeneralPosition (d : ℕ) (X : Finset (Point d)) : Prop :=
  ∀ S : Finset (Point d), S ⊆ X → S.card = d + 1 →
    AffineIndependent ℝ (fun p : ↥S ↦ (p : Point d))

def InConvexPosition {d : ℕ} (X : Finset (Point d)) : Prop :=
  ∀ x ∈ X, x ∉ convexHull ℝ (↑(X.erase x) : Set (Point d))

def ContainsConvexSubset (d n : ℕ) (X : Finset (Point d)) : Prop :=
  ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = n ∧ InConvexPosition Y

def ForcesConvexSubset (d n N : ℕ) : Prop :=
  ∀ X : Finset (Point d), N ≤ X.card → InGeneralPosition d X →
    ContainsConvexSubset d n X

def HasErdosSzekeresNumber (d n : ℕ) : Prop :=
  Set.Nonempty {N : ℕ | ForcesConvexSubset d n N}

noncomputable def erdosSzekeresNumber (d n : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesConvexSubset d n N}

lemma ForcesConvexSubset.mono {d n N M : ℕ} (hNM : N ≤ M)
    (hN : ForcesConvexSubset d n N) : ForcesConvexSubset d n M := by
  intro X hMX hgp
  exact hN X (hNM.trans hMX) hgp

lemma erdosSzekeresNumber_forces {d n : ℕ}
    (h : HasErdosSzekeresNumber d n) :
    ForcesConvexSubset d n (erdosSzekeresNumber d n) := by
  exact Nat.sInf_mem h

lemma erdosSzekeresNumber_le {d n N : ℕ}
    (hN : ForcesConvexSubset d n N) :
    erdosSzekeresNumber d n ≤ N := by
  exact Nat.sInf_le hN

def HasSubexponentialUpperBound (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

def HasExponentialLowerBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (1 + c) ^ n < (f n : ℝ)

end

/-! ### Upstream module `JSP527/External/Erdos651/Asymptotic.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-! The asymptotic incompatibility at the end of the resolution of Problem 651. -/

open _root_.Filter _root_.Set
noncomputable section

theorem subexponential_not_exponentialLowerBound
    {f : ℕ → ℕ} (hf : HasSubexponentialUpperBound f) :
    ¬ HasExponentialLowerBound f := by
  rintro ⟨c, hc, hlow⟩
  let ε : ℝ := Real.logb 2 (1 + c)
  have hbase : 0 < 1 + c := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith)
  obtain ⟨n, hup, hlo⟩ := ((hf ε hε).and hlow).exists
  have heq : (2 : ℝ) ^ (ε * (n : ℝ)) = (1 + c) ^ n := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (2 : ℝ) ^ ε = 1 + c by
      dsimp [ε]
      exact Real.rpow_logb (by norm_num) (by norm_num) hbase]
    exact Real.rpow_natCast (1 + c) n
  exact (not_lt_of_ge (hup.trans_eq heq)) hlo

end

end

/-! ### Upstream module `JSP527/External/Erdos651.lean` -/

/-!
# Erdős Problem 651

For `d ≥ 2`, the higher-dimensional Erdős--Szekeres number is the least
cardinality which forces a prescribed number of points in convex position
inside every general-position point set in `ℝ^d`.

Pohoata and Zakharov proved that the three-dimensional numbers are
subexponential.  The main result below formalizes the exact logical content
of their resolution: a `2^{o(n)}` upper bound is incompatible with Erdős's
proposed fixed-base exponential lower bound.

The accompanying mathematical reconstruction, including all geometric
ingredients of Pohoata--Zakharov's proof, is in `tex/651.tex`.
-/

/-! ### Upstream module `JSP527/External/Erdos651/PohoataZakharovBridge.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-! The exact point-set statement of Pohoata--Zakharov's Theorem 1.1 and its
formal implication for Erdős Problem 651. -/

open _root_.Filter _root_.Set
noncomputable section

/-- The literal point-set, epsilon formulation of Theorem 1.1 in
Pohoata--Zakharov: every sufficiently large general-position point set in
three-space whose cardinality is at least `2 ^ (ε * n)` contains `n` points in
convex position. -/
def PohoataZakharovTheoremOneOne : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ X : Finset (Point 3),
        (2 : ℝ) ^ (ε * (n : ℝ)) ≤ (X.card : ℝ) →
        InGeneralPosition 3 X → ContainsConvexSubset 3 n X

/-- The point-set statement of Pohoata--Zakharov gives the numerical
subexponential upper bound.  The passage through an integer cardinality uses
the ceiling of `2 ^ ((ε / 2) * n)`; the factor `ε / 2` absorbs the ceiling. -/
theorem pohoataZakharovTheoremOneOne_imp_subexponential
    (hPZ : PohoataZakharovTheoremOneOne) :
    HasSubexponentialUpperBound (erdosSzekeresNumber 3) := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨n₀, hn₀⟩ := hPZ δ hδ
  rw [eventually_atTop]
  refine ⟨max n₀ ⌈(2 : ℝ) / ε⌉₊, fun n hn ↦ ?_⟩
  have hn₀n : n₀ ≤ n := (le_max_left n₀ ⌈2 / ε⌉₊).trans hn
  have hceiln : ⌈(2 : ℝ) / ε⌉₊ ≤ n := (le_max_right n₀ ⌈2 / ε⌉₊).trans hn
  have hrealn : (2 : ℝ) / ε ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceiln)
  let x : ℝ := (2 : ℝ) ^ (δ * (n : ℝ))
  let N : ℕ := ⌈x⌉₊
  have hexponent : 1 ≤ δ * (n : ℝ) := by
    have hmul : (2 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hrealn
    dsimp [δ]
    nlinarith
  have hx_two : (2 : ℝ) ≤ x := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (δ * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ = x := rfl
  have hforces : ForcesConvexSubset 3 n N := by
    intro X hNX hgp
    apply hn₀ n hn₀n X _ hgp
    exact (Nat.le_ceil x).trans (by exact_mod_cast hNX)
  have hES : erdosSzekeresNumber 3 n ≤ N := erdosSzekeresNumber_le hforces
  have hceil_lt : (N : ℝ) < x + 1 := by
    exact Nat.ceil_lt_add_one (le_trans (by norm_num) hx_two)
  have hxx : x + 1 ≤ x * x := by
    nlinarith
  have hsq : x * x = (2 : ℝ) ^ (ε * (n : ℝ)) := by
    calc
      x * x = x ^ (2 : ℕ) := by ring
      _ = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
      _ = (2 : ℝ) ^ ((δ * (n : ℝ)) * 2) := by
        dsimp [x]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (ε * (n : ℝ)) := by
        congr 1
        dsimp [δ]
        ring
  calc
    (erdosSzekeresNumber 3 n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hES
    _ ≤ x + 1 := hceil_lt.le
    _ ≤ x * x := hxx
    _ = (2 : ℝ) ^ (ε * (n : ℝ)) := hsq

end

end

/-! ### Upstream module `JSP527/External/Erdos651/ConvexCore.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Elementary convex-geometric infrastructure for Erdős Problem 651

This file records exact finite-set facts used repeatedly below: general
and convex position are hereditary, convex position is Mathlib's convex
independence, smaller exact-cardinality subsets can be selected, pointwise
separation certifies convex position, and convex position lifts through an
affine projection that is injective on the selected finite set.
-/

open Affine _root_.Function _root_.Set

noncomputable section

/-- General position is inherited by a finite subset. -/
theorem InGeneralPosition.mono {d : ℕ} {X Y : Finset (Point d)}
    (hX : InGeneralPosition d X) (hYX : Y ⊆ X) :
    InGeneralPosition d Y := by
  intro S hSY hcard
  exact hX S (hSY.trans hYX) hcard

section AffineTransport

variable {d e : ℕ}

/-- Erasing commutes with the image of a finset when the map is injective
on that finset.  The library's global-injectivity version is too strong for
projections, which are only required to separate the selected points. -/
theorem finset_image_erase_of_injOn {X : Finset (Point d)}
    (f : Point d → Point e) (hf : Set.InjOn f X) {x : Point d} (hx : x ∈ X) :
    (X.erase x).image f = (X.image f).erase (f x) := by
  ext z
  constructor
  · simp only [Finset.mem_image, Finset.mem_erase]
    rintro ⟨y, ⟨hyx, hyX⟩, rfl⟩
    refine ⟨?_, ⟨y, hyX, rfl⟩⟩
    exact fun h ↦ hyx (hf hyX hx h)
  · simp only [Finset.mem_image, Finset.mem_erase]
    rintro ⟨hfy, ⟨y, hyX, rfl⟩⟩
    exact ⟨y, ⟨fun hyx ↦ hfy (congrArg f hyx), hyX⟩, rfl⟩

/-- Convex position lifts through an affine projection, provided distinct
selected points have distinct images. -/
theorem InConvexPosition.of_image_affineMap {X : Finset (Point d)}
    (f : Point d →ᵃ[ℝ] Point e) (hf : Set.InjOn f X)
    (himage : InConvexPosition (X.image f)) : InConvexPosition X := by
  intro x hxX hxHull
  apply himage (f x) (Finset.mem_image_of_mem f hxX)
  rw [← finset_image_erase_of_injOn f hf hxX,
    Finset.coe_image, ← f.image_convexHull]
  exact ⟨x, hxHull, rfl⟩

/-- A globally injective affine map preserves convex position. -/
theorem InConvexPosition.image_affineMap {X : Finset (Point d)}
    (hX : InConvexPosition X) (f : Point d →ᵃ[ℝ] Point e)
    (hf : Function.Injective f) : InConvexPosition (X.image f) := by
  intro z hzImage hzHull
  obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.mp hzImage
  apply hX x hxX
  rw [← Finset.image_erase hf X x, Finset.coe_image,
    ← f.image_convexHull] at hzHull
  obtain ⟨y, hyHull, hyx⟩ := hzHull
  simpa only [hf hyx] using hyHull

/-- Affine equivalences preserve convex position in both directions. -/
theorem _root_.AffineEquiv.inConvexPosition_image_iff
    (f : Point d ≃ᵃ[ℝ] Point e) (X : Finset (Point d)) :
    InConvexPosition (X.image f) ↔ InConvexPosition X := by
  constructor
  · exact fun h ↦ h.of_image_affineMap f.toAffineMap f.injective.injOn
  · exact fun h ↦ h.image_affineMap f.toAffineMap f.injective

/-- If the image of a finite set is in general position, then so is the
original set. -/
theorem InGeneralPosition.of_image_affineMap {X : Finset (Point d)}
    (f : Point d →ᵃ[ℝ] Point d) (hf : Set.InjOn f X)
    (himage : InGeneralPosition d (X.image f)) : InGeneralPosition d X := by
  intro S hSX hScard
  have hfS : Set.InjOn f S := hf.mono (by
    intro x hx
    exact hSX hx)
  have hsub : S.image f ⊆ X.image f := by
    intro z hz
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem f (hSX hsS)
  have hcard : (S.image f).card = d + 1 := by
    rw [Finset.card_image_of_injOn hfS, hScard]
  have hAI := himage (S.image f) hsub hcard
  let emb : S ↪ (S.image f : Set (Point d)) :=
    ⟨fun x ↦ ⟨f x, Finset.mem_image_of_mem f x.property⟩,
      fun x y hxy ↦ Subtype.ext
        (hfS x.property y.property (Subtype.ext_iff.mp hxy))⟩
  have hcomp := hAI.comp_embedding emb
  have heq :
      ((fun p : (S.image f : Set (Point d)) ↦ (p : Point d)) ∘ emb) =
        (f ∘ fun p : S ↦ (p : Point d)) := by
    funext p
    rfl
  have hmapped : AffineIndependent ℝ
      (f ∘ fun p : S ↦ (p : Point d)) := heq ▸ hcomp
  exact AffineIndependent.of_comp f hmapped

end AffineTransport

/-- In a 3-dimensional general-position set with at least four points,
every subset of at most three points is affine-independent.  The
cardinality hypothesis is necessary because `InGeneralPosition 3` only
directly constrains four-point subsets. -/
theorem affineIndependent_of_card_le_three_of_generalPosition_three
    {X S : Finset (Point 3)} (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card)
    (hSX : S ⊆ X) (hScard : S.card ≤ 3) :
    AffineIndependent ℝ (fun p : S ↦ (p : Point 3)) := by
  obtain ⟨T, hST, hTX, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hSX (by omega : S.card ≤ 4) hXcard
  have hT : AffineIndependent ℝ (fun p : T ↦ (p : Point 3)) := by
    apply hgp T hTX
    norm_num
    exact hTcard
  exact hT.mono (by
    intro p hp
    exact hST hp)

/-- A finite 3-dimensional general-position set with at least four
points admits a generic affine projection to the plane which is injective
on the set and whose image is again in general position. -/
theorem exists_generic_plane_projection
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card) :
    ∃ π : Point 3 →ᵃ[ℝ] Point 2,
      Set.InjOn π X ∧ InGeneralPosition 2 (X.image π) := by
  classical
  let I := (X.powerset.filter fun S ↦ S.card ≤ 3)
  let bad : I → Submodule ℝ (Point 3) := fun S ↦ vectorSpan ℝ (S.1 : Set (Point 3))
  have hbad : ∀ S : I, bad S ≠ ⊤ := by
    intro S htop
    have hSX : S.1 ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    have hScard : S.1.card ≤ 3 := (Finset.mem_filter.mp S.2).2
    have hAI := affineIndependent_of_card_le_three_of_generalPosition_three
      hgp hXcard hSX hScard
    by_cases hSne : S.1.Nonempty
    · letI : Nonempty S.1 := Finset.nonempty_coe_sort.mpr hSne
      have hfin := hAI.finrank_vectorSpan_add_one
      have hrange : Set.range (fun p : S.1 ↦ (p : Point 3)) = (S.1 : Set (Point 3)) := by
        ext x
        simp
      rw [hrange] at hfin
      change vectorSpan ℝ (S.1 : Set (Point 3)) = ⊤ at htop
      rw [htop] at hfin
      have hdim : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
      rw [finrank_top, hdim, Fintype.card_coe] at hfin
      omega
    · have hSempty : S.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      simpa [bad, hSempty] using htop
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    let E : I := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset X, by simp⟩⟩
    exact hv E (by simp [bad])
  let K : Submodule ℝ (Point 3) := ℝ ∙ v
  have hKfin : Module.finrank ℝ K = 1 := by
    exact finrank_span_singleton hv0
  have hQfin : Module.finrank ℝ (Point 3 ⧸ K) = 2 := by
    have hdim := K.finrank_quotient_add_finrank
    rw [hKfin] at hdim
    have hPdim : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
    omega
  let e : (Point 3 ⧸ K) ≃ₗ[ℝ] Point 2 := LinearEquiv.ofFinrankEq _ _ (by
    rw [hQfin]
    simp [Point])
  let L : Point 3 →ₗ[ℝ] Point 2 := e.toLinearMap.comp K.mkQ
  let π : Point 3 →ᵃ[ℝ] Point 2 := L.toAffineMap
  have hker : LinearMap.ker L = K := by
    ext z
    simp [L, K]
  have hpreserve (S : Finset (Point 3)) (hSX : S ⊆ X) (hScard : S.card ≤ 3) :
      AffineIndependent ℝ (fun z : S ↦ π (z : Point 3)) := by
    have hAI := affineIndependent_of_card_le_three_of_generalPosition_three
      hgp hXcard hSX hScard
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst S
      exact affineIndependent_of_subsingleton ℝ _
    letI : Nonempty S := Finset.nonempty_coe_sort.mpr hS
    let a : S := ⟨hS.choose, hS.choose_spec⟩
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a] at hAI ⊢
    simp_rw [← π.linearMap_vsub]
    apply hAI.map
    rw [show LinearMap.ker π.linear = K by simpa [π] using hker]
    have hspan_le :
        Submodule.span ℝ
            (Set.range (fun z : {z : S // z ≠ a} ↦ (z.1 : Point 3) -ᵥ (a : Point 3))) ≤
          vectorSpan ℝ (S : Set (Point 3)) := by
      rw [Submodule.span_le]
      rintro w ⟨z, rfl⟩
      exact vsub_mem_vectorSpan ℝ z.1.2 a.2
    let SS : I := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSX, hScard⟩⟩
    have hvS : v ∉ vectorSpan ℝ (S : Set (Point 3)) := by
      simpa [bad] using hv SS
    exact Disjoint.mono_left hspan_le
      (Submodule.disjoint_span_singleton_of_notMem hvS)
  have hπinj : Set.InjOn π X := by
    intro x hx y hy hxy
    by_contra hne
    let S : Finset (Point 3) := {x, y}
    have hSX : S ⊆ X := by
      intro z hz
      have hz' : z = x ∨ z = y := by simpa [S] using hz
      rcases hz' with rfl | rfl
      · simpa using hx
      · simpa using hy
    have hScard : S.card ≤ 3 := by
      calc
        S.card ≤ ({y} : Finset (Point 3)).card + 1 := by
          simpa [S] using Finset.card_insert_le x ({y} : Finset (Point 3))
        _ ≤ 3 := by simp
    have hAI := hpreserve S hSX hScard
    have hxyS : x ∈ S := by simp [S]
    have hyyS : y ∈ S := by simp [S]
    exact hAI.injective (show π (⟨x, hxyS⟩ : S) = π (⟨y, hyyS⟩ : S) by exact hxy)
      |> fun h ↦ hne (congrArg Subtype.val h)
  refine ⟨π, hπinj, ?_⟩
  intro T hTsub hTcard
  let S : Finset (Point 3) := X.filter fun x ↦ π x ∈ T
  have hSX : S ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hImage : S.image π = T := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro y hy
      have hyImage := hTsub hy
      obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp hyImage
      subst y
      exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩
  have hπinjS : Set.InjOn π S := hπinj.mono hSX
  have hScard : S.card = 3 := by
    calc
      S.card = (S.image π).card := (Finset.card_image_of_injOn hπinjS).symm
      _ = T.card := congrArg Finset.card hImage
      _ = 3 := by omega
  have hAIS := hpreserve S hSX (by omega)
  have hpreExists (y : T) : ∃ x ∈ S, π x = (y : Point 2) := by
    have hy : (y : Point 2) ∈ S.image π := by
      rw [hImage]
      exact y.2
    exact Finset.mem_image.mp hy
  choose pre hpreS hpre using hpreExists
  let emb : T ↪ S :=
    ⟨fun y ↦ ⟨pre y, hpreS y⟩, fun y z hyz ↦ Subtype.ext (by
      calc
        (y : Point 2) = π (pre y) := (hpre y).symm
        _ = π (pre z) :=
          congrArg π (congrArg Subtype.val hyz)
        _ = (z : Point 2) := hpre z)⟩
  have hemb : (fun z : S ↦ π (z : Point 3)) ∘ emb =
      (fun z : T ↦ (z : Point 2)) := by
    funext y
    exact hpre y
  rw [← hemb]
  exact hAIS.comp_embedding emb

end

end

/-! ### Upstream module `JSP527/External/Erdos651/FinalEstimates.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Numerical endgame for Erdős Problem 651

This file isolates the elementary estimates used at the end of the
Pohoata--Zakharov argument.  The geometric part of the proof only has to
produce an upper bound of the shape

`N n ≤ t n ^ (C * n / t n)`

(with real exponent), where `t n → ∞`.  The results below turn such a bound
into the `2 ^ (o(n))` formulation used in `Definitions.lean`.

We also record the concrete fourth-root cutoff used in the argument and a
small binomial-sum estimate useful when the geometric encoding is counted.
-/

open _root_.Filter _root_.Finset _root_.Set
open scoped BigOperators _root_.Topology

noncomputable section

/-! ## The fourth-root cutoff -/

/-- The integer cutoff `⌊n^(1/4)⌋` used in the parameter choice. -/
def pzQuarterRoot (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- The fourth-root cutoff is unbounded. -/
theorem pzQuarterRoot_tendsto_atTop : Tendsto pzQuarterRoot atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)

/-! ## A binomial counting bound -/

/-! ## The logarithmic loss -/

/-- The coefficient in the logarithm of `t^(C n/t)`. -/
def pzDelta (C : ℝ) (t : ℕ → ℕ) (n : ℕ) : ℝ :=
  C * (Real.log (t n : ℝ) / (t n : ℝ))

/-- For any unbounded integer parameter `t`, its logarithmic loss tends to
zero. -/
theorem pzDelta_tendsto_zero (C : ℝ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) :
    Tendsto (pzDelta C t) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (t n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hratio : Tendsto
      (fun n : ℕ ↦ Real.log (t n : ℝ) / (t n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  change Tendsto
    (fun n : ℕ ↦ C * (Real.log (t n : ℝ) / (t n : ℝ))) atTop (𝓝 0)
  simpa only [mul_zero] using hratio.const_mul C

/-! ## Conversion of the PZ envelope to base-two subexponential growth -/

/-- If `t n → ∞`, then `t^(C n/t)` is eventually smaller than
`2^(ε n)` for every `ε > 0`.  Powers in this statement are real powers. -/
theorem eventually_pzEnvelope_lt_two_rpow (C : ℝ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (t n : ℝ) ^ (C * (n : ℝ) / (t n : ℝ)) <
        (2 : ℝ) ^ (ε * (n : ℝ)) := by
  have htarget : 0 < ε * Real.log 2 :=
    mul_pos hε (Real.log_pos one_lt_two)
  have hsmall : ∀ᶠ n : ℕ in atTop, pzDelta C t n < ε * Real.log 2 :=
    (pzDelta_tendsto_zero C ht).eventually (Iio_mem_nhds htarget)
  filter_upwards [hsmall, ht.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with n hn htpos hnpos
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr htpos),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_lt_exp.mpr
  calc
    Real.log (t n : ℝ) * (C * (n : ℝ) / (t n : ℝ))
        = pzDelta C t n * (n : ℝ) := by rw [pzDelta]; ring
    _ < (ε * Real.log 2) * (n : ℝ) :=
      mul_lt_mul_of_pos_right hn (Nat.cast_pos.mpr hnpos)
    _ = Real.log 2 * (ε * (n : ℝ)) := by ring

end

end

/-! ### Upstream module `JSP527/External/Erdos651/BinomialEnvelope.lean` -/

/-!
# The binomial estimate in the Pohoata--Zakharov endgame

This file records the rounding-sensitive estimate which changes the binomial
coefficient produced by the cap argument into an envelope of the form
`t ^ (C * n / t)`.  The factorial in the binomial coefficient is essential:
the cruder estimate `choose N a ≤ N^a` would retain an unwanted `log n`.
-/

noncomputable section

/-- The cap size used in the alternating cap assembly. -/
def pzCapSize (n t : ℕ) : ℕ :=
  ⌈(2 : ℝ) * n / t⌉₊

theorem pzCapSize_pos {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    0 < pzCapSize n t := by
  rw [pzCapSize]
  apply Nat.ceil_pos.mpr
  positivity

theorem pzCapSize_lower {n t : ℕ} (ht : 0 < t) :
    (2 : ℝ) * n / t ≤ (pzCapSize n t : ℝ) := by
  exact Nat.le_ceil _

theorem pzCapSize_upper {n t : ℕ} (_ht : 0 < t) :
    (pzCapSize n t : ℝ) < (2 : ℝ) * n / t + 1 := by
  apply Nat.ceil_lt_add_one
  positivity

/-- The elementary real binomial estimate `choose (n+a) a ≤ (e(n+a)/a)^a`.
It is proved from Mathlib's Stirling lower bound. -/
theorem choose_add_le_exp_mul_div_pow (n a : ℕ) (ha : 0 < a) :
    ((Nat.choose (n + a) a : ℕ) : ℝ) ≤
      (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * a) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    nlinarith
  have hfac : ((a : ℝ) / Real.exp 1) ^ a ≤ (a.factorial : ℝ) := by
    calc
      ((a : ℝ) / Real.exp 1) ^ a
          ≤ Real.sqrt (2 * Real.pi * a) * ((a : ℝ) / Real.exp 1) ^ a := by
            exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (a.factorial : ℝ) := Stirling.le_factorial_stirling a
  have hchoose : ((Nat.choose (n + a) a : ℕ) : ℝ) ≤
      (((n + a : ℕ) : ℝ) ^ a) / (a.factorial : ℝ) := by
    exact Nat.choose_le_pow_div a (n + a)
  have hfacpos : (0 : ℝ) < (a.factorial : ℝ) := by positivity
  have hbasepos : (0 : ℝ) < (a : ℝ) / Real.exp 1 := by positivity
  calc
    ((Nat.choose (n + a) a : ℕ) : ℝ)
        ≤ (((n + a : ℕ) : ℝ) ^ a) / (a.factorial : ℝ) := hchoose
    _ ≤ (((n + a : ℕ) : ℝ) ^ a) /
          (((a : ℝ) / Real.exp 1) ^ a) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = (((n + a : ℕ) : ℝ) / ((a : ℝ) / Real.exp 1)) ^ a := by
      exact (div_pow _ _ a).symm
    _ = (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := by
      congr 1
      field_simp [ne_of_gt haR, Real.exp_ne_zero]

/-- With `a = ceil(2n/t)`, the cap binomial coefficient is bounded by
`t^(6n/t)`.  The hypotheses are exactly the eventual range used in the
source proof. -/
theorem choose_add_pzCapSize_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n) :
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ≤
      (t : ℝ) ^ ((6 : ℝ) * n / t) := by
  let a := pzCapSize n t
  have ht0 : 0 < t := by omega
  have ha0 : 0 < a := pzCapSize_pos hn ht0
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have htnR : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
  have halower : (2 : ℝ) * n / t ≤ (a : ℝ) := by
    simpa [a] using pzCapSize_lower (n := n) ht0
  have haupper : (a : ℝ) < (2 : ℝ) * n / t + 1 := by
    simpa [a] using pzCapSize_upper (n := n) ht0
  have hratio : ((n + a : ℕ) : ℝ) / (a : ℝ) ≤ (t : ℝ) := by
    rw [Nat.cast_add]
    have hna : (n : ℝ) / (a : ℝ) ≤ (t : ℝ) / 2 := by
      rw [div_le_iff₀ haR]
      have htwo : (2 : ℝ) * n ≤ (a : ℝ) * t :=
        (div_le_iff₀ htR).mp halower
      nlinarith
    rw [add_div, div_self (ne_of_gt haR)]
    have ht2 : (1 : ℝ) ≤ (t : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (show 2 ≤ t by omega)
    linarith
  have hexpt : Real.exp 1 ≤ (t : ℝ) :=
    Real.exp_one_lt_three.le.trans (by exact_mod_cast ht)
  have hbase : Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ) ≤ (t : ℝ) ^ 2 := by
    rw [mul_div_assoc]
    exact (mul_le_mul hexpt hratio (by positivity) (by positivity)).trans_eq (by ring)
  have haexp : (a : ℝ) ≤ (3 : ℝ) * n / t := by
    have hone : (1 : ℝ) ≤ (n : ℝ) / t := by
      rw [le_div_iff₀ htR]
      simpa using htnR
    refine haupper.le.trans ?_
    calc
      (2 : ℝ) * n / t + 1 = 2 * ((n : ℝ) / t) + 1 := by ring
      _ ≤ 2 * ((n : ℝ) / t) + (n : ℝ) / t := by linarith
      _ = (3 : ℝ) * n / t := by ring
  have hchoose := choose_add_le_exp_mul_div_pow n a ha0
  calc
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ)
        = ((Nat.choose (n + a) a : ℕ) : ℝ) := rfl
    _ ≤ (Real.exp 1 * ((n + a : ℕ) : ℝ) / (a : ℝ)) ^ a := hchoose
    _ ≤ ((t : ℝ) ^ 2) ^ a := by
      exact pow_le_pow_left₀ (by positivity) hbase _
    _ = (t : ℝ) ^ (2 * a : ℕ) := (pow_mul _ 2 a).symm
    _ = (t : ℝ) ^ ((2 : ℝ) * a) := by
      rw [← Real.rpow_natCast]
      norm_num
    _ ≤ (t : ℝ) ^ ((6 : ℝ) * n / t) := by
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ t by omega))
      calc
        (2 : ℝ) * a ≤ 2 * ((3 : ℝ) * n / t) :=
          mul_le_mul_of_nonneg_left haexp (by norm_num)
        _ = (6 : ℝ) * n / t := by ring

/-- The sixth power appearing after the two square-root/Dilworth losses is
bounded by the source envelope with the explicit constant `36`. -/
theorem choose_add_pzCapSize_pow_six_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n) :
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6 ≤
      (t : ℝ) ^ ((36 : ℝ) * n / t) := by
  have h := choose_add_pzCapSize_le_envelope n t hn ht htn
  calc
    ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6
        ≤ ((t : ℝ) ^ ((6 : ℝ) * n / t)) ^ (6 : ℕ) :=
          pow_le_pow_left₀ (by positivity) h 6
    _ = (t : ℝ) ^ ((36 : ℝ) * n / t) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring

end

/-! ### Upstream module `JSP527/External/Erdos651/CupsCaps.lean` -/

/-!
# The sharp cups-versus-caps theorem

This file proves the ordered, two-colour tight-path form of the classical
Erdős--Szekeres cups-versus-caps theorem.  Applying the two colours to the
two possible comparisons of consecutive secant slopes gives the usual planar
statement.  The numerical bound is the sharp one needed in Proposition 2.1
of Pohoata--Zakharov:

`Nat.choose (a + b - 4) (a - 2) + 1`.
-/

noncomputable section

/-! ## Ordered tight paths -/

/-- A list is ordered when its entries are strictly increasing.  We use a
small recursive definition because its equations are particularly convenient
for the endpoint-gluing induction below. -/
def Ordered : List ℕ → Prop
  | i :: j :: tail => i < j ∧ Ordered (j :: tail)
  | _ => True

/-- Every entry of `I` belongs to the ambient finite set `S`. -/
def ListIn (I : List ℕ) (S : Finset ℕ) : Prop := ∀ i ∈ I, i ∈ S

/-- `TightPath χ c I` means that every three consecutive entries of `I`
have colour `c`. -/
def TightPath (χ : ℕ → ℕ → ℕ → Bool) (c : Bool) : List ℕ → Prop
  | i :: j :: k :: tail => χ i j k = c ∧ TightPath χ c (j :: k :: tail)
  | _ => True

/-- An ordered monochromatic tight path of prescribed length in `S`. -/
def HasTightPath (χ : ℕ → ℕ → ℕ → Bool) (c : Bool)
    (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ I : List ℕ, Ordered I ∧ ListIn I S ∧ I.length = n ∧ TightPath χ c I

lemma listIn_mono {I : List ℕ} {S T : Finset ℕ} (hST : S ⊆ T)
    (hI : ListIn I S) : ListIn I T := by
  intro i hi
  exact hST (hI i hi)

lemma hasTightPath_mono {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    {S T : Finset ℕ} {n : ℕ} (hST : S ⊆ T) :
    HasTightPath χ c S n → HasTightPath χ c T n := by
  rintro ⟨I, hI, hIS, hlen, hpath⟩
  exact ⟨I, hI, listIn_mono hST hIS, hlen, hpath⟩

lemma tightPath_append_last {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    (u : List ℕ) {z y w : ℕ}
    (hpath : TightPath χ c (u ++ [z, y])) (hzyw : χ z y w = c) :
    TightPath χ c (u ++ [z, y, w]) := by
  induction u with
  | nil => exact ⟨hzyw, trivial⟩
  | cons x u ih =>
      cases u with
      | nil =>
          exact ⟨hpath.1, hzyw, trivial⟩
      | cons x' u =>
          cases u with
          | nil => exact ⟨hpath.1, hpath.2.1, hzyw, trivial⟩
          | cons q tail => exact ⟨hpath.1, ih hpath.2⟩

lemma exists_append_two_of_two_le_length :
    ∀ {I : List ℕ}, 2 ≤ I.length → ∃ u z y, I = u ++ [z, y]
  | [], h => by simp at h
  | [x], h => by simp at h
  | x :: y :: tail, _ => by
      by_cases ht : tail = []
      · subst tail
        exact ⟨[], x, y, rfl⟩
      · have htail : 2 ≤ (y :: tail).length := by
          cases tail with
          | nil => contradiction
          | cons z tail => simp
        obtain ⟨u, z, w, hu⟩ := exists_append_two_of_two_le_length htail
        exact ⟨x :: u, z, w, by simp [hu]⟩

lemma hasTightPath_two_of_one_lt_card
    (χ : ℕ → ℕ → ℕ → Bool) (c : Bool) (S : Finset ℕ)
    (hS : 1 < S.card) : HasTightPath χ c S 2 := by
  rw [Finset.one_lt_card] at hS
  obtain ⟨x, hx, y, hy, hxy⟩ := hS
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact ⟨[x, y], by simp [Ordered, hlt], by simpa [ListIn, hx, hy], rfl,
      by simp [TightPath]⟩
  · exact (hxy heq).elim
  · exact ⟨[y, x], by simp [Ordered, hgt], by simpa [ListIn, hx, hy], rfl,
      by simp [TightPath]⟩

private lemma ordered_append_last {u : List ℕ} {z y w : ℕ}
    (hord : Ordered (u ++ [z, y])) (hyw : y < w) :
    Ordered (u ++ [z, y, w]) := by
  induction u with
  | nil => exact ⟨hord.1, hyw, trivial⟩
  | cons x u ih =>
      cases u with
      | nil => exact ⟨hord.1, hord.2.1, hyw, trivial⟩
      | cons x' u =>
          exact ⟨hord.1, ih hord.2⟩

private lemma listIn_append_last {u : List ℕ} {z y w : ℕ} {S : Finset ℕ}
    (hI : ListIn (u ++ [z, y]) S) (hw : w ∈ S) :
    ListIn (u ++ [z, y, w]) S := by
  intro i hi
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
  by_cases hiw : i = w
  · simpa [hiw] using hw
  · apply hI i
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    tauto

private lemma ordered_last_two {u : List ℕ} {z y : ℕ}
    (h : Ordered (u ++ [z, y])) : z < y := by
  induction u with
  | nil => exact h.1
  | cons x u ih =>
      cases u with
      | nil => exact h.2.1
      | cons x' u => exact ih h.2

/-!
The following bound is proved in its contrapositive form.  The endpoint set
`Y` consists of the right endpoints of blue paths of length `b-1`.  Its
complement avoids a blue path of length `b-1`; and the standard endpoint
gluing argument shows that `Y` avoids a red path of length `a-1`.
-/
private theorem tightPath_avoiding_card_le
    (χ : ℕ → ℕ → ℕ → Bool) :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → ∀ S : Finset ℕ,
      ¬ HasTightPath χ true S a →
      ¬ HasTightPath χ false S b →
      S.card ≤ Nat.choose (a + b - 4) (a - 2) := by
  intro a b ha hb
  generalize hn : a + b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      intro S hred hblue
      by_cases ha2 : a = 2
      · subst a
        have hcard : S.card ≤ 1 := by
          by_contra h
          have hone : 1 < S.card := by omega
          exact hred (hasTightPath_two_of_one_lt_card χ true S hone)
        rw [← hn]
        simpa using hcard
      by_cases hb2 : b = 2
      · subst b
        have hcard : S.card ≤ 1 := by
          by_contra h
          have hone : 1 < S.card := by omega
          exact hblue (hasTightPath_two_of_one_lt_card χ false S hone)
        rw [← hn]
        simpa using hcard
      have ha3 : 3 ≤ a := by omega
      have hb3 : 3 ≤ b := by omega
      classical
      let Y : Finset ℕ := S.filter fun y =>
        ∃ (u : List ℕ) (z : ℕ),
          Ordered (u ++ [z, y]) ∧ ListIn (u ++ [z, y]) S ∧
          (u ++ [z, y]).length = b - 1 ∧ TightPath χ false (u ++ [z, y])
      let C : Finset ℕ := S \ Y
      have hYS : Y ⊆ S := by
        simpa [Y] using (Finset.filter_subset
          (fun y : ℕ => ∃ (u : List ℕ) (z : ℕ),
            Ordered (u ++ [z, y]) ∧ ListIn (u ++ [z, y]) S ∧
            (u ++ [z, y]).length = b - 1 ∧ TightPath χ false (u ++ [z, y])) S)
      have hCS : C ⊆ S := Finset.sdiff_subset
      have hC_red : ¬ HasTightPath χ true C a :=
        fun h => hred (hasTightPath_mono hCS h)
      have hC_blue : ¬ HasTightPath χ false C (b - 1) := by
        rintro ⟨I, hord, hIC, hlen, hpath⟩
        have hlen2 : 2 ≤ I.length := by omega
        obtain ⟨u, z, y, rfl⟩ := exists_append_two_of_two_le_length hlen2
        have hyC : y ∈ C := hIC y (by simp)
        have hyY : y ∈ Y := by
          simp only [Y, Finset.mem_filter]
          refine ⟨hCS hyC, u, z, hord, listIn_mono hCS hIC, hlen, hpath⟩
        exact (Finset.mem_sdiff.mp hyC).2 hyY
      have hY_blue : ¬ HasTightPath χ false Y b :=
        fun h => hblue (hasTightPath_mono hYS h)
      have hY_red : ¬ HasTightPath χ true Y (a - 1) := by
        rintro ⟨I, hordI, hIY, hlenI, hpathI⟩
        cases I with
        | nil => simp at hlenI; omega
        | cons y rest =>
            cases rest with
            | nil => simp at hlenI; omega
            | cons w tail =>
                have hyY : y ∈ Y := hIY y (by simp)
                obtain ⟨hyS, u, z, hordT, hTS, hlenT, hpathT⟩ :=
                  (Finset.mem_filter.mp hyY)
                have hzy : z < y := ordered_last_two hordT
                have hyw : y < w := by simpa [Ordered] using hordI.1
                have hzS : z ∈ S := hTS z (by simp)
                have hwS : w ∈ S := hYS (hIY w (by simp))
                by_cases hcol : χ z y w = true
                · apply hred
                  refine ⟨z :: y :: w :: tail, ?_, ?_, ?_, ?_⟩
                  · exact ⟨hzy, hordI⟩
                  · intro q hq
                    simp only [List.mem_cons] at hq
                    rcases hq with rfl | hq
                    · exact hzS
                    · exact hYS (hIY q (by simpa using hq))
                  · simp at hlenI ⊢
                    omega
                  · exact ⟨hcol, hpathI⟩
                · have hcol' : χ z y w = false := by
                    cases h : χ z y w <;> simp_all
                  apply hblue
                  refine ⟨u ++ [z, y, w], ordered_append_last hordT hyw,
                    listIn_append_last hTS hwS, ?_,
                    tightPath_append_last u hpathT hcol'⟩
                  simp at hlenT ⊢
                  omega
      have hCcard : C.card ≤ Nat.choose (a + (b - 1) - 4) (a - 2) := by
        apply ih (a + (b - 1)) (by omega) a (b - 1) ha (by omega) rfl C hC_red hC_blue
      have hYcard : Y.card ≤ Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) := by
        apply ih ((a - 1) + b) (by omega) (a - 1) b (by omega) hb rfl Y hY_red hY_blue
      have hpartition : C.card + Y.card = S.card := by
        dsimp [C]
        rw [Finset.card_sdiff_add_card]
        rw [Finset.union_eq_left.mpr hYS]
      rw [← hpartition]
      calc
        C.card + Y.card ≤
            Nat.choose (a + (b - 1) - 4) (a - 2) +
              Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) :=
          Nat.add_le_add hCcard hYcard
        _ = Nat.choose (a + b - 4) (a - 2) := by
          have h1 : a + (b - 1) - 4 = a + b - 5 := by omega
          have h2 : (a - 1) + b - 4 = a + b - 5 := by omega
          have h3 : (a - 1) - 2 = a - 3 := by omega
          have hn' : a + b - 4 = (a + b - 5) + 1 := by omega
          have hk : a - 2 = (a - 3) + 1 := by omega
          rw [h1, h2, h3, hn', hk, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one]
          ac_rfl
        _ = Nat.choose (n - 4) (a - 2) := by rw [← hn]

/-- The sharp ordered cups-versus-caps theorem for an arbitrary two-colouring
of consecutive triples. -/
theorem ordered_cups_caps
    (χ : ℕ → ℕ → ℕ → Bool) (S : Finset ℕ) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) < S.card) :
    HasTightPath χ true S a ∨ HasTightPath χ false S b := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hcard) (tightPath_avoiding_card_le χ a b ha hb S h.1 h.2)

/-! ## Planar cups and caps -/

/-- First coordinate of a point of the plane. -/
def planeX (p : Point 2) : ℝ := p 0

/-- Second coordinate of a point of the plane. -/
def planeY (p : Point 2) : ℝ := p 1

/-- Slope of the secant through two planar points. -/
def secantSlope (p q : Point 2) : ℝ :=
  (planeY q - planeY p) / (planeX q - planeX p)

/-- The successive secant slopes along `I` are strictly increasing. -/
def IncreasingSlopes (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  TightPath
    (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
    true I

/-- The decreasing colour together with the no-equal-slopes condition.  By
trichotomy on `ℝ`, these two clauses say exactly that the successive slopes
strictly decrease. -/
def DecreasingSlopes (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      false I ∧
    ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k)

/-- The enumeration `I` follows increasing first coordinate. -/
def LeftToRight (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i < j → planeX (p i) < planeX (p j)

/-- An indexed planar cup.  The first conjunct records that indices occur in
their prescribed left-to-right order. -/
def IsPlanarCup (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  Ordered I ∧ LeftToRight p I ∧ IncreasingSlopes p I

/-- An indexed planar cap. -/
def IsPlanarCap (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  Ordered I ∧ LeftToRight p I ∧ DecreasingSlopes p I

private lemma tightPath_slope_true
    (p : ℕ → Point 2) (I : List ℕ)
    (h : TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      true I) : IncreasingSlopes p I := by
  exact h

private lemma tightPath_slope_false
    (p : ℕ → Point 2) (S : Finset ℕ) (I : List ℕ)
    (hIS : ListIn I S)
    (hne : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k))
    (hord : Ordered I)
    (h : TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      false I) : DecreasingSlopes p I := by
  refine ⟨h, ?_⟩
  intro i hi j hj k hk hij hjk
  exact hne i (hIS i hi) j (hIS j hj) k (hIS k hk) hij hjk

/-- The exact planar cups-versus-caps bound.  `hne` is the no-three-collinear
condition in slope form.  (The usual harmless rotation of the point set lets
the index order be chosen so first coordinates increase.) -/
theorem planar_cups_caps
    (p : ℕ → Point 2) (S : Finset ℕ) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : ∀ i ∈ S, ∀ j ∈ S, i < j → planeX (p i) < planeX (p j))
    (hne : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k))
    (hcard : Nat.choose (a + b - 4) (a - 2) < S.card) :
    (∃ I : List ℕ, ListIn I S ∧ I.length = a ∧ IsPlanarCup p I) ∨
      (∃ I : List ℕ, ListIn I S ∧ I.length = b ∧ IsPlanarCap p I) := by
  let χ : ℕ → ℕ → ℕ → Bool := fun i j k =>
    decide (secantSlope (p i) (p j) < secantSlope (p j) (p k))
  rcases ordered_cups_caps χ S a b ha hb hcard with hcup | hcap
  · obtain ⟨I, hord, hIS, hlen, hpath⟩ := hcup
    exact Or.inl ⟨I, hIS, hlen, hord,
      (fun i hi j hj hij => hx i (hIS i hi) j (hIS j hj) hij),
      tightPath_slope_true p I hpath⟩
  · obtain ⟨I, hord, hIS, hlen, hpath⟩ := hcap
    exact Or.inr ⟨I, hIS, hlen, hord,
      (fun i hi j hj hij => hx i (hIS i hi) j (hIS j hj) hij),
      tightPath_slope_false p S I hIS hne hord hpath⟩

end

/-! ### Upstream module `JSP527/External/Erdos651/PolytopeCap.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The polytope-cap reduction in Pohoata--Zakharov

This file isolates Proposition 2.1 of Pohoata--Zakharov.  The two geometric
notions in the statement, `PFree` and `PCap`, are stated directly in affine
and convex geometry.  The proof of the proposition is factored through the
finite family of preorders obtained by projecting along the edges of
the polytope.

The finite chain-cover consequence of Dilworth is proved here from Hall's
marriage theorem, first for partial orders and then for preorders via
antisymmetrization.  Thus the geometric certificate below contains only
the projection-separation and planar lifting facts.  The theorem
`pohoata_zakharov_prop_two_one` proves the published cardinal bound,
including its exact exponent.
-/

open _root_.Set

noncomputable section

/-! ## Oriented trihedral polyhedra -/

/-- The closed negative orthant in `Point d`. -/
def negativeOrthant (d : ℕ) : Set (Point d) :=
  {x | ∀ i, x i ≤ 0}

theorem convex_negativeOrthant (d : ℕ) : Convex ℝ (negativeOrthant d) := by
  intro x hx y hy a b ha hb hab i
  change a * x i + b * y i ≤ 0
  have hxi := hx i
  have hyi := hy i
  nlinarith

/-- An oriented nondegenerate intersection of three affine halfspaces.
The affine equivalence is the simultaneous coordinate map of the three
normalized affine functionals.  Thus its carrier is literally
`φ₀ ≤ 0 ∩ φ₁ ≤ 0 ∩ φ₂ ≤ 0`, and affine independence of the
three bounding planes is built into the equivalence rather than postulated
by a determinant side condition. -/
structure OrientedTrihedral where
  normalization : Point 3 ≃ᵃ[ℝ] Point 3

namespace OrientedTrihedral

/-- The `i`th normalized oriented affine functional. -/
def functional (T : OrientedTrihedral) (i : Fin 3) (x : Point 3) : ℝ :=
  T.normalization x i

/-- The actual three-halfspace polyhedron. -/
def carrier (T : OrientedTrihedral) : Set (Point 3) :=
  T.normalization ⁻¹' negativeOrthant 3

theorem mem_carrier_iff (T : OrientedTrihedral) (x : Point 3) :
    x ∈ T.carrier ↔ ∀ i, T.functional i x ≤ 0 := by
  rfl

theorem convex_carrier (T : OrientedTrihedral) : Convex ℝ T.carrier := by
  exact (convex_negativeOrthant 3).affine_preimage T.normalization.toAffineMap

end OrientedTrihedral

/-- Delete coordinate zero; this is projection along the first edge of the
standard trihedral cone. -/
def dropCoordinate0 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 1, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Delete coordinate one. -/
def dropCoordinate1 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 0, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Delete coordinate two. -/
def dropCoordinate2 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Canonical projection along one of the three trihedral edges. -/
def dropCoordinate3 (i : Fin 3) : Point 3 →ₗ[ℝ] Point 2 :=
  if i = 0 then dropCoordinate0
  else if i = 1 then dropCoordinate1
  else dropCoordinate2

def insertCoordinate0 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![0, y 0, y 1]

def insertCoordinate1 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![y 0, 0, y 1]

def insertCoordinate2 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![y 0, y 1, 0]

theorem dropCoordinate3_image_negativeOrthant (i : Fin 3) :
    dropCoordinate3 i '' negativeOrthant 3 = negativeOrthant 2 := by
  fin_cases i
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 1
      · exact hx 2
    · intro hy
      refine ⟨insertCoordinate0 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simp [insertCoordinate0]
        · simpa [insertCoordinate0] using hy 0
        · simpa [insertCoordinate0] using hy 1
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate0,
          insertCoordinate0]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 0
      · exact hx 2
    · intro hy
      refine ⟨insertCoordinate1 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simpa [insertCoordinate1] using hy 0
        · simp [insertCoordinate1]
        · simpa [insertCoordinate1] using hy 1
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate1,
          insertCoordinate1]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 0
      · exact hx 1
    · intro hy
      refine ⟨insertCoordinate2 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simpa [insertCoordinate2] using hy 0
        · simpa [insertCoordinate2] using hy 1
        · simp [insertCoordinate2]
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate2,
          insertCoordinate2]

/-! The one-dimensional feasibility sets used to select a separating edge. -/

/-- Parameters at which coordinate `j` of the line from `x` to `y` lies
in the negative half-line. -/
def coordinateFeasible (x y : Point 3) (j : Fin 3) : Set ℝ :=
  {t | x j + t * (y j - x j) ≤ 0}

theorem convex_coordinateFeasible (x y : Point 3) (j : Fin 3) :
    Convex ℝ (coordinateFeasible x y j) := by
  intro p hp q hq a b ha hb hab
  change x j + (a * p + b * q) * (y j - x j) ≤ 0
  change x j + p * (y j - x j) ≤ 0 at hp
  change x j + q * (y j - x j) ≤ 0 at hq
  calc
    x j + (a * p + b * q) * (y j - x j) =
        (a + b) * x j + (a * p + b * q) * (y j - x j) := by
          rw [hab, one_mul]
    _ =
        a * (x j + p * (y j - x j)) +
          b * (x j + q * (y j - x j)) := by ring
    _ ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hp)
      (mul_nonpos_of_nonneg_of_nonpos hb hq)

theorem mem_coordinateFeasible_iff (x y : Point 3) (j : Fin 3) (t : ℝ) :
    t ∈ coordinateFeasible x y j ↔ AffineMap.lineMap x y t j ≤ 0 := by
  simp only [coordinateFeasible, Set.mem_setOf_eq, AffineMap.lineMap_apply_module',
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Helly's theorem in dimension one, specialized to the three coordinate
half-lines: if their triple intersection is empty, one coordinate pair
already has empty intersection. -/
theorem coordinateFeasible_empty_pair {x y : Point 3}
    (h : ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty) :
    ¬ (coordinateFeasible x y 1 ∩ coordinateFeasible x y 2).Nonempty ∨
      ¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 2).Nonempty ∨
      ¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 1).Nonempty := by
  by_contra hpairs
  push Not at hpairs
  rcases hpairs with ⟨h12, h02, h01⟩
  apply h
  suffices (⋂ j ∈ (Finset.univ : Finset (Fin 3)),
      coordinateFeasible x y j).Nonempty by simpa using this
  apply Convex.helly_theorem' (𝕜 := ℝ) (E := ℝ) (s := Finset.univ)
  · intro i hi
    exact convex_coordinateFeasible x y i
  · intro I hI hcard
    have hcard' : I.card ≤ 2 := by simpa using hcard
    have hmiss : ∃ k : Fin 3, k ∉ I := by
      by_contra hall
      push Not at hall
      have huniv : Finset.univ ⊆ I := by
        intro k hk
        exact hall k
      have hthree : 3 ≤ I.card := by
        simpa using Finset.card_le_card huniv
      omega
    obtain ⟨k, hk⟩ := hmiss
    fin_cases k
    · obtain ⟨t, ht1, ht2⟩ := h12
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact (hk hj).elim
      · exact ht1
      · exact ht2
    · obtain ⟨t, ht0, ht2⟩ := h02
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact ht0
      · exact (hk hj).elim
      · exact ht2
    · obtain ⟨t, ht0, ht1⟩ := h01
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact ht0
      · exact ht1
      · exact (hk hj).elim

theorem coordinateFeasible_mem_congr_of_coordinate_eq
    {x y : Point 3} {j : Fin 3} (hxy : x j = y j) (s t : ℝ) :
    s ∈ coordinateFeasible x y j ↔ t ∈ coordinateFeasible x y j := by
  simp [coordinateFeasible, hxy]

theorem coordinateFeasible_empty_left_or_right_of_constant
    {x y : Point 3} {j k : Fin 3}
    (hj : x j = y j) (hk : x k = y k)
    (hempty : ¬ (coordinateFeasible x y j ∩ coordinateFeasible x y k).Nonempty) :
    ¬ (coordinateFeasible x y j).Nonempty ∨
      ¬ (coordinateFeasible x y k).Nonempty := by
  by_contra h
  push Not at h
  rcases h with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  apply hempty
  exact ⟨0,
    (coordinateFeasible_mem_congr_of_coordinate_eq hj s 0).mp hs,
    (coordinateFeasible_mem_congr_of_coordinate_eq hk t 0).mp ht⟩

/-- For distinct endpoints, an empty coordinate pair can be chosen so that
at least one of its two coordinates changes along the line.  Equivalently,
the corresponding edge projection has distinct endpoints. -/
theorem coordinateFeasible_empty_changing_pair {x y : Point 3} (hxy : x ≠ y)
    (h : ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty) :
    (¬ (coordinateFeasible x y 1 ∩ coordinateFeasible x y 2).Nonempty ∧
        (x 1 ≠ y 1 ∨ x 2 ≠ y 2)) ∨
      (¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 2).Nonempty ∧
        (x 0 ≠ y 0 ∨ x 2 ≠ y 2)) ∨
      (¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 1).Nonempty ∧
        (x 0 ≠ y 0 ∨ x 1 ≠ y 1)) := by
  rcases coordinateFeasible_empty_pair h with h12 | h02 | h01
  · by_cases hchange : x 1 ≠ y 1 ∨ x 2 ≠ y 2
    · exact Or.inl ⟨h12, hchange⟩
    · push Not at hchange
      have h0 : x 0 ≠ y 0 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact heq
        · exact hchange.1
        · exact hchange.2
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h12 with h1 | h2
      · exact Or.inr (Or.inr ⟨by
          intro hn
          exact h1 ⟨hn.some, hn.some_mem.2⟩, Or.inl h0⟩)
      · exact Or.inr (Or.inl ⟨by
          intro hn
          exact h2 ⟨hn.some, hn.some_mem.2⟩, Or.inl h0⟩)
  · by_cases hchange : x 0 ≠ y 0 ∨ x 2 ≠ y 2
    · exact Or.inr (Or.inl ⟨h02, hchange⟩)
    · push Not at hchange
      have h1 : x 1 ≠ y 1 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact hchange.1
        · exact heq
        · exact hchange.2
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h02 with h0 | h2
      · exact Or.inr (Or.inr ⟨by
          intro hn
          exact h0 ⟨hn.some, hn.some_mem.1⟩, Or.inr h1⟩)
      · exact Or.inl ⟨by
          intro hn
          exact h2 ⟨hn.some, hn.some_mem.2⟩, Or.inl h1⟩
  · by_cases hchange : x 0 ≠ y 0 ∨ x 1 ≠ y 1
    · exact Or.inr (Or.inr ⟨h01, hchange⟩)
    · push Not at hchange
      have h2 : x 2 ≠ y 2 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact hchange.1
        · exact hchange.2
        · exact heq
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h01 with h0 | h1
      · exact Or.inr (Or.inl ⟨by
          intro hn
          exact h0 ⟨hn.some, hn.some_mem.1⟩, Or.inr h2⟩)
      · exact Or.inl ⟨by
          intro hn
          exact h1 ⟨hn.some, hn.some_mem.1⟩, Or.inr h2⟩

theorem coordinateFeasible_iInter_empty_of_line_disjoint {x y : Point 3}
    (hdisj : Disjoint
      (↑(affineSpan ℝ ({x, y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3)) :
    ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty := by
  rintro ⟨t, ht⟩
  have hzneg : AffineMap.lineMap x y t ∈ negativeOrthant 3 := by
    intro j
    exact (mem_coordinateFeasible_iff x y j t).mp (Set.mem_iInter.mp ht j)
  exact Set.disjoint_left.mp hdisj
    (AffineMap.lineMap_mem_affineSpan_pair t x y) hzneg

/-- A line missing the standard trihedral cone has one of the three edge
projections with distinct projected endpoints and projected line missing
the planar negative orthant. -/
theorem exists_dropCoordinate3_separating {x y : Point 3} (hxy : x ≠ y)
    (hdisj : Disjoint
      (↑(affineSpan ℝ ({x, y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3)) :
    ∃ i : Fin 3,
      dropCoordinate3 i x ≠ dropCoordinate3 i y ∧
        Disjoint
          (↑(affineSpan ℝ
            ({dropCoordinate3 i x, dropCoordinate3 i y} : Set (Point 2))) : Set (Point 2))
          (negativeOrthant 2) := by
  have hall := coordinateFeasible_iInter_empty_of_line_disjoint hdisj
  rcases coordinateFeasible_empty_changing_pair hxy hall with
      ⟨h12, hchange⟩ | ⟨h02, hchange⟩ | ⟨h01, hchange⟩
  · refine ⟨0, ?_, ?_⟩
    · intro heq
      rcases hchange with h1 | h2
      · apply h1
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate0] using this
      · apply h2
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate0] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 0 x, dropCoordinate3 0 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h12
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate0,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate0,
          AffineMap.lineMap_apply_module'] using hzneg 1
  · refine ⟨1, ?_, ?_⟩
    · intro heq
      rcases hchange with h0 | h2
      · apply h0
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate1] using this
      · apply h2
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate1] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 1 x, dropCoordinate3 1 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h02
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate1,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate1,
          AffineMap.lineMap_apply_module'] using hzneg 1
  · refine ⟨2, ?_, ?_⟩
    · intro heq
      rcases hchange with h0 | h1
      · apply h0
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate2] using this
      · apply h1
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate2] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 2 x, dropCoordinate3 2 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h01
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate2,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate2,
          AffineMap.lineMap_apply_module'] using hzneg 1

/-- Projection along the `i`th edge of an oriented trihedral polyhedron,
obtained by normalizing and then deleting coordinate `i`. -/
def OrientedTrihedral.edgeProjection (T : OrientedTrihedral) (i : Fin 3) :
    Point 3 →ᵃ[ℝ] Point 2 :=
  (dropCoordinate3 i).toAffineMap.comp T.normalization.toAffineMap

theorem OrientedTrihedral.edgeProjection_image_carrier
    (T : OrientedTrihedral) (i : Fin 3) :
    T.edgeProjection i '' T.carrier = negativeOrthant 2 := by
  rw [← dropCoordinate3_image_negativeOrthant i]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨T.normalization x, hx, ?_⟩
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨T.normalization.symm z, ?_, ?_⟩
    · simpa [OrientedTrihedral.carrier]
    · simp [OrientedTrihedral.edgeProjection]

/-- The affine line through two points. -/
def lineThrough (x y : Point 3) : Set (Point 3) :=
  affineSpan ℝ ({x, y} : Set (Point 3))

theorem OrientedTrihedral.normalized_line_disjoint
    (T : OrientedTrihedral) {x y : Point 3}
    (hdisj : Disjoint (lineThrough x y) T.carrier) :
    Disjoint
      (↑(affineSpan ℝ
        ({T.normalization x, T.normalization y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3) := by
  rw [Set.disjoint_left]
  intro z hzline hzneg
  change z ∈ affineSpan ℝ
    ({T.normalization x, T.normalization y} : Set (Point 3)) at hzline
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
  obtain ⟨t, rfl⟩ := hzline
  have hmap : T.normalization (AffineMap.lineMap x y t) =
      AffineMap.lineMap (T.normalization x) (T.normalization y) t := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    change T.normalization.toAffineMap (t • (y -ᵥ x) +ᵥ x) =
      t • (T.normalization.toAffineMap y -ᵥ T.normalization.toAffineMap x) +ᵥ
        T.normalization.toAffineMap x
    rw [
      T.normalization.toAffineMap.map_vadd,
      T.normalization.toAffineMap.linear.map_smul,
      T.normalization.toAffineMap.linearMap_vsub]
  apply Set.disjoint_left.mp hdisj
  · exact AffineMap.lineMap_mem_affineSpan_pair t x y
  · change T.normalization (AffineMap.lineMap x y t) ∈ negativeOrthant 3
    simpa [hmap]

/-- A finite set is `P`-free when it is outside `P`, and the line through
any two of its distinct points misses `P`.  In the application `P` is the
underlying set of a (possibly unbounded) convex polytope. -/
def PFree (P : Set (Point 3)) (X : Finset (Point 3)) : Prop :=
  Disjoint (↑X : Set (Point 3)) P ∧
    ∀ {x}, x ∈ X → ∀ {y}, y ∈ X → x ≠ y →
      Disjoint (lineThrough x y) P

/-- A `P`-cap is a finite set in convex position for which every one of its
points remains exposed even after the background polytope `P` is added. -/
def PCap (P : Set (Point 3)) (C : Finset (Point 3)) : Prop :=
  InConvexPosition C ∧
    ∀ x ∈ C,
      x ∉ convexHull ℝ (P ∪ (↑(C.erase x) : Set (Point 3)))

/-- The relation used in (2.5): after projection along an edge, `x ≼ y`
means that the image of `x` lies in the convex hull of the projected
polytope together with the image of `y`. -/
def projectionLE (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) (x y : Point 3) : Prop :=
  π x ∈ convexHull ℝ (π '' P ∪ {π y})

/-- The projection relation (2.5) is always a preorder.  Transitivity is
the nesting `conv(Q ∪ {y}) ⊆ conv(Q ∪ {z})` whenever
`y ∈ conv(Q ∪ {z})`. -/
theorem projectionLE_isPreorder (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) : IsPreorder (Point 3) (projectionLE P π) := by
  let hr : Std.Refl (projectionLE P π) := ⟨by
    intro x
    exact subset_convexHull ℝ _ (Or.inr (Set.mem_singleton _))
    ⟩
  let ht : IsTrans (Point 3) (projectionLE P π) := ⟨by
    intro x y z hxy hyz
    apply convexHull_min ?_ (convex_convexHull ℝ _) hxy
    intro w hw
    rcases hw with hw | rfl
    · exact subset_convexHull ℝ _ (Or.inl hw)
    · exact hyz
    ⟩
  exact @IsPreorder.mk _ _ hr ht

/-- If the projected line through two distinct projected points misses the
projected polyhedron, then the two points are incomparable in the
projection preorder.  This is the geometric implication used after the
edge-separation lemma. -/
theorem projectionLE_incomparable_of_line_disjoint
    (P : Set (Point 3)) (pi : Point 3 →ᵃ[ℝ] Point 2)
    (hconv : Convex ℝ (pi '' P)) (hnonempty : (pi '' P).Nonempty)
    (hne : pi x ≠ pi y)
    (hdisj : Disjoint (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2))
      (pi '' P)) :
    ¬ projectionLE P pi x y ∧ ¬ projectionLE P pi y x := by
  constructor
  · intro hrel
    change pi x ∈ convexHull ℝ (pi '' P ∪ {pi y}) at hrel
    rw [hconv.convexHull_union (convex_singleton (pi y)) hnonempty
      (Set.singleton_nonempty (pi y))] at hrel
    rw [mem_convexJoin] at hrel
    obtain ⟨q, hq, z, hz, hseg⟩ := hrel
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hqline : q ∈
        (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2)) := by
      rw [Set.pair_comm]
      exact ((mem_segment_iff_wbtw).mp hseg).left_mem_affineSpan_of_right_ne hne.symm
    exact Set.disjoint_left.mp hdisj hqline hq
  · intro hrel
    change pi y ∈ convexHull ℝ (pi '' P ∪ {pi x}) at hrel
    rw [hconv.convexHull_union (convex_singleton (pi x)) hnonempty
      (Set.singleton_nonempty (pi x))] at hrel
    rw [mem_convexJoin] at hrel
    obtain ⟨q, hq, z, hz, hseg⟩ := hrel
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hqline : q ∈
        (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2)) := by
      exact ((mem_segment_iff_wbtw).mp hseg).left_mem_affineSpan_of_right_ne hne
    exact Set.disjoint_left.mp hdisj hqline hq

/-- The three canonical edge projections of an oriented trihedral cone
separate every line disjoint from the cone. -/
theorem OrientedTrihedral.edgeProjection_separates
    (T : OrientedTrihedral) {x y : Point 3} (hxy : x ≠ y)
    (hdisj : Disjoint (lineThrough x y) T.carrier) :
    ∃ i : Fin 3,
      ¬ projectionLE T.carrier (T.edgeProjection i) x y ∧
        ¬ projectionLE T.carrier (T.edgeProjection i) y x := by
  have hnormxy : T.normalization x ≠ T.normalization y :=
    T.normalization.injective.ne hxy
  obtain ⟨i, hne, hline⟩ := exists_dropCoordinate3_separating hnormxy
    (T.normalized_line_disjoint hdisj)
  refine ⟨i, ?_⟩
  apply projectionLE_incomparable_of_line_disjoint T.carrier (T.edgeProjection i)
  · rw [T.edgeProjection_image_carrier]
    exact convex_negativeOrthant 2
  · rw [T.edgeProjection_image_carrier]
    exact ⟨0, fun _ => le_rfl⟩
  · exact hne
  · rw [T.edgeProjection_image_carrier]
    simpa [OrientedTrihedral.edgeProjection] using hline

theorem OrientedTrihedral.projectionOrders_separated
    (T : OrientedTrihedral) {X : Finset (Point 3)} (hfree : PFree T.carrier X)
    {x y : ↑X} (hxy : x ≠ y) :
    ∃ i : Fin 3,
      ¬ projectionLE T.carrier (T.edgeProjection i) x.1 y.1 ∧
        ¬ projectionLE T.carrier (T.edgeProjection i) y.1 x.1 := by
  apply T.edgeProjection_separates (fun h => hxy (Subtype.ext h))
  exact hfree.2 x.2 y.2 (fun h => hxy (Subtype.ext h))

/-- The three canonical edge projections in a coordinate frame chosen
generically for the finite set `X`.  The background remains the negative
orthant, while the two retained coordinates are injective on `X` and no
three projected points have an equal consecutive secant slope. -/
structure OrientedTrihedral.GenericProjectionFamily
    (T : OrientedTrihedral) (X : Finset (Point 3)) where
  projection : Fin 3 → Point 3 →ᵃ[ℝ] Point 2
  image_carrier : ∀ i, projection i '' T.carrier = negativeOrthant 2
  separated : PFree T.carrier X → ∀ {x y : ↑X}, x ≠ y →
    ∃ i, ¬ projectionLE T.carrier (projection i) x.1 y.1 ∧
      ¬ projectionLE T.carrier (projection i) y.1 x.1
  planeX_ne : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
    planeX (projection i x) ≠ planeX (projection i y)
  planeY_ne : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
    planeY (projection i x) ≠ planeY (projection i y)
  slope_ne : ∀ i {x y z : Point 3},
    x ∈ X → y ∈ X → z ∈ X →
    x ≠ y → y ≠ z → x ≠ z →
    secantSlope (projection i x) (projection i y) ≠
      secantSlope (projection i y) (projection i z)

/-! ## The planar negative-orthant geometry -/

/-- The numerator of the vertical intercept of the oriented line `pq`.
When `p.x < q.x`, it has the same sign as that intercept. -/
def interceptNumerator (p q : Point 2) : ℝ :=
  planeY p * planeX q - planeY q * planeX p

/-- A convex combination of a point of the negative orthant and `p` belongs
to `conv(Q₂ ∪ {p})`.  This elementary form is used to extract the strict
intercept inequalities forced by projection-antichainness. -/
theorem negativeOrthant_lineMap_mem_convexHull
    {r p : Point 2} (hr : r ∈ negativeOrthant 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap r p t ∈
      convexHull ℝ (negativeOrthant 2 ∪ {p}) := by
  apply (convex_convexHull ℝ _).lineMap_mem
  · exact subset_convexHull ℝ _ (Or.inl hr)
  · exact subset_convexHull ℝ _ (Or.inr (Set.mem_singleton p))
  · exact ht

/-- A convenient coordinatewise sufficient condition for membership in
`conv(Q₂ ∪ {q})`. -/
theorem mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
    {p q : Point 2} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hle : ∀ i, p i ≤ t * q i) :
    p ∈ convexHull ℝ (negativeOrthant 2 ∪ {q}) := by
  let r : Point 2 := (1 - t)⁻¹ • (p - t • q)
  have hr : r ∈ negativeOrthant 2 := by
    intro i
    change (1 - t)⁻¹ * (p i - t * q i) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (sub_nonneg.mpr ht1.le)) (sub_nonpos.mpr (hle i))
  have hline : AffineMap.lineMap r q t = p := by
    simp only [AffineMap.lineMap_apply_module]
    have hne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    dsimp [r]
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    module
  rw [← hline]
  exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- Strictly southwest points belong to the cone hull of the northeast
point.  This is the only monotonicity property of the projection preorder
needed to order an antichain from left to right. -/
theorem mem_convexHull_negativeOrthant_of_both_lt {p q : Point 2}
    (hx : planeX p < planeX q) (hy : planeY p < planeY q) :
    p ∈ convexHull ℝ (negativeOrthant 2 ∪ {q}) := by
  by_cases hqx : planeX q ≤ 0
  · by_cases hqy : planeY q ≤ 0
    · apply subset_convexHull ℝ _
      left
      intro i
      fin_cases i
      · exact hx.le.trans hqx
      · exact hy.le.trans hqy
    · have hqy' : 0 < planeY q := lt_of_not_ge hqy
      by_cases hpy : planeY p ≤ 0
      · apply subset_convexHull ℝ _
        left
        intro i
        fin_cases i
        · exact hx.le.trans hqx
        · exact hpy
      · have hpy' : 0 < planeY p := lt_of_not_ge hpy
        let t := planeY p / planeY q
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
            (t := t)
        · exact div_nonneg hpy'.le hqy'.le
        · exact (div_lt_one hqy').mpr hy
        · intro i
          fin_cases i
          · have ht1 : t ≤ 1 := ((div_lt_one hqy').mpr hy).le
            change planeX p ≤ t * planeX q
            exact hx.le.trans (le_mul_of_le_one_left hqx ht1)
          · dsimp [t]
            field_simp
            simp [planeY]
  · have hqx' : 0 < planeX q := lt_of_not_ge hqx
    by_cases hqy : planeY q ≤ 0
    · by_cases hpx : planeX p ≤ 0
      · apply subset_convexHull ℝ _
        left
        intro i
        fin_cases i
        · exact hpx
        · exact hy.le.trans hqy
      · have hpx' : 0 < planeX p := lt_of_not_ge hpx
        let t := planeX p / planeX q
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
            (t := t)
        · exact div_nonneg hpx'.le hqx'.le
        · exact (div_lt_one hqx').mpr hx
        · intro i
          fin_cases i
          · dsimp [t]
            field_simp
            simp [planeX]
          · have ht1 : t ≤ 1 := ((div_lt_one hqx').mpr hx).le
            change planeY p ≤ t * planeY q
            exact hy.le.trans (le_mul_of_le_one_left hqy ht1)
    · have hqy' : 0 < planeY q := lt_of_not_ge hqy
      by_cases hpy : planeY p ≤ 0
      · by_cases hpx : planeX p ≤ 0
        · apply subset_convexHull ℝ _
          left
          intro i
          fin_cases i
          · exact hpx
          · exact hpy
        · have hpx' : 0 < planeX p := lt_of_not_ge hpx
          let t := planeX p / planeX q
          apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
              (t := t)
          · exact div_nonneg hpx'.le hqx'.le
          · exact (div_lt_one hqx').mpr hx
          · intro i
            fin_cases i
            · dsimp [t]
              field_simp
              simp [planeX]
            · exact hpy.trans (mul_pos
                (div_pos hpx' hqx') hqy').le
      · have hpy' : 0 < planeY p := lt_of_not_ge hpy
        let u := planeX p / planeX q
        let v := planeY p / planeY q
        let t := (max u v + 1) / 2
        have hv0 : 0 ≤ v := div_nonneg hpy'.le hqy'.le
        have hu1 : u < 1 := (div_lt_one hqx').mpr hx
        have hv1 : v < 1 := (div_lt_one hqy').mpr hy
        have hmax0 : 0 ≤ max u v := le_max_of_le_right hv0
        have hmax1 : max u v < 1 := max_lt hu1 hv1
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        have ht1 : t < 1 := by dsimp [t]; linarith
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le ht0 ht1
        intro i
        fin_cases i
        · have hut : u ≤ t := by
            have := le_max_left u v
            dsimp [t]
            linarith
          change planeX p ≤ t * planeX q
          exact (div_le_iff₀ hqx').mp hut
        · have hvt : v ≤ t := by
            have := le_max_right u v
            dsimp [t]
            linarith
          change planeY p ≤ t * planeY q
          exact (div_le_iff₀ hqy').mp hvt

theorem not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
    {p q : Point 2}
    (h : q ∉ convexHull ℝ (negativeOrthant 2 ∪ {p})) :
    q ∉ negativeOrthant 2 := by
  intro hq
  exact h (subset_convexHull ℝ _ (Or.inl hq))

/-- If the right endpoint has nonpositive first coordinate, failure of the
projection relation forces the line intercept to be strictly positive. -/
theorem interceptNumerator_pos_of_right_nonpos
    {p q : Point 2} (hx : planeX p < planeX q)
    (hy : planeY q < planeY p) (hqx : planeX q ≤ 0)
    (hnot : q ∉ convexHull ℝ (negativeOrthant 2 ∪ {p})) :
    0 < interceptNumerator p q := by
  by_contra hpos
  have hnum : interceptNumerator p q ≤ 0 := le_of_not_gt hpos
  have hqout := not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton hnot
  have hqy : 0 < planeY q := by
    by_contra h
    apply hqout
    intro i
    fin_cases i
    · exact hqx
    · simpa [planeY] using le_of_not_gt h
  have hpy : 0 < planeY p := hqy.trans hy
  let t : ℝ := planeY q / planeY p
  have ht0 : 0 ≤ t := div_nonneg hqy.le hpy.le
  have ht1 : t < 1 := (div_lt_one hpy).mpr hy
  let r : Point 2 := WithLp.toLp 2
    ![(planeX q - t * planeX p) / (1 - t), 0]
  have hr : r ∈ negativeOrthant 2 := by
    intro i
    fin_cases i
    · change (planeX q - t * planeX p) / (1 - t) ≤ 0
      have hden : 0 < 1 - t := sub_pos.mpr ht1
      rw [div_nonpos_iff]
      right
      refine ⟨?_, hden.le⟩
      dsimp [t, interceptNumerator] at hnum ⊢
      rw [sub_nonpos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hpy]
      nlinarith
    · simp [r]
  have hline : AffineMap.lineMap r p t = q := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply]
      change t * (planeX p -
          (planeX q - t * planeX p) / (1 - t)) +
          (planeX q - t * planeX p) / (1 - t) = planeX q
      have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
      field_simp
      ring
    · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply]
      change t * (planeY p - 0) + 0 = planeY q
      dsimp [t]
      field_simp
      ring
  apply hnot
  rw [← hline]
  exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- The symmetric strict-intercept lemma when the left endpoint has
nonnegative first coordinate. -/
theorem interceptNumerator_pos_of_left_nonneg
    {p q : Point 2} (hx : planeX p < planeX q)
    (hy : planeY q < planeY p) (hpx : 0 ≤ planeX p)
    (hnot : p ∉ convexHull ℝ (negativeOrthant 2 ∪ {q})) :
    0 < interceptNumerator p q := by
  by_cases hpx0 : planeX p = 0
  · have hqx : 0 < planeX q := by linarith
    have hpout :=
      not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton hnot
    have hpy : 0 < planeY p := by
      by_contra h
      apply hpout
      intro i
      fin_cases i
      · change planeX p ≤ 0
        exact hpx0.le
      · simpa [planeY] using le_of_not_gt h
    simp [interceptNumerator, hpx0]
    positivity
  · have hpx' : 0 < planeX p := lt_of_le_of_ne hpx (Ne.symm hpx0)
    have hqx : 0 < planeX q := hpx'.trans hx
    by_contra hpos
    have hnum : interceptNumerator p q ≤ 0 := le_of_not_gt hpos
    let t : ℝ := planeX p / planeX q
    have ht0 : 0 ≤ t := div_nonneg hpx'.le hqx.le
    have ht1 : t < 1 := (div_lt_one hqx).mpr hx
    let r : Point 2 := WithLp.toLp 2
      ![0, (planeY p - t * planeY q) / (1 - t)]
    have hr : r ∈ negativeOrthant 2 := by
      intro i
      fin_cases i
      · simp [r]
      · change (planeY p - t * planeY q) / (1 - t) ≤ 0
        have hden : 0 < 1 - t := sub_pos.mpr ht1
        rw [div_nonpos_iff]
        right
        refine ⟨?_, hden.le⟩
        dsimp [t, interceptNumerator] at hnum ⊢
        rw [sub_nonpos]
        rw [div_mul_eq_mul_div, le_div_iff₀ hqx]
        nlinarith
    have hline : AffineMap.lineMap r q t = p := by
      apply PiLp.ext
      intro i
      fin_cases i
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply]
        change t * (planeX q - 0) + 0 = planeX p
        dsimp [t]
        field_simp
        ring
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply]
        change t * (planeY q -
            (planeY p - t * planeY q) / (1 - t)) +
            (planeY p - t * planeY q) / (1 - t) = planeY p
        have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
        field_simp
        ring
    apply hnot
    rw [← hline]
    exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- The positive-normal functional whose level sets have slope `m`. -/
def planeLineValue (m : ℝ) (p : Point 2) : ℝ :=
  planeY p - m * planeX p

def planeLineValueLinear (m : ℝ) : Point 2 →ₗ[ℝ] ℝ where
  toFun := planeLineValue m
  map_add' x y := by simp [planeLineValue, planeX, planeY]; ring
  map_smul' c x := by simp [planeLineValue, planeX, planeY]; ring

theorem convex_planeLineValue_lt (m c : ℝ) :
    Convex ℝ {p : Point 2 | planeLineValue m p < c} := by
  exact (convex_Iio c).linear_preimage (planeLineValueLinear m)

theorem planeLineValue_nonpos_on_negativeOrthant {m : ℝ} (hm : m ≤ 0)
    {p : Point 2} (hp : p ∈ negativeOrthant 2) :
    planeLineValue m p ≤ 0 := by
  have hx := hp 0
  have hy := hp 1
  change planeY p - m * planeX p ≤ 0
  have hmx : 0 ≤ m * planeX p := mul_nonneg_of_nonpos_of_nonpos hm hx
  simpa [planeY] using sub_nonpos.mpr (hy.trans hmx)

/-- Signed turn of the oriented triple `p,q,r`. -/
def planeTurn (p q r : Point 2) : ℝ :=
  (planeX q - planeX p) * (planeY r - planeY p) -
    (planeY q - planeY p) * (planeX r - planeX p)

theorem planeTurn_rotate (p q r : Point 2) :
    planeTurn q r p = planeTurn p q r := by
  simp [planeTurn]
  ring

theorem planeTurn_swap_right (p q r : Point 2) :
    planeTurn p r q = -planeTurn p q r := by
  simp [planeTurn]
  ring

theorem slope_lt_slope_iff_turn_pos {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r) :
    secantSlope p q < secantSlope q r ↔ 0 < planeTurn p q r := by
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hpq) (sub_pos.mpr hqr)]
  simp only [planeTurn]
  ring_nf
  constructor <;> intro h <;> nlinarith

theorem slope_gt_slope_iff_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r) :
    secantSlope q r < secantSlope p q ↔ planeTurn p q r < 0 := by
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hqr) (sub_pos.mpr hpq)]
  simp only [planeTurn]
  ring_nf
  constructor <;> intro h <;> nlinarith

theorem secantSlope_neg_of_x_lt_y_gt {p q : Point 2}
    (hx : planeX p < planeX q) (hy : planeY q < planeY p) :
    secantSlope p q < 0 := by
  dsimp [secantSlope]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hy) (sub_pos.mpr hx)

theorem planeLineValue_sub_eq_slope {m : ℝ} {p q : Point 2}
    (hx : planeX p < planeX q) :
    planeLineValue m q - planeLineValue m p =
      (planeX q - planeX p) * (secantSlope p q - m) := by
  have hne : planeX q - planeX p ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  simp [planeLineValue, secantSlope]
  field_simp
  ring

theorem planeLineValue_secantSlope {p q : Point 2}
    (hx : planeX p < planeX q) :
    planeLineValue (secantSlope p q) q =
      interceptNumerator p q / (planeX q - planeX p) := by
  have hne : planeX q - planeX p ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  simp [planeLineValue, secantSlope, interceptNumerator]
  field_simp
  ring

theorem secantSlope_long_lt_left_of_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r)
    (hturn : planeTurn p q r < 0) :
    secantSlope p r < secantSlope p q := by
  have hpr : planeX p < planeX r := hpq.trans hqr
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hpr) (sub_pos.mpr hpq)]
  dsimp [planeTurn] at hturn
  nlinarith [mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hqr)]

theorem secantSlope_right_lt_long_of_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r)
    (hturn : planeTurn p q r < 0) :
    secantSlope q r < secantSlope p r := by
  have hpr : planeX p < planeX r := hpq.trans hqr
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hqr) (sub_pos.mpr hpr)]
  dsimp [planeTurn] at hturn
  nlinarith [mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hqr)]

theorem planeTurn_transitive_pos {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : 0 < planeTurn a b c) (hbcd : 0 < planeTurn b c d) :
    0 < planeTurn a b d ∧ 0 < planeTurn a c d := by
  simp only [planeTurn] at habc hbcd ⊢
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hbc) habc,
    mul_pos (sub_pos.mpr hab) hbcd, mul_pos (sub_pos.mpr hcd) habc,
    mul_pos (sub_pos.mpr hbc) hbcd]

theorem planeTurn_transitive_neg {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : planeTurn a b c < 0) (hbcd : planeTurn b c d < 0) :
    planeTurn a b d < 0 ∧ planeTurn a c d < 0 := by
  simp only [planeTurn] at habc hbcd ⊢
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hbc) (neg_pos.mpr habc),
    mul_pos (sub_pos.mpr hab) (neg_pos.mpr hbcd),
    mul_pos (sub_pos.mpr hcd) (neg_pos.mpr habc),
    mul_pos (sub_pos.mpr hbc) (neg_pos.mpr hbcd)]

theorem adjacent_planeTurn_pos_all (q : ℕ → Point 2) (n : ℕ)
    (hx : ∀ i j, i < j → j < n → planeX (q i) < planeX (q j))
    (hadj : ∀ i, i + 2 < n → 0 < planeTurn (q i) (q (i + 1)) (q (i + 2))) :
    ∀ i j k, i < j → j < k → k < n → 0 < planeTurn (q i) (q j) (q k) := by
  intro i j k hij hjk hkn
  induction k using Nat.strong_induction_on generalizing i j with
  | h k ih =>
      have hk2 : 2 ≤ k := by omega
      have hlast : ∀ a, a < k - 1 → 0 < planeTurn (q a) (q (k - 1)) (q k) := by
        intro a hak
        by_cases ha : a + 1 = k - 1
        · have hak' : a + 2 = k := by omega
          simpa [ha, hak'] using hadj a (by omega)
        · have ha' : a < k - 2 := by omega
          have hm : k - 2 < k - 1 := by omega
          have hmk : k - 1 < k := by omega
          have hold := ih (k - 1) (by omega) a (k - 2) ha' hm (by omega)
          have hadj' : 0 < planeTurn (q (k - 2)) (q (k - 1)) (q k) := by
            have h1 : k - 2 + 1 = k - 1 := by omega
            have h2 : k - 2 + 2 = k := by omega
            simpa [h1, h2] using hadj (k - 2) (by omega)
          exact (planeTurn_transitive_pos
            (hx a (k - 2) ha' (by omega))
            (hx (k - 2) (k - 1) hm (by omega))
            (hx (k - 1) k hmk hkn) hold hadj').2
      by_cases hjlast : j = k - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < k - 1 := by omega
        have hold := ih (k - 1) (by omega) i j hij hj' (by omega)
        exact (planeTurn_transitive_pos
          (hx i j hij (by omega))
          (hx j (k - 1) hj' (by omega))
          (hx (k - 1) k (by omega) hkn) hold (hlast j hj')).1

theorem adjacent_planeTurn_neg_all (q : ℕ → Point 2) (n : ℕ)
    (hx : ∀ i j, i < j → j < n → planeX (q i) < planeX (q j))
    (hadj : ∀ i, i + 2 < n → planeTurn (q i) (q (i + 1)) (q (i + 2)) < 0) :
    ∀ i j k, i < j → j < k → k < n → planeTurn (q i) (q j) (q k) < 0 := by
  intro i j k hij hjk hkn
  induction k using Nat.strong_induction_on generalizing i j with
  | h k ih =>
      have hk2 : 2 ≤ k := by omega
      have hlast : ∀ a, a < k - 1 → planeTurn (q a) (q (k - 1)) (q k) < 0 := by
        intro a hak
        by_cases ha : a + 1 = k - 1
        · have hak' : a + 2 = k := by omega
          simpa [ha, hak'] using hadj a (by omega)
        · have ha' : a < k - 2 := by omega
          have hm : k - 2 < k - 1 := by omega
          have hmk : k - 1 < k := by omega
          have hold := ih (k - 1) (by omega) a (k - 2) ha' hm (by omega)
          have hadj' : planeTurn (q (k - 2)) (q (k - 1)) (q k) < 0 := by
            have h1 : k - 2 + 1 = k - 1 := by omega
            have h2 : k - 2 + 2 = k := by omega
            simpa [h1, h2] using hadj (k - 2) (by omega)
          exact (planeTurn_transitive_neg
            (hx a (k - 2) ha' (by omega))
            (hx (k - 2) (k - 1) hm (by omega))
            (hx (k - 1) k hmk hkn) hold hadj').2
      by_cases hjlast : j = k - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < k - 1 := by omega
        have hold := ih (k - 1) (by omega) i j hij hj' (by omega)
        exact (planeTurn_transitive_neg
          (hx i j hij (by omega))
          (hx j (k - 1) hj' (by omega))
          (hx (k - 1) k (by omega) hkn) hold (hlast j hj')).1

/-- Every vertex of a strictly concave, southwest-to-northeast antichain
has a supporting line with negative slope and strictly positive intercept.
Equivalently, it is strictly exposed by a linear functional with both
coefficients positive, so adding the whole negative orthant does not destroy
the vertex. -/
theorem exists_negativeSlope_strict_support {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hy : ∀ {i j}, i < j → planeY (q j) < planeY (q i))
    (hturn : ∀ {i j k}, i < j → j < k → planeTurn (q i) (q j) (q k) < 0)
    (hanti : ∀ {i j}, i ≠ j →
      q i ∉ convexHull ℝ (negativeOrthant 2 ∪ {q j}))
    (k : Fin n) :
    ∃ m : ℝ, m < 0 ∧ 0 < planeLineValue m (q k) ∧
      ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
  have hn0 : 0 < n := by omega
  have hklt : k.val < n := k.isLt
  by_cases hk0 : k.val = 0
  · let r : Fin n := ⟨1, by omega⟩
    have hkr : k < r := by simpa [Fin.lt_iff_val_lt_val, r, hk0]
    let s := secantSlope (q k) (q r)
    have hs : s < 0 := secantSlope_neg_of_x_lt_y_gt (hx hkr) (hy hkr)
    have hkout : q k ∉ negativeOrthant 2 :=
      not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
        (hanti (show k ≠ r by exact ne_of_lt hkr))
    have hall (m : ℝ) (hsm : s < m) :
        ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
      intro j hj
      have hkj : k < j := by
        apply Fin.lt_iff_val_lt_val.mpr
        have : j.val ≠ 0 := by
          intro hj0
          apply hj
          apply Fin.ext
          omega
        omega
      have hslope : secantSlope (q k) (q j) < m := by
        by_cases hjr : j = r
        · simpa [hjr, s] using hsm
        · have hrj : r < j := by
            apply Fin.lt_iff_val_lt_val.mpr
            dsimp [r]
            have hjv : j.val ≠ 1 := by
              intro h
              apply hjr
              apply Fin.ext
              simpa [r] using h
            omega
          exact (secantSlope_long_lt_left_of_turn_neg (hx hkr) (hx hrj)
            (hturn hkr hrj)).trans hsm
      have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hkj)
      have hdx : 0 < planeX (q j) - planeX (q k) := sub_pos.mpr (hx hkj)
      nlinarith [mul_neg_of_pos_of_neg hdx (sub_neg.mpr hslope)]
    rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
    · have hky : 0 < planeY (q k) := by
        by_contra h
        apply hkout
        intro i
        fin_cases i
        · exact hkx.le
        · simpa [planeY] using le_of_not_gt h
      let u := max s (planeY (q k) / planeX (q k))
      let m := u / 2
      have hratio : planeY (q k) / planeX (q k) < 0 :=
        div_neg_of_pos_of_neg hky hkx
      have hu : u < 0 := max_lt hs hratio
      have hum : u < m := by dsimp [m]; linarith
      have hsm : s < m := (le_max_left _ _).trans_lt hum
      refine ⟨m, by dsimp [m]; linarith, ?_, hall m hsm⟩
      have hratm : planeY (q k) / planeX (q k) < m :=
        (le_max_right _ _).trans_lt hum
      have := (div_lt_iff_of_neg hkx).mp hratm
      dsimp [planeLineValue]
      nlinarith
    · have hky : 0 < planeY (q k) := by
        by_contra h
        apply hkout
        intro i
        fin_cases i
        · change planeX (q k) ≤ 0
          exact hkx.le
        · change planeY (q k) ≤ 0
          exact le_of_not_gt h
      let m := s / 2
      have hsm : s < m := by dsimp [m]; linarith
      refine ⟨m, by dsimp [m]; linarith, ?_, hall m hsm⟩
      dsimp [planeLineValue]
      rw [hkx, mul_zero, sub_zero]
      exact hky
    · have hnum : 0 < interceptNumerator (q k) (q r) :=
        interceptNumerator_pos_of_left_nonneg (hx hkr) (hy hkr) hkx.le
          (hanti (show k ≠ r by exact ne_of_lt hkr))
      let B := planeLineValue s (q k)
      have hB : 0 < B := by
        have heq : planeLineValue (secantSlope (q k) (q r)) (q k) =
            planeLineValue (secantSlope (q k) (q r)) (q r) := by
          have hdiff := planeLineValue_sub_eq_slope
            (m := secantSlope (q k) (q r)) (hx hkr)
          have hz : planeLineValue (secantSlope (q k) (q r)) (q r) -
              planeLineValue (secantSlope (q k) (q r)) (q k) = 0 := by
            simpa only [sub_self, mul_zero] using hdiff
          exact (sub_eq_zero.mp hz).symm
        rw [show B = planeLineValue (secantSlope (q k) (q r)) (q k) by rfl,
          heq, planeLineValue_secantSlope (hx hkr)]
        exact div_pos hnum (sub_pos.mpr (hx hkr))
      let U := min 0 (s + B / (2 * planeX (q k)))
      let m := (s + U) / 2
      have hden : 0 < 2 * planeX (q k) := mul_pos (by norm_num) hkx
      have hratioB : 0 < B / (2 * planeX (q k)) := div_pos hB hden
      have hsU : s < U := lt_min hs (by
        linarith [hratioB])
      have hmU : m < U := by dsimp [m]; linarith
      have hsm : s < m := by dsimp [m]; linarith
      have hm0 : m < 0 := hmU.trans_le (min_le_left _ _)
      refine ⟨m, hm0, ?_, hall m hsm⟩
      have hmB : m ≤ s + B / (2 * planeX (q k)) :=
        hmU.le.trans (min_le_right _ _)
      have hrewrite : planeLineValue m (q k) =
          B - (m - s) * planeX (q k) := by
        simp [B, planeLineValue]
        ring
      rw [hrewrite]
      have hmsB : m - s ≤ B / (2 * planeX (q k)) := by linarith
      have := (le_div_iff₀ hden).mp hmsB
      nlinarith [mul_pos hB (show (0 : ℝ) < 1 by norm_num)]
  · by_cases hklast : k.val + 1 = n
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      let s := secantSlope (q l) (q k)
      have hs : s < 0 := secantSlope_neg_of_x_lt_y_gt (hx hlk) (hy hlk)
      have hkout : q k ∉ negativeOrthant 2 :=
        not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
          (hanti (show k ≠ l by exact ne_of_gt hlk))
      have hall (m : ℝ) (hms : m < s) :
          ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hj
        have hjk : j < k := by
          apply Fin.lt_iff_val_lt_val.mpr
          have : j.val ≠ k.val := by
            intro h
            exact hj (Fin.ext h)
          omega
        have hslope : m < secantSlope (q j) (q k) := by
          by_cases hjl : j = l
          · simpa [hjl, s] using hms
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have hjv : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                apply Fin.ext
                simpa [l] using h
              omega
            exact hms.trans (secantSlope_right_lt_long_of_turn_neg
              (hx hjl') (hx hlk) (hturn hjl' hlk))
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hjk)
        have hdx : 0 < planeX (q k) - planeX (q j) := sub_pos.mpr (hx hjk)
        nlinarith [mul_pos hdx (sub_pos.mpr hslope)]
      rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
      · have hnum : 0 < interceptNumerator (q l) (q k) :=
          interceptNumerator_pos_of_right_nonpos (hx hlk) (hy hlk) hkx.le
            (hanti (show k ≠ l by exact ne_of_gt hlk))
        let B := planeLineValue s (q k)
        have hB : 0 < B := by
          rw [show B = planeLineValue (secantSlope (q l) (q k)) (q k) by rfl]
          rw [planeLineValue_secantSlope (hx hlk)]
          exact div_pos hnum (sub_pos.mpr (hx hlk))
        let d := min 1 (B / (2 * (-planeX (q k))))
        let m := s - d
        have hden : 0 < 2 * (-planeX (q k)) :=
          mul_pos (by norm_num) (neg_pos.mpr hkx)
        have hratioB : 0 < B / (2 * (-planeX (q k))) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by norm_num) hratioB
        refine ⟨m, by dsimp [m]; linarith, ?_, hall m (by dsimp [m]; linarith)⟩
        have hdB : d ≤ B / (2 * (-planeX (q k))) := min_le_right _ _
        have hrewrite : planeLineValue m (q k) = B + d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith
      · have hky : 0 < planeY (q k) := by
          by_contra h
          apply hkout
          intro i
          fin_cases i
          · change planeX (q k) ≤ 0
            exact hkx.le
          · change planeY (q k) ≤ 0
            exact le_of_not_gt h
        let m := s - 1
        refine ⟨m, by dsimp [m]; linarith, ?_, hall m (by dsimp [m]; linarith)⟩
        dsimp [planeLineValue]
        rw [hkx, mul_zero, sub_zero]
        exact hky
      · let u := min s (planeY (q k) / planeX (q k))
        let m := u - 1
        have hums : m < s := (sub_lt_self u (by norm_num)).trans_le (min_le_left _ _)
        have humr : m < planeY (q k) / planeX (q k) :=
          (sub_lt_self u (by norm_num)).trans_le (min_le_right _ _)
        refine ⟨m, hums.trans hs, ?_, hall m hums⟩
        have := (lt_div_iff₀ hkx).mp humr
        dsimp [planeLineValue]
        nlinarith
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨k.val + 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      have hkr : k < r := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [r]
        omega
      let sL := secantSlope (q l) (q k)
      let sR := secantSlope (q k) (q r)
      have hsL : sL < 0 := secantSlope_neg_of_x_lt_y_gt (hx hlk) (hy hlk)
      have hsR : sR < sL :=
        (slope_gt_slope_iff_turn_neg (hx hlk) (hx hkr)).2 (hturn hlk hkr)
      have hkout : q k ∉ negativeOrthant 2 :=
        not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
          (hanti (show k ≠ l by exact ne_of_gt hlk))
      have hleft (m : ℝ) (hm : m < sL) :
          ∀ j, j < k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hjk
        have hslope : sL ≤ secantSlope (q j) (q k) := by
          by_cases hjl : j = l
          · simp [hjl, sL]
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have hjv : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                apply Fin.ext
                simpa [l] using h
              omega
            exact (secantSlope_right_lt_long_of_turn_neg (hx hjl') (hx hlk)
              (hturn hjl' hlk)).le
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hjk)
        have hdx : 0 < planeX (q k) - planeX (q j) := sub_pos.mpr (hx hjk)
        nlinarith [mul_pos hdx (sub_pos.mpr (hm.trans_le hslope))]
      have hright (m : ℝ) (hm : sR < m) :
          ∀ j, k < j → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hkj
        have hslope : secantSlope (q k) (q j) ≤ sR := by
          by_cases hjr : j = r
          · simp [hjr, sR]
          · have hrj : r < j := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [r]
              have hjv : j.val ≠ k.val + 1 := by
                intro h
                apply hjr
                apply Fin.ext
                simpa [r] using h
              omega
            exact (secantSlope_long_lt_left_of_turn_neg (hx hkr) (hx hrj)
              (hturn hkr hrj)).le
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hkj)
        have hdx : 0 < planeX (q j) - planeX (q k) := sub_pos.mpr (hx hkj)
        nlinarith [mul_neg_of_pos_of_neg hdx (sub_neg.mpr (hslope.trans_lt hm))]
      have hall (m : ℝ) (hmL : m < sL) (hmR : sR < m) :
          ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hj
        rcases lt_or_gt_of_ne hj with hjk | hkj
        · exact hleft m hmL j hjk
        · exact hright m hmR j hkj
      rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
      · have hnum : 0 < interceptNumerator (q l) (q k) :=
          interceptNumerator_pos_of_right_nonpos (hx hlk) (hy hlk) hkx.le
            (hanti (show k ≠ l by exact ne_of_gt hlk))
        let B := planeLineValue sL (q k)
        have hB : 0 < B := by
          rw [show B = planeLineValue (secantSlope (q l) (q k)) (q k) by rfl]
          rw [planeLineValue_secantSlope (hx hlk)]
          exact div_pos hnum (sub_pos.mpr (hx hlk))
        let d := min ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
        let m := sL - d
        have hden : 0 < 2 * (-planeX (q k)) :=
          mul_pos (by norm_num) (neg_pos.mpr hkx)
        have hratioB : 0 < B / (2 * (-planeX (q k))) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by linarith) hratioB
        have hmR : sR < m := by
          have hdgap := min_le_left ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
          dsimp [m, d]
          linarith
        refine ⟨m, (sub_lt_self sL hd).trans hsL, ?_,
          hall m (sub_lt_self sL hd) hmR⟩
        have hdB := min_le_right ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
        have hrewrite : planeLineValue m (q k) = B + d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith
      · have hky : 0 < planeY (q k) := by
          by_contra h
          apply hkout
          intro i
          fin_cases i
          · change planeX (q k) ≤ 0
            exact hkx.le
          · change planeY (q k) ≤ 0
            exact le_of_not_gt h
        let m := (sL + sR) / 2
        have hmL : m < sL := by dsimp [m]; linarith
        have hmR : sR < m := by dsimp [m]; linarith
        refine ⟨m, hmL.trans hsL, ?_, hall m hmL hmR⟩
        dsimp [planeLineValue]
        rw [hkx, mul_zero, sub_zero]
        exact hky
      · have hnum : 0 < interceptNumerator (q k) (q r) :=
          interceptNumerator_pos_of_left_nonneg (hx hkr) (hy hkr) hkx.le
            (hanti (show k ≠ r by exact ne_of_lt hkr))
        let B := planeLineValue sR (q k)
        have hB : 0 < B := by
          have heq : planeLineValue (secantSlope (q k) (q r)) (q k) =
              planeLineValue (secantSlope (q k) (q r)) (q r) := by
            have := planeLineValue_sub_eq_slope (m := secantSlope (q k) (q r))
              (hx hkr)
            have hz : planeLineValue (secantSlope (q k) (q r)) (q r) -
                planeLineValue (secantSlope (q k) (q r)) (q k) = 0 := by
              simpa only [sub_self, mul_zero] using this
            exact (sub_eq_zero.mp hz).symm
          rw [show B = planeLineValue (secantSlope (q k) (q r)) (q k) by rfl,
            heq, planeLineValue_secantSlope (hx hkr)]
          exact div_pos hnum (sub_pos.mpr (hx hkr))
        let d := min ((sL - sR) / 2) (B / (2 * planeX (q k)))
        let m := sR + d
        have hden : 0 < 2 * planeX (q k) := mul_pos (by norm_num) hkx
        have hratioB : 0 < B / (2 * planeX (q k)) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by linarith) hratioB
        have hmL : m < sL := by
          have hdgap := min_le_left ((sL - sR) / 2) (B / (2 * planeX (q k)))
          dsimp [m, d]
          linarith
        refine ⟨m, hmL.trans hsL, ?_, hall m hmL (lt_add_of_pos_right sR hd)⟩
        have hdB := min_le_right ((sL - sR) / 2) (B / (2 * planeX (q k)))
        have hrewrite : planeLineValue m (q k) = B - d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith

/-- A finite concave antichain is in relative convex position even after
the negative orthant is adjoined. -/
theorem fin_concaveChain_negativeOrthantCap {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hy : ∀ {i j}, i < j → planeY (q j) < planeY (q i))
    (hturn : ∀ {i j k}, i < j → j < k → planeTurn (q i) (q j) (q k) < 0)
    (hanti : ∀ {i j}, i ≠ j →
      q i ∉ convexHull ℝ (negativeOrthant 2 ∪ {q j})) :
    ∀ k : Fin n, q k ∉ convexHull ℝ
      (negativeOrthant 2 ∪
        ↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) := by
  classical
  intro k hkHull
  obtain ⟨m, hm, hkpos, hstrict⟩ :=
    exists_negativeSlope_strict_support hn q hx hy hturn hanti k
  let H : Set (Point 2) := {z | planeLineValue m z < planeLineValue m (q k)}
  have hsub : negativeOrthant 2 ∪
      ↑((Finset.univ.image q).erase (q k)) ⊆ H := by
    intro z hz
    rcases hz with hzQ | hzC
    · exact (planeLineValue_nonpos_on_negativeOrthant hm.le hzQ).trans_lt hkpos
    · obtain ⟨hzneq, hzmem⟩ := Finset.mem_erase.mp hzC
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hzmem
      apply hstrict j
      intro hjk
      apply hzneq
      exact congrArg q hjk
  have : q k ∈ H := convexHull_min hsub (convex_planeLineValue_lt _ _) hkHull
  have hbad : planeLineValue m (q k) < planeLineValue m (q k) := by
    simpa [H] using this
  exact (lt_irrefl _ hbad)

theorem convex_planeTurn_nonneg (p q : Point 2) :
    Convex ℝ {z : Point 2 | 0 ≤ planeTurn p q z} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  calc
    0 ≤ a * planeTurn p q x + b * planeTurn p q y :=
      add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    _ = planeTurn p q (a • x + b • y) := by
      have hb' : b = 1 - a := by linarith
      rw [hb']
      simp only [planeTurn, planeX, planeY, PiLp.add_apply, PiLp.smul_apply]
      ring

/-- A chain whose every ordered triple turns left is in ordinary convex
position.  Endpoints are exposed by the first coordinate; an internal point
is separated by the line through its two neighboring points. -/
theorem fin_convexChain_inConvexPosition {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hturn : ∀ {i j k}, i < j → j < k → 0 < planeTurn (q i) (q j) (q k)) :
    InConvexPosition (Finset.univ.image q) := by
  classical
  intro z hzC
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzC
  by_cases hk0 : k.val = 0
  · let H : Set (Point 2) := {z | planeX (q k) < planeX z}
    have hconv : Convex ℝ H := by
      exact (convex_Ioi (planeX (q k))).linear_preimage
        { toFun := planeX
          map_add' := by intro x y; simp [planeX]
          map_smul' := by intro c x; simp [planeX] }
    intro hkHull
    have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆ H := by
      intro w hw
      obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
      apply hx
      apply Fin.lt_iff_val_lt_val.mpr
      have : j.val ≠ 0 := by
        intro h
        apply hwne
        congr 1
        apply Fin.ext
        simpa [hk0] using h
      omega
    have := convexHull_min hsub hconv hkHull
    have hbad : planeX (q k) < planeX (q k) := by simpa [H] using this
    exact (lt_irrefl _ hbad)
  · by_cases hklast : k.val + 1 = n
    · let H : Set (Point 2) := {z | planeX z < planeX (q k)}
      have hconv : Convex ℝ H := by
        exact (convex_Iio (planeX (q k))).linear_preimage
          { toFun := planeX
            map_add' := by intro x y; simp [planeX]
            map_smul' := by intro c x; simp [planeX] }
      intro hkHull
      have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆ H := by
        intro w hw
        obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
        apply hx
        apply Fin.lt_iff_val_lt_val.mpr
        have : j.val ≠ k.val := by
          intro h
          apply hwne
          congr 1
          exact Fin.ext h
        omega
      have := convexHull_min hsub hconv hkHull
      have hbad : planeX (q k) < planeX (q k) := by simpa [H] using this
      exact (lt_irrefl _ hbad)
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨k.val + 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      have hkr : k < r := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [r]
        omega
      intro hkHull
      have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆
          {z | 0 ≤ planeTurn (q l) (q r) z} := by
        intro w hw
        obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
        rcases lt_trichotomy j k with hjk | hjk | hkj
        · by_cases hjl : j = l
          · subst j
            dsimp [planeTurn]
            nlinarith
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                exact Fin.ext (by simpa [l] using h)
              omega
            change 0 ≤ planeTurn (q l) (q r) (q j)
            rw [planeTurn_rotate]
            exact (hturn hjl' (hlk.trans hkr)).le
        · exact (hwne (congrArg q hjk)).elim
        · by_cases hjr : j = r
          · subst j
            dsimp [planeTurn]
            nlinarith
          · have hrj : r < j := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [r]
              have : j.val ≠ k.val + 1 := by
                intro h
                apply hjr
                exact Fin.ext (by simpa [r] using h)
              omega
            exact (hturn (hlk.trans hkr) hrj).le
      have hmem := convexHull_min hsub (convex_planeTurn_nonneg (q l) (q r)) hkHull
      have hkneg : planeTurn (q l) (q r) (q k) < 0 := by
        rw [planeTurn_swap_right]
        exact neg_neg_of_pos (hturn hlk hkr)
      exact (not_le_of_gt hkneg) hmem

/-- The projected version of the exposed-point part of `PCap`. -/
def ProjectedPCap (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) (C : Finset (Point 3)) : Prop :=
  ∀ x ∈ C,
    π x ∉ convexHull ℝ
      (π '' P ∪ π '' (↑(C.erase x) : Set (Point 3)))

/-- Convex position after applying a (not necessarily injective globally)
linear projection. -/
def ProjectedConvexPosition
    (π : Point 3 →ᵃ[ℝ] Point 2) (C : Finset (Point 3)) : Prop :=
  ∀ x ∈ C,
    π x ∉ convexHull ℝ (π '' (↑(C.erase x) : Set (Point 3)))

/-- Convex position in the projected plane always lifts to convex position
upstairs.  No injectivity hypothesis is needed: the displayed projected
extreme-point certificates themselves rule out a collision. -/
theorem ProjectedConvexPosition.inConvexPosition
    {C : Finset (Point 3)} {π : Point 3 →ᵃ[ℝ] Point 2}
    (hC : ProjectedConvexPosition π C) : InConvexPosition C := by
  intro x hxC hxHull
  apply hC x hxC
  rw [← π.image_convexHull]
  exact ⟨x, hxHull, rfl⟩

/-- A projected `P`-cap lifts to an actual `P`-cap. -/
theorem ProjectedPCap.pcap
    {P : Set (Point 3)} {C : Finset (Point 3)}
    {π : Point 3 →ᵃ[ℝ] Point 2} (hC : ProjectedPCap P π C) :
    PCap P C := by
  refine ⟨?_, ?_⟩
  · intro x hxC hxHull
    apply hC x hxC
    apply convexHull_mono (Set.subset_union_right)
    rw [← π.image_convexHull]
    exact ⟨x, hxHull, rfl⟩
  · intro x hxC hxHull
    apply hC x hxC
    rw [← Set.image_union, ← π.image_convexHull]
    exact ⟨x, hxHull, rfl⟩

/-- A coloring by `m` colors whose color classes are chains. -/
def IsChainColoring {α : Type*} (r : α → α → Prop) {m : ℕ}
    (color : α → Fin m) : Prop :=
  ∀ {x y}, color x = color y → r x y ∨ r y x

/-! The finite matching-to-chain part of Dilworth's theorem. -/

structure IncreasingMatching (α : Type*) [PartialOrder α] (m : ℕ) where
  next : α → α ⊕ Fin m
  injective_next : Function.Injective next
  lt_of_next_eq : ∀ {x y}, next x = Sum.inl y → x < y

namespace IncreasingMatching

variable {α : Type*} [Fintype α] [PartialOrder α] {m : ℕ}

private theorem gt_wellFounded : WellFounded (fun y x : α => x < y) := by
  let ht : IsTrans α (fun y x : α => x < y) := ⟨by
    intro a b c hba hcb
    exact hcb.trans hba⟩
  let hi : Std.Irrefl (fun y x : α => x < y) := ⟨by
    intro a
    exact lt_irrefl a⟩
  exact @Finite.wellFounded_of_trans_of_irrefl α _ _ ht hi

/-- The unique forward trace of a point ends at a dummy color. -/
inductive TracesTo (M : IncreasingMatching α m) : α → ℕ → Fin m → Prop
  | stop {x : α} {c : Fin m} (h : M.next x = Sum.inr c) :
      TracesTo M x 0 c
  | step {x y : α} {n : ℕ} {c : Fin m}
      (hxy : M.next x = Sum.inl y) (hrest : TracesTo M y n c) :
      TracesTo M x (n + 1) c

theorem exists_trace (M : IncreasingMatching α m) :
    ∀ x, ∃ n c, TracesTo M x n c := by
  intro x
  let Q : α → Prop := fun x => ∃ n c, TracesTo M x n c
  change Q x
  refine (gt_wellFounded (α := α)).induction x ?_
  intro x ih
  cases hx : M.next x with
  | inl y =>
      obtain ⟨n, c, htrace⟩ := ih y (M.lt_of_next_eq hx)
      exact ⟨n + 1, c, TracesTo.step hx htrace⟩
  | inr c => exact ⟨0, c, TracesTo.stop hx⟩

theorem trace_start_unique (M : IncreasingMatching α m) {x y : α}
    {n : ℕ} {c : Fin m} (hx : TracesTo M x n c) (hy : TracesTo M y n c) :
    x = y := by
  induction hx generalizing y with
  | stop hx =>
      cases hy with
      | stop hy => exact M.injective_next (hx.trans hy.symm)
  | step hx hrest ih =>
      cases hy with
      | step hy hrest' =>
          have htail := ih hrest'
          apply M.injective_next
          exact hx.trans <|
            (congrArg (Sum.inl : α → α ⊕ Fin m) htail).trans hy.symm

theorem le_of_traces (M : IncreasingMatching α m) {x y : α}
    {nx ny : ℕ} {c : Fin m} (hx : TracesTo M x nx c) (hy : TracesTo M y ny c)
    (hdepth : nx ≤ ny) : y ≤ x := by
  induction hy generalizing x nx with
  | stop hy =>
      have hnx : nx = 0 := Nat.eq_zero_of_le_zero hdepth
      subst nx
      have hxy := M.trace_start_unique hx (TracesTo.stop hy)
      simpa [hxy]
  | @step y y' ny c hy hrest ih =>
      by_cases heq : nx = ny + 1
      · subst nx
        have hxy := M.trace_start_unique hx (TracesTo.step hy hrest)
        simpa [hxy]
      · have hnx : nx ≤ ny := by omega
        exact (M.lt_of_next_eq hy).le.trans (ih hx hnx)

/-- Distance to the terminal dummy color, together with that color. -/
noncomputable def traceData (M : IncreasingMatching α m) (x : α) : ℕ × Fin m :=
  let h := M.exists_trace x
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

noncomputable def depth (M : IncreasingMatching α m) (x : α) : ℕ :=
  (M.traceData x).1

noncomputable def terminal (M : IncreasingMatching α m) (x : α) : Fin m :=
  (M.traceData x).2

theorem traceData_spec (M : IncreasingMatching α m) (x : α) :
    TracesTo M x (M.depth x) (M.terminal x) := by
  simp only [depth, terminal, traceData]
  exact Classical.choose_spec (Classical.choose_spec (M.exists_trace x))

theorem le_of_depth_le_of_terminal_eq (M : IncreasingMatching α m) :
    ∀ x y, M.depth x ≤ M.depth y → M.terminal x = M.terminal y → y ≤ x := by
  intro x y hdepth hterminal
  have hx := M.traceData_spec x
  rw [hterminal] at hx
  exact M.le_of_traces hx (M.traceData_spec y) hdepth

theorem terminal_chainColoring (M : IncreasingMatching α m) :
    IsChainColoring (fun x y : α => x ≤ y) M.terminal := by
  intro x y hxy
  rcases le_total (M.depth x) (M.depth y) with h | h
  · exact Or.inr (M.le_of_depth_le_of_terminal_eq x y h hxy)
  · exact Or.inl (M.le_of_depth_le_of_terminal_eq y x h hxy.symm)

end IncreasingMatching

/-- The precise finite consequence of Dilworth used in Proposition 2.1:
if every antichain has at most `m` elements, the poset is the union of `m`
chains. -/
def HasDilworthChainCover {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) : Prop :=
  ∀ m : ℕ, 0 < m →
    (∀ A : Finset α, IsAntichain r (↑A : Set α) → A.card ≤ m) →
      ∃ color : α → Fin m, IsChainColoring r color

/-- The finite chain-cover theorem for partial orders.  The proof is the
standard Hall matching proof of Dilworth: minimal elements of a test set
use the `m` dummy right vertices, while every nonminimal element contributes
its own strict-successor right vertex.  Following the resulting increasing
matching partitions the poset into its terminal-color chains. -/
theorem finite_dilworth_partialOrder {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : HasDilworthChainCover (fun x y : α => x ≤ y) := by
  classical
  intro m hm hwidth
  let R : α → α ⊕ Fin m → Prop := fun x z =>
    match z with
    | Sum.inl y => x < y
    | Sum.inr _ => True
  have hHall : ∀ A : Finset α,
      A.card ≤ ({z | ∃ x ∈ A, R x z} : Finset (α ⊕ Fin m)).card := by
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    let minima : Finset α := A.filter fun x => ¬ ∃ y ∈ A, y < x
    have hminAnti : IsAntichain (fun x y : α => x ≤ y)
        (↑minima : Set α) := by
      intro x hx y hy hxy hle
      simp only [minima, Finset.mem_coe, Finset.mem_filter] at hx hy
      apply hy.2
      exact ⟨x, hx.1, lt_of_le_of_ne hle hxy⟩
    have hminCard : minima.card ≤ m := hwidth minima hminAnti
    let rank : ↑minima → Fin m := fun x =>
      ⟨(Fintype.equivFin (↑minima) x).val,
        (Fintype.equivFin (↑minima) x).isLt.trans_le (by simpa using hminCard)⟩
    have hrank : Function.Injective rank := by
      intro x y hxy
      apply (Fintype.equivFin (↑minima)).injective
      apply Fin.ext
      simpa [rank] using congrArg Fin.val hxy
    let f : ↑A → α ⊕ Fin m := fun x =>
      if hx : x.1 ∈ minima then Sum.inr (rank ⟨x.1, hx⟩) else Sum.inl x.1
    have hfmem (x : ↑A) : f x ∈ ({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m)) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hx : x.1 ∈ minima
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hA
        exact ⟨a, ha, by simp [f, hx, R]⟩
      · have hex : ∃ y ∈ A, y < x.1 := by
          simpa [minima, x.2] using hx
        obtain ⟨y, hyA, hyx⟩ := hex
        exact ⟨y, hyA, by simpa [f, hx, R] using hyx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : x.1 ∈ minima
      · by_cases hy : y.1 ∈ minima
        · have hr : rank ⟨x.1, hx⟩ = rank ⟨y.1, hy⟩ :=
            @Sum.inr.inj α (Fin m) _ _ (by simpa [f, hx, hy] using hxy)
          have hval : x.1 = y.1 :=
            congrArg (fun z : ↑minima => z.1) (hrank hr)
          exact Subtype.ext hval
        · have hbad : (Sum.inr (rank ⟨x.1, hx⟩) : α ⊕ Fin m) = Sum.inl y.1 := by
            simpa [f, hx, hy] using hxy
          exact (Sum.inr_ne_inl hbad).elim
      · by_cases hy : y.1 ∈ minima
        · have hbad : (Sum.inl x.1 : α ⊕ Fin m) = Sum.inr (rank ⟨y.1, hy⟩) := by
            simpa [f, hx, hy] using hxy
          exact (Sum.inl_ne_inr hbad).elim
        · have heq : (Sum.inl x.1 : α ⊕ Fin m) = Sum.inl y.1 := by
            simpa [f, hx, hy] using hxy
          exact Subtype.ext (@Sum.inl.inj α (Fin m) _ _ heq)
    let g : ↑A → ↑({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m)) :=
      fun x => ⟨f x, hfmem x⟩
    have hg : Function.Injective g := fun _ _ h => hf (congrArg Subtype.val h)
    rw [← Fintype.card_coe A,
      ← Fintype.card_coe ({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m))]
    exact Fintype.card_le_of_injective g hg
  obtain ⟨next, hnext, hR⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hHall
  let M : IncreasingMatching α m :=
    { next := next
      injective_next := hnext
      lt_of_next_eq := by
        intro x y hxy
        have := hR x
        simpa [R, hxy] using this }
  exact ⟨M.terminal, M.terminal_chainColoring⟩

/-- Dilworth's finite chain-cover consequence for preorders.  Mutual
comparability is quotiented out by `Antisymmetrization`; a representative
order embedding transfers antichains to the original preorder, and the
resulting quotient chain coloring is pulled back. -/
theorem finite_dilworth_preorder {α : Type*} [Fintype α] [DecidableEq α]
    [Preorder α] : HasDilworthChainCover (fun x y : α => x ≤ y) := by
  classical
  intro m hm hwidth
  let β := Antisymmetrization α (fun x y : α => x ≤ y)
  letI : Fintype β := Fintype.ofSurjective
    (toAntisymmetrization (fun x y : α => x ≤ y)) fun q =>
      ⟨ofAntisymmetrization (fun x y : α => x ≤ y) q,
        toAntisymmetrization_ofAntisymmetrization (fun x y : α => x ≤ y) q⟩
  let e : β ↪o α := OrderEmbedding.ofAntisymmetrization α
  have hwidthβ (A : Finset β)
      (hA : IsAntichain (fun x y : β => x ≤ y) (↑A : Set β)) : A.card ≤ m := by
    let B : Finset α := A.map e.toEmbedding
    have hB : IsAntichain (fun x y : α => x ≤ y) (↑B : Set α) := by
      intro x hx y hy hxy hle
      simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨qx, hqx, rfl⟩ := hx
      obtain ⟨qy, hqy, hqyval⟩ := hy
      subst y
      have hqq : qx = qy := hA.eq hqx hqy (e.le_iff_le.mp hle)
      exact hxy (congrArg e hqq)
    have := hwidth B hB
    simpa [B] using this
  obtain ⟨color, hcolor⟩ :=
    finite_dilworth_partialOrder (α := β) m hm hwidthβ
  refine ⟨fun x => color (toAntisymmetrization (fun x y : α => x ≤ y) x), ?_⟩
  intro x y hxy
  rcases hcolor hxy with hle | hge
  · exact Or.inl (toAntisymmetrization_le_toAntisymmetrization_iff.mp hle)
  · exact Or.inr (toAntisymmetrization_le_toAntisymmetrization_iff.mp hge)

/-- Unbundled form, convenient when several preorders live on the same
finite carrier. -/
theorem finite_dilworth_of_isPreorder {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) (hr : IsPreorder α r) : HasDilworthChainCover r := by
  letI : Preorder α :=
    { le := r
      le_refl := hr.refl
      le_trans := hr.trans }
  change HasDilworthChainCover (fun x y : α => x ≤ y)
  exact finite_dilworth_preorder (α := α)

/-- A family of finite preorders, one for every edge direction, with
the two properties used in the multi-order Dilworth argument. -/
structure MultiOrderDilworthData (α ι : Type*)
    [Fintype α] [DecidableEq α] [Fintype ι] where
  rel : ι → α → α → Prop
  preorder : ∀ i, IsPreorder α (rel i)
  separated : ∀ {x y}, x ≠ y →
    ∃ i, ¬ rel i x y ∧ ¬ rel i y x

/-- The exact iterated-Dilworth pigeonhole argument.  If each of `e`
orders had width at most `m`, color into `m` chains in every order.  The
resulting map into `m^e` color vectors cannot be injective, while the
separation property says that it must be injective. -/
theorem MultiOrderDilworthData.exists_large_antichain
    {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι]
    (D : MultiOrderDilworthData α ι) {m : ℕ} (hm : 0 < m)
    (hcard : m ^ Fintype.card ι < Fintype.card α) :
    ∃ i : ι, ∃ A : Finset α,
      IsAntichain (D.rel i) (↑A : Set α) ∧ m < A.card := by
  classical
  by_contra h
  push Not at h
  have hbound (i : ι) :
      ∀ A : Finset α, IsAntichain (D.rel i) (↑A : Set α) → A.card ≤ m := by
    intro A hA
    exact h i A hA
  choose color hcolor using fun i =>
    finite_dilworth_of_isPreorder (D.rel i) (D.preorder i) m hm (hbound i)
  let signature : α → (∀ i : ι, Fin m) := fun x i => color i x
  have hsignature : Function.Injective signature := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hixy, hiyx⟩ := D.separated hne
    have hc : color i x = color i y := congrFun hxy i
    exact (hcolor i hc).elim hixy hiyx
  have hle : Fintype.card α ≤ m ^ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective signature hsignature
  exact (Nat.not_le_of_lt hcard) hle

/-- All geometric inputs to Proposition 2.1, organized edge by edge.

`separated` is the projection-separation lemma combined with `PFree`, and `planar_dichotomy`
is the cups--caps theorem after projection. -/
structure ProjectionOrderCertificate
    (P : Set (Point 3)) (X : Finset (Point 3)) (ι : Type*)
    [Fintype ι] where
  projection : ι → Point 3 →ᵃ[ℝ] Point 2
  separated : PFree P X → ∀ {x y : ↑X}, x ≠ y →
    ∃ i, ¬ projectionLE P (projection i) x.1 y.1 ∧
      ¬ projectionLE P (projection i) y.1 x.1
  planar_dichotomy : ∀ i (A : Finset (↑X)) (a b : ℕ),
    2 ≤ a → 2 ≤ b →
    IsAntichain (fun x y : ↑X => projectionLE P (projection i) x.1 y.1)
      (↑A : Set (↑X)) →
    Nat.choose (a + b - 4) (a - 2) < A.card →
      (∃ C : Finset (↑X), C ⊆ A ∧ C.card = a ∧
        ProjectedPCap P (projection i) (C.map (Function.Embedding.subtype _))) ∨
      (∃ C : Finset (↑X), C ⊆ A ∧ C.card = b ∧
        ProjectedConvexPosition (projection i)
          (C.map (Function.Embedding.subtype _)))

private lemma polytope_ordered_pairwise_lt {I : List ℕ} (hI : Ordered I) :
    I.Pairwise (· < ·) := by
  induction I with
  | nil => simp
  | cons x tail ih =>
      cases tail with
      | nil => simp
      | cons y tail =>
          exact List.Pairwise.cons_cons_of_trans hI.1 (ih hI.2)

private lemma polytope_tightPath_get_consecutive
    {χ : ℕ → ℕ → ℕ → Bool} {c : Bool} {I : List ℕ}
    (hI : TightPath χ c I) (i : ℕ) (hi : i + 2 < I.length) :
    χ I[i] I[i + 1] I[i + 2] = c := by
  induction i generalizing I with
  | zero =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail => simpa [TightPath] using hI.1
  | succ i ih =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail =>
                  have hi' : i + 2 < (y :: z :: tail).length :=
                    Nat.lt_of_succ_lt_succ hi
                  have hh := ih hI.2 hi'
                  simpa using hh

/-- The generic edge projections of an oriented trihedral supply every
geometric input in the projection-certificate form of Proposition 2.1. -/
def OrientedTrihedral.GenericProjectionFamily.toProjectionOrderCertificate
    {T : OrientedTrihedral} {X : Finset (Point 3)}
    (G : T.GenericProjectionFamily X) :
    ProjectionOrderCertificate T.carrier X (Fin 3) := by
  classical
  refine {
    projection := G.projection
    separated := G.separated
    planar_dichotomy := ?_ }
  intro edge A a b ha hb hanti hcard
  have hApos : 0 < A.card := Nat.zero_lt_of_lt hcard
  let coordinate : ↥A → ℝ := fun x => planeX (G.projection edge x.1.1)
  have hcoordinate : Function.Injective coordinate := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    exact (G.planeX_ne edge (x := x.1.1) (y := y.1.1) x.1.2 y.1.2 hne) hxy
  letI : LinearOrder ↥A := LinearOrder.lift' coordinate hcoordinate
  let e : Fin A.card ≃o ↥A := Fintype.orderIsoFinOfCardEq ↥A (by simp)
  let u : ℕ → ↥X := fun j =>
    if hj : j < A.card then (e ⟨j, hj⟩).1 else (e ⟨0, hApos⟩).1
  let p : ℕ → Point 2 := fun j => G.projection edge (u j).1
  have huA {j : ℕ} (hj : j < A.card) : u j ∈ A := by
    change (if h : j < A.card then (e ⟨j, h⟩).1 else (e ⟨0, hApos⟩).1) ∈ A
    rw [dif_pos hj]
    exact (e ⟨j, hj⟩).2
  have hpX : ∀ j ∈ Finset.range A.card, ∀ k ∈ Finset.range A.card,
      j < k → planeX (p j) < planeX (p k) := by
    intro j hj k hk hjk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have he := e.strictMono (show (⟨j, hj'⟩ : Fin A.card) < ⟨k, hk'⟩ by exact hjk)
    change coordinate (e ⟨j, hj'⟩) < coordinate (e ⟨k, hk'⟩) at he
    simpa [coordinate, p, u, hj', hk'] using he
  have hpSlope : ∀ j ∈ Finset.range A.card, ∀ k ∈ Finset.range A.card,
      ∀ l ∈ Finset.range A.card, j < k → k < l →
        secantSlope (p j) (p k) ≠ secantSlope (p k) (p l) := by
    intro j hj k hk l hl hjk hkl
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    apply G.slope_ne edge (u j).2 (u k).2 (u l).2
    · intro h
      exact (ne_of_lt (hpX j hj k hk hjk)) (congrArg (planeX ∘ G.projection edge) h)
    · intro h
      exact (ne_of_lt (hpX k hk l hl hkl)) (congrArg (planeX ∘ G.projection edge) h)
    · intro h
      exact (ne_of_lt (hpX j hj l hl (hjk.trans hkl)))
        (congrArg (planeX ∘ G.projection edge) h)
  have hchoose : Nat.choose (b + a - 4) (b - 2) =
      Nat.choose (a + b - 4) (a - 2) := by
    have hsum : a + b - 4 = (a - 2) + (b - 2) := by omega
    calc
      Nat.choose (b + a - 4) (b - 2) =
          Nat.choose (a + b - 4) (b - 2) := by congr 2 <;> omega
      _ = Nat.choose (a + b - 4) (a - 2) :=
        (Nat.choose_symm_of_eq_add hsum).symm
  have hcard' : Nat.choose (b + a - 4) (b - 2) <
      (Finset.range A.card).card := by
    simpa only [Finset.card_range, hchoose] using hcard
  rcases planar_cups_caps p (Finset.range A.card) b a hb ha hpX hpSlope hcard' with
    hcup | hcap
  · obtain ⟨I, hIS, hlen, hcup⟩ := hcup
    let castIndex : Fin b → Fin I.length := fun j =>
      ⟨j.1, by simpa [hlen] using j.2⟩
    let index : Fin b → ℕ := fun j => I.get (castIndex j)
    have hindex_mem (j : Fin b) : index j ∈ Finset.range A.card := by
      apply hIS
      exact List.get_mem I (castIndex j)
    have hindex_strict : StrictMono index := by
      intro j k hjk
      have hget := (polytope_ordered_pairwise_lt hcup.1).rel_get_of_lt
        (show castIndex j < castIndex k by exact hjk)
      simpa [index] using hget
    let c : Fin b → ↥X := fun j => u (index j)
    let q : Fin b → Point 2 := fun j => p (index j)
    have hcA (j : Fin b) : c j ∈ A := by
      exact huA (Finset.mem_range.mp (hindex_mem j))
    have hcinj : Function.Injective c := by
      intro j k hck
      have hj := Finset.mem_range.mp (hindex_mem j)
      have hk := Finset.mem_range.mp (hindex_mem k)
      have heq : e ⟨index j, hj⟩ = e ⟨index k, hk⟩ := by
        apply Subtype.ext
        simpa [c, u, hj, hk] using hck
      have hfin := e.injective heq
      apply hindex_strict.injective
      exact Fin.ext_iff.mp hfin
    have hqinj : Function.Injective q := by
      intro j k hq
      apply hcinj
      apply Subtype.ext
      by_contra hne
      exact (G.planeX_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hne)
        (congrArg planeX hq)
    have hqx : ∀ {j k : Fin b}, j < k → planeX (q j) < planeX (q k) := by
      intro j k hjk
      exact hpX _ (hindex_mem j) _ (hindex_mem k) (hindex_strict hjk)
    let qNat : ℕ → Point 2 := fun j => if hj : j < b then q ⟨j, hj⟩ else 0
    have hqNatX : ∀ j k, j < k → k < b → planeX (qNat j) < planeX (qNat k) := by
      intro j k hjk hkb
      have hjb : j < b := hjk.trans hkb
      simpa [qNat, hjb, hkb] using
        hqx (show (⟨j, hjb⟩ : Fin b) < ⟨k, hkb⟩ by exact hjk)
    have hadj : ∀ j, j + 2 < b →
        0 < planeTurn (qNat j) (qNat (j + 1)) (qNat (j + 2)) := by
      intro j hj
      have hj0 : j < b := by omega
      have hj1 : j + 1 < b := by omega
      have hsraw := polytope_tightPath_get_consecutive hcup.2.2 j (by
        simpa [hlen] using hj)
      have hslope : secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) <
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        simpa [q, index, castIndex] using of_decide_eq_true hsraw
      have hturn := (slope_lt_slope_iff_turn_pos
        (hqx (show (⟨j, hj0⟩ : Fin b) < ⟨j + 1, hj1⟩ by
          change j < j + 1
          omega))
        (hqx (show (⟨j + 1, hj1⟩ : Fin b) < ⟨j + 2, hj⟩ by
          change j + 1 < j + 2
          omega))).1 hslope
      simpa [qNat, hj0, hj1, hj] using hturn
    have hturn : ∀ {j k l : Fin b}, j < k → k < l →
        0 < planeTurn (q j) (q k) (q l) := by
      intro j k l hjk hkl
      have h := adjacent_planeTurn_pos_all qNat b hqNatX hadj
        j.1 k.1 l.1 hjk hkl l.2
      simpa [qNat, j.2, k.2, l.2] using h
    have hconv := fin_convexChain_inConvexPosition hb q hqx hturn
    let C : Finset (↥X) := Finset.univ.image c
    have hCA : C ⊆ A := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hcA j
    have hCcard : C.card = b := by
      change (Finset.univ.image c).card = b
      rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ,
        Fintype.card_fin]
    have hprojectedErase (j : Fin b) :
        G.projection edge ''
            (↑((C.map (Function.Embedding.subtype _)).erase (c j).1) : Set (Point 3)) ⊆
          (↑((Finset.univ.image q).erase (q j)) : Set (Point 2)) := by
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨hyne, hyC⟩ := Finset.mem_erase.mp hy
      obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hyC
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hsC
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image_of_mem q (Finset.mem_univ k)⟩
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hyne rfl
      simpa [q, c, p] using hqinj.ne hkj
    right
    refine ⟨C, hCA, hCcard, ?_⟩
    intro x hx
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsC
    intro hhull
    exact hconv (q j) (Finset.mem_image_of_mem q (Finset.mem_univ j))
      (convexHull_mono (hprojectedErase j) hhull)
  · obtain ⟨I, hIS, hlen, hcap⟩ := hcap
    let castIndex : Fin a → Fin I.length := fun j =>
      ⟨j.1, by simpa [hlen] using j.2⟩
    let index : Fin a → ℕ := fun j => I.get (castIndex j)
    have hindex_mem (j : Fin a) : index j ∈ Finset.range A.card := by
      apply hIS
      exact List.get_mem I (castIndex j)
    have hindex_strict : StrictMono index := by
      intro j k hjk
      have hget := (polytope_ordered_pairwise_lt hcap.1).rel_get_of_lt
        (show castIndex j < castIndex k by exact hjk)
      simpa [index] using hget
    let c : Fin a → ↥X := fun j => u (index j)
    let q : Fin a → Point 2 := fun j => p (index j)
    have hcA (j : Fin a) : c j ∈ A :=
      huA (Finset.mem_range.mp (hindex_mem j))
    have hcinj : Function.Injective c := by
      intro j k hck
      have hj := Finset.mem_range.mp (hindex_mem j)
      have hk := Finset.mem_range.mp (hindex_mem k)
      have heq : e ⟨index j, hj⟩ = e ⟨index k, hk⟩ := by
        apply Subtype.ext
        simpa [c, u, hj, hk] using hck
      have hfin := e.injective heq
      apply hindex_strict.injective
      exact Fin.ext_iff.mp hfin
    have hqinj : Function.Injective q := by
      intro j k hq
      apply hcinj
      apply Subtype.ext
      by_contra hne
      exact (G.planeX_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hne)
        (congrArg planeX hq)
    have hqx : ∀ {j k : Fin a}, j < k → planeX (q j) < planeX (q k) := by
      intro j k hjk
      exact hpX _ (hindex_mem j) _ (hindex_mem k) (hindex_strict hjk)
    have hnotrel {j k : Fin a} (hjk : j ≠ k) :
        ¬ projectionLE T.carrier (G.projection edge) (c j).1 (c k).1 := by
      intro hrel
      have heq := hanti.eq (hcA j) (hcA k) hrel
      exact hjk (hcinj heq)
    have hqy : ∀ {j k : Fin a}, j < k → planeY (q k) < planeY (q j) := by
      intro j k hjk
      have hjk' : j ≠ k := ne_of_lt hjk
      have hpoint : (c j).1 ≠ (c k).1 := by
        intro h
        exact hjk' (hcinj (Subtype.ext h))
      have hyne := G.planeY_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hpoint
      rcases lt_trichotomy (planeY (q j)) (planeY (q k)) with hy | hy | hy
      · exfalso
        apply hnotrel hjk'
        rw [projectionLE, G.image_carrier edge]
        exact mem_convexHull_negativeOrthant_of_both_lt (hqx hjk) hy
      · exact (hyne hy).elim
      · exact hy
    have hantiQ : ∀ {j k : Fin a}, j ≠ k →
        q j ∉ convexHull ℝ (negativeOrthant 2 ∪ {q k}) := by
      intro j k hjk hmem
      apply hnotrel hjk
      rw [projectionLE, G.image_carrier edge]
      exact hmem
    let qNat : ℕ → Point 2 := fun j => if hj : j < a then q ⟨j, hj⟩ else 0
    have hqNatX : ∀ j k, j < k → k < a → planeX (qNat j) < planeX (qNat k) := by
      intro j k hjk hka
      have hja : j < a := hjk.trans hka
      simpa [qNat, hja, hka] using
        hqx (show (⟨j, hja⟩ : Fin a) < ⟨k, hka⟩ by exact hjk)
    have hadj : ∀ j, j + 2 < a →
        planeTurn (qNat j) (qNat (j + 1)) (qNat (j + 2)) < 0 := by
      intro j hj
      have hj0 : j < a := by omega
      have hj1 : j + 1 < a := by omega
      have hsraw := polytope_tightPath_get_consecutive hcap.2.2.1 j (by
        simpa [hlen] using hj)
      have hnotSlope : ¬ secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) <
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        simpa [q, index, castIndex] using of_decide_eq_false hsraw
      have hneSlope : secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) ≠
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        apply hcap.2.2.2
        · exact List.get_mem I (castIndex ⟨j, hj0⟩)
        · exact List.get_mem I (castIndex ⟨j + 1, hj1⟩)
        · exact List.get_mem I (castIndex ⟨j + 2, hj⟩)
        · exact hindex_strict (show (⟨j, hj0⟩ : Fin a) < ⟨j + 1, hj1⟩ by
            change j < j + 1
            omega)
        · exact hindex_strict (show (⟨j + 1, hj1⟩ : Fin a) < ⟨j + 2, hj⟩ by
            change j + 1 < j + 2
            omega)
      have hslope : secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) <
          secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) :=
        lt_of_le_of_ne (le_of_not_gt hnotSlope) hneSlope.symm
      have hturn := (slope_gt_slope_iff_turn_neg
        (hqx (show (⟨j, hj0⟩ : Fin a) < ⟨j + 1, hj1⟩ by
          change j < j + 1
          omega))
        (hqx (show (⟨j + 1, hj1⟩ : Fin a) < ⟨j + 2, hj⟩ by
          change j + 1 < j + 2
          omega))).1 hslope
      simpa [qNat, hj0, hj1, hj] using hturn
    have hturn : ∀ {j k l : Fin a}, j < k → k < l →
        planeTurn (q j) (q k) (q l) < 0 := by
      intro j k l hjk hkl
      have h := adjacent_planeTurn_neg_all qNat a hqNatX hadj
        j.1 k.1 l.1 hjk hkl l.2
      simpa [qNat, j.2, k.2, l.2] using h
    have hnegcap := fin_concaveChain_negativeOrthantCap ha q hqx hqy hturn hantiQ
    let C : Finset (↥X) := Finset.univ.image c
    have hCA : C ⊆ A := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hcA j
    have hCcard : C.card = a := by
      change (Finset.univ.image c).card = a
      rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ,
        Fintype.card_fin]
    have hprojectedErase (j : Fin a) :
        G.projection edge ''
            (↑((C.map (Function.Embedding.subtype _)).erase (c j).1) : Set (Point 3)) ⊆
          (↑((Finset.univ.image q).erase (q j)) : Set (Point 2)) := by
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨hyne, hyC⟩ := Finset.mem_erase.mp hy
      obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hyC
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hsC
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image_of_mem q (Finset.mem_univ k)⟩
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hyne rfl
      simpa [q, c, p] using hqinj.ne hkj
    left
    refine ⟨C, hCA, hCcard, ?_⟩
    intro x hx
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsC
    intro hhull
    apply hnegcap j
    apply convexHull_mono ?_ hhull
    intro z hz
    rcases hz with hzP | hzC
    · left
      rw [← G.image_carrier edge]
      exact hzP
    · exact Or.inr (hprojectedErase j hzC)

/-- Pohoata--Zakharov, Proposition 2.1, in projection-certificate form.
The cardinal threshold and its exponent are exactly those in the paper. -/
theorem pohoata_zakharov_prop_two_one
    {P : Set (Point 3)} {X : Finset (Point 3)} {ι : Type*}
    [Fintype ι]
    (cert : ProjectionOrderCertificate P X ι)
    (hfree : PFree P X) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) ^ Fintype.card ι < X.card) :
    (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = a ∧ PCap P C) ∨
      (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = b ∧
        InConvexPosition C) := by
  classical
  let m := Nat.choose (a + b - 4) (a - 2)
  have hindex : a - 2 ≤ a + b - 4 := by omega
  have hm : 0 < m := Nat.choose_pos hindex
  let D : MultiOrderDilworthData (↑X) ι :=
    { rel := fun i x y => projectionLE P (cert.projection i) x.1 y.1
      preorder := fun i =>
        { refl := fun x => (projectionLE_isPreorder P (cert.projection i)).refl x.1
          trans := fun x y z hxy hyz =>
            (projectionLE_isPreorder P (cert.projection i)).trans
              x.1 y.1 z.1 hxy hyz }
      separated := cert.separated hfree }
  have hcard' : m ^ Fintype.card ι < Fintype.card (↑X) := by
    simpa [m] using hcard
  obtain ⟨i, A, hAanti, hAcard⟩ := D.exists_large_antichain hm hcard'
  rcases cert.planar_dichotomy i A a b ha hb hAanti hAcard with hcap | hconv
  · left
    obtain ⟨C, hCA, hCa, hCcap⟩ := hcap
    refine ⟨C.map (Function.Embedding.subtype _), ?_, ?_, hCcap.pcap⟩
    · intro x hx
      simp only [Finset.mem_map] at hx
      obtain ⟨y, hyC, rfl⟩ := hx
      exact y.2
    · simpa using hCa
  · right
    obtain ⟨C, hCA, hCb, hCconv⟩ := hconv
    refine ⟨C.map (Function.Embedding.subtype _), ?_, ?_, hCconv.inConvexPosition⟩
    · intro x hx
      simp only [Finset.mem_map] at hx
      obtain ⟨y, hyC, rfl⟩ := hx
      exact y.2
    · simpa using hCb

/-- A convenient padded form of the at-most-three-edge specialization,
with the edge directions indexed by `Fin 3`. -/
theorem pohoata_zakharov_prop_two_one_three_edges
    {P : Set (Point 3)} {X : Finset (Point 3)}
    (cert : ProjectionOrderCertificate P X (Fin 3))
    (hfree : PFree P X) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) ^ 3 < X.card) :
    (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = a ∧ PCap P C) ∨
      (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = b ∧
        InConvexPosition C) := by
  apply pohoata_zakharov_prop_two_one cert hfree ha hb
  simpa using hcard

end

end

/-! ### Upstream module `JSP527/External/Erdos651/CapAssembly.lean` -/

/-!
# Assembling polytope caps

The final combinatorial step of Pohoata--Zakharov chooses several caps, one
inside each of several clusters.  For the cap in cluster `i`, the auxiliary
polyhedron contains every other chosen cluster.  Its defining exposed-point
condition therefore exposes the same point in the union of all the caps.
-/

noncomputable section

/-- Caps relative to polyhedra which contain all the other caps assemble to a
set in convex position.  No disjointness hypothesis is needed: membership in
more than one cap only makes the point fall under the `i = j` branch as well. -/
theorem inConvexPosition_biUnion_of_pCaps {q : ℕ}
    (P : Fin q → Set (Point 3)) (K : Fin q → Finset (Point 3))
    (hcap : ∀ i, PCap (P i) (K i))
    (hothers : ∀ i j, i ≠ j → (↑(K j) : Set (Point 3)) ⊆ P i) :
    InConvexPosition (Finset.univ.biUnion K) := by
  classical
  intro x hxU hxHull
  obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hxU
  apply (hcap i).2 x hxi
  apply convexHull_mono (s := (↑((Finset.univ.biUnion K).erase x) : Set (Point 3)))
  · intro y hy
    have hyU : y ∈ Finset.univ.biUnion K := Finset.mem_of_mem_erase hy
    obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hyU
    by_cases hij : i = j
    · right
      subst j
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hy, hyj⟩
    · left
      exact hothers i j hij hyj
  · exact hxHull

/-- The same assembly lemma with an explicit ambient-cardinality conclusion.
This is the form used after choosing equal-sized caps. -/
theorem containsConvexSubset_of_biUnion_pCaps {q n : ℕ}
    (P : Fin q → Set (Point 3)) (K : Fin q → Finset (Point 3))
    (hcap : ∀ i, PCap (P i) (K i))
    (hothers : ∀ i j, i ≠ j → (↑(K j) : Set (Point 3)) ⊆ P i)
    (hcard : n ≤ (Finset.univ.biUnion K).card) :
    ContainsConvexSubset 3 n (Finset.univ.biUnion K) := by
  let U := Finset.univ.biUnion K
  have hU : InConvexPosition U := inConvexPosition_biUnion_of_pCaps P K hcap hothers
  obtain ⟨Y, hYU, hYcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨Y, hYU, hYcard, ?_⟩
  intro x hxY hxHull
  apply hU x (hYU hxY)
  exact convexHull_mono (by
    intro y hy
    exact Finset.erase_subset_erase x hYU hy) hxHull

end

/-! ### Upstream module `JSP527/External/Erdos651/FiniteRamsey.lean` -/

/-!
# Finite uniform hypergraph Ramsey selection

This file proves the finite two-colour Ramsey theorem for uniform hypergraphs.  The proof is the
usual induction on the uniformity.  At the successor step we repeatedly choose a new vertex and
apply the theorem in one lower uniformity to make the colour seen from that vertex constant on a
large reservoir.  Among twice as many canonized vertices as are needed, one of the two colours
occurs often enough.
-/

/-- `H` is monochromatic for `c` on its `r`-element subsets. -/
def MonochromaticOn {α : Type*} [DecidableEq α]
    (r : ℕ) (c : Finset α → Bool) (H : Finset α) : Prop :=
  ∃ b : Bool, ∀ A : Finset α, A ⊆ H → A.card = r → c A = b

/-- An explicit (very large) finite two-colour uniform Ramsey bound. -/
def uniformRamseyBound : ℕ → ℕ → ℕ
  | 0, m => m
  | r + 1, m => (fun t => 1 + uniformRamseyBound r t)^[2 * m] 0
termination_by r _ => r

/-- The number of vertices required to construct a canonized chain of length `q`, assuming the
Ramsey theorem in uniformity `r`. -/
private def canonicalBound (r q : ℕ) : ℕ :=
  (fun t => 1 + uniformRamseyBound r t)^[q] 0

private lemma canonicalBound_succ (r q : ℕ) :
    canonicalBound r (q + 1) = 1 + uniformRamseyBound r (canonicalBound r q) := by
  simp [canonicalBound, Function.iterate_succ_apply']

/-- A chain whose vertex `x` is labelled by the common colour of all edges consisting of `x` and
`r` later vertices.  Storing the label beside the vertex makes the final pigeonhole step clean. -/
private def IsCanonicalChain {α : Type*} [DecidableEq α]
    (r : ℕ) (c : Finset α → Bool) : List (α × Bool) → Prop
  | [] => True
  | (x, b) :: ps =>
      x ∉ ps.map Prod.fst ∧ IsCanonicalChain r c ps ∧
        ∀ A : Finset α, A ⊆ (ps.map Prod.fst).toFinset → A.card = r →
          c (insert x A) = b

private lemma IsCanonicalChain.fst_nodup {α : Type*} [DecidableEq α]
    {r : ℕ} {c : Finset α → Bool} {ps : List (α × Bool)}
    (h : IsCanonicalChain r c ps) : (ps.map Prod.fst).Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨x, b⟩
      simp only [IsCanonicalChain] at h
      simpa using List.nodup_cons.mpr ⟨h.1, ih h.2.1⟩

private lemma IsCanonicalChain.filter_snd {α : Type*} [DecidableEq α]
    {r : ℕ} {c : Finset α → Bool} {ps : List (α × Bool)}
    (h : IsCanonicalChain r c ps) (b : Bool) :
    IsCanonicalChain r c (ps.filter fun p => decide (p.2 = b)) := by
  induction ps with
  | nil => simp [IsCanonicalChain]
  | cons p ps ih =>
      rcases p with ⟨x, d⟩
      simp only [IsCanonicalChain] at h
      by_cases hdb : d = b
      · subst d
        simp only [List.filter_cons, decide_true, if_true, IsCanonicalChain]
        refine ⟨?_, ih h.2.1, ?_⟩
        · intro hx
          apply h.1
          simp only [List.mem_map] at hx ⊢
          obtain ⟨p, hp, rfl⟩ := hx
          exact ⟨p, List.mem_of_mem_filter hp, rfl⟩
        · intro A hA hcard
          exact h.2.2 A (hA.trans (by
            intro y hy
            simp only [List.mem_toFinset, List.mem_map] at hy ⊢
            obtain ⟨p, hp, rfl⟩ := hy
            exact ⟨p, List.mem_of_mem_filter hp, rfl⟩)) hcard
      · simp only [List.filter_cons, hdb, decide_false, Bool.false_eq]
        exact ih h.2.1

private lemma IsCanonicalChain.monochromatic_of_constant_snd
    {α : Type*} [DecidableEq α] {r : ℕ} {c : Finset α → Bool}
    {ps : List (α × Bool)} (h : IsCanonicalChain r c ps) (b : Bool)
    (hb : ∀ p ∈ ps, p.2 = b) :
    ∀ A : Finset α, A ⊆ (ps.map Prod.fst).toFinset → A.card = r + 1 → c A = b := by
  induction ps with
  | nil =>
      intro A hA hcard
      have : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
      subst A
      simp at hcard
  | cons p ps ih =>
      rcases p with ⟨x, d⟩
      simp only [IsCanonicalChain] at h
      intro A hA hcard
      have hd : d = b := hb (x, d) (by simp)
      by_cases hx : x ∈ A
      · have herase : A.erase x ⊆ (ps.map Prod.fst).toFinset := by
          intro y hy
          have hyA : y ∈ A := Finset.mem_of_mem_erase hy
          have hy' := hA hyA
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hy'
          rcases hy' with rfl | hy'
          · exact False.elim ((Finset.ne_of_mem_erase hy) rfl)
          · exact hy'
        have hcardErase : (A.erase x).card = r := by
          rw [Finset.card_erase_of_mem hx]
          omega
        have hc := h.2.2 (A.erase x) herase hcardErase
        rw [Finset.insert_erase hx] at hc
        exact hc.trans hd
      · apply ih h.2.1 (fun p hp => hb p (by simp [hp])) A ?_ hcard
        intro y hy
        have hy' := hA hy
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hy'
        exact hy'.resolve_left (fun hxy => hx (hxy ▸ hy))

/-- The explicit bound has the required two-colour uniform Ramsey property, on an arbitrary finite
ambient set. -/
theorem uniformRamseyBound_spec (r m : ℕ) {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : uniformRamseyBound r m ≤ X.card)
    (c : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn r c H := by
  induction r generalizing m α with
  | zero =>
      obtain ⟨H, hHX, hcard⟩ := Finset.exists_subset_card_eq hX
      have hcard' : H.card = m := by simpa [uniformRamseyBound] using hcard
      refine ⟨H, hHX, hcard', c ∅, ?_⟩
      intro A _ hA
      simpa [Finset.card_eq_zero.mp hA]
  | succ r ihr =>
      have chain : ∀ (q : ℕ) (Y : Finset α),
          canonicalBound r q ≤ Y.card → (d : Finset α → Bool) →
          ∃ ps : List (α × Bool), ps.length = q ∧ IsCanonicalChain r d ps ∧
            ∀ p ∈ ps, p.1 ∈ Y := by
        intro q
        induction q with
        | zero =>
            intro Y _ d
            exact ⟨[], rfl, trivial, by simp⟩
        | succ q ihq =>
            intro Y hY d
            rw [canonicalBound_succ] at hY
            have hYpos : 0 < Y.card := by omega
            obtain ⟨x, hxY⟩ := Finset.card_pos.mp hYpos
            let Z := Y.erase x
            have hZ : uniformRamseyBound r (canonicalBound r q) ≤ Z.card := by
              dsimp [Z]
              rw [Finset.card_erase_of_mem hxY]
              omega
            obtain ⟨K, hKZ, hKcard, hKmono⟩ :=
              ihr (canonicalBound r q) Z hZ (fun A => d (insert x A))
            rcases hKmono with ⟨b, hb⟩
            obtain ⟨ps, hpslen, hpscan, hpsK⟩ :=
              ihq K (by simpa [hKcard]) d
            refine ⟨(x, b) :: ps, by simp [hpslen], ?_, ?_⟩
            · simp only [IsCanonicalChain]
              refine ⟨?_, hpscan, ?_⟩
              · intro hx
                simp only [List.mem_map] at hx
                obtain ⟨p, hp, hp1⟩ := hx
                have hpxK : p.1 ∈ K := hpsK p hp
                have hpxZ : p.1 ∈ Z := hKZ hpxK
                have hne : p.1 ≠ x := by
                  exact (Finset.mem_erase.mp hpxZ).1
                exact hne hp1
              · intro A hA hcard
                apply hb A ?_ hcard
                intro y hy
                have : y ∈ (ps.map Prod.fst).toFinset := hA hy
                simp only [List.mem_toFinset, List.mem_map] at this
                obtain ⟨p, hp, rfl⟩ := this
                exact hpsK p hp
            · intro p hp
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hp
              · exact hxY
              · exact (Finset.mem_erase.mp (hKZ (hpsK p hp))).2
      have hbound : canonicalBound r (2 * m) ≤ X.card := by
        simpa [uniformRamseyBound, canonicalBound] using hX
      obtain ⟨ps, hpslen, hpscan, hpsX⟩ := chain (2 * m) X hbound c
      have htrue_or_false :
          m ≤ (ps.filter fun p => p.2).length ∨
            m ≤ (ps.filter fun p => !p.2).length := by
        have hpartition := ps.length_eq_length_filter_add (fun p => p.2)
        rw [hpslen] at hpartition
        omega
      rcases htrue_or_false with hmany | hmany
      · let qs := ps.filter fun p => p.2
        have hqscan : IsCanonicalChain r c qs := by
          simpa [qs] using hpscan.filter_snd true
        have hqsnd : ∀ p ∈ qs, p.2 = true := by
          intro p hp
          change p ∈ ps.filter (fun p => p.2) at hp
          exact (List.mem_filter.mp hp).2
        have hqnodup := hqscan.fst_nodup
        have hqcard : (qs.map Prod.fst).toFinset.card = qs.length := by
          rw [List.toFinset_card_of_nodup hqnodup]
          simp
        have hmq : m ≤ (qs.map Prod.fst).toFinset.card := by
          rw [hqcard]
          simpa [qs] using hmany
        obtain ⟨H, hHq, hHcard⟩ := Finset.exists_subset_card_eq hmq
        refine ⟨H, ?_, hHcard, true, ?_⟩
        · intro x hx
          have hxq : x ∈ (qs.map Prod.fst).toFinset := hHq hx
          simp only [List.mem_toFinset, List.mem_map] at hxq
          obtain ⟨p, hpq, rfl⟩ := hxq
          apply hpsX p
          change p ∈ ps.filter (fun p => p.2) at hpq
          exact (List.mem_filter.mp hpq).1
        · intro A hAH hAcard
          exact hqscan.monochromatic_of_constant_snd true hqsnd A (hAH.trans hHq) hAcard
      · let qs := ps.filter fun p => !p.2
        have hqscan : IsCanonicalChain r c qs := by
          simpa [qs] using hpscan.filter_snd false
        have hqsnd : ∀ p ∈ qs, p.2 = false := by
          intro p hp
          change p ∈ ps.filter (fun p => !p.2) at hp
          have hp' := (List.mem_filter.mp hp).2
          simpa using hp'
        have hqnodup := hqscan.fst_nodup
        have hqcard : (qs.map Prod.fst).toFinset.card = qs.length := by
          rw [List.toFinset_card_of_nodup hqnodup]
          simp
        have hmq : m ≤ (qs.map Prod.fst).toFinset.card := by
          rw [hqcard]
          simpa [qs] using hmany
        obtain ⟨H, hHq, hHcard⟩ := Finset.exists_subset_card_eq hmq
        refine ⟨H, ?_, hHcard, false, ?_⟩
        · intro x hx
          have hxq : x ∈ (qs.map Prod.fst).toFinset := hHq hx
          simp only [List.mem_toFinset, List.mem_map] at hxq
          obtain ⟨p, hpq, rfl⟩ := hxq
          apply hpsX p
          change p ∈ ps.filter (fun p => !p.2) at hpq
          exact (List.mem_filter.mp hpq).1
        · intro A hAH hAcard
          exact hqscan.monochromatic_of_constant_snd false hqsnd A (hAH.trans hHq) hAcard

/-- A Ramsey threshold sequence that is pointwise at least the requested clique size. -/
def uniformRamseySequence (r m : ℕ) : ℕ := uniformRamseyBound r m + m

/-- Selection at the unbounded Ramsey threshold sequence. -/
theorem uniformRamseySequence_spec (r m : ℕ) {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : uniformRamseySequence r m ≤ X.card)
    (c : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn r c H := by
  apply uniformRamseyBound_spec r m X ?_ c
  exact (Nat.le_add_right _ _).trans hX

/-! ### Upstream module `JSP527/External/Erdos651/CapRamsey.lean` -/

/-!
# The second Dilworth--Ramsey--cap step of Pohoata--Zakharov

This file contains the finite combinatorial part of Section 3 of the
Pohoata--Zakharov proof.  The geometric construction preceding this step
associates two polyhedra `P₁, P₂` to every triple of cluster indices and
proves two implications on the middle cluster:

* an antichain for `x ∈ conv({y} ∪ P₁)` is `P₁`-free;
* a chain for the same relation is `P₂`-free.

Those are recorded as fields of `MiddleTripleGadget`; everything else in
this file is derived.  In particular, finite Dilworth gives a free subset
of cardinality at least the integer square root, triple Ramsey makes the
choice of `P₁` or `P₂` uniform, Proposition 2.1 extracts caps, and the cap
assembly lemma gives the final convex set.
-/

noncomputable section

/-! ## The source preorder and its square-root dichotomy -/

/-- Relation (4.9) in the source: `x ≼[P] y` means that `x` belongs to
the convex hull of `y` together with the background polyhedron `P`. -/
def sourcePolytopeLE (P : Set (Point 3)) (x y : Point 3) : Prop :=
  x ∈ convexHull ℝ ({y} ∪ P)

/-- The relation in (4.9) is reflexive and transitive.  Antisymmetry is not
needed: finite Dilworth is available for preorders via antisymmetrization. -/
theorem sourcePolytopeLE_isPreorder (P : Set (Point 3)) :
    IsPreorder (Point 3) (sourcePolytopeLE P) := by
  let hr : Std.Refl (sourcePolytopeLE P) := ⟨by
    intro x
    exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton x))⟩
  let ht : IsTrans (Point 3) (sourcePolytopeLE P) := ⟨by
    intro x y z hxy hyz
    apply convexHull_min ?_ (convex_convexHull ℝ _) hxy
    intro w hw
    rcases hw with rfl | hw
    · exact hyz
    · exact subset_convexHull ℝ _ (Or.inr hw)⟩
  exact @IsPreorder.mk _ _ hr ht

/-- Every two members of `A` are comparable under `r`.  Reflexivity makes
this formulation equivalent to the usual finite-chain predicate, and it is
convenient for fibers of a Dilworth chain coloring. -/
def PairwiseComparable {α : Type*} (r : α → α → Prop)
    (A : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → r x y ∨ r y x

/-- The elementary width-height consequence of finite Dilworth.  A finite
preorder has a chain or antichain containing at least `⌊√|X|⌋` elements. -/
theorem exists_sqrt_chain_or_antichain
    {α : Type*} [DecidableEq α] (X : Finset α)
    (r : α → α → Prop) (hr : IsPreorder α r) :
    ∃ A : Finset α, A ⊆ X ∧ Nat.sqrt X.card ≤ A.card ∧
      (IsAntichain r (↑A : Set α) ∨ PairwiseComparable r A) := by
  classical
  let s := Nat.sqrt X.card
  by_cases hs : s = 0
  · refine ⟨∅, Finset.empty_subset _, by simpa using hs, Or.inl ?_⟩
    simp
  let αX := ↑X
  let rX : αX → αX → Prop := fun x y => r x.1 y.1
  have hrX : IsPreorder αX rX :=
    { refl := fun x => hr.refl x.1
      trans := fun _ _ _ hxy hyz => hr.trans _ _ _ hxy hyz }
  by_cases hwide : ∃ A : Finset αX,
      IsAntichain rX (↑A : Set αX) ∧ s ≤ A.card
  · obtain ⟨A, hAanti, hAs⟩ := hwide
    let B := A.map (Function.Embedding.subtype _)
    refine ⟨B, ?_, ?_, Or.inl ?_⟩
    · intro x hx
      simp only [B, Finset.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · simpa [B] using hAs
    · intro x hx y hy hxy hrel
      simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨x', hx'A, rfl⟩ := hx
      obtain ⟨y', hy'A, hy'eq⟩ := hy
      subst y
      exact hAanti hx'A hy'A (fun h => hxy (congrArg Subtype.val h)) hrel
  · push_neg at hwide
    have hspos : 0 < s := Nat.pos_of_ne_zero hs
    letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.1 hspos
    obtain ⟨color, hcolor⟩ :=
      finite_dilworth_of_isPreorder rX hrX s hspos (by
        intro A hA
        exact (hwide A hA).le)
    have hsq : s * s ≤ Fintype.card αX := by
      simpa [s, αX] using Nat.sqrt_le X.card
    obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
      (f := color) (n := s) (by simpa using hsq)
    let A : Finset αX := Finset.univ.filter fun x => color x = c
    have hAcard : s ≤ A.card := by
      simpa [A] using hc
    let B := A.map (Function.Embedding.subtype _)
    refine ⟨B, ?_, by simpa [B] using hAcard, Or.inr ?_⟩
    · intro x hx
      simp only [B, Finset.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · intro x hx y hy
      simp only [B, Finset.mem_map] at hx hy
      obtain ⟨x', hx'A, rfl⟩ := hx
      obtain ⟨y', hy'A, hy'eq⟩ := hy
      subst y
      apply hcolor
      have hxc : color x' = c := (Finset.mem_filter.mp hx'A).2
      have hyc : color y' = c := (Finset.mem_filter.mp hy'A).2
      exact hxc.trans hyc.symm

/-- Exact (non-rounded) width-height form: the selected chain or antichain
has cardinality whose square is at least the cardinality of the ambient
finite set. -/
theorem exists_chain_or_antichain_card_le_square
    {α : Type*} [DecidableEq α] (X : Finset α)
    (r : α → α → Prop) (hr : IsPreorder α r) :
    ∃ A : Finset α, A ⊆ X ∧ X.card ≤ A.card * A.card ∧
      (IsAntichain r (↑A : Set α) ∨ PairwiseComparable r A) := by
  classical
  let s := Nat.sqrt X.card
  by_cases hsquare : s * s = X.card
  · obtain ⟨A, hAX, hAs, hA⟩ := exists_sqrt_chain_or_antichain X r hr
    refine ⟨A, hAX, ?_, hA⟩
    calc
      X.card = s * s := hsquare.symm
      _ ≤ A.card * A.card := Nat.mul_le_mul hAs hAs
  · have hsle : s * s ≤ X.card := by
      simpa [s] using Nat.sqrt_le X.card
    have hss : s * s < X.card := lt_of_le_of_ne hsle hsquare
    have hspos : 0 < s := by
      simp only [s, Nat.sqrt_pos]
      omega
    let αX := ↑X
    let rX : αX → αX → Prop := fun x y => r x.1 y.1
    have hrX : IsPreorder αX rX :=
      { refl := fun x => hr.refl x.1
        trans := fun _ _ _ hxy hyz => hr.trans _ _ _ hxy hyz }
    by_cases hwide : ∃ A : Finset αX,
        IsAntichain rX (↑A : Set αX) ∧ s < A.card
    · obtain ⟨A, hAanti, hAs⟩ := hwide
      let B := A.map (Function.Embedding.subtype _)
      refine ⟨B, ?_, ?_, Or.inl ?_⟩
      · intro x hx
        simp only [B, Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2
      · have hsucc : s + 1 ≤ A.card := by omega
        have hroot : X.card < (s + 1) * (s + 1) := by
          simpa [s] using Nat.lt_succ_sqrt X.card
        calc
          X.card ≤ (s + 1) * (s + 1) := hroot.le
          _ ≤ A.card * A.card := Nat.mul_le_mul hsucc hsucc
          _ = B.card * B.card := by simp [B]
      · intro x hx y hy hxy hrel
        simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
        obtain ⟨x', hx'A, rfl⟩ := hx
        obtain ⟨y', hy'A, hy'eq⟩ := hy
        subst y
        exact hAanti hx'A hy'A (fun h => hxy (congrArg Subtype.val h)) hrel
    · push_neg at hwide
      letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.1 hspos
      obtain ⟨color, hcolor⟩ :=
        finite_dilworth_of_isPreorder rX hrX s hspos hwide
      obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
        (f := color) (n := s) (by simpa [αX] using hss)
      let A : Finset αX := Finset.univ.filter fun x => color x = c
      have hAs : s < A.card := by
        simpa [A] using hc
      let B := A.map (Function.Embedding.subtype _)
      refine ⟨B, ?_, ?_, Or.inr ?_⟩
      · intro x hx
        simp only [B, Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2
      · have hsucc : s + 1 ≤ A.card := by omega
        have hroot : X.card < (s + 1) * (s + 1) := by
          simpa [s] using Nat.lt_succ_sqrt X.card
        calc
          X.card ≤ (s + 1) * (s + 1) := hroot.le
          _ ≤ A.card * A.card := Nat.mul_le_mul hsucc hsucc
          _ = B.card * B.card := by simp [B]
      · intro x hx y hy
        simp only [B, Finset.mem_map] at hx hy
        obtain ⟨x', hx'A, rfl⟩ := hx
        obtain ⟨y', hy'A, hy'eq⟩ := hy
        subst y
        apply hcolor
        have hxc : color x' = c := (Finset.mem_filter.mp hx'A).2
        have hyc : color y' = c := (Finset.mem_filter.mp hy'A).2
        exact hxc.trans hyc.symm

/-! ## A triple gadget and the induced Ramsey color -/

/-- The precise geometric output needed from the three-polytope construction
for one triple of cluster indices.  The two fields ending in `_free` are the
line-separation statements proved by the geometry; the square-root loss and
all subsequent selections are not assumptions. -/
structure MiddleTripleGadget where
  middle : Finset (Point 3)
  firstPolytope : Set (Point 3)
  secondPolytope : Set (Point 3)
  antichain_first_free : ∀ A : Finset (Point 3), A ⊆ middle →
    IsAntichain (sourcePolytopeLE firstPolytope) (↑A : Set (Point 3)) →
      PFree firstPolytope A
  chain_second_free : ∀ A : Finset (Point 3), A ⊆ middle →
    PairwiseComparable (sourcePolytopeLE firstPolytope) A →
      PFree secondPolytope A

/-- A convenient adapter from the two line implications established by the
three-convex-set geometry.  The first implication says that any line meeting
`P₁` makes its two middle points comparable; the second says that comparable
middle points span a line missing `P₂`. -/
def MiddleTripleGadget.ofLineSeparation
    (middle : Finset (Point 3))
    (P₁ P₂ : Set (Point 3))
    (hmiddle_first : Disjoint (↑middle : Set (Point 3)) P₁)
    (hmiddle_second : Disjoint (↑middle : Set (Point 3)) P₂)
    (hfirst : ∀ ⦃x⦄, x ∈ middle → ∀ ⦃y⦄, y ∈ middle → x ≠ y →
      ¬ Disjoint (lineThrough x y) P₁ →
        sourcePolytopeLE P₁ x y ∨ sourcePolytopeLE P₁ y x)
    (hsecond : ∀ ⦃x⦄, x ∈ middle → ∀ ⦃y⦄, y ∈ middle → x ≠ y →
      (sourcePolytopeLE P₁ x y ∨ sourcePolytopeLE P₁ y x) →
        Disjoint (lineThrough x y) P₂) :
    MiddleTripleGadget where
  middle := middle
  firstPolytope := P₁
  secondPolytope := P₂
  antichain_first_free := by
    intro A hAmiddle hAanti
    refine ⟨hmiddle_first.mono ?_ (fun _ h => h), ?_⟩
    · intro x hx
      exact hAmiddle hx
    · intro x hxA y hyA hxy
      by_contra hline
      rcases hfirst (hAmiddle hxA) (hAmiddle hyA) hxy hline with hrel | hrel
      · exact hAanti hxA hyA hxy hrel
      · exact hAanti hyA hxA hxy.symm hrel
  chain_second_free := by
    intro A hAmiddle hAchain
    refine ⟨hmiddle_second.mono ?_ (fun _ h => h), ?_⟩
    · intro x hx
      exact hAmiddle hx
    · intro x hxA y hyA hxy
      exact hsecond (hAmiddle hxA) (hAmiddle hyA) hxy (hAchain hxA hyA)

/-- A gadget always supplies a square-root-sized free set for one of its
two background polyhedra, in the exact integer form `|middle| ≤ |Z|²`. -/
theorem MiddleTripleGadget.exists_large_free_subset_exact (G : MiddleTripleGadget) :
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z) ∨
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.secondPolytope Z) := by
  obtain ⟨A, hAmid, hAcard, hAanti | hAchain⟩ :=
    exists_chain_or_antichain_card_le_square G.middle
      (sourcePolytopeLE G.firstPolytope)
      (sourcePolytopeLE_isPreorder G.firstPolytope)
  · exact Or.inl ⟨A, hAmid, hAcard, G.antichain_first_free A hAmid hAanti⟩
  · exact Or.inr ⟨A, hAmid, hAcard, G.chain_second_free A hAmid hAchain⟩

/-- Red (`true`) means that the first-polytope alternative exists. -/
noncomputable def MiddleTripleGadget.color (G : MiddleTripleGadget) : Bool := by
  classical
  exact decide (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
    G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z)

/-- The Ramsey color records a genuine free-set choice, with the exact
quadratic cardinality bound. -/
theorem MiddleTripleGadget.color_spec_exact (G : MiddleTripleGadget) :
    ∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧
      PFree (if G.color then G.firstPolytope else G.secondPolytope) Z := by
  classical
  by_cases h : ∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z
  · obtain ⟨Z, hZ⟩ := id h
    refine ⟨Z, hZ.1, hZ.2.1, ?_⟩
    simpa [MiddleTripleGadget.color, h] using hZ.2.2
  · rcases G.exists_large_free_subset_exact with hfirst | hsecond
    · exact (h hfirst).elim
    · obtain ⟨Z, hZ⟩ := hsecond
      refine ⟨Z, hZ.1, hZ.2.1, ?_⟩
      simpa [MiddleTripleGadget.color, h] using hZ.2.2

/-- A family assigning geometric data only to genuine triples. -/
abbrev TripleGadgetFamily (ι : Type*) [DecidableEq ι] :=
  ∀ J : Finset ι, J.card = 3 → MiddleTripleGadget

/-! ## The alternating triples in an odd monochromatic clique -/

/-- Position immediately before the selected middle position. -/
def alternatingLeftPosition {q : ℕ} (r : Fin q) : Fin (2 * q + 1) :=
  ⟨2 * r.1, by omega⟩

/-- The selected even cluster in the source's one-based numbering (an odd
position in Lean's zero-based indexing). -/
def alternatingMiddlePosition {q : ℕ} (r : Fin q) : Fin (2 * q + 1) :=
  ⟨2 * r.1 + 1, by omega⟩

/-- The common final member of all alternating triples. -/
def alternatingLastPosition (q : ℕ) : Fin (2 * q + 1) :=
  ⟨2 * q, by omega⟩

/-- The triple consisting of a consecutive left/middle pair and the last
point of an odd clique. -/
def alternatingTriple {q : ℕ} {ι : Type*} [DecidableEq ι]
    (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) : Finset ι :=
  {j (alternatingLeftPosition r), j (alternatingMiddlePosition r),
    j (alternatingLastPosition q)}

theorem alternatingTriple_card {q : ℕ} {ι : Type*} [DecidableEq ι]
    (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) :
    (alternatingTriple j r).card = 3 := by
  have hlm : j (alternatingLeftPosition r) ≠ j (alternatingMiddlePosition r) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 = 2 * r.1 + 1 at hv
    omega
  have hll : j (alternatingLeftPosition r) ≠ j (alternatingLastPosition q) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 = 2 * q at hv
    omega
  have hml : j (alternatingMiddlePosition r) ≠ j (alternatingLastPosition q) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 + 1 = 2 * q at hv
    omega
  simp [alternatingTriple, hlm, hll, hml]

/-- The gadget belonging to one of the canonical alternating triples. -/
def alternatingGadget {q : ℕ} {ι : Type*} [DecidableEq ι]
    (G : TripleGadgetFamily ι) (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) :
    MiddleTripleGadget :=
  G (alternatingTriple j r) (alternatingTriple_card j r)

/-- A monochromatic odd clique supplies a free set on every alternating
middle cluster, with the same choice of background polyhedron. -/
theorem exists_alternating_free_subsets_of_monochromatic_clique
    {q : ℕ} {ι : Type*} [DecidableEq ι]
    (G : TripleGadgetFamily ι)
    (H : Finset ι) (j : Fin (2 * q + 1) ↪ ι)
    (hjH : ∀ p, j p ∈ H) (b : Bool)
    (hmono : ∀ J : Finset ι, J ⊆ H → ∀ hJ : J.card = 3,
      (G J hJ).color = b) :
    ∀ r : Fin q, ∃ Z : Finset (Point 3),
      Z ⊆ (alternatingGadget G j r).middle ∧
      (alternatingGadget G j r).middle.card ≤ Z.card * Z.card ∧
      PFree
        (if b then (alternatingGadget G j r).firstPolytope
          else (alternatingGadget G j r).secondPolytope) Z := by
  intro r
  have hJH : alternatingTriple j r ⊆ H := by
    intro x hx
    simp only [alternatingTriple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hjH _
    · exact hjH _
    · exact hjH _
  obtain ⟨Z, hZmid, hZcard, hZfree⟩ :=
    (alternatingGadget G j r).color_spec_exact
  refine ⟨Z, hZmid, hZcard, ?_⟩
  have hb : (alternatingGadget G j r).color = b :=
    hmono _ hJH (alternatingTriple_card j r)
  rw [hb] at hZfree
  exact hZfree

/-! ## Proposition 2.1 on alternating clusters and cap assembly -/

/-- Inputs retained after the monochromatic triple-clique step.  Each
`freeSet i` lies in a distinct middle cluster, is free from its selected
background polyhedron, and comes with the unconditional three-edge
projection certificate of Proposition 2.1.  The containment field is (4.8). -/
structure AlternatingFreeFamily (q : ℕ) (X : Finset (Point 3)) where
  middle : Fin q → Finset (Point 3)
  background : Fin q → Set (Point 3)
  freeSet : Fin q → Finset (Point 3)
  middle_subset : ∀ i, middle i ⊆ X
  free_subset_middle : ∀ i, freeSet i ⊆ middle i
  middle_card_le_free_square : ∀ i,
    (middle i).card ≤ (freeSet i).card * (freeSet i).card
  free_disjoint : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint freeSet
  free : ∀ i, PFree (background i) (freeSet i)
  certificate : ∀ i, ProjectionOrderCertificate (background i) (freeSet i) (Fin 3)
  other_free_subset : ∀ i j, i ≠ j →
    (↑(freeSet j) : Set (Point 3)) ⊆ background i

theorem AlternatingFreeFamily.free_subset
    {q : ℕ} {X : Finset (Point 3)} (F : AlternatingFreeFamily q X) (i : Fin q) :
    F.freeSet i ⊆ X :=
  (F.free_subset_middle i).trans (F.middle_subset i)

/-- If every alternating free set clears the cups--caps threshold, then
either Proposition 2.1 directly finds `n` convex points or its cap branches
assemble to at least `n` convex points. -/
theorem AlternatingFreeFamily.containsConvexSubset
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hlarge : ∀ i,
      Nat.choose (a + n - 4) (a - 2) ^ 3 < (F.freeSet i).card) :
    ContainsConvexSubset 3 n X := by
  classical
  have hbranch (i : Fin q) :
      (∃ C : Finset (Point 3), C ⊆ F.freeSet i ∧ C.card = a ∧
        PCap (F.background i) C) ∨
      (∃ C : Finset (Point 3), C ⊆ F.freeSet i ∧ C.card = n ∧
        InConvexPosition C) :=
    pohoata_zakharov_prop_two_one_three_edges (F.certificate i)
      (F.free i) ha hn (hlarge i)
  by_cases hdirect : ∃ i : Fin q, ∃ C : Finset (Point 3),
      C ⊆ F.freeSet i ∧ C.card = n ∧ InConvexPosition C
  · obtain ⟨i, C, hCZ, hCcard, hCconv⟩ := hdirect
    exact ⟨C, hCZ.trans (F.free_subset i), hCcard, hCconv⟩
  ·
    have hcap (i : Fin q) : ∃ C : Finset (Point 3),
        C ⊆ F.freeSet i ∧ C.card = a ∧ PCap (F.background i) C := by
      rcases hbranch i with h | h
      · exact h
      · exact (hdirect ⟨i, h⟩).elim
    choose K hKsubset hKcard hKcap using hcap
    have hKdisj : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint K := by
      intro i _ j _ hij
      exact (F.free_disjoint (Finset.mem_univ i) (Finset.mem_univ j) hij).mono
        (hKsubset i) (hKsubset j)
    have hUcard : (Finset.univ.biUnion K).card = q * a := by
      rw [Finset.card_biUnion hKdisj]
      simp [hKcard]
    have hconvU : ContainsConvexSubset 3 n (Finset.univ.biUnion K) := by
      apply containsConvexSubset_of_biUnion_pCaps F.background K hKcap
      · intro i j hij
        exact (Finset.coe_subset.mpr (hKsubset j)).trans (F.other_free_subset i j hij)
      · rw [hUcard]
        exact hcount
    obtain ⟨Y, hYU, hYcard, hYconv⟩ := hconvU
    refine ⟨Y, ?_, hYcard, hYconv⟩
    intro y hy
    obtain ⟨i, -, hyi⟩ := Finset.mem_biUnion.mp (hYU hy)
    exact F.free_subset i (hKsubset i hyi)

end

/-! ### Upstream module `JSP527/External/Erdos651/Kirchberger.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Kirchberger witnesses and strict separation in three dimensions

This file proves the finite form of Kirchberger's theorem used in the
Pohoata--Zakharov argument.  If the convex hulls of two finite point sets in
`ℝ³` meet, the intersection is already witnessed by subsets containing at
most five points in total.  The proof applies Carathéodory's theorem in the
four-dimensional homogenized space `Point 3 × ℝ`.

We also record convenient strict-separation forms for finite point sets and
their convex hulls.
-/

open _root_.Set

noncomputable section

private def kirchbergerPos (a : Point 3) : Point 3 × ℝ := (a, 1)

private def kirchbergerNeg (b : Point 3) : Point 3 × ℝ := (-b, -1)

private lemma kirchbergerPos_injective : Function.Injective kirchbergerPos := by
  intro a b h
  exact congrArg Prod.fst h

private lemma kirchbergerNeg_injective : Function.Injective kirchbergerNeg := by
  intro a b h
  simpa [kirchbergerNeg] using congrArg (fun z : Point 3 × ℝ => -z.1) h

/-- **Finite Kirchberger theorem in `ℝ³`.**  An intersection of two finite
convex hulls has a witness using at most five points in total. -/
theorem finite_kirchberger_point3 (A B : Finset (Point 3))
    (hAB : (convexHull ℝ (A : Set (Point 3)) ∩
      convexHull ℝ (B : Set (Point 3))).Nonempty) :
    ∃ A' B' : Finset (Point 3), A' ⊆ A ∧ B' ⊆ B ∧
      A'.card + B'.card ≤ 5 ∧
      (convexHull ℝ (A' : Set (Point 3)) ∩
        convexHull ℝ (B' : Set (Point 3))).Nonempty := by
  classical
  obtain ⟨x, hxA, hxB⟩ := hAB
  rw [Finset.mem_convexHull'] at hxA hxB
  obtain ⟨wa, hwa_nonneg, hwa_sum, hwa_center⟩ := hxA
  obtain ⟨wb, hwb_nonneg, hwb_sum, hwb_center⟩ := hxB
  let S : Finset (Point 3 × ℝ) :=
    A.image kirchbergerPos ∪ B.image kirchbergerNeg
  have hdisj : Disjoint (A.image kirchbergerPos) (B.image kirchbergerNeg) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hzB
    have := congrArg Prod.snd heq
    norm_num [kirchbergerPos, kirchbergerNeg] at this
  let w : Point 3 × ℝ → ℝ := fun z =>
    if z.2 = 1 then (2 : ℝ)⁻¹ * wa z.1 else (2 : ℝ)⁻¹ * wb (-z.1)
  have hw_nonneg : ∀ z ∈ S, 0 ≤ w z := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      simp [w, kirchbergerPos, hwa_nonneg a ha]
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      simp only [w, kirchbergerNeg, neg_neg]
      rw [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
      exact mul_nonneg (by norm_num) (hwb_nonneg b hb)
  have hw_sum : ∑ z ∈ S, w z = 1 := by
    rw [show S = A.image kirchbergerPos ∪ B.image kirchbergerNeg by rfl,
      Finset.sum_union hdisj]
    rw [Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn]
    simp only [w, kirchbergerPos, kirchbergerNeg, neg_neg,
      if_pos rfl, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    rw [← Finset.mul_sum, hwa_sum, ← Finset.mul_sum, hwb_sum]
    norm_num
  have hw_center : ∑ z ∈ S, w z • z = 0 := by
    rw [show S = A.image kirchbergerPos ∪ B.image kirchbergerNeg by rfl,
      Finset.sum_union hdisj]
    rw [Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn]
    simp only [w, kirchbergerPos, kirchbergerNeg, neg_neg,
      if_pos rfl, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero]
      simp_rw [mul_smul, smul_neg]
      rw [← Finset.smul_sum, Finset.sum_neg_distrib, ← Finset.smul_sum,
        hwa_center, hwb_center]
      simp
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero,
        smul_eq_mul, mul_one, mul_neg, mul_one]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hwa_sum, hwb_sum]
      norm_num
  have hzero : (0 : Point 3 × ℝ) ∈ convexHull ℝ (S : Set (Point 3 × ℝ)) := by
    rw [Finset.mem_convexHull']
    exact ⟨w, hw_nonneg, hw_sum, hw_center⟩
  rw [convexHull_eq_union] at hzero
  simp only [Set.mem_iUnion, exists_prop] at hzero
  obtain ⟨t, htS, ht_ind, ht_zero⟩ := hzero
  let A' : Finset (Point 3) := A.filter fun a => kirchbergerPos a ∈ t
  let B' : Finset (Point 3) := B.filter fun b => kirchbergerNeg b ∈ t
  have hA'_sub : A' ⊆ A := Finset.filter_subset _ _
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  have ht_eq : t = A'.image kirchbergerPos ∪ B'.image kirchbergerNeg := by
    ext z
    constructor
    · intro hz
      have hzS := htS hz
      change z ∈ A.image kirchbergerPos ∪ B.image kirchbergerNeg at hzS
      rw [Finset.mem_union] at hzS
      rcases hzS with hzA | hzB
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
        rw [Finset.mem_union]
        exact Or.inl (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hz⟩, rfl⟩)
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hzB
        rw [Finset.mem_union]
        exact Or.inr (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hz⟩, rfl⟩)
    · intro hz
      rw [Finset.mem_union] at hz
      rcases hz with hz | hz
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp ha).2
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp hb).2
  have hcard : A'.card + B'.card ≤ 5 := by
    have ht_card : t.card ≤ 5 := by
      calc
        t.card = Fintype.card t := by simp
        _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Point 3 × ℝ))) + 1 :=
          ht_ind.card_le_finrank_succ
        _ ≤ Module.finrank ℝ (Point 3 × ℝ) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
        _ = 5 := by simp [Point]
    rw [ht_eq, Finset.card_union_of_disjoint] at ht_card
    · simpa [Finset.card_image_iff.mpr kirchbergerPos_injective.injOn,
        Finset.card_image_iff.mpr kirchbergerNeg_injective.injOn] using ht_card
    · exact hdisj.mono (Finset.image_subset_image hA'_sub)
        (Finset.image_subset_image hB'_sub)
  rw [Finset.mem_convexHull'] at ht_zero
  obtain ⟨wt, hwt_nonneg, hwt_sum, hwt_center⟩ := ht_zero
  have ht_disj : Disjoint (A'.image kirchbergerPos) (B'.image kirchbergerNeg) :=
    hdisj.mono (Finset.image_subset_image hA'_sub) (Finset.image_subset_image hB'_sub)
  have hsum_split :
      (∑ a ∈ A', wt (kirchbergerPos a)) +
        ∑ b ∈ B', wt (kirchbergerNeg b) = 1 := by
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hwt_sum
    exact hwt_sum
  have hheight :
      (∑ a ∈ A', wt (kirchbergerPos a)) -
        ∑ b ∈ B', wt (kirchbergerNeg b) = 0 := by
    have hsnd := congrArg Prod.snd hwt_center
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hsnd
    simpa [kirchbergerPos, kirchbergerNeg, Prod.snd_sum,
      Finset.sum_sub_distrib, sub_eq_add_neg] using hsnd
  have hsumA : ∑ a ∈ A', (2 * wt (kirchbergerPos a)) = 1 := by
    rw [← Finset.mul_sum]
    linarith
  have hsumB : ∑ b ∈ B', (2 * wt (kirchbergerNeg b)) = 1 := by
    rw [← Finset.mul_sum]
    linarith
  let y : Point 3 := ∑ a ∈ A', (2 * wt (kirchbergerPos a)) • a
  have hyA : y ∈ convexHull ℝ (A' : Set (Point 3)) := by
    rw [Finset.mem_convexHull']
    refine ⟨fun a => 2 * wt (kirchbergerPos a), ?_, hsumA, rfl⟩
    intro a ha
    apply mul_nonneg (by norm_num)
    apply hwt_nonneg
    rw [ht_eq, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hfirst :
      (∑ a ∈ A', wt (kirchbergerPos a) • a) =
        ∑ b ∈ B', wt (kirchbergerNeg b) • b := by
    have hfst := congrArg Prod.fst hwt_center
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hfst
    apply sub_eq_zero.mp
    simpa [kirchbergerPos, kirchbergerNeg, Prod.fst_sum,
      Finset.sum_neg_distrib, sub_eq_add_neg] using hfst
  have hy_eq : y = ∑ b ∈ B', (2 * wt (kirchbergerNeg b)) • b := by
    dsimp [y]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, hfirst, Finset.smul_sum]
  have hyB : y ∈ convexHull ℝ (B' : Set (Point 3)) := by
    rw [Finset.mem_convexHull']
    refine ⟨fun b => 2 * wt (kirchbergerNeg b), ?_, hsumB, hy_eq.symm⟩
    intro b hb
    apply mul_nonneg (by norm_num)
    apply hwt_nonneg
    rw [ht_eq, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  exact ⟨A', B', hA'_sub, hB'_sub, hcard, y, hyA, hyB⟩

/-- Disjoint finite convex hulls in `ℝ³` have a strict affine separator. -/
theorem finite_convexHulls_strictly_separated_point3 (A B : Finset (Point 3))
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3)))) :
    ∃ (f : Point 3 →L[ℝ] ℝ) (c : ℝ),
      (∀ a ∈ convexHull ℝ (A : Set (Point 3)), f a < c) ∧
      ∀ b ∈ convexHull ℝ (B : Set (Point 3)), c < f b := by
  obtain ⟨f, u, v, hA, huv, hB⟩ :=
    geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ (A : Set (Point 3)))
      (show IsCompact (convexHull ℝ (A : Set (Point 3))) from
        (Finset.finite_toSet A).isCompact_convexHull ℝ)
      (convex_convexHull ℝ (B : Set (Point 3)))
      (show IsClosed (convexHull ℝ (B : Set (Point 3))) from
        ((Finset.finite_toSet B).isCompact_convexHull ℝ).isClosed) hdisj
  exact ⟨f, u, hA, fun b hb => huv.trans (hB b hb)⟩

/-- Pointwise version of strict separation for finite sets in `ℝ³`. -/
theorem finite_sets_strictly_separated_point3 (A B : Finset (Point 3))
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3)))) :
    ∃ (f : Point 3 →L[ℝ] ℝ) (c : ℝ),
      (∀ a ∈ A, f a < c) ∧ ∀ b ∈ B, c < f b := by
  obtain ⟨f, c, hA, hB⟩ := finite_convexHulls_strictly_separated_point3 A B hdisj
  exact ⟨f, c,
    fun a ha => hA a (subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)),
    fun b hb => hB b (subset_convexHull ℝ _ (Finset.mem_coe.mpr hb))⟩

end

end

/-! ### Upstream module `JSP527/External/Erdos651/AboveBelow.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The above--below relation

This file isolates the geometric Ramsey step in the Pohoata--Zakharov proof.
The vertical projection forgets the last coordinate. When the projections of
two segments cross in their relative interiors, their lifts are strictly
ordered by height as soon as the four endpoints are affinely independent.
-/

open _root_.AffineMap _root_.Set

noncomputable section

/-- Projection of `R^3` to the first two coordinates. -/
def verticalProjection (p : Point 3) : Point 2 :=
  WithLp.toLp 2 fun i : Fin 2 => p i.castSucc

/-- The last coordinate of a point of `R^3`. -/
def verticalHeight (p : Point 3) : ℝ := p 2

/-- A parametrized point of the segment from `p` to `q`. -/
def segmentPoint (p q : Point 3) (t : ℝ) : Point 3 :=
  lineMap p q t

/-- Signed area of the projected ordered triangle. -/
def projectedOrientation (a b c : Point 3) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- The projections of `ac` and `bd` cross at the displayed interior parameters. -/
def ProjectedSegmentsCrossAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  t ∈ Ioo (0 : ℝ) 1 ∧ u ∈ Ioo (0 : ℝ) 1 ∧
    verticalProjection (segmentPoint a c t) =
      verticalProjection (segmentPoint b d u)

/-- At a projected crossing, the segment `ac` is strictly above `bd`. -/
def SegmentAboveAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  ProjectedSegmentsCrossAt a c b d t u ∧
    verticalHeight (segmentPoint b d u) < verticalHeight (segmentPoint a c t)

/-- At a projected crossing, the segment `ac` is strictly below `bd`. -/
def SegmentBelowAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  ProjectedSegmentsCrossAt a c b d t u ∧
    verticalHeight (segmentPoint a c t) < verticalHeight (segmentPoint b d u)

/-- The two projected open segments cross and `ac` is above `bd`. -/
def SegmentAbove (a c b d : Point 3) : Prop :=
  ∃ t u : ℝ, SegmentAboveAt a c b d t u

/-- The two projected open segments cross and `ac` is below `bd`. -/
def SegmentBelow (a c b d : Point 3) : Prop :=
  ∃ t u : ℝ, SegmentBelowAt a c b d t u

private lemma projectedOrientation_identities_of_crossing
    {a b c d : Point 3} {t u : ℝ}
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    u * projectedOrientation a b d = t * projectedOrientation a b c ∧
      u * projectedOrientation a c d = (1 - u) * projectedOrientation a b c ∧
      u * projectedOrientation b c d = (1 - t) * projectedOrientation a b c := by
  have h₀ := congrArg (fun p : Point 2 => p 0) hcross.2.2
  have h₁ := congrArg (fun p : Point 2 => p 1) hcross.2.2
  simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub] at h₀ h₁
  have r₀ : u * (d 0 - a 0) - t * (c 0 - a 0) +
      (1 - u) * (b 0 - a 0) = 0 := by linarith [h₀]
  have r₁ : u * (d 1 - a 1) - t * (c 1 - a 1) +
      (1 - u) * (b 1 - a 1) = 0 := by linarith [h₁]
  constructor
  · simp only [projectedOrientation]
    linear_combination (b 0 - a 0) * r₁ - (b 1 - a 1) * r₀
  constructor
  · simp only [projectedOrientation]
    linear_combination (c 0 - a 0) * r₁ - (c 1 - a 1) * r₀
  · simp only [projectedOrientation]
    linear_combination (c 0 - b 0) * r₁ - (c 1 - b 1) * r₀

lemma point3_eq_of_projection_eq_of_height_eq {p q : Point 3}
    (hproj : verticalProjection p = verticalProjection q)
    (hheight : verticalHeight p = verticalHeight q) : p = q := by
  ext i
  fin_cases i
  · simpa [verticalProjection] using congrArg (fun r : Point 2 => r 0) hproj
  · simpa [verticalProjection] using congrArg (fun r : Point 2 => r 1) hproj
  · simpa [verticalHeight] using hheight

lemma crossing_height_ne_of_affineIndependent
    {a c b d : Point 3} {t u : ℝ}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    verticalHeight (segmentPoint a c t) ≠
      verticalHeight (segmentPoint b d u) := by
  intro hheight
  have heq : segmentPoint a c t = segmentPoint b d u :=
    point3_eq_of_projection_eq_of_height_eq hcross.2.2 hheight
  let w₁ : Fin 4 → ℝ := Finset.affineCombinationLineMapWeights 0 2 t
  let w₂ : Fin 4 → ℝ := Finset.affineCombinationLineMapWeights 1 3 u
  have hw₁ : ∑ i, w₁ i = 1 := by
    simpa [w₁] using
      (Finset.sum_affineCombinationLineMapWeights (s := (Finset.univ : Finset (Fin 4)))
        (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by simp) (by simp) t)
  have hw₂ : ∑ i, w₂ i = 1 := by
    simpa [w₂] using
      (Finset.sum_affineCombinationLineMapWeights (s := (Finset.univ : Finset (Fin 4)))
        (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by simp) (by simp) u)
  have hac : (Finset.univ : Finset (Fin 4)).affineCombination ℝ ![a, b, c, d] w₁ =
      segmentPoint a c t := by
    simpa [w₁, segmentPoint] using
      (Finset.affineCombination_affineCombinationLineMapWeights
        (s := (Finset.univ : Finset (Fin 4))) ![a, b, c, d]
        (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by simp) (by simp) t)
  have hbd : (Finset.univ : Finset (Fin 4)).affineCombination ℝ ![a, b, c, d] w₂ =
      segmentPoint b d u := by
    simpa [w₂, segmentPoint] using
      (Finset.affineCombination_affineCombinationLineMapWeights
        (s := (Finset.univ : Finset (Fin 4))) ![a, b, c, d]
        (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by simp) (by simp) u)
  have hweights : ∀ i ∈ (Finset.univ : Finset (Fin 4)), w₁ i = w₂ i :=
    (hind.affineCombination_eq_iff_eq hw₁ hw₂).mp (hac.trans (heq.trans hbd.symm))
  have hzero : 1 - t = 0 := by
    simpa [w₁, w₂] using hweights 0 (by simp)
  linarith [hcross.1.2]

theorem segmentAboveAt_or_segmentBelowAt
    {a c b d : Point 3} {t u : ℝ}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    SegmentAboveAt a c b d t u ∨ SegmentBelowAt a c b d t u := by
  rcases lt_or_gt_of_ne (crossing_height_ne_of_affineIndependent hind hcross) with h | h
  · exact Or.inr ⟨hcross, h⟩
  · exact Or.inl ⟨hcross, h⟩

theorem segmentAbove_or_segmentBelow
    {a c b d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ∃ t u : ℝ, ProjectedSegmentsCrossAt a c b d t u) :
    SegmentAbove a c b d ∨ SegmentBelow a c b d := by
  obtain ⟨t, u, htu⟩ := hcross
  rcases segmentAboveAt_or_segmentBelowAt hind htu with h | h
  · exact Or.inl ⟨t, u, h⟩
  · exact Or.inr ⟨t, u, h⟩

/-! ## The oriented-volume form of above/below -/

/-- Matrix of the three displacement vectors from `a`. -/
def vsubMatrix (a b c d : Point 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![b - a, c - a, d - a] j i

/-- Signed volume of the ordered tetrahedron `(a,b,c,d)`. -/
def orientedVolume (a b c d : Point 3) : ℝ :=
  (vsubMatrix a b c d).det

private lemma orientedVolume_eq (a b c d : Point 3) :
    orientedVolume a b c d =
      (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
      (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
      (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0)) := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

/-- The signed volume is an affine functional of its fourth vertex. -/
def orientedVolumeLinear (a b c : Point 3) : Point 3 →ₗ[ℝ] ℝ where
  toFun p := orientedVolume a b c p - orientedVolume a b c 0
  map_add' p q := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hadd (i : Fin 3) : (p + q) i = p i + q i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hadd, hzero]
    ring
  map_smul' r p := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hsmul (i : Fin 3) : (r • p) i = r * p i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hsmul, hzero, RingHom.id_apply]
    ring

def orientedVolumeAffine (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (orientedVolumeLinear a b c).toAffineMap +
    AffineMap.const ℝ (Point 3) (orientedVolume a b c 0)

@[simp] lemma orientedVolumeAffine_apply (a b c p : Point 3) :
    orientedVolumeAffine a b c p = orientedVolume a b c p := by
  simp [orientedVolumeAffine, orientedVolumeLinear]

private lemma mem_convexHull_zero_face
    (T : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ) {z : Point 3}
    (hφ : ∀ p ∈ T, 0 ≤ φ p) (hz : z ∈ convexHull ℝ (T : Set (Point 3)))
    (hz0 : φ z = 0) :
    z ∈ convexHull ℝ ((T.filter fun p => φ p = 0 : Finset (Point 3)) : Set (Point 3)) := by
  obtain ⟨w, hw, hwsum, hwz⟩ := Finset.mem_convexHull'.mp hz
  let U := T.filter fun p => φ p = 0
  have hzcomb : T.affineCombination ℝ id w = z := by
    rw [T.affineCombination_eq_linear_combination _ _ hwsum]
    simpa using hwz
  have hsumprod : ∑ p ∈ T, w p * φ p = φ z := by
    calc
      ∑ p ∈ T, w p * φ p = T.affineCombination ℝ (φ ∘ id) w := by
        rw [T.affineCombination_eq_linear_combination _ _ hwsum]
        simp only [Function.comp_apply, id_eq, smul_eq_mul]
      _ = φ (T.affineCombination ℝ id w) :=
        (T.map_affineCombination id w hwsum φ).symm
      _ = φ z := by rw [hzcomb]
  have hsumzero : ∑ p ∈ T, w p * φ p = 0 := hsumprod.trans hz0
  have hterm : ∀ p ∈ T, w p * φ p = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hsumzero
    · exact hsumzero
    · intro p hp
      exact mul_nonneg (hw p hp) (hφ p hp)
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hwzero : ∀ p ∈ T, p ∉ U → w p = 0 := by
    intro p hpT hpU
    have hφne : φ p ≠ 0 := by
      intro hφ
      exact hpU (Finset.mem_filter.2 ⟨hpT, hφ⟩)
    exact (mul_eq_zero.mp (hterm p hpT)).resolve_right hφne
  have hsumU : ∑ p ∈ U, w p = 1 := by
    rw [Finset.sum_subset hUT hwzero]
    exact hwsum
  have hpointU : ∑ p ∈ U, w p • p = z := by
    rw [Finset.sum_subset hUT]
    · exact hwz
    · intro p hpT hpU
      simp [hwzero p hpT hpU]
  apply Finset.mem_convexHull'.2
  exact ⟨w, (fun p hp => hw p (hUT hp)), hsumU, hpointU⟩

lemma orientedVolume_ne_zero_of_affineIndependent {a b c d : Point 3}
    (h : AffineIndependent ℝ ![a, b, c, d]) : orientedVolume a b c d ≠ 0 := by
  have hv : LinearIndependent ℝ ![b - a, c - a, d - a] := by
    apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 4)) ?_).mpr
      ((affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c, d] 0).mp h)
    funext i
    fin_cases i <;> rfl
  have hcols : LinearIndependent ℝ (vsubMatrix a b c d).col := by
    have hmapped := hv.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun :
        (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) =
          (vsubMatrix a b c d).col := by
      funext j i
      rfl
    change LinearIndependent ℝ
      (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) at hmapped
    rw [hfun] at hmapped
    exact hmapped
  exact ((Matrix.isUnit_iff_isUnit_det (vsubMatrix a b c d)).mp
    ((Matrix.linearIndependent_cols_iff_isUnit).mp hcols)).ne_zero

private lemma crossing_orientedVolume_identity
    {a b c d : Point 3} {t u : ℝ}
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    u * orientedVolume a b c d =
      -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
        ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) := by
  have h₀ := congrArg (fun p : Point 2 => p 0) hcross.2.2
  have h₁ := congrArg (fun p : Point 2 => p 1) hcross.2.2
  simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h₀ h₁
  have r₀ : u * (d 0 - a 0) - t * (c 0 - a 0) + (1 - u) * (b 0 - a 0) = 0 := by
    linarith [h₀]
  have r₁ : u * (d 1 - a 1) - t * (c 1 - a 1) + (1 - u) * (b 1 - a 1) = 0 := by
    linarith [h₁]
  rw [orientedVolume_eq]
  simp [verticalHeight, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  linear_combination
    ((b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1)) * r₀ +
    ((b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2)) * r₁

private lemma orientedVolume_rotate (a b c d : Point 3) :
    orientedVolume a b c d = -orientedVolume d a b c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

private lemma orientedVolume_middle_rotate (a b c d : Point 3) :
    orientedVolume a b c d = orientedVolume a d b c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

private lemma orientedVolume_swap_last (a b c d : Point 3) :
    orientedVolume a b c d = -orientedVolume a b d c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_first (a b c : Point 3) :
    orientedVolume a b c a = 0 := by
  rw [orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_second (a b c : Point 3) :
    orientedVolume a b c b = 0 := by
  rw [orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_third (a b c : Point 3) :
    orientedVolume a b c c = 0 := by
  rw [orientedVolume_eq]
  ring

private lemma ordered_above_volume_orientation_neg
    {a b c d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (h : SegmentAbove a c b d) :
    orientedVolume a b c d * projectedOrientation a b c < 0 := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hid := crossing_orientedVolume_identity hcross
  have hu : 0 < u := hcross.2.1.1
  have hH : 0 < verticalHeight (segmentPoint a c t) -
      verticalHeight (segmentPoint b d u) := sub_pos.mpr hheight
  have hP : projectedOrientation a b c ≠ 0 := by
    intro hP0
    have hV : orientedVolume a b c d = 0 := by
      have : u * orientedVolume a b c d = 0 := by
        rw [hid]
        change -(verticalHeight (segmentPoint a c t) -
          verticalHeight (segmentPoint b d u)) * projectedOrientation a b c = 0
        rw [hP0, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hu.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hind hV
  have hsq : 0 < projectedOrientation a b c ^ 2 := sq_pos_of_ne_zero hP
  have hidP := congrArg (fun z : ℝ => z * projectedOrientation a b c) hid
  have hmul : u * (orientedVolume a b c d * projectedOrientation a b c) < 0 := by
    calc
      u * (orientedVolume a b c d * projectedOrientation a b c) =
          (u * orientedVolume a b c d) * projectedOrientation a b c := by ring
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) *
            projectedOrientation a b c := hidP
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          projectedOrientation a b c ^ 2 := by
        rw [pow_two, projectedOrientation]
        ring
      _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hH) hsq
  by_contra hnonneg
  exact (not_lt_of_ge (mul_nonneg hu.le (le_of_not_gt hnonneg))) hmul

private lemma ordered_below_volume_orientation_pos
    {a b c d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (h : SegmentBelow a c b d) :
    0 < orientedVolume a b c d * projectedOrientation a b c := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hid := crossing_orientedVolume_identity hcross
  have hu : 0 < u := hcross.2.1.1
  have hH : verticalHeight (segmentPoint a c t) -
      verticalHeight (segmentPoint b d u) < 0 := sub_neg.mpr hheight
  have hP : projectedOrientation a b c ≠ 0 := by
    intro hP0
    have hV : orientedVolume a b c d = 0 := by
      have : u * orientedVolume a b c d = 0 := by
        rw [hid]
        change -(verticalHeight (segmentPoint a c t) -
          verticalHeight (segmentPoint b d u)) * projectedOrientation a b c = 0
        rw [hP0, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hu.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hind hV
  have hsq : 0 < projectedOrientation a b c ^ 2 := sq_pos_of_ne_zero hP
  have hidP := congrArg (fun z : ℝ => z * projectedOrientation a b c) hid
  have hmul : 0 < u * (orientedVolume a b c d * projectedOrientation a b c) := by
    calc
      0 < -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          projectedOrientation a b c ^ 2 := mul_pos (neg_pos.mpr hH) hsq
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) *
            projectedOrientation a b c := by
        rw [pow_two, projectedOrientation]
        ring
      _ = (u * orientedVolume a b c d) * projectedOrientation a b c := hidP.symm
      _ = u * (orientedVolume a b c d * projectedOrientation a b c) := by ring
  by_contra hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt hnonpos))) hmul

private lemma product_pos_of_positive_ratio {P Q u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hQ : Q ≠ 0) (h : u * P = v * Q) :
    0 < Q * P := by
  have hsq : 0 < Q ^ 2 := sq_pos_of_ne_zero hQ
  have hmul := congrArg (fun z : ℝ => z * Q) h
  have : 0 < u * (Q * P) := by
    nlinarith
  by_contra hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt hnonpos))) this

private lemma same_sign_trans {A B C : ℝ}
    (hAB : 0 < A * B) (hBC : 0 < B * C) : 0 < A * C := by
  rcases (mul_pos_iff.mp hBC) with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · exact mul_pos (pos_of_mul_pos_left hAB hB.le) hC
  · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left hAB hB.le) hC

private lemma opposite_sign_trans {A B C : ℝ}
    (hAB : A * B < 0) (hBC : 0 < B * C) : A * C < 0 := by
  rcases (mul_pos_iff.mp hBC) with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · exact mul_neg_of_neg_of_pos (neg_of_mul_neg_left hAB hB.le) hC
  · exact mul_neg_of_pos_of_neg (pos_of_mul_neg_left hAB hB.le) hC

/-! ## The four-uniform Ramsey selection -/

/-- Every interlaced quadruple of indices has the projected crossing and
general-position properties needed by the above--below dichotomy.  Consecutive
vertices of a strictly convex projected polygon satisfy this predicate. -/
def IsProjectedConvexChain {I : Type*} [LinearOrder I]
    (x : I → Point 3) (S : Finset I) : Prop :=
  ∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
    i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
      AffineIndependent ℝ ![x i₀, x i₁, x i₂, x i₃] ∧
        ∃ t u : ℝ, ProjectedSegmentsCrossAt (x i₀) (x i₂) (x i₁) (x i₃) t u

/-- All interlaced chords on `S` have the same strict vertical order. -/
def UniformAboveBelowOn {I : Type*} [LinearOrder I]
    (x : I → Point 3) (S : Finset I) : Prop :=
  (∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
        SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃)) ∨
  (∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
        SegmentBelow (x i₀) (x i₂) (x i₁) (x i₃))

private lemma cutSign_above_before
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i a b c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (hi : i ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hia : i < a) (hab : a < b) (hbc : b < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain i hi a ha b hb c hc hia hab hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove i hi a ha b hb c hc hia hab hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x i) (x a) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x i) (x a) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.1.2) hQ hids.2.2
  have h := opposite_sign_trans hneg hsame
  rw [orientedVolume_rotate]
  nlinarith

private lemma cutSign_above_between₁
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a i b c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hi : i ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hai : a < i) (hib : i < b) (hbc : b < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain a ha i hi b hb c hc hai hib hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove a ha i hi b hb c hc hai hib hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x i) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x a) (x i) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.2.1.2) hQ hids.2.1
  rw [orientedVolume_middle_rotate]
  exact opposite_sign_trans hneg hsame

private lemma cutSign_above_between₂
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b i c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hi : i ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbi : b < i) (hic : i < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain a ha b hb i hi c hc hab hbi hic
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove a ha b hb i hi c hc hab hbi hic)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x b) (x i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x a) (x b) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 hcross.1.1 hQ hids.1
  have h := opposite_sign_trans hneg hsame
  rw [orientedVolume_swap_last]
  nlinarith

private lemma cutSign_above_after
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hi : i ∈ S)
    (hab : a < b) (hbc : b < c) (hci : c < i) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 :=
  ordered_above_volume_orientation_neg
    (hchain a ha b hb c hc i hi hab hbc hci).1
    (habove a ha b hb c hc i hi hab hbc hci)

private lemma cutSign_below_before
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i a b c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (hi : i ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hia : i < a) (hab : a < b) (hbc : b < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain i hi a ha b hb c hc hia hab hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow i hi a ha b hb c hc hia hab hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x i) (x a) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x i) (x a) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.1.2) hQ hids.2.2
  have h := same_sign_trans hpos hsame
  rw [orientedVolume_rotate]
  nlinarith

private lemma cutSign_below_between₁
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a i b c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hi : i ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hai : a < i) (hib : i < b) (hbc : b < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain a ha i hi b hb c hc hai hib hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow a ha i hi b hb c hc hai hib hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x i) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x a) (x i) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.2.1.2) hQ hids.2.1
  rw [orientedVolume_middle_rotate]
  exact same_sign_trans hpos hsame

private lemma cutSign_below_between₂
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b i c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hi : i ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbi : b < i) (hic : i < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain a ha b hb i hi c hc hab hbi hic
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow a ha b hb i hi c hc hab hbi hic)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x b) (x i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x a) (x b) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 hcross.1.1 hQ hids.1
  have h := same_sign_trans hpos hsame
  rw [orientedVolume_swap_last]
  nlinarith

private lemma cutSign_below_after
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hi : i ∈ S)
    (hab : a < b) (hbc : b < c) (hci : c < i) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
  ordered_below_volume_orientation_pos
    (hchain a ha b hb c hc i hi hab hbc hci).1
    (hbelow a ha b hb c hc i hi hab hbc hci)

/-- The affine cut through three vertices, normalized so that the sign
lemmas above do not depend on the orientation of their projection. -/
private def alternatingCutAffine (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  projectedOrientation a b c • orientedVolumeAffine a b c

@[simp] private lemma alternatingCutAffine_apply (a b c p : Point 3) :
    alternatingCutAffine a b c p =
      orientedVolume a b c p * projectedOrientation a b c := by
  simp [alternatingCutAffine, mul_comm]

private theorem convexHulls_disjoint_of_weak_affine_separator
    (A B : Finset (Point 3)) (f : Point 3 →ᵃ[ℝ] ℝ)
    (hAB : Disjoint A B) (hA : ∀ p ∈ A, 0 ≤ f p) (hB : ∀ p ∈ B, f p ≤ 0)
    (hzero : AffineIndependent ℝ
      (fun p : ↥((A.filter fun p => f p = 0) ∪ (B.filter fun p => f p = 0)) ↦
        (p : Point 3))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  classical
  rw [Set.disjoint_left]
  intro z hzA hzB
  have hznonneg : 0 ≤ f z := by
    have hz : z ∈ f ⁻¹' Set.Ici 0 :=
      convexHull_min (fun p hp => hA p hp)
        ((convex_Ici (0 : ℝ)).affine_preimage f) hzA
    exact hz
  have hznonpos : f z ≤ 0 := by
    have hz : z ∈ f ⁻¹' Set.Iic 0 :=
      convexHull_min (fun p hp => hB p hp)
        ((convex_Iic (0 : ℝ)).affine_preimage f) hzB
    exact hz
  have hzf : f z = 0 := le_antisymm hznonpos hznonneg
  have hzAf := mem_convexHull_zero_face A f hA hzA hzf
  have hzBf' := mem_convexHull_zero_face B (-f)
    (by intro p hp; simpa using neg_nonneg.mpr (hB p hp)) hzB (by simp [hzf])
  have hfilter : B.filter (fun p => (-f) p = 0) = B.filter fun p => f p = 0 := by
    ext p
    simp
  rw [hfilter] at hzBf'
  have hinter := hzero.convexHull_inter'
  have hzinter : z ∈
      convexHull ℝ ((A.filter fun p => f p = 0) : Set (Point 3)) ∩
        convexHull ℝ ((B.filter fun p => f p = 0) : Set (Point 3)) :=
    ⟨hzAf, hzBf'⟩
  rw [← hinter] at hzinter
  have hdiszero : Disjoint
      (((A.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3))
      (((B.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    change p ∈ A.filter (fun p => f p = 0) at hpA
    change p ∈ B.filter (fun p => f p = 0) at hpB
    exact Finset.disjoint_left.1 hAB (Finset.mem_filter.1 hpA).1
      (Finset.mem_filter.1 hpB).1
  have hempty :
      (((A.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) ∩
        (((B.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdiszero
  rw [hempty] at hzinter
  simpa using hzinter

private lemma affineIndependent_finset_of_subset_quad
    {p₀ p₁ p₂ p₃ : Point 3} {T : Finset (Point 3)}
    (h : AffineIndependent ℝ ![p₀, p₁, p₂, p₃])
    (hT : T ⊆ {p₀, p₁, p₂, p₃}) :
    AffineIndependent ℝ (fun p : ↥T ↦ (p : Point 3)) := by
  have hrange : Set.range (![p₀, p₁, p₂, p₃] : Fin 4 → Point 3) =
      ({p₀, p₁, p₂, p₃} : Set (Point 3)) := by
    ext p
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  have hrangeAI := h.range
  rw [hrange] at hrangeAI
  exact hrangeAI.mono (by
    intro p hp
    simpa using hT hp)

private theorem five_point_partition_disjoint_of_adjacent_pair
    (A B : Finset (Point 3)) (f : Point 3 →ᵃ[ℝ] ℝ)
    {p q r s t : Point 3}
    (hAB : Disjoint A B)
    (hAcov : A ⊆ {p, q, r, s, t}) (hBcov : B ⊆ {p, q, r, s, t})
    (hpq : (p ∈ A ∧ q ∈ A) ∨ (p ∈ B ∧ q ∈ B))
    (hroot : f r = 0 ∧ f s = 0 ∧ f t = 0)
    (hsign : (0 < f p ∧ 0 < f q) ∨ (f p < 0 ∧ f q < 0))
    (hrootAI : AffineIndependent ℝ
      (fun z : ↥({r, s, t} : Finset (Point 3)) ↦ (z : Point 3))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  classical
  have hfp : f p ≠ 0 := by rcases hsign with h | h <;> nlinarith [h.1]
  have hfq : f q ≠ 0 := by rcases hsign with h | h <;> nlinarith [h.2]
  have hzero_f : AffineIndependent ℝ
      (fun z : ↥((A.filter fun z => f z = 0) ∪ (B.filter fun z => f z = 0)) ↦
        (z : Point 3)) := by
    apply hrootAI.mono
    intro z hz
    simp only [Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq] at hz
    have hzcover : z ∈ ({p, q, r, s, t} : Finset (Point 3)) := by
      rcases hz with hz | hz
      · exact hAcov hz.1
      · exact hBcov hz.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzcover ⊢
    rcases hzcover with rfl | rfl | rfl | rfl | rfl
    · rcases hz with hz | hz <;> exact (hfp hz.2).elim
    · rcases hz with hz | hz <;> exact (hfq hz.2).elim
    · simp
    · simp
    · simp
  have hzero_neg : AffineIndependent ℝ
      (fun z : ↥((A.filter fun z => (-f) z = 0) ∪ (B.filter fun z => (-f) z = 0)) ↦
        (z : Point 3)) := by
    have heq :
        (A.filter fun z => (-f) z = 0) ∪ (B.filter fun z => (-f) z = 0) =
          (A.filter fun z => f z = 0) ∪ (B.filter fun z => f z = 0) := by
      ext z
      simp
    rw [heq]
    exact hzero_f
  rcases hpq with hpqA | hpqB
  · rcases hsign with hpos | hneg
    · apply convexHulls_disjoint_of_weak_affine_separator A B f hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact hpos.1.le
        · exact hpos.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hpqA.1 hzB).elim
        · exact (Finset.disjoint_left.1 hAB hpqA.2 hzB).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_f
    · apply convexHulls_disjoint_of_weak_affine_separator A B (-f) hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · simpa using neg_nonneg.mpr hneg.1.le
        · simpa using neg_nonneg.mpr hneg.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hpqA.1 hzB).elim
        · exact (Finset.disjoint_left.1 hAB hpqA.2 hzB).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_neg
  · rcases hsign with hpos | hneg
    · apply convexHulls_disjoint_of_weak_affine_separator A B (-f) hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.1).elim
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.2).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · simpa using neg_nonpos.mpr hpos.1.le
        · simpa using neg_nonpos.mpr hpos.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_neg
    · apply convexHulls_disjoint_of_weak_affine_separator A B f hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.1).elim
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.2).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact hneg.1.le
        · exact hneg.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_f

private noncomputable def quadAboveColor {I : Type*} [LinearOrder I]
    (x : I → Point 3) (A : Finset I) : Bool := by
  classical
  exact decide (∃ i₀ i₁ i₂ i₃ : I,
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧
    A = {i₀, i₁, i₂, i₃} ∧ SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃))

private lemma interlaced_insert_card {I : Type*} [LinearOrder I]
    {i₀ i₁ i₂ i₃ : I} (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) :
    ({i₀, i₁, i₂, i₃} : Finset I).card = 4 := by
  have h₀₂ : i₀ ≠ i₂ := (h₀₁.trans h₁₂).ne
  have h₀₃ : i₀ ≠ i₃ := (h₀₁.trans (h₁₂.trans h₂₃)).ne
  have h₁₃ : i₁ ≠ i₃ := (h₁₂.trans h₂₃).ne
  simp [h₀₁.ne, h₁₂.ne, h₂₃.ne, h₀₂, h₀₃, h₁₃]

/-- The same four-uniform Ramsey selection with the concrete threshold used
by the nested-scale Pohoata--Zakharov assembly. -/
theorem exists_uniformAboveBelow_subchain_of_ramseySequence
    {m : ℕ} {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I)
    (hcard : uniformRamseySequence 4 m ≤ S.card)
    (hchain : IsProjectedConvexChain x S) :
    ∃ H : Finset I, H ⊆ S ∧ H.card = m ∧ UniformAboveBelowOn x H := by
  classical
  obtain ⟨H, hHS, hHm, b, hb⟩ :=
    uniformRamseySequence_spec 4 m S hcard (quadAboveColor x)
  refine ⟨H, hHS, hHm, ?_⟩
  cases b with
  | false =>
      right
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hcfalse : quadAboveColor x A = false := hb A hAH hAcard
      have hnabove : ¬ SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃) := by
        intro habove
        have : quadAboveColor x A = true := by
          change decide (∃ j₀ j₁ j₂ j₃ : I,
            j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
            A = {j₀, j₁, j₂, j₃} ∧
              SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃)) = true
          exact decide_eq_true ⟨i₀, i₁, i₂, i₃, h₀₁, h₁₂, h₂₃, rfl, habove⟩
        simp_all
      have hdata := hchain i₀ (hHS hi₀) i₁ (hHS hi₁)
        i₂ (hHS hi₂) i₃ (hHS hi₃) h₀₁ h₁₂ h₂₃
      exact (segmentAbove_or_segmentBelow hdata.1 hdata.2).resolve_left hnabove
  | true =>
      left
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hctrue : quadAboveColor x A = true := hb A hAH hAcard
      have hex : ∃ j₀ j₁ j₂ j₃ : I,
          j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
          A = {j₀, j₁, j₂, j₃} ∧
            SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃) := by
        apply of_decide_eq_true
        exact hctrue
      obtain ⟨j₀, j₁, j₂, j₃, hj₀₁, hj₁₂, hj₂₃, hAeq, habove⟩ := hex
      have hmem0 : j₀ ∈ A := by rw [hAeq]; simp
      have hmem1 : j₁ ∈ A := by rw [hAeq]; simp
      have hmem2 : j₂ ∈ A := by rw [hAeq]; simp
      have hmem3 : j₃ ∈ A := by rw [hAeq]; simp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hmem0 hmem1 hmem2 hmem3
      have hj₀ : j₀ = i₀ := by grind
      have hj₁ : j₁ = i₁ := by grind
      have hj₂ : j₂ = i₂ := by grind
      have hj₃ : j₃ = i₃ := by grind
      simpa [hj₀, hj₁, hj₂, hj₃] using habove

/-! ## Alternating blocks and the five-point separation reduction -/

/-- The first side of the four consecutive blocks cut at `a,b,c`: the
initial and the third block. -/
def firstAlternatingBlock {I : Type*} [LinearOrder I]
    (S : Finset I) (a b c : I) : Finset I :=
  S.filter fun i => i < a ∨ (b ≤ i ∧ i < c)

/-- The second side of the four consecutive blocks cut at `a,b,c`: the
second and final block. -/
def secondAlternatingBlock {I : Type*} [LinearOrder I]
    (S : Finset I) (a b c : I) : Finset I :=
  S.filter fun i => (a ≤ i ∧ i < b) ∨ c ≤ i

private lemma IsProjectedConvexChain.injOn
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    (hchain : IsProjectedConvexChain x S) (hcard : 4 ≤ S.card) :
    Set.InjOn x (S : Set I) := by
  classical
  intro i hi j hj hij
  by_contra hne
  have hpcard : ({i, j} : Finset I).card = 2 := by simp [hne]
  have hpS : ({i, j} : Finset I) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  obtain ⟨T, hpT, hTS, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hpS (by omega : ({i, j} : Finset I).card ≤ 4) hcard
  let e : Fin 4 ↪o I := T.orderEmbOfFin hTcard
  have heS (r : Fin 4) : e r ∈ S :=
    hTS (T.orderEmbOfFin_mem hTcard r)
  have he₀₁ : e 0 < e 1 := e.strictMono (by omega)
  have he₁₂ : e 1 < e 2 := e.strictMono (by omega)
  have he₂₃ : e 2 < e 3 := e.strictMono (by omega)
  have heAI := (hchain (e 0) (heS 0) (e 1) (heS 1) (e 2) (heS 2) (e 3) (heS 3)
    he₀₁ he₁₂ he₂₃).1
  have hefun : (![x (e 0), x (e 1), x (e 2), x (e 3)] : Fin 4 → Point 3) =
      fun r => x (e r) := by
    funext r
    fin_cases r <;> rfl
  rw [hefun] at heAI
  have hiT : i ∈ T := hpT (by simp)
  have hjT : j ∈ T := hpT (by simp)
  have hiimage : i ∈ Finset.image e Finset.univ := by
    rw [T.image_orderEmbOfFin_univ hTcard]
    exact hiT
  have hjimage : j ∈ Finset.image e Finset.univ := by
    rw [T.image_orderEmbOfFin_univ hTcard]
    exact hjT
  obtain ⟨ri, -, hri⟩ := Finset.mem_image.1 hiimage
  obtain ⟨rj, -, hrj⟩ := Finset.mem_image.1 hjimage
  have hrirj : ri = rj := heAI.injective (by simpa [hri, hrj] using hij)
  apply hne
  exact hri.symm.trans ((congrArg e hrirj).trans hrj)

/-- The local five-index classification.  Five ordered indices placed in
four consecutive alternating blocks have an adjacent pair in one block.
The plane through the other three indices has one strict sign on that pair;
its zero face is an affinely independent face of an ordered quadruple. -/
private theorem five_ordered_alternatingBlock_hulls_disjoint
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i₀ i₁ i₂ i₃ i₄ : I}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S)
    (hinj : Set.InjOn x (S : Set I))
    (hi₀ : i₀ ∈ S) (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S)
    (hi₃ : i₃ ∈ S) (hi₄ : i₄ ∈ S)
    (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄) :
    let U : Finset I := {i₀, i₁, i₂, i₃, i₄}
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock U a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock U a b c).image x : Set (Point 3))) := by
  classical
  dsimp only
  let U : Finset I := {i₀, i₁, i₂, i₃, i₄}
  let P := firstAlternatingBlock U a b c
  let Q := secondAlternatingBlock U a b c
  let A := P.image x
  let B := Q.image x
  have hiU : ∀ r ∈ U, r ∈ S := by
    intro r hr
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro r hrP hrQ
    simp only [P, Q, firstAlternatingBlock, secondAlternatingBlock,
      Finset.mem_filter] at hrP hrQ
    grind
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨r, hrP, rfl⟩ := Finset.mem_image.1 hyA
    obtain ⟨s, hsQ, hrs⟩ := Finset.mem_image.1 hyB
    have hrU : r ∈ U := by
      exact (Finset.mem_filter.1 hrP).1
    have hsU : s ∈ U := by
      exact (Finset.mem_filter.1 hsQ).1
    have hrs' : r = s := hinj (hiU r hrU) (hiU s hsU) hrs.symm
    subst s
    exact Finset.disjoint_left.1 hPQ hrP hsQ
  have hAcov : A ⊆ {x i₀, x i₁, x i₂, x i₃, x i₄} := by
    intro y hy
    obtain ⟨r, hrP, rfl⟩ := Finset.mem_image.1 hy
    have hrU : r ∈ U := (Finset.mem_filter.1 hrP).1
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hrU ⊢
    rcases hrU with rfl | rfl | rfl | rfl | rfl <;> simp
  have hBcov : B ⊆ {x i₀, x i₁, x i₂, x i₃, x i₄} := by
    intro y hy
    obtain ⟨r, hrQ, rfl⟩ := Finset.mem_image.1 hy
    have hrU : r ∈ U := (Finset.mem_filter.1 hrQ).1
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hrU ⊢
    rcases hrU with rfl | rfl | rfl | rfl | rfl <;> simp
  have hpair :
      ((i₀ ∈ P ∧ i₁ ∈ P) ∨ (i₀ ∈ Q ∧ i₁ ∈ Q)) ∨
      ((i₁ ∈ P ∧ i₂ ∈ P) ∨ (i₁ ∈ Q ∧ i₂ ∈ Q)) ∨
      ((i₂ ∈ P ∧ i₃ ∈ P) ∨ (i₂ ∈ Q ∧ i₃ ∈ Q)) ∨
      ((i₃ ∈ P ∧ i₄ ∈ P) ∨ (i₃ ∈ Q ∧ i₄ ∈ Q)) := by
    simp only [P, Q, firstAlternatingBlock, secondAlternatingBlock,
      Finset.mem_filter]
    simp only [U, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
      true_and]
    grind
  have hcover_perm (p q r s t : Point 3)
      (heq : ({p, q, r, s, t} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄}) :
      A ⊆ {p, q, r, s, t} ∧ B ⊆ {p, q, r, s, t} := by
    rw [heq]
    exact ⟨hAcov, hBcov⟩
  rcases hpair with hpair | hpair | hpair | hpair
  · let f := alternatingCutAffine (x i₂) (x i₃) (x i₄)
    have hpq : (x i₀ ∈ A ∧ x i₁ ∈ A) ∨ (x i₀ ∈ B ∧ x i₁ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₂) = 0 ∧ f (x i₃) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₀) ∧ 0 < f (x i₁)) ∨
        (f (x i₀) < 0 ∧ f (x i₁) < 0) := by
      rcases huniform with habove | hbelow
      · left
        simpa [f] using ⟨
          cutSign_above_before hchain habove hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄,
          cutSign_above_before hchain habove hi₁ hi₂ hi₃ hi₄
            h₁₂ h₂₃ h₃₄⟩
      · right
        simpa [f] using ⟨
          cutSign_below_before hchain hbelow hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄,
          cutSign_below_before hchain hbelow hi₁ hi₂ hi₃ hi₄
            h₁₂ h₂₃ h₃₄⟩
    have hquad := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₂, x i₃, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have hcov := hcover_perm (x i₀) (x i₁) (x i₂) (x i₃) (x i₄) rfl
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₃) (x i₄)
    have hpq : (x i₁ ∈ A ∧ x i₂ ∈ A) ∨ (x i₁ ∈ B ∧ x i₂ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₃) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₁) ∧ 0 < f (x i₂)) ∨
        (f (x i₁) < 0 ∧ f (x i₂) < 0) := by
      rcases huniform with habove | hbelow
      · right
        simpa [f] using ⟨
          cutSign_above_between₁ hchain habove hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄,
          cutSign_above_between₁ hchain habove hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄⟩
      · left
        simpa [f] using ⟨
          cutSign_below_between₁ hchain hbelow hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄,
          cutSign_below_between₁ hchain hbelow hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₃ hi₃ i₄ hi₄ h₀₁
      (h₁₂.trans h₂₃) h₃₄).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₃, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₁, x i₂, x i₀, x i₃, x i₄} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₁) (x i₂) (x i₀) (x i₃) (x i₄) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₁) (x i₄)
    have hpq : (x i₂ ∈ A ∧ x i₃ ∈ A) ∨ (x i₂ ∈ B ∧ x i₃ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₁) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₂) ∧ 0 < f (x i₃)) ∨
        (f (x i₂) < 0 ∧ f (x i₃) < 0) := by
      rcases huniform with habove | hbelow
      · left
        simpa [f] using ⟨
          cutSign_above_between₂ hchain habove hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄),
          cutSign_above_between₂ hchain habove hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄⟩
      · right
        simpa [f] using ⟨
          cutSign_below_between₂ hchain hbelow hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄),
          cutSign_below_between₂ hchain hbelow hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₂ hi₂ i₄ hi₄ h₀₁ h₁₂
      (h₂₃.trans h₃₄)).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₁, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₂, x i₃, x i₀, x i₁, x i₄} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₂) (x i₃) (x i₀) (x i₁) (x i₄) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₁) (x i₂)
    have hpq : (x i₃ ∈ A ∧ x i₄ ∈ A) ∨ (x i₃ ∈ B ∧ x i₄ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₁) = 0 ∧ f (x i₂) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₃) ∧ 0 < f (x i₄)) ∨
        (f (x i₃) < 0 ∧ f (x i₄) < 0) := by
      rcases huniform with habove | hbelow
      · right
        simpa [f] using ⟨
          cutSign_above_after hchain habove hi₀ hi₁ hi₂ hi₃ h₀₁ h₁₂ h₂₃,
          cutSign_above_after hchain habove hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄)⟩
      · left
        simpa [f] using ⟨
          cutSign_below_after hchain hbelow hi₀ hi₁ hi₂ hi₃ h₀₁ h₁₂ h₂₃,
          cutSign_below_after hchain hbelow hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄)⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₁, x i₂} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₃, x i₄, x i₀, x i₁, x i₂} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₃) (x i₄) (x i₀) (x i₁) (x i₂) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI

/-- In dimension three, it is enough to rule out intersecting convex hulls
on subconfigurations using at most five points in total.  This is the exact
finite form of the Kirchberger reduction used in the alternating-block step. -/
theorem finite_hulls_disjoint_of_five_point_witnesses
    (A B : Finset (Point 3))
    (hsmall : ∀ A' B' : Finset (Point 3), A' ⊆ A → B' ⊆ B →
      A'.card + B'.card ≤ 5 →
        Disjoint (convexHull ℝ (A' : Set (Point 3)))
          (convexHull ℝ (B' : Set (Point 3)))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  obtain ⟨A', B', hA'A, hB'B, hcard, hinter⟩ :=
    finite_kirchberger_point3 A B ⟨z, hzA, hzB⟩
  obtain ⟨z', hz'A, hz'B⟩ := hinter
  exact Set.disjoint_left.1 (hsmall A' B' hA'A hB'B hcard) hz'A hz'B

/-- Alternating-block hull separation, reduced to the only local witnesses
which can occur in `R^3`.  The above--below sign condition is used downstream
to discharge `hsmall` by its four- and five-point circuit analysis. -/
theorem alternatingBlock_hulls_disjoint_of_five_point_witnesses
    {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I) (a b c : I)
    (hsmall : ∀ A' B' : Finset (Point 3),
      A' ⊆ (firstAlternatingBlock S a b c).image x →
      B' ⊆ (secondAlternatingBlock S a b c).image x →
      A'.card + B'.card ≤ 5 →
        Disjoint (convexHull ℝ (A' : Set (Point 3)))
          (convexHull ℝ (B' : Set (Point 3)))) :
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock S a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock S a b c).image x : Set (Point 3))) :=
  finite_hulls_disjoint_of_five_point_witnesses _ _ hsmall

/-- **Pohoata--Zakharov, Corollary 2.4 (alternating-block form).**
For a five-point-or-longer projected convex chain with one uniform
above/below color, the hulls of the first-and-third and second-and-fourth
blocks are disjoint for every weakly ordered triple of cuts.

The proof applies Kirchberger in `R³`, pulls a witness of size at most five
back to chain indices, and extends it to exactly five indices.  Of the four
consecutive block colors, some color is repeated on adjacent witness
indices.  The four cases are precisely the green circuit types; the cut
plane through the other three indices excludes each of them. -/
theorem alternatingBlock_hulls_disjoint
    {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I) (a b c : I)
    (hcard : 5 ≤ S.card) (hab : a ≤ b) (hbc : b ≤ c)
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S) :
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock S a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock S a b c).image x : Set (Point 3))) := by
  classical
  have hinj : Set.InjOn x (S : Set I) := hchain.injOn (by omega)
  apply alternatingBlock_hulls_disjoint_of_five_point_witnesses x S a b c
  intro A' B' hA' hB' hwcard
  let IA := (firstAlternatingBlock S a b c).filter fun i => x i ∈ A'
  let IB := (secondAlternatingBlock S a b c).filter fun i => x i ∈ B'
  have hIAimage : IA.image x = A' := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hi).2
    · intro hp
      have hpbig := hA' hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hpbig
      exact Finset.mem_image_of_mem x (Finset.mem_filter.2 ⟨hi, hp⟩)
  have hIBimage : IB.image x = B' := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hi).2
    · intro hp
      have hpbig := hB' hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hpbig
      exact Finset.mem_image_of_mem x (Finset.mem_filter.2 ⟨hi, hp⟩)
  have hIAS : IA ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
  have hIBS : IB ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
  have hIAcard : IA.card = A'.card := by
    rw [← hIAimage]
    exact (Finset.card_image_of_injOn (hinj.mono hIAS)).symm
  have hIBcard : IB.card = B'.card := by
    rw [← hIBimage]
    exact (Finset.card_image_of_injOn (hinj.mono hIBS)).symm
  have hIAIB : Disjoint IA IB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hiA' := Finset.mem_filter.1 (Finset.mem_filter.1 hiA).1
    have hiB' := Finset.mem_filter.1 (Finset.mem_filter.1 hiB).1
    grind
  have hunionS : IA ∪ IB ⊆ S := Finset.union_subset hIAS hIBS
  have hunioncard : (IA ∪ IB).card ≤ 5 := by
    rw [Finset.card_union_of_disjoint hIAIB, hIAcard, hIBcard]
    exact hwcard
  obtain ⟨U, hsubU, hUS, hUcard⟩ :=
    Finset.exists_subsuperset_card_eq hunionS hunioncard hcard
  let e : Fin 5 ↪o I := U.orderEmbOfFin hUcard
  have heU (r : Fin 5) : e r ∈ U := U.orderEmbOfFin_mem hUcard r
  have heS (r : Fin 5) : e r ∈ S := hUS (heU r)
  have he₀₁ : e 0 < e 1 := e.strictMono (by omega)
  have he₁₂ : e 1 < e 2 := e.strictMono (by omega)
  have he₂₃ : e 2 < e 3 := e.strictMono (by omega)
  have he₃₄ : e 3 < e 4 := e.strictMono (by omega)
  have hfive := five_ordered_alternatingBlock_hulls_disjoint hab hbc hchain huniform hinj
    (heS 0) (heS 1) (heS 2) (heS 3) (heS 4) he₀₁ he₁₂ he₂₃ he₃₄
  have hUeq : ({e 0, e 1, e 2, e 3, e 4} : Finset I) = U := by
    ext i
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> exact heU _
    · intro hi
      have hirange : i ∈ Set.range e := by
        have hrange : Set.range e = (U : Set I) := by
          simpa only [e] using U.range_orderEmbOfFin hUcard
        rw [hrange]
        exact hi
      obtain ⟨r, rfl⟩ := hirange
      fin_cases r <;> simp
  rw [hUeq] at hfive
  have hIAU : IA ⊆ firstAlternatingBlock U a b c := by
    intro i hi
    have hiData := Finset.mem_filter.1 hi
    have hiBlock := Finset.mem_filter.1 hiData.1
    exact Finset.mem_filter.2 ⟨hsubU (Finset.mem_union_left IB hi), hiBlock.2⟩
  have hIBU : IB ⊆ secondAlternatingBlock U a b c := by
    intro i hi
    have hiData := Finset.mem_filter.1 hi
    have hiBlock := Finset.mem_filter.1 hiData.1
    exact Finset.mem_filter.2 ⟨hsubU (Finset.mem_union_right IA hi), hiBlock.2⟩
  have hA'sub : A' ⊆ (firstAlternatingBlock U a b c).image x := by
    rw [← hIAimage]
    exact Finset.image_mono x hIAU
  have hB'sub : B' ⊆ (secondAlternatingBlock U a b c).image x := by
    rw [← hIBimage]
    exact Finset.image_mono x hIBU
  exact hfive.mono (convexHull_mono (by exact hA'sub))
    (convexHull_mono (by exact hB'sub))

end

end

/-! ### Upstream module `JSP527/External/Erdos651/PositiveFraction.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The planar positive-fraction configuration

This file records the exact robust-transversal output used in the
Pohoata--Zakharov argument.  A configuration consists of `k` disjoint cells
inside the original planar set; every cell contains the stated
`2^(-40*k)` fraction, and every transversal is in convex position.
-/

open _root_.Set
noncomputable section

/-- The integral form of the density `|X_i| >= 2^(-40*k) |X|`.
It avoids any rounding convention: over the naturals this is exactly
`|X| <= 2^(40*k) * |X_i|`. -/
def HasPositiveFractionDensity (k : ℕ) (X A : Finset (Point 2)) : Prop :=
  X.card ≤ 2 ^ (40 * k) * A.card

def planarClusterUnion {k : ℕ} (cell : Fin k → Finset (Point 2))
    (I : Finset (Fin k)) : Finset (Point 2) :=
  I.biUnion cell

/-- Source-correct strong convex position: the hull of each whole cell is
disjoint from the hull of the union of all other whole cells. -/
def StrongConvexPositionPlanarCells {k : ℕ}
    (cell : Fin k → Finset (Point 2)) : Prop :=
  ∀ i,
    Disjoint
      (convexHull ℝ ((cell i : Finset (Point 2)) : Set (Point 2)))
      (convexHull ℝ
        ((planarClusterUnion cell (Finset.univ.erase i) :
          Finset (Point 2)) : Set (Point 2)))

/-- A robust convex `k`-clustering of a planar point set. -/
structure PositiveFractionConfiguration (k : ℕ) (X : Finset (Point 2)) where
  cell : Fin k → Finset (Point 2)
  cell_subset : ∀ i, cell i ⊆ X
  cell_disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (cell i) (cell j)
  cell_dense : ∀ i, HasPositiveFractionDensity k X (cell i)
  transversal_convex : ∀ p : Fin k → Point 2,
    (∀ i, p i ∈ cell i) → InConvexPosition (Finset.univ.image p)

/-- The source-correct strengthened output retained for the three-dimensional
Pohoata--Zakharov assembly. -/
structure StrongPositiveFractionConfiguration (k : ℕ)
    (X : Finset (Point 2)) extends PositiveFractionConfiguration k X where
  strong_convex : StrongConvexPositionPlanarCells cell

/-- Pairwise-disjoint cells separated by strict convex half-spaces give the
robust-transversal conclusion.  This is the final geometric step of the
Pór--Valtr support-region argument. -/
lemma transversal_convex_of_cell_separators {k : ℕ}
    (cell : Fin k → Finset (Point 2))
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (cell i) (cell j))
    (f : Fin k → Point 2 → ℝ)
    (hconv : ∀ i, Convex ℝ {z | 0 < f i z})
    (hneg : ∀ i, ∀ z ∈ cell i, f i z < 0)
    (hpos : ∀ i j, i ≠ j → ∀ z ∈ cell j, 0 < f i z)
    (p : Fin k → Point 2) (hp : ∀ i, p i ∈ cell i) :
    InConvexPosition (Finset.univ.image p) := by
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj hne)) (hp i) (by simpa [hij] using hp j)
  intro z hzY hzHull
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzY
  have hsubset :
      (↑((Finset.univ.image p).erase (p i)) : Set (Point 2)) ⊆
        {z | 0 < f i z} := by
    intro w hw
    have hw' := Finset.mem_erase.mp hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw'.2
    have hij : i ≠ j := fun h => hw'.1 (congrArg p h).symm
    exact hpos i j hij (p j) (hp j)
  have hipos : p i ∈ {z | 0 < f i z} :=
    convexHull_min hsubset (hconv i) hzHull
  exact (not_lt_of_ge (le_of_lt (hneg i (p i) (hp i)))) hipos

/-! ## Oriented support wedges -/

/-- The determinant of two vectors in the coordinate plane. -/
def det2 (u v : Point 2) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Signed oriented distance, up to a positive scale, from the directed line
`ab`.  Pór--Valtr support wedges are intersections of strict sign conditions
for these functions. -/
def supportValue (σ : ℝ) (a b z : Point 2) : ℝ :=
  σ * det2 (b - a) (z - a)

/-- The open Pór--Valtr support cell at edge `i` of an oriented supporting
polygon. Its own edge sees the point on the negative side and every other
supporting edge sees it on the positive side. -/
def SupportCell {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2) (i : Fin m) :
    Set (Point 2) :=
  {z | supportValue σ (edgeStart i) (edgeEnd i) z < 0 ∧
    ∀ j : Fin m, j ≠ i →
      0 < supportValue σ (edgeStart j) (edgeEnd j) z}

/-- A generic linear coordinate used to put a finite planar set in
left-to-right order. -/
def genericCoordinate (t : ℝ) (p : Point 2) : ℝ := p 0 + t * p 1

/-- The shear realizing `genericCoordinate` as the first coordinate. -/
def genericShearLinearEquiv (t : ℝ) : Point 2 ≃ₗ[ℝ] Point 2 where
  toFun p := WithLp.toLp 2 ![p 0 + t * p 1, p 1]
  invFun p := WithLp.toLp 2 ![p 0 - t * p 1, p 1]
  left_inv p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  right_inv p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  map_add' p q := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring

def genericShear (t : ℝ) : Point 2 ≃ᵃ[ℝ] Point 2 :=
  (genericShearLinearEquiv t).toAffineEquiv

@[simp] lemma planeX_genericShear (t : ℝ) (p : Point 2) :
    planeX (genericShear t p) = genericCoordinate t p := by
  simp [genericShear, genericShearLinearEquiv, planeX, genericCoordinate]

/-! The two orientations used below are represented by a bit.  Keeping the
bit in the finite support-frame type is what gives exactly the factor `2` in
the incidence count. -/
def pvSigma (upper : Bool) : ℝ := if upper then 1 else -1

@[simp] lemma pvSigma_true : pvSigma true = 1 := rfl
@[simp] lemma pvSigma_false : pvSigma false = -1 := rfl

/-- Coordinate form of collinearity in the plane.  This is deliberately
stated for `Point 2`, so the strictness supplied by general position can be
fed directly into the support-value inequalities. -/
lemma collinear_iff_det2_eq_zero (a b c : Point 2) :
    Collinear ℝ ({a, b, c} : Set (Point 2)) ↔ det2 (b - a) (c - a) = 0 := by
  rw [collinear_iff_of_mem
    (show a ∈ ({a, b, c} : Set (Point 2)) by simp)]
  constructor
  · rintro ⟨v, hv⟩
    rcases hv b (by simp) with ⟨r₂, hr₂⟩
    rcases hv c (by simp) with ⟨r₃, hr₃⟩
    have hx₂ : b 0 - a 0 = r₂ * v 0 := by
      have h := congrArg (fun p : Point 2 => p 0) hr₂
      simp at h
      linarith
    have hy₂ : b 1 - a 1 = r₂ * v 1 := by
      have h := congrArg (fun p : Point 2 => p 1) hr₂
      simp at h
      linarith
    have hx₃ : c 0 - a 0 = r₃ * v 0 := by
      have h := congrArg (fun p : Point 2 => p 0) hr₃
      simp at h
      linarith
    have hy₃ : c 1 - a 1 = r₃ * v 1 := by
      have h := congrArg (fun p : Point 2 => p 1) hr₃
      simp at h
      linarith
    simp only [det2, PiLp.sub_apply]
    rw [hx₂, hy₂, hx₃, hy₃]
    ring
  · intro hdet
    by_cases hx : b 0 - a 0 = 0
    · by_cases hy : b 1 - a 1 = 0
      · refine ⟨c - a, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with hpa | hpb | hpc
        · subst p
          refine ⟨0, by simp⟩
        · subst p
          refine ⟨0, ?_⟩
          apply PiLp.ext
          intro i
          fin_cases i
          · simpa using sub_eq_zero.mp hx
          · simpa using sub_eq_zero.mp hy
        · subst p
          refine ⟨1, by simp⟩
      · have hx₃ : c 0 - a 0 = 0 := by
          have hprod : (b 1 - a 1) * (c 0 - a 0) = 0 := by
            have hneg : -((b 1 - a 1) * (c 0 - a 0)) = 0 := by
              simpa [det2, hx] using hdet
            exact neg_eq_zero.mp hneg
          exact (mul_eq_zero.mp hprod).resolve_left hy
        refine ⟨b - a, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with hpa | hpb | hpc
        · subst p
          refine ⟨0, by simp⟩
        · subst p
          refine ⟨1, by simp⟩
        · subst p
          refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
          apply PiLp.ext
          intro i
          fin_cases i
          · simp [AffineMap.lineMap_apply, vsub_eq_sub, hx, hx₃]
            linarith
          · simp [AffineMap.lineMap_apply, vsub_eq_sub]
            field_simp [hy]
            linarith
    · refine ⟨b - a, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpa | hpb | hpc
      · subst p
        refine ⟨0, by simp⟩
      · subst p
        refine ⟨1, by simp⟩
      · subst p
        refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
        have hy₃ : c 1 - a 1 =
            ((c 0 - a 0) / (b 0 - a 0)) * (b 1 - a 1) := by
          simp only [det2, PiLp.sub_apply] at hdet
          field_simp [hx]
          nlinarith
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [AffineMap.lineMap_apply, vsub_eq_sub]
          field_simp [hx]
          linarith
        · simp [AffineMap.lineMap_apply, vsub_eq_sub]
          linarith [hy₃]

/-- General position gives the strict determinant alternative for every
three distinct members. -/
lemma det2_ne_zero_of_generalPosition {X : Finset (Point 2)}
    (hgp : InGeneralPosition 2 X) {a b c : Point 2}
    (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det2 (b - a) (c - a) ≠ 0 := by
  let p : Fin 3 → Point 2 := ![a, b, c]
  have hp_inj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  let S : Finset (Point 2) := Finset.univ.image p
  have hSX : S ⊆ X := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i <;> simpa [p]
  have hScard : S.card = 2 + 1 := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hp_inj.injOn]
    simp
  have hAI := hgp S hSX hScard
  let e : Fin 3 ↪ S :=
    ⟨fun i => ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩,
      fun i j hij => hp_inj (Subtype.ext_iff.mp hij)⟩
  have hcomp := hAI.comp_embedding e
  have hpAI : AffineIndependent ℝ p := by
    have heq : (fun i : Fin 3 ↦ ((e i : S) : Point 2)) = p := by
      rfl
    rw [← heq]
    exact hcomp
  have hncol : ¬ Collinear ℝ ({a, b, c} : Set (Point 2)) := by
    exact affineIndependent_iff_not_collinear_set.mp (by simpa [p] using hpAI)
  exact fun hzero => hncol ((collinear_iff_det2_eq_zero a b c).2 hzero)

/-- The orientation colouring of four points in increasing first-coordinate
order is transitive. -/
lemma supportValue_transitive (upper : Bool) {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : 0 < supportValue (pvSigma upper) a b c)
    (hbcd : 0 < supportValue (pvSigma upper) b c d) :
    0 < supportValue (pvSigma upper) a b d ∧
      0 < supportValue (pvSigma upper) a c d := by
  have hA : 0 < planeX b - planeX a := sub_pos.mpr hab
  have hB : 0 < planeX c - planeX b := sub_pos.mpr hbc
  have hC : 0 < planeX d - planeX c := sub_pos.mpr hcd
  have hid₁ :
      (planeX c - planeX b) * supportValue (pvSigma upper) a b d =
        ((planeX c - planeX b) + (planeX d - planeX c)) *
            supportValue (pvSigma upper) a b c +
          (planeX b - planeX a) * supportValue (pvSigma upper) b c d := by
    simp only [supportValue, det2, planeX, PiLp.sub_apply]
    ring
  have hid₂ :
      (planeX c - planeX b) * supportValue (pvSigma upper) a c d =
        (planeX d - planeX c) * supportValue (pvSigma upper) a b c +
          ((planeX b - planeX a) + (planeX c - planeX b)) *
            supportValue (pvSigma upper) b c d := by
    simp only [supportValue, det2, planeX, PiLp.sub_apply]
    ring
  constructor
  · apply pos_of_mul_pos_right _ hB.le
    rw [hid₁]
    exact add_pos (mul_pos (add_pos hB hC) habc) (mul_pos hA hbcd)
  · apply pos_of_mul_pos_right _ hB.le
    rw [hid₂]
    exact add_pos (mul_pos hC habc) (mul_pos (add_pos hA hB) hbcd)

lemma supportValue_genericShear (t σ : ℝ) (a b c : Point 2) :
    supportValue σ (genericShear t a) (genericShear t b) (genericShear t c) =
      supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp [det2, genericShear, genericShearLinearEquiv]
  ring

lemma supportValue_transitive_generic (t : ℝ) (upper : Bool)
    {a b c d : Point 2}
    (hab : genericCoordinate t a < genericCoordinate t b)
    (hbc : genericCoordinate t b < genericCoordinate t c)
    (hcd : genericCoordinate t c < genericCoordinate t d)
    (habc : 0 < supportValue (pvSigma upper) a b c)
    (hbcd : 0 < supportValue (pvSigma upper) b c d) :
    0 < supportValue (pvSigma upper) a b d ∧
      0 < supportValue (pvSigma upper) a c d := by
  have h := supportValue_transitive upper
    (a := genericShear t a) (b := genericShear t b)
    (c := genericShear t c) (d := genericShear t d)
    (by simpa using hab) (by simpa using hbc) (by simpa using hcd)
    (by simpa only [supportValue_genericShear] using habc)
    (by simpa only [supportValue_genericShear] using hbcd)
  simpa only [supportValue_genericShear] using h

/-- For the transitive orientation colouring, a monochromatic tight path is
already monochromatic on all triples. -/
lemma adjacent_supportValue_all (t : ℝ) (upper : Bool) (q : ℕ → Point 2)
    (n : ℕ)
    (hx : ∀ i j, i < j → j < n →
      genericCoordinate t (q i) < genericCoordinate t (q j))
    (hadj : ∀ i, i + 2 < n →
      0 < supportValue (pvSigma upper) (q i) (q (i + 1)) (q (i + 2))) :
    ∀ i j l, i < j → j < l → l < n →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l) := by
  intro i j l hij hjl hln
  induction l using Nat.strong_induction_on generalizing i j with
  | h l ih =>
      have hl2 : 2 ≤ l := by omega
      have hlast : ∀ a, a < l - 1 →
          0 < supportValue (pvSigma upper) (q a) (q (l - 1)) (q l) := by
        intro a halast
        by_cases ha : a + 1 = l - 1
        · have hal : a + 2 = l := by omega
          simpa [ha, hal] using hadj a (by omega)
        · have ha' : a < l - 2 := by omega
          have hm : l - 2 < l - 1 := by omega
          have hml : l - 1 < l := by omega
          have hold : 0 < supportValue (pvSigma upper)
              (q a) (q (l - 2)) (q (l - 1)) :=
            ih (l - 1) (by omega) a (l - 2) ha' hm (by omega)
          have hadj' : 0 < supportValue (pvSigma upper)
              (q (l - 2)) (q (l - 1)) (q l) := by
            have heq1 : l - 2 + 1 = l - 1 := by omega
            have heq2 : l - 2 + 2 = l := by omega
            simpa [heq1, heq2] using hadj (l - 2) (by omega)
          exact (supportValue_transitive_generic t upper
            (hx a (l - 2) ha' (by omega))
            (hx (l - 2) (l - 1) hm (by omega))
            (hx (l - 1) l hml hln) hold hadj').2
      by_cases hj : j = l - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < l - 1 := by omega
        have hold : 0 < supportValue (pvSigma upper)
            (q i) (q j) (q (l - 1)) :=
          ih (l - 1) (by omega) i j hij hj' (by omega)
        exact (supportValue_transitive_generic t upper
          (hx i j hij (by omega))
          (hx j (l - 1) hj' (by omega))
          (hx (l - 1) l (by omega) hln) hold (hlast j hj')).1

lemma supportValue_swap_right (σ : ℝ) (a b c : Point 2) :
    supportValue σ a c b = -supportValue σ a b c := by
  unfold supportValue
  have h : det2 (c - a) (b - a) = -det2 (b - a) (c - a) := by
    simp only [det2, PiLp.sub_apply]
    ring
  rw [h]
  ring

lemma supportValue_swap_left (σ : ℝ) (a b c : Point 2) :
    supportValue σ b a c = -supportValue σ a b c := by
  unfold supportValue
  have h : det2 (a - b) (c - b) = -det2 (b - a) (c - a) := by
    simp only [det2, PiLp.sub_apply]
    ring
  rw [h]
  ring

lemma supportValue_rotate (σ : ℝ) (a b c : Point 2) :
    supportValue σ b c a = supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp only [det2, PiLp.sub_apply]
  ring

lemma supportValue_rotate' (σ : ℝ) (a b c : Point 2) :
    supportValue σ c a b = supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp only [det2, PiLp.sub_apply]
  ring

/-- A good `4*k`-set, with its canonical left-to-right cup/cap witness. -/
def PVGood (t : ℝ) (k : ℕ) (Q : Finset (Point 2)) : Prop :=
  ∃ upper : Bool, ∃ q : Fin (4 * k) → Point 2,
    Function.Injective q ∧ Finset.univ.image q = Q ∧
    StrictMono (genericCoordinate t ∘ q) ∧
    ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l)

/-- The finite type over which support frames are averaged.  The bit is a
duplicate incidence label; the orientation itself is recovered from the
ordered anchor tuple.  Thus there are exactly `2 * |X|^(2*k)` possible
frames while each good cup/cap is incident to two of them. -/
abbrev PVFrame (k : ℕ) (X : Finset (Point 2)) :=
  Bool × (Fin (2 * k) → ↥X)

def cyclicSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩

def pvFrameSigma {k : ℕ} {X : Finset (Point 2)}
    (hk : 2 ≤ k) (F : PVFrame k X) : ℝ :=
  if 0 < det2
      ((F.2 ⟨1, by omega⟩ : Point 2) - (F.2 ⟨0, by omega⟩ : Point 2))
      ((F.2 ⟨2, by omega⟩ : Point 2) - (F.2 ⟨0, by omega⟩ : Point 2))
    then 1 else -1

def pvFrameStart {k : ℕ} {X : Finset (Point 2)}
    (F : PVFrame k X) (i : Fin (2 * k)) : Point 2 := F.2 i

def pvFrameEnd {k : ℕ} {X : Finset (Point 2)}
    (hk : 0 < k) (F : PVFrame k X) (i : Fin (2 * k)) : Point 2 :=
  F.2 (cyclicSucc (by omega : 0 < 2 * k) i)

def pvFrameCell {k : ℕ} {X : Finset (Point 2)}
    (hk : 2 ≤ k) (F : PVFrame k X) (i : Fin (2 * k)) :
    Finset (Point 2) := by
  classical
  exact X.filter fun z => z ∈ SupportCell (pvFrameSigma hk F)
    (pvFrameStart F) (pvFrameEnd (by omega : 0 < k) F) i

/-- The data witnessing that a good cup/cap is incident to a support frame.
Keeping the actual ordered `4*k`-chain makes both the fiber injection and the
later interlaced-chord certificate lossless. -/
structure PVSupportData (t : ℝ) {k : ℕ} {X : Finset (Point 2)} (hk : 2 ≤ k)
    (Q : Finset (Point 2)) (F : PVFrame k X) where
  upper : Bool
  q : Fin (4 * k) → Point 2
  q_injective : Function.Injective q
  q_image : Finset.univ.image q = Q
  q_strictMono : StrictMono (genericCoordinate t ∘ q)
  q_orient : ∀ i j l : Fin (4 * k), i < j → j < l →
    0 < supportValue (pvSigma upper) (q i) (q j) (q l)
  frame_sigma : pvFrameSigma hk F = pvSigma upper
  anchor_even : ∀ i : Fin (2 * k),
    (F.2 i : Point 2) = q ⟨2 * i, by omega⟩
  odd_mem_cell : ∀ i : Fin (2 * k),
    q ⟨2 * i + 1, by omega⟩ ∈ pvFrameCell hk F i

def PVSupports (t : ℝ) {k : ℕ} {X : Finset (Point 2)} (hk : 2 ≤ k)
    (Q : Finset (Point 2)) (F : PVFrame k X) : Prop :=
  Nonempty (PVSupportData t hk Q F)

/-- The even vertices of an oriented `4*k`-chain support all the odd
vertices in the corresponding `2*k` open cells. -/
lemma alternating_support_cells {t : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (upper : Bool) (q : Fin (4 * k) → Point 2)
    (hx : StrictMono (genericCoordinate t ∘ q))
    (horient : ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l)) :
    let a : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i, by omega⟩
    let v : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i + 1, by omega⟩
    ∀ i, v i ∈ SupportCell (pvSigma upper) a
      (fun j => a (cyclicSucc (by omega : 0 < 2 * k) j)) i := by
  dsimp only
  intro i
  let evenIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    ⟨2 * (r : ℕ), by have := r.isLt; omega⟩
  let oddIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    ⟨2 * (r : ℕ) + 1, by have := r.isLt; omega⟩
  let nextIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    evenIdx (cyclicSucc (by omega : 0 < 2 * k) r)
  change supportValue (pvSigma upper) (q (evenIdx i)) (q (nextIdx i))
      (q (oddIdx i)) < 0 ∧
    ∀ j, j ≠ i →
      0 < supportValue (pvSigma upper) (q (evenIdx j)) (q (nextIdx j))
        (q (oddIdx i))
  constructor
  · by_cases hi : (i : ℕ) + 1 < 2 * k
    · let ip : Fin (2 * k) := ⟨(i : ℕ) + 1, hi⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) i = ip := by
        apply Fin.ext
        simp [cyclicSucc, ip, Nat.mod_eq_of_lt hi]
      have hnext : nextIdx i = evenIdx ip := by
        dsimp [nextIdx]
        rw [hsucc]
      have h := horient (evenIdx i) (oddIdx i) (evenIdx ip)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx]))
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, ip]; omega))
      rw [hnext, supportValue_swap_right]
      exact neg_lt_zero.mpr h
    · have hlast : (i : ℕ) = 2 * k - 1 := by omega
      let iz : Fin (2 * k) := ⟨0, by omega⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) i = iz := by
        apply Fin.ext
        have heq : 2 * k - 1 + 1 = 2 * k := by omega
        simp [cyclicSucc, iz, hlast, heq]
      have hnext : nextIdx i = evenIdx iz := by
        dsimp [nextIdx]
        rw [hsucc]
      have h := horient (evenIdx iz) (evenIdx i) (oddIdx i)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, iz]; omega))
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx]))
      rw [hnext, supportValue_swap_left]
      exact neg_lt_zero.mpr h
  · intro j hji
    by_cases hj : (j : ℕ) + 1 < 2 * k
    · let jp : Fin (2 * k) := ⟨(j : ℕ) + 1, hj⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) j = jp := by
        apply Fin.ext
        simp [cyclicSucc, jp, Nat.mod_eq_of_lt hj]
      have hnext : nextIdx j = evenIdx jp := by
        dsimp [nextIdx]
        rw [hsucc]
      rw [hnext]
      rcases lt_or_gt_of_ne hji with hij | hij
      · exact horient (evenIdx j) (evenIdx jp) (oddIdx i)
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, jp]))
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, jp]; omega))
      · have h := horient (oddIdx i) (evenIdx j) (evenIdx jp)
          (Fin.mk_lt_mk.mpr (by
            change 2 * (i : ℕ) + 1 < 2 * (j : ℕ)
            omega))
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, jp]))
        rw [supportValue_rotate]
        exact h
    · have hjlast : (j : ℕ) = 2 * k - 1 := by omega
      let iz : Fin (2 * k) := ⟨0, by omega⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) j = iz := by
        apply Fin.ext
        have heq : 2 * k - 1 + 1 = 2 * k := by omega
        simp [cyclicSucc, iz, hjlast, heq]
      have hnext : nextIdx j = evenIdx iz := by
        dsimp [nextIdx]
        rw [hsucc]
      rw [hnext]
      have hi : (i : ℕ) < 2 * k - 1 := by omega
      have h := horient (evenIdx iz) (oddIdx i) (evenIdx j)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, iz]))
        (Fin.mk_lt_mk.mpr (by
          change 2 * (i : ℕ) + 1 < 2 * (j : ℕ)
          omega))
      rw [supportValue_rotate']
      exact h

lemma pvFrameSigma_alternating {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (upper : Bool) (q : Fin (4 * k) → Point 2)
    (horient : ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l))
    {X : Finset (Point 2)}
    (hqX : ∀ i, q i ∈ X) (tag : Bool) :
    pvFrameSigma hk
      (tag, fun i : Fin (2 * k) =>
        (⟨q ⟨2 * i, by omega⟩, hqX _⟩ : ↥X)) = pvSigma upper := by
  let i₀ : Fin (4 * k) := ⟨0, by omega⟩
  let i₁ : Fin (4 * k) := ⟨2, by omega⟩
  let i₂ : Fin (4 * k) := ⟨4, by omega⟩
  have h := horient i₀ i₁ i₂
    (by simp [i₀, i₁]) (by simp [i₁, i₂])
  cases upper
  · have hdet : det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) < 0 := by
      simpa [supportValue, pvSigma] using h
    have hnpos : ¬ 0 < det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) := by
      exact not_lt.mpr (le_of_lt hdet)
    simp [pvFrameSigma, pvSigma, hnpos]
  · have hpos : 0 < det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) := by
      simpa [supportValue, pvSigma] using h
    simp [pvFrameSigma, pvSigma, hpos]

lemma image_even_union_image_odd {k : ℕ} (hk : 1 ≤ k)
    (q : Fin (4 * k) → Point 2) :
    (Finset.univ.image fun i : Fin (2 * k) => q ⟨2 * i, by omega⟩) ∪
        (Finset.univ.image fun i : Fin (2 * k) => q ⟨2 * i + 1, by omega⟩) =
      Finset.univ.image q := by
  ext z
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨⟨2 * i, by omega⟩, rfl⟩
    · exact ⟨⟨2 * i + 1, by omega⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one (r : ℕ) with heven | hodd
    · left
      let i : Fin (2 * k) := ⟨(r : ℕ) / 2, by omega⟩
      refine ⟨i, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [i]
      omega
    · right
      let i : Fin (2 * k) := ⟨(r : ℕ) / 2, by omega⟩
      refine ⟨i, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [i]
      omega

/-- Every good cup/cap is incident to both duplicate labels of its even
support frame. -/
lemma pvGood_supports_two_frames {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {X Q : Finset (Point 2)} (hQX : Q ⊆ X) (hgood : PVGood t k Q) :
    ∃ A : Fin (2 * k) → ↥X,
      PVSupports t hk Q (false, A) ∧ PVSupports t hk Q (true, A) := by
  classical
  obtain ⟨upper, q, hqinj, hqQ, hx, horient⟩ := hgood
  have hqX : ∀ i, q i ∈ X := by
    intro i
    apply hQX
    rw [← hqQ]
    exact Finset.mem_image_of_mem q (Finset.mem_univ i)
  let A : Fin (2 * k) → ↥X := fun i => ⟨q ⟨2 * i, by omega⟩, hqX _⟩
  let v : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i + 1, by omega⟩
  have hcells (tag : Bool) : ∀ i, v i ∈ pvFrameCell hk (tag, A) i := by
    intro i
    rw [pvFrameCell, Finset.mem_filter]
    constructor
    · exact hqX _
    · rw [pvFrameSigma_alternating (t := t) hk upper q horient hqX tag]
      change q ⟨2 * (i : ℕ) + 1, by omega⟩ ∈
        SupportCell (pvSigma upper)
          (fun j : Fin (2 * k) => q ⟨2 * (j : ℕ), by omega⟩)
          (fun j : Fin (2 * k) =>
            q ⟨2 * ((cyclicSucc (by omega : 0 < 2 * k) j) : ℕ), by
              have hj := (cyclicSucc (by omega : 0 < 2 * k) j).isLt
              omega⟩) i
      exact alternating_support_cells (show 1 ≤ k by omega) upper q hx horient i
  refine ⟨A, ?_, ?_⟩
  all_goals
    refine ⟨{
      upper := upper
      q := q
      q_injective := hqinj
      q_image := hqQ
      q_strictMono := hx
      q_orient := horient
      frame_sigma := pvFrameSigma_alternating (t := t) hk upper q horient hqX _
      anchor_even := by intro i; rfl
      odd_mem_cell := hcells _ }⟩

lemma ordered_pairwise_lt {I : List ℕ} (hI : Ordered I) : I.Pairwise (· < ·) := by
  induction I with
  | nil => simp
  | cons x tail ih =>
      cases tail with
      | nil => simp
      | cons y tail =>
          exact List.Pairwise.cons_cons_of_trans hI.1 (ih hI.2)

lemma tightPath_get_consecutive {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    {I : List ℕ} (hI : TightPath χ c I) (i : ℕ) (hi : i + 2 < I.length) :
    χ I[i] I[i + 1] I[i + 2] = c := by
  induction i generalizing I with
  | zero =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail => simpa [TightPath] using hI.1
  | succ i ih =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail =>
                  have hi' : i + 2 < (y :: z :: tail).length := by
                    simp only [List.length_cons] at hi ⊢
                    omega
                  have hh := ih hI.2 hi'
                  simpa using hh

/-- The local cups--caps witness inside every `2^(8*k)`-set. -/
lemma exists_pvGood_subset {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {X Z : Finset (Point 2)}
    (ht : Set.InjOn (genericCoordinate t) X)
    (hgp : InGeneralPosition 2 X) (hZX : Z ⊆ X)
    (hZcard : Z.card = 2 ^ (8 * k)) :
    ∃ Q ∈ X.powersetCard (4 * k), PVGood t k Q ∧ Q ⊆ Z := by
  classical
  have htZ : Set.InjOn (genericCoordinate t) Z := ht.mono hZX
  letI : LinearOrder ↥Z := LinearOrder.lift'
    (fun z : ↥Z => genericCoordinate t z) (by
      intro a b hab
      exact Subtype.ext (htZ a.property b.property hab))
  let e : Fin (2 ^ (8 * k)) ≃o ↥Z :=
    Fintype.orderIsoFinOfCardEq ↥Z (by simpa using hZcard)
  let p : ℕ → Point 2 := fun i =>
    if hi : i < 2 ^ (8 * k) then (e ⟨i, hi⟩ : Point 2) else 0
  have hp_mem : ∀ i ∈ Finset.range (2 ^ (8 * k)), p i ∈ Z := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [p, hi', e]
  have hp_strict : ∀ i j, i ∈ Finset.range (2 ^ (8 * k)) →
      j ∈ Finset.range (2 ^ (8 * k)) → i < j →
      genericCoordinate t (p i) < genericCoordinate t (p j) := by
    intro i j hi hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have he := e.strictMono (show (⟨i, hi'⟩ : Fin _) < ⟨j, hj'⟩ by exact hij)
    change genericCoordinate t (e ⟨i, hi'⟩ : Point 2) <
      genericCoordinate t (e ⟨j, hj'⟩ : Point 2) at he
    simpa [p, hi', hj'] using he
  let χ : ℕ → ℕ → ℕ → Bool := fun i j l =>
    decide (0 < supportValue 1 (p i) (p j) (p l))
  have hchoose : Nat.choose (4 * k + 4 * k - 4) (4 * k - 2) <
      (Finset.range (2 ^ (8 * k))).card := by
    have hle : Nat.choose (4 * k + 4 * k - 4) (4 * k - 2) ≤
        2 ^ (4 * k + 4 * k - 4) := Nat.choose_le_two_pow _ _
    simp only [Finset.card_range]
    exact hle.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rcases ordered_cups_caps χ (Finset.range (2 ^ (8 * k)))
      (4 * k) (4 * k) (by omega) (by omega) hchoose with hred | hblue
  all_goals
    obtain ⟨I, hordered, hIrange, hIlen, hpath⟩ := ‹HasTightPath χ _ _ _›
    let idx : Fin (4 * k) → Fin I.length := fun i =>
      ⟨i, by simpa [hIlen] using i.isLt⟩
    let q : Fin (4 * k) → Point 2 := fun i => p (I.get (idx i))
    have hIpair := ordered_pairwise_lt hordered
    have hqx : StrictMono (genericCoordinate t ∘ q) := by
      intro i j hij
      apply hp_strict
      · exact hIrange _ (List.get_mem _ _)
      · exact hIrange _ (List.get_mem _ _)
      · exact hIpair.rel_get_of_lt (show idx i < idx j by simpa [idx] using hij)
    have hqinj : Function.Injective q := by
      intro i j hij
      apply hqx.injective
      exact congrArg (genericCoordinate t) hij
    let qNat : ℕ → Point 2 := fun r =>
      if hr : r < I.length then p (I.get ⟨r, hr⟩) else 0
    have qNat_eq (r : ℕ) (hr : r < 4 * k) :
        qNat r = q ⟨r, hr⟩ := by
      have hrI : r < I.length := by simpa [hIlen] using hr
      simp [qNat, q, idx, hrI]
    let Q := Finset.univ.image q
    have hQcard : Q.card = 4 * k := by
      dsimp [Q]
      rw [Finset.card_image_iff.mpr hqinj.injOn]
      simp
    have hQZ : Q ⊆ Z := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hp_mem _ (hIrange _ (List.get_mem _ _))
    have hQX : Q ⊆ X := hQZ.trans hZX
    refine ⟨Q, Finset.mem_powersetCard.mpr ⟨hQX, hQcard⟩, ?_, hQZ⟩
  · refine ⟨true, q, hqinj, rfl, hqx, ?_⟩
    intro i j l hij hjl
    have hall := adjacent_supportValue_all t true
      qNat (4 * k)
      (by
        intro a b hab hbn
        rw [qNat_eq a (by omega), qNat_eq b hbn]
        exact hqx (show (⟨a, by omega⟩ : Fin (4 * k)) < ⟨b, hbn⟩ by exact hab))
      (by
        intro a ha
        have htight := tightPath_get_consecutive hpath a (by simpa [hIlen] using ha)
        rw [qNat_eq a (by omega), qNat_eq (a + 1) (by omega),
          qNat_eq (a + 2) ha]
        simpa [χ, q, idx] using of_decide_eq_true htight)
      i j l hij hjl l.isLt
    simpa only [qNat_eq i i.isLt, qNat_eq j j.isLt, qNat_eq l l.isLt] using hall
  · refine ⟨false, q, hqinj, rfl, hqx, ?_⟩
    have hadjneg : ∀ a, a + 2 < 4 * k →
        0 < supportValue (pvSigma false)
          (qNat a) (qNat (a + 1)) (qNat (a + 2)) := by
      intro a ha
      have htight := tightPath_get_consecutive hpath a (by simpa [hIlen] using ha)
      have haI : a < I.length := by omega
      have ha1I : a + 1 < I.length := by omega
      have ha2I : a + 2 < I.length := by omega
      have hnpos : ¬ 0 < supportValue 1
          (qNat a) (qNat (a + 1)) (qNat (a + 2)) := by
        simpa [χ, qNat, haI, ha1I, ha2I] using of_decide_eq_false htight
      let ia : Fin (4 * k) := ⟨a, by omega⟩
      let ib : Fin (4 * k) := ⟨a + 1, by omega⟩
      let ic : Fin (4 * k) := ⟨a + 2, ha⟩
      have hne : det2
          (q ib - q ia) (q ic - q ia) ≠ 0 := by
        apply det2_ne_zero_of_generalPosition hgp
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · intro heq
          exact (ne_of_lt (hqx (by simp [ia, ib])))
            (congrArg (genericCoordinate t) heq)
        · intro heq
          exact (ne_of_lt (hqx (by simp [ia, ic])))
            (congrArg (genericCoordinate t) heq)
        · intro heq
          exact (ne_of_lt (hqx (by simp [ib, ic])))
            (congrArg (genericCoordinate t) heq)
      have hne' : det2
          (qNat (a + 1) - qNat a) (qNat (a + 2) - qNat a) ≠ 0 := by
        simpa only [qNat_eq a (by omega), qNat_eq (a + 1) (by omega),
          qNat_eq (a + 2) ha, ia, ib, ic] using hne
      simp only [supportValue, pvSigma_false, neg_mul, one_mul]
      simp only [supportValue, one_mul] at hnpos
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hnpos) hne')
    intro i j l hij hjl
    have hall := adjacent_supportValue_all t false
      qNat (4 * k)
      (by
        intro a b hab hbn
        rw [qNat_eq a (by omega), qNat_eq b hbn]
        exact hqx (show (⟨a, by omega⟩ : Fin (4 * k)) < ⟨b, hbn⟩ by exact hab))
      hadjneg i j l hij hjl l.isLt
    simpa only [qNat_eq i i.isLt, qNat_eq j j.isLt, qNat_eq l l.isLt] using hall
/-- Every finite planar set admits a linear coordinate taking distinct
values on distinct points.  This is the formal version of the harmless
generic rotation at the start of the cups--caps argument. -/
lemma exists_genericCoordinate_injOn (X : Finset (Point 2)) :
    ∃ t : ℝ, Set.InjOn (genericCoordinate t) X := by
  classical
  let pairs : Finset (Point 2 × Point 2) :=
    (X.product X).filter (fun pq ↦ pq.1 ≠ pq.2 ∧ pq.1 1 ≠ pq.2 1)
  let bad : Finset ℝ := pairs.image
    (fun pq ↦ -(pq.1 0 - pq.2 0) / (pq.1 1 - pq.2 1))
  let B : ℝ := ∑ u ∈ bad, |u|
  let t : ℝ := B + 1
  have ht : t ∉ bad := by
    intro htbad
    have habs : |t| ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum
        (s := bad) (f := fun u : ℝ ↦ |u|) (fun _ _ ↦ abs_nonneg _) htbad
    have ht_le : t ≤ B := (le_abs_self t).trans habs
    dsimp [t] at ht_le
    linarith
  refine ⟨t, ?_⟩
  intro p hp q hq heq
  by_cases hy : p 1 = q 1
  · have hx : p 0 = q 0 := by
      dsimp [genericCoordinate] at heq
      rw [hy] at heq
      linarith
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hx
    · exact hy
  · have hpq : p ≠ q := by
      intro h
      exact hy (congrArg (fun z : Point 2 ↦ z 1) h)
    have hpairs : (p, q) ∈ pairs := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq, hy⟩
    have htbad : t ∈ bad := by
      rw [Finset.mem_image]
      exact ⟨(p, q), hpairs, by
        dsimp [genericCoordinate] at heq
        field_simp
        nlinarith⟩
    exact (ht htbad).elim

/-- The positive side of an oriented line is convex. -/
lemma supportValue_positive_convex (σ : ℝ) (a b : Point 2) :
    Convex ℝ {z | 0 < supportValue σ a b z} := by
  let L : Point 2 →ₗ[ℝ] ℝ :=
    { toFun := fun z => σ * det2 (b - a) z
      map_add' := by
        intro x y
        simp [det2]
        ring
      map_smul' := by
        intro c x
        simp [det2]
        ring }
  have hL (z : Point 2) : supportValue σ a b z = L z - L a := by
    simp [supportValue, L, det2]
    ring
  have hlinear : IsLinearMap ℝ (L : Point 2 → ℝ) :=
    LinearMap.isLinearMap_of_compatibleSMul ℝ L
  simpa only [hL, sub_pos] using convex_halfSpace_gt hlinear (L a)

lemma supportValue_negative_convex (σ : ℝ) (a b : Point 2) :
    Convex ℝ {z | supportValue σ a b z < 0} := by
  have h := supportValue_positive_convex (-σ) a b
  simpa [supportValue] using h

lemma supportCell_disjoint {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (SupportCell σ edgeStart edgeEnd i)
      (SupportCell σ edgeStart edgeEnd j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact (not_lt_of_ge (le_of_lt (hzj.2 i hij))) hzi.1

lemma supportValue_lineMap (σ : ℝ) (a b x y : Point 2) (t : ℝ) :
    supportValue σ a b (AffineMap.lineMap x y t) =
      (1 - t) * supportValue σ a b x + t * supportValue σ a b y := by
  simp [supportValue, det2, AffineMap.lineMap_apply, vsub_eq_sub]
  ring

lemma supportCell_convex {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2) (i : Fin m) :
    Convex ℝ (SupportCell σ edgeStart edgeEnd i) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  constructor
  · exact (convex_iff_add_mem.mp
      (supportValue_negative_convex σ (edgeStart i) (edgeEnd i)))
        hx.1 hy.1 ha hb hab
  · intro j hji
    exact (convex_iff_add_mem.mp
      (supportValue_positive_convex σ (edgeStart j) (edgeEnd j)))
        (hx.2 j hji) (hy.2 j hji) ha hb hab

/-- Three distinct support cells contain no collinear transversal, including
points in the convex open cells rather than only points of the finite set. -/
lemma det2_ne_zero_of_mem_supportCells {m : ℕ} {σ : ℝ}
    {edgeStart edgeEnd : Fin m → Point 2} {i j l : Fin m}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {a b c : Point 2}
    (ha : a ∈ SupportCell σ edgeStart edgeEnd i)
    (hb : b ∈ SupportCell σ edgeStart edgeEnd j)
    (hc : c ∈ SupportCell σ edgeStart edgeEnd l) :
    det2 (b - a) (c - a) ≠ 0 := by
  have hab : a ≠ b := by
    intro h
    subst b
    linarith [ha.1, hb.2 i hij]
  have hac : a ≠ c := by
    intro h
    subst c
    linarith [ha.1, hc.2 i hil]
  intro hdet
  have contradiction_of_line (r : ℝ)
      (hline : c = AffineMap.lineMap a b r) : False := by
    by_cases hr0 : r ≤ 0
    · have hid := supportValue_lineMap σ (edgeStart i) (edgeEnd i) a b r
      rw [← hline] at hid
      have hfirst : (1 - r) * supportValue σ (edgeStart i) (edgeEnd i) a < 0 :=
        mul_neg_of_pos_of_neg (by linarith) ha.1
      have hsecond : r * supportValue σ (edgeStart i) (edgeEnd i) b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hr0 (hb.2 i hij).le
      linarith [hc.2 i hil]
    · by_cases hr1 : 1 ≤ r
      · have hid := supportValue_lineMap σ (edgeStart j) (edgeEnd j) a b r
        rw [← hline] at hid
        have hfirst : (1 - r) * supportValue σ (edgeStart j) (edgeEnd j) a ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (ha.2 j hij.symm).le
        have hsecond : r * supportValue σ (edgeStart j) (edgeEnd j) b < 0 :=
          mul_neg_of_pos_of_neg (by linarith) hb.1
        linarith [hc.2 j hjl]
      · have hid := supportValue_lineMap σ (edgeStart l) (edgeEnd l) a b r
        rw [← hline] at hid
        have hfirst : 0 < (1 - r) * supportValue σ (edgeStart l) (edgeEnd l) a :=
          mul_pos (by linarith) (ha.2 l hil.symm)
        have hsecond : 0 < r * supportValue σ (edgeStart l) (edgeEnd l) b :=
          mul_pos (by linarith) (hb.2 l hjl.symm)
        linarith [hc.1]
  by_cases hx : b 0 - a 0 = 0
  · have hy : b 1 - a 1 ≠ 0 := by
      intro hy
      apply hab
      apply PiLp.ext
      intro r
      fin_cases r <;> simp_all <;> linarith
    let r := (c 1 - a 1) / (b 1 - a 1)
    apply contradiction_of_line r
    apply PiLp.ext
    intro q
    fin_cases q
    · have hx' : c 0 - a 0 = 0 := by
        simp only [det2, PiLp.sub_apply, hx, zero_mul, zero_sub] at hdet
        have hp : (b 1 - a 1) * (c 0 - a 0) = 0 := neg_eq_zero.mp hdet
        exact (mul_eq_zero.mp hp).resolve_left hy
      simp [r, AffineMap.lineMap_apply, vsub_eq_sub, hx]
      linarith [hx']
    · simp [r, AffineMap.lineMap_apply, vsub_eq_sub]
      field_simp [hy]
      ring
  · let r := (c 0 - a 0) / (b 0 - a 0)
    apply contradiction_of_line r
    have hy : c 1 - a 1 = r * (b 1 - a 1) := by
      dsimp [r]
      simp only [det2, PiLp.sub_apply] at hdet
      field_simp [hx]
      nlinarith
    apply PiLp.ext
    intro q
    fin_cases q
    · simp [r, AffineMap.lineMap_apply, vsub_eq_sub]
      field_simp [hx]
      ring
    · simp [AffineMap.lineMap_apply, vsub_eq_sub]
      linarith [hy]

/-- Moving the third point inside one convex support cell cannot change the
orientation of a transversal triple. -/
lemma supportValue_transport_third {m : ℕ} {σ : ℝ} (hσ : σ ≠ 0)
    {edgeStart edgeEnd : Fin m → Point 2} {i j l : Fin m}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {a b c c' : Point 2}
    (ha : a ∈ SupportCell σ edgeStart edgeEnd i)
    (hb : b ∈ SupportCell σ edgeStart edgeEnd j)
    (hc : c ∈ SupportCell σ edgeStart edgeEnd l)
    (hc' : c' ∈ SupportCell σ edgeStart edgeEnd l)
    (hpos : 0 < supportValue σ a b c) :
    0 < supportValue σ a b c' := by
  have hdet' := det2_ne_zero_of_mem_supportCells hij hil hjl ha hb hc'
  have hsv' : supportValue σ a b c' ≠ 0 := by
    simpa only [supportValue] using mul_ne_zero hσ hdet'
  by_contra hnpos
  have hneg : supportValue σ a b c' < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hsv'
  let s := supportValue σ a b c /
    (supportValue σ a b c - supportValue σ a b c')
  have hden : 0 < supportValue σ a b c - supportValue σ a b c' := by linarith
  have hs0 : 0 < s := div_pos hpos hden
  have hs1 : s < 1 := by
    rw [div_lt_one hden]
    linarith
  let z := AffineMap.lineMap c c' s
  have hzcell : z ∈ SupportCell σ edgeStart edgeEnd l :=
    (supportCell_convex σ edgeStart edgeEnd l).lineMap_mem hc hc' ⟨hs0.le, hs1.le⟩
  have hzero : supportValue σ a b z = 0 := by
    rw [show supportValue σ a b z =
      (1 - s) * supportValue σ a b c + s * supportValue σ a b c' by
        exact supportValue_lineMap σ a b c c' s]
    dsimp [s]
    field_simp [ne_of_gt hden]
    ring
  have hdetz := det2_ne_zero_of_mem_supportCells hij hil hjl ha hb hzcell
  exact hdetz ((mul_eq_zero.mp hzero).resolve_left hσ)

/-- Strong output together with the increasing cyclic support-edge labels
used to form its cells. -/
structure OrderedStrongPositiveFractionConfiguration (k : ℕ)
    (X : Finset (Point 2))
    extends StrongPositiveFractionConfiguration k X where
  supportSize : ℕ
  supportSize_pos : 0 < supportSize
  supportIndex : Fin k → Fin supportSize
  supportIndex_strictMono : StrictMono supportIndex
  supportSigma : ℝ
  supportSigma_ne_zero : supportSigma ≠ 0
  supportStart : Fin supportSize → Point 2
  supportEnd : Fin supportSize → Point 2
  cell_support_sign : ∀ i, ∀ z ∈ cell i,
    z ∈ SupportCell supportSigma supportStart supportEnd (supportIndex i)
  representative : Fin k → Point 2
  representative_mem : ∀ i, representative i ∈ cell i
  representative_orient : ∀ i j l : Fin k, i < j → j < l →
    0 < supportValue supportSigma
      (representative i) (representative j) (representative l)

/-- Every transversal has the cyclic orientation fixed by the retained
cup/cap representative, even after the cells are shrunk. -/
theorem OrderedStrongPositiveFractionConfiguration.transversal_orient
    {k : ℕ} {X : Finset (Point 2)}
    (C : OrderedStrongPositiveFractionConfiguration k X)
    (p : Fin k → Point 2) (hp : ∀ i, p i ∈ C.cell i) :
    ∀ i j l : Fin k, i < j → j < l →
      0 < supportValue C.supportSigma (p i) (p j) (p l) := by
  intro i j l hij hjl
  have hidx_ij : C.supportIndex i ≠ C.supportIndex j :=
    ne_of_lt (C.supportIndex_strictMono hij)
  have hidx_il : C.supportIndex i ≠ C.supportIndex l :=
    ne_of_lt (C.supportIndex_strictMono (hij.trans hjl))
  have hidx_jl : C.supportIndex j ≠ C.supportIndex l :=
    ne_of_lt (C.supportIndex_strictMono hjl)
  have hri := C.cell_support_sign i (C.representative i) (C.representative_mem i)
  have hrj := C.cell_support_sign j (C.representative j) (C.representative_mem j)
  have hrl := C.cell_support_sign l (C.representative l) (C.representative_mem l)
  have hpi := C.cell_support_sign i (p i) (hp i)
  have hpj := C.cell_support_sign j (p j) (hp j)
  have hpl := C.cell_support_sign l (p l) (hp l)
  have h₁ : 0 < supportValue C.supportSigma
      (C.representative i) (C.representative j) (p l) :=
    supportValue_transport_third C.supportSigma_ne_zero
      hidx_ij hidx_il hidx_jl hri hrj hrl hpl
      (C.representative_orient i j l hij hjl)
  have h₂rot : 0 < supportValue C.supportSigma
      (p l) (C.representative i) (p j) := by
    apply supportValue_transport_third C.supportSigma_ne_zero
      hidx_il.symm hidx_jl.symm hidx_ij hpl hri hrj hpj
    rw [supportValue_rotate']
    exact h₁
  have h₂ : 0 < supportValue C.supportSigma
      (C.representative i) (p j) (p l) := by
    rw [supportValue_rotate]
    exact h₂rot
  have h₃rot : 0 < supportValue C.supportSigma (p j) (p l) (p i) := by
    apply supportValue_transport_third C.supportSigma_ne_zero
      hidx_jl hidx_ij.symm hidx_il.symm hpj hpl hri hpi
    rw [supportValue_rotate]
    exact h₂
  rw [supportValue_rotate] at h₃rot
  exact h₃rot

/-- Four points with one strict orientation on all increasing triples have
crossing interlaced open segments. -/
lemma interlaced_planar_segments_cross {σ : ℝ} {a b c d : Point 2}
    (habc : 0 < supportValue σ a b c)
    (habd : 0 < supportValue σ a b d)
    (hacd : 0 < supportValue σ a c d)
    (hbcd : 0 < supportValue σ b c d) :
    ∃ t u : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1 ∧
      AffineMap.lineMap a c t = AffineMap.lineMap b d u := by
  let A := supportValue σ a b d
  let C := supportValue σ a b c
  let S := supportValue σ a b c + supportValue σ a c d
  have hA : 0 < A := habd
  have hC : 0 < C := habc
  have hS : 0 < S := by dsimp [S]; linarith
  have hSA : S - A = supportValue σ b c d := by
    dsimp [S, A]
    simp [supportValue, det2]
    ring
  have hSC : S - C = supportValue σ a c d := by
    dsimp [S, C]
    ring
  refine ⟨A / S, C / S, ⟨div_pos hA hS, ?_⟩,
    ⟨div_pos hC hS, ?_⟩, ?_⟩
  · rw [div_lt_one hS]
    linarith
  · rw [div_lt_one hS]
    linarith
  · apply PiLp.ext
    intro i
    fin_cases i <;>
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    all_goals
      dsimp [A, C, S]
      field_simp [ne_of_gt hS]
      simp [supportValue, det2]
      ring

/-- The ordered planar representatives in a positive-fraction package give
the exact projected-chain predicate after any lift whose four-tuples are
affinely independent. -/
theorem OrderedStrongPositiveFractionConfiguration.isProjectedConvexChain
    {k : ℕ} {X : Finset (Point 2)}
    (C : OrderedStrongPositiveFractionConfiguration k X)
    (x : Fin k → Point 3)
    (hproj : ∀ i, verticalProjection (x i) ∈ C.cell i)
    (hAI : ∀ i₀ i₁ i₂ i₃ : Fin k,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
      AffineIndependent ℝ ![x i₀, x i₁, x i₂, x i₃]) :
    IsProjectedConvexChain x Finset.univ := by
  intro i₀ _ i₁ _ i₂ _ i₃ _ h01 h12 h23
  refine ⟨hAI i₀ i₁ i₂ i₃ h01 h12 h23, ?_⟩
  let p : Fin k → Point 2 := fun i => verticalProjection (x i)
  obtain ⟨t, u, ht, hu, hcross⟩ := interlaced_planar_segments_cross
    (C.transversal_orient p hproj i₀ i₁ i₂ h01 h12)
    (C.transversal_orient p hproj i₀ i₁ i₃ h01 (h12.trans h23))
    (C.transversal_orient p hproj i₀ i₂ i₃ (h01.trans h12) h23)
    (C.transversal_orient p hproj i₁ i₂ i₃ h12 h23)
  refine ⟨t, u, ht, hu, ?_⟩
  have hline (p q : Point 3) (r : ℝ) :
      verticalProjection (segmentPoint p q r) =
        AffineMap.lineMap (verticalProjection p) (verticalProjection q) r := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply,
        vsub_eq_sub]
  rw [hline, hline]
  simpa only [p] using hcross

/-- The support signs separate the convex hull of each entire cell from the
hull of all other entire cells.  This is the source's strong family-convexity
property, stronger than merely checking transversals. -/
lemma strongConvexPositionPlanarCells_of_supportSigns {k : ℕ}
    (cell : Fin k → Finset (Point 2))
    (σ : ℝ) (edgeStart edgeEnd : Fin k → Point 2)
    (hsign : ∀ i, ∀ z ∈ cell i,
      z ∈ SupportCell σ edgeStart edgeEnd i) :
    StrongConvexPositionPlanarCells cell := by
  intro i
  rw [Set.disjoint_left]
  intro z hzi hzothers
  let f : Point 2 → ℝ := supportValue σ (edgeStart i) (edgeEnd i)
  have hown : (↑(cell i) : Set (Point 2)) ⊆ {w | f w < 0} := by
    intro w hw
    exact (hsign i w hw).1
  have hzneg : f z < 0 :=
    convexHull_min hown (by
      simpa [f] using supportValue_negative_convex σ (edgeStart i) (edgeEnd i)) hzi
  have hother :
      (↑(planarClusterUnion cell (Finset.univ.erase i)) : Set (Point 2)) ⊆
        {w | 0 < f w} := by
    intro w hw
    simp only [planarClusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hw
    obtain ⟨j, hj, hwj⟩ := hw
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact (hsign j w hwj).2 i hji.symm
  have hzpos : 0 < f z :=
    convexHull_min hother (by
      simpa [f] using supportValue_positive_convex σ (edgeStart i) (edgeEnd i)) hzothers
  linarith

/-- The finite output of the support-region counting argument.  Unlike the
usual picture of the regions, this records only their affine sign pattern,
which is exactly what is needed for robust convexity. -/
structure PositiveFractionSupportFrame (k : ℕ) (X : Finset (Point 2)) where
  sigma : ℝ
  edgeStart : Fin k → Point 2
  edgeEnd : Fin k → Point 2
  cell : Fin k → Finset (Point 2)
  cell_subset : ∀ i, cell i ⊆ X
  cell_dense : ∀ i, HasPositiveFractionDensity k X (cell i)
  cell_sign : ∀ i, ∀ z ∈ cell i,
    z ∈ SupportCell sigma edgeStart edgeEnd i

/-- Strict support-region sign certificates produce a positive-fraction
configuration.  Thus all geometry after the Pór--Valtr incidence count is
contained in this short lemma. -/
def PositiveFractionSupportFrame.toConfiguration {k : ℕ}
    {X : Finset (Point 2)} (F : PositiveFractionSupportFrame k X) :
    PositiveFractionConfiguration k X where
  cell := F.cell
  cell_subset := F.cell_subset
  cell_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hzi' := F.cell_sign i z hzi
    have hzj' := F.cell_sign j z hzj
    exact Set.disjoint_left.mp
      (supportCell_disjoint F.sigma F.edgeStart F.edgeEnd hij) hzi' hzj'
  cell_dense := F.cell_dense
  transversal_convex := by
    intro p hp
    apply transversal_convex_of_cell_separators F.cell
      (fun {i j} hij => by
        rw [Finset.disjoint_left]
        intro z hzi hzj
        exact Set.disjoint_left.mp
          (supportCell_disjoint F.sigma F.edgeStart F.edgeEnd hij)
          (F.cell_sign _ _ hzi) (F.cell_sign _ _ hzj))
      (fun i z => supportValue F.sigma (F.edgeStart i) (F.edgeEnd i) z)
      (fun i => supportValue_positive_convex _ _ _)
      (fun i z hz => (F.cell_sign i z hz).1)
      (fun i j hij z hz => (F.cell_sign j z hz).2 i hij)
      p hp

def PositiveFractionSupportFrame.toStrongConfiguration {k : ℕ}
    {X : Finset (Point 2)} (F : PositiveFractionSupportFrame k X) :
    StrongPositiveFractionConfiguration k X where
  toPositiveFractionConfiguration := F.toConfiguration
  strong_convex := strongConvexPositionPlanarCells_of_supportSigns
    F.cell F.sigma F.edgeStart F.edgeEnd F.cell_sign

/-! ## Finite incidence counting -/

/-- Double-counting local witnesses inside all `m`-subsets gives the usual
supersaturation inequality. -/
theorem supersaturation_double_count
    {α : Type*} [DecidableEq α]
    (X : Finset α) (m s : ℕ) (good : Finset α → Prop)
    [DecidablePred good]
    (hsm : s ≤ m) (hmX : m ≤ X.card)
    (hlocal : ∀ Z ∈ X.powersetCard m,
      ∃ Q ∈ X.powersetCard s, good Q ∧ Q ⊆ Z) :
    X.card.choose s ≤ m.choose s * ((X.powersetCard s).filter good).card := by
  classical
  let Ms := X.powersetCard m
  let Gs := (X.powersetCard s).filter good
  let inc : ℕ := ∑ Z ∈ Ms, ∑ Q ∈ Gs, if Q ⊆ Z then 1 else 0
  have hlower : Ms.card ≤ inc := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro Z hZ
    obtain ⟨Q, hQ, hgood, hQZ⟩ := hlocal Z (by simpa [Ms] using hZ)
    have hQGs : Q ∈ Gs := by simp [Gs, hQ, hgood]
    have hone := Finset.single_le_sum
      (s := Gs) (f := fun Q ↦ if Q ⊆ Z then 1 else 0)
      (fun _ _ ↦ Nat.zero_le _) hQGs
    simpa [hQZ] using hone
  have hswap : inc = ∑ Q ∈ Gs, ((Ms.filter (Q ⊆ ·)).card) := by
    dsimp [inc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Q _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hext (Q : Finset α) (hQ : Q ∈ Gs) :
      (Ms.filter (Q ⊆ ·)).card = (X.card - s).choose (m - s) := by
    have hQpow : Q ∈ X.powersetCard s := (Finset.mem_filter.mp hQ).1
    have hQX : Q ⊆ X := (Finset.mem_powersetCard.mp hQpow).1
    have hQcard : Q.card = s := (Finset.mem_powersetCard.mp hQpow).2
    simpa [Ms, hQcard] using
      Finset.card_filter_powersetCard_subset Q X m hQX
        (hQcard.trans_le hsm)
  have hinc : inc = Gs.card * (X.card - s).choose (m - s) := by
    rw [hswap]
    calc
      (∑ Q ∈ Gs, (Ms.filter (Q ⊆ ·)).card) =
          ∑ Q ∈ Gs, (X.card - s).choose (m - s) := by
            apply Finset.sum_congr rfl
            intro Q hQ
            exact hext Q hQ
      _ = Gs.card * (X.card - s).choose (m - s) := by simp
  have hraw : X.card.choose m ≤
      Gs.card * (X.card - s).choose (m - s) := by
    simpa [Ms, Finset.card_powersetCard, hinc] using hlower
  have hmul := Nat.mul_le_mul_right (m.choose s) hraw
  have hchoose : X.card.choose m * m.choose s =
      X.card.choose s * (X.card - s).choose (m - s) := Nat.choose_mul hsm
  have hextpos : 0 < (X.card - s).choose (m - s) := by
    apply Nat.choose_pos
    exact Nat.sub_le_sub_right hmX s
  have hcancel : X.card.choose s * (X.card - s).choose (m - s) ≤
      (m.choose s * Gs.card) * (X.card - s).choose (m - s) := by
    calc
      X.card.choose s * (X.card - s).choose (m - s) =
          X.card.choose m * m.choose s := hchoose.symm
      _ ≤ (Gs.card * (X.card - s).choose (m - s)) * m.choose s := hmul
      _ = (m.choose s * Gs.card) * (X.card - s).choose (m - s) := by ac_rfl
  simpa [Gs] using Nat.le_of_mul_le_mul_right hcancel hextpos

/-- Averaging a two-sided incidence relation over at most `2*N^q` frames. -/
theorem frame_incidence_averaging
    {Good Frame : Type*} [DecidableEq Good] [DecidableEq Frame]
    (G : Finset Good) (F : Finset Frame) (supports : Good → Frame → Prop)
    [DecidableRel supports]
    (ambient arity : ℕ) (hG : G.Nonempty)
    (htwo : ∀ g ∈ G, 2 ≤ (F.filter (supports g)).card)
    (hframes : F.card ≤ 2 * ambient ^ arity) :
    ∃ f ∈ F,
      G.card ≤ ambient ^ arity * (G.filter (fun g ↦ supports g f)).card := by
  classical
  let inc : ℕ := ∑ g ∈ G, ∑ f ∈ F, if supports g f then 1 else 0
  have hlower : 2 * G.card ≤ inc := by
    calc
      2 * G.card = ∑ g ∈ G, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ g ∈ G, (F.filter (supports g)).card := by
        apply Finset.sum_le_sum
        intro g hg
        exact htwo g hg
      _ = inc := by
        dsimp [inc]
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hF : F.Nonempty := by
    obtain ⟨g, hg⟩ := hG
    have hp : 0 < (F.filter (supports g)).card :=
      lt_of_lt_of_le (by norm_num) (htwo g hg)
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hp
    exact ⟨f, (Finset.mem_filter.mp hf).1⟩
  obtain ⟨f, hfF, hfmax⟩ := F.exists_max_image
    (fun f ↦ (G.filter (fun g ↦ supports g f)).card) hF
  have hswap : inc = ∑ f ∈ F, (G.filter (fun g ↦ supports g f)).card := by
    dsimp [inc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f' _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hupper : inc ≤ F.card * (G.filter (fun g ↦ supports g f)).card := by
    rw [hswap]
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul F
      (fun f' ↦ (G.filter (fun g ↦ supports g f')).card)
      ((G.filter (fun g ↦ supports g f)).card) hfmax
  refine ⟨f, hfF, ?_⟩
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by norm_num)
  calc
    2 * G.card ≤ inc := hlower
    _ ≤ F.card * (G.filter (fun g ↦ supports g f)).card := hupper
    _ ≤ (2 * ambient ^ arity) * (G.filter (fun g ↦ supports g f)).card :=
      Nat.mul_le_mul_right _ hframes
    _ = 2 * (ambient ^ arity * (G.filter (fun g ↦ supports g f)).card) := by ac_rfl

/-- Integral fourth-power form of the numerical Pór--Valtr estimate. -/
theorem density_of_pv_power_bound_le
    (k N alpha : ℕ) (hk : 0 < k) (h8 : 8 * k ≤ N)
    (hpow : ((N - 4 * k) ^ 4) ^ k ≤
      (2 ^ (32 * k) * alpha * N ^ 3) ^ k) :
    N ≤ 2 ^ (40 * k) * alpha := by
  have hbase : (N - 4 * k) ^ 4 ≤ 2 ^ (32 * k) * alpha * N ^ 3 := by
    apply Nat.le_of_not_lt
    intro hrev
    have hp := (Nat.pow_lt_pow_iff_left hk.ne').mpr hrev
    omega
  have hhalf : N ≤ 2 * (N - 4 * k) := by omega
  have hfour : N ^ 4 ≤ 16 * (N - 4 * k) ^ 4 := by
    calc
      N ^ 4 ≤ (2 * (N - 4 * k)) ^ 4 := Nat.pow_le_pow_left hhalf _
      _ = 16 * (N - 4 * k) ^ 4 := by ring
  have hwide : N ^ 4 ≤ (16 * 2 ^ (32 * k) * alpha) * N ^ 3 := by
    calc
      N ^ 4 ≤ 16 * (N - 4 * k) ^ 4 := hfour
      _ ≤ 16 * (2 ^ (32 * k) * alpha * N ^ 3) := Nat.mul_le_mul_left _ hbase
      _ = (16 * 2 ^ (32 * k) * alpha) * N ^ 3 := by ring
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < 8 * k) h8
  have hcubic : 0 < N ^ 3 := pow_pos hNpos _
  have hsmall : N ≤ 16 * 2 ^ (32 * k) * alpha := by
    apply Nat.le_of_mul_le_mul_right (c := N ^ 3) _ hcubic
    simpa only [show N * N ^ 3 = N ^ 4 by ring] using hwide
  have hscale : 16 * 2 ^ (32 * k) ≤ 2 ^ (40 * k) := by
    calc
      16 * 2 ^ (32 * k) = 2 ^ (32 * k + 4) := by ring
      _ ≤ 2 ^ (40 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hsmall.trans (Nat.mul_le_mul_right alpha hscale)

lemma eight_mul_le_two_pow_40_mul (k : ℕ) : 8 * k ≤ 2 ^ (40 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp : 1 ≤ 2 ^ (40 * k) := Nat.one_le_two_pow
      rw [Nat.mul_succ, Nat.mul_succ, Nat.pow_add]
      norm_num at ⊢
      nlinarith

/-- Splitting `2*k` natural numbers into their upper and lower halves gives
the order-statistic estimate used in the Pór--Valtr product argument. -/
theorem exists_half_order_statistic (k N : ℕ) (hk : 0 < k)
    (t : Fin (2 * k) → ℕ) (htN : ∀ i, t i ≤ N) :
    ∃ alpha : ℕ, ∃ I : Finset (Fin (2 * k)),
      I.card = k ∧ (∀ i ∈ I, alpha ≤ t i) ∧
      (∏ i, t i) ≤ alpha ^ k * N ^ k := by
  classical
  let sigma : Equiv.Perm (Fin (2 * k)) := Tuple.sort t
  let L : Finset (Fin (2 * k)) :=
    Finset.univ.filter (fun j ↦ (j : ℕ) < k)
  let H : Finset (Fin (2 * k)) :=
    Finset.univ.filter (fun j ↦ k ≤ (j : ℕ))
  let alpha := t (sigma ⟨k, by omega⟩)
  let I := H.image sigma
  have hLcard : L.card = k := by
    simpa [L, min_eq_right (by omega : k ≤ 2 * k)] using
      (Fin.card_filter_val_lt (n := 2 * k) (m := k))
  have hHcard : H.card = k := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * k))))
      (p := fun j ↦ (j : ℕ) < k)
    have hnot : (Finset.univ.filter fun j : Fin (2 * k) ↦ ¬ (j : ℕ) < k) = H := by
      ext j
      simp [H]
    rw [hnot, hLcard] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  have hdisj : Disjoint L H := by
    simp [L, H, Finset.disjoint_left]
  have hcover : L ∪ H = Finset.univ := by
    ext j
    simp [L, H]
    omega
  have hmono : Monotone (t ∘ sigma) := Tuple.monotone_sort t
  have hlow : ∀ j ∈ L, t (sigma j) ≤ alpha := by
    intro j hj
    apply hmono
    have hjlt : (j : ℕ) < k := by simpa [L] using hj
    exact Fin.mk_le_mk.mpr (by omega)
  have hlarge : ∀ j ∈ H, alpha ≤ t (sigma j) := by
    intro j hj
    apply hmono
    have hjge : k ≤ (j : ℕ) := by simpa [H] using hj
    exact Fin.mk_le_mk.mpr hjge
  have hLprod : (∏ j ∈ L, t (sigma j)) ≤ alpha ^ k := by
    calc
      (∏ j ∈ L, t (sigma j)) ≤ ∏ _j ∈ L, alpha := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ Nat.zero_le _
        · exact hlow
      _ = alpha ^ k := by simp [hLcard]
  have hHprod : (∏ j ∈ H, t (sigma j)) ≤ N ^ k := by
    calc
      (∏ j ∈ H, t (sigma j)) ≤ ∏ _j ∈ H, N := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ Nat.zero_le _
        · intro j _
          exact htN (sigma j)
      _ = N ^ k := by simp [hHcard]
  have hperm : (∏ i, t i) = ∏ j, t (sigma j) := by
    exact Finset.prod_equiv sigma.symm (fun _ ↦ by simp) (fun _ _ ↦ by simp)
  refine ⟨alpha, I, ?_, ?_, ?_⟩
  · rw [show I.card = H.card from Finset.card_image_of_injective H sigma.injective]
    exact hHcard
  · intro i hi
    simp only [I, Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact hlarge j hj
  · rw [hperm, ← hcover, Finset.prod_union hdisj]
    exact Nat.mul_le_mul hLprod hHprod

/-- The complete cardinality endgame of the Pór--Valtr proof.  The
geometric incidence argument supplies `hsuper`, `hframe`, and `hfiber`; the
last hypothesis is the elementary lower/upper-half ordering of the `2*k`
cell sizes. -/
theorem pv_cardinality_endgame
    (k N G P : ℕ) (hk : 4 ≤ k) (hN : 2 ^ (40 * k) ≤ N)
    (t : Fin (2 * k) → ℕ)
    (hsuper : N.choose (4 * k) ≤
      (2 ^ (8 * k)).choose (4 * k) * G)
    (hframe : G ≤ N ^ (2 * k) * P)
    (hfiber : P ≤ ∏ i, t i)
    (htN : ∀ i, t i ≤ N) :
    ∃ I : Finset (Fin (2 * k)), I.card = k ∧
      ∀ i ∈ I, N ≤ 2 ^ (40 * k) * t i := by
  have hkpos : 0 < k := by omega
  obtain ⟨alpha, I, hIcard, hIlarge, hprod⟩ :=
    exists_half_order_statistic k N hkpos t htN
  have h8 : 8 * k ≤ N := (eight_mul_le_two_pow_40_mul k).trans hN
  have hsubpow : (N - 4 * k) ^ (4 * k) ≤
      (4 * k).factorial * N.choose (4 * k) := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (N + 1 - 4 * k) ^ (4 * k) :=
        Nat.pow_le_pow_left (by omega) _
      _ ≤ N.descFactorial (4 * k) := Nat.pow_sub_le_descFactorial _ _
      _ = (4 * k).factorial * N.choose (4 * k) :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  have hchooseM : (4 * k).factorial * (2 ^ (8 * k)).choose (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have hgood : (N - 4 * k) ^ (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) * G := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (4 * k).factorial * N.choose (4 * k) := hsubpow
      _ ≤ (4 * k).factorial * ((2 ^ (8 * k)).choose (4 * k) * G) :=
        Nat.mul_le_mul_left _ hsuper
      _ = ((4 * k).factorial * (2 ^ (8 * k)).choose (4 * k)) * G := by ring
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * G := Nat.mul_le_mul_right G hchooseM
  have hall : (N - 4 * k) ^ (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) *
        (N ^ (2 * k) * (alpha ^ k * N ^ k)) := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (2 ^ (8 * k)) ^ (4 * k) * G := hgood
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * (N ^ (2 * k) * P) :=
        Nat.mul_le_mul_left _ hframe
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * (N ^ (2 * k) * ∏ i, t i) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfiber)
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) *
          (N ^ (2 * k) * (alpha ^ k * N ^ k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hprod)
  have hMpow : (2 ^ (8 * k)) ^ (4 * k) = (2 ^ (32 * k)) ^ k := by
    calc
      (2 ^ (8 * k)) ^ (4 * k) = 2 ^ ((8 * k) * (4 * k)) :=
        (pow_mul 2 (8 * k) (4 * k)).symm
      _ = 2 ^ ((32 * k) * k) := by congr 1 <;> ring
      _ = (2 ^ (32 * k)) ^ k := pow_mul 2 (32 * k) k
  have hNpow : N ^ (2 * k) * N ^ k = (N ^ 3) ^ k := by
    calc
      N ^ (2 * k) * N ^ k = N ^ (2 * k + k) := (pow_add N _ _).symm
      _ = N ^ (3 * k) := by congr 1 <;> omega
      _ = (N ^ 3) ^ k := pow_mul N 3 k
  have hpower : ((N - 4 * k) ^ 4) ^ k ≤
      (2 ^ (32 * k) * alpha * N ^ 3) ^ k := by
    calc
      ((N - 4 * k) ^ 4) ^ k = (N - 4 * k) ^ (4 * k) := by rw [← pow_mul]
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) *
          (N ^ (2 * k) * (alpha ^ k * N ^ k)) := hall
      _ = (2 ^ (32 * k) * alpha * N ^ 3) ^ k := by
        rw [hMpow, mul_pow, mul_pow]
        rw [← hNpow]
        ring
  have hdense : N ≤ 2 ^ (40 * k) * alpha :=
    density_of_pv_power_bound_le k N alpha hkpos h8 hpower
  refine ⟨I, hIcard, ?_⟩
  intro i hi
  exact hdense.trans (Nat.mul_le_mul_left _ (hIlarge i hi))

/-! ## Assembly of the Pór--Valtr incidence argument -/

theorem exists_orderedStrongPositiveFractionConfiguration
    (k : ℕ) (hk : 4 ≤ k) (X : Finset (Point 2))
    (hcard : 2 ^ (40 * k) ≤ X.card)
    (hgp : InGeneralPosition 2 X) :
    Nonempty (OrderedStrongPositiveFractionConfiguration k X) := by
  classical
  obtain ⟨t, ht⟩ := exists_genericCoordinate_injOn X
  let good : Finset (Point 2) → Prop := PVGood t k
  let G : Finset (Finset (Point 2)) :=
    (X.powersetCard (4 * k)).filter good
  let Frame := PVFrame k X
  let frames : Finset Frame := Finset.univ
  let supports : Finset (Point 2) → Frame → Prop :=
    PVSupports t (show 2 ≤ k by omega)
  have hm : 4 * k ≤ 2 ^ (8 * k) := by
    have h8 : 8 * k ≤ 2 ^ (8 * k) :=
      Nat.le_of_lt (8 * k).lt_two_pow_self
    omega
  have hmX : 2 ^ (8 * k) ≤ X.card := by
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 8 * k ≤ 40 * k)).trans hcard
  have hlocal : ∀ Z ∈ X.powersetCard (2 ^ (8 * k)),
      ∃ Q ∈ X.powersetCard (4 * k), good Q ∧ Q ⊆ Z := by
    intro Z hZ
    have hZX := (Finset.mem_powersetCard.mp hZ).1
    have hZcard := (Finset.mem_powersetCard.mp hZ).2
    simpa [good] using exists_pvGood_subset (t := t) (show 2 ≤ k by omega)
      ht hgp hZX hZcard
  have hsuper : X.card.choose (4 * k) ≤
      (2 ^ (8 * k)).choose (4 * k) * G.card := by
    simpa [G, good] using supersaturation_double_count X
      (2 ^ (8 * k)) (4 * k) good hm hmX hlocal
  have hGnonempty : G.Nonempty := by
    obtain ⟨Z, hZX, hZcard⟩ := Finset.exists_subset_card_eq hmX
    obtain ⟨Q, hQpow, hgood, hQZ⟩ :=
      hlocal Z (Finset.mem_powersetCard.mpr ⟨hZX, hZcard⟩)
    exact ⟨Q, by simp [G, hQpow, hgood]⟩
  have htwo : ∀ Q ∈ G, 2 ≤ (frames.filter (supports Q)).card := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    obtain ⟨A, hfalse, htrue⟩ := pvGood_supports_two_frames
      (t := t) (show 2 ≤ k by omega)
      (Finset.mem_powersetCard.mp hQdata.1).1 hQdata.2
    let f0 : Frame := (false, A)
    let f1 : Frame := (true, A)
    have hf0 : f0 ∈ frames.filter (supports Q) := by
      simp [frames, supports, f0, hfalse]
    have hf1 : f1 ∈ frames.filter (supports Q) := by
      simp [frames, supports, f1, htrue]
    have hne : f0 ≠ f1 := by
      intro h
      have hh : false = true := congrArg Prod.fst h
      simp at hh
    have hpair : ({f0, f1} : Finset Frame) ⊆ frames.filter (supports Q) := by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl <;> assumption
    simpa [hne] using Finset.card_le_card hpair
  have hframes : frames.card ≤ 2 * X.card ^ (2 * k) := by
    simp [frames, Frame, PVFrame]
  obtain ⟨F, hF, hframe⟩ := frame_incidence_averaging
    G frames supports X.card (2 * k) hGnonempty htwo hframes
  let fiber : Finset (Finset (Point 2)) := G.filter (fun Q => supports Q F)
  have hfiber_nonempty : fiber.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hz : fiber.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hz' : (G.filter fun Q => supports Q F).card = 0 := by
      simpa [fiber] using hz
    rw [hz', Nat.mul_zero] at hframe
    have hGpos : 0 < G.card := hGnonempty.card_pos
    omega
  obtain ⟨Q₀, hQ₀⟩ := hfiber_nonempty
  let W : PVSupportData t (show 2 ≤ k by omega) Q₀ F :=
    Classical.choice (show supports Q₀ F by
      have hQ₀' : Q₀ ∈ G.filter (fun Q => supports Q F) := by
        simpa only [fiber] using hQ₀
      exact (Finset.mem_filter.mp hQ₀').2)
  let cell : Fin (2 * k) → Finset (Point 2) :=
    fun i => pvFrameCell (show 2 ≤ k by omega) F i
  have hfiber : fiber.card ≤ ∏ i, (cell i).card := by
    let V := (i : Fin (2 * k)) → ↥(cell i)
    let witness : (Q : ↥fiber) →
        PVSupportData t (show 2 ≤ k by omega) (Q : Finset (Point 2)) F := fun Q =>
      Classical.choice (show supports (Q : Finset (Point 2)) F by
        have hQ' : (Q : Finset (Point 2)) ∈ G.filter (fun R => supports R F) := by
          simpa only [fiber] using Q.property
        exact (Finset.mem_filter.mp hQ').2)
    let chosen : (Q : ↥fiber) → Fin (2 * k) → Point 2 := fun Q i =>
      (witness Q).q ⟨2 * i + 1, by omega⟩
    have hchosen (Q : ↥fiber) :
        (∀ i, chosen Q i ∈ (Q : Finset (Point 2)) ∧ chosen Q i ∈ cell i) ∧
        (Q : Finset (Point 2)) =
          (Finset.univ.image fun i => (F.2 i : Point 2)) ∪
            Finset.univ.image (chosen Q) := by
      constructor
      · intro i
        constructor
        · rw [← (witness Q).q_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · exact (witness Q).odd_mem_cell i
      · rw [← (witness Q).q_image,
          ← image_even_union_image_odd (show 1 ≤ k by omega) (witness Q).q]
        congr 1
        ext z
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor <;> rintro ⟨i, rfl⟩
        · exact ⟨i, (witness Q).anchor_even i⟩
        · exact ⟨i, (witness Q).anchor_even i |>.symm⟩
    let encode : ↥fiber → V := fun Q i => ⟨chosen Q i, (hchosen Q).1 i |>.2⟩
    have hencode : Function.Injective encode := by
      intro Q R hQR
      apply Subtype.ext
      rw [(hchosen Q).2, (hchosen R).2]
      congr 1
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨i, rfl⟩
      · exact ⟨i, (congrArg Subtype.val (congrFun hQR i)).symm⟩
      · exact ⟨i, congrArg Subtype.val (congrFun hQR i)⟩
    have hc := Fintype.card_le_of_injective encode hencode
    calc
      fiber.card = Fintype.card ↥fiber := (Fintype.card_coe fiber).symm
      _ ≤ Fintype.card V := hc
      _ = ∏ i, (cell i).card := by simp [V, Fintype.card_pi]
  have htN : ∀ i, (cell i).card ≤ X.card := by
    intro i
    apply Finset.card_le_card
    simpa only [cell, pvFrameCell] using
      (Finset.filter_subset (fun z => z ∈ SupportCell
        (pvFrameSigma (show 2 ≤ k by omega) F)
        (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) i) X)
  obtain ⟨I, hIcard, hIdense⟩ := pv_cardinality_endgame
    k X.card G.card fiber.card hk hcard (fun i => (cell i).card) hsuper
    (by simpa [fiber] using hframe) hfiber htN
  let eI : Fin k ≃o ↥I := I.orderIsoOfFin hIcard
  let idx : Fin k → Fin (2 * k) := fun i => (eI i : Fin (2 * k))
  have hidxinj : Function.Injective idx := by
    intro i j hij
    apply eI.injective
    apply Subtype.ext
    simpa only [idx] using hij
  let selectedCell : Fin k → Finset (Point 2) := fun i => cell (idx i)
  let SF : PositiveFractionSupportFrame k X :=
    { sigma := pvFrameSigma (show 2 ≤ k by omega) F
      edgeStart := fun i => pvFrameStart F (idx i)
      edgeEnd := fun i => pvFrameEnd (show 0 < k by omega) F (idx i)
      cell := selectedCell
      cell_subset := by
        intro i
        simpa only [selectedCell, cell, pvFrameCell] using
          (Finset.filter_subset (fun z => z ∈ SupportCell
            (pvFrameSigma (show 2 ≤ k by omega) F)
            (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) X)
      cell_dense := by
        intro i
        exact hIdense (idx i) (eI i).property
      cell_sign := by
        intro i z hz
        have hz' : z ∈ X.filter (fun w => w ∈ SupportCell
            (pvFrameSigma (show 2 ≤ k by omega) F)
            (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) := by
          simpa only [selectedCell, cell, pvFrameCell] using hz
        obtain ⟨_, hown, hother⟩ := Finset.mem_filter.mp hz'
        refine ⟨hown, ?_⟩
        intro j hji
        exact hother (idx j) (fun heq => hji (hidxinj heq)) }
  refine ⟨{
    toStrongPositiveFractionConfiguration := SF.toStrongConfiguration
    supportSize := 2 * k
    supportSize_pos := by omega
    supportIndex := idx
    supportIndex_strictMono := by
      intro i j hij
      exact eI.strictMono hij
    supportSigma := pvFrameSigma (show 2 ≤ k by omega) F
    supportSigma_ne_zero := by
      rw [W.frame_sigma]
      cases W.upper <;> norm_num [pvSigma]
    supportStart := pvFrameStart F
    supportEnd := pvFrameEnd (show 0 < k by omega) F
    cell_support_sign := by
      intro i z hz
      change z ∈ SF.cell i at hz
      change z ∈ selectedCell i at hz
      have hz' : z ∈ X.filter (fun w => w ∈ SupportCell
          (pvFrameSigma (show 2 ≤ k by omega) F)
          (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) := by
        simpa only [selectedCell, cell, pvFrameCell] using hz
      exact (Finset.mem_filter.mp hz').2
    representative := fun i => W.q ⟨2 * (idx i) + 1, by omega⟩
    representative_mem := by
      intro i
      change W.q ⟨2 * (idx i) + 1, by omega⟩ ∈ SF.cell i
      change W.q ⟨2 * (idx i) + 1, by omega⟩ ∈ selectedCell i
      simpa only [selectedCell, cell] using W.odd_mem_cell (idx i)
    representative_orient := by
      intro i j l hij hjl
      rw [W.frame_sigma]
      apply W.q_orient
      · have := eI.strictMono hij
        have hval : (idx i : ℕ) < (idx j : ℕ) := by
          simpa [idx] using this
        exact Fin.mk_lt_mk.mpr (by omega)
      · have := eI.strictMono hjl
        have hval : (idx j : ℕ) < (idx l : ℕ) := by
          simpa [idx] using this
        exact Fin.mk_lt_mk.mpr (by omega) }⟩

end

end

/-! ### Upstream module `JSP527/External/Erdos651/HamSandwich.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The finite oriented ham-sandwich step in dimension three

This file records the finite, oriented form used in the Pohoata--Zakharov
selection argument.  Affine functionals are oriented so that the first two
colours are retained on the positive side and the last two on the negative
side.

The strictification lemmas are stated separately.  This is useful because a
closed discrete ham-sandwich cut can contain points of the finite sets, while
the later convex-hull argument needs strict separation.
-/

open scoped InnerProductSpace

noncomputable section

/-- The positive, respectively negative, strict sides of an oriented affine
hyperplane. -/
def strictPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ) : Set (Point 3) := {x | 0 < φ x}

def strictNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ) : Set (Point 3) := {x | φ x < 0}

/-- An affine functional strictly separates two finite point sets, with the
orientation from `N` towards `P`. -/
def StrictlySeparates (φ : Point 3 →ᵃ[ℝ] ℝ)
    (P N : Finset (Point 3)) : Prop :=
  (∀ x ∈ P, 0 < φ x) ∧ ∀ x ∈ N, φ x < 0

/-- A finite set lies in the closed positive side of an affine functional. -/
def InClosedPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ)
    (X : Finset (Point 3)) : Prop :=
  ∀ x ∈ X, 0 ≤ φ x

/-- A finite set lies in the closed negative side of an affine functional. -/
def InClosedNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ)
    (X : Finset (Point 3)) : Prop :=
  ∀ x ∈ X, φ x ≤ 0

/-- The integer form of "`Y` contains at least half of `X`".  It avoids
rounding conventions and is exactly what is needed in the iterative loss
estimate. -/
def IsHalfOf (Y X : Finset (Point 3)) : Prop :=
  Y ⊆ X ∧ X.card ≤ 2 * Y.card

/-- Data furnished by a strict oriented four-colour ham-sandwich cut. -/
structure OrientedHalfSelection
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) where
  φ : Point 3 →ᵃ[ℝ] ℝ
  Y₁ : Finset (Point 3)
  Y₂ : Finset (Point 3)
  Y₃ : Finset (Point 3)
  Y₄ : Finset (Point 3)
  half₁ : IsHalfOf Y₁ X₁
  half₂ : IsHalfOf Y₂ X₂
  half₃ : IsHalfOf Y₃ X₃
  half₄ : IsHalfOf Y₄ X₄
  positive₁ : ∀ x ∈ Y₁, 0 < φ x
  positive₂ : ∀ x ∈ Y₂, 0 < φ x
  negative₃ : ∀ x ∈ Y₃, φ x < 0
  negative₄ : ∀ x ∈ Y₄, φ x < 0

/-- Closed-side data before perturbing the ham-sandwich hyperplane away
from its finitely many boundary points. -/
structure ClosedOrientedHalfSelection
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) where
  φ : Point 3 →ᵃ[ℝ] ℝ
  Y₁ : Finset (Point 3)
  Y₂ : Finset (Point 3)
  Y₃ : Finset (Point 3)
  Y₄ : Finset (Point 3)
  half₁ : IsHalfOf Y₁ X₁
  half₂ : IsHalfOf Y₂ X₂
  half₃ : IsHalfOf Y₃ X₃
  half₄ : IsHalfOf Y₄ X₄
  positive₁ : InClosedPositiveSide φ Y₁
  positive₂ : InClosedPositiveSide φ Y₂
  negative₃ : InClosedNegativeSide φ Y₃
  negative₄ : InClosedNegativeSide φ Y₄
  nonconstant : φ.linear ≠ 0

/-- A closed hyperplane bisects a finite set if both of its closed sides
contain at least half of that set. -/
def ClosedBisects (φ : Point 3 →ᵃ[ℝ] ℝ) (X : Finset (Point 3)) : Prop :=
  X.card ≤ 2 * (X.filter fun x ↦ 0 ≤ φ x).card ∧
    X.card ≤ 2 * (X.filter fun x ↦ φ x ≤ 0).card

/-- The exact missing topological/combinatorial input: the finite discrete
ham-sandwich theorem for three point sets in `ℝ³`. -/
def ThreeSetDiscreteHamSandwich : Prop :=
  ∀ X₁ X₂ X₃ : Finset (Point 3),
    ∃ φ : Point 3 →ᵃ[ℝ] ℝ, φ.linear ≠ 0 ∧
      ClosedBisects φ X₁ ∧ ClosedBisects φ X₂ ∧ ClosedBisects φ X₃

/-! We prove the topological input in the only dimension needed here.  The
proof is the elementary covering-space proof of Borsuk--Ulam for
`S² → ℝ²`: a zero-free odd map would give an odd circle-valued map;
lifting its restriction to a hemisphere through `Circle.exp` contradicts
the two possible orientations of the equator. -/

private abbrev SphereTwo := Metric.sphere (0 : Point 3) 1
private abbrev DiskTwo := Metric.closedBall (0 : Point 2) 1

private def sphereTwoNeg (x : SphereTwo) : SphereTwo :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

@[simp] private lemma sphereTwoNeg_val (x : SphereTwo) :
    (sphereTwoNeg x : Point 3) = -x := rfl

private def pointTwoComplex : Point 2 ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private def pointTwoCircle (x : Point 2) (hx : x ≠ 0) : Circle :=
  ⟨pointTwoComplex x / (‖x‖ : ℂ), by
    change pointTwoComplex x / (‖x‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_div, LinearIsometryEquiv.norm_map]
    simp [norm_ne_zero_iff.mpr hx]⟩

private def upperHemisphere (z : DiskTwo) : SphereTwo :=
  ⟨WithLp.toLp 2 ![(z.1 0), (z.1 1), Real.sqrt (1 - ‖z.1‖ ^ 2)], by
    rw [Metric.mem_sphere, _root_.dist_zero_right]
    apply sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) |>.mp
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three]
    simp
    have hzsq : (z.1 0) ^ 2 + (z.1 1) ^ 2 = ‖z.1‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp
    rw [hzsq]
    rw [Real.sq_sqrt]
    · ring
    · have hz := z.2
      rw [Metric.mem_closedBall, _root_.dist_zero_right] at hz
      apply sub_nonneg.mpr
      simpa using ((sq_le_sq₀ (norm_nonneg z.1)
        (by norm_num : (0 : ℝ) ≤ 1)).mpr hz)⟩

private lemma continuous_upperHemisphere : Continuous upperHemisphere := by
  apply Continuous.subtype_mk
  fun_prop

private def circleDisk (q : Circle) : DiskTwo :=
  ⟨pointTwoComplex.symm (q : ℂ), by
    rw [Metric.mem_closedBall, _root_.dist_zero_right,
      LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

private lemma continuous_circleDisk : Continuous circleDisk := by
  apply Continuous.subtype_mk
  exact pointTwoComplex.symm.continuous.comp continuous_subtype_val

private lemma circleDisk_neg (q : Circle) :
    circleDisk (-q) = -circleDisk q := by
  apply Subtype.ext
  change pointTwoComplex.symm (-(q : ℂ)) = -pointTwoComplex.symm (q : ℂ)
  exact map_neg _ _

private lemma upperHemisphere_circleDisk_neg (q : Circle) :
    upperHemisphere (circleDisk (-q)) =
      sphereTwoNeg (upperHemisphere (circleDisk q)) := by
  apply Subtype.ext
  rw [circleDisk_neg]
  ext i
  fin_cases i <;>
    simp [upperHemisphere, circleDisk, pointTwoComplex,
      Circle.norm_coe]

/-- The two-dimensional Borsuk--Ulam theorem, in the concrete form used by
the finite median argument below. -/
private theorem borsukUlamSphereTwo
    (f : SphereTwo → Point 2) (hf : Continuous f)
    (hodd : ∀ x, f (sphereTwoNeg x) = -f x) :
    ∃ x, f x = 0 := by
  by_contra hzero
  push_neg at hzero
  let g : SphereTwo → Circle := fun x ↦ pointTwoCircle (f x) (hzero x)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    change Continuous fun x ↦ pointTwoComplex (f x) / (‖f x‖ : ℂ)
    apply Continuous.div₀
    · exact pointTwoComplex.continuous.comp hf
    · exact Complex.continuous_ofReal.comp hf.norm
    · intro x
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hzero x))
  have hgodd (x : SphereTwo) : g (sphereTwoNeg x) = -g x := by
    apply Circle.ext
    change pointTwoComplex (f (sphereTwoNeg x)) /
        (‖f (sphereTwoNeg x)‖ : ℂ) =
      -(pointTwoComplex (f x) / (‖f x‖ : ℂ))
    rw [hodd, map_neg, norm_neg]
    exact neg_div _ _

  let G : C(DiskTwo, Circle) :=
    ⟨fun z ↦ g (upperHemisphere z), hg.comp continuous_upperHemisphere⟩
  let z₀ : DiskTwo := ⟨0, by simp⟩
  letI : ContractibleSpace DiskTwo :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : LocallyPathConnectedSpace DiskTwo :=
    (convex_closedBall (0 : Point 2) 1).locallyPathConnectedSpace
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (G z₀)
  obtain ⟨L, hL, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts G z₀ e₀ he₀

  let D : Circle → ℝ := fun q ↦ L (circleDisk (-q)) - L (circleDisk q)
  have hDcont : Continuous D := by
    dsimp [D]
    exact (L.continuous.comp (continuous_circleDisk.comp continuous_neg)).sub
      (L.continuous.comp continuous_circleDisk)
  have hDexp (q : Circle) : Circle.exp (D q) = -1 := by
    rw [show D q = L (circleDisk (-q)) - L (circleDisk q) by rfl,
      Circle.exp_sub]
    have hLpoint (z : DiskTwo) : Circle.exp (L z) = G z := by
      exact congr_fun hL.2 z
    rw [hLpoint, hLpoint]
    change g (upperHemisphere (circleDisk (-q))) /
      g (upperHemisphere (circleDisk q)) = -1
    rw [upperHemisphere_circleDisk_neg, hgodd]
    rw [neg_div]
    have hself : g (upperHemisphere (circleDisk q)) /
        g (upperHemisphere (circleDisk q)) = 1 := div_self' _
    rw [hself]
  have hDneg (q : Circle) : D (-q) = -D q := by
    simp only [D, neg_neg]
    ring

  let I := Set.Icc (0 : ℝ) 1
  let q : I → Circle := fun t ↦ Circle.exp (Real.pi * t.1)
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  let d : C(I, ℝ) := ⟨fun t ↦ D (q t), hDcont.comp hqcont⟩
  let K : C(I, Circle) := ContinuousMap.const I (-1)
  let t₀ : I := ⟨0, by dsimp [I]; simp⟩
  let t₁ : I := ⟨1, by dsimp [I]; simp⟩
  letI : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hd_lifts : Circle.exp ∘ d = K := by
    funext t
    exact hDexp (q t)
  obtain ⟨J, hJ, hJunique⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts K t₀ (d t₀)
      (congr_fun hd_lifts t₀)
  have hd_eq_J : d = J := hJunique d ⟨rfl, hd_lifts⟩
  let c : C(I, ℝ) := ContinuousMap.const I (d t₀)
  have hc_lifts : Circle.exp ∘ c = K := by
    funext t
    change Circle.exp (d t₀) = -1
    exact hDexp (q t₀)
  have hc_eq_J : c = J := hJunique c ⟨rfl, hc_lifts⟩
  have hdc : d = c := hd_eq_J.trans hc_eq_J.symm
  have hq₀ : q t₀ = 1 := by
    apply Circle.ext
    simp [q, t₀]
  have hq₁ : q t₁ = -1 := by
    apply Circle.ext
    simp [q, t₁, Circle.coe_exp, Complex.exp_pi_mul_I]
  have hdend : D (-1) = D 1 := by
    have := DFunLike.congr_fun hdc t₁
    simpa [d, c, hq₀, hq₁] using this
  have hD1 : D 1 = 0 := by
    have hneg : D (-1) = -D 1 := by simpa using hDneg (1 : Circle)
    rw [hdend] at hneg
    linarith
  have hone : (1 : Circle) = -1 := by
    calc
      1 = Circle.exp 0 := Circle.exp_zero.symm
      _ = Circle.exp (D 1) := congr_arg Circle.exp hD1.symm
      _ = -1 := hDexp 1
  exact Circle.neg_ne_self 1 hone.symm

private lemma majoritySize_le_card {X : Finset (Point 3)} (hX : X.Nonempty) :
    X.card / 2 + 1 ≤ X.card := by
  have := Finset.card_pos.mpr hX
  omega

private lemma majorityFamily_nonempty {X : Finset (Point 3)} (hX : X.Nonempty) :
    (X.powersetCard (X.card / 2 + 1)).Nonempty :=
  Finset.powersetCard_nonempty.mpr (majoritySize_le_card hX)

private lemma majorityMember_nonempty {X A : Finset (Point 3)}
    (hA : A ∈ X.powersetCard (X.card / 2 + 1)) : A.Nonempty := by
  rw [Finset.mem_powersetCard] at hA
  apply Finset.card_pos.mp
  omega

private lemma neg_finset_sup' {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    -(s.sup' hs f) = s.inf' hs (fun i ↦ -f i) := by
  apply le_antisymm
  · apply Finset.le_inf' hs
    intro i hi
    exact neg_le_neg (Finset.le_sup' f hi)
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hs f
    have h := Finset.inf'_le (fun i ↦ -f i) hi
    rw [hsup]
    exact h

private lemma neg_finset_inf' {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    -(s.inf' hs f) = s.sup' hs (fun i ↦ -f i) := by
  apply le_antisymm
  · obtain ⟨i, hi, hinf⟩ := Finset.exists_mem_eq_inf' hs f
    have h := Finset.le_sup' (fun i ↦ -f i) hi
    rw [hinf]
    exact h
  · apply Finset.sup'_le hs
    intro i hi
    exact neg_le_neg (Finset.inf'_le f hi)

private def lowerMedian (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) : ℝ :=
  let F := X.powersetCard (X.card / 2 + 1)
  F.attach.sup' (majorityFamily_nonempty hX).attach fun A ↦
    A.1.inf' (majorityMember_nonempty A.2) fun x ↦ ⟪u.1, (x : Point 3)⟫_ℝ

private def upperMedian (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) : ℝ :=
  let F := X.powersetCard (X.card / 2 + 1)
  F.attach.inf' (majorityFamily_nonempty hX).attach fun A ↦
    A.1.sup' (majorityMember_nonempty A.2) fun x ↦ ⟪u.1, (x : Point 3)⟫_ℝ

private def finiteMedian (X : Finset (Point 3)) (u : SphereTwo) : ℝ :=
  if hX : X.Nonempty then (lowerMedian X hX u + upperMedian X hX u) / 2 else 0

private lemma continuous_lowerMedian (X : Finset (Point 3)) (hX : X.Nonempty) :
    Continuous (lowerMedian X hX) := by
  unfold lowerMedian
  apply Continuous.finset_sup'_apply (majorityFamily_nonempty hX).attach
  intro A hA
  apply Continuous.finset_inf'_apply (majorityMember_nonempty A.2)
  intro x hx
  fun_prop

private lemma continuous_upperMedian (X : Finset (Point 3)) (hX : X.Nonempty) :
    Continuous (upperMedian X hX) := by
  unfold upperMedian
  apply Continuous.finset_inf'_apply (majorityFamily_nonempty hX).attach
  intro A hA
  apply Continuous.finset_sup'_apply (majorityMember_nonempty A.2)
  intro x hx
  fun_prop

private lemma continuous_finiteMedian (X : Finset (Point 3)) :
    Continuous (finiteMedian X) := by
  change Continuous fun u ↦ finiteMedian X u
  by_cases hX : X.Nonempty
  · simpa only [finiteMedian, dif_pos hX, Pi.add_apply] using
      (continuous_lowerMedian X hX).add (continuous_upperMedian X hX) |>.div_const 2
  · simpa only [finiteMedian, dif_neg hX] using
      (continuous_const : Continuous fun _ : SphereTwo ↦ (0 : ℝ))

@[simp] private lemma sphereTwoNeg_neg (u : SphereTwo) :
    sphereTwoNeg (sphereTwoNeg u) = u := by
  apply Subtype.ext
  simp [sphereTwoNeg]

private lemma lowerMedian_neg (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) :
    lowerMedian X hX (sphereTwoNeg u) = -upperMedian X hX u := by
  dsimp only [lowerMedian, upperMedian]
  rw [neg_finset_inf']
  congr 1
  funext A
  rw [neg_finset_sup']
  congr 1
  funext x
  simp [sphereTwoNeg]

private lemma upperMedian_neg (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) :
    upperMedian X hX (sphereTwoNeg u) = -lowerMedian X hX u := by
  have h := lowerMedian_neg X hX (sphereTwoNeg u)
  simp only [sphereTwoNeg_neg] at h
  linarith

private lemma finiteMedian_neg (X : Finset (Point 3)) (u : SphereTwo) :
    finiteMedian X (sphereTwoNeg u) = -finiteMedian X u := by
  by_cases hX : X.Nonempty
  · simp only [finiteMedian, dif_pos hX, lowerMedian_neg, upperMedian_neg]
    ring
  · simp [finiteMedian, hX]

private lemma majorityMembers_inter_nonempty {X A B : Finset (Point 3)}
    (hA : A ∈ X.powersetCard (X.card / 2 + 1))
    (hB : B ∈ X.powersetCard (X.card / 2 + 1)) :
    (A ∩ B).Nonempty := by
  rw [Finset.mem_powersetCard] at hA hB
  apply Finset.inter_nonempty_of_card_lt_card_add_card hA.1 hB.1
  rw [hA.2, hB.2]
  omega

private lemma lowerMedian_le_upperMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    lowerMedian X hX u ≤ upperMedian X hX u := by
  unfold lowerMedian upperMedian
  apply Finset.sup'_le (majorityFamily_nonempty hX).attach
  intro A hA
  apply Finset.le_inf' (majorityFamily_nonempty hX).attach
  intro B hB
  obtain ⟨x, hx⟩ := majorityMembers_inter_nonempty A.2 B.2
  rw [Finset.mem_inter] at hx
  exact (Finset.inf'_le (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) hx.1).trans
    (Finset.le_sup' (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) hx.2)

private lemma lowerMedian_le_finiteMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    lowerMedian X hX u ≤ finiteMedian X u := by
  rw [finiteMedian, dif_pos hX]
  have := lowerMedian_le_upperMedian X hX u
  linarith

private lemma finiteMedian_le_upperMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    finiteMedian X u ≤ upperMedian X hX u := by
  rw [finiteMedian, dif_pos hX]
  have := lowerMedian_le_upperMedian X hX u
  linarith

private lemma card_filter_lowerMedian_lt_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ lowerMedian X hX u < ⟪u.1, x⟫_ℝ).card ≤ X.card / 2 := by
  by_contra hcard
  have hq : X.card / 2 + 1 ≤
      (X.filter fun x ↦ lowerMedian X hX u < ⟪u.1, x⟫_ℝ).card := by omega
  obtain ⟨A, hAfilter, hAcard⟩ := Finset.exists_subset_card_eq hq
  have hAX : A ⊆ X := hAfilter.trans (Finset.filter_subset _ _)
  have hAmem : A ∈ X.powersetCard (X.card / 2 + 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨hAX, hAcard⟩
  have hlt : lowerMedian X hX u <
      A.inf' (majorityMember_nonempty hAmem) (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) := by
    rw [Finset.lt_inf'_iff]
    intro x hx
    exact (Finset.mem_filter.mp (hAfilter hx)).2
  have hle : A.inf' (majorityMember_nonempty hAmem)
      (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) ≤ lowerMedian X hX u := by
    unfold lowerMedian
    exact Finset.le_sup'
      (fun B : {B // B ∈ X.powersetCard (X.card / 2 + 1)} ↦
        B.1.inf' (majorityMember_nonempty B.2)
          (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ))
      (show (⟨A, hAmem⟩ :
      {A // A ∈ X.powersetCard (X.card / 2 + 1)}) ∈
        (X.powersetCard (X.card / 2 + 1)).attach by simp)
  exact (not_lt_of_ge hle) hlt

private lemma card_filter_lt_upperMedian_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < upperMedian X hX u).card ≤ X.card / 2 := by
  by_contra hcard
  have hq : X.card / 2 + 1 ≤
      (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < upperMedian X hX u).card := by omega
  obtain ⟨A, hAfilter, hAcard⟩ := Finset.exists_subset_card_eq hq
  have hAX : A ⊆ X := hAfilter.trans (Finset.filter_subset _ _)
  have hAmem : A ∈ X.powersetCard (X.card / 2 + 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨hAX, hAcard⟩
  have hlt : A.sup' (majorityMember_nonempty hAmem)
      (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) < upperMedian X hX u := by
    rw [Finset.sup'_lt_iff]
    intro x hx
    exact (Finset.mem_filter.mp (hAfilter hx)).2
  have hle : upperMedian X hX u ≤
      A.sup' (majorityMember_nonempty hAmem) (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) := by
    unfold upperMedian
    exact Finset.inf'_le
      (fun B : {B // B ∈ X.powersetCard (X.card / 2 + 1)} ↦
        B.1.sup' (majorityMember_nonempty B.2)
          (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ))
      (show (⟨A, hAmem⟩ :
      {A // A ∈ X.powersetCard (X.card / 2 + 1)}) ∈
        (X.powersetCard (X.card / 2 + 1)).attach by simp)
  exact (not_lt_of_ge hle) hlt

private lemma card_filter_finiteMedian_lt_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ finiteMedian X u < ⟪u.1, x⟫_ℝ).card ≤ X.card / 2 := by
  refine (Finset.card_le_card ?_).trans (card_filter_lowerMedian_lt_le X hX u)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, (lowerMedian_le_finiteMedian X hX u).trans_lt hx.2⟩

private lemma card_filter_lt_finiteMedian_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < finiteMedian X u).card ≤ X.card / 2 := by
  refine (Finset.card_le_card ?_).trans (card_filter_lt_upperMedian_le X hX u)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le (finiteMedian_le_upperMedian X hX u)⟩

private def medianAffine (u : SphereTwo) (t : ℝ) : Point 3 →ᵃ[ℝ] ℝ :=
  (innerSL ℝ u.1).toLinearMap.toAffineMap - AffineMap.const ℝ (Point 3) t

@[simp] private lemma medianAffine_apply (u : SphereTwo) (t : ℝ) (x : Point 3) :
    medianAffine u t x = ⟪u.1, x⟫_ℝ - t := by
  simp [medianAffine]

private lemma medianAffine_linear_ne_zero (u : SphereTwo) :
    (medianAffine u t).linear ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero u.1
  have hunorm : ‖u.1‖ = 1 := by
    simpa [Metric.mem_sphere] using u.2
  simp [medianAffine, real_inner_self_eq_norm_sq, hunorm] at h

private lemma medianAffine_closedBisects (X : Finset (Point 3)) (u : SphereTwo) :
    ClosedBisects (medianAffine u (finiteMedian X u)) X := by
  classical
  by_cases hX : X.Nonempty
  · have hlt := card_filter_lt_finiteMedian_le X hX u
    have hgt := card_filter_finiteMedian_lt_le X hX u
    have hpospart := Finset.card_filter_add_card_filter_not
      (s := X) (fun x ↦ 0 ≤ medianAffine u (finiteMedian X u) x)
    have hnegpart := Finset.card_filter_add_card_filter_not
      (s := X) (fun x ↦ medianAffine u (finiteMedian X u) x ≤ 0)
    have hnotpos :
        (X.filter fun x ↦ ¬0 ≤ medianAffine u (finiteMedian X u) x).card ≤
          X.card / 2 := by
      simpa only [medianAffine_apply, not_le, sub_neg] using hlt
    have hnotneg :
        (X.filter fun x ↦ ¬medianAffine u (finiteMedian X u) x ≤ 0).card ≤
          X.card / 2 := by
      simpa only [medianAffine_apply, not_le, sub_pos] using hgt
    constructor <;> omega
  · have : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst X
    simp [ClosedBisects]

/-- The finite discrete ham-sandwich theorem for three finite point sets in
dimension three.  The proof uses continuous canonical medians of the three
families of one-dimensional projections and `borsukUlamSphereTwo`. -/
theorem threeSetDiscreteHamSandwich : ThreeSetDiscreteHamSandwich := by
  intro X₁ X₂ X₃
  let F : SphereTwo → Point 2 := fun u ↦
    WithLp.toLp 2 ![finiteMedian X₂ u - finiteMedian X₁ u,
      finiteMedian X₃ u - finiteMedian X₁ u]
  have hFcont : Continuous F := by
    have h₁c : Continuous (finiteMedian X₁) := continuous_finiteMedian X₁
    have h₂c : Continuous (finiteMedian X₂) := continuous_finiteMedian X₂
    have h₃c : Continuous (finiteMedian X₃) := continuous_finiteMedian X₃
    dsimp [F]
    fun_prop
  have hFodd (u : SphereTwo) : F (sphereTwoNeg u) = -F u := by
    ext i
    fin_cases i <;> simp [F, finiteMedian_neg] <;> ring
  obtain ⟨u, hu⟩ := borsukUlamSphereTwo F hFcont hFodd
  have h₂₁ : finiteMedian X₂ u = finiteMedian X₁ u := by
    have h := congr_arg (fun v : Point 2 ↦ v 0) hu
    have hz : finiteMedian X₂ u - finiteMedian X₁ u = 0 := by
      simpa [F] using h
    exact sub_eq_zero.mp hz
  have h₃₁ : finiteMedian X₃ u = finiteMedian X₁ u := by
    have h := congr_arg (fun v : Point 2 ↦ v 1) hu
    have hz : finiteMedian X₃ u - finiteMedian X₁ u = 0 := by
      simpa [F] using h
    exact sub_eq_zero.mp hz
  refine ⟨medianAffine u (finiteMedian X₁ u), medianAffine_linear_ne_zero u,
    medianAffine_closedBisects X₁ u, ?_, ?_⟩
  · simpa [h₂₁] using medianAffine_closedBisects X₂ u
  · simpa [h₃₁] using medianAffine_closedBisects X₃ u

/-- At least one of the two closed sides of any oriented affine hyperplane
contains half of a finite set. -/
lemma half_in_one_closed_side (φ : Point 3 →ᵃ[ℝ] ℝ) (X : Finset (Point 3)) :
    X.card ≤ 2 * (X.filter fun x ↦ 0 ≤ φ x).card ∨
      X.card ≤ 2 * (X.filter fun x ↦ φ x ≤ 0).card := by
  classical
  let P := X.filter fun x ↦ 0 ≤ φ x
  let N := X.filter fun x ↦ φ x ≤ 0
  have hsub : X ⊆ P ∪ N := by
    intro x hx
    rcases le_total 0 (φ x) with h | h
    · exact Finset.mem_union_left N (by simp [P, hx, h])
    · exact Finset.mem_union_right P (by simp [N, hx, h])
  have hcard : X.card ≤ P.card + N.card := by
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le P N).trans_eq (by omega))
  change X.card ≤ 2 * P.card ∨ X.card ≤ 2 * N.card
  by_cases hP : X.card ≤ 2 * P.card
  · exact Or.inl hP
  · right
    omega

/-- Bisecting three colours and orienting the cut according to the fourth
gives the required `2`-versus-`2` closed-side selection. -/
theorem exists_closedOrientedHalfSelection_of_bisectsThree
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ)
    (h₁ : ClosedBisects φ X₁) (h₂ : ClosedBisects φ X₂)
    (h₃ : ClosedBisects φ X₃) (hφ : φ.linear ≠ 0) :
    ∃ S : ClosedOrientedHalfSelection X₁ X₂ X₃ X₄, True := by
  classical
  rcases half_in_one_closed_side φ X₄ with h₄ | h₄
  · refine ⟨
      { φ := -φ
        Y₁ := X₁.filter fun x ↦ φ x ≤ 0
        Y₂ := X₂.filter fun x ↦ φ x ≤ 0
        Y₃ := X₃.filter fun x ↦ 0 ≤ φ x
        Y₄ := X₄.filter fun x ↦ 0 ≤ φ x
        half₁ := ⟨Finset.filter_subset _ _, h₁.2⟩
        half₂ := ⟨Finset.filter_subset _ _, h₂.2⟩
        half₃ := ⟨Finset.filter_subset _ _, h₃.1⟩
        half₄ := ⟨Finset.filter_subset _ _, h₄⟩
        positive₁ := by simp [InClosedPositiveSide]
        positive₂ := by simp [InClosedPositiveSide]
        negative₃ := by simp [InClosedNegativeSide]
        negative₄ := by simp [InClosedNegativeSide]
        nonconstant := by simpa using hφ }, trivial⟩
  · refine ⟨
      { φ := φ
        Y₁ := X₁.filter fun x ↦ 0 ≤ φ x
        Y₂ := X₂.filter fun x ↦ 0 ≤ φ x
        Y₃ := X₃.filter fun x ↦ φ x ≤ 0
        Y₄ := X₄.filter fun x ↦ φ x ≤ 0
        half₁ := ⟨Finset.filter_subset _ _, h₁.1⟩
        half₂ := ⟨Finset.filter_subset _ _, h₂.1⟩
        half₃ := ⟨Finset.filter_subset _ _, h₃.2⟩
        half₄ := ⟨Finset.filter_subset _ _, h₄⟩
        positive₁ := by simp [InClosedPositiveSide]
        positive₂ := by simp [InClosedPositiveSide]
        negative₃ := by simp [InClosedNegativeSide]
        negative₄ := by simp [InClosedNegativeSide]
        nonconstant := hφ }, trivial⟩

noncomputable def closedOrientedHalfSelection_of_bisectsThree
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ)
    (h₁ : ClosedBisects φ X₁) (h₂ : ClosedBisects φ X₂)
    (h₃ : ClosedBisects φ X₃) (hφ : φ.linear ≠ 0) :
    ClosedOrientedHalfSelection X₁ X₂ X₃ X₄ :=
  (exists_closedOrientedHalfSelection_of_bisectsThree X₁ X₂ X₃ X₄ φ h₁ h₂ h₃ hφ).choose

/-- In a point set of cardinality at least four, the project's exact-card
general-position predicate also gives affine independence of every subset of
cardinality at most four.  The lower bound is necessary because
`InGeneralPosition` is intentionally phrased using exact four-subsets. -/
lemma affineIndependent_of_subset_of_card_le_four
    {U A : Finset (Point 3)} (hU : 4 ≤ U.card)
    (hgp : InGeneralPosition 3 U) (hAU : A ⊆ U) (hA : A.card ≤ 4) :
    AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) := by
  classical
  obtain ⟨S, hAS, hSU, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hAU hA hU
  have hSind : AffineIndependent ℝ (fun x : S ↦ (x : Point 3)) := by
    apply hgp S hSU
    omega
  let e : A ↪ S :=
    ⟨fun x ↦ ⟨x, hAS x.2⟩, fun x y h ↦ Subtype.ext
      (show (x : Point 3) = (y : Point 3) from
        congr_arg (fun z : S ↦ (z : Point 3)) h)⟩
  convert hSind.comp_embedding e using 1
  funext x
  rfl

/-- A nonconstant affine hyperplane contains at most three points of a
general-position set in `ℝ³`. -/
lemma card_filter_affineMap_eq_zero_le_three
    {U : Finset (Point 3)} {φ : Point 3 →ᵃ[ℝ] ℝ}
    (hgp : InGeneralPosition 3 U) (hφ : φ.linear ≠ 0) :
    (U.filter fun x ↦ φ x = 0).card ≤ 3 := by
  classical
  let B := U.filter fun x ↦ φ x = 0
  by_contra hB
  have hfour : 4 ≤ B.card := by
    dsimp [B]
    omega
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq hfour
  have hSind : AffineIndependent ℝ (fun x : S ↦ (x : Point 3)) := by
    apply hgp S (hSB.trans (Finset.filter_subset _ _))
    omega
  have hSspan : affineSpan ℝ (Set.range fun x : S ↦ (x : Point 3)) = ⊤ := by
    apply hSind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simpa using hScard
  let b : AffineBasis S ℝ (Point 3) :=
    ⟨(fun x : S ↦ (x : Point 3)), hSind, hSspan⟩
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  let i : S := ⟨hSne.choose, hSne.choose_spec⟩
  have hzero (x : S) : φ (b x) = 0 := by
    exact (Finset.mem_filter.mp (hSB x.2)).2
  have hlin : φ.linear = 0 := by
    apply (b.basisOf i).ext
    intro j
    rw [b.basisOf_apply, φ.linearMap_vsub]
    simp [hzero]
  exact hφ hlin

lemma convex_strictPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ) :
    Convex ℝ (strictPositiveSide φ) := by
  exact (convex_Ioi (0 : ℝ)).affine_preimage φ

lemma convex_strictNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ) :
    Convex ℝ (strictNegativeSide φ) := by
  exact (convex_Iio (0 : ℝ)).affine_preimage φ

/-- Strict affine separation propagates from a finite set to its convex
hull. -/
lemma convexHull_subset_strictPositiveSide {φ : Point 3 →ᵃ[ℝ] ℝ}
    {P : Finset (Point 3)} (hP : ∀ x ∈ P, 0 < φ x) :
    convexHull ℝ (↑P : Set (Point 3)) ⊆ strictPositiveSide φ := by
  apply convexHull_min
  · intro x hx
    exact hP x (by simpa using hx)
  · exact convex_strictPositiveSide φ

lemma convexHull_subset_strictNegativeSide {φ : Point 3 →ᵃ[ℝ] ℝ}
    {N : Finset (Point 3)} (hN : ∀ x ∈ N, φ x < 0) :
    convexHull ℝ (↑N : Set (Point 3)) ⊆ strictNegativeSide φ := by
  apply convexHull_min
  · intro x hx
    exact hN x (by simpa using hx)
  · exact convex_strictNegativeSide φ

/-- The convex-hull wrapper used by the two-separation iteration. -/
theorem convexHulls_disjoint_of_strictlySeparates
    {φ : Point 3 →ᵃ[ℝ] ℝ} {P N : Finset (Point 3)}
    (h : StrictlySeparates φ P N) :
    Disjoint (convexHull ℝ (↑P : Set (Point 3)))
      (convexHull ℝ (↑N : Set (Point 3))) := by
  rw [Set.disjoint_left]
  intro x hxP hxN
  have hp : 0 < φ x := convexHull_subset_strictPositiveSide h.1 hxP
  have hn : φ x < 0 := convexHull_subset_strictNegativeSide h.2 hxN
  exact (not_lt_of_ge hp.le) hn

/-- All prescribed values on an affinely independent family extend to an
affine functional. -/
lemma _root_.AffineIndependent.exists_affineMap_apply_eq
    {ι : Type*} {p : ι → Point 3} (hp : AffineIndependent ℝ p)
    (w : ι → ℝ) :
    ∃ g : Point 3 →ᵃ[ℝ] ℝ, ∀ i, g (p i) = w i := by
  classical
  let s : Set (Point 3) := Set.range p
  let e : ι ≃ s := Equiv.ofInjective p hp.injective
  have hs : AffineIndependent ℝ (fun x : s ↦ (x : Point 3)) := by
    convert hp.comp_embedding e.symm.toEmbedding using 1
    funext x
    exact (congr_arg Subtype.val (e.apply_symm_apply x)).symm
  obtain ⟨t, hst, htind, htspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ (Point 3) :=
    ⟨(fun x : t ↦ (x : Point 3)), htind, by
      have hrange : Set.range (fun x : t ↦ (x : Point 3)) = t := by
        ext x
        simp
      rw [hrange]
      exact htspan⟩
  letI : Finite t := b.finite
  letI : Fintype t := Fintype.ofFinite t
  let value : t → ℝ := fun x ↦ if h : (x : Point 3) ∈ s then w (e.symm ⟨x, h⟩) else 0
  let g : Point 3 →ᵃ[ℝ] ℝ := ∑ j : t, value j • b.coord j
  refine ⟨g, ?_⟩
  intro i
  let j : t := ⟨p i, hst ⟨i, rfl⟩⟩
  have hj : b j = p i := rfl
  have hvalue : value j = w i := by
    simp [value, j, s, e]
  rw [← hj]
  dsimp [g]
  have happly (S : Finset t) :
      (∑ k ∈ S, value k • b.coord k) (b j) =
        ∑ k ∈ S, value k * b.coord k (b j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih => simp [hk, ih]
  rw [happly Finset.univ]
  rw [Finset.sum_eq_single j]
  · simpa using hvalue
  · intro k _ hkj
    rw [b.coord_apply_ne hkj]
    simp
  · simp

/-- A positive perturbation which is already strict at parameter `t` stays
strict when the parameter is decreased, provided the unperturbed value is
nonnegative and zeros point in the positive perturbation direction. -/
private lemma perturb_pos_of_le
    {a b t u : ℝ} (ha : 0 ≤ a) (hz : a = 0 → 0 < b)
    (ht : 0 < t) (hu : 0 < u) (hut : u ≤ t) (h : 0 < a + t * b) :
    0 < a + u * b := by
  by_cases hb : 0 ≤ b
  · by_cases ha0 : a = 0
    · subst a
      simpa using mul_pos hu (hz rfl)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ha (Ne.symm ha0))
        (mul_nonneg hu.le hb)
  · have hb' : b < 0 := lt_of_not_ge hb
    have hm : t * b ≤ u * b := mul_le_mul_of_nonpos_right hut hb'.le
    linarith

/-- Simultaneously make finitely many weak positive inequalities strict by a
sufficiently small positive perturbation. -/
private lemma exists_small_strict_perturb
    {α : Type*} (S : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x)
    (hz : ∀ x ∈ S, a x = 0 → 0 < b x) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ S, 0 < a x + t * b x := by
  classical
  induction S using Finset.induction_on
  case empty => exact ⟨1, by norm_num, by simp⟩
  case insert y S hy ih =>
      have haS : ∀ z ∈ S, 0 ≤ a z := fun z hzmem ↦ ha z (Finset.mem_insert_of_mem hzmem)
      have hzS : ∀ z ∈ S, a z = 0 → 0 < b z :=
        fun z hzmem ↦ hz z (Finset.mem_insert_of_mem hzmem)
      obtain ⟨t, ht, hSt⟩ := ih haS hzS
      by_cases hb : 0 ≤ b y
      · refine ⟨t, ht, ?_⟩
        intro z hzmem
        rw [Finset.mem_insert] at hzmem
        rcases hzmem with hzy | hzmem
        · subst z
          by_cases hay0 : a y = 0
          · rw [hay0, zero_add]
            exact mul_pos ht (hz y (by simp) hay0)
          · exact add_pos_of_pos_of_nonneg
              (lt_of_le_of_ne (ha y (by simp)) (Ne.symm hay0)) (mul_nonneg ht.le hb)
        · exact hSt z hzmem
      · have hby : b y < 0 := lt_of_not_ge hb
        have hay : 0 < a y := by
          refine lt_of_le_of_ne (ha y (by simp)) ?_
          intro hzero
          have := hz y (by simp) hzero.symm
          linarith
        let d : ℝ := a y / (2 * (-b y))
        have hd : 0 < d := div_pos hay (mul_pos (by norm_num) (neg_pos.mpr hby))
        let u := min t d
        have hu : 0 < u := lt_min ht hd
        have hut : u ≤ t := min_le_left _ _
        have hud : u ≤ d := min_le_right _ _
        have hdcalc : d * b y = -(a y) / 2 := by
          dsimp [d]
          field_simp [hby.ne]
        have huy : 0 < a y + u * b y := by
          have hmul : d * b y ≤ u * b y :=
            mul_le_mul_of_nonpos_right hud hby.le
          rw [hdcalc] at hmul
          linarith
        refine ⟨u, hu, ?_⟩
        intro z hzmem
        rw [Finset.mem_insert] at hzmem
        rcases hzmem with hzy | hzmem
        · subst z
          exact huy
        · exact perturb_pos_of_le (haS z hzmem) (hzS z hzmem) ht hu hut (hSt z hzmem)

/-- Perturb an oriented affine hyperplane away from two finite sets.  The
boundary points may be prescribed independently as long as their union is
affinely independent. -/
theorem exists_strict_separator_of_weak_of_boundary_affineIndependent
    {φ : Point 3 →ᵃ[ℝ] ℝ} {P N : Finset (Point 3)}
    (hP : InClosedPositiveSide φ P) (hN : InClosedNegativeSide φ N)
    (hdisj : Disjoint P N)
    (hind : AffineIndependent ℝ
      (fun x : ↥((P.filter fun p ↦ φ p = 0) ∪
        (N.filter fun p ↦ φ p = 0)) ↦ (x : Point 3))) :
    ∃ ψ : Point 3 →ᵃ[ℝ] ℝ, StrictlySeparates ψ P N := by
  classical
  let Bp := P.filter fun p ↦ φ p = 0
  let Bn := N.filter fun p ↦ φ p = 0
  let B := Bp ∪ Bn
  let w : B → ℝ := fun x ↦ if (x : Point 3) ∈ Bp then 1 else -1
  obtain ⟨g, hg⟩ := AffineIndependent.exists_affineMap_apply_eq hind w
  have hgP : ∀ x ∈ P, φ x = 0 → 0 < g x := by
    intro x hx hx0
    have hxbp : x ∈ Bp := by simp [Bp, hx, hx0]
    have hxb : x ∈ B := Finset.mem_union_left Bn hxbp
    have := hg (⟨x, hxb⟩ : B)
    simp [w, hxbp] at this
    linarith
  have hgN : ∀ x ∈ N, φ x = 0 → g x < 0 := by
    intro x hx hx0
    have hxbn : x ∈ Bn := by simp [Bn, hx, hx0]
    have hxnot : x ∉ Bp := by
      intro hxbp
      exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hxbp).1 hx
    have hxb : x ∈ B := Finset.mem_union_right Bp hxbn
    have := hg (⟨x, hxb⟩ : B)
    simp [w, hxnot] at this
    linarith
  let S : Finset (Point 3 ⊕ Point 3) := P.disjSum N
  let a : Point 3 ⊕ Point 3 → ℝ := fun z ↦ Sum.elim φ (fun x ↦ -φ x) z
  let b : Point 3 ⊕ Point 3 → ℝ := fun z ↦ Sum.elim g (fun x ↦ -g x) z
  have ha : ∀ z ∈ S, 0 ≤ a z := by
    intro z hz
    rcases z with x | x
    · exact hP x (by simpa [S] using hz)
    · exact neg_nonneg.mpr (hN x (by simpa [S] using hz))
  have hz : ∀ z ∈ S, a z = 0 → 0 < b z := by
    intro z hzS hz0
    rcases z with x | x
    · exact hgP x (by simpa [S] using hzS) (by simpa [a] using hz0)
    · have hx0 : φ x = 0 := by simpa [a] using hz0
      exact neg_pos.mpr (hgN x (by simpa [S] using hzS) hx0)
  obtain ⟨t, ht, htS⟩ := exists_small_strict_perturb S a b ha hz
  let ψ : Point 3 →ᵃ[ℝ] ℝ := φ + t • g
  refine ⟨ψ, ?_, ?_⟩
  · intro x hx
    have := htS (Sum.inl x) (by simp [S, hx])
    simpa [ψ, a, b] using this
  · intro x hx
    have := htS (Sum.inr x) (by simp [S, hx])
    dsimp [a, b] at this
    change φ x + t * g x < 0
    linarith

/-- Ambient-set version of strictification.  It is the form needed during
iteration: the four current colour classes may have become small, but their
boundary points are still controlled by the original general-position set. -/
theorem ClosedOrientedHalfSelection.exists_strictification_in_ambient
    {U X₁ X₂ X₃ X₄ : Finset (Point 3)}
    (S : ClosedOrientedHalfSelection X₁ X₂ X₃ X₄)
    (hX₁ : X₁ ⊆ U) (hX₂ : X₂ ⊆ U) (hX₃ : X₃ ⊆ U) (hX₄ : X₄ ⊆ U)
    (hdisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄))
    (hcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  classical
  let P := S.Y₁ ∪ S.Y₂
  let N := S.Y₃ ∪ S.Y₄
  let B := (P.filter fun p ↦ S.φ p = 0) ∪ (N.filter fun p ↦ S.φ p = 0)
  have hPU : P ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX₁ (S.half₁.1 hx)
    · exact hX₂ (S.half₂.1 hx)
  have hNU : N ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX₃ (S.half₃.1 hx)
    · exact hX₄ (S.half₄.1 hx)
  have hBU : B ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hPU (Finset.mem_filter.mp hx).1
    · exact hNU (Finset.mem_filter.mp hx).1
  have hBzero : B ⊆ U.filter fun x ↦ S.φ x = 0 := by
    intro x hx
    simp only [Finset.mem_filter]
    refine ⟨hBU hx, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hx).2
  have hBcard : B.card ≤ 4 := by
    have hz := card_filter_affineMap_eq_zero_le_three hgp S.nonconstant
    have := Finset.card_le_card hBzero
    omega
  have hBind : AffineIndependent ℝ (fun x : B ↦ (x : Point 3)) := by
    exact affineIndependent_of_subset_of_card_le_four hcard hgp hBU hBcard
  obtain ⟨ψ, hψ⟩ :=
    exists_strict_separator_of_weak_of_boundary_affineIndependent
      (φ := S.φ) (P := P) (N := N) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.positive₁ x hx
        · exact S.positive₂ x hx) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.negative₃ x hx
        · exact S.negative₄ x hx) hdisj hBind
  refine ⟨
    { φ := ψ
      Y₁ := S.Y₁
      Y₂ := S.Y₂
      Y₃ := S.Y₃
      Y₄ := S.Y₄
      half₁ := S.half₁
      half₂ := S.half₂
      half₃ := S.half₃
      half₄ := S.half₄
      positive₁ := fun x hx ↦ hψ.1 x (Finset.mem_union_left _ hx)
      positive₂ := fun x hx ↦ hψ.1 x (Finset.mem_union_right _ hx)
      negative₃ := fun x hx ↦ hψ.2 x (Finset.mem_union_left _ hx)
      negative₄ := fun x hx ↦ hψ.2 x (Finset.mem_union_right _ hx) }⟩

/-- Iteration-friendly ambient wrapper for the unconditional theorem. -/
theorem exists_orientedHalfSelection_of_subset_ambient
    (U X₁ X₂ X₃ X₄ : Finset (Point 3))
    (hX₁ : X₁ ⊆ U) (hX₂ : X₂ ⊆ U) (hX₃ : X₃ ⊆ U) (hX₄ : X₄ ⊆ U)
    (hdisj : Disjoint (X₁ ∪ X₂) (X₃ ∪ X₄))
    (hcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  obtain ⟨φ, hφ, h₁, h₂, h₃⟩ := threeSetDiscreteHamSandwich X₁ X₂ X₃
  let S := closedOrientedHalfSelection_of_bisectsThree X₁ X₂ X₃ X₄ φ h₁ h₂ h₃ hφ
  have hselDisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄) := by
    apply hdisj.mono
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₁.1 hx)
      · exact Finset.mem_union_right _ (S.half₂.1 hx)
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₃.1 hx)
      · exact Finset.mem_union_right _ (S.half₄.1 hx)
  exact S.exists_strictification_in_ambient hX₁ hX₂ hX₃ hX₄ hselDisj hcard hgp

/-- The selected positive and negative unions have disjoint convex hulls. -/
theorem OrientedHalfSelection.convexHulls_disjoint
    {X₁ X₂ X₃ X₄ : Finset (Point 3)}
    (S : OrientedHalfSelection X₁ X₂ X₃ X₄) :
    Disjoint
      (convexHull ℝ (↑(S.Y₁ ∪ S.Y₂) : Set (Point 3)))
      (convexHull ℝ (↑(S.Y₃ ∪ S.Y₄) : Set (Point 3))) := by
  apply convexHulls_disjoint_of_strictlySeparates (φ := S.φ)
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact S.positive₁ x hx
    · exact S.positive₂ x hx
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact S.negative₃ x hx
    · exact S.negative₄ x hx

end

end

/-! ### Upstream module `JSP527/External/Erdos651/TwoSeparation.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Two-separated families of point clusters

This file contains the separation notions used in Propositions 2.5 and 2.7
of Pohoata--Zakharov.  All hulls below are actual convex hulls in `ℝ³`.
-/

open _root_.Set

noncomputable section

private def vsubMatrix_v1 (a b c d : Point 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![b - a, c - a, d - a] j i

private def orientedVolume_v2 (a b c d : Point 3) : ℝ :=
  (vsubMatrix_v1 a b c d).det

private lemma orientedVolume_eq_v3 (a b c d : Point 3) :
    orientedVolume_v2 a b c d =
      (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
      (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
      (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0)) := by
  simp [orientedVolume_v2, vsubMatrix_v1, Matrix.det_fin_three]
  ring

private def orientedVolumeLinear_v4 (a b c : Point 3) : Point 3 →ₗ[ℝ] ℝ where
  toFun p := orientedVolume_v2 a b c p - orientedVolume_v2 a b c 0
  map_add' p q := by
    rw [orientedVolume_eq_v3, orientedVolume_eq_v3, orientedVolume_eq_v3, orientedVolume_eq_v3]
    change _ = _
    have hadd (i : Fin 3) : (p + q) i = p i + q i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hadd, hzero]
    ring
  map_smul' r p := by
    rw [orientedVolume_eq_v3, orientedVolume_eq_v3, orientedVolume_eq_v3]
    change _ = _
    have hsmul (i : Fin 3) : (r • p) i = r * p i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hsmul, hzero, RingHom.id_apply]
    ring

private def orientedVolumeAffine_v5 (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (orientedVolumeLinear_v4 a b c).toAffineMap +
    AffineMap.const ℝ (Point 3) (orientedVolume_v2 a b c 0)

@[simp] private lemma orientedVolumeAffine_apply_v6 (a b c p : Point 3) :
    orientedVolumeAffine_v5 a b c p = orientedVolume_v2 a b c p := by
  simp [orientedVolumeAffine_v5, orientedVolumeLinear_v4]

private lemma orientedVolume_ne_zero_of_affineIndependent_v7 {a b c d : Point 3}
    (h : AffineIndependent ℝ ![a, b, c, d]) : orientedVolume_v2 a b c d ≠ 0 := by
  have hv : LinearIndependent ℝ ![b - a, c - a, d - a] := by
    apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 4)) ?_).mpr
      ((affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c, d] 0).mp h)
    funext i
    fin_cases i <;> rfl
  have hcols : LinearIndependent ℝ (vsubMatrix_v1 a b c d).col := by
    have hmapped := hv.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun :
        (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) =
          (vsubMatrix_v1 a b c d).col := by
      funext j i
      rfl
    change LinearIndependent ℝ
      (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) at hmapped
    rw [hfun] at hmapped
    exact hmapped
  exact ((Matrix.isUnit_iff_isUnit_det (vsubMatrix_v1 a b c d)).mp
    ((Matrix.linearIndependent_cols_iff_isUnit).mp hcols)).ne_zero

/-- The union of the clusters with indices in `I`. -/
def clusterUnion {k : ℕ} (X : Fin k → Finset (Point 3))
    (I : Finset (Fin k)) : Finset (Point 3) :=
  I.biUnion X

@[simp] theorem clusterUnion_empty {k : ℕ}
    (X : Fin k → Finset (Point 3)) :
    clusterUnion X ∅ = ∅ := by
  simp [clusterUnion]

@[simp] theorem clusterUnion_singleton {k : ℕ}
    (X : Fin k → Finset (Point 3)) (i : Fin k) :
    clusterUnion X {i} = X i := by
  simp [clusterUnion]

theorem clusterUnion_mono {k : ℕ} {X Y : Fin k → Finset (Point 3)}
    (hXY : ∀ i, X i ⊆ Y i) (I : Finset (Fin k)) :
    clusterUnion X I ⊆ clusterUnion Y I := by
  classical
  intro x hx
  simp only [clusterUnion, Finset.mem_biUnion] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hi, hXY i hxi⟩

theorem clusterUnion_index_mono {k : ℕ} (X : Fin k → Finset (Point 3))
    {I J : Finset (Fin k)} (hIJ : I ⊆ J) :
    clusterUnion X I ⊆ clusterUnion X J := by
  classical
  intro x hx
  simp only [clusterUnion, Finset.mem_biUnion] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hIJ hi, hxi⟩

/-- The point set obtained by taking every cluster. -/
def allClusters {k : ℕ} (X : Fin k → Finset (Point 3)) :
    Finset (Point 3) :=
  clusterUnion X Finset.univ

theorem mem_allClusters_iff {k : ℕ} {X : Fin k → Finset (Point 3)}
    {x : Point 3} :
    x ∈ allClusters X ↔ ∃ i, x ∈ X i := by
  classical
  simp [allClusters, clusterUnion]

/-- The clusters are pairwise disjoint as finite point sets. -/
def PairwiseDisjointClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → Disjoint (X i) (X j)

/-- Pohoata--Zakharov's `2`-separation condition.  Convex hulls belonging
to two disjoint pairs of cluster indices do not meet. -/
def TwoSeparatedClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ ⦃i j i' j' : Fin k⦄,
    i ≠ j → i' ≠ j' →
    Disjoint ({i, j} : Finset (Fin k)) {i', j'} →
    Disjoint
      (convexHull ℝ ((X i ∪ X j : Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ ((X i' ∪ X j' : Finset (Point 3)) : Set (Point 3)))

/-- The strong convex-position hypothesis for a family of clusters: the
convex hull of any one cluster misses the hull of all the other clusters. -/
def StrongConvexPositionClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ i,
    Disjoint
      (convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        ((clusterUnion X (Finset.univ.erase i) : Finset (Point 3)) : Set (Point 3)))

theorem PairwiseDisjointClusters.mono {k : ℕ}
    {X Y : Fin k → Finset (Point 3)}
    (hX : PairwiseDisjointClusters X) (hYX : ∀ i, Y i ⊆ X i) :
    PairwiseDisjointClusters Y := by
  intro i j hij
  exact (hX hij).mono (hYX i) (hYX j)

theorem StrongConvexPositionClusters.mono {k : ℕ}
    {X Y : Fin k → Finset (Point 3)}
    (hX : StrongConvexPositionClusters X) (hYX : ∀ i, Y i ⊆ X i) :
    StrongConvexPositionClusters Y := by
  intro i
  apply (hX i).mono
  · exact convexHull_mono (by
      intro x hx
      exact hYX i hx)
  · exact convexHull_mono (clusterUnion_mono hYX _)

/-- Strong convex position in particular forces distinct clusters to be
disjoint.  This is useful when assigning a Kirchberger witness point to its
unique cluster. -/
theorem StrongConvexPositionClusters.pairwiseDisjoint {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (hX : StrongConvexPositionClusters X) :
    PairwiseDisjointClusters X := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro y hyi hyj
  have hyHullI : y ∈ convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hyi)
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin k)) := by
    simp [hij.symm]
  have hyOthers : y ∈ clusterUnion X (Finset.univ.erase i) := by
    simp only [clusterUnion, Finset.mem_biUnion]
    exact ⟨j, hj, hyj⟩
  have hyHullOthers :
      y ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase i) : Finset (Point 3)) :
          Set (Point 3)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hyOthers)
  exact Set.disjoint_left.1 (hX i) hyHullI hyHullOthers

/-! ### The iterative two-separation selection -/

/-- One of the three unordered pairings of four different cluster indices.
The inequalities order each pair, and put first the pair containing the
least of the four indices.  Thus every pairing is represented exactly once. -/
@[ext] structure SeparationCut (k : ℕ) where
  p₁ : Fin k
  p₂ : Fin k
  n₁ : Fin k
  n₂ : Fin k
  hp : p₁ < p₂
  hn : n₁ < n₂
  hfirst : p₁ < n₁
  hdisj : Disjoint ({p₁, p₂} : Finset (Fin k)) {n₁, n₂}
  deriving DecidableEq, Fintype

namespace SeparationCut

def Contains {k : ℕ} (c : SeparationCut k) (i : Fin k) : Prop :=
  i = c.p₁ ∨ i = c.p₂ ∨ i = c.n₁ ∨ i = c.n₂

instance {k : ℕ} (c : SeparationCut k) (i : Fin k) : Decidable (c.Contains i) := by
  unfold Contains
  infer_instance

@[simp] theorem contains_p₁ {k : ℕ} (c : SeparationCut k) : c.Contains c.p₁ :=
  Or.inl rfl

@[simp] theorem contains_p₂ {k : ℕ} (c : SeparationCut k) : c.Contains c.p₂ :=
  Or.inr (Or.inl rfl)

theorem pair_ne {k : ℕ} (c : SeparationCut k) : c.p₁ ≠ c.p₂ := ne_of_lt c.hp

theorem neg_ne {k : ℕ} (c : SeparationCut k) : c.n₁ ≠ c.n₂ := ne_of_lt c.hn

theorem cross_ne {k : ℕ} (c : SeparationCut k) :
    c.p₁ ≠ c.n₁ ∧ c.p₁ ≠ c.n₂ ∧
      c.p₂ ≠ c.n₁ ∧ c.p₂ ≠ c.n₂ := by
  have hd := Finset.disjoint_left.mp c.hdisj
  constructor
  · intro h
    exact hd (a := c.p₁) (by simp) (by simp [h])
  constructor
  · intro h
    exact hd (a := c.p₁) (by simp) (by simp [h])
  constructor
  · intro h
    exact hd (a := c.p₂) (by simp) (by simp [h])
  · intro h
    exact hd (a := c.p₂) (by simp) (by simp [h])

/-- For a fixed participating index, a cut is determined by its partner and
the ordered endpoints of the other pair. -/
private def codeAt {k : ℕ} (i : Fin k) (c : SeparationCut k) :
    Fin k × Fin k × Fin k :=
  if i = c.p₁ then (c.p₂, c.n₁, c.n₂)
  else if i = c.p₂ then (c.p₁, c.n₁, c.n₂)
  else if i = c.n₁ then (c.n₂, c.p₁, c.p₂)
  else (c.n₁, c.p₁, c.p₂)

private theorem codeAt_p₁ {k : ℕ} (c : SeparationCut k) :
    codeAt c.p₁ c = (c.p₂, c.n₁, c.n₂) := by
  simp [codeAt]

private theorem codeAt_p₂ {k : ℕ} (c : SeparationCut k) :
    codeAt c.p₂ c = (c.p₁, c.n₁, c.n₂) := by
  simp [codeAt, c.pair_ne.symm]

private theorem codeAt_n₁ {k : ℕ} (c : SeparationCut k) :
    codeAt c.n₁ c = (c.n₂, c.p₁, c.p₂) := by
  obtain ⟨hp₁n₁, _, hp₂n₁, _⟩ := c.cross_ne
  simp [codeAt, hp₁n₁.symm, hp₂n₁.symm]

private theorem codeAt_n₂ {k : ℕ} (c : SeparationCut k) :
    codeAt c.n₂ c = (c.n₁, c.p₁, c.p₂) := by
  obtain ⟨_, hp₁n₂, _, hp₂n₂⟩ := c.cross_ne
  simp [codeAt, hp₁n₂.symm, hp₂n₂.symm, c.neg_ne.symm]

private theorem codeAt_injective {k : ℕ} (i : Fin k) :
    Set.InjOn (codeAt i) {c : SeparationCut k | c.Contains i} := by
  intro c hc d hd hcode
  change c.Contains i at hc
  change d.Contains i at hd
  have chp := c.hp
  have chn := c.hn
  have chfirst := c.hfirst
  have dhp := d.hp
  have dhn := d.hn
  have dhfirst := d.hfirst
  have codeP₁ (e : SeparationCut k) (h : i = e.p₁) :
      codeAt i e = (e.p₂, e.n₁, e.n₂) := by
    rw [h]
    exact codeAt_p₁ e
  have codeP₂ (e : SeparationCut k) (h : i = e.p₂) :
      codeAt i e = (e.p₁, e.n₁, e.n₂) := by
    rw [h]
    exact codeAt_p₂ e
  have codeN₁ (e : SeparationCut k) (h : i = e.n₁) :
      codeAt i e = (e.n₂, e.p₁, e.p₂) := by
    rw [h]
    exact codeAt_n₁ e
  have codeN₂ (e : SeparationCut k) (h : i = e.n₂) :
      codeAt i e = (e.n₁, e.p₁, e.p₂) := by
    rw [h]
    exact codeAt_n₂ e
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd
  all_goals first
    | rw [codeP₁ c hc, codeP₁ d hd] at hcode
    | rw [codeP₁ c hc, codeP₂ d hd] at hcode
    | rw [codeP₁ c hc, codeN₁ d hd] at hcode
    | rw [codeP₁ c hc, codeN₂ d hd] at hcode
    | rw [codeP₂ c hc, codeP₁ d hd] at hcode
    | rw [codeP₂ c hc, codeP₂ d hd] at hcode
    | rw [codeP₂ c hc, codeN₁ d hd] at hcode
    | rw [codeP₂ c hc, codeN₂ d hd] at hcode
    | rw [codeN₁ c hc, codeP₁ d hd] at hcode
    | rw [codeN₁ c hc, codeP₂ d hd] at hcode
    | rw [codeN₁ c hc, codeN₁ d hd] at hcode
    | rw [codeN₁ c hc, codeN₂ d hd] at hcode
    | rw [codeN₂ c hc, codeP₁ d hd] at hcode
    | rw [codeN₂ c hc, codeP₂ d hd] at hcode
    | rw [codeN₂ c hc, codeN₁ d hd] at hcode
    | rw [codeN₂ c hc, codeN₂ d hd] at hcode
  all_goals simp only [Prod.mk.injEq] at hcode
  all_goals apply SeparationCut.ext <;> omega

theorem number_containing_le_cube {k : ℕ} (i : Fin k) :
    ((Finset.univ : Finset (SeparationCut k)).filter fun c ↦ c.Contains i).card ≤ k ^ 3 := by
  classical
  let C := (Finset.univ : Finset (SeparationCut k)).filter fun c ↦ c.Contains i
  have hinj : Set.InjOn (codeAt i) (C : Set (SeparationCut k)) := by
    intro c hc d hd
    apply codeAt_injective i
    · exact (Finset.mem_filter.mp hc).2
    · exact (Finset.mem_filter.mp hd).2
  have himage : (C.image (codeAt i)).card = C.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : C.image (codeAt i) ⊆ Finset.univ := Finset.subset_univ _
  calc
    C.card = (C.image (codeAt i)).card := himage.symm
    _ ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k)).card := Finset.card_le_card hsub
    _ = k ^ 3 := by simp [pow_succ, mul_assoc]

/-- Replace the four participating clusters by the four selected halves. -/
private noncomputable def selectedFamily {k : ℕ}
    (Y : Fin k → Finset (Point 3)) (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    Fin k → Finset (Point 3) := fun i ↦
  if i = c.p₁ then S.Y₁
  else if i = c.p₂ then S.Y₂
  else if i = c.n₁ then S.Y₃
  else if i = c.n₂ then S.Y₄
  else Y i

private theorem selectedFamily_subset {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    ∀ i, selectedFamily Y c S i ⊆ Y i := by
  intro i
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  by_cases h₁ : i = c.p₁
  · subst i
    simpa [selectedFamily, c.pair_ne, hp₁n₁, hp₁n₂] using S.half₁.1
  by_cases h₂ : i = c.p₂
  · subst i
    simpa [selectedFamily, c.pair_ne.symm, hp₂n₁, hp₂n₂] using S.half₂.1
  by_cases h₃ : i = c.n₁
  · subst i
    simpa [selectedFamily, h₁, h₂, c.neg_ne, hp₁n₁.symm,
      hp₂n₁.symm] using S.half₃.1
  by_cases h₄ : i = c.n₂
  · subst i
    simpa [selectedFamily, h₁, h₂, h₃, c.neg_ne.symm,
      hp₁n₂.symm, hp₂n₂.symm] using S.half₄.1
  · simp [selectedFamily, h₁, h₂, h₃, h₄]

private theorem selectedFamily_half {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂))
    (i : Fin k) :
    (Y i).card ≤ 2 ^ (if c.Contains i then 1 else 0) *
      (selectedFamily Y c S i).card := by
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  by_cases h₁ : i = c.p₁
  · subst i
    simpa [selectedFamily, c.pair_ne, hp₁n₁, hp₁n₂] using S.half₁.2
  by_cases h₂ : i = c.p₂
  · subst i
    simpa [selectedFamily, c.pair_ne.symm, hp₂n₁, hp₂n₂] using S.half₂.2
  by_cases h₃ : i = c.n₁
  · subst i
    simpa [selectedFamily, h₁, h₂, c.neg_ne, hp₁n₁.symm,
      hp₂n₁.symm, Contains] using S.half₃.2
  by_cases h₄ : i = c.n₂
  · subst i
    simpa [selectedFamily, h₁, h₂, h₃, c.neg_ne.symm,
      hp₁n₂.symm, hp₂n₂.symm, Contains] using S.half₄.2
  · have hnot : ¬ c.Contains i := by
      simp only [Contains, not_or]
      exact ⟨h₁, h₂, h₃, h₄⟩
    simp [selectedFamily, h₁, h₂, h₃, h₄, hnot]

private theorem selectedFamily_separates {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    Disjoint
      (convexHull ℝ
        (((selectedFamily Y c S c.p₁) ∪ (selectedFamily Y c S c.p₂) :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        (((selectedFamily Y c S c.n₁) ∪ (selectedFamily Y c S c.n₂) :
          Finset (Point 3)) : Set (Point 3))) := by
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  have e₁ : selectedFamily Y c S c.p₁ = S.Y₁ := by
    simp [selectedFamily]
  have e₂ : selectedFamily Y c S c.p₂ = S.Y₂ := by
    simp [selectedFamily, c.pair_ne.symm]
  have e₃ : selectedFamily Y c S c.n₁ = S.Y₃ := by
    simp [selectedFamily, hp₁n₁.symm, hp₂n₁.symm]
  have e₄ : selectedFamily Y c S c.n₂ = S.Y₄ := by
    simp [selectedFamily, hp₁n₂.symm, hp₂n₂.symm, c.neg_ne.symm]
  simpa only [e₁, e₂, e₃, e₄] using S.convexHulls_disjoint

end SeparationCut

/-- A current family together with the fact that it was obtained by shrinking
the original clusters. -/
private structure ClusterSubfamily {k : ℕ}
    (X : Fin k → Finset (Point 3)) where
  family : Fin k → Finset (Point 3)
  subset : ∀ i, family i ⊆ X i

private theorem allClusters_card_ge_four_of_cut {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (c : SeparationCut k) : 4 ≤ (allClusters X).card := by
  classical
  have hne (i : Fin k) : (X i).Nonempty := by
    apply Finset.card_pos.mp
    have := hcard i
    have : 0 < 2 ^ (k ^ 3) := pow_pos (by omega : 0 < (2 : ℕ)) _
    omega
  choose xp hxp using fun i ↦ hne i
  let W : Finset (Point 3) := {xp c.p₁, xp c.p₂, xp c.n₁, xp c.n₂}
  have hxp_ne {i j : Fin k} (hij : i ≠ j) : xp i ≠ xp j := by
    intro heq
    have hd := hdisj hij
    rw [Finset.disjoint_left] at hd
    have hxj : xp i ∈ X j := by simpa [heq] using hxp j
    exact hd (hxp i) hxj
  have hWcard : W.card = 4 := by
    obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
    simp [W, hxp_ne c.pair_ne, hxp_ne c.neg_ne, hxp_ne hp₁n₁,
      hxp_ne hp₁n₂, hxp_ne hp₂n₁, hxp_ne hp₂n₂]
  have hWU : W ⊆ allClusters X := by
    intro y hy
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    all_goals rw [mem_allClusters_iff]; exact ⟨_, hxp _⟩
  rw [← hWcard]
  exact Finset.card_le_card hWU

private theorem cut_pair_disjoint {k : ℕ}
    {Y : Fin k → Finset (Point 3)}
    (hY : PairwiseDisjointClusters Y) (c : SeparationCut k) :
    Disjoint (Y c.p₁ ∪ Y c.p₂) (Y c.n₁ ∪ Y c.n₂) := by
  rw [Finset.disjoint_left]
  intro y hyp hyn
  rcases Finset.mem_union.mp hyp with hyp | hyp <;>
    rcases Finset.mem_union.mp hyn with hyn | hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.2.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.2.2) hyp hyn

/-- Perform one of the finitely many strict ham-sandwich cuts. -/
private noncomputable def applySeparationCut {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) : ClusterSubfamily X := by
  let U := allClusters X
  have hYU (i : Fin k) : Y.family i ⊆ U := by
    intro y hy
    rw [mem_allClusters_iff]
    exact ⟨i, Y.subset i hy⟩
  let S := Classical.choice (exists_orientedHalfSelection_of_subset_ambient
    U (Y.family c.p₁) (Y.family c.p₂) (Y.family c.n₁) (Y.family c.n₂)
    (hYU c.p₁) (hYU c.p₂) (hYU c.n₁) (hYU c.n₂)
    (cut_pair_disjoint (hdisj.mono Y.subset) c)
    (allClusters_card_ge_four_of_cut hdisj hcard c) hgp)
  exact
    { family := SeparationCut.selectedFamily Y.family c S
      subset := fun i ↦ (SeparationCut.selectedFamily_subset c S i).trans (Y.subset i) }

private theorem applySeparationCut_subset {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) :
    ∀ i, (applySeparationCut X hdisj hcard hgp c Y).family i ⊆ Y.family i := by
  intro i
  exact SeparationCut.selectedFamily_subset _ _ _

private theorem applySeparationCut_half {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) (i : Fin k) :
    (Y.family i).card ≤ 2 ^ (if c.Contains i then 1 else 0) *
      ((applySeparationCut X hdisj hcard hgp c Y).family i).card := by
  exact SeparationCut.selectedFamily_half _ _ _

private theorem applySeparationCut_separates {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) :
    Disjoint
      (convexHull ℝ
        ((((applySeparationCut X hdisj hcard hgp c Y).family c.p₁) ∪
          ((applySeparationCut X hdisj hcard hgp c Y).family c.p₂) :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        ((((applySeparationCut X hdisj hcard hgp c Y).family c.n₁) ∪
          ((applySeparationCut X hdisj hcard hgp c Y).family c.n₂) :
          Finset (Point 3)) : Set (Point 3))) := by
  exact SeparationCut.selectedFamily_separates _ _

private noncomputable def runSeparationCuts {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X)) :
    List (SeparationCut k) → ClusterSubfamily X → ClusterSubfamily X
  | [], Y => Y
  | c :: cs, Y => runSeparationCuts X hdisj hcard hgp cs
      (applySeparationCut X hdisj hcard hgp c Y)

private theorem runSeparationCuts_subset {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X) :
    ∀ i, (runSeparationCuts X hdisj hcard hgp cs Y).family i ⊆ Y.family i := by
  induction cs generalizing Y with
  | nil => exact fun i ↦ Finset.Subset.rfl
  | cons c cs ih =>
      intro i
      exact (ih _ i).trans (applySeparationCut_subset X hdisj hcard hgp c Y i)

private theorem runSeparationCuts_loss {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X) (i : Fin k) :
    (Y.family i).card ≤
      2 ^ (cs.countP fun c ↦ c.Contains i) *
        ((runSeparationCuts X hdisj hcard hgp cs Y).family i).card := by
  induction cs generalizing Y with
  | nil => simp [runSeparationCuts]
  | cons c cs ih =>
      let Z := applySeparationCut X hdisj hcard hgp c Y
      have hstep := applySeparationCut_half X hdisj hcard hgp c Y i
      have htail := ih Z
      calc
        (Y.family i).card ≤ 2 ^ (if c.Contains i then 1 else 0) * (Z.family i).card := hstep
        _ ≤ 2 ^ (if c.Contains i then 1 else 0) *
              (2 ^ (cs.countP fun d ↦ d.Contains i) *
                ((runSeparationCuts X hdisj hcard hgp cs Z).family i).card) :=
          Nat.mul_le_mul_left _ htail
        _ = 2 ^ ((c :: cs).countP fun d ↦ d.Contains i) *
              ((runSeparationCuts X hdisj hcard hgp (c :: cs) Y).family i).card := by
          simp only [List.countP_cons, runSeparationCuts]
          split <;> simp_all [pow_succ, Z] <;> ring

private theorem runSeparationCuts_separates {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X)
    {c : SeparationCut k} (hc : c ∈ cs) :
    Disjoint
      (convexHull ℝ
        (((runSeparationCuts X hdisj hcard hgp cs Y).family c.p₁ ∪
          (runSeparationCuts X hdisj hcard hgp cs Y).family c.p₂ :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        (((runSeparationCuts X hdisj hcard hgp cs Y).family c.n₁ ∪
          (runSeparationCuts X hdisj hcard hgp cs Y).family c.n₂ :
          Finset (Point 3)) : Set (Point 3))) := by
  induction cs generalizing Y with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      let Z := applySeparationCut X hdisj hcard hgp d Y
      rcases hc with hcd | hc
      · subst c
        apply (applySeparationCut_separates X hdisj hcard hgp d Y).mono
        all_goals
          apply convexHull_mono
          intro y hy
          simp only [Finset.coe_union, mem_union, Finset.mem_coe] at hy ⊢
          exact hy.elim
            (fun h ↦ Or.inl (runSeparationCuts_subset X hdisj hcard hgp ds Z _ h))
            (fun h ↦ Or.inr (runSeparationCuts_subset X hdisj hcard hgp ds Z _ h))
      · exact ih Z hc

private theorem pair_disjoint_of_cross_ne {α : Type*} [DecidableEq α]
    {a b c d : α} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint ({a, b} : Finset α) {c, d} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with hxa | hxb <;> rcases hx₂ with hxc | hxd
  · exact hac (hxa.symm.trans hxc)
  · exact had (hxa.symm.trans hxd)
  · exact hbc (hxb.symm.trans hxc)
  · exact hbd (hxb.symm.trans hxd)

private theorem vector4_injective_of_pairwise {α : Type*}
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem exists_separationCut_of_ordered_pairs {k : ℕ}
    {a b c d : Fin k} (hab : a < b) (hcd : c < d)
    (hdisj : Disjoint ({a, b} : Finset (Fin k)) {c, d}) :
    ∃ q : SeparationCut k,
      (q.p₁ = a ∧ q.p₂ = b ∧ q.n₁ = c ∧ q.n₂ = d) ∨
      (q.p₁ = c ∧ q.p₂ = d ∧ q.n₁ = a ∧ q.n₂ = b) := by
  have hac : a ≠ c := by
    intro h
    subst c
    have hd := Finset.disjoint_left.mp hdisj
    exact hd (a := a) (by simp) (by simp)
  rcases lt_or_gt_of_ne hac with hac | hca
  · exact ⟨⟨a, b, c, d, hab, hcd, hac, hdisj⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨⟨c, d, a, b, hcd, hab, hca, hdisj.symm⟩,
      Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem exists_separationCut_of_pairs {k : ℕ}
    {i j i' j' : Fin k} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hdisj : Disjoint ({i, j} : Finset (Fin k)) {i', j'}) :
    ∃ q : SeparationCut k,
      (((q.p₁ = i ∧ q.p₂ = j) ∨ (q.p₁ = j ∧ q.p₂ = i)) ∧
        ((q.n₁ = i' ∧ q.n₂ = j') ∨ (q.n₁ = j' ∧ q.n₂ = i'))) ∨
      (((q.p₁ = i' ∧ q.p₂ = j') ∨ (q.p₁ = j' ∧ q.p₂ = i')) ∧
        ((q.n₁ = i ∧ q.n₂ = j) ∨ (q.n₁ = j ∧ q.n₂ = i))) := by
  rcases lt_or_gt_of_ne hij with hij | hji <;>
    rcases lt_or_gt_of_ne hi'j' with hi'j' | hj'i'
  · obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hij hi'j' hdisj
    · exact ⟨q, Or.inl ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({i, j} : Finset (Fin k)) {j', i'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hij hj'i' hd
    · exact ⟨q, Or.inl ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({j, i} : Finset (Fin k)) {i', j'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hji hi'j' hd
    · exact ⟨q, Or.inl ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({j, i} : Finset (Fin k)) {j', i'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hji hj'i' hd
    · exact ⟨q, Or.inl ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩

/-- Pohoata--Zakharov Proposition 2.5.  Processing the three pairings of
every four indices loses at most a factor `2^(k^3)` from each cluster. -/
theorem exists_twoSeparated_subclusters {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X)) :
    ∃ Y : Fin k → Finset (Point 3),
      (∀ i, Y i ⊆ X i) ∧ TwoSeparatedClusters Y ∧
        ∀ i, (X i).card ≤ 2 ^ (k ^ 3) * (Y i).card := by
  classical
  let initial : ClusterSubfamily X := ⟨X, fun _ ↦ Finset.Subset.rfl⟩
  let cuts : List (SeparationCut k) := (Finset.univ : Finset (SeparationCut k)).toList
  let final := runSeparationCuts X hdisj hcard hgp cuts initial
  refine ⟨final.family, final.subset, ?_, ?_⟩
  · intro i j i' j' hij hi'j' hpairs
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_pairs hij hi'j' hpairs
    · obtain ⟨hp, hn⟩ := hq
      have hsep := runSeparationCuts_separates X hdisj hcard hgp cuts initial
        (c := q) (by simp [cuts])
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simpa only [Finset.union_comm] using hsep
    · obtain ⟨hp, hn⟩ := hq
      have hsep := runSeparationCuts_separates X hdisj hcard hgp cuts initial
        (c := q) (by simp [cuts])
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simpa only [Finset.union_comm] using hsep.symm
  · intro i
    have hloss := runSeparationCuts_loss X hdisj hcard hgp cuts initial i
    have hcount : (cuts.countP fun c ↦ c.Contains i) ≤ k ^ 3 := by
      rw [← (Finset.univ : Finset (SeparationCut k)).nodup_toList.card_eq_countP]
      simpa [cuts] using SeparationCut.number_containing_le_cube i
    calc
      (X i).card ≤ 2 ^ (cuts.countP fun c ↦ c.Contains i) * (final.family i).card := hloss
      _ ≤ 2 ^ (k ^ 3) * (final.family i).card := by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hcount)

/-! ### The oriented-matroid core of pattern lifting -/

private theorem convexHull_image_subset_clusterHull {k n : ℕ}
    {X : Fin k → Finset (Point 3)} {idx : Fin n → Fin k}
    {p : Fin n → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    (S : Finset (Fin n)) :
    convexHull ℝ (p '' (S : Set (Fin n))) ⊆
      convexHull ℝ
        ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3)) := by
  apply convexHull_min
  · rintro y ⟨t, ht, rfl⟩
    apply convexHull_mono (s := ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
      (t := ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3))) ?_ (hp t)
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨idx t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hy⟩
  · exact convex_convexHull ℝ _

/-- Four points chosen from the four cluster hulls are affinely independent.
The `1+3` Radon partitions are excluded by strong convex position, and the
`2+2` partitions by two-separation. -/
private theorem affineIndependent_four_clusterHull_points {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3))) :
    AffineIndependent ℝ p := by
  classical
  by_contra hdep
  obtain ⟨I, z, hzI, hzIc⟩ := Convex.radon_partition hdep
  let S : Finset (Fin 4) := I.toFinite.toFinset
  let T : Finset (Fin 4) := Finset.univ \ S
  have hScoe : (S : Set (Fin 4)) = I := I.toFinite.coe_toFinset
  have hTcoe : (T : Set (Fin 4)) = Iᶜ := by
    ext t
    simp [T, hScoe]
  have hzS : z ∈ convexHull ℝ
      ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3)) :=
    convexHull_image_subset_clusterHull hp S (by simpa [hScoe] using hzI)
  have hzT : z ∈ convexHull ℝ
      ((clusterUnion X (T.image idx) : Finset (Point 3)) : Set (Point 3)) :=
    convexHull_image_subset_clusterHull hp T (by simpa [hTcoe] using hzIc)
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hzS
    simpa only [Finset.image_empty, clusterUnion_empty, Finset.coe_empty,
      convexHull_empty, Set.mem_empty_iff_false] using hzS
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hzT
    simpa only [Finset.image_empty, clusterUnion_empty, Finset.coe_empty,
      convexHull_empty, Set.mem_empty_iff_false] using hzT
  have hSTcard : S.card + T.card = 4 := by
    change S.card + (Finset.univ \ S).card = 4
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    have hle := Finset.card_le_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hle ⊢
    omega
  by_cases hSone : S.card = 1
  · obtain ⟨s, hS⟩ := Finset.card_eq_one.mp hSone
    have hTim : ({s} : Finset (Fin 4)).image idx = {idx s} := by simp
    have hother : T.image idx ⊆ (Finset.univ.erase (idx s) : Finset (Fin k)) := by
      intro j hj
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
      have hts : t ≠ s := by
        intro h
        subst t
        simp [T, hS] at ht
      simp [hidx.ne hts]
    have hzOthers : z ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase (idx s)) : Finset (Point 3)) : Set (Point 3)) :=
      convexHull_mono (clusterUnion_index_mono X hother) hzT
    have hzOne : z ∈ convexHull ℝ ((X (idx s) : Finset (Point 3)) : Set (Point 3)) := by
      simpa [hS, hTim] using hzS
    exact Set.disjoint_left.mp (hstrong (idx s)) hzOne hzOthers
  by_cases hTone : T.card = 1
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hTone
    have hSim : ({t} : Finset (Fin 4)).image idx = {idx t} := by simp
    have hother : S.image idx ⊆ (Finset.univ.erase (idx t) : Finset (Fin k)) := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      have hst : s ≠ t := by
        intro h
        subst s
        have : t ∈ T := by simpa [ht]
        simp [T, hs] at this
      simp [hidx.ne hst]
    have hzOthers : z ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase (idx t)) : Finset (Point 3)) : Set (Point 3)) :=
      convexHull_mono (clusterUnion_index_mono X hother) hzS
    have hzOne : z ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
      rw [ht] at hzT
      simpa [hSim] using hzT
    exact Set.disjoint_left.mp (hstrong (idx t)) hzOne hzOthers
  · have hScard : S.card = 2 := by
      have := Finset.card_pos.mpr hSne
      have := Finset.card_pos.mpr hTne
      omega
    have hTcard : T.card = 2 := by omega
    obtain ⟨s₁, s₂, hsne, hS⟩ := Finset.card_eq_two.mp hScard
    obtain ⟨t₁, t₂, htne, ht⟩ := Finset.card_eq_two.mp hTcard
    have hcross₁₁ : s₁ ≠ t₁ := by
      intro h
      subst t₁
      have : s₁ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₁₂ : s₁ ≠ t₂ := by
      intro h
      subst t₂
      have : s₁ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₂₁ : s₂ ≠ t₁ := by
      intro h
      subst t₁
      have : s₂ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₂₂ : s₂ ≠ t₂ := by
      intro h
      subst t₂
      have : s₂ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hpairs : Disjoint ({idx s₁, idx s₂} : Finset (Fin k)) {idx t₁, idx t₂} := by
      exact pair_disjoint_of_cross_ne (hidx.ne hcross₁₁) (hidx.ne hcross₁₂)
        (hidx.ne hcross₂₁) (hidx.ne hcross₂₂)
    have hsep := htwo (hidx.ne hsne) (hidx.ne htne) hpairs
    apply Set.disjoint_left.mp hsep
    · simpa [hS, clusterUnion] using hzS
    · rw [ht] at hzT
      simpa [clusterUnion] using hzT

private theorem affineMap_same_sign_on_convex {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (φ : E →ᵃ[ℝ] ℝ) {C : Set E} (hC : Convex ℝ C)
    {p q : E} (hp : p ∈ C) (hq : q ∈ C)
    (hnone : ∀ r ∈ C, φ r ≠ 0) : 0 < φ p * φ q := by
  have hp0 := hnone p hp
  have hq0 := hnone q hq
  rcases hp0.lt_or_gt with hpneg | hppos
  · rcases hq0.lt_or_gt with hqneg | hqpos
    · exact mul_pos_of_neg_of_neg hpneg hqneg
    · let t : ℝ := -φ p / (φ q - φ p)
      have hden : 0 < φ q - φ p := sub_pos.mpr (hpneg.trans hqpos)
      have ht0 : 0 < t := div_pos (neg_pos.mpr hpneg) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hr := hC.lineMap_mem hp hq ⟨ht0.le, ht1.le⟩
      have hz : φ (AffineMap.lineMap p q t) = 0 := by
        rw [φ.apply_lineMap, AffineMap.lineMap_apply_ring]
        dsimp [t]
        field_simp
        ring
      exact False.elim (hnone _ hr hz)
  · rcases hq0.lt_or_gt with hqneg | hqpos
    · let t : ℝ := -φ q / (φ p - φ q)
      have hden : 0 < φ p - φ q := sub_pos.mpr (hqneg.trans hppos)
      have ht0 : 0 < t := div_pos (neg_pos.mpr hqneg) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hr := hC.lineMap_mem hq hp ⟨ht0.le, ht1.le⟩
      have hz : φ (AffineMap.lineMap q p t) = 0 := by
        rw [φ.apply_lineMap, AffineMap.lineMap_apply_ring]
        dsimp [t]
        field_simp
        ring
      exact False.elim (hnone _ hr hz)
    · exact mul_pos hppos hqpos

private lemma orientedVolume_rotate' (a b c d : Point 3) :
    orientedVolume_v2 b c d a = -orientedVolume_v2 a b c d := by
  simp [orientedVolume_v2, vsubMatrix_v1, Matrix.det_fin_three]
  ring

private lemma orientedVolume_cycle_last' (a b c d : Point 3) :
    orientedVolume_v2 a c d b = orientedVolume_v2 a b c d := by
  simp [orientedVolume_v2, vsubMatrix_v1, Matrix.det_fin_three]
  ring

private lemma orientedVolume_swap_last' (a b c d : Point 3) :
    orientedVolume_v2 a b d c = -orientedVolume_v2 a b c d := by
  simp [orientedVolume_v2, vsubMatrix_v1, Matrix.det_fin_three]
  ring

private theorem orientedVolume_last_same_sign {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    {q : Point 3}
    (hq : q ∈ convexHull ℝ ((X (idx 3) : Finset (Point 3)) : Set (Point 3))) :
    0 < orientedVolume_v2 (p 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (p 0) (p 1) (p 2) q := by
  let φ := orientedVolumeAffine_v5 (p 0) (p 1) (p 2)
  have hnone : ∀ r ∈ convexHull ℝ ((X (idx 3) : Finset (Point 3)) : Set (Point 3)),
      φ r ≠ 0 := by
    intro r hr hzero
    have hai : AffineIndependent ℝ ![p 0, p 1, p 2, r] :=
      affineIndependent_four_clusterHull_points htwo hstrong hidx (by
        intro t
        fin_cases t
        · simpa using hp 0
        · simpa using hp 1
        · simpa using hp 2
        · simpa using hr)
    exact orientedVolume_ne_zero_of_affineIndependent_v7 hai (by simpa [φ] using hzero)
  simpa [φ] using affineMap_same_sign_on_convex φ (convex_convexHull ℝ _)
    (hp 3) hq hnone

private theorem orientedVolumes_same_sign_in_clusterHulls {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p q : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    (hq : ∀ t, q t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3))) :
    0 < orientedVolume_v2 (p 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (q 1) (q 2) (q 3) := by
  let r₁ : Fin 4 → Point 3 := ![q 0, p 1, p 2, p 3]
  let r₂ : Fin 4 → Point 3 := ![q 0, q 1, p 2, p 3]
  let r₃ : Fin 4 → Point 3 := ![q 0, q 1, q 2, p 3]
  have hr₁ : ∀ t, r₁ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₁, hp, hq]
  have hr₂ : ∀ t, r₂ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₂, hp, hq]
  have hr₃ : ∀ t, r₃ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₃, hp, hq]
  have h₁last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 1, idx 2, idx 3, idx 0])
    (p := ![p 1, p 2, p 3, p 0]) (q := q 0) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp]) (by simpa using hq 0)
  have h₁ : 0 < orientedVolume_v2 (p 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (p 1) (p 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₁last
    simpa only [orientedVolume_rotate' (p 0) (p 1) (p 2) (p 3),
      orientedVolume_rotate' (q 0) (p 1) (p 2) (p 3), neg_mul_neg] using h₁last
  have h₂last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 0, idx 2, idx 3, idx 1])
    (p := ![q 0, p 2, p 3, p 1]) (q := q 1) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp, hq]) (by simpa using hq 1)
  have h₂ : 0 < orientedVolume_v2 (q 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (q 1) (p 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₂last
    simpa only [orientedVolume_cycle_last' (q 0) (p 1) (p 2) (p 3),
      orientedVolume_cycle_last' (q 0) (q 1) (p 2) (p 3)] using h₂last
  have h₃last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 0, idx 1, idx 3, idx 2])
    (p := ![q 0, q 1, p 3, p 2]) (q := q 2) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp, hq]) (by simpa using hq 2)
  have h₃ : 0 < orientedVolume_v2 (q 0) (q 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (q 1) (q 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₃last
    simpa only [orientedVolume_swap_last' (q 0) (q 1) (p 2) (p 3),
      orientedVolume_swap_last' (q 0) (q 1) (q 2) (p 3), neg_mul_neg] using h₃last
  have h₄ := orientedVolume_last_same_sign htwo hstrong hidx hr₃ (hq 3)
  have h12 : 0 < orientedVolume_v2 (p 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (q 1) (p 2) (p 3) := by
    rcases (mul_pos_iff.mp h₂) with hpos | hneg
    · exact mul_pos (pos_of_mul_pos_left h₁ hpos.1.le) hpos.2
    · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h₁ hneg.1.le) hneg.2
  have h123 : 0 < orientedVolume_v2 (p 0) (p 1) (p 2) (p 3) *
      orientedVolume_v2 (q 0) (q 1) (q 2) (p 3) := by
    rcases (mul_pos_iff.mp h₃) with hpos | hneg
    · exact mul_pos (pos_of_mul_pos_left h12 hpos.1.le) hpos.2
    · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h12 hneg.1.le) hneg.2
  rcases (mul_pos_iff.mp h₄) with hpos | hneg
  · exact mul_pos (pos_of_mul_pos_left h123 hpos.1.le) hpos.2
  · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h123 hneg.1.le) hneg.2

private def fivePoints (a b c d e : Point 3) : Fin 5 → Point 3 := ![a, b, c, d, e]

private def fiveCofactors (a b c d e : Point 3) : Fin 5 → ℝ :=
  ![orientedVolume_v2 b c d e, -orientedVolume_v2 a c d e,
    orientedVolume_v2 a b d e, -orientedVolume_v2 a b c e,
    orientedVolume_v2 a b c d]

private theorem fiveCofactors_sum (a b c d e : Point 3) :
    ∑ i, fiveCofactors a b c d e i = 0 := by
  simp [fiveCofactors, Fin.sum_univ_succ, orientedVolume_v2, vsubMatrix_v1,
    Matrix.det_fin_three]
  ring

private theorem fiveCofactors_point_sum (a b c d e : Point 3) :
    ∑ i, fiveCofactors a b c d e i • fivePoints a b c d e i = 0 := by
  ext j
  fin_cases j <;>
    simp [fiveCofactors, fivePoints, Fin.sum_univ_succ, orientedVolume_v2,
      vsubMatrix_v1, Matrix.det_fin_three] <;> ring

private theorem affineRelation_eq_zero_of_last_zero
    {a b c d e : Point 3} (hai : AffineIndependent ℝ ![a, b, c, d])
    {u : Fin 5 → ℝ} (hsum : ∑ i, u i = 0)
    (hpoint : ∑ i, u i • fivePoints a b c d e i = 0) (hu4 : u 4 = 0) :
    u = 0 := by
  let u₄ : Fin 4 → ℝ := ![u 0, u 1, u 2, u 3]
  have hsum₄ : ∑ i, u₄ i = ∑ i, (0 : Fin 4 → ℝ) i := by
    simpa [u₄, Fin.sum_univ_succ, hu4] using hsum
  have hpoint₄ : ∑ i, u₄ i • ![a, b, c, d] i =
      ∑ i, (0 : Fin 4 → ℝ) i • ![a, b, c, d] i := by
    simpa [u₄, fivePoints, Fin.sum_univ_succ, hu4] using hpoint
  have hu := hai.eq_of_sum_eq_sum (s := Finset.univ) hsum₄ hpoint₄
  funext i
  fin_cases i
  · simpa [u₄] using hu 0 (by simp)
  · simpa [u₄] using hu 1 (by simp)
  · simpa [u₄] using hu 2 (by simp)
  · simpa [u₄] using hu 3 (by simp)
  · simpa [hu4]

private theorem fiveCofactors_proportional
    {a b c d e : Point 3} (hai : AffineIndependent ℝ ![a, b, c, d])
    {u : Fin 5 → ℝ} (hsum : ∑ i, u i = 0)
    (hpoint : ∑ i, u i • fivePoints a b c d e i = 0) (hu4 : u 4 ≠ 0) :
    fiveCofactors a b c d e =
      fun i ↦ (fiveCofactors a b c d e 4 / u 4) * u i := by
  let r := fiveCofactors a b c d e 4 / u 4
  let v : Fin 5 → ℝ := fun i ↦ fiveCofactors a b c d e i - r * u i
  have hvsum : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, ← Finset.mul_sum, fiveCofactors_sum, hsum,
      mul_zero, sub_zero]
  have hvpoint : ∑ i, v i • fivePoints a b c d e i = 0 := by
    rw [show (∑ i, v i • fivePoints a b c d e i) =
        (∑ i, fiveCofactors a b c d e i • fivePoints a b c d e i) -
          r • ∑ i, u i • fivePoints a b c d e i by
      simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]]
    rw [fiveCofactors_point_sum, hpoint, smul_zero, sub_zero]
  have hv4 : v 4 = 0 := by
    dsimp [v, r]
    rw [div_mul_cancel₀ _ hu4, sub_self]
  have hv := affineRelation_eq_zero_of_last_zero hai hvsum hvpoint hv4
  funext i
  have := congr_fun hv i
  simp only [v, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- A strict oriented affine-hyperplane sign function, written as
`normal x - offset`.  Positivity and negativity are the two open
half-spaces. -/
def planeValue (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ)
    (x : Point 3) : ℝ :=
  normal x - offset

/-- A representative `x i` is chosen from every cluster. -/
def IsClusterTransversal {k : ℕ} (X : Fin k → Finset (Point 3))
    (x : Fin k → Point 3) : Prop :=
  ∀ i, x i ∈ X i

/-- The sign pattern of a strict plane on a transversal. -/
def HasRepresentativePlanePattern {k : ℕ}
    (x : Fin k → Point 3) (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  normal ≠ 0 ∧ ∀ i, planeValue normal offset (x i) ≠ 0

/-- A plane on the full clusters realizes exactly the signs induced on the
chosen representatives by another plane. -/
def LiftsRepresentativePlanePattern {k : ℕ}
    (X : Fin k → Finset (Point 3)) (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  ∃ (liftNormal : Point 3 →L[ℝ] ℝ) (liftOffset : ℝ),
    liftNormal ≠ 0 ∧
    ∀ i y, y ∈ X i →
      (0 < planeValue normal offset (x i) →
        0 < planeValue liftNormal liftOffset y) ∧
      (planeValue normal offset (x i) < 0 →
        planeValue liftNormal liftOffset y < 0)

/-- Indices whose representatives lie in the positive open half-space. -/
def positiveClusterIndices {k : ℕ} (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => 0 < planeValue normal offset (x i)

/-- Indices whose representatives lie in the negative open half-space. -/
def negativeClusterIndices {k : ℕ} (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => planeValue normal offset (x i) < 0

/-- The geometric conclusion needed before invoking strict hyperplane
separation: the hulls of the unions of the negative and positive clusters
are disjoint. -/
def RepresentativePatternHullsSeparated {k : ℕ}
    (X : Fin k → Finset (Point 3)) (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  Disjoint
    (convexHull ℝ
      ((clusterUnion X (negativeClusterIndices x normal offset) :
        Finset (Point 3)) : Set (Point 3)))
    (convexHull ℝ
      ((clusterUnion X (positiveClusterIndices x normal offset) :
        Finset (Point 3)) : Set (Point 3)))

private theorem fiveCluster_segment_triangle_pattern_impossible {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {ia ib ic id ie : Fin k}
    (hindices : Function.Injective ![ia, ib, ic, id, ie])
    {a b c d e : Point 3}
    (ha : a ∈ X ia) (hb : b ∈ X ib) (hc : c ∈ X ic)
    (hd : d ∈ X id) (he : e ∈ X ie)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hacneg : planeValue normal offset (x ia) < 0 ∧
      planeValue normal offset (x ic) < 0)
    (hbdeposit : 0 < planeValue normal offset (x ib) ∧
      0 < planeValue normal offset (x id) ∧
      0 < planeValue normal offset (x ie))
    (hinter : (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) : False := by
  classical
  have hidx4 (v : Fin 4 → Fin 5) (hv : Function.Injective v) :
      Function.Injective fun t ↦ ![ia, ib, ic, id, ie] (v t) := hindices.comp hv
  have hinj0 : Function.Injective ![ib, ic, id, ie] := by
    exact vector4_injective_of_pairwise ib ic id ie
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj1 : Function.Injective ![ia, ic, id, ie] := by
    exact vector4_injective_of_pairwise ia ic id ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj2 : Function.Injective ![ia, ib, id, ie] := by
    exact vector4_injective_of_pairwise ia ib id ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj3 : Function.Injective ![ia, ib, ic, ie] := by
    exact vector4_injective_of_pairwise ia ib ic ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
  have hinj4 : Function.Injective ![ia, ib, ic, id] := by
    exact vector4_injective_of_pairwise ia ib ic id
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
  have hpHull (i : Fin k) {y : Point 3} (hy : y ∈ X i) :
      y ∈ convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)) :=
    subset_convexHull ℝ _ hy
  have hvol0 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ib, ic, id, ie]) (p := ![b, c, d, e])
    (q := ![x ib, x ic, x id, x ie])
    hinj0 (by
      intro t; fin_cases t
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol1 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ic, id, ie]) (p := ![a, c, d, e])
    (q := ![x ia, x ic, x id, x ie])
    hinj1 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ic hc
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol2 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, id, ie]) (p := ![a, b, d, e])
    (q := ![x ia, x ib, x id, x ie])
    hinj2 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol3 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, ic, ie]) (p := ![a, b, c, e])
    (q := ![x ia, x ib, x ic, x ie])
    hinj3 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol4 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, ic, id]) (p := ![a, b, c, d])
    (q := ![x ia, x ib, x ic, x id])
    hinj4 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull id hd) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  obtain ⟨z, hzac, hzbde⟩ := hinter
  obtain ⟨w, hw, hwsum, hwpoint⟩ := Finset.mem_convexHull'.mp hzac
  obtain ⟨v, hv, hvsum, hvpoint⟩ := Finset.mem_convexHull'.mp hzbde
  have hac : a ≠ c := by
    intro h
    subst c
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (0 : Fin 5) ≠ 2))) ha hc
  have hbd : b ≠ d := by
    intro h
    subst d
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (1 : Fin 5) ≠ 3))) hb hd
  have hbe : b ≠ e := by
    intro h
    subst e
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (1 : Fin 5) ≠ 4))) hb he
  have hde : d ≠ e := by
    intro h
    subst e
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (3 : Fin 5) ≠ 4))) hd he
  have hwsum' : w a + w c = 1 := by simpa [hac] using hwsum
  have hvsum' : v b + v d + v e = 1 := by simpa [hbd, hbe, hde, add_assoc] using hvsum
  have hwpoint' : w a • a + w c • c = z := by simpa [hac] using hwpoint
  have hvpoint' : v b • b + v d • d + v e • e = z := by
    simpa [hbd, hbe, hde, add_assoc] using hvpoint
  let u : Fin 5 → ℝ := ![w a, -v b, w c, -v d, -v e]
  have husum : ∑ i, u i = 0 := by
    simp [u, Fin.sum_univ_succ]
    linarith
  have hupoint : ∑ i, u i • fivePoints a b c d e i = 0 := by
    calc
      ∑ i, u i • fivePoints a b c d e i =
          (w a • a + w c • c) - (v b • b + v d • d + v e • e) := by
            simp [u, fivePoints, Fin.sum_univ_succ]
            module
      _ = z - z := by rw [hwpoint', hvpoint']
      _ = 0 := sub_self z
  have hu4 : u 4 ≠ 0 := by
    intro hu
    have hve0 : v e = 0 := by simpa [u] using hu
    have hzbd : z ∈ convexHull ℝ (({b, d} : Finset (Point 3)) : Set (Point 3)) := by
      rw [Finset.mem_convexHull']
      refine ⟨v, ?_, ?_, ?_⟩
      · intro y hy
        exact hv y (by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          exact hy.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
      · simpa [hbd, hbe, hde, hve0, add_assoc] using hvsum
      · simpa [hbd, hbe, hde, hve0, add_assoc] using hvpoint
    have hiaib : ia ≠ ib := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide)
    have hiaid : ia ≠ id := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide)
    have hicib : ic ≠ ib := by
      simpa using hindices.ne (show (2 : Fin 5) ≠ 1 by decide)
    have hicid : ic ≠ id := by
      simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide)
    have hiac : ia ≠ ic := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide)
    have hibd : ib ≠ id := by
      simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide)
    have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
      exact pair_disjoint_of_cross_ne hiaib hiaid hicib hicid
    have hsep := htwo hiac hibd hpairs
    apply Set.disjoint_left.mp hsep
    · apply convexHull_mono (s := (({a, c} : Finset (Point 3)) : Set (Point 3)))
        (t := (((X ia ∪ X ic : Finset (Point 3))) : Set (Point 3))) ?_ hzac
      intro y hy
      simp only [Finset.mem_coe, Finset.mem_union]
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr hc
    · apply convexHull_mono (s := (({b, d} : Finset (Point 3)) : Set (Point 3)))
        (t := (((X ib ∪ X id : Finset (Point 3))) : Set (Point 3))) ?_ hzbd
      intro y hy
      simp only [Finset.mem_coe, Finset.mem_union]
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inl hb
      · exact Or.inr hd
  have hai : AffineIndependent ℝ ![a, b, c, d] :=
    affineIndependent_four_clusterHull_points htwo hstrong
      hinj4 (by
        intro t; fin_cases t
        · exact hpHull ia ha
        · exact hpHull ib hb
        · exact hpHull ic hc
        · exact hpHull id hd)
  have hprop := fiveCofactors_proportional hai husum hupoint hu4
  let r := fiveCofactors a b c d e 4 / u 4
  have hr : r ≠ 0 := by
    have hV : fiveCofactors a b c d e 4 ≠ 0 := by
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hai
    exact div_ne_zero hV hu4
  have hupos : 0 < u 0 ∧ u 2 > 0 := by
    have hC0 : fiveCofactors a b c d e 0 ≠ 0 := by
      have hi := affineIndependent_four_clusterHull_points htwo hstrong
        (idx := ![ib, ic, id, ie]) (p := ![b, c, d, e])
        hinj0 (by
          intro t; fin_cases t
          · exact hpHull ib hb
          · exact hpHull ic hc
          · exact hpHull id hd
          · exact hpHull ie he)
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hi
    have hC2 : fiveCofactors a b c d e 2 ≠ 0 := by
      have hi := affineIndependent_four_clusterHull_points htwo hstrong
        (idx := ![ia, ib, id, ie]) (p := ![a, b, d, e])
        hinj2 (by
          intro t; fin_cases t
          · exact hpHull ia ha
          · exact hpHull ib hb
          · exact hpHull id hd
          · exact hpHull ie he)
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hi
    have hu0 : u 0 ≠ 0 := by
      intro h
      have := congr_fun hprop 0
      simp [r, h, hC0] at this
    have hu2 : u 2 ≠ 0 := by
      intro h
      have := congr_fun hprop 2
      simp [r, h, hC2] at this
    exact ⟨lt_of_le_of_ne (hw a (by simp)) (Ne.symm (by simpa [u] using hu0)),
      lt_of_le_of_ne (hw c (by simp)) (Ne.symm (by simpa [u] using hu2))⟩
  have huneg : u 1 < 0 ∧ u 3 < 0 ∧ u 4 < 0 := by
    have getneg (j : Fin 5) (hj : j = 1 ∨ j = 3 ∨ j = 4) : u j < 0 := by
      have hC : fiveCofactors a b c d e j ≠ 0 := by
        rcases hj with rfl | rfl | rfl
        · have hi := affineIndependent_four_clusterHull_points htwo hstrong
            (idx := ![ia, ic, id, ie]) (p := ![a, c, d, e])
            hinj1 (by
              intro t; fin_cases t
              · exact hpHull ia ha
              · exact hpHull ic hc
              · exact hpHull id hd
              · exact hpHull ie he)
          simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hi
        · have hi := affineIndependent_four_clusterHull_points htwo hstrong
            (idx := ![ia, ib, ic, ie]) (p := ![a, b, c, e])
            hinj3 (by
              intro t; fin_cases t
              · exact hpHull ia ha
              · exact hpHull ib hb
              · exact hpHull ic hc
              · exact hpHull ie he)
          simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hi
        · simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent_v7 hai
      have hu : u j ≠ 0 := by
        intro h
        have := congr_fun hprop j
        simp [r, h, hC] at this
      rcases hj with rfl | rfl | rfl
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv b (by simp))
          (Ne.symm (by simpa [u] using hu)))
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv d (by simp))
          (Ne.symm (by simpa [u] using hu)))
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv e (by simp))
          (Ne.symm (by simpa [u] using hu)))
    exact ⟨getneg 1 (Or.inl rfl), getneg 3 (Or.inr (Or.inl rfl)),
      getneg 4 (Or.inr (Or.inr rfl))⟩
  let q : Fin 5 → Point 3 := ![x ia, x ib, x ic, x id, x ie]
  let D := fiveCofactors (q 0) (q 1) (q 2) (q 3) (q 4)
  have hsame : ∀ j, 0 < fiveCofactors a b c d e j * D j := by
    intro j
    fin_cases j
    · simpa [D, q, fiveCofactors] using hvol0
    · simpa [D, q, fiveCofactors] using hvol1
    · simpa [D, q, fiveCofactors] using hvol2
    · simpa [D, q, fiveCofactors] using hvol3
    · simpa [D, q, fiveCofactors] using hvol4
  have hDsum : ∑ j, D j = 0 := by simpa [D, q] using fiveCofactors_sum (q 0) (q 1) (q 2) (q 3) (q 4)
  have hDpoint : ∑ j, D j • q j = 0 := by
    simpa [D, q, fivePoints] using fiveCofactors_point_sum (q 0) (q 1) (q 2) (q 3) (q 4)
  have hplane : ∑ j, D j * planeValue normal offset (q j) = 0 := by
    have hn := congrArg normal hDpoint
    change normal (∑ j, D j • q j) = normal 0 at hn
    simp only [map_sum, ContinuousLinearMap.map_smul_of_tower, map_zero] at hn
    simp only [planeValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hDsum,
      zero_mul, sub_zero]
    simpa [smul_eq_mul] using hn
  rcases hr.lt_or_gt with hrneg | hrpos
  · have hDsign : D 0 < 0 ∧ 0 < D 1 ∧ D 2 < 0 ∧ 0 < D 3 ∧ 0 < D 4 := by
      have hc (j : Fin 5) : fiveCofactors a b c d e j = r * u j := by
        simpa [r] using congr_fun hprop j
      constructor
      · have : fiveCofactors a b c d e 0 < 0 := by rw [hc]; exact mul_neg_of_neg_of_pos hrneg hupos.1
        exact neg_of_mul_pos_right (hsame 0) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 1 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.1
        exact pos_of_mul_pos_right (hsame 1) this.le
      constructor
      · have : fiveCofactors a b c d e 2 < 0 := by rw [hc]; exact mul_neg_of_neg_of_pos hrneg hupos.2
        exact neg_of_mul_pos_right (hsame 2) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 3 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.2.1
        exact pos_of_mul_pos_right (hsame 3) this.le
      · have : 0 < fiveCofactors a b c d e 4 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.2.2
        exact pos_of_mul_pos_right (hsame 4) this.le
    have := hplane
    simp [Fin.sum_univ_succ, q] at this
    linarith [mul_pos_of_neg_of_neg hDsign.1 hacneg.1,
      mul_pos hDsign.2.1 hbdeposit.1,
      mul_pos_of_neg_of_neg hDsign.2.2.1 hacneg.2,
      mul_pos hDsign.2.2.2.1 hbdeposit.2.1,
      mul_pos hDsign.2.2.2.2 hbdeposit.2.2]
  · have hDsign : 0 < D 0 ∧ D 1 < 0 ∧ 0 < D 2 ∧ D 3 < 0 ∧ D 4 < 0 := by
      have hc (j : Fin 5) : fiveCofactors a b c d e j = r * u j := by
        simpa [r] using congr_fun hprop j
      constructor
      · have : 0 < fiveCofactors a b c d e 0 := by rw [hc]; exact mul_pos hrpos hupos.1
        exact pos_of_mul_pos_right (hsame 0) this.le
      constructor
      · have : fiveCofactors a b c d e 1 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.1
        exact neg_of_mul_pos_right (hsame 1) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 2 := by rw [hc]; exact mul_pos hrpos hupos.2
        exact pos_of_mul_pos_right (hsame 2) this.le
      constructor
      · have : fiveCofactors a b c d e 3 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.2.1
        exact neg_of_mul_pos_right (hsame 3) this.le
      · have : fiveCofactors a b c d e 4 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.2.2
        exact neg_of_mul_pos_right (hsame 4) this.le
    have := hplane
    simp [Fin.sum_univ_succ, q] at this
    linarith [mul_neg_of_pos_of_neg hDsign.1 hacneg.1,
      mul_neg_of_neg_of_pos hDsign.2.1 hbdeposit.1,
      mul_neg_of_pos_of_neg hDsign.2.2.1 hacneg.2,
      mul_neg_of_neg_of_pos hDsign.2.2.2.1 hbdeposit.2.1,
      mul_neg_of_neg_of_pos hDsign.2.2.2.2 hbdeposit.2.2]

private theorem hulls_disjoint_of_one_cluster {k : ℕ}
    {X : Fin k → Finset (Point 3)} (hstrong : StrongConvexPositionClusters X)
    {i : Fin k} {J : Finset (Fin k)} (hiJ : i ∉ J)
    {A B : Finset (Point 3)} (hA : A ⊆ X i)
    (hB : B ⊆ clusterUnion X J) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  apply (hstrong i).mono
  · exact convexHull_mono hA
  · apply convexHull_mono
    exact hB.trans (clusterUnion_index_mono X (by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ]
      exact ⟨fun hji ↦ hiJ (hji ▸ hj), trivial⟩))

private theorem hulls_disjoint_of_two_pairs {k : ℕ}
    {X : Fin k → Finset (Point 3)} (htwo : TwoSeparatedClusters X)
    {i j i' j' : Fin k} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hpairs : Disjoint ({i, j} : Finset (Fin k)) {i', j'})
    {A B : Finset (Point 3)} (hA : A ⊆ X i ∪ X j)
    (hB : B ⊆ X i' ∪ X j') :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) :=
  (htwo hij hi'j' hpairs).mono (convexHull_mono hA) (convexHull_mono hB)

private theorem pair_disjoint_of_mem {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : Disjoint S T)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T) :
    Disjoint ({a, b} : Finset α) {c, d} := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have hxS' : x ∈ S := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact ha
    · exact hb
  have hxT' : x ∈ T := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with rfl | rfl
    · exact hc
    · exact hd
  exact Finset.disjoint_left.mp hST hxS' hxT'

private theorem vector5_injective_of_pairwise {α : Type*}
    (a b c d e : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Kirchberger plus the `1+4` and `2+2` exclusions leaves exactly a
five-cluster `2+3` Radon witness. -/
private theorem fiveCluster_witness_of_hulls_intersect {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {N P : Finset (Fin k)} (hNP : Disjoint N P)
    (hinter : (convexHull ℝ ((clusterUnion X N : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ ((clusterUnion X P : Finset (Point 3)) : Set (Point 3))).Nonempty) :
    (∃ ia ib ic id ie a b c d e,
      Function.Injective ![ia, ib, ic, id, ie] ∧
      ia ∈ N ∧ ic ∈ N ∧ ib ∈ P ∧ id ∈ P ∧ ie ∈ P ∧
      a ∈ X ia ∧ b ∈ X ib ∧ c ∈ X ic ∧ d ∈ X id ∧ e ∈ X ie ∧
      (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
        convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) ∨
    (∃ ia ib ic id ie a b c d e,
      Function.Injective ![ia, ib, ic, id, ie] ∧
      ia ∈ P ∧ ic ∈ P ∧ ib ∈ N ∧ id ∈ N ∧ ie ∈ N ∧
      a ∈ X ia ∧ b ∈ X ib ∧ c ∈ X ic ∧ d ∈ X id ∧ e ∈ X ie ∧
      (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
        convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) := by
  classical
  obtain ⟨A, B, hAN, hBP, hcard, z, hzA, hzB⟩ :=
    finite_kirchberger_point3 (clusterUnion X N) (clusterUnion X P) hinter
  have hAne : A.Nonempty := by
    by_contra h
    have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst A
    simp at hzA
  have hBne : B.Nonempty := by
    by_contra h
    have : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst B
    simp at hzB
  have indexN {y : Point 3} (hy : y ∈ A) : ∃ i ∈ N, y ∈ X i := by
    exact Finset.mem_biUnion.mp (hAN hy)
  have indexP {y : Point 3} (hy : y ∈ B) : ∃ i ∈ P, y ∈ X i := by
    exact Finset.mem_biUnion.mp (hBP hy)
  by_cases hAone : A.card = 1
  · obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAone
    rw [hA] at hAN hzA indexN
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    have hBP' : B ⊆ clusterUnion X P := hBP
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
        (A := {a}) (B := B)
        (fun h ↦ Finset.disjoint_left.mp hNP hiaN h) (by simpa using ha) hBP')
      (by simpa using hzA) hzB)
  by_cases hBone : B.card = 1
  · obtain ⟨b, hB⟩ := Finset.card_eq_one.mp hBone
    rw [hB] at hBP hzB indexP
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
        (A := {b}) (B := A)
        (fun h ↦ Finset.disjoint_left.mp hNP h hibP) (by simpa using hb) hAN).symm
      hzA (by simpa using hzB))
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  have hA2 : 2 ≤ A.card := by omega
  have hB2 : 2 ≤ B.card := by omega
  have hsizes : (A.card = 2 ∧ B.card = 2) ∨
      (A.card = 2 ∧ B.card = 3) ∨ (A.card = 3 ∧ B.card = 2) := by omega
  rcases hsizes with h22 | h23 | h32
  · obtain ⟨a, c, hac, hA⟩ := Finset.card_eq_two.mp h22.1
    obtain ⟨b, d, hbd, hB⟩ := Finset.card_eq_two.mp h22.2
    subst A; subst B
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    obtain ⟨ic, hicN, hc⟩ := indexN (y := c) (by simp)
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    obtain ⟨id, hidP, hd⟩ := indexP (y := d) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
          (fun h ↦ Finset.disjoint_left.mp hNP hiaN h)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hBP) hzA hzB)
    by_cases hibd : ib = id
    · subst id
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
          (fun h ↦ Finset.disjoint_left.mp hNP h hibP)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hAN).symm hzA hzB)
    have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
      exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_union_left _ ha
          · exact Finset.mem_union_right _ hc)
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_union_left _ hb
          · exact Finset.mem_union_right _ hd)) hzA hzB)
  · obtain ⟨a, c, hac, hA⟩ := Finset.card_eq_two.mp h23.1
    obtain ⟨b, d, e, hbd, hbe, hde, hB⟩ := Finset.card_eq_three.mp h23.2
    subst A; subst B
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    obtain ⟨ic, hicN, hc⟩ := indexN (y := c) (by simp)
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    obtain ⟨id, hidP, hd⟩ := indexP (y := d) (by simp)
    obtain ⟨ie, hieP, he⟩ := indexP (y := e) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
          (fun h ↦ Finset.disjoint_left.mp hNP hiaN h)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hBP) hzA hzB)
    have cross {i j : Fin k} (hi : i ∈ N) (hj : j ∈ P) : i ≠ j := by
      intro h
      exact Finset.disjoint_left.mp hNP hi (h ▸ hj)
    by_cases hibd : ib = id
    · subst id
      by_cases hibie : ib = ie
      · subst ie
        exact False.elim (Set.disjoint_left.mp
          (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
            (fun h ↦ Finset.disjoint_left.mp hNP h hibP)
            (by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl <;> assumption) hAN).symm hzA hzB)
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, ie} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hieP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibie hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_left _ hd
            · exact Finset.mem_union_right _ he)) hzA hzB)
    by_cases hibe : ib = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_left _ he)) hzA hzB)
    by_cases hide : id = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_right _ he)) hzA hzB)
    left
    refine ⟨ia, ib, ic, id, ie, a, b, c, d, e, ?_, hiaN, hicN, hibP, hidP, hieP,
      ha, hb, hc, hd, he, ?_⟩
    · exact vector5_injective_of_pairwise ia ib ic id ie
        (cross hiaN hibP) hiac (cross hiaN hidP) (cross hiaN hieP)
        (cross hicN hibP).symm hibd hibe (cross hicN hidP)
        (cross hicN hieP) hide
    · exact ⟨z, hzA, hzB⟩
  · obtain ⟨b, d, e, hbd, hbe, hde, hA⟩ := Finset.card_eq_three.mp h32.1
    obtain ⟨a, c, hac, hB⟩ := Finset.card_eq_two.mp h32.2
    subst A; subst B
    obtain ⟨ib, hibN, hb⟩ := indexN (y := b) (by simp)
    obtain ⟨id, hidN, hd⟩ := indexN (y := d) (by simp)
    obtain ⟨ie, hieN, he⟩ := indexN (y := e) (by simp)
    obtain ⟨ia, hiaP, ha⟩ := indexP (y := a) (by simp)
    obtain ⟨ic, hicP, hc⟩ := indexP (y := c) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := N)
          (fun h ↦ Finset.disjoint_left.mp hNP h hiaP)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hAN).symm hzA hzB)
    have cross {i j : Fin k} (hi : i ∈ P) (hj : j ∈ N) : i ≠ j := by
      intro h
      exact Finset.disjoint_left.mp hNP hj (h ▸ hi)
    by_cases hibd : ib = id
    · subst id
      by_cases hibie : ib = ie
      · subst ie
        exact False.elim (Set.disjoint_left.mp
          (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := P)
            (fun h ↦ Finset.disjoint_left.mp hNP hibN h)
            (by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl <;> assumption) hBP) hzA hzB)
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, ie} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hieN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibie hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_left _ hd
            · exact Finset.mem_union_right _ he)) hzB hzA)
    by_cases hibe : ib = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hidN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac (by exact fun h ↦ hibd h) hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_left _ he)) hzB hzA)
    by_cases hide : id = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hidN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_right _ he)) hzB hzA)
    right
    refine ⟨ia, ib, ic, id, ie, a, b, c, d, e, ?_, hiaP, hicP, hibN, hidN, hieN,
      ha, hb, hc, hd, he, ?_⟩
    · exact vector5_injective_of_pairwise ia ib ic id ie
        (cross hiaP hibN) hiac (cross hiaP hidN) (cross hiaP hieN)
        (cross hicP hibN).symm hibd hibe (cross hicP hidN)
        (cross hicP hieN) hide
    · exact ⟨z, hzB, hzA⟩

/-- The exact geometric core of Pohoata--Zakharov Proposition 2.7. -/
theorem representativePatternHullsSeparated_of_twoSeparated_of_strong {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hpattern : HasRepresentativePlanePattern x normal offset) :
    RepresentativePatternHullsSeparated X x normal offset := by
  classical
  let N := negativeClusterIndices x normal offset
  let P := positiveClusterIndices x normal offset
  have hNP : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro i hiN hiP
    have hn : planeValue normal offset (x i) < 0 := by
      simpa [N, negativeClusterIndices] using hiN
    have hp : 0 < planeValue normal offset (x i) := by
      simpa [P, positiveClusterIndices] using hiP
    linarith
  rw [RepresentativePatternHullsSeparated, Set.disjoint_left]
  intro z hzN hzP
  have hinter : (convexHull ℝ
        ((clusterUnion X N : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ
        ((clusterUnion X P : Finset (Point 3)) : Set (Point 3))).Nonempty :=
    ⟨z, hzN, hzP⟩
  obtain hfive | hfive := fiveCluster_witness_of_hulls_intersect htwo hstrong hNP hinter
  · obtain ⟨ia, ib, ic, id, ie, a, b, c, d, e, hindices,
      hiaN, hicN, hibP, hidP, hieP, ha, hb, hc, hd, he, hwit⟩ := hfive
    apply fiveCluster_segment_triangle_pattern_impossible htwo hstrong hindices
      ha hb hc hd he hx
    · constructor <;> simpa [N, negativeClusterIndices] using ‹_ ∈ N›
    · constructor
      · simpa [P, positiveClusterIndices] using hibP
      constructor <;> simpa [P, positiveClusterIndices] using ‹_ ∈ P›
    · exact hwit
  · obtain ⟨ia, ib, ic, id, ie, a, b, c, d, e, hindices,
      hiaP, hicP, hibN, hidN, hieN, ha, hb, hc, hd, he, hwit⟩ := hfive
    apply fiveCluster_segment_triangle_pattern_impossible htwo hstrong hindices
      ha hb hc hd he hx (normal := -normal) (offset := -offset)
    · constructor
      · have hp : 0 < planeValue normal offset (x ia) := by
          simpa [P, positiveClusterIndices] using hiaP
        simpa [planeValue] using neg_neg_of_pos hp
      · have hp : 0 < planeValue normal offset (x ic) := by
          simpa [P, positiveClusterIndices] using hicP
        simpa [planeValue] using neg_neg_of_pos hp
    · constructor
      · have hn : planeValue normal offset (x ib) < 0 := by
          simpa [N, negativeClusterIndices] using hibN
        simpa [planeValue] using neg_pos.mpr hn
      constructor
      · have hn : planeValue normal offset (x id) < 0 := by
          simpa [N, negativeClusterIndices] using hidN
        simpa [planeValue] using neg_pos.mpr hn
      · have hn : planeValue normal offset (x ie) < 0 := by
          simpa [N, negativeClusterIndices] using hieN
        simpa [planeValue] using neg_pos.mpr hn
    · exact hwit

private theorem abs_le_sum_abs_of_mem {S : Finset (Point 3)}
    (normal : Point 3 →L[ℝ] ℝ) {y : Point 3} (hy : y ∈ S) :
    |normal y| ≤ ∑ z ∈ S, |normal z| := by
  exact Finset.single_le_sum (fun z _ => abs_nonneg (normal z)) hy

/-- Once the two union hulls are known to be disjoint, finite-dimensional
strict separation produces a plane realizing the representative pattern on
every point of every cluster.  The two one-sided cases are handled by
translating the original nonzero normal beyond the finite point family. -/
theorem liftsRepresentativePlanePattern_of_hullsSeparated {k : ℕ}
    {X : Fin k → Finset (Point 3)} {x : Fin k → Point 3}
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hx : IsClusterTransversal X x)
    (hpattern : HasRepresentativePlanePattern x normal offset)
    (hsep : RepresentativePatternHullsSeparated X x normal offset) :
    LiftsRepresentativePlanePattern X x normal offset := by
  classical
  let P := positiveClusterIndices x normal offset
  let N := negativeClusterIndices x normal offset
  let U := allClusters X
  let M : ℝ := (∑ z ∈ U, |normal z|) + 1
  by_cases hP : P.Nonempty
  · by_cases hN : N.Nonempty
    · obtain ⟨f, u, hNlt, hPlt⟩ :=
        finite_convexHulls_strictly_separated_point3
          (clusterUnion X N) (clusterUnion X P)
          (by simpa [RepresentativePatternHullsSeparated, P, N] using hsep)
      have hf : f ≠ 0 := by
        intro hf
        obtain ⟨i, hiN⟩ := hN
        obtain ⟨j, hjP⟩ := hP
        have hxiN : x i ∈ clusterUnion X N := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiN, hx i⟩
        have hxjP : x j ∈ clusterUnion X P := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨j, hjP, hx j⟩
        have hi := hNlt (x i)
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hxiN))
        have hj := hPlt (x j)
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hxjP))
        simp only [hf, zero_apply] at hi hj
        linarith
      refine ⟨f, u, hf, ?_⟩
      intro i y hy
      constructor
      · intro hi
        have hiP : i ∈ P := by
          simpa [P, positiveClusterIndices] using hi
        have hyP : y ∈ clusterUnion X P := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiP, hy⟩
        have := hPlt y
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hyP))
        dsimp [planeValue]
        linarith
      · intro hi
        have hiN : i ∈ N := by
          simpa [N, negativeClusterIndices] using hi
        have hyN : y ∈ clusterUnion X N := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiN, hy⟩
        have := hNlt y
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hyN))
        dsimp [planeValue]
        linarith
    · refine ⟨normal, -M, hpattern.1, ?_⟩
      intro i y hy
      have hyU : y ∈ U := by
        rw [mem_allClusters_iff]
        exact ⟨i, hy⟩
      have habs : |normal y| ≤ ∑ z ∈ U, |normal z| :=
        abs_le_sum_abs_of_mem normal hyU
      have hallpos : 0 < planeValue normal (-M) y := by
        have hnegabs : -|normal y| ≤ normal y := neg_abs_le (normal y)
        dsimp [planeValue, M]
        linarith
      constructor
      · exact fun _ => hallpos
      · intro hi
        have hiN : i ∈ N := by
          simpa [N, negativeClusterIndices] using hi
        exact False.elim (hN ⟨i, hiN⟩)
  · refine ⟨normal, M, hpattern.1, ?_⟩
    intro i y hy
    have hyU : y ∈ U := by
      rw [mem_allClusters_iff]
      exact ⟨i, hy⟩
    have habs : |normal y| ≤ ∑ z ∈ U, |normal z| :=
      abs_le_sum_abs_of_mem normal hyU
    have hallneg : planeValue normal M y < 0 := by
      have hleabs : normal y ≤ |normal y| := le_abs_self (normal y)
      dsimp [planeValue, M]
      linarith
    constructor
    · intro hi
      have hiP : i ∈ P := by
        simpa [P, positiveClusterIndices] using hi
      exact False.elim (hP ⟨i, hiP⟩)
    · exact fun _ => hallneg

/-- Pohoata--Zakharov Proposition 2.7: every strict representative-plane
pattern lifts to a strict plane on the full clusters. -/
theorem liftsRepresentativePlanePattern_of_twoSeparated_of_strong {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hpattern : HasRepresentativePlanePattern x normal offset) :
    LiftsRepresentativePlanePattern X x normal offset :=
  liftsRepresentativePlanePattern_of_hullsSeparated hx hpattern
    (representativePatternHullsSeparated_of_twoSeparated_of_strong
      htwo hstrong hx hpattern)

end

end

/-! ### Upstream module `JSP527/External/Erdos651/TrihedralGadget.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The trihedral gadget of Pohoata--Zakharov

This file formalizes the three-region construction in Proposition 3.1 of
Pohoata--Zakharov.  For `j₁ < j₂ < j₃`, the clusters other than the
middle cluster `X j₂` are divided into the two alternating regions

* `i < j₁` or `j₂ < i ≤ j₃`, and
* `j₁ ≤ i < j₂` or `j₃ < i`.

The robust planar support construction separates the middle cluster from all
the others.  The two lifted alternating-block separations split the first
region from the second region together with the middle, and the second region
from the first together with the middle.  We turn these three strict
separations into two honest nondegenerate `OrientedTrihedral`s.

There are two small but important technical points.

1. Three separating normals need not initially be linearly independent.  The
   strict sign conditions form an open set.  The complement of every proper
   subspace of the three-dimensional dual is dense, so the normals can be
   perturbed, successively, to an independent triple without changing any
   sign on the finite cluster union.
2. Using the same closed threshold for both polyhedra would leave a common
   boundary ray.  We therefore choose a second threshold strictly inside the
   positive side of each finite separation.  The resulting closed
   polyhedra have a genuine gap, which supplies exactly the three convex-
   position separations used in the subsequent poset argument.
-/

open scoped InnerProductSpace

noncomputable section

abbrev PlaneNormal := Point 3 →L[ℝ] ℝ

/-! ## Alternating index regions -/

/-- The first region in (4.8): the initial block and the block immediately
after the middle index. -/
def firstTrihedralIndices {k : ℕ} (j₁ j₂ j₃ : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => i < j₁ ∨ (j₂ < i ∧ i ≤ j₃)

/-- The second region in (4.8): the block before the middle index and the
final block. -/
def secondTrihedralIndices {k : ℕ} (j₁ j₂ j₃ : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun i => (j₁ ≤ i ∧ i < j₂) ∨ j₃ < i

@[simp] theorem mem_firstTrihedralIndices {k : ℕ} {j₁ j₂ j₃ i : Fin k} :
    i ∈ firstTrihedralIndices j₁ j₂ j₃ ↔
      i < j₁ ∨ (j₂ < i ∧ i ≤ j₃) := by
  simp [firstTrihedralIndices]

@[simp] theorem mem_secondTrihedralIndices {k : ℕ} {j₁ j₂ j₃ i : Fin k} :
    i ∈ secondTrihedralIndices j₁ j₂ j₃ ↔
      (j₁ ≤ i ∧ i < j₂) ∨ j₃ < i := by
  simp [secondTrihedralIndices]

theorem trihedralIndices_union_middle {k : ℕ}
    {j₁ j₂ j₃ : Fin k} (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    firstTrihedralIndices j₁ j₂ j₃ ∪
        (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}) = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_union, mem_firstTrihedralIndices,
    mem_secondTrihedralIndices, Finset.mem_singleton, Finset.mem_univ, iff_true]
  rcases lt_trichotomy i j₁ with hi | rfl | hi
  · exact Or.inl (Or.inl hi)
  · exact Or.inr (Or.inl (Or.inl ⟨le_rfl, h₁₂⟩))
  · rcases lt_trichotomy i j₂ with hi₂ | rfl | hi₂
    · exact Or.inr (Or.inl (Or.inl ⟨hi.le, hi₂⟩))
    · exact Or.inr (Or.inr rfl)
    · by_cases hi₃ : i ≤ j₃
      · exact Or.inl (Or.inr ⟨hi₂, hi₃⟩)
      · exact Or.inr (Or.inl (Or.inr (lt_of_not_ge hi₃)))

/-! ## Strict finite plane patterns -/

/-- A normal and two separated levels realizing a strict finite bipartition.
The negative finite set lies strictly below `low`; the positive finite set
lies strictly above `high`. -/
structure StrictPlaneSplit (A B : Finset (Point 3)) where
  normal : PlaneNormal
  low : ℝ
  high : ℝ
  low_lt_high : low < high
  left_lt_low : ∀ x ∈ A, normal x < low
  high_lt_right : ∀ x ∈ B, high < normal x

/-- The un-gapped strict sign pattern about one level. -/
def RealizesPlanePattern (A B : Finset (Point 3))
    (normal : PlaneNormal) (offset : ℝ) : Prop :=
  (∀ x ∈ A, normal x < offset) ∧
    ∀ x ∈ B, offset < normal x

abbrev PlaneConstraint := PlaneNormal →ₗ[ℝ] ℝ

/-- A generic scalar coordinate separates a prescribed pair of points. -/
def pointDifferenceConstraint (x y : Point 3) : PlaneConstraint where
  toFun normal := normal x - normal y
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- With the first planar coordinate fixed to `first`, this is the oriented
area of the images of `x,y,z` as a linear functional of the second
coordinate. -/
def planarOrientationConstraint (first : PlaneNormal)
    (x y z : Point 3) : PlaneConstraint where
  toFun second :=
    (first y - first x) * (second z - second x) -
      (first z - first x) * (second y - second x)
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- Every triple of distinct points of `U` is affinely independent.  This is
the exact finite generic-position consequence needed for the three edge
projections. -/
def NoThreeCollinear (U : Finset (Point 3)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
    x ≠ y → y ≠ z → x ≠ z →
      LinearIndependent ℝ ![y - x, z - x]

/-- The finite constraints saying that one scalar coordinate is injective on
`U`. -/
def pointDifferenceConstraints (U : Finset (Point 3)) : Finset PlaneConstraint :=
  by
    classical
    exact ((U.product U).filter fun p => p.1 ≠ p.2).image
      fun p => pointDifferenceConstraint p.1 p.2

/-- Once `first` is injective, these finite constraints say that the planar
map `(first, second)` sends no distinct triple of `U` to a collinear triple. -/
def planarOrientationConstraints (U : Finset (Point 3))
    (first : PlaneNormal) : Finset PlaneConstraint :=
  by
    classical
    exact ((U.product (U.product U)).filter fun p =>
        p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2).image
      fun p => planarOrientationConstraint first p.1 p.2.1 p.2.2

private theorem isOpen_realizesPlanePattern (A B : Finset (Point 3)) (offset : ℝ) :
    IsOpen {normal : PlaneNormal | RealizesPlanePattern A B normal offset} := by
  classical
  have hcontinuous (x : Point 3) :
      Continuous (fun normal : PlaneNormal => normal x) := by
    fun_prop
  have hleft : IsOpen {normal : PlaneNormal | ∀ x ∈ A, normal x < offset} := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert x A hx ih =>
        simpa only [Finset.mem_insert, forall_eq_or_imp, Set.setOf_and] using
          (isOpen_lt (hcontinuous x) continuous_const).inter ih
  have hright : IsOpen {normal : PlaneNormal | ∀ x ∈ B, offset < normal x} := by
    induction B using Finset.induction_on with
    | empty => simp
    | @insert x B hx ih =>
        simpa only [Finset.mem_insert, forall_eq_or_imp, Set.setOf_and] using
          (isOpen_lt continuous_const (hcontinuous x)).inter ih
  simpa only [RealizesPlanePattern, Set.setOf_and] using hleft.inter hright

private theorem finrank_planeNormal : Module.finrank ℝ PlaneNormal = 3 := by
  rw [← (LinearMap.toContinuousLinearMap
    (E := Point 3) (F' := ℝ)).finrank_eq]
  rw [Module.finrank_linearMap_self, finrank_euclideanSpace_fin]

private theorem span_planeNormals_ne_top {m : ℕ} (hm : m < 3)
    (v : Fin m → PlaneNormal) :
    Submodule.span ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ Fintype.card (Fin m) :=
    finrank_range_le_card (R := ℝ) v
  rw [htop, finrank_top, finrank_planeNormal] at hdim
  exact (not_le_of_gt hm) (by simpa using hdim)

private theorem dense_compl_ker_planeConstraint {L : PlaneConstraint} (hL : L ≠ 0) :
    Dense (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ) := by
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra hne
  have htop := (LinearMap.ker L).eq_top_of_nonempty_interior'
    (Set.nonempty_iff_ne_empty.mpr hne)
  exact hL (LinearMap.ker_eq_top.mp htop)

private theorem isOpen_compl_ker_planeConstraint (L : PlaneConstraint) :
    IsOpen (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ) := by
  exact (Submodule.closed_of_finiteDimensional (LinearMap.ker L)).isOpen_compl

/-- A nonempty open family of normals contains a point avoiding any finite
family of nonzero linear equations. -/
private theorem exists_mem_open_avoiding_constraints
    {O : Set PlaneNormal} (hO : IsOpen O) (hOne : O.Nonempty)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0) :
    ∃ normal ∈ O, ∀ L ∈ C, L normal ≠ 0 := by
  classical
  induction C using Finset.induction_on generalizing O with
  | empty =>
      obtain ⟨normal, hn⟩ := hOne
      exact ⟨normal, hn, by simp⟩
  | @insert L C hLC ih =>
      have hL : L ≠ 0 := hC L (by simp)
      let O' : Set PlaneNormal :=
        O ∩ (((LinearMap.ker L : Submodule ℝ PlaneNormal) : Set PlaneNormal)ᶜ)
      have hO' : IsOpen O' :=
        hO.inter (isOpen_compl_ker_planeConstraint L)
      have hOne' : O'.Nonempty := by
        obtain ⟨normal, hnker, hnO⟩ :=
          (dense_compl_ker_planeConstraint hL).exists_mem_open hO hOne
        exact ⟨normal, hnO, hnker⟩
      obtain ⟨normal, hnO', hnC⟩ :=
        ih hO' hOne' (fun K hKC => hC K (by simp [hKC]))
      refine ⟨normal, hnO'.1, ?_⟩
      intro K hK
      rw [Finset.mem_insert] at hK
      rcases hK with rfl | hK
      · simpa only [Set.mem_compl_iff, SetLike.mem_coe, LinearMap.mem_ker] using hnO'.2
      · exact hnC K hK

/-- Strict finite sign patterns can avoid any proper linear subspace of the
dual.  This is the sign-preserving perturbation used to make the three
separators independent. -/
private theorem exists_pattern_normal_not_mem
    (A B : Finset (Point 3)) (offset : ℝ)
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (normal : PlaneNormal) (hpattern : RealizesPlanePattern A B normal offset) :
    ∃ normal' : PlaneNormal,
      normal' ∉ W ∧ RealizesPlanePattern A B normal' offset := by
  have hinterior : interior (W : Set PlaneNormal) = ∅ := by
    by_contra hne
    exact hW (W.eq_top_of_nonempty_interior'
      (Set.nonempty_iff_ne_empty.mpr hne))
  have hdense : Dense ((W : Set PlaneNormal)ᶜ) :=
    interior_eq_empty_iff_dense_compl.mp hinterior
  obtain ⟨normal', hnW, hnpat⟩ :=
    hdense.exists_mem_open (isOpen_realizesPlanePattern A B offset)
      ⟨normal, hpattern⟩
  exact ⟨normal', hnW, hnpat⟩

/-- Simultaneously avoid a proper subspace and finitely many nonzero
polynomial-linear genericity equations while preserving all finite signs. -/
private theorem exists_pattern_normal_not_mem_avoiding
    (A B : Finset (Point 3)) (offset : ℝ)
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0)
    (normal : PlaneNormal) (hpattern : RealizesPlanePattern A B normal offset) :
    ∃ normal' : PlaneNormal,
      normal' ∉ W ∧ RealizesPlanePattern A B normal' offset ∧
        ∀ L ∈ C, L normal' ≠ 0 := by
  obtain ⟨witness, hwW, hwpattern⟩ :=
    exists_pattern_normal_not_mem A B offset W hW normal hpattern
  let O : Set PlaneNormal :=
    {normal | RealizesPlanePattern A B normal offset} ∩ (W : Set PlaneNormal)ᶜ
  have hO : IsOpen O :=
    (isOpen_realizesPlanePattern A B offset).inter
      (Submodule.closed_of_finiteDimensional W).isOpen_compl
  have hOne : O.Nonempty := ⟨witness, hwpattern, hwW⟩
  obtain ⟨normal', hnO, hnC⟩ :=
    exists_mem_open_avoiding_constraints hO hOne C hC
  exact ⟨normal', hnO.2, hnO.1, hnC⟩

private theorem exists_high_level {B : Finset (Point 3)} (hB : B.Nonempty)
    (normal : PlaneNormal) (offset : ℝ)
    (hpositive : ∀ x ∈ B, offset < normal x) :
    ∃ high : ℝ, offset < high ∧ ∀ x ∈ B, high < normal x := by
  classical
  have himage : (B.image normal).Nonempty := hB.image normal
  let m : ℝ := (B.image normal).min' himage
  have hoffset_m : offset < m := by
    obtain ⟨x, hxB, hxm⟩ := Finset.mem_image.mp
      (Finset.min'_mem (B.image normal) himage)
    show offset < (B.image normal).min' himage
    rw [← hxm]
    exact hpositive x hxB
  refine ⟨(offset + m) / 2, by linarith, ?_⟩
  intro x hxB
  have hm_le : m ≤ normal x :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem normal hxB)
  linarith

theorem pointDifferenceConstraint_ne_zero {x y : Point 3} (hxy : x ≠ y) :
    pointDifferenceConstraint x y ≠ 0 := by
  intro hzero
  have h := congrArg (fun L : PlaneConstraint => L (innerSL ℝ (x - y))) hzero
  simp only [pointDifferenceConstraint, LinearMap.zero_apply,
    innerSL_apply_apply] at h
  have hinner : ⟪x - y, x - y⟫_ℝ = 0 := by
    calc
      ⟪x - y, x - y⟫_ℝ =
          ⟪x - y, x⟫_ℝ - ⟪x - y, y⟫_ℝ := by rw [inner_sub_right]
      _ = 0 := h
  exact (inner_self_ne_zero.mpr (sub_ne_zero.mpr hxy)) hinner

theorem pointDifferenceConstraints_nonzero (U : Finset (Point 3)) :
    ∀ L ∈ pointDifferenceConstraints U, L ≠ 0 := by
  classical
  intro L hL
  simp only [pointDifferenceConstraints, Finset.mem_image] at hL
  obtain ⟨p, hp, rfl⟩ := hL
  exact pointDifferenceConstraint_ne_zero (Finset.mem_filter.mp hp).2

theorem realizes_pointDifferenceConstraints_iff
    {U : Finset (Point 3)} {normal : PlaneNormal} :
    (∀ L ∈ pointDifferenceConstraints U, L normal ≠ 0) ↔
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → normal x ≠ normal y := by
  classical
  constructor
  · intro h x hx y hy hxy hEq
    have hmem : pointDifferenceConstraint x y ∈ pointDifferenceConstraints U := by
      simp only [pointDifferenceConstraints, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product]
      exact ⟨(x, y), ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩
    exact h _ hmem (by simp [pointDifferenceConstraint, hEq])
  · intro h L hL
    simp only [pointDifferenceConstraints, Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hp' := Finset.mem_filter.mp hp
    have hpU := Finset.mem_product.mp hp'.1
    exact sub_ne_zero_of_ne (h p.1 hpU.1 p.2 hpU.2 hp'.2)

private theorem planarOrientationConstraint_ne_zero
    {U : Finset (Point 3)} (htriple : NoThreeCollinear U)
    {first : PlaneNormal}
    (hfirst : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → first x ≠ first y)
    {x y z : Point 3} (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    planarOrientationConstraint first x y z ≠ 0 := by
  intro hzero
  let a : ℝ := first y - first x
  let b : ℝ := first z - first x
  let v : Point 3 := y - x
  let w : Point 3 := z - x
  let q : Point 3 := a • w - b • v
  have ha : a ≠ 0 := sub_ne_zero.mpr (hfirst y hy x hx hxy.symm)
  have hb : b ≠ 0 := sub_ne_zero.mpr (hfirst z hz x hx hxz.symm)
  have hqinner := LinearMap.congr_fun hzero (innerSL ℝ q)
  have hqzero : q = 0 := by
    apply ((inner_self_eq_zero (𝕜 := ℝ)).mp ?_)
    calc
      ⟪q, q⟫_ℝ =
          a * (innerSL ℝ q z - innerSL ℝ q x) -
            b * (innerSL ℝ q y - innerSL ℝ q x) := by
        simp only [q, v, w, innerSL_apply_apply, inner_sub_right,
          inner_sub_left, real_inner_smul_right]
        ring
      _ = 0 := by
        simpa only [planarOrientationConstraint, a, b, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.zero_apply] using hqinner
  have hrel : a • w = b • v := sub_eq_zero.mp hqzero
  have hvw : (a / b) • w = v := by
    calc
      (a / b) • w = b⁻¹ • (a • w) := by
        simp only [div_eq_mul_inv, smul_smul]
        congr 1
        ring
      _ = b⁻¹ • (b • v) := congrArg (fun t : Point 3 => b⁻¹ • t) hrel
      _ = v := by simp [smul_smul, hb]
  have hlin := htriple x hx y hy z hz hxy hyz hxz
  exact (linearIndependent_fin2.mp hlin).2 (a / b) hvw

theorem planarOrientationConstraints_nonzero
    {U : Finset (Point 3)} (htriple : NoThreeCollinear U)
    {first : PlaneNormal}
    (hfirst : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → first x ≠ first y) :
    ∀ L ∈ planarOrientationConstraints U first, L ≠ 0 := by
  classical
  intro L hL
  simp only [planarOrientationConstraints, Finset.mem_image] at hL
  obtain ⟨p, hp, rfl⟩ := hL
  have hp' := Finset.mem_filter.mp hp
  have hpU := Finset.mem_product.mp hp'.1
  exact planarOrientationConstraint_ne_zero htriple hfirst
    hpU.1 (Finset.mem_product.mp hpU.2).1 (Finset.mem_product.mp hpU.2).2
    hp'.2.1 hp'.2.2.1 hp'.2.2.2

theorem realizes_planarOrientationConstraints_iff
    {U : Finset (Point 3)} {first second : PlaneNormal} :
    (∀ L ∈ planarOrientationConstraints U first, L second ≠ 0) ↔
      ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
        x ≠ y → y ≠ z → x ≠ z →
          (first y - first x) * (second z - second x) -
            (first z - first x) * (second y - second x) ≠ 0 := by
  classical
  constructor
  · intro h x hx y hy z hz hxy hyz hxz
    apply h (planarOrientationConstraint first x y z)
    simp only [planarOrientationConstraints, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product]
    exact ⟨(x, y, z), ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_product.mpr ⟨hy, hz⟩⟩,
      hxy, hyz, hxz⟩, rfl⟩
  · intro h L hL
    simp only [planarOrientationConstraints, Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hp' := Finset.mem_filter.mp hp
    have hpU := Finset.mem_product.mp hp'.1
    exact h p.1 hpU.1 p.2.1 (Finset.mem_product.mp hpU.2).1
      p.2.2 (Finset.mem_product.mp hpU.2).2
      hp'.2.1 hp'.2.2.1 hp'.2.2.2

private theorem exists_strictPlaneSplit_avoiding_generic
    (A B : Finset (Point 3)) (hB : B.Nonempty)
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))))
    (W : Submodule ℝ PlaneNormal) (hW : W ≠ ⊤)
    (C : Finset PlaneConstraint) (hC : ∀ L ∈ C, L ≠ 0) :
    ∃ split : StrictPlaneSplit A B,
      split.normal ∉ W ∧ ∀ L ∈ C, L split.normal ≠ 0 := by
  obtain ⟨normal, offset, hleft, hright⟩ :=
    finite_sets_strictly_separated_point3 A B hdisj
  obtain ⟨normal', hnW, hpattern, hnC⟩ :=
    exists_pattern_normal_not_mem_avoiding A B offset W hW C hC normal
      ⟨hleft, hright⟩
  obtain ⟨high, hoffset_high, hhigh⟩ :=
    exists_high_level hB normal' offset hpattern.2
  exact ⟨⟨normal', offset, high, hoffset_high, hpattern.1, hhigh⟩, hnW, hnC⟩

/-! ## From an independent triple of planes to an oriented trihedral -/

private def algebraicNormal (normal : PlaneNormal) : Module.Dual ℝ (Point 3) :=
  normal.toLinearMap

private theorem algebraicNormals_linearIndependent {normal : Fin 3 → PlaneNormal}
    (h : LinearIndependent ℝ normal) :
    LinearIndependent ℝ (fun i => algebraicNormal (normal i)) := by
  let e : (Module.Dual ℝ (Point 3)) ≃ₗ[ℝ] PlaneNormal :=
    LinearMap.toContinuousLinearMap
  have hmapped := h.map' e.symm.toLinearMap (by simp)
  exact hmapped

private def planeCoordinateLinearEquiv (normal : Fin 3 → PlaneNormal)
    (h : LinearIndependent ℝ normal) : Point 3 ≃ₗ[ℝ] Point 3 := by
  let an : Fin 3 → Module.Dual ℝ (Point 3) :=
    fun i => algebraicNormal (normal i)
  have han : LinearIndependent ℝ an := algebraicNormals_linearIndependent h
  have hcard : Fintype.card (Fin 3) =
      Module.finrank ℝ (Module.Dual ℝ (Point 3)) := by
    rw [Subspace.dual_finrank_eq, finrank_euclideanSpace_fin]
    simp
  let b : Module.Basis (Fin 3) ℝ (Module.Dual ℝ (Point 3)) :=
    basisOfLinearIndependentOfCardEqFinrank' an han hcard
  let eFun : Point 3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    (Module.evalEquiv ℝ (Point 3)).trans b.dualBasis.equivFun
  exact eFun.trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm

private theorem planeCoordinateLinearEquiv_apply
    (normal : Fin 3 → PlaneNormal) (h : LinearIndependent ℝ normal)
    (x : Point 3) (i : Fin 3) :
    planeCoordinateLinearEquiv normal h x i = normal i x := by
  simp only [planeCoordinateLinearEquiv, LinearEquiv.trans_apply,
    WithLp.coe_symm_linearEquiv, WithLp.ofLp_toLp,
    Module.Basis.dualBasis_equivFun, Module.evalEquiv_apply, Module.Dual.eval_apply]
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

/-- The oriented trihedral whose normalized coordinates are the prescribed
independent affine functionals `normal i x - offset i`. -/
def orientedTrihedralOfIndependentPlanes
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) : OrientedTrihedral where
  normalization :=
    (planeCoordinateLinearEquiv normal h).toAffineEquiv.trans
      (AffineEquiv.constVAdd ℝ (Point 3) (-(WithLp.toLp 2 offset)))

@[simp] theorem orientedTrihedralOfIndependentPlanes_functional
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) (i : Fin 3) (x : Point 3) :
    (orientedTrihedralOfIndependentPlanes normal offset h).functional i x =
      normal i x - offset i := by
  simp [orientedTrihedralOfIndependentPlanes, OrientedTrihedral.functional,
    planeCoordinateLinearEquiv_apply]
  ring

private theorem secantSlope_ne_of_orientation
    {ax ay az bx «by» bz : ℝ}
    (haxy : ax ≠ ay) (hayz : ay ≠ az)
    (horient : (ay - ax) * (bz - bx) - (az - ax) * («by» - bx) ≠ 0) :
    («by» - bx) / (ay - ax) ≠ (bz - «by») / (az - ay) := by
  intro hslope
  have hcross := (div_eq_div_iff
    (sub_ne_zero.mpr haxy.symm) (sub_ne_zero.mpr hayz.symm)).mp hslope
  apply horient
  nlinarith

/-- The canonical edge projections are fully generic on `X` if each of the
three normalized affine coordinates is injective on `X` and every pair of
their linear parts has nonzero oriented area on every distinct triple. -/
private def genericProjectionFamilyOfIndependentPlanes
    (normal : Fin 3 → PlaneNormal) (offset : Fin 3 → ℝ)
    (h : LinearIndependent ℝ normal) (X : Finset (Point 3))
    (hinjective : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
      normal i x ≠ normal i y)
    (horient01 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 0 y - normal 0 x) * (normal 1 z - normal 1 x) -
          (normal 0 z - normal 0 x) * (normal 1 y - normal 1 x) ≠ 0)
    (horient02 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 0 y - normal 0 x) * (normal 2 z - normal 2 x) -
          (normal 0 z - normal 0 x) * (normal 2 y - normal 2 x) ≠ 0)
    (horient12 : ∀ {x y z : Point 3},
      x ∈ X → y ∈ X → z ∈ X →
      x ≠ y → y ≠ z → x ≠ z →
        (normal 1 y - normal 1 x) * (normal 2 z - normal 2 x) -
          (normal 1 z - normal 1 x) * (normal 2 y - normal 2 x) ≠ 0) :
    (orientedTrihedralOfIndependentPlanes normal offset h).GenericProjectionFamily X := by
  let T := orientedTrihedralOfIndependentPlanes normal offset h
  have hcoord : ∀ (i : Fin 3) (w : Point 3), T.normalization w i = normal i w - offset i :=
    orientedTrihedralOfIndependentPlanes_functional normal offset h
  refine {
    projection := T.edgeProjection
    image_carrier := T.edgeProjection_image_carrier
    separated := fun hfree _ _ hxy => T.projectionOrders_separated hfree hxy
    planeX_ne := ?_
    planeY_ne := ?_
    slope_ne := ?_ }
  · intro i x y hx hy hxy
    fin_cases i
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, planeX, hcoord] using hinjective 1 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, planeX, hcoord] using hinjective 0 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, planeX, hcoord] using hinjective 0 hx hy hxy
  · intro i x y hx hy hxy
    fin_cases i
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, planeY, hcoord] using hinjective 2 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, planeY, hcoord] using hinjective 2 hx hy hxy
    · simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, planeY, hcoord] using hinjective 1 hx hy hxy
  · intro i x y z hx hy hz hxy hyz hxz
    fin_cases i
    · have ho := horient12 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 1 hx hy hxy) (hinjective 1 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate0, secantSlope, planeX, planeY, hcoord] using hs
    · have ho := horient02 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 0 hx hy hxy) (hinjective 0 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate1, secantSlope, planeX, planeY, hcoord] using hs
    · have ho := horient01 hx hy hz hxy hyz hxz
      have hs := secantSlope_ne_of_orientation
        (hinjective 0 hx hy hxy) (hinjective 0 hy hz hyz) ho
      simpa [T, OrientedTrihedral.edgeProjection, dropCoordinate3,
        dropCoordinate2, secantSlope, planeX, planeY, hcoord] using hs

/-! ## The geometric output -/

/-- Three sets are in the strong three-object convex-position configuration
needed in the second Dilworth step.  Each object misses the convex hull of
the other two. -/
def ThreeSetsInConvexPosition (A B C : Set (Point 3)) : Prop :=
  Disjoint A (convexHull ℝ (B ∪ C)) ∧
    Disjoint B (convexHull ℝ (A ∪ C)) ∧
      Disjoint C (convexHull ℝ (A ∪ B))

/-- The complete Proposition 3.1 gadget attached to a middle cluster. -/
structure TrihedralClusterGadget {k : ℕ} (X : Fin k → Finset (Point 3))
    (j₁ j₂ j₃ : Fin k) where
  first : OrientedTrihedral
  second : OrientedTrihedral
  first_region_subset :
    (↑(clusterUnion X (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      first.carrier
  second_region_subset :
    (↑(clusterUnion X (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      second.carrier
  convex_position : ThreeSetsInConvexPosition first.carrier second.carrier
    (convexHull ℝ (↑(X j₂) : Set (Point 3)))
  first_line_comparable : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
    ¬ Disjoint (lineThrough x y) first.carrier →
      sourcePolytopeLE first.carrier x y ∨
        sourcePolytopeLE first.carrier y x
  comparable_line_second : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
    (sourcePolytopeLE first.carrier x y ∨
      sourcePolytopeLE first.carrier y x) →
        Disjoint (lineThrough x y) second.carrier
  first_generic : ∀ Y : Finset (Point 3), Y ⊆ X j₂ → first.GenericProjectionFamily Y
  second_generic : ∀ Y : Finset (Point 3), Y ⊆ X j₂ → second.GenericProjectionFamily Y

namespace TrihedralClusterGadget

theorem middle_disjoint_first {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    Disjoint (↑(X j₂) : Set (Point 3)) G.first.carrier := by
  apply Disjoint.symm
  exact G.convex_position.1.mono_right
    ((subset_convexHull ℝ _).trans (Set.subset_union_right.trans (subset_convexHull ℝ _)))

theorem middle_disjoint_second {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    Disjoint (↑(X j₂) : Set (Point 3)) G.second.carrier := by
  apply Disjoint.symm
  exact G.convex_position.2.1.mono_right
    ((subset_convexHull ℝ _).trans (Set.subset_union_right.trans (subset_convexHull ℝ _)))

/-- The exact input consumed by the second Dilworth--Ramsey step.  All free-
set conclusions are derived by `ofLineSeparation`; none is a field of the
trihedral construction. -/
def toMiddleTripleGadget {k : ℕ} {X : Fin k → Finset (Point 3)}
    {j₁ j₂ j₃ : Fin k} (G : TrihedralClusterGadget X j₁ j₂ j₃) :
    MiddleTripleGadget :=
  MiddleTripleGadget.ofLineSeparation (X j₂) G.first.carrier G.second.carrier
    G.middle_disjoint_first G.middle_disjoint_second
    (fun ⦃_⦄ hx ⦃_⦄ hy hxy hline => G.first_line_comparable hx hy hxy hline)
    (fun ⦃_⦄ hx ⦃_⦄ hy hxy hrel => G.comparable_line_second hx hy hxy hrel)

end TrihedralClusterGadget

private theorem convex_plane_le (normal : PlaneNormal) (c : ℝ) :
    Convex ℝ {x : Point 3 | normal x ≤ c} := by
  exact convex_halfSpace_le normal.toLinearMap.isLinear c

private theorem convex_plane_ge (normal : PlaneNormal) (c : ℝ) :
    Convex ℝ {x : Point 3 | c ≤ normal x} := by
  exact convex_halfSpace_ge normal.toLinearMap.isLinear c

private theorem convexHull_subset_plane_le {S : Set (Point 3)}
    {normal : PlaneNormal} {c : ℝ} (hS : ∀ x ∈ S, normal x ≤ c) :
    convexHull ℝ S ⊆ {x : Point 3 | normal x ≤ c} :=
  convexHull_min hS (convex_plane_le normal c)

private theorem convexHull_subset_plane_ge {S : Set (Point 3)}
    {normal : PlaneNormal} {c : ℝ} (hS : ∀ x ∈ S, c ≤ normal x) :
    convexHull ℝ S ⊆ {x : Point 3 | c ≤ normal x} :=
  convexHull_min hS (convex_plane_ge normal c)

private theorem disjoint_of_plane_gap {A B : Set (Point 3)}
    {normal : PlaneNormal} {low high : ℝ} (hlh : low < high)
    (hA : ∀ x ∈ A, high ≤ normal x)
    (hB : ∀ x ∈ B, normal x ≤ low) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  exact (not_le_of_gt hlh) ((hA x hxA).trans (hB x hxB))

/-! ## The source-poset line implications -/

/-- A line through two points of a convex set which meets a disjoint convex
background makes one of the two points lie in the convex hull of the other
point and the background.  The proof is the one-dimensional parameter
calculation used immediately after Proposition 3.1 in the source. -/
private theorem source_comparable_of_line_meets
    {P C : Set (Point 3)} (hC : Convex ℝ C) (hPC : Disjoint P C)
    {x y : Point 3} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hmeet : ¬ Disjoint (lineThrough x y) P) :
    sourcePolytopeLE P x y ∨ sourcePolytopeLE P y x := by
  obtain ⟨p, hpline, hpP⟩ := Set.not_disjoint_iff.mp hmeet
  rw [lineThrough, SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hpline
  obtain ⟨t, ht⟩ := hpline
  have htout : t ∉ Set.Icc (0 : ℝ) 1 := by
    intro htI
    apply Set.disjoint_left.mp hPC hpP
    rw [← ht]
    exact hC.lineMap_mem hx hy htI
  have htcase : t < 0 ∨ 1 < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using htout
  rcases htcase with htneg | htpos
  · left
    let s : ℝ := -t / (1 - t)
    have hden : 0 < 1 - t := by linarith
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) hden.le
      · exact (div_le_one hden).mpr (by linarith)
    have heq : AffineMap.lineMap p y s = x := by
      rw [← ht]
      ext i
      simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
        WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [sourcePolytopeLE, ← heq]
    apply (convex_convexHull ℝ _).lineMap_mem
    · exact subset_convexHull ℝ _ (Or.inr hpP)
    · exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton y))
    · exact hs
  · right
    let s : ℝ := 1 / t
    have ht0 : 0 < t := by linarith
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg zero_le_one ht0.le
      · exact (div_le_one ht0).mpr (by linarith)
    have heq : AffineMap.lineMap x p s = y := by
      rw [← ht]
      ext i
      simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
        WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [sourcePolytopeLE, ← heq]
    apply (convex_convexHull ℝ _).lineMap_mem
    · exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton x))
    · exact subset_convexHull ℝ _ (Or.inr hpP)
    · exact hs

private theorem line_meets_of_sourcePolytopeLE
    {P : Set (Point 3)} (hPconv : Convex ℝ P) (hPne : P.Nonempty)
    {x y : Point 3} (hxy : x ≠ y) (hxP : x ∉ P)
    (hrel : sourcePolytopeLE P x y) :
    ¬ Disjoint (lineThrough x y) P := by
  rw [sourcePolytopeLE,
    (convex_singleton y).convexHull_union hPconv
      (Set.singleton_nonempty y) hPne, mem_convexJoin] at hrel
  obtain ⟨q, hq, p, hpP, hxseg⟩ := hrel
  rw [Set.mem_singleton_iff] at hq
  subst q
  have hpLine : p ∈ lineThrough x y := by
    rw [lineThrough, Set.pair_comm x y]
    exact ((mem_segment_iff_wbtw.mp hxseg).symm).left_mem_affineSpan_of_right_ne
      hxy.symm
  exact Set.not_disjoint_iff.mpr ⟨p, hpLine, hpP⟩

/-- If two sets lie strictly on one side of a linear functional while two
points lie on the other side, their common affine line cannot meet both sets
when each set is exposed from the convex hull of the other set and the high
side.  This is the collinear three-object argument in an explicit scalar
parameter form. -/
private theorem line_disjoint_of_two_low_exposed
    {P Q C : Set (Point 3)} (normal : PlaneNormal) {low high : ℝ}
    (hlh : low < high)
    (hP : ∀ p ∈ P, normal p ≤ low) (hQ : ∀ q ∈ Q, normal q ≤ low)
    (hC : ∀ c ∈ C, high ≤ normal c)
    (hPexposed : Disjoint P (convexHull ℝ (Q ∪ C)))
    (hQexposed : Disjoint Q (convexHull ℝ (P ∪ C)))
    {x y : Point 3} (hx : x ∈ C) (hy : y ∈ C) :
    ¬ Disjoint (lineThrough x y) P → Disjoint (lineThrough x y) Q := by
  intro hlineP
  by_contra hlineQ
  obtain ⟨p, hpline, hpP⟩ := Set.not_disjoint_iff.mp hlineP
  obtain ⟨q, hqline, hqQ⟩ := Set.not_disjoint_iff.mp hlineQ
  rw [lineThrough, SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hpline hqline
  obtain ⟨t, ht⟩ := hpline
  obtain ⟨u, hu⟩ := hqline
  have htout : t < 0 ∨ 1 < t := by
    have htI : t ∉ Set.Icc (0 : ℝ) 1 := by
      intro htI
      have hpHigh : high ≤ normal p := by
        rw [← ht]
        simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub,
          smul_eq_mul]
        rcases htI with ⟨ht0, ht1⟩
        nlinarith [hC x hx, hC y hy]
      exact (not_le_of_gt hlh) (hpHigh.trans (hP p hpP))
    simpa only [Set.mem_Icc, not_and_or, not_le] using htI
  have huout : u < 0 ∨ 1 < u := by
    have huI : u ∉ Set.Icc (0 : ℝ) 1 := by
      intro huI
      have hqHigh : high ≤ normal q := by
        rw [← hu]
        simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub,
          smul_eq_mul]
        rcases huI with ⟨hu0, hu1⟩
        nlinarith [hC x hx, hC y hy]
      exact (not_le_of_gt hlh) (hqHigh.trans (hQ q hqQ))
    simpa only [Set.mem_Icc, not_and_or, not_le] using huI
  have hpformula : normal p = (1 - t) * normal x + t * normal y := by
    rw [← ht]
    simp [AffineMap.lineMap_apply_module']
    ring
  have hqformula : normal q = (1 - u) * normal x + u * normal y := by
    rw [← hu]
    simp [AffineMap.lineMap_apply_module']
    ring
  have hsame : (t < 0 ∧ u < 0) ∨ (1 < t ∧ 1 < u) := by
    rcases htout with htneg | htpos <;> rcases huout with huneg | hupos
    · exact Or.inl ⟨htneg, huneg⟩
    · exfalso
      nlinarith [hP p hpP, hQ q hqQ, hC x hx, hC y hy,
        hpformula, hqformula]
    · exfalso
      nlinarith [hP p hpP, hQ q hqQ, hC x hx, hC y hy,
        hpformula, hqformula]
    · exact Or.inr ⟨htpos, hupos⟩
  rcases hsame with hneg | hpos
  · rcases le_total t u with htu | hut
    · have ht0 : t ≠ 0 := ne_of_lt hneg.1
      let s : ℝ := 1 - u / t
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · have : u / t ≤ 1 := (div_le_one_of_neg hneg.1).2 htu
          linarith
        · have : 0 ≤ u / t := div_nonneg_of_nonpos hneg.2.le hneg.1.le
          linarith
      have heq : AffineMap.lineMap p x s = q := by
        rw [← ht, ← hu]
        ext i
        simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
          WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      apply Set.disjoint_left.mp hQexposed hqQ
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inl hpP)
      · exact subset_convexHull ℝ _ (Or.inr hx)
      · exact hs
    · have hu0 : u ≠ 0 := ne_of_lt hneg.2
      let s : ℝ := 1 - t / u
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · have : t / u ≤ 1 := (div_le_one_of_neg hneg.2).2 hut
          linarith
        · have : 0 ≤ t / u := div_nonneg_of_nonpos hneg.1.le hneg.2.le
          linarith
      have heq : AffineMap.lineMap q x s = p := by
        rw [← hu, ← ht]
        ext i
        simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
          WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      apply Set.disjoint_left.mp hPexposed hpP
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inl hqQ)
      · exact subset_convexHull ℝ _ (Or.inr hx)
      · exact hs
  · rcases le_total t u with htu | hut
    · have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpos.2)
      let s : ℝ := (t - 1) / (u - 1)
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · exact (div_le_one (by linarith)).mpr (by linarith)
      have heq : AffineMap.lineMap y q s = p := by
        rw [← hu, ← ht]
        ext i
        simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
          WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      apply Set.disjoint_left.mp hPexposed hpP
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inr hy)
      · exact subset_convexHull ℝ _ (Or.inl hqQ)
      · exact hs
    · have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpos.1)
      let s : ℝ := (u - 1) / (t - 1)
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · exact (div_le_one (by linarith)).mpr (by linarith)
      have heq : AffineMap.lineMap y p s = q := by
        rw [← ht, ← hu]
        ext i
        simp only [AffineMap.lineMap_apply_module', s, WithLp.ofLp_add, WithLp.ofLp_sub,
          WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      apply Set.disjoint_left.mp hQexposed hqQ
      rw [← heq]
      apply (convex_convexHull ℝ _).lineMap_mem
      · exact subset_convexHull ℝ _ (Or.inr hy)
      · exact subset_convexHull ℝ _ (Or.inl hpP)
      · exact hs
/-!
The following is the literal construction.  Its two separation hypotheses
are exactly the full-cluster conclusions produced by applying Proposition
2.7 to the two alternating representative-plane patterns.  No polyhedron,
poset, free-set, or cap conclusion is assumed.
-/

set_option maxHeartbeats 400000 in
/-- Pohoata--Zakharov Proposition 3.1: two alternating-block separations and
strong convex position of the support clusters produce the two trihedral
polyhedra with the containments (4.8) and the required three-object convex
position. -/
theorem pohoata_zakharov_prop_three_one {k : ℕ}
    (X : Fin k → Finset (Point 3)) (j₁ j₂ j₃ : Fin k)
    (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃)
    (hne : ∀ i, (X i).Nonempty)
    (htriple : NoThreeCollinear (X j₂))
    (hstrong : StrongConvexPositionClusters X)
    (hfirst : Disjoint
      (convexHull ℝ
        (↑(clusterUnion X (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion X
          (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) : Set (Point 3))))
    (hsecond : Disjoint
      (convexHull ℝ
        (↑(clusterUnion X
          (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion X (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))) :
    Nonempty (TrihedralClusterGadget X j₁ j₂ j₃) := by
  classical
  let I₁ := firstTrihedralIndices j₁ j₂ j₃
  let I₂ := secondTrihedralIndices j₁ j₂ j₃
  let A₀ := clusterUnion X (Finset.univ.erase j₂)
  let B₀ := X j₂
  let A₁ := clusterUnion X (I₂ ∪ {j₂})
  let B₁ := clusterUnion X I₁
  let A₂ := clusterUnion X I₂
  let B₂ := clusterUnion X (I₁ ∪ {j₂})

  have hB₀ : B₀.Nonempty := hne j₂
  have hj₃I₁ : j₃ ∈ I₁ := by
    simp [I₁, h₂₃]
  have hB₁ : B₁.Nonempty := by
    obtain ⟨x, hx⟩ := hne j₃
    exact ⟨x, by
      simp only [B₁, clusterUnion, Finset.mem_biUnion]
      exact ⟨j₃, hj₃I₁, hx⟩⟩
  have hB₂ : B₂.Nonempty := by
    obtain ⟨x, hx⟩ := hne j₂
    exact ⟨x, by
      simp only [B₂, clusterUnion, Finset.mem_biUnion]
      exact ⟨j₂, by simp, hx⟩⟩

  have hsep₀ : Disjoint (convexHull ℝ (A₀ : Set (Point 3)))
      (convexHull ℝ (B₀ : Set (Point 3))) := by
    simpa [A₀, B₀] using (hstrong j₂).symm
  have hsep₁ : Disjoint (convexHull ℝ (A₁ : Set (Point 3)))
      (convexHull ℝ (B₁ : Set (Point 3))) := by
    simpa [A₁, B₁, I₁, I₂] using hfirst.symm
  have hsep₂ : Disjoint (convexHull ℝ (A₂ : Set (Point 3)))
      (convexHull ℝ (B₂ : Set (Point 3))) := by
    simpa [A₂, B₂, I₁, I₂] using hsecond.symm

  let emptyNormals : Fin 0 → PlaneNormal := fun i => Fin.elim0 i
  let W₀ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range emptyNormals)
  have hW₀ : W₀ ≠ ⊤ := span_planeNormals_ne_top (by omega) emptyNormals
  let C₀ := pointDifferenceConstraints B₀
  have hC₀ : ∀ L ∈ C₀, L ≠ 0 := by
    simpa [C₀] using pointDifferenceConstraints_nonzero B₀
  obtain ⟨S₀, hS₀W, hS₀C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₀ B₀ hB₀ hsep₀ W₀ hW₀ C₀ hC₀
  have hS₀inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₀.normal x ≠ S₀.normal y := by
    exact realizes_pointDifferenceConstraints_iff.mp (by simpa [C₀] using hS₀C)

  let normals₁ : Fin 1 → PlaneNormal := Fin.snoc emptyNormals S₀.normal
  let W₁ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range normals₁)
  have hW₁ : W₁ ≠ ⊤ := span_planeNormals_ne_top (by omega) normals₁
  let C₁ := pointDifferenceConstraints B₀ ∪ planarOrientationConstraints B₀ S₀.normal
  have hC₁ : ∀ L ∈ C₁, L ≠ 0 := by
    intro L hL
    rw [Finset.mem_union] at hL
    exact hL.elim (pointDifferenceConstraints_nonzero B₀ L)
      (planarOrientationConstraints_nonzero htriple hS₀inj L)
  obtain ⟨S₁, hS₁W, hS₁C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₁ B₁ hB₁ hsep₁ W₁ hW₁ C₁ hC₁
  have hS₁inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₁.normal x ≠ S₁.normal y := by
    apply realizes_pointDifferenceConstraints_iff.mp
    intro L hL
    exact hS₁C L (by simp [C₁, hL])
  have hS₀S₁orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₀.normal y - S₀.normal x) * (S₁.normal z - S₁.normal x) -
            (S₀.normal z - S₀.normal x) * (S₁.normal y - S₁.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₁C L (by simp [C₁, hL])

  let normals₂ : Fin 2 → PlaneNormal := Fin.snoc normals₁ S₁.normal
  let W₂ : Submodule ℝ PlaneNormal :=
    Submodule.span ℝ (Set.range normals₂)
  have hW₂ : W₂ ≠ ⊤ := span_planeNormals_ne_top (by omega) normals₂
  let C₂ := pointDifferenceConstraints B₀ ∪
    (planarOrientationConstraints B₀ S₀.normal ∪
      planarOrientationConstraints B₀ S₁.normal)
  have hC₂ : ∀ L ∈ C₂, L ≠ 0 := by
    intro L hL
    simp only [C₂, Finset.mem_union] at hL
    rcases hL with hL | hL | hL
    · exact pointDifferenceConstraints_nonzero B₀ L hL
    · exact planarOrientationConstraints_nonzero htriple hS₀inj L hL
    · exact planarOrientationConstraints_nonzero htriple hS₁inj L hL
  obtain ⟨S₂, hS₂W, hS₂C⟩ :=
    exists_strictPlaneSplit_avoiding_generic A₂ B₂ hB₂ hsep₂ W₂ hW₂ C₂ hC₂
  have hS₂inj : ∀ x ∈ B₀, ∀ y ∈ B₀, x ≠ y → S₂.normal x ≠ S₂.normal y := by
    apply realizes_pointDifferenceConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])
  have hS₀S₂orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₀.normal y - S₀.normal x) * (S₂.normal z - S₂.normal x) -
            (S₀.normal z - S₀.normal x) * (S₂.normal y - S₂.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])
  have hS₁S₂orient :
      ∀ x ∈ B₀, ∀ y ∈ B₀, ∀ z ∈ B₀,
        x ≠ y → y ≠ z → x ≠ z →
          (S₁.normal y - S₁.normal x) * (S₂.normal z - S₂.normal x) -
            (S₁.normal z - S₁.normal x) * (S₂.normal y - S₂.normal x) ≠ 0 := by
    apply realizes_planarOrientationConstraints_iff.mp
    intro L hL
    exact hS₂C L (by simp [C₂, hL])

  let normals : Fin 3 → PlaneNormal := Fin.snoc normals₂ S₂.normal
  have hempty : LinearIndependent ℝ emptyNormals := linearIndependent_empty_type
  have hnormals₁ : LinearIndependent ℝ normals₁ := by
    exact hempty.finSnoc hS₀W
  have hnormals₂ : LinearIndependent ℝ normals₂ := by
    exact hnormals₁.finSnoc hS₁W
  have hnormals : LinearIndependent ℝ normals := by
    exact hnormals₂.finSnoc hS₂W

  let signs : Fin 3 → ℝˣ := ![(1 : ℝˣ), (-1 : ℝˣ), (-1 : ℝˣ)]
  let firstNormals : Fin 3 → PlaneNormal := signs • normals
  have hfirstNormals : LinearIndependent ℝ firstNormals := by
    exact hnormals.units_smul signs
  let firstOffsets : Fin 3 → ℝ := ![S₀.low, -S₁.high, -S₂.high]
  let secondOffsets : Fin 3 → ℝ := ![S₀.low, S₁.low, S₂.low]
  let P₁ : OrientedTrihedral :=
    orientedTrihedralOfIndependentPlanes firstNormals firstOffsets hfirstNormals
  let P₂ : OrientedTrihedral :=
    orientedTrihedralOfIndependentPlanes normals secondOffsets hnormals

  have hnormals0 : normals 0 = S₀.normal := by
    simp [normals, normals₂, normals₁, Fin.snoc]
  have hnormals1 : normals 1 = S₁.normal := by
    simp [normals, normals₂, normals₁, Fin.snoc]
  have hnormals2 : normals 2 = S₂.normal := by
    simp [normals, normals₂, normals₁, Fin.snoc]
  have hnormalsinj : ∀ i {x y : Point 3}, x ∈ B₀ → y ∈ B₀ → x ≠ y →
      normals i x ≠ normals i y := by
    intro i x y hx hy hxy
    fin_cases i
    · simpa [hnormals0] using hS₀inj x hx y hy hxy
    · simpa [hnormals1] using hS₁inj x hx y hy hxy
    · simpa [hnormals2] using hS₂inj x hx y hy hxy
  have hnormals01 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 0 y - normals 0 x) * (normals 1 z - normals 1 x) -
          (normals 0 z - normals 0 x) * (normals 1 y - normals 1 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz
    simpa [hnormals0, hnormals1] using hS₀S₁orient x hx y hy z hz hxy hyz hxz
  have hnormals02 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 0 y - normals 0 x) * (normals 2 z - normals 2 x) -
          (normals 0 z - normals 0 x) * (normals 2 y - normals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz
    simpa [hnormals0, hnormals2] using hS₀S₂orient x hx y hy z hz hxy hyz hxz
  have hnormals12 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (normals 1 y - normals 1 x) * (normals 2 z - normals 2 x) -
          (normals 1 z - normals 1 x) * (normals 2 y - normals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz
    simpa [hnormals1, hnormals2] using hS₁S₂orient x hx y hy z hz hxy hyz hxz
  have hfirstNormalsinj : ∀ i {x y : Point 3}, x ∈ B₀ → y ∈ B₀ → x ≠ y →
      firstNormals i x ≠ firstNormals i y := by
    intro i x y hx hy hxy
    fin_cases i
    · simpa [firstNormals, signs] using hnormalsinj (i := 0) hx hy hxy
    · simpa [firstNormals, signs] using hnormalsinj (i := 1) hx hy hxy
    · simpa [firstNormals, signs] using hnormalsinj (i := 2) hx hy hxy
  have hfirstNormals01 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 0 y - firstNormals 0 x) *
            (firstNormals 1 z - firstNormals 1 x) -
          (firstNormals 0 z - firstNormals 0 x) *
            (firstNormals 1 y - firstNormals 1 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals01 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  have hfirstNormals02 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 0 y - firstNormals 0 x) *
            (firstNormals 2 z - firstNormals 2 x) -
          (firstNormals 0 z - firstNormals 0 x) *
            (firstNormals 2 y - firstNormals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals02 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  have hfirstNormals12 : ∀ {x y z : Point 3},
      x ∈ B₀ → y ∈ B₀ → z ∈ B₀ →
      x ≠ y → y ≠ z → x ≠ z →
        (firstNormals 1 y - firstNormals 1 x) *
            (firstNormals 2 z - firstNormals 2 x) -
          (firstNormals 1 z - firstNormals 1 x) *
            (firstNormals 2 y - firstNormals 2 x) ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz hzero
    apply hnormals12 hx hy hz hxy hyz hxz
    simp [firstNormals, signs] at hzero
    nlinarith
  let P₁generic : ∀ Y : Finset (Point 3), Y ⊆ B₀ →
      P₁.GenericProjectionFamily Y := fun Y hY =>
    genericProjectionFamilyOfIndependentPlanes firstNormals firstOffsets hfirstNormals Y
      (fun i {_ _} hx hy hxy => hfirstNormalsinj i (hY hx) (hY hy) hxy)
      (fun {_ _ _} hx hy hz => hfirstNormals01 (hY hx) (hY hy) (hY hz))
      (fun {_ _ _} hx hy hz => hfirstNormals02 (hY hx) (hY hy) (hY hz))
      (fun {_ _ _} hx hy hz => hfirstNormals12 (hY hx) (hY hy) (hY hz))
  let P₂generic : ∀ Y : Finset (Point 3), Y ⊆ B₀ →
      P₂.GenericProjectionFamily Y := fun Y hY =>
    genericProjectionFamilyOfIndependentPlanes normals secondOffsets hnormals Y
      (fun i {_ _} hx hy hxy => hnormalsinj i (hY hx) (hY hy) hxy)
      (fun {_ _ _} hx hy hz => hnormals01 (hY hx) (hY hy) (hY hz))
      (fun {_ _ _} hx hy hz => hnormals02 (hY hx) (hY hy) (hY hz))
      (fun {_ _ _} hx hy hz => hnormals12 (hY hx) (hY hy) (hY hz))
  have hP₁mem (x : Point 3)
      (h₀ : S₀.normal x ≤ S₀.low)
      (h₁ : S₁.high ≤ S₁.normal x)
      (h₂ : S₂.high ≤ S₂.normal x) : x ∈ P₁.carrier := by
    rw [OrientedTrihedral.mem_carrier_iff]
    intro i
    fin_cases i
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals0]
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals1] using (neg_le_neg h₁)
    · simpa [P₁, firstNormals, firstOffsets, signs, hnormals2] using (neg_le_neg h₂)
  have hP₂mem (x : Point 3)
      (h₀ : S₀.normal x ≤ S₀.low)
      (h₁ : S₁.normal x ≤ S₁.low)
      (h₂ : S₂.normal x ≤ S₂.low) : x ∈ P₂.carrier := by
    rw [OrientedTrihedral.mem_carrier_iff]
    intro i
    fin_cases i
    · simpa [P₂, secondOffsets, hnormals0] using h₀
    · simpa [P₂, secondOffsets, hnormals1] using h₁
    · simpa [P₂, secondOffsets, hnormals2] using h₂

  have hfirst_subset : (↑(clusterUnion X I₁) : Set (Point 3)) ⊆ P₁.carrier := by
    intro x hx
    have hxB₁ : x ∈ B₁ := by simpa [B₁]
    have hxB₂ : x ∈ B₂ := by
      simp only [B₂, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact ⟨i, by simp [hi], hxi⟩
    have hxA₀ : x ∈ A₀ := by
      simp only [A₀, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      have hij : i ≠ j₂ := by
        intro h
        subst i
        simp [I₁, h₁₂, h₂₃] at hi
        exact absurd h₁₂ (asymm hi)
      exact ⟨i, by simp [hij], hxi⟩
    exact hP₁mem x (S₀.left_lt_low x hxA₀).le
      (S₁.high_lt_right x hxB₁).le
      (S₂.high_lt_right x hxB₂).le
  have hsecond_subset : (↑(clusterUnion X I₂) : Set (Point 3)) ⊆ P₂.carrier := by
    intro x hx
    have hxA₁ : x ∈ A₁ := by
      simp only [A₁, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact ⟨i, by simp [hi], hxi⟩
    have hxA₂ : x ∈ A₂ := by simpa [A₂]
    have hxA₀ : x ∈ A₀ := by
      simp only [A₀, clusterUnion, Finset.mem_biUnion]
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      have hij : i ≠ j₂ := by
        intro h
        subst i
        simp [I₂, h₁₂, h₂₃] at hi
        exact absurd h₂₃ (asymm hi)
      exact ⟨i, by simp [hij], hxi⟩
    exact hP₂mem x (S₀.left_lt_low x hxA₀).le
      (S₁.left_lt_low x hxA₁).le
      (S₂.left_lt_low x hxA₂).le

  have hP₁bounds (x : Point 3) (hx : x ∈ P₁.carrier) :
      S₀.normal x ≤ S₀.low ∧
        S₁.high ≤ S₁.normal x ∧
          S₂.high ≤ S₂.normal x := by
    rw [OrientedTrihedral.mem_carrier_iff] at hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp [P₁, orientedTrihedralOfIndependentPlanes_functional,
      firstNormals, firstOffsets, signs, Pi.smul_apply, Units.smul_def,
      hnormals0, hnormals1, hnormals2] at h0 h1 h2
    constructor
    · linarith
    · constructor <;> linarith
  have hP₂bounds (x : Point 3) (hx : x ∈ P₂.carrier) :
      S₀.normal x ≤ S₀.low ∧
        S₁.normal x ≤ S₁.low ∧
          S₂.normal x ≤ S₂.low := by
    rw [OrientedTrihedral.mem_carrier_iff] at hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp [P₂, orientedTrihedralOfIndependentPlanes_functional,
      secondOffsets, hnormals0, hnormals1, hnormals2] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hM₀ (x : Point 3) (hx : x ∈ X j₂) :
      S₀.high ≤ S₀.normal x :=
    (S₀.high_lt_right x (by simpa [B₀] using hx)).le
  have hM₁ (x : Point 3) (hx : x ∈ X j₂) :
      S₁.normal x ≤ S₁.low := by
    apply (S₁.left_lt_low x ?_).le
    simp only [A₁, clusterUnion, Finset.mem_biUnion]
    exact ⟨j₂, by simp, hx⟩
  have hM₂ (x : Point 3) (hx : x ∈ X j₂) :
      S₂.high ≤ S₂.normal x := by
    apply (S₂.high_lt_right x ?_).le
    simp only [B₂, clusterUnion, Finset.mem_biUnion]
    exact ⟨j₂, by simp, hx⟩

  let M : Set (Point 3) := convexHull ℝ (↑(X j₂) : Set (Point 3))
  have hM₀hull : ∀ x ∈ M, S₀.high ≤ S₀.normal x := by
    exact convexHull_subset_plane_ge (fun x hx => hM₀ x hx)
  have hM₁hull : ∀ x ∈ M, S₁.normal x ≤ S₁.low := by
    exact convexHull_subset_plane_le (fun x hx => hM₁ x hx)
  have hM₂hull : ∀ x ∈ M, S₂.high ≤ S₂.normal x := by
    exact convexHull_subset_plane_ge (fun x hx => hM₂ x hx)

  have hconv₁ : Disjoint P₁.carrier (convexHull ℝ (P₂.carrier ∪ M)) := by
    apply disjoint_of_plane_gap S₁.low_lt_high
    · exact fun x hx => (hP₁bounds x hx).2.1
    · apply convexHull_subset_plane_le
      intro x hx
      rcases hx with hx | hx
      · exact (hP₂bounds x hx).2.1
      · exact hM₁hull x hx
  have hconv₂ : Disjoint P₂.carrier (convexHull ℝ (P₁.carrier ∪ M)) := by
    apply Disjoint.symm
    apply disjoint_of_plane_gap S₂.low_lt_high
    · apply convexHull_subset_plane_ge
      intro x hx
      rcases hx with hx | hx
      · exact (hP₁bounds x hx).2.2
      · exact hM₂hull x hx
    · exact fun x hx => (hP₂bounds x hx).2.2
  have hconvM : Disjoint M (convexHull ℝ (P₁.carrier ∪ P₂.carrier)) := by
    apply disjoint_of_plane_gap S₀.low_lt_high
    · exact hM₀hull
    · apply convexHull_subset_plane_le
      intro x hx
      exact hx.elim (fun h => (hP₁bounds x h).1) (fun h => (hP₂bounds x h).1)

  have hP₁M : Disjoint P₁.carrier M := by
    apply hconv₁.mono_right
    intro x hx
    exact subset_convexHull ℝ _ (Or.inr hx)
  have hP₂M : Disjoint P₂.carrier M := by
    apply hconv₂.mono_right
    intro x hx
    exact subset_convexHull ℝ _ (Or.inr hx)
  have hP₁ne : P₁.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hB₁
    exact ⟨x, hfirst_subset (by simpa [B₁])⟩
  have hfirstLine : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
      ¬ Disjoint (lineThrough x y) P₁.carrier →
        sourcePolytopeLE P₁.carrier x y ∨
          sourcePolytopeLE P₁.carrier y x := by
    intro x hx y hy hxy hmeet
    apply source_comparable_of_line_meets (convex_convexHull ℝ _) hP₁M
      (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy) hxy hmeet
  have hsecondLine : ∀ {x}, x ∈ X j₂ → ∀ {y}, y ∈ X j₂ → x ≠ y →
      (sourcePolytopeLE P₁.carrier x y ∨
        sourcePolytopeLE P₁.carrier y x) →
          Disjoint (lineThrough x y) P₂.carrier := by
    intro x hx y hy hxy hrel
    have hxM : x ∈ M := subset_convexHull ℝ _ hx
    have hyM : y ∈ M := subset_convexHull ℝ _ hy
    have hmeet : ¬ Disjoint (lineThrough x y) P₁.carrier := by
      rcases hrel with hrel | hrel
      · exact line_meets_of_sourcePolytopeLE P₁.convex_carrier hP₁ne hxy
          (Set.disjoint_left.mp hP₁M · hxM) hrel
      · have hmeet' := line_meets_of_sourcePolytopeLE
          P₁.convex_carrier hP₁ne hxy.symm
          (Set.disjoint_left.mp hP₁M · hyM) hrel
        simpa [lineThrough, Set.pair_comm] using hmeet'
    exact line_disjoint_of_two_low_exposed S₀.normal S₀.low_lt_high
      (fun p hp => (hP₁bounds p hp).1) (fun q hq => (hP₂bounds q hq).1)
      hM₀hull hconv₁ hconv₂ hxM hyM hmeet

  exact ⟨⟨P₁, P₂, by simpa [I₁], by simpa [I₂],
    ⟨hconv₁, hconv₂, hconvM⟩, hfirstLine, hsecondLine,
      P₁generic, P₂generic⟩⟩

end

end

/-! ### Upstream module `JSP527/PZ/Assembly.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex (original assembly draft), with completion and repairs for the JSP-000527
submission (2026-09-16).

Derived from plby/lean-proofs `src/latest/ErdosProblems/Erdos651/PohoataZakharovProof.lean`
(commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e), a draft that was never part of that
repository's build and that reduced Theorem 1.1 to an unproved extraction hypothesis.  This file
keeps that draft's statements (repaired where they did not elaborate) and adds the missing
unconditional extraction; every deviation from the original is listed in `external-changes.txt`.
-/

/-!
# The Pohoata--Zakharov assembly

This file assembles the geometric and numerical ingredients of the proof of
Pohoata--Zakharov, Theorem 1.1.  In particular, it keeps the cap-union step
and the conversion of the source's final envelope into the literal point-set
epsilon statement explicit.
-/

open _root_.Filter _root_.Finset _root_.Set
noncomputable section

/-! ## Lifting the planar positive-fraction configuration -/

/-- The vertical projection of `ℝ³` onto its first two coordinates, packaged
as an affine map so it can be used where a `Point 3 →ᵃ[ℝ] Point 2` is
required. -/
def verticalProjectionAffine : Point 3 →ᵃ[ℝ] Point 2 :=
  dropCoordinate2.toAffineMap

@[simp] theorem coe_verticalProjectionAffine :
    ⇑verticalProjectionAffine = verticalProjection := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [verticalProjectionAffine, dropCoordinate2, verticalProjection]

/-- A Pór--Valtr configuration in a generic planar projection of `X`.
The actual spatial cells are the points of `X` whose images lie in the
corresponding planar cells. -/
structure LiftedPositiveFractionConfiguration
    (k : ℕ) (X : Finset (Point 3)) where
  projection : Point 3 →ᵃ[ℝ] Point 2
  projection_inj : Set.InjOn projection X
  planar : OrderedStrongPositiveFractionConfiguration k (X.image projection)

def LiftedPositiveFractionConfiguration.cell
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    Finset (Point 3) :=
  X.filter fun x ↦ C.projection x ∈ C.planar.cell i

theorem LiftedPositiveFractionConfiguration.cell_subset
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    C.cell i ⊆ X := by
  exact Finset.filter_subset _ _

theorem LiftedPositiveFractionConfiguration.image_cell
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    (C.cell i).image C.projection = C.planar.cell i := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    have hyambient := C.planar.cell_subset i hy
    obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp hyambient
    subst y
    exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩

theorem LiftedPositiveFractionConfiguration.cell_card
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    (C.cell i).card = (C.planar.cell i).card := by
  rw [← C.image_cell i, Finset.card_image_of_injOn]
  exact C.projection_inj.mono (C.cell_subset i)

theorem LiftedPositiveFractionConfiguration.cell_disjoint
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) :
    PairwiseDisjointClusters C.cell := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hpi : C.projection x ∈ C.planar.cell i :=
    (Finset.mem_filter.mp hxi).2
  have hpj : C.projection x ∈ C.planar.cell j :=
    (Finset.mem_filter.mp hxj).2
  exact Finset.disjoint_left.mp (C.planar.cell_disjoint hij) hpi hpj

theorem LiftedPositiveFractionConfiguration.cell_density
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    X.card ≤ 2 ^ (40 * k) * (C.cell i).card := by
  have hambient : (X.image C.projection).card = X.card :=
    Finset.card_image_of_injOn C.projection_inj
  simpa [HasPositiveFractionDensity, hambient, C.cell_card i] using
    C.planar.cell_dense i

theorem LiftedPositiveFractionConfiguration.allCells_subset
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) :
    allClusters C.cell ⊆ X := by
  intro x hx
  rw [mem_allClusters_iff] at hx
  exact C.cell_subset hx.choose hx.choose_spec

theorem LiftedPositiveFractionConfiguration.image_clusterUnion
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (I : Finset (Fin k)) :
    (clusterUnion C.cell I).image C.projection =
      planarClusterUnion C.planar.cell I := by
  classical
  ext y
  simp only [clusterUnion, planarClusterUnion, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨x, ⟨i, hiI, hxi⟩, rfl⟩
    exact ⟨i, hiI, by
      rw [← C.image_cell i]
      exact Finset.mem_image_of_mem C.projection hxi⟩
  · rintro ⟨i, hiI, hyi⟩
    rw [← C.image_cell i] at hyi
    obtain ⟨x, hxi, rfl⟩ := Finset.mem_image.mp hyi
    exact ⟨x, ⟨i, hiI, hxi⟩, rfl⟩

/-- Whole-cell strong convex position also lifts through the generic affine
projection. -/
theorem LiftedPositiveFractionConfiguration.strong_convex :
    {k : ℕ} → {X : Finset (Point 3)} →
    (C : LiftedPositiveFractionConfiguration k X) →
    StrongConvexPositionClusters C.cell := by
  intro k X C i
  rw [Set.disjoint_left]
  intro z hzi hzother
  have hzpi : C.projection z ∈
      convexHull ℝ ((C.planar.cell i : Finset (Point 2)) : Set (Point 2)) := by
    rw [← C.image_cell i, Finset.coe_image, ← C.projection.image_convexHull]
    exact ⟨z, hzi, rfl⟩
  have hzpother : C.projection z ∈
      convexHull ℝ
        ((planarClusterUnion C.planar.cell (Finset.univ.erase i) :
          Finset (Point 2)) : Set (Point 2)) := by
    rw [← C.image_clusterUnion (Finset.univ.erase i), Finset.coe_image,
      ← C.projection.image_convexHull]
    exact ⟨z, hzother, rfl⟩
  exact Set.disjoint_left.1 (C.planar.strong_convex i) hzpi hzpother

/-- The output after Proposition 2.5, retaining the source-correct strong
convexity and the exact combined density loss. -/
structure SeparatedPositiveFractionClusters
    (k : ℕ) (X : Finset (Point 3)) where
  source : LiftedPositiveFractionConfiguration k X
  cluster : Fin k → Finset (Point 3)
  cluster_subset_source : ∀ i, cluster i ⊆ source.cell i
  twoSeparated : TwoSeparatedClusters cluster
  strongConvex : StrongConvexPositionClusters cluster
  density : ∀ i,
    X.card ≤ 2 ^ (40 * k + k ^ 3) * (cluster i).card
  nonempty : ∀ i, (cluster i).Nonempty

def SeparatedPositiveFractionClusters.representative
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) (i : Fin k) : Point 3 :=
  Exists.choose (C.nonempty i)

theorem SeparatedPositiveFractionClusters.representative_mem
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) :
    IsClusterTransversal C.cluster C.representative := by
  intro i
  exact Exists.choose_spec (C.nonempty i)

theorem SeparatedPositiveFractionClusters.representative_projection_mem
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) (i : Fin k) :
    C.source.projection (C.representative i) ∈ C.source.planar.cell i := by
  exact (Finset.mem_filter.mp
    (C.cluster_subset_source i (C.representative_mem i))).2

theorem SeparatedPositiveFractionClusters.representative_injective
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) :
    Function.Injective C.representative := by
  intro i j hij
  by_contra hne
  have hdisj := C.strongConvex.pairwiseDisjoint hne
  exact Finset.disjoint_left.mp hdisj (C.representative_mem i)
    (hij ▸ C.representative_mem j)

/-- A convenient general-position consequence for an explicitly indexed
four-tuple. -/
theorem affineIndependent_fin_four_of_generalPosition
    {U : Finset (Point 3)} (hUcard : 4 ≤ U.card)
    (hgp : InGeneralPosition 3 U) (p : Fin 4 → Point 3)
    (hpU : ∀ i, p i ∈ U) (hpinj : Function.Injective p) :
    AffineIndependent ℝ p := by
  classical
  let A := Finset.univ.image p
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hpU i
  have hAcard : A.card ≤ 4 := by
    simpa [A] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := p)
  have hAind : AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) :=
    affineIndependent_of_subset_of_card_le_four hUcard hgp hAU hAcard
  let e : Fin 4 ↪ A :=
    ⟨fun i ↦ ⟨p i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩,
      fun i j hij ↦ hpinj (congrArg Subtype.val hij)⟩
  convert hAind.comp_embedding e using 1
  funext i
  rfl

theorem SeparatedPositiveFractionClusters.representative_four_independent
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X)
    (hXcard : 4 ≤ X.card) (hgp : InGeneralPosition 3 X)
    (i₀ i₁ i₂ i₃ : Fin k)
    (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) :
    AffineIndependent ℝ ![C.representative i₀, C.representative i₁,
      C.representative i₂, C.representative i₃] := by
  let f : Fin 4 → Fin k := ![i₀, i₁, i₂, i₃]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f] <;> omega
  have hkey : AffineIndependent ℝ (C.representative ∘ f) := by
    apply affineIndependent_fin_four_of_generalPosition hXcard hgp
    · intro i
      exact C.source.cell_subset (f i)
        (C.cluster_subset_source (f i) (C.representative_mem (f i)))
    · exact C.representative_injective.comp hfinj
  have hfun : (C.representative ∘ f) = ![C.representative i₀,
      C.representative i₁, C.representative i₂, C.representative i₃] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at hkey

/-! ## Reindexing a selected ordered subfamily -/

def reindexClusters {k m : ℕ} (X : Fin k → Finset (Point 3))
    (e : Fin m ↪ Fin k) : Fin m → Finset (Point 3) :=
  fun i ↦ X (e i)

theorem TwoSeparatedClusters.reindex {k m : ℕ}
    {X : Fin k → Finset (Point 3)} (hX : TwoSeparatedClusters X)
    (e : Fin m ↪ Fin k) : TwoSeparatedClusters (reindexClusters X e) := by
  intro i j i' j' hij hi'j' hpairs
  apply hX (e.injective.ne hij) (e.injective.ne hi'j')
  simpa using (Finset.disjoint_map e).mpr hpairs

theorem StrongConvexPositionClusters.reindex {k m : ℕ}
    {X : Fin k → Finset (Point 3)} (hX : StrongConvexPositionClusters X)
    (e : Fin m ↪ Fin k) :
    StrongConvexPositionClusters (reindexClusters X e) := by
  classical
  intro i
  apply (hX (e i)).mono_right
  apply convexHull_mono
  intro x hx
  simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hx ⊢
  obtain ⟨j, hj, hxj⟩ := hx
  refine ⟨e j, ?_, hxj⟩
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
  exact e.injective.ne hj

theorem IsProjectedConvexChain.reindex_univ {k m : ℕ}
    {x : Fin k → Point 3} (hchain : IsProjectedConvexChain x Finset.univ)
    (e : Fin m ↪o Fin k) :
    IsProjectedConvexChain (fun i ↦ x (e i)) Finset.univ := by
  intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
  exact hchain (e i₀) (Finset.mem_univ _) (e i₁) (Finset.mem_univ _)
    (e i₂) (Finset.mem_univ _) (e i₃) (Finset.mem_univ _)
    (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)

theorem UniformAboveBelowOn.reindex_orderEmbOfFin
    {k m : ℕ} {x : Fin k → Point 3} {H : Finset (Fin k)}
    (huniform : UniformAboveBelowOn x H) (hHcard : H.card = m) :
    UniformAboveBelowOn
      (fun i ↦ x (H.orderEmbOfFin hHcard i)) Finset.univ := by
  let e : Fin m ↪o Fin k := H.orderEmbOfFin hHcard
  rcases huniform with habove | hbelow
  · left
    intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
    exact habove (e i₀) (H.orderEmbOfFin_mem hHcard i₀)
      (e i₁) (H.orderEmbOfFin_mem hHcard i₁)
      (e i₂) (H.orderEmbOfFin_mem hHcard i₂)
      (e i₃) (H.orderEmbOfFin_mem hHcard i₃)
      (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)
  · right
    intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
    exact hbelow (e i₀) (H.orderEmbOfFin_mem hHcard i₀)
      (e i₁) (H.orderEmbOfFin_mem hHcard i₁)
      (e i₂) (H.orderEmbOfFin_mem hHcard i₂)
      (e i₃) (H.orderEmbOfFin_mem hHcard i₃)
      (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)

/-- The positive-fraction clusters after the four-uniform Ramsey selection,
reindexed in their inherited order. -/
structure UniformSeparatedClusters
    (k m : ℕ) (X : Finset (Point 3)) where
  cluster : Fin m → Finset (Point 3)
  representative : Fin m → Point 3
  cluster_subset : ∀ i, cluster i ⊆ X
  representative_mem : IsClusterTransversal cluster representative
  nonempty : ∀ i, (cluster i).Nonempty
  twoSeparated : TwoSeparatedClusters cluster
  strongConvex : StrongConvexPositionClusters cluster
  density : ∀ i,
    X.card ≤ 2 ^ (40 * k + k ^ 3) * (cluster i).card
  projectedChain : IsProjectedConvexChain representative Finset.univ
  uniformAboveBelow : UniformAboveBelowOn representative Finset.univ

/-- Select and order a uniform above/below subfamily.  The density exponent
is kept as the original positive-fraction parameter `k`; the later assembly
will instantiate `k = pzQuarterRoot n`. -/
def SeparatedPositiveFractionClusters.selectUniform
    {k m : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X)
    (H : Finset (Fin k)) (hHcard : H.card = m)
    (hchain : IsProjectedConvexChain C.representative Finset.univ)
    (huniform : UniformAboveBelowOn C.representative H) :
    UniformSeparatedClusters k m X where
  cluster := reindexClusters C.cluster (H.orderEmbOfFin hHcard).toEmbedding
  representative := fun i ↦ C.representative (H.orderEmbOfFin hHcard i)
  cluster_subset := fun _ ↦
    (C.cluster_subset_source _).trans (C.source.cell_subset _)
  representative_mem := fun _ ↦ C.representative_mem _
  nonempty := fun _ ↦ C.nonempty _
  twoSeparated := C.twoSeparated.reindex _
  strongConvex := C.strongConvex.reindex _
  density := fun i ↦ C.density (H.orderEmbOfFin hHcard i)
  projectedChain := hchain.reindex_univ (H.orderEmbOfFin hHcard)
  uniformAboveBelow := huniform.reindex_orderEmbOfFin hHcard

def finCastSuccOrderEmb (k : ℕ) : Fin k ↪o Fin (k + 1) where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective k
  map_rel_iff' := by simp

def extendFinPoint {k : ℕ} (x : Fin k → Point 3) : Fin (k + 1) → Point 3 :=
  fun i ↦ if hi : i.1 < k then x ⟨i.1, hi⟩ else 0

@[simp] theorem extendFinPoint_castSucc {k : ℕ} (x : Fin k → Point 3)
    (i : Fin k) : extendFinPoint x (Fin.castSucc i) = x i := by
  simp [extendFinPoint]

/-- Corollary 2.4 in the exact half-open convention used by Proposition
3.1.  Passing from `Fin k` to `Fin (k+1)` supplies the cut immediately after
`j₃`, including when `j₃` is the final index. -/
theorem trihedral_representative_hulls_disjoint
    {k : ℕ} (x : Fin k → Point 3) (hcard : 5 ≤ k)
    (hchain : IsProjectedConvexChain x Finset.univ)
    (huniform : UniformAboveBelowOn x Finset.univ)
    (j₁ j₂ j₃ : Fin k) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Disjoint
      (convexHull ℝ
        ((firstTrihedralIndices j₁ j₂ j₃).image x : Set (Point 3)))
      (convexHull ℝ
        (((secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x) :
          Set (Point 3))) ∧
    Disjoint
      (convexHull ℝ
        (((firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x) :
          Set (Point 3)))
      (convexHull ℝ
        ((secondTrihedralIndices j₁ j₂ j₃).image x : Set (Point 3))) := by
  classical
  let e : Fin k ↪o Fin (k + 1) := finCastSuccOrderEmb k
  let S : Finset (Fin (k + 1)) := Finset.univ.map e.toEmbedding
  let x' : Fin (k + 1) → Point 3 := extendFinPoint x
  have hx' (i : Fin k) : x' (e i) = x i := by
    simp [x', e, finCastSuccOrderEmb]
  have hScard : S.card = k := by simp [S]
  have hchain' : IsProjectedConvexChain x' S := by
    intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
    obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
    obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
    obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
    obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
    simpa only [RelEmbedding.coe_toEmbedding, hx'] using
      hchain q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
      q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
      (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
  have huniform' : UniformAboveBelowOn x' S := by
    rcases huniform with habove | hbelow
    · left
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
      obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
      obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
      obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
      obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
      simpa only [RelEmbedding.coe_toEmbedding, hx'] using
        habove q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
        q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
        (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
    · right
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
      obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
      obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
      obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
      obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
      simpa only [RelEmbedding.coe_toEmbedding, hx'] using
        hbelow q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
        q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
        (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
  have he (i : Fin k) : e i = Fin.castSucc i := rfl
  have blockImage (T : Finset (Fin (k + 1))) (R : Finset (Fin k))
      (hTS : T ⊆ S) (hR : ∀ i : Fin k, e i ∈ T ↔ i ∈ R) :
      T.image x' = R.image x := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, haT, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hTS haT)
      exact Finset.mem_image.2 ⟨i, (hR i).mp haT, (hx' i).symm⟩
    · intro hy
      obtain ⟨i, hiR, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.2 ⟨e i, (hR i).mpr hiR, hx' i⟩
  have hmemS (i : Fin k) : (Fin.castSucc i : Fin (k + 1)) ∈ S :=
    Finset.mem_map_of_mem _ (Finset.mem_univ i)
  have hfirst₁ :
      (firstAlternatingBlock S (e j₁) (Fin.succ j₂) (Fin.succ j₃)).image x' =
        (firstTrihedralIndices j₁ j₂ j₃).image x := by
    refine blockImage _ _ (Finset.filter_subset _ _) ?_
    intro i
    simp only [firstAlternatingBlock, Finset.mem_filter, he, hmemS, true_and,
      mem_firstTrihedralIndices, Fin.lt_def, Fin.le_def, Fin.val_castSucc,
      Fin.val_succ]
    omega
  have hsecond₁ :
      (secondAlternatingBlock S (e j₁) (Fin.succ j₂) (Fin.succ j₃)).image x' =
        (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x := by
    refine blockImage _ _ (Finset.filter_subset _ _) ?_
    intro i
    simp only [secondAlternatingBlock, Finset.mem_filter, he, hmemS, true_and,
      Finset.mem_union, mem_secondTrihedralIndices, Finset.mem_singleton,
      Fin.lt_def, Fin.le_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have hfirst₂ :
      (firstAlternatingBlock S (e j₁) (e j₂) (Fin.succ j₃)).image x' =
        (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x := by
    refine blockImage _ _ (Finset.filter_subset _ _) ?_
    intro i
    simp only [firstAlternatingBlock, Finset.mem_filter, he, hmemS, true_and,
      Finset.mem_union, mem_firstTrihedralIndices, Finset.mem_singleton,
      Fin.lt_def, Fin.le_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have hsecond₂ :
      (secondAlternatingBlock S (e j₁) (e j₂) (Fin.succ j₃)).image x' =
        (secondTrihedralIndices j₁ j₂ j₃).image x := by
    refine blockImage _ _ (Finset.filter_subset _ _) ?_
    intro i
    simp only [secondAlternatingBlock, Finset.mem_filter, he, hmemS, true_and,
      mem_secondTrihedralIndices, Fin.lt_def, Fin.le_def, Fin.val_castSucc,
      Fin.val_succ]
    omega
  have hval₁₂ : (j₁ : Fin k).1 < (j₂ : Fin k).1 := Fin.lt_def.mp h₁₂
  have hval₂₃ : (j₂ : Fin k).1 < (j₃ : Fin k).1 := Fin.lt_def.mp h₂₃
  have hle₁ : (e j₁ : Fin (k + 1)) ≤ Fin.succ j₂ := by
    simp only [Fin.le_def, he, Fin.val_castSucc, Fin.val_succ]
    omega
  have hle₂ : (Fin.succ j₂ : Fin (k + 1)) ≤ Fin.succ j₃ := by
    simp only [Fin.le_def, Fin.val_succ]
    omega
  have hle₃ : (e j₁ : Fin (k + 1)) ≤ e j₂ := by
    simp only [Fin.le_def, he, Fin.val_castSucc]
    omega
  have hle₄ : (e j₂ : Fin (k + 1)) ≤ Fin.succ j₃ := by
    simp only [Fin.le_def, he, Fin.val_castSucc, Fin.val_succ]
    omega
  constructor
  · have h := alternatingBlock_hulls_disjoint x' S (e j₁) (Fin.succ j₂)
      (Fin.succ j₃) (by simpa only [hScard] using hcard) hle₁ hle₂
      hchain' huniform'
    simpa only [hfirst₁, hsecond₁] using h
  · have h := alternatingBlock_hulls_disjoint x' S (e j₁) (e j₂)
      (Fin.succ j₃) (by simpa only [hScard] using hcard) hle₃ hle₄
      hchain' huniform'
    simpa only [hfirst₂, hsecond₂] using h
/-- Proposition 2.7 turns a strict separation of representative blocks into
the same separation for the unions of their full clusters. -/
theorem UniformSeparatedClusters.fullCluster_hulls_disjoint
    {k m : ℕ} {X : Finset (Point 3)}
    (C : UniformSeparatedClusters k m X)
    (A B : Finset (Fin m)) (hAB : A ∪ B = Finset.univ)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hrep : Disjoint
      (convexHull ℝ (A.image C.representative : Set (Point 3)))
      (convexHull ℝ (B.image C.representative : Set (Point 3)))) :
    Disjoint
      (convexHull ℝ (clusterUnion C.cluster A : Set (Point 3)))
      (convexHull ℝ (clusterUnion C.cluster B : Set (Point 3))) := by
  classical
  obtain ⟨f, c, hAneg, hBpos⟩ :=
    finite_sets_strictly_separated_point3
      (A.image C.representative) (B.image C.representative) hrep
  have hf : f ≠ 0 := by
    intro hf
    obtain ⟨i, hiA⟩ := hAne
    obtain ⟨j, hjB⟩ := hBne
    have hi := hAneg (C.representative i)
      (Finset.mem_image_of_mem C.representative hiA)
    have hj := hBpos (C.representative j)
      (Finset.mem_image_of_mem C.representative hjB)
    simp only [hf, _root_.zero_apply] at hi hj
    linarith
  have hpattern : HasRepresentativePlanePattern C.representative f c := by
    refine ⟨hf, ?_⟩
    intro i
    have hi : i ∈ A ∪ B := by rw [hAB]; simp
    rcases Finset.mem_union.mp hi with hiA | hiB
    · have hlt := hAneg (C.representative i)
        (Finset.mem_image_of_mem C.representative hiA)
      dsimp [planeValue]
      linarith
    · have hgt := hBpos (C.representative i)
        (Finset.mem_image_of_mem C.representative hiB)
      dsimp [planeValue]
      linarith
  obtain ⟨g, d, hg, hlift⟩ :=
    liftsRepresentativePlanePattern_of_twoSeparated_of_strong
      C.twoSeparated C.strongConvex C.representative_mem hpattern
  have hAgen : (↑(clusterUnion C.cluster A) : Set (Point 3)) ⊆
      {y | g y < d} := by
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hy
    obtain ⟨i, hiA, hyi⟩ := hy
    have hirep := hAneg (C.representative i)
      (Finset.mem_image_of_mem C.representative hiA)
    have := (hlift i y hyi).2 (by
      dsimp [planeValue]
      linarith)
    simpa [planeValue] using this
  have hBgen : (↑(clusterUnion C.cluster B) : Set (Point 3)) ⊆
      {y | d < g y} := by
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hy
    obtain ⟨i, hiB, hyi⟩ := hy
    have hirep := hBpos (C.representative i)
      (Finset.mem_image_of_mem C.representative hiB)
    have := (hlift i y hyi).1 (by
      dsimp [planeValue]
      linarith)
    simpa [planeValue] using this
  rw [Set.disjoint_left]
  intro y hyA hyB
  have hyneg : g y < d :=
    convexHull_min hAgen (convex_halfSpace_lt g.isLinear d) hyA
  have hypos : d < g y :=
    convexHull_min hBgen (convex_halfSpace_gt g.isLinear d) hyB
  linarith

/-! ## Aligning a generic projection with the vertical coordinates -/

/-- The evident coordinate identification `(ℝ² × ℝ) ≃ₗ ℝ³`. -/
def pointTwoProdRealEquivPointThree :
    (Point 2 × ℝ) ≃ₗ[ℝ] Point 3 where
  toFun yz := WithLp.toLp 2 ![yz.1 0, yz.1 1, yz.2]
  invFun x := (WithLp.toLp 2 ![x 0, x 1], x 2)
  left_inv yz := by
    rcases yz with ⟨y, z⟩
    apply Prod.ext
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp
    · simp
  right_inv x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp

/-- Every surjective affine projection to the plane can be completed by one
linear coordinate to an affine coordinate system on `ℝ³`.  After this
change of coordinates it is literally `verticalProjection`, so all the
hard-coded above/below lemmas apply without changing their geometry. -/
theorem exists_affineEquiv_verticalProjection_eq_of_surjective
    (π : Point 3 →ᵃ[ℝ] Point 2) (hπ : Function.Surjective π.linear) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      ∀ x, verticalProjection (e x) = π x := by
  classical
  let L : Point 3 →ₗ[ℝ] Point 2 := π.linear
  obtain ⟨g, hg⟩ :=
    L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hg' : Function.RightInverse g L := LinearMap.ext_iff.mp hg
  have hkerfin : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    have hrank := L.finrank_range_add_finrank_ker
    have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hπ
    rw [hrange] at hrank
    have hdom : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
    have hcod : Module.finrank ℝ (Point 2) = 2 := by simp [Point]
    rw [finrank_top, hcod, hdom] at hrank
    omega
  let eK : LinearMap.ker L ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq _ _ (by
    rw [hkerfin]
    simp)
  have hPker : ∀ x : Point 3,
      ((LinearMap.id : Point 3 →ₗ[ℝ] Point 3) - g.comp L) x ∈
        LinearMap.ker L := by
    intro x
    have hx : ((LinearMap.id : Point 3 →ₗ[ℝ] Point 3) - g.comp L) x =
        x - g (L x) := rfl
    rw [LinearMap.mem_ker, hx, map_sub, hg' (L x), sub_self]
  let Pk : Point 3 →ₗ[ℝ] LinearMap.ker L :=
    ((LinearMap.id : Point 3 →ₗ[ℝ] Point 3) - g.comp L).codRestrict _ hPker
  have hPkval : ∀ x : Point 3, ((Pk x : LinearMap.ker L) : Point 3) =
      x - g (L x) := fun _ ↦ rfl
  let D : Point 3 ≃ₗ[ℝ] (Point 2 × ℝ) :=
    { toFun := fun x ↦ (L x, eK (Pk x))
      invFun := fun yz ↦ g yz.1 + ((eK.symm yz.2 : LinearMap.ker L) : Point 3)
      left_inv := by
        intro x
        simp only [eK.symm_apply_apply, hPkval]
        abel
      right_inv := by
        intro yz
        have hv : L ((eK.symm yz.2 : LinearMap.ker L) : Point 3) = 0 :=
          LinearMap.map_coe_ker L _
        have hfst : L (g yz.1 + ((eK.symm yz.2 : LinearMap.ker L) : Point 3)) =
            yz.1 := by
          rw [map_add, hg' yz.1, hv, add_zero]
        have hsnd :
            Pk (g yz.1 + ((eK.symm yz.2 : LinearMap.ker L) : Point 3)) =
              eK.symm yz.2 := by
          apply Subtype.ext
          rw [hPkval, hfst]
          abel
        rw [Prod.ext_iff]
        exact ⟨hfst, by simp only [hsnd, eK.apply_symm_apply]⟩
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  let E : Point 3 ≃ₗ[ℝ] Point 3 :=
    D.trans pointTwoProdRealEquivPointThree
  let shift : Point 3 := pointTwoProdRealEquivPointThree (π 0, 0)
  let e : Point 3 ≃ᵃ[ℝ] Point 3 :=
    E.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Point 3) shift)
  refine ⟨e, ?_⟩
  intro x
  apply PiLp.ext
  intro i
  have hlinear := congrArg (fun y : Point 2 ↦ y i)
    (π.linearMap_vsub x 0)
  fin_cases i
  · simp [e, E, shift, D, L, verticalProjection,
      pointTwoProdRealEquivPointThree, vsub_eq_sub] at hlinear ⊢
    linarith
  · simp [e, E, shift, D, L, verticalProjection,
      pointTwoProdRealEquivPointThree, vsub_eq_sub] at hlinear ⊢
    linarith

/-- Three noncollinear values force the linear part of a planar affine map
to be onto. -/
theorem affineProjection_linear_surjective_of_image_generalPosition
    {X : Finset (Point 3)} (π : Point 3 →ᵃ[ℝ] Point 2)
    (hπinj : Set.InjOn π X) (hXcard : 3 ≤ X.card)
    (hgp : InGeneralPosition 2 (X.image π)) :
    Function.Surjective π.linear := by
  classical
  have himagecard : (X.image π).card = X.card :=
    Finset.card_image_of_injOn hπinj
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ (X.image π).card by
      simpa [himagecard] using hXcard)
  have hAI : AffineIndependent ℝ (fun y : T ↦ (y : Point 2)) := by
    apply hgp T hTsub
    simpa using hTcard
  have hspan :
      vectorSpan ℝ (Set.range fun y : T ↦ (y : Point 2)) = ⊤ := by
    apply hAI.vectorSpan_eq_top_of_card_eq_finrank_add_one
    simp [Point, hTcard]
  have hTne : T.Nonempty := by rw [← Finset.card_pos, hTcard]; norm_num
  let a : T := ⟨Exists.choose hTne, Exists.choose_spec hTne⟩
  have hle : vectorSpan ℝ (Set.range fun y : T ↦ (y : Point 2)) ≤
      LinearMap.range π.linear := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self a),
      Submodule.span_le]
    rintro v ⟨_, ⟨b, rfl⟩, rfl⟩
    have hbimage := hTsub b.property
    have haimage := hTsub a.property
    obtain ⟨xb, hxbX, hxbeq⟩ := Finset.mem_image.mp hbimage
    obtain ⟨xa, hxaX, hxaeq⟩ := Finset.mem_image.mp haimage
    refine ⟨xb - xa, ?_⟩
    have hv := π.linearMap_vsub xb xa
    simpa [vsub_eq_sub, hxbeq, hxaeq] using hv
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  exact hle

theorem inGeneralPosition_image_affineEquiv
    {d : ℕ} {X : Finset (Point d)} (hX : InGeneralPosition d X)
    (e : Point d ≃ᵃ[ℝ] Point d) :
    InGeneralPosition d (X.image e) := by
  apply InGeneralPosition.of_image_affineMap e.symm.toAffineMap
    e.symm.injective.injOn
  have hback : (X.image e).image (e.symm.toAffineMap : Point d → Point d) =
      X := by
    ext x
    simp
  rw [hback]
  exact hX

/-- Generic projection in the coordinate form needed by `AboveBelow`.
The affine equivalence is returned explicitly so the eventual convex subset
can be transported back to the original point set. -/
theorem exists_vertical_generic_affineEquiv
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hXcard : 4 ≤ X.card) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      InGeneralPosition 3 (X.image e) ∧
      Set.InjOn verticalProjection (X.image e) ∧
      InGeneralPosition 2 ((X.image e).image verticalProjection) := by
  obtain ⟨π, hπinj, hπgp⟩ := exists_generic_plane_projection hgp hXcard
  have hπsurj : Function.Surjective π.linear :=
    affineProjection_linear_surjective_of_image_generalPosition π hπinj
      (by omega) hπgp
  obtain ⟨e, he⟩ :=
    exists_affineEquiv_verticalProjection_eq_of_surjective π hπsurj
  have himage : (X.image e).image verticalProjection = X.image π := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hxX, rfl⟩, rfl⟩
      exact ⟨x, hxX, (he x).symm⟩
    · rintro ⟨x, hxX, rfl⟩
      exact ⟨e x, ⟨x, hxX, rfl⟩, he x⟩
  refine ⟨e, inGeneralPosition_image_affineEquiv hgp e, ?_, ?_⟩

  · intro ex hex ey hey hxy
    obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.mp hex
    obtain ⟨y, hyX, rfl⟩ := Finset.mem_image.mp hey
    apply congrArg e
    exact hπinj hxX hyX (by simpa only [he] using hxy)
  · simpa only [himage] using hπgp

/-! ## The exact rounding used for the alternating cap union -/

/-- There are `ceil(t/2)` alternating indices, and caps of cardinality
`ceil(2n/t)` therefore contribute at least `n` points. -/
theorem target_le_alternating_cap_count (n t : ℕ) (ht : 0 < t) :
    n ≤ ((t + 1) / 2) * ⌈(2 : ℝ) * n / t⌉₊ := by
  let a : ℕ := ⌈(2 : ℝ) * n / t⌉₊
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hdiv : (2 : ℝ) * n / t ≤ (a : ℝ) := by
    exact Nat.le_ceil _
  have hmulR : (2 : ℝ) * n ≤ t * a := by
    simpa [mul_comm] using (div_le_iff₀ htR).mp hdiv
  have hmul : 2 * n ≤ t * a := by exact_mod_cast hmulR
  have htceil : t ≤ 2 * ((t + 1) / 2) := by omega
  have htwice : 2 * n ≤ 2 * (((t + 1) / 2) * a) := by
    calc
      2 * n ≤ t * a := hmul
      _ ≤ (2 * ((t + 1) / 2)) * a := Nat.mul_le_mul_right a htceil
      _ = 2 * (((t + 1) / 2) * a) := by ac_rfl
  change n ≤ ((t + 1) / 2) * a
  exact Nat.le_of_mul_le_mul_left htwice (by norm_num)

/-! ## Elementary binomial estimates -/

/-- The rounded cups--caps coefficient is dominated by the cleaner
`choose (n+a) a` coefficient used in `BinomialEnvelope`. -/
theorem choose_cap_threshold_le_choose_add (n a : ℕ) (ha : 2 ≤ a) :
    Nat.choose (a + n - 4) (a - 2) ≤ Nat.choose (n + a) a := by
  let N := a + n - 4
  let b := a - 2
  have hstep₁ : Nat.choose N b ≤ Nat.choose (N + 1) (b + 1) := by
    rw [Nat.choose_succ_succ']
    omega
  have hstep₂ : Nat.choose (N + 1) (b + 1) ≤
      Nat.choose (N + 2) (b + 2) := by
    have hsplit : Nat.choose (N + 2) (b + 2) =
        Nat.choose (N + 1) (b + 1) + Nat.choose (N + 1) (b + 2) :=
      Nat.choose_succ_succ' (N + 1) (b + 1)
    omega
  calc
    Nat.choose (a + n - 4) (a - 2) = Nat.choose N b := rfl
    _ ≤ Nat.choose (N + 1) (b + 1) := hstep₁
    _ ≤ Nat.choose (N + 2) (b + 2) := hstep₂
    _ = Nat.choose (N + 2) a := by
      congr 1
      omega
    _ ≤ Nat.choose (n + a) a := by
      apply Nat.choose_le_choose
      dsimp [N]
      omega

/-- The sixth power of the exact coefficient appearing in Proposition 2.1
is bounded by the explicit binomial envelope. -/
theorem choose_cap_threshold_pow_six_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n)
    (ha : 2 ≤ pzCapSize n t) :
    ((Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6 ≤
      (t : ℝ) ^ ((36 : ℝ) * n / t) := by
  have hchoose := choose_cap_threshold_le_choose_add n (pzCapSize n t) ha
  calc
    ((Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6
        ≤ ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6 := by
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hchoose) 6
    _ ≤ (t : ℝ) ^ ((36 : ℝ) * n / t) :=
      choose_add_pzCapSize_pow_six_le_envelope n t hn ht htn

/-! ## A concrete unbounded Ramsey-clique scale -/

/-- The largest clique size whose explicit `r`-uniform Ramsey bound fits
below `k`.  The `m = 0` disjunct makes the defining finite set nonempty. -/
def pzRamseyCliqueSizeFor (r k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).filter fun m =>
    m = 0 ∨ uniformRamseySequence r m ≤ k).sup id

/-- The inverse triple-Ramsey scale. -/
def pzRamseyCliqueSize (k : ℕ) : ℕ :=
  pzRamseyCliqueSizeFor 3 k

theorem pzRamseyCliqueSizeFor_le (r k : ℕ) :
    pzRamseyCliqueSizeFor r k ≤ k := by
  apply Finset.sup_le
  intro m hm
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

theorem pzRamseyCliqueSize_le (k : ℕ) : pzRamseyCliqueSize k ≤ k :=
  pzRamseyCliqueSizeFor_le 3 k

/-- A positive value of the inverse scale genuinely satisfies the explicit
Ramsey threshold (rather than coming from the adjoined zero). -/
theorem uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos
    {r k : ℕ} (hk : 0 < pzRamseyCliqueSizeFor r k) :
    uniformRamseySequence r (pzRamseyCliqueSizeFor r k) ≤ k := by
  let S := (Finset.range (k + 1)).filter fun m =>
    m = 0 ∨ uniformRamseySequence r m ≤ k
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  obtain ⟨m, hmS, hm⟩ := Finset.sup_mem_of_nonempty (f := id) hS
  have heq : m = pzRamseyCliqueSizeFor r k := by
    simpa [S, pzRamseyCliqueSizeFor] using hm
  have hmprop := (Finset.mem_filter.mp hmS).2
  rcases hmprop with rfl | hmle
  · rw [← heq] at hk
    exact absurd hk (lt_irrefl 0)
  · simpa only [heq] using hmle

theorem uniformRamseySequence_le_of_pzRamseyCliqueSize_pos
    {k : ℕ} (hk : 0 < pzRamseyCliqueSize k) :
    uniformRamseySequence 3 (pzRamseyCliqueSize k) ≤ k :=
  uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos hk

/-- Every fixed clique size is eventually admitted by the inverse Ramsey
scale. -/
theorem eventually_le_pzRamseyCliqueSizeFor (r m : ℕ) :
    ∀ᶠ k : ℕ in atTop, m ≤ pzRamseyCliqueSizeFor r k := by
  filter_upwards [eventually_ge_atTop (max m (uniformRamseySequence r m))]
    with k hk
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((le_max_left _ _).trans hk),
    Or.inr ((le_max_right _ _).trans hk)⟩

/-- The inverse triple-Ramsey scale tends to infinity. -/
theorem pzRamseyCliqueSizeFor_tendsto_atTop (r : ℕ) :
    Tendsto (pzRamseyCliqueSizeFor r) atTop atTop := by
  rw [tendsto_atTop]
  exact eventually_le_pzRamseyCliqueSizeFor r

theorem pzRamseyCliqueSize_tendsto_atTop :
    Tendsto pzRamseyCliqueSize atTop atTop :=
  pzRamseyCliqueSizeFor_tendsto_atTop 3

/-- The size retained after the four-uniform above/below Ramsey step. -/
def pzAboveBelowScale (n : ℕ) : ℕ :=
  pzRamseyCliqueSizeFor 4 (pzQuarterRoot n)

theorem pzAboveBelowScale_tendsto_atTop :
    Tendsto pzAboveBelowScale atTop atTop :=
  (pzRamseyCliqueSizeFor_tendsto_atTop 4).comp pzQuarterRoot_tendsto_atTop

theorem pzAboveBelowScale_le_quarterRoot (n : ℕ) :
    pzAboveBelowScale n ≤ pzQuarterRoot n :=
  pzRamseyCliqueSizeFor_le 4 _

/-- The size of the clique retained after the final triple-Ramsey step. -/
def pzSourceCliqueSize (n : ℕ) : ℕ :=
  pzRamseyCliqueSize (pzAboveBelowScale n)

theorem pzSourceCliqueSize_tendsto_atTop :
    Tendsto pzSourceCliqueSize atTop atTop :=
  pzRamseyCliqueSize_tendsto_atTop.comp pzAboveBelowScale_tendsto_atTop

/-- The slowly growing scale used in the source envelope.  If the final
triple-Ramsey clique has size `m`, we retain its largest odd initial segment
`2q+1` and put `t=2q`.  Thus there are exactly
`q = (t+1)/2` alternating middle clusters, with no parity loss in the cap
count. -/
def pzSourceScale (n : ℕ) : ℕ :=
  2 * ((pzSourceCliqueSize n - 1) / 2)

theorem pzSourceScale_tendsto_atTop :
    Tendsto pzSourceScale atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [pzSourceCliqueSize_tendsto_atTop.eventually_ge_atTop (b + 2)]
    with n hn
  dsimp [pzSourceScale]
  omega

theorem pzSourceScale_add_one_le_cliqueSize (n : ℕ)
    (h : 0 < pzSourceCliqueSize n) :
    pzSourceScale n + 1 ≤ pzSourceCliqueSize n := by
  dsimp [pzSourceScale]
  omega

theorem pzSourceScale_even (n : ℕ) : Even (pzSourceScale n) := by
  exact ⟨(pzSourceCliqueSize n - 1) / 2, by
    simp only [pzSourceScale]
    omega⟩

theorem pzSourceScale_le_quarterRoot (n : ℕ) :
    pzSourceScale n ≤ pzQuarterRoot n := by
  have hle : pzSourceScale n ≤ pzSourceCliqueSize n := by
    dsimp [pzSourceScale]
    omega
  exact hle.trans
    ((pzRamseyCliqueSize_le _).trans (pzAboveBelowScale_le_quarterRoot n))

/-- The integer fourth root has fourth power at most its argument. -/
theorem pzQuarterRoot_pow_four_le (n : ℕ) :
    pzQuarterRoot n ^ 4 ≤ n := by
  have hfloor : (pzQuarterRoot n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hpow : (pzQuarterRoot n : ℝ) ^ 4 ≤
      ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hfloor 4
  have hrpow : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (n : ℝ) := by
    convert Real.rpow_inv_natCast_pow (x := (n : ℝ)) (n := 4)
      (by positivity) (by norm_num) using 1
    norm_num
  exact_mod_cast hpow.trans_eq hrpow

/-- The positive-fraction and repeated-halving loss is absorbed by a
`t^(41 n/t)` factor.  This is the exact elementary comparison used in the
source: `t ≤ k₀`, `k₀⁴ ≤ n`, and eventually `2 ≤ t`. -/
theorem positiveFractionLoss_le_sourceEnvelope
    (n : ℕ) (ht : 2 ≤ pzSourceScale n) :
    ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^
        ((41 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) := by
  let k := pzQuarterRoot n
  let t := pzSourceScale n
  have ht0 : 0 < t := by omega
  have htk : t ≤ k := pzSourceScale_le_quarterRoot n
  have hk0 : 0 < k := lt_of_lt_of_le (by omega) htk
  have hk4 : k ^ 4 ≤ n := pzQuarterRoot_pow_four_le n
  have htk3 : k ^ 3 * t ≤ n := by
    calc
      k ^ 3 * t ≤ k ^ 3 * k := Nat.mul_le_mul_left _ htk
      _ = k ^ 4 := by ring
      _ ≤ n := hk4
  have hk_le_k3 : k ≤ k ^ 3 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ k by omega)
      (show 1 ≤ 3 by omega)
  have hbasepow :
      (2 ^ (40 * k + k ^ 3) : ℕ) ≤ t ^ (40 * k + k ^ 3) :=
    Nat.pow_le_pow_left ht _
  have hexpR : ((40 * k + k ^ 3 : ℕ) : ℝ) ≤
      (41 : ℝ) * (n : ℝ) / (t : ℝ) := by
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    have hk3R : (k : ℝ) ^ 3 ≤ (n : ℝ) / (t : ℝ) := by
      rw [le_div_iff₀ htR]
      exact_mod_cast htk3
    have hkR : (k : ℝ) ≤ (k : ℝ) ^ 3 := by exact_mod_cast hk_le_k3
    rw [mul_div_assoc]
    push_cast
    linarith
  calc
    ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ)
        = ((2 ^ (40 * k + k ^ 3) : ℕ) : ℝ) := rfl
    _ ≤ ((t ^ (40 * k + k ^ 3) : ℕ) : ℝ) := by exact_mod_cast hbasepow
    _ = (t : ℝ) ^ ((40 * k + k ^ 3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_cast
    _ ≤ (t : ℝ) ^ ((41 : ℝ) * (n : ℝ) / (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ t by omega)) hexpR

theorem two_le_pzCapSize {n t : ℕ} (ht : 0 < t) (htn : t ≤ n) :
    2 ≤ pzCapSize n t := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htwo : (2 : ℝ) ≤ (2 : ℝ) * n / t := by
    rw [le_div_iff₀ htR]
    exact_mod_cast Nat.mul_le_mul_left 2 htn
  exact_mod_cast htwo.trans (pzCapSize_lower (n := n) ht)

/-- After the positive-fraction and `2`-separation losses and the two
square-root losses, the exact cap threshold is still bounded by a PZ
envelope.  The explicit constant is `41 + 36 = 77`. -/
theorem loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope
    (n : ℕ) (hn : 0 < n) (ht : 3 ≤ pzSourceScale n)
    (htn : pzSourceScale n ≤ n) :
    (((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)) *
        Nat.choose
          (pzCapSize n (pzSourceScale n) + n - 4)
          (pzCapSize n (pzSourceScale n) - 2) ^ 6 : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^
        ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) := by
  let t := pzSourceScale n
  have ht0 : 0 < t := by omega
  have hcap : 2 ≤ pzCapSize n t := two_le_pzCapSize ht0 htn
  have hloss := positiveFractionLoss_le_sourceEnvelope n (show 2 ≤ t by omega)
  have hchoose := choose_cap_threshold_pow_six_le_envelope n t hn ht htn hcap
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  calc
    (((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)) *
        Nat.choose (pzCapSize n (pzSourceScale n) + n - 4)
          (pzCapSize n (pzSourceScale n) - 2) ^ 6 : ℕ) : ℝ)
        = ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) *
          ((Nat.choose (pzCapSize n t + n - 4)
            (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6 := by
              simp only [t, Nat.cast_mul, Nat.cast_pow]
    _ ≤ t ^ ((41 : ℝ) * (n : ℝ) / t) *
          t ^ ((36 : ℝ) * (n : ℝ) / t) :=
      mul_le_mul hloss hchoose (by positivity) (by positivity)
    _ = t ^ ((77 : ℝ) * (n : ℝ) / t) := by
      rw [← Real.rpow_add htR]
      congr 1
      ring

/-! ## Eliminating the two square-root losses exactly -/

/-- Once the geometric construction has produced its alternating free
family, the density bound and the exact quadratic Dilworth bound turn the
strict source threshold into caps (or a direct convex set). -/
theorem AlternatingFreeFamily.containsConvexSubset_of_sourceThreshold
    {n t : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily ((t + 1) / 2) X)
    (hn : 2 ≤ n) (ht : 3 ≤ t) (htn : t ≤ n)
    (hdensity : ∀ i,
      X.card ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
        (F.middle i).card)
    (hthreshold :
      2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
          Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) ^ 6 <
        X.card) :
    ContainsConvexSubset 3 n X := by
  let a := pzCapSize n t
  let loss := 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)
  let B := Nat.choose (a + n - 4) (a - 2) ^ 3
  have ht0 : 0 < t := by omega
  have ha : 2 ≤ a := by
    exact two_le_pzCapSize ht0 htn
  apply F.containsConvexSubset ha hn (by
    simpa [a, pzCapSize] using target_le_alternating_cap_count n t ht0)
  intro i
  have hloss : 0 < loss := by simp [loss]
  have hthreshold' : loss * (B * B) < X.card := by
    have hpow : B * B =
        Nat.choose (a + n - 4) (a - 2) ^ 6 := by
      dsimp [B]
      rw [← pow_add]
    rw [hpow]
    simpa [loss, a] using hthreshold
  have hBBmiddle : B * B < (F.middle i).card := by
    apply Nat.lt_of_mul_lt_mul_left
    calc
      loss * (B * B) < X.card := hthreshold'
      _ ≤ loss * (F.middle i).card := by simpa [loss] using hdensity i
  by_contra hnot
  have hfreeB : (F.freeSet i).card ≤ B := Nat.le_of_not_gt hnot
  have hmiddleBB : (F.middle i).card ≤ B * B :=
    (F.middle_card_le_free_square i).trans
      (Nat.mul_le_mul hfreeB hfreeB)
  exact (Nat.not_lt_of_ge hmiddleBB) hBBmiddle

theorem AlternatingFreeFamily.containsConvexSubset_of_sourceEnvelope
    {n : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily ((pzSourceScale n + 1) / 2) X)
    (hn : 2 ≤ n) (ht : 3 ≤ pzSourceScale n)
    (htn : pzSourceScale n ≤ n)
    (hdensity : ∀ i,
      X.card ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
        (F.middle i).card)
    (hlarge :
      (pzSourceScale n : ℝ) ^
          ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) <
        (X.card : ℝ)) :
    ContainsConvexSubset 3 n X := by
  have hbound := loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope
    n (by omega) ht htn
  have hthreshold :
      2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
          Nat.choose
            (pzCapSize n (pzSourceScale n) + n - 4)
            (pzCapSize n (pzSourceScale n) - 2) ^ 6 < X.card := by
    exact_mod_cast hbound.trans_lt hlarge
  exact F.containsConvexSubset_of_sourceThreshold hn ht htn hdensity hthreshold

theorem eventually_uniformRamseySequence_aboveBelowScale_le_quarterRoot :
    ∀ᶠ n : ℕ in atTop,
      uniformRamseySequence 4 (pzAboveBelowScale n) ≤ pzQuarterRoot n := by
  filter_upwards [pzAboveBelowScale_tendsto_atTop.eventually_gt_atTop 0]
    with n hn
  exact uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos hn

/-- Triple Ramsey selection at the exact slowly growing source scale.  The
returned clique has the odd cardinality `t+1`; consequently its alternating
middle indices are indexed by `Fin ((t+1)/2)`. -/
theorem pzSourceScale_tripleRamsey
    {α : Type*} [DecidableEq α] (n : ℕ) (A : Finset α)
    (hscale : 0 < pzSourceScale n)
    (hcard : pzAboveBelowScale n ≤ A.card)
    (color : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ A ∧ H.card = pzSourceScale n + 1 ∧
      MonochromaticOn 3 color H := by
  have hclique : 0 < pzSourceCliqueSize n := by
    rcases Nat.eq_zero_or_pos (pzSourceCliqueSize n) with hc | hc
    · exfalso
      have hz : pzSourceScale n = 0 := by simp [pzSourceScale, hc]
      omega
    · exact hc
  obtain ⟨H₀, hH₀A, hH₀card, hH₀mono⟩ :=
    uniformRamseySequence_spec 3 (pzSourceCliqueSize n) A
      ((uniformRamseySequence_le_of_pzRamseyCliqueSize_pos hclique).trans hcard)
      color
  have htarget : pzSourceScale n + 1 ≤ H₀.card := by
    rw [hH₀card]
    exact pzSourceScale_add_one_le_cliqueSize n hclique
  obtain ⟨H, hHH₀, hHcard⟩ := Finset.exists_subset_card_eq htarget
  refine ⟨H, hHH₀.trans hH₀A, hHcard, ?_⟩
  rcases hH₀mono with ⟨b, hb⟩
  exact ⟨b, fun J hJ hJcard ↦ hb J (hJ.trans hHH₀) hJcard⟩

/-! ## The final source envelope -/

/-- The exact output expected from the finite geometric/combinatorial part
of the source proof.  Its scale is the size of the final monochromatic
triple clique. -/
structure PohoataZakharovEnvelopeCertificate where
  scale : ℕ → ℕ
  constant : ℝ
  scale_tendsto : Tendsto scale atTop atTop
  forces_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ X : Finset (Point 3), InGeneralPosition 3 X →
      (scale n : ℝ) ^ (constant * (n : ℝ) / (scale n : ℝ)) < (X.card : ℝ) →
      ContainsConvexSubset 3 n X

/-- An envelope certificate implies the literal point-set epsilon statement
of Theorem 1.1. -/
theorem PohoataZakharovEnvelopeCertificate.theoremOneOne
    (cert : PohoataZakharovEnvelopeCertificate) :
    PohoataZakharovTheoremOneOne := by
  intro ε hε
  have henv := eventually_pzEnvelope_lt_two_rpow
    cert.constant cert.scale_tendsto hε
  have hforce := cert.forces_eventually
  rw [eventually_atTop] at henv hforce
  obtain ⟨N₁, hN₁⟩ := hforce
  obtain ⟨N₂, hN₂⟩ := henv
  refine ⟨max N₁ N₂, fun n hn X hcard hgp ↦ ?_⟩
  exact hN₁ n ((le_max_left _ _).trans hn) X hgp
    ((hN₂ n ((le_max_right _ _).trans hn)).trans_le hcard)

/-! ## Existence of the numerical Erdős--Szekeres function -/

/-- The literal PZ theorem also proves that the forcing set defining
`erdosSzekeresNumber 3 n` is nonempty for every `n`. -/
theorem hasErdosSzekeresNumber_three_of_theoremOneOne
    (hPZ : PohoataZakharovTheoremOneOne) :
    ∀ n : ℕ, HasErdosSzekeresNumber 3 n := by
  intro n
  obtain ⟨n₀, hn₀⟩ := hPZ 1 (by norm_num)
  let m := max n n₀
  let N : ℕ := ⌈(2 : ℝ) ^ (m : ℝ)⌉₊
  refine ⟨N, ?_⟩
  intro X hNX hgp
  have hmconv : ContainsConvexSubset 3 m X := by
    apply hn₀ m (le_max_right n n₀) X _ hgp
    have hceil : (2 : ℝ) ^ (m : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hNX' : (N : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hNX
    simpa only [one_mul] using hceil.trans hNX'
  obtain ⟨Y, hYX, hYcard, hYconv⟩ := hmconv
  have hnY : n ≤ Y.card := by simpa only [hYcard] using le_max_left n n₀
  obtain ⟨Z, hZY, hZcard⟩ := Finset.exists_subset_card_eq hnY
  refine ⟨Z, hZY.trans hYX, hZcard, ?_⟩
  intro x hxZ hxHull
  apply hYconv x (hZY hxZ)
  exact convexHull_mono (by
    intro y hy
    exact Finset.erase_subset_erase x hZY hy) hxHull

end

end

/-! ### Upstream module `JSP527/PZ/Clusters.lean` -/

/-!
# Sections 2--3 of Pohoata--Zakharov, up to the uniform above/below selection

This file runs the geometric pipeline of the Pohoata--Zakharov argument on a large
general-position set `X ⊆ ℝ³` whose vertical projection is injective and planar-generic:
a Pór--Valtr positive-fraction configuration is lifted through the vertical projection,
Proposition 2.5 makes the cells two-separated while keeping strong convex position, the
resulting representatives form a projected convex chain, and a four-uniform Ramsey
selection makes the above/below pattern uniform.

It also records the transport lemma which produces the three projection hypotheses from an
arbitrary general-position set, together with the transfer of convex subsets back.
-/

noncomputable section

/-- Proposition 2.5 with the underlying lifted configuration retained, so that later steps
can see which planar projection the cells came from. -/
theorem exists_separatedPositiveFractionClusters_source
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X)
    (hgp : InGeneralPosition 3 X)
    (hlarge : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    ∃ D : SeparatedPositiveFractionClusters k X, D.source = C := by
  classical
  have hcell : ∀ i, 2 ^ (k ^ 3) ≤ (C.cell i).card := by
    intro i
    have hmul : 2 ^ (40 * k) * 2 ^ (k ^ 3) ≤ 2 ^ (40 * k) * (C.cell i).card := by
      calc
        2 ^ (40 * k) * 2 ^ (k ^ 3) = 2 ^ (40 * k + k ^ 3) := (pow_add 2 _ _).symm
        _ ≤ X.card := hlarge
        _ ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  have hallgp : InGeneralPosition 3 (allClusters C.cell) := hgp.mono C.allCells_subset
  obtain ⟨Y, hYC, hYtwo, hYloss⟩ :=
    exists_twoSeparated_subclusters C.cell C.cell_disjoint hcell hallgp
  have hYdensity : ∀ i, X.card ≤ 2 ^ (40 * k + k ^ 3) * (Y i).card := by
    intro i
    calc
      X.card ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
      _ ≤ 2 ^ (40 * k) * (2 ^ (k ^ 3) * (Y i).card) := Nat.mul_le_mul_left _ (hYloss i)
      _ = 2 ^ (40 * k + k ^ 3) * (Y i).card := by
        rw [pow_add]
        ring
  have hYne : ∀ i, (Y i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hi
    have hd := hYdensity i
    rw [hi] at hd
    simp only [Finset.card_empty, mul_zero, Nat.le_zero] at hd
    have hpos : 0 < X.card := lt_of_lt_of_le (by positivity) hlarge
    omega
  exact ⟨{
    source := C
    cluster := Y
    cluster_subset_source := hYC
    twoSeparated := hYtwo
    strongConvex := C.strong_convex.mono hYC
    density := hYdensity
    nonempty := hYne }, rfl⟩

/-- The two-separated positive-fraction clusters coming from the vertical projection,
together with the projected-convex-chain property of their representatives. -/
theorem exists_separatedPositiveFractionClusters_projectedChain
    {k : ℕ} (hk : 4 ≤ k)
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hproj : Set.InjOn verticalProjection X)
    (hgp2 : InGeneralPosition 2 (X.image verticalProjection))
    (hcard : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    ∃ C : SeparatedPositiveFractionClusters k X,
      IsProjectedConvexChain C.representative Finset.univ := by
  classical
  have hexp : 2 ≤ 40 * k + k ^ 3 := le_trans (by omega) (Nat.le_add_right _ _)
  have hXcard : 4 ≤ X.card := by
    refine le_trans ?_ hcard
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (40 * k + k ^ 3) := Nat.pow_le_pow_right (by norm_num) hexp
  have hcard40 : 2 ^ (40 * k) ≤ X.card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)) hcard
  obtain ⟨P⟩ := exists_orderedStrongPositiveFractionConfiguration k hk
    (X.image verticalProjection)
    (by rw [Finset.card_image_of_injOn hproj]; exact hcard40) hgp2
  obtain ⟨C, hCvert⟩ : ∃ C : LiftedPositiveFractionConfiguration k X,
      ⇑C.projection = verticalProjection := by
    refine ⟨⟨verticalProjectionAffine, ?_, ?_⟩, coe_verticalProjectionAffine⟩
    · simpa only [coe_verticalProjectionAffine] using hproj
    · simpa only [coe_verticalProjectionAffine] using P
  obtain ⟨D, hD⟩ := exists_separatedPositiveFractionClusters_source C hgp hcard
  subst hD
  refine ⟨D, ?_⟩
  apply D.source.planar.isProjectedConvexChain
  · intro i
    rw [← hCvert]
    exact D.representative_projection_mem i
  · intro i₀ i₁ i₂ i₃ h₀₁ h₁₂ h₂₃
    exact D.representative_four_independent hXcard hgp i₀ i₁ i₂ i₃ h₀₁ h₁₂ h₂₃

/-- Sections 2–3 of Pohoata–Zakharov up to the uniform above/below selection: a large
general-position set in `ℝ³` with injective, planar-general-position vertical projection
carries `m` two-separated, strongly convex clusters whose representatives form a projected
convex chain with uniform above/below pattern. -/
theorem exists_uniformSeparatedClusters {k m : ℕ} (hk : 4 ≤ k)
    (hkm : uniformRamseySequence 4 m ≤ k)
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hproj : Set.InjOn verticalProjection X)
    (hgp2 : InGeneralPosition 2 (X.image verticalProjection))
    (hcard : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    Nonempty (UniformSeparatedClusters k m X) := by
  classical
  obtain ⟨C, hchain⟩ :=
    exists_separatedPositiveFractionClusters_projectedChain hk hgp hproj hgp2 hcard
  obtain ⟨H, -, hHcard, huniform⟩ :=
    exists_uniformAboveBelow_subchain_of_ramseySequence C.representative Finset.univ
      (by simpa using hkm) hchain
  exact ⟨C.selectUniform H hHcard hchain huniform⟩

/-- Every general-position set with at least four points has an affine image which is
generic for the vertical projection, and convex subsets of that image transport back. -/
theorem exists_generic_image {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hXcard : 4 ≤ X.card) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      InGeneralPosition 3 (X.image e) ∧
      Set.InjOn verticalProjection (X.image e) ∧
      InGeneralPosition 2 ((X.image e).image verticalProjection) ∧
      (X.image e).card = X.card ∧
      (∀ n, ContainsConvexSubset 3 n (X.image e) → ContainsConvexSubset 3 n X) := by
  classical
  obtain ⟨e, hgpe, hinj, hgp2⟩ := exists_vertical_generic_affineEquiv hgp hXcard
  refine ⟨e, hgpe, hinj, hgp2, Finset.card_image_of_injective X e.injective, ?_⟩
  rintro n ⟨Y, hYsub, hYcard, hYconv⟩
  refine ⟨Y.image e.symm, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hYsub hy)
    simpa using hx
  · rw [Finset.card_image_of_injective _ e.symm.injective, hYcard]
  · exact (AffineEquiv.inConvexPosition_image_iff e.symm Y).mpr hYconv

end

/-! ### Upstream module `JSP527/PZ/Gadgets.lean` -/

/-!
# Proposition 3.1 on every ordered triple of a uniform separated cluster family

This file turns the single-triple statement `pohoata_zakharov_prop_three_one` into the
triple-indexed family consumed by the Ramsey step of Pohoata--Zakharov.  For a uniform
separated cluster family `U` on `Fin m` with `5 ≤ m` it produces, for every ordered triple
`j₁ < j₂ < j₃`, the two trihedral polyhedra containing the two alternating regions of (4.8),
and it packages the whole assignment as a `TripleGadgetFamily (Fin m)` indexed by three-element
subsets through the increasing enumeration `Finset.orderEmbOfFin`.
-/

noncomputable section

/-- Distinct clusters are disjoint and nonempty, so a family of `m` of them inside `X` forces
`m ≤ X.card`; four clusters already give the cardinality needed for general position to
constrain triples. -/
theorem UniformSeparatedClusters.four_le_card {k m : ℕ} {X : Finset (Point 3)}
    (U : UniformSeparatedClusters k m X) (hm : 4 ≤ m) : 4 ≤ X.card := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin m)), U.representative i ∈ X := fun i _ =>
    U.cluster_subset i (U.representative_mem i)
  have hinj : Set.InjOn U.representative (Finset.univ : Finset (Fin m)) := by
    intro i _ j _ hij
    by_contra hne
    exact Finset.disjoint_left.mp (U.strongConvex.pairwiseDisjoint hne)
      (U.representative_mem i) (hij ▸ U.representative_mem j)
  have hcard : m ≤ X.card := by
    simpa using Finset.card_le_card_of_injOn U.representative hmem hinj
  omega

/-- The three-point analogue of `affineIndependent_fin_four_of_generalPosition`: an explicitly
indexed injective triple of a general-position set with at least four points is affinely
independent. -/
theorem affineIndependent_fin_three_of_generalPosition {U : Finset (Point 3)}
    (hUcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) (p : Fin 3 → Point 3)
    (hpU : ∀ i, p i ∈ U) (hpinj : Function.Injective p) :
    AffineIndependent ℝ p := by
  classical
  let A := Finset.univ.image p
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hpU i
  have hAcard : A.card ≤ 3 := by
    simpa [A] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := p)
  have hAind : AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) :=
    affineIndependent_of_card_le_three_of_generalPosition_three hgp hUcard hAU hAcard
  let e : Fin 3 ↪ A :=
    ⟨fun i ↦ ⟨p i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩,
      fun i j hij ↦ hpinj (congrArg Subtype.val hij)⟩
  convert hAind.comp_embedding e using 1
  funext i
  rfl

/-- A subset of a three-dimensional general-position set with at least four points has no three
collinear points, in the linear-independence form required by Proposition 3.1. -/
theorem noThreeCollinear_of_generalPosition {X Y : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card) (hYX : Y ⊆ X) :
    NoThreeCollinear Y := by
  intro x hx y hy z hz hxy hyz hxz
  have hpU : ∀ i, ![x, y, z] i ∈ X := by
    intro i
    fin_cases i
    · exact hYX hx
    · exact hYX hy
    · exact hYX hz
  have hpinj : Function.Injective ![x, y, z] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h : AffineIndependent ℝ ![x, y, z] :=
    affineIndependent_fin_three_of_generalPosition hXcard hgp _ hpU hpinj
  apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 3)) ?_).mpr
    ((affineIndependent_iff_linearIndependent_vsub ℝ ![x, y, z] 0).mp h)
  funext i
  fin_cases i <;> rfl

/-- The two full-cluster separations required by Proposition 3.1, obtained from the
representative-level Corollary 2.4 through Proposition 2.7. -/
theorem UniformSeparatedClusters.trihedral_cluster_hulls_disjoint {k m : ℕ}
    {X : Finset (Point 3)} (U : UniformSeparatedClusters k m X) (hm : 5 ≤ m)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Disjoint
      (convexHull ℝ
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) :
          Set (Point 3))) ∧
    Disjoint
      (convexHull ℝ
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) :
          Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3))) := by
  classical
  obtain ⟨hrep₁, hrep₂⟩ :=
    trihedral_representative_hulls_disjoint U.representative hm U.projectedChain
      U.uniformAboveBelow j₁ j₂ j₃ h₁₂ h₂₃
  have hunion := trihedralIndices_union_middle h₁₂ h₂₃
  have hunion' : (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}) ∪
      secondTrihedralIndices j₁ j₂ j₃ = Finset.univ := by
    rw [Finset.union_assoc, Finset.union_comm ({j₂} : Finset (Fin m))]
    exact hunion
  have hj₃ : j₃ ∈ firstTrihedralIndices j₁ j₂ j₃ := by simp [h₂₃]
  have hj₁ : j₁ ∈ secondTrihedralIndices j₁ j₂ j₃ := by simp [h₁₂]
  exact ⟨U.fullCluster_hulls_disjoint _ _ hunion ⟨j₃, hj₃⟩ ⟨j₂, by simp⟩ hrep₁,
    U.fullCluster_hulls_disjoint _ _ hunion' ⟨j₂, by simp⟩ ⟨j₁, hj₁⟩ hrep₂⟩

/-- Proposition 3.1 applied to one ordered triple of a uniform separated cluster family. -/
theorem exists_trihedralClusterGadget {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m)
    (U : UniformSeparatedClusters k m X) (j₁ j₂ j₃ : Fin m)
    (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Nonempty (TrihedralClusterGadget U.cluster j₁ j₂ j₃) := by
  obtain ⟨hfirst, hsecond⟩ :=
    U.trihedral_cluster_hulls_disjoint hm j₁ j₂ j₃ h₁₂ h₂₃
  exact pohoata_zakharov_prop_three_one U.cluster j₁ j₂ j₃ h₁₂ h₂₃ U.nonempty
    (noThreeCollinear_of_generalPosition hgp (U.four_le_card (by omega))
      (U.cluster_subset j₂))
    U.strongConvex hfirst hsecond

/-- A choice of Proposition 3.1 gadget for each ordered triple. -/
def clusterGadget {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    TrihedralClusterGadget U.cluster j₁ j₂ j₃ :=
  Classical.choice (exists_trihedralClusterGadget hgp hm U j₁ j₂ j₃ h₁₂ h₂₃)

/-- The triple gadget family attached to a uniform separated cluster family: a three-element
index set is enumerated increasingly and receives the gadget of its sorted triple. -/
def gadgetFamily {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X) :
    TripleGadgetFamily (Fin m) := fun J hJ =>
  (clusterGadget hgp hm U (J.orderEmbOfFin hJ 0) (J.orderEmbOfFin hJ 1)
      (J.orderEmbOfFin hJ 2) ((J.orderEmbOfFin hJ).strictMono (by decide))
      ((J.orderEmbOfFin hJ).strictMono (by decide))).toMiddleTripleGadget

/-- The middle cluster and the two containments (4.8) for the gadget attached to a
three-element index set with a named increasing enumeration. -/
theorem gadgetFamily_spec {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (J : Finset (Fin m)) (hJ : J.card = 3) (j₁ j₂ j₃ : Fin m)
    (h0 : J.orderEmbOfFin hJ 0 = j₁) (h1 : J.orderEmbOfFin hJ 1 = j₂)
    (h2 : J.orderEmbOfFin hJ 2 = j₃) :
    (gadgetFamily hgp hm U J hJ).middle = U.cluster j₂ ∧
    (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U J hJ).firstPolytope ∧
    (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U J hJ).secondPolytope := by
  subst h0
  subst h1
  subst h2
  exact ⟨rfl, (clusterGadget hgp hm U _ _ _ _ _).first_region_subset,
    (clusterGadget hgp hm U _ _ _ _ _).second_region_subset⟩

/-- The middle cluster and the two containments (4.8) for every ordered triple. -/
theorem gadgetFamily_spec_triple {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃)
    (hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3) :
    (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
    (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).firstPolytope ∧
    (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).secondPolytope := by
  classical
  have h₁₃ : j₁ < j₃ := h₁₂.trans h₂₃
  have hmono : StrictMono ![j₁, j₂, j₃] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hmem : ∀ i, ![j₁, j₂, j₃] i ∈ ({j₁, j₂, j₃} : Finset (Fin m)) := by
    intro i
    fin_cases i <;> simp
  have hsorted := Finset.orderEmbOfFin_unique hJ hmem hmono
  exact gadgetFamily_spec hgp hm U _ hJ j₁ j₂ j₃ (congrFun hsorted 0).symm
    (congrFun hsorted 1).symm (congrFun hsorted 2).symm

/-- The projection-order certificates on every subset of the middle cluster, for the gadget
attached to a three-element index set with a named increasing enumeration. -/
theorem gadgetFamily_certificates {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (J : Finset (Fin m)) (hJ : J.card = 3) (j₂ : Fin m)
    (h1 : J.orderEmbOfFin hJ 1 = j₂) :
    (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
      Nonempty (ProjectionOrderCertificate (gadgetFamily hgp hm U J hJ).firstPolytope Y
        (Fin 3))) ∧
    (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
      Nonempty (ProjectionOrderCertificate (gadgetFamily hgp hm U J hJ).secondPolytope Y
        (Fin 3))) := by
  subst h1
  exact ⟨fun Y hY =>
      ⟨((clusterGadget hgp hm U _ _ _ _ _).first_generic Y hY).toProjectionOrderCertificate⟩,
    fun Y hY =>
      ⟨((clusterGadget hgp hm U _ _ _ _ _).second_generic Y hY).toProjectionOrderCertificate⟩⟩

/-- The triple gadget family of a uniform separated cluster family, together with the middle
cluster, the two containments (4.8), and the projection-order certificates of Proposition 2.1
on every subset of the middle cluster, for every ordered triple. -/
theorem exists_tripleGadgetFamily {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m)
    (U : UniformSeparatedClusters k m X) :
    ∃ G : TripleGadgetFamily (Fin m),
      ∀ (j₁ j₂ j₃ : Fin m), j₁ < j₂ → j₂ < j₃ →
        ∀ hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3,
          (G {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
          (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
            (G {j₁, j₂, j₃} hJ).firstPolytope ∧
          (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
            (G {j₁, j₂, j₃} hJ).secondPolytope ∧
          (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
            Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).firstPolytope Y
              (Fin 3))) ∧
          (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
            Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).secondPolytope Y
              (Fin 3))) := by
  classical
  refine ⟨gadgetFamily hgp hm U, ?_⟩
  intro j₁ j₂ j₃ h₁₂ h₂₃ hJ
  obtain ⟨hmid, hfirst, hsecond⟩ :=
    gadgetFamily_spec_triple hgp hm U j₁ j₂ j₃ h₁₂ h₂₃ hJ
  have hmono : StrictMono ![j₁, j₂, j₃] := by
    intro a b hab
    have h₁₃ : j₁ < j₃ := h₁₂.trans h₂₃
    fin_cases a <;> fin_cases b <;> simp_all
  have hmem : ∀ i, ![j₁, j₂, j₃] i ∈ ({j₁, j₂, j₃} : Finset (Fin m)) := by
    intro i
    fin_cases i <;> simp
  have hsorted := Finset.orderEmbOfFin_unique hJ hmem hmono
  obtain ⟨hcert₁, hcert₂⟩ :=
    gadgetFamily_certificates hgp hm U _ hJ j₂ (congrFun hsorted 1).symm
  exact ⟨hmid, hfirst, hsecond, hcert₁, hcert₂⟩

end

/-! ### Upstream module `JSP527/PZ/Extraction.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (JSP-000527 submission, 2026-09-16).
-/

/-!
# The unconditional extraction step of Pohoata--Zakharov

This file closes the end of Section 3 of Pohoata--Zakharov.  A large general-position set in
`ℝ³` is first moved by an affine equivalence into a position generic for the vertical
projection, then carries `m = pzAboveBelowScale n` two-separated, strongly convex clusters with
a uniform above/below pattern.  Proposition 3.1 attaches two trihedral polyhedra to every
ordered triple of clusters; the triple Ramsey step of the assembly makes the resulting
Dilworth colour constant on a clique of `t + 1 = 2q + 1` indices.

The alternating triples of that clique (`alternatingTriple`) then give `q` middle clusters,
each carrying a free set for the *same* polyhedron.  For the red colour the clique is read
left to right, for the blue colour right to left; in both cases the middle index of every
other alternating triple lies in the region of (4.8) covered by the selected polyhedron, so
the free sets are mutually contained in each other's backgrounds.  This is exactly an
`AlternatingFreeFamily`, and `containsConvexSubset_of_sourceEnvelope` converts it into a
convex subset of size `n`.
-/

open _root_.Filter _root_.Finset _root_.Set

noncomputable section

/-- The alternating free family extracted from a monochromatic triple clique.  The data is
presented abstractly: `a₁ r < a₂ r < a₃ r` is the sorted `r`-th alternating triple, `b` is the
Ramsey colour, and `hother` records that every other middle index lies in the region of (4.8)
belonging to the selected polyhedron. -/
theorem exists_alternatingFreeFamily {k m q : ℕ} {X : Finset (Point 3)}
    (U : UniformSeparatedClusters k m X) (G : TripleGadgetFamily (Fin m))
    (hspec : ∀ j₁ j₂ j₃ : Fin m, j₁ < j₂ → j₂ < j₃ →
      ∀ hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3,
        (G {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
          (G {j₁, j₂, j₃} hJ).firstPolytope ∧
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
          (G {j₁, j₂, j₃} hJ).secondPolytope ∧
        (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
          Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).firstPolytope Y (Fin 3))) ∧
        (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
          Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).secondPolytope Y (Fin 3))))
    (b : Bool) (jb : Fin (2 * q + 1) ↪ Fin m) (a₁ a₂ a₃ : Fin q → Fin m)
    (h₁₂ : ∀ r : Fin q, a₁ r < a₂ r) (h₂₃ : ∀ r : Fin q, a₂ r < a₃ r)
    (htriple : ∀ r : Fin q, alternatingTriple jb r = {a₁ r, a₂ r, a₃ r})
    (h₂inj : Function.Injective a₂)
    (hother : ∀ r r' : Fin q, r ≠ r' →
      a₂ r' ∈ (if b then firstTrihedralIndices (a₁ r) (a₂ r) (a₃ r)
        else secondTrihedralIndices (a₁ r) (a₂ r) (a₃ r)))
    (hfree : ∀ r : Fin q, ∃ Z : Finset (Point 3),
      Z ⊆ (alternatingGadget G jb r).middle ∧
      (alternatingGadget G jb r).middle.card ≤ Z.card * Z.card ∧
      PFree (if b then (alternatingGadget G jb r).firstPolytope
        else (alternatingGadget G jb r).secondPolytope) Z) :
    ∃ F : AlternatingFreeFamily q X,
      ∀ r : Fin q, X.card ≤ 2 ^ (40 * k + k ^ 3) * (F.middle r).card := by
  classical
  have hGcongr : ∀ (S S' : Finset (Fin m)) (hS : S.card = 3) (hS' : S'.card = 3),
      S = S' → G S hS = G S' hS' := by
    rintro S S' hS hS' rfl
    rfl
  have hcard3 : ∀ r : Fin q, ({a₁ r, a₂ r, a₃ r} : Finset (Fin m)).card = 3 := by
    intro r
    rw [← htriple r]
    exact alternatingTriple_card jb r
  have hgad : ∀ r : Fin q, alternatingGadget G jb r = G {a₁ r, a₂ r, a₃ r} (hcard3 r) :=
    fun r => hGcongr _ _ _ _ (htriple r)
  have hmid : ∀ r : Fin q, (alternatingGadget G jb r).middle = U.cluster (a₂ r) := by
    intro r
    rw [hgad r]
    exact (hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)).1
  obtain ⟨bg, hbg⟩ : ∃ bg : Fin q → Set (Point 3), ∀ r : Fin q,
      bg r = if b then (alternatingGadget G jb r).firstPolytope
        else (alternatingGadget G jb r).secondPolytope := ⟨_, fun _ => rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin q → Finset (Fin m), ∀ r : Fin q,
      idx r = if b then firstTrihedralIndices (a₁ r) (a₂ r) (a₃ r)
        else secondTrihedralIndices (a₁ r) (a₂ r) (a₃ r) := ⟨_, fun _ => rfl⟩
  have hsub : ∀ r : Fin q,
      (↑(clusterUnion U.cluster (idx r)) : Set (Point 3)) ⊆ bg r := by
    intro r
    obtain ⟨-, hfirst, hsecond, -, -⟩ := hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)
    rw [hidx r, hbg r]
    cases b
    · simpa [hgad r] using hsecond
    · simpa [hgad r] using hfirst
  have hcert : ∀ (r : Fin q) (Y : Finset (Point 3)), Y ⊆ U.cluster (a₂ r) →
      Nonempty (ProjectionOrderCertificate (bg r) Y (Fin 3)) := by
    intro r Y hY
    obtain ⟨-, -, -, hc₁, hc₂⟩ := hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)
    rw [hbg r]
    cases b
    · simpa [hgad r] using hc₂ Y hY
    · simpa [hgad r] using hc₁ Y hY
  choose Z hZmid hZcard hZfree using hfree
  have hZcluster : ∀ r : Fin q, Z r ⊆ U.cluster (a₂ r) := by
    intro r
    rw [← hmid r]
    exact hZmid r
  refine ⟨{ middle := fun r => U.cluster (a₂ r)
            background := bg
            freeSet := Z
            middle_subset := fun r => U.cluster_subset (a₂ r)
            free_subset_middle := hZcluster
            middle_card_le_free_square := fun r => by rw [← hmid r]; exact hZcard r
            free_disjoint := ?_
            free := fun r => by rw [hbg r]; exact hZfree r
            certificate := fun r => Classical.choice (hcert r (Z r) (hZcluster r))
            other_free_subset := ?_ }, fun r => U.density (a₂ r)⟩
  · intro r _ r' _ hne
    exact (U.strongConvex.pairwiseDisjoint fun h => hne (h₂inj h)).mono
      (hZcluster r) (hZcluster r')
  · intro r r' hne
    refine subset_trans ?_ (hsub r)
    intro x hx
    have hxc : x ∈ U.cluster (a₂ r') := hZcluster r' hx
    have hmem : a₂ r' ∈ idx r := by
      rw [hidx r]
      exact hother r r' hne
    simp only [clusterUnion, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨a₂ r', by simpa using hmem, hxc⟩

/-- The extraction theorem: for every large `n`, a general-position set in `ℝ³` beyond the
source envelope `t ^ (77 n / t)` at scale `t = pzSourceScale n` contains `n` points in convex
position. -/
theorem pohoataZakharov_forces_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ X : Finset (Point 3), InGeneralPosition 3 X →
      (pzSourceScale n : ℝ) ^ ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) < (X.card : ℝ) →
      ContainsConvexSubset 3 n X := by
  classical
  filter_upwards [pzQuarterRoot_tendsto_atTop.eventually_ge_atTop 4,
    pzAboveBelowScale_tendsto_atTop.eventually_ge_atTop 5,
    pzSourceScale_tendsto_atTop.eventually_ge_atTop 3,
    eventually_uniformRamseySequence_aboveBelowScale_le_quarterRoot,
    eventually_ge_atTop 2] with n hk4 hm5 ht3 hkm hn2
  intro X hgp hlarge
  set q := (pzSourceScale n + 1) / 2 with hqdef
  have hq2 : pzSourceScale n = 2 * q := by
    obtain ⟨s, hs⟩ := pzSourceScale_even n
    omega
  -- numerical preliminaries
  have htk := pzSourceScale_le_quarterRoot n
  have hk4' := pzQuarterRoot_pow_four_le n
  have hkle : pzQuarterRoot n ≤ pzQuarterRoot n ^ 4 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ pzQuarterRoot n by omega) (show 1 ≤ 4 by omega)
  have htn : pzSourceScale n ≤ n := htk.trans (hkle.trans hk4')
  have ht1 : (1 : ℝ) ≤ (pzSourceScale n : ℝ) := by
    have h : (1 : ℕ) ≤ pzSourceScale n := by omega
    exact_mod_cast h
  have hexp : (41 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ) ≤
      (77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have htpos : (0 : ℝ) < (pzSourceScale n : ℝ) := by linarith
    gcongr
    norm_num
  have henv : ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^ ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) :=
    (positiveFractionLoss_le_sourceEnvelope n (by omega)).trans
      (Real.rpow_le_rpow_of_exponent_le ht1 hexp)
  have hcardX : 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) ≤ X.card := by
    have h := henv.trans_lt hlarge
    exact_mod_cast h.le
  have hX4 : 4 ≤ X.card := by
    refine le_trans ?_ hcardX
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) :=
          Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (Nat.le_add_right _ _))
  -- the geometric pipeline
  obtain ⟨e, hgpe, hinj, hgp2, hcarde, htrans⟩ := exists_generic_image hgp hX4
  have hcardX' : 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) ≤ (X.image e).card := by
    rw [hcarde]; exact hcardX
  obtain ⟨U⟩ := exists_uniformSeparatedClusters (k := pzQuarterRoot n)
    (by omega) hkm hgpe hinj hgp2 hcardX'
  obtain ⟨G, hG⟩ := exists_tripleGadgetFamily hgpe hm5 U
  -- the triple Ramsey step
  obtain ⟨H, -, hHcard, hHmono⟩ := pzSourceScale_tripleRamsey n
    (Finset.univ : Finset (Fin (pzAboveBelowScale n))) (by omega) (by simp)
    (fun J => if hJ : J.card = 3 then (G J hJ).color else false)
  obtain ⟨bcol, hb⟩ := hHmono
  have hHcard2 : H.card = 2 * q + 1 := by omega
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin (2 * q + 1) ↪o Fin (pzAboveBelowScale n), ∀ p, e₀ p ∈ H :=
    ⟨H.orderEmbOfFin hHcard2, H.orderEmbOfFin_mem hHcard2⟩
  have hmono : ∀ J : Finset (Fin (pzAboveBelowScale n)), J ⊆ H → ∀ hJ : J.card = 3,
      (G J hJ).color = bcol := by
    intro J hJH hJ
    have h : (if hJ' : J.card = 3 then (G J hJ').color else false) = bcol := hb J hJH hJ
    rw [dite_eq_left_of_eq_true (eq_true hJ)] at h
    exact h
  have hlt : ∀ p p' : Fin (2 * q + 1), p.1 < p'.1 → e₀ p < e₀ p' :=
    fun p p' h => e₀.lt_iff_lt.mpr h
  have hle : ∀ p p' : Fin (2 * q + 1), p.1 ≤ p'.1 → e₀ p ≤ e₀ p' :=
    fun p p' h => e₀.le_iff_le.mpr h
  have hinj₀ : ∀ p p' : Fin (2 * q + 1), e₀ p = e₀ p' → p.1 = p'.1 :=
    fun p p' h => congrArg Fin.val (e₀.injective h)
  -- the alternating free family, red clique read forwards and blue clique read backwards
  obtain ⟨F, hFdens⟩ : ∃ F : AlternatingFreeFamily q (X.image e),
      ∀ r : Fin q, (X.image e).card ≤
        2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) * (F.middle r).card := by
    cases bcol
    · refine exists_alternatingFreeFamily U G hG false
        ((⟨Fin.rev, Fin.rev_injective⟩ : Fin (2 * q + 1) ↪ Fin (2 * q + 1)).trans
          e₀.toEmbedding)
        (fun _ => e₀ (Fin.rev (alternatingLastPosition q)))
        (fun r => e₀ (Fin.rev (alternatingMiddlePosition r)))
        (fun r => e₀ (Fin.rev (alternatingLeftPosition r))) ?_ ?_ ?_ ?_ ?_ ?_
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [Fin.val_rev, alternatingLastPosition, alternatingMiddlePosition]
        omega
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLeftPosition]
        omega
      · intro r
        simp only [alternatingTriple]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · intro r r' h
        have hr := r.isLt
        have hr' := r'.isLt
        have h' := hinj₀ _ _ h
        simp only [Fin.val_rev, alternatingMiddlePosition] at h'
        exact Fin.ext (by omega)
      · intro r r' hne
        have hr := r.isLt
        have hr' := r'.isLt
        have hne' : r.1 ≠ r'.1 := fun h => hne (Fin.ext h)
        simp only [Bool.false_eq_true, ite_false, mem_secondTrihedralIndices]
        rcases lt_or_gt_of_ne hne' with h | h
        · left
          constructor
          · refine hle _ _ ?_
            simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLastPosition]
            omega
          · refine hlt _ _ ?_
            simp only [Fin.val_rev, alternatingMiddlePosition]
            omega
        · right
          refine hlt _ _ ?_
          simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLeftPosition]
          omega
      · exact exists_alternating_free_subsets_of_monochromatic_clique G H
          ((⟨Fin.rev, Fin.rev_injective⟩ : Fin (2 * q + 1) ↪ Fin (2 * q + 1)).trans
            e₀.toEmbedding) (fun p => he₀ _) false hmono
    · refine exists_alternatingFreeFamily U G hG true e₀.toEmbedding
        (fun r => e₀ (alternatingLeftPosition r))
        (fun r => e₀ (alternatingMiddlePosition r))
        (fun _ => e₀ (alternatingLastPosition q)) ?_ ?_ ?_ ?_ ?_ ?_
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [alternatingLeftPosition, alternatingMiddlePosition]
        omega
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [alternatingMiddlePosition, alternatingLastPosition]
        omega
      · intro r
        rfl
      · intro r r' h
        have hr := r.isLt
        have hr' := r'.isLt
        have h' := hinj₀ _ _ h
        simp only [alternatingMiddlePosition] at h'
        exact Fin.ext (by omega)
      · intro r r' hne
        have hr := r.isLt
        have hr' := r'.isLt
        have hne' : r.1 ≠ r'.1 := fun h => hne (Fin.ext h)
        simp only [reduceIte, mem_firstTrihedralIndices]
        rcases lt_or_gt_of_ne hne' with h | h
        · right
          constructor
          · refine hlt _ _ ?_
            simp only [alternatingMiddlePosition]
            omega
          · refine hle _ _ ?_
            simp only [alternatingMiddlePosition, alternatingLastPosition]
            omega
        · left
          refine hlt _ _ ?_
          simp only [alternatingMiddlePosition, alternatingLeftPosition]
          omega
      · exact exists_alternating_free_subsets_of_monochromatic_clique G H _
          (fun p => he₀ p) true hmono
  -- conclude
  refine htrans n (F.containsConvexSubset_of_sourceEnvelope hn2 ht3 htn hFdens ?_)
  rw [hcarde]
  exact hlarge

end

end

/-! ### Upstream module `JSP527/PZ/Main.lean` -/

/-!
# Erdős Problem 651: `f₃(n) ≤ 2^{o(n)}` (Pohoata–Zakharov 2022, Theorem 1.1)

The extraction theorem `Erdos651.pohoataZakharov_forces_eventually` supplies the envelope
certificate of the assembly (scale `pzSourceScale`, constant `77`); the bridge lemmas of plby's
`Erdos651` module turn it into the point-set statement, the well-definedness of the
Erdős–Szekeres numbers, the subexponential upper bound and the refutation of Erdős's
conjectured exponential lower bound.
-/

namespace PohoataZakharov

/-- The envelope certificate of the assembly, discharged by the extraction theorem. -/
noncomputable def certificate : Erdos651.PohoataZakharovEnvelopeCertificate where
  scale := Erdos651.pzSourceScale
  constant := 77
  scale_tendsto := Erdos651.pzSourceScale_tendsto_atTop
  forces_eventually := Erdos651.pohoataZakharov_forces_eventually

/-- Pohoata–Zakharov, Theorem 1.1 (point-set form). -/
theorem theorem_one_one : Erdos651.PohoataZakharovTheoremOneOne :=
  certificate.theoremOneOne

/-- The Erdős–Szekeres number in dimension three exists for every `n`. -/
theorem hasErdosSzekeresNumber_three (n : ℕ) : Erdos651.HasErdosSzekeresNumber 3 n :=
  Erdos651.hasErdosSzekeresNumber_three_of_theoremOneOne theorem_one_one n

/-- `f₃(n) ≤ 2 ^ (o(n))`: the negative answer to Erdős Problem 651. -/
theorem erdos_651_subexponential :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3) :=
  Erdos651.pohoataZakharovTheoremOneOne_imp_subexponential theorem_one_one

end PohoataZakharov

/-! ### Upstream module `JSP527/PZ/Dimensions.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

/-!
# Erdős Problem 651 in every dimension `d ≥ 3`

A generic linear projection `Point (d + 2) → Point (d + 1)` is injective on a fixed finite
general-position set and carries it to a general-position set: the direction of the projection
is chosen outside the finitely many proper subspaces spanned by the differences of the small
subsets, which is possible because a real vector space is not a finite union of proper
subspaces.  Convex position pulls back along any affine map that is injective on the set, so a
convex-position certificate found in dimension `d + 1` lifts to dimension `d + 2`.

This makes the Erdős–Szekeres numbers decrease with the dimension, up to the additive constant
forced by sets that are too small for the projection argument: `f_{d+1}(n) ≤ max (f_d(n)) (d+3)`
for `d ≥ 1`.  The constant is harmless asymptotically, so the Pohoata–Zakharov subexponential
bound and the refutation of Erdős's conjectured exponential lower bound hold in every
dimension `d ≥ 3`.
-/

open Erdos651 _root_.Filter

namespace PohoataZakharov

section GenericProjection

variable {d : ℕ}

/-- The fibre-selection finset of a subset of an image maps exactly onto that subset. -/
theorem image_filter_mem {e : ℕ} {X : Finset (Point d)} {T : Finset (Point e)}
    (π : Point d → Point e) (hT : T ⊆ X.image π) :
    (X.filter fun x ↦ π x ∈ T).image π = T := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp (hT hy)
    subst hxy
    exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩

/-- In a `(d + 2)`-dimensional general-position set with at least `d + 3` points, every subset
of at most `d + 2` points is affinely independent.  The cardinality hypothesis is necessary
because `InGeneralPosition (d + 2)` only directly constrains `(d + 3)`-point subsets. -/
theorem affineIndependent_of_card_le_of_inGeneralPosition {X S : Finset (Point (d + 2))}
    (hgp : InGeneralPosition (d + 2) X) (hXcard : d + 3 ≤ X.card) (hSX : S ⊆ X)
    (hScard : S.card ≤ d + 2) :
    AffineIndependent ℝ (fun p : S ↦ (p : Point (d + 2))) := by
  obtain ⟨T, hST, hTX, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hSX (by omega : S.card ≤ d + 3) hXcard
  have hT : AffineIndependent ℝ (fun p : T ↦ (p : Point (d + 2))) := hgp T hTX (by omega)
  exact hT.mono (by
    intro p hp
    exact hST hp)

/-- A finite general-position set of at least `d + 3` points in `Point (d + 2)` admits a
generic affine projection to `Point (d + 1)` which is injective on the set and whose image is
again in general position. -/
theorem exists_generic_projection {X : Finset (Point (d + 2))}
    (hgp : InGeneralPosition (d + 2) X) (hXcard : d + 3 ≤ X.card) :
    ∃ π : Point (d + 2) →ᵃ[ℝ] Point (d + 1),
      Set.InjOn π X ∧ InGeneralPosition (d + 1) (X.image π) := by
  classical
  have hdim : Module.finrank ℝ (Point (d + 2)) = d + 2 := by simp [Point]
  let I := X.powerset.filter fun S ↦ S.card ≤ d + 2
  let bad : I → Submodule ℝ (Point (d + 2)) :=
    fun S ↦ vectorSpan ℝ (S.1 : Set (Point (d + 2)))
  have hbad : ∀ S : I, bad S ≠ ⊤ := by
    intro S htop
    have hSX : S.1 ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    have hScard : S.1.card ≤ d + 2 := (Finset.mem_filter.mp S.2).2
    have hAI := affineIndependent_of_card_le_of_inGeneralPosition hgp hXcard hSX hScard
    by_cases hSne : S.1.Nonempty
    · let _ : Nonempty S.1 := Finset.nonempty_coe_sort.mpr hSne
      have hfin := hAI.finrank_vectorSpan_add_one
      have hrange :
          Set.range (fun p : S.1 ↦ (p : Point (d + 2))) = (S.1 : Set (Point (d + 2))) := by
        ext x
        simp
      rw [hrange] at hfin
      change vectorSpan ℝ (S.1 : Set (Point (d + 2))) = ⊤ at htop
      rw [htop, finrank_top, hdim, Fintype.card_coe] at hfin
      omega
    · have hSempty : S.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      simp [bad, hSempty] at htop
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    let E : I := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset X, by simp⟩⟩
    exact hv E (by simp [bad])
  let K : Submodule ℝ (Point (d + 2)) := ℝ ∙ v
  have hKfin : Module.finrank ℝ K = 1 := finrank_span_singleton hv0
  have hQfin : Module.finrank ℝ (Point (d + 2) ⧸ K) = d + 1 := by
    have hsum := K.finrank_quotient_add_finrank
    rw [hKfin] at hsum
    omega
  let e : (Point (d + 2) ⧸ K) ≃ₗ[ℝ] Point (d + 1) := LinearEquiv.ofFinrankEq _ _ (by
    rw [hQfin]
    simp [Point])
  let L : Point (d + 2) →ₗ[ℝ] Point (d + 1) := e.toLinearMap.comp K.mkQ
  let π : Point (d + 2) →ᵃ[ℝ] Point (d + 1) := L.toAffineMap
  have hker : LinearMap.ker L = K := by
    ext z
    simp [L, K]
  have hpreserve (S : Finset (Point (d + 2))) (hSX : S ⊆ X) (hScard : S.card ≤ d + 2) :
      AffineIndependent ℝ (fun z : S ↦ π (z : Point (d + 2))) := by
    have hAI := affineIndependent_of_card_le_of_inGeneralPosition hgp hXcard hSX hScard
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst S
      exact affineIndependent_of_subsingleton ℝ _
    let _ : Nonempty S := Finset.nonempty_coe_sort.mpr hS
    let a : S := ⟨hS.choose, hS.choose_spec⟩
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a] at hAI ⊢
    simp_rw [← π.linearMap_vsub]
    apply hAI.map
    rw [show LinearMap.ker π.linear = K by simpa [π] using hker]
    have hspan_le :
        Submodule.span ℝ
            (Set.range fun z : {z : S // z ≠ a} ↦
              (z.1 : Point (d + 2)) -ᵥ (a : Point (d + 2))) ≤
          vectorSpan ℝ (S : Set (Point (d + 2))) := by
      rw [Submodule.span_le]
      rintro w ⟨z, rfl⟩
      exact vsub_mem_vectorSpan ℝ z.1.2 a.2
    let SS : I := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSX, hScard⟩⟩
    have hvS : v ∉ vectorSpan ℝ (S : Set (Point (d + 2))) := by simpa [bad] using hv SS
    exact Disjoint.mono_left hspan_le (Submodule.disjoint_span_singleton_of_notMem hvS)
  have hπinj : Set.InjOn π X := by
    intro x hx y hy hxy
    by_contra hne
    let S : Finset (Point (d + 2)) := {x, y}
    have hSX : S ⊆ X := by
      intro z hz
      have hz' : z = x ∨ z = y := by simpa [S] using hz
      rcases hz' with rfl | rfl
      · simpa using hx
      · simpa using hy
    have hScard : S.card ≤ d + 2 := by
      have hle : S.card ≤ ({y} : Finset (Point (d + 2))).card + 1 := by
        simpa [S] using Finset.card_insert_le x ({y} : Finset (Point (d + 2)))
      simp only [Finset.card_singleton] at hle
      omega
    have hAI := hpreserve S hSX hScard
    have hxyS : x ∈ S := by simp [S]
    have hyyS : y ∈ S := by simp [S]
    exact hne (congrArg Subtype.val
      (hAI.injective (show π (⟨x, hxyS⟩ : S) = π (⟨y, hyyS⟩ : S) from hxy)))
  refine ⟨π, hπinj, ?_⟩
  intro T hTsub hTcard
  let S : Finset (Point (d + 2)) := X.filter fun x ↦ π x ∈ T
  have hSX : S ⊆ X := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hImage : S.image π = T := image_filter_mem _ hTsub
  have hπinjS : Set.InjOn π S := hπinj.mono hSX
  have hScard : S.card = d + 2 := by
    have h1 : S.card = T.card := by
      rw [← Finset.card_image_of_injOn hπinjS, hImage]
    omega
  have hAIS := hpreserve S hSX (by omega)
  have hpreExists (y : T) : ∃ x ∈ S, π x = (y : Point (d + 1)) := by
    have hy : (y : Point (d + 1)) ∈ S.image π := by
      rw [hImage]
      exact y.2
    exact Finset.mem_image.mp hy
  choose pre hpreS hpre using hpreExists
  let emb : T ↪ S :=
    ⟨fun y ↦ ⟨pre y, hpreS y⟩, fun y z hyz ↦ Subtype.ext (by
      calc
        (y : Point (d + 1)) = π (pre y) := (hpre y).symm
        _ = π (pre z) := congrArg π (congrArg Subtype.val hyz)
        _ = (z : Point (d + 1)) := hpre z)⟩
  have hemb : (fun z : S ↦ π (z : Point (d + 2))) ∘ emb =
      fun z : T ↦ (z : Point (d + 1)) := by
    funext y
    exact hpre y
  rw [← hemb]
  exact hAIS.comp_embedding emb

end GenericProjection

/-- A convex-position subset of the image of an affine map that is injective on `X` pulls back
to a convex-position subset of `X` of the same cardinality. -/
theorem containsConvexSubset_of_image {d e n : ℕ} {X : Finset (Point d)}
    (π : Point d →ᵃ[ℝ] Point e) (hπ : Set.InjOn π X)
    (h : ContainsConvexSubset e n (X.image π)) : ContainsConvexSubset d n X := by
  classical
  obtain ⟨Y, hYsub, hYcard, hYconv⟩ := h
  refine ⟨X.filter fun x ↦ π x ∈ Y, Finset.filter_subset _ _, ?_, ?_⟩
  · calc (X.filter fun x ↦ π x ∈ Y).card
        = ((X.filter fun x ↦ π x ∈ Y).image π).card :=
          (Finset.card_image_of_injOn (hπ.mono (Finset.filter_subset _ _))).symm
      _ = Y.card := congrArg Finset.card (image_filter_mem _ hYsub)
      _ = n := hYcard
  · refine InConvexPosition.of_image_affineMap π (hπ.mono (Finset.filter_subset _ _)) ?_
    rw [image_filter_mem (π := (π : Point d → Point e)) hYsub]
    exact hYconv

/-- The forcing property transfers from dimension `d + 1` to dimension `d + 2`, provided the
threshold is large enough for the generic projection to exist. -/
theorem forcesConvexSubset_succ {d n N : ℕ} (hN : d + 3 ≤ N)
    (h : ForcesConvexSubset (d + 1) n N) : ForcesConvexSubset (d + 2) n N := by
  intro X hNX hgp
  obtain ⟨π, hinj, himg⟩ := exists_generic_projection hgp (by omega)
  refine containsConvexSubset_of_image π hinj (h _ ?_ himg)
  rw [Finset.card_image_of_injOn hinj]
  exact hNX

/-- Existence of the Erdős–Szekeres number transfers from dimension `d + 1` to `d + 2`. -/
theorem hasErdosSzekeresNumber_succ {d n : ℕ} (h : HasErdosSzekeresNumber (d + 1) n) :
    HasErdosSzekeresNumber (d + 2) n := by
  obtain ⟨N, hN⟩ := h
  exact ⟨max N (d + 3), forcesConvexSubset_succ (le_max_right _ _) (hN.mono (le_max_left _ _))⟩

/-- The Erdős–Szekeres number does not increase with the dimension, up to the additive
constant forced by point sets too small to project generically. -/
theorem erdosSzekeresNumber_succ_le {d n : ℕ} (h : HasErdosSzekeresNumber (d + 1) n) :
    erdosSzekeresNumber (d + 2) n ≤ max (erdosSzekeresNumber (d + 1) n) (d + 3) :=
  erdosSzekeresNumber_le
    (forcesConvexSubset_succ (le_max_right _ _) ((erdosSzekeresNumber_forces h).mono
      (le_max_left _ _)))

/-- The Erdős–Szekeres number exists in every dimension `d ≥ 3`. -/
theorem hasErdosSzekeresNumber_add_three (d n : ℕ) : HasErdosSzekeresNumber (d + 3) n := by
  induction d with
  | zero => exact hasErdosSzekeresNumber_three n
  | succ d ih => exact hasErdosSzekeresNumber_succ (d := d + 2) ih

/-- The Erdős–Szekeres number in dimension `d + 3` is bounded by the three-dimensional one, up
to an additive constant depending only on the dimension. -/
theorem erdosSzekeresNumber_add_three_le (d n : ℕ) :
    erdosSzekeresNumber (d + 3) n ≤ max (erdosSzekeresNumber 3 n) (d + 4) := by
  induction d with
  | zero => exact le_max_left _ _
  | succ d ih =>
    have h : erdosSzekeresNumber (d + 4) n ≤ max (erdosSzekeresNumber (d + 3) n) (d + 5) :=
      erdosSzekeresNumber_succ_le (d := d + 2) (hasErdosSzekeresNumber_add_three d n)
    have hg : erdosSzekeresNumber (d + 1 + 3) n = erdosSzekeresNumber (d + 4) n := rfl
    rw [hg]
    omega

/-- Pohoata–Zakharov in every dimension `d ≥ 3`: `f_d(n) ≤ 2 ^ (o(n))`. -/
theorem erdos_651_subexponential_all_dimensions (d : ℕ) :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber (d + 3)) := by
  intro ε hε
  have htend : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (ε * (n : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (Tendsto.const_mul_atTop hε tendsto_natCast_atTop_atTop)
  filter_upwards [erdos_651_subexponential ε hε, htend.eventually_ge_atTop ((d : ℝ) + 4)]
    with n h3 hc
  have hle : (erdosSzekeresNumber (d + 3) n : ℝ) ≤
      max ((erdosSzekeresNumber 3 n : ℕ) : ℝ) ((d : ℝ) + 4) := by
    exact_mod_cast erdosSzekeresNumber_add_three_le d n
  exact hle.trans (max_le h3 hc)

/-- Erdős's conjectured exponential lower bound fails in every dimension `d ≥ 3`. -/
theorem erdos_651_disproved_all_dimensions (d : ℕ) :
    ¬ Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber (d + 3)) :=
  Erdos651.subexponential_not_exponentialLowerBound (erdos_651_subexponential_all_dimensions d)

end PohoataZakharov

end

/-- Erdős Problem 651: in every dimension `k ≥ 3`, the Erdős--Szekeres number `f_k(n)` has no
exponential lower bound `(1 + c)^n` with `c > 0`. -/
theorem erdos_651 :
    ∀ k : ℕ, 3 ≤ k → ¬ HasExponentialLowerBound (erdosSzekeresNumber k) := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 3 := ⟨k - 3, by omega⟩
  exact PohoataZakharov.erdos_651_disproved_all_dimensions d

#print axioms erdos_651
-- 'Erdos651.erdos_651' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos651
