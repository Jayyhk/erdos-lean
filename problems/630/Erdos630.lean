import Mathlib

namespace Erdos630

/-
# Erdős Problem 630

The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any
assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent
vertices receive distinct colours. Does every planar bipartite graph $G$ have
$\chi_L(G)\leq 3$?

The answer is **yes**, proved by Alon and Tarsi [AlTa92]. `erdos_630` states it for every finite
simple graph with a plane drawing (`PlaneDrawing`: injective vertex positions, continuous simple
edge arcs with the correct endpoints, avoiding other vertices, and with disjoint interiors) and
arbitrary three-element lists from any colour type. Euler's formula and the edge bound for
planar bipartite graphs are proved from the drawing itself.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000511), building
on the orientation and kernel argument of `plby/lean-proofs` (`ErdosProblems/Erdos630.lean`) and
vendoring the plane-topology library `alonamaloh/schoenflies-lean` by Álvaro Begué. The 93
modules forming the closure of `erdos_630` are flattened here in dependency order, with the
upstream `PlanarListColoring` namespace merged into this file's `Erdos630`, and the final
theorem renamed from upstream `planar_bipartite_three_list_colorable_palette`.

Declarations that `erdos_630` does not depend on have been removed.
-/

universe u

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Plane.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The plane, and the compactness toolkit

The plane is `EuclideanSpace ℝ (Fin 2)`. This module fixes that choice, supplies the
orientation form `det` and the right-angle rotation `perp` used to keep track of the two
sides of a polygonal curve, and collects the elementary consequences of compactness and
connectedness that the rest of the development uses without comment.

## Blueprint

* `det`, `perp` — Appendix C, item 1.
* `Plane.notMem_of_mem_segment_of_isMinOn` — Lemma 1.3 (nearest-point segment).
* `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff`
  — Lemma 1.4 (a), (b), (c) (compact separation).
* `Plane.eq_singleton_iInter_of_diam_tendsto_zero` — Lemma 1.6 (nested compact singleton).
* `Plane.connectedComponentIn_eq_of_frontier_disjoint` — Lemma 1.7 (recognizing a component).

Lemma 1.5 (closure and diameter) is `Metric.diam_closure` in Mathlib.
-/

open Metric _root_.Set

namespace Schoenflies

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- Build a point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-! ### The orientation form and the right-angle rotation -/

/-- The orientation form `det (a, b) = a₁b₂ - a₂b₁`. It is positive exactly when `b` lies
counterclockwise of `a`. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- `u` turned counterclockwise through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

@[simp] theorem det_self (a : Plane) : det a a = 0 := by simp [det]; ring

theorem det_comm (a b : Plane) : det a b = -det b a := by simp [det]; ring

@[simp] theorem det_smul_left (r : ℝ) (a b : Plane) : det (r • a) b = r * det a b := by
  simp [det]; ring

@[simp] theorem det_smul_right (r : ℝ) (a b : Plane) : det a (r • b) = r * det a b := by
  simp [det]; ring

theorem det_add_left (a b c : Plane) : det (a + b) c = det a c + det b c := by
  simp [det]; ring

theorem det_add_right (a b c : Plane) : det a (b + c) = det a b + det a c := by
  simp [det]; ring

/-- The defining property of `perp`: it is the counterclockwise right-angle rotation, so it
pairs positively with its argument. -/
@[simp] theorem det_perp_self (u : Plane) : det u (perp u) = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [det, Fin.sum_univ_two]
  ring

theorem inner_eq (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

@[simp] theorem inner_perp_self (u : Plane) : inner ℝ u (perp u) = 0 := by
  rw [inner_eq]; simp; ring

/-- Against `perp` on the right, `det` becomes the inner product. Together with
`det_perp_left` this is what lets the strip lemma trade one for the other. -/
@[simp] theorem det_perp_right (u v : Plane) : det u (perp v) = inner ℝ u v := by
  rw [inner_eq]; simp [det]

@[simp] theorem det_perp_left (u v : Plane) : det (perp u) v = -inner ℝ u v := by
  rw [inner_eq]; simp [det]; ring

@[simp] theorem norm_perp (u : Plane) : ‖perp u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]
  ring

/-- Two vectors are parallel exactly when the orientation form kills them. This is the
angle-free reading of "`u` and `v` point along one line". -/
theorem det_eq_zero_iff_smul (u v : Plane) (hu : u ≠ 0) :
    det u v = 0 ↔ ∃ r : ℝ, v = r • u := by
  constructor
  · intro h
    -- `u ≠ 0` means some coordinate is nonzero; solve for the ratio there.
    have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (by ext i; fin_cases i <;> simp [hc.1, hc.2])
    simp only [det, sub_eq_zero] at h
    rcases hcoord with h0 | h1
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
    · refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
  · rintro ⟨r, rfl⟩
    simp

/-! ### Compactness -/

variable {K L U V : Set Plane} {x a y : Plane}

/-- Lemma 1.3 (nearest-point segment). If `a` is a point of `K` nearest to `x ∉ K`, then the
half-open segment `[x, a)` misses `K`. -/
theorem notMem_of_mem_segment_of_isMinOn (haK : a ∈ K) (hxK : x ∉ K)
    (hmin : ∀ b ∈ K, dist x a ≤ dist x b) (hy : y ∈ segment ℝ x a) (hya : y ≠ a) :
    y ∉ K := by
  intro hyK
  -- `a ≠ x`, since `a ∈ K` and `x ∉ K`, so the segment is nondegenerate.
  have hax : a ≠ x := fun h => hxK (h ▸ haK)
  have hpos : 0 < dist x a := dist_pos.2 (Ne.symm hax)
  -- Write `y = x + t • (a - x)` with `0 ≤ t ≤ 1`; `t = 1` is excluded by `y ≠ a`.
  rw [segment_eq_image' ℝ x a] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exact absurd (by rw [h]; module) hya
  -- Then `dist x y = t * dist x a < dist x a`, contradicting minimality.
  have hdist : dist x (x + t • (a - x)) = t * dist x a := by
    rw [dist_eq_norm, dist_eq_norm]
    have : x - (x + t • (a - x)) = t • (x - a) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have := hmin _ hyK
  rw [hdist] at this
  nlinarith

/-- Lemma 1.4 (a) (compact separation). A compact set inside an open set has a uniform
neighbourhood inside it. Empty `K` is allowed: `thickening ρ ∅ = ∅`. -/
theorem exists_thickening_subset (hK : IsCompact K) (hU : IsOpen U) (h : K ⊆ U) :
    ∃ ρ > 0, thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU h

/-- Lemma 1.4 (b) (compact separation). Two disjoint nonempty compact sets have positive
distance. -/
theorem exists_dist_pos (hK : IsCompact K) (hL : IsCompact L) (hd : Disjoint K L) :
    ∃ ρ > 0, ∀ p ∈ K, ∀ q ∈ L, ρ ≤ dist p q := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hK.exists_thickening_subset_open hL.isClosed.isOpen_compl (disjoint_left.1 hd)
  refine ⟨ρ, hρ, fun p hp q hq => ?_⟩
  by_contra hlt
  exact hsub (mem_thickening_iff.2 ⟨p, hp, by rw [dist_comm]; exact not_le.1 hlt⟩) hq

/-- Lemma 1.7 (recognizing a component). A region inside an open set whose frontier misses that
open set is a connected component of it. -/
theorem connectedComponentIn_eq_of_frontier_disjoint (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hsub : U ⊆ V) (hfr : frontier U ∩ V = ∅) (hx : x ∈ U) :
    connectedComponentIn V x = U := by
  -- `U` is closed in `V`: `closure U ∩ V = (U ∪ ∂U) ∩ V = U`.
  have hclosed : closure U ∩ V ⊆ U := by
    rintro z ⟨hz1, hz2⟩
    by_contra hzU
    have : z ∈ frontier U ∩ V := ⟨by rw [hU.frontier_eq]; exact ⟨hz1, hzU⟩, hz2⟩
    rw [hfr] at this
    exact this
  refine subset_antisymm ?_ (hUconn.subset_connectedComponentIn hx hsub)
  -- The component `C` is covered by the disjoint open sets `U` and `(closure U)ᶜ`, and meets `U`.
  have hcover : connectedComponentIn V x ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure U
    · exact Or.inl (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)
    · exact Or.inr h
  have hmeet : (connectedComponentIn V x ∩ U).Nonempty :=
    ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  have hempty : ¬ (connectedComponentIn V x ∩ (closure U)ᶜ).Nonempty := by
    intro hne
    obtain ⟨z, hz⟩ :=
      isPreconnected_connectedComponentIn U (closure U)ᶜ hU isClosed_closure.isOpen_compl
        hcover hmeet hne
    exact hz.2.2 (subset_closure hz.2.1)
  intro z hz
  by_contra hzU
  exact hempty ⟨z, hz, fun h => hzU (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)⟩

end Plane

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Curve.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open _root_.Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

/-! ### The unit interval, as a subset of `ℝ` -/

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

theorem isCompact_I : IsCompact I := isCompact_Icc

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous. -/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

/-- Running a piece the other way round. -/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Concatenate.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Gluing arcs

Two arcs meeting only at the endpoint they share glue to one arc; two arcs meeting at *both*
of their ends glue to a Jordan curve. The glued parametrisation runs the first arc over the
lower half of the parameter interval and the second over the upper half, each at double
speed: `t ↦ f (2 * t)` below the midpoint and `t ↦ g (2 * t - 1)` above it. Since the
parameter here is an honest real number, that is literally what the definition says.

The halves are `[0, 1/2]` and `[1/2, 1]`. They cover the interval, and each is closed, so
continuity is Mathlib's pasting lemma `ContinuousOn.union_of_isClosed`. Injectivity splits
four ways — both parameters below the midpoint, both above, and the two mixed orders — and
only the mixed cases use the hypothesis that the two arcs meet nowhere else: there the common
value lies on both arcs, hence is the shared endpoint, and each arc's own injectivity pins
its parameter to the midpoint.

At the midpoint itself both branches of the `if` are meaningful and they agree, precisely
because the first arc finishes where the second starts. That is what makes the glued map well
defined rather than merely continuous, and it is why `concatenate_upperHalf` — the statement
that the glued map *is* the retimed second arc on the whole closed upper half, midpoint
included — carries the shared-endpoint hypothesis.

For the loop the seam analysis gains a second legitimate meeting point: besides the middle,
where the arcs are glued, there are the outer ends, where the loop is allowed to repeat
itself. Pinning those needs the start/finish counterparts of the midpoint lemmas.

## Blueprint

* `concatenate` — §1, the glued parametrisation.
* `IsArc.concatenate`, `IsArcBetween.concatenate` — two arcs meeting only at the endpoint they
  share glue to an arc.
* `IsLoop.concatenate` — two arcs glued along both of their ends make a loop.
* `IsJordanCurve.of_two_arcs` — two arcs meeting exactly at their two shared endpoints make a
  Jordan curve; the converse of the two-arcs decomposition, and the form every *construction*
  of a curve takes.
-/

open _root_.Set unitInterval

namespace Schoenflies

/-! ### The two halves of the parameter interval -/

/-- The lower half of the parameter interval, where the first arc runs. -/
def lowerHalf : Set ℝ := Icc 0 (1 / 2)

/-- The upper half of the parameter interval, where the second arc runs. The two halves
overlap in the midpoint: that is the seam. -/
def upperHalf : Set ℝ := Icc (1 / 2) 1

theorem halves_union : lowerHalf ∪ upperHalf = I :=
  Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_Icc

theorem isClosed_upperHalf : IsClosed upperHalf := isClosed_Icc

/-- Doubling a parameter below the midpoint reaches at most one. -/
theorem double_mem_I {t : ℝ} (ht : t ∈ lowerHalf) : 2 * t ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Doubling a parameter above the midpoint and stepping back reaches at least zero. -/
theorem doubleBack_mem_I {t : ℝ} (ht : t ∈ upperHalf) : 2 * t - 1 ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### The glued parametrisation -/

/-- Run `f` over the lower half of the interval and `g` over the upper half, each at double
speed. -/
noncomputable def concatenate (f g : ℝ → Plane) : ℝ → Plane :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

variable {f g : ℝ → Plane}

theorem concatenate_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concatenate f g t = f (2 * t) :=
  if_pos ht

theorem concatenate_of_not_le {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    concatenate f g t = g (2 * t - 1) :=
  if_neg ht

theorem concatenate_zero : concatenate f g 0 = f 0 := by
  rw [concatenate_of_le (by norm_num)]
  norm_num

theorem concatenate_one : concatenate f g 1 = g 1 := by
  rw [concatenate_of_not_le (by norm_num)]
  norm_num

/-- On the *closed* upper half the glued map is the retimed second arc — at the midpoint
included, where the `if` still takes the first branch. The two branches agree there only
because the first arc finishes where the second starts, which is what makes the glued map
well defined. -/
theorem concatenate_upperHalf (hmid : f 1 = g 0) {t : ℝ} (ht : t ∈ upperHalf) :
    concatenate f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · -- The only parameter of the upper half below the midpoint is the midpoint.
    have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    rw [concatenate_of_le h]
    norm_num
    exact hmid
  · exact concatenate_of_not_le h

/-! ### Continuity -/

/-- Continuity of the glued map: each half carries a composition, and the halves are closed
and cover. -/
theorem continuousOn_concatenate (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hmid : f 1 = g 0) : ContinuousOn (concatenate f g) I := by
  rw [← halves_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_lowerHalf isClosed_upperHalf
  · -- On the lower half the glued map is `f` doubled.
    have h : ContinuousOn (fun t : ℝ => f (2 * t)) lowerHalf :=
      hf.comp (by fun_prop) fun t ht => double_mem_I ht
    exact h.congr fun t ht => concatenate_of_le ht.2
  · -- On the upper half it is `g`, doubled and stepped back.
    have h : ContinuousOn (fun t : ℝ => g (2 * t - 1)) upperHalf :=
      hg.comp (by fun_prop) fun t ht => doubleBack_mem_I ht
    exact h.congr fun t ht => concatenate_upperHalf hmid ht

/-! ### Pinning a parameter at the seam

At a point where two of the pieces meet, the value is one of the shared points, and the
injectivity of the arc it belongs to pins the parameter. Each half needs its own statement,
since they retime differently; the loop needs the outer ends as well as the middle. -/

theorem lowerHalf_at_finish (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 1) : t = 1 / 2 := by
  have := hfi (double_mem_I ht) one_mem_I h
  linarith

theorem upperHalf_at_start (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 0) : t = 1 / 2 := by
  have := hgi (doubleBack_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_finish (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 1) : t = 1 := by
  have := hgi (doubleBack_mem_I ht) one_mem_I h
  linarith

/-! ### Injectivity -/

/-- Across the seam: the common value lies on both arcs, so it is the shared endpoint, and
each half's injectivity pins its own parameter to the midpoint. Stated for a parameter of
each half rather than for `x` and `y`, so that the two orderings of the case split are the
same theorem. -/
theorem concatenate_seam (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩
  have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs meeting only at the endpoint they share glue to an injective map. -/
theorem injOn_concatenate (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) : InjOn (concatenate f g) I := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · -- Both parameters run the first arc: its own injectivity, doubled.
      rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
      have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenate_seam hfi hgi hmid hmeet ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenate_seam hfi hgi hmid hmeet ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · -- Both run the second arc.
      rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
      have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2⟩) (doubleBack_mem_I ⟨hyg.le, hy.2⟩) h
      linarith

/-! ### What the glued map covers -/

/-- Each half retimes *onto* the whole interval, so the glued map's image is exactly the two
arcs together. -/
theorem image_concatenate (hmid : f 1 = g 0) : concatenate f g '' I = f '' I ∪ g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_I ⟨ht.1, h⟩, (concatenate_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_I ⟨h.le, ht.2⟩,
        (concatenate_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · -- Half a parameter is the one that doubles to it.
      refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

/-! ### The set-level gluing theorems

This is the form the rest of the development speaks: a piece is an arc between two named
points, the parametrisations are chosen inside the proofs and never seen again. -/

/-- Two pieces meeting only at the point where they are joined make one piece. -/
theorem IsArcBetween.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) :
    IsArcBetween (A ∪ B) a c := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf1]
    exact hmeet z hz hz'
  refine ⟨_, continuousOn_concatenate hfc hgc hmid, injOn_concatenate hfi hgi hmid hmeet',
    ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim]
  · rw [concatenate_zero]; exact hf0
  · rw [concatenate_one]; exact hg1

/-! ### Closing the loop

Two arcs that share *both* of their ends — the second runs back from where the first arrived
to where it set out — glue to a loop rather than to an arc. Everything above carries over
except the seam analysis: a common value now has two ways to be legitimate, at the middle
where the arcs are glued and at the outer ends where the loop closes, and the second of those
is exactly the repetition `IsLoop` allows itself at the finish. -/

/-- Across the seam, when the two arcs also share their outer ends. At the middle the
argument is the one for arcs; at the outer ends the second arc is at its finish, so its
parameter is `1` — which the hypothesis has excluded. -/
theorem concatenate_seam_loop (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf) (hy1 : y ≠ 1)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  rcases hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩ with
    hz | hz
  · -- The value is where the loop closes: the second arc is at its finish, so `y = 1`.
    exact absurd (upperHalf_at_finish hgi hy (by rw [← h, hz]; exact hclose.symm)) hy1
  · have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
    rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs glued along both of their ends make a loop. -/
theorem IsLoop.concatenate (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I)
    (hgi : InjOn g I) (hmid : f 1 = g 0) (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) :
    IsLoop (Schoenflies.concatenate f g) where
  continuousOn := continuousOn_concatenate hfc hgc hmid
  closes := by rw [concatenate_zero, concatenate_one]; exact hclose.symm
  injOn := by
    intro x hx y hy h
    have hy1 : y ≠ 1 := ne_of_lt hy.2
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    rcases le_or_gt x (1 / 2) with hxl | hxg
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
        have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
        linarith
      · exact concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hx.1, hxl⟩
          ⟨hyg.le, hy.2.le⟩ hy1 h
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · exact (concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hy.1, hyl⟩
          ⟨hxg.le, hx.2.le⟩ hx1 h.symm).symm
      · rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
        have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2.le⟩)
          (doubleBack_mem_I ⟨hyg.le, hy.2.le⟩) h
        linarith

/-- Two pieces meeting exactly at their two shared endpoints make a Jordan curve. This is the
converse of the two-arcs decomposition, and the form every construction of a curve takes: a
cycle of a plane graph arrives as a path and one more edge back to where it started. -/
theorem IsJordanCurve.of_two_arcs {A B : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b a) (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    IsJordanCurve (A ∪ B) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨_, IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_⟩
  rw [image_concatenate hmid, hfim, hgim]

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Walk.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

/-! ### The vertices an edge list touches -/

open _root_.Graph in
/-- The vertices lying on at least one edge of `W`. -/
def _root_.Graph.coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

open _root_.Graph in
/-- The vertices a walk from `u` along `W` visits: its source, plus the ends of every edge it
takes. Defined for any edge list, not just for one that walks — the freshness clause of a
path reads it about the *rest* of the path before that rest is known to be a walk at all. -/
def _root_.Graph.walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := insert u (G.coveredVertices W)

open _root_.Graph in
theorem _root_.Graph.mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

open _root_.Graph in
theorem _root_.Graph.mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

open _root_.Graph in
@[simp]
theorem _root_.Graph.coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

open _root_.Graph in
@[simp]
theorem _root_.Graph.walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

open _root_.Graph in
theorem _root_.Graph.mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

open _root_.Graph in
theorem _root_.Graph.mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

open _root_.Graph in
theorem _root_.Graph.coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

open _root_.Graph in
theorem _root_.Graph.walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

open _root_.Graph in
@[simp]
theorem _root_.Graph.coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

open _root_.Graph in
@[simp]
theorem _root_.Graph.walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

open _root_.Graph in
theorem _root_.Graph.coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

open _root_.Graph in
/-- Every vertex on an edge of the graph is a vertex of the graph. -/
theorem _root_.Graph.coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

open _root_.Graph in
theorem _root_.Graph.walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

open _root_.Graph in
/-- Moving the visited set across a first step, forwards: a vertex the walk visits is either
the vertex it departs from or a vertex the rest of it visits. This is where the step lemma is
used — the edge `e` has only the two ends `u` and `w`, so a vertex on `e` is one of them. -/
theorem _root_.Graph.mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

open _root_.Graph in
/-- Moving the visited set across a first step, backwards. -/
theorem _root_.Graph.mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

/-! ### Walks -/

open _root_.Graph in
/-- `G.IsWalk u W v` : the edges of `W`, in order, walk from `u` to `v` in `G`. Each edge is
taken from the vertex the previous one arrived at; the list is read at its head, so the
relation is built at the source end. -/
inductive _root_.Graph.IsWalk (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a walk. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsWalk x [] x
  /-- Taking an edge from the source of a walk prepends it. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsWalk w W v) :
      G.IsWalk u (e :: W) v

open _root_.Graph in
theorem _root_.Graph.IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

open _root_.Graph in
theorem _root_.Graph.IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

open _root_.Graph in
theorem _root_.Graph.IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

open _root_.Graph in
/-- The edges of a walk are edges of the graph. -/
theorem _root_.Graph.IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

open _root_.Graph in
theorem _root_.Graph.IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

open _root_.Graph in
/-- Every vertex a walk visits is a vertex of the graph — with no hypothesis, since the
empty walk already stands at one. -/
theorem _root_.Graph.IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

open _root_.Graph in
@[simp]
theorem _root_.Graph.isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

open _root_.Graph in
theorem _root_.Graph.IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

open _root_.Graph in
/-- Walks concatenate, with no side condition. -/
theorem _root_.Graph.IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

open _root_.Graph in
/-- A walk runs backwards along the reverse of its edge list, with no side condition. -/
theorem _root_.Graph.IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

open _root_.Graph in
/-- A walk in a subgraph is a walk in the graph. -/
theorem _root_.Graph.IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

open _root_.Graph in
/-- A walk of a graph whose edges all survive into a subgraph is a walk of that subgraph.
This is the direction a deletion argument needs: an edge is removed, and a walk that never
used it is still there. -/
theorem _root_.Graph.IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

open _root_.Graph in
/-- A walk that starts inside a set of vertices and ends outside it crosses the boundary
along one of its own edges. -/
theorem _root_.Graph.IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

/-! ### Paths -/

open _root_.Graph in
/-- `G.IsPath u W v` : a walk from `u` to `v` that never returns to a vertex it has left.
The condition is carried step by step — the vertex a step departs from is not among those the
rest of the path visits — rather than imposed afterwards on a computed vertex list. -/
inductive _root_.Graph.IsPath (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a path. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsPath x [] x
  /-- A step onto a path is allowed when the vertex it departs from is fresh. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsPath w W v)
      (hfresh : u ∉ G.walkVertices w W) : G.IsPath u (e :: W) v

open _root_.Graph in
theorem _root_.Graph.IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

open _root_.Graph in
theorem _root_.Graph.IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

open _root_.Graph in
theorem _root_.Graph.IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

open _root_.Graph in
/-- One edge between two distinct vertices is a path. -/
theorem _root_.Graph.IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

open _root_.Graph in
/-- A path's step never departs from where it arrives: the freshness clause already says so,
because a walk always visits its own source. -/
theorem _root_.Graph.IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

open _root_.Graph in
/-- **A path never takes a loop.** This is why nothing in this file has to assume the graph is
loopless: a step along a loop would depart from the vertex it arrives at, which the freshness
clause forbids. -/
theorem _root_.Graph.IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      -- `hloop : G.IsLink e x x` shares an edge with `hl : G.IsLink e u w`, so `u = w`.
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

open _root_.Graph in
/-- A path takes no edge twice: an edge it took again would put the vertex it departed from
back among the ones the rest of the path visits. -/
theorem _root_.Graph.IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

open _root_.Graph in
/-- A path in a subgraph is a path in the graph: the freshness clause reads only which
vertices the remaining edges touch, and a subgraph's edges have the same ends there. -/
theorem _root_.Graph.IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    -- Freshness travels because `H`'s edges link the same pairs in `G`.
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

open _root_.Graph in
theorem _root_.Graph.IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

open _root_.Graph in
/-- A path grows at its **target** end. The relation is built at the source end, so this is
the direction that has to be worked for; it is what reversal runs on. -/
theorem _root_.Graph.IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    -- The departure vertex is still fresh: the only new edge is `e`, whose ends are the old
    -- target `w` — already visited — and `v`, which the source is not.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

open _root_.Graph in
/-- A path runs backwards over the same edges. -/
theorem _root_.Graph.IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    -- `u` avoids everything the rest of the path visits, and reversal changes none of that.
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

open _root_.Graph in
/-- **Cutting a path at a vertex it passes through.** A path through `x` has a piece of itself
running from `x` to its target, and that piece uses only the path's own edges. This is the
engine of `Graph.IsWalk.contains_path`: when the next vertex is already on the path built so
far, the path is cut there instead of extended, so nothing ever gets longer. -/
theorem _root_.Graph.IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

open _root_.Graph in
/-- A path splits at any vertex it visits, and the far half never returns to the source.
`Graph.IsPath.from_visited` is the suffix alone; the prefix is the awkward half, since the
relation is built at the source end and the prefix is what the induction has to carry
forward. -/
theorem _root_.Graph.IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    -- The far half's edges are among the rest, which the source already avoided.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

open _root_.Graph in
/-- **Every walk contains a path** between the same two vertices, using only the walk's own
edges. This is the blueprint's "shorten an arbitrary walk at repeated vertices"; the
induction never lengthens anything, because the only alternative to prepending an edge is to
cut the path already built (`Graph.IsPath.from_visited`). -/
theorem _root_.Graph.IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · -- The step lands on the path already built: cut it there rather than extend it.
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

/-! ### Reachability -/

open _root_.Graph in
/-- `G.Reaches u v` : some walk of `G` runs from `u` to `v`. Stated with a walk rather than a
path because walks are what arguments build — they concatenate and reverse with no side
condition — and a path is recovered on demand (`Graph.Reaches.exists_isPath`). -/
def _root_.Graph.Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

open _root_.Graph in
theorem _root_.Graph.Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

open _root_.Graph in
@[refl]
theorem _root_.Graph.Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

open _root_.Graph in
theorem _root_.Graph.Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

open _root_.Graph in
theorem _root_.Graph.Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

open _root_.Graph in
theorem _root_.Graph.Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

open _root_.Graph in
/-- Whatever a walk reaches, a path reaches. -/
theorem _root_.Graph.Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

open _root_.Graph in
theorem _root_.Graph.Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

/-! ### Connectedness -/

open _root_.Graph in
/-- A graph is connected when it has a vertex and every vertex reaches every other. The
nonemptiness clause is not bureaucracy: it is what makes the counting statements about trees
true as stated. -/
def _root_.Graph.Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

open _root_.Graph in
theorem _root_.Graph.Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

open _root_.Graph in
/-- A graph is connected as soon as one vertex reaches all the others: reachability is
symmetric and transitive, so a common hub joins every pair. -/
theorem _root_.Graph.Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

open _root_.Graph in
theorem _root_.Graph.coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

open _root_.Graph in
theorem _root_.Graph.walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

open _root_.Graph in
/-- A path of a graph whose edges all survive into a subgraph is a path of that subgraph —
the companion of `Graph.IsWalk.anti`, which it is otherwise identical to. Freshness comes
down the inclusion because the subgraph's edges touch no vertices the graph's do not. -/
theorem _root_.Graph.IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Cycle.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

/-! ### Cycles -/

open _root_.Graph in
/-- `G.IsCycleThrough e u v D` : the edge `e` links `u` to `v`, and `D` is a path from `u`
back to `v` that does not use `e`. The cycle is `e` together with `D`; it is presented
through `e` because that is the edge every question is asked about. -/
def _root_.Graph.IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-! ### Acyclicity -/

/-! ### Bridges -/

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Topology.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Topology of the plane: the gaps Mathlib leaves

Appendix C of the blueprint lists the topology imported without proof. Almost all of it is in
Mathlib: compactness and Heine–Borel, the compact-to-Hausdorff homeomorphism criterion,
connectedness and its stability under images, unions through a common point, adjoining closure
points (`IsPreconnected.subset_closure`), a connected set inside a disjoint union of two opens
(`IsPreconnected.subset_left_of_subset_union`), `Metric.diam_closure`, thickenings, and the
two-piece pasting lemma (`continuousOn_union_iff_of_isClosed`).

This module collects the few that are not stated in the form the development uses.

## Blueprint

* `isOpen_connectedComponentIn` — Appendix C item 4: components of open subsets of the plane
  are open. The plane is locally connected, so this is Mathlib's, restated at `Plane` so that
  the instance is found once here rather than at every call site.
* `frontier_connectedComponentIn_compl_subset` — Appendix C item 5: the boundary of a component
  of the complement of a closed set lies in that closed set. This is the form Part I uses to
  recognize that a region's frontier sits on the curve.
* `continuousOn_union_of_isClosed` — Appendix C item 6, the pasting lemma, in the two-piece
  form the development pastes with.
-/

open Metric _root_.Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

/-- Components of an open subset of the plane are open. The plane is locally connected. -/
theorem isOpen_connectedComponentIn (hU : IsOpen U) : IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

/-- Appendix C item 5. The frontier of a component of the complement of a closed set lies in
that closed set.

A frontier point off `K` would be a point of the open set `Kᶜ` in the closure of the
component; adjoining it keeps the component connected, so it was in the component already. -/
theorem frontier_connectedComponentIn_compl_subset (hK : IsClosed K) (x : Plane) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCopen : IsOpen C := isOpen_connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  -- `z` is a frontier point of the open set `C`, so it lies in `closure C` but not in `C`.
  rw [hCopen.frontier_eq] at hz
  obtain ⟨hzclosure, hzC⟩ := hz
  -- `C` is nonempty, since it has a frontier point in its closure.
  have hxU : x ∈ Kᶜ := by
    by_contra hx
    rw [hC, connectedComponentIn_eq_empty hx] at hzclosure
    simp at hzclosure
  -- Adjoining `z` keeps it connected and inside `Kᶜ`, so `z` was in the component already.
  have hsub : C ∪ {z} ⊆ Kᶜ := by
    refine union_subset (connectedComponentIn_subset _ _) ?_
    simpa using hzK
  have hconn : IsPreconnected (C ∪ {z}) :=
    (isPreconnected_connectedComponentIn (F := Kᶜ) (x := x)).subset_closure
      subset_union_left (union_subset subset_closure (by simpa using hzclosure))
  have : C ∪ {z} ⊆ C :=
    hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU)) hsub
  exact hzC (this (Or.inr rfl))

end Plane

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Square.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The sup metric and axis-parallel squares

The blueprint takes the Euclidean norm as primary and uses the sup norm for the
axis-parallel objects the polygonal work is built on: grids of small squares, the vertex
squares of the redrawing argument, and the large square a bounded set is caught inside.
Appendix C item 1 asks for the comparison `‖x‖∞ ≤ ‖x‖ ≤ √2 ‖x‖∞`, which is `supNorm_le_norm`
and `norm_le_sqrt_two_mul_supNorm` here.

The one theorem of substance is `isConnected_beyondSquare`: the plane outside a closed
square is connected. It is a *square* and not a disk on purpose — the outside of a square is
exactly a union of four half-planes, each convex, with consecutive ones sharing a point,
whereas the outside of a disk would need the polar decomposition this development withholds.

## Blueprint

* `supNorm`, `supDist` — Appendix C, item 1 (the sup metric).
* `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` — the comparison, used without comment.
* `closedSquare`, `openSquare` — the axis-parallel square about a point.
* `isConnected_beyondSquare` — the outside of a square is connected; what makes exactly one
  face of a plane graph unbounded.
-/

open Metric _root_.Set

namespace Schoenflies

namespace Plane

/-! ### Coordinates -/

theorem sub_apply (x y : Plane) (i : Fin 2) : (x - y) i = x i - y i := rfl

theorem smul_add_apply (a b : ℝ) (x y : Plane) (i : Fin 2) :
    (a • x + b • y) i = a * x i + b * y i := by simp

theorem continuous_coord (i : Fin 2) : Continuous fun x : Plane => x i :=
  PiLp.continuous_apply _ _ i

/-! ### The sup norm -/

/-- The sup norm `‖x‖∞ = max |x₁| |x₂|`. -/
noncomputable def supNorm (x : Plane) : ℝ := max |x 0| |x 1|

/-- The sup distance. -/
noncomputable def supDist (x y : Plane) : ℝ := supNorm (x - y)

theorem supNorm_nonneg (x : Plane) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem supDist_nonneg (x y : Plane) : 0 ≤ supDist x y := supNorm_nonneg _

@[simp] theorem supDist_self (x : Plane) : supDist x x = 0 := by
  simp [supDist, supNorm]

theorem supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  simp only [supDist, supNorm, sub_apply]
  rw [abs_sub_comm (x 0) (y 0), abs_sub_comm (x 1) (y 1)]

theorem abs_sub_zero_le_supDist (x y : Plane) : |x 0 - y 0| ≤ supDist x y :=
  le_max_left _ _

theorem abs_sub_one_le_supDist (x y : Plane) : |x 1 - y 1| ≤ supDist x y :=
  le_max_right _ _

theorem abs_zero_le_supNorm (x : Plane) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : Plane) : |x 1| ≤ supNorm x := le_max_right _ _

/-- The sup distance satisfies the triangle inequality, one coordinate at a time. -/
theorem supDist_triangle (x y z : Plane) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_zero_le_supDist x y) (abs_sub_zero_le_supDist y z)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_one_le_supDist x y) (abs_sub_one_le_supDist y z)

theorem norm_sq_eq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- Half of Appendix C item 1's comparison: the sup norm is at most the Euclidean norm. -/
theorem supNorm_le_norm (x : Plane) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

/-- The other half: the Euclidean norm is at most `√2` times the sup norm. -/
theorem norm_le_sqrt_two_mul_supNorm (x : Plane) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

/-! ### Coordinate half-planes

One convexity proof per direction serves all four sides of a square, and the outside of a
square is four of them. -/

theorem convex_coord_le (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_ge (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r ≤ x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_lt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i < r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem convex_coord_gt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r < x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem isOpen_coord_lt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | x i < r} :=
  isOpen_lt (continuous_coord i) continuous_const

theorem isOpen_coord_gt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | r < x i} :=
  isOpen_lt continuous_const (continuous_coord i)

/-! ### Axis-parallel squares -/

/-- The closed axis-parallel square of radius `r` about `c`. -/
def closedSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c ≤ r}

/-- The open axis-parallel square of radius `r` about `c`. -/
def openSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c < r}

theorem closedSquare_eq_inter (c : Plane) (r : ℝ) :
    closedSquare c r =
      ({x : Plane | c 0 - r ≤ x 0} ∩ {x : Plane | x 0 ≤ c 0 + r}) ∩
      ({x : Plane | c 1 - r ≤ x 1} ∩ {x : Plane | x 1 ≤ c 1 + r}) := by
  ext x
  simp only [closedSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem openSquare_eq_inter (c : Plane) (r : ℝ) :
    openSquare c r =
      ({x : Plane | c 0 - r < x 0} ∩ {x : Plane | x 0 < c 0 + r}) ∩
      ({x : Plane | c 1 - r < x 1} ∩ {x : Plane | x 1 < c 1 + r}) := by
  ext x
  simp only [openSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_lt_iff, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem convex_closedSquare (c : Plane) (r : ℝ) : Convex ℝ (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((convex_coord_ge 0 _).inter (convex_coord_le 0 _)).inter
    ((convex_coord_ge 1 _).inter (convex_coord_le 1 _))

theorem convex_openSquare (c : Plane) (r : ℝ) : Convex ℝ (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter
    ((convex_coord_gt 1 _).inter (convex_coord_lt 1 _))

theorem isOpen_openSquare (c : Plane) (r : ℝ) : IsOpen (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter
    ((isOpen_coord_gt 1 _).inter (isOpen_coord_lt 1 _))

theorem isClosed_closedSquare (c : Plane) (r : ℝ) : IsClosed (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((isClosed_le continuous_const (continuous_coord 0)).inter
      (isClosed_le (continuous_coord 0) continuous_const)).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

/-! ### The outside of a square -/

/-- The plane outside the closed square of radius `r` about the origin. -/
def beyondSquare (r : ℝ) : Set Plane := {x | r < |x 0| ∨ r < |x 1|}

/-- The outside of a square is connected.

Four half-planes, each convex and hence connected, with consecutive ones sharing a corner.
No polar decomposition, and no arbitrary union of connected sets. The radius needs no sign
condition: for `r < 0` the four half-planes already cover the plane. -/
theorem isConnected_beyondSquare (r : ℝ) : IsConnected (beyondSquare r) := by
  set R : Set Plane := {x : Plane | r < x 0} with hR
  set L : Set Plane := {x : Plane | x 0 < -r} with hL
  set T : Set Plane := {x : Plane | r < x 1} with hT
  set B : Set Plane := {x : Plane | x 1 < -r} with hB
  have hcover : beyondSquare r = R ∪ T ∪ L ∪ B := by
    ext x
    simp only [beyondSquare, hR, hL, hT, hB, mem_setOf_eq, mem_union, lt_abs]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (by linarith)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  -- Consecutive sides share a corner. Membership unfolds definitionally, so `show` states
  -- the inequality the corner satisfies and `linarith` closes it.
  have hRT : mk (r + 1) (r + 1) ∈ R ∩ T :=
    ⟨show r < r + 1 by linarith, show r < r + 1 by linarith⟩
  have hTL : mk (-r - 1) (r + 1) ∈ T ∩ L :=
    ⟨show r < r + 1 by linarith, show -r - 1 < -r by linarith⟩
  have hLB : mk (-r - 1) (-r - 1) ∈ L ∩ B :=
    ⟨show -r - 1 < -r by linarith, show -r - 1 < -r by linarith⟩
  have cR : IsConnected R :=
    (convex_coord_gt 0 r).isConnected ⟨mk (r + 1) 0, show r < r + 1 by linarith⟩
  have cL : IsConnected L :=
    (convex_coord_lt 0 (-r)).isConnected ⟨mk (-r - 1) 0, show -r - 1 < -r by linarith⟩
  have cT : IsConnected T :=
    (convex_coord_gt 1 r).isConnected ⟨mk 0 (r + 1), show r < r + 1 by linarith⟩
  have cB : IsConnected B :=
    (convex_coord_lt 1 (-r)).isConnected ⟨mk 0 (-r - 1), show -r - 1 < -r by linarith⟩
  have c1 : IsConnected (R ∪ T) := cR.union ⟨mk (r + 1) (r + 1), hRT.1, hRT.2⟩ cT
  have c2 : IsConnected (R ∪ T ∪ L) :=
    c1.union ⟨mk (-r - 1) (r + 1), Or.inr hTL.1, hTL.2⟩ cL
  have c3 : IsConnected (R ∪ T ∪ L ∪ B) :=
    c2.union ⟨mk (-r - 1) (-r - 1), Or.inr hLB.1, hLB.2⟩ cB
  rw [hcover]
  exact c3

end Plane

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Bounded.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Catching a bounded set inside a square

The outer face of a plane graph is found by catching the whole drawing — finitely many points
and finitely many compact arcs — inside one axis-parallel square, and then observing that the
outside of that square is connected (`isConnected_beyondSquare`) and therefore lies in a single
face. This module is the "catching" half.

The key identity is `beyondSquare_eq_compl`: the outside of a square, as defined by a
coordinate inequality, *is* the complement of the closed square. It is what lets the
connectedness theorem be applied to a complement.

## Blueprint

* `beyondSquare_eq_compl` — the outside of a square is the complement of the closed square.
* `exists_closedSquare_of_isBounded`, `IsCompact.exists_closedSquare` — a bounded set is caught
  inside a square about the origin.
* `isOpen_compl_of_finite_isCompact` — the complement of a finite union of compact sets is
  open; the exterior of a plane graph is open for this reason.
-/

open Metric _root_.Set

namespace Schoenflies

namespace Plane

@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

/-- The outside of a square is exactly the complement of the closed square. -/
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, mem_setOf_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

/-- A bounded set sits inside a closed square about the origin, of nonnegative radius. -/
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

end Plane

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Degree.lean` -/

/-!
# Degree and the handshake lemma

Degree counting on Mathlib's multigraph `Graph α β`, for graphs with finitely many vertices
and finitely many edges.

## Carrying finiteness

`V(G)` and `E(G)` are `Set α` and `Set β`, not types, so finiteness has to be carried
somehow. The choice made here — and inherited by every later graph module — is a
`Prop`-valued class

```
class Graph.Finite (G : Graph α β) : Prop
```

bundling `V(G).Finite` and `E(G).Finite`, with `G.vertexFinset` and `G.edgeFinset` derived
from it. The reasons:

* It is a `Prop`, so it is proof irrelevant. `G.vertexFinset` and `G.degree` therefore do not
  depend on *which* finiteness proof is in scope, and two lemmas proved with different
  instances still compose. A bundled `Finset`-valued structure would not have that property:
  it duplicates the `vertexSet` data and forces a `↑G.vertexFinset = V(G)` side condition at
  every call site.
* It is a class, so it is silent at the call site — the statements below read like ordinary
  graph theory instead of dragging two `Set.Finite` hypotheses through every signature. The
  price is that a subgraph does not get an instance for free; `Graph.Finite.of_le` produces
  one, and `haveI` installs it locally. That is the right trade: in this development
  finiteness is a standing assumption on the ambient graph and subgraphs are formed
  constantly.
* `Finite ↥V(G)` and `Finite ↥E(G)` instances are provided too, so Mathlib's own machinery
  (`Set.Finite.subset`, `Set.toFinite`, ...) fires without help.

Counts are `Set.ncard`. `Set.ncard` is total — it is `0` on an infinite set — so `G.degree`
is defined for every graph and needs no instance argument; finiteness enters only where a
theorem actually needs it.

## Degree

`G.degree x` is the number of *edge ends* at `x`:

```
G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard
```

A non-loop edge at `x` is counted once, by the first summand. A loop at `x` is counted
twice, once by each summand. This is the definition the handshake lemma needs, and it agrees
with `SimpleGraph.degree` on loopless graphs.

## Blueprint

* `Graph.sum_degree_eq_two_mul_ncard_edgeSet` — "the degree sum is twice the number of
  edges", the counting step in the proof of Lemma `lem:three-leaf-tree` (Trees with three
  leaves). The whole content is `Graph.ncard_inc_add_ncard_isLoopAt`: an edge has exactly two
  ends.
* `Graph.IsLeaf` — "the vertices of degree one are the leaves", same lemma.

## Namespace

Everything lives in the root `Graph` namespace rather than in `Schoenflies`, so that dot
notation `G.degree`, `G.IsLeaf`, `G.vertexFinset` works on a `G : Graph α β`. Later graph
modules should do the same.
-/

section
variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-! ### Finiteness -/

open _root_.Graph in
/-- `G.Finite` says that the multigraph `G` has finitely many vertices and finitely many
edges. Both halves are needed: the vertex set does not bound the edge set (parallel edges)
and the edge set does not bound the vertex set (isolated vertices). -/
class _root_.Graph.Finite (G : Graph α β) : Prop where
  /-- A finite graph has finitely many vertices. -/
  finite_vertexSet : V(G).Finite
  /-- A finite graph has finitely many edges. -/
  finite_edgeSet : E(G).Finite

open _root_.Graph in
theorem _root_.Graph.finite_vertexSet (G : Graph α β) [G.Finite] : V(G).Finite := Finite.finite_vertexSet

open _root_.Graph in
theorem _root_.Graph.finite_edgeSet (G : Graph α β) [G.Finite] : E(G).Finite := Finite.finite_edgeSet

open _root_.Graph in
/-- A subgraph of a finite graph is finite. This is not an instance — `H` cannot be
recovered from the goal — so install it with `haveI := Graph.Finite.of_le h`. -/
theorem _root_.Graph.Finite.of_le (h : H ≤ G) [G.Finite] : H.Finite :=
  ⟨(_root_.Graph.finite_vertexSet G).subset h.vertexSet_mono,
   (_root_.Graph.finite_edgeSet G).subset h.edgeSet_mono⟩

open _root_.Graph in
/-- The edge set of a finite graph, as a `Finset`. -/
noncomputable def _root_.Graph.edgeFinset (G : Graph α β) [G.Finite] : Finset β :=
  (finite_edgeSet G).toFinset

open _root_.Graph in
@[simp]
theorem _root_.Graph.mem_edgeFinset [G.Finite] : e ∈ G.edgeFinset ↔ e ∈ E(G) :=
  Set.Finite.mem_toFinset _

open _root_.Graph in
@[simp, norm_cast]
theorem _root_.Graph.coe_edgeFinset [G.Finite] : (G.edgeFinset : Set β) = E(G) :=
  Set.Finite.coe_toFinset _

open _root_.Graph in
@[simp]
theorem _root_.Graph.card_edgeFinset [G.Finite] : G.edgeFinset.card = E(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-! ### Incidence sets, unfolded -/

/-! ### Degree -/

/-! ### An edge has exactly two ends

This is the entire content of the handshake lemma: summed over the vertices, the number of
ends an edge has there is two, whether the edge is a loop (two ends at one vertex) or not
(one end at each of two vertices).
-/

/-! ### The handshake lemma -/

/-! ### Leaves -/

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Drawing.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open Metric _root_.Set Schoenflies unitInterval
section
variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

open _root_.Graph in
/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def _root_.Graph.edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

open _root_.Graph in
/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure _root_.Graph.IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

open _root_.Graph in
/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses. -/
theorem _root_.Graph.IsDrawing.edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

open _root_.Graph in
theorem _root_.Graph.IsDrawing.isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

open _root_.Graph in
theorem _root_.Graph.IsDrawing.isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

open _root_.Graph in
/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices". -/
theorem _root_.Graph.IsDrawing.arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

/-! ### What a plane graph occupies -/

open _root_.Graph in
/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def _root_.Graph.pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

open _root_.Graph in
theorem _root_.Graph.vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := subset_union_left

open _root_.Graph in
theorem _root_.Graph.edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  subset_union_of_subset_right (subset_biUnion_of_mem he) _

open _root_.Graph in
/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs. -/
theorem _root_.Graph.IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

open _root_.Graph in
theorem _root_.Graph.IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

open _root_.Graph in
/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def _root_.Graph.exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

open _root_.Graph in
theorem _root_.Graph.IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

open _root_.Graph in
/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def _root_.Graph.face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

open _root_.Graph in
theorem _root_.Graph.face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

open _root_.Graph in
theorem _root_.Graph.mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

open _root_.Graph in
theorem _root_.Graph.IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

open _root_.Graph in
/-- Faces partition the exterior: two faces either coincide or are disjoint. -/
theorem _root_.Graph.face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolyPath.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric _root_.Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

@[simp] theorem poly_nil : poly [] = ∅ := rfl

@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

/-- Every vertex lies on the carrier. -/
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex. -/
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment. -/
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

/-- Concatenating two vertex lists that agree at the join concatenates their carriers. The
hypothesis is what makes this true: without it `poly [a] ∪ poly [b] = {a, b}` misses the segment
that `poly [a, b]` carries. -/
theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Polygonal.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric _root_.Set

namespace Schoenflies

/-- A set is polygonal when it is the carrier of a finite vertex list, that is, a finite union
of line segments. -/
def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

/-- `lineMap a b` is injective on the unit interval exactly when the segment is
nondegenerate: two parameters differ by a multiple of `b - a`. Exposed separately because the
plane-graph drawing condition asks for the parametrization, not just its image. -/
theorem injOn_lineMap {a b : Plane} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

/-- A nondegenerate segment is an arc between its endpoints, parametrized by
`AffineMap.lineMap a b`. -/
theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

/-- **A polygonal set is carried by a vertex list running from any of its points to any other.**
The list is written with its two ends displayed, so no `List.head`/`List.getLast` obligations
appear. -/
theorem exists_poly_anchored : ∀ (vs : List Plane), vs ≠ [] → ∀ z w : Plane,
    z ∈ poly vs → w ∈ poly vs → ∃ mid : List Plane, poly (z :: (mid ++ [w])) = poly vs := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    rcases tl with _ | ⟨v, rest⟩
    · -- A one-point carrier: both ends are that point.
      intro _ z w hz hw
      rw [poly_singleton, Set.mem_singleton_iff] at hz hw
      subst hz; subst hw
      exact ⟨[], by simp [segment_same]⟩
    · intro _ z w hz hw
      have hne : (v :: rest) ≠ [] := List.cons_ne_nil v rest
      have hv : v ∈ poly (v :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
      rw [poly_cons_cons] at hz hw
      -- `segment z u ⊆ segment u v` for `z` on the first edge, and likewise for `w`.
      have hsub : ∀ p ∈ segment ℝ u v, segment ℝ p u ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset hp (left_mem_segment ℝ u v)
      have hsub' : ∀ p ∈ segment ℝ u v, segment ℝ u p ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · -- Both ends on the first edge: run out along the rest of the list and back.
          obtain ⟨Z, hZ⟩ := ih hne v v hv hv
          refine ⟨u :: v :: (Z ++ [v, v, u]), ?_⟩
          have hlast : (z :: u :: (v :: (Z ++ [v]))).getLast (by simp) = v := by
            simp
          have hsplit : z :: ((u :: v :: (Z ++ [v, v, u])) ++ [w])
              = (z :: u :: (v :: (Z ++ [v]))) ++ (v :: u :: [w]) := by
            simp
          have h1 : poly (z :: u :: (v :: (Z ++ [v])))
              = segment ℝ z u ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hZ]
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          have hd2 : segment ℝ u v ∪ segment ℝ u w ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            Set.union_subset Set.subset_union_left ((hsub' w hw).trans Set.subset_union_left)
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, h1, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1, Set.union_eq_self_of_subset_right hd2]
        · -- The far end is on the rest: append its list to the first edge.
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨u :: v :: Y, ?_⟩
          have hsplit : z :: ((u :: v :: Y) ++ [w]) = z :: u :: (v :: (Y ++ [w])) := by simp
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          rw [hsplit, poly_cons_cons, poly_cons_cons, hY, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1]
      · rcases hw with hw | hw
        · -- The near end is on the rest: run to `v`, then out along the first edge.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          refine ⟨X ++ [v, v, u], ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u]) ++ [w]) = (z :: (X ++ [v])) ++ (v :: u :: [w]) := by
            simp
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, hX, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_right (hsub' w hw), Set.union_comm]
        · -- Both ends on the rest: run from one to `v`, out and back along the first edge, on.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨X ++ [v, v, u] ++ (v :: Y), ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u] ++ (v :: Y)) ++ [w])
              = (z :: (X ++ [v])) ++ (v :: u :: (v :: (Y ++ [w]))) := by simp
          have h2 : poly (v :: u :: (v :: (Y ++ [w])))
              = segment ℝ u v ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hY, segment_symm ℝ v u]
          have hd1 : segment ℝ u v ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_left
          have hd2 : poly (v :: rest) ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_right
          rw [hsplit, poly_append (by simp) v (u :: (v :: (Y ++ [w]))) hlast, hX, h2,
            poly_cons_cons, Set.union_eq_self_of_subset_left hd1,
            Set.union_eq_self_of_subset_left hd2]

/-- **Two polygonal sets that meet have a polygonal union.** Anchor both lists at a common
point and concatenate. -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hmeet : (A ∩ B).Nonempty) : IsPolygonal (A ∪ B) := by
  obtain ⟨vs, rfl⟩ := hA
  obtain ⟨ws, rfl⟩ := hB
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have hvs : vs ≠ [] := by rintro rfl; exact hzA
  have hws : ws ≠ [] := by rintro rfl; exact hzB
  obtain ⟨X, hX⟩ := exists_poly_anchored vs hvs z z hzA hzA
  obtain ⟨Y, hY⟩ := exists_poly_anchored ws hws z z hzB hzB
  refine ⟨(z :: (X ++ [z])) ++ (z :: (Y ++ [z])), ?_⟩
  have hlast : (z :: (X ++ [z])).getLast (by simp) = z := by simp
  rw [poly_append (by simp) z (Y ++ [z]) hlast, hX, hY]

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/CycleJordan.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open _root_.Set Schoenflies unitInterval
section
variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

open _root_.Graph in
/-- The point set of a list of edges: the Schoenflies.IsPolygonal.union of their edge arcs. A walk is a list of edges,
so this is what a walk of a plane graph draws. -/
def _root_.Graph.edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

open _root_.Graph in
theorem _root_.Graph.mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

open _root_.Graph in
theorem _root_.Graph.mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

open _root_.Graph in
@[simp]
theorem _root_.Graph.edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

open _root_.Graph in
@[simp]
theorem _root_.Graph.edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

open _root_.Graph in
theorem _root_.Graph.edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

open _root_.Graph in
/-- A list of edges of the graph occupies part of what the graph occupies. -/
theorem _root_.Graph.edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

open _root_.Graph in
/-- **An edge of a plane graph has two distinct ends.** An edge with equal ends would be drawn
by an arc whose parametrisation returns to its start, which its injectivity forbids. -/
theorem _root_.Graph.IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

open _root_.Graph in
/-- **The first edge's arc meets the rest of the path only at the waypoint.** Two cases, and
neither is geometric beyond the workhorse `Graph.IsDrawing.arcs_meet_at_vertex`: if the rest
takes the same edge again, the source is one of its ends; if it takes a different one, a
common point is a vertex incident with both, so it is the source or the waypoint. Either way a
point that was the source would put the source among the vertices the rest visits, which is
what the path's freshness clause forbids. -/
theorem _root_.Graph.IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  -- Taking the same edge again would put the source among the vertices the rest visits.
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

open _root_.Graph in
/-- **The realisation of a path is an arc between its two ends.** The path must go somewhere:
the empty path draws the empty set, which is not an arc.

The induction is on the path, at the source end, and what it carries is the existence of the
arc. At each step the first edge's arc and the rest's arc meet only at the waypoint
(`Graph.IsDrawing.first_edge_meets_rest`), so `Schoenflies.IsArcBetween.concatenate` glues
them. -/
theorem _root_.Graph.IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · -- A single edge: the rest contributes nothing, and the path arrives where the edge does.
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

/-! ### The realisation of a cycle -/

open _root_.Graph in
/-- The detour of a cycle is a path with at least one edge — an empty detour would return to
where it set out, and the edge it is a detour for has two distinct ends — so it is drawn by an
arc between those ends. -/
theorem _root_.Graph.IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

open _root_.Graph in
/-- **The detour of a cycle meets the edge only at the edge's two ends.** A common point lies
on the edge and on some edge of the detour, which the detour does not contain, so it is a
vertex incident with the edge — and an edge has only its two ends. -/
theorem _root_.Graph.IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

open _root_.Graph in
/-- **The realisation of a cycle is a Jordan curve.** The detour is drawn by an arc from one
end of the edge to the other, the edge is drawn by an arc back, and the two meet only at those
two ends, so `Schoenflies.IsJordanCurve.of_two_arcs` closes the loop. -/
theorem _root_.Graph.IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

open _root_.Graph in
/-- The source of a nonempty walk lies on what the walk draws. -/
theorem _root_.Graph.IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

open _root_.Graph in
/-- **A walk of a polygonal plane graph draws a polygonal set.** Consecutive edges share the
vertex between them, so the Schoenflies.IsPolygonal.union stays a single vertex list. -/
theorem _root_.Graph.IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/TwoConnected.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

open _root_.Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

/-! ### Deleting one vertex -/

open _root_.Graph in
theorem _root_.Graph.mem_deleteVerts_singleton : y ∈ V(G.deleteVerts {x}) ↔ y ∈ V(G) ∧ y ≠ x := by
  simp

open _root_.Graph in
theorem _root_.Graph.mem_deleteVerts_singleton_of_ne (hy : y ∈ V(G)) (hyx : y ≠ x) :
    y ∈ V(G.deleteVerts {x}) :=
  mem_deleteVerts_singleton.2 ⟨hy, hyx⟩

open _root_.Graph in
/-- Deleting a vertex the graph does not have leaves the graph alone — on the nose, not merely
up to isomorphism, because `V(G) \ {x}` is literally `V(G)`. -/
theorem _root_.Graph.deleteVerts_singleton_eq_self (hx : x ∉ V(G)) : G.deleteVerts {x} = G := by
  rw [deleteVerts, sdiff_singleton_eq_self hx, induce_vertexSet]

open _root_.Graph in
/-- Deleting the same vertices from both sides of an inclusion keeps it. -/
theorem _root_.Graph.deleteVerts_mono (h : G ≤ H) (X : Set α) : G.deleteVerts X ≤ H.deleteVerts X where
  vertexSet_mono := by
    simp only [vertexSet_deleteVerts]
    exact sdiff_subset_sdiff_left h.vertexSet_mono
  isLink_mono e x y hl := by
    rw [deleteVerts_isLink] at hl ⊢
    exact ⟨h.isLink_mono hl.1, hl.2.1, hl.2.2⟩

/-! ### Walks across a vertex deletion -/

open _root_.Graph in
/-- Connectedness is unharmed by deleting a vertex the graph does not have. -/
theorem _root_.Graph.Connected.deleteVerts_singleton_of_notMem (h : G.Connected) (hx : x ∉ V(G)) :
    (G.deleteVerts {x}).Connected := by
  rwa [deleteVerts_singleton_eq_self hx]

/-! ### Cut vertices -/

/-! ### At least three vertices -/

open _root_.Graph in
/-- The graph has three pairwise distinct vertices. Stated existentially rather than as
`3 ≤ V(G).ncard` so that it is monotone with no finiteness hypothesis. -/
def _root_.Graph.HasThreeVertices (G : Graph α β) : Prop :=
  ∃ a ∈ V(G), ∃ b ∈ V(G), ∃ c ∈ V(G), a ≠ b ∧ a ≠ c ∧ b ≠ c

open _root_.Graph in
theorem _root_.Graph.HasThreeVertices.mono (h : G.HasThreeVertices) (hV : V(G) ⊆ V(H)) :
    H.HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  exact ⟨p, hV hp, q, hV hq, r, hV hr, hpq, hpr, hqr⟩

open _root_.Graph in
/-- **Any two vertices leave a third over.** This, and not the counting clause itself, is what
every consumer of 2-connectivity uses; the two named vertices need not even be vertices of the
graph. -/
theorem _root_.Graph.HasThreeVertices.exists_ne_ne (h : G.HasThreeVertices) (u v : α) :
    ∃ w ∈ V(G), w ≠ u ∧ w ≠ v := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  by_contra hcon
  push Not at hcon
  -- Every vertex is `u` or `v`, so the three distinct ones cannot all fit.
  have key : ∀ z ∈ V(G), z = u ∨ z = v := fun z hz ↦ (em (z = u)).imp id (hcon z hz)
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

/-! ### Two-connectivity -/

open _root_.Graph in
/-- **The blueprint's convention, verbatim**: at least three vertices, connected, and still
connected after any one vertex is deleted. -/
structure _root_.Graph.IsTwoConnected (G : Graph α β) : Prop where
  /-- The graph has at least three vertices. -/
  hasThreeVertices : G.HasThreeVertices
  /-- The graph is connected. -/
  connected : G.Connected
  /-- Deleting any one vertex leaves it connected. -/
  deleteVerts_connected : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected

open _root_.Graph in
/-- The deletion clause with its hypothesis dropped: deleting a vertex the graph does not have
changes nothing, so no consumer has to check membership first. -/
theorem _root_.Graph.IsTwoConnected.deleteVerts_connected' (h : G.IsTwoConnected) (x : α) :
    (G.deleteVerts {x}).Connected := by
  by_cases hx : x ∈ V(G)
  · exact h.deleteVerts_connected hx
  · exact h.connected.deleteVerts_singleton_of_notMem hx

/-! ### The union of two graphs -/

open _root_.Graph in
/-- The union of two graphs. On an edge belonging to both, `G`'s ends win — a resolution is
needed, since two graphs may disagree about the ends of a shared edge name; for
`Graph.Compatible` graphs, which is the only case the development forms, the disjunction
collapses to the naive one. -/
protected def _root_.Graph.union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e _ :=
    { symm := by
        rintro x y (hxy | ⟨he, hxy⟩)
        exacts [Or.inl hxy.symm, Or.inr ⟨he, hxy.symm⟩] }
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y c d (hxy | ⟨hg, hxy⟩) (hcd | ⟨hg', hcd⟩)
    · exact hxy.left_eq_or_eq hcd
    · exact absurd hxy.edge_mem hg'
    · exact absurd hcd.edge_mem hg
    · exact hxy.left_eq_or_eq hcd
  edge_mem_iff_exists_isLink g := by
    constructor
    · rintro (hg | hg)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
        exact ⟨x, y, Or.inl hxy⟩
      · by_cases hgG : g ∈ E(G)
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hgG
          exact ⟨x, y, Or.inl hxy⟩
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
          exact ⟨x, y, Or.inr ⟨hgG, hxy⟩⟩
    · rintro ⟨x, y, (hxy | ⟨-, hxy⟩)⟩
      exacts [Or.inl hxy.edge_mem, Or.inr hxy.edge_mem]
  left_mem_of_isLink := by
    rintro g x y (hxy | ⟨-, hxy⟩)
    exacts [Or.inl hxy.left_mem, Or.inr hxy.left_mem]

open _root_.Graph in
@[simp]
theorem _root_.Graph.vertexSet_union (G H : Graph α β) : V(G.union H) = V(G) ∪ V(H) := rfl

open _root_.Graph in
@[simp]
theorem _root_.Graph.edgeSet_union (G H : Graph α β) : E(G.union H) = E(G) ∪ E(H) := rfl

open _root_.Graph in
theorem _root_.Graph.left_le_union (G H : Graph α β) : G ≤ G.union H where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ h := Or.inl h

open _root_.Graph in
/-- Two subgraphs of one graph have their union inside it. -/
theorem _root_.Graph.union_le (hGK : G ≤ K) (hHK : H ≤ K) : G.union H ≤ K where
  vertexSet_mono := Set.union_subset hGK.vertexSet_mono hHK.vertexSet_mono
  isLink_mono := by
    rintro g p q (h | ⟨-, h⟩)
    exacts [hGK.isLink_mono h, hHK.isLink_mono h]

open _root_.Graph in
/-- The right-hand graph is a subgraph of the union only when the two agree about their shared
edges — without that, no graph has both as subgraphs. -/
theorem _root_.Graph.Compatible.right_le_union (h : G.Compatible H) : H ≤ G.union H where
  vertexSet_mono := subset_union_right
  isLink_mono e x y hxy := by
    by_cases hg : e ∈ E(G)
    · exact Or.inl ((h.isLink_congr hg hxy.edge_mem).2 hxy)
    · exact Or.inr ⟨hg, hxy⟩

open _root_.Graph in
/-- **Two connected parts covering a graph and sharing a vertex make it connected.** Used
twice below — once for the union itself, once for the union with a vertex deleted — and both
times the two parts are `G` and `H` while the whole is not their union on the nose. -/
theorem _root_.Graph.Connected.of_two_subgraphs (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K) (hV : V(K) ⊆ V(G₁) ∪ V(G₂))
    (hc₁ : G₁.Connected) (hc₂ : G₂.Connected) (hs₁ : s ∈ V(G₁)) (hs₂ : s ∈ V(G₂)) :
    K.Connected := by
  refine Connected.of_hub (h₁.vertexSet_mono hs₁) fun z hz ↦ ?_
  rcases hV hz with hz' | hz'
  · exact (hc₁.reaches hs₁ hz').mono h₁
  · exact (hc₂.reaches hs₂ hz').mono h₂

open _root_.Graph in
theorem _root_.Graph.Compatible.union_connected (h : G.Compatible H) (hG : G.Connected) (hH : H.Connected)
    (hs : s ∈ V(G)) (hs' : s ∈ V(H)) : (G.union H).Connected :=
  Connected.of_two_subgraphs (left_le_union G H) h.right_le_union subset_rfl hG hH hs hs'

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Component.lean` -/

/-!
# Components and shortest paths

The two prerequisites of the relative ear decomposition (`lem:relative-ear`) that no earlier
module builds: the **component** of a vertex, and a **shortest** walk between two vertices.
Both are then spent on the geometric heart of that lemma — a component of `G - S` has two
distinct neighbours in `S`, and a path between two of them whose interior lies outside `S`.

## The component is a comprehension

`G.component u = {v | G.Reaches u v}`, exactly as `connectedComponentIn` collects the points
a space reaches. Nothing restricts the comprehension to `V(G)`: the empty walk already demands
a vertex of the graph (`Graph.IsWalk.nil`), so `G.Reaches u v` carries `v ∈ V(G)` with it, and
a clause `v ∈ V(G) ∧ …` would be redundant noise at every use site. When `u ∉ V(G)` the
component is empty, which is the convention that makes the covering statement
`Graph.iUnion_component` true with no side condition.

Reachability is an equivalence relation on `V(G)`, so the component is closed under `Reaches`,
two components are equal or disjoint, and the components cover `V(G)`. The one statement that
is not pure equivalence-relation bookkeeping is that the **induced** subgraph on a component
is connected: a walk between two vertices of a component never leaves it
(`Graph.IsWalk.walkVertices_subset_component`), so it is already a walk of the induced
subgraph, by `Graph.IsWalk.anti`.

## Shortest walks need no finiteness

The set of lengths of walks from `u` to `v` is a nonempty set of naturals, so it has a least
element — `Nat.find`, with no `Graph.Finite` hypothesis anywhere. That is worth noticing: the
blueprint says "in a finite graph", but finiteness is used there only to terminate the ear
*process*, never to find one shortest path.

A minimum-length walk is automatically a path (`Graph.IsWalk.isPath_of_minLength`). The proof
is the induction of `Graph.IsWalk.contains_path` run once more, with lengths attached: if the
step's source were revisited later, `Graph.IsPath.from_visited` would cut the tail down to a
strictly shorter walk with the same ends, and a path's edge list repeats nothing
(`Graph.IsPath.nodup`), so the cut piece really is no longer than what it came from
(`List.subperm_of_subset`).

## The two neighbours, without a contradiction

The blueprint argues by contradiction: "otherwise its unique neighbour would be a cut vertex".
Here the two neighbours are *constructed*, in the shape `Graph.IsTwoConnected.no_bridge`
already uses. A walk from the component out to a vertex of `S` crosses the boundary
(`Graph.IsWalk.crossing`), and the crossing edge's far end is in `S` — because a neighbour
outside `S` would still be in the component. That is the first neighbour `c`. For the second,
delete `c`: the big graph is still connected, so the same crossing argument runs inside
`G - c`, and its crossing edge's far end is a neighbour that is not `c`.

Two distinct vertices of `S` are needed, and used exactly once: the walk of the second step
must aim at a vertex of `S` other than `c`. In the application `S` is the vertex set of a
2-connected subgraph, which has three.

## Blueprint

* `Graph.component`, `Graph.induce_component_connected` — "a component `L` of `G - V(H₀)`" in
  the proof of `lem:relative-ear`.
* `Graph.exists_minLength_isPath` — "a shortest path through `L`", same proof.
* `Graph.IsTwoConnected.component_two_neighbors` — "if a component `L` of `G - V(H₀)` contains
  a vertex, it has at least two distinct neighbors in `H₀`; otherwise its unique neighbor
  would be a cut vertex of `G`".
* `Graph.IsTwoConnected.exists_path_through_component` — "a shortest path through `L` between
  two such neighbors is an ear": a path of `G` between two distinct vertices of `S`, whose
  every other vertex is outside `S`, which has at least one such vertex, and each of whose
  edges has an end outside `S`. The word *ear* is not used here and nothing about ears is
  assumed; this is the raw path that a consumer recognises as one.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

section
variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

/-! ### Components -/

open _root_.Graph in
/-- The component of `u` in `G`: the vertices `u` reaches. A comprehension over the vertices,
not an indexed union of connected subgraphs; the membership test is `Graph.Reaches` itself,
which is why every closure property below is one line of the reachability API.

No `v ∈ V(G)` clause: `Graph.Reaches` already carries it, since the empty walk demands a
vertex of the graph. For `u ∉ V(G)` the component is empty. -/
def _root_.Graph.component (G : Graph α β) (u : α) : Set α := {v | G.Reaches u v}

open _root_.Graph in
theorem _root_.Graph.component_subset_vertexSet : G.component u ⊆ V(G) := fun _ h ↦ Reaches.right_mem h

open _root_.Graph in
theorem _root_.Graph.mem_component_self (hu : u ∈ V(G)) : u ∈ G.component u := Reaches.refl hu

open _root_.Graph in
/-- **A component is closed under reachability**, which is the property every consumer uses:
whatever a vertex of the component reaches is in the component. -/
theorem _root_.Graph.mem_component_of_reaches (hv : v ∈ G.component u) (h : G.Reaches v w) :
    w ∈ G.component u :=
  Reaches.trans hv h

open _root_.Graph in
/-- A component is closed under taking an edge. -/
theorem _root_.Graph.mem_component_of_isLink (hx : x ∈ G.component u) (hl : G.IsLink e x y) :
    y ∈ G.component u :=
  mem_component_of_reaches hx (Reaches.of_isLink hl)

/-! ### The subgraph induced on a component -/

/-! ### Shortest walks and shortest paths -/

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

open _root_.Graph in
/-- A walk of `G - S` visits only vertices of `G` outside `S` — computed in `G`, which is the
form the freshness clause of a path of `G` reads. -/
theorem _root_.Graph.IsWalk.walkVertices_subset_of_deleteVerts (h : (G.deleteVerts S).IsWalk u W v) :
    G.walkVertices u W ⊆ V(G) \ S := by
  intro z hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨g, hg, hinc⟩
  · simpa using h.left_mem
  -- An edge of the walk survives the deletion, so both of its ends do.
  have hgE := h.edge_mem hg
  rw [edgeSet_deleteVerts] at hgE
  obtain ⟨s, t, hst, hs, ht⟩ := hgE
  rcases hinc.eq_or_eq_of_isLink hst with rfl | rfl
  exacts [⟨hst.left_mem, hs⟩, ⟨hst.right_mem, ht⟩]

open _root_.Graph in
/-- The component of `G - S` at `x`, seen in `G`: outside `S`, and inside `V(G)`. -/
theorem _root_.Graph.component_deleteVerts_subset : (G.deleteVerts S).component x ⊆ V(G) \ S := by
  intro z hz
  have := component_subset_vertexSet hz
  rwa [vertexSet_deleteVerts] at this

open _root_.Graph in
/-- **A neighbour of a component of `G - S` that is outside `S` is in the component.** The
edge joining them survives the deletion, so it extends the walk. -/
theorem _root_.Graph.mem_component_deleteVerts_of_isLink (hp : p ∈ (G.deleteVerts S).component x)
    (hl : G.IsLink e p q) (hq : q ∉ S) : q ∈ (G.deleteVerts S).component x :=
  mem_component_of_isLink hp
    ((deleteVerts_isLink G S).2 ⟨hl, (component_deleteVerts_subset hp).2, hq⟩)

open _root_.Graph in
/-- **Walking out of a component of `G - S` meets `S` along an edge.** The walk may live in
any subgraph `K` of `G` — it is run inside `G - c` once — but the component is always the one
of `G - S`, which is what makes the conclusion usable twice.

This is `Graph.IsWalk.crossing` plus the previous lemma: the crossing edge's far end is
outside the component, so it cannot be outside `S`. -/
theorem _root_.Graph.exists_isLink_out_of_component {K : Graph α β} (hKG : K ≤ G)
    (h : K.IsWalk x W v) (hx : x ∈ (G.deleteVerts S).component x) (hv : v ∈ S) :
    ∃ p ∈ (G.deleteVerts S).component x, ∃ g ∈ W, ∃ t ∈ S, K.IsLink g p t := by
  have hvL : v ∉ (G.deleteVerts S).component x := fun hmem ↦
    (component_deleteVerts_subset hmem).2 hv
  obtain ⟨g, hg, s, t, hst, hs, ht⟩ := h.crossing hx hvL
  refine ⟨s, hs, g, hg, t, ?_, hst⟩
  by_contra htS
  exact ht (mem_component_deleteVerts_of_isLink hs (hst.mono hKG) htS)

/-! ### The two neighbours of a component, and the path through it -/

open _root_.Graph in
/-- **A component of `G - S` has two distinct neighbours in `S`** — the first half of
`lem:relative-ear`, with the blueprint's contradiction turned into a construction.

`S` must contain two distinct vertices; in the application it is the vertex set of a
2-connected subgraph, which has three. The first neighbour `c` comes from a walk of `G` out of
the component to a vertex of `S`; the second from the same walk run inside `G - c`, which is
still connected because `G` is 2-connected, and aimed at a vertex of `S` other than `c`. -/
theorem _root_.Graph.IsTwoConnected.component_two_neighbors (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (∃ p ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g p c) ∧
      (∃ q ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g q d) := by
  have hxD : x ∈ V(G.deleteVerts S) := by rw [vertexSet_deleteVerts]; exact ⟨hx, hxS⟩
  have hxL : x ∈ (G.deleteVerts S).component x := mem_component_self hxD
  -- First neighbour: walk from `x` to `a` in `G` and take the edge where it leaves.
  obtain ⟨W, hW⟩ := hG.connected.reaches hx (hS ha)
  obtain ⟨p, hp, g, -, c, hc, hgpc⟩ := exists_isLink_out_of_component le_rfl hW hxL ha
  -- Second neighbour: aim at a vertex of `S` other than `c`, inside `G - c`.
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ S, t ≠ c := by
    rcases eq_or_ne a c with rfl | hac
    · exact ⟨b, hb, fun h ↦ hab h.symm⟩
    · exact ⟨a, ha, hac⟩
  have hxc : x ∈ V(G.deleteVerts {c}) :=
    mem_deleteVerts_singleton_of_ne hx fun h ↦ hxS (h ▸ hc)
  have htc' : t ∈ V(G.deleteVerts {c}) := mem_deleteVerts_singleton_of_ne (hS ht) htc
  obtain ⟨W', hW'⟩ := (hG.deleteVerts_connected' c).reaches hxc htc'
  obtain ⟨q, hq, g', -, d, hd, hgqd⟩ :=
    exists_isLink_out_of_component deleteVerts_le hW' hxL ht
  -- The second crossing edge lives in `G - c`, so its far end is not `c`.
  have hdc : d ≠ c := by
    have := ((deleteVerts_isLink G {c}).1 hgqd).2.2
    simpa using this
  exact ⟨c, hc, d, hd, fun h ↦ hdc h.symm, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd.mono deleteVerts_le⟩⟩

open _root_.Graph in
/-- Reading off the vertices of a walk with one edge appended at the far end. Purely about
lists; used to check the freshness clause when a path inside a component is capped with an
edge back into `S`. -/
theorem _root_.Graph.mem_walkVertices_append_singleton (hy : y ∈ G.walkVertices u (W ++ [e])) :
    y ∈ G.walkVertices u W ∨ G.Inc e y := by
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with h | ⟨g, hg, hinc⟩
  · exact Or.inl (mem_walkVertices_of_mem_covered h)
  · obtain rfl : g = e := by simpa using hg
    exact Or.inr hinc

open _root_.Graph in
/-- **The path through a component** — the second half of `lem:relative-ear`, without the word
*ear*: in a 2-connected `G`, from a vertex outside a set `S` that has two distinct vertices,
one gets a path of `G` whose two endpoints are distinct vertices of `S`, whose every other
vertex is outside `S`, which has at least one vertex outside `S`, and each of whose edges has
an end outside `S`.

The last two clauses are what make the ear process terminate and what make the path *new*: it
really does add a vertex, and none of its edges belongs to a subgraph whose vertices all lie
in `S`.

The path is built from the two neighbours of the component: the edge into the component, a
path across the component (in `G - S`, hence never touching `S`), and the edge back out. -/
theorem _root_.Graph.IsTwoConnected.exists_path_through_component (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, ∃ P, c ≠ d ∧ G.IsPath c P d ∧
      (∀ y ∈ G.walkVertices c P, y ≠ c → y ≠ d → y ∉ S) ∧
      (∃ y ∈ G.walkVertices c P, y ∉ S) ∧
      ∀ f ∈ P, ∃ y, G.Inc f y ∧ y ∉ S := by
  obtain ⟨c, hc, d, hd, hcd, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd⟩⟩ :=
    hG.component_two_neighbors hS ha hb hab hx hxS
  have hpS : p ∉ S := (component_deleteVerts_subset hp).2
  have hqS : q ∉ S := (component_deleteVerts_subset hq).2
  -- A path across the component, taken in `G - S` so that it cannot touch `S`.
  obtain ⟨Q, hQ⟩ := Reaches.exists_isPath (Reaches.trans (Reaches.symm hq) hp)
  have hQvert : G.walkVertices q Q ⊆ V(G) \ S :=
    hQ.isWalk.walkVertices_subset_of_deleteVerts
  have hQG : G.IsPath q Q p := hQ.mono deleteVerts_le
  -- Cap it with the edge `p — c`, which is fresh because `c ∈ S`.
  have hcQ : c ∉ G.walkVertices q Q := fun hmem ↦ (hQvert hmem).2 hc
  have hQc : G.IsPath q (Q ++ [g]) c := hQG.extend_at_target hgpc hcQ
  -- Prepend the edge `d — q`, fresh because `d ∈ S` and `d ≠ c`.
  have hdQc : d ∉ G.walkVertices q (Q ++ [g]) := by
    intro hmem
    rcases mem_walkVertices_append_singleton hmem with hmem' | hinc
    · exact (hQvert hmem').2 hd
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS hd, hcd rfl]
  have hpath : G.IsPath d (g' :: (Q ++ [g])) c := .cons hgqd.symm hQc hdQc
  refine ⟨d, hd, c, hc, _, fun h ↦ hcd h.symm, hpath, fun y hy hyd hyc ↦ ?_,
    ⟨q, mem_walkVertices_cons_of_mem hgqd.symm mem_walkVertices_self, hqS⟩, fun f hf ↦ ?_⟩
  · -- Every vertex is `d`, `c`, or one that `G - S` reached.
    rcases mem_walkVertices_cons hgqd.symm hy with rfl | hy'
    · exact absurd rfl hyd
    rcases mem_walkVertices_append_singleton hy' with hmem | hinc
    · exact (hQvert hmem).2
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS, absurd rfl hyc]
  · -- Every edge touches the component: the two capping edges at `q` and at `p`, the rest at
    -- both of their ends.
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨q, hgqd.inc_left, hqS⟩
    rcases List.mem_append.1 hf' with hf' | hf'
    · have hfE := hQ.isWalk.edge_mem hf'
      rw [edgeSet_deleteVerts] at hfE
      obtain ⟨s, t, hst, hs, -⟩ := hfE
      exact ⟨s, hst.inc_left, hs⟩
    · obtain rfl : f = g := by simpa using hf'
      exact ⟨p, hgpc.inc_left, hpS⟩

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/PathGraph.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

open _root_.Set
section
variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

open _root_.Graph in
/-- **A walk that never visits `c` survives the deletion of `c`.** Every deletion argument in
the ear layer reduces to this. -/
theorem _root_.Graph.IsWalk.avoiding (h : G.IsWalk u W v) (hc : c ∉ G.walkVertices u W) :
    (G.deleteVerts {c}).IsWalk u W v := by
  induction h with
  | @nil x hx =>
    refine .nil ?_
    rw [vertexSet_deleteVerts]
    exact ⟨hx, by rintro (rfl : x = c); exact hc mem_walkVertices_self⟩
  | @cons u w v e W hl _ ih =>
    have hw : w ∈ G.walkVertices u (e :: W) :=
      mem_walkVertices_cons_of_mem hl mem_walkVertices_self
    have hcw : c ∉ G.walkVertices w W := fun h ↦ hc (mem_walkVertices_cons_of_mem hl h)
    refine .cons ?_ (ih hcw)
    rw [deleteVerts_isLink]
    refine ⟨hl, ?_, ?_⟩
    · rintro (rfl : u ∈ ({c} : Set α))
      exact hc mem_walkVertices_self
    · rintro (rfl : w ∈ ({c} : Set α))
      exact hc hw

open _root_.Graph in
/-- Reversal does not change which vertices a walk visits — but it does change the source, so
this is not `Graph.walkVertices_reverse`, which keeps it. -/
theorem _root_.Graph.IsWalk.reverse_walkVertices (h : G.IsWalk u W v) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  have h₁ : v ∈ G.walkVertices u W := h.target_mem_walkVertices
  have h₂ : u ∈ G.walkVertices v W := by
    have := h.reverse.target_mem_walkVertices
    rwa [walkVertices_reverse] at this
  rw [walkVertices_reverse]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_) <;>
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
  exacts [h₁, mem_walkVertices_of_mem_covered hcov, h₂, mem_walkVertices_of_mem_covered hcov]

open _root_.Graph in
/-- Splitting the visited set along a concatenation. Purely about lists: no walk is needed,
and the middle vertex `w` is arbitrary. -/
theorem _root_.Graph.walkVertices_append_subset :
    G.walkVertices u (W₁ ++ W₂) ⊆ G.walkVertices u W₁ ∪ G.walkVertices w W₂ := by
  rintro y hy
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  · rw [coveredVertices_append] at hcov
    exact hcov.imp mem_walkVertices_of_mem_covered mem_walkVertices_of_mem_covered

/-! ### Reaching an end of a path after a deletion -/

open _root_.Graph in
/-- A vertex of a path other than its source still reaches the target once the source is
deleted: cut the path at the vertex, and the far half never returns to the source. -/
theorem _root_.Graph.IsPath.reaches_target_of_ne_source (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxu : x ≠ u) : (G.deleteVerts {u}).Reaches x v := by
  obtain ⟨-, W₂, -, -, h₂, hback⟩ := h.split hx
  exact ⟨W₂, h₂.isWalk.avoiding (hback.resolve_left hxu)⟩

open _root_.Graph in
/-- The mirror image, run on the reversed path. -/
theorem _root_.Graph.IsPath.reaches_source_of_ne_target (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxv : x ≠ v) : (G.deleteVerts {v}).Reaches x u :=
  h.reverse.reaches_target_of_ne_source (by rwa [h.isWalk.reverse_walkVertices]) hxv

open _root_.Graph in
/-- **Deleting any vertex leaves every other vertex of a path able to reach an end.**
Uniform in the deleted vertex `c`: if `c` is on the path the path is cut there and each
remaining vertex sits on a half that runs to that half's far end; if `c` is off the path the
path is cut at the vertex itself and its near half, reversed, runs to the source. -/
theorem _root_.Graph.IsPath.reaches_an_end (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W)
    (hxc : x ≠ c) :
    (G.deleteVerts {c}).Reaches x u ∨ (G.deleteVerts {c}).Reaches x v := by
  by_cases hc : c ∈ G.walkVertices u W
  · obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := h.split hc
    rcases walkVertices_append_subset (w := c) hx with hx₁ | hx₂
    · exact Or.inl (h₁.reaches_source_of_ne_target hx₁ hxc)
    · exact Or.inr (h₂.reaches_target_of_ne_source hx₂ hxc)
  · -- The deletion misses the path entirely, so the near half survives whole.
    obtain ⟨W₁, W₂, rfl, h₁, -, -⟩ := h.split hx
    refine Or.inl ⟨W₁.reverse, h₁.reverse.isWalk.avoiding ?_⟩
    rw [h₁.isWalk.reverse_walkVertices]
    exact fun hmem ↦ hc (walkVertices_mono (List.subset_append_left _ _) hmem)

/-! ### A graph that is a path -/

open _root_.Graph in
/-- `P.IsPathGraph u W v` : the graph `P` *is* the path from `u` to `v` along `W`. Its own
edges are exactly the entries of `W`, and its vertices are exactly the ones that path visits.

The edge list is an index rather than an existential because its order is used: an argument
that deletes a vertex cuts `W` in two, and a graph whose edges were only a set would have to
recover the order first. -/
structure _root_.Graph.IsPathGraph (P : Graph α β) (u : α) (W : List β) (v : α) : Prop where
  /-- The graph's own edges, in the given order, form a path from one end to the other. -/
  isPath : P.IsPath u W v
  /-- The graph has no edges beyond that path's. -/
  edgeSet_eq : E(P) = {e | e ∈ W}
  /-- The graph has no vertices beyond the ones that path visits. -/
  vertexSet_eq : V(P) = P.walkVertices u W

open _root_.Graph in
/-- A vertex of a path graph is visited by its path. -/
theorem _root_.Graph.IsPathGraph.mem_walkVertices (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) :
    x ∈ P.walkVertices u W := h.vertexSet_eq ▸ hx

open _root_.Graph in
theorem _root_.Graph.IsPathGraph.mem_edgeSet (h : P.IsPathGraph u W v) (he : e ∈ W) : e ∈ E(P) := by
  rw [h.edgeSet_eq]; exact he

open _root_.Graph in
theorem _root_.Graph.IsPathGraph.source_mem (h : P.IsPathGraph u W v) : u ∈ V(P) := h.isPath.left_mem

open _root_.Graph in
/-- A path graph is connected: every vertex is visited, so the path's own prefix runs to it
from the source. -/
theorem _root_.Graph.IsPathGraph.connected (h : P.IsPathGraph u W v) : P.Connected := by
  refine Connected.of_hub h.source_mem fun x hx ↦ ?_
  obtain ⟨W₁, -, -, h₁, -, -⟩ := h.isPath.split (h.mem_walkVertices hx)
  exact ⟨W₁, h₁.isWalk⟩

open _root_.Graph in
/-- **Whatever vertex is deleted, every remaining vertex of a path graph still reaches one of
its two ends.** This is what the ear argument turns on: the ear's two ends are the only
vertices it shares with the graph it is glued to, so a surviving vertex of the ear has to
reach one of them inside the ear itself. -/
theorem _root_.Graph.IsPathGraph.reaches_an_end (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) (hxc : x ≠ c) :
    (P.deleteVerts {c}).Reaches x u ∨ (P.deleteVerts {c}).Reaches x v :=
  h.isPath.reaches_an_end (h.mem_walkVertices hx) hxc

/-! ### Constructing a path graph -/

open _root_.Graph in
/-- **The subgraph of `G` spanned by the walk `W` from `u`**: the vertices that walk visits,
carrying exactly the walk's own edges.

This is the construction an ear decomposition needs — a path found inside a big graph, turned
into a graph of its own so that it can be unioned back in. It is built from Mathlib's
`Graph.restrict` and `Graph.induce`, so that `Graph.pathGraphOf_le` is almost free. -/
def _root_.Graph.pathGraphOf (G : Graph α β) (u : α) (W : List β) : Graph α β :=
  (G.restrict {e | e ∈ W}).induce (G.walkVertices u W)

open _root_.Graph in
@[simp]
theorem _root_.Graph.pathGraphOf_vertexSet : V(G.pathGraphOf u W) = G.walkVertices u W := rfl

open _root_.Graph in
@[simp]
theorem _root_.Graph.pathGraphOf_isLink :
    (G.pathGraphOf u W).IsLink e x y ↔
      e ∈ W ∧ G.IsLink e x y ∧ x ∈ G.walkVertices u W ∧ y ∈ G.walkVertices u W := by
  simp only [pathGraphOf, induce_isLink, restrict_isLink, mem_setOf_eq]
  tauto

open _root_.Graph in
theorem _root_.Graph.mem_vertexSet_pathGraphOf_self : u ∈ V(G.pathGraphOf u W) := mem_walkVertices_self

open _root_.Graph in
/-- The spanned subgraph really is a subgraph. -/
theorem _root_.Graph.pathGraphOf_le (h : G.IsWalk u W v) : G.pathGraphOf u W ≤ G :=
  le_trans (induce_le h.walkVertices_subset) restrict_le

open _root_.Graph in
/-- Its edges are exactly the walk's. One inclusion is the definition; the other needs the
walk, to know that an entry of `W` is an edge of `G` at all and that its ends are visited. -/
theorem _root_.Graph.pathGraphOf_edgeSet (h : G.IsWalk u W v) : E(G.pathGraphOf u W) = {e | e ∈ W} := by
  ext f
  rw [edgeSet_eq_setOf_exists_isLink]
  simp only [pathGraphOf_isLink, mem_setOf_eq]
  refine ⟨fun ⟨_, _, hf, _⟩ ↦ hf, fun hf ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hf)
  exact ⟨a, b, hf, hab, mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_left⟩,
    mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_right⟩⟩

open _root_.Graph in
/-- The spanned subgraph visits the same vertices as the ambient graph does along `W`: its
edges are the same edges, joining the same pairs. No walk is needed — an end of an edge of
`W` is visited by definition, so it survives the induced subgraph. -/
theorem _root_.Graph.coveredVertices_pathGraphOf :
    (G.pathGraphOf u W).coveredVertices W = G.coveredVertices W := by
  refine Set.Subset.antisymm (fun z ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, (pathGraphOf_isLink.1 hy).2.1⟩)
    fun z ⟨f, hf, y, hy⟩ ↦ ?_
  · exact ⟨f, hf, y, pathGraphOf_isLink.2 ⟨hf, hy,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_left⟩,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_right⟩⟩⟩

open _root_.Graph in
theorem _root_.Graph.walkVertices_pathGraphOf :
    (G.pathGraphOf u W).walkVertices u W = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_pathGraphOf]

open _root_.Graph in
/-- The path runs inside the subgraph it spans. -/
theorem _root_.Graph.IsPath.pathGraphOf (h : G.IsPath u W v) : (G.pathGraphOf u W).IsPath u W v :=
  h.anti (pathGraphOf_le h.isWalk) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h.isWalk) ▸ he

open _root_.Graph in
/-- **A path of `G` spans a path graph.** This is the construction the whole file exists
for: the object every `Graph.IsPathGraph` hypothesis elsewhere is discharged by. -/
theorem _root_.Graph.IsPath.isPathGraph_pathGraphOf (h : G.IsPath u W v) :
    (G.pathGraphOf u W).IsPathGraph u W v where
  isPath := h.pathGraphOf
  edgeSet_eq := pathGraphOf_edgeSet h.isWalk
  vertexSet_eq := by rw [pathGraphOf_vertexSet, walkVertices_pathGraphOf]

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

open _root_.Graph in
/-- A step of a walk adds exactly one vertex to the visited set. -/
theorem _root_.Graph.walkVertices_cons (hl : G.IsLink e u w) :
    G.walkVertices u (e :: W) = insert u (G.walkVertices w W) := by
  ext x
  constructor
  · intro hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ hx']
  · intro hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    exacts [mem_walkVertices_self, mem_walkVertices_cons_of_mem hl hx']

open _root_.Graph in
theorem _root_.Graph.IsWalk.finite_walkVertices (h : G.IsWalk u W v) : (G.walkVertices u W).Finite := by
  induction h with
  | nil => rw [walkVertices_nil]; exact Set.finite_singleton _
  | @cons u w v e W hl _ ih => rw [walkVertices_cons hl]; exact Set.Finite.insert u ih

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Ear.lean` -/

/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

section
variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-! ### Attaching an ear -/

open _root_.Graph in
/-- **`lem:subdivision-ear-preserve` (b): attaching an ear preserves 2-connectivity.** `P` is
a path whose two distinct ends lie in the 2-connected graph `G`; then `G ∪ P` is 2-connected.

The blueprint's hypothesis that the ear's internal vertices are new is **not** needed. Delete
a vertex `c`. One of the ear's two ends survives, and it is the hub: `G - c` is connected and
contains it, and every surviving vertex of the ear reaches one of the two ends inside the ear
(`Graph.IsPathGraph.reaches_an_end`) — an end which, having been reached after the deletion, is
itself not `c`, so it lies in `G - c` too. -/
theorem _root_.Graph.IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    -- One of the ear's two ends survives the deletion; it is the hub.
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    -- Every surviving vertex of the graph side reaches the hub inside the graph side.
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · -- On the ear, one of the two ends is still reachable, and it survived the deletion.
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

/-! ### Replacing an edge by a path -/

/-! ### Finding an ear -/

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Tree.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

/-! ### Trees -/

/-! ### A walk departs along an edge -/

open _root_.Graph in
/-- A path between two distinct vertices takes at least one edge. -/
theorem _root_.Graph.IsPath.ne_nil (h : G.IsPath u P v) (huv : u ≠ v) : P ≠ [] := by
  rintro rfl
  exact huv h.isWalk.eq_of_nil

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

open _root_.Graph in
/-- An edge of a path incident with the path's source is the one the path departs along. -/
theorem _root_.Graph.IsPath.eq_head_of_inc_source (h : G.IsPath u (e :: W) v) (hf : f ∈ e :: W)
    (hinc : G.Inc f u) : f = e := by
  cases h with
  | cons hl hW hfresh =>
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hfresh

/-! ### A longest path -/

open _root_.Graph in
/-- A path repeats no edge, so it is no longer than the graph has edges. -/
theorem _root_.Graph.IsPath.length_le_ncard_edgeSet [G.Finite] (h : G.IsPath u P v) :
    P.length ≤ E(G).ncard := by
  classical
  have hsub : P.toFinset ⊆ G.edgeFinset := fun f hf ↦
    mem_edgeFinset.2 (h.edge_mem (List.mem_toFinset.1 hf))
  calc P.length = P.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
    _ = E(G).ncard := card_edgeFinset

open _root_.Graph in
/-- **A finite graph with a vertex has a longest path.** The lengths of paths are bounded by
the number of edges, so `Nat.findGreatest` picks the largest length that occurs, and the
witnessing path is longest. -/
theorem _root_.Graph.exists_longest_path [G.Finite] (hu : u ∈ V(G)) :
    ∃ x y Q, G.IsPath x Q y ∧ ∀ x' y' (Q' : List β), G.IsPath x' Q' y' → Q'.length ≤ Q.length := by
  classical
  -- `p n` : some path has length exactly `n`.
  set p : ℕ → Prop :=
    fun n ↦ ∃ (x : α) (y : α) (Q : List β), G.IsPath x Q y ∧ Q.length = n with hp
  have hp0 : p 0 := ⟨u, u, [], .nil hu, rfl⟩
  obtain ⟨x, y, Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le E(G).ncard) hp0
  refine ⟨x, y, Q, hQ, fun x' y' Q' hQ' ↦ ?_⟩
  have hle := Nat.le_findGreatest (P := p) hQ'.length_le_ncard_edgeSet ⟨x', y', Q', hQ', rfl⟩
  omega

/-! ### Both ends of a longest path are leaves -/

/-! ### A path steers clear of a leaf -/

/-! ### Vertex deletion -/

/-! ### A tree has one edge fewer than it has vertices -/

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/RelativeEar.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open _root_.Set
section
variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

open _root_.Graph in
/-- **An edge of a subgraph has its ends in the subgraph**, even when the incidence is only
known in the big graph. This is what turns "every edge of the ear has an end outside `V(K)`"
into "no edge of the ear is an edge of `K`". -/
theorem _root_.Graph.mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

open _root_.Graph in
/-- **A subgraph with all the vertices and all the edges is the graph.** The termination
condition of the ear process. -/
theorem _root_.Graph.eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

/-! ### The relative ear -/

open _root_.Graph in
/-- **`lem:relative-ear`, the ear.** A 2-connected subgraph `K` of a loopless 2-connected `G`
that is missing a vertex or an edge has a *relative* ear: a path of `G` whose two distinct
endpoints lie in `K`, whose every other vertex lies **outside** `K`, and none of whose edges
belongs to `K`.

This is the blueprint's own construction, and the freshness of the interior is what
distinguishes it from `Graph.IsTwoConnected.ear_exists`. The first branch takes a component
`L` of `G - V(K)` and a path across it between two of its neighbours in `K`
(`Graph.IsTwoConnected.exists_path_through_component`); the two distinct vertices of `V(K)`
that construction needs are supplied by the counting clause of `K.IsTwoConnected`. The second
branch is the blueprint's "if all vertices are already present, add a missing edge as an ear
of length one", and it is the only place looplessness is used. -/
theorem _root_.Graph.IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    -- The subgraph's three vertices supply the two distinct targets the component needs.
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    -- Each edge of the ear has an end outside `V(K)`, so it is not an edge of `K`.
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · -- Every vertex is already present, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · -- A one-edge path visits nothing but its two ends, so freshness is vacuous.
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

open _root_.Graph in
/-- **One step of the relative ear decomposition.** The ear of
`Graph.IsTwoConnected.relative_ear_exists`, glued on with `Graph.IsTwoConnected.ear`: the
enlarged graph is again a 2-connected subgraph of `G` between `K` and `G`, and it has an edge
that `K` did not have.

The ear data is handed back alongside the enlarged graph, because a consumer of the geometric
version needs the *path*, not merely the fact that the subgraph grew. -/
theorem _root_.Graph.IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

open _root_.Graph in
@[simp]
theorem _root_.Graph.vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

open _root_.Graph in
theorem _root_.Graph.edgeSet_union_pathGraphOf (h : G.IsWalk a D b) :
    E(B.union (G.pathGraphOf a D)) = E(B) ∪ {e | e ∈ D} := by
  rw [edgeSet_union, pathGraphOf_edgeSet h]

/-! ### Iterating: the decomposition itself -/

open _root_.Graph in
/-- **`lem:relative-ear`.** A 2-connected subgraph `K` of a finite loopless 2-connected graph
`G` grows to `G` by repeatedly adding relative ears, stated as the induction principle a
consumer uses: whatever holds of `K` and survives the addition of one ear holds of `G`.

The step is given the whole ear — the path `D` of `G`, its two distinct ends in the current
subgraph `B`, and the fact that its other vertices are outside `B` — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`.

"Finiteness terminates the process" is the strong induction below on `(E(G) \ E(B)).ncard`:
every ear contributes an edge of `G` that `B` was missing, and the process can only be stuck
when `B` has all of `G`'s vertices and edges, which makes `B = G`. -/
theorem _root_.Graph.IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  -- One step, packaged with the strict drop of the measure.
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    -- A subgraph that is not the graph is missing a vertex or an edge.
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    -- The new edge is one the old subgraph was missing, and nothing was lost.
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  -- Strong induction on the number of edges of `G` the subgraph is still missing.
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · -- Nothing is missing, yet an ear was found: its edges were missing after all.
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/OuterFace.lean` -/

/-!
# The outer face

Exactly one face of a finite plane graph is unbounded.

The plane fact this needs is not "the exterior of a large disk is connected" but the exterior
of a *square*, and that one is elementary — `Plane.isConnected_beyondSquare`, four convex
half-planes with consecutive ones sharing a corner. The disk version is what would have
needed a traversal of the circle, which a trigonometry-free development withholds.

No face is produced as data: a face is named by a point of it, as `Graph.face` always has
been, so "the outer face" is "the face through any point far enough out".

## Blueprint

* `exists_unbounded_face` — some face is unbounded.
* `unbounded_face_unique` — any two unbounded faces coincide.
* `beyondSquare_subset_face` — an unbounded face swallows the whole outside of any square
  containing the drawing. This is the working form: it is how one proves a given point lies in
  the outer face.
-/

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Subarc.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open _root_.Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

/-- The affine map carrying `[0, 1]` onto the parameter interval between `a` and `b`,
running from `a` to `b`. -/
def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

/-- The reparametrisation is injective as soon as it is not constant. -/
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

/-- `reparam a b` carries the unit interval exactly onto `uIcc a b`. This is `segment_eq_image'`
read through the identification of a real segment with an unordered closed interval. -/
theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  change (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b
  simpa only [smul_eq_mul] using h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

/-- A subinterval of the unit interval stays inside it: `uIcc` is the convex hull of its two
endpoints, and the unit interval is convex. -/
theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

/-! ### Subarcs -/

/-- The subarc of `f` between the parameters `a` and `b`: the arc traversed from `f a` to
`f b`, reparametrised so that it is again a map on `[0, 1]`. -/
def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

/-- The image of a subarc is the arc restricted to the subinterval — which is what "sub"
means, and the form every consumer wants. -/
theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

/-- Injectivity of the subarc needs injectivity of `f` only where the subarc runs. -/
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

/-- A subarc between two distinct parameters is an arc between the two values there. The
injectivity hypothesis is confined to the traversed interval, so this applies to a piece of a
Jordan curve as well as to a piece of an arc. -/
theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

/-- The version for an arc, whose parametrisation is injective everywhere. -/
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

/-! ### The arc without its endpoints -/

/-- The open arc — the blueprint's `P°`: an arc with its two endpoints removed.

Taken on the parameter side, as the image of the open unit interval, because that is the form
the subarc basis argument needs: an open subarc is the image of an open subinterval.
Injectivity then says it is also the arc minus the two endpoint *values*, which is how the
blueprint reads it (`openArc_eq_diff`). -/
def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

/-- On an arc the two readings of "without its endpoints" agree: dropping the endpoints of the
parameter interval drops exactly the two endpoint values, since injectivity means no other
parameter shares them. -/
theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- **The interior of an arc is the image of the open parameter interval.** The bridge from
`IsArcBetween`, which is about the set, to `openArc`, which is about a parametrisation. -/
theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

/-- **The interior of an arc is connected.** It is the continuous image of `Ioo 0 1`. -/
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

/-- The interior of an arc is nonempty: `Ioo 0 1` is. -/
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- The interior of an arc is connected in the nonempty sense. -/
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

/-- **An endpoint of an arc is a limit of its interior.** This is what turns "the closure of a
cell meets the curve in one arc only" into a statement about the *endpoints* of a crosscut, and
it is what says an ear's two ends lie on the boundary of the face its interior lies in. -/
theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  -- The endpoint is the limit of the interior as the parameter tends to `0`.
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

/-! ### A parametrisation is an open map onto its arc -/

/-- **The parametrisation is an open map onto its arc.** The image of a relatively open piece
of the parameter interval is relatively open in the arc.

No inverse is constructed. The complement piece `I \ U` is compact, so its image is compact,
so it is closed; and by injectivity the image of `U ∩ I` is exactly the arc minus that closed
set. Stated for a relatively open *piece* `U ∩ I` rather than for a subarc, because at an
endpoint the basic neighbourhood is half-open — `openArc` of a subarc is the interior case,
and this covers both. -/
theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · -- The discarded piece is compact, hence closed, so its complement is open.
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · -- Injectivity turns "remove the image" into "image of the removal".
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

/-! ### The subarc basis -/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/FaceCycles.lean` -/

/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

section
variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

open _root_.Graph in
/-- **A vertex of a loopless 2-connected graph has a neighbour other than any prescribed
vertex** — in particular it has two distinct neighbours, and neither is itself. -/
theorem _root_.Graph.IsTwoConnected.exists_adj_ne (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) (hv : v ∈ V(G)) (w : α) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  rcases eq_or_ne v w with rfl | hvw
  · -- Deleting nothing: a walk to any other vertex leaves along a non-loop.
    obtain ⟨z, hz, hzv, -⟩ := h.hasThreeVertices.exists_ne_ne v v
    obtain ⟨T, hT⟩ := h.connected.reaches hv hz
    cases hT with
    | nil => exact absurd rfl hzv
    | @cons _ y _ g _ hl _ => exact ⟨y, ⟨g, hl⟩, fun hh ↦ hnl (hh ▸ hl)⟩
  · -- Deleting `w`: a walk to a third vertex leaves along an edge that survived it.
    obtain ⟨z, hz, hzv, hzw⟩ := h.hasThreeVertices.exists_ne_ne v w
    obtain ⟨T, hT⟩ := (h.deleteVerts_connected' w).reaches
      (mem_deleteVerts_singleton_of_ne hv hvw) (mem_deleteVerts_singleton_of_ne hz hzw)
    cases hT with
    | nil => exact absurd rfl (Ne.symm hzv)
    | @cons _ y _ g _ hl _ =>
      exact ⟨y, ⟨g, hl.mono deleteVerts_le⟩, (mem_deleteVerts_singleton.1 hl.right_mem).2⟩

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

open _root_.Graph in
/-- **A path from a vertex back to itself is empty.** The first step would depart from the
vertex the rest of the path arrives at, which the freshness clause forbids. -/
theorem _root_.Graph.IsPath.eq_nil_of_eq (h : G.IsPath u W u) : W = [] := by
  cases h with
  | nil => rfl
  | cons _ hT hfresh => exact absurd hT.target_mem_walkVertices hfresh

open _root_.Graph in
/-- A cycle with at least three vertices — the blueprint's "cycle of length at least three".
The third vertex is named rather than counted, because that is what both consumers want. -/
structure _root_.Graph.IsLongCycle (G : Graph α β) (e : β) (u v : α) (D : List β) (w : α) : Prop where
  /-- The edge and the detour form a cycle. -/
  isCycle : G.IsCycleThrough e u v D
  /-- The detour visits a third vertex … -/
  mem : w ∈ G.walkVertices u D
  /-- … distinct from the source of the edge … -/
  ne_left : w ≠ u
  /-- … and from its target. -/
  ne_right : w ≠ v

section

variable (h : G.IsLongCycle e u v D w)
include h

open _root_.Graph in
theorem _root_.Graph.IsLongCycle.isPath : G.IsPath u D v := h.isCycle.isPath

open _root_.Graph in
/-- The two ends of the edge are distinct: otherwise the detour would be a path from a vertex
to itself, hence empty, and would visit no third vertex. -/
theorem _root_.Graph.IsLongCycle.ne : u ≠ v := by
  rintro rfl
  have hnil : D = [] := h.isPath.eq_nil_of_eq
  have hmem := h.mem
  rw [hnil, walkVertices_nil] at hmem
  exact h.ne_left hmem

end

open _root_.Graph in
/-- **"The resulting closed subpath is a cycle of length at least three."** A finite loopless
2-connected graph has a cycle with three distinct vertices.

Take a maximal path `u —W→ v`. Its source `u` has a neighbour `x` other than the vertex `w₀`
the path first steps to (`Graph.IsTwoConnected.exists_adj_ne`), and `x` lies on the path:
otherwise the edge to it could be prepended, contradicting maximality. Cutting the path at `x`
gives a path from `u` to `x` whose first step is still to `w₀`, and the chord closes it into a
cycle through `u`, `w₀` and `x`. The chord is not an edge of that piece: an edge at `u` in the
tail is what the path's freshness clause forbids, and the first edge is not the chord because
their far ends differ. -/
theorem _root_.Graph.IsTwoConnected.exists_long_cycle [G.Finite] (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) :
    ∃ g u x D w, G.IsLongCycle g u x D w := by
  obtain ⟨p, hp, -⟩ := h.hasThreeVertices
  obtain ⟨u, v, W, hpath, hmax⟩ := exists_longest_path hp
  -- The maximal path is not empty: an edge at its source could otherwise be prepended.
  obtain ⟨f, W', rfl⟩ : ∃ f W', W = f :: W' := by
    cases hW : W with
    | cons f W' => exact ⟨f, W', rfl⟩
    | nil =>
      obtain ⟨y, ⟨g, hl⟩, hyu⟩ := h.exists_adj_ne hnl hpath.left_mem u
      have hle := hmax _ _ _ (IsPath.single hl.symm hyu)
      rw [hW] at hle
      simp at hle
  obtain ⟨w₀, hl₀, hpath', hfresh⟩ : ∃ w₀, G.IsLink f u w₀ ∧ G.IsPath w₀ W' v ∧
      u ∉ G.walkVertices w₀ W' := by
    cases hpath with
    | cons hl hW hfr => exact ⟨_, hl, hW, hfr⟩
  -- A second neighbour of the source, distinct from the vertex the path first steps to.
  obtain ⟨x, ⟨g, hlg⟩, hxw₀⟩ := h.exists_adj_ne hnl hpath.left_mem w₀
  have hxu : x ≠ u := fun hh ↦ hnl (hh ▸ hlg)
  -- It lies on the path: otherwise the chord would prepend to it.
  have hxW : x ∈ G.walkVertices u (f :: W') := by
    by_contra hx
    have hle := hmax _ _ _ (IsPath.cons hlg.symm hpath hx)
    simp at hle
  obtain ⟨W₁, W₂, hsplit, h₁, -, -⟩ := hpath.split hxW
  have hW₁sub : W₁ ⊆ f :: W' := hsplit ▸ List.subset_append_left _ _
  -- The chord is not an edge of the piece: not the first edge, and not one further along.
  have hgW₁ : g ∉ W₁ := by
    intro hg
    rcases List.mem_cons.1 (hW₁sub hg) with rfl | hg'
    · exact hxw₀ (hlg.right_unique hl₀)
    · exact hfresh (mem_walkVertices_of_mem_covered ⟨g, hg', hlg.inc_left⟩)
  -- The piece starts with the first edge, so it visits the vertex the path first stepped to.
  have hfW₁ : f ∈ W₁ := by
    rcases W₁ with _ | ⟨a, T⟩
    · exact absurd h₁.isWalk.eq_of_nil (Ne.symm hxu)
    · obtain ⟨rfl, -⟩ : f = a ∧ W' = T ++ W₂ := by simpa using hsplit
      exact List.mem_cons_self
  exact ⟨g, u, x, W₁, w₀, ⟨hlg, h₁, hgW₁⟩,
    mem_walkVertices_of_mem_covered ⟨f, hfW₁, hl₀.inc_right⟩,
    fun hh ↦ hnl (hh ▸ hl₀), Ne.symm hxw₀⟩

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

open _root_.Graph in
/-- **A path graph grows with its edge list.** General, and not in
`Schoenflies/Graph/PathGraph.lean`; the integrator may want to hoist it. -/
theorem _root_.Graph.pathGraphOf_mono (h : W ⊆ D) : G.pathGraphOf u W ≤ G.pathGraphOf u D where
  vertexSet_mono := by
    simpa only [pathGraphOf_vertexSet] using walkVertices_mono (u := u) h
  isLink_mono := by
    intro f x y hl
    obtain ⟨hf, hxy, hx, hy⟩ := pathGraphOf_isLink.1 hl
    exact pathGraphOf_isLink.2
      ⟨h hf, hxy, walkVertices_mono h hx, walkVertices_mono h hy⟩

open _root_.Graph in
/-- The subgraph of `G` drawn by a cycle: the detour followed by the edge, as a closed walk.
Exported as the object rather than hidden behind an existential — the consumer of
`lem:face-cycles` needs the graph itself, to feed it to the ear decomposition. -/
def _root_.Graph.cycleGraph (G : Graph α β) (u : α) (e : β) (D : List β) : Graph α β :=
  G.pathGraphOf u (D ++ [e])

open _root_.Graph in
/-- The detour spans a path subgraph of the cycle. -/
theorem _root_.Graph.pathGraphOf_le_cycleGraph : G.pathGraphOf u D ≤ G.cycleGraph u e D :=
  pathGraphOf_mono (List.subset_append_left _ _)

section

variable (hc : G.IsCycleThrough e u v D)
include hc

open _root_.Graph in
/-- Going round: the detour and then the edge is a closed walk at the source. -/
theorem _root_.Graph.IsCycleThrough.isWalk_round : G.IsWalk u (D ++ [e]) u :=
  hc.isPath.isWalk.append (IsWalk.single hc.isLink.symm)

open _root_.Graph in
/-- Closing the cycle adds no vertex: both ends of the edge are already on the detour. -/
theorem _root_.Graph.IsCycleThrough.walkVertices_round : G.walkVertices u (D ++ [e]) = G.walkVertices u D := by
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (walkVertices_mono (List.subset_append_left _ _))
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with hcov | ⟨g, hg, hinc⟩
  · exact mem_walkVertices_of_mem_covered hcov
  obtain rfl : g = e := by simpa using hg
  rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
  · exact mem_walkVertices_self
  · exact hc.isPath.target_mem_walkVertices

open _root_.Graph in
@[simp]
theorem _root_.Graph.IsCycleThrough.cycleGraph_vertexSet : V(G.cycleGraph u e D) = G.walkVertices u D := by
  rw [cycleGraph, pathGraphOf_vertexSet, hc.walkVertices_round]

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.cycleGraph_le : G.cycleGraph u e D ≤ G := pathGraphOf_le hc.isWalk_round

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.cycleGraph_edgeSet : E(G.cycleGraph u e D) = {f | f ∈ D ++ [e]} :=
  pathGraphOf_edgeSet hc.isWalk_round

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.left_mem_cycleGraph : u ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact mem_walkVertices_self

open _root_.Graph in
theorem _root_.Graph.IsCycleThrough.right_mem_cycleGraph : v ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact hc.isPath.target_mem_walkVertices

open _root_.Graph in
/-- The edge of the cycle really is an edge of the cycle graph, joining the same two ends. -/
theorem _root_.Graph.IsCycleThrough.cycleGraph_isLink : (G.cycleGraph u e D).IsLink e u v :=
  pathGraphOf_isLink.2 ⟨by simp, hc.isLink,
    hc.walkVertices_round ▸ mem_walkVertices_self,
    hc.walkVertices_round ▸ hc.isPath.target_mem_walkVertices⟩

open _root_.Graph in
/-- The cycle graph is connected: every vertex it has is visited by the detour, and the
detour's own prefix runs there from the source. -/
theorem _root_.Graph.IsCycleThrough.cycleGraph_connected : (G.cycleGraph u e D).Connected := by
  refine Connected.of_hub hc.left_mem_cycleGraph fun x hx ↦ ?_
  rw [hc.cycleGraph_vertexSet] at hx
  obtain ⟨W₁, W₂, hcat, h₁, -, -⟩ := hc.isPath.split hx
  refine ⟨W₁, h₁.isWalk.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg ↦ ?_⟩
  rw [hc.cycleGraph_edgeSet]
  exact List.mem_append_left _ (hcat ▸ List.mem_append_left _ hg)

end

section

variable (h : G.IsLongCycle e u v D w)
include h

open _root_.Graph in
theorem _root_.Graph.IsLongCycle.mem_cycleGraph : w ∈ V(G.cycleGraph u e D) := by
  rw [h.isCycle.cycleGraph_vertexSet]; exact h.mem

open _root_.Graph in
/-- **A cycle with three vertices is 2-connected**, which is what
`Graph.IsTwoConnected.ear_decomposition` asks of its starting subgraph.

Delete a vertex `c`. One of the two ends of the cycle's edge survives, and it is the hub:
every remaining vertex reaches an end of the *detour* inside the detour
(`Graph.IsPathGraph.reaches_an_end`), an end which — having been reached after the deletion —
survived it too, so the cycle's edge is still there to carry it the rest of the way. -/
theorem _root_.Graph.IsLongCycle.isTwoConnected : (G.cycleGraph u e D).IsTwoConnected where
  hasThreeVertices :=
    ⟨u, h.isCycle.left_mem_cycleGraph, v, h.isCycle.right_mem_cycleGraph,
      w, h.mem_cycleGraph, h.ne, Ne.symm h.ne_left, Ne.symm h.ne_right⟩
  connected := h.isCycle.cycleGraph_connected
  deleteVerts_connected := by
    intro c _
    set Kc := G.cycleGraph u e D with hKc
    set Pc := G.pathGraphOf u D with hPc
    have hPK : Pc.deleteVerts {c} ≤ Kc.deleteVerts {c} :=
      deleteVerts_mono pathGraphOf_le_cycleGraph _
    have hPpath : Pc.IsPathGraph u D v := h.isPath.isPathGraph_pathGraphOf
    -- The hub is whichever end of the cycle's edge survived; the argument is symmetric in
    -- the two, so it is done once for a named pair and applied twice.
    have main : ∀ a b : α, Kc.IsLink e a b → a ≠ c →
        (∀ x ∈ V(Kc), x ≠ c →
          (Pc.deleteVerts {c}).Reaches x a ∨ (Pc.deleteVerts {c}).Reaches x b) →
        (Kc.deleteVerts {c}).Connected := by
      intro a b hab hac hends
      refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hab.left_mem hac) fun x hx ↦ ?_
      rw [vertexSet_deleteVerts] at hx
      obtain ⟨hxK, hxc⟩ := hx
      have hxc' : x ≠ c := by simpa using hxc
      rcases hends x hxK hxc' with hr | hr
      · exact (hr.mono hPK).symm
      · -- The far end was reached, so it survived; the cycle's edge joins it to the hub.
        have hbc : b ≠ c := (mem_deleteVerts_singleton.1 (hr.mono hPK).right_mem).2
        have hedge : (Kc.deleteVerts {c}).Reaches b a :=
          ⟨[e], IsWalk.single ((deleteVerts_isLink _ _).2 ⟨hab.symm, by simpa using hbc,
            by simpa using hac⟩)⟩
        exact ((hr.mono hPK).trans hedge).symm
    have hV : ∀ x ∈ V(Kc), x ∈ V(Pc) := fun x hx ↦ by
      rw [hKc, h.isCycle.cycleGraph_vertexSet] at hx; exact hx
    by_cases hcu : u = c
    · -- The source is gone, so the target is the hub.
      refine main v u h.isCycle.cycleGraph_isLink.symm (fun hh ↦ h.ne (hh.trans hcu.symm).symm)
        fun x hx hxc ↦ (hPpath.reaches_an_end (hV x hx) hxc).symm
    · exact main u v h.isCycle.cycleGraph_isLink hcu
        fun x hx hxc ↦ hPpath.reaches_an_end (hV x hx) hxc

end

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

open _root_.Graph in
/-- **An edge of a path incident to its source is the path's first edge**, in the form that
decomposes the path — `Graph.IsPath.eq_head_of_inc_source` says the same about a list already
known to be a cons, and is what does the work here. -/
theorem _root_.Graph.IsPath.eq_cons_of_inc_left (h : G.IsPath u D v) (hg : g ∈ D) (hinc : G.Inc g u) :
    ∃ w T, D = g :: T ∧ G.IsLink g u w ∧ G.IsPath w T v := by
  cases D with
  | nil => simp at hg
  | cons a T =>
    obtain rfl : g = a := h.eq_head_of_inc_source hg hinc
    cases h with
    | cons hl hT _ => exact ⟨_, T, rfl, hl, hT⟩

open _root_.Graph in
/-- **An edge of an ear that the subgraph already has is the whole ear.** Both ends of such an
edge lie in the subgraph, so the ear's freshness clause makes them the ear's own two ends; the
edge is then the ear's first edge and its far end is the ear's target, so nothing follows it.
-/
theorem _root_.Graph.IsPath.eq_singleton_of_edge_mem (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B))
    (hg : g ∈ D) (hgB : g ∈ E(B)) : D = [g] ∧ G.IsLink g u v := by
  -- Both ends of the edge lie in the subgraph, so both are ends of the path.
  have hends : ∀ y, G.Inc g y → y = u ∨ y = v := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact hint y (mem_walkVertices_of_mem_covered ⟨g, hg, hy⟩) hcon.1 hcon.2
      (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hy)
  -- The edge is not a loop, so its two ends are exactly the two ends of the path.
  obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (hpath.edge_mem hg)
  have hpqne : p ≠ q := by rintro rfl; exact hpath.not_isLoopAt hg p hpq
  have hincu : G.Inc g u := by
    rcases hends p hpq.inc_left with rfl | rfl
    · exact hpq.inc_left
    · rcases hends q hpq.inc_right with rfl | rfl
      · exact hpq.inc_right
      · exact absurd rfl hpqne
  -- So it is the path's first edge, and its far end is the path's target.
  obtain ⟨w, T, rfl, hl, hT⟩ := hpath.eq_cons_of_inc_left hg hincu
  have hwv : w = v := by
    rcases hends w hl.inc_right with rfl | hh
    · exact absurd hl (hpath.not_isLoopAt List.mem_cons_self _)
    · exact hh
  subst hwv
  exact ⟨by rw [hT.eq_nil_of_eq], hl⟩

open _root_.Graph in
/-- **Either every edge of the ear is new, or the ear changes nothing.** The disjunction the
step of `Graph.IsTwoConnected.ear_decomposition` has to open before it can do any geometry. -/
theorem _root_.Graph.ear_edges_notMem_or_union_eq (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hu : u ∈ V(B)) (hv : v ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B)) :
    (∀ g ∈ D, g ∉ E(B)) ∨ B.union (G.pathGraphOf u D) = B := by
  by_cases hall : ∀ g ∈ D, g ∉ E(B)
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨g, hg, hgB⟩ := hall
  obtain ⟨rfl, hl⟩ := hpath.eq_singleton_of_edge_mem hBG huv hint hg hgB
  -- The ear is a single edge the subgraph already carries, joining two of its own vertices.
  refine le_antisymm (union_le le_rfl ?_) (left_le_union _ _)
  refine ⟨fun y hy ↦ ?_, fun f x y hf ↦ ?_⟩
  · rcases mem_walkVertices_iff.1 (pathGraphOf_vertexSet ▸ hy) with rfl | ⟨f, hf, hinc⟩
    · exact hu
    · obtain rfl : f = g := by simpa using hf
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      exacts [hu, hv]
  · obtain ⟨hfg, hxy, -, -⟩ := pathGraphOf_isLink.1 hf
    obtain rfl : f = g := by simpa using hfg
    exact (hBG.isLink_iff hgB).2 hxy

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

open _root_.Graph in
/-- What a union of two plane graphs occupies is what the two of them occupy. -/
@[simp]
theorem _root_.Graph.pointSet_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet (B.union P) drawing = pointSet B drawing ∪ pointSet P drawing := by
  simp only [pointSet, vertexSet_union, edgeSet_union, Set.biUnion_union]
  ext w
  simp only [Set.mem_union]
  tauto

open _root_.Graph in
/-- Adding a graph removes exactly its own point set from the exterior. -/
theorem _root_.Graph.exterior_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    exterior (B.union P) drawing = exterior B drawing \ pointSet P drawing := by
  rw [exterior, exterior, pointSet_union, Set.compl_union]
  rfl

open _root_.Graph in
/-- A face of the enlarged graph lies inside a face of the old one. -/
theorem _root_.Graph.face_union_subset : face (B.union P) drawing z ⊆ face B drawing z := by
  by_cases hz : z ∈ exterior (B.union P) drawing
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hz) fun w hw ↦ ?_
    exact ((exterior_union B P drawing) ▸ face_subset_exterior _ _ _ hw).1
  · rw [face, connectedComponentIn_eq_empty hz]
    exact Set.empty_subset _

open _root_.Graph in
/-- **"All other faces are unchanged."** A face the ear does not touch survives the ear. -/
theorem _root_.Graph.face_union_eq_of_disjoint (hz : z ∈ exterior B drawing)
    (hdis : Disjoint (face B drawing z) (pointSet P drawing)) :
    face (B.union P) drawing z = face B drawing z := by
  refine Set.Subset.antisymm face_union_subset ?_
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_face hz) fun w hw ↦ ?_
  rw [exterior_union]
  exact ⟨face_subset_exterior _ _ _ hw, fun hwP ↦ Set.disjoint_left.1 hdis hw hwP⟩

open _root_.Graph in
/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face."** The topological half: a nonempty preconnected subset of the exterior lies in one
face. -/
theorem _root_.Graph.exists_face_of_isPreconnected (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hsub : S ⊆ exterior B drawing) :
    ∃ z ∈ exterior B drawing, S ⊆ face B drawing z := by
  obtain ⟨z, hz⟩ := hSne
  exact ⟨z, hsub hz, hS.subset_connectedComponentIn hz hsub⟩

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

open _root_.Graph in
/-- **The ear's realisation meets the drawing of the current subgraph only in the ear's two
ends.** Two cases, and both come down to the ear's freshness clause: a point of the ear on a
*vertex* of `B` is an end of the edge of the ear it lies on
(`Graph.IsDrawing.vertex_mem_edgeArc`), and a point of the ear on an *edge* of `B` is a vertex
incident with both (`Graph.IsDrawing.edge_inter`) — the two edges being distinct because no
edge of the ear belongs to `B`. Either way the point is a vertex of `B` that the ear visits,
which the freshness clause makes one of the ear's two ends. -/
theorem _root_.Graph.IsDrawing.edgesCover_inter_pointSet (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    edgesCover drawing D ∩ pointSet B drawing ⊆ {a, b} := by
  -- A vertex of `B` that an edge of the ear is incident with is one of the ear's two ends.
  have key : ∀ p, (∃ f ∈ D, G.Inc f p) → p ∈ V(B) → p = a ∨ p = b := by
    rintro p ⟨f, hf, hinc⟩ hpB
    by_contra hcon
    push Not at hcon
    exact hint p (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hcon.1 hcon.2 hpB
  rintro p ⟨hpD, hpB⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hpD
  have hfG : f ∈ E(G) := hpath.edge_mem hf
  rcases hpB with hpV | hpE
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hfG
    have hinc : G.Inc f p := by
      rcases hG.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpf with rfl | rfl
      exacts [hxy.inc_left, hxy.inc_right]
    exact key p ⟨f, hf, hinc⟩ hpV
  · simp only [Set.mem_iUnion, exists_prop] at hpE
    obtain ⟨g, hgB, hpg⟩ := hpE
    have hfg : f ≠ g := fun hh ↦ hnew f hf (hh ▸ hgB)
    obtain ⟨-, hincf, hincg⟩ := hG.edge_inter hfG (hBG.edgeSet_mono hgB) hfg hpf hpg
    exact key p ⟨f, hf, hincf⟩ (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hincg)

open _root_.Graph in
/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face `F`."** The ear's realisation without its two ends is an arc's interior, hence connected,
and it misses the drawing of `B` altogether, so it lies in a single face. -/
theorem _root_.Graph.IsDrawing.exists_face_of_ear (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b) (hab : a ≠ b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    ∃ z ∈ exterior B drawing, edgesCover drawing D \ {a, b} ⊆ face B drawing z := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hconn := harc.isConnected_diff
  refine exists_face_of_isPreconnected hconn.isPreconnected hconn.nonempty fun w hw hwB ↦ ?_
  exact hw.2 (hG.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hwB⟩)

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

open _root_.Graph in
/-- **A subgraph of a plane graph is a plane graph**, with the same drawing. -/
theorem _root_.Graph.IsDrawing.mono (hG : IsDrawing G drawing) (hBG : B ≤ G) : IsDrawing B drawing where
  edge_param := fun e he ↦ by
    obtain ⟨hc, hi, hl⟩ := hG.edge_param (hBG.edgeSet_mono he)
    exact ⟨hc, hi, (hBG.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hmem ↦
    hG.vertex_mem_edgeArc (hl.mono hBG) (hBG.vertexSet_mono hv) hmem
  edge_inter := fun e f he hf hef p hpe hpf ↦ by
    obtain ⟨-, hince, hincf⟩ :=
      hG.edge_inter (hBG.edgeSet_mono he) (hBG.edgeSet_mono hf) hef hpe hpf
    obtain ⟨y, hy⟩ := hince
    obtain ⟨y', hy'⟩ := hincf
    exact ⟨mem_vertexSet_of_inc_of_mem_edgeSet hBG he ⟨y, hy⟩,
      ⟨y, (hBG.isLink_iff he).2 hy⟩, ⟨y', (hBG.isLink_iff hf).2 hy'⟩⟩

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

open _root_.Graph in
/-- **"The ear's two endpoints are limits of its interior, which lies in `F`, so they lie on
`∂F`."** This is the hypothesis `thm:polygonal-crosscut` needs of a crosscut: its two ends are
on the boundary curve of the region it cuts. -/
theorem _root_.Graph.IsDrawing.ends_mem_frontier_face (hG : IsDrawing G drawing)
    (hopen : IsOpen (face B drawing z)) (hpath : G.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing D \ {a, b} ⊆ face B drawing z) :
    a ∈ frontier (face B drawing z) ∧ b ∈ frontier (face B drawing z) := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hnot : ∀ y ∈ V(B), y ∉ face B drawing z := fun y hy hyf ↦
    face_subset_exterior _ _ _ hyf (vertexSet_subset_pointSet hy)
  refine ⟨⟨closure_mono hsub harc.left_mem_closure_diff, ?_⟩,
    ⟨closure_mono hsub harc.right_mem_closure_diff, ?_⟩⟩
  · rw [hopen.interior_eq]; exact hnot a ha
  · rw [hopen.interior_eq]; exact hnot b hb

end Plane

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/SegmentCut.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

open _root_.Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting a segment at one of its points loses nothing: the two halves cover it. -/
theorem segment_split (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · -- `x` lies on the near half. Rescale `v` by `β`, unless `β = 0`, when the cut is at `a`.
    left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hvβ' : v / β * β = v := div_mul_cancel₀ v hβne
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        calc (1 - v / β) + (v / β) * α
            = (1 - v / β) + (v / β) * (1 - β) := by rw [hα']
          _ = 1 - v / β * β := by ring
          _ = 1 - v := by rw [hvβ']
          _ = u := by linarith
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hvβ']
  · -- `x` lies on the far half. Rescale `u` by `α`, which is positive because `v > β`.
    right
    have hαpos : 0 < α := by linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have huα : u ≤ α := by linarith
    refine ⟨u / α, 1 - u / α, by positivity, by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ huα hαpos.le, by ring, ?_⟩
    have huα' : u / α * α = u := div_mul_cancel₀ u hαne
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hβ' : β = 1 - α := by linarith
      calc (u / α) * β + (1 - u / α)
          = (u / α) * (1 - α) + (1 - u / α) := by rw [hβ']
        _ = 1 - u / α * α := by ring
        _ = 1 - u := by rw [huα']
        _ = v := by linarith
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef, huα']

/-- Cutting is permanent, near half: the interior of the near piece stays inside the
interior of the whole. -/
theorem openSegment_left_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s + t * α, t * β, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/-- Cutting is permanent, far half. -/
theorem openSegment_right_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s * α, s * β + t, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/SegmentOrder.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Along one segment: the distance from an end as a coordinate

Everything the polygonal overlay has to say about several collinear segments — which piece
lies inside which, where a piece may end, when two pieces have to coincide — is
one-dimensional: it happens along a single straight segment. This module supplies the
coordinate that makes it ordinary arithmetic. Along a nondegenerate `segment ℝ a b` the
distance from `a` determines the point, and it reads betweenness off as a pair of
inequalities, so a claim about four collinear points becomes a claim about four reals.

No new geometry is needed. `dist_left_lineMap` already says the distance from `a` *is* the
parameter of `AffineMap.lineMap a b`, scaled by the segment's length, and `image_segment`
already says that parametrization carries segments of `ℝ` to segments of the plane. What is
added here is the translation, stated once so that the arithmetic does not have to be redone
at every use.

The two results the module exists for come last, and they are what makes cutting at every
meet enough:

* a piece that meets an overlap and keeps the overlap's ends out of its interior lies inside
  the overlap (`segment_inside_of_ends_outside`);
* two pieces whose interiors meet, each keeping the other's ends out of its interior, are the
  same pair of points (`same_ends_of_meeting_interiors`).

Both are stated **inside one ambient segment**. Collinearity is not optional: a piece crossing
the overlap transversally would meet it and avoid both its ends without lying inside it, so
every point named is a point of one ambient `segment ℝ a b`.

Both are also stated with no orientation asked of the caller. The `_oriented` forms they wrap
are near-end-first, which is what the arithmetic wants; the unoriented forms decide the
orientation themselves, and they are what the overlay uses.

## A note on degenerate pieces

Mathlib's `openSegment ℝ u u` is `{u}`, not `∅`. A degenerate piece therefore has a nonempty
interior, and the strict translation `dist_lt_of_mem_openSegment` genuinely needs `u ≠ v`.
The two headline theorems do *not* ask for it: in each of them a degenerate piece is either
excluded by the hypotheses or settled outright, and that case split lives inside the proof.

## Blueprint

* `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` — the separation behind
  the deduplication clause of the polygonal overlay (`lem:polygonal-overlay`, "represent every
  duplicate geometric subsegment only once") and of the subdivision in
  `lem:polygonal-connected` ("delete duplicate subsegments"): once every piece's ends are cut
  points, and so interior to nothing, two pieces that share an interior point coincide instead
  of merely overlapping.
-/

open _root_.Set

namespace Schoenflies

variable {a b : Plane}

/-! ### The parametrization of a segment

`AffineMap.lineMap a b` walks from `a` to `b`. It carries a segment of `ℝ` onto the
corresponding piece of `[a, b]`, and it turns the distance from `a` into multiplication by
the segment's length. Those two facts are the whole content of the module; the rest is
arithmetic. -/

/-- The distance from the left endpoint to the point at parameter `t` is `t` times the
segment's length. This is `dist_left_lineMap` with the absolute value discharged. -/
theorem dist_left_lineMap_of_nonneg (a b : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist a (AffineMap.lineMap a b t) = t * dist a b := by
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The piece of `[a, b]` spanned by two parameters is the image of the segment they span. -/
theorem segment_lineMap_image (a b : Plane) (p q : ℝ) :
    segment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' segment ℝ p q := by
  simp

/-- The same for interiors. -/
theorem openSegment_lineMap_image (a b : Plane) (p q : ℝ) :
    openSegment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' openSegment ℝ p q := by
  simp

/-- Every point of `[a, b]` carries a parameter: a number `t ∈ [0, 1]` placing it on the
segment, whose distance from `a` is `t` times the segment's length. This is the only way the
rest of the module looks at a point of the segment. -/
theorem exists_param_of_mem_segment {x : Plane} (hx : x ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap a b t = x ∧ dist a x = t * dist a b := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  exact ⟨t, ht0, ht1, rfl, dist_left_lineMap_of_nonneg a b ht0⟩

/-! ### The coordinate -/

/-- Along a nondegenerate segment, the distance from the left endpoint **orders the
parameters**: a nonzero length cancels from `s * ‖b - a‖ ≤ t * ‖b - a‖`. -/
theorem parameter_le_of_distance (hab : a ≠ b) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : dist a (AffineMap.lineMap a b s) ≤ dist a (AffineMap.lineMap a b t)) : s ≤ t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  rw [dist_left_lineMap_of_nonneg a b hs, dist_left_lineMap_of_nonneg a b ht] at h
  exact le_of_mul_le_mul_right (by linarith) hd

/-- The distance from `a` determines the point: two points of a nondegenerate `[a, b]` at
equal distance from `a` are equal. -/
theorem eq_of_dist_left_eq (hab : a ≠ b) {x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (h : dist a x = dist a y) : x = y := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨s, -, -, rfl, hsd⟩ := exists_param_of_mem_segment hx
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hy
  rw [hsd, htd] at h
  rw [mul_right_cancel₀ (ne_of_gt hd) h]

/-! ### Betweenness as a pair of inequalities -/

/-- A point between two points of the segment is between them in distance from `a` as well:
measured from `a`, the nearer end comes first. -/
theorem dist_le_of_mem_segment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : dist a u ≤ dist a v) (hx : x ∈ segment ℝ u v) :
    dist a u ≤ dist a x ∧ dist a x ≤ dist a v := by
  have hd : (0 : ℝ) ≤ dist a b := dist_nonneg
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p ≤ q := parameter_le_of_distance hab hp0 hq0 huv
  -- The parametrization carries `[p, q]` onto the piece, so `x` has a parameter in `[p, q]`.
  rw [segment_lineMap_image, segment_eq_Icc hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment whose distance from `a` lies between the two ends'
distances lies between the ends. -/
theorem mem_segment_of_dist_le (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u ≤ dist a x)
    (h₂ : dist a x ≤ dist a v) : x ∈ segment ℝ u v := by
  obtain ⟨p, hp0, -, rfl, -⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, -⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, ht0, -, rfl, -⟩ := exists_param_of_mem_segment hx
  have hpt : p ≤ t := parameter_le_of_distance hab hp0 ht0 h₁
  have htq : t ≤ q := parameter_le_of_distance hab ht0 hq0 h₂
  rw [segment_lineMap_image, segment_eq_Icc (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### The same translation for interiors

`openSegment ℝ u u = {u}` in Mathlib, so the strict form asks for a nondegenerate piece; its
converse does not, since strict inequalities force nondegeneracy on their own. -/

/-- A point interior to a nondegenerate piece of the segment is strictly between its ends in
distance from `a`. -/
theorem dist_lt_of_mem_openSegment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : u ≠ v) (hor : dist a u ≤ dist a v)
    (hx : x ∈ openSegment ℝ u v) : dist a u < dist a x ∧ dist a x < dist a v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p < q :=
    lt_of_le_of_ne (parameter_le_of_distance hab hp0 hq0 hor) fun h => huv (by rw [h])
  rw [openSegment_lineMap_image, openSegment_eq_Ioo hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt.le)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment strictly between the ends in distance from `a` is
interior to the piece they span. -/
theorem mem_openSegment_of_dist_lt (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u < dist a x)
    (h₂ : dist a x < dist a v) : x ∈ openSegment ℝ u v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, -, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, -, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hx
  rw [hpd, htd] at h₁
  rw [htd, hqd] at h₂
  have hpt : p < t := lt_of_mul_lt_mul_right h₁ hd.le
  have htq : t < q := lt_of_mul_lt_mul_right h₂ hd.le
  rw [openSegment_lineMap_image, openSegment_eq_Ioo (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### Where a point that is not interior to a piece must sit

These two carry the whole one-dimensional argument. A point of the ambient segment kept out
of a piece's interior has to be outside on one side or the other, and knowing which side it
is not settles it. -/

/-- A point of the ambient segment kept out of `[u, v]`'s interior and lying before `v` lies
at or before `u`. -/
theorem dist_le_left_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a y < dist a v) : dist a y ≤ dist a u := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy (lt_of_not_ge hcon) hlt)

/-- The mirror: a point of the ambient segment kept out of `[u, v]`'s interior and lying
after `u` lies at or after `v`. -/
theorem le_dist_right_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a u < dist a y) : dist a v ≤ dist a y := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy hlt (lt_of_not_ge hcon))

/-! ### What the overlay is after -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap — near-end-first form. -/
theorem segment_inside_of_ends_outside_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hpiece : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hover : dist a s ≤ dist a t)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  -- A degenerate overlap is impossible: its only interior point is `s`, which by hypothesis
  -- is not interior to the piece, whereas `x` is.
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxo
    rw [← hxo] at hsout
    exact absurd hxp hsout
  -- A degenerate piece is the single point `x`, which already lies in the overlap.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxp
    rw [segment_same, singleton_subset_iff, ← hxp]
    exact openSegment_subset_segment ℝ s t hxo
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hpiece hxp
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hover hxo
  -- The overlap starts at or before the piece and ends at or after it.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  intro y hy
  have hyab : y ∈ segment ℝ a b := (convex_segment a b).segment_subset hu hv hy
  obtain ⟨huy, hyv⟩ := dist_le_of_mem_segment hab hu hv hpiece hy
  exact mem_segment_of_dist_le hab hs ht hyab (hsu.trans huy) (hyv.trans hvt)

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, have the same ends — near-end-first form. -/
theorem same_ends_of_meeting_interiors_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hfirst : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hsecond : dist a s ≤ dist a t)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    u = s ∧ v = t := by
  -- Neither piece can be degenerate: its only interior point would then be one of its own
  -- ends, which the other piece is required to keep out of its interior.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxu
    rw [← hxu] at huout
    exact absurd hxs huout
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxs
    rw [← hxs] at hsout
    exact absurd hxu hsout
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hfirst hxu
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hsecond hxs
  -- Each piece's near end lies at or before the other's, so they agree.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hus : dist a u ≤ dist a s :=
    dist_le_left_of_notMem_openSegment hab hs ht hu huout (hux.trans hxt)
  -- And the same on the far side.
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  have htv : dist a t ≤ dist a v :=
    le_dist_right_of_notMem_openSegment hab hs ht hv hvout (hsx.trans hxv)
  exact ⟨eq_of_dist_left_eq hab hu hs (le_antisymm hus hsu),
    eq_of_dist_left_eq hab hv ht (le_antisymm hvt htv)⟩

/-! ### The same two, asking the caller nothing about orientation

A piece is a pair of ends, and which of them is nearer `a` is none of the caller's business —
`segment` and `openSegment` do not care. The oriented forms above are near-end-first because
that is what the arithmetic wants; these decide the orientation themselves. Every hypothesis
is restated in both spellings first, so each of the four cases is just "which way round, then
cite". -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap.

Collinearity is not optional: every point named is a point of one ambient `segment ℝ a b`. A
piece crossing the overlap transversally would meet it and avoid both its ends without lying
inside it. -/
theorem segment_inside_of_ends_outside (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  have hxp' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxo' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hrevPiece : segment ℝ v u = segment ℝ u v := segment_symm ℝ v u
  have hrevOverlap : segment ℝ t s = segment ℝ s t := segment_symm ℝ t s
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact segment_inside_of_ends_outside_oriented hab hu hv hp hs ht ho hxp hxo hsout htout
  · rw [← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hu hv hp ht hs ho hxp hxo' htout hsout
  · rw [← hrevPiece]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp hs ht ho hxp' hxo hsout' htout'
  · rw [← hrevPiece, ← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp ht hs ho hxp' hxo' htout' hsout'

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, are the same pair of points — in one order or the other.

This is the separation the deduplication clause is for: overlapping collinear pieces cannot
be pulled apart by cutting, and after enough cuts they coincide instead. -/
theorem same_ends_of_meeting_interiors (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    (u = s ∧ v = t) ∨ (u = t ∧ v = s) := by
  have hxu' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxs' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have huout' : u ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hvout' : v ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact Or.inl (same_ends_of_meeting_interiors_oriented hab hu hv hp hs ht ho hxu hxs
      hsout htout huout hvout)
  · exact Or.inr (same_ends_of_meeting_interiors_oriented hab hu hv hp ht hs ho hxu hxs'
      htout hsout huout' hvout')
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp hs ht ho hxu' hxs
      hsout' htout' hvout huout
    exact Or.inr ⟨h₂, h₁⟩
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp ht hs ho hxu' hxs'
      htout' hsout' hvout' huout'
    exact Or.inl ⟨h₂, h₁⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Subdivide.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Subdividing a list of segments

A polygonal edge **is** its pair of endpoints: a straight segment is determined by its ends,
so naming one by anything else names a distinction that does not exist. `Piece := Plane ×
Plane`, and the blueprint's "represent every duplicate geometric subsegment only once"
becomes deduplication of a list of *names*, with no geometry in it.

**The subdivision recurses on the POINT list, not on the segment.** `subdivide pieces points`
cuts every current piece at the head point and recurses with the rest. Read literally the
blueprint wants the cut points as data, which would need a choice operator (the meets are
existential) and then a sort (to order them along each segment). Neither is required: order
does not matter, because cutting at a point that has already become an endpoint is a no-op.

Three facts about one cut, each lifted across the piece list and then across the point list:

* `subdivide_cover` — cutting loses nothing, so a subdivision occupies what it came from;
* `subdivide_ne` — no piece degenerates, so the drawing condition's invariant survives;
* `subdivide_interior_subset` — every piece's interior lies inside the interior of a piece
  it came from. This is what makes a cut **permanent**: nothing later can put a removed point
  back into an interior.

## Blueprint

* `Piece`, `cover` — the segment representation and what a list of them occupies.
* `subdivide` and its three properties — the cutting half of Lemma 3.7 (polygonal overlay).
-/

open Metric _root_.Set

namespace Schoenflies

/-- A polygonal edge is its pair of endpoints. -/
abbrev Piece := Plane × Plane

namespace Piece

/-- The closed segment a piece occupies. -/
def seg (P : Piece) : Set Plane := segment ℝ P.1 P.2

/-- The interior of a piece. -/
def interior (P : Piece) : Set Plane := openSegment ℝ P.1 P.2

/-- A piece is nondegenerate when its two ends differ. -/
def Nondeg (P : Piece) : Prop := P.1 ≠ P.2

end Piece

/-- What a list of pieces occupies. -/
def cover (pieces : List Piece) : Set Plane := ⋃ P ∈ pieces, P.seg

@[simp] theorem cover_nil : cover [] = ∅ := by simp [cover]

@[simp] theorem cover_cons (P : Piece) (ps : List Piece) :
    cover (P :: ps) = P.seg ∪ cover ps := by
  simp [cover]

theorem cover_append (ps qs : List Piece) : cover (ps ++ qs) = cover ps ∪ cover qs := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.cons_append, cover_cons, cover_cons, ih, union_assoc]

theorem cover_flatMap (f : Piece → List Piece) (ps : List Piece) :
    cover (ps.flatMap f) = ⋃ P ∈ ps, cover (f P) := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.flatMap_cons, cover_append, ih]; simp

/-! ### One cut -/

open scoped Classical in
/-- Cut one piece at one point: two pieces if the point is interior to it, and the piece
unchanged otherwise. Cutting at a point that is already an endpoint is a no-op. -/
noncomputable def splitAt (p : Plane) (P : Piece) : List Piece :=
  if p ∈ P.interior then [(P.1, p), (p, P.2)] else [P]

theorem splitAt_cover (p : Plane) (P : Piece) : cover (splitAt p P) = P.seg := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    simp only [cover_cons, cover_nil, union_empty]
    exact (segment_split hp).symm
  · simp

/-- Cutting at an interior point leaves both halves nondegenerate: an interior point differs
from both ends. -/
theorem splitAt_ne (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, Q.Nondeg := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    -- `p` is strictly inside, so it is neither end.
    have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

/-- Cutting is permanent: each half's interior lies inside the whole's. -/
theorem splitAt_interior_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact openSegment_left_subset h
    · rcases List.mem_singleton.1 hQ with rfl
      exact openSegment_right_subset h
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact subset_rfl

/-- After cutting at `p`, no piece has `p` in its interior.

Nondegeneracy is needed: a degenerate piece `(p, p)` has `p` in its interior and cutting it
produces two more copies of itself. -/
theorem splitAt_avoids (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, p ∉ Q.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact fun hmem => h1 (right_mem_openSegment_iff.1 hmem)
    · rcases List.mem_singleton.1 hQ with rfl
      exact fun hmem => h2 (left_mem_openSegment_iff.1 hmem)
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact h

/-! ### One cut, across the whole list -/

/-- Cut every piece of the list at one point. -/
noncomputable def splitAllAt (p : Plane) (pieces : List Piece) : List Piece :=
  pieces.flatMap (splitAt p)

theorem splitAllAt_cover (p : Plane) (pieces : List Piece) :
    cover (splitAllAt p pieces) = cover pieces := by
  rw [splitAllAt, cover_flatMap]
  simp only [splitAt_cover]
  rfl

theorem splitAllAt_ne (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_ne p (h P hP) Q hQP

theorem splitAllAt_interior_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_interior_subset p P Q hQP⟩

theorem splitAllAt_avoids (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, p ∉ Q.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_avoids p (h P hP) Q hQP

/-! ### The subdivision -/

/-- Subdivide a list of pieces at a list of points, recursing on the POINT list: cut every
current piece at the head, then carry on with the tail. -/
noncomputable def subdivide (pieces : List Piece) : List Plane → List Piece
  | [] => pieces
  | p :: ps => subdivide (splitAllAt p pieces) ps

@[simp] theorem subdivide_nil (pieces : List Piece) : subdivide pieces [] = pieces := rfl

@[simp] theorem subdivide_cons (pieces : List Piece) (p : Plane) (ps : List Plane) :
    subdivide pieces (p :: ps) = subdivide (splitAllAt p pieces) ps := rfl

/-- Cutting loses nothing: a subdivision occupies exactly what it came from. -/
theorem subdivide_cover (pieces : List Piece) (points : List Plane) :
    cover (subdivide pieces points) = cover pieces := by
  induction points generalizing pieces with
  | nil => rfl
  | cons p ps ih => rw [subdivide_cons, ih, splitAllAt_cover]

/-- No piece degenerates. -/
theorem subdivide_ne {pieces : List Piece} (points : List Plane)
    (h : ∀ P ∈ pieces, P.Nondeg) : ∀ Q ∈ subdivide pieces points, Q.Nondeg := by
  induction points generalizing pieces with
  | nil => exact h
  | cons p ps ih => exact ih (splitAllAt_ne p h)

/-- Every piece's interior lies inside the interior of a piece it came from. This is what
makes a cut permanent. -/
theorem subdivide_interior_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP⟩ := splitAllAt_interior_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP⟩

/-- After subdividing, no cut point is interior to any piece. Permanence is what makes this
work: a later cut only shrinks interiors, so a point removed early stays removed. -/
theorem subdivide_avoids {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ Q ∈ subdivide pieces points, p ∉ Q.interior := by
  induction points generalizing pieces with
  | nil => simp
  | cons p ps ih =>
    intro q hq Q hQ
    rcases List.mem_cons.1 hq with rfl | hq
    · -- `q` was cut out at this step; permanence keeps it out of every later piece.
      obtain ⟨R, hR, hQR⟩ := subdivide_interior_subset (splitAllAt q pieces) ps Q hQ
      exact fun hmem => splitAllAt_avoids q hnd R hR (hQR hmem)
    · exact ih (pieces := splitAllAt p pieces) (splitAllAt_ne p hnd) q hq Q hQ

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/SegmentMeet.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# How two segments meet

Two segments meet in nothing, or in a segment. The blueprint says "the empty set, one
point, or one closed interval" (Lemma 3.7, polygonal overlay); a point *is* a segment with
equal endpoints, so the statement folds to a dichotomy, and that is the form the overlay
wants — it subdivides at the endpoints of whatever the meet turns out to be, and a
degenerate meet contributes one subdivision point.

No case analysis on whether the segments are parallel, and no determinant. The meet is
compact and convex, so its preimage under the parametrization `lineMap a b` is a compact
convex subset of `ℝ`, hence a closed interval; pushing that interval forward is a segment.

## Blueprint

* `segment_inter_segment` — the meet dichotomy used by Lemma 3.7.
-/

open Metric _root_.Set

namespace Schoenflies

/-- Two segments meet in nothing, or in a segment. -/
theorem segment_inter_segment (a b c d : Plane)
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ p q : Plane, segment ℝ a b ∩ segment ℝ c d = segment ℝ p q := by
  set S : Set Plane := segment ℝ a b ∩ segment ℝ c d with hSdef
  have hScompact : IsCompact S := (isCompact_segment a b).inter (isCompact_segment c d)
  have hSconvex : Convex ℝ S := (convex_segment a b).inter (convex_segment c d)
  -- Pull the meet back along the parametrization of the first segment.
  set f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a b with hfdef
  set T : Set ℝ := Icc 0 1 ∩ f ⁻¹' S with hTdef
  -- `T` carries `S` forward. Note this needs no injectivity of `f`, so the degenerate case
  -- `a = b` is not a separate case.
  have himage : f '' T = S := by
    refine subset_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ht.2
    · have : x ∈ segment ℝ a b := hx.1
      rw [segment_eq_image_lineMap] at this
      obtain ⟨t, ht, rfl⟩ := this
      exact ⟨t, ⟨ht, hx⟩, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have : x ∈ f '' T := by rw [himage]; exact hx
    obtain ⟨t, ht, -⟩ := this
    exact ⟨t, ht⟩
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.inter (hScompact.isClosed.preimage AffineMap.lineMap_continuous))
      inter_subset_left
  have hTconvex : Convex ℝ T := (convex_Icc 0 1).inter (hSconvex.affine_preimage f)
  -- A nonempty compact convex subset of `ℝ` is a closed interval.
  obtain ⟨t₀, t₁, hTIcc⟩ : ∃ t₀ t₁, T = Icc t₀ t₁ :=
    ⟨_, _, eq_Icc_of_connected_compact ⟨hTne, hTconvex.isPreconnected⟩ hTcompact⟩
  have hle : t₀ ≤ t₁ := by
    rw [hTIcc] at hTne
    exact nonempty_Icc.1 hTne
  exact ⟨f t₀, f t₁, by rw [← himage, hTIcc, ← segment_eq_Icc hle, image_segment]⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Overlay.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The polygonal overlay

Finitely many segments become a plane graph once they are subdivided at their meets and each
duplicated subsegment is named once (`lem:polygonal-overlay`).

## Blueprint

* `polygonal_overlay` — Lemma 3.7 (polygonal overlay).
-/

open Metric _root_.Set

namespace Schoenflies

/-! ### Two more properties of `subdivide`

Both belong in `Schoenflies/Subdivide.lean` beside the other four; they are here because that
module is on `main`.

`subdivide_subset` is `subdivide_interior_subset` with the **closed** inclusion carried
alongside the open one, in one existential: separation reads a piece's ends off its source
segment and its interior off the source's interior, and it needs both at the same source.

`subdivide_ends` is the endpoint criterion — an end of a piece that is not a cut point was an
end all along. Without it the case of two pieces from different sources does not close: two
different subpieces can both sit inside one long overlap. -/

/-- Cutting one piece keeps each half inside the whole, closed and open at once. -/
theorem splitAt_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ⟨(convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hp,
        openSegment_left_subset h⟩
    · rcases List.mem_singleton.1 hQ with rfl
      exact ⟨(convex_segment P.1 P.2).segment_subset hp (right_mem_segment ℝ _ _),
        openSegment_right_subset h⟩
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact ⟨subset_rfl, subset_rfl⟩

theorem splitAllAt_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_subset p P Q hQP⟩

/-- Every piece of a subdivision lies inside a piece it came from, both as a segment and as an
interior — and at the **same** source. -/
theorem subdivide_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR, hQR'⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP, hRP'⟩ := splitAllAt_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP, hQR'.trans hRP'⟩

/-- Cutting one piece introduces only the cut point as a new end. -/
theorem splitAt_ends (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, ∀ z, (z = Q.1 ∨ z = Q.2) → z = p ∨ (z = P.1 ∨ z = P.2) := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ z hz
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rcases List.mem_singleton.1 hQ with rfl
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · intro Q hQ z hz
    rcases List.mem_singleton.1 hQ with rfl
    exact Or.inr hz

theorem splitAllAt_ends (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z = p ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  intro Q hQ z hz
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  rcases splitAt_ends p P Q hQP z hz with h | h
  · exact Or.inl h
  · exact Or.inr ⟨P, hP, h⟩

/-- **The endpoint criterion.** An end of a piece of the subdivision is either a cut point or
was an end of a source piece all along. -/
theorem subdivide_ends (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z ∈ points ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ z hz => Or.inr ⟨Q, hQ, hz⟩
  | cons p ps ih =>
    intro Q hQ z hz
    rcases ih (pieces := splitAllAt p pieces) Q hQ z hz with h | ⟨R, hR, hzR⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases splitAllAt_ends p pieces R hR z hzR with rfl | ⟨P, hP, hzP⟩
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr ⟨P, hP, hzP⟩

/-! ### What the cut points have to cover

Two conditions, and between them they are the blueprint's "subdivide at all old endpoints,
isolated intersections, and endpoints of overlapping intervals". The second asks for **some**
pair of ends of each meet rather than every pair, because that is what a construction can
supply: a meet is `segment ℝ u v` and `segment ℝ v u` alike, and that a nondegenerate
segment's ends are determined by its point set is a theorem this development does not have and
does not need. -/

/-- Where two pieces meet. -/
def meetOf (P Q : Piece) : Set Plane := P.seg ∩ Q.seg

theorem meetOf_comm (P Q : Piece) : meetOf P Q = meetOf Q P := inter_comm _ _

/-- Every end of every source piece is a cut point. -/
def EndsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points

/-- For every pair of distinct source pieces that meet, some pair of ends of the meet is
cut. -/
def MeetsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ Q ∈ pieces, P ≠ Q → (meetOf P Q).Nonempty →
    ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points

/-- With the source ends cut too, the endpoint criterion says outright that every end of every
piece of the subdivision is a cut point. -/
theorem subdivide_ends_are_cuts {pieces : List Piece} {points : List Plane}
    (h : EndsAreCut pieces points) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) → z ∈ points := by
  intro Q hQ z hz
  rcases subdivide_ends pieces points Q hQ z hz with h' | ⟨P, hP, hzP⟩
  · exact h'
  · exact h P hP z hzP

/-! ### Producing the cut points

Nothing computes them. The overlay is stated existentially, so the list is built by the
induction that proves it exists, and `segment_inter_segment` hands over the ends of a meet the
moment the meet is known to be nonempty. That is what keeps the choice operator out: the
witnesses of `segment_inter_segment` are not unique, so there is nothing to name. -/

/-- One piece against a list: a point list holding both ends of every meet. -/
theorem exists_meet_points (P : Piece) (others : List Piece) :
    ∃ points : List Plane, ∀ Q ∈ others, (meetOf P Q).Nonempty →
      ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points := by
  induction others with
  | nil => exact ⟨[], by simp⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, htail⟩ := ih
    by_cases hR : (meetOf P R).Nonempty
    · obtain ⟨u, v, huv⟩ := segment_inter_segment P.1 P.2 R.1 R.2 hR
      refine ⟨u :: v :: tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨u, v, huv, by simp, by simp⟩
      · obtain ⟨s, t, hst, hs, ht⟩ := htail Q hQ hne
        exact ⟨s, t, hst, by simp [hs], by simp [ht]⟩
    · refine ⟨tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact absurd hne hR
      · exact htail Q hQ hne

/-- The whole list: the ends of each piece, and both ends of each meet. No sort and no choice
operator — the point list is existential throughout. -/
theorem exists_cut_points (pieces : List Piece) :
    ∃ points : List Plane, EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  induction pieces with
  | nil => exact ⟨[], by simp [EndsAreCut], by simp [MeetsAreCut]⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, hEnds, hMeets⟩ := ih
    obtain ⟨meetPoints, hHead⟩ := exists_meet_points R rs
    refine ⟨R.1 :: R.2 :: (meetPoints ++ tailPoints), fun P hP z hz => ?_,
      fun P hP Q hQ hPQ hne => ?_⟩
    · -- The head's two ends open the list; the tail's ends are already in `tailPoints`.
      rcases List.mem_cons.1 hP with rfl | hPt
      · rcases hz with rfl | rfl <;> simp
      · have := hEnds P hPt z hz
        simp [this]
    · -- A pair involving the head is covered by `meetPoints`, in whichever order it is asked
      -- for; a pair inside the tail was covered already.
      rcases List.mem_cons.1 hP with hPh | hPt
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · exact absurd (hPh.trans hQh.symm) hPQ
        · subst hPh
          obtain ⟨u, v, huv, hu, hv⟩ := hHead Q hQt hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · subst hQh
          have hne' : (meetOf Q P).Nonempty := by rwa [meetOf_comm]
          obtain ⟨u, v, huv, hu, hv⟩ := hHead P hPt hne'
          exact ⟨u, v, by rw [meetOf_comm]; exact huv, by simp [hu], by simp [hv]⟩
        · obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hPt Q hQt hPQ hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩

/-! ### Separation

Cut at every end of every source piece and at both ends of every meet, and two pieces of the
subdivision that share an interior point are the **same** segment — equal, not disjoint.
Overlapping collinear pieces cannot be pulled apart by cutting; after enough cuts they
coincide, which is what the blueprint's deduplication clause is for. -/

/-- Collinearity: two pieces of the subdivision that share an interior point lie inside one
nondegenerate segment. If they came from the same source piece, that piece; if from different
ones, the sources' overlap — nondegenerate because the shared point is interior to it, the
overlap's ends being cut points and so interior to nothing. -/
theorem subdivide_common_segment {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    ∃ A : Piece, A.Nondeg ∧ P.seg ⊆ A.seg ∧ Q.seg ⊆ A.seg := by
  obtain ⟨p, hp, hPseg, hPint⟩ := subdivide_subset pieces points P hP
  obtain ⟨q, hq, hQseg, hQint⟩ := subdivide_subset pieces points Q hQ
  by_cases hpq : p = q
  · subst hpq
    exact ⟨p, hnd p hp, hPseg, hQseg⟩
  -- The sources meet at `x`, so their meet is a segment with both ends cut.
  have hxp : x ∈ p.seg := openSegment_subset_segment ℝ _ _ (hPint hxP)
  have hxq : x ∈ q.seg := openSegment_subset_segment ℝ _ _ (hQint hxQ)
  obtain ⟨u, v, huv, hu, hv⟩ := hMeets p hp q hq hpq ⟨x, hxp, hxq⟩
  have hux : u ∉ P.interior := subdivide_avoids points hnd u hu P hP
  have hvx : v ∉ P.interior := subdivide_avoids points hnd v hv P hP
  have huy : u ∉ Q.interior := subdivide_avoids points hnd u hu Q hQ
  have hvy : v ∉ Q.interior := subdivide_avoids points hnd v hv Q hQ
  -- `x` is interior to the meet: it lies on it, and it is neither of its ends.
  have hxuv : x ∈ segment ℝ u v := huv ▸ ⟨hxp, hxq⟩
  have hxu : u ≠ x := fun h => hux (h ▸ hxP)
  have hxv : v ≠ x := fun h => hvx (h ▸ hxP)
  have hxopen : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right hxu hxv hxuv
  have huvne : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hxopen
    exact hxu hxopen.symm
  -- Both ends of the meet lie on both sources, so each one-dimensional citation has its
  -- ambient segment.
  have hsubp : segment ℝ u v ⊆ p.seg := huv ▸ inter_subset_left
  have hsubq : segment ℝ u v ⊆ q.seg := huv ▸ inter_subset_right
  refine ⟨(u, v), huvne, ?_, ?_⟩
  · exact segment_inside_of_ends_outside (hnd p hp)
      (hPseg (left_mem_segment ℝ _ _)) (hPseg (right_mem_segment ℝ _ _))
      (hsubp (left_mem_segment ℝ _ _)) (hsubp (right_mem_segment ℝ _ _))
      hxP hxopen hux hvx
  · exact segment_inside_of_ends_outside (hnd q hq)
      (hQseg (left_mem_segment ℝ _ _)) (hQseg (right_mem_segment ℝ _ _))
      (hsubq (left_mem_segment ℝ _ _)) (hsubq (right_mem_segment ℝ _ _))
      hxQ hxopen huy hvy

/-- **Separation.** Two pieces of the subdivision that share an interior point are the same
segment, in one order or the other. -/
theorem subdivide_separated {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    P = Q ∨ P = (Q.2, Q.1) := by
  -- Every end of every piece is a cut point, hence interior to nothing.
  have cut : ∀ R ∈ subdivide pieces points, ∀ z, (z = R.1 ∨ z = R.2) → z ∈ points :=
    subdivide_ends_are_cuts hEnds
  have h₁ : Q.1 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inl rfl)) P hP
  have h₂ : Q.2 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inr rfl)) P hP
  have h₃ : P.1 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inl rfl)) Q hQ
  have h₄ : P.2 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inr rfl)) Q hQ
  obtain ⟨A, hA, hPA, hQA⟩ := subdivide_common_segment hnd hMeets hP hQ hxP hxQ
  rcases same_ends_of_meeting_interiors hA
      (hPA (left_mem_segment ℝ _ _)) (hPA (right_mem_segment ℝ _ _))
      (hQA (left_mem_segment ℝ _ _)) (hQA (right_mem_segment ℝ _ _))
      hxP hxQ h₁ h₂ h₃ h₄ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (Prod.ext e₁ e₂)
  · exact Or.inr (Prod.ext e₁ e₂)

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/OverlayGraph.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

open Metric _root_.Set
open scoped _root_.Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-- The lexicographic order on plane points: first coordinate, then second. -/
def Precedes (p q : Plane) : Prop := p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)

theorem precedes_total (p q : Plane) : Precedes p q ∨ Precedes q p := by
  rcases lt_trichotomy (p 0) (q 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (p 1) (q 1) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem eq_of_precedes_of_precedes {p q : Plane} (h : Precedes p q) (h' : Precedes q p) :
    p = q := by
  -- Both coordinates are pinned: the first by trichotomy, the second by antisymmetry of `≤`.
  have key : p 0 = q 0 ∧ p 1 = q 1 := by
    rcases h with h | ⟨ha, hb⟩ <;> rcases h' with h' | ⟨ha', hb'⟩
    · exact absurd h (asymm h')
    · exact absurd h (by rw [ha']; exact lt_irrefl _)
    · exact absurd h' (by rw [ha]; exact lt_irrefl _)
    · exact ⟨ha, le_antisymm hb hb'⟩
  ext i
  fin_cases i
  · exact key.1
  · exact key.2

/-! ### The canonical orientation of a piece -/

open scoped Classical in
/-- A piece with its ends in lexicographic order. Two names for one segment orient to the
same name; that is the whole purpose. -/
noncomputable def orientPiece (P : Piece) : Piece :=
  if Precedes P.1 P.2 then P else (P.2, P.1)

theorem orientPiece_of_precedes {P : Piece} (h : Precedes P.1 P.2) : orientPiece P = P := by
  classical
  exact if_pos h

theorem orientPiece_of_not_precedes {P : Piece} (h : ¬ Precedes P.1 P.2) :
    orientPiece P = (P.2, P.1) := by
  classical
  exact if_neg h

/-- Orienting does not move the segment. -/
@[simp] theorem orientPiece_seg (P : Piece) : (orientPiece P).seg = P.seg := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact segment_symm ℝ _ _

/-- Nor the interior. -/
@[simp] theorem orientPiece_interior (P : Piece) : (orientPiece P).interior = P.interior := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact openSegment_symm ℝ _ _

/-- Nor which points are its ends. -/
theorem orientPiece_ends (P : Piece) (z : Plane) :
    (z = (orientPiece P).1 ∨ z = (orientPiece P).2) ↔ (z = P.1 ∨ z = P.2) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

theorem orientPiece_nondeg {P : Piece} (h : P.Nondeg) : (orientPiece P).Nondeg := by
  by_cases hp : Precedes P.1 P.2
  · rw [orientPiece_of_precedes hp]; exact h
  · rw [orientPiece_of_not_precedes hp]; exact fun e => h e.symm

/-- **Orienting forgets the name it was given.** This is the fact that makes deduplication
carry no geometry. -/
@[simp] theorem orientPiece_swap (P : Piece) : orientPiece (P.2, P.1) = orientPiece P := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
    by_cases h' : Precedes P.2 P.1
    · -- Each end precedes the other, so they are the same point and the pair is its own
      -- reversal.
      have he : P.1 = P.2 := eq_of_precedes_of_precedes h h'
      rw [orientPiece_of_precedes (P := (P.2, P.1)) h']
      exact Prod.ext he.symm he
    · rw [orientPiece_of_not_precedes (P := (P.2, P.1)) h']
  · rw [orientPiece_of_not_precedes h,
      orientPiece_of_precedes (P := (P.2, P.1)) ((precedes_total P.1 P.2).resolve_left h)]

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

theorem cover_eq_of_mem_iff {l₁ l₂ : List Piece} (h : ∀ P, P ∈ l₁ ↔ P ∈ l₂) :
    cover l₁ = cover l₂ := by
  ext x
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, (h P).1 hP, hx⟩, fun ⟨P, hP, hx⟩ => ⟨P, (h P).2 hP, hx⟩⟩

theorem cover_map_orientPiece (l : List Piece) : cover (l.map orientPiece) = cover l := by
  ext x
  simp only [cover, mem_iUnion, exists_prop, List.mem_map]
  constructor
  · rintro ⟨P, ⟨Q, hQ, rfl⟩, hx⟩
    exact ⟨Q, hQ, by rwa [orientPiece_seg] at hx⟩
  · rintro ⟨Q, hQ, hx⟩
    exact ⟨orientPiece Q, ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩

open scoped Classical in
/-- The edges of the overlay: the pieces of the subdivision, oriented and then deduplicated.
Orienting is what makes the deduplication a plain list operation. -/
noncomputable def overlayPieces (pieces : List Piece) (points : List Plane) : List Piece :=
  ((subdivide pieces points).map orientPiece).dedup

theorem mem_overlayPieces {pieces : List Piece} {points : List Plane} {P : Piece} :
    P ∈ overlayPieces pieces points ↔ ∃ Q ∈ subdivide pieces points, orientPiece Q = P := by
  rw [overlayPieces, List.mem_dedup, List.mem_map]

/-- Neither orienting nor deduplicating changes what the pieces occupy. -/
theorem overlayPieces_cover (pieces : List Piece) (points : List Plane) :
    cover (overlayPieces pieces points) = cover pieces := by
  rw [overlayPieces,
    cover_eq_of_mem_iff (l₂ := (subdivide pieces points).map orientPiece) fun _ => List.mem_dedup,
    cover_map_orientPiece, subdivide_cover]

theorem overlayPieces_nondeg {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) : ∀ P ∈ overlayPieces pieces points, P.Nondeg := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact orientPiece_nondeg (subdivide_ne points hnd Q hQ)

/-- Every end of every edge is a cut point: orienting does not change which points are ends,
and `subdivide_ends_are_cuts` covers the subdivision. -/
theorem overlayPieces_ends_cut {pieces : List Piece} {points : List Plane}
    (hEnds : EndsAreCut pieces points) :
    ∀ P ∈ overlayPieces pieces points, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points := by
  intro P hP z hz
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact subdivide_ends_are_cuts hEnds Q hQ z ((orientPiece_ends Q z).1 hz)

/-- And a cut point is interior to no edge. -/
theorem overlayPieces_avoids {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ P ∈ overlayPieces pieces points, p ∉ P.interior := by
  intro p hp P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  rw [orientPiece_interior]
  exact subdivide_avoids points hnd p hp Q hQ

/-- **Distinct edges have disjoint interiors.** This is where separation is spent: two pieces
sharing an interior point are the same segment, so after orienting they are the same *name*,
and a deduplicated list holds a name once. -/
theorem overlayPieces_disjoint_interiors {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) {P Q : Piece}
    (hP : P ∈ overlayPieces pieces points) (hQ : Q ∈ overlayPieces pieces points)
    (hPQ : P ≠ Q) {x : Plane} (hxP : x ∈ P.interior) : x ∉ Q.interior := by
  intro hxQ
  obtain ⟨P', hP', rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨Q', hQ', rfl⟩ := mem_overlayPieces.1 hQ
  rw [orientPiece_interior] at hxP hxQ
  rcases subdivide_separated hnd hEnds hMeets hP' hQ' hxP hxQ with h | h
  · exact hPQ (by rw [h])
  · exact hPQ (by rw [h, orientPiece_swap])

/-! ### The graph -/

/-- The ends of a list of pieces. -/
def endSet (edges : List Piece) : Set Plane := {v | ∃ P ∈ edges, v = P.1 ∨ v = P.2}

/-- The overlay graph: the oriented deduplicated pieces as edges, their ends as vertices.

An edge links `x` and `y` exactly when they are its two ends in one order or the other, which
is what makes `eq_or_eq_of_isLink_of_isLink` a case split with no content. -/
noncomputable def overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph Plane Piece where
  vertexSet := endSet (overlayPieces pieces points)
  IsLink P x y := P ∈ overlayPieces pieces points ∧
    ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ overlayPieces pieces points}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [mem_setOf_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

@[simp] theorem overlayGraph_vertexSet :
    V(overlayGraph pieces points) = endSet (overlayPieces pieces points) := rfl

@[simp] theorem overlayGraph_mem_edgeSet :
    P ∈ E(overlayGraph pieces points) ↔ P ∈ overlayPieces pieces points := Iff.rfl

@[simp] theorem overlayGraph_isLink :
    (overlayGraph pieces points).IsLink P x y ↔
      P ∈ overlayPieces pieces points ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

/-- An end of an edge is a vertex. -/
theorem overlayGraph_inc (hP : P ∈ overlayPieces pieces points) (h : v = P.1 ∨ v = P.2) :
    (overlayGraph pieces points).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-- Every piece is drawn by the affine parametrization of its segment. -/
noncomputable def segmentDrawing (P : Piece) : ℝ → Plane := AffineMap.lineMap P.1 P.2

@[simp] theorem edgeArc_segmentDrawing (P : Piece) :
    Graph.edgeArc segmentDrawing P = P.seg :=
  (segment_eq_image_lineMap ℝ P.1 P.2).symm

/-- **The overlay graph is a plane graph.** -/
theorem overlayGraph_isDrawing (pieces : List Piece) (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) :
    Graph.IsDrawing (overlayGraph pieces points) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · -- An edge is a nondegenerate segment, and `segmentDrawing` IS its parametrization.
    intro P hP
    have hne : P.Nondeg := overlayPieces_nondeg points hnd P (by simpa using hP)
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact ⟨by simpa using hP, Or.inl ⟨rfl, rfl⟩⟩
  · -- A vertex is an end of some edge, hence a cut point, hence interior to nothing; and a
    -- point of a segment that is not interior to it is one of its ends.
    rintro P a b w ⟨hP, h⟩ hw hwarc
    rw [edgeArc_segmentDrawing] at hwarc
    obtain ⟨R, hR, hwR⟩ := hw
    have hwint : w ∉ P.interior :=
      overlayPieces_avoids hnd w (overlayPieces_ends_cut hEnds R hR w hwR) P hP
    have hend : w = P.1 ∨ w = P.2 := by
      by_contra hcon
      push Not at hcon
      exact hwint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hwarc)
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · -- A common point is an end of both edges: if it were an end of neither it would be
    -- interior to both, and if it were an end of just one it would be a cut point, hence not
    -- interior to the other.
    rintro P Q hP hQ hPQ p hpP hpQ
    rw [overlayGraph_mem_edgeSet] at hP hQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    have key : ∀ A B : Piece, A ∈ overlayPieces pieces points →
        B ∈ overlayPieces pieces points → A ≠ B → p ∈ A.seg → p ∈ B.seg →
        (p = A.1 ∨ p = A.2) := by
      intro A B hA hB hAB hpA hpB
      by_contra hcon
      push Not at hcon
      have hintA : p ∈ A.interior :=
        mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpA
      by_cases hendB : p = B.1 ∨ p = B.2
      · exact overlayPieces_avoids hnd p (overlayPieces_ends_cut hEnds B hB p hendB) A hA hintA
      · push Not at hendB
        have hintB : p ∈ B.interior :=
          mem_openSegment_of_ne_left_right (Ne.symm hendB.1) (Ne.symm hendB.2) hpB
        exact overlayPieces_disjoint_interiors hnd hEnds hMeets hA hB hAB hintA hintB
    have hendP := key P Q hP hQ hPQ hpP hpQ
    have hendQ := key Q P hQ hP (Ne.symm hPQ) hpQ hpP
    exact ⟨⟨P, hP, hendP⟩, overlayGraph_inc hP hendP, overlayGraph_inc hQ hendQ⟩

/-- What the graph occupies is what its edges occupy: every vertex is an end of an edge, so
the vertices add nothing. -/
theorem overlayGraph_pointSet (pieces : List Piece) (points : List Plane) :
    Graph.pointSet (overlayGraph pieces points) segmentDrawing = cover pieces := by
  rw [← overlayPieces_cover pieces points]
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, overlayGraph_vertexSet,
    endSet, mem_setOf_eq, overlayGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

theorem finite_endSet (edges : List Piece) : (endSet edges).Finite := by
  -- The end set is the image of a finite list under the two projections.
  have : endSet edges ⊆ (fun P : Piece => P.1) '' {P | P ∈ edges}
      ∪ (fun P : Piece => P.2) '' {P | P ∈ edges} := by
    rintro v ⟨P, hP, rfl | rfl⟩
    · exact Or.inl ⟨P, hP, rfl⟩
    · exact Or.inr ⟨P, hP, rfl⟩
  exact Set.Finite.subset
    ((edges.finite_toSet.image _).union (edges.finite_toSet.image _)) this

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/SimpleArc.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

open Metric _root_.Set
open scoped _root_.Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-- Prepending a vertex to a nonempty list adds the segment to its head. -/
theorem poly_cons_of_ne_nil {vs : List Plane} (h : vs ≠ []) (u : Plane) :
    poly (u :: vs) = segment ℝ u (vs.head h) ∪ poly vs := by
  match vs, h with
  | _ :: _, _ => rfl

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

open scoped Classical in
/-- The nondegenerate segments of a polygonal chain, in order. A repeated vertex contributes
nothing. -/
noncomputable def segsOf : List Plane → List Piece
  | [] => []
  | [_] => []
  | u :: v :: rest => if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest)

@[simp] theorem segsOf_nil : segsOf [] = [] := rfl

@[simp] theorem segsOf_singleton (v : Plane) : segsOf [v] = [] := rfl

open scoped Classical in
theorem segsOf_cons_cons (u v : Plane) (rest : List Plane) :
    segsOf (u :: v :: rest) =
      if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest) := rfl

/-- Every segment produced is nondegenerate — which is the whole point of the definition. -/
theorem segsOf_nondeg (vs : List Plane) : ∀ P ∈ segsOf vs, P.Nondeg := by
  classical
  induction vs with
  | nil => simp
  | cons u tl ih =>
    match tl, ih with
    | [], _ => simp
    | v :: rest, ih =>
      rw [segsOf_cons_cons]
      split_ifs with huv
      · exact ih
      · intro P hP
        rcases List.mem_cons.1 hP with rfl | hP
        · exact huv
        · exact ih P hP

/-- The segments of a chain occupy the chain — unless the chain has collapsed to a point (or
to nothing), in which case there are no segments at all. -/
theorem cover_segsOf (vs : List Plane) :
    cover (segsOf vs) = poly vs ∨ (segsOf vs = [] ∧ (poly vs).Subsingleton) := by
  classical
  induction vs with
  | nil => exact Or.inr ⟨rfl, by simp⟩
  | cons u tl ih =>
    match tl, ih with
    | [], _ => exact Or.inr ⟨rfl, by simp [Set.Subsingleton]⟩
    | v :: rest, ih =>
      rw [segsOf_cons_cons, poly_cons_cons]
      by_cases huv : u = v
      · -- A repeated vertex contributes the point `u`, which the rest of the chain already
        -- holds.
        subst huv
        rw [if_pos rfl, segment_same]
        have hmem : u ∈ poly (u :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
        rcases ih with h | ⟨h1, h2⟩
        · exact Or.inl (by rw [h, union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)])
        · refine Or.inr ⟨h1, ?_⟩
          rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)]
          exact h2
      · rw [if_neg huv, cover_cons]
        refine Or.inl ?_
        rcases ih with h | ⟨h1, h2⟩
        · rw [h]; rfl
        · -- The rest of the chain is the single point `v`, already an end of the new segment.
          rw [h1, cover_nil, union_empty,
            h2.eq_singleton_of_mem (mem_poly_of_mem (List.mem_cons_self ..)),
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))]
          rfl

/-- When a chain carries two distinct points it has not collapsed, so its segments occupy
exactly it. -/
theorem cover_segsOf_eq {vs : List Plane} (ha : a ∈ poly vs) (hb : b ∈ poly vs)
    (hab : a ≠ b) : cover (segsOf vs) = poly vs := by
  rcases cover_segsOf vs with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ha hb) hab

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-- **The realisation of a nonempty walk of the overlay graph is the carrier of a vertex
list**, running from the walk's source to its target.

The list is returned rather than an unnamed polygonal set: the consumers of Lemma 1.1 that
overlay the arc with something else need its vertices. -/
theorem exists_poly_eq_edgesCover {u v : Plane} {W : List Piece}
    (hW : (overlayGraph pieces points).IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = u ∧ vs.getLast h = v ∧
      poly vs = Graph.edgesCover segmentDrawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    -- The edge's arc is the segment from the source to the waypoint, in whichever order the
    -- edge names its ends.
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing]
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    rcases eq_or_ne W [] with rfl | hWne
    · have hwv : w = v := hW.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_⟩
      rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := ih hWne
      refine ⟨u :: vs, by simp, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · rw [poly_cons_of_ne_nil hvs, hhead, hpoly, Graph.edgesCover_cons, hedge]

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-- Both ends of an edge reach the same vertices. -/
theorem overlayGraph_reaches_end {P : Piece} (hP : P ∈ overlayPieces pieces points)
    (hz : x = P.1 ∨ x = P.2) :
    (overlayGraph pieces points).Reaches a P.1 ↔ (overlayGraph pieces points).Reaches a x := by
  have hlink : (overlayGraph pieces points).IsLink P P.1 P.2 :=
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  rcases hz with rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h => h.trans (Graph.Reaches.of_isLink hlink),
      fun h => h.trans (Graph.Reaches.of_isLink hlink).symm⟩

/-- A cut point on the union is a vertex: it lies on some edge, and a cut point is interior to
no edge, so it is one of that edge's two ends. -/
theorem overlayGraph_mem_vertexSet_of_mem_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hxp : x ∈ points) (hx : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hx
  simp only [cover, mem_iUnion, exists_prop] at hx
  obtain ⟨P, hP, hxP⟩ := hx
  have hint : x ∉ P.interior := overlayPieces_avoids hnd x hxp P hP
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-- **The overlay graph of a connected union is connected**, in the form the construction
needs: any vertex reaches any other.

The proof is a clopen argument in the plane. Split the edges into those whose ends the walk
relation reaches from `a` and those it does not; each class carries a compact set, the two
carried sets cover the union, and they are disjoint — a common point would, by the drawing
condition, be a vertex incident with an edge of each class, and incidence is reachability.
Preconnectedness then leaves the second class carrying nothing. -/
theorem overlayGraph_reaches (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    (hap : a ∈ points) (hbp : b ∈ points) (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    (overlayGraph pieces points).Reaches a b := by
  classical
  have hdraw : Graph.IsDrawing (overlayGraph pieces points) segmentDrawing :=
    overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have haV : a ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hap ha
  have hbV : b ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hbp hb
  -- Every edge carries a link between its two ends; this is the only fact about the graph
  -- used below beyond the drawing condition.
  have hlink : ∀ P ∈ overlayPieces pieces points,
      (overlayGraph pieces points).IsLink P P.1 P.2 := fun P hP =>
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  -- The two classes of edges, and the point sets they carry.
  set S : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      (overlayGraph pieces points).Reaches a P.1}, P.seg with hS
  set T : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      ¬ (overlayGraph pieces points).Reaches a P.1}, P.seg with hT
  have hSclosed : IsClosed S :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  have hTclosed : IsClosed T :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  -- The two classes carry the whole union between them.
  have hunion : ∀ z ∈ cover pieces, z ∈ S ∨ z ∈ T := by
    intro z hz
    rw [← overlayPieces_cover pieces points] at hz
    simp only [cover, mem_iUnion, exists_prop] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    by_cases hr : (overlayGraph pieces points).Reaches a P.1
    · exact Or.inl (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
    · exact Or.inr (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
  -- And they carry disjoint sets: a common point is a vertex incident with an edge of each.
  have hdisj : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    simp only [hS, hT, mem_iUnion, mem_setOf_eq, exists_prop] at hzS hzT
    obtain ⟨P, ⟨hP, hPr⟩, hzP⟩ := hzS
    obtain ⟨Q, ⟨hQ, hQr⟩, hzQ⟩ := hzT
    have hPQ : P ≠ Q := by rintro rfl; exact hQr hPr
    obtain ⟨-, hincP, hincQ⟩ := hdraw.edge_inter (overlayGraph_mem_edgeSet.2 hP)
      (overlayGraph_mem_edgeSet.2 hQ) hPQ
      (by rwa [edgeArc_segmentDrawing]) (by rwa [edgeArc_segmentDrawing])
    have hzendP : z = P.1 ∨ z = P.2 := hincP.eq_or_eq_of_isLink (hlink P hP)
    have hzendQ : z = Q.1 ∨ z = Q.2 := hincQ.eq_or_eq_of_isLink (hlink Q hQ)
    exact hQr ((overlayGraph_reaches_end hQ hzendQ).2
      ((overlayGraph_reaches_end hP hzendP).1 hPr))
  -- `a` is carried by the reachable class, so that class is nonempty.
  have haS : a ∈ S := by
    obtain ⟨P, hP, hend⟩ := id haV
    refine mem_biUnion (show P ∈ _ from
      ⟨hP, (overlayGraph_reaches_end hP hend).2 (Graph.Reaches.refl haV)⟩) ?_
    rcases hend with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  -- Preconnectedness: the far class carries nothing that the union contains.
  have hbS : b ∈ S := by
    by_contra hbnot
    have hbT : b ∈ T := (hunion b hb).resolve_left hbnot
    have hsub : cover pieces ⊆ Tᶜ ∪ Sᶜ := by
      intro w hw
      rcases hunion w hw with h | h
      · exact Or.inl fun h' => hdisj w h h'
      · exact Or.inr fun h' => hdisj w h' h
    obtain ⟨z, hzc, hzT, hzS⟩ := hconn Tᶜ Sᶜ hTclosed.isOpen_compl hSclosed.isOpen_compl
      hsub ⟨a, ha, fun h => hdisj a haS h⟩ ⟨b, hb, fun h => hdisj b h hbT⟩
    exact (hunion z hzc).elim hzS hzT
  -- `b` is a vertex on an edge of the reachable class, hence an end of it.
  simp only [hS, mem_iUnion, mem_setOf_eq, exists_prop] at hbS
  obtain ⟨P, ⟨hP, hPr⟩, hbP⟩ := hbS
  have hbend : b = P.1 ∨ b = P.2 :=
    hdraw.vertex_mem_edgeArc (hlink P hP) hbV (by rwa [edgeArc_segmentDrawing])
  exact (overlayGraph_reaches_end hP hbend).1 hPr

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-- **Lemma 1.2 (finite polygonal unions).** If a finite union of nondegenerate segments is
connected, any two distinct points of it are joined inside it by a *simple* polygonal arc.

The arc is returned as a vertex list, not merely as a set: the consumers that overlay it with
another polygonal object need its vertices, and an existential over sets would not give them
back. -/
theorem exists_simple_poly_of_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces)) (hab : a ≠ b)
    (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      poly vs ⊆ cover pieces ∧ IsArcBetween (poly vs) a b := by
  classical
  -- Put the two endpoints on the cut list, so that they become vertices of the overlay. The
  -- two cut conditions ask only that certain points occur in the list, so this is free.
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points pieces
  set pts : List Plane := a :: b :: pts₀ with hpts
  have hEnds : EndsAreCut pieces pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut pieces pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨u, v, huv, by simp [hpts, hu], by simp [hpts, hv]⟩
  have hdraw : Graph.IsDrawing (overlayGraph pieces pts) segmentDrawing :=
    overlayGraph_isDrawing pieces pts hnd hEnds hMeets
  -- A walk from `a` to `b`, thinned to a path.
  have hreach : (overlayGraph pieces pts).Reaches a b :=
    overlayGraph_reaches hnd hconn hEnds hMeets (by simp [hpts]) (by simp [hpts]) ha hb
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hab hpath.isWalk.eq_of_nil
  -- Its realisation is an arc, and it is the carrier of a vertex list.
  have harc : IsArcBetween (Graph.edgesCover segmentDrawing W) a b :=
    hdraw.path_isArcBetween hpath hWne
  obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := exists_poly_eq_edgesCover hpath.isWalk hWne
  refine ⟨vs, hvs, hhead, hlast, ?_, ?_⟩
  · rw [hpoly, ← overlayGraph_pointSet pieces pts]
    exact Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he
  · rw [hpoly]; exact harc

/-- **Lemma 1.2**, for a set presented as a polygonal chain. -/
theorem exists_simple_poly_of_poly {vs : List Plane} (hconn : IsPreconnected (poly vs))
    (hab : a ≠ b) (ha : a ∈ poly vs) (hb : b ∈ poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ poly vs ∧ IsArcBetween (poly ws) a b := by
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  have := exists_simple_poly_of_cover (segsOf_nondeg vs) (hcov ▸ hconn) hab
    (hcov ▸ ha) (hcov ▸ hb)
  rwa [hcov] at this

/-- **Lemma 1.2**, for a set given only as polygonal. -/
theorem exists_simple_poly_of_isPolygonal {A : Set Plane} (hA : IsPolygonal A)
    (hconn : IsPreconnected A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ A ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨vs, rfl⟩ := hA
  exact exists_simple_poly_of_poly hconn hab ha hb

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Direction.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Directions, and the two arcs cut out by a pair of rays

This module supplies the *direction facts* that the two-sided strip lemma runs on. Everything
here is stated through the sign of the orientation form `Plane.det`: no angle is named, no
inverse trigonometric function appears, and no case distinction on the sense of a turn is
ever made.

A *direction* is a unit vector (`Plane.IsDirection`). What actually matters about a direction
is its ray — the set of its positive multiples — because every predicate below is invariant
under positive scaling (`Plane.smul_mem_arcCCW`). So the arcs are defined on all nonzero
vectors and the unit-vector normalisation `Plane.dir` is only a convenience.

## The two arcs

Two directions `u` and `w` that are neither equal nor opposite are exactly two directions with
`det u w ≠ 0` (`Plane.det_ne_zero_iff`). They cut the circle of directions into two open arcs.
The arc traversed counterclockwise from `u` to `w` is `Plane.arcCCW u w`, defined by Sedgewick's
`ccw` predicate on the triple `(u, d, w)`: at least two of the three consecutive orientation
forms are positive. This definition is manifestly invariant under rotating the triple, and — this
is the point — it is correct for *both* arcs at once, the short one and the long one, with no
sign hypothesis in the definition itself.

`Plane.mem_ray_or_mem_arcCCW` and `Plane.arcCCW_disjoint` say that the two arcs and the two
bounding rays partition the nonzero vectors.

## The transfer fact

`Plane.same_arc_of_det_neg_of_det_pos` is Appendix C's transfer fact: *a direction with negative
`det` against the first ray lies on the same arc as a direction with positive `det` against the
second*. Note that no nearness hypothesis is needed for it — see the module note below.

## Blueprint

* `Plane.IsDirection`, `Plane.dir`, `Plane.arcCCW`, `Plane.det_ne_zero_iff`,
  `Plane.mem_ray_or_mem_arcCCW`, `Plane.arcCCW_disjoint` — Appendix C, item 1, "two distinct,
  non-opposite unit vectors bound two open arcs of directions".
* `Plane.same_arc_of_det_neg_of_det_pos` — Appendix C, item 1, the transfer fact.
* `Plane.exists_isDirection_det_ne_zero`, `Plane.exists_isDirection_det_and_inner_ne_zero` —
  Appendix C, item 1, "the existence of a unit vector avoiding any prescribed finite set of
  directions".
* `Plane.germs_split`, `Plane.exists_germ_threshold` — the vertex matching inside Lemma 1.8
  (Two-sided polygonal strips): the two left half-strip germs land on one arc and the two right
  ones on the other.

## A note on "near"

Appendix C states the transfer fact for directions *near* the two bounding rays. The nearness is
not needed: `Plane.mem_arcCCW_rev_iff` shows that the arc counterclockwise from `w` to `u` is cut
out by a *disjunction* of two sign conditions, so a single sign suffices to land on it. The
mirror statement — a direction with positive `det` against `u` and one with negative `det`
against `w` both lie on `arcCCW u w` — is *not* available from one sign each, because that arc is
cut out by the *conjunction* (`Plane.mem_arcCCW_iff`). Lemma 1.8 needs the mirror statement too,
for the two right germs, and there the missing second sign is exactly what "`s/t` small" buys:
`Plane.exists_germ_threshold` supplies it, with an explicit threshold.
-/

open _root_.Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

/-! ### Directions -/

/-- A *direction* is a unit vector. Only the ray a direction spans ever matters below, but
normalising to unit length gives a canonical representative of that ray. -/
def IsDirection (u : Plane) : Prop := ‖u‖ = 1

theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

/-- The unit vector along a nonzero vector. -/
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- `dir u` is a positive multiple of `u`, which is why every sign-of-`det` predicate is blind
to the difference. -/
theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

/-! ### Nonvanishing of `det` -/

theorem ne_zero_left_of_det_ne_zero (h : det u w ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

theorem ne_zero_right_of_det_ne_zero (h : det u w ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

/-! ### The two arcs -/

/-- The open arc of directions traversed counterclockwise from `u` to `w`.

A nonzero `d` lies on it when at least two of the three consecutive orientation forms of the
triple `(u, d, w)` are positive. The definition is a cyclic condition, so it is correct for the
short arc and for the long arc alike, with no hypothesis on the sign of `det u w`. -/
def arcCCW (u w : Plane) : Set Plane :=
  {d | (0 < det u d ∧ 0 < det d w) ∨ (0 < det d w ∧ 0 < det w u) ∨ (0 < det w u ∧ 0 < det u d)}

/-- Fix the orientation by `0 < det u w`, so that `w` is counterclockwise of `u` by less than a
half turn. Then the arc counterclockwise from `u` to `w` is the *short* one, and membership is
the conjunction of two sign conditions. -/
theorem mem_arcCCW_iff (h : 0 < det u w) : d ∈ arcCCW u w ↔ 0 < det u d ∧ 0 < det d w := by
  have hwu : det w u < 0 := by rw [det_comm w u]; linarith
  refine ⟨?_, Or.inl⟩
  rintro (h1 | ⟨_, h2⟩ | ⟨h2, _⟩)
  · exact h1
  · linarith
  · linarith

/-- With the same orientation `0 < det u w`, the arc counterclockwise from `w` back to `u` is the
*long* one — more than a half turn — and membership is a **disjunction**. This asymmetry is the
whole content of the transfer fact: one sign suffices here, two are needed on the short arc. -/
theorem mem_arcCCW_rev_iff (h : 0 < det u w) :
    d ∈ arcCCW w u ↔ det u d < 0 ∨ det d w < 0 := by
  have e1 : det w d = -det d w := det_comm w d
  have e2 : det d u = -det u d := det_comm d u
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h2, _⟩ | ⟨_, h1⟩)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inr (by rw [e1] at h1; linarith)
  · rintro (h1 | h2)
    · exact Or.inr (Or.inl ⟨by rw [e2]; linarith, h⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e1]; linarith⟩)

/-- Every sign-of-`det` condition is blind to positive rescaling, so the arcs really are sets of
*rays*, not of vectors. -/
theorem smul_mem_arcCCW (hr : 0 < r) : r • d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  have key : ∀ x : ℝ, 0 < r * x ↔ 0 < x := by
    intro x
    constructor <;> intro hx <;> nlinarith
  simp only [arcCCW, mem_setOf_eq, det_smul_left, det_smul_right, key]

/-- The two rays and the two arcs exhaust the nonzero vectors. Together with
`Plane.arcCCW_disjoint` this is the statement that two distinct, non-opposite directions bound
two arcs. -/
theorem mem_ray_or_mem_arcCCW (h : 0 < det u w) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • u) ∨ (∃ c : ℝ, 0 < c ∧ d = c • w) ∨
      d ∈ arcCCW u w ∨ d ∈ arcCCW w u := by
  have hu : u ≠ 0 := ne_zero_left_of_det_ne_zero h.ne'
  have hw : w ≠ 0 := ne_zero_right_of_det_ne_zero h.ne'
  by_cases hneg : det u d < 0 ∨ det d w < 0
  · exact Or.inr (Or.inr (Or.inr ((mem_arcCCW_rev_iff h).2 hneg)))
  push Not at hneg
  obtain ⟨h1, h2⟩ := hneg
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inr (Or.inl ((mem_arcCCW_iff h).2 ⟨h1', h2'⟩)))
    · -- `det d w = 0`: `d` lies along the line of `w`, and `det u d ≥ 0` fixes the sign.
      obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul w d hw).1 (by rw [det_comm w d, ← h2']; ring)
      refine Or.inr (Or.inl ⟨c, ?_, rfl⟩)
      rw [det_smul_right] at h1'
      nlinarith
  · -- `det u d = 0`: `d` lies along the line of `u`, and `det d w ≥ 0` fixes the sign.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u d hu).1 h1'.symm
    refine Or.inl ⟨c, ?_, rfl⟩
    rw [det_smul_left] at h2
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · nlinarith
    · exfalso
      have : c = 0 := by
        rcases mul_eq_zero.1 h2'.symm with hc | hd'
        · exact hc
        · exact absurd hd' h.ne'
      exact hd (by rw [this, zero_smul])

/-! ### The transfer fact -/

/-- A direction with **negative** `det` against `u` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_neg (h : 0 < det u w) (hd : det u d < 0) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inl hd)

/-- A direction with **positive** `det` against `w` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_pos (h : 0 < det u w) (hd : 0 < det w d) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inr (by rw [det_comm d w]; linarith))

/-! ### Half-strip germs

Fix a vertex with incoming unit tangent `u` and outgoing unit tangent `w`, and let `r₁ = -u`,
`r₂ = w` be the two rays leaving the vertex, so that `perp r₁ = -u^⊥` and `perp r₂ = w^⊥`.
Then the four half-strip germs of Lemma 1.8 are, in the blueprint's own notation,

* incoming left, `-t u + s u^⊥ = t • r₁ - s • perp r₁`;
* outgoing left, `t w + s w^⊥ = t • r₂ + s • perp r₂`;
* incoming right, `-t u - s u^⊥ = t • r₁ + s • perp r₁`;
* outgoing right, `t w - s w^⊥ = t • r₂ - s • perp r₂`,

each with `t, s > 0`. The four computations below place them on the two arcs. -/

/-- The orientation form of a germ against its own tangent sees only the transverse
coefficient: this is the blueprint's `det(r₁, d) = -s` and `det(r₂, d) = s`. -/
theorem det_germ_self (r : Plane) (t s : ℝ) :
    det r (t • r + s • perp r) = s * ‖r‖ ^ 2 := by
  rw [det_add_right, det_smul_right, det_smul_right, det_self, det_perp_self]
  ring

theorem det_germ_self' (r : Plane) (t s : ℝ) :
    det (t • r + s • perp r) r = -(s * ‖r‖ ^ 2) := by
  rw [det_comm, det_germ_self]

/-- The orientation form of a germ at `r₁` against the *other* ray. The inner-product term is
what makes the transverse coefficient have to be small relative to the longitudinal one. -/
theorem det_germ (r₁ r₂ : Plane) (t s : ℝ) :
    det (t • r₁ + s • perp r₁) r₂ = t * det r₁ r₂ - s * inner ℝ r₁ r₂ := by
  rw [det_add_left, det_smul_left, det_smul_left, det_perp_left]
  ring

/-- The orientation form of a germ at `r₂` against the other ray. -/
theorem det_germ' (r₁ r₂ : Plane) (t s : ℝ) :
    det r₁ (t • r₂ + s • perp r₂) = t * det r₁ r₂ + s * inner ℝ r₁ r₂ := by
  rw [det_add_right, det_smul_right, det_smul_right, det_perp_right]

private theorem sq_norm_pos_left (h : 0 < det r₁ r₂) : 0 < ‖r₁‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_left_of_det_ne_zero h.ne')) 2

private theorem sq_norm_pos_right (h : 0 < det r₁ r₂) : 0 < ‖r₂‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_right_of_det_ne_zero h.ne')) 2

/-- The **incoming left** germ lands on the arc counterclockwise from `r₂` to `r₁`, for *every*
longitudinal coefficient `t`: this is the half of the vertex matching that costs nothing,
because that arc is cut out by a disjunction. -/
theorem germ_mem_arcCCW_rev_of_left (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_neg h ?_
  have e : t • r₁ - s • perp r₁ = t • r₁ + (-s) • perp r₁ := by module
  rw [e, det_germ_self]
  nlinarith [sq_norm_pos_left h]

/-- The **outgoing left** germ lands on the same arc, again for every `t`. -/
theorem germ_mem_arcCCW_rev_of_right (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_pos h ?_
  rw [det_germ_self]
  exact mul_pos hs (sq_norm_pos_right h)

/-- The **incoming right** germ lands on the arc counterclockwise from `r₁` to `r₂` provided the
transverse coefficient is small enough against the longitudinal one. The inequality
`s ⟪r₁, r₂⟫ < t det(r₁, r₂)` is exactly "`s/t` small", written without a division. -/
theorem germ_mem_arcCCW_of_left (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ := by
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [det_germ_self]
    exact mul_pos hs (sq_norm_pos_left h)
  · rw [det_germ]
    linarith

/-- The **outgoing right** germ lands on the same arc, under the same smallness condition. -/
theorem germ_mem_arcCCW_of_right (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂ := by
  have e : t • r₂ - s • perp r₂ = t • r₂ + (-s) • perp r₂ := by module
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [e, det_germ']
    linarith
  · rw [e, det_germ_self']
    nlinarith [sq_norm_pos_right h]

/-- **The vertex matching of Lemma 1.8.** With the strips narrow enough — `s ⟪r₁, r₂⟫` under
`t det(r₁, r₂)` — the two left germs lie on one arc and the two right germs on the other. No
angle is named and no case distinction on the sense of the turn arises: the two cases of the
turn are the two orders in which `r₁` and `r₂` may be presented, and `det_comm` exchanges
them. -/
theorem germs_split (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) :=
  ⟨⟨germ_mem_arcCCW_rev_of_left h hs t, germ_mem_arcCCW_rev_of_right h hs t⟩,
    ⟨germ_mem_arcCCW_of_left h hs hsmall, germ_mem_arcCCW_of_right h hs hsmall⟩⟩

/-! ### A direction avoiding finitely many others

The argument is a counting one, with no measure and no trigonometry: the one-parameter family
`a ↦ (1, a)` meets the line of any fixed nonzero vector at most once, so finitely many vectors
rule out only finitely many parameters, and `ℝ` has more than finitely many. -/

/-- The family used to dodge finitely many directions. -/
private theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

private theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

/-- **Appendix C.** There is a unit vector not parallel to any of a prescribed finite set of
nonzero vectors. This is what lets one rotate coordinates so that no edge of a finite polygonal
figure is horizontal. -/
theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  -- The parameters ruled out by `S` are the slopes of its members, hence at most as many as `S`.
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp; linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  -- `dir` only rescales, so it cannot create a vanishing orientation form.
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h

/-! ### The arcs are open

Not needed by Lemma 1.8, which uses only the partition, but it justifies the word "open" in
"two open arcs of directions". -/

theorem continuous_det_right (u : Plane) : Continuous fun d : Plane => det u d := by
  refine Continuous.sub (Continuous.mul continuous_const ?_) (Continuous.mul continuous_const ?_)
  · exact PiLp.continuous_apply _ _ 1
  · exact PiLp.continuous_apply _ _ 0

end Plane

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/UniformBound.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# One positive bound for finitely many

Every "choose `ε` small enough for all of them" step in the development is this lemma: a
finite family of positive bounds has a single positive bound below all of them. The
polygonal-redrawing argument alone uses it three times, and the two-sided strip lemma chooses
its vertex disks and edge blocks the same way.

It is stated for a *predicate that is monotone downward in the bound* rather than as a `min`
fold, because no consumer wants the value — only that some positive value works for every
member at once.

## Blueprint

* `exists_pos_le_of_finite` — the numerical form.
* `exists_pos_forall_of_finite` — the form consumers use: a downward-monotone predicate
  holding at some positive bound for each member holds at one common positive bound.
-/

open _root_.Set

namespace Schoenflies

variable {ι : Type*}

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

/-- The form the geometry uses: if a property that only gets easier as the bound shrinks holds
at *some* positive bound for each member of a finite family, then it holds at *one* positive
bound for all of them at once. -/
theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  -- Pick a witness for each member, then take a positive bound below all the witnesses.
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Strip.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Two-sided polygonal strips

This module builds the *collar* of Lemma 1.8: an open neighbourhood `N` of a simple closed
polygon `P` whose complement in `N` splits into two connected open sets, the two local sides.

The blueprint's construction is "a small closed disk about every vertex, a thin rectangular
block about every edge, chosen so that consecutive blocks overlap and nonadjacent closures are
disjoint". The blocks here are

* `Plane.cone v A R` — the open sector of radius `R` about a vertex `v` cut out by an arc `A`
  of directions, and
* `Plane.strip a u t₁ t₂ s₁ s₂` — the open rectangle around a directed edge, written in the
  edge's own coordinates `t = ⟪u, x - a⟫` (along) and `s = det u (x - a)` (across).

Everything about the *side matching at a vertex* comes from `Schoenflies/Direction.lean`
through the orientation form; no angle is named. The one new direction fact needed here is the
sign-free repackaging `Plane.germs_split'`: the blueprint's `germs_split` assumes
`0 < det r₁ r₂`, but a polygon turns both ways, and it turns out that *which* named arc carries
the left germs does not depend on the sense of the turn — it is always `arcCCW r₂ r₁`. Only the
side of the smallness hypothesis moves.

## The constants

The blueprint says "the blocks may be chosen so that consecutive edge and vertex blocks overlap
in the prescribed small rectangles around the radial segments, while the closures of all
nonadjacent blocks are disjoint" without naming the constants. `Schoenflies.StripData` names
them: a cone radius `R`, a trim `lam` by which each edge block stops short of its endpoints, and
a half-width `rho`. They should be chosen in this order (this is the recipe the unproved
`exists_stripData` has to follow):

1. `R` from the vertex separations, from the distance of each vertex to the nonincident edges
   (with a factor `2` of slack, spent in `dist_core_vertex`), and from the prescribed open set;
2. `lam := R / 5`, which makes `2 * lam < R` (the cones reach past the ends of the blocks they
   must overlap) and `4 * lam < ‖edge‖` (the blocks are nonempty);
3. `rho` from the distance of each trimmed edge to the other edges, and from the *germ
   threshold* `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex — this last is the
   quantitative form of "make the strips narrow enough that this side matching holds in every
   vertex disk", and it is the only inequality in the list that is not a separation of compact
   sets.

## Blueprint

* `Plane.germs_split'` — the sign-free vertex matching inside Lemma 1.8.
* `Schoenflies.ClosedPolygon` — a simple closed polygonal curve presented by its cyclic vertex
  list.
* `Schoenflies.StripData` — the choice of constants, as a hypothesis.
* `Schoenflies.StripData.sideL`, `.sideR`, `.nbhd`, `.sideL_disjoint_sideR` — the two labelled
  sides of the collar, and that they are disjoint.

## Where the rest of Lemma 1.8 lives

This module builds the apparatus and proves the hard half: the germ matching at a corner and
the disjointness of the two labelled sides. The other two obligations are discharged next door,
and were split out only because they were built concurrently:

* `Schoenflies/StripConstants.lean` — `exists_stripData` and `exists_stripData_subset`, which
  produce the constants, the latter with the collar inside a prescribed open set.
* `Schoenflies/StripConnected.lean` — that each side is connected, and
  `nbhd \ carrier = sideL ∪ sideR`.

`Schoenflies.polygonal_collar` in `Schoenflies/Compose.lean` is the three composed into the
blueprint's Lemma 1.8 (a). `ClosedPolygon.collar` below is a *definition*, not the theorem.

What is still missing from Lemma 1.8 as a whole: the **local two-sidedness** clause (every
sufficiently small disk about a point of the curve meets the complement in exactly two
components, one in each side), and part **(b)**, the arc case.
-/

open Metric _root_.Set

namespace Schoenflies

namespace Plane

variable {u w d r₁ r₂ a x : Plane} {r t s c ρ : ℝ}

/-! ### A sign-free vertex matching

`Plane.germs_split` fixes the orientation with `0 < det r₁ r₂`. A polygon turns both ways, so
the collar needs the statement without that hypothesis. The content of the repackaging is that
the *conclusion* does not move: the two left germs always land on `arcCCW r₂ r₁` and the two
right germs on `arcCCW r₁ r₂`. What moves is which pair needs the smallness hypothesis, so the
sign-free form simply imposes it on both, with absolute values. -/

/-- **The vertex matching, sign-free.** With `r₁` the ray back along the incoming edge and `r₂`
the ray out along the outgoing edge, the two *left* half-strip germs lie on `arcCCW r₂ r₁` and
the two *right* ones on `arcCCW r₁ r₂`, whichever way the polygon turns. The hypothesis
`s * |⟪r₁, r₂⟫| < t * |det r₁ r₂|` is the blueprint's "`s/t` small", written without a division
and without a sign. -/
theorem germs_split' (h : det r₁ r₂ ≠ 0) (hs : 0 < s)
    (hsmall : s * |inner ℝ r₁ r₂| < t * |det r₁ r₂|) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  have hle : inner ℝ r₁ r₂ ≤ |inner ℝ r₁ r₂| := le_abs_self _
  have hle' : inner ℝ r₂ r₁ ≤ |inner ℝ r₁ r₂| := by
    rw [real_inner_comm]; exact hle
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The turn is the other way: exchange the roles of the two rays in `germs_split`.
    have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    have habs : |det r₁ r₂| = det r₂ r₁ := by rw [abs_of_neg hneg, det_comm r₁ r₂]; ring
    have hsmall' : s * inner ℝ r₂ r₁ < t * det r₂ r₁ := by
      rw [habs] at hsmall
      nlinarith
    have H := germs_split h' hs hsmall'
    exact ⟨⟨H.2.2, H.2.1⟩, ⟨H.1.2, H.1.1⟩⟩
  · have habs : |det r₁ r₂| = det r₁ r₂ := abs_of_pos hpos
    have hsmall' : s * inner ℝ r₁ r₂ < t * det r₁ r₂ := by
      rw [habs] at hsmall
      nlinarith
    exact germs_split hpos hs hsmall'

/-! ### The two arcs, without a sign hypothesis -/

/-- The two rays and the two arcs exhaust the nonzero vectors, whichever the sign of
`det r₁ r₂`. -/
theorem mem_ray_or_mem_arcCCW' (h : det r₁ r₂ ≠ 0) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • r₁) ∨ (∃ c : ℝ, 0 < c ∧ d = c • r₂) ∨
      d ∈ arcCCW r₁ r₂ ∨ d ∈ arcCCW r₂ r₁ := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    rcases mem_ray_or_mem_arcCCW h' hd with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact mem_ray_or_mem_arcCCW hpos hd

/-- A nonnegative multiple of a bounding ray lies on neither arc: the arcs are *open*, and `0`
is on neither. This is what keeps the two incident edges out of the vertex sectors. -/
theorem notMem_arcCCW_smul (u w : Plane) (hc : 0 ≤ c) :
    c • u ∉ arcCCW u w ∧ c • u ∉ arcCCW w u := by
  have e1 : det u (c • u) = 0 := by rw [det_smul_right, det_self, mul_zero]
  have e2 : det (c • u) u = 0 := by rw [det_smul_left, det_self, mul_zero]
  have e3 : det (c • u) w = c * det u w := det_smul_left _ _ _
  have e4 : det w (c • u) = c * det w u := det_smul_right _ _ _
  have e5 : det w u = -det u w := det_comm w u
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩)
    · rw [e1] at h1; exact lt_irrefl 0 h1
    · rw [e3] at h1; rw [e5] at h2; nlinarith
    · rw [e1] at h2; exact lt_irrefl 0 h2
  · rintro (⟨_, h2⟩ | ⟨h2, _⟩ | ⟨h1, h2⟩)
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e4, e5] at h2; nlinarith

/-- Half-spaces through the origin are convex; `det u ·` is linear. -/
theorem isLinearMap_det_right (u : Plane) : IsLinearMap ℝ fun d : Plane => det u d :=
  ⟨fun x y => det_add_right u x y, fun c x => by rw [det_smul_right, smul_eq_mul]⟩

theorem isLinearMap_det_left (w : Plane) : IsLinearMap ℝ fun d : Plane => det d w :=
  ⟨fun x y => det_add_left x y w, fun c x => by rw [det_smul_left, smul_eq_mul]⟩

theorem convex_det_right_pos (u : Plane) : Convex ℝ {d : Plane | 0 < det u d} :=
  convex_halfSpace_gt (isLinearMap_det_right u) 0

theorem convex_det_right_neg (u : Plane) : Convex ℝ {d : Plane | det u d < 0} :=
  convex_halfSpace_lt (isLinearMap_det_right u) 0

theorem convex_det_left_pos (w : Plane) : Convex ℝ {d : Plane | 0 < det d w} :=
  convex_halfSpace_gt (isLinearMap_det_left w) 0

theorem convex_det_left_neg (w : Plane) : Convex ℝ {d : Plane | det d w < 0} :=
  convex_halfSpace_lt (isLinearMap_det_left w) 0

/-- An arc met with a ball about the origin is connected. When the arc is the short one it is an
intersection of two half-planes, hence convex; when it is the long one it is a *union* of two
half-planes, and `-(u + w)` lies in both. -/
theorem isConnected_arcCCW_ball (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (arcCCW u w ∩ ball (0 : Plane) ρ) := by
  -- A scaling factor small enough to put the witness inside the ball.
  have hne : u + w ≠ 0 := by
    intro hz
    have hw : w = -u := by linear_combination (norm := module) hz
    rw [hw, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self,
      mul_zero] at h
    exact h rfl
  have hnpos : 0 < ‖u + w‖ := norm_pos_iff.2 hne
  obtain ⟨ε, hε, hεball⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * ‖u + w‖ < ρ := by
    refine ⟨ρ / (2 * ‖u + w‖), by positivity, ?_⟩
    have : ρ / (2 * ‖u + w‖) * ‖u + w‖ = ρ / 2 := by field_simp
    rw [this]; linarith
  have hball : ∀ σ : ℝ, |σ| = ε → σ • (u + w) ∈ ball (0 : Plane) ρ := by
    intro σ hσ
    rw [mem_ball, _root_.dist_zero_right, norm_smul, Real.norm_eq_abs, hσ]
    exact hεball
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The long arc: `{det w d < 0} ∪ {det d u < 0}`, glued at `-(u + w)`.
    have h' : 0 < det w u := by rw [det_comm w u]; linarith
    have harc : arcCCW u w = {d : Plane | det w d < 0} ∪ {d : Plane | det d u < 0} := by
      ext d
      rw [mem_arcCCW_rev_iff h']
      simp only [mem_union, mem_setOf_eq]
    have hd0 : (-ε) • (u + w) ∈ ball (0 : Plane) ρ :=
      hball _ (by rw [abs_of_neg (neg_neg_iff_pos.2 hε), neg_neg])
    have hA : (-ε) • (u + w) ∈ {d : Plane | det w d < 0} := by
      change det w ((-ε) • (u + w)) < 0
      rw [det_smul_right, det_add_right, det_self, add_zero]
      nlinarith
    have hB : (-ε) • (u + w) ∈ {d : Plane | det d u < 0} := by
      change det ((-ε) • (u + w)) u < 0
      rw [det_smul_left, det_add_left, det_self, zero_add]
      nlinarith
    refine ⟨⟨_, by rw [harc]; exact ⟨Or.inl hA, hd0⟩⟩, ?_⟩
    rw [harc, union_inter_distrib_right]
    exact IsPreconnected.union _ ⟨hA, hd0⟩ ⟨hB, hd0⟩
      ((convex_det_right_neg w).inter (convex_ball _ _)).isPreconnected
      ((convex_det_left_neg u).inter (convex_ball _ _)).isPreconnected
  · -- The short arc: an intersection of two half-planes, hence convex.
    have harc : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      rw [mem_arcCCW_iff hpos]
      simp only [mem_inter_iff, mem_setOf_eq]
    have hmem : ε • (u + w) ∈ arcCCW u w ∩ ball (0 : Plane) ρ := by
      refine ⟨?_, hball _ (abs_of_pos hε)⟩
      rw [harc]
      constructor
      · change 0 < det u (ε • (u + w))
        rw [det_smul_right, det_add_right, det_self, zero_add]
        positivity
      · change 0 < det (ε • (u + w)) w
        rw [det_smul_left, det_add_left, det_self, add_zero]
        positivity
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [harc]
    exact (((convex_det_right_pos u).inter (convex_det_left_pos w)).inter
      (convex_ball _ _)).isPreconnected

/-! ### Vertex sectors

The "small closed disk about a vertex" of the blueprint is replaced by an open *sector*: the
part of a ball about the vertex lying in a prescribed arc of directions. The two sectors cut out
by the two arcs are exactly the two components of the ball minus the two incident radial
segments, which is what makes the labelling at a vertex well defined. -/

/-- The open sector of radius `ρ` about `v` spanned by the set `A` of directions. -/
def cone (v : Plane) (A : Set Plane) (ρ : ℝ) : Set Plane := {x | x - v ∈ A} ∩ ball v ρ

theorem cone_subset_ball {v : Plane} {A : Set Plane} : cone v A ρ ⊆ ball v ρ := inter_subset_right

/-- A sector is the translate of an arc met with a ball at the origin, so it inherits its
connectedness from `Plane.isConnected_arcCCW_ball`. -/
theorem cone_eq_image (v : Plane) (A : Set Plane) (ρ : ℝ) :
    cone v A ρ = (fun d => v + d) '' (A ∩ ball (0 : Plane) ρ) := by
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    refine ⟨y - v, ⟨hy, ?_⟩, ?_⟩
    · rw [mem_ball, _root_.dist_zero_right, ← dist_eq_norm]
      exact hb
    · change v + (y - v) = y
      module
  · rintro ⟨d, ⟨hd, hb⟩, rfl⟩
    have he : v + d - v = d := by module
    refine ⟨by rw [mem_setOf_eq, he]; exact hd, ?_⟩
    rw [mem_ball, dist_eq_norm, he]
    rw [mem_ball, _root_.dist_zero_right] at hb
    exact hb

theorem isConnected_cone_arcCCW (v : Plane) (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (cone v (arcCCW u w) ρ) := by
  rw [cone_eq_image]
  have hc : Continuous fun d : Plane => v + d := continuous_const.add continuous_id
  exact (isConnected_arcCCW_ball h hρ).image _ hc.continuousOn

/-! ### Edge blocks

The block around a directed edge is described in the edge's own frame: `coordAlong` is the
progress along the edge and `coordAcross` the signed distance to its line. Both are affine, so
the block is an intersection of four open half-planes — open and convex at a glance. -/

/-- Progress along the directed edge that starts at `a` with unit tangent `u`. -/
noncomputable def coordAlong (a u x : Plane) : ℝ := inner ℝ u (x - a)

/-- Signed distance from `x` to the line of the directed edge that starts at `a` with unit
tangent `u`; positive on the left. -/
def coordAcross (a u x : Plane) : ℝ := det u (x - a)

/-- The orientation form is the inner product against the turned vector. -/
theorem det_eq_inner_perp (u v : Plane) : det u v = inner ℝ (perp u) v := by
  rw [inner_eq, det]
  simp [perp]
  ring

theorem abs_det_le (u v : Plane) : |det u v| ≤ ‖u‖ * ‖v‖ := by
  rw [det_eq_inner_perp]
  calc |inner ℝ (perp u) v| ≤ ‖perp u‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_perp]

@[simp] theorem coordAlong_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAlong a u (a + t • u + s • perp u) = t := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAlong, h, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_perp_self, hu.norm]
  ring

@[simp] theorem coordAcross_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAcross a u (a + t • u + s • perp u) = s := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAcross, h, det_germ_self, hu.norm]
  ring

/-- The frame is complete: every point is recovered from its two coordinates. -/
theorem frame_decomp (hu : IsDirection u) (a x : Plane) :
    x = a + (coordAlong a u x) • u + (coordAcross a u x) • perp u := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have := hu.norm
    rw [EuclideanSpace.norm_eq] at this
    have h2 : Real.sqrt (∑ i, ‖u i‖ ^ 2) ^ 2 = 1 ^ 2 := by rw [this]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h2
    simpa [Fin.sum_univ_two, sq_abs] using h2
  have hal : coordAlong a u x = u 0 * (x 0 - a 0) + u 1 * (x 1 - a 1) := by
    rw [coordAlong, inner_eq]; simp
  have hac : coordAcross a u x = u 0 * (x 1 - a 1) - u 1 * (x 0 - a 0) := by
    rw [coordAcross, det]; simp
  ext i
  fin_cases i
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 0 - x 0) * hnorm
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 1 - x 1) * hnorm

/-- Both coordinates are `1`-Lipschitz, which is how a small ball about a point of the edge
stays inside the block. -/
theorem abs_coordAlong_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAlong a u x - coordAlong a u y| ≤ dist x y := by
  have h : coordAlong a u x - coordAlong a u y = inner ℝ u (x - y) := by
    rw [coordAlong, coordAlong, ← inner_sub_right]
    congr 1
    module
  rw [h, dist_eq_norm]
  calc |inner ℝ u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

theorem abs_coordAcross_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAcross a u x - coordAcross a u y| ≤ dist x y := by
  have h : coordAcross a u x - coordAcross a u y = det u (x - y) := by
    simp only [coordAcross, det]
    simp
    ring
  rw [h, dist_eq_norm]
  calc |det u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_det_le _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

/-- The open block around the directed edge from `a` with unit tangent `u`: the points whose
progress lies in `(t₁, t₂)` and whose signed distance lies in `(s₁, s₂)`. -/
def strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Set Plane :=
  {x | t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
    s₁ < coordAcross a u x ∧ coordAcross a u x < s₂}

theorem mem_strip_iff {t₁ t₂ s₁ s₂ : ℝ} :
    x ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
      s₁ < coordAcross a u x ∧ coordAcross a u x < s₂ := Iff.rfl

theorem continuous_coordAlong (a u : Plane) : Continuous (coordAlong a u) :=
  (continuous_const.inner (continuous_id.sub continuous_const))

theorem continuous_coordAcross (a u : Plane) : Continuous (coordAcross a u) :=
  (continuous_det_right u).comp (continuous_id.sub continuous_const)

theorem isOpen_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : IsOpen (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ < coordAlong a u x} ∩ {x : Plane | coordAlong a u x < t₂}) ∩
        ({x : Plane | s₁ < coordAcross a u x} ∩ {x : Plane | coordAcross a u x < s₂}) := by
    ext y
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [key]
  exact ((isOpen_lt continuous_const (continuous_coordAlong a u)).inter
      (isOpen_lt (continuous_coordAlong a u) continuous_const)).inter
    ((isOpen_lt continuous_const (continuous_coordAcross a u)).inter
      (isOpen_lt (continuous_coordAcross a u) continuous_const))

theorem convex_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Convex ℝ (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ + inner ℝ u a < inner ℝ u x} ∩ {x : Plane | inner ℝ u x < t₂ + inner ℝ u a})
        ∩ ({x : Plane | s₁ + det u a < det u x} ∩ {x : Plane | det u x < s₂ + det u a}) := by
    ext y
    have h1 : coordAlong a u y = inner ℝ u y - inner ℝ u a := by
      rw [coordAlong, inner_sub_right]
    have h2 : coordAcross a u y = det u y - det u a := by
      simp only [coordAcross, det]
      simp
      ring
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq, h1, h2]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [key]
  have hlin : IsLinearMap ℝ fun x : Plane => inner ℝ u x :=
    ⟨fun x y => inner_add_right _ _ _, fun c x => by rw [real_inner_smul_right, smul_eq_mul]⟩
  exact ((convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)).inter
    ((convex_halfSpace_gt (isLinearMap_det_right u) _).inter
      (convex_halfSpace_lt (isLinearMap_det_right u) _))

/-- A point of a block is at distance `|coordAcross|` from the foot of its perpendicular on the
edge line, which is the point of the edge with the same progress. -/
theorem dist_foot (hu : IsDirection u) (a x : Plane) :
    dist x (a + (coordAlong a u x) • u) = |coordAcross a u x| := by
  have h := frame_decomp hu a x
  rw [dist_eq_norm]
  have hx : x - (a + (coordAlong a u x) • u) = (coordAcross a u x) • perp u := by
    nth_rewrite 1 [h]
    module
  rw [hx, norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one]

end Plane

/-! ## Simple closed polygons

A polygon is presented by its cyclic vertex list. Indexing by `ZMod (m + 3)` builds in both the
cyclic successor and the requirement that there are at least three vertices, and it makes
`NeZero` available without a side hypothesis. -/

open Plane

variable {m : ℕ}

/-- A simple closed polygonal curve, presented by its cyclic vertex list. -/
structure ClosedPolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
  /-- No redundant vertex: the two edges at a vertex are not collinear. The blueprint deletes
  such vertices before starting, and the vertex matching needs `det ≠ 0` there. -/
  corner : ∀ i : ZMod (m + 3), det (vertex (i - 1) - vertex i) (vertex (i + 1) - vertex i) ≠ 0

namespace ClosedPolygon

variable (P : ClosedPolygon m) (i j : ZMod (m + 3)) (c t s : ℝ)

theorem one_ne_zero' : (1 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd one_pos h
  omega

theorem succ_ne_self : i + 1 ≠ i := fun h => one_ne_zero' (m := m) (by linear_combination h)

theorem vertex_ne : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  succ_ne_self i (P.vertex_inj h).symm

/-! ### Edges, in their own frame -/

/-- The length of the edge leaving vertex `i`. -/
noncomputable def len : ℝ := ‖P.vertex (i + 1) - P.vertex i‖

/-- The unit tangent of the edge leaving vertex `i`, which is also the outgoing ray at `i`. -/
noncomputable def tang : Plane := dir (P.vertex (i + 1) - P.vertex i)

/-- The incoming ray at vertex `i`: the direction back along the edge that arrives there. -/
noncomputable def rayIn : Plane := dir (P.vertex (i - 1) - P.vertex i)

/-- The point of the plane at progress `t` and signed offset `s` in the frame of edge `i`. -/
noncomputable def off : Plane := P.vertex i + t • P.tang i + s • perp (P.tang i)

/-- The point of edge `i` at distance `c` from its initial vertex. -/
noncomputable def pt : Plane := P.off i c 0

/-- The edge leaving vertex `i`. -/
def edge : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier of the polygon: the union of its edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P i j c t s}

theorem sub_ne_zero_of_edge : P.vertex (i + 1) - P.vertex i ≠ 0 :=
  sub_ne_zero.2 (P.vertex_ne i).symm

theorem len_pos : 0 < P.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (P.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (P.len i) • P.tang i = P.vertex (i + 1) - P.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem off_zero_zero : P.off i 0 0 = P.vertex i := by rw [off]; module

theorem pt_zero : P.pt i 0 = P.vertex i := off_zero_zero

theorem pt_len : P.pt i (P.len i) = P.vertex (i + 1) := by
  rw [pt, off, zero_smul, add_zero, len_smul_tang]
  module

theorem off_sub_vertex : P.off i t s - P.vertex i = t • P.tang i + s • perp (P.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : P.pt i c - P.vertex i = c • P.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (P.pt i c) (P.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem dist_off_vertex_le : dist (P.off i t s) (P.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • P.tang i + s • perp (P.tang i)‖ ≤ ‖t • P.tang i‖ + ‖s • perp (P.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

@[simp] theorem coordAlong_off : coordAlong (P.vertex i) (P.tang i) (P.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (P.vertex i) (P.tang i) (P.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

/-- Every point is the point of some frame position, so the two coordinates identify it. -/
theorem off_coord (P : ClosedPolygon m) (i : ZMod (m + 3)) (x : Plane) :
    x = P.off i (coordAlong (P.vertex i) (P.tang i) x) (coordAcross (P.vertex i) (P.tang i) x) :=
  frame_decomp isDirection_tang _ _

theorem mem_edge_iff {x : Plane} :
    x ∈ P.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (P.len i), x = P.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * P.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (P := P) (i := i)]
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / P.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (P := P) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (P.len i)) : P.pt i c ∈ P.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : P.vertex i ∈ P.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_mem_carrier : P.vertex i ∈ P.carrier := Set.mem_iUnion.2 ⟨i, vertex_mem_edge⟩

theorem edge_subset_carrier : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

/-- The incoming ray at `i + 1` is the reverse of the tangent of edge `i`. This is the identity
that lets the two germs at a shared vertex be compared. -/
theorem rayIn_succ : P.rayIn (i + 1) = -P.tang i := by
  rw [rayIn, tang, add_sub_cancel_right, dir, dir, norm_sub_rev]
  module

theorem vertex_pred_ne : P.vertex (i - 1) - P.vertex i ≠ 0 := by
  have h := P.vertex_ne (i - 1)
  rw [sub_add_cancel] at h
  exact sub_ne_zero.2 h

theorem det_rays_ne_zero : det (P.rayIn i) (P.tang i) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (vertex_pred_ne (P := P) (i := i))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (P := P) (i := i))
  rw [rayIn, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (P.corner i))

/-- A point of the edge arriving at `i` is a nonnegative multiple of the incoming ray away from
the vertex; a point of the edge leaving `i` is a nonnegative multiple of the outgoing one. This
is what keeps the two incident edges out of both sectors at `i`. -/
theorem mem_edge_pred_sub {x : Plane} (hx : x ∈ P.edge (i - 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.rayIn i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hx
  refine ⟨P.len (i - 1) - c, by linarith, ?_⟩
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at this
  have hv : P.vertex i = P.vertex (i - 1 + 1) := by rw [hsucc]
  have hlen : P.vertex (i - 1 + 1) = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang]; module
  rw [pt, off, zero_smul, add_zero, hr, hv, hlen]
  module

theorem mem_edge_sub {x : Plane} (hx : x ∈ P.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.tang i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := hx
  exact ⟨c, hc0, pt_sub_vertex⟩

theorem pt_eq : P.pt i c = P.vertex i + c • P.tang i := by rw [pt, off, zero_smul, add_zero]

end ClosedPolygon

/-! ## The constants

`StripData` is the blueprint's "choose the blocks so that consecutive ones overlap and
nonadjacent closures are disjoint", with every constant named. The three numbers are a cone
radius `R`, a trim `lam` and a half-width `rho`; the separation hypotheses are exactly the
instances of Lemma 1.4 (b) that the construction consumes, and `germ` is the vertex-matching
threshold. Producing them is the unproved `exists_stripData`; see the Status section. -/

/-- The constants of the collar of a simple closed polygon. -/
structure StripData (P : ClosedPolygon m) where
  /-- The radius of the vertex sectors. -/
  R : ℝ
  /-- The distance by which an edge block stops short of each endpoint of its edge. -/
  lam : ℝ
  /-- The half-width of an edge block. -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
  /-- The sectors reach past the ends of the blocks they have to overlap. -/
  two_lam_lt_R : 2 * lam < R
  /-- The blocks are nonempty, with room to spare at both ends. -/
  four_lam_lt_len : ∀ i, 4 * lam < P.len i
  /-- A sector does not run past the far end of an incident edge. -/
  R_le_len : ∀ i, R ≤ P.len i
  /-- Distinct vertices are `2R` apart, so distinct sectors are disjoint. -/
  sep_vertex : ∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)
  /-- A vertex is `2R` away from every nonincident edge. The factor `2` is the slack that a
  block of half-width `rho ≤ R` needs in `notMem_sectorL_of_far`. -/
  sep_vertex_edge : ∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y
  /-- The trimmed edge `i` is `2 * rho` away from every other edge. -/
  sep_trim_edge : ∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
    2 * rho ≤ dist (P.pt i c) y
  /-- **The vertex-matching threshold.** This is the only hypothesis that is not a separation of
  compact sets: it says the blocks are narrow enough, relative to how far they stop short of the
  vertices, for `Plane.germs_split'` to apply at every corner. -/
  germ : ∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)|

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

theorem lam_pos : 0 < D.lam := lt_trans D.rho_pos D.rho_lt_lam

theorem R_pos : 0 < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]

theorem rho_lt_R : D.rho < D.R := by
  have := D.lam_pos; have := D.rho_lt_lam; linarith [D.two_lam_lt_R]

/-! ### The four families of blocks -/

/-- The left block of edge `i`. -/
def blockL (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) 0 D.rho

/-- The right block of edge `i`. -/
def blockR (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) 0

/-- The left sector at vertex `i`: the arc `arcCCW (tang i) (rayIn i)` is the one carrying both
left germs, by `Plane.germs_split'`. -/
def sectorL (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.tang i) (P.rayIn i)) D.R

/-- The right sector at vertex `i`. -/
def sectorR (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.rayIn i) (P.tang i)) D.R

/-- The left side of the collar. -/
def sideL : Set Plane := ⋃ i, (D.sectorL i ∪ D.blockL i)

/-- The right side of the collar. -/
def sideR : Set Plane := ⋃ i, (D.sectorR i ∪ D.blockR i)

/-- The collar itself. -/
def nbhd : Set Plane := D.sideL ∪ D.sideR ∪ P.carrier

theorem mem_blockL_iff : x ∈ D.blockL i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      0 < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < D.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ D.blockR i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      -D.rho < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < 0 := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : P.off i t s ∈ D.blockL i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ 0 < s ∧ s < D.rho := by
  rw [mem_blockL_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : P.off i t s ∈ D.blockR i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem convex_blockL : Convex ℝ (D.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (D.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL : IsConnected (D.sectorL i) :=
  isConnected_cone_arcCCW _ (by rw [det_comm]; exact neg_ne_zero.2 ClosedPolygon.det_rays_ne_zero)
    D.R_pos

theorem isConnected_sectorR : IsConnected (D.sectorR i) :=
  isConnected_cone_arcCCW _ ClosedPolygon.det_rays_ne_zero D.R_pos

/-! ### Where the blocks live

A block sits inside the `rho`-neighbourhood of the trimmed edge, and a sector inside the ball of
radius `R` about its vertex. Every "nonadjacent blocks are disjoint" step below is one of these
two containments against one of the separation hypotheses. -/

/-- The foot of the perpendicular from a point of a block lies on the trimmed edge, within `rho`
of the point. -/
theorem exists_foot (h : x ∈ D.blockL i ∪ D.blockR i) :
    ∃ c ∈ Set.Icc D.lam (P.len i - D.lam), dist x (P.pt i c) < D.rho := by
  refine ⟨coordAlong (P.vertex i) (P.tang i) x, ?_, ?_⟩
  · rcases h with h | h
    · exact ⟨(D.mem_blockL_iff.1 h).1.le, (D.mem_blockL_iff.1 h).2.1.le⟩
    · exact ⟨(D.mem_blockR_iff.1 h).1.le, (D.mem_blockR_iff.1 h).2.1.le⟩
  · rw [ClosedPolygon.pt_eq, dist_foot ClosedPolygon.isDirection_tang]
    rcases h with h | h
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockL_iff.1 h
      rw [abs_of_pos h1]; exact h2
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockR_iff.1 h
      rw [abs_of_neg h2]; linarith

theorem sector_subset_ball : D.sectorL i ⊆ ball (P.vertex i) D.R := cone_subset_ball
theorem sectorR_subset_ball : D.sectorR i ⊆ ball (P.vertex i) D.R := cone_subset_ball

/-! ### The germ argument at a vertex

These four lemmas are the whole content of "at a vertex the left sides of the incoming and
outgoing strips enter the same component of the vertex disk minus the two incident rays". Each
is one projection of `Plane.germs_split'`, applied to the frame decomposition of a point of a
block. -/

/-- The threshold hypothesis, specialised to a point of a block. -/
theorem germ_ineq {t s : ℝ} (ht : D.lam < t) (hs0 : 0 < s) (hs : s < D.rho) :
    s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)| := by
  have hd : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have habs : (0 : ℝ) ≤ |inner ℝ (P.rayIn i) (P.tang i)| := abs_nonneg _
  have h1 : s * |inner ℝ (P.rayIn i) (P.tang i)| ≤ s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by
    nlinarith
  have h2 : s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) <
      D.rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by nlinarith
  have h3 := D.germ i
  nlinarith

/-- A point of the left block of edge `i`, seen from the vertex it leaves, is the outgoing left
germ, hence in the left arc there. -/
theorem blockL_sub_mem_arcL_start (h : x ∈ D.blockL i) :
    x - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  have hx := ClosedPolygon.off_coord P i x
  rw [hx, ClosedPolygon.off_sub_vertex]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3 (D.germ_ineq h1 h3 h4)).1.2

/-- The same point, seen from the vertex it arrives at, is the incoming left germ. -/
theorem blockL_sub_mem_arcL_finish (h : x ∈ D.blockL i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3
    (D.germ_ineq (i := i + 1) (by linarith) h3 h4)).1.1

/-- A point of the right block of edge `i`, seen from the vertex it leaves, is the outgoing right
germ, hence in the right arc there. -/
theorem blockR_sub_mem_arcR_start (h : x ∈ D.blockR i) :
    x - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hkey : x - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [hx, ClosedPolygon.off_sub_vertex]; module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq h1 (by linarith) (by linarith))).2.2

/-- The same point, seen from the vertex it arrives at, is the incoming right germ. -/
theorem blockR_sub_mem_arcR_finish (h : x ∈ D.blockR i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq (i := i + 1) (by linarith) (by linarith) (by linarith))).2.1

/-! ### Nonadjacent blocks are disjoint

Everything here is one of the separation hypotheses of `StripData` against one of the two
containments `exists_foot` and `sector_subset_ball`. -/

theorem pt_mem_edge_of_trim {c : ℝ} (hc : c ∈ Set.Icc D.lam (P.len i - D.lam)) :
    P.pt i c ∈ P.edge i :=
  ClosedPolygon.pt_mem_edge ⟨le_trans D.lam_pos.le hc.1, le_trans hc.2 (by linarith [D.lam_pos])⟩

/-- A block misses every edge but its own. -/
theorem block_notMem_edge (h : x ∈ D.blockL i ∪ D.blockR i) (hj : j ≠ i) : x ∉ P.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have := D.sep_trim_edge i j hj c hc x hx
  rw [dist_comm] at hd
  linarith [D.rho_pos]

/-- A block misses its own edge, because its points have nonzero offset. -/
theorem block_notMem_own_edge (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.edge i := by
  intro hx
  rw [ClosedPolygon.mem_edge_iff] at hx
  obtain ⟨c, _, rfl⟩ := hx
  have hzero : coordAcross (P.vertex i) (P.tang i) (P.pt i c) = 0 := by
    rw [ClosedPolygon.pt]; exact ClosedPolygon.coordAcross_off
  rcases h with h | h
  · have hpos := (D.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := (D.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg

theorem block_notMem_carrier (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hij : j = i
  · exact D.block_notMem_own_edge h (hij ▸ hj)
  · exact D.block_notMem_edge h hij hj

/-- A sector misses every edge that is not incident to its vertex. -/
theorem sector_notMem_far_edge (h : x ∈ ball (P.vertex i) D.R) (hj1 : j ≠ i - 1) (hj2 : j ≠ i) :
    x ∉ P.edge j := by
  intro hx
  have := D.sep_vertex_edge i j hj1 hj2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [D.R_pos]

/-- A sector misses the two edges incident to its vertex: their points lie on the two bounding
rays, and the arcs are open. -/
theorem sectorL_notMem_carrier (h : x ∈ D.sectorL i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).1) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).2) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sectorR_notMem_carrier (h : x ∈ D.sectorR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).2) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).1) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sideL_disjoint_carrier : Disjoint D.sideL P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorL_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inl hi) hc

theorem sideR_disjoint_carrier : Disjoint D.sideR P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorR_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inr hi) hc

/-! ### The two sides are disjoint

Four families times four families. The pairs with distinct indices are settled by distance; the
pairs at a shared index are settled by `Plane.arcCCW_disjoint'` through the germ lemmas. -/

end StripData

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Parity.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The crossing count of a polygon, and its parity

This is the arithmetic half of the polygonal Jordan curve theorem. A closed polygon is a
list of edges; a point off it gets a number, the count of edges the ray leaving the point
meets; and the whole separation statement follows from the fact that this number changes by
one exactly when the ray's foot sweeps across an edge.

## The frame

The blueprint rotates the coordinate system so that no edge is horizontal. Rotating a curve
is a change of the curve, which would have to be transported back at the end, so instead the
*ray direction* is carried as a parameter. A direction `u` (a unit vector,
`Plane.IsDirection`) fixes an orthonormal frame through

* `fwd u z` — how far along `u` the point `z` lies,
* `hgt u z` — how far across `u` it lies, positive on the counterclockwise side.

"Horizontal" becomes "level for `u`", i.e. `hgt u a = hgt u b`, and
`exists_direction_hgt_ne` — a one-line consequence of `Plane.exists_isDirection_det_ne_zero`
— supplies a `u` for which no edge of a finite list is level. Nothing below needs the
direction to be produced that way: `hgt u P.1 ≠ hgt u P.2` for every piece is carried as a
hypothesis, so no curve is ever moved and nothing has to be transported back.

## The count

An edge is a `Piece`, i.e. its pair of ends, and a polygon is a `List Piece` — the same
representation the overlay uses, so a subdivision produced by `Schoenflies.subdivide` can be
fed straight in. `Crosses u P q` says that the level line through `q` meets `P` strictly
beyond `q`, with the blueprint's half-open convention at the lower end, which is what makes
the count well defined with no genericity assumption. `crossings` counts and `parity`
reduces mod `2`.

Closedness of the polygon enters through `IsClosedChain`: the boundary of the edge list
vanishes mod `2`, stated by duality as "every `ZMod 2`-valued function of the ends sums to
zero over the list". `edgesOf` builds a closed chain from a cyclic vertex list, and
`IsClosedChain` survives `subdivide`.

## Blueprint

* `crossings`, `parity` — the count `π_C` of the section "The polygonal Jordan and crosscut
  theorems".
* `exists_direction_hgt_ne` — the setup of that section: a ray direction level for no edge.
* `crossings_subdivide`, `parity_subdivide` — Lemma 2.1 (subdivision invariance). Proved for
  the *count*, not only its parity, and for the whole `subdivide` operation of
  `Schoenflies.Subdivide`, not only for a single cut.
* `parity_eq_of_mem_ball`, `parity_eq_of_isPreconnected`,
  `parity_eq_of_mem_connectedComponentIn` — the first half of Lemma 2.2 (crossing parity):
  `π_C` is locally constant off the polygon, hence constant on each component of the
  complement.
* `parity_flip` — the second half of Lemma 4.4: the two local sides of an edge have opposite
  parity.
* `parity_eq_zero_of_lt` — `π_C = 0` beyond the polygon in the ray direction; the value on
  the unbounded region.
* `IsClosedChain`, `edgesOf`, `isClosedChain_subdivide` — the closedness hypothesis, its
  supply from a cyclic vertex list, and its survival of subdivision.
-/

open Metric _root_.Set

namespace Schoenflies

variable {u a b c p q z w : Plane} {s t : ℝ} {L : List Piece}

/-! ### The frame attached to a direction -/

/-- How far across the direction `u` the point `z` lies. Edges on which this is constant are
the blueprint's horizontal edges. -/
def hgt (u z : Plane) : ℝ := Plane.det u z

/-- How far along the direction `u` the point `z` lies. The ray from `q` is the set of points
of the same `hgt` and larger `fwd`. -/
noncomputable def fwd (u z : Plane) : ℝ := inner ℝ z u

theorem hgt_eq (u z : Plane) : hgt u z = u 0 * z 1 - u 1 * z 0 := rfl

theorem fwd_eq (u z : Plane) : fwd u z = z 0 * u 0 + z 1 * u 1 := Plane.inner_eq z u

namespace Plane

theorem add_apply (x y : Plane) (i : Fin 2) : (x + y) i = x i + y i := rfl

theorem smul_apply (r : ℝ) (x : Plane) (i : Fin 2) : (r • x) i = r * x i := rfl

end Plane

/-- The coordinate rewriting used throughout: every claim about `hgt` and `fwd` of an affine
combination is a polynomial identity in the four coordinates. -/
theorem hgt_lin (u a b : Plane) (t : ℝ) :
    hgt u (a + t • (b - a)) = hgt u a + t * (hgt u b - hgt u a) := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem fwd_lin (u a b : Plane) (t : ℝ) :
    fwd u (a + t • (b - a)) = fwd u a + t * (fwd u b - fwd u a) := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem hgt_sub (u x y : Plane) : hgt u (x - y) = hgt u x - hgt u y := by
  simp only [hgt_eq, Plane.sub_apply]; ring

theorem fwd_sub (u x y : Plane) : fwd u (x - y) = fwd u x - fwd u y := by
  simp only [fwd_eq, Plane.sub_apply]; ring

theorem hgt_add_smul (u v x : Plane) (t : ℝ) :
    hgt u (x + t • v) = hgt u x + t * hgt u v := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply]; ring

theorem fwd_add_smul (u v x : Plane) (t : ℝ) :
    fwd u (x + t • v) = fwd u x + t * fwd u v := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply]; ring

section Direction

variable (hu : Plane.IsDirection u)
include hu

theorem norm_sq_one : u 0 ^ 2 + u 1 ^ 2 = 1 := by
  rw [← Plane.norm_sq_eq, hu, one_pow]

omit hu in
@[simp] theorem hgt_self : hgt u u = 0 := by simp only [hgt_eq]; ring

theorem fwd_self : fwd u u = 1 := by rw [fwd_eq, ← norm_sq_one hu]; ring

theorem hgt_perp : hgt u (Plane.perp u) = 1 := by
  rw [hgt_eq, ← norm_sq_one hu]; simp only [Plane.perp_zero, Plane.perp_one]; ring

omit hu in
theorem fwd_perp : fwd u (Plane.perp u) = 0 := by
  simp only [fwd_eq, Plane.perp_zero, Plane.perp_one]; ring

/-- The frame is a basis: every vector is its two coordinates. -/
theorem decomp (v : Plane) : v = fwd u v • u + hgt u v • Plane.perp u := by
  have h1 := norm_sq_one hu
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Plane.add_apply, Plane.smul_apply, Plane.perp_zero,
      Plane.perp_one, hgt_eq, fwd_eq]
  · linear_combination (-(v 0)) * h1
  · linear_combination (-(v 1)) * h1

/-- Two points with the same frame coordinates are equal. -/
theorem eq_of_coords (h1 : fwd u z = fwd u w) (h2 : hgt u z = hgt u w) : z = w := by
  have hz := decomp hu z
  have hw := decomp hu w
  rw [h1, h2] at hz
  exact hz.trans hw.symm

theorem abs_fwd_le_norm (v : Plane) : |fwd u v| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v u
  rw [hu, mul_one] at h
  exact h

end Direction

/-! ### Where an edge meets a level line -/

/-- The point of the line through `a` and `b` at height `t`. Only used when the line is not
level, i.e. `hgt u a ≠ hgt u b`. -/
noncomputable def meet (u a b : Plane) (t : ℝ) : Plane :=
  a + ((t - hgt u a) / (hgt u b - hgt u a)) • (b - a)

theorem hgt_meet (h : hgt u a ≠ hgt u b) (t : ℝ) : hgt u (meet u a b t) = t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [meet, hgt_lin]
  field_simp
  ring

/-- Below the top and above the bottom, the meeting point is on the edge. -/
theorem meet_mem_segment (h : hgt u a < hgt u b) (h1 : hgt u a ≤ t) (h2 : t ≤ hgt u b) :
    meet u a b t ∈ segment ℝ a b := by
  have hne : (0:ℝ) < hgt u b - hgt u a := by linarith
  rw [segment_eq_image' ℝ a b]
  exact ⟨_, ⟨div_nonneg (by linarith) hne.le, (div_le_one hne).2 (by linarith)⟩, rfl⟩

/-- The meeting point is the only point of the edge at its height. -/
theorem eq_meet (h : hgt u a ≠ hgt u b) (hz : z ∈ segment ℝ a b) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨r, -, rfl⟩ := hz
  have : (hgt u (a + r • (b - a)) - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hgt_lin]; field_simp; ring
  rw [meet, this]

/-- Reversing an edge does not move its meeting point. -/
theorem meet_swap (h : hgt u a ≠ hgt u b) (t : ℝ) : meet u b a t = meet u a b t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : (t - hgt u b) / (hgt u a - hgt u b)
      = 1 - (t - hgt u a) / (hgt u b - hgt u a) := by field_simp; ring
  rw [meet, meet, h2, sub_smul, one_smul, smul_sub, smul_sub]
  abel

/-! ### The crossing count -/

/-- The edge `P` meets the level line through `q` strictly beyond `q`.

The height test is half-open at the bottom: an edge whose lower end is exactly at the height
of `q` counts, one whose upper end is counts not. That convention is what makes the count
well defined at every `q` off the polygon, with no genericity assumption. -/
def Crosses (u : Plane) (P : Piece) (q : Plane) : Prop :=
  min (hgt u P.1) (hgt u P.2) ≤ hgt u q ∧ hgt u q < max (hgt u P.1) (hgt u P.2) ∧
    fwd u q < fwd u (meet u P.1 P.2 (hgt u q))

/-- Crossing is decided classically; the count is a `noncomputable` definition. -/
noncomputable instance decidableCrosses (u : Plane) (P : Piece) (q : Plane) :
    Decidable (Crosses u P q) := Classical.dec _

theorem crosses_swap (h : hgt u a ≠ hgt u b) (q : Plane) :
    Crosses u (b, a) q ↔ Crosses u (a, b) q := by
  simp only [Crosses, meet_swap h, min_comm (hgt u b) (hgt u a), max_comm (hgt u b) (hgt u a)]

/-- The contribution of one edge to the parity. -/
noncomputable def mark (u : Plane) (P : Piece) (q : Plane) : ZMod 2 :=
  if Crosses u P q then 1 else 0

/-- The crossing parity `π_C(q)`. -/
noncomputable def parity (u : Plane) (L : List Piece) (q : Plane) : ZMod 2 :=
  (L.map (fun P => mark u P q)).sum

theorem parity_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    parity u (L₁ ++ L₂) q = parity u L₁ q + parity u L₂ q := by
  simp [parity, List.sum_append]

/-! ### Subdivision invariance -/

/-- An interior point of a non-level edge is strictly between its ends in height. -/
theorem hgt_lt_of_mem_openSegment (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a < hgt u c ∧ hgt u c < hgt u b := by
  rw [openSegment_eq_image' ℝ a b] at hc
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hc
  rw [hgt_lin]
  constructor
  · nlinarith
  · nlinarith

/-! ### Closed chains -/

theorem sum_map_add {α : Type*} (l : List α) (F G : α → ZMod 2) :
    (l.map (fun x => F x + G x)).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem add_self_zmod_two (x : ZMod 2) : x + x = 0 := by
  revert x; decide

/-- The edge list is a **closed chain**: its boundary vanishes mod `2`. Stated by duality —
every `ZMod 2`-valued function of the ends sums to zero over the list — which is exactly what
the parity argument consumes, and which `isClosedChain_edgesOf` supplies for a cyclic vertex
list. -/
def IsClosedChain (L : List Piece) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map (fun P => f P.1 + f P.2)).sum = 0

/-! ### What a list of edges occupies -/

theorem mem_cover {P : Piece} (hP : P ∈ L) (hz : z ∈ P.seg) : z ∈ cover L :=
  Set.mem_biUnion hP hz

theorem isCompact_cover (L : List Piece) : IsCompact (cover L) := by
  induction L with
  | nil => rw [cover_nil]; exact isCompact_empty
  | cons P L ih => rw [cover_cons]; exact (isCompact_segment P.1 P.2).union ih

theorem isClosed_cover (L : List Piece) : IsClosed (cover L) := (isCompact_cover L).isClosed

/-- Where an edge meets the level line, when it does. -/
theorem meet_mem_seg {P : Piece} (h : hgt u P.1 ≠ hgt u P.2)
    (h1 : min (hgt u P.1) (hgt u P.2) ≤ t) (h2 : t ≤ max (hgt u P.1) (hgt u P.2)) :
    meet u P.1 P.2 t ∈ P.seg := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [min_eq_left hlt.le] at h1
    rw [max_eq_right hlt.le] at h2
    exact meet_mem_segment hlt h1 h2
  · rw [min_eq_right hlt.le] at h1
    rw [max_eq_left hlt.le] at h2
    have hmem := meet_mem_segment hlt h1 h2
    rwa [meet_swap h, segment_symm] at hmem

/-! ### Moving the base point -/

section Moves

variable (hu : Plane.IsDirection u)
include hu

omit hu in
theorem hgt_along (q : Plane) (s : ℝ) : hgt u (q + s • u) = hgt u q := by
  rw [hgt_add_smul, hgt_self]; ring

theorem fwd_along (q : Plane) (s : ℝ) : fwd u (q + s • u) = fwd u q + s := by
  rw [fwd_add_smul, fwd_self hu]; ring

theorem hgt_across (q : Plane) (s : ℝ) : hgt u (q + s • Plane.perp u) = hgt u q + s := by
  rw [hgt_add_smul, hgt_perp hu]; ring

omit hu in
theorem fwd_across (q : Plane) (s : ℝ) : fwd u (q + s • Plane.perp u) = fwd u q := by
  rw [fwd_add_smul, fwd_perp]; ring

/-- The segment from `q` in the ray direction is exactly the points at the same height with
`fwd` in between. -/
theorem mem_segment_along {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : hgt u y = hgt u q)
    (h2 : fwd u q ≤ fwd u y) (h3 : fwd u y ≤ fwd u q + s) :
    y ∈ segment ℝ q (q + s • u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu (by linarith) h1
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • u)]
    refine ⟨(fwd u y - fwd u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • u - q = s • u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_self hu]; ring)
      (by rw [hgt_add_smul, hgt_self, h1]; ring)

/-- The segment from `q` across the ray direction is exactly the points with the same `fwd`
and height in between. -/
theorem mem_segment_across {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : fwd u y = fwd u q)
    (h2 : hgt u q ≤ hgt u y) (h3 : hgt u y ≤ hgt u q + s) :
    y ∈ segment ℝ q (q + s • Plane.perp u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu h1 (by linarith)
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • Plane.perp u)]
    refine ⟨(hgt u y - hgt u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • Plane.perp u - q = s • Plane.perp u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_perp, h1]; ring)
      (by rw [hgt_add_smul, hgt_perp hu]; ring)

omit hu in
/-- A connected piece of an edge that stays between two heights and never meets the level
line `fwd = ξ` stays on one side of it. -/
theorem side_const {lo hi ξ : ℝ}
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = ξ → lo ≤ hgt u y → hgt u y ≤ hi → False)
    (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzl : lo ≤ hgt u z) (hzh : hgt u z ≤ hi) (hwl : lo ≤ hgt u w) (hwh : hgt u w ≤ hi) :
    (ξ < fwd u z ↔ ξ < fwd u w) := by
  have key : ∀ z w : Plane, z ∈ segment ℝ a b → w ∈ segment ℝ a b →
      lo ≤ hgt u z → hgt u z ≤ hi → lo ≤ hgt u w → hgt u w ≤ hi →
      ξ < fwd u z → ξ < fwd u w := by
    intro z w hz hw hzl hzh hwl hwh hlt
    by_contra hcon
    push Not at hcon
    have hpos : 0 < fwd u z - fwd u w := by linarith
    set r := (fwd u z - ξ) / (fwd u z - fwd u w) with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hy : z + r • (w - z) ∈ segment ℝ a b :=
      (convex_segment a b).segment_subset hz hw
        (by rw [segment_eq_image' ℝ z w]; exact ⟨r, ⟨hr0, hr1⟩, rfl⟩)
    refine hmiss _ hy ?_ ?_ ?_
    · rw [fwd_lin, hr]; field_simp; ring
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwl), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzl)]
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwh), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzh)]
  exact ⟨fun h => key z w hz hw hzl hzh hwl hwh h, fun h => key w z hw hz hwl hwh hzl hzh h⟩

/-- Moving the base point along the ray direction, without meeting the polygon, changes no
crossing. -/
theorem parity_move_along (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane} {s : ℝ}
    (hs : 0 ≤ s) (hmiss : ∀ y ∈ segment ℝ q (q + s • u), y ∉ cover L) :
    parity u L (q + s • u) = parity u L q := by
  refine congrArg List.sum (List.map_congr_left ?_)
  intro P hP
  have hPne := hL P hP
  have hiff : Crosses u P (q + s • u) ↔ Crosses u P q := by
    simp only [Crosses, hgt_along, fwd_along hu]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hmiss _ (mem_segment_along hu hs (hgt_meet hPne _) h3.le hcon)
        (mem_cover hP (meet_mem_seg hPne h1 h2.le))
  simp only [mark, hiff]

end Moves

/-! ### Sweeping across the ray direction -/

/-- The marker attached to a vertex when the base point is swept across by `s`: the vertex
counts when its height lies in the half-open band swept out and it lies beyond the base
point. Summed over both ends of every edge this vanishes, because the polygon is closed;
that is the whole content of crossing parity. -/
noncomputable def fmark (u q : Plane) (s : ℝ) (v : Plane) : ZMod 2 :=
  if hgt u q < hgt u v ∧ hgt u v ≤ hgt u q + s ∧ fwd u q < fwd u v then 1 else 0

theorem mark_swap (h : hgt u a ≠ hgt u b) (q : Plane) : mark u (b, a) q = mark u (a, b) q := by
  simp only [mark, crosses_swap h]

section Across

variable (hu : Plane.IsDirection u)
include hu

/-- One edge, swept across. The crossings gained or lost are exactly the ends whose heights
the sweep passes, on the far side of the base point. -/
private theorem mark_step {q : Plane} {s : ℝ} (hs : 0 ≤ s) (hab : hgt u a < hgt u b)
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
      hgt u y ≤ hgt u q + s → False) :
    mark u (a, b) q + mark u (a, b) (q + s • Plane.perp u)
      = fmark u q s a + fmark u q s b := by
  have hne : hgt u a ≠ hgt u b := ne_of_lt hab
  have hha : ∀ t : ℝ, hgt u (meet u a b t) = t := fun t => hgt_meet hne t
  have hma : ∀ t : ℝ, hgt u a ≤ t → t ≤ hgt u b → meet u a b t ∈ segment ℝ a b :=
    fun t h1 h2 => meet_mem_segment hab h1 h2
  have haseg : a ∈ segment ℝ a b := left_mem_segment ℝ a b
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hside : ∀ z, z ∈ segment ℝ a b → ∀ w, w ∈ segment ℝ a b →
      hgt u q ≤ hgt u z → hgt u z ≤ hgt u q + s →
      hgt u q ≤ hgt u w → hgt u w ≤ hgt u q + s →
      (fwd u q < fwd u z ↔ fwd u q < fwd u w) :=
    fun z hz w hw h1 h2 h3 h4 => side_const hmiss hz hw h1 h2 h3 h4
  simp only [mark, fmark, Crosses, min_eq_left hab.le, max_eq_right hab.le,
    hgt_across hu, fwd_across]
  rcases le_or_gt (hgt u a) (hgt u q) with hA | hA
  · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
    · -- the sweep stays strictly below the upper end: no end is passed
      have e := hside (meet u a b (hgt u q)) (hma _ hA (by linarith))
        (meet u a b (hgt u q + s)) (hma _ (by linarith) hB.le)
        (hha _).ge (by rw [hha]; linarith) (by rw [hha]; linarith) (hha _).le
      by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
      · rw [if_pos ⟨hA, by linarith, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩,
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
        decide
      · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
          if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g)),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
    · rcases lt_or_ge (hgt u q) (hgt u b) with hB2 | hB2
      · -- the sweep passes the upper end
        have e := hside (meet u a b (hgt u q)) (hma _ hA hB2.le) b hbseg
          (hha _).ge (by rw [hha]; linarith) (by linarith) hB
        by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
        · rw [if_pos ⟨hA, hB2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hB2, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
      · -- the edge is entirely below the sweep
        rw [if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith)]
  · rcases le_or_gt (hgt u a) (hgt u q + s) with hA2 | hA2
    · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
      · -- the sweep passes the lower end only
        have e := hside (meet u a b (hgt u q + s)) (hma _ hA2 hB.le) a haseg
          (by rw [hha]; linarith) (hha _).le (by linarith) hA2
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hA2, hB, e.2 hD⟩,
            if_pos ⟨hA, hA2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith)]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.1 g)),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith)]
      · -- the sweep passes both ends
        have e := hside a haseg b hbseg (by linarith) hA2 (by linarith) hB
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_pos ⟨hA, hA2, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
    · -- the edge is entirely above the sweep
      rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith),
        if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]

/-- Sweeping the base point across the ray direction, without meeting the polygon, does not
change the parity. This is where the polygon has to be closed. -/
theorem parity_move_across (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q : Plane} {s : ℝ} (hs : 0 ≤ s)
    (hmiss : ∀ y ∈ segment ℝ q (q + s • Plane.perp u), y ∉ cover L) :
    parity u L (q + s • Plane.perp u) = parity u L q := by
  have key : ∀ P ∈ L, mark u P q + mark u P (q + s • Plane.perp u)
      = fmark u q s P.1 + fmark u q s P.2 := by
    intro P hP
    obtain ⟨a, b⟩ := P
    have hne := hL (a, b) hP
    have hmiss' : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
        hgt u y ≤ hgt u q + s → False := fun y hy h1 h2 h3 =>
      hmiss y (mem_segment_across hu hs h1 h2 h3) (mem_cover hP hy)
    rcases lt_or_gt_of_ne hne with h | h
    · exact mark_step hu hs h hmiss'
    · have hmiss'' : ∀ y ∈ segment ℝ b a, fwd u y = fwd u q → hgt u q ≤ hgt u y →
          hgt u y ≤ hgt u q + s → False := by
        intro y hy
        exact hmiss' y (by rwa [segment_symm] at hy)
      have hstep := mark_step hu hs h hmiss''
      rw [mark_swap hne, mark_swap hne] at hstep
      rw [hstep]
      exact add_comm _ _
  have hzero : parity u L q + parity u L (q + s • Plane.perp u) = 0 := by
    rw [parity, parity, ← sum_map_add, List.map_congr_left key]
    exact hC (fun v => fmark u q s v)
  have harith : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact harith _ _ hzero

/-- The two moves, for a shift of either sign. -/
theorem parity_move_along' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q q' : Plane} (s : ℝ)
    (hq' : q' = q + s • u) (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_along hu hL hs hmiss
  · have hq : q = q' + (-s) • u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_along hu hL (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

theorem parity_move_across' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} (s : ℝ) (hq' : q' = q + s • Plane.perp u)
    (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_across hu hL hC hs hmiss
  · have hq : q = q' + (-s) • Plane.perp u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • Plane.perp u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_across hu hL hC (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

end Across

/-! ### Crossing parity -/

theorem exists_ball_avoiding {z : Plane} (h : z ∉ cover L) :
    ∃ ε > 0, ∀ y ∈ ball z ε, y ∉ cover L := by
  have hopen := (isClosed_cover L).isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hsub⟩ := hopen z h
  exact ⟨ε, hε, fun y hy => hsub hy⟩

section Constancy

variable (hu : Plane.IsDirection u)
include hu

/-- The parity is constant on a ball that misses the polygon: reach any nearby point by a
move along the ray direction followed by a move across it. -/
theorem parity_eq_of_mem_ball (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} {ε : ℝ} (hq' : q' ∈ ball q ε) (hmiss : ∀ y ∈ ball q ε, y ∉ cover L) :
    parity u L q' = parity u L q := by
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (mem_ball.1 hq')
  have hqb : q ∈ ball q ε := mem_ball_self hεpos
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = q + (fwd u (q' - q)) • u := ⟨_, rfl⟩
  have hwball : w ∈ ball q ε := by
    have hsub : q + (fwd u (q' - q)) • u - q = (fwd u (q' - q)) • u := by abel
    rw [mem_ball, dist_eq_norm, hw, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    calc |fwd u (q' - q)| ≤ ‖q' - q‖ := abs_fwd_le_norm hu _
      _ = dist q' q := (dist_eq_norm q' q).symm
      _ < ε := mem_ball.1 hq'
  have hq'w : q' = w + (hgt u (q' - q)) • Plane.perp u := by
    have hd := decomp hu (q' - q)
    rw [hw, add_assoc, ← hd]
    abel
  have h1 : parity u L w = parity u L q :=
    parity_move_along' hu hL _ hw
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hqb hwball hy))
  have h2 : parity u L q' = parity u L w :=
    parity_move_across' hu hL hC _ hq'w
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hwball hq' hy))
  rw [h2, h1]

/-- **Crossing parity** (Lemma 2.2). `π_C` is constant on every preconnected subset of the
complement of the polygon — in particular on every component. -/
theorem parity_eq_of_isPreconnected (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {S : Set Plane} (hS : IsPreconnected S)
    (hSC : ∀ z ∈ S, z ∉ cover L) {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    parity u L x = parity u L y := by
  by_contra hne
  have hopen : ∀ c : ZMod 2, IsOpen {z : Plane | z ∉ cover L ∧ parity u L z = c} := by
    intro c
    rw [Metric.isOpen_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hz1
    exact ⟨ε, hε, fun t ht => ⟨hball t ht,
      by rw [parity_eq_of_mem_ball hu hL hC ht hball, hz2]⟩⟩
  have htwo : ∀ e : ZMod 2, e = parity u L x ∨ e = parity u L y := by
    revert hne
    generalize parity u L x = c
    generalize parity u L y = d
    revert c d
    decide
  obtain ⟨z, -, hzA, hzB⟩ :=
    hS _ _ (hopen (parity u L x)) (hopen (parity u L y))
      (fun t ht => (htwo (parity u L t)).imp (fun h => ⟨hSC t ht, h⟩) (fun h => ⟨hSC t ht, h⟩))
      ⟨x, hx, hSC x hx, rfl⟩ ⟨y, hy, hSC y hy, rfl⟩
  exact hne (hzA.2 ▸ hzB.2)

/-- The parity is constant on the component of the complement containing a point. -/
theorem parity_eq_of_mem_connectedComponentIn (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {x y : Plane} (hx : x ∉ cover L)
    (hy : y ∈ connectedComponentIn (cover L)ᶜ x) : parity u L y = parity u L x :=
  parity_eq_of_isPreconnected hu hL hC isPreconnected_connectedComponentIn
    (fun _ ht => connectedComponentIn_subset _ _ ht) hy (mem_connectedComponentIn hx)

end Constancy

/-! ### The value far along the ray, and the jump across an edge -/

/-- Beyond the polygon in the ray direction the count is zero. -/
theorem parity_eq_zero_of_lt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane}
    (h : ∀ z ∈ cover L, fwd u z < fwd u q) : parity u L q = 0 := by
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  refine if_neg ?_
  rintro ⟨h1, h2, h3⟩
  exact absurd (h _ (mem_cover hP (meet_mem_seg (hL P hP) h1 h2.le))) (not_lt.2 h3.le)

section Flip

variable (hu : Plane.IsDirection u)
include hu

/-- **Opposite sides of an edge** (Lemma 2.2, second half). At an interior point `p` of one
edge of the list which no other edge of the list passes through, the two points just before
and just after `p` in the ray direction lie off the polygon and have opposite parity: the
count changes by one as the base point sweeps across the edge. -/
theorem parity_flip {L₁ L₂ : List Piece} {a b p : Plane}
    (hL : ∀ P ∈ L₁ ++ (a, b) :: L₂, hgt u P.1 ≠ hgt u P.2)
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      p + t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
        = parity u (L₁ ++ (a, b) :: L₂) (p + t • u) + 1 := by
  have hab : hgt u a ≠ hgt u b := hL (a, b) (by simp)
  have hpK : p ∉ cover (L₁ ++ L₂) := by
    rw [cover_append]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hpK
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  -- the two test points and their frame coordinates
  have hneg : p - t • u = p + (-t) • u := by rw [neg_smul]; abel
  have hgm : hgt u (p - t • u) = hgt u p := by rw [hneg, hgt_along]
  have hgp : hgt u (p + t • u) = hgt u p := hgt_along p t
  have hfm : fwd u (p - t • u) = fwd u p - t := by rw [hneg, fwd_along hu]; ring
  have hfp : fwd u (p + t • u) = fwd u p + t := fwd_along hu p t
  have hdist : ∀ r : ℝ, |r| < ε → p + r • u ∈ ball p ε := by
    intro r hr
    have hsub : p + r • u - p = r • u := by abel
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    exact hr
  have habsm : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht]; exact htε
  have habsp : |t| < ε := by rw [abs_of_pos ht]; exact htε
  -- the only point of the edge at the height of `p` is `p` itself
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have hmeetp : meet u a b (hgt u p) = p := (eq_meet hab hpseg).symm
  have hnotseg : ∀ r : ℝ, r ≠ 0 → p + r • u ∉ segment ℝ a b := by
    intro r hr hmem
    have heq : p + r • u = p := by
      rw [eq_meet hab hmem, hgt_along, hmeetp]
    have hf : fwd u (p + r • u) = fwd u p + r := fwd_along hu p r
    rw [heq] at hf
    exact hr (by linarith)
  have hcov : ∀ r : ℝ, r ≠ 0 → |r| < ε → p + r • u ∉ cover (L₁ ++ (a, b) :: L₂) := by
    intro r hr hrε hmem
    rw [cover_append, cover_cons] at hmem
    rcases hmem with h | h | h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inl h)
    · exact hnotseg r hr h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inr h)
  -- an edge other than `(a, b)` meets the level line far from `p`, so it is not affected
  have hfar : ∀ P ∈ L₁ ++ L₂, hgt u P.1 ≠ hgt u P.2 →
      min (hgt u P.1) (hgt u P.2) ≤ hgt u p → hgt u p ≤ max (hgt u P.1) (hgt u P.2) →
      ε ≤ |fwd u (meet u P.1 P.2 (hgt u p)) - fwd u p| := by
    intro P hP hPne g1 g2
    have hmcov : meet u P.1 P.2 (hgt u p) ∈ cover (L₁ ++ L₂) :=
      mem_cover hP (meet_mem_seg hPne g1 g2)
    have hmnb : ¬ (dist (meet u P.1 P.2 (hgt u p)) p < ε) := fun h =>
      hball _ (mem_ball.2 h) hmcov
    push Not at hmnb
    rw [dist_eq_norm] at hmnb
    have hh : hgt u (meet u P.1 P.2 (hgt u p) - p) = 0 := by
      rw [hgt_sub, hgt_meet hPne]; ring
    have hd := decomp hu (meet u P.1 P.2 (hgt u p) - p)
    rw [hh, zero_smul, add_zero] at hd
    have hnorm : ‖meet u P.1 P.2 (hgt u p) - p‖
        = |fwd u (meet u P.1 P.2 (hgt u p) - p)| := by
      conv_lhs => rw [hd]
      rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [hnorm, fwd_sub] at hmnb
    exact hmnb
  have hother : ∀ P ∈ L₁ ++ L₂, mark u P (p - t • u) + mark u P (p + t • u) = 0 := by
    intro P hP
    have hPne : hgt u P.1 ≠ hgt u P.2 := by
      rcases List.mem_append.1 hP with h | h
      · exact hL P (by simp [h])
      · exact hL P (by simp [h])
    have hiff : Crosses u P (p - t • u) ↔ Crosses u P (p + t • u) := by
      simp only [Crosses, hgm, hgp, hfm, hfp]
      constructor
      · rintro ⟨g1, g2, g3⟩
        refine ⟨g1, g2, ?_⟩
        rcases le_abs.1 (hfar P hP hPne g1 g2.le) with hcase | hcase
        · linarith
        · linarith
      · rintro ⟨g1, g2, g3⟩
        exact ⟨g1, g2, by linarith⟩
    simp only [mark, hiff]
    exact add_self_zmod_two _
  -- the edge `(a, b)` itself is crossed from exactly one of the two points
  have hbtw : min (hgt u a) (hgt u b) < hgt u p ∧ hgt u p < max (hgt u a) (hgt u b) := by
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h hp
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨g1, g2⟩
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hp)
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨g1, g2⟩
  have hedge : mark u (a, b) (p - t • u) + mark u (a, b) (p + t • u) = 1 := by
    have hm1 : Crosses u (a, b) (p - t • u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hgm]; exact hbtw.1.le
      · rw [hgm]; exact hbtw.2
      · rw [hgm, hfm, hmeetp]; linarith
    have hm2 : ¬ Crosses u (a, b) (p + t • u) := by
      rintro ⟨-, -, g⟩
      rw [hgp, hfp, hmeetp] at g
      linarith
    rw [mark, mark, if_pos hm1, if_neg hm2, add_zero]
  refine ⟨by rw [hneg]; exact hcov (-t) (by linarith) habsm, hcov t (ne_of_gt ht) habsp, ?_⟩
  have hz1 : (L₁.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_left _ hP)
  have hz2 : (L₂.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_right _ hP)
  have hsum : parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
      + parity u (L₁ ++ (a, b) :: L₂) (p + t • u) = 1 := by
    rw [parity, parity, ← sum_map_add, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, hz1, hz2, hedge]
    ring
  have harith : ∀ x y : ZMod 2, x + y = 1 → x = y + 1 := by decide
  exact harith _ _ hsum

end Flip

/-! ### Choosing the ray direction -/

/-- The blueprint's opening move — "rotate so that no edge is horizontal" — without rotating
anything: finitely many edge directions rule out only finitely many rays, so some direction
is level for none of them. -/
theorem exists_direction_hgt_ne (L : List Piece) (hnd : ∀ P ∈ L, P.Nondeg) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2 := by
  obtain ⟨u, hu, hdet⟩ :=
    Plane.exists_isDirection_det_ne_zero (L.finite_toSet.image (fun P : Piece => P.2 - P.1))
  refine ⟨u, hu, fun P hP heq => ?_⟩
  have hne : P.2 - P.1 ≠ 0 := sub_ne_zero.2 fun h => hnd P hP h.symm
  have hzero : hgt u (P.2 - P.1) = 0 := by rw [hgt_sub, heq]; ring
  exact hdet _ ⟨P, hP, rfl⟩ hne hzero

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolygonBridge.lean` -/

/-!
# The polygon bridge

Two independent representations of a closed polygon had grown up side by side and never met.
`Schoenflies/Strip.lean` carries `ClosedPolygon m`, a cyclic vertex list indexed by
`ZMod (m + 3)`, and everything the collar of Lemma 1.8 says is said about it.
`Schoenflies/Parity.lean` carries `List Piece` together with `IsClosedChain`, and everything
the crossing count of Lemma 2.1 and Lemma 2.2 says is said about *that*. Neither knew about
the other, and — worse — nothing anywhere produced a `ClosedPolygon`, so every theorem about
one was formally a theorem about a structure that might have been empty.

This module closes the three gaps.

## Non-vacuity

`Schoenflies.triangle` builds a `ClosedPolygon 0` out of any three points with nonzero
orientation determinant, and `Schoenflies.unitTriangle` is the concrete instance with vertices
`(0,0)`, `(1,0)`, `(0,1)`. The only real work is `edges_meet`: two edges of a triangle share
exactly one endpoint, and `Schoenflies.segment_inter_shared` says two segments meeting at an
endpoint whose far ends are off the shared line meet nowhere else. That lemma is proved by
taking the orientation form against the first segment's direction, which kills the first
segment's own parameter and forces the second's to vanish.

## The representation bridge

`ClosedPolygon.pieces` lists the `m + 3` edges as pairs of endpoints, in cyclic order.
It is a closed chain (`ClosedPolygon.isClosedChain_pieces`), every piece is nondegenerate
(`ClosedPolygon.pieces_nondeg`), and — the point of the exercise —
`ClosedPolygon.cover_pieces` says it occupies exactly the polygon's carrier. Closedness is a
telescoping sum: `Schoenflies.sum_range_boundary` evaluates the mod-`2` boundary of the chain
`0 → 1 → ⋯ → n` as the sum of its two ends, and the two ends of `0 → ⋯ → m + 3` are the same
vertex because `m + 3` is `0` in `ZMod (m + 3)`.

## The curve bridge

`ClosedPolygon.isJordanCurve_carrier` and `ClosedPolygon.isPolygonal_carrier` say the carrier
is a simple closed polygonal curve in the blueprint's sense, which is what the polygonal Jordan
curve theorem (Theorem 2.3) takes as its hypothesis. The loop is built by concatenating edge
parametrizations around the cycle: `ClosedPolygon.chain k` is the union of the edges leaving
vertices `0, …, k`, and `ClosedPolygon.isArcBetween_chain` grows it one edge at a time by
`IsArcBetween.concatenate`. The hypothesis that concatenation needs — the new edge meets what
came before only at the vertex they share — is exactly `edges_meet` twice over: once to place
the meeting point among the new edge's own two endpoints, and once more to rule out the far
one, which would otherwise let the polygon close early. The last edge closes the loop through
`IsJordanCurve.of_two_arcs`, and there the far endpoint is *not* ruled out: it is the second
shared point that makes the two arcs a curve rather than an arc.

## Both halves at once

The last section is what the bridge is for: the two statements of Lemma 2.2 — parity is
constant on a component of the complement, and it flips across an edge — restated for the
*carrier* of a `ClosedPolygon` rather than for the cover of an anonymous list. The flip needs
the edge list split around the edge being crossed, which is `List.append_of_mem` together with
`ClosedPolygon.pieces_nodup`; that the two remaining fragments miss the crossing point is
`edges_meet` a third time.

## Blueprint

* `Schoenflies.triangle`, `Schoenflies.unitTriangle` — witnesses that §1's "simple closed
  polygonal curve" is not vacuous.
* `ClosedPolygon.pieces`, `ClosedPolygon.cover_pieces`, `ClosedPolygon.isClosedChain_pieces` —
  the edge list the crossing count of §2 is defined on, and that it carries the polygon.
* `ClosedPolygon.isJordanCurve_carrier`, `ClosedPolygon.isPolygonal_carrier` — §1, "a simple
  closed polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier` — the two halves of Lemma 2.2, read off a
  `ClosedPolygon`. These are the statements Theorem 2.3 consumes.

One general lemma is stated here that does not belong here: `Schoenflies.exists_of_mem_cover`,
the destructor matching `Schoenflies.mem_cover`, whose home is `Schoenflies/Parity.lean`.
-/

namespace Schoenflies

variable {m : ℕ}

/-! ## Two segments that share an endpoint

The one piece of plane geometry this module needs. `Schoenflies/SegmentMeet.lean` describes
the intersection of two arbitrary segments; here the two are known to share an endpoint, and
the conclusion is sharper and the proof shorter. -/

/-! ## Non-vacuity: a triangle is a closed polygon

Nothing in the strip development ever built a `ClosedPolygon`, so `polygonal_collar` and every
theorem beside it was formally a theorem about a structure with no known inhabitant. A triangle
is the smallest witness, and no coordinates are needed: any three points with nonzero
orientation determinant will do. -/

/-! ## A telescoping sum mod two -/

/-- The mod-`2` boundary of the chain `0 → 1 → ⋯ → n` is the sum of its two ends: every
interior vertex is counted twice. This is the whole content of "a cycle is a closed chain". -/
theorem sum_range_boundary (g : ℕ → ZMod 2) :
    ∀ n : ℕ, ((List.range n).map fun j => g j + g (j + 1)).sum = g 0 + g n
  | 0 => by simpa using (add_self_zmod_two (g 0)).symm
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_boundary g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linear_combination add_self_zmod_two (g n)

namespace ClosedPolygon

/-! ## Natural-number indices

Both bridges run over the vertices with a natural number and cast into `ZMod (m + 3)`. Below
the modulus the cast is injective, which is what turns "these two indices are different
naturals" into "these are different edges" and back. -/

/-- Below the modulus, casting a natural number into `ZMod (m + 3)` is injective. -/
theorem natCast_inj {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3)
    (h : (j : ZMod (m + 3)) = (k : ZMod (m + 3))) : j = k := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at hval

/-- The successor, pushed through the cast. -/
theorem natCast_succ (j : ℕ) : ((j + 1 : ℕ) : ZMod (m + 3)) = (j : ZMod (m + 3)) + 1 := by
  push_cast; ring

variable {P : ClosedPolygon m}

/-- **An edge meets an earlier edge only at its own initial vertex.** `edges_meet` puts the
meeting point at one of the two ends of the later edge; the far end is ruled out by applying
`edges_meet` the other way round, which would put the later edge's *terminal* vertex on the
earlier edge and hence make it one of two vertices it cannot be. This is what stops the
polygon from closing before it has run through all its vertices. -/
theorem edge_meet_earlier {j k : ℕ} (hjk : j < k) (hk : k + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzk : z ∈ P.edge (k : ZMod (m + 3))) :
    z = P.vertex (k : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hkn : k < m + 3 := by omega
  have hne : (k : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : k ≠ j) (natCast_inj hkn hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzk hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  -- The far end: it would have to be one of the earlier edge's two ends as well.
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzk)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : k + 1 = j := natCast_inj hk hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← natCast_succ] at hmem2
    have : k + 1 = j + 1 := natCast_inj hk (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-- **The last edge meets every earlier edge only at a vertex it shares with the cycle's ends.**
Here the far end is *not* excluded: the last edge runs back to vertex `0`, so both of its ends
are legitimate meeting points, and that is precisely what makes the carrier a closed curve
rather than an arc. -/
theorem edge_meet_last {j : ℕ} (hj : j < m + 2) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3)))
    (hz : z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3))) :
    z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
  have hne : ((m + 2 : ℕ) : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : m + 2 ≠ j) (natCast_inj (by omega) (by omega) heq)
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hz hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact Or.inr hmem
  · rw [hlast] at hmem
    exact Or.inl hmem

/-! ## The representation bridge

`Schoenflies/Parity.lean` counts crossings of a `List Piece`; `ClosedPolygon.pieces` is the
list it should be handed. The four obligations below are exactly what every parity statement
asks for: a list, closedness, nondegeneracy, and — the one that carries the geometry — that
the list occupies the polygon. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form
the crossing count of §2 is defined on. -/
def pieces (P : ClosedPolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : ClosedPolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge of a simple closed polygon is degenerate: consecutive vertices are distinct. -/
theorem pieces_nondeg (P : ClosedPolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact P.vertex_ne i

/-- **The edge list is a closed chain.** Each vertex is the terminal end of one edge and the
initial end of the next, so it is counted twice; the cycle closes because `m + 3` is `0` in
`ZMod (m + 3)`, which makes the two ends of the telescoping sum the same vertex. -/
theorem isClosedChain_pieces (P : ClosedPolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** Without this equation no parity statement says
anything about a `ClosedPolygon`: the crossing count is defined against `cover`, and the collar
against `carrier`. -/
theorem cover_pieces (P : ClosedPolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-! ## The curve bridge

`chain k` is the union of the edges leaving vertices `0, …, k`. Each is an arc from vertex `0`
to vertex `k + 1`, obtained from its predecessor by `IsArcBetween.concatenate`; the whole
carrier is the last of them plus the edge that runs back to vertex `0`. -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : ClosedPolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} {k : ℕ} :
    z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- Running through all `m + 3` edges exhausts the carrier. -/
theorem chain_eq_carrier (P : ClosedPolygon m) : P.chain (m + 2) = P.carrier := by
  ext z
  rw [mem_chain_iff]
  constructor
  · rintro ⟨j, -, hzj⟩
    exact Set.mem_iUnion.2 ⟨_, hzj⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
    refine ⟨i.val, ?_, ?_⟩
    · have := ZMod.val_lt i
      omega
    · rwa [ZMod.natCast_rightInverse i]

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share:
`edge_meet_earlier` is exactly the hypothesis `IsArcBetween.concatenate` asks for. The bound
`k + 1 < m + 3` is what keeps the growing arc from meeting its own start. -/
theorem isArcBetween_chain (P : ClosedPolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [natCast_succ]
    exact isArcBetween_segment (P.vertex_ne 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [natCast_succ (k + 1)]
      exact isArcBetween_segment (P.vertex_ne _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-- **The carrier of a simple closed polygon is a Jordan curve.** The arc through all but the
last edge, and the last edge running back to where it started, meet exactly at their two
shared endpoints. -/
theorem isJordanCurve_carrier (P : ClosedPolygon m) : IsJordanCurve P.carrier := by
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hA : IsArcBetween (P.chain (m + 1)) (P.vertex 0)
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) := P.isArcBetween_chain (m + 1) (by omega)
  have hedge : P.edge ((m + 2 : ℕ) : ZMod (m + 3))
      = segment ℝ (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [edge, hlast]
  have hB : IsArcBetween (P.edge ((m + 2 : ℕ) : ZMod (m + 3)))
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [hedge]
    refine isArcBetween_segment ?_
    rw [← hlast]
    exact P.vertex_ne _
  have hmeet : ∀ z ∈ P.chain (m + 1), z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) →
      z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
    intro z hz hze
    obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
    exact edge_meet_last (by omega) hzj hze
  have hcurve := IsJordanCurve.of_two_arcs hA hB hmeet
  have hsplit : P.chain (m + 2)
      = P.chain (m + 1) ∪ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) := rfl
  rwa [← hsplit, chain_eq_carrier] at hcurve

/-! ### The carrier is polygonal

`IsPolygonal` asks for a vertex list whose `poly` carrier is the set. Cycling once round the
polygon and coming back to the first vertex is that list. -/

/-! ## The bridge in use

With both halves in place a parity statement can be read off a `ClosedPolygon` directly. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate
system so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : ClosedPolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity for a closed polygon** (Lemma 2.2): `π_C` is constant on the component
of the complement of the *carrier* containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-! ### The flip across an edge

The second half of Lemma 2.2 is stated for the edge list split around the edge being crossed,
`L₁ ++ (a, b) :: L₂`. Splitting is `List.append_of_mem`; what has to be checked is that the two
remaining fragments miss the point being crossed, and that is `edges_meet` again — another edge
can reach an interior point of this one only at one of this one's two ends, which an interior
point is not. -/

/-- What a list of pieces occupies, taken apart. The counterpart of `Schoenflies.mem_cover`,
which only builds; **this belongs next to it in `Schoenflies/Parity.lean`.** -/
theorem exists_of_mem_cover {L : List Piece} {z : Plane} (hz : z ∈ cover L) :
    ∃ R ∈ L, z ∈ R.seg := by
  rw [cover] at hz
  simpa using hz

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's
meeting point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {i j : ZMod (m + 3)} (hij : j ≠ i) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact P.vertex_ne i (left_mem_openSegment_iff.1 hp)
  · exact P.vertex_ne i (right_mem_openSegment_iff.1 hp)

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : ClosedPolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-- **Opposite sides of an edge, for a closed polygon** (Lemma 2.2, second half). Just before
and just after an interior point of an edge, in the ray direction, the base point is off the
carrier and the crossing parity differs by one. -/
theorem parity_flip_carrier (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

end ClosedPolygon

end Schoenflies

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/StripConstants.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The constants of a polygonal collar exist

`Schoenflies.StripData` names the three numbers the two-sided strip lemma runs on — a cone
radius `R`, a trim `lam` and a half-width `rho` — together with the separation hypotheses they
have to satisfy. Everything in `Schoenflies/Strip.lean` is stated *for a given* `StripData`;
this module produces one, removing that parameter from the resulting theorem.

The recipe is the blueprint's own, in the blueprint's order:

1. `R` from three sources — the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, and the prescribed open set — each an instance of Lemma 1.4, plus
   `R ≤ len i` so that a sector cannot run past the far end of an incident edge. The vertex
   separations are asked for with a factor `2` of slack, which is what the block-versus-sector
   estimates of `Strip.lean` spend.
2. `lam := R / 5`, which gives `2 * lam < R` and, through `R ≤ len i`, also `4 * lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, and from the germ
   threshold `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex. The determinant is
   nonzero at a corner, so the threshold is a positive upper bound on `rho` and is met by
   shrinking; `rho < lam` is one more shrinking.

Steps 1 and 3 are finite families of positive bounds, combined by
`Schoenflies.exists_pos_forall_of_finite`.

## What simplicity is used for

Two of the separations are *false* for a self-touching closed polygonal curve, and each is the
exact point where `ClosedPolygon.edges_meet` is consumed:

* `ClosedPolygon.vertex_notMem_edge` — a vertex lies on no edge but the two incident to it.
  This is what makes `{vertex i}` and `edge j` disjoint compact sets.
* `ClosedPolygon.trimmed_disjoint_edge` — the trimmed core of an edge misses every other edge.
  Here the two endpoints allowed by `edges_meet` are excluded by the trim itself, since a point
  of the core is at distance at least `lam` from both.

`edges_meet` as stated is one-sided (`edge i ∩ edge j ⊆ {vertex i, vertex (i + 1)}`), but it is
quantified over all ordered pairs, so the symmetric instance is available and both proofs below
use whichever side is convenient. It carries enough simplicity for both statements.

## Blueprint

* `Schoenflies.exists_stripData_subset` — the constants of Lemma 1.8 (Two-sided polygonal
  strips), chosen inside a prescribed open set containing the curve; this is the "Lemma 1.4 (a)
  lets all disks and strips be chosen inside the prescribed open set" of the last paragraph of
  the proof.
* `Schoenflies.exists_stripData` — the same without a prescribed open set.
* `Schoenflies.ClosedPolygon.exists_cone_radius`,
  `Schoenflies.ClosedPolygon.exists_half_width` — steps 1 and 3 of the recipe, which are the
  instances of Lemma 1.4 that Lemma 1.8 consumes.
* `Schoenflies.StripData.nbhd_subset_thickening` — the collar of Lemma 1.8 lies in the
  `R`-neighbourhood of the curve, which is how the prescribed open set is honoured.
-/

open Metric _root_.Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i j : ZMod (m + 3)} {c lam : ℝ}

/-! ### Compactness of the pieces -/

theorem isCompact_edge : IsCompact (P.edge i) := isCompact_segment _ _

theorem isCompact_carrier (P : ClosedPolygon m) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_edge

theorem continuous_pt (P : ClosedPolygon m) (i : ZMod (m + 3)) : Continuous (P.pt i) := by
  have h : P.pt i = fun c : ℝ => P.vertex i + c • P.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives

The two statements below are the only consumers of `ClosedPolygon.edges_meet` in the whole
choice of constants, and neither is true without it. -/

/-- **Simplicity, first form.** A vertex lies on no edge but the two edges incident to it.
Without this the "a vertex is `2R` away from every nonincident edge" hypothesis of `StripData`
would be unsatisfiable, since the vertex would sit *on* one of those edges. -/
theorem vertex_notMem_edge (hj1 : j ≠ i - 1) (hj2 : j ≠ i) : P.vertex i ∉ P.edge j := by
  intro hx
  -- Use `edges_meet` in the order that puts the *other* edge's endpoints on the right.
  have hmem : P.vertex i ∈ P.edge j ∩ P.edge i := ⟨hx, vertex_mem_edge⟩
  have hsub := P.edges_meet j i hj2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · exact hj2 (P.vertex_inj h).symm
  · exact hj1 (by rw [P.vertex_inj h]; ring)

/-- The trimmed core of edge `i`: the points of the edge at distance at least `lam` from both
of its endpoints. An edge block of `StripData` hugs this core. -/
def trimmed (P : ClosedPolygon m) (i : ZMod (m + 3)) (lam : ℝ) : Set Plane :=
  P.pt i '' Set.Icc lam (P.len i - lam)

theorem pt_mem_trimmed (hc : c ∈ Set.Icc lam (P.len i - lam)) : P.pt i c ∈ P.trimmed i lam :=
  ⟨c, hc, rfl⟩

theorem isCompact_trimmed : IsCompact (P.trimmed i lam) :=
  isCompact_Icc.image (P.continuous_pt i)

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge. The two
common points `edges_meet` allows are the endpoints of the edge, and the trim removes them: a
core point is at distance at least `lam` from either endpoint. No lower bound on the edge
length is needed: if the trim eats the whole edge the core is empty. -/
theorem trimmed_disjoint_edge (hlam : 0 < lam) (hij : j ≠ i) :
    Disjoint (P.trimmed i lam) (P.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ P.len i := le_trans hc.2 (by linarith)
  have hmem : P.pt i c ∈ P.edge i ∩ P.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := P.edges_meet i j (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · -- The core point is the initial vertex, so its progress is `0`, below the trim.
    have h0 : |c| = 0 := by rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, _root_.dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · -- The core point is the terminal vertex, so its progress is `len i`, above the trim.
    have h0 : |c| = P.len i := by
      rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, len, dist_eq_norm]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.2]

end ClosedPolygon

/-! ## Where the collar lives

The collar sits inside the `R`-neighbourhood of the curve: a sector is inside a ball of radius
`R` about a point of the curve, and a block is within `rho < R` of the foot of its
perpendicular, which is on the curve. This is the whole content of "the neighbourhoods may be
chosen inside any prescribed open set containing the curve". -/

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P)

/-- The collar of `Strip.lean` lies in the `R`-neighbourhood of the polygon. -/
theorem nbhd_subset_thickening : D.nbhd ⊆ thickening D.R P.carrier := by
  intro x hx
  have hx' : x ∈ D.sideL ∪ D.sideR ∪ P.carrier := hx
  rcases hx' with (hL | hR) | hc
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inl hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hR
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inr hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · exact self_subset_thickening D.R_pos _ hc

end StripData

/-! ## Choosing the constants -/

namespace ClosedPolygon

/-- **Step 1: the cone radius.** One positive `R` that is below every edge length, that
separates the vertices pairwise with a factor `2` to spare, that keeps every vertex `2R` away
from every nonincident edge, and whose neighbourhood of the curve stays inside the prescribed
open set. -/
theorem exists_cone_radius (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ R > 0, (∀ i, R ≤ P.len i) ∧
      (∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)) ∧
      (∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y) ∧
      thickening R P.carrier ⊆ U := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_univ (α := ZMod (m + 3))) (f := fun i => P.len i)
      (fun _ _ => len_pos)
  -- (2) the pairwise vertex separations: distinct vertices are distinct points
  have h₂ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.1 ≠ p.2 → ε ≤ dist (P.vertex p.1) (P.vertex p.2)) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (P.vertex i) (P.vertex j),
          dist_pos.2 fun h => hij (P.vertex_inj h), fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to: simplicity makes them disjoint
  have h₃ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 - 1 → p.2 ≠ p.1 → ∀ y ∈ P.edge p.2, ε ≤ dist (P.vertex p.1) y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ -
      by_cases hj1 : j = i - 1
      · exact ⟨1, one_pos, fun h => absurd hj1 h⟩
      by_cases hj2 : j = i
      · exact ⟨1, one_pos, fun _ h => absurd hj2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hj1 hj2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set
  obtain ⟨e₄, he₄, hthick⟩ := Plane.exists_thickening_subset (isCompact_carrier P) hU hPU
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) he₄), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i (Set.mem_univ i))
  · intro i j hij
    have h := hvv (i, j) (Set.mem_univ _) hij
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · intro i j hj1 hj2 y hy
    have h := hve (i, j) (Set.mem_univ _) hj1 hj2 y hy
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans
      (thickening_mono (le_trans (min_le_right _ _) (min_le_right _ _)) _) hthick

/-- The germ threshold at a single vertex. The corner condition makes `det ≠ 0`, so the right
side is positive and the inequality is a genuine upper bound on the half-width. -/
theorem exists_germ_bound (P : ClosedPolygon m) (i : ZMod (m + 3)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ ε > 0, ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
      lam * |det (P.rayIn i) (P.tang i)| := by
  have hb : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 det_rays_ne_zero
  have ha : 0 < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
    have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
  refine ⟨lam * |det (P.rayIn i) (P.tang i)| / (1 + |inner ℝ (P.rayIn i) (P.tang i)|),
    div_pos (mul_pos hlam hb) ha, le_of_eq ?_⟩
  field_simp

/-- **Step 3: the half-width.** One positive `rho` below `lam`, separating each trimmed edge
from every other edge with a factor `2` to spare, and meeting the germ threshold at every
vertex. Only `0 < lam` is needed: if `lam` were so large that a trimmed edge came out empty,
its separation clause would be vacuous. -/
theorem exists_half_width (P : ClosedPolygon m) {lam : ℝ} (hlam : 0 < lam) :
    ∃ rho > 0, rho < lam ∧
      (∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
        2 * rho ≤ dist (P.pt i c) y) ∧
      (∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
        lam * |det (P.rayIn i) (P.tang i)|) := by
  -- (1) each trimmed edge against every other edge: two disjoint compact sets
  have h₁ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 → ∀ x ∈ P.trimmed p.1 lam, ∀ y ∈ P.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ -
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every vertex
  have h₂ : ∃ ε > 0, ∀ i : ZMod (m + 3), i ∈ (Set.univ : Set _) →
      ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)| := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
        have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
      nlinarith
    · intro i _
      exact P.exists_germ_bound i hlam
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  refine ⟨min (min (ε₁ / 2) ε₂) (lam / 2),
    lt_min (lt_min (by linarith) hε₂) (by linarith), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro i j hij c hc y hy
    have h := htrim (i, j) (Set.mem_univ _) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i
    have h := hgerm i (Set.mem_univ _)
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
      have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith

end ClosedPolygon

/-- **Lemma 1.8, the constants.** Every simple closed polygon carries a `StripData`, and its
collar can be put inside any prescribed open set containing the curve. This is what makes
`Schoenflies/Strip.lean` with the required constants supplied. -/
theorem exists_stripData_subset (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) : ∃ D : StripData P, D.nbhd ⊆ U := by
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRU⟩ := P.exists_cone_radius hU hPU
  have hlam : (0 : ℝ) < R / 5 := by linarith
  have hlen4 : ∀ i, 4 * (R / 5) < P.len i := fun i => by have := hRlen i; linarith
  obtain ⟨rho, hrho, hrl, htrim, hgerm⟩ := P.exists_half_width hlam
  refine ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, hlen4, hRlen, hRvv, hRve, htrim, hgerm⟩, ?_⟩
  exact subset_trans (StripData.nbhd_subset_thickening _) hRU

/-- Every simple closed polygon carries a `StripData`. -/
theorem exists_stripData (P : ClosedPolygon m) : Nonempty (StripData P) :=
  ⟨(exists_stripData_subset P isOpen_univ (subset_univ _)).choose⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/StripConnected.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The collar of a closed polygon is two-sided

`Schoenflies/Strip.lean` builds the blocks of Lemma 1.8 and proves the hard local half of the
statement: the two labelled sides are disjoint. This module closes the lemma for a *closed*
polygon by supplying the two remaining global facts.

* **Each side is connected.** The blueprint says "consecutive edge and vertex blocks overlap in
  a nonempty labelled half-strip, so the union of all left pieces is connected". Here that
  overlap is produced explicitly: `StripData.mem_overlapL_start` puts the point at frame
  position `(3 lam / 2, rho / 2)` in both `blockL i` and `sectorL i`, and
  `StripData.mem_overlapL_finish` puts the point at `(len i - 3 lam / 2, rho / 2)` in both
  `blockL i` and `sectorL (i + 1)`. The two `StripData` constraints that make these work are
  exactly the two the structure advertises for the purpose: `four_lam_lt_len` keeps the frame
  position inside the block, and `two_lam_lt_R` keeps it inside the sector, since
  `3 lam / 2 + rho / 2 < 2 lam < R`.

  The chaining is then a finite induction along `chainL`, and it does **not** need the
  wrap-around: connectedness of a union of connected sets only needs *some* spanning tree of
  the overlap graph, and the linear chain `0, 1, …, m + 2` is one. The blueprint's "the labels
  return consistently after one circuit" is a statement about the *labelling*, not about
  connectedness, and it is `Strip.sideL_disjoint_sideR`, already proved: it is what makes
  `sideL` and `sideR` two sets rather than one.

* **The collar is a neighbourhood, and removing the curve leaves exactly the two sides.**
  `StripData.nbhd_diff_carrier` is immediate from the two disjointness results of `Strip.lean`.
  Openness of `nbhd` is not: `nbhd` contains the curve, so it has to be recognised as a union
  of open sets. `StripData.nbhd_eq` does that, rewriting it as the union of the vertex balls
  and the full edge tubes; the two inclusions are `ball_diff_carrier_subset` and
  `tube_diff_carrier_subset` one way, and the covering of each edge by "near the first vertex,
  near the second vertex, or in the trimmed middle" the other way.

## Blueprint

* `Schoenflies.StripData.isConnected_sideL`, `.isConnected_sideR` — "the union of all left
  pieces is connected; the same is true on the right", inside Lemma 1.8 (a).
* `Schoenflies.StripData.nbhd_diff_carrier` — `N \ P = N_L ⊔ N_R`, Lemma 1.8 (a).
* `Schoenflies.StripData.collar` — Lemma 1.8 (a) for a closed polygon, given the constants.

Producing the constants is `exists_stripData`, which lives elsewhere; every statement here is
for a given `D : StripData P`, exactly as in `Schoenflies/Strip.lean`.
-/

open Metric _root_.Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {c t s : ℝ}

/-! ### Two frames at one edge

Everything below needs the edge frame read from *both* ends: `Strip.lean` has the departure
end, and the overlap with the sector at the far vertex needs the arrival end. -/

/-- The incoming ray at a vertex is a unit vector. -/
theorem isDirection_rayIn : IsDirection (P.rayIn i) := isDirection_dir vertex_pred_ne

/-- The far vertex of edge `i` sits at frame position `(len i, 0)`. -/
theorem off_sub_vertex_succ :
    P.off i t s - P.vertex (i + 1) = (t - P.len i) • P.tang i + s • perp (P.tang i) := by
  have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
    rw [len_smul_tang]; module
  rw [off, hv]; module

/-- The block-to-far-sector distance bound, the mirror of `dist_off_vertex_le`. -/
theorem dist_off_vertex_succ_le : dist (P.off i t s) (P.vertex (i + 1)) ≤ |t - P.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - P.len i) • P.tang i + s • perp (P.tang i)‖
      ≤ ‖(t - P.len i) • P.tang i‖ + ‖s • perp (P.tang i)‖ := norm_add_le _ _
    _ = |t - P.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

/-- The distance from a point of edge `i` to the edge's far endpoint, the mirror of
`dist_pt_vertex`. -/
theorem dist_pt_vertex_succ : dist (P.pt i c) (P.vertex (i + 1)) = |c - P.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

/-! ### The two incident edges, as rays out of a vertex

`mem_edge_sub` and `mem_edge_pred_sub` read a point of an incident edge as a multiple of a ray.
The converses are what says that a ball about a vertex minus the curve is covered by the two
sectors: a direction on one of the two rays is *on the curve*, not beside it. -/

/-- Walking back along the incoming ray from vertex `i` traverses the previous edge. -/
theorem vertex_add_smul_rayIn (P : ClosedPolygon m) (i : ZMod (m + 3)) (c : ℝ) :
    P.vertex i + c • P.rayIn i = P.pt (i - 1) (P.len (i - 1) - c) := by
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have h := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at h
  have hlen : P.vertex i = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang, hsucc]; module
  rw [pt_eq, hr, hlen]
  module

/-- A point of the incoming ray at distance at most the previous edge's length lies on that
edge. -/
theorem mem_edge_pred_of_smul_rayIn (hc0 : 0 ≤ c) (hc1 : c ≤ P.len (i - 1)) :
    P.vertex i + c • P.rayIn i ∈ P.edge (i - 1) := by
  rw [vertex_add_smul_rayIn]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

/-- A point of the outgoing ray at distance at most the edge's length lies on that edge. -/
theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ P.len i) :
    P.vertex i + c • P.tang i ∈ P.edge i := by
  rw [← pt_eq]
  exact pt_mem_edge ⟨hc0, hc1⟩

end ClosedPolygon

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
vertex in question. The two hypotheses of `StripData` that were put there for this are
`four_lam_lt_len` — which gives `3 lam / 2 < len i - lam`, so the point is inside the block —
and `two_lam_lt_R` together with `rho < lam` — which gives
`3 lam / 2 + rho / 2 < 2 lam < R`, so the point is inside the sector. -/

/-- The along-coordinate of the witnesses clears the near trim. -/
theorem lam_lt_three_halves_lam : D.lam < 3 * D.lam / 2 := by have := D.lam_pos; linarith

/-- …and stays short of the far one, by `four_lam_lt_len`. -/
theorem three_halves_lam_lt : 3 * D.lam / 2 < P.len i - D.lam := by
  have := D.lam_pos
  have := D.four_lam_lt_len i
  linarith

/-- …and the whole witness stays inside the sector, by `rho_lt_lam` and `two_lam_lt_R`. -/
theorem overlap_dist_lt : 3 * D.lam / 2 + D.rho / 2 < D.R := by
  have := D.rho_lt_lam
  have := D.two_lam_lt_R
  linarith

/-- **The overlap at the departure vertex.** The point at frame position `(3 lam / 2, rho / 2)`
of edge `i` lies both in the left block of that edge and in the left sector at `i`. -/
theorem mem_overlapL_start :
    P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL i := by
  have hmem : P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_start hmem, ?_⟩
  -- The sector reaches this far because `3 lam / 2 + rho / 2 < 2 lam < R`.
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- **The overlap at the arrival vertex.** The point at frame position
`(len i - 3 lam / 2, rho / 2)` of edge `i` lies both in the left block of that edge and in the
left sector at `i + 1`. -/
theorem mem_overlapL_finish :
    P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_start`. -/
theorem mem_overlapR_start :
    P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR i := by
  have hmem : P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_start hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_finish`. -/
theorem mem_overlapR_finish :
    P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

theorem blockL_nonempty : (D.blockL i).Nonempty := ⟨_, D.mem_overlapL_start.1⟩
theorem blockR_nonempty : (D.blockR i).Nonempty := ⟨_, D.mem_overlapR_start.1⟩

theorem isConnected_blockL : IsConnected (D.blockL i) :=
  D.convex_blockL.isConnected D.blockL_nonempty

theorem isConnected_blockR : IsConnected (D.blockR i) :=
  D.convex_blockR.isConnected D.blockR_nonempty

end StripData

/-! ## Chaining a cyclic family

The union of the left pieces is connected because consecutive pieces overlap. This is a fact
about any cyclically indexed family, and it is worth isolating: it is used once on the left and
once on the right, and it is where the "cyclic" of the blueprint gets examined.

The point to notice is that the closing overlap `F (last) ∩ F 0` is **not used**. A union of
connected sets is connected as soon as the overlap graph is connected, and the path
`0 — 1 — ⋯ — N-1` already spans it; the extra edge back to `0` is a cycle, not a new vertex.
The blueprint's "the labels return consistently after one circuit" is therefore not needed
*here*: it is needed to know that the left label and the right label never collide, which is
`StripData.sideL_disjoint_sideR`, and that is already proved. -/

/-- A cyclically indexed family of connected sets in which every member meets its successor has
connected union. Only the overlaps along the linear chain `0, 1, …, N - 1` are consumed. -/
theorem isConnected_iUnion_zmod {α : Type*} [TopologicalSpace α] {N : ℕ} [NeZero N]
    (F : ZMod N → Set α) (hconn : ∀ i, IsConnected (F i))
    (hmeet : ∀ i, (F i ∩ F (i + 1)).Nonempty) : IsConnected (⋃ i, F i) := by
  -- `chain k` is the union of the pieces with index the cast of some `j ≤ k`.
  set chain : ℕ → Set α := fun k => ⋃ j : ℕ, ⋃ _ : j ≤ k, F (j : ZMod N) with hchain
  have hstep : ∀ k : ℕ, chain (k + 1) = chain k ∪ F ((k + 1 : ℕ) : ZMod N) := by
    intro k
    ext y
    simp only [hchain, Set.mem_iUnion, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨j, hj, hy⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact Or.inl ⟨j, Nat.lt_succ_iff.1 h, hy⟩
      · exact Or.inr ((le_antisymm hj h) ▸ hy)
    · rintro (⟨j, hj, hy⟩ | hy)
      · exact ⟨j, le_trans hj (Nat.le_succ k), hy⟩
      · exact ⟨k + 1, le_refl _, hy⟩
  have hzero : chain 0 = F 0 := by
    ext y
    simp only [hchain, Set.mem_iUnion, Nat.le_zero, exists_prop]
    constructor
    · rintro ⟨j, rfl, hy⟩; simpa using hy
    · intro hy; exact ⟨0, rfl, by simpa using hy⟩
  have key : ∀ k : ℕ, IsConnected (chain k) := by
    intro k
    induction k with
    | zero => rw [hzero]; exact hconn 0
    | succ k ih =>
        rw [hstep k]
        refine IsConnected.union ?_ ih (hconn _)
        -- The overlap of the last two links, transported along `((k+1 : ℕ) : ZMod N) = k + 1`.
        obtain ⟨y, hy1, hy2⟩ := hmeet ((k : ℕ) : ZMod N)
        refine ⟨y, ?_, ?_⟩
        · exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_refl k, hy1⟩⟩
        · rwa [show ((k + 1 : ℕ) : ZMod N) = ((k : ℕ) : ZMod N) + 1 by push_cast; ring]
  have hcover : (⋃ i, F i) = chain (N - 1) := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion_subset fun i y hy => ?_
      have hval : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_rightInverse i
      have hlt : i.val < N := ZMod.val_lt i
      refine Set.mem_iUnion.2 ⟨i.val, Set.mem_iUnion.2 ⟨by omega, ?_⟩⟩
      rw [hval]
      exact hy
    · refine Set.iUnion_subset fun j => Set.iUnion_subset fun _ => Set.subset_iUnion _ _
  rw [hcover]
  exact key _

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The two sides are connected -/

/-- The left piece at index `i`: the left sector at vertex `i` glued to the left block of the
edge leaving `i`. -/
def pieceL (i : ZMod (m + 3)) : Set Plane := D.sectorL i ∪ D.blockL i

/-- The right piece at index `i`. -/
def pieceR (i : ZMod (m + 3)) : Set Plane := D.sectorR i ∪ D.blockR i

theorem sideL_eq_iUnion : D.sideL = ⋃ i, D.pieceL i := rfl
theorem sideR_eq_iUnion : D.sideR = ⋃ i, D.pieceR i := rfl

/-- A piece is connected: its sector and its block overlap, at `mem_overlapL_start`. -/
theorem isConnected_pieceL : IsConnected (D.pieceL i) :=
  IsConnected.union ⟨_, D.mem_overlapL_start.2, D.mem_overlapL_start.1⟩ D.isConnected_sectorL
    D.isConnected_blockL

theorem isConnected_pieceR : IsConnected (D.pieceR i) :=
  IsConnected.union ⟨_, D.mem_overlapR_start.2, D.mem_overlapR_start.1⟩ D.isConnected_sectorR
    D.isConnected_blockR

/-- Consecutive pieces overlap: the block of edge `i` reaches into the sector at `i + 1`. -/
theorem pieceL_inter_succ_nonempty : (D.pieceL i ∩ D.pieceL (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapL_finish.1, Or.inl D.mem_overlapL_finish.2⟩

theorem pieceR_inter_succ_nonempty : (D.pieceR i ∩ D.pieceR (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapR_finish.1, Or.inl D.mem_overlapR_finish.2⟩

/-- **The left side of the collar is connected.** -/
theorem isConnected_sideL : IsConnected D.sideL := by
  rw [D.sideL_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceL)
    (fun i => D.pieceL_inter_succ_nonempty)

/-- **The right side of the collar is connected.** -/
theorem isConnected_sideR : IsConnected D.sideR := by
  rw [D.sideR_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceR)
    (fun i => D.pieceR_inter_succ_nonempty)

/-! ### The collar minus the curve is exactly the two sides

`nbhd` was *defined* as `sideL ∪ sideR ∪ carrier`, so this is only the two disjointness
statements of `Strip.lean` read backwards. -/

/-- **Lemma 1.8 (a), the set equality.** Removing the curve from the collar leaves exactly the
two labelled sides. With `sideL_disjoint_sideR` this is `N \ P = N_L ⊔ N_R`. -/
theorem nbhd_diff_carrier : D.nbhd \ P.carrier = D.sideL ∪ D.sideR := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyc
  · intro hy
    refine ⟨Or.inl hy, ?_⟩
    rcases hy with h | h
    · exact fun hc => Set.disjoint_left.1 D.sideL_disjoint_carrier h hc
    · exact fun hc => Set.disjoint_left.1 D.sideR_disjoint_carrier h hc

theorem carrier_subset_nbhd : P.carrier ⊆ D.nbhd := fun _ hy => Or.inr hy

/-! ### The collar is open

`nbhd` contains the curve, so openness is not formal: it has to be exhibited as a union of open
sets. The two families are the vertex balls and the *full* edge tubes — the block of half-width
`rho` on both sides of the trimmed edge, core included. Each of the two is covered by
`nbhd` because its points off the curve are labelled (`ball_diff_carrier_subset`,
`tube_diff_carrier_subset`); conversely they cover `nbhd`, the only nontrivial part being that
they cover the curve itself, which is the three-way split of an edge into "within `R` of the
first vertex", "within `R` of the second", and "in the trimmed middle". -/

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. It is the
union of the two blocks with the piece of the edge between them. -/
def tube (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) D.rho

theorem isOpen_tube : IsOpen (D.tube i) := isOpen_strip _ _ _ _ _ _

theorem mem_tube_off {t s : ℝ} : P.off i t s ∈ D.tube i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < D.rho := by
  rw [tube, mem_strip_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem blockL_subset_tube : D.blockL i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 hy
  exact ⟨h1, h2, by linarith [D.rho_pos], h4⟩

theorem blockR_subset_tube : D.blockR i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 hy
  exact ⟨h1, h2, h3, by linarith [D.rho_pos]⟩

/-- **A vertex ball minus the curve is covered by the two sectors at that vertex.** A point of
the ball off the curve points in some direction from the vertex; by `mem_ray_or_mem_arcCCW'`
that direction is either one of the two incident rays — and then the point is *on* the incident
edge, because `R_le_len` says the sector does not run past the far end — or on one of the two
arcs, and then the point is in the corresponding sector. -/
theorem ball_diff_carrier_subset :
    ball (P.vertex i) D.R \ P.carrier ⊆ D.sectorL i ∪ D.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - P.vertex i ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply hyc
    rw [h]
    exact ClosedPolygon.vertex_mem_carrier
  rcases mem_ray_or_mem_arcCCW' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i)) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i - 1`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_rayIn.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.rayIn i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_pred_of_smul_rayIn hc.le
      (le_trans hy.le (D.R_le_len (i - 1))))
  · -- Out along the outgoing edge: the point lies on edge `i`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_tang.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.tang i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_of_smul_tang hc.le
      (le_trans hy.le (D.R_le_len i)))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the curve is its two blocks.** The only points of a tube on the curve are
those on the core of its own edge. -/
theorem tube_diff_carrier_subset : D.tube i \ P.carrier ⊆ D.blockL i ∪ D.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with h | h | h
  · exact Or.inr (D.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · exfalso
    apply hyc
    have hy0 : y = P.pt i (coordAlong (P.vertex i) (P.tang i) y) := by
      rw [ClosedPolygon.pt, ← h]
      exact ClosedPolygon.off_coord P i y
    rw [hy0]
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.pt_mem_edge
      ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩)
  · exact Or.inl (D.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- Each edge is covered by the ball at its first vertex, the ball at its second, and its own
tube: `lam < R` leaves no gap in the middle. -/
theorem carrier_subset_balls_union_tubes :
    P.carrier ⊆ (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  rintro y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rw [ClosedPolygon.mem_edge_iff] at hi
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hi
  rcases lt_or_ge c D.R with h1 | h1
  · refine Or.inl (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (P.len i - D.R) c with h2 | h2
  · refine Or.inl (Set.mem_iUnion.2 ⟨i + 1, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [ClosedPolygon.pt]
    have hlam := D.lam_pos
    have hR := D.two_lam_lt_R
    exact D.mem_tube_off.2 ⟨by linarith, by linarith, by linarith [D.rho_pos], D.rho_pos⟩

/-- The collar is the union of the vertex balls and the edge tubes. This is the presentation
that makes it visibly open. -/
theorem nbhd_eq : D.nbhd = (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ((hy | hy) | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sector_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockL_subset_tube hi⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sectorR_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockR_subset_tube hi⟩)
    · exact D.carrier_subset_balls_union_tubes hy
  · rintro y (hy | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.ball_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.tube_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))

theorem isOpen_nbhd : IsOpen D.nbhd := by
  rw [D.nbhd_eq]
  exact (isOpen_iUnion fun _ => isOpen_ball).union (isOpen_iUnion fun _ => D.isOpen_tube)

/-! ### Lemma 1.8 (a) -/

end StripData

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/StripLocal.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The local two-sidedness assertion of Lemma 1.8

`Schoenflies/Strip.lean`, `Schoenflies/StripConstants.lean` and `Schoenflies/StripConnected.lean`
build the collar of a simple closed polygon and prove the *global* half of Lemma 1.8 (a): the
collar minus the curve is the disjoint union of two connected open sets. This module adds the
*local* half, the sentence of the blueprint that begins "In either case the two sets `N_L`, `N_R`
are the two local sides of the curve in the following precise sense".

Two statements come out of it, and they are the two the polygonal Jordan curve theorem consumes.

* `Schoenflies.StripData.local_two_sided` and its packaging
  `Schoenflies.StripData.exists_reference_points`: a small enough disk about a point of the
  *relative interior* of an edge meets the polygon exactly in that edge, and the rest of the disk
  is the two open half-disks, one in each side. This is what supplies the two reference points
  `z_L`, `z_R` of the parity argument, together with the fact that they are separated by a single
  crossing of the curve.
* `Schoenflies.StripData.carrier_subset_closure_sideL` and `…_sideR`: every point of the polygon
  is in the closure of both sides. With `StripData.sideL_disjoint_carrier` this says the polygon
  is contained in the boundary of each side, which is what turns "there are exactly two regions"
  into "both regions have boundary `C`".

## What is proved, and how

The disk argument along an edge is `StripData.core_ball_trichotomy`: both frame coordinates are
`1`-Lipschitz, so a ball of radius at most `min lam rho` about a point of the middle stretch of
an edge cannot leave the block range in the longitudinal coordinate nor the block width in the
transverse one; the sign of the transverse coordinate then reads off which of the three pieces —
left block, edge, right block — the point is in.

Approaching a point of the polygon from a given side is `StripData.exists_near_sides`. Away from
the vertices the block does it. Near a vertex the block is not available (it stops short by
`lam`), and the approach is through the *sector*, reached by shrinking the transverse offset with
the longitudinal one held fixed: the germ lemmas `ClosedPolygon.off_sub_mem_arcL_start` and
friends need only that the offset be small against the progress, so at a point at distance `t > 0`
from the vertex any offset below `t · |det| / (1 + |⟪·,·⟫|)` works. At the vertex itself neither
is available and the approach is instead by shrinking a point of the sector towards the vertex,
which stays in the sector because an arc of directions is a cone (`Plane.smul_mem_arcCCW`).

## Blueprint

* `Schoenflies.StripData.local_two_sided`, `Schoenflies.StripData.exists_reference_points` —
  Lemma 1.8, the local two-sidedness assertion, along the relative interior of an edge.
* `Schoenflies.StripData.carrier_subset_closure_sideL`, `…_sideR` — the consequence of it used
  for "both regions have boundary `C`".
* `Schoenflies.ClosedPolygon.exists_two_sided_collar` — Lemma 1.8 (a) with those two clauses
  added, in existential form.

The local two-sidedness assertion *at a vertex* is not proved here; see the module note at the
end.
-/

open Metric _root_.Set

namespace Schoenflies

namespace Plane

/-- The origin is on no arc: the arcs are open arcs of *directions*. -/
theorem zero_notMem_arcCCW (u w : Plane) : (0 : Plane) ∉ arcCCW u w := by
  have h := (notMem_arcCCW_smul u w (le_refl (0 : ℝ))).1
  rwa [zero_smul] at h

end Plane

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {t s : ℝ}

/-- Seen from the vertex it arrives at, a frame position of edge `i` is a germ at the incoming
ray there. This is the companion of `ClosedPolygon.off_sub_vertex`, which does the same at the
vertex the edge leaves. -/
theorem off_sub_vertex_succ_ray : P.off i t s - P.vertex (i + 1) =
    (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
  have hr : P.rayIn (i + 1) = -P.tang i := rayIn_succ
  have hp : perp (-P.tang i) = -perp (P.tang i) := by ext k; fin_cases k <;> simp [perp]
  rw [off_sub_vertex_succ, hr, hp]
  module

/-! ### The four germs, for an arbitrary frame position

`StripData.blockL_sub_mem_arcL_start` and its three companions apply `Plane.germs_split'` to a
point of a *block*, where the smallness of the offset comes from the `germ` field of the
`StripData`. The four lemmas here are the same projections with the smallness left as a
hypothesis, which is what an approach to a point of the curve needs: there the progress `t` is
fixed by the point being approached and only the offset shrinks. -/

theorem off_sub_mem_arcL_start (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  rw [off_sub_vertex]
  exact (germs_split' det_rays_ne_zero hs hsm).1.2

theorem off_sub_mem_arcR_start (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  have h : P.off i t s - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.2

theorem off_sub_mem_arcL_finish (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' det_rays_ne_zero hs hsm).1.1

theorem off_sub_mem_arcR_finish (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  have h : P.off i t s - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.1

/-- Offsetting a point of an edge moves it exactly the offset. -/
theorem dist_off_pt : dist (P.off i t s) (P.pt i t) = |s| := by
  rw [ClosedPolygon.pt, dist_eq_norm, show P.off i t s - P.off i t 0 = s • perp (P.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

end ClosedPolygon

/-- One positive number below several prescribed thresholds at once. Used to offset a point of an
edge by less than the germ threshold at both of its endpoints, less than the block half-width and
less than a prescribed accuracy. -/
private theorem exists_common_bound {a b X₁ X₂ K₁ K₂ Y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hY : 0 < Y) :
    ∃ σ : ℝ, 0 < σ ∧ σ < a ∧ σ < b ∧ σ * K₁ ≤ X₁ ∧ σ * K₂ ≤ X₂ ∧ σ < Y := by
  refine ⟨min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_min_iff, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨div_pos hX₁ hK₁, div_pos hX₂ hK₂⟩, by linarith⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₁ / K₁ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₁.le
    rwa [div_mul_cancel₀ _ hK₁.ne'] at h2
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₂ / K₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₂.le
    rwa [div_mul_cancel₀ _ hK₂.ne'] at h2
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i : ZMod (m + 3)}

/-! ### The disk about a point in the middle of an edge -/

/-- **The local picture along an edge.** A ball of radius at most `min lam rho` about a point of
the middle stretch of an edge is split by the sign of the transverse coordinate: positive is the
left block, negative the right block, zero the edge itself. Both coordinates are `1`-Lipschitz,
which is the whole proof. -/
theorem core_ball_trichotomy {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hη : η ≤ min D.lam D.rho) {y : Plane} (hy0 : y ∈ ball (P.pt i c) η) :
    (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.blockL i) ∧
      (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.blockR i) ∧
      (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
  have hy : dist y (P.pt i c) < min D.lam D.rho := lt_of_lt_of_le (mem_ball.1 hy0) hη
  set t := coordAlong (P.vertex i) (P.tang i) y with ht
  set σ := coordAcross (P.vertex i) (P.tang i) y with hσ
  have hyeq : y = P.off i t σ := ClosedPolygon.off_coord P i y
  have hpt : P.pt i c = P.off i c 0 := rfl
  have hta : |t - c| ≤ dist y (P.pt i c) := by
    have h := abs_coordAlong_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAlong_off] at h
    exact h
  have hsa : |σ| ≤ dist y (P.pt i c) := by
    have h := abs_coordAcross_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAcross_off, sub_zero] at h
    exact h
  have hlam : dist y (P.pt i c) < D.lam := lt_of_lt_of_le hy (min_le_left _ _)
  have hrho : dist y (P.pt i c) < D.rho := lt_of_lt_of_le hy (min_le_right _ _)
  have htlow : D.lam < t := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.1]
  have hthigh : t < P.len i - D.lam := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.2]
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · rw [hyeq]
    exact D.mem_blockL_off.2 ⟨htlow, hthigh, hs, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.2]⟩
  · rw [hyeq]
    exact D.mem_blockR_off.2 ⟨htlow, hthigh, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.1], hs⟩
  · rw [hyeq, hs, ← ClosedPolygon.pt]
    exact ClosedPolygon.pt_mem_edge ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩

/-- **Local two-sidedness at an interior point of an edge.** A small enough disk about a point in
the middle stretch of an edge meets the polygon exactly in that edge; off the edge the disk lies
in the two blocks, one on each side; and both sides are met, at the two points obtained by
offsetting the centre. -/
theorem local_two_sided {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hηpos : 0 < η) (hη : η ≤ min D.lam D.rho) :
    ball (P.pt i c) η ∩ P.carrier ⊆ P.edge i ∧
      (∀ y ∈ ball (P.pt i c) η, y ∉ P.carrier →
        (0 < coordAcross (P.vertex i) (P.tang i) y ∧ y ∈ D.sideL) ∨
          (coordAcross (P.vertex i) (P.tang i) y < 0 ∧ y ∈ D.sideR)) ∧
      P.off i c (η / 2) ∈ ball (P.pt i c) η ∩ D.sideL ∧
      P.off i c (-(η / 2)) ∈ ball (P.pt i c) η ∩ D.sideR := by
  have hsplit : ∀ y ∈ ball (P.pt i c) η,
      (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.sideL) ∧
        (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.sideR) ∧
        (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
    intro y hy
    obtain ⟨hL, hR, hE⟩ := D.core_ball_trichotomy h1 h2 hη hy
    exact ⟨fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hL hs)⟩,
      fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hR hs)⟩, hE⟩
  have hball : ∀ σ : ℝ, |σ| < η → P.off i c σ ∈ ball (P.pt i c) η := by
    intro σ hσ
    rw [mem_ball, ClosedPolygon.dist_off_pt]
    exact hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyc⟩
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideR_disjoint_carrier ((hsplit y hy).2.1 hs))
    · exact (hsplit y hy).2.2 hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideL_disjoint_carrier ((hsplit y hy).1 hs))
  · intro y hy hyc
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact Or.inr ⟨hs, (hsplit y hy).2.1 hs⟩
    · exact absurd (ClosedPolygon.edge_subset_carrier ((hsplit y hy).2.2 hs)) hyc
    · exact Or.inl ⟨hs, (hsplit y hy).1 hs⟩
  · have hmem := hball (η / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith
  · have hmem := hball (-(η / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).2.1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith

/-! ### Every point of the polygon is on the boundary of both sides -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex, which
stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorL i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorL (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

theorem exists_near_sectorR {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorR i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorR (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

/-- **Both sides come arbitrarily close to every point of the polygon.** Away from the vertices
this is the block; at a vertex it is `exists_near_sectorL`; in between it is the germ with the
progress held fixed and the offset shrunk below the corner's threshold. -/
theorem exists_near_sides {x : Plane} (hx : x ∈ P.carrier) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ D.sideL, dist x y < ε) ∧ (∃ y ∈ D.sideR, dist x y < ε) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := ClosedPolygon.mem_edge_iff.1 hi
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex
    rw [← hc0', ClosedPolygon.pt_zero]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε i
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε i
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex
    rw [hc1', ClosedPolygon.pt_len]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε (i + 1)
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε (i + 1)
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i + 1, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i + 1, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  -- an interior point of the edge: offset it, by less than every threshold at once
  have hL₁ : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hL₂ : 0 < |det (P.rayIn (i + 1)) (P.tang (i + 1))| :=
    abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hK₁ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by positivity
  have hK₂ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| := by positivity
  have hRlam : D.lam < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]
  obtain ⟨σ, hσpos, hσε, hσrho, hσ1, hσ2, hσR⟩ := exists_common_bound hε D.rho_pos
    (mul_pos hc0' hL₁) (mul_pos (show (0:ℝ) < P.len i - c by linarith) hL₂) hK₁ hK₂
    (show (0:ℝ) < D.R - D.lam by linarith)
  have hg1 : σ * |inner ℝ (P.rayIn i) (P.tang i)| < c * |det (P.rayIn i) (P.tang i)| := by
    nlinarith
  have hg2 : σ * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - c) * |det (P.rayIn (i + 1)) (P.tang (i + 1))| := by nlinarith
  have hdistL : dist (P.pt i c) (P.off i c σ) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_pos hσpos]; linarith
  have hdistR : dist (P.pt i c) (P.off i c (-σ)) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  by_cases hmid : D.lam < c ∧ c < P.len i - D.lam
  · -- the block does it
    exact ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩)⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩)⟩, hdistR⟩⟩
  push Not at hmid
  by_cases hnear : c ≤ D.lam
  · -- near the initial vertex: the sector there, reached by the germ
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex i) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_start hσpos hg1,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_start (by linarith) (by rw [neg_neg]; exact hg1),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩
  · -- near the terminal vertex
    push Not at hnear
    have hfar : P.len i - c ≤ D.lam := by have h := hmid hnear; linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex (i + 1)) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_succ_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < P.len i - c)] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_finish hσpos hg2,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_finish (by linarith) (by rw [neg_neg]; exact hg2),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩

/-- Every point of the polygon is in the closure of the left side. With
`StripData.sideL_disjoint_carrier` this says the polygon is contained in the boundary of the left
side. -/
theorem carrier_subset_closure_sideL : P.carrier ⊆ closure D.sideL := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨y, hy, hd⟩, -⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

theorem carrier_subset_closure_sideR : P.carrier ⊆ closure D.sideR := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨y, hy, hd⟩⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

end StripData

/-!
## What is still missing from Lemma 1.8

Two things.

* The local two-sidedness assertion *at a vertex*. `StripData.ball_diff_carrier_subset` already
  says that a ball of radius `R` about a vertex minus the polygon lies in the two sectors there,
  and `StripData.sectorL_disjoint_sectorR` (through `sideL_disjoint_sideR`) says those are
  disjoint; what is not proved is that each of the two intersections
  `ball (P.vertex i) η ∩ sectorL i` is *connected*, i.e. that the ball minus the curve has
  exactly two components at a vertex rather than merely being covered by two disjoint open sets.
  For a ball of radius `η ≤ R` this is true and the proof is the one in
  `Plane.isConnected_arcCCW_ball`, since `ball (P.vertex i) η ∩ sectorL i = cone (P.vertex i) A η`
  for the same arc `A`. Nothing in the polygonal Jordan curve theorem needs it.
* Lemma 1.8 (b), the case of a polygonal *arc* with a compact subarc of its interior. The blocks
  and sectors here are built from a cyclic vertex family; the arc case needs the same
  construction along a linear chain, with the two end cross-sections and no cap. None of it is
  formalised.
-/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/CrosscutCells.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

open Bornology _root_.Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

/-- The union of the bounded components of the complement — the blueprint's `Int(C)` once `C`
is known to be separating. -/
def inside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x)}

/-- The union of the unbounded components of the complement — the blueprint's `Ext(C)` once `C`
is known to be separating. -/
def outside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x)}

theorem inside_subset_compl : inside C ⊆ Cᶜ := fun _ hx => hx.1

theorem outside_subset_compl : outside C ⊆ Cᶜ := fun _ hx => hx.1

theorem inside_union_outside (C : Set Plane) : inside C ∪ outside C = Cᶜ := by
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Cᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩

theorem disjoint_inside_outside : Disjoint (inside C) (outside C) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb' hb

/-- Boundedness of the component is constant along a component, so the inside is a union of
whole components. -/
theorem connectedComponentIn_subset_inside (hx : x ∈ inside C) :
    connectedComponentIn Cᶜ x ⊆ inside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

theorem connectedComponentIn_subset_outside (hx : x ∈ outside C) :
    connectedComponentIn Cᶜ x ⊆ outside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/-- A union of components of an open set is open. -/
theorem isOpen_inside (hC : IsClosed C) : IsOpen (inside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_inside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

theorem isOpen_outside (hC : IsClosed C) : IsOpen (outside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_outside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/-! ### Definition 2.4: a separating Jordan curve -/

/-- Definition 2.4. A Jordan curve is *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with boundary `C`.

Since `inside C` and `outside C` always partition the complement into the bounded-component
part and the unbounded-component part, "exactly two regions, one bounded and one unbounded"
says precisely that each part is a single region; and the boundedness of one and unboundedness
of the other are then consequences rather than hypotheses (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`). -/
structure IsSeparating (C : Set Plane) : Prop where
  /-- The set is a Jordan curve. -/
  isJordanCurve : IsJordanCurve C
  /-- The bounded part of the complement is a single region. -/
  isConnected_inside : IsConnected (inside C)
  /-- The unbounded part of the complement is a single region. -/
  isConnected_outside : IsConnected (outside C)
  /-- The inside has the curve as its boundary. -/
  frontier_inside : frontier (inside C) = C
  /-- The outside has the curve as its boundary. -/
  frontier_outside : frontier (outside C) = C

namespace IsSeparating

theorem isClosed (h : IsSeparating C) : IsClosed C := h.isJordanCurve.isClosed

theorem isOpen_inside (h : IsSeparating C) : IsOpen (Schoenflies.inside C) :=
  Schoenflies.isOpen_inside h.isClosed

theorem isOpen_outside (h : IsSeparating C) : IsOpen (Schoenflies.outside C) :=
  Schoenflies.isOpen_outside h.isClosed

/-- The inside really is one *region* of the complement, that is, a connected component of it:
it is a union of components which is itself connected. Together with its twin below this is
the "exactly two regions" clause of Definition 2.4. -/
theorem connectedComponentIn_eq_inside (h : IsSeparating C) (hx : x ∈ Schoenflies.inside C) :
    connectedComponentIn Cᶜ x = Schoenflies.inside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_inside hx)
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hx inside_subset_compl)

/-- The outside is a connected component of the complement. -/
theorem connectedComponentIn_eq_outside (h : IsSeparating C) (hx : x ∈ Schoenflies.outside C) :
    connectedComponentIn Cᶜ x = Schoenflies.outside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_outside hx)
    (h.isConnected_outside.isPreconnected.subset_connectedComponentIn hx outside_subset_compl)

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-- `Ω` is a region of the complement of `C`. -/
def IsRegionOf (C Ω : Set Plane) : Prop := Ω = inside C ∨ Ω = outside C

/-- `Ω` and `Ω'` are the two regions of the complement of `C`, in one order or the other. -/
def IsRegionPair (C Ω Ω' : Set Plane) : Prop :=
  (Ω = inside C ∧ Ω' = outside C) ∨ (Ω = outside C ∧ Ω' = inside C)

/-- Every component of the complement is one of the two regions: there are no others. This is
the last clause of "exactly two regions". -/
theorem IsSeparating.isRegionOf_connectedComponentIn (h : IsSeparating C) (hx : x ∉ C) :
    IsRegionOf C (connectedComponentIn Cᶜ x) := by
  have hx' : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hx
  rcases hx' with hx' | hx'
  · exact Or.inl (h.connectedComponentIn_eq_inside hx')
  · exact Or.inr (h.connectedComponentIn_eq_outside hx')

namespace IsRegionOf

theorem inside (C : Set Plane) : IsRegionOf C (Schoenflies.inside C) := Or.inl rfl

theorem outside (C : Set Plane) : IsRegionOf C (Schoenflies.outside C) := Or.inr rfl

theorem subset_compl (h : IsRegionOf C Ω) : Ω ⊆ Cᶜ := by
  rcases h with rfl | rfl
  · exact inside_subset_compl
  · exact outside_subset_compl

theorem isOpen (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsOpen Ω := by
  rcases h with rfl | rfl
  · exact hC.isOpen_inside
  · exact hC.isOpen_outside

theorem isConnected (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsConnected Ω := by
  rcases h with rfl | rfl
  · exact hC.isConnected_inside
  · exact hC.isConnected_outside

/-- A region is a connected component of the complement. -/
theorem connectedComponentIn_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) (hx : x ∈ Ω) :
    connectedComponentIn Cᶜ x = Ω := by
  rcases h with rfl | rfl
  · exact hC.connectedComponentIn_eq_inside hx
  · exact hC.connectedComponentIn_eq_outside hx

theorem frontier_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : frontier Ω = C := by
  rcases h with rfl | rfl
  · exact hC.frontier_inside
  · exact hC.frontier_outside

/-- Every point of the curve is a limit of points of the region: this is the half of
`frontier Ω = C` that absorption uses. -/
theorem subset_closure (h : IsRegionOf C Ω) (hC : IsSeparating C) : C ⊆ closure Ω := by
  rw [← h.frontier_eq hC]
  exact frontier_subset_closure

/-- The closure of a region is the region together with the curve. -/
theorem closure_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : closure Ω = Ω ∪ C := by
  have hfr := h.frontier_eq hC
  rw [(h.isOpen hC).frontier_eq] at hfr
  rw [← hfr, Set.union_sdiff_cancel _root_.subset_closure]

end IsRegionOf

namespace IsRegionPair

theorem left (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem right (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem symm (h : IsRegionPair C Ω Ω') : IsRegionPair C Ω' Ω := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem union_eq (h : IsRegionPair C Ω Ω') : Ω ∪ Ω' = Cᶜ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inside_union_outside C
  · rw [Set.union_comm]
    exact inside_union_outside C

theorem disjoint (h : IsRegionPair C Ω Ω') : Disjoint Ω Ω' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_inside_outside
  · exact disjoint_inside_outside.symm

/-- A connected set off the curve and off one region lies in the other. This is the only place
where "exactly two regions" is used, and it is used in exactly that form. -/
theorem subset_left_of_isPreconnected (h : IsRegionPair C Ω Ω') (hC : IsSeparating C)
    {S : Set Plane} (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : S ⊆ Cᶜ)
    (hSΩ' : Disjoint S Ω') : S ⊆ Ω := by
  obtain ⟨z, hz⟩ := hne
  have hcover : S ⊆ Ω ∪ Ω' := by rw [h.union_eq]; exact hSC
  have hzΩ : z ∈ Ω := (hcover hz).resolve_right fun hz' => Set.disjoint_left.1 hSΩ' hz hz'
  exact hS.subset_left_of_subset_union (h.left.isOpen hC) (h.right.isOpen hC) h.disjoint hcover
    ⟨z, hz, hzΩ⟩

end IsRegionPair

/-- A nonempty connected set disjoint from the curve lies in one of the two regions. This is
the well-definedness clause of Lemma 2.6: "being connected it lies in one region of
`ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined". -/
theorem IsSeparating.exists_isRegionPair_subset (hC : IsSeparating C) {S : Set Plane}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : Disjoint S C) :
    ∃ W V, IsRegionPair C W V ∧ S ⊆ W := by
  obtain ⟨z, hz⟩ := hne
  have hSc : S ⊆ Cᶜ := fun w hw => Set.disjoint_left.1 hSC hw
  have hcover : S ⊆ inside C ∪ outside C := by rw [inside_union_outside]; exact hSc
  by_cases hzin : z ∈ inside C
  · exact ⟨inside C, outside C, Or.inl ⟨rfl, rfl⟩,
      hS.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
        hcover ⟨z, hz, hzin⟩⟩
  · refine ⟨outside C, inside C, Or.inr ⟨rfl, rfl⟩, ?_⟩
    refine hS.subset_left_of_subset_union hC.isOpen_outside hC.isOpen_inside
      disjoint_inside_outside.symm ?_ ⟨z, hz, (hcover hz).resolve_left hzin⟩
    rw [Set.union_comm]
    exact hcover

/-! ### Lemma 2.5: absorption -/

/-- Lemma 2.5 (absorption), set-theoretic core. If every point of `C` is a limit of points of
`Ω`, and `Ω` sits inside an open `V` whose frontier lies in `J`, then `C` misses `V` only where
`J` does. -/
theorem absorption_of_subset_closure (hCΩ : C ⊆ closure Ω) (hV : IsOpen V)
    (hfr : frontier V ⊆ J) (hsub : Ω ⊆ V) : C \ J ⊆ V := by
  rintro z ⟨hzC, hzJ⟩
  by_contra hzV
  -- `z` lies in the closure of `V` but not in `V`, so it lies on the frontier, hence in `J`.
  exact hzJ (hfr (by rw [hV.frontier_eq]; exact ⟨closure_mono hsub (hCΩ hzC), hzV⟩))

/-- Lemma 2.5 (absorption). If a region `Ω` of the complement of a separating curve `C` is
contained in a region `V` of the complement of a separating curve `J`, then all of `C` off `J`
lies in `V`. -/
theorem IsSeparating.absorption (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionOf C Ω) (hV : IsRegionOf J V) (hsub : Ω ⊆ V) : C \ J ⊆ V :=
  absorption_of_subset_closure (hΩ.subset_closure hC) (hV.isOpen hJ)
    (hV.frontier_eq hJ).subset hsub

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-- The far region `Ω'` absorbs all of `C` off `J`, so the near cell `V` misses `C` entirely:
the part of `C` off `J` is in `W`, and the part on `J` is off `V` because `V` misses `J`. -/
theorem disjoint_cell_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : Disjoint V C := by
  have hCW : C \ J ⊆ W := hC.absorption hJ hΩ' hWV.left hΩW
  rw [Set.disjoint_left]
  intro z hzV hzC
  by_cases hzJ : z ∈ J
  · exact hWV.right.subset_compl hzV hzJ
  · exact Set.disjoint_left.1 hWV.symm.disjoint hzV (hCW ⟨hzC, hzJ⟩)

/-- Lemma 2.6, first half of (a): the cell `V` is contained in `Ω ∖ P`. It misses `C`, it is
connected, and it misses `Ω'` because `Ω' ⊆ W`; so it lies in `Ω`. It misses `P` because it
misses `J ⊇ P`. -/
theorem cell_subset_region_diff (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) : V ⊆ Ω \ P := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ.right hWV hΩW
  have hVJ : V ⊆ Jᶜ := hWV.right.subset_compl
  -- `V` and `W` are the two regions of `ℝ² ∖ J`, and `Ω'` sits inside `W`.
  have hVΩ' : Disjoint V Ω' := hWV.symm.disjoint.mono_right hΩW
  have hVΩ : V ⊆ Ω :=
    hΩ.subset_left_of_isPreconnected hC (hWV.right.isConnected hJ).isPreconnected
      (hWV.right.isConnected hJ).nonempty (fun z hz => Set.disjoint_left.1 hVC hz) hVΩ'
  exact fun z hz => ⟨hVΩ hz, fun hzP => hVJ hz (hPJ hzP)⟩

/-- Lemma 2.6 (a): the cell `V` is a connected component of `Ω ∖ P`. Its frontier is `J`, which
lies in `C ∪ P` and so misses the open set `Ω ∖ P`; Lemma 1.7 does the rest. -/
theorem cell_isComponent (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) (hJCP : J ⊆ C ∪ P) :
    ∀ z ∈ V, connectedComponentIn (Ω \ P) z = V := by
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected
    (cell_subset_region_diff hC hJ hΩ hWV hΩW hPJ) ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hwΩ, hwP⟩
  rcases hJCP hwJ with hwC | hwP'
  · exact hΩ.left.subset_compl hwΩ hwC
  · exact hwP hwP'

/-- Lemma 2.6 (c): the closure of the cell meets `C` exactly in `J ∩ C`. The closure is
`V ∪ J`, and `V` misses `C`. -/
theorem closure_cell_inter_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : closure V ∩ C = J ∩ C := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ' hWV hΩW
  rw [hWV.right.closure_eq hJ, Set.union_inter_distrib_right, hVC.inter_eq, Set.empty_union]

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-- The two curves of Lemma 2.6 are Jordan curves: an arc from `p` to `q` and a second arc from
`p` to `q` meeting it only at those two points glue to a Jordan curve. -/
theorem isJordanCurve_union (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hmeet : ∀ z ∈ A, z ∈ P → z = p ∨ z = q) : IsJordanCurve (A ∪ P) :=
  IsJordanCurve.of_two_arcs hA hP.reverse hmeet

/-- Lemma 2.6 (b), arc side: the two arcs of `C` from `p` to `q` are distinct, because they
meet only at `p` and `q` while neither is just `{p, q}`. -/
theorem arcs_ne (hmeet : A₁ ∩ A₂ ⊆ {p, q}) (hA : ¬ A₁ ⊆ {p, q}) : A₁ ≠ A₂ := by
  rintro rfl
  exact hA fun z hz => hmeet ⟨hz, hz⟩

/-! ### Lemma 2.6, bundled -/

/-- **Lemma 2.6 (crosscut cells).** Let `C` be a separating curve with regions `Ω` and `Ω'`,
let `A₁, A₂ ⊆ C` be the two arcs cut out by a crosscut `P` which meets `C` only in points of
both arcs, and suppose the two curves `Jᵢ = Aᵢ ∪ P` are separating. Let `Wᵢ` be the region of
`ℝ² ∖ Jᵢ` containing `Ω'` and `Vᵢ` the other one. Then

* (a) each `Vᵢ` is a connected component of `Ω ∖ P`;
* (b) `V₁ ≠ V₂`;
* (c) `closure Vᵢ ∩ C = Aᵢ`.

The blueprint proves (b) from the boundaries; here it falls straight out of (c), since
`V₁ = V₂` would make `A₁ = A₂`. -/
theorem crosscut_cells (hC : IsSeparating C)
    (hJ₁ : IsSeparating (A₁ ∪ P)) (hJ₂ : IsSeparating (A₂ ∪ P))
    (hA₁ : A₁ ⊆ C) (hA₂ : A₂ ⊆ C) (hP₁ : P ∩ C ⊆ A₁) (hP₂ : P ∩ C ⊆ A₂) (hne : A₁ ≠ A₂)
    (hΩ : IsRegionPair C Ω Ω')
    {W₁ V₁ W₂ V₂ : Set Plane}
    (hWV₁ : IsRegionPair (A₁ ∪ P) W₁ V₁) (hΩW₁ : Ω' ⊆ W₁)
    (hWV₂ : IsRegionPair (A₂ ∪ P) W₂ V₂) (hΩW₂ : Ω' ⊆ W₂) :
    (V₁ ⊆ Ω \ P ∧ ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (V₂ ⊆ Ω \ P ∧ ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      V₁ ≠ V₂ ∧ closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  -- The two inclusions that replace the arc hypotheses.
  have hPJ : ∀ A : Set Plane, P ⊆ A ∪ P := fun A => Set.subset_union_right
  have hJCP : ∀ {A : Set Plane}, A ⊆ C → A ∪ P ⊆ C ∪ P := fun hA =>
    Set.union_subset_union_left P hA
  -- (c): `(Aᵢ ∪ P) ∩ C = Aᵢ`, since `Aᵢ ⊆ C` and `P ∩ C ⊆ Aᵢ`.
  have hinter : ∀ {A : Set Plane}, A ⊆ C → P ∩ C ⊆ A → (A ∪ P) ∩ C = A := by
    intro A hAC hPC
    refine Set.Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hAC hz⟩
    rintro z ⟨hz | hz, hzC⟩
    · exact hz
    · exact hPC ⟨hz, hzC⟩
  have hc₁ : closure V₁ ∩ C = A₁ := by
    rw [closure_cell_inter_curve hC hJ₁ hΩ.right hWV₁ hΩW₁]; exact hinter hA₁ hP₁
  have hc₂ : closure V₂ ∩ C = A₂ := by
    rw [closure_cell_inter_curve hC hJ₂ hΩ.right hWV₂ hΩW₂]; exact hinter hA₂ hP₂
  refine ⟨⟨cell_subset_region_diff hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁),
      cell_isComponent hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁) (hJCP hA₁)⟩,
    ⟨cell_subset_region_diff hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂),
      cell_isComponent hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂) (hJCP hA₂)⟩, ?_, hc₁, hc₂⟩
  -- (b): equal cells would have equal closures, hence equal arcs.
  rintro rfl
  exact hne (hc₁.symm.trans hc₂)

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolygonalJordan.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The polygonal Jordan curve theorem

Theorem 2.3: the complement of a simple closed polygon has exactly two regions, one bounded and
one unbounded, and each has the polygon as its frontier. Moreover the crossing parity of §2 is
`1` on the bounded region and `0` on the unbounded one.

## The three inputs, and where each is spent

* **Lemma 1.8, the collar** (`Schoenflies.StripData`, `StripData.local_two_sided`,
  `StripData.carrier_subset_closure_sideL`). It supplies the two *tracks* `N_L`, `N_R`: connected,
  disjoint, off the curve, together filling `N ∖ C`, and each with the whole curve in its closure.
* **Lemma 1.3, the nearest-point segment** (`Plane.notMem_of_mem_segment_of_isMinOn`). It gets an
  arbitrary point of the complement onto a track: walk from it to a nearest point of the curve;
  the walk misses the curve, and its final stretch is inside the collar.
* **Lemma 2.2, crossing parity** (`ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier`). It keeps the two tracks apart: they cannot be joined
  inside the complement, because a point just before and a point just after an edge differ in
  parity and parity is constant on a connected subset of the complement.

## Blueprint

* `Schoenflies.ClosedPolygon.exists_opposite_parity_sides`,
  `…parity_ne_of_mem_sides`, `…connectedComponentIn_ne_of_mem_sides` — the two tracks of the
  collar carry different parities, hence lie in different components. The "at least two" half.
* `Schoenflies.ClosedPolygon.exists_mem_sides_connectedComponentIn`,
  `…connectedComponentIn_eq_of_notMem` — every point of the complement lies in the component of a
  point of a track. The "at most two" half.
* `Schoenflies.ClosedPolygon.isSeparating_carrier` — **Theorem 2.3**, in the form Definition 2.4
  asks for: `IsSeparating P.carrier`. With it come `inside P.carrier` and `outside P.carrier` as
  the blueprint's `Int(C)` and `Ext(C)`, and the whole `IsSeparating` API of
  `Schoenflies/CrosscutCells.lean`.
* `Schoenflies.ClosedPolygon.connectedComponentIn_eq_inside_or_outside` — "exactly two regions",
  explicitly: the component of any point off the polygon is one of the two named regions.
* `Schoenflies.ClosedPolygon.parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_of_mem_outside` — the last sentence of Theorem 2.3, `π_C = 1` inside and
  `π_C = 0` outside, for **every** admissible ray direction, not just for one chosen at the start.
* `Schoenflies.ClosedPolygon.polygonal_jordan` — the same theorem with `IsSeparating` unfolded,
  for a reader who wants the statement without the definition.
* `Schoenflies.isSeparating_unitTriangle` — non-vacuity: the whole chain applies to the one
  polygon the development constructs.

## Two facts restated

`isBounded_closedSquare` and `not_isBounded_beyondSquare` below are stated `private`. They are
*not* new: they exist as `Graph.isBounded_closedSquare` and `Graph.not_isBounded_beyondSquare` in
`Schoenflies/Graph/OuterFace.lean`. Neither has any graph content — they are plane facts about
`Schoenflies.Plane.closedSquare` whose home is `Schoenflies/Bounded.lean` — and importing the
whole plane-graph layer into the polygonal Jordan curve theorem, which every later graph
argument depends on, would invert the layering. They are `private` so that the duplicate names
cannot collide when the integrator hoists the originals.
-/

open Bornology Metric _root_.Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ### Two plane facts about squares

See the module docstring: these belong in `Schoenflies/Bounded.lean` and are restated here only
to keep the graph layer out of the import graph of Theorem 2.3. -/

/-- A closed axis-parallel square is bounded. -/
private theorem isBounded_closedSquare (r : ℝ) : IsBounded (Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Plane.supNorm x ≤ r := by simpa [Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r :=
    le_trans (Plane.norm_le_sqrt_two_mul_supNorm x)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- The outside of a square is unbounded: it contains points of every size. -/
private theorem not_isBounded_beyondSquare (r : ℝ) : ¬ IsBounded (Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hb
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hmem : Plane.mk t 0 ∈ Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin : Plane.supDist (Plane.mk t 0) 0 ≤ s := hs hmem
  rw [Plane.supDist_zero] at hin
  have h1 : |t| ≤ Plane.supNorm (Plane.mk t 0) := by
    simp only [Plane.supNorm]; exact le_max_left _ _
  rw [abs_of_nonneg ht0] at h1
  linarith

/-! ### Small arithmetic and topology helpers -/

/-- In `ZMod 2` nothing is its own successor; this is what "the parities differ" comes down to. -/
private theorem zmod_two_ne_add_one (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- Two points joined by a preconnected subset of `F` have the same component of `F`. -/
private theorem comp_eq_of_isPreconnected {F S : Set Plane} (hS : IsPreconnected S) (hSF : S ⊆ F)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    connectedComponentIn F x = connectedComponentIn F y :=
  connectedComponentIn_eq (hS.subset_connectedComponentIn hx hSF hy)

/-- Distinct components are disjoint. -/
private theorem comp_disjoint {F : Set Plane} {x y : Plane}
    (h : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

namespace ClosedPolygon

variable {P : ClosedPolygon m}

theorem isClosed_carrier (P : ClosedPolygon m) : IsClosed P.carrier :=
  P.isCompact_carrier.isClosed

theorem carrier_nonempty (P : ClosedPolygon m) : P.carrier.Nonempty :=
  ⟨P.vertex 0, vertex_mem_carrier⟩

theorem sideL_subset_compl (D : StripData P) : D.sideL ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideL_disjoint_carrier hz

theorem sideR_subset_compl (D : StripData P) : D.sideR ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideR_disjoint_carrier hz

/-- **No edge is parallel to an admissible ray direction.** "No edge is horizontal" says exactly
that the two ends of an edge are at different heights, which is that the edge's tangent and the
ray direction span the plane. -/
theorem det_tang_ne_zero {u : Plane} (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    (i : ZMod (m + 3)) : det (P.tang i) u ≠ 0 := by
  have hne : hgt u (P.vertex i) ≠ hgt u (P.vertex (i + 1)) := hL _ (P.mem_pieces i)
  have hsub : det u (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
    rw [show det u (P.vertex (i + 1) - P.vertex i) = hgt u (P.vertex (i + 1) - P.vertex i) from rfl,
      hgt_sub, sub_ne_zero]
    exact Ne.symm hne
  rw [← len_smul_tang, det_smul_right] at hsub
  intro hz
  exact hsub (by rw [det_comm, hz, neg_zero, mul_zero])

/-! ### At least two regions: the two tracks are separated by one crossing

The blueprint: "Choose a sufficiently small disk `B` around an interior point of an edge, and
reference points `z_L ∈ B ∩ N_L`, `z_R ∈ B ∩ N_R` in its two components. The two reference points
have opposite parity."

The disk is the one of `StripData.local_two_sided`; the two reference points are the two points
just before and just after the midpoint of the edge *in the ray direction*, which is what makes
`parity_flip_carrier` applicable to them. That they land in the two different tracks is read off
the sign of their transverse coordinate `det (tang i) (· - vertex i)`, and the two signs are
opposite and nonzero because `det (tang i) u ≠ 0` — the edge is not parallel to the ray. -/

/-- **The two tracks of the collar carry different parities.** The witnesses are a point just
before and a point just after the midpoint of the edge `i` in the ray direction: they lie in the
two different tracks, and the crossing count changes by one between them. -/
theorem exists_opposite_parity_sides (P : ClosedPolygon m) (D : StripData P)
    (i : ZMod (m + 3)) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ zL ∈ D.sideL, ∃ zR ∈ D.sideR, parity u P.pieces zL ≠ parity u P.pieces zR := by
  have h4 := D.four_lam_lt_len i
  have hlam := D.lam_pos
  have hlen : 0 < P.len i := len_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < min D.lam D.rho := lt_min hlam D.rho_pos
  obtain ⟨-, hsides, -, -⟩ := D.local_two_sided (i := i) hlow hhigh hηpos le_rfl
  -- the midpoint of the edge is an interior point of it
  have hmid : P.vertex i + ((P.len i / 2) / P.len i) • (P.vertex (i + 1) - P.vertex i)
      = P.pt i (P.len i / 2) := by
    rw [← len_smul_tang, smul_smul, div_mul_cancel₀ _ hlen.ne', pt_eq]
  have hp : P.pt i (P.len i / 2) ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) := by
    rw [openSegment_eq_image' ℝ]
    exact ⟨(P.len i / 2) / P.len i,
      ⟨div_pos (by linarith) hlen, by rw [div_lt_one hlen]; linarith⟩, hmid⟩
  obtain ⟨δ, hδ, hflip⟩ := P.parity_flip_carrier hu hL i hp
  have ht0 : 0 < min (δ / 2) (min D.lam D.rho / 2) := lt_min (by linarith) (by linarith)
  have htδ : min (δ / 2) (min D.lam D.rho / 2) < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : min (δ / 2) (min D.lam D.rho / 2) < min D.lam D.rho :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set t : ℝ := min (δ / 2) (min D.lam D.rho / 2)
  obtain ⟨hbef, haft, hpar⟩ := hflip t ht0 htδ
  -- both test points lie in the disk of `local_two_sided`
  have hball : ∀ r : ℝ, |r| < min D.lam D.rho →
      P.pt i (P.len i / 2) + r • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    intro r hr
    rw [mem_ball, dist_eq_norm,
      show P.pt i (P.len i / 2) + r • u - P.pt i (P.len i / 2) = r • u by abel,
      norm_smul, Real.norm_eq_abs, hu.norm, mul_one]
    exact hr
  have hbaft := hball t (by rw [abs_of_pos ht0]; exact htη)
  have hbbef : P.pt i (P.len i / 2) - t • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    have h := hball (-t) (by rw [abs_of_neg (by linarith), neg_neg]; exact htη)
    rwa [neg_smul, ← sub_eq_add_neg] at h
  -- the transverse coordinate of a point offset from the edge in the ray direction
  have hkey : ∀ r : ℝ, coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) + r • u)
      = r * det (P.tang i) u := by
    intro r
    rw [coordAcross, show P.pt i (P.len i / 2) + r • u - P.vertex i
        = (P.len i / 2) • P.tang i + r • u by rw [pt_eq]; module,
      det_add_right, det_smul_right, det_self, mul_zero, zero_add, det_smul_right]
  have hcaaft := hkey t
  have hcabef : coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) - t • u)
      = -(t * det (P.tang i) u) := by
    have h := hkey (-t)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hsaft := hsides _ hbaft haft
  have hsbef := hsides _ hbbef hbef
  rcases lt_or_gt_of_ne (det_tang_ne_zero hL i) with hneg | hpos
  · -- the ray points to the right of the edge: the earlier test point is on the left
    have hlt : t * det (P.tang i) u < 0 := mul_neg_of_pos_of_neg ht0 hneg
    refine ⟨P.pt i (P.len i / 2) - t • u, ?_, P.pt i (P.len i / 2) + t • u, ?_, ?_⟩
    · rcases hsbef with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcabef] at h; linarith
    · rcases hsaft with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcaaft] at h; linarith
      · exact h
    · rw [hpar]; exact Ne.symm (zmod_two_ne_add_one _)
  · have hgt0 : 0 < t * det (P.tang i) u := mul_pos ht0 hpos
    refine ⟨P.pt i (P.len i / 2) + t • u, ?_, P.pt i (P.len i / 2) - t • u, ?_, ?_⟩
    · rcases hsaft with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcaaft] at h; linarith
    · rcases hsbef with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcabef] at h; linarith
      · exact h
    · rw [hpar]; exact zmod_two_ne_add_one _

/-- The crossing parity is constant on the left track: it is connected and misses the polygon. -/
theorem parity_eq_of_mem_sideL (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideL) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideL.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideL_subset_compl D hz) hx hy

/-- The crossing parity is constant on the right track. -/
theorem parity_eq_of_mem_sideR (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideR) (hy : y ∈ D.sideR) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideR.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideR_subset_compl D hz) hx hy

/-- **The two tracks of the collar have opposite parity**, whichever points of them are chosen.
This is the "at least two regions" half of Theorem 2.3: no connected subset of the complement
meets both tracks, since parity is constant on such a subset. -/
theorem parity_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) : parity u P.pieces x ≠ parity u P.pieces y := by
  obtain ⟨zL, hzL, zR, hzR, hne⟩ := P.exists_opposite_parity_sides D 0 hu hL
  rw [P.parity_eq_of_mem_sideL D hu hL hx hzL, P.parity_eq_of_mem_sideR D hu hL hy hzR]
  exact hne

/-- The two tracks lie in different components of the complement. -/
theorem connectedComponentIn_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) :
    connectedComponentIn P.carrierᶜ x ≠ connectedComponentIn P.carrierᶜ y := by
  obtain ⟨u, hu, hL⟩ := P.exists_direction_pieces
  intro heq
  refine P.parity_ne_of_mem_sides D hu hL hx hy ?_
  have hxc : x ∈ connectedComponentIn P.carrierᶜ y := by
    rw [← heq]; exact mem_connectedComponentIn (sideL_subset_compl D hx)
  exact P.parity_eq_of_mem_connectedComponentIn_carrier hu hL (sideR_subset_compl D hy) hxc

/-! ### At most two regions: walk to the nearest point of the polygon

The blueprint: "Let `x ∉ C`, and choose a nearest point `a ∈ C`. By Lemma 1.3, `[x, a)` avoids
`C`. Its final portion lies in `N_L` or `N_R`, and that track is connected. Hence `x` lies in the
component of either `z_L` or `z_R`." -/

/-- **At most two regions.** Every point of the complement lies in the component of a point of one
of the two tracks: walk towards a nearest point of the polygon — Lemma 1.3 says the walk misses
the polygon — and stop just short of it, inside the collar. -/
theorem exists_mem_sides_connectedComponentIn (P : ClosedPolygon m) (D : StripData P) {x : Plane}
    (hx : x ∉ P.carrier) :
    ∃ y ∈ D.sideL ∪ D.sideR,
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ y := by
  -- a nearest point of the polygon, and the segment towards it
  obtain ⟨a, haC, hmin⟩ := P.isCompact_carrier.exists_isMinOn P.carrier_nonempty
    (continuous_const.dist continuous_id).continuousOn
  have hmin' : ∀ b ∈ P.carrier, dist x a ≤ dist x b := isMinOn_iff.1 hmin
  have hax : a ≠ x := fun h => hx (h ▸ haC)
  have hvne : a - x ≠ 0 := sub_ne_zero.2 hax
  have hvpos : 0 < ‖a - x‖ := norm_pos_iff.2 hvne
  have hcont : Continuous (fun θ : ℝ => x + θ • (a - x)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- Lemma 1.3: the half-open segment misses the polygon
  have hoff : ∀ θ : ℝ, θ ∈ Ico (0 : ℝ) 1 → x + θ • (a - x) ∉ P.carrier := by
    intro θ hθ
    refine Plane.notMem_of_mem_segment_of_isMinOn haC hx hmin' ?_ ?_
    · rw [segment_eq_image' ℝ x a]; exact ⟨θ, ⟨hθ.1, hθ.2.le⟩, rfl⟩
    · intro h
      have h0 : (θ - 1) • (a - x) = 0 := by linear_combination (norm := module) h
      rcases smul_eq_zero.1 h0 with h1 | h1
      · have := hθ.2; linarith
      · exact hvne h1
  have hSΩ : (fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1 ⊆ P.carrierᶜ := by
    rintro z ⟨θ, hθ, rfl⟩
    exact hoff θ hθ
  have hSpre : IsPreconnected ((fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1) :=
    isPreconnected_Ico.image _ hcont.continuousOn
  -- the collar is a neighbourhood of the nearest point, so the final stretch lies in it
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 D.isOpen_nbhd a (D.carrier_subset_nbhd haC)
  have hmpos : 0 < min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) := lt_min (by norm_num) (by positivity)
  have hmhalf : min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) ≤ 1 / 2 := min_le_left _ _
  have hθmem : (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hprod : ε / (2 * ‖a - x‖) * ‖a - x‖ = ε / 2 := by
    field_simp
  have hdist : dist (x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x)) a < ε := by
    rw [dist_eq_norm, show x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) - a
        = (-(min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)))) • (a - x) by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hmpos]
    calc min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) * ‖a - x‖
        ≤ ε / (2 * ‖a - x‖) * ‖a - x‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hvpos.le
      _ = ε / 2 := hprod
      _ < ε := by linarith
  set y : Plane := x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) with hy
  have hyLR : y ∈ D.sideL ∪ D.sideR := by
    rw [← D.nbhd_diff_carrier]
    exact ⟨hεball (mem_ball.2 hdist), hoff _ hθmem⟩
  exact ⟨y, hyLR, comp_eq_of_isPreconnected hSpre hSΩ ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩
    ⟨_, hθmem, hy.symm⟩⟩

/-- Every point of the complement lies in the component of one of two fixed reference points,
one on each track. This is `exists_mem_sides_connectedComponentIn` with the track collapsed to a
point, which is possible because each track is connected. -/
theorem connectedComponentIn_eq_of_notMem (P : ClosedPolygon m) (D : StripData P)
    {zL zR : Plane} (hzL : zL ∈ D.sideL) (hzR : zR ∈ D.sideR) {x : Plane} (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR := by
  obtain ⟨y, hy, hyx⟩ := P.exists_mem_sides_connectedComponentIn D hx
  rcases hy with hy | hy
  · exact Or.inl (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideL.isPreconnected
      (sideL_subset_compl D) hy hzL))
  · exact Or.inr (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideR.isPreconnected
      (sideR_subset_compl D) hy hzR))

end ClosedPolygon

/-! ### Packaging: from "exactly two components" to `IsSeparating`

`Schoenflies/CrosscutCells.lean` defines `inside C` and `outside C` as the union of the bounded
and of the unbounded components of `Cᶜ`, *without* any separation hypothesis, and Definition 2.4
is the assertion that each of the two is a single region with boundary `C`. So the last step of
Theorem 2.3 is to identify the two components found above with `inside C` and `outside C`, and
that identification needs no case analysis on which of them is which: the one that swallows the
outside of a containing square is the unbounded one by definition, and the other is caught inside
the square. -/

/-- With exactly two components and the outside of a square inside the second, the first is the
bounded part of the complement and the second the unbounded part. -/
private theorem inside_outside_of_two_components {C : Set Plane} {r : ℝ} {z₁ z₂ : Plane}
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    inside C = connectedComponentIn Cᶜ z₁ ∧ outside C = connectedComponentIn Cᶜ z₂ := by
  have hdisj := comp_disjoint hne
  -- the first component misses the outside of the square, hence sits inside it
  have h1sq : connectedComponentIn Cᶜ z₁ ⊆ Plane.closedSquare 0 r := by
    intro w hw
    by_contra hwq
    exact Set.disjoint_left.1 hdisj hw (hbey (by rw [Plane.beyondSquare_eq_compl]; exact hwq))
  have h1bdd : IsBounded (connectedComponentIn Cᶜ z₁) := (isBounded_closedSquare r).subset h1sq
  have h2unb : ¬ IsBounded (connectedComponentIn Cᶜ z₂) := fun hb =>
    not_isBounded_beyondSquare r (hb.subset hbey)
  constructor
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · rw [← h]; exact mem_connectedComponentIn hw.1
      · exact absurd (h ▸ hw.2) h2unb
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h1bdd
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · exact absurd (h ▸ h1bdd) hw.2
      · rw [← h]; exact mem_connectedComponentIn hw.1
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h2unb

/-- A component of the complement of a closed set has that set as its frontier as soon as the set
is in its closure: one inclusion is Appendix C item 5, the other is that the component misses the
set altogether. -/
private theorem frontier_connectedComponentIn_eq {C : Set Plane} (hC : IsClosed C) (z : Plane)
    (hcl : C ⊆ closure (connectedComponentIn Cᶜ z)) :
    frontier (connectedComponentIn Cᶜ z) = C := by
  refine Set.Subset.antisymm (Plane.frontier_connectedComponentIn_compl_subset hC z) fun w hw => ?_
  rw [(Plane.isOpen_connectedComponentIn hC.isOpen_compl).frontier_eq]
  exact ⟨hcl hw, fun hmem => connectedComponentIn_subset _ _ hmem hw⟩

/-- The packaging step: two distinct components exhausting the complement, each with the curve in
its closure, and the outside of a containing square inside the second, make the curve
separating. -/
private theorem isSeparating_of_two_components {C : Set Plane} (hJ : IsJordanCurve C)
    (hC : IsClosed C) {r : ℝ} {z₁ z₂ : Plane} (h₁ : z₁ ∉ C) (h₂ : z₂ ∉ C)
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hcl₁ : C ⊆ closure (connectedComponentIn Cᶜ z₁))
    (hcl₂ : C ⊆ closure (connectedComponentIn Cᶜ z₂))
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    IsSeparating C := by
  obtain ⟨hin, hout⟩ := inside_outside_of_two_components hne hall hbey
  refine ⟨hJ, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact ⟨⟨z₁, mem_connectedComponentIn h₁⟩, isPreconnected_connectedComponentIn⟩
  · rw [hout]; exact ⟨⟨z₂, mem_connectedComponentIn h₂⟩, isPreconnected_connectedComponentIn⟩
  · rw [hin]; exact frontier_connectedComponentIn_eq hC z₁ hcl₁
  · rw [hout]; exact frontier_connectedComponentIn_eq hC z₂ hcl₂

namespace ClosedPolygon

/-- **The polygonal Jordan curve theorem** (Theorem 2.3), in the form Definition 2.4 asks for.
The complement of a simple closed polygon has exactly two regions, one bounded and one unbounded,
and each has the polygon as its frontier.

The bounded region is `Schoenflies.inside P.carrier` and the unbounded one
`Schoenflies.outside P.carrier`; everything the blueprint writes `Int(C)` and `Ext(C)` for, and
the whole `IsSeparating` API of `Schoenflies/CrosscutCells.lean`, comes with this statement. -/
theorem isSeparating_carrier (P : ClosedPolygon m) : IsSeparating P.carrier := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hzLC : zL ∉ P.carrier := sideL_subset_compl D hzL
  have hzRC : zR ∉ P.carrier := sideR_subset_compl D hzR
  have hne := P.connectedComponentIn_ne_of_mem_sides D hzL hzR
  have hall : ∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x =
      connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR :=
    fun x hx => P.connectedComponentIn_eq_of_notMem D hzL hzR hx
  -- each track is inside the component of its reference point, so the curve is in its closure
  have hsubL : D.sideL ⊆ connectedComponentIn P.carrierᶜ zL :=
    D.isConnected_sideL.isPreconnected.subset_connectedComponentIn hzL (sideL_subset_compl D)
  have hsubR : D.sideR ⊆ connectedComponentIn P.carrierᶜ zR :=
    D.isConnected_sideR.isPreconnected.subset_connectedComponentIn hzR (sideR_subset_compl D)
  have hclL : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zL) :=
    subset_trans D.carrier_subset_closure_sideL (closure_mono hsubL)
  have hclR : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zR) :=
    subset_trans D.carrier_subset_closure_sideR (closure_mono hsubR)
  -- a square containing the polygon; its outside lies in one of the two components
  obtain ⟨r, -, hrC⟩ := IsCompact.exists_closedSquare P.isCompact_carrier
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  obtain ⟨w, hw⟩ := (Plane.isConnected_beyondSquare r).nonempty
  have hbeysub : Plane.beyondSquare r ⊆ connectedComponentIn P.carrierᶜ w :=
    (Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hw hbeyC
  rcases hall w (hbeyC hw) with hcw | hcw
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzRC hzLC
      (Ne.symm hne) (fun x hx => (hall x hx).symm) hclR hclL (hcw ▸ hbeysub)
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzLC hzRC
      hne hall hclL hclR (hcw ▸ hbeysub)

/-! ### The parity values

The blueprint: "take a point `q` whose coordinate along the ray exceeds that of every point of the
compact set `C`. No edge crosses the level line through `q` beyond `q`, so `π_C(q) = 0`; and `q`
lies in the unbounded region." Here `q` is chosen to be beyond a containing *square* as well, so
that it visibly lies in the unbounded region: the outside of that square is connected, misses the
polygon, and is unbounded. -/

/-! ### The theorem, unpacked -/

end ClosedPolygon

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/ParitySplitting.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Parity splitting: a crosscut adds the two crossing counts

Lemma 2.7. A crosscut `P` of a simple closed polygon `C` cuts it into two arcs `A₁, A₂`, and
the two closed curves `Jᵢ = Aᵢ ∪ P` satisfy `π_C = π_{J₁} + π_{J₂}` off `C ∪ P`. The blueprint
calls this identity "the whole of the polygonal crosscut theorem": Lemma 2.6 exhibits two cells
of `Ω ∖ P`, and this is what says there are no others.

## Where the split is made, and why

The crossing count of `Schoenflies/Parity.lean` is a function of a `List Piece`, not of a set,
and not of a `ClosedPolygon`. Two edge lists with the same carrier can have different parity —
a list that traverses one segment twice is the obvious example — so the identity cannot be
stated for the sets `Aᵢ ∪ P`. It is stated, and proved, for **edge lists**:

    the edge list of `C` is `A₁ ++ A₂`, that of `Jᵢ` is `Aᵢ ++ K`,

where `K` is the edge list of the crosscut. Then `π_{J₁} + π_{J₂} = π_{A₁} + π_{A₂} + 2 π_K`
and the crosscut's contribution cancels mod `2`. That is `parity_split`, and it needs no
geometry at all — no simplicity, no direction, no separation. Everything the blueprint's
picture contributes is in the *hypothesis* that the lists decompose that way.

Two mismatches between "the edge list of `Jᵢ` is `Aᵢ` together with `K`" and literal list
equality have to be absorbed, because a consumer building `Jᵢ` as a `ClosedPolygon` controls
neither:

* the edges come in some cyclic order of that polygon's own choosing, and
* one of the two curves must traverse the crosscut backwards, so its pieces are the *reversed*
  pairs.

`SameEdges` is the equivalence that forgives exactly these two: a permutation of the lists
after each piece has been put in canonical order by `Schoenflies.orientPiece`. Parity, carrier,
closedness and non-levelness are all invariant under it (`SameEdges.parity_eq`,
`SameEdges.cover_eq`, `SameEdges.isChainFrom`, `SameEdges.hgt_ne`), so a consumer may hand over
its edge list in whatever order and orientation it happens to have —
`sameEdges_of_perm_reverse_swap` absorbs both mismatches in one step.

Nothing is assumed about the *sets*: `ClosedPolygon.carrier_eq_of_sameEdges` derives
`Jᵢ.carrier = Aᵢ ∪ P` from the edge lists alone, so the geometric hypothesis a consumer has to
discharge is only ever combinatorial.

## The construction

`ClosedPolygon.arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and
runs forward through `k` edges — the object the split produces, exported as an object rather
than hidden behind an existential. Its two governing facts are

* `ClosedPolygon.arcPieces_split_perm`: `arcPieces C a k ++ arcPieces C (a + k) (m + 3 - k)` is
  a permutation of `C.pieces` — the arcs really do partition the edges; and
* `ClosedPolygon.isChainFrom_arcPieces`: the arc's mod-`2` boundary is its two end vertices,
  which is what makes `Aᵢ ++ K` a *closed* chain and hence eligible for every parity theorem.

`IsChainFrom` is the open-path companion of `Schoenflies.IsClosedChain`, stated by the same
duality; `IsChainFrom.isClosedChain_append` is the one-line reason that an arc and a crosscut
with the same two ends close up. `pathPieces` turns a polyline into such a chain, which is how
the crosscut itself is normally presented.

The endpoints of the crosscut are taken to be **vertices** of `C`; the blueprint's opening
move, "subdivide `C` at `p` and `q`", is what puts them there, and is `parity_subdivide`
(Lemma 2.1) applied before any of this. Nothing below re-proves it. A consumer whose crosscut
lands in the interiors of edges rewrites with `parity_subdivide` first and then applies
`parity_split` to the subdivided list, whose hypotheses are about lists and not about polygons;
what such a consumer must supply for itself is the decomposition of the *subdivided* list into
two arcs, which `arcPieces` does not provide — `arcPieces` splits `C.pieces` at vertices.

## Blueprint

* `SameEdges`, `IsChainFrom`, `pathPieces`, `ClosedPolygon.arcPieces` — the definition of the
  split. "After the subdivision the edge set of `C` is the disjoint union of the edge sets of
  `A₁` and `A₂`, and the edge set of `Jᵢ` is that of `Aᵢ` together with that of `P`."
* `parity_split`, `ClosedPolygon.parity_splitting` — Lemma 2.7, equation (2.2)
  `π_C = π_{J₁} + π_{J₂}`.
* `ClosedPolygon.crosscut_inside_exactly_one`, `ClosedPolygon.crosscut_outside_agree` — the
  "Consequently" of Lemma 2.7, which is where Theorem 2.3 enters: a point of `Int(C)` off `P`
  lies inside exactly one of `J₁, J₂`, and a point of `Ext(C)` off `P` lies inside both or
  inside neither.
* `ClosedPolygon.parity_eq_one_iff` — the two halves of the last sentence of Theorem 2.3, read
  as a single criterion.
* `ClosedPolygon.carrier_eq_of_sameEdges`, `ClosedPolygon.notMem_carrier_of_sameEdges` — the
  bridge back to the sets: `Jᵢ` occupies `Aᵢ ∪ P`, so "off `C` and off `P`" is "off `Jᵢ`".

One lemma here strengthens one on `main`: `mark_swap'` drops the non-levelness hypothesis of
`Schoenflies.mark_swap`, because a level edge is crossed from nowhere and so contributes `0`
under either name. Its home is `Schoenflies/Parity.lean`.
-/

open Metric _root_.Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

/-! ## Edge lists up to order and orientation

Parity, carrier and closedness are all functions of the *multiset of unoriented* edges. This
section says so, so that a consumer may present the edge list of a curve in any order and with
either name for each edge. -/

/-- A level edge is crossed from nowhere: the ray from `q` would have to leave at a height both
`≥` and `<` the common height of the two ends. -/
theorem not_crosses_of_level {c d : Plane} (h : hgt u c = hgt u d) (q : Plane) :
    ¬ Crosses u (c, d) q := by
  intro hcr
  obtain ⟨h1, h2, -⟩ := hcr
  have e1 : ((c, d) : Piece).1 = c := rfl
  have e2 : ((c, d) : Piece).2 = d := rfl
  rw [e1, e2, h, min_self] at h1
  rw [e1, e2, h, max_self] at h2
  linarith

/-- **The contribution of an edge does not depend on which end is named first.** This is
`Schoenflies.mark_swap` with its non-levelness hypothesis removed: a level edge contributes `0`
under either name. -/
theorem mark_swap' (u : Plane) (P : Piece) (q : Plane) : mark u (P.2, P.1) q = mark u P q := by
  obtain ⟨a, b⟩ := P
  by_cases h : hgt u a = hgt u b
  · rw [mark, mark, if_neg (not_crosses_of_level h.symm q), if_neg (not_crosses_of_level h q)]
  · exact mark_swap h q

/-- Reordering the edges does not change the count. -/
theorem parity_perm (h : L₁.Perm L₂) (u q : Plane) : parity u L₁ q = parity u L₂ q :=
  (h.map fun P => mark u P q).sum_eq

/-- Reordering the edges does not change what they occupy. -/
theorem cover_perm (h : L₁.Perm L₂) : cover L₁ = cover L₂ := by
  ext z
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.1 hP, hz⟩, fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.2 hP, hz⟩⟩

/-- `orientPiece` either leaves a piece alone or reverses it; that is all this file uses. -/
theorem orientPiece_eq_or (P : Piece) : orientPiece P = P ∨ orientPiece P = (P.2, P.1) := by
  by_cases h : Precedes P.1 P.2
  · exact Or.inl (orientPiece_of_precedes h)
  · exact Or.inr (orientPiece_of_not_precedes h)

theorem mark_orientPiece (u : Plane) (P : Piece) (q : Plane) :
    mark u (orientPiece P) q = mark u P q := by
  rcases orientPiece_eq_or P with h | h
  · rw [h]
  · rw [h, mark_swap']

theorem parity_map_orientPiece (u : Plane) (L : List Piece) (q : Plane) :
    parity u (L.map orientPiece) q = parity u L q := by
  simp only [parity, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun P _ => mark_orientPiece u P q)

/-- **Two edge lists carry the same edges**: they agree after reordering, each edge being free
to be named by either of its two ends first. This is the relation under which "the edge list of
`Jᵢ` is that of `Aᵢ` together with that of `P`" is true — a `ClosedPolygon` built on `Aᵢ ∪ P`
lists its edges in its own cyclic order, and traverses one of the two pieces backwards. -/
def SameEdges (L₁ L₂ : List Piece) : Prop := (L₁.map orientPiece).Perm (L₂.map orientPiece)

/-- A reordering is in particular the same edges. -/
theorem SameEdges.of_perm (h : L₁.Perm L₂) : SameEdges L₁ L₂ := h.map _

theorem SameEdges.parity_eq (h : SameEdges L₁ L₂) (u q : Plane) :
    parity u L₁ q = parity u L₂ q := by
  rw [← parity_map_orientPiece u L₁ q, ← parity_map_orientPiece u L₂ q]
  exact parity_perm h u q

theorem hgt_ne_append (h₁ : ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2)
    (h₂ : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) : ∀ Q ∈ L₁ ++ L₂, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact h₁ Q h
  · exact h₂ Q h

/-! ## Chains with two ends

`Schoenflies.IsClosedChain` says the mod-`2` boundary of an edge list vanishes. An arc and a
crosscut are not closed; each has a boundary, namely its two ends, and closing them up is the
statement that the two boundaries agree. Stated by the same duality as `IsClosedChain`, so that
the two definitions compose with nothing but `List.sum_append`. -/

/-- `L` is a **chain from `p` to `q`**: its mod-`2` boundary is `p` together with `q`. Stated by
duality, exactly as `Schoenflies.IsClosedChain` is. -/
def IsChainFrom (L : List Piece) (p q : Plane) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map fun P => f P.1 + f P.2).sum = f p + f q

/-- A chain whose two ends coincide is a closed chain, and conversely. -/
theorem isChainFrom_self_iff : IsChainFrom L p p ↔ IsClosedChain L := by
  constructor <;> intro h f
  · rw [h f]; exact add_self_zmod_two _
  · rw [h f]; exact (add_self_zmod_two _).symm

theorem isChainFrom_nil (p : Plane) : IsChainFrom [] p p := fun f => by
  simp [(add_self_zmod_two (f p)).symm]

/-- Chains compose end to end. -/
theorem IsChainFrom.append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ q r) :
    IsChainFrom (L₁ ++ L₂) p r := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  linear_combination add_self_zmod_two (f q)

/-- **Two chains with the same two ends close up.** This is the whole reason `Aᵢ ∪ P` is a
closed curve as far as the crossing count is concerned. -/
theorem IsChainFrom.isClosedChain_append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ p q) :
    IsClosedChain (L₁ ++ L₂) := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  exact add_self_zmod_two _

/-! ### The edges of a polyline

How a crosscut is normally presented: a list of points. `pathPieces` reads off its edges, and
`isChainFrom_pathPieces` says its boundary is the two ends of the list. -/

/-! ## The two arcs of a polygon

`arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and runs forward
through `k` edges. Its two ends are vertices `a` and `a + k`, and for `k ≤ m + 3` the two arcs
`arcPieces C a k` and `arcPieces C (a + k) (m + 3 - k)` between them use each edge of `C`
exactly once. -/

/-! ## The identity

Everything above was the definition. The identity itself is one line of `ZMod 2` arithmetic:
the crosscut is counted once in each of `π_{J₁}` and `π_{J₂}`, so its contribution cancels. -/

/-- **Parity splitting** (Lemma 2.7), in edge-list form and with no geometry whatever. If the
edge list of `C` is the two arcs `A₁, A₂` and the edge list of `Jᵢ` is `Aᵢ` together with the
crosscut's list `K` — in each case up to reordering and up to reversing individual edges — then
`π_{J₁} + π_{J₂} = π_C` at *every* point of the plane.

The hypotheses carry all of the blueprint's picture; the proof is that `K` is counted twice. -/
theorem parity_split (u : Plane) {LC A₁ A₂ K : List Piece}
    (hC : SameEdges LC (A₁ ++ A₂)) (h₁ : SameEdges L₁ (A₁ ++ K)) (h₂ : SameEdges L₂ (A₂ ++ K))
    (q : Plane) : parity u L₁ q + parity u L₂ q = parity u LC q := by
  rw [h₁.parity_eq u q, h₂.parity_eq u q, hC.parity_eq u q, parity_append, parity_append,
    parity_append]
  linear_combination add_self_zmod_two (parity u K q)

namespace ClosedPolygon

/-! ### What the identity says about the regions

Theorem 2.3 fixes the two values of `π` for each of the three curves — `1` on the bounded
region, `0` on the unbounded one — and the identity then reads off the blueprint's
"consequently". -/

end ClosedPolygon

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolygonalCrosscut.lean` -/

/-!
# Theorem 2.8: two-sided polygonal crosscuts

A crosscut `P` of a simple closed polygon `C` cuts one of the two regions of `ℝ² ∖ C` into
exactly two, bounded by the two curves `Jᵢ = Aᵢ ∪ P`; and `ℝ² ∖ (C ∪ P)` then has exactly three
regions, with boundaries `C, J₁, J₂`.

## One theorem, not two

The blueprint splits the statement into case (a), the crosscut inside `C`, and case (b), the
crosscut outside. The two cases differ only in *which* region of `ℝ² ∖ Jᵢ` is the new cell: in
case (a) it is `Int(Jᵢ)` for both `i`, while in case (b) it is `Ext(J₁)` for one index and
`Int(J₂)` for the other, and which is which is not determined by the data. What *is* uniform is
the description "the region of `ℝ² ∖ Jᵢ` on the far side from a point `y` of the region of
`ℝ² ∖ C` that the crosscut does not enter". So the whole theorem is proved once, for

    farRegion J y  =  the region of `ℝ² ∖ J` that does not contain `y`,

and the two cases of the blueprint are then read off by identifying `farRegion` with `inside`
or with `outside` (`IsSeparating.farRegion_eq_inside`, `…_eq_outside`). A reference point `y`
in the untouched region is the one extra datum this costs, and it is exactly the datum the
blueprint hides in the phrase "let `Ω` be the region containing `P ∖ {p, q}`".

## Exhaustion is pure parity, in both cases at once

Lemma 2.6 (`Schoenflies.crosscut_cells`) already exhibits the two cells as components of
`Ω ∖ P`. All that Theorem 2.8 adds is that there are no others, and the blueprint reads this
off Lemma 2.7. Here the reading is uniform. Write `πJ` for the crossing count of a curve `J`.
For points `x, y` off `J` — Theorem 2.3 —

    `x` and `y` lie in different regions of `ℝ² ∖ J`  ↔  `πJ(x) ≠ πJ(y)`,

which is `ClosedPolygon.parity_ne_iff_mem_farRegion`. Lemma 2.7 gives
`πJ₁ + πJ₂ = πC` at every point, so subtracting the identity at `y` from the identity at `x`
turns "`x` is separated from `y` by `C`" into "`x` is separated from `y` by exactly one of
`J₁, J₂`" — `IsPolygonalCrosscut.separates_xor`, whose entire proof is sixteen cases of `ZMod 2`
arithmetic. No case distinction on inside/outside is made anywhere.

## The hypotheses, bundled

`IsPolygonalCrosscut C J₁ J₂ K a k y` collects the seven hypotheses of the theorem: the two
curves of the split carry the right edges (`Schoenflies.SameEdges`, from Lemma 2.7), the
crosscut meets `C` only in points common to both arcs, and the reference point `y` lies off `C`
in a region the crosscut does not enter. It is closed under swapping the two arcs
(`IsPolygonalCrosscut.symm`), which is why every statement below is proved for index `1` only.

Realizing `J₁` and `J₂` as `ClosedPolygon`s is the consumer's job, exactly as in Lemma 2.7 —
see the note there about the `corner` field. Nothing in this file inspects `corner`.

## Blueprint

* `farRegion`, `IsSeparating.isRegionPair_farRegion`, `IsSeparating.farRegion_eq_inside`,
  `IsSeparating.farRegion_eq_outside` — the blueprint's `Ω`, `Ω†`, `Vᵢ` and `Wᵢ` named as
  functions of a reference point instead of by an existential.
* `ClosedPolygon.arc` — the arcs `A₁, A₂` of Theorem 2.8, as sets; `…vertex_mem_arc`,
  `…vertex_add_mem_arc`, `…endpoints_subset_arc`, `…endpoints_subset_arc'` — the two cut
  vertices lie on both arcs, which is what "the crosscut meets `C` only in its endpoints" has
  to say to be usable.
* `ClosedPolygon.parity_ne_iff_mem_farRegion` — Theorem 2.3 read as a separation criterion.
* `IsPolygonalCrosscut` — the hypotheses of Theorem 2.8; `IsPolygonalCrosscut.of_endpoints` is
  the constructor a consumer should use, and `IsPolygonalCrosscut.symm` swaps the two arcs.
* `IsPolygonalCrosscut.separates_xor` — Lemma 2.7's "consequently", in the uniform form.
* `IsPolygonalCrosscut.region_eq`, `…cells_disjoint`, `…cells_ne`, `…cell_isComponent₁/₂`,
  `…frontier_cell₁/₂`, `…closure_cell_inter₁/₂` — the two cells of `Ω ∖ P`.
* `IsPolygonalCrosscut.inside_diff_eq` — Theorem 2.8(a).
* `IsPolygonalCrosscut.outside_diff_eq`, `…inside_exactly_one` — Theorem 2.8(b).
* `IsPolygonalCrosscut.compl_eq`, `…isComponent`, `…near_isComponent`,
  `…cell_isComponent_compl₁/₂`, `…cell_ne_near₁/₂`, `…frontier_near` — "in either case
  `ℝ² ∖ (C ∪ P)` has exactly three regions, with boundaries `C, J₁, J₂`".
* `polygonal_crosscut` — Theorem 2.8, bundled.
-/

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

/-! ## The region on the far side of a point

The blueprint names the four regions in play — `Ω`, `Ω†`, `Wᵢ`, `Vᵢ` — by their relation to one
another: `Ω†` is the region of `ℝ² ∖ C` the crosscut does not enter, and `Vᵢ` is the region of
`ℝ² ∖ Jᵢ` on the other side of `Jᵢ` from `Ω†`. Fixing a point `y ∈ Ω†` turns all four into
functions of the data. -/

/-- The region of `ℝ² ∖ C` that does **not** contain `y`: everything off `C` except the
component of `y`. For a separating curve this really is the other region
(`IsSeparating.isRegionPair_farRegion`); no hypothesis is needed to define it. -/
def farRegion (C : Set Plane) (y : Plane) : Set Plane := Cᶜ \ connectedComponentIn Cᶜ y

theorem compl_diff_inside (C : Set Plane) : Cᶜ \ inside C = outside C := by
  ext w
  constructor
  · rintro ⟨hw, hwin⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_left hwin
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside h hw⟩

theorem compl_diff_outside (C : Set Plane) : Cᶜ \ outside C = inside C := by
  ext w
  constructor
  · rintro ⟨hw, hwout⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_right hwout
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside hw h⟩

/-- The component of `y` and the far region are *the* two regions of `ℝ² ∖ C`. -/
theorem IsSeparating.isRegionPair_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionPair C (connectedComponentIn Cᶜ y) (farRegion C y) := by
  rcases hC.isRegionOf_connectedComponentIn hy with hc | hc
  · exact Or.inl ⟨hc, by rw [farRegion, hc, compl_diff_inside]⟩
  · exact Or.inr ⟨hc, by rw [farRegion, hc, compl_diff_outside]⟩

theorem IsSeparating.isRegionOf_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionOf C (farRegion C y) := (hC.isRegionPair_farRegion hy).right

/-! ## The three regions of `ℝ² ∖ (C ∪ P)`, abstractly

Lemma 2.6 places the two cells inside `Ω ∖ P`; the last paragraph of the proof of Theorem 2.8
places all three regions inside `ℝ² ∖ (C ∪ P)`, and the argument is the same each time: an open
connected set whose frontier misses the ambient open set is a component of it (Lemma 1.7). -/

/-! ## The arcs of a polygon, and parity as a separation criterion -/

/-- Going `k` steps forward and then the remaining `m + 3 - k` returns to where one started:
the second arc of a split ends at the first arc's starting vertex. -/
theorem zmod_add_sub_cancel {m k : ℕ} (hk : k ≤ m + 3) (a : ZMod (m + 3)) :
    a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
  have hcast : ((k : ℕ) : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = 0 := by
    rw [← Nat.cast_add, show k + (m + 3 - k) = m + 3 by omega]
    exact ZMod.natCast_self _
  rw [add_assoc, hcast, add_zero]

/-! ## The hypotheses of Theorem 2.8 -/

namespace IsPolygonalCrosscut

/-! ### The elementary consequences -/

/-! ### The two cells

Lemma 2.6 applies with `Ω = farRegion C.carrier y`, `Ω' = connectedComponentIn C.carrierᶜ y`,
`Wᵢ = connectedComponentIn Jᵢ.carrierᶜ y` and `Vᵢ = farRegion Jᵢ.carrier y`. The inclusion
`Ω' ⊆ Wᵢ` — the blueprint's "being connected it lies in one region of `ℝ² ∖ Jᵢ`" — is
`near_subset₁`, and needs no separation hypothesis at all. -/

/-! ### Exhaustion: the crossing counts add up

This is the whole of Theorem 2.8 beyond Lemma 2.6, and it is one `ZMod 2` computation. -/

/-! ### The three regions of `ℝ² ∖ (C ∪ P)` -/

/-! ### The blueprint's two cases -/

end IsPolygonalCrosscut

end Schoenflies

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/TwoArcs.lean` -/

/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

namespace Schoenflies

namespace IsLoop

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

/-! ### The three pieces are arcs -/

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-! ### Covering, and where the pieces meet -/

/-! ### The two arcs, at chosen parameters -/

end IsLoop

/-! ### The theorem -/

end Schoenflies

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Realization.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: an `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger than
the blueprint's notion, and until now nothing said that a set-level polygonal Jordan curve
admits such a presentation. This module proves it.

## How the vertex list is found

The curve is *not* read off the vertex list `IsPolygonal` hands over: that list may retrace
itself, cross itself, and repeat segments, and it carries no order along the curve. Two
structures are laid over the point set instead and then matched.

* **From the plane side**, the overlay of `Schoenflies/OverlayGraph.lean`, with the graph
  discarded: `Schoenflies.IsClean` is a finite list of nondegenerate segments occupying the
  curve, with pairwise disjoint interiors and no end interior to any of them. Around an interior
  point of a piece the curve *is* that piece (`IsClean.exists_ball_subset_seg`), so the piece
  interiors are separated by honest open sets of the plane (`Schoenflies.nearPiece`) and a
  connected subset of the curve away from the ends lies inside a single piece.
* **From the curve side**, the loop's parameters at which it reaches an end of a piece. They
  form a finite subset of `[0, 1)` containing `0` — `0` because the loop's start is put on the
  cut list, so that the last gap is the one that closes the curve — and, listed in increasing
  order, they cut `[0, 1)` into gaps.

The two match: a gap image is connected and misses the ends, so it lies in one piece interior;
and the interior is connected and covered by the *closed* gap images, so it lies in that one
gap. Gaps and pieces therefore correspond one to one, the ends of a gap are the ends of its
piece, and the ends listed in the loop's order are a cyclic vertex list whose edges are the
pieces. That list satisfies `vertex_inj` and `edges_meet` but not `corner`, which is what
`Schoenflies.PrePolygon` is for; `corner` is then arranged by deleting redundant vertices.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`
  — the blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two
  consecutive edges are collinear", as an operation rather than an invariant.
* `Schoenflies.IsClean`, `Schoenflies.exists_isClean` — Lemma 3.7 (polygonal overlay) with the
  combinatorics dropped: what the overlay says about the point set alone.
* `Schoenflies.par`, `Schoenflies.parNext`, `Schoenflies.exists_mem_gap` — the parameters in
  increasing order, and that their gaps tile `[0, 1)`.
* `Schoenflies.exists_prePolygon_of_isJordanCurve`, `Schoenflies.exists_closedPolygon` — §1:
  every simple closed polygonal curve, in the blueprint's set-level sense, is the carrier of a
  `ClosedPolygon`.
* `Schoenflies.IsStraightAt`, `Schoenflies.IsCornerAt`,
  `Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
  `Schoenflies.ClosedPolygon.isCornerAt_vertex` — the vertex set of a realization is *exactly*
  the set of points at which the curve does not run straight. So a named point can be required
  to be a vertex precisely when it is a corner, and no realization has any choice about it.
* `Schoenflies.ClosedPolygon.rotate`, `…isArcBetween_arc`, `…arc_inter` — the two arcs of a
  splitting, as arcs between the two cut vertices meeting exactly there.
* `Schoenflies.two_arcs_unique` — two points cut a Jordan curve into two arcs in only one way.
* `Schoenflies.exists_closedPolygon_corners`, `Schoenflies.exists_closedPolygon_split`,
  `Schoenflies.exists_closedPolygon_arcs`, `Schoenflies.exists_closedPolygon_arcs_ordered` — the
  realization with named corners, with the splitting indices, and with the two arcs identified.
  The last is the shape `Graph.IsHexRealization` asks for.

## The corner hypothesis is not an artefact

`exists_closedPolygon_arcs` requires the two cut points to be corners.
`ClosedPolygon.isCornerAt_vertex` shows that this cannot be dropped: every vertex of every
realization is a corner, so a cut point at which the curve runs straight is a vertex of *no*
realization, and no `ClosedPolygon` with that carrier has an arc ending there. A consumer that
needs to cut at a straight point has to change the curve — bend it there — which is a different
theorem, and is exactly the freedom `Graph.IsK33Config.not_isDrawing` reserves for itself.
-/

open Metric _root_.Set unitInterval

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-- A simple closed polygonal curve presented by its cyclic vertex list, with redundant
vertices allowed: `ClosedPolygon` less its `corner` field. -/
structure PrePolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PrePolygon

variable {m : ℕ} (P : PrePolygon m)

/-- The edge leaving vertex `i`. -/
def edge (i : ZMod (m + 3)) : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier: the union of the edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P}

theorem edge_subset_carrier (i : ZMod (m + 3)) : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

theorem vertex_ne_succ (i : ZMod (m + 3)) : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  ClosedPolygon.succ_ne_self i (P.vertex_inj h).symm

end PrePolygon

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

theorem val_one_eq : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num]
  exact ZMod.val_cast_of_lt (by omega)

/-- The successor of a non-final index is the next one. -/
theorem val_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : (j + 1).val = j.val + 1 := by
  rw [ZMod.val_add, val_one_eq, Nat.mod_eq_of_lt h]

/-- The successor of the final index wraps to `0`. -/
theorem val_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : (j + 1).val = 0 := by
  rw [ZMod.val_add, val_one_eq, h, Nat.mod_self]

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

@[simp] theorem rotate_vertex (P : PrePolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

/-- Rotating does not move the curve: the edges are the same, listed from elsewhere. -/
theorem carrier_rotate (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.rotate a).carrier = P.carrier := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · rw [hedge]; exact edge_subset_carrier _
  · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := P.rotate a) (i - a))
    rw [hedge, add_sub_cancel]

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

section Delete

variable {m : ℕ}

/-- An index of the shortened list, read in the original one: the same numeral. -/
def emb (j : ZMod (m + 3)) : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3))

theorem neg_one_eq_cast : (-1 : ZMod (m + 1 + 3)) = ((m + 3 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem neg_two_eq_cast : (-1 - 1 : ZMod (m + 1 + 3)) = ((m + 2 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem emb_injective : Function.Injective (emb (m := m)) := fun i j h =>
  ZMod.val_injective _ (ClosedPolygon.natCast_inj (m := m + 1)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt j; omega) h)

theorem emb_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : emb (j + 1) = emb j + 1 := by
  rw [emb, emb, val_succ_of_lt h, Nat.cast_add, Nat.cast_one]

theorem emb_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb (j + 1) = 0 := by
  rw [emb, val_succ_last h, Nat.cast_zero]

theorem emb_eq_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb j = -1 - 1 := by
  rw [emb, neg_two_eq_cast, show j.val = m + 2 by omega]

/-- Below the last index, `emb` misses both the deleted vertex and its predecessor. -/
theorem emb_ne_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    emb j ≠ -1 ∧ emb j ≠ -1 - 1 := by
  have hj := ZMod.val_lt j
  constructor
  · rw [neg_one_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 3)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)
  · rw [neg_two_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 2)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)

/-- Every index other than the deleted vertex and its predecessor is hit by `emb`. -/
theorem exists_emb_eq {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    ∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i := by
  have hi := ZMod.val_lt i
  have hne1 : i.val ≠ m + 3 := by
    rintro he
    exact h1 (by rw [neg_one_eq_cast, ← he, ZMod.natCast_rightInverse i])
  have hne2 : i.val ≠ m + 2 := by
    rintro he
    exact h2 (by rw [neg_two_eq_cast, ← he, ZMod.natCast_rightInverse i])
  refine ⟨(i.val : ZMod (m + 3)), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt (show i.val < m + 3 by omega)]; omega
  · rw [emb, ZMod.val_cast_of_lt (show i.val < m + 3 by omega), ZMod.natCast_rightInverse i]

variable (P : PrePolygon (m + 1))

/-- The vertex list with its last entry dropped. -/
def dropVertex (j : ZMod (m + 3)) : Plane := P.vertex (emb j)

variable {P}

theorem dropVertex_injective : Function.Injective P.dropVertex :=
  fun _ _ h => emb_injective (P.vertex_inj h)

/-- Away from the deleted vertex the edges are unchanged. -/
theorem dropVertex_edge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (emb j) := by
  rw [dropVertex, dropVertex, emb_succ_of_lt h, edge]

/-- The final edge of the shortened list is the union of the two edges at the deleted vertex —
which is a segment precisely because the deleted vertex is interior to it. -/
theorem dropVertex_edge_last
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (-1 - 1) ∪ P.edge (-1) := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  rw [dropVertex, dropVertex, emb_succ_last h, emb_eq_last h, edge, edge, e1, e2]
  exact segment_split (openSegment_subset_segment ℝ _ _ hcol)

/-- The deleted vertex lies on no edge but its own two: `edges_meet` puts a meeting point at an
end of the other edge, and the deleted vertex is an end only of the two edges at it. -/
theorem vertex_last_notMem_edge {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    P.vertex (-1) ∉ P.edge i := by
  intro hmem
  have hself : P.vertex (-1) ∈ P.edge (-1) := left_mem_segment ℝ _ _
  have hme := P.edges_meet i (-1) h1 (Set.mem_inter hmem hself)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
  rcases hme with he | he
  · exact h1 (P.vertex_inj he).symm
  · exact h2 (by linear_combination -P.vertex_inj he)

/-- **Simplicity survives the deletion.** The only new edge is the merged one, and the point
that has to be kept out of it — the deleted vertex — lies on no other edge at all. -/
theorem dropVertex_edges_meet
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    (j k : ZMod (m + 3)) (hjk : j ≠ k) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) ∩
      segment ℝ (P.dropVertex k) (P.dropVertex (k + 1)) ⊆
      {P.dropVertex j, P.dropVertex (j + 1)} := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
  have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
  rcases eq_or_lt_of_le hjv with hj | hj
  · -- `j` is the last index, so its edge is the merged one.
    have hdj : P.dropVertex j = P.vertex (-1 - 1) := by rw [dropVertex, emb_eq_last hj]
    have hdj1 : P.dropVertex (j + 1) = P.vertex 0 := by rw [dropVertex, emb_succ_last hj]
    rcases eq_or_lt_of_le hkv with hk | hk
    · exact absurd (ZMod.val_injective _ (by omega : j.val = k.val)) hjk
    obtain ⟨hk1, hk2⟩ := emb_ne_of_lt hk
    have hout := vertex_last_notMem_edge (P := P) hk1 hk2
    rw [dropVertex_edge_last hcol hj, dropVertex_edge_of_lt hk, hdj, hdj1]
    rintro x ⟨hx1 | hx1, hx2⟩
    · have hme := P.edges_meet _ _ (fun h => hk2 h.symm) (Set.mem_inter hx1 hx2)
      rw [e1] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact hme.imp id fun h => absurd (h ▸ hx2) hout
    · have hme := P.edges_meet _ _ (fun h => hk1 h.symm) (Set.mem_inter hx1 hx2)
      rw [e2] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact Or.inr (hme.resolve_left fun h => absurd (h ▸ hx2) hout)
  · -- `j` is an ordinary index, so its edge is unchanged.
    obtain ⟨hj1, hj2⟩ := emb_ne_of_lt hj
    have hdj : P.dropVertex j = P.vertex (emb j) := rfl
    have hdj1 : P.dropVertex (j + 1) = P.vertex (emb j + 1) := by
      rw [dropVertex, emb_succ_of_lt hj]
    rw [dropVertex_edge_of_lt hj, hdj, hdj1]
    rcases eq_or_lt_of_le hkv with hk | hk
    · rw [dropVertex_edge_last hcol hk]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact P.edges_meet _ _ hj2 (Set.mem_inter hx1 hx2)
      · exact P.edges_meet _ _ hj1 (Set.mem_inter hx1 hx2)
    · rw [dropVertex_edge_of_lt hk]
      exact fun x hx => P.edges_meet _ _ (fun h => hjk (emb_injective h)) hx

/-- **The polygon with a redundant vertex deleted.** -/
def deleteLast (P : PrePolygon (m + 1))
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) : PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := dropVertex_injective
  edges_meet := dropVertex_edges_meet hcol

/-- **Deleting a redundant vertex does not move the curve.** -/
theorem carrier_deleteLast
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) :
    (deleteLast P hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with hj | hj
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_last hcol hj]
      exact Set.union_subset (edge_subset_carrier _) (edge_subset_carrier _)
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj]
      exact edge_subset_carrier _
  · by_cases hi : i = -1 ∨ i = -1 - 1
    · -- The two edges at the deleted vertex are both inside the merged one.
      set j : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3)) with hjdef
      have hj : j.val + 1 = m + 3 := by rw [hjdef, ZMod.val_cast_of_lt (by omega)]
      have hmerge : (deleteLast P hcol).edge j = P.edge (-1 - 1) ∪ P.edge (-1) :=
        dropVertex_edge_last hcol hj
      refine le_trans ?_ (le_trans (le_of_eq hmerge.symm) (edge_subset_carrier j))
      rcases hi with rfl | rfl
      · exact Set.subset_union_right
      · exact Set.subset_union_left
    · push Not at hi
      obtain ⟨j, hj, hemb⟩ := exists_emb_eq hi.1 hi.2
      have : (deleteLast P hcol).edge j = P.edge i := by
        rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj, hemb]
      exact le_trans (le_of_eq this.symm) (edge_subset_carrier j)

end Delete

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

/-- A nondegenerate segment is not contained in the pair of its own endpoints. -/
theorem exists_mem_segment_ne {a b : Plane} (hab : a ≠ b) :
    ∃ p ∈ segment ℝ a b, p ≠ a ∧ p ≠ b := by
  have hmem : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSegment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨_, openSegment_subset_segment ℝ a b hmem, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    exact hab (left_mem_openSegment_iff.1 hmem)
  · intro h
    rw [h] at hmem
    exact hab (right_mem_openSegment_iff.1 hmem)

/-- **Three collinear points meeting only at the shared one are in the order that makes the
middle one interior.** The alternative — the two segments running the same way out of `b` —
makes them overlap in a nondegenerate segment, which the meeting hypothesis forbids. -/
theorem mem_openSegment_of_det_eq_zero' {a b c : Plane} (hab : a ≠ b) (hcb : c ≠ b)
    (hmeet : segment ℝ a b ∩ segment ℝ b c ⊆ {a, b})
    (h : det (a - b) (c - b) = 0) : b ∈ openSegment ℝ a c := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨r, hr⟩ := (det_eq_zero_iff_smul _ _ hab').1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hr
    exact hcb hr
  have hcexp : c = b + r • (a - b) := by linear_combination (norm := module) hr
  have hrneg : r < 0 := by
    rcases lt_trichotomy r 0 with hlt | heq | hgt
    · exact hlt
    · exact absurd heq hr0
    exfalso
    -- A short step out of `b` towards `a` is then also a step towards `c`.
    have hμpos : 0 < min 1 r / 2 := by positivity
    set μ : ℝ := min 1 r / 2 with hμdef
    have hμ1 : μ < 1 := by
      have h1 : min 1 r ≤ 1 := min_le_left _ _
      rw [hμdef]; linarith
    have hμler : μ / r < 1 := by
      rw [div_lt_one hgt]
      have h1 : min 1 r ≤ r := min_le_right _ _
      rw [hμdef]; linarith
    have hμr : μ / r * r = μ := div_mul_cancel₀ _ (ne_of_gt hgt)
    have hz₁ : μ • a + (1 - μ) • b ∈ segment ℝ a b :=
      ⟨μ, 1 - μ, hμpos.le, by linarith, by ring, rfl⟩
    have hz₂ : μ • a + (1 - μ) • b ∈ segment ℝ b c := by
      refine ⟨1 - μ / r, μ / r, by linarith, by positivity, by ring, ?_⟩
      have expand : (1 - μ / r) • b + (μ / r) • (b + r • (a - b))
          = (μ / r * r) • a + (1 - μ / r * r) • b := by module
      rw [hcexp, expand, hμr]
    have hmem := hmeet ⟨hz₁, hz₂⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with he | he
    · have hkey : (1 - μ) • (a - b) = 0 := by linear_combination (norm := module) -he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact (by linarith : (0 : ℝ) < 1 - μ).ne' h'
      · exact hab' h'
    · have hkey : μ • (a - b) = 0 := by linear_combination (norm := module) he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact hμpos.ne' h'
      · exact hab' h'
  -- Opposite directions: the vertex is a strict convex combination of its neighbours.
  have hden : (0 : ℝ) < 1 - r := by linarith
  refine ⟨-r / (1 - r), 1 / (1 - r), div_pos (by linarith) hden, div_pos one_pos hden,
    by field_simp; ring, ?_⟩
  have expand : (-r / (1 - r)) • a + (1 / (1 - r)) • (b + r • (a - b))
      = (-r / (1 - r) + 1 / (1 - r) * r) • a + (1 / (1 - r) - 1 / (1 - r) * r) • b := by module
  rw [hcexp, expand, show -r / (1 - r) + 1 / (1 - r) * r = 0 by field_simp; ring,
    show (1 : ℝ) / (1 - r) - 1 / (1 - r) * r = 1 by field_simp, zero_smul, one_smul, zero_add]

variable {m : ℕ} {P : PrePolygon m}

/-- **A redundant vertex is interior to the segment joining its neighbours.** -/
theorem mem_openSegment_of_det_eq_zero (i : ZMod (m + 3))
    (h : det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0) :
    P.vertex i ∈ openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  have hpred : i - 1 + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := fun he =>
    ClosedPolygon.succ_ne_self (i - 1) (by rw [hpred]; exact he.symm)
  have hmeet := P.edges_meet (i - 1) i hne
  rw [hpred] at hmeet
  exact mem_openSegment_of_det_eq_zero' (fun he => hne (P.vertex_inj he))
    (fun he => ClosedPolygon.succ_ne_self i (P.vertex_inj he)) hmeet h

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- A three-vertex polygon has no redundant vertex: were the last one interior to the segment
joining the other two, the edge before it would lie inside the edge opposite it. -/
theorem not_collinear_triangle (P : PrePolygon 0) :
    P.vertex (-1) ∉ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  intro hcol
  have e1 : (-1 - 1 : ZMod (0 + 3)) + 1 = -1 := by decide
  have e2 : (-1 : ZMod (0 + 3)) ≠ -1 - 1 := by decide
  have hsplit : segment ℝ (P.vertex (-1 - 1)) (P.vertex 0)
      = segment ℝ (P.vertex (-1 - 1)) (P.vertex (-1)) ∪ segment ℝ (P.vertex (-1)) (P.vertex 0) :=
    segment_split (openSegment_subset_segment ℝ _ _ hcol)
  -- The edge before the redundant vertex sits inside the edge opposite it.
  have hsub : P.edge (-1 - 1) ⊆ P.edge (-1 - 1 - 1) := by
    have e3 : (-1 - 1 - 1 : ZMod (0 + 3)) = 0 := by decide
    have e4 : (0 : ZMod (0 + 3)) + 1 = -1 - 1 := by decide
    rw [edge, edge, e1, e3, e4, segment_symm ℝ (P.vertex 0) (P.vertex (-1 - 1)), hsplit]
    exact Set.subset_union_left
  obtain ⟨p, hp, hp1, hp2⟩ := exists_mem_segment_ne (P.vertex_ne_succ (-1 - 1))
  rcases P.edges_meet (-1 - 1) (-1 - 1 - 1) (by decide) ⟨hp, hsub hp⟩ with h | h
  exacts [hp1 h, hp2 h]

/-- **Every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier.** This is the
blueprint's "delete redundant vertices at which two consecutive edges are collinear", run to
completion; the induction is on the number of vertices, which each deletion lowers by one. -/
theorem exists_closedPolygon_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (m' : ℕ) (P' : ClosedPolygon m'), P'.carrier = P.carrier := by
  intro m
  induction m with
  | zero =>
    intro P
    by_cases hc : ∀ i : ZMod (0 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨0, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine absurd ?_ (not_collinear_triangle (P.rotate (i + 1)))
      have e1 : i + 1 + (-1 : ZMod (0 + 3)) = i := by ring
      have e2 : i + 1 + (-1 - 1 : ZMod (0 + 3)) = i - 1 := by ring
      have e3 : i + 1 + (0 : ZMod (0 + 3)) = i + 1 := by ring
      rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
      exact mem_openSegment_of_det_eq_zero i hi
  | succ m ih =>
    intro P
    by_cases hc : ∀ i : ZMod (m + 1 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m + 1, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hcol : (P.rotate (i + 1)).vertex (-1) ∈
          openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
        have e1 : i + 1 + (-1 : ZMod (m + 1 + 3)) = i := by ring
        have e2 : i + 1 + (-1 - 1 : ZMod (m + 1 + 3)) = i - 1 := by ring
        have e3 : i + 1 + (0 : ZMod (m + 1 + 3)) = i + 1 := by ring
        rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
        exact mem_openSegment_of_det_eq_zero i hi
      obtain ⟨m', P', hP'⟩ := ih (deleteLast (P.rotate (i + 1)) hcol)
      exact ⟨m', P', by rw [hP', carrier_deleteLast, carrier_rotate]⟩

/-- Assembling a cyclic vertex family into a `PrePolygon`. The index type is `ZMod n` for an
`n` known only to be at least three, which is what `PrePolygon` asks for after `n` is written
`m + 3`. -/
theorem exists_prePolygon {n : ℕ} (hn : 3 ≤ n) (w : ZMod n → Plane) (hinj : Function.Injective w)
    (hmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)}) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = ⋃ i, segment ℝ (w i) (w (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact ⟨m, ⟨w, hinj, hmeet⟩, rfl⟩

end PrePolygon

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-- A finite list of segments presenting a polygonal set as a plane graph would: occupying it,
nondegenerate, with pairwise disjoint interiors, and with no end interior to any piece. -/
structure IsClean (Q : List Piece) (C : Set Plane) : Prop where
  /-- The pieces occupy the set. -/
  cover_eq : cover Q = C
  /-- No piece is a point. -/
  nondeg : ∀ R ∈ Q, R.Nondeg
  /-- No end of any piece is interior to any piece. -/
  ends : ∀ R ∈ Q, ∀ S ∈ Q, ∀ z, (z = R.1 ∨ z = R.2) → z ∉ S.interior
  /-- Distinct pieces have disjoint interiors. -/
  interiors : ∀ R ∈ Q, ∀ S ∈ Q, R ≠ S → ∀ x ∈ R.interior, x ∉ S.interior

/-- **Every polygonal set with two points in it has a clean presentation**, and any finite list
of points of it may be required to be among the ends. Lengthening the cut list is free: both
`EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in it. -/
theorem exists_isClean {C : Set Plane} (hC : IsPolygonal C) {a b : Plane} (ha : a ∈ C)
    (hb : b ∈ C) (hab : a ≠ b) (extra : List Plane) :
    ∃ Q : List Piece, IsClean Q C ∧ ∀ p ∈ extra, p ∈ C → ∃ R ∈ Q, p = R.1 ∨ p = R.2 := by
  obtain ⟨vs, rfl⟩ := hC
  have hnd : ∀ P ∈ segsOf vs, P.Nondeg := segsOf_nondeg vs
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  obtain ⟨pts, hEnds, hMeets⟩ := exists_cut_points (segsOf vs)
  refine ⟨overlayPieces (segsOf vs) (pts ++ extra), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [overlayPieces_cover, hcov]
  · exact overlayPieces_nondeg _ hnd
  · intro R hR S hS z hz
    exact overlayPieces_avoids hnd z
      (overlayPieces_ends_cut (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) R hR z hz)
      S hS
  · intro R hR S hS hRS x hx
    refine overlayPieces_disjoint_interiors hnd
      (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) (fun P hP Q hQ hPQ hne => ?_)
      hR hS hRS hx
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hP Q hQ hPQ hne
    exact ⟨u, v, huv, List.mem_append_left _ hu, List.mem_append_left _ hv⟩
  · -- A required point lies on some piece and is interior to none, hence is an end of one.
    intro p hp hpC
    have hpts : p ∈ pts ++ extra := List.mem_append_right _ hp
    have hpcov : p ∈ cover (overlayPieces (segsOf vs) (pts ++ extra)) := by
      rw [overlayPieces_cover, hcov]; exact hpC
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hpcov
    refine ⟨R, hR, ?_⟩
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids hnd p hpts R hR
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpR)

/-- A point of a piece is interior to it or one of its ends. -/
theorem mem_interior_or_end {R : Piece} {x : Plane} (hx : x ∈ R.seg) :
    x ∈ R.interior ∨ x = R.1 ∨ x = R.2 := by
  by_cases hcon : x = R.1 ∨ x = R.2
  · exact Or.inr hcon
  · push Not at hcon
    exact Or.inl (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hx)

/-- The open set that isolates one piece from the others: the union of the balls in which the
curve is that piece alone. -/
def nearPiece (C : Set Plane) (R : Piece) : Set Plane :=
  {y | ∃ x ∈ R.interior, ∃ r > 0, y ∈ ball x r ∧ ball x r ∩ C ⊆ R.seg}

theorem isOpen_nearPiece {C : Set Plane} {R : Piece} : IsOpen (nearPiece C R) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hx, r, hr, hyb, hsub⟩
  exact ⟨ball x r, fun z hz => ⟨x, hx, r, hr, hz, hsub⟩, isOpen_ball, hyb⟩

namespace IsClean

variable {Q : List Piece} {C : Set Plane} {R S : Piece} {x : Plane} (h : IsClean Q C)
include h

/-- **Two distinct clean pieces meet only at ends of the first.** This is `edges_meet`, before
the pieces have been put in cyclic order. -/
theorem seg_inter_subset (hR : R ∈ Q) (hS : S ∈ Q) (hRS : R ≠ S) :
    R.seg ∩ S.seg ⊆ {R.1, R.2} := by
  rintro z ⟨hzR, hzS⟩
  rcases mem_interior_or_end hzR with hz | hz
  · exfalso
    rcases mem_interior_or_end hzS with hz' | hz'
    · exact h.interiors R hR S hS hRS z hz hz'
    · exact h.ends S hS R hR z hz' hz
  · exact hz

theorem seg_subset (hR : R ∈ Q) : R.seg ⊆ C := by
  rw [← h.cover_eq]
  exact fun z hz => mem_cover hR hz

theorem mem_cover_of_mem (hz : x ∈ C) : x ∈ cover Q := by rw [h.cover_eq]; exact hz

/-- **The curve minus the ends is the disjoint union of the piece interiors.** -/
theorem diff_endSet_eq : C \ endSet Q = ⋃ R ∈ Q, R.interior := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hz.1)
    refine Set.mem_iUnion₂.2 ⟨R, hR, ?_⟩
    rcases mem_interior_or_end hzR with hz' | hz'
    · exact hz'
    · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz'⟩) hz.2
  · obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨h.seg_subset hR (openSegment_subset_segment ℝ _ _ hzR),
      fun ⟨S, hS, hz'⟩ => h.ends S hS R hR z hz' hzR⟩

/-- **Near an interior point the curve is that piece alone.** The other pieces are finitely many
closed sets missing the point: interior points are not shared, and an end of another piece
cannot be interior to this one. -/
theorem exists_ball_subset_seg (hR : R ∈ Q) (hx : x ∈ R.interior) :
    ∃ r > 0, ball x r ∩ C ⊆ R.seg := by
  have hmiss : ∀ S ∈ Q, S ≠ R → x ∉ S.seg := by
    intro S hS hSR hxS
    rcases mem_interior_or_end hxS with hz | hz
    · exact h.interiors S hS R hR hSR x hz hx
    · exact h.ends S hS R hR x hz hx
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {S : Piece | S ∈ Q ∧ S ≠ R}) (Q.finite_toSet.subset fun _ hS => hS.1)
    (P := fun S ε => ∀ y ∈ ball x ε, y ∉ S.seg)
    (fun _ _ _ _ hδε hP y hy => hP y (ball_subset_ball hδε hy))
    (fun S hS => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment S.1 S.2).isClosed.isOpen_compl x (hmiss S hS.1 hS.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzC⟩
  obtain ⟨S, hS, hzS⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hzC)
  by_cases hSR : S = R
  · exact hSR ▸ hzS
  · exact absurd hzS (hball S ⟨hS, hSR⟩ z hzb)

theorem interior_subset_nearPiece (hR : R ∈ Q) : R.interior ⊆ nearPiece C R := by
  intro y hy
  obtain ⟨r, hr, hsub⟩ := h.exists_ball_subset_seg hR hy
  exact ⟨y, hy, r, hr, mem_ball_self hr, hsub⟩

omit h in
theorem nearPiece_inter_diff (hR : R ∈ Q) : nearPiece C R ∩ (C \ endSet Q) ⊆ R.interior := by
  rintro z ⟨⟨y, hy, r, hr, hzb, hsub⟩, hzC, hzV⟩
  rcases mem_interior_or_end (hsub ⟨hzb, hzC⟩) with hz | hz
  · exact hz
  · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz⟩) hzV

/-- **A connected piece of the curve away from the ends lies inside a single piece.** The
`nearPiece` sets are honest open sets of the plane that trace out the pieces on the curve, so
`IsPreconnected` can be applied to them directly. -/
theorem preconnected_subset_interior {A : Set Plane} (hA : IsPreconnected A) (hA0 : A.Nonempty)
    (hAsub : A ⊆ C \ endSet Q) : ∃ R ∈ Q, A ⊆ R.interior := by
  obtain ⟨x₀, hx₀⟩ := hA0
  have hAint : A ⊆ ⋃ R ∈ Q, R.interior := by rw [← h.diff_endSet_eq]; exact hAsub
  obtain ⟨R, hR, hx₀R⟩ := Set.mem_iUnion₂.1 (hAint hx₀)
  refine ⟨R, hR, ?_⟩
  set W : Set Plane := ⋃ S ∈ {S : Piece | S ∈ Q ∧ S ≠ R}, nearPiece C S with hW
  have hWopen : IsOpen W := isOpen_biUnion fun _ _ => isOpen_nearPiece
  have hcover : A ⊆ nearPiece C R ∪ W := by
    intro z hz
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 (hAint hz)
    by_cases hSR : S = R
    · exact Or.inl (h.interior_subset_nearPiece hR (hSR ▸ hzS))
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨S, ⟨hS, hSR⟩, h.interior_subset_nearPiece hS hzS⟩)
  have hempty : ¬ (A ∩ (nearPiece C R ∩ W)).Nonempty := by
    rintro ⟨z, hzA, hzR, hzW⟩
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 hzW
    exact h.interiors R hR S hS.1 (Ne.symm hS.2) z (nearPiece_inter_diff hR ⟨hzR, hAsub hzA⟩)
      (nearPiece_inter_diff hS.1 ⟨hzS, hAsub hzA⟩)
  have hnotW : ¬ (A ∩ W).Nonempty := fun hv =>
    hempty (hA _ _ isOpen_nearPiece hWopen hcover ⟨x₀, hx₀, h.interior_subset_nearPiece hR hx₀R⟩ hv)
  intro z hz
  refine nearPiece_inter_diff hR ⟨?_, hAsub hz⟩
  exact (hcover hz).resolve_right fun hzW => hnotW ⟨z, hz, hzW⟩

end IsClean

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

section Gaps

variable {n : ℕ} {T : Finset ℝ} (hcard : T.card = n)

/-- The `i`-th parameter, in increasing order. -/
noncomputable def par (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  T.orderEmbOfFin hcard i

/-- The right end of the `i`-th gap: the next parameter, or `1` for the last gap. -/
noncomputable def parNext (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  if h : (i : ℕ) + 1 < n then T.orderEmbOfFin hcard ⟨(i : ℕ) + 1, h⟩ else 1

theorem par_mem (i : Fin n) : par T hcard i ∈ T := T.orderEmbOfFin_mem hcard i

theorem par_lt_par {i j : Fin n} (h : i < j) : par T hcard i < par T hcard j :=
  (T.orderEmbOfFin hcard).strictMono h

theorem par_lt_iff {i j : Fin n} : par T hcard i < par T hcard j ↔ i < j :=
  (T.orderEmbOfFin hcard).lt_iff_lt

theorem par_le_par {i j : Fin n} (h : i ≤ j) : par T hcard i ≤ par T hcard j :=
  (T.orderEmbOfFin hcard).monotone h

theorem exists_par_eq {s : ℝ} (hs : s ∈ T) : ∃ i : Fin n, par T hcard i = s := by
  have := T.range_orderEmbOfFin hcard
  rw [Set.ext_iff] at this
  exact (this s).2 hs

variable (hT : ∀ s ∈ T, s ∈ Ico (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ T)
include hcard hT h0

omit hT in
theorem par_card_pos : 0 < n := by
  rw [← hcard]
  exact Finset.card_pos.2 ⟨0, h0⟩

/-- The first parameter is `0`: the loop is at a vertex when it starts. -/
theorem par_zero : par T hcard ⟨0, par_card_pos hcard h0⟩ = 0 := by
  rw [par, Finset.orderEmbOfFin_zero hcard (par_card_pos hcard h0)]
  exact le_antisymm (Finset.min'_le _ _ h0)
    (Finset.le_min' _ _ _ fun s hs => (hT s hs).1)

omit h0 in
theorem parNext_le_one (i : Fin n) : parNext T hcard i ≤ 1 := by
  rw [parNext]
  split_ifs with hi
  · exact le_of_lt (hT _ (T.orderEmbOfFin_mem hcard _)).2
  · exact le_refl 1

omit h0 in
theorem par_lt_parNext (i : Fin n) : par T hcard i < parNext T hcard i := by
  rw [parNext]
  split_ifs with hi
  · exact par_lt_par hcard (by exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _) : i < ⟨(i : ℕ) + 1, hi⟩)
  · exact (hT _ (par_mem hcard i)).2

omit hT h0 in
/-- No parameter lies strictly inside a gap. -/
theorem notMem_of_mem_gap {i : Fin n} {s : ℝ} (hs : s ∈ Ioo (par T hcard i) (parNext T hcard i)) :
    s ∉ T := by
  intro hsT
  obtain ⟨j, rfl⟩ := exists_par_eq hcard hsT
  have hij : i < j := (par_lt_iff hcard).1 hs.1
  rw [parNext] at hs
  split_ifs at hs with hi
  · exact absurd hs.2 (not_lt.2 (par_le_par hcard (by exact Fin.mk_le_of_le_val hij)))
  · exact absurd j.isLt (by omega)

omit hT h0 in
/-- Distinct gaps are disjoint. -/
theorem gap_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Ioo (par T hcard i) (parNext T hcard i))
      (Ioo (par T hcard j) (parNext T hcard j)) := by
  -- One of the two comes first; its right end is at most the other's left end.
  have key : ∀ a b : Fin n, a < b → parNext T hcard a ≤ par T hcard b := by
    intro a b hab
    rw [parNext]
    split_ifs with ha
    · exact par_le_par hcard (Fin.mk_le_of_le_val hab)
    · exact absurd b.isLt (by omega)
  rw [Set.disjoint_left]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx.2 (key i j hlt)) (not_lt.2 hx'.1.le)
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx'.2 (key j i hlt)) (not_lt.2 hx.1.le)

omit h0 in
theorem gap_subset_Ico (i : Fin n) :
    Ioo (par T hcard i) (parNext T hcard i) ⊆ Ico (0 : ℝ) 1 := fun _ hs =>
  ⟨le_of_lt (lt_of_le_of_lt (hT _ (par_mem hcard i)).1 hs.1),
    lt_of_lt_of_le hs.2 (parNext_le_one hcard hT i)⟩

omit h0 in
theorem gapClosure_subset_I (i : Fin n) :
    Icc (par T hcard i) (parNext T hcard i) ⊆ I := by
  intro s hs
  exact ⟨le_trans (hT _ (par_mem hcard i)).1 hs.1, le_trans hs.2 (parNext_le_one hcard hT i)⟩

/-- **The gaps cover `[0, 1)` minus the parameters.** The gap containing `s` starts at the
largest parameter below `s`. -/
theorem exists_mem_gap {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hsT : s ∉ T) :
    ∃ i : Fin n, s ∈ Ioo (par T hcard i) (parNext T hcard i) := by
  classical
  have hn : 0 < n := par_card_pos hcard h0
  -- The gap containing `s` starts at the largest parameter below it.
  obtain ⟨i₀, hi₀le, hi₀max⟩ : ∃ i₀ : Fin n, par T hcard i₀ ≤ s ∧
      ∀ j : Fin n, par T hcard j ≤ s → j ≤ i₀ := by
    have hSne : (Finset.univ.filter fun i : Fin n => par T hcard i ≤ s).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [par_zero hcard hT h0]; exact hs.1⟩⟩
    exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
      fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
  refine ⟨i₀, lt_of_le_of_ne hi₀le fun he => hsT (he ▸ par_mem hcard _), ?_⟩
  rw [parNext]
  split_ifs with hi
  · by_contra hcon
    push Not at hcon
    exact absurd (hi₀max ⟨(i₀ : ℕ) + 1, hi⟩ hcon)
      (not_le.2 (Fin.lt_def.2 (Nat.lt_succ_self _)))
  · exact hs.2

end Gaps

/-- A closed interval is its interior together with its two ends. -/
theorem Icc_eq_Ioo_union_ends {a b : ℝ} (hab : a ≤ b) : Icc a b = Ioo a b ∪ {a, b} := by
  ext x
  simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inl rfl)
    · rcases eq_or_lt_of_le h2 with rfl | h2'
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨h1', h2'⟩
  · rintro (⟨h1, h2⟩ | rfl | rfl)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩

/-- Two points of a nondegenerate pair, each known to be one of two given points, exhaust
them. -/
theorem pair_eq_of_mem_pair {a b p q : Plane} (hab : a ≠ b) (ha : a = p ∨ a = q)
    (hb : b = p ∨ b = q) : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-- The successor in `ZMod n`, read as a numeral below `n`. -/
theorem zmod_val_succ {n : ℕ} (hn : 1 < n) (j : ZMod n) :
    (j + 1).val = if j.val + 1 < n then j.val + 1 else 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have h1 : (1 : ZMod n).val = 1 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
    exact ZMod.val_cast_of_lt hn
  rw [ZMod.val_add, h1]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hj : j.val + 1 = n := by have := ZMod.val_lt j; omega
    rw [hj, Nat.mod_self]

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-- **A polygonal Jordan curve is the carrier of a cyclic vertex list.** -/
theorem exists_prePolygon_of_isJordanCurve {C : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) : ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C := by
  classical
  obtain ⟨f, hf, hfC⟩ := hJ
  -- Two distinct points of `C`, so that the clean presentation does not collapse.
  have hmemC : ∀ s ∈ I, f s ∈ C := fun s hs => hfC ▸ ⟨s, hs, rfl⟩
  have h0C : f 0 ∈ C := hmemC 0 zero_mem_I
  have hhC : f (1 / 2) ∈ C := hmemC _ ⟨by norm_num, by norm_num⟩
  have hne : f 0 ≠ f (1 / 2) := fun he =>
    absurd (hf.injOn ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, by norm_num⟩ he) (by norm_num)
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hP h0C hhC hne [f 0]
  obtain ⟨R₀, hR₀, hR₀end⟩ := hextra (f 0) (List.mem_singleton_self _) h0C
  have hV₀ : f 0 ∈ endSet Q := ⟨R₀, hR₀, hR₀end⟩
  -- Every point of the curve is reached before the loop closes.
  have hsurj : ∀ z ∈ C, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    rw [← hfC] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨0, ⟨le_refl 0, by norm_num⟩, hf.closes⟩
    · exact ⟨s, ⟨hs.1, hlt⟩, rfl⟩
  -- The parameters at which the loop is at an end of a piece.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hf.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, hV₀⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · rw [← hf.closes]; exact hV₀
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i =>
    ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hf.continuousOn.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ C \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemC s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hf.continuousOn (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (C \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hf.injOn (hIoo j ht) (hIoo i hs) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the curve away from the ends of the pieces.
  have hcov : (⋃ i, G i) = C \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz.1
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (hpcsub i)
    set W : Set Plane := ⋃ j ∈ ({i}ᶜ : Set (Fin n)), Z j with hW
    have hWclosed : IsClosed W :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => (hZcompact j).isClosed
    have hAdiff : (pc i).interior ⊆ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]
      exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
    have hAZ : (pc i).interior ⊆ Z i ∪ W := by
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hAdiff hz)
      by_cases hji : j = i
      · exact Or.inl ((hZeq i) ▸ Or.inl (hji ▸ hj))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, (hZeq j) ▸ Or.inl hj⟩)
    have hGW : ∀ z ∈ G i, z ∉ W := by
      intro z hz hzW
      obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
      have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hGdiff i hz⟩
      exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j (Ne.symm hji)) z ⟨hz, this⟩
    have hcover2 : (pc i).interior ⊆ Wᶜ ∪ (Z i)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · refine Or.inr fun hzZ => ?_
        exact hGW z ((hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩) hzW
      · exact Or.inl hzW
    have hnone : ¬ ((pc i).interior ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
      rintro ⟨z, hz, hzW, hzZ⟩
      rcases hAZ hz with h | h
      exacts [hzZ h, hzW h]
    have hconv : IsPreconnected ((pc i).interior) :=
      (convex_openSegment _ _).isPreconnected
    obtain ⟨z₀, hz₀⟩ := hGne i
    have hAu : ((pc i).interior ∩ Wᶜ).Nonempty := ⟨z₀, hpcsub i hz₀, hGW z₀ hz₀⟩
    have hnotv : ¬ ((pc i).interior ∩ (Z i)ᶜ).Nonempty := fun hv =>
      hnone (hconv _ _ hWclosed.isOpen_compl (hZcompact i).isClosed.isOpen_compl hcover2 hAu hv)
    intro z hz
    have hzZ : z ∈ Z i := by
      by_contra hzZ
      exact hnotv ⟨z, hz, hzZ⟩
    exact (hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R := by
    intro R hR
    have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]; exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hxd)
    refine ⟨i, ?_⟩
    by_contra hne'
    exact hQ.interiors (pc i) (hpcQ i) R hR hne' _ (hpceq i ▸ hi) hx
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    have hnd : (pc i).1 ≠ (pc i).2 := hQ.nondeg _ (hpcQ i)
    have hclosure : (pc i).seg ⊆ Z i := by
      have hcl : closure ((pc i).interior) ⊆ Z i := by
        rw [hpceq i]
        exact closure_minimal (fun z hz => (hZeq i) ▸ Or.inl hz) (hZcompact i).isClosed
      rwa [Piece.interior, closure_openSegment] at hcl
    have hmem : ∀ z, z = (pc i).1 ∨ z = (pc i).2 → z = f (tp i) ∨ z = f (nx i) := by
      intro z hz
      have hzseg : z ∈ (pc i).seg := by
        rcases hz with rfl | rfl
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hZeq i) ▸ hclosure hzseg with hzG | hzE
      · exfalso
        rw [← hpceq i] at hzG
        rcases hz with rfl | rfl
        exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
    exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  have hfne : ∀ i, f (tp i) ≠ f (nx i) := by
    intro i he
    refine hQ.nondeg _ (hpcQ i) ?_
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  -- There are at least three parameters.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt2 | hge
    · exfalso
      have hcond : ¬ ((⟨0, hn0⟩ : Fin n) : ℕ) + 1 < n :=
        fun hc => absurd (lt_of_le_of_lt (Nat.le_add_left 1 _) hc) (by omega)
      have hnx0 : nx ⟨0, hn0⟩ = 1 := by rw [hnx, parNext, dif_neg hcond]
      exact hfne ⟨0, hn0⟩ (by rw [htp0, hnx0]; exact hf.closes)
    · exact hge
  haveI : NeZero n := ⟨by omega⟩
  -- The cyclic vertex list: the ends, in the order the loop reaches them.
  set w : ZMod n → Plane := fun j => f (tp ⟨j.val, ZMod.val_lt j⟩) with hw
  have hwsucc : ∀ j : ZMod n, w (j + 1) = f (nx ⟨j.val, ZMod.val_lt j⟩) := by
    intro j
    have hjlt := ZMod.val_lt j
    by_cases hj : j.val + 1 < n
    · have hval : (j + 1).val = j.val + 1 := by rw [zmod_val_succ (by omega) j, if_pos hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨j.val + 1, hj⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [hnx, parNext, dif_pos (show (⟨j.val, hjlt⟩ : Fin n).val + 1 < n from hj)]
      rfl
    · have hval : (j + 1).val = 0 := by rw [zmod_val_succ (by omega) j, if_neg hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨0, hn0⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [htp0, hnx, parNext, dif_neg (show ¬ ((⟨j.val, hjlt⟩ : Fin n).val + 1 < n) from hj)]
      exact hf.closes
  have hedgeq : ∀ j : ZMod n,
      segment ℝ (w j) (w (j + 1)) = (pc ⟨j.val, ZMod.val_lt j⟩).seg := by
    intro j
    rw [hwsucc j, hpcseg]
  have hwinj : Function.Injective w := by
    intro j k hjk
    simp only [hw] at hjk
    have h1 := hf.injOn (hTle _ (par_mem hcard ⟨j.val, ZMod.val_lt j⟩))
      (hTle _ (par_mem hcard ⟨k.val, ZMod.val_lt k⟩)) hjk
    exact ZMod.val_injective _ (congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1))
  have hwmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i j hij
    rw [hedgeq i, hedgeq j]
    have hne' : pc ⟨i.val, ZMod.val_lt i⟩ ≠ pc ⟨j.val, ZMod.val_lt j⟩ := fun he =>
      hij (ZMod.val_injective _ (congrArg Fin.val (hpcinj he)))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i.val, ZMod.val_lt i⟩) := rfl
    rcases hends ⟨i.val, ZMod.val_lt i⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwsucc i]
    · rw [h1, h2, ← hwi, ← hwsucc i, Set.pair_comm]
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hlt3 | hge
    · exfalso
      have hn2' : n = 2 := by omega
      have hone : (1 : ZMod n).val = 1 := by
        rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
        exact ZMod.val_cast_of_lt (by omega)
      have h01 : (0 : ZMod n) ≠ 1 := by
        intro he
        have hv : (0 : ZMod n).val = (1 : ZMod n).val := by rw [he]
        rw [ZMod.val_zero, hone] at hv
        omega
      have hsucc1 : (1 : ZMod n) + 1 = 0 := by
        refine ZMod.val_injective _ ?_
        rw [zmod_val_succ (by omega) 1, hone, if_neg (by omega), ZMod.val_zero]
      have hw01 : w 0 ≠ w 1 := fun he => h01 (hwinj he)
      obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne hw01
      have hmem := hwmeet 0 1 h01
        ⟨by rw [zero_add]; exact hp, by rw [hsucc1, segment_symm]; exact hp⟩
      rw [zero_add] at hmem
      rcases hmem with h | h
      exacts [hp1 h, hp2 h]
    · exact hge
  -- Assemble.
  refine (PrePolygon.exists_prePolygon hn3 w hwinj hwmeet).imp fun m hm => hm.imp fun P hP => ?_
  rw [hP, ← hQ.cover_eq]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) ?_
  · rw [hedgeq j]
    exact fun z hz => mem_cover (hpcQ _) hz
  · rw [cover]
    refine Set.iUnion₂_subset fun R hR => ?_
    obtain ⟨i, rfl⟩ := hpcsurj R hR
    have hfin : (⟨((i.val : ℕ) : ZMod n).val, ZMod.val_lt _⟩ : Fin n) = i :=
      Fin.val_injective (ZMod.val_cast_of_lt i.isLt)
    refine le_trans (le_of_eq ?_)
      (Set.subset_iUnion (fun j : ZMod n => segment ℝ (w j) (w (j + 1))) ((i.val : ℕ) : ZMod n))
    rw [hedgeq, hfin]

/-! ## The realization theorem -/

/-- **Every simple closed polygonal curve is the carrier of a `ClosedPolygon`.** This is the
blueprint's set-level notion — `IsJordanCurve` together with `IsPolygonal`, no condition on
vertices — matched with the presentation the development works with. -/
theorem exists_closedPolygon {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar'⟩ := PrePolygon.exists_closedPolygon_of_prePolygon m P
  exact ⟨m', P', by rw [hcar', hcar]⟩

/-! ## Corners

A realization cannot put a vertex wherever it likes: `corner` forbids a vertex at which the
curve runs straight through. The points that *must* be vertices are exactly the ones at which
it does not, and this is what a consumer needing a named point to be a vertex has to check. -/

/-! ## The two arcs of a splitting

`ClosedPolygon.arc a k` and `ClosedPolygon.arc (a + k) (m + 3 - k)` are what a consumer tracking
a decomposition of the curve has to be handed. This section says what they are: two arcs between
the two cut vertices, covering the curve and meeting exactly there. -/

/-! ## The two-arc decomposition is unique

Two points cut a Jordan curve into two arcs, and *only* into those two: the interior of any arc
of the curve between them is connected and misses both, so it lies on one side of any other such
splitting. Without this a realization could name two arcs and still not be known to name the two
arcs a consumer started from. -/

/-- The interior of an arc — the arc less its two endpoints — is connected and nonempty. The
paired form the uniqueness argument below destructures; both halves are in
`Schoenflies/Subarc.lean`, which is where the shared set identity `A ∖ {p, q} = f '' Ioo 0 1`
lives. -/
theorem IsArcBetween.preconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) ∧ (A \ {p, q}).Nonempty :=
  ⟨h.isPreconnected_diff, h.nonempty_diff⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/FaceCyclesProof.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

open Metric _root_.Set unitInterval
namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-- **An arc between two points contained in an arc between the same two points is all of
it.** Removing an interior point of the ambient arc splits it into two relatively open halves;
a connected subset containing both ends would have to meet both and therefore their empty
intersection. -/
theorem IsArcBetween.eq_of_subset {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hBA : B ⊆ A) : B = A := by
  obtain ⟨f, hc, hi, hAim, hf0, hf1⟩ := hA
  refine Set.Subset.antisymm hBA fun x hx => ?_
  by_contra hxB
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ I, f t = x := by rw [← hAim] at hx; exact hx
  -- The parameter is strictly inside, since both ends belong to `B`.
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | h
    · exact absurd (hf0 ▸ hB.left_mem) hxB
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact absurd (hf1 ▸ hB.right_mem) hxB
    · exact h
  obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hc hi (U := Iio t) isOpen_Iio
  obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hc hi (U := Ioi t) isOpen_Ioi
  rw [hAim] at hV₁ hV₂
  -- The two halves are disjoint, by injectivity of the parametrisation.
  have hdisj : (A ∩ (V₁ ∩ V₂)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z ⟨hzA, hz₁, hz₂⟩ => ?_
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzA⟩
    obtain ⟨r, hr, hrs⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzA⟩
    have hrs' : r = s := hi hr.2 hs.2 hrs
    have h1 : t < r := hr.1
    have h2 : s < t := hs.1
    rw [hrs'] at h1
    linarith
  -- `B` misses the removed point, so it lies in the union of the two halves.
  have hsub : B ⊆ V₁ ∪ V₂ := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by
      have := hBA hz; rw [← hAim] at this; exact this
    have hst : s ≠ t := by rintro rfl; exact hxB hz
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inl (by
        have : f s ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
    · exact Or.inr (by
        have : f s ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
  have hp₁ : (B ∩ V₁).Nonempty := by
    refine ⟨p, hB.left_mem, ?_⟩
    have : f 0 ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨0, ⟨ht0, zero_mem_I⟩, rfl⟩
    exact hf0 ▸ this.1
  have hq₂ : (B ∩ V₂).Nonempty := by
    refine ⟨q, hB.right_mem, ?_⟩
    have : f 1 ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨1, ⟨ht1, one_mem_I⟩, rfl⟩
    exact hf1 ▸ this.1
  obtain ⟨z, hzB, hz⟩ :=
    hB.isArc.isConnected.isPreconnected V₁ V₂ hV₁open hV₂open hsub hp₁ hq₂
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨hBA hzB, hz⟩

/-! ## Concatenating polylines -/

/-- **Appending two vertex lists joins their carriers by one segment.** The segment runs from
the last vertex of the first list to the first vertex of the second, and is degenerate — hence
contributes nothing — exactly when the two lists already share that vertex. -/
theorem poly_append_join : ∀ {as : List Plane} (h₁ : as ≠ []) {bs : List Plane} (h₂ : bs ≠ []),
    poly (as ++ bs) = poly as ∪ segment ℝ (as.getLast h₁) (bs.head h₂) ∪ poly bs
  | [], h₁, _, _ => absurd rfl h₁
  | [x], _, bs, h₂ => by
    rw [List.singleton_append, poly_cons_of_ne_nil h₂, poly_singleton,
      List.getLast_singleton]
    rw [Set.union_assoc, Set.singleton_union]
    exact (Set.insert_eq_self.2
      (Set.mem_union_left _ (left_mem_segment ℝ x (bs.head h₂)))).symm
  | x :: y :: as, _, bs, h₂ => by
    have hne : (y :: as) ≠ [] := List.cons_ne_nil _ _
    rw [List.cons_append, poly_cons_of_ne_nil (by simp), poly_cons_cons,
      poly_append_join hne h₂, List.head_append_of_ne_nil hne,
      List.getLast_cons hne]
    ac_rfl

/-- **Two polylines meeting end to head concatenate.** The joining segment collapses to the
shared vertex. -/
theorem poly_append_of_eq {as bs : List Plane} (h₁ : as ≠ []) (h₂ : bs ≠ [])
    (h : as.getLast h₁ = bs.head h₂) : poly (as ++ bs) = poly as ∪ poly bs := by
  rw [poly_append_join h₁ h₂, h, segment_same, Set.union_assoc, Set.singleton_union,
    Set.insert_eq_self.2 (head_mem_poly h₂)]

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-- **Cutting inside one component.** The component of `z` in `S ∖ P` sees only the component
of `z` in `S`. -/
theorem connectedComponentIn_diff (S P : Set Plane) (z : Plane) :
    connectedComponentIn (S \ P) z = connectedComponentIn (connectedComponentIn S z \ P) z := by
  by_cases hz : z ∈ S \ P
  · have hcomp : connectedComponentIn (S \ P) z ⊆ connectedComponentIn S z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans Set.sdiff_subset)
    have hzR : z ∈ connectedComponentIn (connectedComponentIn S z \ P) z :=
      mem_connectedComponentIn ⟨mem_connectedComponentIn hz.1, hz.2⟩
    refine Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) fun w hw =>
          ⟨hcomp hw, (connectedComponentIn_subset _ _ hw).2⟩)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzR fun w hw => ?_)
    have hw' : w ∈ connectedComponentIn S z \ P := connectedComponentIn_subset _ _ hw
    exact ⟨connectedComponentIn_subset _ _ hw'.1, hw'.2⟩
  · rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty]
    rintro ⟨hw, hwP⟩
    exact hz ⟨connectedComponentIn_subset _ _ hw, hwP⟩

/-! ## A polygonal arc is a polyline running from one end to the other -/

/-- **A polygonal arc is `poly` of a vertex list running from one of its ends to the other.**
`Schoenflies.exists_simple_poly_of_isPolygonal` produces a simple polygonal arc *inside* the
set between the two points; being an arc between the same two ends it is the whole of it, by
`Schoenflies.IsArcBetween.eq_of_subset`. -/
theorem IsArcBetween.exists_poly_eq {A : Set Plane} {p q : Plane} (harc : IsArcBetween A p q)
    (hpoly : IsPolygonal A) (hpq : p ≠ q) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = p ∧ vs.getLast h = q ∧ poly vs = A := by
  obtain ⟨vs, hvs, hhead, hlast, hsub, hsubarc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly harc.isArc.isConnected.isPreconnected hpq
      harc.left_mem harc.right_mem
  exact ⟨vs, hvs, hhead, hlast, harc.eq_of_subset hsubarc hsub⟩

end Schoenflies

section
/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

open _root_.Graph in
/-- **Two paths meeting only at the junction concatenate.** The freshness clause of the joined
path is the freshness of the first together with the meeting condition: a vertex the second
half visits and the first half departs from would be the junction, which the first half has
already arrived at. -/
theorem _root_.Graph.IsPath.append : ∀ {u w v : α} {W₁ W₂ : List β}, G.IsPath u W₁ w → G.IsPath w W₂ v →
    (∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices w W₂ → y = w) → G.IsPath u (W₁ ++ W₂) v := by
  intro u w v W₁ W₂ h₁
  induction h₁ with
  | nil hx => intro h₂ _; simpa using h₂
  | @cons u w₀ w e W hl hW hfresh ih =>
    intro h₂ hmeet
    refine List.cons_append .. ▸ IsPath.cons hl
      (ih h₂ fun y hy hy₂ => hmeet y (mem_walkVertices_cons_of_mem hl hy) hy₂) fun hmem => ?_
    -- The departure vertex is fresh: the only new vertices are those of the second half, and
    -- one of those shared with the first half would be the junction, already visited.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · have := hmeet u mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact hfresh (this ▸ hW.target_mem_walkVertices)

open _root_.Graph in
/-- **A path splits at any vertex it visits, and the two halves meet only there.** This is
`Graph.IsPath.split` with the meeting condition in place of its weaker last clause. -/
theorem _root_.Graph.IsPath.split_meet (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      ∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices x W₂ → y = x := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', fun y hy _ => by simpa using hy⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh,
        fun y hy _ => by simpa using hy⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, hmeet⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem),
      h₂, fun y hy hy₂ => ?_⟩
    -- A vertex of the extended prefix is either the new source — which the far half never
    -- visits, by freshness — or one the induction hypothesis already handles.
    rcases mem_walkVertices_cons hl hy with rfl | hy'
    · exfalso
      rcases mem_walkVertices_iff.1 hy₂ with rfl | hcov
      · exact hfresh (walkVertices_mono hsub₁ h₁.target_mem_walkVertices)
      · exact hfresh (mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov))
    · exact hmeet y hy' hy₂

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

open _root_.Graph in
/-- **The complementary arc of a cut cycle**, together with the two facts a geometric consumer
needs: that the two arcs between them use every edge of the cycle exactly once, and that they
visit no common vertex but the two cut points. -/
theorem _root_.Graph.IsCycleThrough.split_aux {G : Graph α β} {e : β} {u v c d : α} {D X Y Z : List β}
    (hc : G.IsCycleThrough e u v D) (hD : D = X ++ (Y ++ Z)) (hX : G.IsPath u X c)
    (hY : G.IsPath c Y d) (hZ : G.IsPath d Z v) (hcd : c ≠ d)
    (hM1 : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices c (Y ++ Z) → y = c)
    (hM2 : ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d Z → y = d) :
    G.IsPath d (Z ++ e :: X) c ∧ (Y ++ (Z ++ e :: X)).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d (Z ++ e :: X) → y = c ∨ y = d := by
  have hZsub : G.walkVertices d Z ⊆ G.walkVertices c (Y ++ Z) := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
    · exact walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono
        (List.subset_append_right _ _) hcov)
  -- A vertex of the first stretch that the last stretch also reaches would merge the two cuts.
  have hclash : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices d Z → False := by
    intro y hy hyZ
    obtain rfl : y = c := hM1 y hy (hZsub hyZ)
    exact hcd (hM2 y mem_walkVertices_self hyZ)
  have hvZ : v ∈ G.walkVertices d Z := hZ.target_mem_walkVertices
  have hvX : v ∉ G.walkVertices u X := fun hh => hclash v hh hvZ
  -- The closing edge, then the first stretch, is a path from the far end back to the first cut.
  have hePath : G.IsPath v (e :: X) c := IsPath.cons hc.isLink.symm hX hvX
  -- Its vertices, other than `v` itself, are those of the first stretch.
  have hcons : ∀ y ∈ G.walkVertices v (e :: X), y = v ∨ y ∈ G.walkVertices u X := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
    · exact Or.inl rfl
    rcases List.mem_cons.1 hg with rfl | hg'
    · rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
      · exact Or.inr mem_walkVertices_self
      · exact Or.inl rfl
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨g, hg', hinc⟩)
  refine ⟨hZ.append hePath fun y hy hy' => ?_, ?_, fun y hy hy' => ?_⟩
  · rcases hcons y hy' with rfl | hyX
    · rfl
    · exact absurd hyX fun hh => hclash y hh hy
  · subst hD
    rw [show Y ++ (Z ++ e :: X) = (Y ++ Z) ++ (e :: X) by rw [List.append_assoc]]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)
  · -- A vertex on both arcs is on the last stretch — hence the second cut — or on the first,
    -- hence the first cut.
    rcases mem_walkVertices_iff.1 hy' with rfl | hcov
    · exact Or.inr rfl
    rw [coveredVertices_append] at hcov
    rcases hcov with hcovZ | hcovE
    · exact Or.inr (hM2 y hy (mem_walkVertices_of_mem_covered hcovZ))
    · rcases hcons y (mem_walkVertices_of_mem_covered hcovE) with rfl | hyX
      · exact Or.inr (hM2 y hy hvZ)
      · exact Or.inl (hM1 y hyX (walkVertices_mono (List.subset_append_left _ _) hy))

open _root_.Graph in
/-- **A cycle cut at two of its vertices is two paths between them.** The two arcs use every
edge of the cycle exactly once — that is what the permutation says — and they have no vertex in
common but the two cut points. This is the combinatorial half of "the ear is a crosscut of the
face": the geometric half reads the two arcs of the Jordan curve off it. -/
theorem _root_.Graph.IsCycleThrough.split_at {G : Graph α β} {e : β} {u v a b : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (ha : a ∈ G.walkVertices u D) (hb : b ∈ G.walkVertices u D)
    (hab : a ≠ b) :
    ∃ D₁ D₂ : List β, G.IsPath a D₁ b ∧ G.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hc.isPath.split_meet ha
  -- The second cut point lies on one of the two stretches the first one made.
  have hcases : b ∈ G.walkVertices a Q ∨ b ∈ G.walkVertices u P := by
    rw [hPQ] at hb
    rcases mem_walkVertices_iff.1 hb with rfl | hcov
    · exact Or.inr mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (mem_walkVertices_of_mem_covered h)
    · exact Or.inl (mem_walkVertices_of_mem_covered h)
  rcases hcases with hbQ | hbP
  · -- `b` comes after `a`: cut the far stretch at `b`.
    obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hbQ
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P) (Y := Q₁) (Z := Q₂)
      (by rw [hPQ, hQ12]) hP hQ1 hQ2 hab (by rw [← hQ12]; exact hM1) hM2
    exact ⟨Q₁, Q₂ ++ e :: P, hQ1, hpath, hperm, hmeet⟩
  · -- `b` comes before `a`: cut the near stretch at `b`, and the two roles are exchanged.
    obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hbP
    have hP1sub : G.walkVertices u P₁ ⊆ G.walkVertices u P :=
      walkVertices_mono (by rw [hP12]; exact List.subset_append_left _ _)
    have hP2sub : G.walkVertices b P₂ ⊆ G.walkVertices u P := by
      intro y hy
      rcases mem_walkVertices_iff.1 hy with rfl | hcov
      · exact hbP
      · exact mem_walkVertices_of_mem_covered
          (coveredVertices_mono (by rw [hP12]; exact List.subset_append_right _ _) hcov)
    have hM1' : ∀ y ∈ G.walkVertices u P₁, y ∈ G.walkVertices b (P₂ ++ Q) → y = b := by
      intro y hy hy'
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · rfl
      rw [coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 y hy (mem_walkVertices_of_mem_covered h)
      · -- A vertex both stretches of the near half and the far half reach merges the two cuts.
        exfalso
        obtain rfl : y = a := hM1 y (hP1sub hy) (mem_walkVertices_of_mem_covered h)
        exact hab (hM2 y hy hP2.target_mem_walkVertices)
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P₁) (Y := P₂) (Z := Q)
      (by rw [hPQ, hP12, List.append_assoc]) hP1 hP2 hQ (Ne.symm hab) hM1'
      fun y hy hy' => hM1 y (hP2sub hy) hy'
    refine ⟨Q ++ e :: P₁, P₂, hpath, hP2, List.perm_append_comm.trans hperm, fun y hy hy' => ?_⟩
    exact (hmeet y hy' hy).symm

/-! ### Splicing an ear onto an arc

The blueprint's "the crosscut replaces `F` by exactly two regions, both bounded by cycles": the
two new cycles are the two arcs of the old one, each closed up by the ear. This is the
combinatorial construction of one of them. -/

open _root_.Graph in
/-- Incidence along edges of a subgraph is the same in the subgraph as in the graph, so the
vertices a walk visits do not depend on which of the two it is read in. -/
theorem _root_.Graph.coveredVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.coveredVertices W = H.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, (hHG.isLink_iff (hW g hg)).2 hy⟩
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, hy.mono hHG⟩

open _root_.Graph in
theorem _root_.Graph.walkVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.walkVertices u W = H.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_congr_of_le hHG hW]

open _root_.Graph in
/-- **The cycle an ear splices onto an arc of the old cycle.** The closed walk runs along the
arc and back along the ear; presented as `Graph.IsCycleThrough`, its named edge is the ear's
first, and its detour is the arc followed by the rest of the ear reversed. -/
theorem _root_.Graph.exists_spliced_cycle {B G : Graph α β} (hBG : B ≤ G) {a b : α} {D₁ D' : List β}
    (hD1 : B.IsPath a D₁ b) (hear : G.IsPath a D' b) (hab : a ≠ b)
    (hnew : ∀ g ∈ D', g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B)) :
    ∃ (f : β) (x y : α) (T : List β),
      (B.union (G.pathGraphOf a D')).IsCycleThrough f x y T ∧ (f :: T).Perm (D₁ ++ D') := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, D' = f :: T := by
    cases D' with
    | nil => exact absurd hear.isWalk.eq_of_nil hab
    | cons f T => exact ⟨f, T, rfl⟩
  obtain ⟨w, hl, hT, hfresh⟩ :
      ∃ w, G.IsLink f a w ∧ G.IsPath w T b ∧ a ∉ G.walkVertices w T := by
    cases hear with
    | cons hl hT hfr => exact ⟨_, hl, hT, hfr⟩
  set P := G.pathGraphOf a (f :: T) with hP
  have hPG : P ≤ G := pathGraphOf_le hear.isWalk
  have hcompat : B.Compatible P := Compatible.of_le_le hBG hPG
  have hPB : P ≤ B.union P := hcompat.right_le_union
  have hBB : B ≤ B.union P := left_le_union _ _
  have hedges : ∀ g ∈ T, g ∈ E(P) := fun g hg => by
    rw [pathGraphOf_edgeSet hear.isWalk]; exact List.mem_cons_of_mem _ hg
  -- The ear's tail, run backwards, is a path of the enlarged graph from the far end.
  have hTrev : (B.union P).IsPath b T.reverse w := by
    refine ((hT.reverse.anti hPG ?_ ?_).mono hPB)
    · rw [pathGraphOf_vertexSet]; exact hear.isWalk.target_mem_walkVertices
    · intro g hg; exact hedges g (List.mem_reverse.1 hg)
  have hD1' : (B.union P).IsPath a D₁ b := hD1.mono hBB
  have hTedges : ∀ g ∈ T.reverse, g ∈ E(P) := fun g hg => hedges g (List.mem_reverse.1 hg)
  have hcovP : ∀ W' : List β, (∀ g ∈ W', g ∈ E(P)) →
      (B.union P).coveredVertices W' = G.coveredVertices W' := by
    intro W' hW'
    rw [coveredVertices_congr_of_le hPB hW', ← coveredVertices_congr_of_le hPG hW']
  -- The arc and the ear's tail meet only at the ear's far end: a common vertex lies in the old
  -- subgraph, so the ear's freshness clause makes it one of the ear's two ends, and the source
  -- is not one the rest of the ear visits.
  have hmeet : ∀ y ∈ (B.union P).walkVertices a D₁, y ∈ (B.union P).walkVertices b T.reverse →
      y = b := by
    intro y hy hy'
    have hyB : y ∈ V(B) := by
      rw [walkVertices_congr_of_le hBB (fun g hg => hD1.edge_mem hg)] at hy
      exact hD1.isWalk.walkVertices_subset hy
    have hy'' : y = b ∨ y ∈ G.coveredVertices T := by
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · exact Or.inl rfl
      · rw [hcovP _ hTedges, coveredVertices_reverse] at hcov
        exact Or.inr hcov
    rcases hy'' with rfl | hcov
    · rfl
    have hyD : y ∈ G.walkVertices a (f :: T) :=
      mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
    by_contra hyb
    obtain rfl : y = a := by
      by_contra hya
      exact hint y hyD hya hyb hyB
    exact hfresh (mem_walkVertices_of_mem_covered hcov)
  refine ⟨f, a, w, D₁ ++ T.reverse, ⟨?_, hD1'.append hTrev hmeet, ?_⟩, ?_⟩
  · exact (pathGraphOf_isLink.2 ⟨List.mem_cons_self, hl, mem_walkVertices_self,
      mem_walkVertices_of_mem_covered ⟨f, List.mem_cons_self, hl.inc_right⟩⟩).mono hPB
  · -- The ear's first edge is on neither the arc — it is not an edge of the old subgraph at
    -- all — nor the rest of the ear, which is a path.
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact hnew f List.mem_cons_self (hD1.edge_mem h)
    · exact (List.nodup_cons.1 hear.nodup).1 (List.mem_reverse.1 h)
  · exact ((List.reverse_perm T).append_left D₁).cons f |>.trans List.perm_middle.symm

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

open _root_.Graph in
/-- Going round the cycle the other way: the edge, then the detour, is a closed walk at the
edge's far end. This is the walk whose edge list is `e :: D`, the list every statement about
the realisation of a cycle is phrased with. -/
theorem _root_.Graph.IsCycleThrough.isWalk_cons {α : Type*} {G : Graph α β} {e : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) : G.IsWalk v (e :: D) v :=
  IsWalk.cons hc.isLink.symm hc.isPath.isWalk

open _root_.Graph in
/-- **The realisation of a cycle of a polygonal plane graph is a separating Jordan curve.**
`Schoenflies.IsSeparating` is Definition 2.4: the complement has exactly two regions, one
bounded and one unbounded, each with the curve as its boundary. -/
theorem _root_.Graph.IsDrawing.cycle_isSeparating (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : IsSeparating (edgesCover drawing (e :: D)) := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon (h.cycle_isJordanCurve hc)
    (h.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _))
  exact hP ▸ P.isSeparating_carrier

/-! ## What a subgraph spanned by a walk occupies -/

open _root_.Graph in
/-- An end of an edge lies on that edge's arc. -/
theorem _root_.Graph.IsDrawing.inc_mem_edgeArc (h : IsDrawing G drawing) {x : Plane} (hinc : G.Inc e x) :
    x ∈ edgeArc drawing e := by
  obtain ⟨y, hy⟩ := hinc
  exact (h.edge_isArcBetween hy).left_mem

open _root_.Graph in
/-- **The subgraph spanned by a nonempty walk occupies exactly what the walk draws.** Its
vertices are ends of its edges, so they add nothing to the union of the edge arcs. -/
theorem _root_.Graph.IsDrawing.pointSet_pathGraphOf (h : IsDrawing G drawing) (hW : G.IsWalk u W v)
    (hne : W ≠ []) : pointSet (G.pathGraphOf u W) drawing = edgesCover drawing W := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, W = f :: T := by
    cases W with
    | nil => exact absurd rfl hne
    | cons f T => exact ⟨f, T, rfl⟩
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · -- Every vertex the walk visits is an end of one of its edges.
    intro x hx
    rw [pathGraphOf_vertexSet] at hx
    rcases mem_walkVertices_iff.1 hx with rfl | ⟨g, hg, hinc⟩
    · cases hW with
      | cons hl _ => exact mem_edgesCover List.mem_cons_self (h.inc_mem_edgeArc hl.inc_left)
    · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)
  · refine Set.iUnion₂_subset fun g hg => ?_
    rw [pathGraphOf_edgeSet hW] at hg
    exact fun z hz => mem_edgesCover hg hz
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
    refine edgeArc_subset_pointSet ?_ hzg
    rw [pathGraphOf_edgeSet hW]
    exact hg

open _root_.Graph in
/-- **The cycle subgraph occupies exactly what the cycle draws.** -/
theorem _root_.Graph.IsDrawing.pointSet_cycleGraph (h : IsDrawing G drawing) {e : β} {u v : Plane}
    {D : List β} (hc : G.IsCycleThrough e u v D) :
    pointSet (G.cycleGraph u e D) drawing = edgesCover drawing (e :: D) := by
  have hround := h.pointSet_pathGraphOf hc.isWalk_round (by simp)
  rw [cycleGraph, hround]
  refine Set.Subset.antisymm (edgesCover_mono fun g hg => ?_) (edgesCover_mono fun g hg => ?_)
  · rcases List.mem_append.1 hg with hg' | hg'
    · exact List.mem_cons_of_mem _ hg'
    · obtain rfl : g = e := by simpa using hg'
      exact List.mem_cons_self
  · rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ hg'

/-! ## The conclusion of `lem:face-cycles`, at one face -/

open _root_.Graph in
/-- **A face bounded by a named cycle.** The face `face G drawing z` is one of the two regions
of the complement of the realisation of the cycle `e :: D` — which is the blueprint's "every
face … has a cycle as its boundary *and is one of the two complementary regions of that
cycle*". The cycle is a parameter rather than an existential so that a consumer that has
produced one keeps it. -/
structure _root_.Graph.IsFaceCycle (G : Graph Plane β) (drawing : β → ℝ → Plane) (z : Plane)
    (e : β) (u v : Plane) (D : List β) : Prop where
  /-- The named data really is a cycle of the graph. -/
  isCycle : G.IsCycleThrough e u v D
  /-- Its realisation separates the plane into exactly two regions. -/
  isSeparating : IsSeparating (edgesCover drawing (e :: D))
  /-- The face is one of those two. -/
  isRegionOf : IsRegionOf (edgesCover drawing (e :: D)) (face G drawing z)

section

variable {e : β} {u v : Plane} {D : List β}

open _root_.Graph in
/-- **"has a cycle as its boundary"**: the frontier of the face is the realisation. -/
theorem _root_.Graph.IsFaceCycle.frontier_eq (h : IsFaceCycle G drawing z e u v D) :
    frontier (face G drawing z) = edgesCover drawing (e :: D) :=
  h.isRegionOf.frontier_eq h.isSeparating

open _root_.Graph in
/-- A face bounded by a cycle of a subgraph is bounded by the same cycle of the whole graph,
*provided the face itself is unchanged* — which is the shape the induction step needs when it
carries a face past an ear that does not touch it. -/
theorem _root_.Graph.IsFaceCycle.mono (h : IsFaceCycle B drawing z e u v D) (hBG : B ≤ G)
    (hface : face G drawing z = face B drawing z) : IsFaceCycle G drawing z e u v D where
  isCycle := ⟨h.isCycle.isLink.mono hBG, h.isCycle.isPath.mono hBG, h.isCycle.notMem⟩
  isSeparating := h.isSeparating
  isRegionOf := hface ▸ h.isRegionOf

end

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

open _root_.Graph in
/-- A vertex of the graph lying on the realisation of a cycle is a vertex of that cycle. -/
theorem _root_.Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover (h : IsDrawing G drawing) {e : β}
    {u v z : Plane} {D : List β} (hc : G.IsCycleThrough e u v D) (hzV : z ∈ V(G))
    (hz : z ∈ edgesCover drawing (e :: D)) : z ∈ G.walkVertices u D := by
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  rcases List.mem_cons.1 hg with rfl | hg'
  · rcases h.vertex_mem_edgeArc hc.isLink hzV hzg with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hc.isPath.edge_mem hg')
    rcases h.vertex_mem_edgeArc hxy hzV hzg with rfl | rfl
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_left⟩
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_right⟩

open _root_.Graph in
/-- **The realisation of a cycle, cut at two of its vertices, is two arcs meeting exactly
there.** The hypotheses are the output of `Graph.IsCycleThrough.split_at`, read in the plane. -/
theorem _root_.Graph.IsDrawing.arcs_of_split (h : IsDrawing G drawing) {a b : Plane} {D₁ D₂ : List β}
    (h₁ : G.IsPath a D₁ b) (h₂ : G.IsPath b D₂ a) (hab : a ≠ b)
    (hdisj : ∀ g ∈ D₁, g ∉ D₂)
    (hmeet : ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b) :
    IsArcBetween (edgesCover drawing D₁) a b ∧ IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} := by
  have harc₁ : IsArcBetween (edgesCover drawing D₁) a b :=
    h.path_isArcBetween h₁ (h₁.ne_nil hab)
  have harc₂ : IsArcBetween (edgesCover drawing D₂) b a :=
    h.path_isArcBetween h₂ (h₂.ne_nil (Ne.symm hab))
  refine ⟨harc₁, harc₂, Set.Subset.antisymm (fun z ⟨hz₁, hz₂⟩ => ?_) ?_⟩
  · -- A common point lies on an edge of each, and the two edges are distinct.
    obtain ⟨g₁, hg₁, hzg₁⟩ := mem_edgesCover_iff.1 hz₁
    obtain ⟨g₂, hg₂, hzg₂⟩ := mem_edgesCover_iff.1 hz₂
    have hne : g₁ ≠ g₂ := fun hh => hdisj g₁ hg₁ (hh ▸ hg₂)
    obtain ⟨-, hinc₁, hinc₂⟩ :=
      h.edge_inter (h₁.edge_mem hg₁) (h₂.edge_mem hg₂) hne hzg₁ hzg₂
    exact hmeet z (mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩)
      (mem_walkVertices_of_mem_covered ⟨g₂, hg₂, hinc₂⟩)
  · rintro z (rfl | rfl)
    exacts [⟨harc₁.left_mem, harc₂.right_mem⟩, ⟨harc₁.right_mem, harc₂.left_mem⟩]

end

namespace Schoenflies

/-! ## The obligation this module does not discharge

**Read this before using `Graph.face_cycles`.** Everything below the base case is proved
*modulo* one hypothesis, `Schoenflies.CrosscutSplitsRegion`, and the final theorem carries it
as an argument. It is the exhaustion clause of `thm:polygonal-crosscut` — Theorem 2.8, in the
shape `Schoenflies.IsPolygonalCrosscut.region_eq` and
`Schoenflies.IsPolygonalCrosscut.cell_isComponent₁` already have it — at a crosscut whose two
endpoints are **arbitrary points of the curve**.

`main`'s Theorem 2.8 cannot be applied here, and the reason is not a missing bridge. Its
hypotheses `edges₁`/`edges₂` are stated against `ClosedPolygon.arcPieces C a k`, which splits
the polygon's edge list **at two of its vertices**; and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` every vertex of every realization of a curve is a
*corner* of it. In the induction below the two cut points are the ear's endpoints, which are
graph vertices at which the two cycle edges may perfectly well leave along opposite rays — the
curve then runs straight through the cut point, which is therefore a vertex of no
`ClosedPolygon` with that carrier, and no realization theorem can supply one. Discharging this
hypothesis needs Theorem 2.8 restated for an edge-list split made at arbitrary points, which in
turn needs the parity theory for polygon presentations carrying redundant vertices
(`Schoenflies.PrePolygon`) rather than only for `ClosedPolygon`. That is a separate module. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.**
`J` is a separating polygonal curve cut by the points `p, q` into the arcs `A₁, A₂`; `P` is a
polygonal crosscut from `p` to `q` meeting `J` only there and running inside the region `Ω`.
The claim is that every component of `Ω ∖ P` is a region of `A₁ ∪ P` or of `A₂ ∪ P` — the
blueprint's "Theorem 2.8 replaces `F` by exactly two regions, both bounded by cycles".

This is **assumed**, not proved; see the section docstring for why `main`'s Theorem 2.8 does
not apply. -/
def CrosscutSplitsRegion : Prop :=
  ∀ (J A₁ A₂ P Ω : Set Plane) (p q : Plane),
    IsSeparating J → IsPolygonal J → IsPolygonal P →
    IsArcBetween A₁ p q → IsArcBetween A₂ p q → A₁ ∪ A₂ = J → A₁ ∩ A₂ = {p, q} →
    IsArcBetween P p q → P ∩ J = {p, q} → IsRegionOf J Ω → P \ {p, q} ⊆ Ω →
    ∀ z ∈ Ω \ P, IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \ P) z)

end Schoenflies

section
open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
/-! ## What a list of edges draws depends only on which edges are on it -/

open _root_.Graph in
theorem _root_.Graph.edgesCover_append (drawing : β → ℝ → Plane) (W₁ W₂ : List β) :
    edgesCover drawing (W₁ ++ W₂) = edgesCover drawing W₁ ∪ edgesCover drawing W₂ := by
  refine Set.Subset.antisymm (fun z hz => ?_)
    (Set.union_subset (edgesCover_mono (List.subset_append_left _ _))
      (edgesCover_mono (List.subset_append_right _ _)))
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  exact (List.mem_append.1 hg).imp (fun h => mem_edgesCover h hzg) fun h => mem_edgesCover h hzg

open _root_.Graph in
theorem _root_.Graph.edgesCover_perm {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesCover drawing W₁ = edgesCover drawing W₂ :=
  Set.Subset.antisymm (edgesCover_mono fun _ hg => hp.mem_iff.1 hg)
    (edgesCover_mono fun _ hg => hp.mem_iff.2 hg)

open _root_.Graph in
theorem _root_.Graph.edgesCover_reverse (drawing : β → ℝ → Plane) (W : List β) :
    edgesCover drawing W.reverse = edgesCover drawing W := edgesCover_perm (List.reverse_perm W)

/-! ## The induction step: one ear

"Suppose it holds for the current graph and add the next geometric ear. Its interior is
connected and disjoint from the current graph, so it lies in one current face `F` … the ear is
therefore a crosscut of that side, and Theorem `thm:polygonal-crosscut` replaces `F` by exactly
two regions, both bounded by cycles; all other faces are unchanged."

Everything here is proved, except that the appeal to Theorem 2.8 is to the hypothesis
`Schoenflies.CrosscutSplitsRegion` instead. -/

/-! ## `lem:face-cycles`

"The cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`. We prove
by induction that every face is exactly one of the two regions bounded by its boundary cycle." -/

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PrePolygonSep.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Separation and crossing parity before normalization

`Schoenflies.ClosedPolygon` carries a `corner` field — no three consecutive vertices collinear —
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` shows that field is not slack: a point at which
the curve runs straight is a vertex of *no* `ClosedPolygon` presentation of it. So a consumer that
must present a curve with vertices at prescribed points cannot use `ClosedPolygon` at all, and the
plane-graph arguments are exactly such consumers: the branch points of a drawing land wherever the
drawing puts them.

`Schoenflies.PrePolygon` is the presentation without that field, and vertices may be put anywhere.
This module gives it everything the crosscut chain asks of a simple closed polygon: an edge list
for the crossing count, the curve statements, the polygonal Jordan curve theorem, and the two
parity values.

## Everything transports across normalization, except the parity

`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon` deletes redundant vertices and returns
a genuine `ClosedPolygon` **with the same carrier**. Any property of the carrier *as a set* is
therefore free: `isJordanCurve_carrier`, `isPolygonal_carrier` and `isSeparating_carrier` below are
each three lines, and none of them needs a word about vertices.

The crossing parity is not a property of the carrier. It is computed from a *list of edges*, and
normalization changes that list: it merges collinear edges, so `P.pieces` is a subdivision of the
normalized polygon's. Lemma 2.1 (`Schoenflies.parity_subdivide`) says subdivision does not change
the parity, which is why one *expects* the parity to transport — but the normalization theorem is
an existence statement and keeps no record of which points were deleted, so there is no
subdivision in hand to feed it. See the note at the end of this docstring.

The parity is therefore re-derived here, and the derivation turns out not to need the collar at
all. Once the curve is known to separate, the two values are forced:

* far along the ray direction the count is zero, and the half-plane where it is zero is convex and
  unbounded, hence lies in the unbounded region — so `π_C = 0` on the outside;
* across an interior point of any one edge the count jumps by one (Lemma 2.2), and the two test
  points lie off the curve, so they lie in different regions — so the other region carries `1`.

Both steps are stated for an arbitrary closed chain whose cover separates the plane
(`Schoenflies.parity_eq_zero_of_mem_outside_cover`, `…parity_eq_one_of_mem_inside_cover`); the
`PrePolygon` statements are instances. **The `ClosedPolygon` versions in
`Schoenflies/PolygonalJordan.lean` are instances too** — `ClosedPolygon.parity_eq_one_of_mem_inside`
currently goes through `StripData`, and does not have to.

## Blueprint

* `Schoenflies.PrePolygon.pieces`, `…cover_pieces`, `…isClosedChain_pieces`, `…pieces_nondeg` —
  the edge list the crossing count of §2 is defined on, for a vertex list that has not been
  normalized. Same list as `ClosedPolygon.pieces`; `PrePolygon.pieces_toPre` is `rfl`.
* `Schoenflies.PrePolygon.isJordanCurve_carrier`, `…isPolygonal_carrier` — §1, "a simple closed
  polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `Schoenflies.PrePolygon.isSeparating_carrier` — **Theorem 2.3** in the form Definition 2.4 asks
  for, for a polygon presented with redundant vertices.
* `Schoenflies.PrePolygon.parity_flip_carrier` — Lemma 2.2, second half.
* `Schoenflies.parity_eq_zero_of_mem_outside_cover`,
  `Schoenflies.parity_eq_one_of_mem_inside_cover` — the last sentence of Theorem 2.3, for an
  arbitrary closed chain whose cover separates.
* `Schoenflies.PrePolygon.parity_eq_zero_of_mem_outside`, `…parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_iff`, `…parity_eq_one_iff` — the same, read off a `PrePolygon`.

## Two notes for the integrator

**`PrePolygon.pieces` duplicates `ClosedPolygon.pieces`.** The two definitions are literally the
same expression and `PrePolygon.pieces_toPre` proves them equal by `rfl`. The right arrangement is
to define `ClosedPolygon.pieces P := P.toPre.pieces` and to keep only the `PrePolygon` proofs — the
proofs of `cover_pieces`, `isClosedChain_pieces`, `pieces_nondeg`, `pieces_nodup`,
`notMem_edge_of_mem_openSegment` and `parity_flip_carrier` in `Schoenflies/PolygonBridge.lean` use
`vertex_inj` and `edges_meet` and nothing else, so they are the proofs below with `ClosedPolygon`
written for `PrePolygon`. That refactor cannot happen inside this module: `PrePolygon` is declared
in `Schoenflies/Realization.lean`, which is *downstream* of `PolygonBridge`. It needs `PrePolygon`
moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

**Merging collinear edges is a subdivision, but not one this development can point at.** Deleting
a redundant vertex `v` replaces the two edges at `v` by their union, which is exactly undoing
`Schoenflies.splitAt v` on the merged edge; iterating, `P.pieces` is `subdivide P'.pieces vs` for
the list `vs` of deleted vertices — *up to the order of the list*, which `rotate` disturbs. So two
things are missing before `parity_subdivide` could be used here: `Schoenflies.parity` invariance
under `List.Perm` (immediate, `parity` is a sum over the list), and a strengthening of
`exists_closedPolygon_of_prePolygon` to
`∃ m' (P' : ClosedPolygon m') (vs : List Plane), P'.carrier = P.carrier ∧
  P.pieces ~ subdivide P'.pieces vs`, carried through the induction. The direct argument below is
shorter than either.
-/

open Bornology Metric _root_.Set

namespace Schoenflies

/-! ## Small arithmetic helpers

Copies of two `private` facts of `Schoenflies/PolygonalJordan.lean`; they are `private` there and
so are these. -/

/-- In `ZMod 2` nothing is its own successor: this is what "the parities differ" comes down to. -/
private theorem ne_add_one_zmod_two (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- The only two values, named. -/
private theorem eq_one_of_ne_zero_zmod_two {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

/-! ## The two parity values from separation alone

The blueprint reads the two values off a point far along the ray direction and off a point either
side of an edge. Neither step knows anything about vertices, so both are stated here for an
arbitrary closed chain whose cover separates the plane. -/

section GeneralParity

variable {L : List Piece} {u : Plane}

/-- The forward coordinate is linear. This is all that is needed to see that a half-plane is
convex. -/
private theorem isLinearMap_fwd (u : Plane) : IsLinearMap ℝ (fwd u) where
  map_add x y := by simp only [fwd_eq, Plane.add_apply]; ring
  map_smul c x := by simp only [fwd_eq, Plane.smul_apply, smul_eq_mul]; ring

/-- The half-plane of points more than `R` along the ray direction. Beyond a bound on the polygon
it is the region in which the crossing count is visibly zero, and it is unbounded, which is what
places it in the unbounded region. -/
private def farSide (u : Plane) (R : ℝ) : Set Plane := {z | R < fwd u z}

private theorem convex_farSide (u : Plane) (R : ℝ) : Convex ℝ (farSide u R) :=
  convex_halfSpace_gt (isLinearMap_fwd u) R

/-- The forward coordinate of a multiple of the direction is the multiple. -/
private theorem fwd_smul_self (hu : Plane.IsDirection u) (s : ℝ) : fwd u (s • u) = s := by
  have h : fwd u (s • u) = s * fwd u u := by simp only [fwd_eq, Plane.smul_apply]; ring
  rw [h, fwd_self hu, mul_one]

/-- The half-plane is unbounded: it contains points of every size along the direction. -/
private theorem not_isBounded_farSide (hu : Plane.IsDirection u) (R : ℝ) :
    ¬ IsBounded (farSide u R) := by
  intro hb
  obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : Plane)
  set t : ℝ := max (max R R') 0 + 1 with htdef
  have h0 : 0 ≤ max (max R R') 0 := le_max_right _ _
  have hpos : 0 < t := by rw [htdef]; linarith
  have hR1 : R < t := by
    have := le_trans (le_max_left R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hR2 : R' < t := by
    have := le_trans (le_max_right R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hmem : t • u ∈ farSide u R := by
    change R < fwd u (t • u)
    rw [fwd_smul_self hu]; exact hR1
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_pos hpos]
  have := mem_closedBall_zero_iff.1 (hR' hmem)
  rw [hnorm] at this
  linarith

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane.

The blueprint's argument: a point far enough along the ray direction is crossed by no edge, and the
whole half-plane of such points is convex — hence connected — and unbounded, so it lies in the
unbounded region. Parity is constant there (Lemma 2.2), and the value is the one read off the far
point. -/
theorem parity_eq_zero_of_mem_outside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {x : Plane} (hx : x ∈ outside (cover L)) :
    parity u L x = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_cover L).isBounded.subset_closedBall (0 : Plane)
  have hcov : ∀ z ∈ cover L, fwd u z ≤ R := fun z hz =>
    le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) (mem_closedBall_zero_iff.1 (hR hz))
  have hdisj : farSide u R ⊆ (cover L)ᶜ := fun z hz hzc => absurd (hcov z hzc) (not_le.2 hz)
  have hqf : fwd u ((R + 1) • u) = R + 1 := fwd_smul_self hu (R + 1)
  have hqmem : (R + 1) • u ∈ farSide u R := by
    change R < fwd u ((R + 1) • u)
    rw [hqf]; linarith
  -- the far point is in the unbounded region, because the whole half-plane is
  have hqout : (R + 1) • u ∈ outside (cover L) := by
    refine ⟨hdisj hqmem, fun hb => not_isBounded_farSide hu R (hb.subset ?_)⟩
    exact (convex_farSide u R).isPreconnected.subset_connectedComponentIn hqmem hdisj
  have hq0 : parity u L ((R + 1) • u) = 0 :=
    parity_eq_zero_of_lt hL fun z hz => lt_of_le_of_lt (hcov z hz) (by rw [hqf]; linarith)
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL hC hsep.isConnected_outside.isPreconnected
    (fun z hz => hz.1) hx hqout

/-- **`π_C = 1` on the bounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane and which has *some* two points of the complement with different
parities.

Those two points cannot be in the same region, since parity is constant on a region; so one of them
is inside and the other outside. The outside carries `0`, hence the inside does not.

For a polygon the two points are supplied by Lemma 2.2: just before and just after an interior
point of any single edge. -/
theorem parity_eq_one_of_mem_inside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {a b : Plane} (ha : a ∉ cover L) (hb : b ∉ cover L)
    (hab : parity u L a ≠ parity u L b) {x : Plane} (hx : x ∈ inside (cover L)) :
    parity u L x = 1 := by
  have hzero : ∀ y ∈ outside (cover L), parity u L y = 0 := fun y hy =>
    parity_eq_zero_of_mem_outside_cover hu hL hC hsep hy
  have hconst : ∀ y ∈ inside (cover L), parity u L y = parity u L x := fun y hy =>
    parity_eq_of_isPreconnected hu hL hC hsep.isConnected_inside.isPreconnected
      (fun z hz => hz.1) hy hx
  have hma : a ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact ha
  have hmb : b ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact hb
  refine eq_one_of_ne_zero_zmod_two ?_
  rcases hma with h | h <;> rcases hmb with h' | h'
  · exact absurd ((hconst a h).trans (hconst b h').symm) hab
  · rw [hzero b h'] at hab
    rw [← hconst a h]
    exact hab
  · rw [hzero a h] at hab
    rw [← hconst b h']
    exact Ne.symm hab
  · exact absurd ((hzero a h).trans (hzero b h').symm) hab

end GeneralParity

namespace PrePolygon

variable {m : ℕ}

/-! ## The edge list

Verbatim `Schoenflies.ClosedPolygon.pieces` with the structure changed; `pieces_toPre` records
that the two are the same list. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form the
crossing count of §2 is defined on. -/
def pieces (P : PrePolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : PrePolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : PrePolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge is degenerate: consecutive vertices are distinct. Redundant vertices are allowed, but
repeated ones are not. -/
theorem pieces_nondeg (P : PrePolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact vertex_ne_succ i

/-- **The edge list is a closed chain.** Each vertex ends one edge and starts the next, so it is
counted twice; the cycle closes because `m + 3` is `0` in `ZMod (m + 3)`. -/
theorem isClosedChain_pieces (P : PrePolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** This is the equation that turns every parity statement,
which is about `cover`, into a statement about the carrier. -/
theorem cover_pieces (P : PrePolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : PrePolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact ClosedPolygon.natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-! ## The curve statements, and separation

All three are properties of the carrier as a set, and normalization keeps the carrier, so all three
come across from the `ClosedPolygon` versions with nothing to check. -/

/-- **The polygonal Jordan curve theorem** (Theorem 2.3) for a polygon presented with redundant
vertices, in the form Definition 2.4 asks for.

This is the statement the crosscut machinery of `Schoenflies/CrosscutCells.lean` onwards consumes,
and `IsSeparating` speaks only of the carrier, so normalizing and quoting
`ClosedPolygon.isSeparating_carrier` is the whole proof. -/
theorem isSeparating_carrier (P : PrePolygon m) : IsSeparating P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isSeparating_carrier

/-! ## The crossing parity

The list-level statements of `Schoenflies/Parity.lean`, read off a `PrePolygon`. -/

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's meeting
point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {P : PrePolygon m} {i j : ZMod (m + 3)} (hij : j ≠ i)
    {p : Plane} (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact vertex_ne_succ i (left_mem_openSegment_iff.1 hp)
  · exact vertex_ne_succ i (right_mem_openSegment_iff.1 hp)

/-- **Opposite sides of an edge** (Lemma 2.2, second half). Just before and just after an interior
point of an edge, in the ray direction, the base point is off the carrier and the crossing parity
differs by one.

The edge being crossed is split out of the list by `List.append_of_mem`; that the two remaining
fragments miss the crossing point is `edges_meet`, through
`PrePolygon.notMem_edge_of_mem_openSegment`. -/
theorem parity_flip_carrier (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  -- `exists_of_mem_cover` is the destructor matching `Schoenflies.mem_cover`; it lives, by
  -- accident, inside the `ClosedPolygon` namespace in `Schoenflies/PolygonBridge.lean`.
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

/-- Two points off the curve at which the parity differs: just before and just after the midpoint
of the first edge. This is what turns the separation theorem into the two parity *values*. -/
theorem exists_parity_ne (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ a b : Plane, a ∉ P.carrier ∧ b ∉ P.carrier ∧
      parity u P.pieces a ≠ parity u P.pieces b := by
  have hpmem : (1 / 2 : ℝ) • P.vertex 0 + (1 / 2 : ℝ) • P.vertex 1
      ∈ openSegment ℝ (P.vertex 0) (P.vertex (0 + 1)) := by
    rw [zero_add]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨δ, hδ, hmain⟩ := P.parity_flip_carrier hu hL 0 hpmem
  obtain ⟨h1, h2, h3⟩ := hmain (δ / 2) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, fun hh => ?_⟩
  rw [h3] at hh
  exact ne_add_one_zmod_two _ hh.symm

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_zero_of_mem_outside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

/-- **`π_C = 1` on the bounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_one_of_mem_inside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

end PrePolygon

/-! ## The `ClosedPolygon` parity values are instances

A machine check of the claim made in this module's docstring. `Schoenflies/PolygonalJordan.lean`
proves `ClosedPolygon.parity_eq_one_of_mem_inside` from a `StripData` — the collar of Lemma 1.8,
which is where `corner` is used. The collar is needed for Theorem 2.3 itself, but *not* a second
time for the parity value: given separation, the two values follow from the general lemmas above.
The two `example`s below are the same statements, re-proved that way. -/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PrePolygonArc.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric _root_.Set

namespace Schoenflies

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- The edge list of the arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

@[simp] theorem arcPieces_zero (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPieces a (k + l) = P.arcPieces a k ++ P.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (P : PrePolygon m) : P.arcPieces 0 (m + 3) = P.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ P.arcPieces a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPieces a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPieces a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_perm (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPieces a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPieces a (m + 3)
      = P.arcPieces a (m + 3 - a.val) ++ P.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPieces 0 a.val ++ P.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `P` exactly once. -/
theorem arcPieces_split_perm (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm P a

theorem sameEdges_arcPieces_split (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm P a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (P.arcPieces a k) ∪ cover (P.arcPieces (a + k) (m + 3 - k)) = P.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm P a hk), cover_pieces]

theorem cover_arcPieces_subset (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (P.arcPieces a k) ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

/-! ## The arcs as sets -/

/-- The arc of `P` that leaves vertex `a` and runs forward through `k` edges, as a set. -/
def arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPieces a k)

theorem arc_subset_carrier (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arc a k ⊆ P.carrier := cover_arcPieces_subset P a k

theorem arc_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arc a k ∪ P.arc (a + k) (m + 3 - k) = P.carrier := cover_arcPieces_union P a hk

/-- An arc is compact: it is a finite union of segments. -/
theorem isCompact_arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : IsCompact (P.arc a k) :=
  isCompact_cover _

theorem mem_arc_iff {z : Plane} :
    z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arc a k := by
  refine mem_arc_iff.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero, edge]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have h : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, h]
  refine mem_arc_iff.2 ⟨k - 1, by omega, ?_⟩
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** -/
theorem endpoints_subset_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arc a hk
  · exact P.vertex_add_mem_arc a hk

theorem endpoints_subset_arc' (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arc (a + k) hpos

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : PrePolygon m) (a : ZMod (m + 3)) {x z : ℕ} (hx : x < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    x = z :=
  ClosedPolygon.natCast_inj hx hz (add_left_cancel (P.vertex_inj he))

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_inter (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (ClosedPolygon.natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  have hzero : k + t + 1 = m + 3 →
      ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- An interior point of the first edge of an arc: a point of the arc that is neither cut
vertex, which is what says the arc is more than its two ends. -/
theorem arc_not_subset_endpoints (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : ¬ P.arc a k ⊆ ({P.vertex a, P.vertex (a + k)} : Set Plane) := by
  intro hsub
  set x : Plane := (1 / 2 : ℝ) • P.vertex a + (1 / 2 : ℝ) • P.vertex (a + 1) with hxdef
  have hxo : x ∈ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxarc : x ∈ P.arc a k :=
    mem_arc_iff.2 ⟨0, hk1, by
      rw [Nat.cast_zero, add_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  have hkne : (k : ZMod (m + 3)) ≠ 0 := by
    intro he
    have h0 : ((k : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by rw [he, Nat.cast_zero]
    have hk0 := ClosedPolygon.natCast_inj (m := m) (show k < m + 3 by omega)
      (show 0 < m + 3 by omega) h0
    omega
  rcases hsub hxarc with h | h
  · exact P.vertex_ne_succ a (left_mem_openSegment_iff.1 (h ▸ hxo))
  · refine notMem_edge_of_mem_openSegment (P := P) (i := a) (j := a + k)
      (fun he => hkne (by linear_combination he)) hxo ?_
    rw [edge, h]
    exact left_mem_segment ℝ _ _

/-! ### An arc as a polyline

`arc a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

/-- The vertex list of an arc. -/
def arcList (P : PrePolygon m) (a : ZMod (m + 3)) : ℕ → List Plane
  | 0 => [P.vertex a]
  | k + 1 => P.vertex a :: arcList P (a + 1) k

theorem arcList_ne_nil (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : P.arcList a k ≠ [] := by
  cases k <;> simp [arcList]

theorem getLast_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    (P.arcList a k).getLast (P.arcList_ne_nil a k) = P.vertex (a + k)
  | 0, P, a => by simp [arcList]
  | k + 1, P, a => by
    change (P.vertex a :: P.arcList (a + 1) k).getLast (List.cons_ne_nil _ _)
        = P.vertex (a + ((k + 1 : ℕ) : ZMod (m + 3)))
    rw [List.getLast_cons (P.arcList_ne_nil (a + 1) k), getLast_arcList k P (a + 1)]
    congr 1
    push_cast
    ring

theorem arcPieces_succ (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcPieces a (k + 1) = (P.vertex a, P.vertex (a + 1)) :: P.arcPieces (a + 1) k := by
  rw [arcPieces, arcPieces, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [Nat.cast_zero, add_zero]
  · refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    congr 2 <;> · push_cast; ring

theorem poly_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    poly (P.arcList a (k + 1)) = P.arc a (k + 1)
  | 0, P, a => by
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ ({P.vertex (a + 1)} : Set Plane)
        = cover (P.arcPieces a 1)
    rw [arcPieces_succ P a 0, arcPieces_zero, cover_cons, cover_nil, Set.union_empty]
    exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ _ _))
  | k + 1, P, a => by
    have hstep : poly (P.arcList a (k + 2))
        = segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ poly (P.arcList (a + 1) (k + 1)) := rfl
    rw [hstep, poly_arcList k P (a + 1)]
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ cover (P.arcPieces (a + 1) (k + 1))
        = cover (P.arcPieces a (k + 2))
    rw [arcPieces_succ P a (k + 1), cover_cons]
    rfl

theorem poly_arcList_of_pos (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    poly (P.arcList a k) = P.arc a k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact poly_arcList k' P a

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-- **The two halves of a cut segment meet only at the cut point.** -/
theorem segment_halves_inter {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    segment ℝ u w ∩ segment ℝ w v ⊆ {w} := by
  rintro x ⟨hx1, hx2⟩
  have hws : w ∈ segment ℝ u v := openSegment_subset_segment ℝ _ _ hw
  have hwd := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    (by simp) hws
  have h1 := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) hws (by simp) hx1
  have h2 := dist_le_of_mem_segment huv hws (right_mem_segment ℝ u v) hwd.2 hx2
  have hxs : x ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hws hx1
  exact eq_of_dist_left_eq huv hxs hws (le_antisymm h1.2 h2.1)

/-- The far end of a cut segment is not on the near half. -/
theorem right_notMem_left_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    v ∉ segment ℝ u w := by
  intro hv
  have hvw : v = w := segment_halves_inter huv hw ⟨hv, right_mem_segment ℝ w v⟩
  rw [← hvw] at hw
  exact huv (right_mem_openSegment_iff.1 hw)

/-- The near end of a cut segment is not on the far half. -/
theorem left_notMem_right_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    u ∉ segment ℝ w v := by
  intro hu
  have huw : u = w := segment_halves_inter huv hw ⟨left_mem_segment ℝ u w, hu⟩
  rw [← huw] at hw
  exact huv (left_mem_openSegment_iff.1 hw)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a redundant vertex; this is the inverse operation,
and it is what makes `PrePolygon` the right presentation for a consumer that must cut the curve
at prescribed points. The vertex is inserted at the end of the list, interior to the last edge;
`Schoenflies.PrePolygon.rotate` brings any edge there. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {z : Plane}

/-- The index `-1` of a cyclic list of length `m + 3`, as a numeral. -/
theorem val_neg_one : (-1 : ZMod (m + 3)).val = m + 2 := by
  have h : (-1 : ZMod (m + 3)) = ((m + 2 : ℕ) : ZMod (m + 3)) := by
    have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination -h0
  rw [h, ZMod.val_cast_of_lt (by omega)]

/-- The last edge, with its second endpoint written as vertex `0`. -/
theorem edge_neg_one (P : PrePolygon m) :
    P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

/-- **A point interior to an edge is a vertex of no index.** -/
theorem vertex_ne_of_mem_openSegment {i : ZMod (m + 3)} {w : Plane}
    (hw : w ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) (j : ZMod (m + 3)) :
    P.vertex j ≠ w := by
  intro he
  by_cases hji : j = i
  · rw [hji] at he
    rw [← he] at hw
    exact vertex_ne_succ i (left_mem_openSegment_iff.1 hw)
  · have hmem : w ∈ P.edge j := by rw [edge, ← he]; exact left_mem_segment ℝ _ _
    exact notMem_edge_of_mem_openSegment hji hw hmem

/-- The vertex family with `z` appended at the end: the old numerals name the old vertices, and
the one new index names `z`. -/
def insVertex (P : PrePolygon m) (z : Plane) (j : ZMod (m + 1 + 3)) : Plane :=
  if j.val < m + 3 then P.vertex ((j.val : ℕ) : ZMod (m + 3)) else z

theorem insVertex_emb (P : PrePolygon m) (z : Plane) (j : ZMod (m + 3)) :
    insVertex P z (emb j) = P.vertex j := by
  have hlt : j.val < m + 3 := ZMod.val_lt j
  have hval : (emb j).val = j.val := by
    rw [emb, ZMod.val_cast_of_lt (by omega)]
  rw [insVertex, if_pos (by rw [hval]; exact hlt), hval, ZMod.natCast_rightInverse j]

theorem val_neg_one' : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast, ZMod.val_cast_of_lt (by omega)]

theorem insVertex_neg_one (P : PrePolygon m) (z : Plane) : insVertex P z (-1) = z := by
  rw [insVertex, if_neg (by rw [val_neg_one' (m := m)]; omega)]

/-- Away from the inserted vertex the edges are unchanged. -/
theorem insEdge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (insVertex P z (emb j)) (insVertex P z (emb j + 1)) = P.edge j := by
  rw [← emb_succ_of_lt h, insVertex_emb, insVertex_emb, edge]

/-- The penultimate edge of the lengthened list: the near half of the cut edge. -/
theorem insEdge_pen (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1 - 1)) (insVertex P z (-1 - 1 + 1))
      = segment ℝ (P.vertex (-1)) z := by
  have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
  have h1 : insVertex P z (-1 - 1) = P.vertex (-1) := by rw [← he, insVertex_emb]
  have h2 : insVertex P z (-1 - 1 + 1) = z := by
    rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]
  rw [h1, h2]

/-- The last edge of the lengthened list: the far half of the cut edge. -/
theorem insEdge_last (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1)) (insVertex P z (-1 + 1)) = segment ℝ z (P.vertex 0) := by
  have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
  have h1 : insVertex P z (-1) = z := insVertex_neg_one P z
  have h2 : insVertex P z (-1 + 1) = P.vertex 0 := by
    rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]
  rw [h1, h2]

theorem vertex_neg_one_ne_zero (P : PrePolygon m) : P.vertex (-1) ≠ P.vertex 0 := by
  have h := vertex_ne_succ (P := P) (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
include hz

/-- The two new edges cover the edge they replace. -/
theorem insEdge_union : segment ℝ (P.vertex (-1)) z ∪ segment ℝ z (P.vertex 0) = P.edge (-1) := by
  rw [edge_neg_one]
  exact (segment_split (openSegment_subset_segment ℝ _ _ hz)).symm

theorem insEdge_pen_subset : segment ℝ (P.vertex (-1)) z ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_left

theorem insEdge_last_subset : segment ℝ z (P.vertex 0) ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_right

/-- **The polygon with one extra vertex, interior to its last edge** — equivalently, with the
last edge split in two at a prescribed interior point. -/
def insertLast (P : PrePolygon m) (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    PrePolygon (m + 1) where
  vertex := insVertex P z
  vertex_inj := by
    intro i j hij
    have hzv : ∀ l : ZMod (m + 3), P.vertex l ≠ z := by
      intro l
      refine vertex_ne_of_mem_openSegment (i := -1) ?_ l
      rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring]
    simp only [insVertex] at hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    by_cases hli : i.val < m + 3 <;> by_cases hlj : j.val < m + 3
    · rw [if_pos hli, if_pos hlj] at hij
      exact ZMod.val_injective _
        (ClosedPolygon.natCast_inj hli hlj (P.vertex_inj hij))
    · rw [if_pos hli, if_neg hlj] at hij
      exact absurd hij (hzv _)
    · rw [if_neg hli, if_pos hlj] at hij
      exact absurd hij.symm (hzv _)
    · exact ZMod.val_injective _ (by omega)
  edges_meet := by
    have hne0 : P.vertex (-1) ≠ P.vertex 0 := vertex_neg_one_ne_zero P
    have hhalf := segment_halves_inter hne0 hz
    have hpen := insEdge_pen P z
    have hlast := insEdge_last P z
    -- The shape of the edge at each of the three kinds of index.
    have hshape : ∀ i : ZMod (m + 1 + 3),
        (∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i ∧
            segment ℝ (insVertex P z i) (insVertex P z (i + 1)) = P.edge j ∧
            ({insVertex P z i, insVertex P z (i + 1)} : Set Plane)
              = {P.vertex j, P.vertex (j + 1)}) ∨
          (i = -1 - 1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ (P.vertex (-1)) z) ∨
          (i = -1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ z (P.vertex 0)) := by
      intro i
      by_cases h1 : i = -1
      · exact Or.inr (Or.inr ⟨h1, by rw [h1]; exact hlast⟩)
      by_cases h2 : i = -1 - 1
      · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact hpen⟩)
      obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine Or.inl ⟨j, hjv, rfl, insEdge_of_lt hjv, ?_⟩
      rw [insVertex_emb, ← emb_succ_of_lt hjv, insVertex_emb]
    intro i j hij
    have hi := hshape i
    have hj := hshape j
    -- The names of the two ends of the edge at `i`, in each case.
    rcases hi with ⟨ji, hjiv, rfl, hEi, hVi⟩ | ⟨rfl, hEi⟩ | ⟨rfl, hEi⟩
    · have hjine : ji ≠ -1 := by
        intro he
        rw [he, val_neg_one] at hjiv
        omega
      rw [hEi, hVi]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, hEj⟩
      · rw [hEj]
        exact P.edges_meet ji jj fun he => hij (by rw [he])
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_pen_subset hz hx.2⟩
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_last_subset hz hx.2⟩
    · rw [hEi]
      have hV : ({insVertex P z (-1 - 1), insVertex P z (-1 - 1 + 1)} : Set Plane)
          = {P.vertex (-1), z} := by
        have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
        rw [show insVertex P z (-1 - 1) = P.vertex (-1) by rw [← he, insVertex_emb],
          show insVertex P z (-1 - 1 + 1) = z by
            rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hEj⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_pen_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact absurd (hmem ▸ hx1) (right_notMem_left_half hne0 hz)
      · exact absurd rfl hij
      · rw [hEj]
        exact fun x hx => Or.inr (hhalf hx)
    · rw [hEi]
      have hV : ({insVertex P z (-1), insVertex P z (-1 + 1)} : Set Plane)
          = {z, P.vertex 0} := by
        have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
        rw [insVertex_neg_one,
          show insVertex P z (-1 + 1) = P.vertex 0 by
            rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, -⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_last_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact absurd (hmem ▸ hx1) (left_notMem_right_half hne0 hz)
        · exact Or.inr hmem
      · rw [hEj]
        exact fun x hx => Or.inl (hhalf ⟨hx.2, hx.1⟩)
      · exact absurd rfl hij

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLast : (insertLast P hz).carrier = P.carrier := by
  have hpen := insEdge_pen P z
  have hlast := insEdge_last P z
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · by_cases h1 : i = -1
    · subst h1
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_last_subset hz) (edge_subset_carrier _))
      exact hlast
    by_cases h2 : i = -1 - 1
    · subst h2
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_pen_subset hz) (edge_subset_carrier _))
      exact hpen
    · obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine le_trans (le_of_eq ?_) (edge_subset_carrier j)
      exact insEdge_of_lt hjv
  · by_cases hjlast : j.val + 1 < m + 3
    · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := insertLast P hz) (emb j))
      exact (insEdge_of_lt hjlast (P := P) (z := z)).symm
    · have hjm : j = -1 := by
        have := ZMod.val_lt j
        exact ZMod.val_injective _ (by rw [val_neg_one]; omega)
      subst hjm
      rw [← insEdge_union hz]
      refine Set.union_subset ?_ ?_
      · refine le_trans (le_of_eq hpen.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1 - 1))
      · refine le_trans (le_of_eq hlast.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1))

/-- The inserted vertex is a vertex. -/
theorem insertLast_mem_vertex : ∃ j, (insertLast P hz).vertex j = z :=
  ⟨-1, insVertex_neg_one P z⟩

/-- The old vertices are still vertices. -/
theorem insertLast_old_vertex (i : ZMod (m + 3)) : ∃ j, (insertLast P hz).vertex j = P.vertex i :=
  ⟨emb i, insVertex_emb P z i⟩

end Insert

/-- **A named point of the curve becomes a vertex**, and the old vertices stay vertices. Either
the point already is a vertex, or it is interior to exactly one edge, and then that edge is
brought to the end of the list by `Schoenflies.PrePolygon.rotate` and cut by
`Schoenflies.PrePolygon.insertLast`. -/
theorem exists_prePolygon_insert {m : ℕ} (P : PrePolygon m) {z : Plane} (hz : z ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧ (∃ j, P'.vertex j = z) ∧
      ∀ i, ∃ j, P'.vertex j = P.vertex i := by
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
  by_cases hend : z = P.vertex i ∨ z = P.vertex (i + 1)
  · exact ⟨m, P, rfl, by rcases hend with rfl | rfl; exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩],
      fun i => ⟨i, rfl⟩⟩
  · push Not at hend
    have hopen : z ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hzi
    -- Rotate so that the edge in question is the last one.
    set Q : PrePolygon m := P.rotate (i + 1) with hQ
    have hQm : Q.vertex (-1) = P.vertex i := by
      rw [hQ, rotate_vertex, show i + 1 + (-1 : ZMod (m + 3)) = i by ring]
    have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
      rw [hQ, rotate_vertex, add_zero]
    have hopen' : z ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by rw [hQm, hQ0]; exact hopen
    refine ⟨m + 1, insertLast Q hopen', ?_, insertLast_mem_vertex hopen', fun l => ?_⟩
    · rw [carrier_insertLast hopen', hQ, carrier_rotate]
    · obtain ⟨j, hj⟩ := insertLast_old_vertex hopen' (l - (i + 1))
      exact ⟨j, by rw [hj, hQ, rotate_vertex, add_sub_cancel]⟩

/-- **Every point of a finite list on the curve can be made a vertex at once.** -/
theorem exists_prePolygon_vertices : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ z ∈ S, z ∈ P.carrier) →
      ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
        (∀ z ∈ S, ∃ j, P'.vertex j = z) ∧ (∀ i, ∃ j, P'.vertex j = P.vertex i)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun i => ⟨i, rfl⟩⟩
  | z :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hcar₁, ⟨j₀, hj₀⟩, hold₁⟩ :=
      exists_prePolygon_insert P (hS z (List.mem_cons_self ..))
    obtain ⟨m₂, P₂, hcar₂, hnew₂, hold₂⟩ := exists_prePolygon_vertices S P₁
      (fun w hw => by rw [hcar₁]; exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨m₂, P₂, by rw [hcar₂, hcar₁], fun w hw => ?_, fun i => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw'
      · obtain ⟨j, hj⟩ := hold₂ j₀
        exact ⟨j, by rw [hj, hj₀]⟩
      · exact hnew₂ w hw'
    · obtain ⟨j₁, hj₁⟩ := hold₁ i
      obtain ⟨j, hj⟩ := hold₂ j₁
      exact ⟨j, by rw [hj, hj₁]⟩

end PrePolygon

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

/-- **The realization theorem for `PrePolygon`, with named points.** Any finite list of points of
the curve — corners or not — can be required to be among the vertices. -/
theorem exists_prePolygon_points {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, p ∈ C) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C ∧ ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar', hnew, -⟩ :=
    PrePolygon.exists_prePolygon_vertices S P (fun z hz => by rw [hcar]; exact hS z hz)
  exact ⟨m', P', by rw [hcar', hcar], hnew⟩

/-- **The realization theorem tracking two named points**, for a presentation that may carry
redundant vertices. Unlike `Schoenflies.exists_closedPolygon_split` this asks nothing of the two
points but that they lie on the curve: a `PrePolygon` has no `corner` field to obstruct a vertex
where the curve runs straight. -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_prePolygon_points hJ hP [p, q]
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/FaceCyclesLand.lean` -/

/-!
# `lem:face-cycles`, with nothing assumed

`Schoenflies/FaceCyclesProof.lean` proves `lem:face-cycles` modulo one hypothesis,
`Schoenflies.CrosscutSplitsRegion`: the exhaustion clause of `thm:polygonal-crosscut` for a
crosscut whose two endpoints are *arbitrary points* of the curve. This module proves that
hypothesis and restates the lemma without it (`Graph.face_cycles'`,
`Graph.IsDrawing.hasFaceCycles_union'`).

## Why the crosscut theorem had to be redone, and how far

`main`'s Theorem 2.8 (`Schoenflies.IsPolygonalCrosscut`) cuts a `ClosedPolygon` at two of *its
vertices*, and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says a point at which the curve runs
straight is a vertex of no `ClosedPolygon` presentation of it. In the ear induction the two cut
points are graph vertices, at which the two cycle edges may leave along opposite rays. So the
presentation has to be `Schoenflies.PrePolygon`, which has no `corner` field, and the two `main`
hypotheses `edges₁`/`edges₂` — multiset equalities `SameEdges Jᵢ.pieces (Aᵢ ++ K)` — have to go
as well, for the reason `Schoenflies/FaceCyclesProof.lean` records: the merged curve `Aᵢ ∪ P` may
run straight through a cut point, and then no presentation of it has an edge ending there.

Both go away at once by never realizing `J₁` and `J₂` at all. The two curves of the split are
given by *literal* edge lists `Aᵢ ++ K`, so Lemma 2.7 (`Schoenflies.parity_split`) applies with
nothing to check, and only the *easy* half of Theorem 2.3 is asked of them: "points in the same
region have the same crossing count", which is Lemma 2.2
(`Schoenflies.parity_eq_of_mem_connectedComponentIn`) and needs no realization. The hard half —
the two values `0` and `1` — is needed for `J` alone, where
`Schoenflies.PrePolygon.parity_eq_one_iff` of `Schoenflies/PrePolygonSep.lean` supplies it. That
is the whole of the reduction; Lemma 2.6 (`Schoenflies.crosscut_cells`) is already stated at the
set level and is quoted unchanged.

What the presentation still has to do is put the two cut points *on* its vertex list, and that is
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`, the inverse of
`Schoenflies.PrePolygon.deleteLast`. A point interior to an edge is brought to the last edge by
`Schoenflies.PrePolygon.rotate` and the edge is split in two; simplicity survives because the far
end of the split edge lies on neither half.

## For the integrator

The `Schoenflies.PrePolygon` arc apparatus this module runs on —
`Schoenflies.PrePolygon.arcPieces`, `…arc`, `…arcList`, `…insertLast` and
`Schoenflies.exists_prePolygon_split` — lives in `Schoenflies/PrePolygonArc.lean`, shared with
`Schoenflies/Graph/K33Land.lean`. It is `Schoenflies.ClosedPolygon.arcPieces` and its API of
`Schoenflies/ParitySplitting.lean` and `Schoenflies/Realization.lean` transcribed with the
structure changed — the proofs use `vertex_inj` and `edges_meet` and nothing else. The right
arrangement, as `Schoenflies/PrePolygonSep.lean` already says of `pieces`, is to prove them once
for `PrePolygon` and define the `ClosedPolygon` versions as `P.toPre.arcPieces`; that needs
`PrePolygon` moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

Three declarations here are general and belong elsewhere:
`Schoenflies.isSeparating_of_isJordanCurve` in `Schoenflies/Realization.lean`,
`Schoenflies.IsArcBetween.ne` in `Schoenflies/Curve.lean`, and
`Schoenflies.isChainFrom_segsOf` in `Schoenflies/ParitySplitting.lean` beside
`Schoenflies.isChainFrom_pathPieces`. `Schoenflies.two_arcs_unique_of_isClosed` subsumes
`Schoenflies.two_arcs_unique` and should replace it in `Schoenflies/Realization.lean`.

Once this module is moved above `Schoenflies/FaceCyclesProof.lean`, the hypothesis
`Schoenflies.CrosscutSplitsRegion` can be deleted from `Graph.face_cycles` and
`Graph.IsDrawing.hasFaceCycles_union`, and the two primed statements at the end here dropped.

## Blueprint

* `Schoenflies.two_arcs_unique_of_isClosed` — the two arcs a pair of points cuts a curve into are
  determined, with the competing splitting known only to be closed and nondegenerate.
* `Schoenflies.crosscutSplitsRegion` — the exhaustion clause of `thm:polygonal-crosscut` at
  arbitrary cut points: `Schoenflies.CrosscutSplitsRegion`, proved.
* `Graph.IsDrawing.hasFaceCycles_union'` — one ear of `lem:face-cycles`.
* `Graph.face_cycles'` — **`lem:face-cycles`**.
* `Graph.IsFaceCycle.eq_inside_of_isBounded'` — "in particular, every bounded face is the
  interior of its boundary cycle".
-/
namespace Schoenflies

/-! ## Small pieces the assembly needs -/

/-- **A polygonal Jordan curve separates the plane** (Theorem 2.3, at the set level): realize it
and quote `Schoenflies.ClosedPolygon.isSeparating_carrier`. -/
theorem isSeparating_of_isJordanCurve {S : Set Plane} (hJ : IsJordanCurve S)
    (hP : IsPolygonal S) : IsSeparating S := by
  obtain ⟨m, Q, hQ⟩ := exists_closedPolygon hJ hP
  exact hQ ▸ Q.isSeparating_carrier

/-- The two ends of an arc are distinct: they are the images of `0` and `1`. -/
theorem IsArcBetween.ne {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨f, -, hinj, -, hf0, hf1⟩ := h
  intro he
  have h01 : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (by rw [hf0, hf1, he])
  norm_num at h01

/-- **A polyline is a chain from its first point to its last**, with its degenerate steps
dropped. `Schoenflies.isChainFrom_pathPieces` says this for `Schoenflies.pathPieces`, which keeps
them; `Schoenflies.segsOf` is the list a consumer needing nondegenerate edges must use. -/
theorem isChainFrom_segsOf : ∀ (vs : List Plane) (h : vs ≠ []),
    IsChainFrom (segsOf vs) (vs.head h) (vs.getLast h)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isChainFrom_nil v
  | u :: v :: rest, hu => by
    classical
    have hne : (v :: rest) ≠ [] := List.cons_ne_nil _ _
    have ih : IsChainFrom (segsOf (v :: rest)) v ((v :: rest).getLast hne) :=
      isChainFrom_segsOf (v :: rest) hne
    have hgl : (u :: v :: rest).getLast hu = (v :: rest).getLast hne := List.getLast_cons hne
    rw [show (u :: v :: rest).head hu = u from rfl, hgl, segsOf_cons_cons]
    split_ifs with huv
    · rw [huv]; exact ih
    · intro f
      simp only [List.map_cons, List.sum_cons]
      rw [ih f]
      linear_combination add_self_zmod_two (f v)

/-- **The two-arc decomposition is determined, and the competitor need not be known to be two
arcs.** This is `Schoenflies.two_arcs_unique` with the hypotheses on the second splitting weakened
to what its proof uses: the two sets are closed and neither is just the two cut points. The edge
lists of a polygon supply exactly that, and nothing tells us they are arcs until this lemma has
said so. -/
theorem two_arcs_unique_of_isClosed {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hc1 : IsClosed D₁) (hc2 : IsClosed D₂)
    (hn1 : ¬ D₁ ⊆ ({p, q} : Set Plane)) (hn2 : ¬ D₂ ⊆ ({p, q} : Set Plane)) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ D₁
      · by_cases h2 : w ∈ D₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hD] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun w hw => ?_)
      by_contra hwD2
      exact hnone (hconn _ _ hc1.isOpen_compl hc2.isOpen_compl hsub hcase ⟨w, hw, hwD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun w hw => ?_)
      by_contra hwD1
      exact hcase ⟨w, hw, hwD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} →
      ¬ D' ⊆ ({p, q} : Set Plane) → A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'n h1 h2
    refine hD'n ?_
    rw [← hDDi]
    intro w hw
    have hwC : w ∈ C := by rw [← hDD]; exact Or.inr hw
    rw [← hA] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := by rw [← hX'Y']; exact Or.inl hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hn2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hn1 h1 h2) (by simp)

/-! ## Theorem 2.8 at arbitrary cut points

The blueprint's Theorem 2.8 is proved on `main` for a crosscut cutting a `ClosedPolygon` at two
of *its vertices*; `Schoenflies.ClosedPolygon.isCornerAt_vertex` makes that a real restriction,
since a point where the curve runs straight is a vertex of no `ClosedPolygon` presentation. The
exhaustion clause is what a consumer splitting a face at two graph vertices needs, and here it is
proved with no condition on the two points beyond lying on the curve.

The route is the blueprint's, with `PrePolygon` in place of `ClosedPolygon` and with the two
`Schoenflies.SameEdges` hypotheses of `Schoenflies.IsPolygonalCrosscut` replaced by *literal*
edge lists: the two curves of the split are presented as `Aᵢ ++ K`, so Lemma 2.7
(`Schoenflies.parity_split`) applies with nothing to check. Only one direction of Theorem 2.3 is
needed for those two lists — "the same region forces the same count", which is Lemma 2.2 and asks
for no realization at all. The other direction is needed only for the curve `C` itself, and there
`Schoenflies.PrePolygon.parity_eq_one_iff` supplies it. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.** This is
`Schoenflies.CrosscutSplitsRegion`, the hypothesis `Schoenflies/FaceCyclesProof.lean` was left
with. -/
theorem crosscutSplitsRegion : CrosscutSplitsRegion := by
  intro J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2 hunion hinter hParc hPJ hΩ hPsub z hz
  have hpq : p ≠ q := hA1.ne
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ :=
    exists_prePolygon_split hJsep.isJordanCurve hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  have hpqD1 : ({p, q} : Set Plane) ⊆ C.arc a k := by
    rw [← hDinter]; exact Set.inter_subset_left
  have hpqD2 : ({p, q} : Set Plane) ⊆ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) := by
    rw [← hDinter]; exact Set.inter_subset_right
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating.
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A reference point in the region the crosscut does not enter.
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyJ : y ∉ J := hΩpair.right.subset_compl hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ S : Set Plane, S ⊆ J → Ω' ⊆ (S ∪ P)ᶜ := by
    intro S hSJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hSJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ C.arc a k ∪ P := hΩ'sub _ hD1J hy
  have hyJ2 : y ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := hΩ'sub _ hD2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (C.arc a k ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD1J)
  have hΩW2 : Ω' ⊆
      connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD2J)
  have heqΩ' : connectedComponentIn Jᶜ y = Ω' := hΩpair.right.connectedComponentIn_eq hJsep hy
  -- 6. Lemma 2.6: the two cells are components of `Ω ∖ P`.
  obtain ⟨⟨-, hV1comp⟩, ⟨-, hV2comp⟩, -, -, -⟩ :=
    crosscut_cells hJsep hJ1 hJ2 hD1J hD2J (by rw [hPJ]; exact hpqD1) (by rw [hPJ]; exact hpqD2)
      (arcs_ne (le_of_eq hDinter) hD1n) hΩpair (hJ1.isRegionPair_farRegion hyJ1) hΩW1
      (hJ2.isRegionPair_farRegion hyJ2) hΩW2
  -- 7. Exhaustion, by Lemma 2.7 and the two values of Theorem 2.3.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  have hexh : ∀ w ∈ Ω \ P, w ∈ farRegion (C.arc a k ∪ P) y ∨
      w ∈ farRegion (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) y := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hwJ : w ∉ J := hΩ.subset_compl hw.1
    have hw1 : w ∉ C.arc a k ∪ P := by
      rintro (h | h)
      · exact hwJ (hD1J h)
      · exact hw.2 h
    have hw2 : w ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      · exact hwJ (hD2J h)
      · exact hw.2 h
    have hmem1 : w ∈ connectedComponentIn (C.arc a k ∪ P)ᶜ y := by
      by_contra hc1
      exact hn1 ⟨hw1, hc1⟩
    have hmem2 : w ∈
        connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y := by
      by_contra hc2
      exact hn2 ⟨hw2, hc2⟩
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) w
        = parity u (C.arcPieces a k ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev1 hclosed1 (by rw [hcov1]; exact hyJ1)
        (by rw [hcov1]; exact hmem1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev2 hclosed2 (by rw [hcov2]; exact hyJ2)
        (by rw [hcov2]; exact hmem2)
    have hkey : parity u C.pieces w = parity u C.pieces y := by
      rw [← hsplit w, ← hsplit y, hp1, hp2]
    rcases hΩpair with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · rw [C.parity_eq_one_of_mem_inside hu hlevC
          (show w ∈ inside C.carrier by rw [hcar]; exact hin ▸ hw.1),
        C.parity_eq_zero_of_mem_outside hu hlevC
          (show y ∈ outside C.carrier by rw [hcar]; exact hout ▸ hy)] at hkey
      exact absurd hkey (by decide)
    · rw [C.parity_eq_zero_of_mem_outside hu hlevC
          (show w ∈ outside C.carrier by rw [hcar]; exact hout ▸ hw.1),
        C.parity_eq_one_of_mem_inside hu hlevC
          (show y ∈ inside C.carrier by rw [hcar]; exact hin ▸ hy)] at hkey
      exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hexh z hz with hv | hv
    · exact Or.inl (by rw [e1, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inr (by rw [e2, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)
  · rcases hexh z hz with hv | hv
    · exact Or.inr (by rw [e2, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inl (by rw [e1, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)

end Schoenflies

/-! ## `lem:face-cycles`, with nothing assumed

`Graph.IsDrawing.hasFaceCycles_union` and `Graph.face_cycles` of
`Schoenflies/FaceCyclesProof.lean` carry the hypothesis `Schoenflies.CrosscutSplitsRegion`;
`Schoenflies.crosscutSplitsRegion` above proves it, so here are the two statements with the
hypothesis discharged. **These are the forms a consumer should use.** Once this module's
`PrePolygon` development is hoisted above `Schoenflies/FaceCyclesProof.lean` the hypothesis can
be deleted from the originals and the primes here dropped. -/

/-! ### Upstream module `MerLeanExperiment/FaceSystem.lean` -/

section
open _root_.Set Schoenflies

section
variable {β : Type u}

open _root_.Graph in
/-- A named actual face and an edge list obtained by permuting one of its simple boundaries. -/
def _root_.Graph.IsBoundaryList (G : Graph Plane β) (drawing : β → ℝ → Plane)
    (U : Set Plane) (W : List β) : Prop :=
  ∃ (z : Plane) (e : β) (a b : Plane) (D : List β),
    z ∈ exterior G drawing ∧ U = face G drawing z ∧
    IsFaceCycle G drawing z e a b D ∧ W.Perm (e :: D)

open _root_.Graph in
/-- A finite enumeration of all actual faces with simple boundary edge lists.
This is internal output of ear induction, not a hypothesis defining planarity. -/
structure _root_.Graph.FaceSystem (G : Graph Plane β) (drawing : β → ℝ → Plane) where
  /-- Each pair contains an actual face and its boundary edge list. -/
  boundaries : Finset (Set Plane × List β)
  /-- Every recorded boundary is a simple cycle of this graph. -/
  valid : ∀ q ∈ boundaries, IsBoundaryList G drawing q.1 q.2
  /-- No actual face is recorded twice. -/
  unique : Set.InjOn Prod.fst (↑boundaries : Set (Set Plane × List β))
  /-- Every component of the graph's complement is recorded. -/
  exhaustive : ∀ z ∈ exterior G drawing, ∃ q ∈ boundaries, q.1 = face G drawing z

open _root_.Graph in
/-- The number of faces in the finite enumeration. -/
def _root_.Graph.FaceSystem.faceCount {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem G drawing) : ℕ := M.boundaries.card

open _root_.Graph in
/-- Total original-edge boundary length; geometric segment counts play no role. -/
def _root_.Graph.FaceSystem.boundaryLength {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem G drawing) : ℕ := ∑ q ∈ M.boundaries, q.2.length

end

end

/-! ### Upstream module `MerLeanExperiment/FaceSystemBasics.lean` -/

section
open _root_.Set Schoenflies

section
variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {U : Set Plane} {W : List β}

open _root_.Graph in
/-- An actual enumerated face is nonempty. -/
theorem _root_.Graph.IsBoundaryList.nonempty (h : IsBoundaryList G drawing U W) : U.Nonempty := by
  obtain ⟨z, e, a, b, D, hz, rfl, hface, hperm⟩ := h
  exact ⟨z, mem_face hz⟩

open _root_.Graph in
/-- An actual face lies in the complement of the drawn graph. -/
theorem _root_.Graph.IsBoundaryList.subset_exterior (h : IsBoundaryList G drawing U W) :
    U ⊆ exterior G drawing := by
  obtain ⟨z, e, a, b, D, hz, rfl, hface, hperm⟩ := h
  exact face_subset_exterior G drawing z

open _root_.Graph in
/-- Any point in an actual face names that same connected component. -/
theorem _root_.Graph.IsBoundaryList.face_eq (h : IsBoundaryList G drawing U W)
    {z : Plane} (hz : z ∈ U) : face G drawing z = U := by
  obtain ⟨x, e, a, b, D, hx, rfl, hface, hperm⟩ := h
  exact (connectedComponentIn_eq hz).symm

open _root_.Graph in
/-- Distinct entries in the face enumeration have disjoint actual regions. -/
theorem _root_.Graph.FaceSystem.disjoint_regions (M : FaceSystem G drawing)
    {q r : Set Plane × List β} (hq : q ∈ M.boundaries) (hr : r ∈ M.boundaries)
    (hne : q ≠ r) : Disjoint q.1 r.1 := by
  obtain ⟨zq, eq, aq, bq, Dq, hzq, hqface, hcycleq, hpermq⟩ := M.valid q hq
  obtain ⟨zr, er, ar, br, Dr, hzr, hrface, hcycler, hpermr⟩ := M.valid r hr
  rcases face_eq_or_disjoint (G := G) (drawing := drawing) zq zr with heq | hdisj
  · exact False.elim <| hne <| M.unique (by simpa using hq) (by simpa using hr) <|
      hqface.trans (heq.trans hrface.symm)
  · rw [hqface, hrface]
    exact hdisj

end

end

/-! ### Upstream module `MerLeanExperiment/CycleFaceSystem.lean` -/

section
open scoped _root_.Graph Classical
open _root_.Set Schoenflies

open _root_.Graph in
/-- The graph spanned by a drawn cycle has its two actual regions as faces,
with two copies of the same boundary edge list. -/
theorem _root_.Graph.IsDrawing.exists_cycle_faceSystem
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    {e : β} {a b : Plane} {D : List β} (hc : G.IsCycleThrough e a b D) :
    ∃ M : FaceSystem (G.cycleGraph a e D) drawing,
      M.faceCount = 2 ∧ M.boundaryLength = 2 * (e :: D).length := by
  let C := edgesCover drawing (e :: D)
  let H := G.cycleGraph a e D
  let W := e :: D
  have hsep : IsSeparating C := h.cycle_isSeparating hpoly hc
  have hcyc : H.IsCycleThrough e a b D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]
        exact List.mem_append_left _ hg,
      hc.notMem⟩
  obtain ⟨zi, hzi⟩ := hsep.isConnected_inside.nonempty
  obtain ⟨zo, hzo⟩ := hsep.isConnected_outside.nonempty
  have hziExt : zi ∈ exterior H drawing := by
    rw [exterior, h.pointSet_cycleGraph hc]
    exact inside_subset_compl hzi
  have hzoExt : zo ∈ exterior H drawing := by
    rw [exterior, h.pointSet_cycleGraph hc]
    exact outside_subset_compl hzo
  have hfacei : face H drawing zi = inside C := by
    rw [face, exterior, h.pointSet_cycleGraph hc]
    exact hsep.connectedComponentIn_eq_inside hzi
  have hfaceo : face H drawing zo = outside C := by
    rw [face, exterior, h.pointSet_cycleGraph hc]
    exact hsep.connectedComponentIn_eq_outside hzo
  have hboundaryi : IsBoundaryList H drawing (inside C) W := by
    refine ⟨zi, e, a, b, D, hziExt, hfacei.symm, ?_, List.Perm.refl W⟩
    exact ⟨hcyc, hsep, hfacei ▸ IsRegionOf.inside C⟩
  have hboundaryo : IsBoundaryList H drawing (outside C) W := by
    refine ⟨zo, e, a, b, D, hzoExt, hfaceo.symm, ?_, List.Perm.refl W⟩
    exact ⟨hcyc, hsep, hfaceo ▸ IsRegionOf.outside C⟩
  have hregions : inside C ≠ outside C := by
    intro heq
    exact Set.disjoint_left.mp disjoint_inside_outside hzi (heq ▸ hzi)
  let qi : Set Plane × List β := (inside C, W)
  let qo : Set Plane × List β := (outside C, W)
  have hqne : qi ≠ qo := fun heq => hregions (congrArg Prod.fst heq)
  let M : FaceSystem H drawing :=
    { boundaries := {qi, qo}
      valid := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hboundaryi
        · exact hboundaryo
      unique := by
        intro q hq r hr hqr
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hq hr
        rcases hq with rfl | rfl <;> rcases hr with rfl | rfl
        · rfl
        · exact False.elim (hregions hqr)
        · exact False.elim (hregions hqr.symm)
        · rfl
      exhaustive := by
        intro z hz
        have hreg : IsRegionOf C (face H drawing z) := by
          rw [face, exterior, h.pointSet_cycleGraph hc]
          rw [exterior, h.pointSet_cycleGraph hc] at hz
          exact hsep.isRegionOf_connectedComponentIn hz
        rcases hreg with hreg | hreg
        · exact ⟨qi, by simp, hreg.symm⟩
        · exact ⟨qo, by simp, hreg.symm⟩ }
  refine ⟨M, ?_, ?_⟩
  · simp [M, FaceSystem.faceCount, hqne]
  · simp [M, FaceSystem.boundaryLength, hqne, qi, qo, W]
    omega

end

/-! ### Upstream module `MerLeanExperiment/PathCounts.lean` -/

section
variable {α β : Type*} {G : Graph α β} {a b c : α} {e : β} {W : List β}

open _root_.Graph in
/-- A simple path visits one more vertex than its number of edges. -/
theorem _root_.Graph.IsPath.ncard_walkVertices (h : G.IsPath a W b) :
    (G.walkVertices a W).ncard = W.length + 1 := by
  induction h with
  | nil => simp [walkVertices_nil]
  | cons he hW hfresh ih =>
      rw [walkVertices_cons he, Set.ncard_insert_of_notMem hfresh hW.isWalk.finite_walkVertices,
        ih]
      simp

open _root_.Graph in
/-- The edge set of the graph spanned by a simple path has exactly the path length. -/
theorem _root_.Graph.IsPath.ncard_pathGraphOf_edges (h : G.IsPath a W b) :
    E(G.pathGraphOf a W).ncard = W.length := by
  classical
  rw [pathGraphOf_edgeSet h.isWalk]
  have hset : {e | e ∈ W} = (↑W.toFinset : Set β) := by
    ext f
    simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup h.nodup]

end

/-! ### Upstream module `MerLeanExperiment/CycleCounts.lean` -/

section
variable {α β : Type*} {G : Graph α β} {a b : α} {e : β} {W : List β}

open _root_.Graph in
/-- The cycle graph has one vertex per boundary edge. -/
theorem _root_.Graph.IsCycleThrough.ncard_cycleGraph_vertices (h : G.IsCycleThrough e a b W) :
    V(G.cycleGraph a e W).ncard = (e :: W).length := by
  rw [h.cycleGraph_vertexSet, h.isPath.ncard_walkVertices]
  simp

open _root_.Graph in
/-- The cycle graph's boundary edge list enumerates its edges without repetition. -/
theorem _root_.Graph.IsCycleThrough.ncard_cycleGraph_edges (h : G.IsCycleThrough e a b W) :
    E(G.cycleGraph a e W).ncard = (e :: W).length := by
  classical
  rw [h.cycleGraph_edgeSet]
  have hn_cons : (e :: W).Nodup := List.nodup_cons.2 ⟨h.notMem, h.isPath.nodup⟩
  have hn : (W ++ [e]).Nodup := List.nodup_append_comm.mp (by simpa using hn_cons)
  have hset : {f | f ∈ W ++ [e]} = (↑(W ++ [e]).toFinset : Set β) := by
    ext f
    simp [or_comm]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hn]
  simp

end

/-! ### Upstream module `MerLeanExperiment/EarGeometry.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license.
Adapted from Schoenflies/FaceCyclesProof.lean at
05a43d29cde026618777db3d4e4316204ccca237, hasFaceCycles_union.
-/

open _root_.Set Schoenflies

open _root_.Graph in
/-- Splitting a genuine face boundary at an ear's endpoints produces the two
separating polygonal curves used by the exact crosscut theorem. -/
theorem _root_.Graph.IsDrawing.ear_split_geometry
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B))
    {z : Plane} (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    {e : β} {u v : Plane} {D : List β} (hface : IsFaceCycle B drawing z e u v D) :
    ∃ D₁ D₂ : List β,
      B.IsPath a D₁ b ∧ B.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      IsArcBetween (edgesCover drawing D₁) a b ∧
      IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} ∧
      edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) ∧
      edgesCover drawing P ∩ edgesCover drawing (e :: D) = {a, b} ∧
      IsSeparating (edgesCover drawing D₁ ∪ edgesCover drawing P) ∧
      IsSeparating (edgesCover drawing D₂ ∪ edgesCover drawing P) := by
  have : B.Finite := Graph.Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : P ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a P ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a P) ≤ G := union_le hBG hPG
  have hB' : IsDrawing (B.union (G.pathGraphOf a P)) drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B.union (G.pathGraphOf a P)), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hParc : IsArcBetween (edgesCover drawing P) a b :=
    h.path_isArcBetween hpath hne
  have hopenF : IsOpen (face B drawing z) := hB.isOpen_face z
  obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub
  have hfr : frontier (face B drawing z) = edgesCover drawing (e :: D) :=
    hface.frontier_eq
  have haW : a ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
  have hbW : b ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
  obtain ⟨D₁, D₂, hD₁, hD₂, hperm, hmeet⟩ :=
    hface.isCycle.split_at haW hbW hab
  have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
    hface.isCycle.isPath.nodup⟩
  have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
    (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
  obtain ⟨harc₁, harc₂, hinter⟩ :=
    hB.arcs_of_split hD₁ hD₂ hab hdisj hmeet
  have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ =
      edgesCover drawing (e :: D) := by
    rw [← edgesCover_append, edgesCover_perm hperm]
  have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
    edgesCover_subset_pointSet fun g hg => by
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact hface.isCycle.isLink.edge_mem
      · exact hface.isCycle.isPath.edge_mem hg'
  have hmeetJ : edgesCover drawing P ∩ edgesCover drawing (e :: D) = {a, b} := by
    refine Set.Subset.antisymm (fun w hw =>
      h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
    rintro w (rfl | rfl)
    · exact ⟨hParc.left_mem, hfr ▸ haF⟩
    · exact ⟨hParc.right_mem, hfr ▸ hbF⟩
  obtain ⟨f₁, x₁, y₁, T₁, hcyc₁, hperm₁⟩ :=
    exists_spliced_cycle hBG hD₁ hpath hab hnew hint
  have hsep₁ : IsSeparating (edgesCover drawing D₁ ∪ edgesCover drawing P) := by
    have hcov : edgesCover drawing (f₁ :: T₁) =
        edgesCover drawing D₁ ∪ edgesCover drawing P := by
      rw [edgesCover_perm hperm₁, edgesCover_append]
    rw [← hcov]
    exact hB'.cycle_isSeparating hpoly' hcyc₁
  obtain ⟨f₂, x₂, y₂, T₂, hcyc₂, hperm₂⟩ :=
    exists_spliced_cycle hBG hD₂.reverse hpath hab hnew hint
  have hsep₂ : IsSeparating (edgesCover drawing D₂ ∪ edgesCover drawing P) := by
    have hcov : edgesCover drawing (f₂ :: T₂) =
        edgesCover drawing D₂ ∪ edgesCover drawing P := by
      rw [edgesCover_perm hperm₂, edgesCover_append, edgesCover_reverse]
    rw [← hcov]
    exact hB'.cycle_isSeparating hpoly' hcyc₂
  exact ⟨D₁, D₂, hD₁, hD₂, hperm, harc₁, harc₂, hinter, hunion,
    hmeetJ, hsep₁, hsep₂⟩

end

/-! ### Upstream module `MerLeanExperiment/CrosscutRegions.lean` -/

namespace Schoenflies

/-- Elementary region selection for a crosscut. -/
theorem region_eq_right_of_disjoint
    {C W V S R : Set Plane}
    (hWV : IsRegionPair C W V)
    (hR : IsRegionOf C R)
    (hne : S.Nonempty) (hSW : S ⊆ W)
    (hRS : Disjoint R S) : R = V := by
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hR with hR | hR
    · subst R
      obtain ⟨x, hxS⟩ := hne
      exact False.elim (Set.disjoint_left.mp hRS (hSW hxS) hxS)
    · exact hR
  · rcases hR with hR | hR
    · exact hR
    · subst R
      obtain ⟨x, hxS⟩ := hne
      exact False.elim (Set.disjoint_left.mp hRS (hSW hxS) hxS)

/-- Elementary region selection for a crosscut. -/
theorem oppositeRegion_disjoint_crosscut_curve
    {J A P Ω Ω' : Set Plane} {p q : Plane}
    (hΩ : IsRegionPair J Ω Ω')
    (hAJ : A ⊆ J)
    (hends : ({p, q} : Set Plane) ⊆ J)
    (hPsub : P \ {p, q} ⊆ Ω) :
    Disjoint Ω' (A ∪ P) := by
  rw [Set.disjoint_left]
  intro x hxΩ' hx
  rcases hx with hxA | hxP
  · exact (hΩ.right.subset_compl hxΩ') (hAJ hxA)
  · by_cases hxend : x ∈ ({p, q} : Set Plane)
    · exact (hΩ.right.subset_compl hxΩ') (hends hxend)
    · exact Set.disjoint_left.mp hΩ.disjoint (hPsub ⟨hxP, hxend⟩) hxΩ'

end Schoenflies

/-! ### Upstream module `MerLeanExperiment/CrosscutComponents.lean` -/

section
open _root_.Set
namespace Schoenflies

/-- Matching actual components of a region partition. -/
theorem component_eq_one_of_two_regions
    {J₁ J₂ W₁ V₁ W₂ V₂ S T : Set Plane}
    (hWV₁ : IsRegionPair J₁ W₁ V₁)
    (hWV₂ : IsRegionPair J₂ W₂ V₂)
    (hSne : S.Nonempty)
    (hSW₁ : S ⊆ W₁) (hSW₂ : S ⊆ W₂)
    (hTS : Disjoint T S)
    (hexhaust : ∀ z ∈ T,
      IsRegionOf J₁ (connectedComponentIn T z) ∨
      IsRegionOf J₂ (connectedComponentIn T z)) :
    ∀ z ∈ T,
      connectedComponentIn T z = V₁ ∨
      connectedComponentIn T z = V₂ := by
  intro z hz
  have hcomponent : Disjoint (connectedComponentIn T z) S :=
    hTS.mono (connectedComponentIn_subset T z) Subset.rfl
  rcases hexhaust z hz with hregion | hregion
  · exact Or.inl <|
      region_eq_right_of_disjoint hWV₁ hregion hSne hSW₁ hcomponent
  · exact Or.inr <|
      region_eq_right_of_disjoint hWV₂ hregion hSne hSW₂ hcomponent

/-- Matching actual components of a region partition. -/
theorem eq_union_and_disjoint_of_two_components
    {T V₁ V₂ : Set Plane}
    (hV₁ : V₁ ⊆ T) (hV₂ : V₂ ⊆ T)
    (hc₁ : ∀ z ∈ V₁, connectedComponentIn T z = V₁)
    (hc₂ : ∀ z ∈ V₂, connectedComponentIn T z = V₂)
    (hne : V₁ ≠ V₂)
    (hexhaust : ∀ z ∈ T,
      connectedComponentIn T z = V₁ ∨
      connectedComponentIn T z = V₂) :
    T = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ := by
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      have hzcomponent : z ∈ connectedComponentIn T z :=
        mem_connectedComponentIn hz
      rcases hexhaust z hz with hcomponent | hcomponent
      · exact Or.inl (hcomponent ▸ hzcomponent)
      · exact Or.inr (hcomponent ▸ hzcomponent)
    · intro z hz
      rcases hz with hz | hz
      · exact hV₁ hz
      · exact hV₂ hz
  · rw [Set.disjoint_left]
    intro z hz₁ hz₂
    apply hne
    calc
      V₁ = connectedComponentIn T z := (hc₁ z hz₁).symm
      _ = V₂ := hc₂ z hz₂

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/CrosscutExact.lean` -/

section
open _root_.Set
namespace Schoenflies

/-- A crosscut splits either old region into exactly two actual components. -/
theorem crosscut_exactly_two_components
    {J A₁ A₂ P Ω : Set Plane} {p q : Plane}
    (hJ : IsSeparating J)
    (hJpoly : IsPolygonal J) (hPpoly : IsPolygonal P)
    (hA₁ : IsArcBetween A₁ p q) (hA₂ : IsArcBetween A₂ p q)
    (hunion : A₁ ∪ A₂ = J)
    (hinter : A₁ ∩ A₂ = {p, q})
    (hP : IsArcBetween P p q) (hPJ : P ∩ J = {p, q})
    (hΩ : IsRegionOf J Ω) (hPsub : P \ {p, q} ⊆ Ω)
    (hJ₁ : IsSeparating (A₁ ∪ P))
    (hJ₂ : IsSeparating (A₂ ∪ P)) :
    ∃ V₁ V₂ : Set Plane,
      IsRegionOf (A₁ ∪ P) V₁ ∧ IsRegionOf (A₂ ∪ P) V₂ ∧
      V₁.Nonempty ∧ V₂.Nonempty ∧ V₁ ≠ V₂ ∧
      Ω \ P = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ ∧
      (∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      frontier V₁ = A₁ ∪ P ∧ frontier V₂ = A₂ ∪ P := by
  have hA₁J : A₁ ⊆ J := by
    rw [← hunion]
    exact Set.subset_union_left
  have hA₂J : A₂ ⊆ J := by
    rw [← hunion]
    exact Set.subset_union_right
  have hends : ({p, q} : Set Plane) ⊆ J := by
    rintro z (rfl | rfl)
    · exact hA₁J hA₁.left_mem
    · exact hA₁J hA₁.right_mem
  have hendsA₁ : ({p, q} : Set Plane) ⊆ A₁ := by
    rintro z (rfl | rfl)
    · exact hA₁.left_mem
    · exact hA₁.right_mem
  have hendsA₂ : ({p, q} : Set Plane) ⊆ A₂ := by
    rintro z (rfl | rfl)
    · exact hA₂.left_mem
    · exact hA₂.right_mem
  have hP₁ : P ∩ J ⊆ A₁ := by
    rw [hPJ]
    exact hendsA₁
  have hP₂ : P ∩ J ⊆ A₂ := by
    rw [hPJ]
    exact hendsA₂
  have hA₁ne : A₁ ≠ A₂ := by
    apply arcs_ne (le_of_eq hinter)
    obtain ⟨z, hzA₁, hzends⟩ := hA₁.nonempty_diff
    exact fun hsub => hzends (hsub hzA₁)
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with hΩ | hΩ
    · exact ⟨outside J, Or.inl ⟨hΩ, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨hΩ, rfl⟩⟩
  have hΩ'conn := hΩpair.right.isConnected hJ
  have hΩ'A₁P : Disjoint Ω' (A₁ ∪ P) :=
    oppositeRegion_disjoint_crosscut_curve hΩpair hA₁J hends hPsub
  have hΩ'A₂P : Disjoint Ω' (A₂ ∪ P) :=
    oppositeRegion_disjoint_crosscut_curve hΩpair hA₂J hends hPsub
  obtain ⟨W₁, V₁, hWV₁, hΩW₁⟩ :=
    hJ₁.exists_isRegionPair_subset hΩ'conn.isPreconnected hΩ'conn.nonempty hΩ'A₁P
  obtain ⟨W₂, V₂, hWV₂, hΩW₂⟩ :=
    hJ₂.exists_isRegionPair_subset hΩ'conn.isPreconnected hΩ'conn.nonempty hΩ'A₂P
  obtain ⟨⟨hV₁sub, hc₁⟩, ⟨hV₂sub, hc₂⟩, hVne, -, -⟩ :=
    crosscut_cells hJ hJ₁ hJ₂ hA₁J hA₂J hP₁ hP₂ hA₁ne hΩpair
      hWV₁ hΩW₁ hWV₂ hΩW₂
  have hexhaust :=
    crosscutSplitsRegion J A₁ A₂ P Ω p q hJ hJpoly hPpoly hA₁ hA₂ hunion hinter
      hP hPJ hΩpair.left hPsub
  have hdiff : Disjoint (Ω \ P) Ω' :=
    hΩpair.disjoint.mono sdiff_subset Subset.rfl
  have hcomponents := component_eq_one_of_two_regions hWV₁ hWV₂ hΩ'conn.nonempty
    hΩW₁ hΩW₂ hdiff hexhaust
  obtain ⟨hpartition, hVdisjoint⟩ :=
    eq_union_and_disjoint_of_two_components hV₁sub hV₂sub hc₁ hc₂ hVne hcomponents
  exact ⟨V₁, V₂, hWV₁.right, hWV₂.right,
    (hWV₁.right.isConnected hJ₁).nonempty, (hWV₂.right.isConnected hJ₂).nonempty,
    hVne, hpartition, hVdisjoint, hc₁, hc₂,
    hWV₁.right.frontier_eq hJ₁, hWV₂.right.frontier_eq hJ₂⟩

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/SplicedBoundary.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- A component cut from an old face is the actual face bounded by its spliced cycle. -/
theorem _root_.Graph.IsDrawing.spliced_boundaryList
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {A P : List β} (hA : B.IsPath a A b) (hpath : G.IsPath a P b)
    (hab : a ≠ b) (hnew : ∀ g ∈ P, g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    {z : Plane} {U : Set Plane} (hUne : U.Nonempty)
    (hsub : U ⊆ face B drawing z \ edgesCover drawing P)
    (hc : ∀ w ∈ U,
      connectedComponentIn (face B drawing z \ edgesCover drawing P) w = U)
    (hregion : IsRegionOf (edgesCover drawing A ∪ edgesCover drawing P) U) :
    IsBoundaryList (B.union (G.pathGraphOf a P)) drawing U (A ++ P) := by
  obtain ⟨f, x, y, T, hcyc, hperm⟩ :=
    exists_spliced_cycle hBG hA hpath hab hnew hint
  let H := B.union (G.pathGraphOf a P)
  have hPG : G.pathGraphOf a P ≤ G := pathGraphOf_le hpath.isWalk
  have hHG : H ≤ G := union_le hBG hPG
  have hH : IsDrawing H drawing := h.mono hHG
  have hpolyH : ∀ g ∈ E(H), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hHG.edgeSet_mono hg)
  have hne : P ≠ [] := hpath.ne_nil hab
  have hext : exterior H drawing = exterior B drawing \ edgesCover drawing P := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  obtain ⟨w, hwU⟩ := hUne
  obtain ⟨hwface, hwP⟩ := hsub hwU
  have hwext : w ∈ exterior H drawing := by
    rw [hext]
    exact ⟨face_subset_exterior B drawing z hwface, hwP⟩
  have holdface : face B drawing w = face B drawing z :=
    (connectedComponentIn_eq hwface).symm
  change connectedComponentIn (exterior B drawing) w = face B drawing z at holdface
  have hface : face H drawing w = U := by
    have hstep : face H drawing w =
        connectedComponentIn (exterior B drawing \ edgesCover drawing P) w := by
      rw [face, hext]
    rw [hstep, Schoenflies.connectedComponentIn_diff, holdface]
    exact hc w hwU
  have hcover : edgesCover drawing (f :: T) =
      edgesCover drawing A ∪ edgesCover drawing P := by
    rw [edgesCover_perm hperm, edgesCover_append]
  have hfaceCycle : IsFaceCycle H drawing w f x y T := by
    refine ⟨hcyc, hH.cycle_isSeparating hpolyH hcyc, ?_⟩
    rw [hcover, hface]
    exact hregion
  exact ⟨w, f, x, y, T, hwext, hface.symm, hfaceCycle, hperm.symm⟩

end

/-! ### Upstream module `MerLeanExperiment/EarFaceSplit.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- The affected old face splits into two actual new faces with the exact edge-length balance. -/
theorem _root_.Graph.IsDrawing.ear_face_split
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B))
    {z : Plane} (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    {e : β} {u v : Plane} {D : List β} (hface : IsFaceCycle B drawing z e u v D) :
    ∃ q₁ q₂ : Set Plane × List β,
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing q₁.1 q₁.2 ∧
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing q₂.1 q₂.2 ∧
      q₁.1 ≠ q₂.1 ∧
      face B drawing z \ edgesCover drawing P = q₁.1 ∪ q₂.1 ∧
      q₁.2.length + q₂.2.length = (e :: D).length + 2 * P.length := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hperm, harc₁, harc₂, hinter, hunion,
      hmeet, hsep₁, hsep₂⟩ :=
    h.ear_split_geometry hpoly hBG hpath hab ha hb hint hnew hsub hface
  have hne : P ≠ [] := hpath.ne_nil hab
  have hPArc : IsArcBetween (edgesCover drawing P) a b :=
    h.path_isArcBetween hpath hne
  have hJpoly : IsPolygonal (edgesCover drawing (e :: D)) :=
    h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
      (List.cons_ne_nil e D)
  have hPpoly : IsPolygonal (edgesCover drawing P) :=
    h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  obtain ⟨U₁, U₂, hreg₁, hreg₂, hU₁ne, hU₂ne, hUne, hpartition,
      hUdisj, hc₁, hc₂, hfront₁, hfront₂⟩ :=
    crosscut_exactly_two_components hface.isSeparating hJpoly hPpoly harc₁
      harc₂.reverse hunion hinter hPArc hmeet hface.isRegionOf hsub hsep₁ hsep₂
  have hU₁sub : U₁ ⊆ face B drawing z \ edgesCover drawing P := by
    rw [hpartition]
    exact Set.subset_union_left
  have hU₂sub : U₂ ⊆ face B drawing z \ edgesCover drawing P := by
    rw [hpartition]
    exact Set.subset_union_right
  have hboundary₁ : IsBoundaryList (B.union (G.pathGraphOf a P)) drawing
      U₁ (D₁ ++ P) :=
    h.spliced_boundaryList hpoly hBG hD₁ hpath hab hnew hint hU₁ne hU₁sub hc₁ hreg₁
  have hboundary₂ : IsBoundaryList (B.union (G.pathGraphOf a P)) drawing
      U₂ (D₂.reverse ++ P) := by
    apply h.spliced_boundaryList hpoly hBG hD₂.reverse hpath hab hnew hint
      hU₂ne hU₂sub hc₂
    simpa only [edgesCover_reverse] using hreg₂
  have hlength : D₁.length + D₂.length = (e :: D).length := by
    simpa only [List.length_append] using hperm.length_eq
  refine ⟨(U₁, D₁ ++ P), (U₂, D₂.reverse ++ P), hboundary₁, hboundary₂,
    hUne, hpartition, ?_⟩
  simp only [List.length_append, List.length_reverse]
  omega

end

/-! ### Upstream module `MerLeanExperiment/UnaffectedFaces.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- An actual face untouched by an added graph keeps its original cycle boundary. -/
theorem _root_.Graph.IsBoundaryList.mono_union_of_disjoint
    {β : Type*} {B P : Graph Plane β} {drawing : β → ℝ → Plane}
    {U : Set Plane} {W : List β} (hU : IsBoundaryList B drawing U W)
    (hdis : Disjoint U (pointSet P drawing)) :
    IsBoundaryList (B.union P) drawing U W := by
  obtain ⟨z, e, a, b, D, hz, hUface, hface, hperm⟩ := hU
  have hdisface : Disjoint (face B drawing z) (pointSet P drawing) := by
    rw [← hUface]
    exact hdis
  have hzunion : z ∈ exterior (B.union P) drawing := by
    rw [exterior_union]
    exact ⟨hz, fun hzP => Set.disjoint_left.mp hdisface (mem_face hz) hzP⟩
  have hfaceeq : face (B.union P) drawing z = face B drawing z :=
    face_union_eq_of_disjoint hz hdisface
  exact ⟨z, e, a, b, D, hzunion, hUface.trans hfaceeq.symm,
    hface.mono (left_le_union B P) hfaceeq, hperm⟩

open _root_.Graph in
/-- An ear lying in one old face misses each other actual face. -/
theorem _root_.Graph.IsDrawing.ear_disjoint_of_other_face
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
    (h : IsDrawing G drawing) {a b z : Plane} {P W : List β} {U : Set Plane}
    (hpath : G.IsPath a P b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    (hU : IsBoundaryList B drawing U W) (hdis : Disjoint U (face B drawing z)) :
    Disjoint U (pointSet (G.pathGraphOf a P) drawing) := by
  have hne : P ≠ [] := hpath.ne_nil hab
  rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
  intro w hwU hwP
  have hwext : w ∈ exterior B drawing := hU.subset_exterior hwU
  have hwends : w ∉ ({a, b} : Set Plane) := by
    rintro (rfl | rfl)
    · exact hwext (vertexSet_subset_pointSet ha)
    · exact hwext (vertexSet_subset_pointSet hb)
  exact Set.disjoint_left.mp hdis hwU (hsub ⟨hwP, hwends⟩)

end

/-! ### Upstream module `MerLeanExperiment/FinsetReplacement.lean` -/

section
variable {α : Type*} [DecidableEq α]

open _root_.Finset in
/-- Replacing one old item by two fresh distinct items increases cardinality by one. -/
theorem _root_.Finset.card_replace_one_by_two (s : Finset α) {q a b : α}
    (hq : q ∈ s) (ha : a ∉ s.erase q) (hb : b ∉ s.erase q) (hab : a ≠ b) :
    (insert a (insert b (s.erase q))).card = s.card + 1 := by
  rw [card_insert_of_notMem (by simp [ha, hab]), card_insert_of_notMem hb,
    card_erase_add_one hq]

open _root_.Finset in
/-- The weight of a one-to-two replacement differs by the removed and added weights. -/
theorem _root_.Finset.sum_replace_one_by_two (s : Finset α) (w : α → ℕ) {q a b : α}
    (hq : q ∈ s) (ha : a ∉ s.erase q) (hb : b ∉ s.erase q) (hab : a ≠ b) :
    (∑ x ∈ insert a (insert b (s.erase q)), w x) + w q =
      (∑ x ∈ s, w x) + w a + w b := by
  rw [sum_insert (by simp [ha, hab]), sum_insert hb]
  have hsum := sum_erase_add s w hq
  omega

end

/-! ### Upstream module `MerLeanExperiment/FaceReplacement.lean` -/

section
open scoped _root_.Graph Classical
open _root_.Set Schoenflies

open _root_.Graph in
/-- Replace one old face by two actual new faces while preserving the complete enumeration.
Every geometric input is supplied by the crosscut and unaffected-face lemmas at the ear step. -/
theorem _root_.Graph.FaceSystem.exists_replacement
    {β : Type*} {B H : Graph Plane β} {drawing : β → ℝ → Plane}
    (M : FaceSystem B drawing) (q q₁ q₂ : Set Plane × List β) (hq : q ∈ M.boundaries)
    (hv₁ : IsBoundaryList H drawing q₁.1 q₁.2)
    (hv₂ : IsBoundaryList H drawing q₂.1 q₂.2) (hne : q₁.1 ≠ q₂.1)
    (hsub₁ : q₁.1 ⊆ q.1) (hsub₂ : q₂.1 ⊆ q.1)
    (hsurvive : ∀ r ∈ M.boundaries, r ≠ q → IsBoundaryList H drawing r.1 r.2)
    (hext : exterior H drawing ⊆ exterior B drawing)
    (hcover : ∀ z ∈ exterior H drawing, z ∈ q.1 → z ∈ q₁.1 ∨ z ∈ q₂.1) :
    ∃ M' : FaceSystem H drawing,
      M'.boundaries = insert q₁ (insert q₂ (M.boundaries.erase q)) ∧
      M'.faceCount = M.faceCount + 1 ∧
      M'.boundaryLength + q.2.length =
        M.boundaryLength + q₁.2.length + q₂.2.length := by
  let old := M.boundaries.erase q
  have hfresh₁ : q₁ ∉ old := by
    intro hmem
    have hr := (Finset.mem_erase.mp hmem).2
    have hrq := (Finset.mem_erase.mp hmem).1
    obtain ⟨z, hz⟩ := hv₁.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hr hrq.symm) (hsub₁ hz) hz
  have hfresh₂ : q₂ ∉ old := by
    intro hmem
    have hr := (Finset.mem_erase.mp hmem).2
    have hrq := (Finset.mem_erase.mp hmem).1
    obtain ⟨z, hz⟩ := hv₂.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hr hrq.symm) (hsub₂ hz) hz
  have hq₁q₂ : q₁ ≠ q₂ := fun h ↦ hne (congrArg Prod.fst h)
  have hregion₁ : ∀ r ∈ old, q₁.1 ≠ r.1 := by
    intro r hr her
    have hrM := (Finset.mem_erase.mp hr).2
    have hrq := (Finset.mem_erase.mp hr).1
    obtain ⟨z, hz⟩ := hv₁.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hrM hrq.symm)
      (hsub₁ hz) (her ▸ hz)
  have hregion₂ : ∀ r ∈ old, q₂.1 ≠ r.1 := by
    intro r hr her
    have hrM := (Finset.mem_erase.mp hr).2
    have hrq := (Finset.mem_erase.mp hr).1
    obtain ⟨z, hz⟩ := hv₂.nonempty
    exact Set.disjoint_left.1 (M.disjoint_regions hq hrM hrq.symm)
      (hsub₂ hz) (her ▸ hz)
  let newBoundaries := insert q₁ (insert q₂ old)
  let M' : FaceSystem H drawing :=
    { boundaries := newBoundaries
      valid := by
        intro r hr
        simp only [newBoundaries, Finset.mem_insert] at hr
        rcases hr with rfl | rfl | hr
        · exact hv₁
        · exact hv₂
        · exact hsurvive r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
      unique := by
        intro r hr s hs hrs
        simp only [newBoundaries, Finset.coe_insert, Set.mem_insert_iff] at hr hs
        rcases hr with rfl | rfl | hr
        · rcases hs with rfl | rfl | hs
          · rfl
          · exact False.elim (hne hrs)
          · exact False.elim (hregion₁ s hs hrs)
        · rcases hs with rfl | rfl | hs
          · exact False.elim (hne hrs.symm)
          · rfl
          · exact False.elim (hregion₂ s hs hrs)
        · rcases hs with rfl | rfl | hs
          · exact False.elim (hregion₁ r hr hrs.symm)
          · exact False.elim (hregion₂ r hr hrs.symm)
          · exact M.unique (Finset.mem_erase.mp hr).2
              (Finset.mem_erase.mp hs).2 hrs
      exhaustive := by
        intro z hz
        obtain ⟨r, hr, hrface⟩ := M.exhaustive z (hext hz)
        have hzr : z ∈ r.1 := by
          rw [hrface]
          exact mem_face (hext hz)
        by_cases hrq : r = q
        · subst r
          rcases hcover z hz hzr with hz₁ | hz₂
          · exact ⟨q₁, by simp [newBoundaries], (hv₁.face_eq hz₁).symm⟩
          · exact ⟨q₂, by simp [newBoundaries], (hv₂.face_eq hz₂).symm⟩
        · have hrOld : r ∈ old := Finset.mem_erase.mpr ⟨hrq, hr⟩
          exact ⟨r, by simp [newBoundaries, hrOld],
            ((hsurvive r hr hrq).face_eq hzr).symm⟩ }
  refine ⟨M', rfl, ?_, ?_⟩
  · exact Finset.card_replace_one_by_two M.boundaries hq hfresh₁ hfresh₂ hq₁q₂
  · exact Finset.sum_replace_one_by_two M.boundaries (fun r ↦ r.2.length)
      hq hfresh₁ hfresh₂ hq₁q₂

end

/-! ### Upstream module `MerLeanExperiment/EarFaceSystem.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- Adding a proper ear constructs a full new face system, increasing its face count by one
and its total boundary length by twice the ear length. -/
theorem _root_.Graph.IsDrawing.exists_ear_faceSystem
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    (M : FaceSystem B drawing)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B)) :
    ∃ M' : FaceSystem (B.union (G.pathGraphOf a P)) drawing,
      M'.faceCount = M.faceCount + 1 ∧
      M'.boundaryLength = M.boundaryLength + 2 * P.length := by
  have hne : P ≠ [] := hpath.ne_nil hab
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  obtain ⟨q, hq, hqface⟩ := M.exhaustive z₀ hz₀
  obtain ⟨z₁, e, u, v, D, hz₁, hqface₁, hface, hperm⟩ := M.valid q hq
  have hfaces : face B drawing z₀ = face B drawing z₁ :=
    hqface.symm.trans hqface₁
  have hsub₁ : edgesCover drawing P \ {a, b} ⊆ face B drawing z₁ := by
    rw [← hfaces]
    exact hsub₀
  obtain ⟨q₁, q₂, hv₁, hv₂, hq₁q₂, hpartition, hlength⟩ :=
    h.ear_face_split hpoly hBG hpath hab ha hb hint hnew hsub₁ hface
  have hsubq₁ : q₁.1 ⊆ q.1 := by
    rw [hqface₁]
    intro z hz
    exact (hpartition.symm ▸ Set.mem_union_left q₂.1 hz).1
  have hsubq₂ : q₂.1 ⊆ q.1 := by
    rw [hqface₁]
    intro z hz
    exact (hpartition.symm ▸ Set.mem_union_right q₁.1 hz).1
  have hsurvive : ∀ r ∈ M.boundaries, r ≠ q →
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing r.1 r.2 := by
    intro r hr hrq
    have hdisOld : Disjoint r.1 q.1 := M.disjoint_regions hr hq hrq
    have hdisFace : Disjoint r.1 (face B drawing z₁) := by
      rw [← hqface₁]
      exact hdisOld
    exact (M.valid r hr).mono_union_of_disjoint <|
      h.ear_disjoint_of_other_face hpath hab ha hb hsub₁ (M.valid r hr) hdisFace
  have hext : exterior (B.union (G.pathGraphOf a P)) drawing ⊆
      exterior B drawing := by
    rw [exterior_union]
    exact Set.inter_subset_left
  have hcover : ∀ z ∈ exterior (B.union (G.pathGraphOf a P)) drawing,
      z ∈ q.1 → z ∈ q₁.1 ∨ z ∈ q₂.1 := by
    intro z hz hzq
    have hz' := hz
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne] at hz'
    have hzDiff : z ∈ face B drawing z₁ \ edgesCover drawing P :=
      ⟨hqface₁.symm ▸ hzq, hz'.2⟩
    have hzUnion : z ∈ q₁.1 ∪ q₂.1 := hpartition ▸ hzDiff
    exact hzUnion
  obtain ⟨M', _hM', hcount, hweight⟩ := M.exists_replacement q q₁ q₂ hq
    hv₁ hv₂ hq₁q₂ hsubq₁ hsubq₂ hsurvive hext hcover
  refine ⟨M', hcount, ?_⟩
  have hremoved : q.2.length = (e :: D).length := hperm.length_eq
  omega

end

/-! ### Upstream module `MerLeanExperiment/EarCounts.lean` -/

section
variable {α β : Type*} {G B : Graph α β} [G.Finite]
    {a b : α} {P : List β}

open _root_.Graph in
/-- A proper ear adds exactly its path length many new edges. -/
theorem _root_.Graph.ncard_edges_union_ear (hBG : B ≤ G) (hpath : G.IsPath a P b)
    (hnew : ∀ e ∈ P, e ∉ E(B)) :
    E(B.union (G.pathGraphOf a P)).ncard = E(B).ncard + P.length := by
  let _ : B.Finite := Graph.Finite.of_le hBG
  have hdisj : Disjoint E(B) {e | e ∈ P} :=
    Set.disjoint_left.2 fun _ heB heP ↦ hnew _ heP heB
  have hPfinite : {e | e ∈ P}.Finite := List.finite_toSet P
  rw [edgeSet_union_pathGraphOf hpath.isWalk,
    Set.ncard_union_eq hdisj (Graph.finite_edgeSet B) hPfinite]
  have hcount : {e | e ∈ P}.ncard = P.length := by
    rw [← pathGraphOf_edgeSet hpath.isWalk]
    exact hpath.ncard_pathGraphOf_edges
  rw [hcount]

open _root_.Graph in
/-- An ear with two old endpoints adds all its internal vertices and no others. -/
theorem _root_.Graph.ncard_vertices_union_ear (hBG : B ≤ G) (hpath : G.IsPath a P b)
    (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B)) :
    V(B.union (G.pathGraphOf a P)).ncard + 1 = V(B).ncard + P.length := by
  let _ : B.Finite := Graph.Finite.of_le hBG
  have hinter : V(B) ∩ G.walkVertices a P = {a, b} := by
    ext y
    constructor
    · rintro ⟨hyB, hyP⟩
      by_cases hya : y = a
      · simp [hya]
      by_cases hyb : y = b
      · simp [hyb]
      exact (hint y hyP hya hyb hyB).elim
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨ha, mem_walkVertices_self⟩
      · exact ⟨hb, hpath.target_mem_walkVertices⟩
  have hcard := Set.ncard_union_add_ncard_inter (V(B)) (G.walkVertices a P)
    (Graph.finite_vertexSet B) hpath.isWalk.finite_walkVertices
  rw [hinter, Set.ncard_pair hab, hpath.ncard_walkVertices] at hcard
  rw [vertexSet_union_pathGraphOf]
  omega

end

/-! ### Upstream module `MerLeanExperiment/EulerFaceSystem.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- Euler's formula and twice-per-edge boundary counting are constructed from an ordinary
polygonal drawing by cycle-and-ear induction. They are conclusions, not drawing certificates. -/
theorem _root_.Graph.IsDrawing.exists_euler_faceSystem
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Loopless] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (htwo : G.IsTwoConnected) :
    ∃ M : FaceSystem G drawing,
      V(G).ncard + M.faceCount = E(G).ncard + 2 ∧
      M.boundaryLength = 2 * E(G).ncard := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x ↦ Graph.not_isLoopAt G g x
  obtain ⟨e, u, v, D, w, hlong⟩ := htwo.exists_long_cycle hnl
  let motive := fun B : Graph Plane β ↦
    ∃ M : FaceSystem B drawing,
      V(B).ncard + M.faceCount = E(B).ncard + 2 ∧
      M.boundaryLength = 2 * E(B).ncard
  apply htwo.ear_decomposition (motive := motive) hnl hlong.isTwoConnected
    hlong.isCycle.cycleGraph_le
  · obtain ⟨M, hfaces, hlength⟩ :=
      h.exists_cycle_faceSystem hpoly hlong.isCycle
    refine ⟨M, ?_, ?_⟩
    · rw [hlong.isCycle.ncard_cycleGraph_vertices,
        hlong.isCycle.ncard_cycleGraph_edges, hfaces]
    · rw [hlength, hlong.isCycle.ncard_cycleGraph_edges]
  · intro B a b P _htwoB _hcycleB hBG hmot hpath hab ha hb hint
    rcases ear_edges_notMem_or_union_eq hBG hpath hab ha hb hint with hnew | heq
    · obtain ⟨M, heuler, hsum⟩ := hmot
      obtain ⟨M', hfaces, hlength⟩ :=
        h.exists_ear_faceSystem hpoly hBG M hpath hab ha hb hint hnew
      refine ⟨M', ?_, ?_⟩
      · have hvert := ncard_vertices_union_ear hBG hpath hab ha hb hint
        have hedge := ncard_edges_union_ear hBG hpath hnew
        omega
      · have hedge := ncard_edges_union_ear hBG hpath hnew
        omega
    · rw [heq]
      exact hmot

end

/-! ### Upstream module `MerLeanExperiment/BipartiteWalks.lean` -/

open _root_.Graph in
/-- The parity of a walk length determines the endpoint color. -/
theorem _root_.Graph.IsWalk.color_val_end
    {α β : Type*} {G : Graph α β} (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {a b : α} {W : List β} (h : G.IsWalk a W b) :
    (c b).val = ((c a).val + W.length) % 2 := by
  induction h with
  | @nil x hx =>
      simp only [List.length_nil, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (c x).isLt).symm
  | @cons u w v e W hl hW ih =>
      have hne : (c u).val ≠ (c w).val := by
        intro heq
        exact hcolor e u w hl (Fin.ext heq)
      have hstep : (c w).val = ((c u).val + 1) % 2 := by
        omega
      simp only [List.length_cons]
      omega

open _root_.Graph in
/-- A closed walk in a bipartite graph has even length. -/
theorem _root_.Graph.IsWalk.even_length_of_bicoloring
    {α β : Type*} {G : Graph α β} (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {a : α} {W : List β} (h : G.IsWalk a W a) : Even W.length := by
  have hend := h.color_val_end c hcolor
  have hmod : W.length % 2 = 0 := by
    omega
  exact even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hmod)

/-! ### Upstream module `MerLeanExperiment/SimpleCycleLength.lean` -/

open _root_.Graph in
/-- A simple cycle in a simple graph has at least three edges. -/
theorem _root_.Graph.IsCycleThrough.three_le_length
    {α β : Type*} {G : Graph α β} [G.Simple]
    {e : β} {a b : α} {W : List β} (h : G.IsCycleThrough e a b W) :
    3 ≤ (e :: W).length := by
  by_contra hlt
  have hWlt : W.length < 2 := by simp only [List.length_cons] at hlt; omega
  cases W with
  | nil =>
      exact h.isLink.ne h.isPath.isWalk.eq_of_nil
  | cons f T =>
      cases T with
      | nil =>
          have hlinkf : G.IsLink f a b := by
            cases h.isPath.isWalk with
            | @cons _ w _ _ _ hl htail =>
                have hwb : w = b := htail.eq_of_nil
                subst w
                exact hl
          have hef : e = f := h.isLink.eq hlinkf
          exact h.notMem (by simp [hef])
      | cons g T =>
          simp only [List.length_cons] at hWlt
          omega

open _root_.Graph in
/-- A simple cycle in a bipartite simple graph has at least four edges. -/
theorem _root_.Graph.IsCycleThrough.four_le_length_of_bicoloring
    {α β : Type*} {G : Graph α β} [G.Simple] (c : α → Fin 2)
    (hcolor : ∀ (e : β) (x y : α), G.IsLink e x y → c x ≠ c y)
    {e : β} {a b : α} {W : List β} (h : G.IsCycleThrough e a b W) :
    4 ≤ (e :: W).length := by
  have hclosed : G.IsWalk a (e :: W.reverse) a :=
    .cons h.isLink h.isPath.reverse.isWalk
  have heven : Even (e :: W).length := by
    simpa using hclosed.even_length_of_bicoloring c hcolor
  have hthree : 3 ≤ (e :: W).length := h.three_le_length
  obtain ⟨k, hk⟩ := heven
  omega

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/VertexSquares.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The vertex squares, the last parameter inside a closed set, and the cores

Three of the ordinary bricks of the polygonal redrawing of a finite plane graph.

**The vertex squares.** Around each vertex of a finite plane graph sits a closed axis-parallel
square which meets no other vertex and no edge arc of an edge not incident with that vertex.
One compact separation per other vertex and per non-incident arc, then the single-`ε`-for-all
lemma of `Schoenflies/UniformBound.lean`. Squares rather than disks because the assembly needs
the boundary to be made of segments; convexity, which the radial segments of the last step
want, both shapes have.

Because the choice is made once for all vertices rather than vertex by vertex, halving the
common radius also makes *distinct squares disjoint* — which the cores of the next brick need
and which the per-vertex statement does not give. That is why `exists_vertexSquares` is the
form to consume and `exists_square_at` only its ingredient.

**The last parameter inside a closed set.** The parameters at which an arc lies in a closed
set form a compact subset of the parameter interval; if it is nonempty its supremum is
attained, and past that supremum the arc has left the set for good. The mirror statement about
the infimum is what the far end of an edge wants: the arc leaves the square at `v` for the last
time and enters the square at `w` for the first time.

**The cores.** The subarc of an edge between those two parameters. It meets the square at `v`
in its own first endpoint only, the square at `w` in its own last endpoint only, and — the
clause the assembly really uses — it contains no vertex, which makes distinct cores disjoint
without any further estimate.

## Blueprint

Bricks B2, B3 and B4 of `lem:polygonal-redrawing`.

* `Plane.closedBall_subset_closedSquare`, `Plane.closedSquare_subset_ball` — a square sits
  inside a ball and vice versa, the comparison every separation argument passes through.
* `Plane.supDist_triangle`, `Plane.closedSquare_mono_center`, `Plane.mem_closedSquare_self` —
  square arithmetic missing from `Schoenflies/Square.lean`.
* `exists_last_mem_Icc`, `exists_first_mem_Icc`, `exists_last_mem`, `exists_first_mem` — B3,
  with `isCompact_parameters_mem` behind them.
* `Graph.IsDrawing.exists_square_at` — B2 at one vertex.
* `Graph.IsDrawing.exists_vertexSquares` — B2 as consumed: one radius for every vertex, with
  distinct squares disjoint.
* `Graph.IsDrawing.exists_core` — B4, the core of one edge.
* `Graph.IsDrawing.disjoint_of_subset_edgeArc` — B4's "distinct cores are disjoint".
* `Graph.IsDrawing.closedSquare_disjoint_edgeArc_of_ne` — B4's "meets no other vertex square",
  which is a property of the whole arc.
-/

open Metric _root_.Set unitInterval

namespace Schoenflies

namespace Plane

/-! ### Square arithmetic

`Schoenflies/Square.lean` has convexity, openness and closedness of `closedSquare` but no
triangle inequality for `supDist` and no monotonicity at a general centre; both are needed
here. -/

/-- Squares about a common centre grow with the radius. `Bounded.closedSquare_mono` says this
only about the origin. -/
theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

/-- The centre lies in its own square. -/
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

/-- The inscribed ball: a ball is inside the square of the same radius, since the sup norm is
at most the Euclidean norm. -/
theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

/-- The circumscribed ball, in the form the separations want: a square of *half* a given
radius sits inside the open ball of that radius, because `√2 < 2`. -/
theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

/-! ### B3 — the last point of an arc inside a closed set -/

/-- The parameters at which a curve lies in a closed set form a compact subset of the
parameter interval: the parametrisation is continuous there and the interval is compact.

Stated over an arbitrary `Icc` and not only over `[0, 1]`, because the *second* use of B3 —
the first entry into the far vertex's square — has to happen after the last exit from the near
one, i.e. on the interval `[a, 1]`. -/
theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

/-- The last parameter inside a closed set. Given one parameter whose point lies in `C`, there
is a largest one: the curve is in `C` there, and at every larger parameter of the interval it
has left `C` for good.

This is the supremum of a nonempty compact set of parameters, which is therefore attained. -/
theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  -- A parameter past the supremum that still lands in `C` would be a member above it.
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

/-- The mirror of `exists_last_mem_Icc`: the first parameter inside a closed set. Before it the
curve has not yet reached `C`. -/
theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

/-- B3 on the unit interval: the last parameter at which an arc is inside a closed set. -/
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

end Schoenflies

/-! ### B2 — the vertex squares -/

open Schoenflies
section
variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

open _root_.Graph in
/-- A vertex lies on no arc of an edge it is not incident with: the arc meets the vertex set
only at its own two ends, and those are the vertices it is incident with. -/
theorem _root_.Graph.IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

open _root_.Graph in
/-- B2 at a single vertex: a closed square about `v` meeting no other vertex and no arc of an
edge not incident with `v`.

The two families are separated the same way — one compact separation each, then the common
positive bound of `exists_pos_forall_of_finite` — and the two radii are then merged by taking
the smaller, which is legitimate because shrinking a square preserves "meets nothing". -/
theorem _root_.Graph.IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  -- The other vertices.
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · -- `w` is at positive Euclidean distance from `v`, and a square of half that radius
        -- sits inside the ball of that radius.
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  -- The non-incident edges.
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

open _root_.Graph in
/-- B2 as its consumers want it: **one** radius serving every vertex at once, with the squares
about distinct vertices disjoint.

Disjointness is not a consequence of the per-vertex statement — a square about `v` avoiding
`w` says nothing about a square about `w` reaching towards `v`. It comes from choosing the
radius once for all vertices and then halving it: two squares of radius `r` that met would put
their centres within `2r` in the sup metric, i.e. each centre in the other's square of radius
`2r`, which the unhalved choice forbids. -/
theorem _root_.Graph.IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  -- One radius for all vertices, by the same monotone-downward bound.
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · -- Both centres are within `r/2` of `x`, hence within `r` of each other.
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

/-! ### B4 — the cores -/

open _root_.Graph in
/-- An edge is incident only with its own two ends. -/
theorem _root_.Graph.not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

open _root_.Graph in
/-- **Distinct cores are disjoint.** A subset of one edge's arc containing no vertex meets no
other edge's arc at all, because distinct edges meet only at vertices. Stated for arbitrary
subsets rather than for cores, since that is all the argument uses — and it is why
`exists_core` carries `Disjoint K V(G)` rather than a clause about other edges. -/
theorem _root_.Graph.IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

open _root_.Graph in
/-- **The core of an edge.** Between the last parameter at which the edge's arc is inside the
square about `v` and the first parameter after that at which it is inside the square about `w`
sits a subarc `K` — the core — which meets the square at `v` in its first endpoint only, meets
the square at `w` in its last endpoint only, and contains no vertex at all.

The two squares must be disjoint, which is what the uniform choice of `exists_vertexSquares`
provides; disjointness in particular forces `v ≠ w`, so **this says nothing about a loop
edge** — see the module report.

The "first entry after the last exit" is not the same as "first entry": nothing forbids the
arc from dipping into the far square and coming back, so the second application of B3 is over
`[a, 1]` and not over `[0, 1]`.

That the endpoints of the core are *not* the vertices themselves is where the positivity of
the radius is used: the arc starts at the centre of the square about `v`, so it is still
inside the square just after leaving it, and the last exit therefore happens at a positive
parameter. That fact is what makes `Disjoint K V(G)` true and hence distinct cores disjoint. -/
theorem _root_.Graph.IsDrawing.exists_core (h : IsDrawing G drawing) {e : β} {v w : Plane} {r : ℝ}
    (hr : 0 < r) (hlink : G.IsLink e v w)
    (hdisj : Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r)) :
    ∃ (K : Set Plane) (p q : Plane),
      K ⊆ edgeArc drawing e ∧ IsCompact K ∧ IsArcBetween K p q ∧
      K ∩ Plane.closedSquare v r = {p} ∧ K ∩ Plane.closedSquare w r = {q} ∧
      Disjoint K V(G) := by
  obtain ⟨f, hcont, hinj, himg, hf0, hf1⟩ := h.edge_isArcBetween hlink
  have hv0 : f 0 ∈ Plane.closedSquare v r := by
    rw [hf0]; exact Plane.mem_closedSquare_self v hr.le
  have hw1 : f 1 ∈ Plane.closedSquare w r := by
    rw [hf1]; exact Plane.mem_closedSquare_self w hr.le
  -- The last exit from the square at `v` …
  obtain ⟨a, haI, -, haD, hafter⟩ :=
    exists_last_mem hcont (Plane.isClosed_closedSquare v r) zero_mem_I hv0
  have hsub : Icc a 1 ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, ht.2⟩
  -- … and the first entry into the square at `w` after it.
  obtain ⟨b, hbmem, -, hbD, hbefore⟩ :=
    exists_first_mem_Icc (hcont.mono hsub) (Plane.isClosed_closedSquare w r)
      (right_mem_Icc.2 haI.2) hw1
  have hbI : b ∈ I := hsub hbmem
  have hne : a ≠ b := by
    intro hEq
    rw [hEq] at haD
    exact Set.disjoint_left.1 hdisj haD hbD
  have hIccI : Icc a b ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, le_trans ht.2 hbmem.2⟩
  -- The core does not reach back to `v`: just after `0` the arc is still inside the square.
  have hpv : f a ≠ v := by
    intro hEq
    have ha0 : a = 0 := hinj haI zero_mem_I (by rw [hEq, hf0])
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 zero_mem_I) r hr
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have htI : min (δ / 2) 1 ∈ I := ⟨ht0.le, min_le_right _ _⟩
    have hdist : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine hafter _ htI (by rw [ha0]; exact ht0) (Plane.closedBall_subset_closedSquare v r ?_)
    rw [mem_closedBall, ← hf0]
    exact (hclose htI hdist).le
  -- Symmetrically, the core does not reach forward to `w`.
  have hqw : f b ≠ w := by
    intro hEq
    have hb1 : b = 1 := hinj hbI one_mem_I (by rw [hEq, hf1])
    have halt1 : a < 1 := by rw [← hb1]; exact lt_of_le_of_ne hbmem.1 hne
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 1 one_mem_I) r hr
    have hmax1 : max (1 - δ / 2) ((a + 1) / 2) < 1 := max_lt (by linarith) (by linarith)
    have hmaxa : a ≤ max (1 - δ / 2) ((a + 1) / 2) :=
      le_trans (by linarith) (le_max_right _ _)
    have htmem : max (1 - δ / 2) ((a + 1) / 2) ∈ Icc a 1 := ⟨hmaxa, hmax1.le⟩
    have hdist : dist (max (1 - δ / 2) ((a + 1) / 2)) 1 < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have := le_max_left (1 - δ / 2) ((a + 1) / 2)
      linarith
    refine hbefore _ htmem (by rw [hb1]; exact hmax1)
      (Plane.closedBall_subset_closedSquare w r ?_)
    rw [mem_closedBall, ← hf1]
    exact (hclose (hsub htmem) hdist).le
  -- The core itself.
  have harc : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    have hsubarc := isArcBetween_subarc_of_injOn_I hcont hinj haI hbI hne
    rwa [uIcc_of_le hbmem.1] at hsubarc
  have hKsub : f '' Icc a b ⊆ edgeArc drawing e := by
    rw [← himg]; exact image_mono hIccI
  have hKv : f '' Icc a b ∩ Plane.closedSquare v r = {f a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hafter t (hIccI ht) hlt)
    · rintro rfl
      exact ⟨⟨a, ⟨le_refl a, hbmem.1⟩, rfl⟩, haD⟩
  have hKw : f '' Icc a b ∩ Plane.closedSquare w r = {f b} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.2 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hbefore t ⟨ht.1, le_trans ht.2 hbmem.2⟩ hlt)
    · rintro rfl
      exact ⟨⟨b, ⟨hbmem.1, le_refl b⟩, rfl⟩, hbD⟩
  refine ⟨f '' Icc a b, f a, f b, hKsub, harc.isArc.isCompact, harc, hKv, hKw,
    Set.disjoint_left.2 fun x hxK hxV => ?_⟩
  -- A vertex on the core is an end of the edge, and each end is excluded by the two facts
  -- above together with the descriptions of `K ∩ D_v` and `K ∩ D_w`.
  rcases h.vertex_mem_edgeArc hlink hxV (hKsub hxK) with heq | heq
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare v r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self v hr.le⟩
    rw [hKv, mem_singleton_iff] at hmem
    exact hpv (hmem ▸ heq)
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare w r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self w hr.le⟩
    rw [hKw, mem_singleton_iff] at hmem
    exact hqw (hmem ▸ heq)

end

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/LocallyPolygonal.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The plane minus finitely many open squares is locally polygonally connected

This is brick B5 of the polygonal-redrawing argument. The redrawing cuts an open axis-parallel
square out of the plane around each vertex of the graph; what the rest of the argument needs of
the leftover set `M` is that it is *locally polygonally connected* — every point of `M` has a
relatively open neighbourhood all of whose points are joined to each other by polygonal paths
running inside `M`. That is what feeds the clopen argument one level up (brick B6), where the
basic open piece is no longer a ball.

The informal description of the three basic shapes — a disk away from every square, a half-disk
against one side, a three-quarter disk at a corner — suggests an angular case analysis. There is
none here. Both the squares and the basic neighbourhoods are axis-parallel, so each shape is an
intersection of a small square with the complement of an open square, and

* the complement of an open square is the union of the four closed coordinate half-planes that
  bound it (`Plane.compl_openSquare_subset_iUnion`);
* intersecting with a small square gives four *rectangles*, each convex;
* if the small square is small enough, each of those rectangles is either empty or contains the
  centre `p` (`Plane.exists_radius_sides`).

A union of convex sets with a common point is polygonally connected by two segments through that
point, which is `isLocallyPolyConnAt_of_star`. The three shapes are then just the three ways the
list of nonempty pieces can come out (one, two adjacent, or two adjacent again with `p` on the
corner) and none of them has to be named.

The passage from one square to finitely many is a shrinking step: since the closed squares are
pairwise disjoint, a point lies in at most one of them, and a small enough neighbourhood of any
point misses all the others outright, so `M` looks locally exactly like the one-square case.

## Blueprint

* `PolyConnIn` — "joined by a polygonal path inside `S`"; the relation Lemma 1.1 produces.
* `IsLocallyPolyConn` — the local form of polygonal connectedness, brick B5's conclusion.
* `polyConnIn_of_convex`, `polyConnIn_union_of_convex` — a rectangle, and two rectangles that
  meet, are polygonally connected.
* `Plane.sideHalfPlane`, `Plane.sideGap` — the four half-planes bounding a square and the room
  between a point and each of them.
* `isLocallyPolyConnAt_compl_openSquare` — the one-square case: the complement of any open
  square is locally polygonally connected, at every point of the plane.
* `isLocallyPolyConn_compl_biUnion` — brick B5: the plane minus finitely many open squares with
  pairwise disjoint closures is locally polygonally connected.
-/

open Metric _root_.Set

namespace Schoenflies

variable {S T : Set Plane} {x y z : Plane}

/-! ### Two list lemmas about `poly`

`PolyPath.lean` has `poly_concat`, which extends a vertex list by a single vertex. Transitivity
and symmetry of polygonal connectedness need the two-list versions; both are general facts about
`poly` and belong beside `poly_concat` rather than here. -/

/-! ### Polygonal connectedness inside a set -/

/-- `x` and `y` are joined by a polygonal path lying inside `S`.

This is the relation `exists_poly_of_isPreconnected` produces; naming it lets the local statement
below be phrased without repeating the vertex-list existential. -/
def PolyConnIn (S : Set Plane) (x y : Plane) : Prop :=
  ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ S ∧ vs.head h = x ∧ vs.getLast h = y

/-! ### The local statement -/

/-- `S` is polygonally connected near `p`: some open `U` containing `p` has all the points of
`U ∩ S` joined to each other by polygonal paths *inside `S`*.

`U ∩ S` is the relative neighbourhood; stating it through an ambient open set avoids carrying a
subtype topology. Note the paths are required to lie in `S`, not in the neighbourhood — that is
the form brick B6's clopen argument consumes. -/
def IsLocallyPolyConnAt (S : Set Plane) (p : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyConnIn S x y

/-- `S` is locally polygonally connected: polygonally connected near each of its points. -/
def IsLocallyPolyConn (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt S p

/-! ### The four sides of a square -/

namespace Plane

/-- A coordinate description of the open square: it is the set of points within `r` of the
centre in each coordinate separately. -/
theorem mem_openSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ openSquare c r ↔ ∀ i, |x i - c i| < r := by
  simp only [openSquare, mem_setOf_eq, supDist, supNorm, sub_apply, max_lt_iff,
    Fin.forall_fin_two]

/-- The centre of a square of positive radius is in it. -/
theorem mem_openSquare_self {p : Plane} {s : ℝ} (hs : 0 < s) : p ∈ openSquare p s := by
  simpa [openSquare] using hs

/-- Squares about a point grow with the radius. -/
theorem openSquare_mono {p : Plane} {s t : ℝ} (h : s ≤ t) : openSquare p s ⊆ openSquare p t :=
  fun _ hx => lt_of_lt_of_le hx h

/-- The closed half-plane on the far side of the `i`-th pair of sides of the square about `c` of
radius `r`; `b = true` picks the upper one. The four of them cover the complement of the square,
and each is convex, which is all the argument uses them for. -/
def sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) : Set Plane :=
  cond b {x | c i + r ≤ x i} {x | x i ≤ c i - r}

/-- How much room there is between `p` and the half-plane `sideHalfPlane c r i b`: positive
exactly when `p` is outside it, and an upper bound on a square radius that keeps a neighbourhood
of `p` clear of it. -/
noncomputable def sideGap (c : Plane) (r : ℝ) (p : Plane) (i : Fin 2) (b : Bool) : ℝ :=
  cond b ((c i + r) - p i) (p i - (c i - r))

theorem convex_sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    Convex ℝ (sideHalfPlane c r i b) := by
  cases b
  · exact convex_coord_le i _
  · exact convex_coord_ge i _

/-- Each of the four half-planes misses the open square. -/
theorem sideHalfPlane_subset_compl (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    sideHalfPlane c r i b ⊆ (openSquare c r)ᶜ := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff c r x).1 hmem i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hx) (by linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hx) (by linarith [hlt.2])

/-- The complement of an open square is covered by the four closed half-planes bounding it. -/
theorem compl_openSquare_subset_iUnion (c : Plane) (r : ℝ) :
    (openSquare c r)ᶜ ⊆ ⋃ ib : Fin 2 × Bool, sideHalfPlane c r ib.1 ib.2 := by
  intro x hx
  rw [mem_compl_iff, mem_openSquare_iff] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  rcases le_abs.1 hi with h | h
  · exact mem_iUnion.2 ⟨(i, true), show c i + r ≤ x i by linarith⟩
  · exact mem_iUnion.2 ⟨(i, false), show x i ≤ c i - r by linarith⟩

/-- If the radius is at most the room between `p` and a half-plane, the square about `p` of that
radius misses the half-plane. No sign condition on the gap: when it is nonpositive the radius is
too, and the square is empty. -/
theorem openSquare_disjoint_sideHalfPlane {c : Plane} {r s : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (hs : s ≤ sideGap c r p i b) :
    ∀ x ∈ openSquare p s, x ∉ sideHalfPlane c r i b := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff p s x).1 hx i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hmem) (by
      simp only [sideGap, cond_false] at hs; linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hmem) (by
      simp only [sideGap, cond_true] at hs; linarith [hlt.2])

/-- If there is no room between `p` and a half-plane, `p` is in it. -/
theorem mem_sideHalfPlane_of_sideGap_nonpos {c : Plane} {r : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (h : sideGap c r p i b ≤ 0) : p ∈ sideHalfPlane c r i b := by
  cases b
  · simp only [sideGap, cond_false] at h
    exact show p i ≤ c i - r by linarith
  · simp only [sideGap, cond_true] at h
    exact show c i + r ≤ p i by linarith

end Plane

/-! ### Choosing one radius for finitely many constraints -/

/-- A positive lower bound for whichever members of a finite family happen to be positive.
This is `exists_pos_le_of_finite` with the selection built in; the members that are nonpositive
impose nothing. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (d : ι → ℝ) :
    ∃ s > 0, ∀ i, 0 < d i → s ≤ d i := by
  obtain ⟨s, hs, hle⟩ :=
    exists_pos_le_of_finite (S := {i : ι | 0 < d i}) (Set.toFinite _) (f := d) fun _ hi => hi
  exact ⟨s, hs, fun i hi => hle i hi⟩

/-- A radius small enough that the square about `p` misses every side half-plane of the square
about `c` that `p` itself is outside of. -/
theorem Plane.exists_radius_sides (c : Plane) (r : ℝ) (p : Plane) :
    ∃ s > 0, ∀ ib : Fin 2 × Bool,
      ∀ z ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2,
        p ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2 := by
  obtain ⟨s, hs, hle⟩ := exists_pos_le_of_pos fun ib : Fin 2 × Bool => sideGap c r p ib.1 ib.2
  refine ⟨s, hs, fun ib z hz => ⟨?_, ?_⟩⟩
  · -- `p` is the centre of its own square, which is nonempty because `s > 0`.
    exact mem_openSquare_self hs
  · -- If there were room, the square about `p` would already miss this half-plane, and `z`
    -- could not be in it.
    by_contra hp
    exact openSquare_disjoint_sideHalfPlane
      (hle ib (lt_of_not_ge fun hcon => hp (mem_sideHalfPlane_of_sideGap_nonpos hcon))) z hz.1 hz.2

/-! ### The one-square case -/

/-! ### Finitely many squares -/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolygonalCarrier.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Polygonal connectedness over a carrier

`Schoenflies.exists_poly_of_isPreconnected` joins two points of an *open* connected subset
of the plane by a polygonal path. The redrawing argument needs the same conclusion for a
carrier that is **not** open in the plane: the ambient set there is the plane minus finitely
many open squares, and the basic neighbourhood of a point on a square's boundary is a
half-disk or a three-quarter disk rather than a ball.

This module restates the clopen argument over an arbitrary carrier `C`. The only hypothesis
on `C` is that it is *locally polygonally connected*: every point has a relatively open
neighbourhood all of whose points it reaches by a polygonal path inside `C`. Openness of `C`
is used nowhere; the ball of the classical proof appears only in
`isLocallyPolyConnected_of_isOpen`, which is what recovers the old statement.

## Blueprint

Brick B6 of `lem:polygonal-redrawing` (H6): polygonal connectivity one level up.

* `PolyReaches` — "joined by a polygonal path inside `C`", as an inductive relation.
  **Note for the integrator:** `Schoenflies/LocallyPolygonal.lean` is being written
  concurrently and defines a relation of the same meaning; the two want unifying.
* `IsLocallyPolyConnected` — the hypothesis replacing openness.
* `PolyReaches.of_isPreconnected` — Lemma 1.1 (polygonal connectedness) over a carrier.
* `exists_poly_of_isPreconnected'` — the old `exists_poly_of_isPreconnected` re-derived from
  it, verbatim; the `example` below it is a machine check that the statements agree.
-/

open Metric _root_.Set

namespace Schoenflies

variable {C D : Set Plane} {x y z : Plane}

/-! ### Joined by a polygonal path inside a carrier -/

/-- `PolyReaches C x y`: there is a polygonal path from `x` to `y` all of whose segments lie
in `C`. Built at the far end — a path is extended by one segment at a time — because that is
the shape both halves of the clopen argument use. `refl` carries `x ∈ C` so that a constant
path witnesses membership, matching `poly [x] = {x}`. -/
inductive PolyReaches (C : Set Plane) (x : Plane) : Plane → Prop
  | refl (hx : x ∈ C) : PolyReaches C x x
  | step {y z : Plane} (h : PolyReaches C x y) (hseg : segment ℝ y z ⊆ C) : PolyReaches C x z

namespace PolyReaches

/-- A single segment inside `C` is already a polygonal path. -/
theorem of_segment (hseg : segment ℝ x y ⊆ C) : PolyReaches C x y :=
  (PolyReaches.refl (hseg (left_mem_segment ℝ x y))).step hseg

theorem trans (h₁ : PolyReaches C x y) (h₂ : PolyReaches C y z) : PolyReaches C x z := by
  induction h₂ with
  | refl _ => exact h₁
  | step _ hseg ih => exact ih.step hseg

/-- Symmetry: a path is run backwards one segment at a time, each reversed segment being the
same set. -/
theorem symm (h : PolyReaches C x y) : PolyReaches C y x := by
  induction h with
  | refl hx => exact PolyReaches.refl hx
  | @step y z _ hseg ih =>
    -- The last segment, reversed, joins `z` back to `y`; then follow the shorter path back.
    exact (of_segment (by rwa [segment_symm])).trans ih

theorem mono (hCD : C ⊆ D) (h : PolyReaches C x y) : PolyReaches D x y := by
  induction h with
  | refl hx => exact PolyReaches.refl (hCD hx)
  | step _ hseg ih => exact ih.step (hseg.trans hCD)

end PolyReaches

/-! ### The relation and the vertex-list representation agree -/

/-- A polygonal path in the sense of `PolyReaches` yields a vertex list with the carrier of
its polygon inside `C`. This is `poly_concat` used once per `step`. -/
theorem PolyReaches.exists_poly (h : PolyReaches C x y) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y := by
  induction h with
  | refl hx => exact ⟨[x], by simp, by simpa using hx, rfl, rfl⟩
  | @step _ z _ hseg ih =>
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := ih
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub hseg
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp

/-- Conversely a vertex list whose polygon lies in `C` joins its ends. -/
theorem polyReaches_of_poly_subset : ∀ {vs : List Plane} (hne : vs ≠ []), poly vs ⊆ C →
    PolyReaches C (vs.head hne) (vs.getLast hne)
  | [], hne, _ => absurd rfl hne
  | [v], _, hsub => PolyReaches.refl (hsub (by simp))
  | u :: v :: rest, _, hsub => by
    rw [poly_cons_cons] at hsub
    have hstep : PolyReaches C u v :=
      PolyReaches.of_segment (subset_union_left.trans hsub)
    have hrest := polyReaches_of_poly_subset (List.cons_ne_nil v rest)
      (subset_union_right.trans hsub)
    rw [List.getLast_cons (List.cons_ne_nil v rest)]
    exact hstep.trans hrest

/-! ### Local polygonal connectedness -/

/-- `C` is locally polygonally connected when every point of `C` has a relatively open
neighbourhood in `C` each of whose points it reaches by a polygonal path inside `C`.

The neighbourhood is presented as `V ∩ C` for an ambient open `V`, which is exactly what a
relatively open neighbourhood is; the paths are only required to stay inside `C`, not inside
the neighbourhood, since that is all the clopen argument uses and it is the weaker demand on
a producer. Ball, half-disk and three-quarter disk all qualify. -/
def IsLocallyPolyConnected (C : Set Plane) : Prop :=
  ∀ w ∈ C, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ V ∩ C, PolyReaches C w z

/-- The relative-openness step, stated once because the clopen argument uses it twice — for
the reachable set and, run backwards, for its relative complement.

A subset of `C` closed under "reach one more point of `C` by a polygonal path" is relatively
open in `C`. The witness is the union of all ambient open sets that are polygonally attached
to a point of `S`; no choice is needed to assemble it. -/
theorem isRelOpen_of_polyReaches_stable (hloc : IsLocallyPolyConnected C) {S : Set Plane}
    (hS : S ⊆ C) (hstable : ∀ w ∈ S, ∀ z ∈ C, PolyReaches C w z → z ∈ S) :
    ∃ U : Set Plane, IsOpen U ∧ S ⊆ U ∧ U ∩ C ⊆ S := by
  refine ⟨⋃₀ {V : Set Plane | IsOpen V ∧ ∃ w ∈ S, ∀ z ∈ V ∩ C, PolyReaches C w z},
    isOpen_sUnion fun V hV => hV.1, fun w hw => ?_, ?_⟩
  · obtain ⟨V, hVopen, hwV, hVreach⟩ := hloc w (hS hw)
    exact ⟨V, ⟨hVopen, w, hw, hVreach⟩, hwV⟩
  · rintro z ⟨⟨V, ⟨_, w, hwS, hVreach⟩, hzV⟩, hzC⟩
    exact hstable w hwS z hzC (hVreach z ⟨hzV, hzC⟩)

/-! ### The theorem -/

/-- Lemma 1.1 (polygonal connectedness) over a carrier: in a relatively connected, locally
polygonally connected set, any two points are joined by a polygonal path inside the set.

The proof is the clopen argument. The points reachable from `x` are relatively open in `C`,
and so are the unreachable ones — the same lemma, since "unreachable" is stable under
reaching too, by symmetry. `IsPreconnected C` then forbids the split. -/
theorem PolyReaches.of_isPreconnected (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : PolyReaches C x y := by
  by_contra hxy
  set R : Set Plane := {w | w ∈ C ∧ PolyReaches C x w} with hRdef
  obtain ⟨U, hUopen, hRU, hUR⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := R) (fun _ hw => hw.1)
      (fun _ hw _ hzC hreach => ⟨hzC, hw.2.trans hreach⟩)
  obtain ⟨U', hU'open, hRU', hU'R⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := C \ R) (fun _ hw => hw.1)
      (fun w hw z hzC hreach => ⟨hzC, fun hzR => hw.2 ⟨hw.1, hzR.2.trans hreach.symm⟩⟩)
  obtain ⟨w, hwC, hwU, hwU'⟩ := hconn U U' hUopen hU'open
    (fun v hv => (em (v ∈ R)).imp (fun h => hRU h) (fun h => hRU' ⟨hv, h⟩))
    ⟨x, hx, hRU ⟨hx, PolyReaches.refl hx⟩⟩
    ⟨y, hy, hRU' ⟨hy, fun h => hxy h.2⟩⟩
  exact (hU'R ⟨hwU', hwC⟩).2 (hUR ⟨hwU, hwC⟩)

/-! ### Producers of the hypothesis -/

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/PolyLocal.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# Local polygonal connectedness, in the form brick B7 consumes

`Schoenflies/LocallyPolygonal.lean` (brick B5) and `Schoenflies/PolygonalCarrier.lean`
(brick B6) were written independently and each carries its own "joined by a polygonal path
inside a set" relation — `PolyConnIn` as an existential over vertex lists, `PolyReaches` as
an inductive relation — with its own local form. This module makes them one, and then fixes
the shape problem that stops B5 from feeding B7.

## The shape problem

Both local forms ask only that the connecting path lie in `S`:

```
IsLocallyPolyConnAt S p  :  ∃ U open ∋ p, ∀ x y ∈ U ∩ S, PolyConnIn S x y
IsLocallyPolyConnected C :  ∀ w ∈ C, ∃ V open ∋ w, ∀ z ∈ V ∩ C, PolyReaches C w z
```

That is enough for B6 — the clopen argument only needs *some* path — but it is a property
with **no local content whatsoever**: any polygonally connected `S` satisfies it with
`U = univ`. In particular it does not survive intersection with an open set, and that is
exactly what B7 needs: `U_e` is a component of a relatively open piece of `M`, and a
replacement arc has to stay inside the thin tube, not merely inside `M`.

The fix is `IsLocallyPolyConnAt'`: *arbitrarily small* neighbourhoods `U` of `p` such that
any two points of `U ∩ S` are joined **inside `U ∩ S`**. B5's proof already produces this —
its paths are two segments inside convex pieces of the small square about `p`, and the
square's radius may be shrunk freely — so nothing geometric is lost, only misstated.
`isLocallyPolyConn'_compl_openSquare` and `isLocallyPolyConn'_compl_biUnion` are B5 in the
strengthened form, and `IsLocallyPolyConn'.weaken` recovers the original statements.

## Blueprint

Brick B5 ↔ brick B6 of `lem:polygonal-redrawing` (H6), and the interface B7 uses.

* `polyConnIn_iff_polyReaches` — the two relations agree.
* `IsLocallyPolyConn.isLocallyPolyConnected`, `IsLocallyPolyConnected.isLocallyPolyConn` —
  the two weak local forms agree, so B5 as originally stated does feed B6.
* `IsLocallyPolyConnAt'`, `IsLocallyPolyConn'` — the strengthened local form.
* `isLocallyPolyConnAt'_of_convex_cover` — the strengthened star lemma: a square about `p`
  cut by convex pieces, each of which contains `p` as soon as it is nonempty.
* `isLocallyPolyConnAt'_compl_openSquare`, `isLocallyPolyConn'_compl_biUnion` — **brick B5**,
  strengthened.
* `IsLocallyPolyConn'.inter_isOpen` — shrinkability: a relatively open piece of a locally
  polygonally connected set is locally polygonally connected.
* `IsRelOpenIn`, `isRelOpenIn_connectedComponentIn` — components of relatively open subsets
  are relatively open, the fact B7 quotes for `U_e`.
* `polyReaches_of_isPreconnected_of_isRelOpenIn`, `polyReaches_connectedComponentIn` — the
  payoff: two points of a connected relatively open piece are joined *inside that piece*.
-/

open Metric _root_.Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

/-! ### The two relations agree

`PolyReaches.exists_poly` and `polyReaches_of_poly_subset` are both on `main`; this is the
one-line packaging that lets a producer of either relation serve a consumer of the other. -/

/-- The vertex-list relation of `LocallyPolygonal.lean` and the inductive relation of
`PolygonalCarrier.lean` are the same relation. -/
theorem polyConnIn_iff_polyReaches : PolyConnIn S x y ↔ PolyReaches S x y := by
  constructor
  · rintro ⟨vs, hne, hsub, hhead, hlast⟩
    have h := polyReaches_of_poly_subset hne hsub
    rwa [hhead, hlast] at h
  · intro h
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h.exists_poly
    exact ⟨vs, hne, hsub, hhead, hlast⟩

alias ⟨PolyConnIn.polyReaches, PolyReaches.polyConnIn⟩ := polyConnIn_iff_polyReaches

/-! ### The two weak local forms agree

`IsLocallyPolyConn` quantifies over *pairs* of points of the neighbourhood,
`IsLocallyPolyConnected` only over paths *from the centre*; symmetry and transitivity of the
relation make the two equivalent. -/

/-- Brick B5's conclusion, read as brick B6's hypothesis. -/
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

/-! ### Squares are a neighbourhood basis

B5 builds its neighbourhoods as axis-parallel squares, and the strengthened local form needs
them arbitrarily small inside a given open set. -/

namespace Plane

/-- A square of half a radius sits inside the ball of that radius, because `√2 < 2`. The open
counterpart of `Plane.closedSquare_subset_ball`, restated here so that this module does not
have to import the graph layer. No sign condition on the radius: for `ε ≤ 0` the square is
already empty. -/
theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

/-- Inside any open set around `p` there is a square about `p`, of radius at most any
prescribed positive bound. -/
theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

/-! ### The strengthened local form -/

/-- `S` is polygonally connected near `p` **inside arbitrarily small neighbourhoods**: for
every open `W` containing `p` there is an open `U ⊆ W` containing `p` such that any two points
of `U ∩ S` are joined by a polygonal path lying in `U ∩ S`.

Two strengthenings over `IsLocallyPolyConnAt`, and both are needed by brick B7. The path is
confined to the neighbourhood, not merely to `S`, because a replacement arc has to stay in its
tube; and the neighbourhoods run through a basis at `p`, because otherwise the property does
not survive intersecting `S` with an open set (`IsLocallyPolyConn'.inter_isOpen`). -/
def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

/-- `S` is locally polygonally connected in the strengthened sense. -/
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

/-- The strengthened form implies the original brick B5 statement, so nothing is lost by
replacing one with the other. -/
theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

/-- What brick B6 consumes. -/
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

/-- The property is local: only the trace of `S` on a neighbourhood of `p` matters. This is
what reduces "finitely many squares" to "one square". -/
theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

/-- A neighbourhood of `p` already inside `S` settles the point: shrink it to a square, which
is convex, so a single segment joins any two of its points. -/
theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

/-- **The strengthened star lemma**, and the whole geometric content of brick B5's three
shapes. Suppose that inside one square about `p` the trace of `S` is covered by convex sets
`H i`, that each `H i` meets that square only inside `S`, and that each `H i` which meets the
square contains `p`. Then `S` is locally polygonally connected at `p` in the strengthened
sense.

Two points of a small square about `p` are then joined by two segments through `p`, each
inside one convex piece of that *small* square — which is why the path never leaves the
neighbourhood. No piece is required to be nonempty and none is named, so the disk, the
half-disk and the three-quarter disk are all this statement. -/
theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  -- Every point of the small relative square is joined to the centre by one segment.
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

/-! ### Brick B5, strengthened

The two theorems of `LocallyPolygonal.lean`, reproved in the strengthened form. The geometry
is unchanged — `Plane.exists_radius_sides` still does all the work — because the pieces the
old proof used were already inside the neighbourhood; only the statement moves. -/

/-- **The one-square case of brick B5, strengthened.** The complement of an open axis-parallel
square is polygonally connected near every point of the plane, by paths confined to the
neighbourhood. -/
theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

/-- **Brick B5, strengthened.** The plane minus finitely many open axis-parallel squares whose
closed squares are pairwise disjoint is locally polygonally connected, with the connecting
paths confined to the neighbourhood.

The two cases are unchanged. Away from all the closed squares a small square about `p` lies
inside `M` outright. Otherwise `p` lies in exactly one closed square, and a small enough square
about `p` misses all the others, so near `p` the set `M` *is* the complement of that one open
square — which is what `IsLocallyPolyConnAt'.congr_nhds` says suffices. -/
theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc

-- A machine check that the strengthened form subsumes the original brick B5: this typechecks
-- only if the two statements line up on the nose.
/-! ### Shrinkability

The point of the strengthening. `IsLocallyPolyConn` does **not** have this property: it holds
for any polygonally connected `S` with `U = univ`, and the comb space — the segments
`{0} × [0,1]`, `{1/n} × [0,1]` and `[0,1] × {0}` — is polygonally connected while its
intersection with a thin open strip about `y = 1` is not locally polygonally connected at
`(0,1)`. -/

/-- **Shrinkability.** A relatively open piece of a locally polygonally connected set is
locally polygonally connected. Taking the neighbourhood inside `W` is what makes this work,
and it is the reason `IsLocallyPolyConnAt'` quantifies over all open `W ∋ p`. -/
theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

/-! ### Relatively open subsets and their components -/

/-- `A` is relatively open in `S`: cut out of `S` by an ambient open set. -/
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

/-- The shape `isRelOpen_of_polyReaches_stable` delivers, read as relative openness. -/
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

/-- Relative openness is transitive, which is how a component of a relatively open piece is
seen to be relatively open in the ambient set. -/
theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

/-- Shrinkability, phrased for a relatively open piece. -/
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

/-- **Components of relatively open subsets are relatively open.** For `S` locally polygonally
connected and `A` relatively open in `S`, each connected component of `A` is relatively open
in `S`.

The proof is `isRelOpen_of_polyReaches_stable`: a polygonal path inside `A` is a connected
subset of `A`, so it cannot leave the component it starts in, which is exactly the stability
that lemma asks for. -/
theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  -- The polygon carrying the path is connected, lies in `A` and starts at `w`.
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

/-! ### The payoff -/

/-- **What brick B7 uses.** In a locally polygonally connected `S`, any two points of a
connected relatively open subset are joined by a polygonal path *inside that subset*. -/
theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

/-- The component form, which is how `U_e` arises: a component of a relatively open piece is
both relatively open and polygonally connected in itself. -/
theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies

end

/-! ### Upstream module `MerLeanExperiment/Vendor/Schoenflies/Graph/Redrawing.lean` -/

section
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/

/-!
# The polygonal redrawing of a finite plane graph

Bricks B7 and B8 of `lem:polygonal-redrawing`, and the headline theorem: every finite plane
graph is drawn again, on the same abstract graph and the same vertices, with polygonal edges.
Since the vertices of a plane graph *are* plane points and the redrawing leaves them where
they are, the blueprint's "isomorphic plane drawing" is the identity isomorphism, and no
`Graph.IsIsomorphism` is built or needed.

## Three things the design did not have, and this module supplies

**Simple polygonal paths.** `Graph.IsDrawing.edge_param` asks for an *injective*
parametrisation, and brick B6 delivers only a `poly` vertex list, which may cross itself. The
blueprint's Lemma 1.1 makes the path simple "by subdividing at self-intersections and taking a
simple path in the resulting finite graph"; `Schoenflies/PolyPath.lean` deferred that half, and
without it brick B8 cannot discharge the drawing condition at all. `IsArcList` and
`PolyReaches.exists_arcList` supply it, by an induction over the inductive relation rather than
by an overlay graph: at each `step` the new segment is run *backwards* from its far end and
stopped the first time it meets the polygon already built, and the old path is truncated
there. That needs no plane geometry beyond `exists_first_mem_Icc`, and in particular no
connectivity theorem for the overlay graph.

**The contact point is on the frame.** `Graph.IsDrawing.exists_core` states that the core meets
the square about a vertex in exactly one point, but not that this point is on the square's
boundary — and if it were interior the core would not lie in the plane minus the open squares,
which is the carrier brick B5 speaks about, nor would the radial segment from the vertex reach
it. `Plane.supDist_eq_of_inter_eq_singleton` closes the gap by connectedness: an interior
contact point would make the core's trace on the square a nonempty proper clopen piece.

**Radial arithmetic.** That two radials of one square meet only at the centre, and that a
radial meets the plane minus the open squares only at its far end, are both the statement that
the sup distance to the centre is a faithful coordinate along a radius
(`Plane.supDist_lt_of_mem_segment`, `Plane.radial_meet`). These are the "distinct radials in
one square meet only at `v`" and "radials meet the replacement paths only at the designated
boundary points" of brick B8's design, and neither is free.

## Blueprint

Bricks B7 and B8 of `lem:polygonal-redrawing` (H6), and the lemma itself.

* `Plane.supNorm_smul`, `Plane.supDist_add_smul`, `Plane.supDist_lt_of_mem_segment`,
  `Plane.segment_subset_closedSquare`, `Plane.radial_meet` — the radial segments of brick B8.
* `Plane.supDist_eq_of_inter_eq_singleton` — a core's contact point lies on the frame of its
  square; the missing clause of brick B4.
* `lastP`, `poly_snoc`, `IsArcList` — a **simple** polygonal path, in the `u :: t`
  presentation that keeps every statement free of dependent nonemptiness proofs.
* `isArcBetween_poly` — the carrier of a simple polygonal path is an arc between its ends.
* `IsArcList.truncate`, `IsArcList.snoc` — cutting one at any of its points, and extending one
  by a segment that touches it only at its last vertex.
* `PolyReaches.exists_arcList` — **every polygonal path contains a simple one**; the deferred
  half of Lemma 1.1.
* `Graph.polygonal_redrawing` — `lem:polygonal-redrawing`, with bricks B7 and B8 inside its
  proof: the `ε` making the tubes about the cores pairwise disjoint, the component `U e` of
  the core inside its tube, and the assembly of radial, replacement path and radial.
-/

open Metric _root_.Set unitInterval
namespace Schoenflies

/-! ### Radial segments in a square

A segment from the centre of a square to a point of its boundary frame leaves the open square
only at its far end, and two such segments in one square meet only at the centre. Those two
facts are the whole of the "radials" half of brick B8, and both are statements about the sup
distance scaling along a segment. -/

namespace Plane

theorem supNorm_smul (a : ℝ) (x : Plane) : supNorm (a • x) = |a| * supNorm x := by
  have h0 : (a • x) 0 = a * x 0 := by simp
  have h1 : (a • x) 1 = a * x 1 := by simp
  simp only [supNorm, h0, h1, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm

theorem supDist_add_smul (c u : Plane) (t : ℝ) : supDist (c + t • u) c = |t| * supNorm u := by
  have h : c + t • u - c = t • u := by abel
  rw [supDist, h, supNorm_smul]

/-- Everything on the segment from `c` to `p` except `p` itself is strictly nearer to `c` than
`p` is, in the sup metric. This is why a radial segment meets the frame of its square only at
its far end. -/
theorem supDist_lt_of_mem_segment {c p x : Plane} (hpc : 0 < supDist p c)
    (hx : x ∈ segment ℝ c p) (hne : x ≠ p) : supDist x c < supDist p c := by
  rw [segment_eq_image' ℝ c p] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hxt' : c + t • (p - c) = x := hxt
  have hval : supDist x c = t * supDist p c := by
    rw [← hxt', supDist_add_smul, abs_of_nonneg ht.1]; rfl
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with heq | h
    · refine absurd ?_ hne
      rw [← hxt', heq]
      module
    · exact h
  rw [hval]
  nlinarith

/-- A radial segment stays inside its square. -/
theorem openSquare_subset_closedSquare (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r := fun x hx => show supDist x c ≤ r from le_of_lt hx

theorem segment_subset_closedSquare {c p : Plane} {r : ℝ} (hr : 0 ≤ r)
    (hpc : supDist p c ≤ r) : segment ℝ c p ⊆ closedSquare c r :=
  (convex_closedSquare c r).segment_subset (mem_closedSquare_self c hr) hpc

/-- **Two radials meet only at the centre.** Two segments from the centres of two squares of a
common radius `r` to points of their frames meet only where they can: if the centres are
distinct the squares are disjoint, and if they agree the two far ends are pinned by the sup
distance, which is injective along a radius. -/
theorem radial_meet {c c' p p' z : Plane} {r : ℝ} (hr : 0 < r) (hp : supDist p c = r)
    (hp' : supDist p' c' = r) (hpp' : p ≠ p')
    (hdisj : c ≠ c' → Disjoint (closedSquare c r) (closedSquare c' r))
    (hz : z ∈ segment ℝ c p) (hz' : z ∈ segment ℝ c' p') : z = c := by
  rcases eq_or_ne c c' with rfl | hcc'
  · -- One square: the two representations of `z` have the same parameter, which must be `0`.
    rw [segment_eq_image' ℝ c p] at hz
    rw [segment_eq_image' ℝ c p'] at hz'
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨s, hs, hzs⟩ := hz'
    have hzt' : c + t • (p - c) = z := hzt
    have hzs' : c + s • (p' - c) = z := hzs
    have h₁ : supDist z c = t * r := by
      rw [← hzt', supDist_add_smul, abs_of_nonneg ht.1, ← hp]; rfl
    have h₂ : supDist z c = s * r := by
      rw [← hzs', supDist_add_smul, abs_of_nonneg hs.1, ← hp']; rfl
    have hEq : t = s := mul_right_cancel₀ hr.ne' (h₁.symm.trans h₂)
    subst hEq
    have hsmul : t • (p - c) = t • (p' - c) := add_left_cancel (hzt'.trans hzs'.symm)
    have hkey : t • (p - p') = 0 := by linear_combination (norm := module) hsmul
    rcases smul_eq_zero.1 hkey with ht0 | hpp
    · rw [← hzt', ht0]; module
    · exact absurd (sub_eq_zero.1 hpp) hpp'
  · exact absurd (Set.disjoint_left.1 (hdisj hcc')
      (segment_subset_closedSquare hr.le hp.le hz)
      (segment_subset_closedSquare hr.le hp'.le hz')) not_false

end Plane

/-! ### Simple polygonal paths

`poly vs` is the carrier of a vertex list, and a general vertex list crosses itself. The
drawing condition of a plane graph asks for an *injective* parametrisation, so what brick B8
needs is a vertex list whose carrier is an **arc**. `IsArcList` is exactly the condition that
makes the concatenation of `Schoenflies/Concatenate.lean` apply at every step: consecutive
vertices differ, and each segment meets the rest of the polygon only at the vertex they
share.

The work of this section is `PolyReaches.exists_arcList`: *any* polygonal path inside a set
contains a simple one with the same ends. That is the half of the blueprint's Lemma 1.1 which
`Schoenflies/PolyPath.lean` deferred, and without it nothing downstream can discharge
`Graph.IsDrawing`. The induction is over the inductive relation `PolyReaches`, and the step
takes the *first* point at which the new segment, run backwards from its far end, meets the
polygon already built, truncates there and appends. -/

/-- The last vertex of a nonempty vertex list, with the nonemptiness discharged by the
`cons`. Carrying the list in the form `u :: t` removes every dependent proof argument from
the statements below. -/
def lastP (u : Plane) (t : List Plane) : Plane := (u :: t).getLast (List.cons_ne_nil u t)

@[simp] theorem lastP_cons (u v : Plane) (t : List Plane) : lastP u (v :: t) = lastP v t :=
  List.getLast_cons (List.cons_ne_nil v t)

theorem lastP_append : ∀ (u : Plane) (t : List Plane) (z : Plane), lastP u (t ++ [z]) = z
  | _, [], _ => rfl
  | u, v :: t, z => by
    rw [List.cons_append, lastP_cons, lastP_append v t z]

theorem lastP_mem_poly (u : Plane) (t : List Plane) : lastP u t ∈ poly (u :: t) :=
  getLast_mem_poly (List.cons_ne_nil u t)

/-- Appending one vertex, in the `u :: t` presentation. -/
theorem poly_snoc (u : Plane) (t : List Plane) (z : Plane) :
    poly (u :: (t ++ [z])) = poly (u :: t) ∪ segment ℝ (lastP u t) z := by
  rw [← List.cons_append, poly_concat (List.cons_ne_nil u t) z]
  rfl

/-- A **simple** polygonal path: consecutive vertices are distinct, and each segment meets the
rest of the polygon exactly in the vertex where they are joined. That is precisely the
hypothesis `Schoenflies.IsArcBetween.concatenate` asks for, one step at a time. -/
def IsArcList : List Plane → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest)

@[simp] theorem isArcList_singleton (v : Plane) : IsArcList [v] := trivial

/-- The carrier of a simple polygonal path is an arc between its ends. The induction glues one
segment at a time with `Schoenflies.IsArcBetween.concatenate`; the meeting hypothesis is the
second clause of `IsArcList`. -/
theorem isArcBetween_poly : ∀ (u v : Plane) (rest : List Plane), IsArcList (u :: v :: rest) →
    IsArcBetween (poly (u :: v :: rest)) u (lastP v rest)
  | u, v, [], h => by
    rw [poly_cons_cons, poly_singleton]
    have : segment ℝ u v ∪ {v} = segment ℝ u v :=
      union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))
    rw [this]
    exact isArcBetween_segment h.1
  | u, v, w :: rest, h => by
    rw [poly_cons_cons, lastP_cons]
    refine (isArcBetween_segment h.1).concatenate (isArcBetween_poly v w rest h.2.2) ?_
    intro z hz hz'
    have : z ∈ segment ℝ u v ∩ poly (v :: w :: rest) := ⟨hz, hz'⟩
    rw [h.2.1] at this
    exact this

/-- **Truncation.** A simple polygonal path may be cut at any point of its carrier: the piece
up to that point is again a simple polygonal path, inside the original one. -/
theorem IsArcList.truncate : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {w : Plane}, w ∈ poly (u :: t) →
      ∃ t' : List Plane, IsArcList (u :: t') ∧ poly (u :: t') ⊆ poly (u :: t) ∧
        lastP u t' = w
  | u, [], _, w, hw => by
    rw [poly_singleton, mem_singleton_iff] at hw
    exact ⟨[], isArcList_singleton u, subset_rfl, hw.symm⟩
  | u, v :: rest, h, w, hw => by
    by_cases hrest : w ∈ poly (v :: rest)
    · obtain ⟨rest', hlist, hsub, hlast⟩ := IsArcList.truncate v rest h.2.2 hrest
      refine ⟨v :: rest', ⟨h.1, ?_, hlist⟩, ?_, by rw [lastP_cons, hlast]⟩
      · refine Subset.antisymm ?_ ?_
        · exact fun z hz => h.2.1 ▸ ⟨hz.1, hsub hz.2⟩
        · rintro z rfl
          exact ⟨right_mem_segment ℝ u z, head_mem_poly (List.cons_ne_nil z rest')⟩
      · rw [poly_cons_cons, poly_cons_cons]
        exact union_subset_union_right _ hsub
    · rw [poly_cons_cons] at hw
      have hseg : w ∈ segment ℝ u v := hw.resolve_right hrest
      rcases eq_or_ne w u with heq | hwu
      · refine ⟨[], isArcList_singleton u, ?_, heq.symm⟩
        rw [poly_singleton, poly_cons_cons]
        exact singleton_subset_iff.2 (Or.inl (left_mem_segment ℝ u v))
      · refine ⟨[w], ⟨Ne.symm hwu, ?_, isArcList_singleton w⟩, ?_, rfl⟩
        · rw [poly_singleton]
          exact Subset.antisymm inter_subset_right
            (singleton_subset_iff.2 ⟨right_mem_segment ℝ u w, rfl⟩)
        · rw [poly_cons_cons, poly_singleton, poly_cons_cons]
          have : segment ℝ u w ∪ {w} = segment ℝ u w :=
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u w))
          rw [this]
          exact subset_union_of_subset_left
            ((convex_segment u v).segment_subset (left_mem_segment ℝ u v) hseg) _

/-- **Extension.** A simple polygonal path may be extended by a segment that meets it only at
its own last vertex. -/
theorem IsArcList.snoc : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {z : Plane}, z ≠ lastP u t →
      segment ℝ (lastP u t) z ∩ poly (u :: t) = {lastP u t} →
      IsArcList (u :: (t ++ [z]))
  | u, [], _, z, hz, _ => by
    refine ⟨Ne.symm hz, ?_, isArcList_singleton z⟩
    rw [poly_singleton]
    exact Subset.antisymm inter_subset_right
      (singleton_subset_iff.2 ⟨right_mem_segment ℝ u z, rfl⟩)
  | u, v :: rest, h, z, hz, hmeet => by
    rw [List.cons_append]
    refine ⟨h.1, ?_, ?_⟩
    · -- The first segment still meets the rest only at `v`: the new piece is barred from it
      -- because it meets the whole old polygon only at its last vertex, which lies on the
      -- rest and hence, if it were on the first segment, would have to be `v`.
      rw [lastP_cons] at hz hmeet
      rw [poly_snoc]
      refine Subset.antisymm ?_ ?_
      · rintro y ⟨hy1, hy2 | hy2⟩
        · exact h.2.1 ▸ ⟨hy1, hy2⟩
        · have hylast : y = lastP v rest := by
            have : y ∈ segment ℝ (lastP v rest) z ∩ poly (u :: v :: rest) :=
              ⟨hy2, Or.inl hy1⟩
            rw [hmeet] at this
            exact this
          have : lastP v rest ∈ segment ℝ u v ∩ poly (v :: rest) :=
            ⟨hylast ▸ hy1, lastP_mem_poly v rest⟩
          rw [h.2.1] at this
          rw [hylast]
          exact this
      · rintro y rfl
        exact ⟨right_mem_segment ℝ u y, Or.inl (head_mem_poly (List.cons_ne_nil y rest))⟩
    · rw [lastP_cons] at hz hmeet
      refine IsArcList.snoc v rest h.2.2 hz (Subset.antisymm ?_ ?_)
      · exact fun y hy => hmeet ▸ ⟨hy.1, Or.inr hy.2⟩
      · exact singleton_subset_iff.2
          ⟨left_mem_segment ℝ _ _, lastP_mem_poly v rest⟩

/-- **Every polygonal path contains a simple one.** This is the half of Lemma 1.1 that
`Schoenflies/PolyPath.lean` deferred, and the reason brick B8 can discharge the injectivity
clause of `Graph.IsDrawing`.

The induction is on `PolyReaches`. At a `step` the new segment is run *backwards* from its far
end and stopped the first time it touches the polygon already built — `exists_first_mem_Icc`
of `Schoenflies/Graph/VertexSquares.lean` is exactly that. The old path is truncated there and
the stub appended; the stub meets the truncation only at the join, because everything strictly
before the stopping parameter misses the old polygon altogether. -/
theorem PolyReaches.exists_arcList {S : Set Plane} {x y : Plane} (h : PolyReaches S x y) :
    ∃ t : List Plane, IsArcList (x :: t) ∧ poly (x :: t) ⊆ S ∧ lastP x t = y := by
  induction h with
  | refl hx => exact ⟨[], isArcList_singleton x, by simpa using hx, rfl⟩
  | @step w z _ hseg ih =>
    obtain ⟨t, hlist, hsub, hlast⟩ := ih
    -- The straight run from `z` back to `w`, stopped the first time it meets the old polygon.
    set γ : ℝ → Plane := fun a => z + a • (w - z) with hγ
    have hγc : ContinuousOn γ (Icc 0 1) := (by fun_prop : Continuous γ).continuousOn
    have hγ1 : γ 1 = w := by simp [hγ]
    have hclosed : IsClosed (poly (x :: t)) := (isCompact_poly _).isClosed
    have hmem1 : γ 1 ∈ poly (x :: t) := by
      rw [hγ1, ← hlast]; exact lastP_mem_poly x t
    obtain ⟨s, hs, -, hsmem, hbefore⟩ :=
      exists_first_mem_Icc hγc hclosed (right_mem_Icc.2 zero_le_one) hmem1
    -- Everything on the stub, bar its far end, is before the stopping parameter.
    have himg : segment ℝ (γ s) z ⊆ γ '' Icc 0 s := by
      rw [segment_symm, segment_eq_image' ℝ z (γ s)]
      rintro u ⟨θ, hθ, rfl⟩
      refine ⟨θ * s, ⟨mul_nonneg hθ.1 hs.1, mul_le_of_le_one_left hs.1 hθ.2⟩, ?_⟩
      simp only [hγ]
      module
    have hstub : ∀ u ∈ segment ℝ (γ s) z, u ∈ poly (x :: t) → u = γ s := by
      intro u hu humem
      obtain ⟨a, ha, rfl⟩ := himg hu
      rcases eq_or_lt_of_le ha.2 with heq | hlt
      · rw [heq]
      · exact absurd humem (hbefore a ⟨ha.1, le_trans ha.2 hs.2⟩ hlt)
    -- The stub lies on the new segment, since `γ s` does.
    have hγs_seg : γ s ∈ segment ℝ z w := by
      rw [segment_eq_image' ℝ z w]
      exact ⟨s, hs, rfl⟩
    have hsegzw : segment ℝ z w ⊆ S := by rw [segment_symm]; exact hseg
    have hstubsub : segment ℝ (γ s) z ⊆ S :=
      Subset.trans ((convex_segment z w).segment_subset hγs_seg (left_mem_segment ℝ z w)) hsegzw
    obtain ⟨t', hlist', hsub', hlast'⟩ := IsArcList.truncate x t hlist hsmem
    rcases eq_or_ne z (γ s) with heq | hzne
    · exact ⟨t', hlist', hsub'.trans hsub, by rw [hlast']; exact heq.symm⟩
    · refine ⟨t' ++ [z], ?_, ?_, lastP_append x t' z⟩
      · refine IsArcList.snoc x t' hlist' (by rw [hlast']; exact hzne) ?_
        rw [hlast']
        refine Subset.antisymm (fun u hu => hstub u hu.1 (hsub' hu.2)) ?_
        exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hlast' ▸ lastP_mem_poly x t'⟩
      · rw [poly_snoc, hlast']
        exact union_subset (hsub'.trans hsub) hstubsub

/-! ### The contact point of a core sits on the frame of its square

`Graph.IsDrawing.exists_core` says the core meets the square about `v` in exactly one point.
That point is on the *frame* of the square and not in its interior, which is what puts the
core in the plane minus the open squares and what makes the radial segment reach the core.
The argument is connectedness, not the parametrisation: were the contact point interior, it
would be a nonempty proper clopen piece of the core. -/

namespace Plane

/-- If a connected set meets a closed square in exactly one point and is not contained in that
square, the meeting point is on the frame: its sup distance to the centre is exactly the
radius. -/
theorem supDist_eq_of_inter_eq_singleton {K : Set Plane} {c p q : Plane} {r : ℝ}
    (hK : IsPreconnected K) (hp : K ∩ closedSquare c r = {p}) (hq : q ∈ K)
    (hqc : q ∉ closedSquare c r) : supDist p c = r := by
  have hpmem : p ∈ K ∩ closedSquare c r := by rw [hp]; rfl
  refine le_antisymm hpmem.2 (le_of_not_gt fun hlt => ?_)
  obtain ⟨w, hwK, hw1, hw2⟩ := hK (openSquare c r) (closedSquare c r)ᶜ
    (isOpen_openSquare c r) (isClosed_closedSquare c r).isOpen_compl
    (fun z hz => by
      by_cases hzc : z ∈ closedSquare c r
      · refine Or.inl ?_
        have hzp : z ∈ K ∩ closedSquare c r := ⟨hz, hzc⟩
        rw [hp, mem_singleton_iff] at hzp
        rw [hzp]
        exact hlt
      · exact Or.inr hzc)
    ⟨p, hpmem.1, hlt⟩ ⟨q, hq, hqc⟩
  exact hw2 (openSquare_subset_closedSquare c r hw1)

end Plane

end Schoenflies

/-! ### Bricks B7 and B8, and the redrawing itself -/

open Schoenflies

open _root_.Graph in
/-- **The polygonal redrawing of a finite plane graph** (`lem:polygonal-redrawing`). A finite
plane graph is drawn again, on the *same* abstract graph and the *same* vertices, with every
edge a polygonal arc. The blueprint speaks of an isomorphic plane drawing; since the vertices
of a plane graph are plane points and the redrawing leaves them where they are, the
isomorphism is the identity and no `Graph.IsIsomorphism` appears.

The construction, in the order the proof takes it.

* **The squares** (brick B2). One radius `r` serves every vertex: the square about a vertex
  meets no other vertex, meets no arc of an edge it is not incident with, and distinct squares
  are disjoint.
* **The cores** (brick B4). Each edge's arc, cut back to what lies between its last exit from
  the square at one end and its first entry into the square at the other. A core carries no
  vertex, so distinct cores are disjoint; and — `Plane.supDist_eq_of_inter_eq_singleton` — its
  two contact points sit on the *frames* of the two squares, so the core lies in the plane `M`
  minus the open squares.
* **The tubes** (brick B7). One `ε` makes the `ε`-tubes about the cores pairwise disjoint, by
  compact separation and the single-bound lemma. `U e` is the connected component, inside
  `M ∩ tube e`, of the core; it is relatively open in `M`, so the strengthened brick B5 joins
  the two contact points by a polygonal path *inside* `U e`.
* **The assembly** (brick B8). The path is straightened to a simple one
  (`Schoenflies.PolyReaches.exists_arcList`), then a radial segment is prepended at each end.
  A radial meets `M` only at its far end and two radials meet only at their common centre, so
  the three pieces glue to an arc; `Schoenflies.isArcBetween_poly` produces the
  parametrisation that `IsDrawing.edge_param` demands. -/
theorem _root_.Graph.polygonal_redrawing {β : Type*} (G : Graph Plane β) [G.Finite]
    (drawing : β → ℝ → Plane) (h : IsDrawing G drawing) :
    ∃ redrawing : β → ℝ → Plane, IsDrawing G redrawing ∧
      ∀ e ∈ E(G), IsPolygonal (edgeArc redrawing e) := by
  classical
  obtain ⟨r, hr, hvert, hnoninc, hsqdisj⟩ := h.exists_vertexSquares
  -- The core of every edge, with the edge's two ends and the core's two contact points.
  have hdata : ∀ e ∈ E(G), ∃ a b p q : Plane, ∃ Kc : Set Plane,
      G.IsLink e a b ∧ Kc ⊆ edgeArc drawing e ∧ IsCompact Kc ∧ IsArcBetween Kc p q ∧
        Kc ∩ Plane.closedSquare a r = {p} ∧ Kc ∩ Plane.closedSquare b r = {q} ∧
        Disjoint Kc V(G) := by
    intro e he
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨Kc, p, q, h1, h2, h3, h4, h5, h6⟩ :=
      h.exists_core hr hl (hsqdisj a hl.left_mem b hl.right_mem (h.ne_of_isLink hl))
    exact ⟨a, b, p, q, Kc, hl, h1, h2, h3, h4, h5, h6⟩
  choose! va vb pa pb core hlink hcoresub hcorecpt hcorearc hcoreA hcoreB hcoreV using hdata
  have hvaV : ∀ e ∈ E(G), va e ∈ V(G) := fun e he => (hlink e he).left_mem
  have hvbV : ∀ e ∈ E(G), vb e ∈ V(G) := fun e he => (hlink e he).right_mem
  have hvab : ∀ e ∈ E(G), va e ≠ vb e := fun e he => h.ne_of_isLink (hlink e he)
  have hpamem : ∀ e ∈ E(G), pa e ∈ core e ∩ Plane.closedSquare (va e) r := by
    intro e he; rw [hcoreA e he]; rfl
  have hpbmem : ∀ e ∈ E(G), pb e ∈ core e ∩ Plane.closedSquare (vb e) r := by
    intro e he; rw [hcoreB e he]; rfl
  have hcoreconn : ∀ e ∈ E(G), IsPreconnected (core e) :=
    fun e he => (hcorearc e he).isArc.isConnected.isPreconnected
  -- The contact points sit on the frames of their squares.
  have hpar : ∀ e ∈ E(G), Plane.supDist (pa e) (va e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreA e he)
      (hpbmem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
      hcon (hpbmem e he).2
  have hpbr : ∀ e ∈ E(G), Plane.supDist (pb e) (vb e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreB e he)
      (hpamem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (vb e) (hvbV e he) (va e) (hvaV e he)
      (Ne.symm (hvab e he))) hcon (hpamem e he).2
  -- The plane minus the open squares, and its local polygonal connectedness (brick B5).
  set M : Set Plane := (⋃ c ∈ V(G), Plane.openSquare c r)ᶜ with hMdef
  have hMloc : IsLocallyPolyConn' M :=
    isLocallyPolyConn'_compl_biUnion (Graph.finite_vertexSet (G := G)) (fun _ => r) hsqdisj
  have hMV : ∀ c ∈ V(G), c ∉ M := fun c hc hcM =>
    hcM (mem_biUnion hc (Plane.mem_openSquare_self hr))
  -- The cores avoid the open squares.
  have hcoreM : ∀ e ∈ E(G), core e ⊆ M := by
    intro e he z hz hcon
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 hcon
    have hzc' : z ∈ Plane.closedSquare c r := Plane.openSquare_subset_closedSquare c r hzc
    rcases eq_or_ne c (va e) with rfl | hca
    · have hzp : z ∈ core e ∩ Plane.closedSquare (va e) r := ⟨hz, hzc'⟩
      rw [hcoreA e he, mem_singleton_iff] at hzp
      rw [hzp] at hzc
      exact absurd (hpar e he) (ne_of_lt hzc)
    · rcases eq_or_ne c (vb e) with rfl | hcb
      · have hzp : z ∈ core e ∩ Plane.closedSquare (vb e) r := ⟨hz, hzc'⟩
        rw [hcoreB e he, mem_singleton_iff] at hzp
        rw [hzp] at hzc
        exact absurd (hpbr e he) (ne_of_lt hzc)
      · exact Set.disjoint_left.1
          (hnoninc c hc e he (not_inc_of_ne (hlink e he) hca hcb)) hzc' (hcoresub e he hz)
  -- Brick B7: one `ε` making the tubes about the cores pairwise disjoint.
  obtain ⟨ε, hε, hεall⟩ : ∃ ε > 0, ∀ e ∈ E(G), ∀ f ∈ E(G), f ≠ e →
      ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e ε => ∀ f ∈ E(G), f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun e δ ε _ hδε hP f hf hfe a ha b hb =>
        le_trans (by linarith) (hP f hf hfe a ha b hb)) ?_
    intro e he
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun f ε => f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun f δ ε _ hδε hP hfe a ha b hb => le_trans (by linarith) (hP hfe a ha b hb)) ?_
    intro f hf
    by_cases hfe : f = e
    · exact ⟨1, one_pos, fun hcon => absurd hfe hcon⟩
    · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos (hcorecpt e he) (hcorecpt f hf)
        (h.disjoint_of_subset_edgeArc he hf (Ne.symm hfe) (hcoresub e he) (hcoreV e he)
          (hcoresub f hf))
      exact ⟨ρ / 2, by linarith, fun _ a ha b hb => by have := hsep a ha b hb; linarith⟩
  set tube : β → Set Plane := fun e => ⋃ z ∈ core e, ball z ε with htubedef
  have htubeopen : ∀ e, IsOpen (tube e) := fun _ => isOpen_biUnion fun _ _ => isOpen_ball
  have htubedisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (tube e) (tube f) := by
    intro e he f hf hef
    refine Set.disjoint_left.2 fun z hze hzf => ?_
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hze
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hzf
    have h1 : dist a z < ε := by rw [dist_comm]; exact hza
    have h2 : dist z b < ε := hzb
    have h3 := hεall e he f hf (Ne.symm hef) a ha b hb
    have h4 := dist_triangle a z b
    linarith
  -- `U e` is the component of the core inside the tube, relatively open in `M`.
  set U : β → Set Plane := fun e => connectedComponentIn (M ∩ tube e) (pa e) with hUdef
  have hrel : ∀ e, IsRelOpenIn M (M ∩ tube e) := fun e => ⟨tube e, htubeopen e, rfl⟩
  have hcoreO : ∀ e ∈ E(G), core e ⊆ M ∩ tube e := fun e he z hz =>
    ⟨hcoreM e he hz, mem_iUnion₂.2 ⟨z, hz, mem_ball_self hε⟩⟩
  have hcoreU : ∀ e ∈ E(G), core e ⊆ U e := fun e he =>
    (hcoreconn e he).subset_connectedComponentIn (hpamem e he).1 (hcoreO e he)
  have hUM : ∀ e, U e ⊆ M := fun _ =>
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hUdisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (U e) (U f) := fun e he f hf hef =>
    Set.disjoint_of_subset ((connectedComponentIn_subset _ _).trans inter_subset_right)
      ((connectedComponentIn_subset _ _).trans inter_subset_right) (htubedisj e he f hf hef)
  have hpaU : ∀ e ∈ E(G), pa e ∈ U e := fun e he => hcoreU e he (hpamem e he).1
  have hpbU : ∀ e ∈ E(G), pb e ∈ U e := fun e he => hcoreU e he (hpbmem e he).1
  have hpath : ∀ e ∈ E(G), PolyReaches (U e) (pa e) (pb e) := fun e he =>
    polyReaches_connectedComponentIn hMloc (hrel e) (hpaU e he) (hpbU e he)
  -- A radial segment meets `M` only at its far end, and stays inside its square.
  have hsegM : ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r →
      ∀ z ∈ segment ℝ c p, z ∈ M → z = p := by
    intro c p hc hpc z hz hzM
    by_contra hne
    refine hzM (mem_biUnion hc ?_)
    have hlt := Plane.supDist_lt_of_mem_segment (by rw [hpc]; exact hr) hz hne
    rw [hpc] at hlt
    exact hlt
  have hsegSq : ∀ c p : Plane, Plane.supDist p c = r →
      segment ℝ c p ⊆ Plane.closedSquare c r :=
    fun c p hpc => Plane.segment_subset_closedSquare hr.le hpc.le
  -- The point set of a redrawn edge, before it is built.
  set Sset : β → Set Plane := fun e =>
    segment ℝ (va e) (pa e) ∪ U e ∪ segment ℝ (vb e) (pb e) with hSsetdef
  have hUcase : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ U e, z ∉ Sset f := by
    intro e he f hf hef z hz hzf
    have hzM : z ∈ M := hUM e hz
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hz
    rcases hzf with (hzf | hzf) | hzf
    · exact hdis ((hsegM (va f) (pa f) (hvaV f hf) (hpar f hf) z hzf hzM) ▸ hpaU f hf)
    · exact hdis hzf
    · exact hdis ((hsegM (vb f) (pb f) (hvbV f hf) (hpbr f hf) z hzf hzM) ▸ hpbU f hf)
  have hRadial : ∀ e ∈ E(G), ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r → p ∈ U e →
      ∀ f ∈ E(G), e ≠ f → ∀ z ∈ segment ℝ c p, z ∈ Sset f → z = c := by
    intro e he c p hc hpc hpU f hf hef z hz hzf
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hpU
    rcases hzf with (hzf | hzf) | hzf
    · exact Plane.radial_meet hr hpc (hpar f hf)
        (fun hEq => hdis (hEq ▸ hpaU f hf)) (fun hne => hsqdisj c hc _ (hvaV f hf) hne) hz hzf
    · exact absurd (hdis ((hsegM c p hc hpc z hz (hUM f hzf)) ▸ hzf)) not_false
    · exact Plane.radial_meet hr hpc (hpbr f hf)
        (fun hEq => hdis (hEq ▸ hpbU f hf)) (fun hne => hsqdisj c hc _ (hvbV f hf) hne) hz hzf
  have hSmeet : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ Sset e, z ∈ Sset f →
      z = va e ∨ z = vb e := by
    intro e he f hf hef z hze hzf
    rcases hze with (hze | hze) | hze
    · exact Or.inl (hRadial e he (va e) (pa e) (hvaV e he) (hpar e he) (hpaU e he)
        f hf hef z hze hzf)
    · exact absurd hzf (hUcase e he f hf hef z hze)
    · exact Or.inr (hRadial e he (vb e) (pb e) (hvbV e he) (hpbr e he) (hpbU e he)
        f hf hef z hze hzf)
  have hSvert : ∀ e ∈ E(G), ∀ v ∈ V(G), v ∈ Sset e → v = va e ∨ v = vb e := by
    intro e he v hv hvS
    rcases hvS with (hvS | hvS) | hvS
    · refine Or.inl (by_contra fun hne => ?_)
      exact hvert (va e) (hvaV e he) v hv hne (hsegSq (va e) (pa e) (hpar e he) hvS)
    · exact absurd (hUM e hvS) (hMV v hv)
    · refine Or.inr (by_contra fun hne => ?_)
      exact hvert (vb e) (hvbV e he) v hv hne (hsegSq (vb e) (pb e) (hpbr e he) hvS)
  -- Brick B8: the redrawn edge, as a parametrisation.
  have harc : ∀ e ∈ E(G), ∃ g : ℝ → Plane,
      ContinuousOn g I ∧ InjOn g I ∧ g 0 = va e ∧ g 1 = vb e ∧
        IsPolygonal (g '' I) ∧ g '' I ⊆ Sset e := by
    intro e he
    obtain ⟨t, hlist, hsub, hlast⟩ := (hpath e he).exists_arcList
    have hpaM : ∀ z ∈ poly (pa e :: t), z ∈ M := fun z hz => hUM e (hsub hz)
    have hAP : va e ≠ pa e := by
      intro hEq
      have hx := hpar e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hBQ : vb e ≠ pb e := by
      intro hEq
      have hx := hpbr e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hpbpoly : pb e ∈ poly (pa e :: t) := hlast ▸ lastP_mem_poly (pa e) t
    -- The far radial meets the straightened path only at the far contact point.
    have hmeetQ : segment ℝ (pb e) (vb e) ∩ poly (pa e :: t) = {pb e} := by
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rw [segment_symm] at hz
        exact hsegM (vb e) (pb e) (hvbV e he) (hpbr e he) z hz.1 (hpaM z hz.2)
      · exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hpbpoly⟩
    have hlist2 : IsArcList (pa e :: (t ++ [vb e])) :=
      IsArcList.snoc (pa e) t hlist (by rw [hlast]; exact hBQ)
        (by rw [hlast]; exact hmeetQ)
    have hpolysnoc : poly (pa e :: (t ++ [vb e]))
        = poly (pa e :: t) ∪ segment ℝ (pb e) (vb e) := by
      rw [poly_snoc, hlast]
    -- The near radial meets the rest only at the near contact point: the straightened path
    -- lives in `M`, and the far radial lives in the other square.
    have hmeetP : segment ℝ (va e) (pa e) ∩ poly (pa e :: (t ++ [vb e])) = {pa e} := by
      rw [hpolysnoc]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨hz1, hz2 | hz2⟩
        · exact hsegM (va e) (pa e) (hvaV e he) (hpar e he) z hz1 (hpaM z hz2)
        · rw [segment_symm] at hz2
          exact absurd (Set.disjoint_left.1
            (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
            (hsegSq (va e) (pa e) (hpar e he) hz1)
            (hsegSq (vb e) (pb e) (hpbr e he) hz2)) not_false
      · exact singleton_subset_iff.2 ⟨right_mem_segment ℝ _ _,
          Or.inl (head_mem_poly (List.cons_ne_nil _ _))⟩
    have hlist3 : IsArcList (va e :: pa e :: (t ++ [vb e])) := ⟨hAP, hmeetP, hlist2⟩
    have harcb := isArcBetween_poly (va e) (pa e) (t ++ [vb e]) hlist3
    rw [lastP_append] at harcb
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := harcb
    refine ⟨g, hgc, hgi, hg0, hg1, ⟨_, hgim⟩, ?_⟩
    rw [hgim, poly_cons_cons, hpolysnoc]
    refine union_subset (subset_union_of_subset_left subset_union_left _)
      (union_subset (hsub.trans (subset_union_of_subset_left subset_union_right _)) ?_)
    rw [segment_symm]
    exact subset_union_right
  choose! F hFc hFi hF0 hF1 hFpoly hFsub using harc
  refine ⟨F, ⟨fun e he => ⟨hFc e he, hFi e he, ?_⟩, ?_, ?_⟩, fun e he => hFpoly e he⟩
  · rw [hF0 e he, hF1 e he]; exact hlink e he
  · intro e a b v hl hv hvarc
    have he : e ∈ E(G) := hl.edge_mem
    rcases hSvert e he v hv (hFsub e he hvarc) with hEq | hEq <;>
      rcases hl.eq_and_eq_or_eq_and_eq (hlink e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hEq.trans h1.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inl (hEq.trans h1.symm)
  · intro e f he hf hef z hze hzf
    have h1 := hSmeet e he f hf hef z (hFsub e he hze) (hFsub f hf hzf)
    have h2 := hSmeet f hf e he (Ne.symm hef) z (hFsub f hf hzf) (hFsub e he hze)
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact hvaV e he
      · rw [hEq]; exact hvbV e he
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact (hlink e he).inc_left
      · rw [hEq]; exact (hlink e he).inc_right
    · rcases h2 with hEq | hEq
      · rw [hEq]; exact (hlink f hf).inc_left
      · rw [hEq]; exact (hlink f hf).inc_right

end

/-! ### Upstream module `MerLeanExperiment/TwoConnectedDensity.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
/-- Every boundary in a bipartite simple face system has at least four edges. -/
theorem _root_.Graph.FaceSystem.four_mul_faceCount_le_boundaryLength
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Simple]
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y)
    (M : FaceSystem G drawing) : 4 * M.faceCount ≤ M.boundaryLength := by
  have hlength : ∀ q ∈ M.boundaries, 4 ≤ q.2.length := by
    intro q hq
    obtain ⟨z, e, a, b, D, hz, hU, hcycle, hperm⟩ := M.valid q hq
    rw [hperm.length_eq]
    exact hcycle.isCycle.four_le_length_of_bicoloring c hcolor
  rw [FaceSystem.faceCount, FaceSystem.boundaryLength]
  calc
    4 * M.boundaries.card = ∑ q ∈ M.boundaries, 4 := by simp [Nat.mul_comm]
    _ ≤ ∑ q ∈ M.boundaries, q.2.length := by
      exact Finset.sum_le_sum fun q hq => hlength q hq

open _root_.Graph in
/-- A finite two-connected bipartite plane graph satisfies the sharp planar edge bound. -/
theorem _root_.Graph.IsDrawing.twoConnected_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (htwo : G.IsTwoConnected)
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨redrawing, hdraw, hpoly⟩ := polygonal_redrawing G drawing h
  obtain ⟨M, heuler, hboundary⟩ := hdraw.exists_euler_faceSystem hpoly htwo
  have hfour := M.four_mul_faceCount_le_boundaryLength c hcolor
  omega

end

/-! ### Upstream module `MerLeanExperiment/GraphSeparation.lean` -/

section
open _root_.Set

open _root_.Graph in
/-- A nonempty disconnected graph splits into two nonempty sets with no edge between them. -/
theorem _root_.Graph.exists_partition_of_not_connected
    {α β : Type*} (G : Graph α β) (hne : V(G).Nonempty) (hc : ¬ G.Connected) :
    ∃ A B : Set α, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = V(G) ∧
      ∀ (e : β) (x y : α), G.IsLink e x y →
        (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
  obtain ⟨a, ha⟩ := hne
  have hfail : ¬ ∀ x ∈ V(G), G.Reaches a x := by
    intro hall
    exact hc (Connected.of_hub ha hall)
  push Not at hfail
  obtain ⟨b, hb, hab⟩ := hfail
  let A : Set α := {x | G.Reaches a x}
  let B : Set α := V(G) \ A
  refine ⟨A, B, ⟨a, Reaches.refl ha⟩, ⟨b, hb, hab⟩, ?_, ?_, ?_⟩
  · exact disjoint_sdiff_right
  · ext x
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact Reaches.right_mem hx
      · exact hx
    · intro hx
      by_cases hax : G.Reaches a x
      · exact Or.inl hax
      · exact Or.inr ⟨hx, hax⟩
  · intro e x y hxy
    by_cases hx : G.Reaches a x
    · exact Or.inl ⟨hx, Reaches.trans hx (Reaches.of_isLink hxy)⟩
    · refine Or.inr ⟨⟨hxy.left_mem, hx⟩, hxy.right_mem, ?_⟩
      intro hy
      exact hx (Reaches.trans hy (Reaches.of_isLink hxy.symm))

end

/-! ### Upstream module `MerLeanExperiment/GraphSeparator.lean` -/

open _root_.Graph in
/-- Failure of two-connectivity gives two nonempty parts separated by at most one vertex. -/
theorem _root_.Graph.exists_small_separator
    {α β : Type*} (G : Graph α β) (hthree : G.HasThreeVertices)
    (htwo : ¬ G.IsTwoConnected) :
    ∃ A B S : Set α,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      (A ∪ B) ∪ S = V(G) ∧ (S = ∅ ∨ ∃ v : α, S = {v}) ∧
      ∀ (e : β) (x y : α), G.IsLink e x y →
        (x ∈ A ∪ S ∧ y ∈ A ∪ S) ∨ (x ∈ B ∪ S ∧ y ∈ B ∪ S) := by
  by_cases hc : G.Connected
  · have hfail : ¬ ∀ ⦃v⦄, v ∈ V(G) → (G.deleteVerts {v}).Connected := by
      intro hdel
      exact htwo ⟨hthree, hc, hdel⟩
    push Not at hfail
    obtain ⟨v, hv, hvdisc⟩ := hfail
    obtain ⟨w, hw, hwv, -⟩ := hthree.exists_ne_ne v v
    have hwdel : w ∈ V(G.deleteVerts {v}) := by
      rw [vertexSet_deleteVerts]
      exact ⟨hw, by simpa using hwv⟩
    obtain ⟨A, B, hA, hB, hAB, hunion, hlink⟩ :=
      exists_partition_of_not_connected (G.deleteVerts {v}) ⟨w, hwdel⟩ hvdisc
    have hAdel : A ⊆ V(G.deleteVerts {v}) := fun x hx ↦ by
      rw [← hunion]
      exact Or.inl hx
    have hBdel : B ⊆ V(G.deleteVerts {v}) := fun x hx ↦ by
      rw [← hunion]
      exact Or.inr hx
    have hAv : Disjoint A ({v} : Set α) := Set.disjoint_left.2 fun x hxA hxv ↦ by
      have hxdel := hAdel hxA
      rw [vertexSet_deleteVerts] at hxdel
      exact hxdel.2 hxv
    have hBv : Disjoint B ({v} : Set α) := Set.disjoint_left.2 fun x hxB hxv ↦ by
      have hxdel := hBdel hxB
      rw [vertexSet_deleteVerts] at hxdel
      exact hxdel.2 hxv
    refine ⟨A, B, {v}, hA, hB, hAB, hAv, hBv, ?_, Or.inr ⟨v, rfl⟩, ?_⟩
    · rw [hunion, vertexSet_deleteVerts]
      ext x
      simp [hv]
    · intro e x y hxy
      by_cases hxv : x = v
      · by_cases hyv : y = v
        · exact Or.inl ⟨Or.inr (by simp [hxv]), Or.inr (by simp [hyv])⟩
        · have hyAB : y ∈ A ∨ y ∈ B := by
            have hyDel : y ∈ V(G.deleteVerts {v}) := by
              rw [vertexSet_deleteVerts]
              exact ⟨hxy.right_mem, by simpa using hyv⟩
            rw [← hunion] at hyDel
            exact hyDel
          rcases hyAB with hyA | hyB
          · exact Or.inl ⟨Or.inr (by simp [hxv]), Or.inl hyA⟩
          · exact Or.inr ⟨Or.inr (by simp [hxv]), Or.inl hyB⟩
      · by_cases hyv : y = v
        · have hxAB : x ∈ A ∨ x ∈ B := by
            have hxDel : x ∈ V(G.deleteVerts {v}) := by
              rw [vertexSet_deleteVerts]
              exact ⟨hxy.left_mem, by simpa using hxv⟩
            rw [← hunion] at hxDel
            exact hxDel
          rcases hxAB with hxA | hxB
          · exact Or.inl ⟨Or.inl hxA, Or.inr (by simp [hyv])⟩
          · exact Or.inr ⟨Or.inl hxB, Or.inr (by simp [hyv])⟩
        · have hxy' : (G.deleteVerts {v}).IsLink e x y :=
            (deleteVerts_isLink G {v}).2 ⟨hxy, by simpa using hxv, by simpa using hyv⟩
          rcases hlink e x y hxy' with hAA | hBB
          · exact Or.inl ⟨Or.inl hAA.1, Or.inl hAA.2⟩
          · exact Or.inr ⟨Or.inl hBB.1, Or.inl hBB.2⟩
  · obtain ⟨A, B, hA, hB, hAB, hunion, hlink⟩ :=
      exists_partition_of_not_connected G (by
        obtain ⟨p, hp, -⟩ := hthree
        exact ⟨p, hp⟩) hc
    refine ⟨A, B, ∅, hA, hB, hAB, by simp, by simp,
      by simpa using hunion, Or.inl rfl, ?_⟩
    intro e x y hxy
    rcases hlink e x y hxy with hAA | hBB
    · exact Or.inl ⟨Or.inl hAA.1, Or.inl hAA.2⟩
    · exact Or.inr ⟨Or.inl hBB.1, Or.inl hBB.2⟩

/-! ### Upstream module `MerLeanExperiment/SmallGraphDensity.lean` -/

open _root_.Graph in
/-- A nonempty simple graph with fewer than three vertices satisfies the density bound. -/
theorem _root_.Graph.small_graph_density
    {α β : Type*} {G : Graph α β} [G.Finite] [G.Simple]
    (hne : V(G).Nonempty) (hsmall : ¬ G.HasThreeVertices) :
    E(G).ncard + 2 ≤ 2 * V(G).ncard := by
  by_cases hE : E(G) = ∅
  · rw [hE]
    simp only [Set.ncard_empty, zero_add]
    have hn : 0 < V(G).ncard :=
      (Set.ncard_pos (Graph.finite_vertexSet G)).mpr hne
    omega
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hE
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have hverts : ∀ z ∈ V(G), z = x ∨ z = y := by
    intro z hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr hzy
    exfalso
    apply hsmall
    exact ⟨x, hxy.left_mem, y, hxy.right_mem, z, hz, hxy.ne,
      fun hxz ↦ hzx hxz.symm, fun hyz ↦ hzy hyz.symm⟩
  have hedge : E(G) = {e} := by
    ext f
    constructor
    · intro hf
      obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet hf
      rcases hverts u huv.left_mem with rfl | rfl <;>
        rcases hverts v huv.right_mem with rfl | rfl
      · exact False.elim (huv.ne rfl)
      · exact Set.mem_singleton_iff.mpr (huv.eq hxy)
      · exact Set.mem_singleton_iff.mpr (huv.symm.eq hxy)
      · exact False.elim (huv.ne rfl)
    · simpa only [Set.mem_singleton_iff] using fun hfe ↦ hfe ▸ he
  have htwo : 2 ≤ V(G).ncard := by
    rw [← Set.ncard_pair hxy.ne]
    apply Set.ncard_le_ncard (ht := Graph.finite_vertexSet G)
    intro z hz
    rcases hz with rfl | rfl
    · exact hxy.left_mem
    · exact hxy.right_mem
  rw [hedge, Set.ncard_singleton]
  omega

/-! ### Upstream module `MerLeanExperiment/SeparatorCounts.lean` -/

section
open _root_.Set

open _root_.Graph in
/-- The two induced halves of a separator partition the edges and have smaller vertex sets. -/
theorem _root_.Graph.small_separator_counts
    {α β : Type*} {G : Graph α β} [G.Finite] [G.Simple]
    {A B S : Set α} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hcover : (A ∪ B) ∪ S = V(G)) (hS : S = ∅ ∨ ∃ v : α, S = {v})
    (hlink : ∀ (e : β) (x y : α), G.IsLink e x y →
      (x ∈ A ∪ S ∧ y ∈ A ∪ S) ∨ (x ∈ B ∪ S ∧ y ∈ B ∪ S)) :
    G.induce (A ∪ S) ≤ G ∧ G.induce (B ∪ S) ≤ G ∧
    (A ∪ S).Nonempty ∧ (B ∪ S).Nonempty ∧
    (A ∪ S).ncard < V(G).ncard ∧ (B ∪ S).ncard < V(G).ncard ∧
    (A ∪ S).ncard + (B ∪ S).ncard ≤ V(G).ncard + 1 ∧
    E(G.induce (A ∪ S)).ncard + E(G.induce (B ∪ S)).ncard = E(G).ncard := by
  let X := A ∪ S
  let Y := B ∪ S
  have hXsub : X ⊆ V(G) := by
    intro x hx
    rw [← hcover]
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hYsub : Y ⊆ V(G) := by
    intro x hx
    rw [← hcover]
    rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hGX : G.induce X ≤ G := G.induce_le hXsub
  have hGY : G.induce Y ≤ G := G.induce_le hYsub
  have hXne : X.Nonempty := hA.mono Set.subset_union_left
  have hYne : Y.Nonempty := hB.mono Set.subset_union_left
  have hXlt : X.ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard (ht := Graph.finite_vertexSet G)
    refine ⟨hXsub, ?_⟩
    obtain ⟨b, hb⟩ := hB
    intro hsub
    rcases hsub (hYsub (Or.inl hb)) with hbA | hbS
    · exact Set.disjoint_left.1 hAB hbA hb
    · exact Set.disjoint_left.1 hBS hb hbS
  have hYlt : Y.ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard (ht := Graph.finite_vertexSet G)
    refine ⟨hYsub, ?_⟩
    obtain ⟨a, ha⟩ := hA
    intro hsub
    rcases hsub (hXsub (Or.inl ha)) with haB | haS
    · exact Set.disjoint_left.1 hAB ha haB
    · exact Set.disjoint_left.1 hAS ha haS
  have hXYunion : X ∪ Y = V(G) := by
    rw [← hcover]
    ext x
    constructor
    · rintro ((hxA | hxS) | hxB | hxS)
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxS
      · exact Or.inl (Or.inr hxB)
      · exact Or.inr hxS
    · rintro ((hxA | hxB) | hxS)
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl hxB)
      · exact Or.inl (Or.inr hxS)
  have hXYinter : X ∩ Y = S := by
    ext x
    constructor
    · rintro ⟨hxA | hxS, hxB | hxS'⟩
      · exact False.elim (Set.disjoint_left.1 hAB hxA hxB)
      · exact hxS'
      · exact hxS
      · exact hxS
    · exact fun hx ↦ ⟨Or.inr hx, Or.inr hx⟩
  have hScard : S.ncard ≤ 1 := by
    rcases hS with rfl | ⟨v, rfl⟩ <;> simp
  have hvertices : X.ncard + Y.ncard ≤ V(G).ncard + 1 := by
    have hcard := Set.ncard_union_add_ncard_inter X Y
      ((Graph.finite_vertexSet G).subset hXsub)
      ((Graph.finite_vertexSet G).subset hYsub)
    rw [hXYunion, hXYinter] at hcard
    omega
  have hedgeUnion : E(G.induce X) ∪ E(G.induce Y) = E(G) := by
    ext e
    constructor
    · rintro (he | he)
      · obtain ⟨x, y, hxy, -⟩ := (G.edgeSet_induce X ▸ he)
        exact hxy.edge_mem
      · obtain ⟨x, y, hxy, -⟩ := (G.edgeSet_induce Y ▸ he)
        exact hxy.edge_mem
    · intro he
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      rcases hlink e x y hxy with hX | hY
      · exact Or.inl (G.edgeSet_induce X ▸ ⟨x, y, hxy, hX⟩)
      · exact Or.inr (G.edgeSet_induce Y ▸ ⟨x, y, hxy, hY⟩)
  have hedgeDisjoint : Disjoint E(G.induce X) E(G.induce Y) := by
    rw [Set.disjoint_left]
    intro e heX heY
    obtain ⟨x, y, hxy, hxX, hyX⟩ := G.edgeSet_induce X ▸ heX
    obtain ⟨u, v, huv, huY, hvY⟩ := G.edgeSet_induce Y ▸ heY
    have hxY : x ∈ Y := (hxy.left_eq_or_eq huv).elim (· ▸ huY) (· ▸ hvY)
    have hyY : y ∈ Y := (hxy.right_eq_or_eq huv).elim (· ▸ huY) (· ▸ hvY)
    have hxS : x ∈ S := hXYinter ▸ ⟨hxX, hxY⟩
    have hyS : y ∈ S := hXYinter ▸ ⟨hyX, hyY⟩
    rcases hS with rfl | ⟨s, rfl⟩
    · exact hxS.elim
    · exact hxy.ne (Set.mem_singleton_iff.1 hxS |>.trans
        (Set.mem_singleton_iff.1 hyS).symm)
  let _ : (G.induce X).Finite := Graph.Finite.of_le hGX
  let _ : (G.induce Y).Finite := Graph.Finite.of_le hGY
  have hedges := Set.ncard_union_eq hedgeDisjoint
    (Graph.finite_edgeSet (G.induce X)) (Graph.finite_edgeSet (G.induce Y))
  rw [hedgeUnion] at hedges
  exact ⟨hGX, hGY, hXne, hYne, hXlt, hYlt, hvertices, hedges.symm⟩

end

/-! ### Upstream module `MerLeanExperiment/PlanarDensity.lean` -/

section
open _root_.Set Schoenflies

open _root_.Graph in
theorem _root_.Graph.IsDrawing.nonempty_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (hne : V(G).Nonempty)
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard + 2 ≤ 2 * V(G).ncard := by
  induction hn : V(G).ncard using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hthree : G.HasThreeVertices
      · by_cases htwo : G.IsTwoConnected
        · have hdense := h.twoConnected_density htwo c hcolor
          omega
        · obtain ⟨A, B, S, hA, hB, hAB, hAS, hBS, hcover, hS, hlink⟩ :=
            exists_small_separator G hthree htwo
          obtain ⟨hGA, hGB, hAne, hBne, hAlt, hBlt, hvertices, hedges⟩ :=
            small_separator_counts hA hB hAB hAS hBS hcover hS hlink
          let GA := G.induce (A ∪ S)
          let GB := G.induce (B ∪ S)
          let _ : GA.Finite := Graph.Finite.of_le hGA
          let _ : GB.Finite := Graph.Finite.of_le hGB
          let _ : GA.Simple := Graph.Simple.anti hGA
          let _ : GB.Simple := Graph.Simple.anti hGB
          have hcolorA : ∀ (e : β) (x y : Plane), GA.IsLink e x y → c x ≠ c y :=
            fun e x y hxy ↦ hcolor e x y (hxy.mono hGA)
          have hcolorB : ∀ (e : β) (x y : Plane), GB.IsLink e x y → c x ≠ c y :=
            fun e x y hxy ↦ hcolor e x y (hxy.mono hGB)
          have hAlt' : (A ∪ S).ncard < n := by simpa [← hn] using hAlt
          have hBlt' : (B ∪ S).ncard < n := by simpa [← hn] using hBlt
          have hdenseA : E(GA).ncard + 2 ≤ 2 * (A ∪ S).ncard := by
            simpa [GA] using ih (A ∪ S).ncard hAlt' (h.mono hGA) hAne hcolorA
          have hdenseB : E(GB).ncard + 2 ≤ 2 * (B ∪ S).ncard := by
            simpa [GB] using ih (B ∪ S).ncard hBlt' (h.mono hGB) hBne hcolorB
          change E(GA).ncard + E(GB).ncard = E(G).ncard at hedges
          omega
      · simpa [← hn] using small_graph_density hne hthree

open _root_.Graph in
theorem _root_.Graph.IsDrawing.bipartite_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard ≤ 2 * V(G).ncard := by
  by_cases hne : V(G).Nonempty
  · have hdense := h.nonempty_density hne c hcolor
    omega
  · have hE : E(G) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨e, he⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact hne ⟨x, hxy.left_mem⟩
    rw [hE]
    simp

end

/-! ### Upstream module `MerLeanExperiment/PlaneDrawing.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Original formal authors: Codex, GPT-5.6 Sol.
This file retains only the ordinary drawing definition, without face certificates.
-/

open scoped unitInterval

variable {V : Type u}

/-- A crossing-free topological drawing of a finite simple graph in the
Euclidean plane.  Edge interiors are simple, avoid all vertex images, and are
pairwise disjoint. -/
structure PlaneDrawing (G : SimpleGraph V) where
  vertexPoint : V → (Fin 2 → ℝ)
  vertexPoint_injective : Function.Injective vertexPoint
  edgePoint : G.edgeSet → I → (Fin 2 → ℝ)
  edge_continuous (e : G.edgeSet) : Continuous (edgePoint e)
  edge_zero (e : G.edgeSet) : edgePoint e 0 = vertexPoint e.1.out.1
  edge_one (e : G.edgeSet) : edgePoint e 1 = vertexPoint e.1.out.2
  edge_interior_injective (e : G.edgeSet) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s = edgePoint e t → s = t
  edge_interior_avoids_vertex (e : G.edgeSet) (v : V) {t : I} :
    t ≠ 0 → t ≠ 1 → edgePoint e t ≠ vertexPoint v
  edge_interiors_disjoint {e f : G.edgeSet} (hef : e ≠ f) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s ≠ edgePoint f t

end

/-! ### Upstream module `MerLeanExperiment/GraphRepresentation.lean` -/

section
open scoped _root_.Graph
open Schoenflies

variable {V : Type u} {G : SimpleGraph V}

/-- The same vertex point in the Euclidean normed plane. -/
noncomputable def PlaneDrawing.point (D : PlaneDrawing G) (v : V) : Plane :=
  WithLp.toLp 2 (D.vertexPoint v)

/-- Relabel the ordinary simple graph's vertices by their plane points. -/
noncomputable def PlaneDrawing.planeGraph (D : PlaneDrawing G) : Graph Plane (Sym2 V) :=
  (Graph.ofSimpleGraph G).map D.point

/-- The plane relabeling does not identify vertices. -/
theorem PlaneDrawing.point_injective (D : PlaneDrawing G) :
    Function.Injective D.point := by
  exact (WithLp.toLp_injective 2).comp D.vertexPoint_injective

/-- Relabeling keeps precisely the original edge set. -/
theorem PlaneDrawing.planeGraph_edgeSet (D : PlaneDrawing G) :
    E(D.planeGraph) = G.edgeSet := rfl

/-- All and only original vertex images are vertices of the plane graph. -/
theorem PlaneDrawing.planeGraph_vertexSet (D : PlaneDrawing G) :
    V(D.planeGraph) = Set.range D.point := by
  ext x
  simp [PlaneDrawing.planeGraph]

/-- An original simple graph remains simple after injective relabeling. -/
theorem PlaneDrawing.planeGraph_simple (D : PlaneDrawing G) : D.planeGraph.Simple := by
  refine { not_isLoopAt := ?_, eq_of_isLink := ?_ }
  · rintro e x ⟨u, v, huv, hu, hv⟩
    exact ((Graph.ofSimpleGraph_adj_iff u v).mp huv.adj).ne
      (D.point_injective (hu.trans hv.symm))
  · rintro e f x y ⟨u, v, huv, hux, hvy⟩ ⟨u', v', huv', hu'x, hv'y⟩
    have huu' : u = u' := D.point_injective (hux.trans hu'x.symm)
    have hvv' : v = v' := D.point_injective (hvy.trans hv'y.symm)
    subst u'
    subst v'
    exact huv.1.trans huv'.1.symm

/-- Both vertex and edge sets of the relabeled graph are finite. -/
theorem PlaneDrawing.planeGraph_finite [Finite V] (D : PlaneDrawing G) :
    D.planeGraph.Finite := by
  constructor
  · rw [D.planeGraph_vertexSet]
    exact Set.finite_range D.point
  · rw [D.planeGraph_edgeSet]
    exact Set.toFinite G.edgeSet

end

/-! ### Upstream module `MerLeanExperiment/PlaneBicoloring.lean` -/

section
open Schoenflies

/-- An original bipartition extends to the relabeled plane graph. -/
theorem PlaneDrawing.exists_bicoloring
    {V : Type*} {G : SimpleGraph V} (D : PlaneDrawing G) (hbipartite : G.IsBipartite) :
    ∃ c : Plane → Fin 2,
      ∀ (e : Sym2 V) (x y : Plane), D.planeGraph.IsLink e x y → c x ≠ c y := by
  obtain ⟨C⟩ := hbipartite
  let c : Plane → Fin 2 := Function.extend D.point C fun _ => 0
  refine ⟨c, ?_⟩
  rintro e x y ⟨u, v, hlink, rfl, rfl⟩
  have hadj : G.Adj u v := (Graph.ofSimpleGraph_adj_iff u v).mp hlink.adj
  have hcu : c (D.point u) = C u := D.point_injective.extend_apply C (fun _ => 0) u
  have hcv : c (D.point v) = C v := D.point_injective.extend_apply C (fun _ => 0) v
  rw [hcu, hcv]
  exact C.valid hadj

end

/-! ### Upstream module `MerLeanExperiment/EdgeSupportedGraph.lean` -/

section
open scoped _root_.Graph
open Schoenflies

variable {V : Type u} {G : SimpleGraph V}
noncomputable local instance decidableEqForEdgeSupportedGraph : DecidableEq V := Classical.decEq V

/-- A finite edge family is realized with exactly its incident vertices. -/
theorem PlaneDrawing.exists_edgeSupported_subgraph
    (D : PlaneDrawing G) (F : Finset G.edgeSet) :
    ∃ H : Graph Plane (Sym2 V), H ≤ D.planeGraph ∧
      E(H).ncard = F.card ∧ V(H).ncard = (F.biUnion fun e => e.1.toFinset).card := by
  let names : Set (Sym2 V) := Subtype.val '' (↑F : Set G.edgeSet)
  let endpoints : Finset V := F.biUnion fun e => e.1.toFinset
  let X : Set Plane := D.point '' (↑endpoints : Set V)
  let H : Graph Plane (Sym2 V) := (D.planeGraph.restrict names).induce X
  have hX : X ⊆ V(D.planeGraph.restrict names) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    change D.point v ∈ V(D.planeGraph)
    rw [D.planeGraph_vertexSet]
    exact ⟨v, rfl⟩
  have hHG : H ≤ D.planeGraph :=
    (Graph.induce_le hX).trans Graph.restrict_le
  have hedges : E(H) = names := by
    ext edge
    constructor
    · intro hedge
      rw [Graph.edgeSet_induce] at hedge
      obtain ⟨x, y, hlink, hx, hy⟩ := hedge
      exact hlink.1
    · rintro ⟨edge', hedge'F, rfl⟩
      have hlink₀ : (Graph.ofSimpleGraph G).IsLink edge'.1 edge'.1.out.1 edge'.1.out.2 :=
        ⟨edge'.1.out_eq.symm, edge'.2⟩
      have hlink : (D.planeGraph.restrict names).IsLink edge'.1
          (D.point edge'.1.out.1) (D.point edge'.1.out.2) :=
        ⟨⟨edge', hedge'F, rfl⟩, hlink₀.map D.point⟩
      have hleft : D.point edge'.1.out.1 ∈ X := by
        refine ⟨edge'.1.out.1, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨edge', hedge'F,
          Sym2.mem_toFinset.mpr (Sym2.out_fst_mem edge'.1)⟩
      have hright : D.point edge'.1.out.2 ∈ X := by
        refine ⟨edge'.1.out.2, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨edge', hedge'F,
          Sym2.mem_toFinset.mpr (Sym2.out_snd_mem edge'.1)⟩
      rw [Graph.edgeSet_induce]
      exact ⟨D.point edge'.1.out.1, D.point edge'.1.out.2,
        hlink, hleft, hright⟩
  refine ⟨H, hHG, ?_, ?_⟩
  · rw [hedges, Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_coe_finset]
  · change X.ncard = endpoints.card
    rw [Set.ncard_image_of_injective _ D.point_injective, Set.ncard_coe_finset]

end

/-! ### Upstream module `MerLeanExperiment/DrawingBasics.lean` -/

section
variable {V : Type u} {G : SimpleGraph V}

/-- In a simple graph the drawing is injective on the entire closed edge. -/
theorem PlaneDrawing.edge_injective (D : PlaneDrawing G) (e : G.edgeSet) :
    Function.Injective (D.edgePoint e) := by
  have hend : e.1.out.1 ≠ e.1.out.2 := by
    intro h
    apply G.not_isDiag_of_mem_edgeSet e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact h
  intro s t hst
  by_cases hs0 : s = 0
  · subst s
    by_cases ht0 : t = 0
    · exact ht0.symm
    by_cases ht1 : t = 1
    · subst t
      exfalso
      apply hend
      apply D.vertexPoint_injective
      rw [← D.edge_zero e, ← D.edge_one e]
      exact hst
    · exact (D.edge_interior_avoids_vertex e e.1.out.1 ht0 ht1
        (hst ▸ D.edge_zero e)).elim
  by_cases hs1 : s = 1
  · subst s
    by_cases ht0 : t = 0
    · subst t
      exfalso
      apply hend
      apply D.vertexPoint_injective
      rw [← D.edge_zero e, ← D.edge_one e]
      exact hst.symm
    by_cases ht1 : t = 1
    · exact ht1.symm
    · exact (D.edge_interior_avoids_vertex e e.1.out.2 ht0 ht1
        (hst ▸ D.edge_one e)).elim
  by_cases ht0 : t = 0
  · subst t
    exact (D.edge_interior_avoids_vertex e e.1.out.1 hs0 hs1
      (hst.symm ▸ D.edge_zero e)).elim
  by_cases ht1 : t = 1
  · subst t
    exact (D.edge_interior_avoids_vertex e e.1.out.2 hs0 hs1
      (hst.symm ▸ D.edge_one e)).elim
  exact D.edge_interior_injective e hs0 hs1 ht0 ht1 hst

end

/-! ### Upstream module `MerLeanExperiment/EdgeParameters.lean` -/

section
open scoped unitInterval
open Schoenflies

variable {V : Type u} {G : SimpleGraph V}

/-- Extend a drawn edge to real parameters by clamping to the closed unit interval. -/
noncomputable def PlaneDrawing.edgeParam (D : PlaneDrawing G) (e : G.edgeSet)
    (t : ℝ) : Plane :=
  WithLp.toLp 2 (D.edgePoint e (Set.projIcc 0 1 zero_le_one t))

/-- The extended real-parameter curve is continuous. -/
theorem PlaneDrawing.continuous_edgeParam (D : PlaneDrawing G) (e : G.edgeSet) :
    Continuous (D.edgeParam e) := by
  exact (PiLp.continuous_toLp 2 _).comp
    ((D.edge_continuous e).comp continuous_projIcc)

/-- The extension equals the original parametrization on its domain. -/
theorem PlaneDrawing.edgeParam_coe (D : PlaneDrawing G) (e : G.edgeSet) (t : I) :
    D.edgeParam e (t : ℝ) = WithLp.toLp 2 (D.edgePoint e t) := by
  simp [PlaneDrawing.edgeParam, Set.projIcc_of_mem zero_le_one t.2]

/-- Clamping leaves the first endpoint unchanged. -/
theorem PlaneDrawing.edgeParam_zero (D : PlaneDrawing G) (e : G.edgeSet) :
    D.edgeParam e 0 = D.point e.1.out.1 := by
  rw [PlaneDrawing.point, ← D.edge_zero e]
  exact D.edgeParam_coe e 0

/-- Clamping leaves the last endpoint unchanged. -/
theorem PlaneDrawing.edgeParam_one (D : PlaneDrawing G) (e : G.edgeSet) :
    D.edgeParam e 1 = D.point e.1.out.2 := by
  rw [PlaneDrawing.point, ← D.edge_one e]
  exact D.edgeParam_coe e 1

/-- An edge remains injective on the real closed unit interval. -/
theorem PlaneDrawing.edgeParam_injOn (D : PlaneDrawing G) (e : G.edgeSet) :
    Set.InjOn (D.edgeParam e) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hsub : (⟨s, hs⟩ : I) = ⟨t, ht⟩ := by
    apply D.edge_injective e
    apply WithLp.toLp_injective 2
    simpa [PlaneDrawing.edgeParam, Set.projIcc_of_mem zero_le_one hs,
      Set.projIcc_of_mem zero_le_one ht] using hst
  exact congrArg Subtype.val hsub

end

/-! ### Upstream module `MerLeanExperiment/EdgeIncidence.lean` -/

section
open scoped unitInterval
variable {V : Type u} {G : SimpleGraph V}

/-- A vertex met by a drawn edge is one of its endpoints. -/
theorem PlaneDrawing.edgeParam_eq_point (D : PlaneDrawing G) (e : G.edgeSet)
    (t : I) (v : V) (h : D.edgeParam e (t : ℝ) = D.point v) :
    v = e.1.out.1 ∨ v = e.1.out.2 := by
  have hraw : D.edgePoint e t = D.vertexPoint v := by
    apply WithLp.toLp_injective 2
    simpa [PlaneDrawing.point, D.edgeParam_coe e t] using h
  by_cases ht0 : t = 0
  · left
    apply D.vertexPoint_injective
    subst t
    exact hraw.symm.trans (D.edge_zero e)
  by_cases ht1 : t = 1
  · right
    apply D.vertexPoint_injective
    subst t
    exact hraw.symm.trans (D.edge_one e)
  exact (D.edge_interior_avoids_vertex e v ht0 ht1 hraw).elim

/-- Distinct edge arcs intersect only at an original vertex image. -/
theorem PlaneDrawing.edgeParam_inter_vertex (D : PlaneDrawing G) (e f : G.edgeSet)
    (hef : e ≠ f) (s t : I)
    (h : D.edgeParam e (s : ℝ) = D.edgeParam f (t : ℝ)) :
    ∃ v : V, D.edgeParam e (s : ℝ) = D.point v := by
  by_cases hs0 : s = 0
  · exact ⟨e.1.out.1, hs0 ▸ D.edgeParam_zero e⟩
  by_cases hs1 : s = 1
  · exact ⟨e.1.out.2, hs1 ▸ D.edgeParam_one e⟩
  by_cases ht0 : t = 0
  · exact ⟨f.1.out.1, h.trans (ht0 ▸ D.edgeParam_zero f)⟩
  by_cases ht1 : t = 1
  · exact ⟨f.1.out.2, h.trans (ht1 ▸ D.edgeParam_one f)⟩
  exfalso
  apply D.edge_interiors_disjoint hef hs0 hs1 ht0 ht1
  apply WithLp.toLp_injective 2
  simpa [D.edgeParam_coe e s, D.edgeParam_coe f t] using h

end

/-! ### Upstream module `MerLeanExperiment/DrawingAdapter.lean` -/

section
open Schoenflies

variable {V : Type u} {G : SimpleGraph V}

/-- Real-plane edge curves indexed by the ambient edge-name type.
Names which are not edges are assigned a dummy value outside all drawing requirements. -/
noncomputable def PlaneDrawing.drawing (D : PlaneDrawing G) (e : Sym2 V)
    (t : ℝ) : Plane := by
  classical
  exact if he : e ∈ G.edgeSet then D.edgeParam ⟨e, he⟩ t else 0

/-- On genuine edges, the ambient drawing agrees with the original edge curve. -/
theorem PlaneDrawing.drawing_of_mem (D : PlaneDrawing G) (e : Sym2 V)
    (he : e ∈ G.edgeSet) (t : ℝ) :
    D.drawing e t = D.edgeParam ⟨e, he⟩ t := by
  simp [PlaneDrawing.drawing, he]

/-- The canonical ordered representatives of an edge give a link in the relabeled graph. -/
private theorem PlaneDrawing.planeGraph_isLink_out (D : PlaneDrawing G) (e : Sym2 V)
    (he : e ∈ G.edgeSet) :
    D.planeGraph.IsLink e (D.point e.out.1) (D.point e.out.2) := by
  apply Graph.IsLink.map D.point
  exact ⟨e.out_eq.symm, he⟩

/-- An ordinary crossing-free drawing realizes the standard plane-graph interface. -/
theorem PlaneDrawing.isDrawing (D : PlaneDrawing G) :
    Graph.IsDrawing D.planeGraph D.drawing := by
  refine { edge_param := ?_, vertex_mem_edgeArc := ?_, edge_inter := ?_ }
  · intro e he
    have hdrawing : D.drawing e = D.edgeParam ⟨e, he⟩ :=
      funext (D.drawing_of_mem e he)
    rw [hdrawing]
    have hl := D.planeGraph_isLink_out e he
    refine ⟨(D.continuous_edgeParam ⟨e, he⟩).continuousOn,
      D.edgeParam_injOn ⟨e, he⟩, ?_⟩
    simpa [D.edgeParam_zero ⟨e, he⟩, D.edgeParam_one ⟨e, he⟩] using hl
  · intro e x y v hl hv hve
    rw [D.planeGraph_vertexSet] at hv
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨t, ht, htw⟩ := hve
    have hpoint : D.edgeParam ⟨e, hl.edge_mem⟩ t = D.point w := by
      rw [← D.drawing_of_mem e hl.edge_mem]
      exact htw
    have hw := D.edgeParam_eq_point ⟨e, hl.edge_mem⟩ ⟨t, ht⟩ w hpoint
    rcases hl.eq_and_eq_or_eq_and_eq
        (D.planeGraph_isLink_out e hl.edge_mem) with hxy | hxy
    · rcases hxy with ⟨rfl, rfl⟩
      exact hw.imp (congrArg D.point) (congrArg D.point)
    · rcases hxy with ⟨rfl, rfl⟩
      exact hw.symm.imp (congrArg D.point) (congrArg D.point)
  · intro e f he hf hef p hpe hpf
    obtain ⟨s, hs, hsp⟩ := hpe
    obtain ⟨t, ht, htp⟩ := hpf
    let ee : G.edgeSet := ⟨e, he⟩
    let ff : G.edgeSet := ⟨f, hf⟩
    have hef' : ee ≠ ff := by
      intro h
      exact hef (congrArg Subtype.val h)
    have hinter : D.edgeParam ee s = D.edgeParam ff t := by
      rw [← D.drawing_of_mem e he, ← D.drawing_of_mem f hf]
      exact hsp.trans htp.symm
    obtain ⟨v, hev⟩ := D.edgeParam_inter_vertex ee ff hef' ⟨s, hs⟩ ⟨t, ht⟩ hinter
    have hpv : p = D.point v := hsp.symm.trans <| (D.drawing_of_mem e he s).trans hev
    have hfv : D.edgeParam ff t = D.point v := hinter.symm.trans hev
    have he_end := D.edgeParam_eq_point ee ⟨s, hs⟩ v hev
    have hf_end := D.edgeParam_eq_point ff ⟨t, ht⟩ v hfv
    rw [hpv]
    refine ⟨?_, ?_, ?_⟩
    · rw [D.planeGraph_vertexSet]
      exact ⟨v, rfl⟩
    · rcases he_end with rfl | rfl
      · exact (D.planeGraph_isLink_out e he).inc_left
      · exact (D.planeGraph_isLink_out e he).inc_right
    · rcases hf_end with rfl | rfl
      · exact (D.planeGraph_isLink_out f hf).inc_left
      · exact (D.planeGraph_isLink_out f hf).inc_right

end

/-! ### Upstream module `MerLeanExperiment/HereditaryDensity.lean` -/

section
open Schoenflies

variable {V : Type u} {G : SimpleGraph V}
noncomputable local instance decidableEqForHereditaryDensity : DecidableEq V := Classical.decEq V

/-- Every finite edge family satisfies the endpoint-density bound. -/
theorem PlaneDrawing.hereditary_density [Finite V]
    (D : PlaneDrawing G) (hbipartite : G.IsBipartite) (F : Finset G.edgeSet) :
    F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card := by
  have hplaneFinite : D.planeGraph.Finite := D.planeGraph_finite
  have hplaneSimple : D.planeGraph.Simple := D.planeGraph_simple
  obtain ⟨c, hcolor⟩ := D.exists_bicoloring hbipartite
  obtain ⟨H, hHG, hedge, hvert⟩ := D.exists_edgeSupported_subgraph F
  have hHFinite : H.Finite := Graph.Finite.of_le hHG
  have hHSimple : H.Simple := Graph.Simple.anti hHG
  have hcolorH : ∀ (e : Sym2 V) (x y : Plane), H.IsLink e x y → c x ≠ c y :=
    fun e x y hxy => hcolor e x y (hxy.mono hHG)
  have hdensity := (D.isDrawing.mono hHG).bipartite_density c hcolorH
  omega

end

/-! ### Upstream module `MerLeanExperiment/TwoOrientation.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/

variable {V : Type u}
noncomputable local instance decidableEqForTwoOrientation : DecidableEq V := Classical.decEq V

/-- An orientation represented by its chosen tail endpoint.  The auxiliary
slot is the Hall matching certificate: injectivity of `(tail, slot)` implies
that no vertex is the tail of more than two edges. -/
structure TwoOrientation (G : SimpleGraph V) where
  tail : G.edgeSet → V
  slot : G.edgeSet → Fin 2
  tail_mem (e : G.edgeSet) : tail e ∈ e.1.toFinset
  slot_injective : Function.Injective fun e => (tail e, slot e)

namespace TwoOrientation

variable {G : SimpleGraph V} (O : TwoOrientation G)

/-- The directed arc relation induced by a chosen tail for every edge. -/
def Arc (u v : V) : Prop :=
  ∃ e : G.edgeSet, O.tail e = u ∧ e.1 = s(u, v)

lemma arc_adj {u v : V} (h : O.Arc u v) : G.Adj u v := by
  obtain ⟨e, -, he⟩ := h
  change s(u, v) ∈ G.edgeSet
  exact he ▸ e.2

lemma arc_ne {u v : V} (h : O.Arc u v) : u ≠ v :=
  (O.arc_adj h).ne

lemma arc_or_arc_symm {u v : V} (h : G.Adj u v) : O.Arc u v ∨ O.Arc v u := by
  classical
  let e : G.edgeSet := ⟨s(u, v), h⟩
  have ht := O.tail_mem e
  change O.tail e ∈ s(u, v).toFinset at ht
  rw [Sym2.mem_toFinset, Sym2.mem_iff] at ht
  rcases ht with ht | ht
  · exact Or.inl ⟨e, ht, rfl⟩
  · exact Or.inr ⟨e, ht, Sym2.eq_swap⟩

/-- The canonically represented edge underlying an arc. -/
def edgeOfArc {u v : V} (h : O.Arc u v) : G.edgeSet :=
  ⟨s(u, v), O.arc_adj h⟩

lemma tail_edgeOfArc {u v : V} (h : O.Arc u v) : O.tail (O.edgeOfArc h) = u := by
  rcases h with ⟨e, he, hval⟩
  have heq : O.edgeOfArc ⟨e, he, hval⟩ = e := Subtype.ext hval.symm
  rw [heq]
  exact he

/-- Out-neighbours inside a finite active vertex set. -/
noncomputable def outNeighbors (U : Finset V) (v : V) : Finset V :=
  by
    classical
    exact U.filter (O.Arc v)

@[simp]
lemma mem_outNeighbors {U : Finset V} {v w : V} :
    w ∈ O.outNeighbors U v ↔ w ∈ U ∧ O.Arc v w := by
  simp [outNeighbors]

lemma outNeighbors_mono {U W : Finset V} (hUW : U ⊆ W) (v : V) :
    O.outNeighbors U v ⊆ O.outNeighbors W v := by
  intro w hw
  simp only [mem_outNeighbors] at hw ⊢
  exact ⟨hUW hw.1, hw.2⟩

/-- The Hall slots force outdegree at most two, also after restriction to any
finite active vertex set. -/
lemma card_outNeighbors_le_two (U : Finset V) (v : V) :
    (O.outNeighbors U v).card ≤ 2 := by
  let f : {w // w ∈ O.outNeighbors U v} → Fin 2 := fun w =>
    O.slot (O.edgeOfArc ((O.mem_outNeighbors.mp w.2).2))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxarc := (O.mem_outNeighbors.mp x.2).2
    have hyarc := (O.mem_outNeighbors.mp y.2).2
    have hpair :
        (O.tail (O.edgeOfArc hxarc), O.slot (O.edgeOfArc hxarc)) =
          (O.tail (O.edgeOfArc hyarc), O.slot (O.edgeOfArc hyarc)) := by
      rw [O.tail_edgeOfArc hxarc, O.tail_edgeOfArc hyarc]
      exact Prod.ext rfl hxy
    have hedge := O.slot_injective hpair
    have hsym : s(v, x.1) = s(v, y.1) := congrArg Subtype.val hedge
    rw [Sym2.eq_iff] at hsym
    rcases hsym with h | h
    · exact h.2
    · exact (O.arc_ne hxarc h.2.symm).elim
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe (O.outNeighbors U v)]
  exact hcard

end TwoOrientation

end

/-! ### Upstream module `MerLeanExperiment/HallOrientation.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/

variable {V : Type u}
noncomputable local instance decidableEqForHallOrientation : DecidableEq V := Classical.decEq V

/-! ## Hall--Hakimi orientation -/

/-- The endpoint slots available to an edge. -/
noncomputable def edgeSlots {G : SimpleGraph V} (e : G.edgeSet) : Finset (V × Fin 2) :=
  by
    classical
    exact e.1.toFinset ×ˢ Finset.univ

lemma biUnion_edgeSlots {G : SimpleGraph V} (F : Finset G.edgeSet) :
    F.biUnion edgeSlots =
      (F.biUnion fun e => e.1.toFinset) ×ˢ (Finset.univ : Finset (Fin 2)) := by
  classical
  ext x
  simp [edgeSlots]

/-- The hereditary endpoint bound gives an orientation of maximum outdegree two. -/
noncomputable def twoOrientation_of_density {G : SimpleGraph V}
    (hdensity : ∀ F : Finset G.edgeSet,
      F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card) : TwoOrientation G := by
  classical
  have hall : ∀ F : Finset G.edgeSet,
      F.card ≤ (F.biUnion edgeSlots).card := by
    intro F
    rw [biUnion_edgeSlots, Finset.card_product]
    simpa [Fintype.card_fin, mul_comm] using
      hdensity F
  let hex := (Finset.all_card_le_biUnion_card_iff_exists_injective edgeSlots).mp hall
  let matchSlot := Classical.choose hex
  have hmatch_inj := (Classical.choose_spec hex).1
  have hmatch_mem := (Classical.choose_spec hex).2
  exact
    { tail := fun e => (matchSlot e).1
      slot := fun e => (matchSlot e).2
      tail_mem := fun e => (Finset.mem_product.mp (hmatch_mem e)).1
      slot_injective := fun _ _ h => hmatch_inj (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h)) }

end

/-! ### Upstream module `MerLeanExperiment/Kernels.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/

variable {V : Type u}
noncomputable local instance decidableEqForKernels : DecidableEq V := Classical.decEq V

/-! ## Kernels of bipartite orientations -/

variable {G : SimpleGraph V}

/-- Vertices in the second bipartition class not yet absorbed by `S`. -/
noncomputable def residual (O : TwoOrientation G) (B S : Finset V) : Finset V :=
  by
    classical
    exact B.filter fun b => ∀ a ∈ S, ¬ O.Arc b a

/-- `S` has no arc to a second-part vertex that is not absorbed by `S`. -/
def Admissible (O : TwoOrientation G) (B S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ residual O B S, ¬ O.Arc a b

/-- A directed kernel in the subdigraph induced by `X`. -/
def IsKernel (O : TwoOrientation G) (X K : Finset V) : Prop :=
  K ⊆ X ∧
    (∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v) ∧
    ∀ v ∈ X, v ∉ K → ∃ k ∈ K, O.Arc v k

namespace IsKernel

lemma subset {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) : K ⊆ X :=
  h.1

lemma arc_free {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) : ¬ O.Arc u v :=
  h.2.1 u hu v hv

lemma absorbs {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {v : V} (hvX : v ∈ X) (hvK : v ∉ K) : ∃ k ∈ K, O.Arc v k :=
  h.2.2 v hvX hvK

lemma isIndepSet {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) :
    G.IsIndepSet (K : Set V) := by
  intro u hu v hv huv hadj
  rcases O.arc_or_arc_symm hadj with huv' | hvu'
  · exact h.arc_free hu hv huv'
  · exact h.arc_free hv hu hvu'

end IsKernel

/-- Every finite induced subdigraph of an orientation of a bipartite graph has
a kernel.  The proof chooses a maximum-cardinality admissible subset of one
bipartition class. -/
theorem exists_kernel_of_bipartite {G : SimpleGraph V} (O : TwoOrientation G)
    (hG : G.IsBipartite) (X : Finset V) :
    ∃ K : Finset V, IsKernel O X K := by
  classical
  rcases hG with ⟨C⟩
  let A : Finset V := X.filter fun v => C v = 0
  let B : Finset V := X.filter fun v => C v = 1
  have hAB (v : V) (hv : v ∈ X) : v ∈ A ∨ v ∈ B := by
    simp only [A, B, Finset.mem_filter, hv, true_and]
    have hc := (C v).isLt
    omega
  have hA_sub : A ⊆ X := Finset.filter_subset _ _
  have hB_sub : B ⊆ X := Finset.filter_subset _ _
  have hA_arc_free {u v : V} (hu : u ∈ A) (hv : v ∈ A) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 0 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 0 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  have hB_arc_free {u v : V} (hu : u ∈ B) (hv : v ∈ B) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 1 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 1 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  let candidates : Finset (Finset V) := A.powerset.filter (Admissible O B)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, Admissible]
  obtain ⟨S, hScand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hSA : S ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hScand).1
  have hSad : Admissible O B S := (Finset.mem_filter.mp hScand).2
  let T : Finset V := residual O B S
  let K : Finset V := S ∪ T
  have hTB : T ⊆ B := Finset.filter_subset _ _
  have hKX : K ⊆ X := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact hA_sub (hSA hvS)
    · exact hB_sub (hTB hvT)
  have hKind : ∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v := by
    intro u hu v hv
    rcases Finset.mem_union.mp hu with huS | huT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact hA_arc_free (hSA huS) (hSA hvS)
      · exact hSad u huS v hvT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact (Finset.mem_filter.mp huT).2 v hvS
      · exact hB_arc_free (hTB huT) (hTB hvT)
  refine ⟨K, hKX, hKind, ?_⟩
  intro x hxX hxK
  rcases hAB x hxX with hxA | hxB
  · have hxS : x ∉ S := fun hx => hxK (Finset.mem_union_left T hx)
    have hex : ∃ b ∈ T, O.Arc x b := by
      by_contra! hnone
      have hres_sub : residual O B (insert x S) ⊆ T := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        apply Finset.mem_filter.mpr
        refine ⟨hb'.1, ?_⟩
        intro a haS
        exact hb'.2 a (Finset.mem_insert_of_mem haS)
      have hins_ad : Admissible O B (insert x S) := by
        intro a ha b hb
        rcases Finset.mem_insert.mp ha with rfl | haS
        · exact hnone b (hres_sub hb)
        · exact hSad a haS b (hres_sub hb)
      have hins_cand : insert x S ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxA hSA), hins_ad⟩
      have hle := hmax (insert x S) hins_cand
      rw [Finset.card_insert_of_notMem hxS] at hle
      omega
    obtain ⟨b, hbT, hxb⟩ := hex
    exact ⟨b, Finset.mem_union_right S hbT, hxb⟩
  · have hxT : x ∉ T := fun hx => hxK (Finset.mem_union_right S hx)
    have hnot : ¬(∀ a ∈ S, ¬ O.Arc x a) := by
      intro h
      exact hxT (Finset.mem_filter.mpr ⟨hxB, h⟩)
    push Not at hnot
    obtain ⟨a, haS, hxa⟩ := hnot
    exact ⟨a, Finset.mem_union_left T haS, hxa⟩

end

/-! ### Upstream module `MerLeanExperiment/KernelColoring.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/

variable {V : Type u}
noncomputable local instance decidableEqForKernelColoring : DecidableEq V := Classical.decEq V

/-! ## The kernel list-colouring lemma -/

/-- A kernel for every finite induced vertex set, together with the local
strict list-size bound, colours any finite active vertex set.  The result is
stated with a total colour function; its guarantees concern the active set. -/
theorem exists_list_coloring_on
    {G : SimpleGraph V} (O : TwoOrientation G)
    (hkernel : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K)
    (L : V → Finset ℕ) (U : Finset V)
    (hcap : ∀ v ∈ U, (O.outNeighbors U v).card < (L v).card) :
    ∃ f : V → ℕ,
      (∀ v ∈ U, f v ∈ L v) ∧
      ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → f u ≠ f v := by
  classical
  induction U using Finset.strongInduction generalizing L with
  | H U ih =>
      by_cases hUne : U.Nonempty
      · obtain ⟨u₀, hu₀U⟩ := hUne
        have hLpos : 0 < (L u₀).card :=
          (Nat.zero_le (O.outNeighbors U u₀).card).trans_lt (hcap u₀ hu₀U)
        have hLne : (L u₀).Nonempty := Finset.card_pos.mp hLpos
        let c : ℕ := (L u₀).min' hLne
        have hcL : c ∈ L u₀ := Finset.min'_mem (L u₀) hLne
        let X : Finset V := U.filter fun v => c ∈ L v
        have hu₀X : u₀ ∈ X := Finset.mem_filter.mpr ⟨hu₀U, hcL⟩
        obtain ⟨K, hK⟩ := hkernel X
        have hKne : K.Nonempty := by
          by_contra h
          have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          obtain ⟨k, hkK, -⟩ := hK.absorbs hu₀X (by simp [hKempty])
          simp [hKempty] at hkK
        let U' : Finset V := U \ K
        let L' : V → Finset ℕ := fun v => (L v).erase c
        have hKsubU : K ⊆ U := by
          exact hK.subset.trans (Finset.filter_subset _ _)
        have hU'ssub : U' ⊂ U := Finset.sdiff_ssubset hKsubU hKne
        have hcap' : ∀ v ∈ U', (O.outNeighbors U' v).card < (L' v).card := by
          intro v hvU'
          have hvU : v ∈ U := Finset.sdiff_subset hvU'
          have houtsub : O.outNeighbors U' v ⊆ O.outNeighbors U v :=
            O.outNeighbors_mono Finset.sdiff_subset v
          by_cases hcv : c ∈ L v
          · have hvX : v ∈ X := Finset.mem_filter.mpr ⟨hvU, hcv⟩
            have hvK : v ∉ K := (Finset.mem_sdiff.mp hvU').2
            obtain ⟨k, hkK, hvk⟩ := hK.absorbs hvX hvK
            have hkU : k ∈ U := hKsubU hkK
            have hkout : k ∈ O.outNeighbors U v :=
              O.mem_outNeighbors.mpr ⟨hkU, hvk⟩
            have hkout' : k ∉ O.outNeighbors U' v := by
              intro hk
              exact (Finset.mem_sdiff.mp (O.mem_outNeighbors.mp hk).1).2 hkK
            have houtssub : O.outNeighbors U' v ⊂ O.outNeighbors U v :=
              Finset.ssubset_iff_subset_ne.mpr ⟨houtsub, fun heq => hkout' (heq ▸ hkout)⟩
            have houtlt := Finset.card_lt_card houtssub
            have hLcard : (L' v).card = (L v).card - 1 := by
              exact Finset.card_erase_of_mem hcv
            have holdlt := hcap v hvU
            dsimp only [L'] at hLcard ⊢
            omega
          · have hL'eq : L' v = L v := by simp [L', hcv]
            rw [hL'eq]
            exact (Finset.card_mono houtsub).trans_lt (hcap v hvU)
        obtain ⟨f, hfL, hfproper⟩ := ih U' hU'ssub L' hcap'
        let g : V → ℕ := fun v => if v ∈ K then c else f v
        refine ⟨g, ?_, ?_⟩
        · intro v hvU
          by_cases hvK : v ∈ K
          · simp only [g, ite_eq_left hvK]
            have hvX : v ∈ X := hK.subset hvK
            exact (Finset.mem_filter.mp hvX).2
          · simp only [g, ite_eq_right hvK]
            have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
            exact Finset.mem_of_mem_erase (hfL v hvU')
        · intro u huU v hvU huv
          by_cases huK : u ∈ K
          · by_cases hvK : v ∈ K
            · exact (hK.isIndepSet huK hvK huv.ne huv).elim
            · simp only [g, ite_eq_left huK, ite_eq_right hvK]
              have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
              exact (Finset.mem_erase.mp (hfL v hvU')).1.symm
          · by_cases hvK : v ∈ K
            · simp only [g, ite_eq_right huK, ite_eq_left hvK]
              have huU' : u ∈ U' := Finset.mem_sdiff.mpr ⟨huU, huK⟩
              exact (Finset.mem_erase.mp (hfL u huU')).1
            · simp only [g, ite_eq_right huK, ite_eq_right hvK]
              exact hfproper u (Finset.mem_sdiff.mpr ⟨huU, huK⟩)
                v (Finset.mem_sdiff.mpr ⟨hvU, hvK⟩) huv
      · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro v hv
          exfalso
          simp [hUempty] at hv
        · intro u hu
          exfalso
          simp [hUempty] at hu

end

/-! ### Upstream module `MerLeanExperiment/ColoringFromDensity.lean` -/

section
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/

variable {V : Type u}
noncomputable local instance decidableEqForColoringFromDensity : DecidableEq V := Classical.decEq V

/-- The hereditary endpoint bound implies three-list-colorability for bipartite graphs. -/
theorem three_list_colorable_of_density
    [Finite V] (G : SimpleGraph V)
    (hdensity : ∀ F : Finset G.edgeSet,
      F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card)
    (hbipartite : G.IsBipartite) (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let O : TwoOrientation G := twoOrientation_of_density hdensity
  have hkernels : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K :=
    fun X => exists_kernel_of_bipartite O hbipartite X
  have hcap : ∀ v ∈ (Finset.univ : Finset V),
      (O.outNeighbors Finset.univ v).card < (L v).card := by
    intro v _
    have hout := O.card_outNeighbors_le_two (Finset.univ : Finset V) v
    rw [hL v]
    omega
  obtain ⟨f, hfL, hfproper⟩ :=
    exists_list_coloring_on O hkernels L (Finset.univ : Finset V) hcap
  refine ⟨SimpleGraph.Coloring.mk f ?_, fun v => hfL v (Finset.mem_univ v)⟩
  intro u v huv
  exact hfproper u (Finset.mem_univ u) v (Finset.mem_univ v) huv

end

/-! ### Upstream module `MerLeanExperiment/Goal.lean` -/

theorem planar_bipartite_three_list_colorable
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v := by
  obtain ⟨D⟩ := hplanar
  exact three_list_colorable_of_density G
    (D.hereditary_density hbipartite) hbipartite L hL

/-! ### Upstream module `MerLeanExperiment/ArbitraryPalette.lean` -/

theorem erdos_630
    {V : Type} {C : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset C) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  let S : Finset C := Finset.univ.biUnion L
  let encode : C → ℕ := fun c =>
    if hc : c ∈ S then (Fintype.equivFin S ⟨c, hc⟩).val else 0
  have hencode_inj : Set.InjOn encode (↑S : Set C) := by
    intro a ha b hb hab
    have ha' : a ∈ S := ha
    have hb' : b ∈ S := hb
    have hea : encode a = (Fintype.equivFin S ⟨a, ha⟩).val := by
      simp [encode, ha']
    have heb : encode b = (Fintype.equivFin S ⟨b, hb⟩).val := by
      simp [encode, hb']
    rw [hea, heb] at hab
    have hsub : (⟨a, ha⟩ : S) = ⟨b, hb⟩ := by
      apply (Fintype.equivFin S).injective
      apply Fin.ext
      exact hab
    exact congrArg Subtype.val hsub
  let LN : V → Finset ℕ := fun v => (L v).image encode
  have hLS (v : V) : ↑(L v) ⊆ (↑S : Set C) := by
    intro c hc
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hc⟩
  have hLN (v : V) : (LN v).card = 3 := by
    rw [Finset.card_image_iff.mpr (hencode_inj.mono (hLS v)), hL v]
  obtain ⟨fN, hfN⟩ :=
    planar_bipartite_three_list_colorable G hplanar hbipartite LN hLN
  have hex (v : V) : ∃ c ∈ L v, encode c = fN v := by
    simpa only [LN, Finset.mem_image] using hfN v
  choose f hfL hfencode using hex
  refine ⟨SimpleGraph.Coloring.mk f ?_, hfL⟩
  intro u v huv huv_eq
  apply fN.valid huv
  rw [← hfencode u, ← hfencode v, huv_eq]

#print axioms erdos_630
-- 'Erdos630.erdos_630' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos630
