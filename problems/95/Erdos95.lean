import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos95

/-
# Problem Description

Erdős Problem 95 ($500). Let `x₁, …, xₙ ∈ ℝ²` determine the distance set `{u₁, …, u_t}`, and
let `f(uᵢ)` be the number of pairs of points at distance `uᵢ`. Then for every `ε > 0`

  `∑ᵢ f(uᵢ)² ≪_ε n^(3+ε)`.

`erdos_95` proves this. Solved by Guth and Katz, who obtained the sharper `≪ n³ log n`; the
convex-polygon case was done earlier by Altman. It is trivial that `∑ᵢ f(uᵢ) = C(n, 2)`.

`Point` is `EuclideanSpace ℝ (Fin 2)`, `pairDistance` is the Euclidean `dist` lifted to
unordered pairs via `Sym2`, `distanceMultiplicity P u` counts the unordered pairs at
distance `u`, and `distanceEnergy P` is `∑ u ∈ distances P, distanceMultiplicity P u ^ 2`.
The constant `C` is chosen after `ε` but before the point set, which is the `≪_ε`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/ElekesSharir.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The Elekes--Sharir line construction

This file develops the elementary coordinate geometry used in the reduction
of the planar equal-distance problem to incidences of lines in three-space.
-/

namespace ES

/-- A point of the Euclidean plane. -/
abbrev PlanePoint := EuclideanSpace ℝ (Fin 2)

/-- Coordinate three-space.  Its topology is not needed for the algebraic
Elekes--Sharir correspondence. -/
abbrev Space3 := Fin 3 → ℝ

/-- Squared Euclidean distance in coordinates. -/
noncomputable def sqDist (p q : PlanePoint) : ℝ :=
  (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2

theorem sqDist_eq_dist_sq (p q : PlanePoint) : sqDist p q = dist p q ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sqDist, Fin.sum_univ_two, Real.dist_eq]
  rw [abs_sub_comm (p 0), abs_sub_comm (p 1), sq_abs, sq_abs]
  ring

theorem sqDist_eq_iff_dist_eq {p q r s : PlanePoint} :
    sqDist p q = sqDist r s ↔ dist p q = dist r s := by
  rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.trans <| by
    constructor
    · rintro (h | h)
      · exact h
      · nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := r) (y := s)]
    · exact Or.inl

/-- The normalized parametrization of the Elekes--Sharir line indexed by
`(p,q)`.  The third coordinate is the line parameter. -/
noncomputable def linePoint (p q : PlanePoint) (t : ℝ) : Space3 :=
  ![(p 0 + q 0) / 2 + t * (q 1 - p 1) / 2,
    (p 1 + q 1) / 2 + t * (p 0 - q 0) / 2,
    t]

/-- Two normalized Elekes--Sharir lines which agree at two distinct
parameters have the same pair of indices. -/
theorem eq_of_linePoint_eq_at_two
    {p q r s : PlanePoint} {t u : ℝ} (htu : t ≠ u)
    (ht : linePoint p q t = linePoint r s t)
    (hu : linePoint p q u = linePoint r s u) :
    p = r ∧ q = s := by
  have ht0 := congrFun ht (0 : Fin 3)
  have ht1 := congrFun ht (1 : Fin 3)
  have hu0 := congrFun hu (0 : Fin 3)
  have hu1 := congrFun hu (1 : Fin 3)
  simp [linePoint] at ht0 ht1 hu0 hu1
  have hprod1 :
      (t - u) * ((q 1 - p 1) - (s 1 - r 1)) = 0 := by
    nlinarith [ht0, hu0]
  have hprod0 :
      (t - u) * ((p 0 - q 0) - (r 0 - s 0)) = 0 := by
    nlinarith [ht1, hu1]
  have htu' : t - u ≠ 0 := sub_ne_zero.mpr htu
  have hslope1 : q 1 - p 1 = s 1 - r 1 := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hprod1 |>.resolve_left htu')
  have hslope0 : p 0 - q 0 = r 0 - s 0 := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hprod0 |>.resolve_left htu')
  have hintercept0 : p 0 + q 0 = r 0 + s 0 := by
    rw [hslope1] at ht0
    linarith [ht0]
  have hintercept1 : p 1 + q 1 = r 1 + s 1 := by
    rw [hslope0] at ht1
    linarith [ht1]
  have hp0 : p 0 = r 0 := by linarith
  have hq0 : q 0 = s 0 := by linarith
  have hp1 : p 1 = r 1 := by linarith
  have hq1 : q 1 = s 1 := by linarith
  constructor
  · apply PiLp.ext
    intro i
    fin_cases i
    · exact hp0
    · exact hp1
  · apply PiLp.ext
    intro i
    fin_cases i
    · exact hq0
    · exact hq1

/-- Incidence with an Elekes--Sharir line. -/
def OnLine (p q : PlanePoint) (x : Space3) : Prop :=
  ∃ t : ℝ, x = linePoint p q t

/-- Two Elekes--Sharir lines have a common point. -/
def Intersects (p q r s : PlanePoint) : Prop :=
  ∃ x : Space3, OnLine p q x ∧ OnLine r s x

/-- Distinct indexed Elekes--Sharir lines have at most one common point. -/
theorem intersection_unique {p q r s : PlanePoint}
    (hne : (p, q) ≠ (r, s)) {x y : Space3}
    (hx₁ : OnLine p q x) (hx₂ : OnLine r s x)
    (hy₁ : OnLine p q y) (hy₂ : OnLine r s y) : x = y := by
  obtain ⟨t, rfl⟩ := hx₁
  obtain ⟨u, htu⟩ := hx₂
  have htu' : t = u := by
    simpa [linePoint] using congrFun htu (2 : Fin 3)
  subst u
  obtain ⟨v, hyv⟩ := hy₁
  obtain ⟨w, hyw⟩ := hy₂
  have hvw : v = w := by
    have := hyv.symm.trans hyw
    simpa [linePoint] using congrFun this (2 : Fin 3)
  subst w
  have htv : t = v := by
    by_contra htv
    apply hne
    exact Prod.ext
      (eq_of_linePoint_eq_at_two htv htu (hyv.symm.trans hyw)).1
      (eq_of_linePoint_eq_at_two htv htu (hyv.symm.trans hyw)).2
  rw [htv]
  exact hyv.symm

/-- The two segments differ by a common translation.  In the
Elekes--Sharir model this is exactly the parallel-line case. -/
def IsTranslation (a b c d : PlanePoint) : Prop :=
  c 0 - a 0 = d 0 - b 0 ∧ c 1 - a 1 = d 1 - b 1

private theorem exists_parameter_of_equal_squares
    {ux uy vx vy : ℝ}
    (h : ux ^ 2 + uy ^ 2 = vx ^ 2 + vy ^ 2)
    (hne : ux ≠ vx ∨ uy ≠ vy) :
    ∃ t : ℝ,
      t * (uy - vy) = ux + vx ∧
      t * (vx - ux) = uy + vy := by
  let den := (uy - vy) ^ 2 + (vx - ux) ^ 2
  have hdenpos : 0 < den := by
    rcases hne with hux | huy
    · have hs : 0 < (vx - ux) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hux.symm)
      dsimp [den]
      nlinarith [sq_nonneg (uy - vy)]
    · have hs : 0 < (uy - vy) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr huy)
      dsimp [den]
      nlinarith [sq_nonneg (vx - ux)]
  have hparallel :
      (uy - vy) * (uy + vy) = (vx - ux) * (ux + vx) := by
    ring_nf at h ⊢
    linarith
  refine ⟨((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) / den, ?_, ?_⟩
  · field_simp [hdenpos.ne']
    dsimp [den]
    calc
      (uy - vy) * ((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) =
          (ux + vx) * (uy - vy) ^ 2 +
            ((uy - vy) * (uy + vy)) * (vx - ux) := by ring
      _ = (ux + vx) * (uy - vy) ^ 2 +
            ((vx - ux) * (ux + vx)) * (vx - ux) := by rw [hparallel]
      _ = (ux + vx) * ((uy - vy) ^ 2 + (vx - ux) ^ 2) := by ring
  · field_simp [hdenpos.ne']
    dsimp [den]
    calc
      (vx - ux) * ((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) =
          ((vx - ux) * (ux + vx)) * (uy - vy) +
            (uy + vy) * (vx - ux) ^ 2 := by ring
      _ = ((uy - vy) * (uy + vy)) * (uy - vy) +
            (uy + vy) * (vx - ux) ^ 2 := by rw [hparallel]
      _ = (uy + vy) * ((uy - vy) ^ 2 + (vx - ux) ^ 2) := by ring

/-- Incidence of the two lines forces equality of the corresponding planar
segment lengths. -/
theorem sqDist_eq_of_intersects {a b c d : PlanePoint}
    (h : Intersects a c b d) : sqDist a b = sqDist c d := by
  rcases h with ⟨x, ⟨t, hact⟩, ⟨u, hbud⟩⟩
  have hlines : linePoint a c t = linePoint b d u := hact.symm.trans hbud
  have h2 : t = u := by
    simpa [linePoint] using congrFun hlines (2 : Fin 3)
  subst u
  have h0 := congrFun hlines (0 : Fin 3)
  have h1 := congrFun hlines (1 : Fin 3)
  simp [linePoint] at h0 h1
  have heq0 :
      (a 0 - b 0) + (c 0 - d 0) =
        t * ((a 1 - b 1) - (c 1 - d 1)) := by
    linarith
  have heq1 :
      (a 1 - b 1) + (c 1 - d 1) =
        t * ((c 0 - d 0) - (a 0 - b 0)) := by
    linarith
  dsimp [sqDist]
  linear_combination
    ((a 0 - b 0) - (c 0 - d 0)) * heq0 +
      ((a 1 - b 1) - (c 1 - d 1)) * heq1

/-- Equal nonzero segment lengths give either a common translation or an
intersection of the associated Elekes--Sharir lines. -/
theorem intersects_of_sqDist_eq_of_not_translation {a b c d : PlanePoint}
    (hdist : sqDist a b = sqDist c d)
    (htrans : ¬IsTranslation a b c d) : Intersects a c b d := by
  have hne : a 0 - b 0 ≠ c 0 - d 0 ∨ a 1 - b 1 ≠ c 1 - d 1 := by
    by_contra h
    push Not at h
    apply htrans
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨t, ht0, ht1⟩ := exists_parameter_of_equal_squares hdist hne
  refine ⟨linePoint a c t, ⟨t, rfl⟩, ⟨t, ?_⟩⟩
  funext i
  fin_cases i
  · simp [linePoint]
    linarith
  · simp [linePoint]
    linarith
  · simp [linePoint]

/-- Parallel Elekes--Sharir lines which meet are the same indexed line.  In
the affine chart used here, `IsTranslation` says precisely that their
direction vectors agree. -/
theorem eq_of_intersects_of_translation {a b c d : PlanePoint}
    (hint : Intersects a c b d) (htrans : IsTranslation a b c d) :
    a = b ∧ c = d := by
  rcases hint with ⟨x, ⟨t, hact⟩, ⟨u, hbud⟩⟩
  have hlines : linePoint a c t = linePoint b d u := hact.symm.trans hbud
  have htu : t = u := by
    simpa [linePoint] using congrFun hlines (2 : Fin 3)
  subst u
  have h0 := congrFun hlines (0 : Fin 3)
  have h1 := congrFun hlines (1 : Fin 3)
  simp [linePoint] at h0 h1
  dsimp [IsTranslation] at htrans
  have hdir1 : a 0 - c 0 = b 0 - d 0 := by linarith [htrans.1]
  rw [htrans.2] at h0
  rw [hdir1] at h1
  have ha0 : a 0 = b 0 := by linarith [h0, htrans.1]
  have ha1 : a 1 = b 1 := by linarith [h1, htrans.2]
  have hc0 : c 0 = d 0 := by linarith [htrans.1, ha0]
  have hc1 : c 1 = d 1 := by linarith [htrans.2, ha1]
  constructor
  · apply PiLp.ext
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact ha0
    · exact ha1
  · apply PiLp.ext
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact hc0
    · exact hc1

end ES

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SetFamilyBounds.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Bounded-overlap finite set families

This file isolates the combinatorial counting lemma behind Guth's surface
pruning argument.  If every member of a finite set family has at least `A`
elements and distinct members overlap in at most `B` elements, then the
family has at most `2|U|/A` members as soon as `A² > 4B|U|`.
-/

open scoped BigOperators

namespace SetFamilyBounds

/-- Number of indexed sets which contain `x`. -/
noncomputable def multiplicity {α ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (x : α) : ℕ := by
  classical
  exact (I.filter fun i ↦ x ∈ S i).card

theorem sum_card_eq_sum_multiplicity
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α)
    (hsub : ∀ i ∈ I, S i ⊆ U) :
    (∑ i ∈ I, (S i).card) = ∑ x ∈ U, multiplicity I S x := by
  classical
  calc
    (∑ i ∈ I, (S i).card) =
        ∑ i ∈ I, ∑ x ∈ U, if x ∈ S i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hfilter : U.filter (fun x ↦ x ∈ S i) = S i := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · exact fun hx ↦ ⟨hsub i hi hx, hx⟩
      calc
        (S i).card = (U.filter fun x ↦ x ∈ S i).card :=
          congrArg Finset.card hfilter.symm
        _ = ∑ x ∈ U, if x ∈ S i then 1 else 0 := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ U, ∑ i ∈ I, if x ∈ S i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ U, multiplicity I S x := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold multiplicity
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hxi : x ∈ S i <;> simp [hxi]

private theorem multiplicity_mul_pred_eq_double_sum
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (x : α) :
    multiplicity I S x * (multiplicity I S x - 1) =
      ∑ i ∈ I, ∑ j ∈ I,
        if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
  classical
  let J := I.filter fun i ↦ x ∈ S i
  let K := (I ×ˢ I).filter fun p ↦ p.1 ≠ p.2 ∧ x ∈ S p.1 ∧ x ∈ S p.2
  have hJK : J.offDiag = K := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product, J, K]
    tauto
  have hright :
      (∑ i ∈ I, ∑ j ∈ I,
        if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0) = K.card := by
    calc
      (∑ i ∈ I, ∑ j ∈ I,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0) =
          ∑ p ∈ I ×ˢ I,
            if p.1 ≠ p.2 ∧ x ∈ S p.1 ∧ x ∈ S p.2 then 1 else 0 := by
        symm
        exact Finset.sum_product I I _
      _ = K.card := by
        symm
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hright, ← hJK]
  rw [show multiplicity I S x = J.card by
    unfold multiplicity
    dsimp only [J]
    congr 1
    ext i
    simp]
  change J.card * (J.card - 1) = J.offDiag.card
  rw [Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib]
  simp

theorem sum_multiplicity_mul_pred_le
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α) (B : ℕ)
    (hoverlap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((S i).filter fun x ↦ x ∈ S j).card ≤ B) :
    (∑ x ∈ U, multiplicity I S x * (multiplicity I S x - 1)) ≤
      B * I.card * (I.card - 1) := by
  classical
  calc
    (∑ x ∈ U, multiplicity I S x * (multiplicity I S x - 1)) =
        ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact multiplicity_mul_pred_eq_double_sum I S x
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, if i ≠ j then B else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ne_eq, not_false_eq_true, if_true]
        have hfilter :
            (U.filter fun x ↦ x ∈ S i ∧ x ∈ S j).card ≤
              ((S i).filter fun x ↦ x ∈ S j).card := by
          apply Finset.card_le_card
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx'.2.1, hx'.2.2⟩
        have hsimple :
            (∑ x ∈ U, if x ∈ S i ∧ x ∈ S j then 1 else 0) ≤ B := by
          calc
          (∑ x ∈ U, if x ∈ S i ∧ x ∈ S j then 1 else 0) =
              (U.filter fun x ↦ x ∈ S i ∧ x ∈ S j).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          _ ≤ ((S i).filter fun x ↦ x ∈ S j).card := hfilter
          _ ≤ B := hoverlap i hi j hj hij
        simpa [hij] using hsimple
    _ = B * I.card * (I.card - 1) := by
      calc
        (∑ i ∈ I, ∑ j ∈ I, if i ≠ j then B else 0) =
            ∑ i ∈ I, B * (I.card - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfilter : I.filter (fun j ↦ i ≠ j) = I.erase i := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_erase]
            tauto
          calc
            (∑ j ∈ I, if i ≠ j then B else 0) =
                ∑ j ∈ I.filter (fun j ↦ i ≠ j), B := by
              rw [Finset.sum_filter]
            _ = ∑ _j ∈ I.erase i, B := by rw [hfilter]
            _ = B * (I.card - 1) := by
              simp [Finset.card_erase_of_mem hi, Nat.mul_comm]
        _ = B * I.card * (I.card - 1) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ac_rfl

/-- Guth's many-large-sets lemma, in a denominator-free form. -/
theorem large_family_bound
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α)
    (A B : ℕ)
    (hsub : ∀ i ∈ I, S i ⊆ U)
    (hlarge : ∀ i ∈ I, A ≤ (S i).card)
    (hoverlap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((S i).filter fun x ↦ x ∈ S j).card ≤ B)
    (hquadratic : 4 * B * U.card < A ^ 2) :
    A * I.card ≤ 2 * U.card := by
  classical
  let k : α → ℕ := multiplicity I S
  let E : ℕ := ∑ x ∈ U, k x
  have hAE : A * I.card ≤ E := by
    rw [show E = ∑ i ∈ I, (S i).card by
      symm
      exact sum_card_eq_sum_multiplicity U I S hsub]
    calc
      A * I.card = ∑ _i ∈ I, A := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ I, (S i).card :=
        Finset.sum_le_sum fun i hi ↦ hlarge i hi
  by_contra hbound
  have htwoU : 2 * U.card < A * I.card := by omega
  have htwoUE : 2 * U.card < E := htwoU.trans_le hAE
  have hcs : (E : ℝ) ^ 2 ≤
      (U.card : ℝ) * ∑ x ∈ U, (k x : ℝ) ^ 2 := by
    simpa [E] using
      (sq_sum_le_card_mul_sum_sq (s := U) (f := fun x ↦ (k x : ℝ)))
  have hover := sum_multiplicity_mul_pred_le U I S B hoverlap
  have hsumSq : (∑ x ∈ U, (k x : ℝ) ^ 2) ≤
      (E : ℝ) + (B : ℝ) * I.card * I.card := by
    have hident : ∀ x, (k x : ℝ) ^ 2 =
        (k x : ℝ) + (k x * (k x - 1) : ℕ) := by
      intro x
      have hnat : ∀ n : ℕ, n ^ 2 = n + n * (n - 1) := by
        intro n
        cases n with
        | zero => simp
        | succ n => simp [Nat.succ_eq_add_one]; ring
      exact_mod_cast hnat (k x)
    have hover' :
        (∑ x ∈ U, k x * (k x - 1)) ≤ B * I.card * I.card := by
      exact hover.trans <| Nat.mul_le_mul_left (B * I.card) (Nat.sub_le I.card 1)
    calc
      (∑ x ∈ U, (k x : ℝ) ^ 2) =
          ∑ x ∈ U, ((k x : ℝ) + (k x * (k x - 1) : ℕ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hident x
      _ = E + (∑ x ∈ U, k x * (k x - 1) : ℕ) := by
        dsimp [E]
        push_cast
        rw [Finset.sum_add_distrib]
      _ ≤ (E : ℝ) + (B : ℝ) * I.card * I.card := by
        exact_mod_cast Nat.add_le_add_left hover' E
  have hEpos : 0 < (E : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt htwoUE)
  have htwoUER : (2 : ℝ) * U.card < E := by exact_mod_cast htwoUE
  have hU_lt_halfE : (U.card : ℝ) < E / 2 := by
    nlinarith
  have hmain : (E : ℝ) ^ 2 <
      (E : ℝ) ^ 2 / 2 + (U.card : ℝ) * B * I.card ^ 2 := by
    calc
      (E : ℝ) ^ 2 ≤ (U.card : ℝ) * ∑ x ∈ U, (k x : ℝ) ^ 2 := hcs
      _ ≤ (U.card : ℝ) *
          ((E : ℝ) + (B : ℝ) * I.card * I.card) := by gcongr
      _ = (U.card : ℝ) * E + (U.card : ℝ) * B * I.card ^ 2 := by ring
      _ < (E : ℝ) ^ 2 / 2 + (U.card : ℝ) * B * I.card ^ 2 := by
        nlinarith
  have hAI : (A : ℝ) * I.card ≤ E := by exact_mod_cast hAE
  have hquadR : 4 * (B : ℝ) * U.card < (A : ℝ) ^ 2 := by
    exact_mod_cast hquadratic
  have hIz : 0 < (I.card : ℝ) := by
    have hIcard : 0 < I.card := by
      by_contra hI
      have hIz : I.card = 0 := Nat.eq_zero_of_not_pos hI
      simp [hIz] at hbound
    exact_mod_cast hIcard
  have hAI_sq : ((A : ℝ) * I.card) ^ 2 ≤ (E : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hAI
  have hquadMul :
      4 * (B : ℝ) * U.card * (I.card : ℝ) ^ 2 <
        ((A : ℝ) * I.card) ^ 2 := by
    calc
      4 * (B : ℝ) * U.card * (I.card : ℝ) ^ 2 <
          (A : ℝ) ^ 2 * (I.card : ℝ) ^ 2 := by
        exact mul_lt_mul_of_pos_right hquadR (sq_pos_of_pos hIz)
      _ = ((A : ℝ) * I.card) ^ 2 := by ring
  nlinarith

end SetFamilyBounds

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/Algebraic.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Algebraic lemmas for Erdős Problem 95

This file contains the elementary algebraic input to the polynomial-partitioning
argument: a polynomial restricted to an affine line has degree at most the
total degree of the original polynomial, and therefore a line not contained in
the zero set has at most that many intersections with it.
-/

open scoped BigOperators

namespace Algebraic

/-- Restriction of a multivariate polynomial to the affine line `x + t • v`. -/
noncomputable def lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) p

theorem eval_lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) (t : ℝ) :
    (lineRestriction p x v).eval t =
      MvPolynomial.eval (fun i => x i + t * v i) p := by
  change Polynomial.evalRingHom t
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) p) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    change Polynomial.eval t (Polynomial.C r) = r
    exact Polynomial.eval_C
  · funext i
    change Polynomial.eval t
      (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) = _
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C]
  · rfl

private theorem natDegree_linear {ι : Type*} (x v : ι → ℝ) (i : ι) :
    (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp only [Polynomial.natDegree_C]
    omega
  · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- Substitution of affine-linear polynomials does not increase total degree. -/
theorem natDegree_lineRestriction {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    (lineRestriction p x v).natDegree ≤ p.totalDegree := by
  rw [lineRestriction]
  conv_lhs => rw [p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  have hprod :
      (d.prod fun i k =>
        (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ k).natDegree ≤
        d.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    exact (Polynomial.natDegree_prod_le d.support _).trans <| by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_pow_le.trans <| by
        simpa using Nat.mul_le_mul_left (d i) (natDegree_linear x v i)
  calc
    _ ≤ (Polynomial.C (MvPolynomial.coeff d p)).natDegree +
        (d.prod fun i k =>
          (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d.sum fun _ k => k := add_le_add (by simp) hprod
    _ = d.sum fun _ k => k := Nat.zero_add _
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- A finite collection of distinct parameters at which a nonzero line
restriction vanishes has cardinality at most the total degree. -/
theorem card_line_zeros_le_totalDegree {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) (S : Finset ℝ)
    (hp : lineRestriction p x v ≠ 0)
    (hS : ∀ t ∈ S, MvPolynomial.eval (fun i => x i + t * v i) p = 0) :
    S.card ≤ p.totalDegree := by
  have hsub : S ⊆ (lineRestriction p x v).roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot,
      eval_lineRestriction]
    exact hS t ht
  calc
    S.card ≤ (lineRestriction p x v).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (lineRestriction p x v).roots.card := Multiset.toFinset_card_le _
    _ ≤ (lineRestriction p x v).natDegree := Polynomial.card_roots' _
    _ ≤ p.totalDegree := natDegree_lineRestriction p x v

/-- An affine line is contained in a polynomial zero set exactly when the
univariate restriction of the polynomial to that line is zero. -/
def LineContained {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) : Prop :=
  lineRestriction p x v = 0

theorem lineContained_iff {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    LineContained p x v ↔
      ∀ t : ℝ, MvPolynomial.eval (fun i ↦ x i + t * v i) p = 0 := by
  constructor
  · intro h t
    unfold LineContained at h
    have ht := congrArg (fun q : Polynomial ℝ ↦ q.eval t) h
    simpa only [eval_lineRestriction, Polynomial.eval_zero] using ht
  · intro h
    unfold LineContained
    apply Polynomial.funext
    intro t
    simpa only [eval_lineRestriction, Polynomial.eval_zero] using h t

theorem lineRestriction_mul {ι : Type*} [Fintype ι]
    (p q : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    lineRestriction (p * q) x v = lineRestriction p x v * lineRestriction q x v := by
  exact map_mul _ p q

/-! ## Low-degree interpolation in three variables -/

/-- Coefficient indices for the box of monomials whose three individual
degrees are at most `k`. -/
abbrev CoeffIndex (k : ℕ) := Fin 3 → Fin (k + 1)

noncomputable def exponent {k : ℕ} (e : CoeffIndex k) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

theorem exponent_injective {k : ℕ} : Function.Injective (@exponent k) := by
  intro e f h
  funext i
  apply Fin.ext
  have hi := congrArg (fun d : Fin 3 →₀ ℕ => d i) h
  simpa [exponent] using hi

noncomputable def boxMonomial {k : ℕ} (e : CoeffIndex k) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.monomial (exponent e) 1

theorem boxMonomial_linearIndependent (k : ℕ) :
    LinearIndependent ℝ (@boxMonomial k) := by
  change LinearIndependent ℝ
    (fun e : CoeffIndex k => MvPolynomial.monomial (exponent e) 1)
  exact (MvPolynomial.basisMonomials (Fin 3) ℝ).linearIndependent.comp
    (@exponent k) exponent_injective

noncomputable def polynomialOfCoefficients (k : ℕ) :
    (CoeffIndex k → ℝ) →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  Fintype.linearCombination ℝ (@boxMonomial k)

theorem polynomialOfCoefficients_injective (k : ℕ) :
    Function.Injective (polynomialOfCoefficients k) :=
  (boxMonomial_linearIndependent k).fintypeLinearCombination_injective

theorem totalDegree_boxMonomial_le (k : ℕ) (e : CoeffIndex k) :
    (boxMonomial e).totalDegree ≤ 3 * k := by
  rw [boxMonomial, MvPolynomial.totalDegree_monomial _ one_ne_zero]
  rw [Finsupp.sum_fintype (exponent e) (fun _ n => n) (fun _ => rfl)]
  calc
    ∑ i, exponent e i ≤ ∑ _i : Fin 3, k := by
      apply Finset.sum_le_sum
      intro i hi
      change (e i).val ≤ k
      omega
    _ = 3 * k := by simp

theorem totalDegree_polynomialOfCoefficients_le
    (k : ℕ) (c : CoeffIndex k → ℝ) :
    (polynomialOfCoefficients k c).totalDegree ≤ 3 * k := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (totalDegree_boxMonomial_le k e)

end Algebraic

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/External/Chapter39.lean` -/

section
/-
This file incorporates the finite sign-vector and Ky Fan infrastructure from
`xiangyazi24/proof_in_the_book` (commit `8ccc127c6c0109fa30ac61541420101376b24482`),
with small compatibility repairs for Lean/Mathlib v4.33.0.
-/

/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and formalizes Matoušek's finite reduction from a too-small Kneser
coloring to a Tucker-labeling counterexample.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The remaining upstream gap is now the finite Ky Fan boundary-parity count,
formalized in two equivalent ways: `KyFanPrefixParityStatement` says that the
positive-first alternating signed-permutation prefix chains are odd, while
`KyFanPrefixModFourStatement` says that both orientations together have
cardinality `2 mod 4`.  This file proves the Matoušek construction from a
hypothetical `(n - 2*k + 1)`-coloring of `KG(n,k)` to a Tucker counterexample,
proves low-dimensional Tucker cases, packages them into an unconditional
low-dimensional Lovász theorem, proves the one-dimensional Ky Fan prefix-parity
count and the vacuous two-dimensional Ky Fan prefix-parity case, and proves
either Ky Fan parity frontier implies
`TuckerLemmaStatement → chapter39`.
-/

namespace ProofsInTheBook.Chapter39

/-- Vertices of the Kneser graph `KG(n,k)`: the `k`-subsets of `[n]`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance (n k : ℕ) : Fintype (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

instance (n k : ℕ) : DecidableEq (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

/-- The Kneser graph: vertices are `k`-subsets, adjacent when disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj a b := a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

/-- Kneser adjacency is irreflexive: no vertex is adjacent to itself. -/
@[simp]
theorem kneserGraph_not_adj_self {n k : ℕ} (a : KneserVertex n k) :
    ¬ (kneserGraph n k).Adj a a := by
  intro h
  exact h.1 rfl

/--
The minimum element of a k-subset (well-defined since k ≥ 1).
-/
noncomputable def KneserVertex.min' {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : Fin n :=
  S.1.min' (by rw [Finset.nonempty_iff_ne_empty]; intro h; have := S.2; simp [h] at this; omega)

/--
The Kneser coloring by minimum element: color each k-subset by its minimum
when that minimum is ≤ n-2k, otherwise assign the default color n-2k+1.
-/
noncomputable def kneserColorNat {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : ℕ :=
  let m := (KneserVertex.min' hk S).val
  if m ≤ n - 2 * k then m else n - 2 * k + 1

theorem kneserColorNat_lt {n k : ℕ} (_hk : 1 ≤ k) (_h2k : 2 * k ≤ n)
    (S : KneserVertex n k) : kneserColorNat _hk S < n - 2 * k + 2 := by
  unfold kneserColorNat
  simp only
  by_cases h : (KneserVertex.min' _hk S).val ≤ n - 2 * k
  · simp [h]
    omega
  · simp [h]

noncomputable def kneserColor {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    KneserVertex n k → Fin (n - 2 * k + 2) :=
  fun S => ⟨kneserColorNat hk S, kneserColorNat_lt hk h2k S⟩

private theorem kneserColor_proper {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (a b : KneserVertex n k) (hadj : (kneserGraph n k).Adj a b) :
    kneserColor hk hn a ≠ kneserColor hk hn b := by
  intro heq
  have hdisj : Disjoint a.1 b.1 := hadj.2
  have hma_mem : KneserVertex.min' hk a ∈ a.1 := Finset.min'_mem _ _
  have hmb_mem : KneserVertex.min' hk b ∈ b.1 := Finset.min'_mem _ _
  have hne_min : (KneserVertex.min' hk a).val ≠ (KneserVertex.min' hk b).val := by
    intro h
    exact Finset.disjoint_left.mp hdisj hma_mem (by rwa [Fin.ext_iff.mpr h])
  simp only [kneserColor, Fin.mk.injEq] at heq
  unfold kneserColorNat at heq
  by_cases ha : (KneserVertex.min' hk a).val ≤ n - 2 * k <;>
    by_cases hb : (KneserVertex.min' hk b).val ≤ n - 2 * k <;>
    simp only [ha, hb, ite_true, ite_false] at heq
  · exact hne_min heq
  · omega
  · omega
  · have ha_neg := ha; have hb_neg := hb
    have ha_sub : ∀ x ∈ (↑a : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact ha_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hb_sub : ∀ x ∈ (↑b : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact hb_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hcard_union : ((↑a : Finset (Fin n)) ∪ ↑b).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj]
      have := a.2; have := b.2; omega
    have hsub : (↑a : Finset (Fin n)) ∪ ↑b ⊆ Finset.univ.filter fun i : Fin n => n - 2 * k < i.val := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rcases Finset.mem_union.mp hx with h | h
        · exact ha_sub x h
        · exact hb_sub x h⟩
    have hle := Finset.card_le_card hsub
    have hfilt_le : (Finset.univ.filter fun i : Fin n => n - 2 * k < i.val).card +
        (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card = n := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => n - 2 * k < i.val)
      simp at this; omega
    have hlow : (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card ≥ n - 2 * k + 1 := by
      have : ∀ j : Fin (n - 2 * k + 1), (⟨j.val, by omega⟩ : Fin n) ∈
          Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k := by
        intro j; simp; omega
      calc _ ≥ Fintype.card (Fin (n - 2 * k + 1)) := by
            exact Finset.card_le_card_of_injOn (fun j => ⟨j.val, by omega⟩)
              (fun j _ => this j) (fun a _ b _ h => by simp [Fin.ext_iff] at h; exact Fin.ext h)
        _ = n - 2 * k + 1 := Fintype.card_fin _
    omega

theorem kneser_chromatic_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  ⟨kneserColor hk hn, kneserColor_proper hk hn⟩

/-! ### Tucker-lemma route for the hard lower bound -/

/-- A sign vector in `{−1,0,1}^n`, represented by its positive and negative supports. -/
structure SignedSubset (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  disjoint : Disjoint pos neg

namespace SignedSubset

/-- Antipodal sign vector: swap positive and negative supports. -/
def antipode {n : ℕ} (X : SignedSubset n) : SignedSubset n where
  pos := X.neg
  neg := X.pos
  disjoint := X.disjoint.symm

/-- The sign vector is not the origin. -/
def Nonzero {n : ℕ} (X : SignedSubset n) : Prop :=
  X.pos.Nonempty ∨ X.neg.Nonempty

theorem antipode_nonzero {n : ℕ} (X : SignedSubset n) :
    X.antipode.Nonzero ↔ X.Nonzero := by
  simp [Nonzero, antipode, or_comm]

/-- Total support size of a sign vector. -/
def card {n : ℕ} (X : SignedSubset n) : ℕ :=
  X.pos.card + X.neg.card

theorem card_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.card = X.card := by
  simp [card, antipode, Nat.add_comm]

theorem card_pos_of_nonzero {n : ℕ} {X : SignedSubset n} (hX : X.Nonzero) :
    0 < X.card := by
  rcases hX with hpos | hneg
  · simp [card, Finset.card_pos.2 hpos]
  · simp [card, Finset.card_pos.2 hneg]

/-- The unsigned support of a sign vector. -/
def support {n : ℕ} (X : SignedSubset n) : Finset (Fin n) :=
  X.pos ∪ X.neg

theorem support_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.support = X.support := by
  ext i
  simp [support, antipode, or_comm]

theorem support_nonempty_iff_nonzero {n : ℕ} (X : SignedSubset n) :
    X.support.Nonempty ↔ X.Nonzero := by
  simp [support, Nonzero]

/-- The largest coordinate in the support of a nonzero sign vector. -/
noncomputable def maxSupport {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Fin n :=
  X.support.max' ((support_nonempty_iff_nonzero X).mpr hX)

theorem maxSupport_mem_support {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.maxSupport hX ∈ X.support := by
  exact Finset.max'_mem _ _

theorem maxSupport_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupport h₁ = X.maxSupport h₂ := by
  unfold maxSupport
  congr

theorem maxSupport_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupport ((antipode_nonzero X).mpr hX) = X.maxSupport hX := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.antipode.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'

/-- The sign of the largest supported coordinate, used in Matoušek's small-support labels. -/
noncomputable def maxSupportPositive {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Bool :=
  decide (X.maxSupport hX ∈ X.pos)

theorem maxSupportPositive_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupportPositive h₁ = X.maxSupportPositive h₂ := by
  unfold maxSupportPositive
  rw [maxSupport_congr_proof X h₁ h₂]

theorem maxSupportPositive_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupportPositive ((antipode_nonzero X).mpr hX) =
      !(X.maxSupportPositive hX) := by
  unfold maxSupportPositive
  rw [maxSupport_antipode]
  change decide (X.maxSupport hX ∈ X.neg) = !decide (X.maxSupport hX ∈ X.pos)
  by_cases hpos : X.maxSupport hX ∈ X.pos
  · have hnotneg : X.maxSupport hX ∉ X.neg := by
      intro hneg
      exact (Finset.disjoint_left.mp X.disjoint) hpos hneg
    simp [hpos, hnotneg]
  · have hneg : X.maxSupport hX ∈ X.neg := by
      have hmem := X.maxSupport_mem_support hX
      exact (Finset.mem_union.mp hmem).resolve_left hpos
    simp [hpos, hneg]

/-- The face order on the cross-polytope boundary, by support inclusion. -/
def Le {n : ℕ} (X Y : SignedSubset n) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

/-- Select the positive or negative support of a sign vector. -/
def side {n : ℕ} (X : SignedSubset n) (positive : Bool) : Finset (Fin n) :=
  if positive then X.pos else X.neg

@[simp]
theorem side_true {n : ℕ} (X : SignedSubset n) : X.side true = X.pos := by
  simp [side]

@[simp]
theorem side_false {n : ℕ} (X : SignedSubset n) : X.side false = X.neg := by
  simp [side]

theorem side_antipode_not {n : ℕ} (X : SignedSubset n) (positive : Bool) :
    X.antipode.side (!positive) = X.side positive := by
  cases positive <;> simp [side, antipode]

theorem side_disjoint_of_le_not {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (positive : Bool) :
    Disjoint (X.side positive) (Y.side (!positive)) := by
  cases positive
  · simp [side]
    exact Disjoint.mono hXY.2 (fun _ h => h) Y.disjoint.symm
  · simp [side]
    exact Disjoint.mono hXY.1 (fun _ h => h) Y.disjoint

theorem eq_of_le_card_eq {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hcard : X.card = Y.card) : X = Y := by
  have hpos_le : X.pos.card ≤ Y.pos.card := Finset.card_le_card hXY.1
  have hneg_le : X.neg.card ≤ Y.neg.card := Finset.card_le_card hXY.2
  have hsum : X.pos.card + X.neg.card = Y.pos.card + Y.neg.card := by
    simpa [card] using hcard
  have hpos_ge : Y.pos.card ≤ X.pos.card := by omega
  have hneg_ge : Y.neg.card ≤ X.neg.card := by omega
  have hpos_eq : X.pos = Y.pos := Finset.eq_of_subset_of_card_le hXY.1 hpos_ge
  have hneg_eq : X.neg = Y.neg := Finset.eq_of_subset_of_card_le hXY.2 hneg_ge
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos_eq hneg_eq
          subst ypos
          subst yneg
          simp

end SignedSubset

/-- Nonzero sign vectors, i.e. vertices/faces of the deleted origin sign complex. -/
abbrev NonzeroSignedSubset (n : ℕ) :=
  {X : SignedSubset n // X.Nonzero}

namespace NonzeroSignedSubset

/-- Antipodal map on nonzero sign vectors. -/
def antipode {n : ℕ} (X : NonzeroSignedSubset n) : NonzeroSignedSubset n :=
  ⟨X.1.antipode, (SignedSubset.antipode_nonzero X.1).mpr X.2⟩

end NonzeroSignedSubset

/-- A signed label `±i`, with `i : Fin m`. -/
structure SignedLabel (m : ℕ) where
  positive : Bool
  index : Fin m
  deriving DecidableEq, Repr

namespace SignedLabel

/-- Negating a signed label flips its sign and keeps its index. -/
def neg {m : ℕ} (L : SignedLabel m) : SignedLabel m where
  positive := !L.positive
  index := L.index

theorem ext {m : ℕ} {L M : SignedLabel m}
    (hpositive : L.positive = M.positive) (hindex : L.index = M.index) : L = M := by
  cases L
  cases M
  simp at hpositive hindex
  subst hpositive
  subst hindex
  rfl

end SignedLabel

/-- `k`-subsets contained in a fixed finite support. -/
abbrev KneserVertexIn (n k : ℕ) (support : Finset (Fin n)) : Type :=
  {A : KneserVertex n k // (A.1 : Finset (Fin n)) ⊆ support}

instance (n k : ℕ) (support : Finset (Fin n)) :
    Fintype (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

instance (n k : ℕ) (support : Finset (Fin n)) :
    DecidableEq (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

theorem KneserVertexIn.nonempty_of_le_card {n k : ℕ} {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    Nonempty (KneserVertexIn n k support) := by
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨⟨⟨A, hAcard⟩, hAsub⟩⟩

/-- The set of colors used on `k`-subsets contained in a support. -/
noncomputable def colorsInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) : Finset (Fin q) :=
  Finset.univ.image fun A : KneserVertexIn n k support => C A.1

theorem colorsInSupport_nonempty {n k q : ℕ} (C : KneserVertex n k → Fin q)
    {support : Finset (Fin n)} (hcard : k ≤ support.card) :
    (colorsInSupport C support).Nonempty := by
  classical
  obtain ⟨A⟩ := KneserVertexIn.nonempty_of_le_card (n := n) (k := k) hcard
  exact ⟨C A.1, by simp [colorsInSupport]⟩

/-- The minimum color appearing on a `k`-subset contained in `support`. -/
noncomputable def minColorInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) (hcard : k ≤ support.card) : Fin q :=
  (colorsInSupport C support).min' (colorsInSupport_nonempty C hcard)

theorem exists_kneserVertexIn_color_eq_minColorInSupport {n k q : ℕ}
    (C : KneserVertex n k → Fin q) {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    ∃ A : KneserVertexIn n k support, C A.1 = minColorInSupport C support hcard := by
  classical
  have hmem :
      minColorInSupport C support hcard ∈ colorsInSupport C support :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨A, _hA, hAeq⟩
  exact ⟨A, hAeq⟩

@[simp]
theorem minColorInSupport_congr_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (support : Finset (Fin n))
    (h₁ h₂ : k ≤ support.card) :
    minColorInSupport C support h₁ = minColorInSupport C support h₂ := by
  unfold minColorInSupport
  congr

/--
Key finite step in Matoušek's Tucker reduction: if two disjoint supports both
contain a `k`-subset, then a proper Kneser coloring gives different minimum
colors on the two supports.
-/
theorem minColorInSupport_ne_of_disjoint {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by
  classical
  obtain ⟨A, hAcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hleft
  obtain ⟨B, hBcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hright
  have hABdisj : Disjoint (A.1.1 : Finset (Fin n)) (B.1.1 : Finset (Fin n)) :=
    Disjoint.mono A.2 B.2 hdisj
  have hABne : A.1 ≠ B.1 := by
    intro h
    have hself : Disjoint (A.1.1 : Finset (Fin n)) (A.1.1 : Finset (Fin n)) := by
      simpa [h] using hABdisj
    have hempty : (A.1.1 : Finset (Fin n)) = ∅ := by
      exact (Finset.disjoint_self_iff_empty _).mp hself
    have hzero : (A.1.1 : Finset (Fin n)).card = 0 := by simp [hempty]
    have hAcard : (A.1.1 : Finset (Fin n)).card = k := A.1.2
    omega
  intro hmin
  exact hC A.1 B.1 ⟨hABne, hABdisj⟩ (hAcolor.trans (hmin.trans hBcolor.symm))

/--
Small-support part of Matoušek's labeling: a nonzero sign vector with total
support at most `2k - 2` receives label index `|X| - 1`.
-/
def matousekSmallSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    Fin (n - 1) :=
  ⟨X.card - 1, by
    have hpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
    omega⟩

/-- Full small-support signed label in Matoušek's construction. -/
noncomputable def matousekSmallSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    SignedLabel (n - 1) where
  positive := X.maxSupportPositive hX
  index := matousekSmallSupportIndex hk hn X hX hsmall

theorem matousekSmallSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall) =
      (matousekSmallSupportLabel hk hn X hX hsmall).neg := by
  change SignedLabel.mk
      (X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX))
      (matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall)) =
    SignedLabel.mk (!(X.maxSupportPositive hX)) (matousekSmallSupportIndex hk hn X hX hsmall)
  have hpositive :
      X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX) =
        !(X.maxSupportPositive hX) :=
    SignedSubset.maxSupportPositive_antipode X hX
  have hindex :
      matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
          (by simpa [SignedSubset.card_antipode] using hsmall) =
        matousekSmallSupportIndex hk hn X hX hsmall := by
    apply Fin.ext
    simp [matousekSmallSupportIndex, SignedSubset.card_antipode]
  exact SignedLabel.ext hpositive hindex

theorem matousekSmallSupportIndex_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportIndex hk hn X hX₁ hsmall₁ =
      matousekSmallSupportIndex hk hn X hX₂ hsmall₂ := by
  apply Fin.ext
  simp [matousekSmallSupportIndex]

theorem matousekSmallSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X hX₁ hsmall₁ =
      matousekSmallSupportLabel hk hn X hX₂ hsmall₂ := by
  apply SignedLabel.ext
  · exact SignedSubset.maxSupportPositive_congr_proof X hX₁ hX₂
  · exact matousekSmallSupportIndex_congr_proof hk hn X hX₁ hX₂ hsmall₁ hsmall₂

theorem matousekSmallSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero)
    (hXsmall : X.card ≤ 2 * k - 2) (hYsmall : Y.card ≤ 2 * k - 2)
    (hXY : SignedSubset.Le X Y) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcard : X.card = Y.card := by
    simp [matousekSmallSupportIndex] at hindex_val
    omega
  have hXYeq : X = Y := SignedSubset.eq_of_le_card_eq hXY hcard
  subst Y
  have hpositive := congrArg SignedLabel.positive hcomp
  simp [matousekSmallSupportLabel, SignedLabel.neg] at hpositive

/--
Large-support color labels occupy the range `2k - 2, …, n - 2`, obtained by
adding the color value to the offset `2k - 2`.
-/
def matousekLargeSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (color : Fin (n - 2 * k + 1)) : Fin (n - 1) :=
  ⟨2 * k - 2 + color.val, by
    have hcolor := color.isLt
    omega⟩

/-- If a sign vector has support at least `2k - 1`, then one side has a `k`-subset. -/
theorem signedSubset_large_support_has_k_side {n k : ℕ} {X : SignedSubset n}
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ X.pos.card ∨ k ≤ X.neg.card := by
  by_contra h
  push Not at h
  simp [SignedSubset.card] at hlarge
  omega

theorem decide_lt_swap_eq_not {α : Type*} [LinearOrder α] [DecidableRel ((· < ·) : α → α → Prop)]
    {a b : α} (hne : a ≠ b) : decide (b < a) = !decide (a < b) := by
  by_cases hab : a < b
  · have hba : ¬ b < a := not_lt_of_ge hab.le
    simp [hab, hba]
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hne.symm
    simp [hab, hba]

/--
Large-support side choice in Matoušek's construction: use the side whose
contained `k`-subsets have smaller minimum color, breaking one-sided cases by
choosing the only side that contains a `k`-subset.
-/
noncomputable def matousekLargeSupportPositive {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (_hlarge : 2 * k - 1 ≤ X.card) : Bool :=
  if hpos : k ≤ X.pos.card then
    if hneg : k ≤ X.neg.card then
      decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg)
    else true
  else false

@[simp]
theorem matousekLargeSupportPositive_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X hlarge₁ =
      matousekLargeSupportPositive C X hlarge₂ := by
  rfl

theorem matousekLargeSupportPositive_card {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ (X.side (matousekLargeSupportPositive C X hlarge)).card := by
  unfold matousekLargeSupportPositive
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · by_cases hlt : minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg
      · simp [hpos, hneg, hlt]
      · simp [hpos, hneg, hlt]
    · simp [hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [hpos, hneg]

theorem matousekLargeSupportPositive_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      !(matousekLargeSupportPositive C X hlarge) := by
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · have hne :
          minColorInSupport C X.pos hpos ≠ minColorInSupport C X.neg hneg :=
        minColorInSupport_ne_of_disjoint hk C hC X.disjoint hpos hneg
      have hswap :
          decide (minColorInSupport C X.neg hneg < minColorInSupport C X.pos hpos) =
            !decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg) :=
        decide_lt_swap_eq_not hne
      simpa [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg] using hswap
    · simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]

/-- The minimum color on the selected large-support side. -/
noncomputable def matousekLargeSupportColor {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : Fin q :=
  minColorInSupport C (X.side (matousekLargeSupportPositive C X hlarge))
    (matousekLargeSupportPositive_card C X hlarge)

theorem matousekLargeSupportColor_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X hlarge₁ =
      matousekLargeSupportColor C X hlarge₂ := by
  simp [matousekLargeSupportColor]

theorem matousekLargeSupportColor_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      matousekLargeSupportColor C X hlarge := by
  have hpositive := matousekLargeSupportPositive_antipode hk C hC X hlarge
  simp [matousekLargeSupportColor, hpositive, SignedSubset.side_antipode_not]

/-- Full large-support signed label in Matoušek's construction. -/
noncomputable def matousekLargeSupportLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge : 2 * k - 1 ≤ X.card) : SignedLabel (n - 1) where
  positive := matousekLargeSupportPositive C X hlarge
  index := matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge)

theorem matousekLargeSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X hlarge₁ =
      matousekLargeSupportLabel hk hn C X hlarge₂ := by
  apply SignedLabel.ext
  · exact matousekLargeSupportPositive_congr_proof C X hlarge₁ hlarge₂
  · apply Fin.ext
    simp [matousekLargeSupportLabel, matousekLargeSupportIndex,
      matousekLargeSupportColor_congr_proof C X hlarge₁ hlarge₂]

theorem matousekLargeSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      (matousekLargeSupportLabel hk hn C X hlarge).neg := by
  change SignedLabel.mk
      (matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge))
      (matousekLargeSupportIndex hk hn
        (matousekLargeSupportColor C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge))) =
    SignedLabel.mk (!(matousekLargeSupportPositive C X hlarge))
      (matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge))
  have hpositive :
      matousekLargeSupportPositive C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge) =
        !(matousekLargeSupportPositive C X hlarge) :=
    matousekLargeSupportPositive_antipode hk C hC X hlarge
  have hindex :
      matousekLargeSupportIndex hk hn
          (matousekLargeSupportColor C X.antipode
            (by simpa [SignedSubset.card_antipode] using hlarge)) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge) := by
    rw [matousekLargeSupportColor_antipode hk C hC X hlarge]
  exact SignedLabel.ext hpositive hindex

theorem matousekLargeSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card) (hYlarge : 2 * k - 1 ≤ Y.card)
    (hXY : SignedSubset.Le X Y) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hpositive :
      matousekLargeSupportPositive C X hXlarge =
        !(matousekLargeSupportPositive C Y hYlarge) := by
    have := congrArg SignedLabel.positive hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hcolor : matousekLargeSupportColor C X hXlarge =
      matousekLargeSupportColor C Y hYlarge := by
    apply Fin.ext
    have hindex_val := congrArg Fin.val hindex
    simp [matousekLargeSupportIndex] at hindex_val
    omega
  have hdisj :
      Disjoint
        (X.side (matousekLargeSupportPositive C X hXlarge))
        (Y.side (matousekLargeSupportPositive C Y hYlarge)) := by
    cases hYpos : matousekLargeSupportPositive C Y hYlarge
    · have hXpos : matousekLargeSupportPositive C X hXlarge = true := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY true
    · have hXpos : matousekLargeSupportPositive C X hXlarge = false := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY false
  have hmin_ne :
      minColorInSupport C
          (X.side (matousekLargeSupportPositive C X hXlarge))
          (matousekLargeSupportPositive_card C X hXlarge) ≠
        minColorInSupport C
          (Y.side (matousekLargeSupportPositive C Y hYlarge))
          (matousekLargeSupportPositive_card C Y hYlarge) :=
    minColorInSupport_ne_of_disjoint hk C hC hdisj
      (matousekLargeSupportPositive_card C X hXlarge)
      (matousekLargeSupportPositive_card C Y hYlarge)
  exact hmin_ne (by simpa [matousekLargeSupportColor] using hcolor)

theorem matousekSmallSupportLabel_ne_neg_large {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hX : X.Nonzero) (hXsmall : X.card ≤ 2 * k - 2)
    (hYlarge : 2 * k - 1 ≤ Y.card) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hcolor := (matousekLargeSupportColor C Y hYlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega

theorem matousekLargeSupportLabel_ne_neg_small {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card)
    (hY : Y.Nonzero) (hYsmall : Y.card ≤ 2 * k - 2) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcolor := (matousekLargeSupportColor C X hXlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega

/-- Matoušek's sign-vector label produced by a hypothetical too-small coloring. -/
noncomputable def matousekTuckerLabel {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) :
    NonzeroSignedSubset n → SignedLabel (n - 1) :=
  fun X =>
    if hsmall : X.1.card ≤ 2 * k - 2 then
      matousekSmallSupportLabel hk hn X.1 X.2 hsmall
    else
      matousekLargeSupportLabel hk hn C X.1 (by omega)

theorem matousekTuckerLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : NonzeroSignedSubset n) :
    matousekTuckerLabel hk hn C X.antipode = (matousekTuckerLabel hk hn C X).neg := by
  unfold matousekTuckerLabel
  by_cases hsmall : X.1.card ≤ 2 * k - 2
  · have hsmall_ant : X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_pos hsmall, dif_pos hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekSmallSupportLabel_congr_proof hk hn X.1.antipode] using
      matousekSmallSupportLabel_antipode hk hn X.1 X.2 hsmall
  · have hlarge : 2 * k - 1 ≤ X.1.card := by omega
    have hsmall_ant : ¬ X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_neg hsmall, dif_neg hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekLargeSupportLabel_congr_proof hk hn C X.1,
      matousekLargeSupportLabel_congr_proof hk hn C X.1.antipode] using
      matousekLargeSupportLabel_antipode hk hn C hC X.1 hlarge

theorem matousekTuckerLabel_no_complementary {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X Y : NonzeroSignedSubset n) :
    SignedSubset.Le X.1 Y.1 →
      matousekTuckerLabel hk hn C X ≠ (matousekTuckerLabel hk hn C Y).neg := by
  intro hXY
  unfold matousekTuckerLabel
  by_cases hXsmall : X.1.card ≤ 2 * k - 2
  · by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall] using
        matousekSmallSupportLabel_ne_neg_of_le hk hn X.2 Y.2 hXsmall hYsmall hXY
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekSmallSupportLabel_ne_neg_large hk hn C X.2 hXsmall hYlarge
  · have hXlarge : 2 * k - 1 ≤ X.1.card := by omega
    by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1] using
        matousekLargeSupportLabel_ne_neg_small hk hn C hXlarge Y.2 hYsmall
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1,
        matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekLargeSupportLabel_ne_neg_of_le hk hn C hC hXlarge hYlarge hXY

/--
Tucker's lemma in the octahedral/sign-vector form needed for the Matoušek
proof of Lovász's theorem.  The remaining proof obligation is supplied by the
finer `KyFanPrefixParityStatement` below.
-/
def TuckerLemmaStatement (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, label X.antipode = (label X).neg) →
      ∃ X Y : NonzeroSignedSubset n,
        SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg

/-- A sign-vector labeling has no complementary comparable pair. -/
def NoComplementaryComparableLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Prop :=
  ∀ X Y : NonzeroSignedSubset n,
    SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

/--
A signed permutation, i.e. a maximal chain in the face lattice of the
cross-polytope boundary: reveal the coordinates in `order`, with the prescribed
sign at each coordinate.
-/
structure SignedPermutation (n : ℕ) where
  order : Equiv.Perm (Fin n)
  positive : Fin n → Bool
  deriving DecidableEq

def signedPermutationEquiv (n : ℕ) :
    SignedPermutation n ≃ Equiv.Perm (Fin n) × (Fin n → Bool) where
  toFun P := (P.order, P.positive)
  invFun data := { order := data.1, positive := data.2 }
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro data
    cases data
    rfl

noncomputable instance (n : ℕ) : Fintype (SignedPermutation n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n) × (Fin n → Bool)) (signedPermutationEquiv n).symm

namespace SignedPermutation

/-- Antipodal signed permutation: keep the order and flip every sign. -/
def antipode {n : ℕ} (P : SignedPermutation n) : SignedPermutation n where
  order := P.order
  positive := fun i => !P.positive i

/-- Positive coordinates in the `i`th prefix face of a signed permutation. -/
def prefixPos {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ P.positive (P.order.symm x)

/-- Negative coordinates in the `i`th prefix face of a signed permutation. -/
def prefixNeg {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ !P.positive (P.order.symm x)

theorem prefix_disjoint {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    Disjoint (P.prefixPos i) (P.prefixNeg i) := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  simp [prefixPos, prefixNeg] at hxpos hxneg
  cases h : P.positive (P.order.symm x) <;> simp [h] at hxpos hxneg

/-- The `i`th prefix face as a sign vector. -/
def prefixSignedSubset {n : ℕ} (P : SignedPermutation n) (i : Fin n) : SignedSubset n where
  pos := P.prefixPos i
  neg := P.prefixNeg i
  disjoint := P.prefix_disjoint i

theorem prefix_nonzero {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).Nonzero := by
  let x : Fin n := P.order i
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hsymm : P.order.symm x = i := by simp [x]
  have hle : P.order.symm x ≤ i := le_of_eq hsymm
  by_cases hpos : P.positive (P.order.symm x) = true
  · left
    exact ⟨x, by simp [prefixSignedSubset, prefixPos, hxuniv, hle, hpos]⟩
  · right
    exact ⟨x, by simp [prefixSignedSubset, prefixNeg, hxuniv, hle, hpos]⟩

/-- The maximal chain associated to a signed permutation. -/
def prefixChain {n : ℕ} (P : SignedPermutation n) (i : Fin n) : NonzeroSignedSubset n :=
  ⟨P.prefixSignedSubset i, P.prefix_nonzero i⟩

end SignedPermutation

/--
Positive-first alternating prefix labels: the absolute label indices strictly
increase, and the signs alternate `+,-,+,-,...` along the prefix chain.
-/
def PositiveAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = decide (Even i.val)

/-- Negative-first alternating prefix labels, the antipodal partner of the positive-first version. -/
def NegativeAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = !decide (Even i.val)

/-- Signed permutations whose prefix labels are positive-first alternating. -/
noncomputable def positiveAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => PositiveAlternatingPrefixLabels label P

/-- Signed permutations whose prefix labels are negative-first alternating. -/
noncomputable def negativeAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => NegativeAlternatingPrefixLabels label P

/-- Positive- or negative-first alternating prefix-label chains. -/
noncomputable def alternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  positiveAlternatingPrefixLabelChains label ∪ negativeAlternatingPrefixLabelChains label

/--
Equivalent mod-four form of the Ky Fan prefix-chain frontier: after both
orientations are counted, the number of alternating maximal chains is `2`
modulo `4`.
-/
def KyFanPrefixModFourStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ r, (alternatingPrefixLabelChains label).card = 4 * r + 2

/--
The exact finite parity statement still missing from Mathlib for this chapter:
under an antipodal labeling with no complementary comparable pair, the number
of positive-first alternating signed-permutation prefix chains is odd.  This is
the standard Ky Fan odd-count statement specialized to the cross-polytope
face-poset model.
-/
def KyFanPrefixParityStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (positiveAlternatingPrefixLabelChains label).card

/-! ### Endpoint-count form of the remaining Ky Fan parity frontier -/

/--
Packaged endpoint data for the Prescott-Su/Fan path proof.  The only
remaining combinatorial construction is to instantiate this structure for the
octahedral flag graph of a concrete Tucker labeling.
-/
structure PathEndpointDecomposition (Positive Negative : Type) [Fintype Positive]
    [Fintype Negative] where
  Path : Type
  Base : Type
  Endpoint : Path → Type
  instPath : Fintype Path
  instBase : Fintype Base
  instEndpoint : ∀ p : Path, Fintype (Endpoint p)
  pathAntipode : Path ≃ Path
  pathAntipode_involutive : Function.Involutive pathAntipode
  pathAntipode_fixedPointFree : ∀ p : Path, pathAntipode p ≠ p
  endpoint_card_two : ∀ p : Path, Fintype.card (Endpoint p) = 2
  classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative)
  base_card : Fintype.card Base = 2

/--
Matoušek's bridge from a too-small Kneser coloring to a Tucker counterexample:
given a proper `(n - 2*k + 1)`-coloring, construct an antipodal sign-vector
labeling with no complementary comparable pair.
-/
def KneserColoringProducesTuckerCounterexample (n k : ℕ) : Prop :=
  ∀ C : KneserVertex n k → Fin (n - 2 * k + 1),
    (∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) →
      ∃ label : NonzeroSignedSubset n → SignedLabel (n - 1),
        (∀ X, label X.antipode = (label X).neg) ∧
          ∀ X Y : NonzeroSignedSubset n,
            SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

theorem kneserColoringProducesTuckerCounterexample_of_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    KneserColoringProducesTuckerCounterexample n k := by
  intro C hC
  refine ⟨matousekTuckerLabel hk hn C, ?_, ?_⟩
  · intro X
    exact matousekTuckerLabel_antipode hk hn C hC X
  · intro X Y hXY
    exact matousekTuckerLabel_no_complementary hk hn C hC X Y hXY

/--
If Tucker's lemma and Matoušek's coloring-to-labeling bridge are available,
the hard Kneser lower bound follows immediately.
-/
theorem kneser_chromatic_lower_bound_from_tucker (n k : ℕ)
    (htucker : TuckerLemmaStatement n)
    (hbridge : KneserColoringProducesTuckerCounterexample n k) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  obtain ⟨label, hantipodal, hno_complementary⟩ := hbridge C hC
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker label hantipodal
  exact hno_complementary X Y hXY hcomp

theorem kneser_chromatic_lower_bound_from_tucker_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  kneser_chromatic_lower_bound_from_tucker n k htucker
    (kneserColoringProducesTuckerCounterexample_of_matousek n k hk hn)

/--
Chapter 39 (Lovász's theorem on Kneser graph chromatic number, conditional on
the discrete Tucker lemma): the upper bound is explicit, and the lower bound
is derived from Tucker's lemma via the formalized Matoušek labeling above.

Remaining gap to an unconditional theorem in Mathlib: prove
`TuckerLemmaStatement`.
-/
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n k hk hn
  · exact kneser_chromatic_lower_bound_from_tucker_matousek n k hk hn htucker

end ProofsInTheBook.Chapter39

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/External/Tucker.lean` -/

section
/-
This file incorporates the unconditional octahedral Tucker proof from
`xiangyazi24/proof_in_the_book` (commit `8ccc127c6c0109fa30ac61541420101376b24482`),
with small compatibility repairs for Lean/Mathlib v4.33.0.
-/

/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation

/-! ## Hemisphere and equator model -/

theorem signedSubset_ext_pos_neg {n : ℕ} {X Y : SignedSubset n}
    (hpos : X.pos = Y.pos) (hneg : X.neg = Y.neg) : X = Y := by
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

/-- The upper hemisphere `B⁺_{r+1}`: the last coordinate is not negative. -/
def UpperHemisphere {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.neg

/-- The equator of `B⁺_{r+1}`: the last coordinate is zero. -/
def Equator {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.pos ∧ Fin.last r ∉ X.1.neg

/-- Embed a sign vector on the first `r` coordinates into the equator of
`{−1,0,1}^{r+1}`. -/
def signedSubsetEquatorEmbed {r : ℕ} (X : SignedSubset r) : SignedSubset (r + 1) where
  pos := X.pos.image Fin.castSucc
  neg := X.neg.image Fin.castSucc
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hypos hyneg
    rcases Finset.mem_image.mp hypos with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hyneg with ⟨b, hbmem, hb⟩
    have hba : b = a := by
      apply Fin.ext
      simpa using congrArg Fin.val hb
    subst b
    exact (Finset.disjoint_left.mp X.disjoint) ha hbmem

/-- The equator embedding on nonzero sign vectors. -/
def equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) : NonzeroSignedSubset (r + 1) :=
  ⟨signedSubsetEquatorEmbed X.1, by
    rcases X.2 with hpos | hneg
    · rcases hpos with ⟨i, hi⟩
      left
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩
    · rcases hneg with ⟨i, hi⟩
      right
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩⟩

theorem equatorEmbed_mem_equator {r : ℕ} (X : NonzeroSignedSubset r) :
    Equator (equatorEmbed X) := by
  constructor
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega

/-- The predecessor of a non-last coordinate. -/
def finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) : Fin r :=
  ⟨i.val, by
    have hle : i.val ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hne : i.val ≠ r := by
      intro hval
      exact hi (Fin.ext hval)
    omega⟩

@[simp]
theorem castSucc_finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) :
    Fin.castSucc (finPredOfNotLast i hi) = i := by
  apply Fin.ext
  rfl

/-- Drop the last zero coordinate from an equatorial sign vector. -/
def equatorDropSignedSubset {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : SignedSubset r where
  pos := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.pos
  neg := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.neg
  disjoint := by
    rw [Finset.disjoint_left]
    intro i hip hin
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hip hin
    exact (Finset.disjoint_left.mp X.1.disjoint) hip hin

theorem equatorDrop_nonzero {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) : (equatorDropSignedSubset X).Nonzero := by
  rcases X.2 with hpos | hneg
  · rcases hpos with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.1 (by simpa [hlast] using hi)
    left
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩
  · rcases hneg with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.2 (by simpa [hlast] using hi)
    right
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩

/-- The inverse map from the equator back to `K_r`. -/
def equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1)) (hX : Equator X) :
    NonzeroSignedSubset r :=
  ⟨equatorDropSignedSubset X, equatorDrop_nonzero X hX⟩

theorem equatorDrop_equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorDrop (equatorEmbed X) (equatorEmbed_mem_equator X) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]

theorem equatorEmbed_equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) :
    equatorEmbed (equatorDrop X hX) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.1 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.2 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast

/-- The equator of the upper hemisphere in `K_{r+1}` is canonically `K_r`. -/
noncomputable def equatorEquiv (r : ℕ) :
    NonzeroSignedSubset r ≃ {X : NonzeroSignedSubset (r + 1) // Equator X} where
  toFun X := ⟨equatorEmbed X, equatorEmbed_mem_equator X⟩
  invFun X := equatorDrop X.1 X.2
  left_inv := by
    intro X
    exact equatorDrop_equatorEmbed X
  right_inv := by
    intro X
    cases X with
    | mk X hX =>
        apply Subtype.ext
        exact equatorEmbed_equatorDrop X hX

theorem equatorEmbed_le {r : ℕ} {X Y : NonzeroSignedSubset r}
    (hXY : SignedSubset.Le X.1 Y.1) :
    SignedSubset.Le (equatorEmbed X).1 (equatorEmbed Y).1 := by
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.1 hi, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.2 hi, rfl⟩

theorem signedSubsetEquatorEmbed_antipode {r : ℕ} (X : SignedSubset r) :
    signedSubsetEquatorEmbed X.antipode = (signedSubsetEquatorEmbed X).antipode := by
  apply signedSubset_ext_pos_neg
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]

theorem equatorEmbed_antipode {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorEmbed X.antipode = (equatorEmbed X).antipode := by
  apply Subtype.ext
  exact signedSubsetEquatorEmbed_antipode X.1

noncomputable def equatorRestrictedLabel {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    NonzeroSignedSubset d → SignedLabel d :=
  fun X => label ((equatorEquiv d) X).1

theorem equatorRestrictedLabel_antipodal {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabel label X.antipode =
      (equatorRestrictedLabel label X).neg := by
  intro X
  simpa [equatorRestrictedLabel, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabel_noComplementary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabel label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabel, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

/-! ## Label-set `A` ridges and the local sigma-degree count -/

/-- The alternating label `α_k = (-1)^k(k+1)` in zero-based `Fin d` notation. -/
def alternatingLabel (k : Fin d) : SignedLabel d where
  positive := decide (Even k.val)
  index := k

@[simp]
theorem alternatingLabel_index (k : Fin d) : (alternatingLabel k).index = k := rfl

@[simp]
theorem alternatingLabel_positive (k : Fin d) :
    (alternatingLabel k).positive = decide (Even k.val) := rfl

/-! ### Alternating labels along an arbitrary increasing index set -/

/-- The alternating label attached to the `a`th element of an index map.  The
sign alternates with the position `a`; the absolute label is `idx a`. -/
def alternatingLabelOf {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    SignedLabel m where
  positive := decide (Even a.val)
  index := idx a

@[simp]
theorem alternatingLabelOf_index {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).index = idx a := rfl

@[simp]
theorem alternatingLabelOf_positive {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).positive = decide (Even a.val) := rfl

theorem alternatingLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    alternatingLabelOf idx a = alternatingLabelOf idx b ↔ a = b := by
  constructor
  · intro h
    apply hidx
    simpa [alternatingLabelOf] using congrArg SignedLabel.index h
  · intro h
    subst h
    rfl

/-- The alternating label set determined by an index map. -/
noncomputable def alternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => alternatingLabelOf idx a

theorem alternatingLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingLabelSetOf idx).card = r := by
  classical
  rw [alternatingLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingLabelOf_inj hidx).mp h

/-- The negative-first alternating label set determined by an index map. -/
noncomputable def alternatingNegLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => (alternatingLabelOf idx a).neg

theorem alternatingNegLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    (alternatingLabelOf idx a).neg = (alternatingLabelOf idx b).neg ↔ a = b := by
  constructor
  · intro h
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  · intro h
    subst h
    rfl

theorem alternatingNegLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingNegLabelSetOf idx).card = r := by
  classical
  rw [alternatingNegLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingNegLabelOf_inj hidx).mp h

/-- The label set carried by an ordered simplex.  The property below does not
use the order except to enumerate the finitely many vertices. -/
noncomputable def simplexLabelSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin k => label (sigma a)

/-- Positive-first alternating simplex, with its index set read off from the
simplex itself.  The `idx` below is an internal witness, not an external
summation parameter. -/
def IsAltPos {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingLabelSetOf idx

/-- Negative-first alternating simplex, with the same self-contained indexing
convention as `IsAltPos`. -/
def IsAltNeg {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingNegLabelSetOf idx

noncomputable instance isAltPos_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltPos label sigma) := by
  classical
  unfold IsAltPos
  infer_instance

noncomputable instance isAltNeg_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltNeg label sigma) := by
  classical
  unfold IsAltNeg
  infer_instance

/-! ### Pure sign-sequence deletion parity -/

def signSeqAltPos {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = decide (Even i.val)

def signSeqAltNeg {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, s i = !decide (Even i.val)

def signSeqDoor {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  (∀ j : Fin (k + 1), j < i → s j = decide (Even j.val)) ∧
    (∀ j : Fin (k + 1), i < j → s j = !decide (Even j.val))

noncomputable def signSeqDoorSet {k : ℕ} (s : Fin (k + 1) → Bool) :
    Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter (signSeqDoor s)

noncomputable instance signSeqDoor_decidable {k : ℕ} (s : Fin (k + 1) → Bool) :
    DecidablePred (signSeqDoor s) := by
  classical
  exact inferInstance

def signSeqBad {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) : Prop :=
  s i = !decide (Even i.val)

theorem signSeq_not_bad_iff {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    ¬ signSeqBad s i ↔ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeq_bad_iff_not_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqBad s i ↔ ¬ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeqDoor_iff_bad_cut {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    signSeqDoor s i ↔
      (∀ j : Fin (k + 1), j < i → ¬ signSeqBad s j) ∧
        (∀ j : Fin (k + 1), i < j → signSeqBad s j) := by
  constructor
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mpr (h.1 j hji)
    · intro j hij
      exact h.2 j hij
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mp (h.1 j hji)
    · intro j hij
      exact h.2 j hij

theorem signSeq_not_even_succ_decide (a : ℕ) :
    (!decide (Even (a + 1))) = decide (Even a) := by
  by_cases ha : Even a <;> simp [ha, Nat.even_add_one]

theorem signSeqDoor_iff_remove_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a)) := by
  constructor
  · intro h a
    by_cases hlt : i.succAbove a < i
    · have hs := h.1 (i.succAbove a) hlt
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hlt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : (i.succAbove a).val = a.val := by
        rw [hsa]
        rfl
      simpa [hval] using hs
    · have hgt : i < i.succAbove a := by
        have hne : i ≠ i.succAbove a := Fin.ne_succAbove i a
        exact lt_of_le_of_ne (le_of_not_gt hlt) hne
      have hs := h.2 (i.succAbove a) hgt
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hgt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : (i.succAbove a).val = a.val + 1 := by
        rw [hsa]
        rfl
      change s (i.succAbove a) = decide (Even a.val)
      rw [hs, hval]
      exact signSeq_not_even_succ_decide a.val
  · intro h
    constructor
    · intro j hji
      have hne : j ≠ i := ne_of_lt hji
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_lt : i.succAbove a < i := by
        simpa [ha] using hji
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hsa_lt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : a.val = j.val := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      simpa [hval] using hs_j
    · intro j hij
      have hne : j ≠ i := ne_of_gt hij
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_gt : i < i.succAbove a := by
        simpa [ha] using hij
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hsa_gt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : j.val = a.val + 1 := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv.symm
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      rw [hs_j, hval]
      exact (signSeq_not_even_succ_decide a.val).symm

theorem signSeqDoor_nonadjacent_false {k : ℕ} {s : Fin (k + 1) → Bool}
    {i j : Fin (k + 1)} (hi : signSeqDoor s i) (hj : signSeqDoor s j)
    (_hij : i < j) :
    j.val ≤ i.val + 1 := by
  by_contra hle
  have hlt : i.val + 1 < j.val := by omega
  let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  have hit : i < t := by
    exact Fin.lt_iff_val_lt_val.mpr (by simp [t])
  have htj : t < j := by
    exact Fin.lt_iff_val_lt_val.mpr (by simpa [t] using hlt)
  have hbad : signSeqBad s t := (signSeqDoor_iff_bad_cut s i).mp hi |>.2 t hit
  have hnot : ¬ signSeqBad s t := (signSeqDoor_iff_bad_cut s j).mp hj |>.1 t htj
  exact hnot hbad

theorem signSeqDoorSet_card_le_two {k : ℕ} (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card ≤ 2 := by
  classical
  by_contra hle
  have htwo : 2 < (signSeqDoorSet s).card := by omega
  rcases Finset.two_lt_card.mp htwo with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have hdoor_a : signSeqDoor s a := by simpa [signSeqDoorSet] using ha
  have hdoor_b : signSeqDoor s b := by simpa [signSeqDoorSet] using hb
  have hdoor_c : signSeqDoor s c := by simpa [signSeqDoorSet] using hc
  have hcontr_pair :
      ∀ {x y : Fin (k + 1)}, signSeqDoor s x → signSeqDoor s y → x < y →
        x.val + 1 < y.val → False := by
    intro x y hx hy hxy hgap
    have hle' := signSeqDoor_nonadjacent_false hx hy hxy
    omega
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_trichotomy c a with hca | hcaeq | haclt
    · exact hcontr_pair hdoor_c hdoor_b (lt_trans hca hablt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hca
        have h2 := Fin.lt_iff_val_lt_val.mp hablt
        omega)
    · exact hac hcaeq.symm
    · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
      · exact hcontr_pair hdoor_a hdoor_b hablt (by
          have h1 := Fin.lt_iff_val_lt_val.mp haclt
          have h2 := Fin.lt_iff_val_lt_val.mp hcb
          omega)
      · exact hbc hcbeq.symm
      · exact hcontr_pair hdoor_a hdoor_c (lt_trans hablt hbclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hablt
          have h2 := Fin.lt_iff_val_lt_val.mp hbclt
          omega)
  · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
    · exact hcontr_pair hdoor_c hdoor_a (lt_trans hcb hbalt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hcb
        have h2 := Fin.lt_iff_val_lt_val.mp hbalt
        omega)
    · exact hbc hcbeq.symm
    · rcases lt_trichotomy c a with hca | hcaeq | haclt
      · exact hcontr_pair hdoor_b hdoor_a hbalt (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbclt
          have h2 := Fin.lt_iff_val_lt_val.mp hca
          omega)
      · exact hac hcaeq.symm
      · exact hcontr_pair hdoor_b hdoor_c (lt_trans hbalt haclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbalt
          have h2 := Fin.lt_iff_val_lt_val.mp haclt
          omega)

theorem signSeqDoor_next_of_not_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hnot : ¬ signSeqBad s i) (hik : i.val < k) :
    signSeqDoor s ⟨i.val + 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    have hjv : j.val < i.val + 1 := Fin.lt_iff_val_lt_val.mp hj
    by_cases hji : j < i
    · exact hi.1 j hji
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : i.val ≤ j.val := by
          exact le_of_not_gt (by
            intro hv
            exact hji (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hnot
  · intro j hj
    apply hi.2
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : i.val + 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
      omega)

theorem signSeqDoor_prev_of_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hbad : signSeqBad s i) (hi0 : 0 < i.val) :
    signSeqDoor s ⟨i.val - 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    apply hi.1
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : j.val < i.val - 1 := Fin.lt_iff_val_lt_val.mp hj
      omega)
  · intro j hj
    have hjv : i.val - 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
    by_cases hij : i < j
    · exact hi.2 j hij
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : j.val ≤ i.val := by
          exact le_of_not_gt (by
            intro hv
            exact hij (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hbad

theorem signSeqDoorSet_eq_singleton_last_of_altPos {k : ℕ}
    {s : Fin (k + 1) → Bool} (hpos : signSeqAltPos s) :
    signSeqDoorSet s = {Fin.last k} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hilast : i = Fin.last k
    · simp [hilast]
    · have hlt : i < Fin.last k := Fin.lt_last_iff_ne_last.mpr hilast
      have hsuf := hdoor.2 (Fin.last k) hlt
      have hposlast := hpos (Fin.last k)
      have hbad : decide (Even (Fin.last k).val) = !decide (Even (Fin.last k).val) :=
        hposlast.symm.trans hsuf
      cases decide (Even (Fin.last k).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (Fin.last k) := by
      constructor
      · intro j _hj
        exact hpos j
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.le_last j)) hj)
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDoorSet_eq_singleton_zero_of_altNeg {k : ℕ}
    {s : Fin (k + 1) → Bool} (hneg : signSeqAltNeg s) :
    signSeqDoorSet s = {0} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hlt : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have hpref := hdoor.1 0 hlt
      have hneg0 := hneg 0
      have hbad : decide (Even (0 : Fin (k + 1)).val) =
          !decide (Even (0 : Fin (k + 1)).val) :=
        hpref.symm.trans hneg0
      cases decide (Even (0 : Fin (k + 1)).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (0 : Fin (k + 1)) := by
      constructor
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
      · intro j _hj
        exact hneg j
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDeletionParity {k : ℕ} (s : Fin (k + 1) → Bool) :
    Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s := by
  classical
  constructor
  · intro hodd
    have hle := signSeqDoorSet_card_le_two s
    have hcard : (signSeqDoorSet s).card = 1 := by
      rcases hodd with ⟨a, ha⟩
      omega
    have hposcard : 0 < (signSeqDoorSet s).card := by omega
    obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp hposcard
    have hi : signSeqDoor s i := by simpa [signSeqDoorSet] using hi_mem
    by_cases hk0 : k = 0
    · subst k
      fin_cases i
      by_cases hs0 : s 0 = true
      · left
        intro j
        fin_cases j
        simpa [hs0]
      · right
        have hsfalse : s 0 = false := by
          cases h : s 0 <;> simp [h] at hs0 ⊢
        intro j
        fin_cases j
        simpa [hsfalse]
    · have hend : i = 0 ∨ i = Fin.last k := by
        by_contra hend
        push_neg at hend
        have hi0v : 0 < i.val := Fin.pos_iff_ne_zero.mpr hend.1
        have hikv : i.val < k := by
          have hilast : i ≠ Fin.last k := hend.2
          have hlelast : i ≤ Fin.last k := Fin.le_last i
          have hneval : i.val ≠ k := by
            intro hv
            exact hilast (Fin.ext (by simpa [Fin.last] using hv))
          have hleval : i.val ≤ k := Fin.le_iff_val_le_val.mp hlelast
          omega
        by_cases hbad : signSeqBad s i
        · let p : Fin (k + 1) := ⟨i.val - 1, by omega⟩
          have hp : signSeqDoor s p := signSeqDoor_prev_of_bad hi hbad hi0v
          have hp_mem : p ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hp
          have hp_ne : p ≠ i := by
            intro hpi
            have hv := congrArg Fin.val hpi
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hp_mem, i, hi_mem, hp_ne⟩
          omega
        · let q : Fin (k + 1) := ⟨i.val + 1, by omega⟩
          have hq : signSeqDoor s q := signSeqDoor_next_of_not_bad hi hbad hikv
          have hq_mem : q ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hq
          have hq_ne : q ≠ i := by
            intro hqi
            have hv := congrArg Fin.val hqi
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hq_mem, i, hi_mem, hq_ne⟩
          omega
      rcases hend with hi0 | hilast
      · right
        intro j
        subst i
        by_cases hj0 : j = 0
        · subst j
          by_contra hnot
          let q : Fin (k + 1) := ⟨1, by omega⟩
          have hnext : signSeqDoor s q := by
            have hkpos : 0 < k := by omega
            have hzero : (0 : Fin (k + 1)).val < k := by simpa using hkpos
            exact signSeqDoor_next_of_not_bad hi
              (by
                intro hb
                exact hnot hb) hzero
          have hnext_mem : q ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hnext
          have hne : q ≠ 0 := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hnext_mem, 0, hi_mem, hne⟩
          omega
        · have hlt : (0 : Fin (k + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
          exact hi.2 j hlt
      · left
        intro j
        subst i
        by_cases hjlast : j = Fin.last k
        · subst j
          by_contra hnot
          let p : Fin (k + 1) := ⟨k - 1, by omega⟩
          have hprev : signSeqDoor s p := by
            exact signSeqDoor_prev_of_bad hi
              ((signSeq_bad_iff_not_altPos s (Fin.last k)).mpr hnot)
              (by simp [Fin.last]; omega)
          have hprev_mem : p ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hprev
          have hne : p ≠ Fin.last k := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hprev_mem, Fin.last k, hi_mem, hne⟩
          omega
        · have hlt : j < Fin.last k := Fin.lt_last_iff_ne_last.mpr hjlast
          exact hi.1 j hlt
  · intro h
    rcases h with hpos | hneg
    · rw [signSeqDoorSet_eq_singleton_last_of_altPos hpos]
      simp
    · rw [signSeqDoorSet_eq_singleton_zero_of_altNeg hneg]
      simp

/-! ### Sorted label-sequence deletion parity -/

noncomputable def labelSeqSet {k m : ℕ} (L : Fin k → SignedLabel m) :
    Finset (SignedLabel m) :=
  Finset.univ.image L

def IsAltPosLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingLabelSetOf idx

def IsAltNegLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∃ idx : Fin k → Fin m, StrictMono idx ∧ labelSeqSet L = alternatingNegLabelSetOf idx

noncomputable instance isAltPosLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltPosLabelSeq L) := by
  classical
  unfold IsAltPosLabelSeq
  infer_instance

noncomputable instance isAltNegLabelSeq_decidable {k m : ℕ}
    (L : Fin k → SignedLabel m) : Decidable (IsAltNegLabelSeq L) := by
  classical
  unfold IsAltNegLabelSeq
  infer_instance

theorem sortedLabelSeq_isAltPos_iff_signSeqAltPos {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltPosLabelSeq L ↔ signSeqAltPos sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : alternatingLabelOf eta b ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]

theorem sortedLabelSeq_isAltNeg_iff_signSeqAltNeg {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltNegLabelSeq L ↔ signSeqAltNeg sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingNegLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : (alternatingLabelOf eta b).neg ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingNegLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingNegLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf, SignedLabel.neg] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, SignedLabel.neg, hsgn a]
      · simp [alternatingLabelOf, SignedLabel.neg]

noncomputable def labelSeqAltPosDeletionSet {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun j => IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a))

theorem sortedLabelSeq_deletion_iff_signSeqDoor {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a })
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔ signSeqDoor sgn j := by
  have hidx_del : StrictMono fun a : Fin k => idx (j.succAbove a) :=
    hidx.comp (Fin.strictMono_succAbove j)
  have hL_del :
      ∀ a : Fin k,
        (fun a : Fin k => L (j.succAbove a)) a =
          { positive := (fun a : Fin k => sgn (j.succAbove a)) a,
            index := (fun a : Fin k => idx (j.succAbove a)) a } := by
    intro a
    exact hL (j.succAbove a)
  exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx_del hL_del).trans
    (signSeqDoor_iff_remove_altPos sgn j).symm

theorem sortedLabelSeq_deletionParity {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  have hset : labelSeqAltPosDeletionSet L = signSeqDoorSet sgn := by
    ext j
    simp [labelSeqAltPosDeletionSet, signSeqDoorSet,
      sortedLabelSeq_deletion_iff_signSeqDoor hidx hL j]
  rw [hset, signSeqDeletionParity]
  constructor
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mpr hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mpr hneg
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mp hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mp hneg

theorem labelSeqSet_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    labelSeqSet (fun a : Fin k => L (e a)) = labelSeqSet L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e a, Finset.mem_univ _, ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e.symm a, Finset.mem_univ _, by simpa using ha⟩

theorem IsAltPosLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltPosLabelSeq L := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem IsAltNegLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltNegLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltNegLabelSeq L := by
  unfold IsAltNegLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem labelSeqSet_delete_comp_perm_eq {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (e (j.succAbove a))) =
      labelSeqSet (fun a : Fin k => L ((e j).succAbove a)) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    have hne : e (j.succAbove a) ≠ e j :=
      e.injective.ne (Fin.succAbove_ne j a)
    rcases Fin.exists_succAbove_eq hne with ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, by simpa [← hb] using ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨b, _hb, hb⟩
    let y : Fin (k + 1) := (e j).succAbove b
    have hne_pre : e.symm y ≠ j := by
      intro hy
      have hy' : y = e j := by
        calc
          y = e (e.symm y) := by simp [y]
          _ = e j := by rw [hy]
      exact Fin.succAbove_ne (e j) b (by simpa [y] using hy')
    rcases Fin.exists_succAbove_eq hne_pre with ⟨a, ha⟩
    have hey : e (j.succAbove a) = y := by
      rw [ha]
      simp [y]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simpa [y, ← hey] using hb⟩

theorem IsAltPosLabelSeq_delete_comp_perm_iff {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e (j.succAbove a))) ↔
      IsAltPosLabelSeq (fun a : Fin k => L ((e j).succAbove a)) := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_delete_comp_perm_eq L e j]

theorem labelSeqAltPosDeletionSet_comp_perm_card {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1))) :
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
      (labelSeqAltPosDeletionSet L).card := by
  classical
  have hmap :
      (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding =
        labelSeqAltPosDeletionSet L := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      subst j
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        simpa [labelSeqAltPosDeletionSet] using hi
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      simpa [labelSeqAltPosDeletionSet] using hiff.mp hi'
    · intro hj
      have hj' : IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj
      let i : Fin (k + 1) := e.symm j
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        apply hiff.mpr
        simpa [i] using hj'
      refine Finset.mem_map.mpr ⟨i, ?_, by simp [i]⟩
      simpa [labelSeqAltPosDeletionSet] using hi'
  calc
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
        ((labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding).card := by
          rw [Finset.card_map]
    _ = (labelSeqAltPosDeletionSet L).card := by rw [hmap]

theorem permutedSortedLabelSeq_deletionParity {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool}
    (hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  have hsorted :=
    sortedLabelSeq_deletionParity (idx := idx) hidx
      (sgn := sgn) (L := fun a : Fin (k + 1) => L (e a)) hLsort
  rw [labelSeqAltPosDeletionSet_comp_perm_card L e] at hsorted
  exact hsorted.trans
    (or_congr (IsAltPosLabelSeq_comp_perm L e) (IsAltNegLabelSeq_comp_perm L e))

def NoOppositeLabelSeq {k m : ℕ} (L : Fin k → SignedLabel m) : Prop :=
  ∀ i j : Fin k, L i ≠ (L j).neg

theorem signedLabel_eq_or_eq_neg_of_index_eq {m : ℕ} (A B : SignedLabel m)
    (hidx : A.index = B.index) : A = B ∨ A = B.neg := by
  cases A with
  | mk apos aidx =>
      cases B with
      | mk bpos bidx =>
          dsimp at hidx
          subst aidx
          cases apos <;> cases bpos <;>
            simp [SignedLabel.neg]

theorem labelSeq_index_injective_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin k → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Function.Injective fun i : Fin k => (L i).index := by
  intro i j hidx
  rcases signedLabel_eq_or_eq_neg_of_index_eq (L i) (L j) hidx with h | h
  · exact hinj h
  · exact False.elim (hno i j h)

theorem labelSeq_deletionParity_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  let idxOf : Fin (k + 1) → Fin m := fun a => (L a).index
  let e : Equiv.Perm (Fin (k + 1)) := Tuple.sort idxOf
  let idx : Fin (k + 1) → Fin m := fun a => idxOf (e a)
  let sgn : Fin (k + 1) → Bool := fun a => (L (e a)).positive
  have hidxOf : Function.Injective idxOf :=
    labelSeq_index_injective_of_injective_of_noOpposite
      (L := L) hinj hno
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    apply e.injective
    exact hidxOf hab
  have hidx_mono : Monotone idx := by
    exact Tuple.monotone_sort idxOf
  have hidx : StrictMono idx :=
    hidx_mono.strictMono_of_injective hidx_inj
  have hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a } := by
    intro a
    apply SignedLabel.ext <;> rfl
  exact permutedSortedLabelSeq_deletionParity
    (L := L) e (idx := idx) hidx (sgn := sgn) hLsort

/-! ## Ky Fan parity statement on the non-degenerate range -/

/-- After deleting `j` from a `(d+1)`-vertex sigma, every label in `A` still
appears.  Since exactly `d` vertices remain, this is the label-set-`A` door
condition used in the deletion count. -/
def SigmaDeletionHasAlternatingLabelSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) (j : Fin (d + 1)) : Prop :=
  ∀ a : Fin d, ∃ t : Fin (d + 1), t ≠ j ∧ sigmaLabel t = alternatingLabel a

/-- The door set of a sigma: deletions that leave the alternating label set `A`. -/
noncomputable def sigmaDoorSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) : Finset (Fin (d + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSet sigmaLabel j

/-- The parameterized deletion condition: deleting `j` leaves the alternating
label set determined by `idx`. -/
def SigmaDeletionHasAlternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) (j : Fin (r + 1)) : Prop :=
  ∀ a : Fin r, ∃ t : Fin (r + 1), t ≠ j ∧
    sigmaLabel t = alternatingLabelOf idx a

/-- Door set for a fixed increasing index set. -/
noncomputable def sigmaDoorSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) : Finset (Fin (r + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j

theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra t : Fin (r + 1)} {k : Fin r}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply (alternatingLabelOf_inj hidx).mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetOf idx ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetOf] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetOf idx).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = r := by
      simp [retained]
    simpa [alternatingLabelSetOf_card hidx, hretained] using himage_le
  have hEq : alternatingLabelSetOf idx = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_injOn {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
    (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetOf_card hidx]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door
      (idx := idx) hidx (extra := extra) (t := t) (k := k)
      hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := (alternatingLabelOf_inj hidx).mp
            (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSetOf] using hdoorExtra
      · simpa [sigmaDoorSetOf] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem labelSeqSet_delete_eq_erase_image {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
      (Finset.univ.erase j).image L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr
      ⟨j.succAbove a, by simp [Fin.succAbove_ne], ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    rcases Fin.exists_succAbove_eq htne with ⟨a, ha⟩
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, by simpa [← ha] using htlabel⟩

theorem SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {j : Fin (r + 1)} :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      alternatingLabelSetOf idx ⊆ (Finset.univ.erase j).image sigmaLabel := by
  classical
  constructor
  · intro hdoor x hx
    rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr
      ⟨t, by simp [htne], htlabel.trans ha⟩
  · intro hsub a
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
      simp [alternatingLabelSetOf]
    have himage := hsub hmem
    rcases Finset.mem_image.mp himage with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    exact ⟨t, htne, htlabel⟩

theorem IsAltPosLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltPosLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltNegLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltNegLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingNegLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {L : Fin (k + 1) → SignedLabel m}
    (horig : labelSeqSet L = alternatingLabelSetOf idx)
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔
      SigmaDeletionHasAlternatingLabelSetOf idx L j := by
  classical
  constructor
  · intro hdel
    rcases hdel with ⟨eta, heta, hdelSet⟩
    let retained : Finset (Fin (k + 1)) := Finset.univ.erase j
    have hret_eq_del :
        labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
          retained.image L := by
      simpa [retained] using labelSeqSet_delete_eq_erase_image L j
    have hret_subset :
        retained.image L ⊆ alternatingLabelSetOf idx := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
      have hxorig : x ∈ labelSeqSet L := by
        rw [← htlabel]
        simp [labelSeqSet]
      simpa [horig] using hxorig
    have hret_card : (retained.image L).card = k := by
      rw [← hret_eq_del, hdelSet, alternatingLabelSetOf_card heta.injective]
    have halt_card : (alternatingLabelSetOf idx).card = k :=
      alternatingLabelSetOf_card hidx.injective
    have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
      apply Finset.eq_of_subset_of_card_le hret_subset
      rw [hret_card, halt_card]
    exact SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image.mpr
      (by simpa [retained, hret_eq_alt])
  · intro hdoor
    refine ⟨idx, hidx, ?_⟩
    have himage :=
      sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
        (idx := idx) hidx.injective (sigmaLabel := L) (extra := j) hdoor
    rw [labelSeqSet_delete_eq_erase_image, himage]

theorem labelSeq_deletionParity_of_not_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hnot : ¬ Function.Injective L)
    (_hno : NoOppositeLabelSeq L) :
    Even (labelSeqAltPosDeletionSet L).card ∧
      ¬ IsAltPosLabelSeq L ∧ ¬ IsAltNegLabelSeq L := by
  classical
  have hnotAltPos : ¬ IsAltPosLabelSeq L := by
    intro h
    exact hnot h.injective
  have hnotAltNeg : ¬ IsAltNegLabelSeq L := by
    intro h
    exact hnot h.injective
  have heven : Even (labelSeqAltPosDeletionSet L).card := by
    by_cases hnonempty : (labelSeqAltPosDeletionSet L).Nonempty
    · rcases hnonempty with ⟨j0, hj0⟩
      have hdel0 :
          IsAltPosLabelSeq (fun a : Fin k => L (j0.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj0
      rcases hdel0 with ⟨idx, hidx, hdelSet⟩
      let retained : Finset (Fin (k + 1)) := Finset.univ.erase j0
      have hret_eq_del :
          labelSeqSet (fun a : Fin k => L (j0.succAbove a)) =
            retained.image L := by
        simpa [retained] using labelSeqSet_delete_eq_erase_image L j0
      have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
        rw [← hret_eq_del, hdelSet]
      have hret_subset_orig : retained.image L ⊆ labelSeqSet L := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
        rw [← htlabel]
        simp [labelSeqSet]
      have hcard_orig_le : (labelSeqSet L).card ≤ k := by
        have himage_le :
            (labelSeqSet L).card ≤ k + 1 := by
          simpa [labelSeqSet] using
            (Finset.card_image_le :
              (Finset.univ.image L).card ≤
                (Finset.univ : Finset (Fin (k + 1))).card)
        have hneq : (labelSeqSet L).card ≠ k + 1 := by
          intro hcard
          have hcard_image :
              (Finset.univ.image L).card =
                (Finset.univ : Finset (Fin (k + 1))).card := by
            simpa [labelSeqSet] using hcard
          have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin (k + 1))) :=
            (Finset.card_image_iff).mp hcard_image
          exact hnot (by
            intro a b hab
            exact hinjOn (by simp) (by simp) hab)
        omega
      have hcard_ret : (retained.image L).card = k := by
        rw [hret_eq_alt, alternatingLabelSetOf_card hidx.injective]
      have hcard_orig_ge : k ≤ (labelSeqSet L).card := by
        have hle : (retained.image L).card ≤ (labelSeqSet L).card :=
          Finset.card_le_card hret_subset_orig
        omega
      have hcard_orig : (labelSeqSet L).card = k := by
        omega
      have hret_eq_orig : retained.image L = labelSeqSet L := by
        apply Finset.eq_of_subset_of_card_le hret_subset_orig
        rw [hcard_orig, hcard_ret]
      have horig : labelSeqSet L = alternatingLabelSetOf idx := by
        rw [← hret_eq_orig, hret_eq_alt]
      have hdoor0 : SigmaDeletionHasAlternatingLabelSetOf idx L j0 := by
        exact (IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
          (idx := idx) hidx (L := L) horig j0).mp
          ⟨idx, hidx, hdelSet⟩
      have hextra_mem : L j0 ∈ alternatingLabelSetOf idx := by
        have hmem : L j0 ∈ labelSeqSet L := by
          simp [labelSeqSet]
        simpa [horig] using hmem
      rcases (by simpa [alternatingLabelSetOf] using hextra_mem) with ⟨a, ha⟩
      have hextra : L j0 = alternatingLabelOf idx a := ha.symm
      have hfixedCard :
          (sigmaDoorSetOf idx L).card = 2 :=
        sigmaDoorSetOf_card_duplicate_of_door
          (idx := idx) hidx.injective (sigmaLabel := L) (extra := j0)
          (k := a) hdoor0 hextra
      have hset :
          labelSeqAltPosDeletionSet L = sigmaDoorSetOf idx L := by
        ext j
        simp [labelSeqAltPosDeletionSet, sigmaDoorSetOf,
          IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
            (idx := idx) hidx (L := L) horig j]
      rw [hset, hfixedCard]
      simp
    · have hempty : labelSeqAltPosDeletionSet L = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simp
  exact ⟨heven, hnotAltPos, hnotAltNeg⟩

theorem labelSeq_deletionParity_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  by_cases hinj : Function.Injective L
  · exact labelSeq_deletionParity_of_injective_of_noOpposite
      (L := L) hinj hno
  · rcases labelSeq_deletionParity_of_not_injective_of_noOpposite
      (L := L) hinj hno with ⟨heven, hnotPos, hnotNeg⟩
    constructor
    · intro hodd
      rcases hodd with ⟨a, ha⟩
      rcases heven with ⟨b, hb⟩
      omega
    · intro h
      rcases h with hpos | hneg
      · exact False.elim (hnotPos hpos)
      · exact False.elim (hnotNeg hneg)

/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/

theorem finset_card_filter_cast_zmod_two {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ZMod 2) =
      ∑ x ∈ s, if p x then (1 : ZMod 2) else 0 := by
  rw [Finset.sum_boole]

theorem fintype_card_subtype_cast_zmod_two {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (Fintype.card {x : α // p x} : ZMod 2) =
      ∑ x : α, if p x then (1 : ZMod 2) else 0 := by
  classical
  rw [← finset_card_filter_cast_zmod_two (Finset.univ : Finset α) p]
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (Fintype.card_subtype p)

/-- In a finite bipartite graph, the number of odd-degree vertices on the
left equals the number of odd-degree vertices on the right modulo two. -/
theorem bipartite_odd_degree_card_eq_mod_two
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by
  classical
  rw [fintype_card_subtype_cast_zmod_two, fintype_card_subtype_cast_zmod_two]
  calc
    (∑ r : R, if Odd (Fintype.card {s : S // edge r s}) then (1 : ZMod 2) else 0)
        = ∑ r : R, (Fintype.card {s : S // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hodd : Odd (Fintype.card {s : S // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two.symm
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {s : S // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two.symm
    _ = ∑ r : R, ∑ s : S, if edge r s then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [← fintype_card_subtype_cast_zmod_two (fun s : S => edge r s)]
    _ = ∑ s : S, ∑ r : R, if edge r s then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (Fintype.card {r : R // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          rw [← fintype_card_subtype_cast_zmod_two (fun r : R => edge r s)]
    _ = ∑ s : S, if Odd (Fintype.card {r : R // edge r s}) then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          by_cases hodd : Odd (Fintype.card {r : R // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {r : R // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two

theorem bipartite_boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge]
    (boundary : R → Prop) [DecidablePred boundary]
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hr :
      ∀ r : R,
        (Odd (Fintype.card {s : S // edge r s}) ↔ boundary r))
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  have hodd := bipartite_odd_degree_card_eq_mod_two (R := R) (S := S) edge
  have hR :
      Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} =
        Fintype.card {r : R // boundary r} := by
    exact Fintype.card_congr
      { toFun := fun r => ⟨r.1, (hr r.1).mp r.2⟩
        invFun := fun r => ⟨r.1, (hr r.1).mpr r.2⟩
        left_inv := by intro r; cases r; rfl
        right_inv := by intro r; cases r; rfl }
  have hS :
      Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} =
        Fintype.card {s : S // topOdd s} := by
    exact Fintype.card_congr
      { toFun := fun s => ⟨s.1, (hs s.1).mp s.2⟩
        invFun := fun s => ⟨s.1, (hs s.1).mpr s.2⟩
        left_inv := by intro s; cases s; rfl
        right_inv := by intro s; cases s; rfl }
  simpa [hR, hS] using hodd

/-- A checked, non-degenerate package for the codimension-one rho degree in
the upper hemisphere.  `R` is the finite type of actual `(r-2)`-ridges and `S`
the finite type of upper top simplices incident to them; `nonempty_R` records
that the ridge side has not collapsed to an empty type. -/
structure RhoDegreeManifoldData (R S : Type*) [Fintype R] [Fintype S] where
  edge : R → S → Prop
  edge_decidable : DecidableRel edge
  boundary : R → Prop
  boundary_decidable : DecidablePred boundary
  nonempty_R : Nonempty R
  degree_card :
    ∀ r : R,
      Fintype.card {s : S // edge r s} = if boundary r then 1 else 2

namespace RhoDegreeManifoldData

attribute [instance] edge_decidable boundary_decidable

theorem odd_degree_iff_boundary
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S) (r : R) :
    Odd (Fintype.card {s : S // D.edge r s}) ↔ D.boundary r := by
  rw [D.degree_card r]
  by_cases hb : D.boundary r <;> simp [hb]

theorem boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // D.boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  exact bipartite_boundary_top_parity D.edge D.boundary topOdd
    (D.odd_degree_iff_boundary) hs

end RhoDegreeManifoldData

/-- Maximal chains lying in the upper hemisphere. -/
def UpperPrefixChain {n : ℕ} (P : SignedPermutation (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), UpperHemisphere (P.prefixChain i)

/-- A represented codimension-one ridge of the upper hemisphere is boundary
exactly when the deleted rank is the top rank and the last coordinate has not
appeared in the retained punctured flag. -/
def RepresentedUpperRidgeBoundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  gap = Fin.last n ∧ P.order.symm (Fin.last n) = Fin.last n

noncomputable instance representedUpperRidgeBoundary_decidable {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Decidable (RepresentedUpperRidgeBoundary P gap) := by
  classical
  exact inferInstance

/-! ## Actual upper-hemisphere label-set-`A` graph -/

noncomputable instance signedSubset_fintype (n : ℕ) : Fintype (SignedSubset n) := by
  classical
  refine Fintype.ofInjective (fun X : SignedSubset n => (X.pos, X.neg)) ?_
  intro X Y h
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance nonzeroSignedSubset_fintype (n : ℕ) :
    Fintype (NonzeroSignedSubset n) := by
  classical
  refine Fintype.ofInjective
    (fun X : NonzeroSignedSubset n => (X.1.pos, X.1.neg)) ?_
  intro X Y h
  apply Subtype.ext
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A concrete ordered codimension-one ridge in the upper hemisphere whose
retained labels are exactly `A`.  The ridge is an actual ordered chain of
vertices; the existential signed-permutation/gap field only certifies that it
is a genuine punctured maximal chain. -/
def ActualHemisphereARidge {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset (d + 1) //
    (∀ a : Fin d, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (d + 1), ∀ a : Fin d,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance actualHemisphereARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereARidge label) := by
  classical
  dsimp [ActualHemisphereARidge]
  infer_instance

/-- Upper-hemisphere maximal chains which contain at least one label-set-`A`
ridge. -/
def ActualHemisphereAChain {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {P : SignedPermutation (d + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (d + 1), ∀ a : Fin d,
        ∃ t : Fin d, label (P.prefixChain (gap.succAbove t)) = alternatingLabel a}

noncomputable instance actualHemisphereAChain_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereAChain label) := by
  classical
  dsimp [ActualHemisphereAChain]
  infer_instance

/-- Incidence between an actual ridge and an upper maximal chain: deleting one
rank of the chain gives exactly the ordered ridge. -/
def actualHemisphereAEdge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) (sigma : ActualHemisphereAChain label) : Prop :=
  ∃ gap : Fin (d + 1), ∀ a : Fin d,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAEdge_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidableRel (actualHemisphereAEdge (label := label)) := by
  classical
  exact inferInstance

/-- Boundary ridges are exactly those whose retained vertices all lie in the
equator. -/
def actualHemisphereABoundary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) : Prop :=
  ∀ a : Fin d, Equator (rho.1 a)

noncomputable instance actualHemisphereABoundary_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereABoundary (label := label)) := by
  classical
  exact inferInstance

/-- Unordered maximal label-set-`A` objects on the equator, expressed in the
same data language as `ActualHemisphereARidge`: the vertices are transported
through `equatorEquiv`, and the maximal-equator witness is a boundary punctured
flag in the upper hemisphere. -/
def EquatorActualARidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset d //
    (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last d) ∧
        ∀ a : Fin d,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last d).succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance equatorActualARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype (EquatorActualARidge label) := by
  classical
  dsimp [EquatorActualARidge]
  infer_instance

/-- A top chain is one-door when deleting exactly one of its vertices leaves
the alternating label set `A`. -/
def actualHemisphereAOneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) : Prop :=
  (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereAOneDoor_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereAOneDoor (label := label)) := by
  classical
  exact inferInstance

/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/

def ActualHemisphereIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxRidge idx label) := by
  classical
  dsimp [ActualHemisphereIdxRidge]
  infer_instance

def ActualHemisphereIdxChain {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (r + 1), ∀ a : Fin r,
        ∃ t : Fin r,
          label (P.prefixChain (gap.succAbove t)) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxChain_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxChain idx label) := by
  classical
  dsimp [ActualHemisphereIdxChain]
  infer_instance

def actualHemisphereIdxEdge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereIdxEdge_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereIdxEdge (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereIdxBoundary {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereIdxBoundary_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxBoundary (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def EquatorActualIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance equatorActualIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualIdxRidge idx label) := by
  classical
  dsimp [EquatorActualIdxRidge]
  infer_instance

abbrev StrictIndexMap (r m : ℕ) :=
  {idx : Fin r → Fin m // StrictMono idx}

@[implicit_reducible]
noncomputable def strictIndexMapFintype (r m : ℕ) :
    Fintype (StrictIndexMap r m) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx)
    (by
      intro idx
      change idx ∈
          ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx) ↔
        StrictMono idx
      simp)

abbrev EquatorActualAnyIdxRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  Σ idx : StrictIndexMap r m, EquatorActualIdxRidge idx.1 label

@[implicit_reducible]
noncomputable def equatorActualAnyIdxRidgeFintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAnyIdxRidge label) := by
  classical
  letI : Fintype (StrictIndexMap r m) := strictIndexMapFintype r m
  infer_instance

def actualHemisphereIdxOneDoor {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereIdxOneDoor_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxOneDoor (idx := idx) (label := label)) := by
  classical
  exact inferInstance

/-! ## Actual upper-hemisphere graph with self-contained alternating labels -/

def ActualHemisphereAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance actualHemisphereAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltRidge label) := by
  classical
  dsimp [ActualHemisphereAltRidge]
  infer_instance

def ActualHemisphereAltChain {r m : ℕ}
    (_label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) // UpperPrefixChain P}

noncomputable instance actualHemisphereAltChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereAltChain label) := by
  classical
  dsimp [ActualHemisphereAltChain]
  infer_instance

def actualHemisphereAltEdge {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label)
    (sigma : ActualHemisphereAltChain label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAltEdge_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereAltEdge (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereAltBoundary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereAltRidge label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereAltBoundary_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltBoundary (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereAltTop {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) : Prop :=
  IsAltPos label (fun i : Fin (r + 1) => sigma.1.prefixChain i) ∨
    IsAltNeg label (fun i : Fin (r + 1) => sigma.1.prefixChain i)

noncomputable instance actualHemisphereAltTop_decidable {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereAltTop (label := label)) := by
  classical
  exact inferInstance

def EquatorActualAltRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      IsAltPos label rho}

noncomputable instance equatorActualAltRidge_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAltRidge label) := by
  classical
  dsimp [EquatorActualAltRidge]
  infer_instance

/-! ## Antipodal and hemisphere bridges for self-contained alternating chains -/

theorem labelSeqSet_alternatingLabelOf {k m : ℕ} (idx : Fin k → Fin m) :
    labelSeqSet (fun a : Fin k => alternatingLabelOf idx a) = alternatingLabelSetOf idx := by
  simp [labelSeqSet, alternatingLabelSetOf]

theorem IsAltPosLabelSeq.not_isAltNeg {k m : ℕ} (hk : 0 < k)
    {L : Fin k → SignedLabel m} :
    IsAltPosLabelSeq L → IsAltNegLabelSeq L → False := by
  classical
  rintro ⟨idx, hidx, hsetPos⟩ hneg
  let Lpos : Fin k → SignedLabel m := fun a => alternatingLabelOf idx a
  have hLposSet : labelSeqSet Lpos = labelSeqSet L := by
    rw [hsetPos]
    exact labelSeqSet_alternatingLabelOf idx
  have hnegPos : IsAltNegLabelSeq Lpos := by
    rcases hneg with ⟨eta, heta, hsetNeg⟩
    exact ⟨eta, heta, hLposSet.trans hsetNeg⟩
  let sgn : Fin k → Bool := fun a => decide (Even a.val)
  have hLpos :
      ∀ a : Fin k, Lpos a = { positive := sgn a, index := idx a } := by
    intro a
    rfl
  have hsgnNeg : signSeqAltNeg sgn :=
    (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hLpos).mp hnegPos
  let i : Fin k := ⟨0, hk⟩
  have hi := hsgnNeg i
  simp [signSeqAltNeg, sgn, i] at hi

theorem IsAltPos.not_isAltNeg {k m n : ℕ} (hk : 0 < k)
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltPos label sigma → IsAltNeg label sigma → False :=
  IsAltPosLabelSeq.not_isAltNeg hk

@[simp]
theorem finPredOfNotLast_castSucc {r : ℕ} (i : Fin r)
    (h : Fin.castSucc i ≠ Fin.last r) :
    finPredOfNotLast (Fin.castSucc i) h = i := by
  apply Fin.ext
  rfl

noncomputable def equatorExtendOrder {r : ℕ} (e : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin (r + 1)) where
  toFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e (finPredOfNotLast i hi))
  invFun i :=
    if hi : i = Fin.last r then
      Fin.last r
    else
      Fin.castSucc (e.symm (finPredOfNotLast i hi))
  left_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]
  right_inv := by
    intro i
    by_cases hi : i = Fin.last r
    · subst i
      simp
    · have hnot :
        Fin.castSucc (e.symm (finPredOfNotLast i hi)) ≠ Fin.last r := by
        exact (Fin.castSucc_lt_last _).ne
      simp [hi, hnot]

@[simp]
theorem equatorExtendOrder_apply_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    equatorExtendOrder e (Fin.last r) = Fin.last r := by
  simp [equatorExtendOrder]

@[simp]
theorem equatorExtendOrder_symm_apply_last {r : ℕ} (e : Equiv.Perm (Fin r)) :
    (equatorExtendOrder e).symm (Fin.last r) = Fin.last r := by
  simp [equatorExtendOrder]

@[simp]
theorem equatorExtendOrder_apply_castSucc {r : ℕ} (e : Equiv.Perm (Fin r))
    (i : Fin r) :
    equatorExtendOrder e (Fin.castSucc i) = Fin.castSucc (e i) := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [equatorExtendOrder, h]

@[simp]
theorem equatorExtendOrder_symm_apply_castSucc {r : ℕ} (e : Equiv.Perm (Fin r))
    (i : Fin r) :
    (equatorExtendOrder e).symm (Fin.castSucc i) = Fin.castSucc (e.symm i) := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [equatorExtendOrder, h]

noncomputable def signedPermutationEquatorExtend {r : ℕ}
    (P : SignedPermutation r) : SignedPermutation (r + 1) where
  order := equatorExtendOrder P.order
  positive := fun i =>
    if hi : i = Fin.last r then true
    else P.positive (finPredOfNotLast i hi)

@[simp]
theorem signedPermutationEquatorExtend_positive_last {r : ℕ}
    (P : SignedPermutation r) :
    (signedPermutationEquatorExtend P).positive (Fin.last r) = true := by
  simp [signedPermutationEquatorExtend]

@[simp]
theorem signedPermutationEquatorExtend_positive_castSucc {r : ℕ}
    (P : SignedPermutation r) (i : Fin r) :
    (signedPermutationEquatorExtend P).positive (Fin.castSucc i) = P.positive i := by
  have h : Fin.castSucc i ≠ Fin.last r := (Fin.castSucc_lt_last i).ne
  simp [signedPermutationEquatorExtend, h]

theorem perm_apply_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    e (Fin.last r) = Fin.last r := by
  calc
    e (Fin.last r) = e (e.symm (Fin.last r)) := by rw [hcoord]
    _ = Fin.last r := by simp

theorem perm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e.symm hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

theorem perm_symm_apply_castSucc_ne_last_of_symm_last {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    e.symm (Fin.castSucc i) ≠ Fin.last r := by
  intro hlast
  have h := congrArg e hlast
  have hcast : Fin.castSucc i = Fin.last r := by
    simpa [perm_apply_last_of_symm_last e hcoord] using h
  exact (Fin.castSucc_lt_last i).ne hcast

noncomputable def equatorDropOrder {r : ℕ} (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) :
    Equiv.Perm (Fin r) where
  toFun i :=
    finPredOfNotLast (e (Fin.castSucc i))
      (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  invFun i :=
    finPredOfNotLast (e.symm (Fin.castSucc i))
      (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)
  left_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e.symm
              (Fin.castSucc
                (finPredOfNotLast (e (Fin.castSucc i))
                  (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e (Fin.castSucc i))
                (perm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e.symm
          (Fin.castSucc
            (finPredOfNotLast (e (Fin.castSucc i))
              (perm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e.symm (e (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp
  right_inv := by
    intro i
    apply Fin.castSucc_injective
    calc
      Fin.castSucc
          (finPredOfNotLast
            (e
              (Fin.castSucc
                (finPredOfNotLast (e.symm (Fin.castSucc i))
                  (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))))
            (perm_apply_castSucc_ne_last_of_symm_last e hcoord
              (finPredOfNotLast (e.symm (Fin.castSucc i))
                (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i)))) =
        e
          (Fin.castSucc
            (finPredOfNotLast (e.symm (Fin.castSucc i))
              (perm_symm_apply_castSucc_ne_last_of_symm_last e hcoord i))) := by
          rw [castSucc_finPredOfNotLast]
      _ = e (e.symm (Fin.castSucc i)) := by
          rw [castSucc_finPredOfNotLast]
      _ = Fin.castSucc i := by simp

@[simp]
theorem equatorDropOrder_apply_castSucc {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    Fin.castSucc (equatorDropOrder e hcoord i) = e (Fin.castSucc i) := by
  dsimp [equatorDropOrder]
  rw [castSucc_finPredOfNotLast]

@[simp]
theorem equatorDropOrder_symm_apply_castSucc {r : ℕ}
    (e : Equiv.Perm (Fin (r + 1)))
    (hcoord : e.symm (Fin.last r) = Fin.last r) (i : Fin r) :
    Fin.castSucc ((equatorDropOrder e hcoord).symm i) =
      e.symm (Fin.castSucc i) := by
  dsimp [equatorDropOrder]
  rw [castSucc_finPredOfNotLast]

def FullAltPosChain {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {P : SignedPermutation r // IsAltPos label (fun i : Fin r => P.prefixChain i)}

noncomputable instance fullAltPosChain_fintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (FullAltPosChain label) := by
  classical
  dsimp [FullAltPosChain]
  infer_instance

/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/

/-- One induction step of Ky Fan parity from the equator count and the two
degree facts.  This is the formal handshaking step; the remaining geometric
work is to instantiate `RhoDegreeManifoldData` for actual hemisphere ridges
and prove the corresponding sigma degree classifier. -/
theorem kyFan_parity_step_from_rho_sigma_data
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topAlternating : S → Prop) [DecidablePred topAlternating]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topAlternating s))
    (hboundary :
      Odd (Fintype.card {r : R // D.boundary r})) :
    Odd (Fintype.card {s : S // topAlternating s}) := by
  have hmod := D.boundary_top_parity topAlternating hs
  have hb : (Fintype.card {r : R // D.boundary r} : ZMod 2) = 1 :=
    hboundary.natCast_zmod_two
  have ht : (Fintype.card {s : S // topAlternating s} : ZMod 2) = 1 := by
    simpa [hb] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht

end ProofsInTheBook.Chapter39

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/Partitioning.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite polynomial partitioning for Erdős Problem 95

This file develops the finite Stone--Tukey input and the sign-cell
bookkeeping used by the low-degree incidence induction.  A strict sign cell
is indexed by a Boolean sign pattern; points on one of the polynomial walls
belong to no strict cell.
-/

open scoped BigOperators

namespace Partitioning

open Erdos95.Algebraic

/-- A real-valued function bisects a finite set when neither strict sign side
contains more than half of its points.  Points on the zero set are allowed on
the cutting wall. -/
def Bisects {X : Type*} (f : X → ℝ) (S : Finset X) : Prop :=
  2 * (S.filter fun x ↦ 0 < f x).card ≤ S.card ∧
    2 * (S.filter fun x ↦ f x < 0).card ≤ S.card

/-- Evaluation of a box-coefficient polynomial is the corresponding finite
linear combination of the box monomials. -/
theorem eval_polynomialOfCoefficients (k : ℕ)
    (c : CoeffIndex k → ℝ) (z : Fin 3 → ℝ) :
    MvPolynomial.eval z (polynomialOfCoefficients k c) =
      ∑ e : CoeffIndex k, c e * MvPolynomial.eval z (boxMonomial e) := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  simp only [map_sum, MvPolynomial.smul_eval]

/-- The strict sign cell cut out inside `S` by a finite list of
polynomials.  `true` denotes the positive side and `false` the negative
side. -/
noncomputable def signCell (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (sign : Fin j → Bool) :
    Finset (Fin 3 → ℝ) :=
  S.filter fun x ↦ ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
    else MvPolynomial.eval x (p i) < 0

theorem mem_signCell_iff {S : Finset (Fin 3 → ℝ)} {j : ℕ}
    {p : Fin j → MvPolynomial (Fin 3) ℝ} {sign : Fin j → Bool}
    {x : Fin 3 → ℝ} :
    x ∈ signCell S p sign ↔
      x ∈ S ∧ ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
        else MvPolynomial.eval x (p i) < 0 := by
  classical
  simp [signCell]

theorem signCell_snoc (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℝ)
    (sign : Fin j → Bool) (b : Bool) :
    signCell S (Fin.snoc p q) (Fin.snoc sign b) =
      (signCell S p sign).filter fun x ↦
        if b then 0 < MvPolynomial.eval x q
        else MvPolynomial.eval x q < 0 := by
  classical
  ext x
  simp only [mem_signCell_iff, Finset.mem_filter]
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  tauto

theorem card_signCell_snoc_le_of_bisects
    (S : Finset (Fin 3 → ℝ)) {j : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℝ)
    (sign : Fin j → Bool)
    (hbisect : Bisects (fun x ↦ MvPolynomial.eval x q) (signCell S p sign))
    (b : Bool) :
    2 * (signCell S (Fin.snoc p q) (Fin.snoc sign b)).card ≤
      (signCell S p sign).card := by
  rw [signCell_snoc]
  cases b with
  | false => simpa [Bisects] using hbisect.2
  | true => simpa [Bisects] using hbisect.1

/-! ## The finite Stone--Tukey interface -/

/-- The universal finite central-hyperplane bisection statement.  The strict
dimension inequality leaves at least one coefficient direction after the
simultaneous bisection constraints.  This is the finite form of the
Stone--Tukey theorem to be proved from Tucker's lemma below. -/
def FiniteLinearBisection : Prop :=
  ∀ (I B X : Type) [Fintype I] [Fintype B],
    Fintype.card I < Fintype.card B →
      ∀ (S : I → Finset X) (a : X → B → ℝ),
        ∃ c : B → ℝ, c ≠ 0 ∧
          ∀ i, Bisects (fun x ↦ ∑ b, c b * a x b) (S i)

/-- A proof of finite linear bisection supplies a nonzero low-degree
polynomial simultaneously bisecting any family whose cardinality fits in the
box coefficient space. -/
theorem exists_bisecting_polynomial_of_finiteLinearBisection
    (hStoneTukey : FiniteLinearBisection)
    (k : ℕ) (I : Type) [Fintype I]
    (S : I → Finset (Fin 3 → ℝ))
    (hcard : Fintype.card I < (k + 1) ^ 3) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ≠ 0 ∧ p.totalDegree ≤ 3 * k ∧
        ∀ i, Bisects (fun x ↦ MvPolynomial.eval x p) (S i) := by
  classical
  have hdim : Fintype.card I < Fintype.card (CoeffIndex k) := by
    simpa [CoeffIndex] using hcard
  obtain ⟨c, hc, hbisect⟩ :=
    hStoneTukey I (CoeffIndex k) (Fin 3 → ℝ) hdim S
      (fun x e ↦ MvPolynomial.eval x (boxMonomial e))
  refine ⟨polynomialOfCoefficients k c, ?_,
    totalDegree_polynomialOfCoefficients_le k c, ?_⟩
  · intro hp
    apply hc
    apply polynomialOfCoefficients_injective k
    simpa using hp
  · intro i
    simpa only [eval_polynomialOfCoefficients] using hbisect i

/-- All current sign cells can be bisected at once whenever their number
fits into the selected coefficient box. -/
theorem exists_next_partition_cut
    (hStoneTukey : FiniteLinearBisection)
    (S : Finset (Fin 3 → ℝ)) {j k : ℕ}
    (p : Fin j → MvPolynomial (Fin 3) ℝ)
    (hcard : 2 ^ j < (k + 1) ^ 3) :
    ∃ q : MvPolynomial (Fin 3) ℝ,
      q ≠ 0 ∧ q.totalDegree ≤ 3 * k ∧
        ∀ sign : Fin j → Bool,
          Bisects (fun x ↦ MvPolynomial.eval x q) (signCell S p sign) := by
  classical
  apply exists_bisecting_polynomial_of_finiteLinearBisection hStoneTukey k
    (Fin j → Bool) (fun sign ↦ signCell S p sign)
  simpa using hcard

/-- Iterating simultaneous bisection produces `2^J` strict sign cells, each
containing at most a `2^{-J}` fraction of the original finite set.  The
inequality is kept in denominator-free natural-number form. -/
theorem exists_partition_cuts_of_finiteLinearBisection
    (hStoneTukey : FiniteLinearBisection)
    (S : Finset (Fin 3 → ℝ)) (J : ℕ) (k : Fin J → ℕ)
    (hfit : ∀ j : Fin J, 2 ^ (j : ℕ) < (k j + 1) ^ 3) :
    ∃ p : Fin J → MvPolynomial (Fin 3) ℝ,
      (∀ j, p j ≠ 0 ∧ (p j).totalDegree ≤ 3 * k j) ∧
        ∀ sign : Fin J → Bool,
          2 ^ J * (signCell S p sign).card ≤ S.card := by
  classical
  induction J with
  | zero =>
      let p : Fin 0 → MvPolynomial (Fin 3) ℝ := fun i ↦ Fin.elim0 i
      refine ⟨p, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro sign
        simp [signCell]
  | succ J ih =>
      have hfitInit : ∀ j : Fin J,
          2 ^ (j : ℕ) < (Fin.init k j + 1) ^ 3 := by
        intro j
        change 2 ^ (j : ℕ) < (k j.castSucc + 1) ^ 3
        exact hfit j.castSucc
      obtain ⟨p, hp, hcells⟩ := ih (Fin.init k) hfitInit
      have hfitLast : 2 ^ J < (k (Fin.last J) + 1) ^ 3 := by
        simpa using hfit (Fin.last J)
      obtain ⟨q, hq, hqdeg, hqbisect⟩ :=
        exists_next_partition_cut hStoneTukey S p hfitLast
      refine ⟨Fin.snoc p q, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · simpa using And.intro hq hqdeg
        · rw [Fin.snoc_castSucc]
          have hi := hp i
          change p i ≠ 0 ∧ (p i).totalDegree ≤ 3 * k i.castSucc at hi
          exact hi
      · intro sign'
        rw [← Fin.snoc_init_self sign']
        calc
          2 ^ (J + 1) *
                (signCell S (Fin.snoc p q)
                  (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card =
              2 ^ J *
                (2 * (signCell S (Fin.snoc p q)
                  (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card) := by
                rw [pow_succ]
                ring
          _ ≤ 2 ^ J * (signCell S p (Fin.init sign')).card :=
            Nat.mul_le_mul_left _
              (card_signCell_snoc_le_of_bisects S p q (Fin.init sign')
                (hqbisect (Fin.init sign')) (sign' (Fin.last J)))
          _ ≤ S.card := hcells (Fin.init sign')

/-! ## The product wall -/

/-- The single polynomial whose zero set is the union of all successive
partitioning walls. -/
noncomputable def partitionPolynomial {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∏ j, p j

theorem partitionPolynomial_ne_zero {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (hp : ∀ j, p j ≠ 0) :
    partitionPolynomial p ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hp j

theorem totalDegree_partitionPolynomial_le {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) :
    (partitionPolynomial p).totalDegree ≤ ∑ j, (p j).totalDegree := by
  classical
  simpa [partitionPolynomial] using
    MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin J)) p

theorem totalDegree_partitionPolynomial_le_sum_three_mul {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (k : Fin J → ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ 3 * k j) :
    (partitionPolynomial p).totalDegree ≤ ∑ j, 3 * k j := by
  exact (totalDegree_partitionPolynomial_le p).trans <|
    Finset.sum_le_sum fun j _ ↦ hdeg j

theorem eval_partitionPolynomial {J : ℕ}
    (p : Fin J → MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (partitionPolynomial p) =
      ∏ j, MvPolynomial.eval x (p j) := by
  classical
  simp [partitionPolynomial, map_prod]

end Partitioning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/Geometry.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Elementary geometry for the Elekes--Sharir line family

This file proves the plane non-clustering estimate in coordinates: a proper
affine plane contains at most one line `L(p,q)` for each fixed first endpoint
`p`, and hence at most `|P|` lines indexed by `P × P`.
-/

namespace ES

/-! ## The ruling vector fields -/

/-- Direction of the normalized line `L(p,q)`. -/
noncomputable def lineDirection (p q : PlanePoint) : Space3 :=
  ![(q 1 - p 1) / 2, (p 0 - q 0) / 2, 1]

/-- Guth's polynomial vector field for the two-parameter family
`{L(p,q) | q ∈ ℝ²}`.  At every point it is a nonzero multiple of the
direction of the unique member of this family through that point. -/
noncomputable def rulingVectorField (p : PlanePoint) (x : Space3) : Space3 :=
  ![x 2 * x 0 + x 1 - x 2 * p 0 - p 1,
    p 0 - x 0 - x 2 * p 1 + x 2 * x 1,
    1 + (x 2) ^ 2]

/-- On `L(p,q)`, the ruling vector field is `(1+t²)` times the normalized
line direction. -/
theorem rulingVectorField_linePoint (p q : PlanePoint) (t : ℝ) :
    rulingVectorField p (linePoint p q t) =
      (1 + t ^ 2) • lineDirection p q := by
  funext i
  fin_cases i <;> simp [rulingVectorField, linePoint, lineDirection] <;> ring

/-- The unique second endpoint `q` such that the ruling line `L(p,q)` passes
through `x`.  The denominator is `1+x₂²`, hence is never zero. -/
noncomputable def secondIndexThrough (p : PlanePoint) (x : Space3) : PlanePoint :=
  let d := 1 + (x 2) ^ 2
  WithLp.toLp 2 ![((2 * x 0 - p 0 + x 2 * p 1) -
      x 2 * (2 * x 1 - p 1 - x 2 * p 0)) / d,
    (x 2 * (2 * x 0 - p 0 + x 2 * p 1) +
      (2 * x 1 - p 1 - x 2 * p 0)) / d]

private theorem one_add_sq_ne_zero (z : ℝ) : 1 + z ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg z]

/-- Every point of three-space lies on the ruling line indexed by
`(p, secondIndexThrough p x)`. -/
theorem linePoint_secondIndexThrough (p : PlanePoint) (x : Space3) :
    linePoint p (secondIndexThrough p x) (x 2) = x := by
  funext i
  fin_cases i
  · simp [linePoint, secondIndexThrough]
    field_simp [one_add_sq_ne_zero (x 2)]
    ring
  · simp [linePoint, secondIndexThrough]
    field_simp [one_add_sq_ne_zero (x 2)]
    ring
  · simp [linePoint]

/-- The affine-linear functional with the given normal vector. -/
noncomputable def planeValue (normal x : Space3) : ℝ :=
  normal 0 * x 0 + normal 1 * x 1 + normal 2 * x 2

/-- The whole Elekes--Sharir line `L(p,q)` lies in the affine plane with
equation `normal ⋅ x = offset`. -/
def LineInAffinePlane (normal : Space3) (offset : ℝ)
    (p q : PlanePoint) : Prop :=
  ∀ t : ℝ, planeValue normal (linePoint p q t) = offset

/-- For a proper affine plane and a fixed first endpoint `p`, at most one
member of the ruling-like family `q ↦ L(p,q)` lies in the plane. -/
theorem eq_of_same_first_of_lines_in_affinePlane
    {normal : Space3} {offset : ℝ} (hnormal : normal ≠ 0)
    {p q r : PlanePoint}
    (hq : LineInAffinePlane normal offset p q)
    (hr : LineInAffinePlane normal offset p r) : q = r := by
  have hq0 := hq 0
  have hq1 := hq 1
  have hr0 := hr 0
  have hr1 := hr 1
  simp [planeValue, linePoint] at hq0 hq1 hr0 hr1
  have hbase :
      normal 0 * (q 0 - r 0) + normal 1 * (q 1 - r 1) = 0 := by
    linarith
  have hdir :
      normal 0 * (q 1 - r 1) - normal 1 * (q 0 - r 0) = 0 := by
    linarith
  have hslope :
      normal 0 * (q 1 - p 1) + normal 1 * (p 0 - q 0) + 2 * normal 2 = 0 := by
    linarith
  have hnorm : 0 < normal 0 ^ 2 + normal 1 ^ 2 := by
    by_contra h
    have hz : normal 0 ^ 2 + normal 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (normal 0), sq_nonneg (normal 1)]
    have hn0 : normal 0 = 0 := by nlinarith [sq_nonneg (normal 1)]
    have hn1 : normal 1 = 0 := by nlinarith [sq_nonneg (normal 0)]
    have hn2 : normal 2 = 0 := by
      rw [hn0, hn1] at hslope
      linarith
    apply hnormal
    funext i
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
  have hxprod :
      (normal 0 ^ 2 + normal 1 ^ 2) * (q 0 - r 0) = 0 := by
    linear_combination normal 0 * hbase - normal 1 * hdir
  have hyprod :
      (normal 0 ^ 2 + normal 1 ^ 2) * (q 1 - r 1) = 0 := by
    linear_combination normal 1 * hbase + normal 0 * hdir
  have hx : q 0 = r 0 := by
    have hne : normal 0 ^ 2 + normal 1 ^ 2 ≠ 0 := hnorm.ne'
    exact sub_eq_zero.mp (mul_eq_zero.mp hxprod |>.resolve_left hne)
  have hy : q 1 = r 1 := by
    have hne : normal 0 ^ 2 + normal 1 ^ 2 ≠ 0 := hnorm.ne'
    exact sub_eq_zero.mp (mul_eq_zero.mp hyprod |>.resolve_left hne)
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- The indexed lines from `P × P` which lie in a specified affine plane. -/
noncomputable def lineIndicesInAffinePlane (P : Finset PlanePoint)
    (normal : Space3) (offset : ℝ) : Finset (PlanePoint × PlanePoint) := by
  classical
  exact (P.product P).filter fun pq => LineInAffinePlane normal offset pq.1 pq.2

/-- The Elekes--Sharir family has at most `|P|` lines in every proper affine
plane. -/
theorem card_lineIndicesInAffinePlane_le (P : Finset PlanePoint)
    {normal : Space3} {offset : ℝ} (hnormal : normal ≠ 0) :
    (lineIndicesInAffinePlane P normal offset).card ≤ P.card := by
  classical
  let S := lineIndicesInAffinePlane P normal offset
  have hinj : Set.InjOn Prod.fst (S : Set (PlanePoint × PlanePoint)) := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext hab
    exact eq_of_same_first_of_lines_in_affinePlane hnormal ha'.2 (hab ▸ hb'.2)
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

end ES

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/Hilbert.lean` -/

section
open scoped BigOperators

namespace Hilbert

open Erdos95.Algebraic Erdos95.ES

noncomputable def exactSumEquiv (n : ℕ) :
    {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} ≃
      ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag n) where
  toFun d := ⟨d.1, by
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨d.2, Finset.subset_univ _⟩⟩
  invFun d := ⟨d.1, (Finset.mem_finsuppAntidiag'.mp d.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance exactSumFintype (n : ℕ) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} :=
  Fintype.ofEquiv _ (exactSumEquiv n).symm

noncomputable instance exactSumFintypeDep {T : ℕ} (n : {n : ℕ // n ≤ T}) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
  exactSumFintype n.1

lemma card_exactSum (n : ℕ) :
    Fintype.card {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n} =
      Nat.multichoose 3 n := by
  classical
  rw [Fintype.card_congr (exactSumEquiv n)]
  simp only [Fintype.card_coe]
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

def boundedNatEquiv (T : ℕ) : {n : ℕ // n ≤ T} ≃ Fin (T + 1) where
  toFun n := ⟨n.1, by omega⟩
  invFun n := ⟨n.1, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedNatFintype (T : ℕ) :
    Fintype {n : ℕ // n ≤ T} :=
  Fintype.ofEquiv (Fin (T + 1)) (boundedNatEquiv T).symm

noncomputable def boundedSumEquiv (T : ℕ) :
    (Σ n : {n : ℕ // n ≤ T},
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) ≃
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} :=
  Equiv.sigmaSubtypeFiberEquivSubtype
    (fun d : Fin 3 →₀ ℕ => d.sum (fun _ e => e))
    (fun d => by rfl)

noncomputable instance boundedSumFintype (T : ℕ) :
    Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} :=
  by
    letI (n : {n : ℕ // n ≤ T}) :
        Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
      exactSumFintype n.1
    letI : Fintype (Σ n : {n : ℕ // n ≤ T},
        {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) :=
      @Sigma.instFintype _ _ (fun n => exactSumFintype n.1) inferInstance
    exact Fintype.ofEquiv _ (boundedSumEquiv T)

lemma card_boundedSum (T : ℕ) :
    Fintype.card {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) ≤ T} =
      (T + 3).choose 3 := by
  classical
  letI (n : {n : ℕ // n ≤ T}) :
      Fintype {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1} :=
    exactSumFintype n.1
  letI : Fintype (Σ n : {n : ℕ // n ≤ T},
      {d : Fin 3 →₀ ℕ // d.sum (fun _ e => e) = n.1}) :=
    @Sigma.instFintype _ _ (fun n => exactSumFintype n.1) inferInstance
  rw [← Fintype.card_congr (boundedSumEquiv T)]
  rw [Fintype.card_sigma]
  simp_rw [card_exactSum]
  rw [← Finset.sum_subtype (Finset.range (T + 1)) (by intro x; simp)]
  simpa [Nat.add_comm] using Nat.sum_range_multichoose T 3

lemma finrank_restrictTotalDegree_fin_three (T : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ T) =
      (T + 3).choose 3 := by
  letI : Fintype {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ T} :=
    boundedSumFintype T
  unfold MvPolynomial.restrictTotalDegree
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport ℝ
      {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ T})]
  exact card_boundedSum T

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
noncomputable abbrev DegreeLE (T : ℕ) :=
  MvPolynomial.restrictTotalDegree (Fin 3) ℝ T

noncomputable def mulDegreeLE (Q : Poly3) (a T : ℕ)
    (hQ : Q.totalDegree = a) (ha : a ≤ T) : DegreeLE (T - a) →ₗ[ℝ] DegreeLE T where
  toFun A := ⟨Q * A.1, by
    rw [MvPolynomial.mem_restrictTotalDegree]
    refine (MvPolynomial.totalDegree_mul Q A.1).trans ?_
    have hA := (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - a) A.1).mp A.2
    rw [hQ]
    omega⟩
  map_add' A B := by ext; simp [mul_add]
  map_smul' r A := by ext; simp [mul_smul_comm]

lemma mulDegreeLE_injective {Q : Poly3} {a T : ℕ}
    (hQ0 : Q ≠ 0) (hQ : Q.totalDegree = a) (ha : a ≤ T) :
    Function.Injective (mulDegreeLE Q a T hQ ha) := by
  intro A B h
  apply Subtype.ext
  apply mul_left_cancel₀ hQ0
  exact congrArg Subtype.val h

lemma finrank_range_mulDegreeLE {Q : Poly3} {a T : ℕ}
    (hQ0 : Q ≠ 0) (hQ : Q.totalDegree = a) (ha : a ≤ T) :
    Module.finrank ℝ (LinearMap.range (mulDegreeLE Q a T hQ ha)) =
      (T - a + 3).choose 3 := by
  rw [← (LinearEquiv.ofInjective (mulDegreeLE Q a T hQ ha)
    (mulDegreeLE_injective hQ0 hQ ha)).finrank_eq]
  exact finrank_restrictTotalDegree_fin_three (T - a)

lemma range_mulDegreeLE_inf {Q R : Poly3} {a b T : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ T) :
    LinearMap.range (mulDegreeLE Q a T hQa (by omega)) ⊓
        LinearMap.range (mulDegreeLE R b T hRb (by omega)) =
      LinearMap.range (mulDegreeLE (Q * R) (a + b) T
        (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT) := by
  ext Z
  constructor
  · rintro ⟨⟨A, hAZ⟩, ⟨B, hBZ⟩⟩
    have heq : Q * A.1 = R * B.1 := by
      have := congrArg Subtype.val (hAZ.trans hBZ.symm)
      exact this
    have hQdvd : Q ∣ R * B.1 := ⟨A.1, heq.symm⟩
    have hQprime : Prime Q :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hQirr
    have hQdvdB : Q ∣ B.1 :=
      (hQprime.dvd_mul.mp hQdvd).resolve_left hQnotR
    obtain ⟨C, hBC⟩ := hQdvdB
    have hAC : A.1 = R * C := by
      apply mul_left_cancel₀ hQ0
      calc
        Q * A.1 = R * B.1 := heq
        _ = R * (Q * C) := by rw [hBC]
        _ = Q * (R * C) := by ring
    have hCdeg : C.totalDegree ≤ T - (a + b) := by
      by_cases hC0 : C = 0
      · simp [hC0]
      · have hBdeg :=
          (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - b) B.1).mp B.2
        rw [hBC, MvPolynomial.totalDegree_mul_of_isDomain hQ0 hC0, hQa] at hBdeg
        omega
    refine ⟨⟨C, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
      (T - (a + b)) C).mpr hCdeg⟩, ?_⟩
    apply Subtype.ext
    change (Q * R) * C = Z.1
    calc
      (Q * R) * C = Q * (R * C) := by ring
      _ = Q * A.1 := by rw [← hAC]
      _ = Z.1 := congrArg Subtype.val hAZ
  · rintro ⟨C, hCZ⟩
    have hCdeg :=
      (MvPolynomial.mem_restrictTotalDegree (Fin 3) (T - (a + b)) C.1).mp C.2
    have hRCdeg : (R * C.1).totalDegree ≤ T - a := by
      refine (MvPolynomial.totalDegree_mul R C.1).trans ?_
      rw [hRb]
      omega
    have hQCdeg : (Q * C.1).totalDegree ≤ T - b := by
      refine (MvPolynomial.totalDegree_mul Q C.1).trans ?_
      rw [hQa]
      omega
    constructor
    · refine ⟨⟨R * C.1, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
        (T - a) (R * C.1)).mpr hRCdeg⟩, ?_⟩
      apply Subtype.ext
      change Q * (R * C.1) = Z.1
      calc
        Q * (R * C.1) = (Q * R) * C.1 := by ring
        _ = Z.1 := congrArg Subtype.val hCZ
    · refine ⟨⟨Q * C.1, (MvPolynomial.mem_restrictTotalDegree (Fin 3)
        (T - b) (Q * C.1)).mpr hQCdeg⟩, ?_⟩
      apply Subtype.ext
      change R * (Q * C.1) = Z.1
      calc
        R * (Q * C.1) = (Q * R) * C.1 := by ring
        _ = Z.1 := congrArg Subtype.val hCZ

lemma six_mul_choose_add_three (n : ℕ) :
    6 * (n + 3).choose 3 = (n + 1) * (n + 2) * (n + 3) := by
  have h3 := Nat.choose_succ_right_eq (n + 3) 2
  have h2 := Nat.choose_succ_right_eq (n + 3) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h3 h2
  have hm2 : n + 3 - 2 = n + 1 := by omega
  have hm1 : n + 3 - 1 = n + 2 := by omega
  rw [hm2] at h3
  rw [hm1] at h2
  nlinarith

lemma choose_cross_bound {a b T : ℕ} (hT : a + b ≤ T) :
    (T + 3).choose 3 + (T - (a + b) + 3).choose 3 ≤
      (T - a + 3).choose 3 + (T - b + 3).choose 3 + a * b * (T + 2) := by
  have h0 := six_mul_choose_add_three T
  have hab := six_mul_choose_add_three (T - (a + b))
  have ha := six_mul_choose_add_three (T - a)
  have hb := six_mul_choose_add_three (T - b)
  have hTa : T - a + a = T := by omega
  have hTb : T - b + b = T := by omega
  have hTab : T - (a + b) + (a + b) = T := by omega
  have hrelA : T - a = T - (a + b) + b := by omega
  have hrelB : T - b = T - (a + b) + a := by omega
  let x := T - (a + b)
  have hx : T - (a + b) = x := rfl
  have hTx : T = x + a + b := by dsimp [x]; omega
  have hAx : T - a = x + b := by dsimp [x]; omega
  have hBx : T - b = x + a := by dsimp [x]; omega
  have hcross :
      6 * ((T + 3).choose 3 + (T - (a + b) + 3).choose 3) +
          3 * a * b * (a + b) =
        6 * ((T - a + 3).choose 3 + (T - b + 3).choose 3) +
          6 * (a * b * (T + 2)) := by
    simp only [Nat.mul_add]
    rw [h0, hab, ha, hb]
    rw [hAx, hBx, hx, hTx]
    ring
  omega

lemma finrank_quotient_principalParts_le {Q R : Poly3} {a b T : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ T) :
    Module.finrank ℝ
        (DegreeLE T ⧸
          (LinearMap.range (mulDegreeLE Q a T hQa (by omega)) ⊔
            LinearMap.range (mulDegreeLE R b T hRb (by omega)))) ≤
      a * b * (T + 2) := by
  let SQ : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE Q a T hQa (by omega))
  let SR : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE R b T hRb (by omega))
  have hquot := (SQ ⊔ SR).finrank_quotient_add_finrank
  have hsup := SQ.finrank_sup_add_finrank_inf_eq SR
  have hQrank : Module.finrank ℝ SQ = (T - a + 3).choose 3 := by
    dsimp [SQ]
    exact finrank_range_mulDegreeLE hQ0 hQa (by omega)
  have hRrank : Module.finrank ℝ SR = (T - b + 3).choose 3 := by
    dsimp [SR]
    exact finrank_range_mulDegreeLE hR0 hRb (by omega)
  have hIrank : Module.finrank ℝ ↥(SQ ⊓ SR) =
      (T - (a + b) + 3).choose 3 := by
    rw [show SQ ⊓ SR =
        LinearMap.range (mulDegreeLE (Q * R) (a + b) T
          (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT) by
      dsimp [SQ, SR]
      exact range_mulDegreeLE_inf hQ0 hR0 hQirr hQnotR hQa hRb hT]
    exact finrank_range_mulDegreeLE (mul_ne_zero hQ0 hR0)
      (by rw [MvPolynomial.totalDegree_mul_of_isDomain hQ0 hR0, hQa, hRb]) hT
  have hVrank : Module.finrank ℝ (DegreeLE T) = (T + 3).choose 3 :=
    finrank_restrictTotalDegree_fin_three T
  have hcross := choose_cross_bound hT
  rw [hQrank, hRrank, hIrank] at hsup
  rw [hVrank] at hquot
  dsimp [SQ, SR] at hquot hsup ⊢
  omega

lemma finrank_quotient_ge_of_diagonal
    {I : Type*} [Fintype I] [DecidableEq I] {s T : ℕ}
    (U : Submodule ℝ (DegreeLE T))
    (F : I × Fin (s + 1) → DegreeLE T)
    (φ : I → DegreeLE T →ₗ[ℝ] Polynomial ℝ)
    (d : I → Polynomial ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hF : ∀ j i k, φ j (F (i, k)) =
      if i = j then d j * Polynomial.X ^ (k : ℕ) else 0)
    (hU : ∀ j G, G ∈ U → φ j G = 0) :
    Fintype.card I * (s + 1) ≤
      Module.finrank ℝ (DegreeLE T ⧸ U) := by
  let b : I × Fin (s + 1) → DegreeLE T ⧸ U :=
    fun z => U.mkQ (F z)
  have hb : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc z
    have hsumQ : U.mkQ (∑ w, c w • F w) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hc
    have hmem : (∑ w, c w • F w) ∈ U := by
      rw [← Submodule.Quotient.mk_eq_zero U]
      change U.mkQ (∑ w, c w • F w) = 0
      exact hsumQ
    have hz := hU z.1 (∑ w, c w • F w) hmem
    rw [map_sum] at hz
    simp only [map_smul] at hz
    rw [Fintype.sum_prod_type] at hz
    have hz' : ∑ k : Fin (s + 1),
        c (z.1, k) • (d z.1 * Polynomial.X ^ (k : ℕ)) = 0 := by
      simpa [hF] using hz
    have hfactor : d z.1 *
        (∑ k : Fin (s + 1),
          Polynomial.C (c (z.1, k)) * Polynomial.X ^ (k : ℕ)) = 0 := by
      rw [Finset.mul_sum]
      simpa only [Polynomial.smul_eq_C_mul, mul_assoc, mul_comm,
        mul_left_comm] using hz'
    have hpoly : (∑ k : Fin (s + 1),
        Polynomial.C (c (z.1, k)) * Polynomial.X ^ (k : ℕ)) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (hd z.1)
    have hcoeff := congrArg (Polynomial.lcoeff ℝ (z.2 : ℕ)) hpoly
    simp only [map_sum, Polynomial.C_mul_X_pow_eq_monomial, map_zero,
      Polynomial.lcoeff_apply] at hcoeff
    have hrewrite :
        (∑ b : Fin (s + 1),
          ((Polynomial.monomial (b : ℕ)) (c (z.1, b))).coeff z.2) =
        ∑ b : Fin (s + 1), if (b : ℕ) = (z.2 : ℕ) then c (z.1, b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Polynomial.coeff_monomial
    rw [hrewrite] at hcoeff
    have hsum :
        (∑ b : Fin (s + 1),
          if (b : ℕ) = (z.2 : ℕ) then c (z.1, b) else 0) = c z := by
      calc
        _ = (if (z.2 : ℕ) = (z.2 : ℕ) then c (z.1, z.2) else 0) := by
          apply Finset.sum_eq_single z.2
          · intro b hb hne
            have hval : (b : ℕ) ≠ (z.2 : ℕ) := fun e => hne (Fin.ext e)
            simp [hval]
          · simp
        _ = c z := by simp
    rw [hsum] at hcoeff
    exact hcoeff
  have hcard := hb.fintype_card_le_finrank
  simpa [b, Fintype.card_prod, Fintype.card_fin] using hcard

noncomputable def lineEquation (p q : PlanePoint) (k : Fin 2) : Poly3 :=
  MvPolynomial.X k.castSucc -
    MvPolynomial.C (linePoint p q 0 k.castSucc) -
      MvPolynomial.C (lineDirection p q k.castSucc) * MvPolynomial.X 2

lemma eval_lineEquation_on_line (p q r s : PlanePoint) (k : Fin 2) (t : ℝ) :
    MvPolynomial.eval (linePoint p q t) (lineEquation r s k) =
      linePoint p q t k.castSucc - linePoint r s t k.castSucc := by
  fin_cases k <;> simp [lineEquation, linePoint, lineDirection] <;> ring

lemma lineContained_lineEquation (p q : PlanePoint) (k : Fin 2) :
    LineContained (lineEquation p q k) (linePoint p q 0) (lineDirection p q) := by
  rw [lineContained_iff]
  intro t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, eval_lineEquation_on_line]
  ring

lemma exists_lineEquation_not_contained
    {p q r s : PlanePoint} (hne : (p, q) ≠ (r, s)) :
    ∃ k : Fin 2,
      ¬ LineContained (lineEquation r s k) (linePoint p q 0) (lineDirection p q) := by
  by_contra h
  push Not at h
  have heq (t : ℝ) : linePoint p q t = linePoint r s t := by
    funext i
    fin_cases i
    · have hz := (lineContained_iff (lineEquation r s 0)
        (linePoint p q 0) (lineDirection p q)).mp (h 0) t
      have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
          linePoint p q t := by
        funext j
        fin_cases j <;> simp [linePoint, lineDirection] <;> ring
      rw [hpoint, eval_lineEquation_on_line] at hz
      exact sub_eq_zero.mp hz
    · have hz := (lineContained_iff (lineEquation r s 1)
        (linePoint p q 0) (lineDirection p q)).mp (h 1) t
      have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
          linePoint p q t := by
        funext j
        fin_cases j <;> simp [linePoint, lineDirection] <;> ring
      rw [hpoint, eval_lineEquation_on_line] at hz
      exact sub_eq_zero.mp hz
    · simp [linePoint]
  exact hne (Prod.ext
    (eq_of_linePoint_eq_at_two (by norm_num : (0 : ℝ) ≠ 1) (heq 0) (heq 1)).1
    (eq_of_linePoint_eq_at_two (by norm_num : (0 : ℝ) ≠ 1) (heq 0) (heq 1)).2)

lemma totalDegree_lineEquation_le (p q : PlanePoint) (k : Fin 2) :
    (lineEquation p q k).totalDegree ≤ 1 := by
  unfold lineEquation
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp
    · simp
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

section Separators

variable {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)

noncomputable def separatorCoordinate (i j : I) : Fin 2 :=
  if h : i = j then 0 else
    Classical.choose (exists_lineEquation_not_contained (hinj.ne h))

noncomputable def lineSeparator (i j : I) : Poly3 :=
  lineEquation (idx j).1 (idx j).2 (separatorCoordinate idx hinj i j)

lemma lineContained_lineSeparator (i j : I) :
    LineContained (lineSeparator idx hinj i j)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) :=
  lineContained_lineEquation _ _ _

lemma not_lineContained_lineSeparator {i j : I} (hij : i ≠ j) :
    ¬ LineContained (lineSeparator idx hinj i j)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2) := by
  unfold lineSeparator separatorCoordinate
  simp only [dif_neg hij]
  exact Classical.choose_spec
    (exists_lineEquation_not_contained (hinj.ne hij))

lemma totalDegree_lineSeparator_le (i j : I) :
    (lineSeparator idx hinj i j).totalDegree ≤ 1 :=
  totalDegree_lineEquation_le _ _ _

noncomputable def lineIsolator (i : I) : Poly3 :=
  ∏ j ∈ (Finset.univ.erase i), lineSeparator idx hinj i j

lemma totalDegree_lineIsolator_le (i : I) :
    (lineIsolator idx hinj i).totalDegree ≤ Fintype.card I - 1 := by
  unfold lineIsolator
  calc
    (∏ j ∈ Finset.univ.erase i, lineSeparator idx hinj i j).totalDegree ≤
        ∑ j ∈ Finset.univ.erase i,
          (lineSeparator idx hinj i j).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact totalDegree_lineSeparator_le idx hinj i j
    _ = Fintype.card I - 1 := by simp

lemma lineRestriction_lineIsolator_ne_zero (i : I) :
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2) ≠ 0 := by
  unfold lineIsolator lineRestriction
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact not_lineContained_lineSeparator idx hinj hji.symm

lemma lineRestriction_lineIsolator_eq_zero {i j : I} (hij : i ≠ j) :
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) = 0 := by
  unfold lineIsolator lineRestriction
  rw [map_prod]
  apply Finset.prod_eq_zero (i := j)
  · exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
  · exact lineContained_lineSeparator idx hinj i j

end Separators

noncomputable def lineRestrictionLinear (T : ℕ) (x v : Fin 3 → ℝ) :
    DegreeLE T →ₗ[ℝ] Polynomial ℝ :=
  (MvPolynomial.aeval
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))).toLinearMap.comp
      (MvPolynomial.restrictTotalDegree (Fin 3) ℝ T).subtype

lemma lineRestrictionLinear_apply (T : ℕ) (x v : Fin 3 → ℝ) (F : DegreeLE T) :
    lineRestrictionLinear T x v F = lineRestriction F.1 x v := by
  simp [lineRestrictionLinear, lineRestriction, MvPolynomial.aeval_def]

lemma lineRestriction_X_two (p q : PlanePoint) :
    lineRestriction (MvPolynomial.X 2 : Poly3)
      (linePoint p q 0) (lineDirection p q) = Polynomial.X := by
  apply Polynomial.funext
  intro t
  rw [eval_lineRestriction]
  simp [linePoint, lineDirection]

noncomputable def isolatorPower
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    (s : ℕ) (z : I × Fin (s + 1)) : DegreeLE (Fintype.card I - 1 + s) :=
  ⟨lineIsolator idx hinj z.1 * MvPolynomial.X 2 ^ (z.2 : ℕ), by
    rw [MvPolynomial.mem_restrictTotalDegree]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hH := totalDegree_lineIsolator_le idx hinj z.1
    rw [MvPolynomial.totalDegree_X_pow]
    have hk : (z.2 : ℕ) ≤ s := by omega
    omega⟩

lemma line_family_quotient_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q R : Poly3} {a b s : ℕ}
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hT : a + b ≤ Fintype.card I - 1 + s)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hRlines : ∀ i, LineContained R
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2)) :
    Fintype.card I * (s + 1) ≤
      Module.finrank ℝ
        (DegreeLE (Fintype.card I - 1 + s) ⧸
          (LinearMap.range (mulDegreeLE Q a (Fintype.card I - 1 + s)
              hQa (by omega)) ⊔
            LinearMap.range (mulDegreeLE R b (Fintype.card I - 1 + s)
              hRb (by omega)))) := by
  let T := Fintype.card I - 1 + s
  let U : Submodule ℝ (DegreeLE T) :=
    LinearMap.range (mulDegreeLE Q a T hQa (by dsimp [T]; omega)) ⊔
      LinearMap.range (mulDegreeLE R b T hRb (by dsimp [T]; omega))
  let φ : I → DegreeLE T →ₗ[ℝ] Polynomial ℝ := fun i =>
    lineRestrictionLinear T (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2)
  let d : I → Polynomial ℝ := fun i =>
    lineRestriction (lineIsolator idx hinj i)
      (linePoint (idx i).1 (idx i).2 0)
      (lineDirection (idx i).1 (idx i).2)
  have hd : ∀ i, d i ≠ 0 := lineRestriction_lineIsolator_ne_zero idx hinj
  have hF : ∀ j i k, φ j (isolatorPower idx hinj s (i, k)) =
      if i = j then d j * Polynomial.X ^ (k : ℕ) else 0 := by
    intro j i k
    dsimp [φ]
    rw [lineRestrictionLinear_apply]
    change lineRestriction
      (lineIsolator idx hinj i * MvPolynomial.X 2 ^ (k : ℕ))
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = _
    rw [lineRestriction_mul]
    have hpow : lineRestriction (MvPolynomial.X 2 ^ (k : ℕ) : Poly3)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = Polynomial.X ^ (k : ℕ) := by
      unfold lineRestriction
      rw [map_pow]
      exact congrArg (fun F : Polynomial ℝ => F ^ (k : ℕ))
        (lineRestriction_X_two (idx j).1 (idx j).2)
    rw [hpow]
    by_cases hij : i = j
    · subst i
      simp [d]
    · rw [lineRestriction_lineIsolator_eq_zero idx hinj hij]
      simp [hij]
  have hU : ∀ j G, G ∈ U → φ j G = 0 := by
    intro j G hG
    rcases Submodule.mem_sup.mp hG with ⟨Y, hY, Z, hZ, rfl⟩
    rw [map_add]
    have hY0 : φ j Y = 0 := by
      obtain ⟨A, hA⟩ := hY
      rw [← hA]
      dsimp [φ]
      rw [lineRestrictionLinear_apply]
      change lineRestriction (Q * A.1)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = 0
      rw [lineRestriction_mul, hQlines j, zero_mul]
    have hZ0 : φ j Z = 0 := by
      obtain ⟨B, hB⟩ := hZ
      rw [← hB]
      dsimp [φ]
      rw [lineRestrictionLinear_apply]
      change lineRestriction (R * B.1)
        (linePoint (idx j).1 (idx j).2 0)
        (lineDirection (idx j).1 (idx j).2) = 0
      rw [lineRestriction_mul, hRlines j, zero_mul]
    rw [hY0, hZ0, add_zero]
  have hlow := finrank_quotient_ge_of_diagonal U
    (isolatorPower idx hinj s) φ d hd hF hU
  simpa [T, U] using hlow

/-- A finite family of distinct normalized Elekes--Sharir lines contained in
two coprime surfaces is uniformly bounded in terms of their degrees.  The
constant is deliberately coarse; only its independence of the line family is
used in the incidence argument. -/
lemma card_le_of_lines_in_two_surfaces
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q R : Poly3} {a b : ℕ}
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0)
    (hQirr : Irreducible Q) (hQnotR : ¬ Q ∣ R)
    (hQa : Q.totalDegree = a) (hRb : R.totalDegree = b)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hRlines : ∀ i, LineContained R
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2)) :
    Fintype.card I ≤ a * b * (2 * (a * b) + a + b + 2) := by
  let m := Fintype.card I
  let s := 2 * (a * b) + a + b + 1
  let T := m - 1 + s
  by_cases hm0 : m = 0
  · simp [m, hm0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hT : a + b ≤ T := by
    dsimp [T, s]
    omega
  have hlo := line_family_quotient_lower idx hinj hQa hRb hT hQlines hRlines
  have hup := finrank_quotient_principalParts_le hQ0 hR0 hQirr hQnotR
    hQa hRb hT
  have hbound : m * (s + 1) ≤ a * b * (T + 2) := by
    exact hlo.trans hup
  have hmone : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
  dsimp [m, s, T] at hbound ⊢
  have hleft : 2 * (a * b) + a + b + 1 + 1 =
      2 * (a * b) + a + b + 2 := by omega
  have hright : Fintype.card I - 1 + (2 * (a * b) + a + b + 1) + 2 =
      Fintype.card I + (2 * (a * b) + a + b + 2) := by
    dsimp [m] at hmpos
    omega
  rw [hleft, hright] at hbound
  have hL : Fintype.card I * (2 * (a * b) + a + b + 2) =
      Fintype.card I * (a * b) +
        Fintype.card I * (a * b + a + b + 2) := by ring
  have hR : a * b * (Fintype.card I + (2 * (a * b) + a + b + 2)) =
      Fintype.card I * (a * b) +
        a * b * (2 * (a * b) + a + b + 2) := by ring
  rw [hL, hR] at hbound
  have hmid : Fintype.card I * (a * b + a + b + 2) ≤
      a * b * (2 * (a * b) + a + b + 2) := by omega
  calc
    Fintype.card I = Fintype.card I * 1 := by omega
    _ ≤ Fintype.card I * (a * b + a + b + 2) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ a * b * (2 * (a * b) + a + b + 2) := hmid

end Hilbert

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/NonClustering.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Low-degree non-clustering for Elekes--Sharir lines

This file develops the polynomial ruling vector field used in Guth's
low-degree proof.  Its first key consequence is completely algebraic: if a
surface contains a line in the ruling with fixed first endpoint, then the
directional derivative of its defining polynomial along the ruling field
contains that line as well.
-/

open scoped BigOperators

namespace NonClustering

open Erdos95.Algebraic
open Erdos95.ES
open Erdos95.Hilbert

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Polynomial coordinates of `ES.rulingVectorField`. -/
noncomputable def rulingPolynomial (p : PlanePoint) : Fin 3 → Poly3
  | 0 => MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1 -
      MvPolynomial.X 2 * MvPolynomial.C (p 0) - MvPolynomial.C (p 1)
  | 1 => MvPolynomial.C (p 0) - MvPolynomial.X 0 -
      MvPolynomial.X 2 * MvPolynomial.C (p 1) +
        MvPolynomial.X 2 * MvPolynomial.X 1
  | 2 => 1 + MvPolynomial.X 2 ^ 2

theorem eval_rulingPolynomial (p : PlanePoint) (x : Space3) (i : Fin 3) :
    MvPolynomial.eval x (rulingPolynomial p i) = rulingVectorField p x i := by
  fin_cases i <;> simp [rulingPolynomial, rulingVectorField] <;> ring

/-- The derivation of a polynomial along the ruling vector field. -/
noncomputable def rulingDerivative (p : PlanePoint) : Poly3 → Poly3 :=
  MvPolynomial.mkDerivation ℝ (rulingPolynomial p)

theorem rulingDerivative_add (p : PlanePoint) (Q R : Poly3) :
    rulingDerivative p (Q + R) = rulingDerivative p Q + rulingDerivative p R := by
  exact map_add _ _ _

theorem rulingDerivative_mul (p : PlanePoint) (Q R : Poly3) :
    rulingDerivative p (Q * R) =
      Q * rulingDerivative p R + R * rulingDerivative p Q := by
  exact (MvPolynomial.mkDerivation ℝ (rulingPolynomial p)).leibniz Q R

/-- Partial differentiation cannot increase total degree. -/
theorem totalDegree_pderiv_le {ι : Type*} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (i : ι) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc : MvPolynomial.coeff m (MvPolynomial.pderiv i Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hcQ : MvPolynomial.coeff (m + Finsupp.single i 1) Q ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hmem : m + Finsupp.single i 1 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hcQ
  calc
    m.sum (fun _ e => e) ≤
        (m + Finsupp.single i 1).sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index'] <;> simp
    _ ≤ Q.totalDegree := MvPolynomial.le_totalDegree hmem

theorem irreducible_totalDegree_pos {Q : Poly3} (hQirr : Irreducible Q) :
    0 < Q.totalDegree := by
  by_contra h
  have hdeg : Q.totalDegree = 0 := by omega
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : MvPolynomial.coeff 0 Q ≠ 0 := by
    intro hc0
    apply hQirr.ne_zero
    rw [hC, hc0, map_zero]
  have hunit : IsUnit (MvPolynomial.coeff 0 Q) := isUnit_iff_ne_zero.mpr hc
  exact hQirr.not_isUnit (hC ▸ hunit.map (MvPolynomial.C : ℝ →+* Poly3))

/-- An irreducible nonconstant polynomial in characteristic zero has a
nonzero partial derivative. -/
theorem exists_pderiv_ne_zero {Q : Poly3} (hQirr : Irreducible Q) :
    ∃ i : Fin 3, MvPolynomial.pderiv i Q ≠ 0 := by
  have hQ0 := hQirr.ne_zero
  have hsupp : Q.support.Nonempty := by
    simpa [MvPolynomial.support_nonempty] using hQ0
  obtain ⟨m, hm, heq⟩ := Q.support.exists_mem_eq_sup hsupp
    (fun m : Fin 3 →₀ ℕ => m.sum fun _ e => e)
  have hsum : 0 < m.sum (fun _ e => e) := by
    rw [← heq]
    exact irreducible_totalDegree_pos hQirr
  have hm0 : m ≠ 0 := by
    intro hzero
    subst m
    simp at hsum
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
  refine ⟨i, ?_⟩
  intro hderiv
  let d := m - Finsupp.single i 1
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hadd : d + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel hmi
  have hcoeffQ : MvPolynomial.coeff m Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hcoeff := MvPolynomial.coeff_pderiv (i := i) Q d
  rw [hderiv, MvPolynomial.coeff_zero, hadd] at hcoeff
  have hnat : (d i : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_ne_zero hcoeffQ hnat) hcoeff.symm

/-- Every nonzero partial derivative has strictly smaller total degree than
a nonconstant polynomial. -/
theorem totalDegree_pderiv_lt {Q : Poly3} {i : Fin 3}
    (hQdeg : 0 < Q.totalDegree) :
    (MvPolynomial.pderiv i Q).totalDegree < Q.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hQdeg]
  intro d hd
  have hc : MvPolynomial.coeff d (MvPolynomial.pderiv i Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hc
  have hcQ : MvPolynomial.coeff (d + Finsupp.single i 1) Q ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hmem : d + Finsupp.single i 1 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hcQ
  have hsum : (d + Finsupp.single i 1).sum (fun _ e => e) =
      d.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index'] <;> simp
  rw [← Nat.add_one_le_iff, ← hsum]
  exact MvPolynomial.le_totalDegree hmem

/-- The Hilbert line-counting bound is monotone when the second degree is
bounded by the first. -/
theorem lineSurfaceBound_mono {a b : ℕ} (hb : b ≤ a) :
    a * b * (2 * (a * b) + a + b + 2) ≤
      a * a * (2 * (a * a) + a + a + 2) := by
  gcongr

/-- A point of a hypersurface is singular when all its first partial
derivatives vanish there. -/
def SingularAt (Q : Poly3) (x : Space3) : Prop :=
  ∀ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i Q) = 0

/-- If every point of every indexed line on an irreducible surface is
singular, the Hilbert bound applied to a nonzero partial derivative bounds
the number of lines. -/
theorem card_le_of_all_lines_singular
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q : Poly3} (hQirr : Irreducible Q)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hsing : ∀ i t, SingularAt Q (linePoint (idx i).1 (idx i).2 t)) :
    Fintype.card I ≤ Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hQirr
  have hdeg := totalDegree_pderiv_lt (i := j) (irreducible_totalDegree_pos hQirr)
  have hnotdiv : ¬ Q ∣ MvPolynomial.pderiv j Q := by
    intro hdiv
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hj
    omega
  have hDlines : ∀ i, LineContained (MvPolynomial.pderiv j Q)
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2) := by
    intro i
    rw [lineContained_iff]
    intro t
    have hpoint : (fun k => linePoint (idx i).1 (idx i).2 0 k +
        t * lineDirection (idx i).1 (idx i).2 k) =
        linePoint (idx i).1 (idx i).2 t := by
      funext k
      fin_cases k <;> simp [linePoint, lineDirection] <;> ring
    rw [hpoint]
    exact hsing i t j
  have hbound := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hj hQirr hnotdiv rfl rfl hQlines hDlines
  exact hbound.trans (lineSurfaceBound_mono hdeg.le)

/-- More lines than the singular-line bound force a nonsingular point on
one of them. -/
theorem exists_nonsingular_point_of_bound_lt_card
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I → PlanePoint × PlanePoint) (hinj : Function.Injective idx)
    {Q : Poly3} (hQirr : Irreducible Q)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx i).1 (idx i).2 0) (lineDirection (idx i).1 (idx i).2))
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        Fintype.card I) :
    ∃ i t, ¬ SingularAt Q (linePoint (idx i).1 (idx i).2 t) := by
  by_contra h
  push Not at h
  exact (Nat.not_le_of_lt hlarge)
    (card_le_of_all_lines_singular idx hinj hQirr hQlines h)

theorem rulingDerivative_eq_pderiv (p : PlanePoint) (Q : Poly3) :
    rulingDerivative p Q =
      rulingPolynomial p 0 * MvPolynomial.pderiv 0 Q +
        rulingPolynomial p 1 * MvPolynomial.pderiv 1 Q +
          rulingPolynomial p 2 * MvPolynomial.pderiv 2 Q := by
  let D : Derivation ℝ Poly3 Poly3 :=
    (rulingPolynomial p 0) • (MvPolynomial.pderiv 0) +
      (rulingPolynomial p 1) • (MvPolynomial.pderiv 1) +
        (rulingPolynomial p 2) • (MvPolynomial.pderiv 2)
  have hD : MvPolynomial.mkDerivation ℝ (rulingPolynomial p) = D := by
    apply MvPolynomial.derivation_ext
    intro j
    fin_cases j <;>
      simp [D, MvPolynomial.pderiv_X, Pi.single_apply]
  have h := DFunLike.congr_fun hD Q
  simpa [rulingDerivative, D, smul_eq_mul] using h

private theorem totalDegree_rulingPolynomial_le (p : PlanePoint) (i : Fin 3) :
    (rulingPolynomial p i).totalDegree ≤ 2 := by
  fin_cases i
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
        · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp
        · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · dsimp only [rulingPolynomial]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact (MvPolynomial.totalDegree_pow _ _).trans (by simp)

/-- The ruling derivative has degree at most two more than the original
polynomial.  The sharper `d+1` estimate is unnecessary for the incidence
argument; this cancellation-free form is stable under all degenerate cases. -/
theorem totalDegree_rulingDerivative_le (p : PlanePoint) (Q : Poly3) :
    (rulingDerivative p Q).totalDegree ≤ Q.totalDegree + 2 := by
  have hterm (i : Fin 3) :
      (rulingPolynomial p i * MvPolynomial.pderiv i Q).totalDegree ≤
        Q.totalDegree + 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans <| by
      have hfield := totalDegree_rulingPolynomial_le p i
      have hderiv := totalDegree_pderiv_le Q i
      omega
  rw [rulingDerivative_eq_pderiv]
  exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
    ((MvPolynomial.totalDegree_add _ _).trans <| max_le (hterm 0) (hterm 1))
    (hterm 2)

/-- Polynomial uniqueness for the first-order ODE used below.  If a
polynomial solution of `a f' = f g` vanishes at a point where `a` does not,
then it vanishes identically. -/
private theorem polynomial_eq_zero_of_mul_derivative_eq_mul
    (a f g : Polynomial ℝ) (t : ℝ)
    (ha : a.eval t ≠ 0) (hfroot : f.eval t = 0)
    (hode : a * f.derivative = f * g) :
    f = 0 := by
  by_contra hf
  have hfroot' : f.IsRoot t := hfroot
  have hdegree : f.natDegree ≠ 0 := by
    intro hzero
    rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, Polynomial.eval_C] at hfroot
    apply hf
    rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, hfroot, map_zero]
  have hfderiv : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdegree
  have haleft : a * f.derivative ≠ 0 := by
    apply mul_ne_zero
    · intro hazero
      exact ha (hazero ▸ Polynomial.eval_zero)
    · exact hfderiv
  have hgright : f * g ≠ 0 := hode ▸ haleft
  have ha_notroot : ¬a.IsRoot t := ha
  have hmult_a : a.rootMultiplicity t = 0 :=
    Polynomial.rootMultiplicity_eq_zero ha_notroot
  have hmult_deriv : f.derivative.rootMultiplicity t =
      f.rootMultiplicity t - 1 :=
    Polynomial.derivative_rootMultiplicity_of_root hfroot'
  have hmult := congrArg (Polynomial.rootMultiplicity t) hode
  rw [Polynomial.rootMultiplicity_mul haleft,
    Polynomial.rootMultiplicity_mul hgright, hmult_a, zero_add,
    hmult_deriv] at hmult
  have hmpos : 0 < f.rootMultiplicity t :=
    (Polynomial.rootMultiplicity_pos hf).mpr hfroot'
  omega

private noncomputable def lineSubstitution {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))

private theorem lineSubstitution_apply {ι : Type*} [Fintype ι]
    (x v : ι → ℝ) (Q : MvPolynomial ι ℝ) :
    lineSubstitution x v Q = lineRestriction Q x v :=
  by simp [lineSubstitution, lineRestriction, MvPolynomial.aeval_def]

/-- Constant-coefficient directional derivative in an arbitrary finite
number of variables. -/
private noncomputable def constantDirectionalDerivative
    {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    MvPolynomial ι ℝ → MvPolynomial ι ℝ :=
  MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (v i))

/-- Formal chain rule for restriction to an affine line, packaged using the
universal derivation of a multivariate polynomial ring. -/
theorem derivative_lineRestriction {ι : Type*} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    (lineRestriction Q x v).derivative =
      lineRestriction (constantDirectionalDerivative v Q) x v := by
  let φ : MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ := lineSubstitution x v
  letI : Algebra (MvPolynomial ι ℝ) (Polynomial ℝ) := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    IsScalarTower.of_algHom φ
  let D₁ : Derivation ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    { toFun := fun F => (φ F).derivative
      map_add' := fun F G => by simp
      map_smul' := fun r F => by
        change (φ (r • F)).derivative = r • (φ F).derivative
        simp
      map_one_eq_zero' := by simp
      leibniz' := fun F G => by
        change (φ (F * G)).derivative =
          F • (φ G).derivative + G • (φ F).derivative
        simp [Polynomial.derivative_mul, mul_comm, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        ring }
  let D₂ : Derivation ℝ (MvPolynomial ι ℝ) (Polynomial ℝ) :=
    { toFun := fun F => φ (constantDirectionalDerivative v F)
      map_add' := fun F G => by simp [constantDirectionalDerivative]
      map_smul' := fun r F => by simp [constantDirectionalDerivative]
      map_one_eq_zero' := by simp [constantDirectionalDerivative]
      leibniz' := fun F G => by
        change φ (constantDirectionalDerivative v (F * G)) =
          F • φ (constantDirectionalDerivative v G) +
            G • φ (constantDirectionalDerivative v F)
        simp [constantDirectionalDerivative, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro i
    dsimp [D₁, D₂]
    change (φ (MvPolynomial.X i)).derivative =
      φ (constantDirectionalDerivative v (MvPolynomial.X i))
    simp [constantDirectionalDerivative, φ, lineSubstitution,
      Polynomial.derivative_mul]
  have h := DFunLike.congr_fun hD Q
  simpa [D₁, D₂, φ, lineSubstitution_apply] using h

private theorem lineRestriction_rulingPolynomial (p q : PlanePoint)
    (i : Fin 3) :
    lineRestriction (rulingPolynomial p i) (linePoint p q 0)
        (lineDirection p q) =
      (1 + Polynomial.X ^ 2) * Polynomial.C (lineDirection p q i) := by
  apply Polynomial.funext
  intro t
  rw [eval_lineRestriction]
  have hpoint : (fun j => linePoint p q 0 j + t * lineDirection p q j) =
      linePoint p q t := by
    funext j
    fin_cases j <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, eval_rulingPolynomial, rulingVectorField_linePoint]
  fin_cases i <;> simp [lineDirection] <;> ring

/-- Restriction of the ruling derivative to a ruling line is `(1+X²)`
times the derivative of the original line restriction. -/
theorem lineRestriction_rulingDerivative (p q : PlanePoint) (Q : Poly3) :
    lineRestriction (rulingDerivative p Q) (linePoint p q 0)
        (lineDirection p q) =
      (1 + Polynomial.X ^ 2) *
        (lineRestriction Q (linePoint p q 0) (lineDirection p q)).derivative := by
  let φ : Poly3 →ₐ[ℝ] Polynomial ℝ :=
    lineSubstitution (linePoint p q 0) (lineDirection p q)
  letI : Algebra Poly3 (Polynomial ℝ) := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℝ Poly3 (Polynomial ℝ) := IsScalarTower.of_algHom φ
  let D₁ : Derivation ℝ Poly3 (Polynomial ℝ) :=
    { toFun := fun F => φ (rulingDerivative p F)
      map_add' := fun F G => by simp [rulingDerivative_add]
      map_smul' := fun r F => by
        change φ (rulingDerivative p (r • F)) = r • φ (rulingDerivative p F)
        simp [rulingDerivative]
      map_one_eq_zero' := by simp [rulingDerivative]
      leibniz' := fun F G => by
        change φ (rulingDerivative p (F * G)) =
          F • φ (rulingDerivative p G) + G • φ (rulingDerivative p F)
        simp [rulingDerivative_mul, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  let Ddir : Derivation ℝ Poly3 (Polynomial ℝ) :=
    { toFun := fun F => φ (constantDirectionalDerivative (lineDirection p q) F)
      map_add' := fun F G => by simp [constantDirectionalDerivative]
      map_smul' := fun r F => by simp [constantDirectionalDerivative]
      map_one_eq_zero' := by simp [constantDirectionalDerivative]
      leibniz' := fun F G => by
        change φ (constantDirectionalDerivative (lineDirection p q) (F * G)) =
          F • φ (constantDirectionalDerivative (lineDirection p q) G) +
            G • φ (constantDirectionalDerivative (lineDirection p q) F)
        simp [constantDirectionalDerivative, Algebra.smul_def, mul_comm,
          RingHom.algebraMap_toAlgebra] }
  let D₂ : Derivation ℝ Poly3 (Polynomial ℝ) :=
    (1 + Polynomial.X ^ 2 : Polynomial ℝ) • Ddir
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro i
    dsimp [D₁, D₂, Ddir]
    change φ (rulingDerivative p (MvPolynomial.X i)) =
      (1 + Polynomial.X ^ 2) *
        φ (constantDirectionalDerivative (lineDirection p q) (MvPolynomial.X i))
    simp only [rulingDerivative, constantDirectionalDerivative,
      MvPolynomial.mkDerivation_X]
    change φ (rulingPolynomial p i) =
      (1 + Polynomial.X ^ 2) * φ (MvPolynomial.C (lineDirection p q i))
    simpa [φ, lineSubstitution_apply] using lineRestriction_rulingPolynomial p q i
  have h := DFunLike.congr_fun hD Q
  rw [derivative_lineRestriction]
  simpa [D₁, D₂, Ddir, φ, lineSubstitution_apply, rulingDerivative] using h

/-- A ruling line contained in `Z(Q)` is also contained in the zero set of
the ruling derivative. -/
theorem lineContained_rulingDerivative {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) :
    LineContained (rulingDerivative p Q)
      (linePoint p q 0) (lineDirection p q) := by
  unfold LineContained at hQ ⊢
  rw [lineRestriction_rulingDerivative, hQ, Polynomial.derivative_zero, mul_zero]

/-- If an irreducible surface factor divides its ruling derivative, the
unique ruling line through any zero of the factor is contained in the
surface.  This is the algebraic uniqueness-of-integral-curves step in
Guth's non-clustering lemma. -/
theorem lineContained_secondIndexThrough_of_dvd_rulingDerivative
    {p : PlanePoint} {Q : Poly3} {x : Space3}
    (hdiv : Q ∣ rulingDerivative p Q)
    (hx : MvPolynomial.eval x Q = 0) :
    LineContained Q
      (linePoint p (secondIndexThrough p x) 0)
      (lineDirection p (secondIndexThrough p x)) := by
  obtain ⟨R, hR⟩ := hdiv
  let q := secondIndexThrough p x
  let f := lineRestriction Q (linePoint p q 0) (lineDirection p q)
  let g := lineRestriction R (linePoint p q 0) (lineDirection p q)
  have hode : (1 + Polynomial.X ^ 2) * f.derivative = f * g := by
    dsimp only [f, g]
    rw [← lineRestriction_rulingDerivative, hR,
      lineRestriction_mul]
  have hroot : f.eval (x 2) = 0 := by
    dsimp only [f]
    rw [eval_lineRestriction]
    have hparam :
        (fun i => linePoint p q 0 i + x 2 * lineDirection p q i) =
          linePoint p q (x 2) := by
      funext i
      fin_cases i <;> simp [linePoint, lineDirection] <;> ring
    rw [hparam]
    change MvPolynomial.eval
      (linePoint p (secondIndexThrough p x) (x 2)) Q = 0
    rw [linePoint_secondIndexThrough]
    exact hx
  have hlead : (1 + Polynomial.X ^ 2 : Polynomial ℝ).eval (x 2) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    nlinarith [sq_nonneg (x 2)]
  exact polynomial_eq_zero_of_mul_derivative_eq_mul
    (1 + Polynomial.X ^ 2) f g (x 2) hlead hroot hode

/-! ## A Hilbert-function line bound -/

/-- Second endpoints whose fixed-first-endpoint ruling lines lie on `Q`. -/
noncomputable def secondIndicesOnSurface (P : Finset PlanePoint)
    (p : PlanePoint) (Q : Poly3) : Finset PlanePoint := by
  classical
  exact P.filter fun q =>
    LineContained Q (linePoint p q 0) (lineDirection p q)

/-- Unless `Q` divides its ruling derivative, only boundedly many members of
one fixed ruling can lie on the irreducible surface `Q`. -/
theorem dvd_rulingDerivative_or_card_secondIndicesOnSurface_le
    (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3)
    (hQirr : Irreducible Q) :
    Q ∣ rulingDerivative p Q ∨
      (secondIndicesOnSurface P p Q).card ≤
        Q.totalDegree * (rulingDerivative p Q).totalDegree *
          (2 * (Q.totalDegree * (rulingDerivative p Q).totalDegree) +
            Q.totalDegree + (rulingDerivative p Q).totalDegree + 2) := by
  classical
  by_cases hdiv : Q ∣ rulingDerivative p Q
  · exact Or.inl hdiv
  · right
    let S := secondIndicesOnSurface P p Q
    let idx : S → PlanePoint × PlanePoint := fun q => (p, q.1)
    have hinj : Function.Injective idx := by
      intro q r hqr
      apply Subtype.ext
      exact congrArg Prod.snd hqr
    have hR0 : rulingDerivative p Q ≠ 0 := by
      intro hzero
      exact hdiv (hzero ▸ dvd_zero Q)
    have hQlines : ∀ q : S, LineContained Q
        (linePoint (idx q).1 (idx q).2 0)
        (lineDirection (idx q).1 (idx q).2) := by
      intro q
      exact (Finset.mem_filter.mp q.2).2
    have hRlines : ∀ q : S, LineContained (rulingDerivative p Q)
        (linePoint (idx q).1 (idx q).2 0)
        (lineDirection (idx q).1 (idx q).2) := by
      intro q
      exact lineContained_rulingDerivative (hQlines q)
    have hbound := card_le_of_lines_in_two_surfaces idx hinj
      hQirr.ne_zero hR0 hQirr hdiv rfl rfl hQlines hRlines
    simpa [S] using hbound

noncomputable def affineFirst (p r : PlanePoint) (s : ℝ) : PlanePoint :=
  (1 - s) • p + s • r

lemma rulingDerivative_affineFirst (p r : PlanePoint) (s : ℝ) (Q : Poly3) :
    rulingDerivative (affineFirst p r s) Q =
      (1 - s) • rulingDerivative p Q + s • rulingDerivative r Q := by
  have hfield (i : Fin 3) :
      rulingPolynomial (affineFirst p r s) i =
        (1 - s) • rulingPolynomial p i + s • rulingPolynomial r i := by
    fin_cases i <;>
      simp [affineFirst, rulingPolynomial, MvPolynomial.smul_eq_C_mul] <;> ring
  rw [rulingDerivative_eq_pderiv, rulingDerivative_eq_pderiv,
    rulingDerivative_eq_pderiv, hfield 0, hfield 1, hfield 2]
  simp only [add_mul, MvPolynomial.smul_eq_C_mul]
  ring

lemma dvd_rulingDerivative_affineFirst {p r : PlanePoint} {Q : Poly3}
    (hp : Q ∣ rulingDerivative p Q) (hr : Q ∣ rulingDerivative r Q) (s : ℝ) :
    Q ∣ rulingDerivative (affineFirst p r s) Q := by
  rw [rulingDerivative_affineFirst]
  exact dvd_add (dvd_smul_of_dvd (1 - s) hp) (dvd_smul_of_dvd s hr)

noncomputable def tangentPolynomial (Q : Poly3) (x : Space3) : Poly3 :=
  ∑ i : Fin 3, MvPolynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv i Q)) *
    (MvPolynomial.X i - MvPolynomial.C (x i))

lemma eval_tangentPolynomial (Q : Poly3) (x y : Space3) :
    MvPolynomial.eval y (tangentPolynomial Q x) =
      ∑ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i Q) * (y i - x i) := by
  simp [tangentPolynomial]

lemma totalDegree_tangentPolynomial_le (Q : Poly3) (x : Space3) :
    (tangentPolynomial Q x).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv i Q))).totalDegree +
        (MvPolynomial.X i - MvPolynomial.C (x i)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 1 := Nat.add_le_add (by simp)
      ((MvPolynomial.totalDegree_sub _ _).trans (by simp))
    _ = 1 := by omega

lemma tangentPolynomial_ne_zero {Q : Poly3} {x : Space3}
    (hx : ¬ SingularAt Q x) : tangentPolynomial Q x ≠ 0 := by
  simp only [SingularAt, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  intro hzero
  let y : Space3 := fun k => x k + if k = j then 1 else 0
  have heval := congrArg (MvPolynomial.eval y) hzero
  rw [eval_tangentPolynomial] at heval
  simp only [map_zero] at heval
  dsimp [y] at heval
  fin_cases j <;> simp at heval <;> exact hj heval

lemma dotGradient_lineDirection_eq_zero {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    ∑ i : Fin 3, MvPolynomial.eval (linePoint p q t) (MvPolynomial.pderiv i Q) *
      lineDirection p q i = 0 := by
  have hDline := lineContained_rulingDerivative hQ
  rw [lineContained_iff] at hDline
  have hD := hDline t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rw [hpoint, rulingDerivative_eq_pderiv] at hD
  simp only [map_add, map_mul, eval_rulingPolynomial] at hD
  rw [rulingVectorField_linePoint] at hD
  simp only [Pi.smul_apply, smul_eq_mul] at hD
  have hfactor :
      (1 + t ^ 2) *
        (∑ i : Fin 3, MvPolynomial.eval (linePoint p q t)
          (MvPolynomial.pderiv i Q) * lineDirection p q i) = 0 := by
    rw [Fin.sum_univ_three]
    linear_combination hD
  exact (mul_eq_zero.mp hfactor).resolve_left <| by
    nlinarith [sq_nonneg t]

lemma lineContained_tangentPolynomial_of_rulingLine
    {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    LineContained (tangentPolynomial Q (linePoint p q t))
      (linePoint p q 0) (lineDirection p q) := by
  rw [lineContained_iff]
  intro u
  rw [eval_tangentPolynomial]
  have hdot := dotGradient_lineDirection_eq_zero hQ t
  rw [Fin.sum_univ_three] at hdot ⊢
  simp [linePoint, lineDirection] at hdot ⊢
  linear_combination (u - t) * hdot

lemma not_dvd_tangentPolynomial {Q : Poly3} {x : Space3}
    (hdeg : 1 < Q.totalDegree) (hnz : tangentPolynomial Q x ≠ 0) :
    ¬ Q ∣ tangentPolynomial Q x := by
  intro hdiv
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hnz
  have htan := totalDegree_tangentPolynomial_le Q x
  omega

lemma affineFirst_injective {p r : PlanePoint} (hpr : p ≠ r) :
    Function.Injective (affineFirst p r) := by
  have hcoord : ∃ j : Fin 2, p j ≠ r j := by
    by_contra h
    push Not at h
    apply hpr
    apply PiLp.ext
    exact h
  obtain ⟨j, hj⟩ := hcoord
  intro s t hst
  have hc := congrArg (fun z : PlanePoint => z j) hst
  simp [affineFirst] at hc
  have hprod : (s - t) * (r j - p j) = 0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hj.symm))

lemma eval_linePoint_eq_zero_of_lineContained {p q : PlanePoint} {Q : Poly3}
    (hQ : LineContained Q (linePoint p q 0) (lineDirection p q)) (t : ℝ) :
    MvPolynomial.eval (linePoint p q t) Q = 0 := by
  rw [lineContained_iff] at hQ
  have h := hQ t
  have hpoint : (fun i => linePoint p q 0 i + t * lineDirection p q i) =
      linePoint p q t := by
    funext i
    fin_cases i <;> simp [linePoint, lineDirection] <;> ring
  rwa [hpoint] at h

lemma eq_of_two_exceptional_of_many_lines
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx₀ : I → PlanePoint × PlanePoint) (hinj₀ : Function.Injective idx₀)
    {Q : Poly3} (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hQlines : ∀ i, LineContained Q
      (linePoint (idx₀ i).1 (idx₀ i).2 0)
      (lineDirection (idx₀ i).1 (idx₀ i).2))
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        Fintype.card I)
    {p r : PlanePoint}
    (hp : Q ∣ rulingDerivative p Q) (hr : Q ∣ rulingDerivative r Q) :
    p = r := by
  by_contra hpr
  obtain ⟨i₀, t₀, hxnsing⟩ :=
    exists_nonsingular_point_of_bound_lt_card idx₀ hinj₀ hQirr hQlines hlarge
  let x : Space3 := linePoint (idx₀ i₀).1 (idx₀ i₀).2 t₀
  have hxQ : MvPolynomial.eval x Q = 0 := by
    exact eval_linePoint_eq_zero_of_lineContained (hQlines i₀) t₀
  have hT0 : tangentPolynomial Q x ≠ 0 := tangentPolynomial_ne_zero hxnsing
  let B := Q.totalDegree * Q.totalDegree *
    (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2)
  let N := B + 1
  let first : Fin N → PlanePoint := fun j => affineFirst p r (j : ℝ)
  let idx : Fin N → PlanePoint × PlanePoint := fun j =>
    (first j, secondIndexThrough (first j) x)
  have hinj : Function.Injective idx := by
    intro j k hjk
    have hfirst : first j = first k := congrArg Prod.fst hjk
    have hcast : (j : ℝ) = (k : ℝ) := by
      exact affineFirst_injective hpr hfirst
    exact Fin.ext (by exact_mod_cast hcast)
  have hdiv (j : Fin N) : Q ∣ rulingDerivative (first j) Q := by
    exact dvd_rulingDerivative_affineFirst hp hr (j : ℝ)
  have hlinesQ : ∀ j, LineContained Q
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) := by
    intro j
    exact lineContained_secondIndexThrough_of_dvd_rulingDerivative (hdiv j) hxQ
  have hlinesT : ∀ j, LineContained (tangentPolynomial Q x)
      (linePoint (idx j).1 (idx j).2 0)
      (lineDirection (idx j).1 (idx j).2) := by
    intro j
    have h := lineContained_tangentPolynomial_of_rulingLine (hlinesQ j) (x 2)
    have hxline : linePoint (idx j).1 (idx j).2 (x 2) = x := by
      exact linePoint_secondIndexThrough (first j) x
    rwa [hxline] at h
  have hnotdiv : ¬ Q ∣ tangentPolynomial Q x :=
    not_dvd_tangentPolynomial hdeg hT0
  have hbound := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hT0 hQirr hnotdiv rfl rfl hlinesQ hlinesT
  have hTdeg : (tangentPolynomial Q x).totalDegree ≤ Q.totalDegree :=
    (totalDegree_tangentPolynomial_le Q x).trans hdeg.le
  have hmono := lineSurfaceBound_mono hTdeg
  have hcontr : Fintype.card (Fin N) ≤ B := hbound.trans hmono
  simpa [N, B] using hcontr

noncomputable def lineIndicesOnSurface (P : Finset PlanePoint) (Q : Poly3) :
    Finset (PlanePoint × PlanePoint) := by
  classical
  exact (P.product P).filter fun pq =>
    LineContained Q (linePoint pq.1 pq.2 0) (lineDirection pq.1 pq.2)

noncomputable def fiberPairs (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3) :
    Finset (PlanePoint × PlanePoint) := by
  classical
  exact (secondIndicesOnSurface P p Q).image fun q => (p, q)

lemma lineIndicesOnSurface_eq_biUnion (P : Finset PlanePoint) (Q : Poly3) :
    lineIndicesOnSurface P Q = P.biUnion fun p => fiberPairs P p Q := by
  classical
  ext pq
  simp [lineIndicesOnSurface, fiberPairs, secondIndicesOnSurface]
  aesop

lemma card_fiberPairs (P : Finset PlanePoint) (p : PlanePoint) (Q : Poly3) :
    (fiberPairs P p Q).card = (secondIndicesOnSurface P p Q).card := by
  classical
  apply Finset.card_image_of_injective
  intro q r hqr
  exact congrArg Prod.snd hqr

lemma card_lineIndicesOnSurface_le_sum_fibers (P : Finset PlanePoint) (Q : Poly3) :
    (lineIndicesOnSurface P Q).card ≤
      ∑ p ∈ P, (secondIndicesOnSurface P p Q).card := by
  rw [lineIndicesOnSurface_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| by
    apply Finset.sum_le_sum
    intro p hp
    rw [card_fiberPairs]

lemma lineSurfaceBound_mono_right {a b c : ℕ} (hbc : b ≤ c) :
    a * b * (2 * (a * b) + a + b + 2) ≤
      a * c * (2 * (a * c) + a + c + 2) := by
  gcongr

noncomputable def rulingFiberBound (Q : Poly3) : ℕ :=
  Q.totalDegree * (Q.totalDegree + 2) *
    (2 * (Q.totalDegree * (Q.totalDegree + 2)) +
      Q.totalDegree + (Q.totalDegree + 2) + 2)

lemma card_secondIndicesOnSurface_le_rulingFiberBound
    (P : Finset PlanePoint) (p : PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hnot : ¬ Q ∣ rulingDerivative p Q) :
    (secondIndicesOnSurface P p Q).card ≤ rulingFiberBound Q := by
  rcases dvd_rulingDerivative_or_card_secondIndicesOnSurface_le P p Q hQirr with
    hdiv | hcard
  · exact (hnot hdiv).elim
  · exact hcard.trans (lineSurfaceBound_mono_right
      (totalDegree_rulingDerivative_le p Q))

noncomputable def exceptionalFirstIndices (P : Finset PlanePoint) (Q : Poly3) :
    Finset PlanePoint := by
  classical
  exact P.filter fun p => Q ∣ rulingDerivative p Q

lemma card_exceptionalFirstIndices_le_one_of_many_lines
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card) :
    (exceptionalFirstIndices P Q).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro p r hp hr
  have hp' := (Finset.mem_filter.mp hp).2
  have hr' := (Finset.mem_filter.mp hr).2
  let S := lineIndicesOnSurface P Q
  let idx : S → PlanePoint × PlanePoint := fun z => z.1
  have hinj : Function.Injective idx := fun a b h => Subtype.ext h
  have hlines : ∀ z : S, LineContained Q
      (linePoint (idx z).1 (idx z).2 0)
      (lineDirection (idx z).1 (idx z).2) := by
    intro z
    exact (Finset.mem_filter.mp z.2).2
  exact eq_of_two_exceptional_of_many_lines idx hinj hQirr hdeg hlines
    (by simpa [S] using hlarge) hp' hr'

lemma card_secondIndicesOnSurface_le_card (P : Finset PlanePoint)
    (p : PlanePoint) (Q : Poly3) :
    (secondIndicesOnSurface P p Q).card ≤ P.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma sum_secondIndicesOnSurface_le_of_many_lines
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card) :
    (∑ p ∈ P, (secondIndicesOnSurface P p Q).card) ≤
      P.card + P.card * rulingFiberBound Q := by
  classical
  let E := exceptionalFirstIndices P Q
  have hE : E.card ≤ 1 :=
    card_exceptionalFirstIndices_le_one_of_many_lines P hQirr hdeg hlarge
  have hexc : (∑ p ∈ E, (secondIndicesOnSurface P p Q).card) ≤ P.card := by
    calc
      _ ≤ E.card • P.card := Finset.sum_le_card_nsmul E _ P.card fun p hp =>
        card_secondIndicesOnSurface_le_card P p Q
      _ ≤ 1 • P.card := by gcongr
      _ = P.card := by simp
  have hnon : (∑ p ∈ P.filter fun p => ¬ Q ∣ rulingDerivative p Q,
      (secondIndicesOnSurface P p Q).card) ≤ P.card * rulingFiberBound Q := by
    calc
      _ ≤ (P.filter fun p => ¬ Q ∣ rulingDerivative p Q).card • rulingFiberBound Q :=
        Finset.sum_le_card_nsmul _ _ _ fun p hp =>
          card_secondIndicesOnSurface_le_rulingFiberBound P p hQirr
            (Finset.mem_filter.mp hp).2
      _ ≤ P.card * rulingFiberBound Q := by
        simpa [nsmul_eq_mul] using Nat.mul_le_mul_right (rulingFiberBound Q)
          (Finset.card_le_card (Finset.filter_subset _ _))
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => Q ∣ rulingDerivative p Q)]
  change (∑ p ∈ E, (secondIndicesOnSurface P p Q).card) +
    (∑ p ∈ P.filter fun p => ¬ Q ∣ rulingDerivative p Q,
      (secondIndicesOnSurface P p Q).card) ≤ _
  omega

lemma card_lineIndicesOnSurface_le_nonLinearIrreducible
    (P : Finset PlanePoint) {Q : Poly3}
    (hQirr : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    (lineIndicesOnSurface P Q).card ≤
      Q.totalDegree * Q.totalDegree *
        (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) +
      P.card + P.card * rulingFiberBound Q := by
  by_cases hlarge : Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) <
        (lineIndicesOnSurface P Q).card
  · exact (card_lineIndicesOnSurface_le_sum_fibers P Q).trans <|
      (sum_secondIndicesOnSurface_le_of_many_lines P hQirr hdeg hlarge).trans
        (by omega)
  · omega

noncomputable def affineNormal (Q : Poly3) : Space3 :=
  fun i => MvPolynomial.coeff (Finsupp.single i 1) Q

noncomputable def affinePolynomial (Q : Poly3) : Poly3 :=
  MvPolynomial.C (MvPolynomial.coeff 0 Q) +
    ∑ i : Fin 3, MvPolynomial.C (affineNormal Q i) * MvPolynomial.X i

lemma eq_affinePolynomial_of_totalDegree_le_one {Q : Poly3}
    (hdeg : Q.totalDegree ≤ 1) : Q = affinePolynomial Q := by
  ext d
  unfold affinePolynomial
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C,
    MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hsum : d.sum (fun _ e => e) = 1
  · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hsum
    have hzero : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single i 1 := Ne.symm hd0
    have hsingleiff (j : Fin 3) :
        Finsupp.single j 1 = Finsupp.single i 1 ↔ j = i :=
      (Finsupp.single_left_injective one_ne_zero).eq_iff
    simp [affineNormal, hsingleiff, hzero]
  · have hcoeff : MvPolynomial.coeff d Q = 0 := by
      by_contra hc
      have hdmem : d ∈ Q.support := MvPolynomial.mem_support_iff.mpr hc
      have hle := (MvPolynomial.le_totalDegree hdmem).trans hdeg
      have hpos : 0 < d.sum (fun _ e => e) := by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
        rw [Finsupp.sum]
        exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
      omega
    have hsingle : ∀ i : Fin 3, d ≠ Finsupp.single i 1 := by
      intro i hi
      apply hsum
      rw [hi]
      simp
    have hsingle' : ∀ i : Fin 3, Finsupp.single i 1 ≠ d :=
      fun i hi => hsingle i hi.symm
    have hzero : (0 : Fin 3 →₀ ℕ) ≠ d := Ne.symm hd0
    simp [affineNormal, hcoeff, hzero, hsingle']

lemma affineNormal_ne_zero_of_totalDegree_eq_one {Q : Poly3}
    (hdeg : Q.totalDegree = 1) : affineNormal Q ≠ 0 := by
  intro hzero
  have hQ := eq_affinePolynomial_of_totalDegree_le_one hdeg.le
  have hz (i : Fin 3) : affineNormal Q i = 0 := congrFun hzero i
  have hQC : Q = MvPolynomial.C (MvPolynomial.coeff 0 Q) := by
    rw [hQ]
    simp [affinePolynomial, hz]
  rw [hQC, MvPolynomial.totalDegree_C] at hdeg
  omega

lemma eval_affinePolynomial (Q : Poly3) (x : Space3) :
    MvPolynomial.eval x (affinePolynomial Q) =
      MvPolynomial.coeff 0 Q + planeValue (affineNormal Q) x := by
  simp [affinePolynomial, affineNormal, planeValue, Fin.sum_univ_three]

lemma lineInAffinePlane_of_lineContained_of_totalDegree_eq_one
    {p q : PlanePoint} {Q : Poly3} (hdeg : Q.totalDegree = 1)
    (hline : LineContained Q (linePoint p q 0) (lineDirection p q)) :
    LineInAffinePlane (affineNormal Q) (-MvPolynomial.coeff 0 Q) p q := by
  intro t
  have hzero := eval_linePoint_eq_zero_of_lineContained hline t
  rw [eq_affinePolynomial_of_totalDegree_le_one hdeg.le,
    eval_affinePolynomial] at hzero
  linarith

lemma card_lineIndicesOnSurface_le_of_totalDegree_eq_one
    (P : Finset PlanePoint) {Q : Poly3} (hdeg : Q.totalDegree = 1) :
    (lineIndicesOnSurface P Q).card ≤ P.card := by
  classical
  have hnormal : affineNormal Q ≠ 0 :=
    affineNormal_ne_zero_of_totalDegree_eq_one hdeg
  have hsub : lineIndicesOnSurface P Q ⊆
      lineIndicesInAffinePlane P (affineNormal Q) (-MvPolynomial.coeff 0 Q) := by
    intro pq hpq
    have hpq' := Finset.mem_filter.mp hpq
    apply Finset.mem_filter.mpr
    refine ⟨hpq'.1, ?_⟩
    exact lineInAffinePlane_of_lineContained_of_totalDegree_eq_one hdeg hpq'.2
  exact (Finset.card_le_card hsub).trans
    (card_lineIndicesInAffinePlane_le P hnormal)

noncomputable def irreducibleSurfaceLineConstant (Q : Poly3) : ℕ :=
  Q.totalDegree * Q.totalDegree *
      (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2) +
    1 + rulingFiberBound Q

lemma card_lineIndicesOnSurface_le_irreducible
    (P : Finset PlanePoint) {Q : Poly3} (hQirr : Irreducible Q) :
    (lineIndicesOnSurface P Q).card ≤
      irreducibleSurfaceLineConstant Q * (P.card + 1) := by
  have hpos := irreducible_totalDegree_pos hQirr
  by_cases hdeg : Q.totalDegree = 1
  · have hline := card_lineIndicesOnSurface_le_of_totalDegree_eq_one P hdeg
    have hconst : 1 ≤ irreducibleSurfaceLineConstant Q := by
      simp [irreducibleSurfaceLineConstant, hdeg, rulingFiberBound]
    exact hline.trans <| calc
      P.card ≤ 1 * (P.card + 1) := by omega
      _ ≤ irreducibleSurfaceLineConstant Q * (P.card + 1) := by gcongr
  · have hdeg' : 1 < Q.totalDegree := by omega
    have hline := card_lineIndicesOnSurface_le_nonLinearIrreducible P hQirr hdeg'
    exact hline.trans <| by
      dsimp [irreducibleSurfaceLineConstant]
      nlinarith [Nat.zero_le (P.card *
        (Q.totalDegree * Q.totalDegree *
          (2 * (Q.totalDegree * Q.totalDegree) + Q.totalDegree + Q.totalDegree + 2))),
        Nat.zero_le (P.card * rulingFiberBound Q)]

end NonClustering

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SurfaceFactors.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Irreducible factors of a partition wall

This file packages unique factorization for three-variable real
polynomials in the form needed by the incidence induction.  In particular,
every line contained in a nonzero wall is contained in one of its
irreducible factors, and a wall of degree `d` has at most `d` distinct
irreducible factors.
-/

namespace SurfaceFactors

open Erdos95.Algebraic Erdos95.ES Erdos95.NonClustering
open UniqueFactorizationMonoid

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- The finset of normalized irreducible factors of a polynomial. -/
noncomputable def irreducibleFactors (Q : Poly3) : Finset Poly3 :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset

theorem mem_irreducibleFactors_iff {Q R : Poly3} :
    R ∈ irreducibleFactors Q ↔
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
  exact Multiset.mem_toFinset

theorem irreducible_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : Irreducible R := by
  exact irreducible_of_normalized_factor R
    (mem_irreducibleFactors_iff.mp hR)

theorem dvd_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : R ∣ Q :=
  dvd_of_mem_normalizedFactors (mem_irreducibleFactors_iff.mp hR)

theorem normalize_eq_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : normalize R = R :=
  normalize_normalized_factor R (mem_irreducibleFactors_iff.mp hR)

theorem not_dvd_of_ne_of_normalized_irreducible
    {Q R : Poly3} (hQirr : Irreducible Q) (hRirr : Irreducible R)
    (hQnorm : normalize Q = Q) (hRnorm : normalize R = R)
    (hne : Q ≠ R) : ¬Q ∣ R := by
  intro hQR
  have hRQ : R ∣ Q := hQirr.dvd_symm hRirr hQR
  apply hne
  simpa only [hQnorm, hRnorm] using normalize_eq_normalize hQR hRQ

theorem totalDegree_le_of_mem_irreducibleFactors {Q R : Poly3}
    (hQ : Q ≠ 0) (hR : R ∈ irreducibleFactors Q) :
    R.totalDegree ≤ Q.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (dvd_of_mem_irreducibleFactors hR) hQ

/-- Every point of a nonzero polynomial wall lies on one of its normalized
irreducible factor walls. -/
theorem exists_factor_eval_eq_zero {Q : Poly3} (hQ : Q ≠ 0)
    {x : Fin 3 → ℝ} (hx : MvPolynomial.eval x Q = 0) :
    ∃ R ∈ irreducibleFactors Q, MvPolynomial.eval x R = 0 := by
  let s := normalizedFactors Q
  have hassoc : Associated Q s.prod := (prod_normalizedFactors hQ).symm
  obtain ⟨A, hA⟩ := hassoc.dvd
  have hprod : MvPolynomial.eval x s.prod = 0 := by
    rw [hA, map_mul, hx, zero_mul]
  let φ : Poly3 →+* ℝ := MvPolynomial.eval₂Hom (RingHom.id ℝ) x
  have hprod' : φ s.prod = 0 := by simpa [φ] using hprod
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hprod'
  obtain ⟨R, hRs, hRzero⟩ := Multiset.mem_map.mp hprod'
  refine ⟨R, mem_irreducibleFactors_iff.mpr ?_, by simpa [φ] using hRzero⟩
  simpa [s] using hRs

private theorem totalDegree_multiset_prod
    (s : Multiset Poly3) (hs : ∀ R ∈ s, R ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      have hR : R ≠ 0 := hs R (by simp)
      have hs0 : s.prod ≠ 0 := Multiset.prod_ne_zero (by
        intro hzero
        exact hs 0 (Multiset.mem_cons_of_mem hzero) rfl)
      rw [Multiset.prod_cons,
        MvPolynomial.totalDegree_mul_of_isDomain hR hs0,
        Multiset.map_cons, Multiset.sum_cons]
      rw [ih (fun T hTs ↦ hs T (by simp [hTs]))]

private theorem sum_toFinset_le_multiset_sum
    (s : Multiset Poly3) (f : Poly3 → ℕ) :
    ∑ R ∈ s.toFinset, f R ≤ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      by_cases hR : R ∈ s.toFinset
      · simpa [hR] using
          ih.trans (Nat.le_add_left (s.map f).sum (f R))
      · simpa [hR] using Nat.add_le_add_left ih (f R)

private theorem multiset_card_le_sum_totalDegree
    (s : Multiset Poly3) (hirr : ∀ R ∈ s, Irreducible R) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      have hRpos : 0 < R.totalDegree :=
        irreducible_totalDegree_pos (hirr R (by simp))
      have his : s.card ≤ (s.map MvPolynomial.totalDegree).sum :=
        ih (fun T hTs ↦ hirr T (by simp [hTs]))
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      omega

private theorem totalDegree_prod_normalizedFactors {Q : Poly3} (hQ : Q ≠ 0) :
    (normalizedFactors Q).prod.totalDegree = Q.totalDegree := by
  have hprod0 : (normalizedFactors Q).prod ≠ 0 :=
    Multiset.prod_ne_zero (by
      intro hzero
      exact (irreducible_of_normalized_factor 0 hzero).ne_zero rfl)
  have hassoc := prod_normalizedFactors hQ
  apply le_antisymm
  · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hassoc.dvd hQ
  · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hassoc.symm.dvd hprod0

/-- A degree-`d` nonzero polynomial has at most `d` distinct irreducible
factors. -/
theorem card_irreducibleFactors_le_totalDegree {Q : Poly3} (hQ : Q ≠ 0) :
    (irreducibleFactors Q).card ≤ Q.totalDegree := by
  calc
    (irreducibleFactors Q).card ≤ (normalizedFactors Q).card := by
      exact Multiset.toFinset_card_le _
    _ ≤ ((normalizedFactors Q).map MvPolynomial.totalDegree).sum :=
      multiset_card_le_sum_totalDegree _
        (fun R hR ↦ irreducible_of_normalized_factor R hR)
    _ = (normalizedFactors Q).prod.totalDegree := by
      symm
      exact totalDegree_multiset_prod _ (fun R hR ↦
        (irreducible_of_normalized_factor R hR).ne_zero)
    _ = Q.totalDegree := totalDegree_prod_normalizedFactors hQ

/-- The sum of the degrees of the distinct normalized irreducible factors is
at most the degree of the original nonzero polynomial. -/
theorem sum_totalDegree_irreducibleFactors_le {Q : Poly3} (hQ : Q ≠ 0) :
    ∑ R ∈ irreducibleFactors Q, R.totalDegree ≤ Q.totalDegree := by
  calc
    ∑ R ∈ irreducibleFactors Q, R.totalDegree ≤
        ((normalizedFactors Q).map MvPolynomial.totalDegree).sum := by
      exact sum_toFinset_le_multiset_sum _ _
    _ = (normalizedFactors Q).prod.totalDegree := by
      symm
      exact totalDegree_multiset_prod _ (fun R hR ↦
        (irreducible_of_normalized_factor R hR).ne_zero)
    _ = Q.totalDegree := totalDegree_prod_normalizedFactors hQ

/-- A degree-only version of the constant in the irreducible-surface
non-clustering theorem. -/
def surfaceLineConstant (d : ℕ) : ℕ :=
  d * d * (2 * (d * d) + d + d + 2) + 1 +
    d * (d + 2) * (2 * (d * (d + 2)) + d + (d + 2) + 2)

theorem irreducibleSurfaceLineConstant_eq (Q : Poly3) :
    irreducibleSurfaceLineConstant Q = surfaceLineConstant Q.totalDegree := by
  rfl

theorem surfaceLineConstant_mono : Monotone surfaceLineConstant := by
  intro a b hab
  unfold surfaceLineConstant
  gcongr

/-- Uniform irreducible-wall occupancy for the Elekes--Sharir family. -/
theorem card_lineIndicesOnSurface_le_degree
    (P : Finset PlanePoint) {Q : Poly3} (hQirr : Irreducible Q)
    {d : ℕ} (hdeg : Q.totalDegree ≤ d) :
    (lineIndicesOnSurface P Q).card ≤
      surfaceLineConstant d * (P.card + 1) := by
  calc
    (lineIndicesOnSurface P Q).card ≤
        irreducibleSurfaceLineConstant Q * (P.card + 1) :=
      card_lineIndicesOnSurface_le_irreducible P hQirr
    _ = surfaceLineConstant Q.totalDegree * (P.card + 1) := by
      rw [irreducibleSurfaceLineConstant_eq]
    _ ≤ surfaceLineConstant d * (P.card + 1) := by
      gcongr
      exact surfaceLineConstant_mono hdeg

end SurfaceFactors

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SignCells.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Sign cells met by an Elekes--Sharir line

A line not contained in the product wall meets at most `degree + 1` strict
sign cells.  The proof assigns to a realized sign pattern the number of wall
roots below a chosen parameter.  Equal ranks force equal signs by the
intermediate value theorem.
-/

open scoped BigOperators

namespace SignCells

open Set Erdos95.Algebraic Erdos95.ES Erdos95.Partitioning

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

private theorem linePoint_eq_base_add (a b : PlanePoint) (t : ℝ) :
    (fun i ↦ linePoint a b 0 i + t * lineDirection a b i) =
      linePoint a b t := by
  funext i
  fin_cases i <;> simp [linePoint, lineDirection] <;> ring

/-- Strict sign patterns realized along the Elekes--Sharir line indexed by
`(a,b)`. -/
noncomputable def lineSignPatterns {J : ℕ} (p : Fin J → Poly3)
    (a b : PlanePoint) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦ ∃ t : ℝ, ∀ j,
    if sign j then 0 < MvPolynomial.eval (linePoint a b t) (p j)
    else MvPolynomial.eval (linePoint a b t) (p j) < 0

theorem mem_lineSignPatterns_iff {J : ℕ} {p : Fin J → Poly3}
    {a b : PlanePoint} {sign : Fin J → Bool} :
    sign ∈ lineSignPatterns p a b ↔ ∃ t : ℝ, ∀ j,
      if sign j then 0 < MvPolynomial.eval (linePoint a b t) (p j)
      else MvPolynomial.eval (linePoint a b t) (p j) < 0 := by
  classical
  simp [lineSignPatterns]

theorem lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
    {J : ℕ} {p : Fin J → Poly3} {a b : PlanePoint}
    {sign : Fin J → Bool} (hsign : sign ∈ lineSignPatterns p a b) :
    lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0 := by
  obtain ⟨t, ht⟩ := mem_lineSignPatterns_iff.mp hsign
  intro hzero
  have hzeroEval := congrArg (fun f : Polynomial ℝ ↦ f.eval t) hzero
  have hwallzero : MvPolynomial.eval (linePoint a b t)
      (partitionPolynomial p) = 0 := by
    simpa [eval_lineRestriction, linePoint_eq_base_add] using hzeroEval
  have hwallne : MvPolynomial.eval (linePoint a b t)
      (partitionPolynomial p) ≠ 0 := by
    rw [eval_partitionPolynomial]
    exact Finset.prod_ne_zero_iff.mpr fun j _hj ↦ by
      have hj := ht j
      split at hj <;> linarith
  exact hwallne hwallzero

private theorem exists_strict_root_between
    (f : Polynomial ℝ) {s t : ℝ} (hst : s < t)
    (hs : 0 < f.eval s) (ht : f.eval t < 0) :
    ∃ u ∈ Ioo s t, f.eval u = 0 := by
  have hzero : (0 : ℝ) ∈ Icc (f.eval t) (f.eval s) := ⟨ht.le, hs.le⟩
  obtain ⟨u, huIcc, hu⟩ :=
    (intermediate_value_Icc' hst.le f.continuous.continuousOn hzero)
  refine ⟨u, ⟨?_, ?_⟩, hu⟩
  · exact lt_of_le_of_ne huIcc.1 fun hus ↦ by
      subst u
      linarith
  · exact lt_of_le_of_ne huIcc.2 fun hut ↦ by
      subst u
      linarith

private theorem exists_strict_root_between_of_opposite
    (f : Polynomial ℝ) {s t : ℝ} (hst : s < t)
    (hopposite : (0 < f.eval s ∧ f.eval t < 0) ∨
      (f.eval s < 0 ∧ 0 < f.eval t)) :
    ∃ u ∈ Ioo s t, f.eval u = 0 := by
  rcases hopposite with h | h
  · exact exists_strict_root_between f hst h.1 h.2
  · obtain ⟨u, hu, hzero⟩ :=
      exists_strict_root_between (-f) hst (by simpa using h.1) (by simpa using h.2)
    exact ⟨u, hu, by simpa using hzero⟩

private theorem card_filter_lt_filter_of_between
    (R : Finset ℝ) {s u t : ℝ} (hsu : s < u) (hut : u < t)
    (huR : u ∈ R) :
    (R.filter fun z ↦ z < s).card < (R.filter fun z ↦ z < t).card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, lt_trans hz'.2 (lt_trans hsu hut)⟩, by
    intro heq
    have huRight : u ∈ R.filter (fun z ↦ z < t) :=
      Finset.mem_filter.mpr ⟨huR, hut⟩
    have huLeft : u ∉ R.filter (fun z ↦ z < s) := by
      simp [not_lt.mpr hsu.le]
    rw [heq] at huLeft
    exact huLeft huRight⟩

private theorem sign_eq_of_equal_rootRank
    {J : ℕ} (p : Fin J → Poly3) (a b : PlanePoint)
    (hwall : lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0)
    {sign₁ sign₂ : Fin J → Bool} {s t : ℝ}
    (hsign₁ : ∀ j, if sign₁ j then
        0 < MvPolynomial.eval (linePoint a b s) (p j)
      else MvPolynomial.eval (linePoint a b s) (p j) < 0)
    (hsign₂ : ∀ j, if sign₂ j then
        0 < MvPolynomial.eval (linePoint a b t) (p j)
      else MvPolynomial.eval (linePoint a b t) (p j) < 0)
    (hrank : (((lineRestriction (partitionPolynomial p)
        (linePoint a b 0) (lineDirection a b)).roots.toFinset.filter
          fun z ↦ z < s).card) =
      (((lineRestriction (partitionPolynomial p)
        (linePoint a b 0) (lineDirection a b)).roots.toFinset.filter
          fun z ↦ z < t).card)) :
    sign₁ = sign₂ := by
  classical
  apply funext
  intro j
  by_contra hne
  have hopp :
      (0 < MvPolynomial.eval (linePoint a b s) (p j) ∧
          MvPolynomial.eval (linePoint a b t) (p j) < 0) ∨
        (MvPolynomial.eval (linePoint a b s) (p j) < 0 ∧
          0 < MvPolynomial.eval (linePoint a b t) (p j)) := by
    cases h₁ : sign₁ j <;> cases h₂ : sign₂ j
    · exact (hne (by simp [h₁, h₂])).elim
    · exact Or.inr ⟨by simpa [h₁] using hsign₁ j,
          by simpa [h₂] using hsign₂ j⟩
    · exact Or.inl ⟨by simpa [h₁] using hsign₁ j,
          by simpa [h₂] using hsign₂ j⟩
    · exact (hne (by simp [h₁, h₂])).elim
  rcases lt_trichotomy s t with hst | rfl | hts
  · let f := lineRestriction (p j) (linePoint a b 0) (lineDirection a b)
    have hsEval : f.eval s = MvPolynomial.eval (linePoint a b s) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have htEval : f.eval t = MvPolynomial.eval (linePoint a b t) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    obtain ⟨u, hu, hfu⟩ := exists_strict_root_between_of_opposite f hst (by
      simpa [hsEval, htEval] using hopp)
    let wall := lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b)
    have hwall' : wall ≠ 0 := hwall
    have hwallu : wall.eval u = 0 := by
      rw [eval_lineRestriction]
      rw [eval_partitionPolynomial]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simpa [f, eval_lineRestriction, linePoint] using hfu
    have huRoot : u ∈ wall.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hwall').mpr hwallu)
    have hlt := card_filter_lt_filter_of_between wall.roots.toFinset
      hu.1 hu.2 huRoot
    exact (ne_of_lt hlt) hrank
  · have hsame := hsign₁ j
    have hsame' := hsign₂ j
    rcases hopp with h | h <;> linarith
  · let f := lineRestriction (p j) (linePoint a b 0) (lineDirection a b)
    have hsEval : f.eval s = MvPolynomial.eval (linePoint a b s) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have htEval : f.eval t = MvPolynomial.eval (linePoint a b t) (p j) := by
      rw [show f = lineRestriction (p j) (linePoint a b 0)
        (lineDirection a b) by rfl, eval_lineRestriction,
        linePoint_eq_base_add]
    have hopp' :
        (0 < f.eval t ∧ f.eval s < 0) ∨ (f.eval t < 0 ∧ 0 < f.eval s) := by
      rcases hopp with h | h
      · exact Or.inr ⟨by simpa [htEval] using h.2, by simpa [hsEval] using h.1⟩
      · exact Or.inl ⟨by simpa [htEval] using h.2, by simpa [hsEval] using h.1⟩
    obtain ⟨u, hu, hfu⟩ := exists_strict_root_between_of_opposite f hts hopp'
    let wall := lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b)
    have hwall' : wall ≠ 0 := hwall
    have hwallu : wall.eval u = 0 := by
      rw [eval_lineRestriction]
      rw [eval_partitionPolynomial]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simpa [f, eval_lineRestriction, linePoint] using hfu
    have huRoot : u ∈ wall.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hwall').mpr hwallu)
    have hlt := card_filter_lt_filter_of_between wall.roots.toFinset
      hu.1 hu.2 huRoot
    exact (ne_of_gt hlt) hrank

/-- A line not contained in the product wall realizes at most one more
strict sign pattern than the wall degree. -/
theorem card_lineSignPatterns_le {J : ℕ} (p : Fin J → Poly3)
    (a b : PlanePoint)
    (hwall : lineRestriction (partitionPolynomial p)
      (linePoint a b 0) (lineDirection a b) ≠ 0) :
    (lineSignPatterns p a b).card ≤
      (partitionPolynomial p).totalDegree + 1 := by
  classical
  let wall := lineRestriction (partitionPolynomial p)
    (linePoint a b 0) (lineDirection a b)
  let parameter : (Fin J → Bool) → ℝ := fun sign ↦
    if h : sign ∈ lineSignPatterns p a b then
      Classical.choose (mem_lineSignPatterns_iff.mp h)
    else 0
  let rank : (Fin J → Bool) → ℕ := fun sign ↦
    (wall.roots.toFinset.filter fun z ↦ z < parameter sign).card
  have hmaps : Set.MapsTo rank (lineSignPatterns p a b)
      (Finset.range (wall.roots.toFinset.card + 1)) := by
    intro sign hsign
    change rank sign ∈ Finset.range (wall.roots.toFinset.card + 1)
    rw [Finset.mem_range]
    dsimp [rank]
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  have hinj : Set.InjOn rank (lineSignPatterns p a b) := by
    intro sign₁ hsign₁ sign₂ hsign₂ hrank
    change sign₁ ∈ lineSignPatterns p a b at hsign₁
    change sign₂ ∈ lineSignPatterns p a b at hsign₂
    have hparam₁ : parameter sign₁ =
        Classical.choose (mem_lineSignPatterns_iff.mp hsign₁) := by
      dsimp [parameter]
      rw [dif_pos hsign₁]
    have hparam₂ : parameter sign₂ =
        Classical.choose (mem_lineSignPatterns_iff.mp hsign₂) := by
      dsimp [parameter]
      rw [dif_pos hsign₂]
    have hw₁ : ∀ j, if sign₁ j then
        0 < MvPolynomial.eval (linePoint a b (parameter sign₁)) (p j)
      else MvPolynomial.eval (linePoint a b (parameter sign₁)) (p j) < 0 := by
      rw [hparam₁]
      exact Classical.choose_spec (mem_lineSignPatterns_iff.mp hsign₁)
    have hw₂ : ∀ j, if sign₂ j then
        0 < MvPolynomial.eval (linePoint a b (parameter sign₂)) (p j)
      else MvPolynomial.eval (linePoint a b (parameter sign₂)) (p j) < 0 := by
      rw [hparam₂]
      exact Classical.choose_spec (mem_lineSignPatterns_iff.mp hsign₂)
    apply sign_eq_of_equal_rootRank p a b hwall hw₁ hw₂
    simpa [rank, wall] using hrank
  calc
    (lineSignPatterns p a b).card ≤
        (Finset.range (wall.roots.toFinset.card + 1)).card :=
      Finset.card_le_card_of_injOn rank hmaps hinj
    _ = wall.roots.toFinset.card + 1 := by simp
    _ ≤ wall.natDegree + 1 := by
      gcongr
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' wall)
    _ ≤ (partitionPolynomial p).totalDegree + 1 := by
      gcongr
      exact natDegree_lineRestriction _ _ _

end SignCells

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/CellLines.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Lines entering strict polynomial sign cells

This file proves the finite line--cell incidence estimate used in the
low-degree partitioning induction.  A line contained in the product wall
enters no strict cell; every other line enters at most `degree + 1` cells.
-/

open scoped BigOperators

namespace CellLines

open Erdos95.Algebraic Erdos95.ES Erdos95.Partitioning Erdos95.SignCells

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- The lines of `L` which pass through a selected point in a strict sign
cell. -/
noncomputable def cellLines (L : Finset LineIndex)
    (S : Finset Space3) {J : ℕ} (p : Fin J → Poly3)
    (sign : Fin J → Bool) : Finset LineIndex := by
  classical
  exact L.filter fun l ↦ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x

theorem mem_cellLines_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {sign : Fin J → Bool}
    {l : LineIndex} :
    l ∈ cellLines L S p sign ↔
      l ∈ L ∧ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x := by
  classical
  simp [cellLines]

theorem sign_mem_lineSignPatterns_of_mem_cellLines
    {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {sign : Fin J → Bool}
    {l : LineIndex} (hl : l ∈ cellLines L S p sign) :
    sign ∈ lineSignPatterns p l.1 l.2 := by
  obtain ⟨_hlL, x, hxcell, t, rfl⟩ := mem_cellLines_iff.mp hl
  apply mem_lineSignPatterns_iff.mpr
  refine ⟨t, ?_⟩
  exact (mem_signCell_iff.mp hxcell).2

/-- The finite relation of a sign cell and a line entering it. -/
noncomputable def cellLineIncidences (L : Finset LineIndex)
    (S : Finset Space3) {J : ℕ} (p : Fin J → Poly3) :
    Finset (Σ _sign : (Fin J → Bool), LineIndex) := by
  classical
  exact (Finset.univ : Finset (Fin J → Bool)).sigma
    (fun sign ↦ cellLines L S p sign)

/-- The same incidence relation, with the order reversed and enlarged to
all sign patterns realized by each line. -/
noncomputable def realizedLinePatterns (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly3) :
    Finset (Σ _l : LineIndex, (Fin J → Bool)) := by
  classical
  exact L.sigma fun l ↦ lineSignPatterns p l.1 l.2

theorem card_cellLineIncidences_le_realizedLinePatterns
    (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) :
    (cellLineIncidences L S p).card ≤ (realizedLinePatterns L p).card := by
  classical
  let swap : (Σ _sign : (Fin J → Bool), LineIndex) →
      (Σ _l : LineIndex, (Fin J → Bool)) := fun z ↦ ⟨z.2, z.1⟩
  apply Finset.card_le_card_of_injOn swap
  · intro z hz
    rcases z with ⟨sign, l⟩
    change ⟨sign, l⟩ ∈ cellLineIncidences L S p at hz
    rw [cellLineIncidences, Finset.mem_sigma] at hz
    have hz' : l ∈ cellLines L S p sign := hz.2
    change ⟨l, sign⟩ ∈ realizedLinePatterns L p
    simp only [realizedLinePatterns, Finset.mem_sigma]
    exact ⟨(mem_cellLines_iff.mp hz').1,
      sign_mem_lineSignPatterns_of_mem_cellLines hz'⟩
  · intro z hz w hw hzw
    rcases z with ⟨sign, l⟩
    rcases w with ⟨sign', l'⟩
    simp only [swap] at hzw
    injection hzw
    subst l'
    subst sign'
    rfl

theorem card_realizedLinePatterns_le
    (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly3) :
    (realizedLinePatterns L p).card ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  classical
  rw [realizedLinePatterns, Finset.card_sigma]
  calc
    (∑ l ∈ L, (lineSignPatterns p l.1 l.2).card) ≤
        ∑ _l ∈ L, ((partitionPolynomial p).totalDegree + 1) := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases hpat : (lineSignPatterns p l.1 l.2).Nonempty
      · obtain ⟨sign, hsign⟩ := hpat
        exact card_lineSignPatterns_le p l.1 l.2
          (lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
            hsign)
      · simp only [Finset.not_nonempty_iff_eq_empty] at hpat
        rw [hpat]
        simp
    _ = L.card * ((partitionPolynomial p).totalDegree + 1) := by simp

/-- Sum form of the line--cell incidence bound. -/
theorem sum_card_cellLines_le
    (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) :
    (∑ sign : Fin J → Bool, (cellLines L S p sign).card) ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  rw [← Finset.card_sigma]
  change (cellLineIncidences L S p).card ≤ _
  exact (card_cellLineIncidences_le_realizedLinePatterns L S p).trans
    (card_realizedLinePatterns_le L p)

end CellLines

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/LineFamilies.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite families of Elekes--Sharir lines

The incidence induction is most naturally stated for an arbitrary subfamily
of the full `P × P` line family.  This file supplies the corresponding finite
rich-point and algebraic-surface definitions.
-/

namespace LineFamilies

open Erdos95.Algebraic Erdos95.ES

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Ordered pairs of distinct intersecting lines from `L`. -/
noncomputable def intersectingPairs (L : Finset LineIndex) :
    Finset (LineIndex × LineIndex) := by
  classical
  exact (L.product L).filter fun z ↦
    z.1 ≠ z.2 ∧ Intersects z.1.1 z.1.2 z.2.1 z.2.2

/-- The unique intersection point of an incident ordered pair. -/
noncomputable def pairIntersection (z : LineIndex × LineIndex) : Space3 := by
  classical
  exact if h : Intersects z.1.1 z.1.2 z.2.1 z.2.2 then
    Classical.choose h
  else 0

theorem pairIntersection_on_first {z : LineIndex × LineIndex}
    (hz : Intersects z.1.1 z.1.2 z.2.1 z.2.2) :
    OnLine z.1.1 z.1.2 (pairIntersection z) := by
  classical
  simp only [pairIntersection, dif_pos hz]
  exact (Classical.choose_spec hz).1

theorem pairIntersection_on_second {z : LineIndex × LineIndex}
    (hz : Intersects z.1.1 z.1.2 z.2.1 z.2.2) :
    OnLine z.2.1 z.2.2 (pairIntersection z) := by
  classical
  simp only [pairIntersection, dif_pos hz]
  exact (Classical.choose_spec hz).2

/-- Lines of a subfamily passing through `x`. -/
noncomputable def linesThrough (L : Finset LineIndex) (x : Space3) :
    Finset LineIndex := by
  classical
  exact L.filter fun l ↦ OnLine l.1 l.2 x

theorem mem_linesThrough_iff {L : Finset LineIndex} {x : Space3}
    {l : LineIndex} :
    l ∈ linesThrough L x ↔ l ∈ L ∧ OnLine l.1 l.2 x := by
  classical
  simp [linesThrough]

theorem linesThrough_mono {L M : Finset LineIndex} (hLM : L ⊆ M)
    (x : Space3) : linesThrough L x ⊆ linesThrough M x := by
  intro l hl
  exact mem_linesThrough_iff.mpr
    ⟨hLM (mem_linesThrough_iff.mp hl).1, (mem_linesThrough_iff.mp hl).2⟩

theorem card_linesThrough_le (L : Finset LineIndex) (x : Space3) :
    (linesThrough L x).card ≤ L.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Actual intersection points of distinct lines in `L`. -/
noncomputable def intersectionPoints (L : Finset LineIndex) : Finset Space3 :=
  (intersectingPairs L).image pairIntersection

/-- Intersection points incident to at least `r` lines of `L`. -/
noncomputable def richPoints (L : Finset LineIndex) (r : ℕ) : Finset Space3 := by
  classical
  exact (intersectionPoints L).filter fun x ↦ r ≤ (linesThrough L x).card

theorem mem_richPoints_iff {L : Finset LineIndex} {r : ℕ} {x : Space3} :
    x ∈ richPoints L r ↔
      x ∈ intersectionPoints L ∧ r ≤ (linesThrough L x).card := by
  classical
  simp [richPoints]

theorem richPoints_mono_family {L M : Finset LineIndex} (hLM : L ⊆ M)
    (r : ℕ) : richPoints L r ⊆ richPoints M r := by
  classical
  intro x hx
  have hxdata := mem_richPoints_iff.mp hx
  have hcard := Finset.card_le_card (linesThrough_mono hLM x)
  have hxinter : x ∈ intersectionPoints M := by
    unfold intersectionPoints at hxdata ⊢
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hxdata.1
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    unfold intersectingPairs at hz ⊢
    have hzdata := Finset.mem_filter.mp hz
    have hzmem := Finset.mem_product.mp hzdata.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hLM hzmem.1, hLM hzmem.2⟩, hzdata.2⟩
  exact mem_richPoints_iff.mpr ⟨hxinter, hxdata.2.trans hcard⟩

theorem pairIntersection_fiber (L : Finset LineIndex) (x : Space3) :
    (intersectingPairs L).filter (fun z ↦ pairIntersection z = x) =
      (linesThrough L x).offDiag := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨hz, hzx⟩
    have hzdata := Finset.mem_filter.mp hz
    have hzmem := Finset.mem_product.mp hzdata.1
    refine ⟨mem_linesThrough_iff.mpr ⟨hzmem.1, ?_⟩,
      mem_linesThrough_iff.mpr ⟨hzmem.2, ?_⟩, hzdata.2.1⟩
    · rw [← hzx]
      exact pairIntersection_on_first hzdata.2.2
    · rw [← hzx]
      exact pairIntersection_on_second hzdata.2.2
  · rintro ⟨hz₁, hz₂, hne⟩
    have hint : Intersects z.1.1 z.1.2 z.2.1 z.2.2 :=
      ⟨x, (mem_linesThrough_iff.mp hz₁).2,
        (mem_linesThrough_iff.mp hz₂).2⟩
    have hzmem : z ∈ intersectingPairs L := by
      unfold intersectingPairs
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_linesThrough_iff.mp hz₁).1,
          (mem_linesThrough_iff.mp hz₂).1⟩, hne, hint⟩
    refine ⟨hzmem, ?_⟩
    exact intersection_unique hne
      (pairIntersection_on_first hint) (pairIntersection_on_second hint)
      (mem_linesThrough_iff.mp hz₁).2 (mem_linesThrough_iff.mp hz₂).2

theorem card_intersectingPairs_eq_sum (L : Finset LineIndex) :
    (intersectingPairs L).card =
      ∑ x ∈ intersectionPoints L,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_image pairIntersection (intersectingPairs L)]
  change _ = ∑ x ∈ (intersectingPairs L).image pairIntersection, _
  apply Finset.sum_congr rfl
  intro x hx
  rw [pairIntersection_fiber, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Each `r`-rich point accounts for at least `r(r-1)` ordered pairs. -/
theorem richness_mul_pred_mul_card_le_intersectingPairs
    (L : Finset LineIndex) (r : ℕ) :
    r * (r - 1) * (richPoints L r).card ≤ (intersectingPairs L).card := by
  classical
  rw [card_intersectingPairs_eq_sum]
  calc
    r * (r - 1) * (richPoints L r).card =
        ∑ x ∈ richPoints L r, r * (r - 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ richPoints L r,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hr := (mem_richPoints_iff.mp hx).2
      exact Nat.mul_le_mul hr (Nat.sub_le_sub_right hr 1)
    _ ≤ ∑ x ∈ intersectionPoints L,
        (linesThrough L x).card * ((linesThrough L x).card - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro x hx hnot
        omega

theorem card_intersectingPairs_le_sq (L : Finset LineIndex) :
    (intersectingPairs L).card ≤ L.card ^ 2 := by
  classical
  calc
    (intersectingPairs L).card ≤ (L.product L).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = L.card ^ 2 := by simp [pow_two]

/-- The elementary universal rich-point estimate. -/
theorem richness_mul_pred_mul_card_le_sq (L : Finset LineIndex) (r : ℕ) :
    r * (r - 1) * (richPoints L r).card ≤ L.card ^ 2 :=
  (richness_mul_pred_mul_card_le_intersectingPairs L r).trans
    (card_intersectingPairs_le_sq L)

/-- Lines of `L` contained in the algebraic surface `Z(Q)`. -/
noncomputable def surfaceLines (L : Finset LineIndex) (Q : Poly3) :
    Finset LineIndex := by
  classical
  exact L.filter fun l ↦ LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem mem_surfaceLines_iff {L : Finset LineIndex} {Q : Poly3}
    {l : LineIndex} :
    l ∈ surfaceLines L Q ↔ l ∈ L ∧ LineContained Q
      (linePoint l.1 l.2 0) (lineDirection l.1 l.2) := by
  classical
  simp [surfaceLines]

theorem surfaceLines_subset (L : Finset LineIndex) (Q : Poly3) :
    surfaceLines L Q ⊆ L := by
  classical
  exact Finset.filter_subset _ _

theorem surfaceLines_mono {L M : Finset LineIndex} (hLM : L ⊆ M)
    (Q : Poly3) : surfaceLines L Q ⊆ surfaceLines M Q := by
  classical
  intro l hl
  have h := mem_surfaceLines_iff.mp hl
  exact mem_surfaceLines_iff.mpr ⟨hLM h.1, h.2⟩

end LineFamilies

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/WallIncidences.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Incidences with a partition wall

For a polynomial `Q`, every line not contained in `Z(Q)` contributes at
most `degree Q` incidences with any finite point set on the wall.  Combined
with richness, this bounds wall points which are not already rich in the
subfamily contained in an irreducible wall component.
-/

open scoped BigOperators

namespace WallIncidences

open Erdos95.Algebraic Erdos95.ES Erdos95.LineFamilies

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

private theorem linePoint_eq_base_add (a b : PlanePoint) (t : ℝ) :
    (fun i ↦ linePoint a b 0 i + t * lineDirection a b i) =
      linePoint a b t := by
  funext i
  fin_cases i <;> simp [linePoint, lineDirection] <;> ring

theorem mem_intersectionPoints_of_two_lines
    {L : Finset LineIndex} {x : Space3} {l m : LineIndex}
    (hl : l ∈ Erdos95.LineFamilies.linesThrough L x) (hm : m ∈ Erdos95.LineFamilies.linesThrough L x)
    (hlm : l ≠ m) : x ∈ Erdos95.LineFamilies.intersectionPoints L := by
  classical
  unfold Erdos95.LineFamilies.intersectionPoints
  apply Finset.mem_image.mpr
  let z : LineIndex × LineIndex := (l, m)
  have hint : Intersects l.1 l.2 m.1 m.2 :=
    ⟨x, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2⟩
  have hz : z ∈ intersectingPairs L := by
    unfold intersectingPairs z
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).1, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).1⟩,
      hlm, hint⟩
  refine ⟨z, hz, ?_⟩
  exact intersection_unique (p := l.1) (q := l.2) (r := m.1) (s := m.2)
    hlm (pairIntersection_on_first (z := z) hint)
    (pairIntersection_on_second (z := z) hint)
    (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2 (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2

/-- Two incident lines suffice to put a point into the finite intersection
point set. -/
theorem mem_richPoints_of_two_le_card_linesThrough
    {L : Finset LineIndex} {x : Space3} {r : ℕ} (hr : 2 ≤ r)
    (hx : r ≤ (Erdos95.LineFamilies.linesThrough L x).card) : x ∈ richPoints L r := by
  classical
  have hone : 1 < (Erdos95.LineFamilies.linesThrough L x).card := lt_of_lt_of_le (by omega) hx
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp hone
  exact mem_richPoints_iff.mpr
    ⟨mem_intersectionPoints_of_two_lines hl hm hlm, hx⟩

/-- Lines through `x` which are not contained in `Z(Q)`. -/
noncomputable def externalLinesThrough (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) : Finset LineIndex := by
  classical
  exact (Erdos95.LineFamilies.linesThrough L x).filter fun l ↦ ¬LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

/-- Lines through `x` which are contained in `Z(Q)`. -/
noncomputable def internalLinesThrough (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) : Finset LineIndex := by
  classical
  exact (Erdos95.LineFamilies.linesThrough L x).filter fun l ↦ LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem linesThrough_surfaceLines (L : Finset LineIndex) (Q : Poly3)
    (x : Space3) :
    Erdos95.LineFamilies.linesThrough (surfaceLines L Q) x =
      internalLinesThrough L Q x := by
  classical
  ext l
  simp only [Erdos95.LineFamilies.mem_linesThrough_iff, mem_surfaceLines_iff,
    internalLinesThrough, Finset.mem_filter]
  tauto

theorem card_external_add_card_surface (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) :
    (externalLinesThrough L Q x).card +
      (Erdos95.LineFamilies.linesThrough (surfaceLines L Q) x).card =
        (Erdos95.LineFamilies.linesThrough L x).card := by
  classical
  rw [linesThrough_surfaceLines]
  unfold externalLinesThrough internalLinesThrough
  simpa only [not_not] using
    (Finset.card_filter_add_card_filter_not
      (s := Erdos95.LineFamilies.linesThrough L x)
      (fun l ↦ ¬LineContained Q
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2)))

/-- The sharp integral form of the richness loss.  Since failure of
`r'`-richness means that at most `r' - 1` contained lines pass through the
point, the number of external lines is at least `r - (r' - 1)`. -/
theorem richness_strict_loss_le_card_external
    {L : Finset LineIndex} {Q : Poly3} {x : Space3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hxrich : r ≤ (Erdos95.LineFamilies.linesThrough L x).card)
    (hxnot : x ∉ richPoints (surfaceLines L Q) r') :
    r - (r' - 1) ≤ (externalLinesThrough L Q x).card := by
  have hcontained : (Erdos95.LineFamilies.linesThrough (surfaceLines L Q) x).card < r' := by
    by_contra hnot
    have hge : r' ≤ (Erdos95.LineFamilies.linesThrough (surfaceLines L Q) x).card := by omega
    exact hxnot (mem_richPoints_of_two_le_card_linesThrough hr' hge)
  have hsum := card_external_add_card_surface L Q x
  omega

/-- Points of `S` lying on both a fixed line and the surface `Z(Q)`. -/
noncomputable def pointsOnLineSurface (S : Finset Space3)
    (l : LineIndex) (Q : Poly3) : Finset Space3 := by
  classical
  exact S.filter fun x ↦
    OnLine l.1 l.2 x ∧ MvPolynomial.eval x Q = 0

theorem card_pointsOnLineSurface_le
    (S : Finset Space3) (l : LineIndex) (Q : Poly3)
    (hline : ¬LineContained Q (linePoint l.1 l.2 0)
      (lineDirection l.1 l.2)) :
    (pointsOnLineSurface S l Q).card ≤ Q.totalDegree := by
  classical
  let parameter : Space3 → ℝ := fun x ↦ x 2
  let T := (pointsOnLineSurface S l Q).image parameter
  have hinj : Set.InjOn parameter (pointsOnLineSurface S l Q) := by
    intro x hx y hy hxy
    have hxline := (Finset.mem_filter.mp hx).2.1
    have hyline := (Finset.mem_filter.mp hy).2.1
    obtain ⟨s, rfl⟩ := hxline
    obtain ⟨t, rfl⟩ := hyline
    have hst : s = t := by simpa [parameter, linePoint] using hxy
    rw [hst]
  have hcard : T.card = (pointsOnLineSurface S l Q).card :=
    Finset.card_image_iff.mpr hinj
  have hzero : ∀ t ∈ T,
      MvPolynomial.eval
        (fun i ↦ linePoint l.1 l.2 0 i + t * lineDirection l.1 l.2 i) Q = 0 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hxdata := Finset.mem_filter.mp hx
    obtain ⟨s, rfl⟩ := hxdata.2.1
    have hs : linePoint l.1 l.2 s 2 = s := by simp [linePoint]
    simp only [parameter, hs]
    rw [linePoint_eq_base_add]
    exact hxdata.2.2
  rw [← hcard]
  exact card_line_zeros_le_totalDegree Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2) T
    (by
      intro hzero
      exact hline hzero) hzero

/-- External line incidences of wall points. -/
noncomputable def externalIncidences (S : Finset Space3)
    (L : Finset LineIndex) (Q : Poly3) :
    Finset (Σ _x : Space3, LineIndex) := by
  classical
  exact S.sigma fun x ↦ externalLinesThrough L Q x

theorem card_externalIncidences_le (S : Finset Space3)
    (L : Finset LineIndex) (Q : Poly3)
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (externalIncidences S L Q).card ≤ Q.totalDegree * L.card := by
  classical
  rw [externalIncidences, Finset.card_sigma]
  have hrewrite :
      (∑ x ∈ S, (externalLinesThrough L Q x).card) =
        ∑ x ∈ S, ∑ l ∈ L,
          if OnLine l.1 l.2 x ∧ ¬LineContained Q
              (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
          then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [externalLinesThrough, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Erdos95.LineFamilies.linesThrough, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hon : OnLine l.1 l.2 x <;>
      by_cases hext : ¬LineContained Q (linePoint l.1 l.2 0)
        (lineDirection l.1 l.2) <;> simp [hon, hext]
  rw [hrewrite, Finset.sum_comm]
  calc
    (∑ l ∈ L, ∑ x ∈ S,
        if OnLine l.1 l.2 x ∧ ¬LineContained Q
            (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
        then 1 else 0) ≤
      ∑ _l ∈ L, Q.totalDegree := by
        apply Finset.sum_le_sum
        intro l hl
        by_cases hline : LineContained Q (linePoint l.1 l.2 0)
            (lineDirection l.1 l.2)
        · simp [hline]
        · have hsum : (∑ x ∈ S,
              if OnLine l.1 l.2 x ∧ ¬LineContained Q
                  (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
              then 1 else 0) = (pointsOnLineSurface S l Q).card := by
            rw [pointsOnLineSurface, Finset.card_eq_sum_ones,
              Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            simp [hline, hwall x hx]
          rw [hsum]
          exact card_pointsOnLineSurface_le S l Q hline
    _ = Q.totalDegree * L.card := by simp [Nat.mul_comm]

theorem strict_loss_mul_card_le_card_externalIncidences
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (Erdos95.LineFamilies.linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r') :
    (r - (r' - 1)) * S.card ≤ (externalIncidences S L Q).card := by
  rw [externalIncidences, Finset.card_sigma]
  calc
    (r - (r' - 1)) * S.card = ∑ _x ∈ S, (r - (r' - 1)) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, (externalLinesThrough L Q x).card :=
      Finset.sum_le_sum fun x hx ↦
        richness_strict_loss_le_card_external hr' (hSrich x hx) (hSnot x hx)

/-- Sharp denominator-free wall estimate, valid also for `r = r' = 2`. -/
theorem richness_strict_loss_mul_card_le_degree_mul_lines
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (Erdos95.LineFamilies.linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r')
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (r - (r' - 1)) * S.card ≤ Q.totalDegree * L.card :=
  (strict_loss_mul_card_le_card_externalIncidences hr' hSrich hSnot).trans
    (card_externalIncidences_le S L Q hwall)

end WallIncidences

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SurfaceCollections.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Collections of low-degree irreducible surfaces

Distinct normalized irreducible surfaces of degree at most `D` have only a
bounded number of common Elekes--Sharir lines.  This is the finite overlap
input in Guth's pruning argument.
-/

namespace SurfaceCollections

open Erdos95.Algebraic Erdos95.ES Erdos95.Hilbert
open Erdos95.LineFamilies Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- A degree-only upper bound for lines common to two distinct normalized
irreducible surfaces. -/
def commonLineConstant (D : ℕ) : ℕ :=
  D * D * (2 * (D * D) + D + D + 2)

/-- Lines of `L` contained in both surfaces. -/
noncomputable def commonSurfaceLines (L : Finset LineIndex)
    (Q R : Poly3) : Finset LineIndex := by
  classical
  exact (surfaceLines L Q).filter fun l ↦ LineContained R
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem mem_commonSurfaceLines_iff {L : Finset LineIndex}
    {Q R : Poly3} {l : LineIndex} :
    l ∈ commonSurfaceLines L Q R ↔
      l ∈ L ∧ LineContained Q
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2) ∧
      LineContained R
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2) := by
  classical
  simp [commonSurfaceLines, mem_surfaceLines_iff]
  tauto

theorem card_commonSurfaceLines_le
    (L : Finset LineIndex) {Q R : Poly3} {D : ℕ}
    (hQirr : Irreducible Q) (hRirr : Irreducible R)
    (hQnorm : normalize Q = Q) (hRnorm : normalize R = R)
    (hQR : Q ≠ R) (hQdeg : Q.totalDegree ≤ D)
    (hRdeg : R.totalDegree ≤ D) :
    (commonSurfaceLines L Q R).card ≤ commonLineConstant D := by
  classical
  let I := {l // l ∈ commonSurfaceLines L Q R}
  let idx : I → LineIndex := fun l ↦ l.1
  have hinj : Function.Injective idx := Subtype.val_injective
  have hI := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hRirr.ne_zero hQirr
    (not_dvd_of_ne_of_normalized_irreducible hQirr hRirr
      hQnorm hRnorm hQR)
    rfl rfl
    (fun i ↦ (mem_commonSurfaceLines_iff.mp i.2).2.1)
    (fun i ↦ (mem_commonSurfaceLines_iff.mp i.2).2.2)
  have hcardI : Fintype.card I = (commonSurfaceLines L Q R).card := by
    simp [I]
  rw [hcardI] at hI
  exact hI.trans <| by
    unfold commonLineConstant
    gcongr

end SurfaceCollections

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/RichPointCombinatorics.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Combinatorics of rich Elekes--Sharir line points

This file contains the elementary large-richness estimate used in Guth's
low-degree induction.  Its only geometric input is that two distinct points
of parameter space lie on at most one indexed Elekes--Sharir line.
-/

namespace RichPointCombinatorics

open Erdos95.ES Erdos95.LineFamilies Erdos95.SetFamilyBounds

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Two distinct points of parameter space share at most one line of an
Elekes--Sharir subfamily. -/
theorem card_common_linesThrough_le_one (L : Finset LineIndex)
    {x y : Space3} (hxy : x ≠ y) :
    ((Erdos95.LineFamilies.linesThrough L x).filter fun l ↦ l ∈ Erdos95.LineFamilies.linesThrough L y).card ≤ 1 := by
  classical
  by_contra hcard
  have hone : 1 < ((Erdos95.LineFamilies.linesThrough L x).filter
      fun l ↦ l ∈ Erdos95.LineFamilies.linesThrough L y).card := by omega
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp hone
  have hlx : OnLine l.1 l.2 x :=
    (Erdos95.LineFamilies.mem_linesThrough_iff.mp (Finset.mem_filter.mp hl).1).2
  have hly : OnLine l.1 l.2 y :=
    (Erdos95.LineFamilies.mem_linesThrough_iff.mp (Finset.mem_filter.mp hl).2).2
  have hmx : OnLine m.1 m.2 x :=
    (Erdos95.LineFamilies.mem_linesThrough_iff.mp (Finset.mem_filter.mp hm).1).2
  have hmy : OnLine m.1 m.2 y :=
    (Erdos95.LineFamilies.mem_linesThrough_iff.mp (Finset.mem_filter.mp hm).2).2
  exact hxy (intersection_unique hlm hlx hmx hly hmy)

/-- Proposition 2.2 of Guth's low-degree paper, in denominator-free form.
When `r² > 4|L|`, the number of `r`-rich points is at most `2|L|/r`. -/
theorem richness_mul_card_le_two_mul_lines
    (L : Finset LineIndex) (r : ℕ) (hlarge : 4 * L.card < r ^ 2) :
    r * (richPoints L r).card ≤ 2 * L.card := by
  classical
  apply large_family_bound L (richPoints L r) (fun x ↦ Erdos95.LineFamilies.linesThrough L x) r 1
  · intro x hx
    exact Finset.filter_subset _ _
  · intro x hx
    exact (mem_richPoints_iff.mp hx).2
  · intro x hx y hy hxy
    exact card_common_linesThrough_le_one L hxy
  · simpa using hlarge

/-- Rich points contributed by at least one surface in a finite collection. -/
noncomputable def surfaceRichPoints (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) : Finset Space3 := by
  classical
  exact F.biUnion fun Q ↦ richPoints (surfaceLines L Q) r

theorem mem_surfaceRichPoints_iff {L : Finset LineIndex}
    {F : Finset Poly3} {r : ℕ} {x : Space3} :
    x ∈ surfaceRichPoints L F r ↔
      ∃ Q ∈ F, x ∈ richPoints (surfaceLines L Q) r := by
  classical
  simp [surfaceRichPoints]

theorem card_surfaceRichPoints_le_sum (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) :
    (surfaceRichPoints L F r).card ≤
      ∑ Q ∈ F, (richPoints (surfaceLines L Q) r).card := by
  classical
  unfold surfaceRichPoints
  exact Finset.card_biUnion_le

theorem surfaceRichPoints_mono_collection
    (L : Finset LineIndex) {F G : Finset Poly3} (hFG : F ⊆ G) (r : ℕ) :
    surfaceRichPoints L F r ⊆ surfaceRichPoints L G r := by
  intro x hx
  obtain ⟨Q, hQF, hxQ⟩ := mem_surfaceRichPoints_iff.mp hx
  exact mem_surfaceRichPoints_iff.mpr ⟨Q, hFG hQF, hxQ⟩

/-- The elementary ordered-pair estimate, summed over a surface collection. -/
theorem richness_mul_pred_mul_card_surfaceRichPoints_le
    (L : Finset LineIndex) (F : Finset Poly3) (r : ℕ) :
    r * (r - 1) * (surfaceRichPoints L F r).card ≤
      ∑ Q ∈ F, (surfaceLines L Q).card ^ 2 := by
  classical
  calc
    r * (r - 1) * (surfaceRichPoints L F r).card ≤
        r * (r - 1) *
          ∑ Q ∈ F, (richPoints (surfaceLines L Q) r).card :=
      Nat.mul_le_mul_left _ (card_surfaceRichPoints_le_sum L F r)
    _ = ∑ Q ∈ F,
        r * (r - 1) * (richPoints (surfaceLines L Q) r).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ Q ∈ F, (surfaceLines L Q).card ^ 2 := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact richness_mul_pred_mul_card_le_sq (surfaceLines L Q) r

end RichPointCombinatorics

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SurfacePruning.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Pruning collections of algebraic surfaces

Distinct normalized irreducible surfaces of bounded degree share only a
bounded number of Elekes--Sharir lines.  The finite bounded-overlap lemma
therefore controls how many such surfaces can each contain many lines.
-/

namespace SurfacePruning

open Erdos95.ES Erdos95.LineFamilies Erdos95.SurfaceCollections
open Erdos95.SetFamilyBounds Erdos95.SurfaceFactors
open Erdos95.RichPointCombinatorics

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem filter_surfaceLines_eq_commonSurfaceLines
    (L : Finset LineIndex) (Q R : Poly3) :
    (surfaceLines L Q).filter (fun l ↦ l ∈ surfaceLines L R) =
      commonSurfaceLines L Q R := by
  classical
  ext l
  simp only [Finset.mem_filter, mem_surfaceLines_iff,
    mem_commonSurfaceLines_iff]
  tauto

/-- Guth's many-large-surfaces lemma, with a slightly stronger quadratic
hypothesis convenient for denominator-free natural-number arithmetic. -/
theorem large_surface_collection_bound
    (L : Finset LineIndex) (F : Finset Poly3) (A D : ℕ)
    (hirr : ∀ Q ∈ F, Irreducible Q)
    (hnorm : ∀ Q ∈ F, normalize Q = Q)
    (hdegree : ∀ Q ∈ F, Q.totalDegree ≤ D)
    (hlarge : ∀ Q ∈ F, A ≤ (surfaceLines L Q).card)
    (hquadratic : 4 * commonLineConstant D * L.card < A ^ 2) :
    A * F.card ≤ 2 * L.card := by
  classical
  apply large_family_bound L F (surfaceLines L) A (commonLineConstant D)
  · intro Q hQ
    exact surfaceLines_subset L Q
  · exact hlarge
  · intro Q hQ R hR hQR
    rw [filter_surfaceLines_eq_commonSurfaceLines]
    exact card_commonSurfaceLines_le L
      (hirr Q hQ) (hirr R hR) (hnorm Q hQ) (hnorm R hR)
      hQR (hdegree Q hQ) (hdegree R hR)
  · exact hquadratic

/-! ## Threshold pruning -/

/-- The members of `F` containing at least `A` lines of `L`. -/
noncomputable def largeSurfaces (L : Finset LineIndex)
    (F : Finset Poly3) (A : ℕ) : Finset Poly3 := by
  classical
  exact F.filter fun Q ↦ A ≤ (surfaceLines L Q).card

/-- The members discarded at threshold `A`. -/
noncomputable def smallSurfaces (L : Finset LineIndex)
    (F : Finset Poly3) (A : ℕ) : Finset Poly3 := by
  classical
  exact F.filter fun Q ↦ (surfaceLines L Q).card < A

theorem mem_largeSurfaces_iff {L : Finset LineIndex}
    {F : Finset Poly3} {A : ℕ} {Q : Poly3} :
    Q ∈ largeSurfaces L F A ↔
      Q ∈ F ∧ A ≤ (surfaceLines L Q).card := by
  classical
  simp [largeSurfaces]

theorem mem_smallSurfaces_iff {L : Finset LineIndex}
    {F : Finset Poly3} {A : ℕ} {Q : Poly3} :
    Q ∈ smallSurfaces L F A ↔
      Q ∈ F ∧ (surfaceLines L Q).card < A := by
  classical
  simp [smallSurfaces]

theorem surfaces_subset_large_union_small
    (L : Finset LineIndex) (F : Finset Poly3) (A : ℕ) :
    F ⊆ largeSurfaces L F A ∪ smallSurfaces L F A := by
  intro Q hQ
  by_cases hlarge : A ≤ (surfaceLines L Q).card
  · exact Finset.mem_union_left _
      (mem_largeSurfaces_iff.mpr ⟨hQ, hlarge⟩)
  · exact Finset.mem_union_right _
      (mem_smallSurfaces_iff.mpr ⟨hQ, Nat.lt_of_not_ge hlarge⟩)

/-- The sum of squared line counts over the discarded collection is bounded
by its cardinality times the square of the threshold. -/
theorem sum_sq_surfaceLines_small_le
    (L : Finset LineIndex) (F : Finset Poly3) (A : ℕ) :
    ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 ≤
      F.card * A ^ 2 := by
  calc
    ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 ≤
        ∑ _Q ∈ smallSurfaces L F A, A ^ 2 := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact Nat.pow_le_pow_left (Nat.le_of_lt
        (mem_smallSurfaces_iff.mp hQ).2) 2
    _ = (smallSurfaces L F A).card * A ^ 2 := by simp
    _ ≤ F.card * A ^ 2 := by
      exact Nat.mul_le_mul_right (A ^ 2)
        (Finset.card_le_card (show smallSurfaces L F A ⊆ F by
          exact Finset.filter_subset _ _))

end SurfacePruning

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/Barycentric.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite barycentric subdivisions

This file gives a small finite-complex model tailored to the combinatorial
Borsuk--Ulam argument needed for Erdos 95.  Faces are nonempty finite sets.
The barycentric subdivision has the nonempty faces of the old complex as
vertices, and its faces are the nonempty chains under inclusion.
-/

namespace Barycentric

/-- A finite abstract simplicial complex, with all computational instances
stored explicitly so that the construction can be iterated. -/
structure FiniteComplex where
  Vertex : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  IsFace : Finset Vertex → Prop
  isFaceDecidable : DecidablePred IsFace
  face_nonempty : ∀ {s}, IsFace s → s.Nonempty
  singleton_face : ∀ v, IsFace {v}
  face_of_nonempty_subset : ∀ {s t}, IsFace s → t ⊆ s → t.Nonempty → IsFace t

attribute [instance] FiniteComplex.vertexFintype
  FiniteComplex.vertexDecidableEq FiniteComplex.isFaceDecidable

/-- A vertex of the barycentric subdivision is a nonempty face of the old
complex. -/
abbrev BaryVertex (K : FiniteComplex) := {s : Finset K.Vertex // K.IsFace s}

/-- A finite set of old faces is a chain under inclusion. -/
def IsFaceChain (K : FiniteComplex) (S : Finset (BaryVertex K)) : Prop :=
  S.Nonempty ∧ ∀ A ∈ S, ∀ B ∈ S, A.1 ⊆ B.1 ∨ B.1 ⊆ A.1

noncomputable instance (K : FiniteComplex) : DecidablePred (IsFaceChain K) := by
  intro S
  classical
  infer_instance

/-- The barycentric subdivision of a finite complex. -/
noncomputable def barycentricSubdivision (K : FiniteComplex) : FiniteComplex where
  Vertex := BaryVertex K
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  IsFace := IsFaceChain K
  isFaceDecidable := inferInstance
  face_nonempty h := h.1
  singleton_face A := by
    refine ⟨Finset.singleton_nonempty A, ?_⟩
    intro B hB C hC
    simp only [Finset.mem_singleton] at hB hC
    subst B
    subst C
    exact Or.inl Finset.Subset.rfl
  face_of_nonempty_subset := by
    intro S T hS hTS hT
    refine ⟨hT, ?_⟩
    intro A hA B hB
    exact hS.2 A (hTS hA) B (hTS hB)

/-- The signed vertices of the boundary of the `d`-cross-polytope. -/
abbrev SignedAtom (d : ℕ) := Fin d × Bool

/-- The boundary complex of the cross-polytope: a face is a nonempty set of
signed coordinate vertices containing no opposite pair. -/
def crossPolytopeBoundary (d : ℕ) : FiniteComplex where
  Vertex := SignedAtom d
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  IsFace s := s.Nonempty ∧
    ∀ i : Fin d, ¬ ((i, false) ∈ s ∧ (i, true) ∈ s)
  isFaceDecidable := inferInstance
  face_nonempty h := h.1
  singleton_face v := by
    refine ⟨Finset.singleton_nonempty v, ?_⟩
    intro i hi
    simp only [Finset.mem_singleton] at hi
    have := hi.1.trans hi.2.symm
    simp at this
  face_of_nonempty_subset := by
    intro s t hs hts ht
    refine ⟨ht, ?_⟩
    intro i hi
    exact hs.2 i ⟨hts hi.1, hts hi.2⟩

/-- Every face of the `d`-cross-polytope boundary has at most `d` vertices. -/
theorem card_face_crossPolytopeBoundary_le (d : ℕ)
    {s : Finset (crossPolytopeBoundary d).Vertex}
    (hs : (crossPolytopeBoundary d).IsFace s) :
    s.card ≤ d := by
  have hinj : Set.InjOn Prod.fst
      (↑s : Set (crossPolytopeBoundary d).Vertex) := by
    rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
    simp only [Prod.fst] at hij
    subst j
    have hbc : b = c := by
      by_contra hbc
      have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
        cases b <;> cases c <;> simp_all
      rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hs.2 i ⟨hib, hjc⟩
      · exact hs.2 i ⟨hjc, hib⟩
    exact Prod.ext rfl hbc
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Barycentric subdivision preserves an a priori face-cardinality bound.
The rank of a vertex in a chain is the cardinality of the old face. -/
theorem card_face_barycentricSubdivision_le
    (K : FiniteComplex) (d : ℕ)
    (hK : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : (barycentricSubdivision K).IsFace S) :
    S.card ≤ d := by
  let rank : BaryVertex K → Fin d := fun A ↦
    ⟨A.1.card - 1, by
      have hpos : 0 < A.1.card := Finset.card_pos.mpr (K.face_nonempty A.2)
      have hle : A.1.card ≤ d := hK A.2
      omega⟩
  have hinj : Set.InjOn rank
      (↑S : Set (barycentricSubdivision K).Vertex) := by
    intro A hA B hB hab
    apply Subtype.ext
    have hcard : A.1.card = B.1.card := by
      have hApos : 0 < A.1.card := Finset.card_pos.mpr (K.face_nonempty A.2)
      have hBpos : 0 < B.1.card := Finset.card_pos.mpr (K.face_nonempty B.2)
      have hval := congrArg Fin.val hab
      dsimp [rank] at hval
      omega
    rcases hS.2 A hA B hB with hAB | hBA
    · exact Finset.eq_of_subset_of_card_le hAB hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hBA hcard.le).symm
  calc
    S.card = (S.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Repeated barycentric subdivision of the cross-polytope boundary. -/
noncomputable def iteratedBoundary (d : ℕ) : ℕ → FiniteComplex
  | 0 => crossPolytopeBoundary d
  | r + 1 => barycentricSubdivision (iteratedBoundary d r)

/-- Every face in every iterated subdivision still has at most `d` vertices. -/
theorem card_face_iteratedBoundary_le (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    s.card ≤ d := by
  induction r with
  | zero => exact card_face_crossPolytopeBoundary_le d hs
  | succ r ih =>
      exact card_face_barycentricSubdivision_le (iteratedBoundary d r) d
        (fun {s} h ↦ ih (s := s) h) hs

/-! ## Antipodal actions -/

/-- An involution of the vertices of a finite complex which preserves its
faces.  The inverse implication for faces follows from involutivity. -/
structure ComplexInvolution (K : FiniteComplex) where
  neg : K.Vertex → K.Vertex
  neg_neg : ∀ v, neg (neg v) = v
  face_neg : ∀ {s}, K.IsFace s → K.IsFace (s.image neg)

namespace ComplexInvolution

variable {K : FiniteComplex} (A : ComplexInvolution K)

theorem neg_injective : Function.Injective A.neg := by
  intro v w h
  simpa only [A.neg_neg] using congrArg A.neg h

theorem image_neg_image_neg (s : Finset K.Vertex) :
    (s.image A.neg).image A.neg = s := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa only [A.neg_neg] using hu
  · intro hv
    exact ⟨A.neg v, ⟨v, hv, rfl⟩, A.neg_neg v⟩

/-- An involution of a complex induces one on its barycentric subdivision. -/
noncomputable def barycentricLift :
    ComplexInvolution (barycentricSubdivision K) where
  neg F := ⟨F.1.image A.neg, A.face_neg F.2⟩
  neg_neg F := by
    apply Subtype.ext
    exact A.image_neg_image_neg F.1
  face_neg := by
    intro S hS
    refine ⟨Finset.image_nonempty.mpr hS.1, ?_⟩
    intro F hF G hG
    rcases Finset.mem_image.mp hF with ⟨F₀, hF₀, rfl⟩
    rcases Finset.mem_image.mp hG with ⟨G₀, hG₀, rfl⟩
    rcases hS.2 F₀ hF₀ G₀ hG₀ with hFG | hGF
    · left
      exact Finset.image_mono _ hFG
    · right
      exact Finset.image_mono _ hGF

end ComplexInvolution

/-- Coordinate-sign reversal on the cross-polytope boundary. -/
def crossPolytopeAntipode (d : ℕ) :
    ComplexInvolution (crossPolytopeBoundary d) where
  neg v := (v.1, !v.2)
  neg_neg v := by cases v with | mk i b => cases b <;> rfl
  face_neg := by
    intro s hs
    refine ⟨Finset.image_nonempty.mpr hs.1, ?_⟩
    intro i hi
    apply hs.2 i
    constructor
    · rcases Finset.mem_image.mp hi.2 with ⟨v, hv, huv⟩
      cases v with
      | mk j b =>
          cases b
          · have hji : j = i := congrArg Prod.fst huv
            subst j
            exact hv
          · simp at huv
    · rcases Finset.mem_image.mp hi.1 with ⟨v, hv, huv⟩
      cases v with
      | mk j b =>
          cases b
          · simp at huv
          · have hji : j = i := congrArg Prod.fst huv
            subst j
            exact hv

/-- The recursively induced antipodal action on every iterated subdivision. -/
noncomputable def iteratedAntipode (d : ℕ) :
    ∀ r, ComplexInvolution (iteratedBoundary d r)
  | 0 => crossPolytopeAntipode d
  | r + 1 => (iteratedAntipode d r).barycentricLift

@[simp] theorem iteratedAntipode_zero_neg (d : ℕ) (v : SignedAtom d) :
    (iteratedAntipode d 0).neg v = (v.1, !v.2) := rfl

@[simp] theorem iteratedAntipode_succ_neg (d r : ℕ)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    (iteratedAntipode d (r + 1)).neg F =
      ⟨F.1.image (iteratedAntipode d r).neg,
        (iteratedAntipode d r).face_neg F.2⟩ := rfl

/-! ## Geometric realization -/

/-- The signed coordinate vector associated with a cross-polytope vertex. -/
def signedBasisVector {d : ℕ} (v : SignedAtom d) : Fin d → ℝ :=
  fun j ↦ if j = v.1 then if v.2 then 1 else -1 else 0

theorem signedBasisVector_antipode {d : ℕ} (v : SignedAtom d) :
    signedBasisVector (v.1, !v.2) = -signedBasisVector v := by
  rcases v with ⟨i, b⟩
  funext j
  by_cases hj : j = i
  · subst j
    cases b <;> simp [signedBasisVector]
  · cases b <;> simp [signedBasisVector, hj]

/-- Arithmetic barycenter of a nonempty finite face. -/
noncomputable def faceAverage {K : FiniteComplex} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (f : K.Vertex → E) (F : BaryVertex K) : E :=
  (F.1.card : ℝ)⁻¹ • ∑ v ∈ F.1, f v

/-- Realization of an iterated barycentric vertex.  At each successor stage
the new vertex is sent to the barycenter of the old face it represents. -/
noncomputable def realize (d : ℕ) :
    ∀ r, (iteratedBoundary d r).Vertex → (Fin d → ℝ)
  | 0 => signedBasisVector
  | r + 1 => faceAverage (realize d r)

@[simp] theorem realize_zero (d : ℕ) (v : SignedAtom d) :
    realize d 0 v = signedBasisVector v := rfl

@[simp] theorem realize_succ (d r : ℕ)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    realize d (r + 1) F = faceAverage (realize d r) F := rfl

theorem faceAverage_image_involution
    {K : FiniteComplex} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : ComplexInvolution K) (f : K.Vertex → E)
    (hf : ∀ v, f (A.neg v) = -f v) (F : BaryVertex K) :
    faceAverage f ⟨F.1.image A.neg, A.face_neg F.2⟩ = -faceAverage f F := by
  have hcard : (F.1.image A.neg).card = F.1.card :=
    Finset.card_image_iff.mpr A.neg_injective.injOn
  have hsum : (∑ v ∈ F.1.image A.neg, f v) = -∑ v ∈ F.1, f v := by
    rw [Finset.sum_image]
    · simp_rw [hf]
      exact Finset.sum_neg_distrib (s := F.1) f
    · exact A.neg_injective.injOn
  simp only [faceAverage, hcard, hsum, smul_neg]

/-- The geometric realization intertwines the combinatorial antipode with
vector negation at every subdivision level. -/
theorem realize_antipode (d r : ℕ) (v : (iteratedBoundary d r).Vertex) :
    realize d r ((iteratedAntipode d r).neg v) = -realize d r v := by
  induction r with
  | zero => exact signedBasisVector_antipode v
  | succ r ih =>
      exact faceAverage_image_involution (iteratedAntipode d r)
        (realize d r) (fun w ↦ ih w) v

/-! ## Quantitative mesh estimates -/

/-- A uniform bound for the diameter of every face in a realization. -/
def FaceDiameter (K : FiniteComplex) {E : Type*} [PseudoMetricSpace E]
    (f : K.Vertex → E) (D : ℝ) : Prop :=
  ∀ ⦃s : Finset K.Vertex⦄, K.IsFace s →
    ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → dist (f v) (f w) ≤ D

/-- The barycenter of a face is at distance at most its diameter from every
point of any containing face. -/
theorem norm_faceAverage_sub_le
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (F G : BaryVertex K)
    (hFG : F.1 ⊆ G.1)
    (hD : ∀ ⦃v⦄, v ∈ G.1 → ∀ ⦃w⦄, w ∈ G.1 → ‖f v - f w‖ ≤ D)
    {y : K.Vertex} (hy : y ∈ G.1) :
    ‖faceAverage f F - f y‖ ≤ D := by
  have hFpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hFinv : 0 ≤ (F.1.card : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr (by exact_mod_cast hFpos))
  have havg :
      faceAverage f F - f y =
        (F.1.card : ℝ)⁻¹ • ∑ x ∈ F.1, (f x - f y) := by
    unfold faceAverage
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
      inv_mul_cancel₀ hFne, one_smul]
  rw [havg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hFinv]
  calc
    (F.1.card : ℝ)⁻¹ * ‖∑ x ∈ F.1, (f x - f y)‖
        ≤ (F.1.card : ℝ)⁻¹ * ∑ x ∈ F.1, ‖f x - f y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le F.1 fun x ↦ f x - f y) hFinv
    _ ≤ (F.1.card : ℝ)⁻¹ * ∑ _x ∈ F.1, D := by
      gcongr with x hx
      exact hD (hFG hx) hy
    _ = D := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
      simp [smul_eq_mul, hFne]

/-- Quantitative form of the nested-barycenter estimate.  The common points
cancel, so only the vertices in `G \ F` contribute. -/
theorem norm_faceAverage_sub_faceAverage_le
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (F G : BaryVertex K)
    (hFG : F.1 ⊆ G.1)
    (hD : ∀ ⦃v⦄, v ∈ G.1 → ∀ ⦃w⦄, w ∈ G.1 → ‖f v - f w‖ ≤ D) :
    ‖faceAverage f F - faceAverage f G‖ ≤
      ((G.1 \ F.1).card : ℝ) / G.1.card * D := by
  have hFpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hGpos : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
  have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hGne : (G.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hGpos)
  have hGinv : 0 ≤ (G.1.card : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr (by exact_mod_cast hGpos))
  have hsumF : (F.1.card : ℝ) • faceAverage f F = ∑ x ∈ F.1, f x := by
    unfold faceAverage
    rw [smul_smul, mul_inv_cancel₀ hFne, one_smul]
  have hsumG : (G.1.card : ℝ) • faceAverage f G = ∑ x ∈ G.1, f x := by
    unfold faceAverage
    rw [smul_smul, mul_inv_cancel₀ hGne, one_smul]
  have hcardNat := Finset.card_sdiff_add_card_eq_card hFG
  have hcardReal :
      (G.1.card : ℝ) = (G.1 \ F.1).card + F.1.card := by
    exact_mod_cast hcardNat.symm
  have hsumSplit := Finset.sum_sdiff (f := f) hFG
  have hid :
      faceAverage f F - faceAverage f G =
        (G.1.card : ℝ)⁻¹ •
          ∑ y ∈ G.1 \ F.1, (faceAverage f F - f y) := by
    apply (smul_right_injective E hGne)
    change (G.1.card : ℝ) • (faceAverage f F - faceAverage f G) =
      (G.1.card : ℝ) • ((G.1.card : ℝ)⁻¹ •
        ∑ y ∈ G.1 \ F.1, (faceAverage f F - f y))
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hGne, one_smul,
      Finset.sum_sub_distrib, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ]
    rw [hsumG, hcardReal, add_smul, hsumF]
    rw [← hsumSplit]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hGinv]
  calc
    (G.1.card : ℝ)⁻¹ *
          ‖∑ y ∈ G.1 \ F.1, (faceAverage f F - f y)‖
        ≤ (G.1.card : ℝ)⁻¹ *
          ∑ y ∈ G.1 \ F.1, ‖faceAverage f F - f y‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (G.1 \ F.1) fun y ↦ faceAverage f F - f y) hGinv
    _ ≤ (G.1.card : ℝ)⁻¹ * ∑ _y ∈ G.1 \ F.1, D := by
      gcongr with y hy
      exact norm_faceAverage_sub_le f D F G hFG hD (Finset.mem_sdiff.mp hy).1
    _ = ((G.1 \ F.1).card : ℝ) / G.1.card * D := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring

theorem card_sdiff_div_le_contraction
    {α : Type*} [DecidableEq α] {F G : Finset α} {d : ℕ}
    (hF : F.Nonempty) (hFG : F ⊆ G) (hGd : G.card ≤ d) (hd : 0 < d) :
    ((G \ F).card : ℝ) / G.card ≤ 1 - 1 / d := by
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  have hGpos : 0 < G.card := lt_of_lt_of_le hFpos (Finset.card_le_card hFG)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hGR : (0 : ℝ) < G.card := by exact_mod_cast hGpos
  have hprodNat : G.card ≤ F.card * d := by
    calc
      G.card ≤ d := hGd
      _ ≤ F.card * d := by nlinarith
  have hprod : (G.card : ℝ) ≤ F.card * d := by exact_mod_cast hprodNat
  have hinv : (1 : ℝ) / d ≤ F.card / G.card := by
    rw [div_le_div_iff₀ hdR hGR]
    simpa using hprod
  have hcardNat := Finset.card_sdiff_add_card_eq_card hFG
  have hcard : ((G \ F).card : ℝ) + F.card = G.card := by
    exact_mod_cast hcardNat
  have hratio : ((G \ F).card : ℝ) / G.card = 1 - F.card / G.card := by
    field_simp
    linarith
  rw [hratio]
  exact sub_le_sub_left hinv 1

/-- One barycentric subdivision shrinks every face diameter by at least the
factor `1 - 1/d` when old faces have at most `d` vertices. -/
theorem faceDiameter_barycentricSubdivision
    (K : FiniteComplex) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (d : ℕ) (hd : 0 < d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (hdiam : FaceDiameter K f D) :
    FaceDiameter (barycentricSubdivision K) (faceAverage f)
      ((1 - 1 / (d : ℝ)) * D) := by
  intro S hS F hFS G hGS
  have hDnonneg : 0 ≤ D := by
    obtain ⟨x, hx⟩ := K.face_nonempty G.2
    simpa using hdiam G.2 hx hx
  rcases hS.2 F hFS G hGS with hFG | hGF
  · rw [dist_eq_norm]
    calc
      ‖faceAverage f F - faceAverage f G‖
          ≤ ((G.1 \ F.1).card : ℝ) / G.1.card * D :=
        norm_faceAverage_sub_faceAverage_le f D F G hFG
          (fun hv hhv hw hhw ↦ by
            simpa [dist_eq_norm] using hdiam G.2 hhv hhw)
      _ ≤ (1 - 1 / (d : ℝ)) * D :=
        mul_le_mul_of_nonneg_right
          (card_sdiff_div_le_contraction
            (K.face_nonempty F.2) hFG (hcard G.2) hd) hDnonneg
  · rw [dist_comm, dist_eq_norm]
    calc
      ‖faceAverage f G - faceAverage f F‖
          ≤ ((F.1 \ G.1).card : ℝ) / F.1.card * D :=
        norm_faceAverage_sub_faceAverage_le f D G F hGF
          (fun hv hhv hw hhw ↦ by
            simpa [dist_eq_norm] using hdiam F.2 hhv hhw)
      _ ≤ (1 - 1 / (d : ℝ)) * D :=
        mul_le_mul_of_nonneg_right
          (card_sdiff_div_le_contraction
            (K.face_nonempty G.2) hGF (hcard F.2) hd) hDnonneg

theorem norm_signedBasisVector_le_one {d : ℕ} (v : SignedAtom d) :
    ‖signedBasisVector v‖ ≤ 1 := by
  rcases v with ⟨i, b⟩
  rw [Pi.norm_def]
  norm_cast
  apply Finset.sup_le
  intro j hj
  by_cases h : j = i
  · subst j
    cases b <;> simp [signedBasisVector]
  · cases b <;> simp [signedBasisVector, h]

theorem faceDiameter_crossPolytope (d : ℕ) :
    FaceDiameter (crossPolytopeBoundary d) signedBasisVector 2 := by
  intro s hs v hv w hw
  calc
    dist (signedBasisVector v) (signedBasisVector w)
        ≤ ‖signedBasisVector v‖ + ‖signedBasisVector w‖ :=
      dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_signedBasisVector_le_one v) (norm_signedBasisVector_le_one w)
    _ = 2 := by norm_num

/-- Explicit exponentially decaying mesh bound for the iterated realization. -/
theorem faceDiameter_realize (d : ℕ) (hd : 0 < d) (r : ℕ) :
    FaceDiameter (iteratedBoundary d r) (realize d r)
      (2 * (1 - 1 / (d : ℝ)) ^ r) := by
  induction r with
  | zero =>
      simpa [iteratedBoundary, realize] using faceDiameter_crossPolytope d
  | succ r ih =>
      have h := faceDiameter_barycentricSubdivision
        (iteratedBoundary d r) (realize d r)
        (2 * (1 - 1 / (d : ℝ)) ^ r) d hd
        (fun {s} hs ↦ card_face_iteratedBoundary_le d r hs) ih
      change FaceDiameter (barycentricSubdivision (iteratedBoundary d r))
        (faceAverage (realize d r))
        (2 * (1 - 1 / (d : ℝ)) ^ (r + 1))
      convert h using 1 <;> rw [pow_succ] <;> ring

/-- Faces in sufficiently deep subdivisions have arbitrarily small diameter. -/
theorem exists_iteratedBoundary_faceDiameter_lt
    (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, ∀ ⦃s : Finset (iteratedBoundary d r).Vertex⦄,
      (iteratedBoundary d r).IsFace s →
        ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s →
          dist (realize d r v) (realize d r w) < ε := by
  let q : ℝ := 1 - 1 / d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ q := by
    dsimp [q]
    have : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one hdR]
      exact_mod_cast hd
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    have : (0 : ℝ) < 1 / d := div_pos zero_lt_one hdR
    linarith
  have htend : Filter.Tendsto (fun r : ℕ ↦ 2 * q ^ r) Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1) :
        Filter.Tendsto (fun r : ℕ ↦ (2 : ℝ) * q ^ r)
          Filter.atTop (nhds ((2 : ℝ) * 0))) using 1 <;> norm_num
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨r, hr⟩ := htend ε hε
  refine ⟨r, ?_⟩
  intro s hs v hv w hw
  have hr' := hr r le_rfl
  have hnonneg : 0 ≤ 2 * q ^ r := mul_nonneg (by norm_num) (pow_nonneg hq0 r)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hr'
  exact lt_of_le_of_lt (faceDiameter_realize d hd r hs hv hw) (by
    simpa [q] using hr')

/-! ## Separation from the origin -/

/-- A finite chain has a largest member.  We select a member of maximal
cardinality and use comparability to turn the cardinality inequality into
inclusion. -/
theorem exists_chain_largest
    {K : FiniteComplex} {S : Finset (BaryVertex K)}
    (hS : IsFaceChain K S) :
    ∃ M ∈ S, ∀ F ∈ S, F.1 ⊆ M.1 := by
  obtain ⟨M, hMS, hMmax⟩ := Finset.exists_max_image S (fun F ↦ F.1.card) hS.1
  refine ⟨M, hMS, ?_⟩
  intro F hFS
  rcases hS.2 F hFS M hMS with hFM | hMF
  · exact hFM
  · have hcard : F.1.card ≤ M.1.card := hMmax F hFS
    have heq : M.1 = F.1 := Finset.eq_of_subset_of_card_le hMF hcard
    simpa [heq]

/-- Base separation for a face of the cross-polytope boundary. -/
theorem face_separated_crossPolytope (d : ℕ)
    {s : Finset (crossPolytopeBoundary d).Vertex}
    (hs : (crossPolytopeBoundary d).IsFace s) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ v ∈ s, L (signedBasisVector v) = 1 := by
  classical
  let sign : Fin d → ℝ := fun i ↦ if (i, true) ∈ s then 1 else -1
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ ∑ i, sign i * x i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        change sign i * (a * x i) = a * (sign i * x i)
        ring }
  refine ⟨L, ?_⟩
  rintro ⟨i, b⟩ hv
  have hnotOpp : (i, !b) ∉ s := by
    intro hopp
    cases b
    · exact hs.2 i ⟨hv, hopp⟩
    · exact hs.2 i ⟨hopp, hv⟩
  cases b
  · have htrue : (i, true) ∉ s := by simpa using hnotOpp
    change (∑ j : Fin d, sign j * signedBasisVector (i, false) j) = 1
    rw [Finset.sum_eq_single i]
    · simp [sign, signedBasisVector, htrue]
    · intro j hj hji
      simp [signedBasisVector, hji]
    · simp
  · change (∑ j : Fin d, sign j * signedBasisVector (i, true) j) = 1
    rw [Finset.sum_eq_single i]
    · have hsign : sign i = 1 := by
        exact if_pos hv
      rw [hsign]
      simp [signedBasisVector]
    · intro j hj hji
      simp [signedBasisVector, hji]
    · simp

/-- Every face is contained in an affine hyperplane not passing through the
origin: one linear functional takes the constant value `1` on all its
realized vertices. -/
theorem face_separated_realize (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ v ∈ s, L (realize d r v) = 1 := by
  classical
  induction r with
  | zero =>
      exact face_separated_crossPolytope d hs
  | succ r ih =>
      obtain ⟨M, hMs, hlargest⟩ := exists_chain_largest hs
      obtain ⟨L, hL⟩ := ih M.2
      refine ⟨L, ?_⟩
      intro F hFs
      have hFM : F.1 ⊆ M.1 := hlargest F hFs
      have hFpos : 0 < F.1.card := Finset.card_pos.mpr
        ((iteratedBoundary d r).face_nonempty F.2)
      have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
      change L (faceAverage (realize d r) F) = 1
      unfold faceAverage
      rw [LinearMapClass.map_smul, map_sum]
      have hsum : (∑ x ∈ F.1, L (realize d r x)) = ∑ _x ∈ F.1, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hL x (hFM hx)
      rw [hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hFne

/-- In particular no realized subdivision vertex is the zero coefficient
vector. -/
theorem realize_ne_zero (d r : ℕ) (v : (iteratedBoundary d r).Vertex) :
    realize d r v ≠ 0 := by
  intro hv
  obtain ⟨L, hL⟩ := face_separated_realize d r
    ((iteratedBoundary d r).singleton_face v)
  have := hL v (by simp)
  rw [hv, map_zero] at this
  norm_num at this

end Barycentric

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/FineTucker.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Tucker parity on iterated barycentric subdivisions

This file proves the refinement-stable Tucker lemma needed for the finite
Stone--Tukey theorem.  The proof is the mod-two Ky Fan incidence argument:
alternating boundary ridges are counted against alternating top simplices.
-/

open scoped BigOperators

namespace FineTucker

open Barycentric
open ProofsInTheBook.Chapter39

/-- Faces of cardinality `d` satisfying a vertex predicate. -/
abbrev RestrictedTopFace (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :=
  {s : Finset K.Vertex // K.IsFace s ∧ s.card = d ∧ ∀ v ∈ s, U v}

/-- Faces of cardinality `d-1` satisfying a vertex predicate. -/
abbrev RestrictedRidge (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :=
  {s : Finset K.Vertex // K.IsFace s ∧ s.card = d - 1 ∧ ∀ v ∈ s, U v}

noncomputable instance restrictedTopFaceFintype
    (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :
    Fintype (RestrictedTopFace K U d) := by
  classical
  infer_instance

noncomputable instance restrictedRidgeFintype
    (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :
    Fintype (RestrictedRidge K U d) := by
  classical
  infer_instance

/-- Incidence is inclusion of the ridge in the top face. -/
def FaceIncident {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (R : RestrictedRidge K U d) (T : RestrictedTopFace K U d) : Prop :=
  R.1 ⊆ T.1

noncomputable instance faceIncidentDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} :
    DecidableRel (FaceIncident (K := K) (U := U) (d := d)) := by
  classical
  infer_instance

/-- A chosen enumeration of a finite face of known cardinality. -/
noncomputable def faceEnum {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) : Fin d → α := by
  let e : {x // x ∈ s} ≃ Fin d :=
    Fintype.equivFinOfCardEq (by simpa using hs)
  exact fun i ↦ (e.symm i).1

theorem faceEnum_mem {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) (i : Fin d) :
    faceEnum s d hs i ∈ s := by
  classical
  unfold faceEnum
  simp

theorem faceEnum_injective {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) :
    Function.Injective (faceEnum s d hs) := by
  classical
  let e : {x // x ∈ s} ≃ Fin d :=
    Fintype.equivFinOfCardEq (by simpa using hs)
  change Function.Injective (fun i ↦ (e.symm i).1)
  intro i j hij
  apply e.symm.injective
  apply Subtype.ext
  exact hij

theorem faceEnum_surjective_subtype {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) :
    Function.Surjective
      (fun i : Fin d ↦ (⟨faceEnum s d hs i, faceEnum_mem s d hs i⟩ : {x // x ∈ s})) := by
  classical
  unfold faceEnum
  exact (Fintype.equivFinOfCardEq (by simpa using hs)).symm.surjective

/-- The labels on a top face, in an arbitrary enumeration.  Alternation is
permutation invariant, so no ordering choice enters the theorem statement. -/
noncomputable def topLabelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    Fin d → SignedLabel m :=
  fun i ↦ label (faceEnum T.1 d T.2.2.1 i)

/-- A ridge has the positive alternating label set. -/
def IsPositiveAlternatingRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (R : RestrictedRidge K U d) : Prop :=
  ∃ idx : Fin (d - 1) → Fin m,
    StrictMono idx ∧ R.1.image label = alternatingLabelSetOf idx

noncomputable instance isPositiveAlternatingRidgeDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsPositiveAlternatingRidge (U := U) (d := d) label) := by
  classical
  intro R
  infer_instance

/-- Positive-or-negative alternating top faces. -/
def IsAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  (∃ idx : Fin d → Fin m,
      StrictMono idx ∧ T.1.image label = alternatingLabelSetOf idx) ∨
    (∃ idx : Fin d → Fin m,
      StrictMono idx ∧ T.1.image label = alternatingNegLabelSetOf idx)

noncomputable instance isAlternatingTopDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsAlternatingTop (U := U) (d := d) label) := by
  classical
  intro T
  infer_instance

/-! ## Ridges inside one top face -/

noncomputable def eraseRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (x : {v // v ∈ T.1}) :
    RestrictedRidge K U d := by
  classical
  refine ⟨T.1.erase x.1, ?_, ?_, ?_⟩
  · apply K.face_of_nonempty_subset T.2.1 (Finset.erase_subset _ _)
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem x.2, T.2.2.1]
    omega
  · rw [Finset.card_erase_of_mem x.2, T.2.2.1]
  · intro v hv
    exact T.2.2.2 v (Finset.mem_of_mem_erase hv)

theorem eraseRidge_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (x : {v // v ∈ T.1}) :
    FaceIncident (eraseRidge hd T x) T :=
  Finset.erase_subset _ _

theorem eraseRidge_injective
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Function.Injective (eraseRidge hd T) := by
  classical
  intro x y hxy
  apply Subtype.ext
  apply (Finset.erase_inj T.1 x.2).mp
  exact congrArg Subtype.val hxy

theorem eraseRidge_surjective_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Function.Surjective
      (fun x : {v // v ∈ T.1} ↦
        (⟨eraseRidge hd T x, eraseRidge_incident hd T x⟩ :
          {R : RestrictedRidge K U d // FaceIncident R T})) := by
  classical
  rintro ⟨R, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ x ∈ T.1, x ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro x hxT
    by_contra hxR
    exact hnone ⟨x, hxT, hxR⟩
  obtain ⟨x, hxT, hxR⟩ := hex
  let xT : {v // v ∈ T.1} := ⟨x, hxT⟩
  refine ⟨xT, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    change v ∈ R.1 at hv
    change v ∈ T.1.erase x
    rw [Finset.mem_erase]
    exact ⟨fun hvx ↦ hxR (hvx ▸ hv), hRT hv⟩
  · rw [(eraseRidge hd T xT).2.2.1, R.2.2.1]

/-- Deleting one vertex gives all and only the ridges incident to a fixed top
face. -/
noncomputable def eraseRidgeEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    {v // v ∈ T.1} ≃ {R : RestrictedRidge K U d // FaceIncident R T} :=
  Equiv.ofBijective
    (fun x ↦ ⟨eraseRidge hd T x, eraseRidge_incident hd T x⟩)
    ⟨fun _ _ h ↦ eraseRidge_injective hd T (congrArg Subtype.val h),
      eraseRidge_surjective_incident hd T⟩

/-- The chosen enumeration as an equivalence onto the vertices of a top
face. -/
noncomputable def faceEnumEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : RestrictedTopFace K U d) : Fin d ≃ {v // v ∈ T.1} := by
  classical
  exact Equiv.ofBijective
    (fun i ↦ ⟨faceEnum T.1 d T.2.2.1 i,
      faceEnum_mem T.1 d T.2.2.1 i⟩)
    ⟨fun _ _ h ↦ faceEnum_injective T.1 d T.2.2.1 (congrArg Subtype.val h),
      faceEnum_surjective_subtype T.1 d T.2.2.1⟩

/-- Incident ridges are canonically indexed by the deleted position in the
chosen top-face enumeration. -/
noncomputable def deletionRidgeEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Fin d ≃ {R : RestrictedRidge K U d // FaceIncident R T} :=
  (faceEnumEquiv T).trans (eraseRidgeEquiv hd T)

theorem deletionRidgeEquiv_val
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (i : Fin d) :
    (deletionRidgeEquiv hd T i).1.1 =
      T.1.erase (faceEnum T.1 d T.2.2.1 i) := by
  rfl

theorem image_label_deletion_eq_labelSeqSet
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) (i : Fin (k + 1)) :
    ((deletionRidgeEquiv (by omega : 2 ≤ k + 1) T i).1.1.image label) =
      labelSeqSet (fun a : Fin k ↦ topLabelSeq label T (i.succAbove a)) := by
  classical
  rw [deletionRidgeEquiv_val]
  ext z
  simp only [Finset.mem_image, labelSeqSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' := Finset.mem_erase.mp hv
    obtain ⟨j, hj⟩ := faceEnum_surjective_subtype
      T.1 (k + 1) T.2.2.1 ⟨v, hv'.2⟩
    have hjval : faceEnum T.1 (k + 1) T.2.2.1 j = v :=
      congrArg Subtype.val hj
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hv'.1 hjval.symm
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
    refine ⟨a, Finset.mem_univ _, ?_⟩
    change label (faceEnum T.1 (k + 1) T.2.2.1 (i.succAbove a)) = label v
    rw [ha, hjval]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨faceEnum T.1 (k + 1) T.2.2.1 (i.succAbove a), ?_, rfl⟩
    rw [Finset.mem_erase]
    refine ⟨?_, faceEnum_mem _ _ _ _⟩
    intro heq
    exact Fin.succAbove_ne i a
      (faceEnum_injective T.1 (k + 1) T.2.2.1 heq)

theorem positiveAlternating_deletionRidge_iff
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) (i : Fin (k + 1)) :
    IsPositiveAlternatingRidge label
        (deletionRidgeEquiv (by omega : 2 ≤ k + 1) T i).1 ↔
      i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T) := by
  classical
  rw [show i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T) ↔
      IsAltPosLabelSeq
        (fun a : Fin k ↦ topLabelSeq label T (i.succAbove a)) by
    simp [labelSeqAltPosDeletionSet]]
  unfold IsPositiveAlternatingRidge IsAltPosLabelSeq
  rw [image_label_deletion_eq_labelSeqSet hk label T i]
  rfl

theorem image_label_top_eq_labelSeqSet
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    T.1.image label = labelSeqSet (topLabelSeq label T) := by
  classical
  ext z
  simp only [Finset.mem_image, labelSeqSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi⟩ := faceEnum_surjective_subtype
      T.1 d T.2.2.1 ⟨v, hv⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change label (faceEnum T.1 d T.2.2.1 i) = label v
    exact congrArg label (congrArg Subtype.val hi)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨faceEnum T.1 d T.2.2.1 i,
      faceEnum_mem T.1 d T.2.2.1 i, rfl⟩

theorem alternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsAlternatingTop label T ↔
      IsAltPosLabelSeq (topLabelSeq label T) ∨
        IsAltNegLabelSeq (topLabelSeq label T) := by
  unfold IsAlternatingTop IsAltPosLabelSeq IsAltNegLabelSeq
  rw [← image_label_top_eq_labelSeqSet label T]

/-- No face contains a complementary pair of labels. -/
def NoComplementaryFaceLabels
    (K : FiniteComplex) {m : ℕ} (label : K.Vertex → SignedLabel m) : Prop :=
  ∀ ⦃s : Finset K.Vertex⦄, K.IsFace s →
    ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → label v ≠ (label w).neg

/-- Positive alternating ridges as a finite type. -/
abbrev PositiveAlternatingRidge
    (K : FiniteComplex) (U : K.Vertex → Prop) (d m : ℕ)
    (label : K.Vertex → SignedLabel m) :=
  {R : RestrictedRidge K U d // IsPositiveAlternatingRidge label R}

noncomputable def altIncidentReassociate
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    {R : {R : RestrictedRidge K U d // FaceIncident R T} //
      IsPositiveAlternatingRidge label R.1} ≃
      {R : PositiveAlternatingRidge K U d m label // FaceIncident R.1 T} where
  toFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  invFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl

/-- Alternating incident ridges are exactly the deletion positions in the
local Ky Fan door set. -/
noncomputable def altIncidentEquivDeletion
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) :
    {i : Fin (k + 1) // i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T)} ≃
      {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T} :=
  ((deletionRidgeEquiv (by omega : 2 ≤ k + 1) T).subtypeEquiv
    (fun i ↦ (positiveAlternating_deletionRidge_iff hk label T i).symm)).trans
      (altIncidentReassociate label T)

theorem card_altIncident_eq_deletionSet_card
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) :
    Fintype.card
        {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T} =
      (labelSeqAltPosDeletionSet (topLabelSeq label T)).card := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (altIncidentEquivDeletion hk label T).symm

theorem topLabelSeq_noOpposite
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    {label : K.Vertex → SignedLabel m} (hno : NoComplementaryFaceLabels K label)
    (T : RestrictedTopFace K U d) :
    NoOppositeLabelSeq (topLabelSeq label T) := by
  intro i j
  apply hno T.2.1
  · exact faceEnum_mem T.1 d T.2.2.1 i
  · exact faceEnum_mem T.1 d T.2.2.1 j

/-- The local sigma-degree parity: a top simplex has an odd number of
alternating ridge doors exactly when its complete label set is alternating. -/
theorem odd_altIncident_iff_alternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) {label : K.Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels K label)
    (T : RestrictedTopFace K U (k + 1)) :
    Odd (Fintype.card
        {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T}) ↔
      IsAlternatingTop label T := by
  rw [card_altIncident_eq_deletionSet_card hk label T,
    labelSeq_deletionParity_of_noOpposite (topLabelSeq_noOpposite hno T),
    ← alternatingTop_iff_labelSeq label T]

/-! ## Abstract hemisphere handshaking -/

/-- The sole geometric input to Ky Fan handshaking: every upper-hemisphere
ridge has one top coface on the equator boundary and two otherwise. -/
structure HemisphereGeometry
    (K : FiniteComplex) (U E : K.Vertex → Prop) (d : ℕ)
    [equatorDecidable : DecidablePred E] where
  ridge_degree : ∀ R : RestrictedRidge K U d,
    Fintype.card {T : RestrictedTopFace K U d // FaceIncident R T} =
      if (∀ v ∈ R.1, E v) then 1 else 2

def IsEquatorRidge
    {K : FiniteComplex} {U E : K.Vertex → Prop} {d : ℕ}
    (R : RestrictedRidge K U d) : Prop :=
  ∀ v ∈ R.1, E v

noncomputable instance isEquatorRidgeDecidable
    {K : FiniteComplex} {U E : K.Vertex → Prop} {d : ℕ}
    [DecidablePred E] :
    DecidablePred (IsEquatorRidge (K := K) (U := U) (E := E) (d := d)) := by
  classical
  intro R
  infer_instance

noncomputable def alternatingRhoData
    {K : FiniteComplex} {U E : K.Vertex → Prop} {k m : ℕ}
    [DecidablePred E]
    (label : K.Vertex → SignedLabel m)
    (H : HemisphereGeometry K U E (k + 1))
    (hne : Nonempty (PositiveAlternatingRidge K U (k + 1) m label)) :
    RhoDegreeManifoldData
      (PositiveAlternatingRidge K U (k + 1) m label)
      (RestrictedTopFace K U (k + 1)) where
  edge R T := FaceIncident R.1 T
  edge_decidable := inferInstance
  boundary R := IsEquatorRidge (E := E) R.1
  boundary_decidable := inferInstance
  nonempty_R := hne
  degree_card R := by
    have hdeg := H.ridge_degree R.1
    change Fintype.card {T : RestrictedTopFace K U (k + 1) //
      FaceIncident R.1 T} = if IsEquatorRidge (E := E) R.1 then 1 else 2
    by_cases h : ∀ v ∈ R.1.1, E v
    · rw [if_pos h] at hdeg
      rw [if_pos (show IsEquatorRidge (E := E) R.1 from h)]
      exact hdeg
    · rw [if_neg h] at hdeg
      rw [if_neg (show ¬IsEquatorRidge (E := E) R.1 from h)]
      exact hdeg

/-- The global Ky Fan handshaking step for an arbitrary triangulated
hemisphere satisfying the `1/2` ridge-degree law. -/
theorem odd_alternatingTop_of_odd_equatorRidge
    {K : FiniteComplex} {U E : K.Vertex → Prop} {k m : ℕ}
    [DecidablePred E]
    (hk : 1 ≤ k) {label : K.Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels K label)
    (H : HemisphereGeometry K U E (k + 1))
    (hboundary : Odd (Fintype.card
      {R : PositiveAlternatingRidge K U (k + 1) m label //
        IsEquatorRidge (E := E) R.1})) :
    Odd (Fintype.card
      {T : RestrictedTopFace K U (k + 1) // IsAlternatingTop label T}) := by
  have hpos : 0 < Fintype.card
      {R : PositiveAlternatingRidge K U (k + 1) m label //
        IsEquatorRidge (E := E) R.1} := by
    rcases hboundary with ⟨a, ha⟩
    omega
  have hne : Nonempty (PositiveAlternatingRidge K U (k + 1) m label) := by
    obtain ⟨R⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨R.1⟩
  exact kyFan_parity_step_from_rho_sigma_data
    (alternatingRhoData label H hne)
    (IsAlternatingTop label)
    (fun T ↦ odd_altIncident_iff_alternatingTop hk hno T)
    hboundary

/-! ## The refined cross-polytope hemispheres -/

/-- Vertex predicate for the closed upper hemisphere in every subdivision of
the boundary of the `(d+1)`-cross-polytope. -/
def UpperVertex (d : ℕ) :
    ∀ r, (iteratedBoundary (d + 1) r).Vertex → Prop
  | 0, v => v ≠ (Fin.last d, false)
  | r + 1, F => ∀ v ∈ F.1, UpperVertex d r v

/-- Vertex predicate for the equator in every subdivision. -/
def EquatorVertex (d : ℕ) :
    ∀ r, (iteratedBoundary (d + 1) r).Vertex → Prop
  | 0, v => v.1 ≠ Fin.last d
  | r + 1, F => ∀ v ∈ F.1, EquatorVertex d r v

noncomputable instance upperVertexDecidable (d r : ℕ) :
    DecidablePred (UpperVertex d r) := by
  classical
  intro v
  infer_instance

noncomputable instance equatorVertexDecidable (d r : ℕ) :
    DecidablePred (EquatorVertex d r) := by
  classical
  intro v
  infer_instance

theorem equatorVertex_upperVertex (d r : ℕ)
    {v : (iteratedBoundary (d + 1) r).Vertex}
    (hv : EquatorVertex d r v) : UpperVertex d r v := by
  induction r with
  | zero =>
      intro heq
      exact hv (congrArg Prod.fst heq)
  | succ r ih =>
      intro w hw
      exact ih (hv w hw)

/-! ### The unsubdivided hemisphere -/

def BaseUpperVertex (d : ℕ)
    (v : (crossPolytopeBoundary (d + 1)).Vertex) : Prop :=
  v ≠ (Fin.last d, false)

def BaseEquatorVertex (d : ℕ)
    (v : (crossPolytopeBoundary (d + 1)).Vertex) : Prop :=
  v.1 ≠ Fin.last d

noncomputable instance baseUpperVertexDecidable (d : ℕ) :
    DecidablePred (BaseUpperVertex d) := by
  classical
  intro v
  infer_instance

noncomputable instance baseEquatorVertexDecidable (d : ℕ) :
    DecidablePred (BaseEquatorVertex d) := by
  classical
  intro v
  infer_instance

def ridgeCoordinateImage (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Finset (Fin (d + 1)) :=
  R.1.image (fun v : (crossPolytopeBoundary (d + 1)).Vertex ↦ v.1)

theorem card_ridgeCoordinateImage (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    (ridgeCoordinateImage d R).card = d := by
  have hinj : Set.InjOn
      (fun v : (crossPolytopeBoundary (d + 1)).Vertex ↦ v.1) (↑R.1) := by
    rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
    simp only at hij
    subst j
    have hbc : b = c := by
      by_contra hbc
      have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
        cases b <;> cases c <;> simp_all
      rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact R.2.1.2 i ⟨hib, hjc⟩
      · exact R.2.1.2 i ⟨hjc, hib⟩
    exact Prod.ext rfl hbc
  rw [ridgeCoordinateImage, Finset.card_image_iff.mpr hinj]
  simpa using R.2.2.1

theorem exists_missingCoordinate (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    ∃ i : Fin (d + 1), i ∉ ridgeCoordinateImage d R := by
  by_contra h
  have hall : ridgeCoordinateImage d R = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  have hc := card_ridgeCoordinateImage d R
  rw [hall] at hc
  simp at hc

noncomputable def missingCoordinate (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Fin (d + 1) :=
  Classical.choose (exists_missingCoordinate d R)

theorem missingCoordinate_not_mem (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    missingCoordinate d R ∉ ridgeCoordinateImage d R :=
  Classical.choose_spec (exists_missingCoordinate d R)

theorem ridgeCoordinateImage_eq_erase_missing (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    ridgeCoordinateImage d R =
      (Finset.univ : Finset (Fin (d + 1))).erase (missingCoordinate d R) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun him ↦ missingCoordinate_not_mem d R (him ▸ hi), Finset.mem_univ i⟩
  · rw [card_ridgeCoordinateImage]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp

theorem coordinate_mem_ridge_of_ne_missing (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    {i : Fin (d + 1)} (hi : i ≠ missingCoordinate d R) :
    i ∈ ridgeCoordinateImage d R := by
  rw [ridgeCoordinateImage_eq_erase_missing]
  simp [hi]

theorem equatorRidge_iff_missingCoordinate_last (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    IsEquatorRidge (E := BaseEquatorVertex d) R ↔
      missingCoordinate d R = Fin.last d := by
  constructor
  · intro hEq
    by_contra hne
    obtain ⟨v, hvR, hvcoord⟩ := Finset.mem_image.mp
      (coordinate_mem_ridge_of_ne_missing d R (Ne.symm hne))
    have := hEq v hvR
    exact this hvcoord
  · intro hlast v hvR
    intro hvlast
    apply missingCoordinate_not_mem d R
    rw [hlast, ridgeCoordinateImage]
    exact Finset.mem_image.mpr ⟨v, hvR, hvlast⟩

def AllowedMissingSign (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : Bool) : Prop :=
  missingCoordinate d R ≠ Fin.last d ∨ b = true

noncomputable instance allowedMissingSignDecidable (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    DecidablePred (AllowedMissingSign d R) := by
  classical
  intro b
  infer_instance

theorem missingAtom_not_mem (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : Bool) :
    (missingCoordinate d R, b) ∉ R.1 := by
  intro h
  exact missingCoordinate_not_mem d R
    (Finset.mem_image.mpr ⟨(missingCoordinate d R, b), h, rfl⟩)

noncomputable def addMissingTop (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : {b : Bool // AllowedMissingSign d R b}) :
    RestrictedTopFace (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1) := by
  classical
  let a : (crossPolytopeBoundary (d + 1)).Vertex := (missingCoordinate d R, b.1)
  refine ⟨insert a R.1, ?_, ?_, ?_⟩
  · refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro i hi
    by_cases hiMissing : i = missingCoordinate d R
    · subst i
      have hfalse : (missingCoordinate d R, false) = a ∨
          (missingCoordinate d R, false) ∈ R.1 := Finset.mem_insert.mp hi.1
      have htrue : (missingCoordinate d R, true) = a ∨
          (missingCoordinate d R, true) ∈ R.1 := Finset.mem_insert.mp hi.2
      rcases hfalse with hfalse | hfalse <;>
        rcases htrue with htrue | htrue
      · dsimp [a] at hfalse htrue
        cases b.1 <;> simp_all
      · exact missingAtom_not_mem d R true htrue
      · exact missingAtom_not_mem d R false hfalse
      · exact R.2.1.2 (missingCoordinate d R) ⟨hfalse, htrue⟩
    · have hfalseR : (i, false) ∈ R.1 := by
        have := Finset.mem_insert.mp hi.1
        rcases this with h | h
        · have := congrArg Prod.fst h
          exact False.elim (hiMissing this)
        · exact h
      have htrueR : (i, true) ∈ R.1 := by
        have := Finset.mem_insert.mp hi.2
        rcases this with h | h
        · have := congrArg Prod.fst h
          exact False.elim (hiMissing this)
        · exact h
      exact R.2.1.2 i ⟨hfalseR, htrueR⟩
  · dsimp [a]
    let atom : (crossPolytopeBoundary (d + 1)).Vertex :=
      (missingCoordinate d R, b.1)
    have hatom : atom ∉ R.1 := by
      exact missingAtom_not_mem d R b.1
    change (insert atom R.1).card = d + 1
    rw [Finset.card_insert_of_notMem hatom, R.2.2.1]
    omega
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvR
    · intro heq
      have hcoord := congrArg Prod.fst heq
      have hsign := congrArg Prod.snd heq
      dsimp [a] at hcoord hsign
      rcases b.2 with hm | hb
      · exact hm hcoord
      · cases b.1 <;> simp_all
    · exact R.2.2.2 v hvR

theorem addMissingTop_incident (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : {b : Bool // AllowedMissingSign d R b}) :
    FaceIncident R (addMissingTop d R b) := by
  intro v hv
  exact Finset.mem_insert_of_mem hv

theorem addMissingTop_injective (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Function.Injective (addMissingTop d R) := by
  classical
  intro b c hbc
  apply Subtype.ext
  by_contra hne
  have hsets : (addMissingTop d R b).1 = (addMissingTop d R c).1 :=
    congrArg (fun T => T.1) hbc
  have hmem : (missingCoordinate d R, b.1) ∈
      (addMissingTop d R c).1 := by
    rw [← hsets]
    let atom : (crossPolytopeBoundary (d + 1)).Vertex :=
      (missingCoordinate d R, b.1)
    change atom ∈ insert atom R.1
    exact Finset.mem_insert.mpr (Or.inl rfl)
  rcases Finset.mem_insert.mp hmem with heq | hR
  · exact hne (congrArg Prod.snd heq)
  · exact missingAtom_not_mem d R b.1 hR

theorem addMissingTop_surjective_incident (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Function.Surjective
      (fun b : {b : Bool // AllowedMissingSign d R b} ↦
        (⟨addMissingTop d R b, addMissingTop_incident d R b⟩ :
          {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
            (BaseUpperVertex d) (d + 1) // FaceIncident R T})) := by
  classical
  rintro ⟨T, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ x ∈ T.1, x ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro x hxT
    by_contra hxR
    exact hnone ⟨x, hxT, hxR⟩
  obtain ⟨x, hxT, hxR⟩ := hex
  have hxcoord : x.1 = missingCoordinate d R := by
    by_contra hne
    obtain ⟨v, hvR, hvcoord⟩ := Finset.mem_image.mp
      (coordinate_mem_ridge_of_ne_missing d R hne)
    have hvT := hRT hvR
    have hsame : v.2 = x.2 := by
      cases hvb : v.2 <;> cases hxb : x.2
      · rfl
      · exfalso
        have hvEq : v = (x.1, false) := Prod.ext hvcoord hvb
        have hxEq : x = (x.1, true) := Prod.ext rfl hxb
        exact T.2.1.2 x.1 ⟨hvEq ▸ hvT, hxEq ▸ hxT⟩
      · exfalso
        have hxEq : x = (x.1, false) := Prod.ext rfl hxb
        have hvEq : v = (x.1, true) := Prod.ext hvcoord hvb
        exact T.2.1.2 x.1 ⟨hxEq ▸ hxT, hvEq ▸ hvT⟩
      · rfl
    have hxv : x = v := Prod.ext hvcoord.symm hsame.symm
    exact hxR (hxv ▸ hvR)
  have hxAllowed : AllowedMissingSign d R x.2 := by
    by_cases hm : missingCoordinate d R = Fin.last d
    · right
      have hxUpper := T.2.2.2 x hxT
      cases hxsign : x.2
      · exfalso
        apply hxUpper
        apply Prod.ext
        · exact hxcoord.trans hm
        · exact hxsign
      · rfl
    · exact Or.inl hm
  let b : {b : Bool // AllowedMissingSign d R b} := ⟨x.2, hxAllowed⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hx : x = (missingCoordinate d R, b.1) :=
    Prod.ext hxcoord rfl
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvR
    · simpa [← hx] using hxT
    · exact hRT hvR
  · rw [(addMissingTop d R b).2.2.1, T.2.2.1]

noncomputable def missingTopEquiv (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    {b : Bool // AllowedMissingSign d R b} ≃
      {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
        (BaseUpperVertex d) (d + 1) // FaceIncident R T} :=
  Equiv.ofBijective
    (fun b ↦ ⟨addMissingTop d R b, addMissingTop_incident d R b⟩)
    ⟨fun _ _ h ↦ addMissingTop_injective d R (congrArg Subtype.val h),
      addMissingTop_surjective_incident d R⟩

theorem card_allowedMissingSign (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Fintype.card {b : Bool // AllowedMissingSign d R b} =
      if IsEquatorRidge (E := BaseEquatorVertex d) R then 1 else 2 := by
  classical
  by_cases hEq : IsEquatorRidge (E := BaseEquatorVertex d) R
  · rw [if_pos hEq]
    have h := (equatorRidge_iff_missingCoordinate_last d R).mp hEq
    simp [AllowedMissingSign, h]
  · rw [if_neg hEq]
    have h : missingCoordinate d R ≠ Fin.last d := by
      intro hm
      exact hEq ((equatorRidge_iff_missingCoordinate_last d R).mpr hm)
    simp [AllowedMissingSign, h]

noncomputable def baseHemisphereGeometry (d : ℕ) :
    HemisphereGeometry (crossPolytopeBoundary (d + 1))
      (BaseUpperVertex d) (BaseEquatorVertex d) (d + 1) where
  ridge_degree R := by
    have hequiv : Fintype.card
        {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
          (BaseUpperVertex d) (d + 1) // FaceIncident R T} =
        Fintype.card {b : Bool // AllowedMissingSign d R b} :=
      Fintype.card_congr (missingTopEquiv d R).symm
    rw [hequiv]
    have hc := card_allowedMissingSign d R
    by_cases h : ∀ v ∈ R.1, BaseEquatorVertex d v
    · rw [if_pos h]
      rw [if_pos (show IsEquatorRidge (E := BaseEquatorVertex d) R from h)] at hc
      exact hc
    · rw [if_neg h]
      rw [if_neg (show ¬IsEquatorRidge (E := BaseEquatorVertex d) R from h)] at hc
      exact hc

/-! ### Barycentric preservation of the ridge-degree law -/

def BaryUpper {K : FiniteComplex} (U : K.Vertex → Prop)
    (F : (barycentricSubdivision K).Vertex) : Prop :=
  ∀ v ∈ F.1, U v

noncomputable instance baryUpperDecidable
    {K : FiniteComplex} (U : K.Vertex → Prop) [DecidablePred U] :
    DecidablePred (BaryUpper U) := by
  classical
  intro F
  infer_instance

noncomputable def baryRank {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (F : (barycentricSubdivision K).Vertex) : Fin d :=
  ⟨F.1.card - 1, by
    have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
    have hl := hcard F.2
    omega⟩

theorem baryRank_injective_on_chain
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : IsFaceChain K S) :
    Set.InjOn (baryRank d hcard) (↑S) := by
  intro F hF G hG hrank
  apply Subtype.ext
  have hcardEq : F.1.card = G.1.card := by
    have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
    have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
    have hv := congrArg Fin.val hrank
    dsimp [baryRank] at hv
    omega
  rcases hS.2 F hF G hG with hFG | hGF
  · exact Finset.eq_of_subset_of_card_le hFG hcardEq.ge
  · exact (Finset.eq_of_subset_of_card_le hGF hcardEq.le).symm

noncomputable def baryRidgeRankImage
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Finset (Fin d) :=
  R.1.image (baryRank d hcard)

theorem card_baryRidgeRankImage
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    (baryRidgeRankImage d hcard R).card = d - 1 := by
  rw [baryRidgeRankImage, Finset.card_image_iff.mpr
    (baryRank_injective_on_chain d hcard R.2.1)]
  exact R.2.2.1

theorem exists_missingBaryRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    ∃ i : Fin d, i ∉ baryRidgeRankImage d hcard R := by
  by_contra h
  have hall : baryRidgeRankImage d hcard R = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  have hc := card_baryRidgeRankImage d hcard R
  rw [hall] at hc
  simp at hc
  omega

noncomputable def missingBaryRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) : Fin d :=
  Classical.choose (exists_missingBaryRank d hd hcard R)

theorem missingBaryRank_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    missingBaryRank d hd hcard R ∉ baryRidgeRankImage d hcard R :=
  Classical.choose_spec (exists_missingBaryRank d hd hcard R)

theorem baryRidgeRankImage_eq_erase_missing
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    baryRidgeRankImage d hcard R =
      (Finset.univ : Finset (Fin d)).erase (missingBaryRank d hd hcard R) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun him ↦ missingBaryRank_not_mem d hd hcard R (him ▸ hi),
      Finset.mem_univ i⟩
  · rw [card_baryRidgeRankImage]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp

theorem baryRank_eq_missing_of_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : (barycentricSubdivision K).Vertex)
    (hF : baryRank d hcard F ∉ baryRidgeRankImage d hcard R) :
    baryRank d hcard F = missingBaryRank d hd hcard R := by
  by_contra hne
  apply hF
  rw [baryRidgeRankImage_eq_erase_missing d hd hcard R]
  simp [hne]

/-- Old faces which can fill the unique missing rank of a barycentric ridge. -/
def IsBaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : (barycentricSubdivision K).Vertex) : Prop :=
  baryRank d hcard F = missingBaryRank d hd hcard R ∧
    (∀ G ∈ R.1, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1) ∧ BaryUpper U F

noncomputable instance isBaryInsertionFaceDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} [DecidablePred U]
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    DecidablePred (IsBaryInsertionFace d hd hcard R) := by
  classical
  intro F
  infer_instance

abbrev BaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :=
  {F : (barycentricSubdivision K).Vertex // IsBaryInsertionFace d hd hcard R F}

theorem baryInsertionFace_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) : F.1 ∉ R.1 := by
  intro hFR
  exact missingBaryRank_not_mem d hd hcard R
    (Finset.mem_image.mpr ⟨F.1, hFR, F.2.1⟩)

noncomputable def addBaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) :
    RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d := by
  classical
  refine ⟨insert F.1 R.1, ?_, ?_, ?_⟩
  · refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | hAR <;>
      rcases Finset.mem_insert.mp hB with rfl | hBR
    · exact Or.inl Finset.Subset.rfl
    · exact F.2.2.1 B hBR
    · rcases F.2.2.1 A hAR with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact R.2.1.2 A hAR B hBR
  · rw [Finset.card_insert_of_notMem (baryInsertionFace_not_mem d hd hcard R F),
      R.2.2.1]
    omega
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAR
    · exact F.2.2.2
    · exact R.2.2.2 A hAR

theorem addBaryInsertionFace_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) :
    FaceIncident R (addBaryInsertionFace d hd hcard R F) := by
  intro A hA
  exact Finset.mem_insert_of_mem hA

theorem addBaryInsertionFace_injective
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Function.Injective (addBaryInsertionFace d hd hcard R) := by
  classical
  intro F G hFG
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hsets : (addBaryInsertionFace d hd hcard R F).1 =
      (addBaryInsertionFace d hd hcard R G).1 :=
    congrArg (fun T => T.1) hFG
  have hmem : F.1 ∈ (addBaryInsertionFace d hd hcard R G).1 := by
    rw [← hsets]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  rcases Finset.mem_insert.mp hmem with h | h
  · exact hne (congrArg Subtype.val h)
  · exact baryInsertionFace_not_mem d hd hcard R F h

theorem addBaryInsertionFace_surjective_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Function.Surjective
      (fun F : BaryInsertionFace d hd hcard R ↦
        (⟨addBaryInsertionFace d hd hcard R F,
          addBaryInsertionFace_incident d hd hcard R F⟩ :
          {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d //
            FaceIncident R T})) := by
  classical
  rintro ⟨T, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ F ∈ T.1, F ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro F hFT
    by_contra hFR
    exact hnone ⟨F, hFT, hFR⟩
  obtain ⟨F, hFT, hFR⟩ := hex
  have hrankNot : baryRank d hcard F ∉ baryRidgeRankImage d hcard R := by
    intro hrank
    rcases Finset.mem_image.mp hrank with ⟨G, hGR, hGF⟩
    have hcardEq : F.1.card = G.1.card := by
      have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      have hv := congrArg Fin.val hGF
      dsimp [baryRank] at hv
      omega
    rcases T.2.1.2 F hFT G (hRT hGR) with hFG | hGFsub
    · exact hFR (by
        have : F = G := Subtype.ext (Finset.eq_of_subset_of_card_le hFG hcardEq.ge)
        simpa [this] using hGR)
    · exact hFR (by
        have : G = F := Subtype.ext
          (Finset.eq_of_subset_of_card_le hGFsub hcardEq.le)
        simpa [← this] using hGR)
  have hInsert : IsBaryInsertionFace d hd hcard R F := by
    refine ⟨baryRank_eq_missing_of_not_mem d hd hcard R F hrankNot, ?_, ?_⟩
    · intro G hGR
      exact T.2.1.2 F hFT G (hRT hGR)
    · exact T.2.2.2 F hFT
  let FI : BaryInsertionFace d hd hcard R := ⟨F, hInsert⟩
  refine ⟨FI, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hGR
    · exact hFT
    · exact hRT hGR
  · rw [(addBaryInsertionFace d hd hcard R FI).2.2.1, T.2.2.1]

noncomputable def baryInsertionFaceEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    BaryInsertionFace d hd hcard R ≃
      {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d //
        FaceIncident R T} :=
  Equiv.ofBijective
    (fun F ↦ ⟨addBaryInsertionFace d hd hcard R F,
      addBaryInsertionFace_incident d hd hcard R F⟩)
    ⟨fun _ _ h ↦ addBaryInsertionFace_injective d hd hcard R
      (congrArg Subtype.val h),
      addBaryInsertionFace_surjective_incident d hd hcard R⟩

theorem rank_mem_baryRidge_of_ne_missing
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    {i : Fin d} (hi : i ≠ missingBaryRank d hd hcard R) :
    i ∈ baryRidgeRankImage d hcard R := by
  rw [baryRidgeRankImage_eq_erase_missing d hd hcard R]
  simp [hi]

noncomputable def baryRidgeMemberAtRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    (barycentricSubdivision K).Vertex :=
  Classical.choose (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))

theorem baryRidgeMemberAtRank_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    baryRidgeMemberAtRank d hd hcard R i hi ∈ R.1 :=
  (Classical.choose_spec (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))).1

theorem baryRidgeMemberAtRank_rank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    baryRank d hcard (baryRidgeMemberAtRank d hd hcard R i hi) = i :=
  (Classical.choose_spec (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))).2

theorem baryRidgeMemberAtRank_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    (baryRidgeMemberAtRank d hd hcard R i hi).1.card = i.val + 1 := by
  have hp : 0 < (baryRidgeMemberAtRank d hd hcard R i hi).1.card :=
    Finset.card_pos.mpr (K.face_nonempty
      (baryRidgeMemberAtRank d hd hcard R i hi).2)
  have hr := congrArg Fin.val
    (baryRidgeMemberAtRank_rank d hd hcard R i hi)
  dsimp [baryRank] at hr
  omega

noncomputable def terminalOldRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    RestrictedRidge K U (k + 2) := by
  let p : Fin (k + 2) := ⟨k, by omega⟩
  have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
    rw [hlast]
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    simp [Fin.last] at hv
  let M := baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp
  refine ⟨M.1, M.2, ?_, ?_⟩
  · rw [baryRidgeMemberAtRank_card]
    change k + 1 = k + 2 - 1
    omega
  · exact R.2.2.2 M (baryRidgeMemberAtRank_mem _ _ _ _ _ _)

theorem terminalOldRidge_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    (⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩ : BaryVertex K) ∈ R.1 := by
  let p : Fin (k + 2) := ⟨k, by omega⟩
  have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
    rw [hlast]
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    simp [Fin.last] at hv
  change baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp ∈ R.1
  exact baryRidgeMemberAtRank_mem (k + 2) (by omega) hcard R p hp

theorem member_subset_terminalOldRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    {G : (barycentricSubdivision K).Vertex} (hGR : G ∈ R.1) :
    G.1 ⊆ (terminalOldRidge k hcard R hlast).1 := by
  let M : (barycentricSubdivision K).Vertex :=
    ⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩
  have hMR : M ∈ R.1 := terminalOldRidge_mem k hcard R hlast
  rcases R.2.1.2 G hGR M hMR with hGM | hMG
  · exact hGM
  · have hGcard : G.1.card ≤ k + 1 := by
      have hrankMem : baryRank (k + 2) hcard G ∈
          baryRidgeRankImage (k + 2) hcard R :=
        Finset.mem_image.mpr ⟨G, hGR, rfl⟩
      rw [baryRidgeRankImage_eq_erase_missing (k + 2) (by omega) hcard R,
        hlast] at hrankMem
      have hval : (baryRank (k + 2) hcard G).val ≤ k := by
        have hne := (Finset.mem_erase.mp hrankMem).1
        have hlt := (baryRank (k + 2) hcard G).isLt
        have hneVal : (baryRank (k + 2) hcard G).val ≠ k + 1 := by
          intro hv
          apply hne
          apply Fin.ext
          simpa [Fin.last] using hv
        omega
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      dsimp [baryRank] at hval
      omega
    have hMcard : M.1.card = k + 1 := (terminalOldRidge k hcard R hlast).2.2.1
    have heq : M.1 = G.1 :=
      Finset.eq_of_subset_of_card_le hMG (by omega)
    change G.1 ⊆ M.1
    rw [heq]

noncomputable def terminalCandidateToOldTop
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    (F : BaryInsertionFace (k + 2) (by omega) hcard R) :
    {T : RestrictedTopFace K U (k + 2) //
      FaceIncident (terminalOldRidge k hcard R hlast) T} := by
  have hFcard : F.1.1.card = k + 2 := by
    have hp : 0 < F.1.1.card := Finset.card_pos.mpr (K.face_nonempty F.1.2)
    have hr := congrArg Fin.val F.2.1
    rw [hlast] at hr
    dsimp [baryRank] at hr
    simp [Fin.last] at hr
    omega
  refine ⟨⟨F.1.1, F.1.2, hFcard, F.2.2.2⟩, ?_⟩
  have hcomp := F.2.2.1
    (⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩ : BaryVertex K)
    (terminalOldRidge_mem k hcard R hlast)
  rcases hcomp with hFM | hMF
  · have hc := Finset.card_le_card hFM
    rw [hFcard, (terminalOldRidge k hcard R hlast).2.2.1] at hc
    omega
  · exact hMF

noncomputable def oldTopToTerminalCandidate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    (T : {T : RestrictedTopFace K U (k + 2) //
      FaceIncident (terminalOldRidge k hcard R hlast) T}) :
    BaryInsertionFace (k + 2) (by omega) hcard R := by
  let F : (barycentricSubdivision K).Vertex := ⟨T.1.1, T.1.2.1⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · apply Fin.ext
    have hpos : 0 < T.1.1.card := by rw [T.1.2.2.1]; omega
    dsimp [baryRank, F]
    rw [T.1.2.2.1, hlast]
    simp [Fin.last]
  · intro G hGR
    right
    exact (member_subset_terminalOldRidge k hcard R hlast hGR).trans T.2
  · exact T.1.2.2.2

noncomputable def terminalCandidateEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    BaryInsertionFace (k + 2) (by omega) hcard R ≃
      {T : RestrictedTopFace K U (k + 2) //
        FaceIncident (terminalOldRidge k hcard R hlast) T} where
  toFun := terminalCandidateToOldTop k hcard R hlast
  invFun := oldTopToTerminalCandidate k hcard R hlast
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-! The internal-rank count is the elementary fact that between nested faces
whose cardinalities differ by two there are exactly two intermediate faces. -/

def IsIntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) (F : BaryVertex K) : Prop :=
  A ⊆ F.1 ∧ F.1 ⊆ B ∧ F.1.card = q + 1

abbrev IntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) :=
  {F : BaryVertex K // IsIntermediateFace A B q F}

noncomputable instance intermediateFaceFintype {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) :
    Fintype (IntermediateFace A B q) := by
  classical
  infer_instance

noncomputable def eraseIntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2)
    (x : {x // x ∈ B \ A}) : IntermediateFace A B q := by
  classical
  have hxB : x.1 ∈ B := (Finset.mem_sdiff.mp x.2).1
  have hxA : x.1 ∉ A := (Finset.mem_sdiff.mp x.2).2
  have hnonempty : (B.erase x.1).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hxB, hBcard]
    omega
  refine ⟨⟨B.erase x.1,
    K.face_of_nonempty_subset hBface (Finset.erase_subset _ _) hnonempty⟩, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_erase]
    exact ⟨fun hax ↦ hxA (hax ▸ ha), hAB ha⟩
  · exact Finset.erase_subset _ _
  · rw [Finset.card_erase_of_mem hxB, hBcard]
    omega

theorem eraseIntermediateFace_injective {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Function.Injective (eraseIntermediateFace A B q hAB hBface hAcard hBcard) := by
  classical
  intro x y hxy
  apply Subtype.ext
  apply (Finset.erase_inj B (Finset.mem_sdiff.mp x.2).1).mp
  exact congrArg (fun F => F.1.1) hxy

theorem eraseIntermediateFace_surjective {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Function.Surjective (eraseIntermediateFace A B q hAB hBface hAcard hBcard) := by
  classical
  intro F
  have hnot : ¬B ⊆ F.1.1 := by
    intro hBF
    have hc := Finset.card_le_card hBF
    rw [hBcard, F.2.2.2] at hc
    omega
  have hex : ∃ x ∈ B, x ∉ F.1.1 := by
    by_contra hnone
    apply hnot
    intro x hxB
    by_contra hxF
    exact hnone ⟨x, hxB, hxF⟩
  obtain ⟨x, hxB, hxF⟩ := hex
  have hxA : x ∉ A := fun hx ↦ hxF (F.2.1 hx)
  let xBA : {x // x ∈ B \ A} := ⟨x, Finset.mem_sdiff.mpr ⟨hxB, hxA⟩⟩
  refine ⟨xBA, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    change v ∈ B.erase x
    rw [Finset.mem_erase]
    exact ⟨fun hvx ↦ hxF (hvx ▸ hv), F.2.2.1 hv⟩
  · rw [(eraseIntermediateFace A B q hAB hBface hAcard hBcard xBA).2.2.2,
      F.2.2.2]

noncomputable def intermediateFaceEquiv {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    {x // x ∈ B \ A} ≃ IntermediateFace A B q :=
  Equiv.ofBijective
    (eraseIntermediateFace A B q hAB hBface hAcard hBcard)
    ⟨eraseIntermediateFace_injective A B q hAB hBface hAcard hBcard,
      eraseIntermediateFace_surjective A B q hAB hBface hAcard hBcard⟩

theorem card_intermediateFace_eq_two {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Fintype.card (IntermediateFace A B q) = 2 := by
  classical
  rw [← Fintype.card_congr
    (intermediateFaceEquiv A B q hAB hBface hAcard hBcard)]
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset hAB, hBcard, hAcard]
  omega

theorem baryRank_card
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (F : (barycentricSubdivision K).Vertex) :
    F.1.card = (baryRank d hcard F).val + 1 := by
  have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  dsimp [baryRank]
  omega

noncomputable def internalUpperFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    (barycentricSubdivision K).Vertex := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  have hi : i.val < k + 1 := by
    have hlt := i.isLt
    have hneVal : i.val ≠ k + 1 := by
      intro hval
      apply hinternal
      apply Fin.ext
      simpa [i, Fin.last] using hval
    omega
  let u : Fin (k + 2) := ⟨i.val + 1, by omega⟩
  have hu : u ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [u] at hv
    omega
  exact baryRidgeMemberAtRank (k + 2) (by omega) hcard R u hu

theorem internalUpperFace_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    internalUpperFace k hcard R hinternal ∈ R.1 := by
  unfold internalUpperFace
  exact baryRidgeMemberAtRank_mem _ _ _ _ _ _

theorem internalUpperFace_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    (internalUpperFace k hcard R hinternal).1.card =
      (missingBaryRank (k + 2) (by omega) hcard R).val + 2 := by
  unfold internalUpperFace
  rw [baryRidgeMemberAtRank_card]

noncomputable def internalLowerSet
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    Finset K.Vertex := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  if hi : i.val = 0 then exact ∅
  else
    let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
    have hl : l ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [l] at hv
      omega
    exact (baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl).1

theorem internalLowerSet_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    (internalLowerSet k hcard R).card =
      (missingBaryRank (k + 2) (by omega) hcard R).val := by
  simp only [internalLowerSet]
  split_ifs with hi
  · simp [hi]
  · rw [baryRidgeMemberAtRank_card]
    change (missingBaryRank (k + 2) (by omega) hcard R).val - 1 + 1 =
      (missingBaryRank (k + 2) (by omega) hcard R).val
    omega

theorem internalLowerSet_subset_upperFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    internalLowerSet k hcard R ⊆ (internalUpperFace k hcard R hinternal).1 := by
  simp only [internalLowerSet]
  split_ifs with hi
  · exact Finset.empty_subset _
  · let i := missingBaryRank (k + 2) (by omega) hcard R
    let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
    have hl : l ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [l] at hv
      omega
    let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
    let B := internalUpperFace k hcard R hinternal
    have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
    have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
    rcases R.2.1.2 L hLR B hBR with hLB | hBL
    · exact hLB
    · have hLc : L.1.card = i.val := by
        rw [baryRidgeMemberAtRank_card]
        dsimp [l]
        omega
      have hBc : B.1.card = i.val + 2 := internalUpperFace_card k hcard R hinternal
      have hc := Finset.card_le_card hBL
      rw [hLc, hBc] at hc
      omega

noncomputable def candidate_to_internalIntermediate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1))
    (F : BaryInsertionFace (k + 2) (by omega) hcard R) :
    IntermediateFace (internalLowerSet k hcard R)
      (internalUpperFace k hcard R hinternal).1
      (missingBaryRank (k + 2) (by omega) hcard R).val := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  have hFcard : F.1.1.card = i.val + 1 := by
    rw [baryRank_card (k + 2) hcard F.1]
    rw [F.2.1]
  refine ⟨F.1, ?_, ?_, hFcard⟩
  · simp only [internalLowerSet]
    split_ifs with hi
    · exact Finset.empty_subset _
    · let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
      have hl : l ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [l] at hv
        omega
      let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
      have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      rcases F.2.2.1 L hLR with hFL | hLF
      · have hLc : L.1.card = i.val := by
          rw [baryRidgeMemberAtRank_card]
          dsimp [l]
          omega
        have hc := Finset.card_le_card hFL
        rw [hFcard, hLc] at hc
        omega
      · exact hLF
  · let B := internalUpperFace k hcard R hinternal
    have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
    rcases F.2.2.1 B hBR with hFB | hBF
    · exact hFB
    · have hBc : B.1.card = i.val + 2 := internalUpperFace_card k hcard R hinternal
      have hc := Finset.card_le_card hBF
      rw [hBc, hFcard] at hc
      omega

noncomputable def internalIntermediate_to_candidate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1))
    (F : IntermediateFace (internalLowerSet k hcard R)
      (internalUpperFace k hcard R hinternal).1
      (missingBaryRank (k + 2) (by omega) hcard R).val) :
    BaryInsertionFace (k + 2) (by omega) hcard R := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  refine ⟨F.1, ?_, ?_, ?_⟩
  · apply Fin.ext
    have hp : 0 < F.1.1.card := Finset.card_pos.mpr (K.face_nonempty F.1.2)
    dsimp [baryRank]
    rw [F.2.2.2]
    omega
  · intro G hGR
    have hGrankMem : baryRank (k + 2) hcard G ∈
        baryRidgeRankImage (k + 2) hcard R :=
      Finset.mem_image.mpr ⟨G, hGR, rfl⟩
    have hGrankNe : baryRank (k + 2) hcard G ≠ i := by
      intro heq
      exact missingBaryRank_not_mem (k + 2) (by omega) hcard R
        (heq ▸ hGrankMem)
    by_cases hlt : (baryRank (k + 2) hcard G).val < i.val
    · right
      have hi0 : i.val ≠ 0 := by omega
      let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
      have hl : l ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [l] at hv
        omega
      let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
      have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      have hGL : G.1 ⊆ L.1 := by
        rcases R.2.1.2 G hGR L hLR with hGL | hLG
        · exact hGL
        · have hGc : G.1.card = (baryRank (k + 2) hcard G).val + 1 :=
            baryRank_card _ _ _
          have hLc : L.1.card = i.val := by
            rw [baryRidgeMemberAtRank_card]
            dsimp [l]
            omega
          have hc := Finset.card_le_card hLG
          rw [hLc, hGc] at hc
          have heq : L.1 = G.1 :=
            Finset.eq_of_subset_of_card_le hLG (by omega)
          simpa [heq]
      have hLF : L.1 ⊆ F.1.1 := by
        have hbase := F.2.1
        simpa [internalLowerSet, i, hi0, l, L] using hbase
      exact hGL.trans hLF
    · left
      have hgt : i.val < (baryRank (k + 2) hcard G).val := by
        have hneVal : (baryRank (k + 2) hcard G).val ≠ i.val := by
          intro hv
          exact hGrankNe (Fin.ext hv)
        omega
      let B := internalUpperFace k hcard R hinternal
      have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
      have hBG : B.1 ⊆ G.1 := by
        rcases R.2.1.2 B hBR G hGR with hBG | hGB
        · exact hBG
        · have hBc : B.1.card = i.val + 2 :=
            internalUpperFace_card k hcard R hinternal
          have hGc : G.1.card = (baryRank (k + 2) hcard G).val + 1 :=
            baryRank_card _ _ _
          have hc := Finset.card_le_card hGB
          rw [hGc, hBc] at hc
          have heq : G.1 = B.1 :=
            Finset.eq_of_subset_of_card_le hGB (by omega)
          simpa [heq]
      exact F.2.2.1.trans hBG
  · intro v hv
    exact R.2.2.2 (internalUpperFace k hcard R hinternal)
      (internalUpperFace_mem k hcard R hinternal) v (F.2.2.1 hv)

noncomputable def internalCandidateEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    BaryInsertionFace (k + 2) (by omega) hcard R ≃
      IntermediateFace (internalLowerSet k hcard R)
        (internalUpperFace k hcard R hinternal).1
        (missingBaryRank (k + 2) (by omega) hcard R).val where
  toFun := candidate_to_internalIntermediate k hcard R hinternal
  invFun := internalIntermediate_to_candidate k hcard R hinternal
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv F := by
    apply Subtype.ext
    rfl

/-! The missing rank is terminal exactly on the equatorial boundary.  This is
the point where the codimension-one bound on equatorial faces is used. -/

theorem baryEquatorRidge_iff
    {K : FiniteComplex} {U E : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (hEcard : ∀ {s : Finset K.Vertex}, K.IsFace s →
      (∀ v ∈ s, E v) → s.card ≤ k + 1)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    IsEquatorRidge (E := BaryUpper E) R ↔
      ∃ hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1),
        IsEquatorRidge (E := E) (terminalOldRidge k hcard R hlast) := by
  constructor
  · intro hEq
    have hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1) := by
      by_contra hinternal
      let p : Fin (k + 2) := Fin.last (k + 1)
      have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
        exact fun h ↦ hinternal h.symm
      let M := baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp
      have hMR : M ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      have hME : ∀ v ∈ M.1, E v := hEq M hMR
      have hsmall : M.1.card ≤ k + 1 := hEcard M.2 hME
      have hlarge : M.1.card = k + 2 := by
        rw [baryRidgeMemberAtRank_card]
        simp [p, Fin.last]
      omega
    refine ⟨hlast, ?_⟩
    intro v hv
    exact hEq
      ⟨(terminalOldRidge k hcard R hlast).1,
        (terminalOldRidge k hcard R hlast).2.1⟩
      (terminalOldRidge_mem k hcard R hlast) v hv
  · rintro ⟨hlast, hterminal⟩
    intro G hGR v hv
    exact hterminal v
      (member_subset_terminalOldRidge k hcard R hlast hGR hv)

theorem card_internalBaryInsertionFace_eq_two
    {K : FiniteComplex} {U : K.Vertex → Prop} [DecidablePred U] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) = 2 := by
  classical
  rw [Fintype.card_congr (internalCandidateEquiv k hcard R hinternal)]
  exact card_intermediateFace_eq_two
    (internalLowerSet k hcard R)
    (internalUpperFace k hcard R hinternal).1
    (missingBaryRank (k + 2) (by omega) hcard R).val
    (internalLowerSet_subset_upperFace k hcard R hinternal)
    (internalUpperFace k hcard R hinternal).2
    (internalLowerSet_card k hcard R)
    (internalUpperFace_card k hcard R hinternal)

theorem card_terminalBaryInsertionFace
    {K : FiniteComplex} {U E : K.Vertex → Prop}
    [DecidablePred U] [DecidablePred E] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (H : HemisphereGeometry K U E (k + 2))
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) =
      if IsEquatorRidge (E := E) (terminalOldRidge k hcard R hlast) then 1 else 2 := by
  classical
  rw [Fintype.card_congr (terminalCandidateEquiv k hcard R hlast)]
  have hdeg := H.ridge_degree (terminalOldRidge k hcard R hlast)
  by_cases h : ∀ v ∈ (terminalOldRidge k hcard R hlast).1, E v
  · rw [if_pos h] at hdeg
    rw [if_pos (show IsEquatorRidge (E := E)
      (terminalOldRidge k hcard R hlast) from h)]
    exact hdeg
  · rw [if_neg h] at hdeg
    rw [if_neg (show ¬IsEquatorRidge (E := E)
      (terminalOldRidge k hcard R hlast) from h)]
    exact hdeg

/-- Barycentric subdivision preserves the one-or-two coface law for a
triangulated hemisphere. -/
noncomputable def barycentricHemisphereGeometry
    {K : FiniteComplex} {U E : K.Vertex → Prop}
    [DecidablePred U] [DecidablePred E] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (hEcard : ∀ {s : Finset K.Vertex}, K.IsFace s →
      (∀ v ∈ s, E v) → s.card ≤ k + 1)
    (H : HemisphereGeometry K U E (k + 2)) :
    HemisphereGeometry (barycentricSubdivision K) (BaryUpper U) (BaryUpper E)
      (k + 2) where
  ridge_degree R := by
    classical
    have hcofaces : Fintype.card
        {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) (k + 2) //
          FaceIncident R T} =
        Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) :=
      Fintype.card_congr (baryInsertionFaceEquiv (k + 2) (by omega) hcard R).symm
    rw [hcofaces]
    by_cases hEq : ∀ v ∈ R.1, BaryUpper E v
    · rw [if_pos hEq]
      obtain ⟨hlast, hterminal⟩ :=
        (baryEquatorRidge_iff k hcard hEcard R).mp hEq
      rw [card_terminalBaryInsertionFace k hcard H R hlast, if_pos hterminal]
    · rw [if_neg hEq]
      by_cases hlast :
          missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)
      · rw [card_terminalBaryInsertionFace k hcard H R hlast]
        rw [if_neg (fun hterminal ↦
          hEq ((baryEquatorRidge_iff k hcard hEcard R).mpr ⟨hlast, hterminal⟩))]
      · exact card_internalBaryInsertionFace_eq_two k hcard R hlast

/-! ### Iterating the hemisphere geometry -/

/-- A chain has at most `d` members if every face occurring as one of its
vertices has at most `d` old vertices. -/
theorem card_baryFace_le_of_vertex_card_bound
    {K : FiniteComplex} (d : ℕ)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : (barycentricSubdivision K).IsFace S)
    (hbound : ∀ F ∈ S, F.1.card ≤ d) :
    S.card ≤ d := by
  classical
  have hdpos : 0 < d := by
    obtain ⟨G, hGS⟩ := hS.1
    have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
    have hGl := hbound G hGS
    omega
  let rank : BaryVertex K → Fin d := fun F ↦
    if hFS : F ∈ S then
      ⟨F.1.card - 1, by
        have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
        have hl := hbound F hFS
        omega⟩
    else ⟨0, hdpos⟩
  have hinj : Set.InjOn rank (↑S : Set (barycentricSubdivision K).Vertex) := by
    intro F hFS G hGS hrank
    have hFS' : F ∈ S := hFS
    have hGS' : G ∈ S := hGS
    apply Subtype.ext
    have hcardEq : F.1.card = G.1.card := by
      have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      have hv := congrArg Fin.val hrank
      simp only [rank, hFS', hGS', dite_true] at hv
      omega
    rcases hS.2 F hFS G hGS with hFG | hGF
    · exact Finset.eq_of_subset_of_card_le hFG hcardEq.ge
    · exact (Finset.eq_of_subset_of_card_le hGF hcardEq.le).symm
  calc
    S.card = (S.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Equatorial faces in the `r`th subdivision of the `(d+1)`-cross-polytope
have at most `d` vertices. -/
theorem card_equatorFace_iteratedBoundary_le (d r : ℕ)
    {s : Finset (iteratedBoundary (d + 1) r).Vertex}
    (hs : (iteratedBoundary (d + 1) r).IsFace s)
    (hEq : ∀ v ∈ s, EquatorVertex d r v) :
    s.card ≤ d := by
  induction r with
  | zero =>
      change Finset (crossPolytopeBoundary (d + 1)).Vertex at s
      change (crossPolytopeBoundary (d + 1)).IsFace s at hs
      change ∀ v ∈ s, BaseEquatorVertex d v at hEq
      have hinj : Set.InjOn Prod.fst
          (↑s : Set (crossPolytopeBoundary (d + 1)).Vertex) := by
        rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
        simp only [Prod.fst] at hij
        subst j
        have hbc : b = c := by
          by_contra hbc
          have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
            cases b <;> cases c <;> simp_all
          rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hs.2 i ⟨hib, hjc⟩
          · exact hs.2 i ⟨hjc, hib⟩
        exact Prod.ext rfl hbc
      have hsubset : s.image Prod.fst ⊆
          (Finset.univ : Finset (Fin (d + 1))).erase (Fin.last d) := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨hEq v hv, Finset.mem_univ _⟩
      calc
        s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
        _ ≤ ((Finset.univ : Finset (Fin (d + 1))).erase (Fin.last d)).card :=
          Finset.card_le_card hsubset
        _ = d := by simp
  | succ r ih =>
      apply card_baryFace_le_of_vertex_card_bound d hs
      intro F hFs
      exact ih F.2 (hEq F hFs)

/-- Every iterated barycentric subdivision carries the same exact
upper-hemisphere ridge-degree law. -/
noncomputable def iteratedHemisphereGeometry (k r : ℕ) :
    HemisphereGeometry (iteratedBoundary (k + 2) r)
      (UpperVertex (k + 1) r) (EquatorVertex (k + 1) r) (k + 2) := by
  induction r with
  | zero =>
      have H := baseHemisphereGeometry (k + 1)
      refine ⟨?_⟩
      intro R
      have hdeg := H.ridge_degree R
      by_cases hEq : ∀ v ∈ R.1, EquatorVertex (k + 1) 0 v
      · rw [if_pos hEq]
        split at hdeg
        · exact hdeg
        · rename_i hnot
          exact (hnot hEq).elim
      · rw [if_neg hEq]
        split at hdeg
        · rename_i hyes
          exact (hEq hyes).elim
        · exact hdeg
  | succ r ih =>
      have H := barycentricHemisphereGeometry k
        (fun {s} hs ↦ card_face_iteratedBoundary_le (k + 2) r hs)
        (fun {s} hs hEq ↦
          card_equatorFace_iteratedBoundary_le (k + 1) r hs hEq)
        ih
      refine ⟨?_⟩
      intro R
      have hdeg := H.ridge_degree R
      by_cases hEq : ∀ v ∈ R.1, EquatorVertex (k + 1) (r + 1) v
      · rw [if_pos hEq]
        split at hdeg
        · exact hdeg
        · rename_i hnot
          exact (hnot hEq).elim
      · rw [if_neg hEq]
        split at hdeg
        · rename_i hyes
          exact (hEq hyes).elim
        · exact hdeg

/-! ### The refined equator as a lower-dimensional refined sphere -/

/-- The vertex equivalence between the equator and the lower-dimensional
sphere, bundled with preservation of all finite faces. -/
structure EquatorEquivData (d r : ℕ) where
  equiv : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v} ≃
    (iteratedBoundary d r).Vertex
  face_iff : ∀ s : Finset {v : (iteratedBoundary (d + 1) r).Vertex //
      EquatorVertex d r v},
    (iteratedBoundary (d + 1) r).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (iteratedBoundary d r).IsFace (s.map equiv.toEmbedding)

noncomputable def baseEquatorVertexEquiv (d : ℕ) :
    {v : (crossPolytopeBoundary (d + 1)).Vertex // BaseEquatorVertex d v} ≃
      (crossPolytopeBoundary d).Vertex where
  toFun v := (finPredOfNotLast v.1.1 v.2, v.1.2)
  invFun v := ⟨(Fin.castSucc v.1, v.2), by
    intro h
    have hv := congrArg Fin.val h
    have hlt := v.1.isLt
    simp [Fin.last] at hv
    omega⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (castSucc_finPredOfNotLast v.1.1 v.2) rfl
  right_inv v := by
    exact Prod.ext (by apply Fin.ext; rfl) rfl

theorem baseEquatorVertexEquiv_face_iff (d : ℕ)
    (s : Finset {v : (crossPolytopeBoundary (d + 1)).Vertex //
      BaseEquatorVertex d v}) :
    (crossPolytopeBoundary (d + 1)).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (crossPolytopeBoundary d).IsFace
        (s.map (baseEquatorVertexEquiv d).toEmbedding) := by
  constructor
  · intro hs
    refine ⟨Finset.map_nonempty.mpr
      (Finset.map_nonempty.mp hs.1), ?_⟩
    intro i hi
    apply hs.2 (Fin.castSucc i)
    constructor
    · rcases Finset.mem_map.mp hi.1 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      change v.1 = (Fin.castSucc i, false)
      apply Prod.ext
      · calc
          v.1.1 = Fin.castSucc (finPredOfNotLast v.1.1 v.2) :=
            (castSucc_finPredOfNotLast v.1.1 v.2).symm
          _ = Fin.castSucc i := congrArg Fin.castSucc (congrArg Prod.fst heq)
      · have hbool := congrArg Prod.snd heq
        change v.1.2 = false at hbool
        exact hbool
    · rcases Finset.mem_map.mp hi.2 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      change v.1 = (Fin.castSucc i, true)
      apply Prod.ext
      · calc
          v.1.1 = Fin.castSucc (finPredOfNotLast v.1.1 v.2) :=
            (castSucc_finPredOfNotLast v.1.1 v.2).symm
          _ = Fin.castSucc i := congrArg Fin.castSucc (congrArg Prod.fst heq)
      · have hbool := congrArg Prod.snd heq
        change v.1.2 = true at hbool
        exact hbool
  · intro hs
    refine ⟨Finset.map_nonempty.mpr
      (Finset.map_nonempty.mp hs.1), ?_⟩
    intro i hi
    have hine : i ≠ Fin.last d := by
      intro hilast
      have hmem : (i, false) ∈ s.map (Function.Embedding.subtype _) := hi.1
      rcases Finset.mem_map.mp hmem with ⟨v, hv, heq⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      exact v.2 (hcoord.trans hilast)
    let j := finPredOfNotLast i hine
    apply hs.2 j
    constructor
    · rcases Finset.mem_map.mp hi.1 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      have hbool : v.1.2 = false := congrArg Prod.snd heq
      apply Prod.ext
      · apply Fin.ext
        dsimp [baseEquatorVertexEquiv, j, finPredOfNotLast]
        exact congrArg Fin.val hcoord
      · exact hbool
    · rcases Finset.mem_map.mp hi.2 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      have hbool : v.1.2 = true := congrArg Prod.snd heq
      apply Prod.ext
      · apply Fin.ext
        dsimp [baseEquatorVertexEquiv, j, finPredOfNotLast]
        exact congrArg Fin.val hcoord
      · exact hbool

noncomputable def baseEquatorEquivData (d : ℕ) : EquatorEquivData d 0 where
  equiv := baseEquatorVertexEquiv d
  face_iff := by
    intro s
    exact baseEquatorVertexEquiv_face_iff d s

noncomputable def equatorBaryVertexToLower
    {d r : ℕ} (D : EquatorEquivData d r)
    (F : {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    (iteratedBoundary d (r + 1)).Vertex := by
  let sE := F.1.1.subtype (EquatorVertex d r)
  refine ⟨sE.map D.equiv.toEmbedding, ?_⟩
  apply (D.face_iff sE).mp
  rw [Finset.subtype_map_of_mem F.2]
  exact F.1.2

noncomputable def lowerBaryVertexToEquator
    {d r : ℕ} (D : EquatorEquivData d r)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v} := by
  let sE := F.1.map D.equiv.symm.toEmbedding
  have hface : (iteratedBoundary (d + 1) r).IsFace
      (sE.map (Function.Embedding.subtype _)) := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using F.2
  refine ⟨⟨sE.map (Function.Embedding.subtype _), hface⟩, ?_⟩
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
  exact w.2

noncomputable def equatorBaryVertexEquiv
    {d r : ℕ} (D : EquatorEquivData d r) :
    {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v} ≃
      (iteratedBoundary d (r + 1)).Vertex where
  toFun := equatorBaryVertexToLower D
  invFun := lowerBaryVertexToEquator D
  left_inv F := by
    have hFE : ∀ v ∈ F.1.1, EquatorVertex d r v := F.2
    apply Subtype.ext
    apply Subtype.ext
    ext v
    simp [equatorBaryVertexToLower, lowerBaryVertexToEquator,
      Finset.map_map, hFE]
    exact fun hv ↦ hFE v hv
  right_inv F := by
    have heq : ∀ a b : (iteratedBoundary d r).Vertex,
        (D.equiv.symm a).1 = (D.equiv.symm b).1 ↔ a = b := by
      intro a b
      constructor
      · intro h
        exact D.equiv.symm.injective (Subtype.ext h)
      · rintro rfl
        rfl
    apply Subtype.ext
    ext v
    simp [equatorBaryVertexToLower, lowerBaryVertexToEquator,
      Finset.map_map, heq]

theorem equatorBaryVertex_subset_iff
    {d r : ℕ} (D : EquatorEquivData d r)
    (F G : {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    F.1.1 ⊆ G.1.1 ↔
      (equatorBaryVertexToLower D F).1 ⊆
        (equatorBaryVertexToLower D G).1 := by
  constructor
  · intro hFG x hx
    rcases Finset.mem_map.mp hx with ⟨w, hw, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨w, Finset.mem_subtype.mpr (hFG (Finset.mem_subtype.mp hw)), rfl⟩
  · intro hFG v hv
    let wF : {v : (iteratedBoundary (d + 1) r).Vertex //
        EquatorVertex d r v} := ⟨v, F.2 v hv⟩
    have hwF : wF ∈ F.1.1.subtype (EquatorVertex d r) :=
      Finset.mem_subtype.mpr hv
    have himage : D.equiv wF ∈ (equatorBaryVertexToLower D F).1 := by
      exact Finset.mem_map.mpr ⟨wF, hwF, rfl⟩
    have himageG := hFG himage
    rcases Finset.mem_map.mp himageG with ⟨wG, hwG, heq⟩
    have hwEq : wG = wF := D.equiv.injective heq
    exact Finset.mem_subtype.mp (hwEq ▸ hwG)

theorem equatorBaryVertexEquiv_face_iff
    {d r : ℕ} (D : EquatorEquivData d r)
    (s : Finset {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    (iteratedBoundary (d + 1) (r + 1)).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (iteratedBoundary d (r + 1)).IsFace
        (s.map (equatorBaryVertexEquiv D).toEmbedding) := by
  constructor
  · intro hs
    refine ⟨Finset.map_nonempty.mpr (Finset.map_nonempty.mp hs.1), ?_⟩
    intro A hA B hB
    rcases Finset.mem_map.mp hA with ⟨F, hF, rfl⟩
    rcases Finset.mem_map.mp hB with ⟨G, hG, rfl⟩
    have hF' : F.1 ∈ s.map (Function.Embedding.subtype _) :=
      Finset.mem_map.mpr ⟨F, hF, rfl⟩
    have hG' : G.1 ∈ s.map (Function.Embedding.subtype _) :=
      Finset.mem_map.mpr ⟨G, hG, rfl⟩
    rcases hs.2 F.1 hF' G.1 hG' with hFG | hGF
    · exact Or.inl ((equatorBaryVertex_subset_iff D F G).mp hFG)
    · exact Or.inr ((equatorBaryVertex_subset_iff D G F).mp hGF)
  · intro hs
    refine ⟨Finset.map_nonempty.mpr (Finset.map_nonempty.mp hs.1), ?_⟩
    intro A hA B hB
    rcases Finset.mem_map.mp hA with ⟨F, hF, rfl⟩
    rcases Finset.mem_map.mp hB with ⟨G, hG, rfl⟩
    have hF' : equatorBaryVertexToLower D F ∈
        s.map (equatorBaryVertexEquiv D).toEmbedding :=
      Finset.mem_map.mpr ⟨F, hF, rfl⟩
    have hG' : equatorBaryVertexToLower D G ∈
        s.map (equatorBaryVertexEquiv D).toEmbedding :=
      Finset.mem_map.mpr ⟨G, hG, rfl⟩
    rcases hs.2 _ hF' _ hG' with hFG | hGF
    · exact Or.inl ((equatorBaryVertex_subset_iff D F G).mpr hFG)
    · exact Or.inr ((equatorBaryVertex_subset_iff D G F).mpr hGF)

noncomputable def succEquatorEquivData
    {d r : ℕ} (D : EquatorEquivData d r) : EquatorEquivData d (r + 1) where
  equiv := equatorBaryVertexEquiv D
  face_iff := equatorBaryVertexEquiv_face_iff D

noncomputable def equatorEquivData (d : ℕ) : ∀ r, EquatorEquivData d r
  | 0 => baseEquatorEquivData d
  | r + 1 => succEquatorEquivData (equatorEquivData d r)

/-- Positive-first alternating top faces, separated from the
positive-or-negative predicate used by hemisphere handshaking. -/
def IsPositiveAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  ∃ idx : Fin d → Fin m,
    StrictMono idx ∧ T.1.image label = alternatingLabelSetOf idx

noncomputable instance isPositiveAlternatingTopDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsPositiveAlternatingTop (U := U) (d := d) label) := by
  classical
  intro T
  infer_instance

abbrev FullPositiveAlternatingTop
    (K : FiniteComplex) (d m : ℕ) (label : K.Vertex → SignedLabel m) :=
  {T : RestrictedTopFace K (fun _ ↦ True) d //
    IsPositiveAlternatingTop label T}

noncomputable def equatorRidgeToLowerTop (d r : ℕ)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d := by
  let D := equatorEquivData d r
  let sE := R.1.1.subtype (EquatorVertex d r)
  refine ⟨sE.map D.equiv.toEmbedding, ?_, ?_, ?_⟩
  · apply (D.face_iff sE).mp
    rw [Finset.subtype_map_of_mem R.2]
    exact R.1.2.1
  · rw [Finset.card_map]
    have hall : R.1.1.filter (EquatorVertex d r) = R.1.1 :=
      Finset.filter_eq_self.mpr R.2
    rw [show sE.card = (R.1.1.filter (EquatorVertex d r)).card by
      simp [sE, Finset.subtype]]
    rw [hall, R.1.2.2.1]
    omega
  · simp

noncomputable def lowerTopToEquatorRidge (d r : ℕ)
    (T : RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d) :
    {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R} := by
  let D := equatorEquivData d r
  let sE := T.1.map D.equiv.symm.toEmbedding
  let s := sE.map (Function.Embedding.subtype _)
  have hsface : (iteratedBoundary (d + 1) r).IsFace s := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using T.2.1
  have hsEq : ∀ v ∈ s, EquatorVertex d r v := by
    intro v hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact w.2
  refine ⟨⟨s, hsface, ?_, ?_⟩, hsEq⟩
  · dsimp [s]
    rw [Finset.card_map, Finset.card_map, T.2.2.1]
  · intro v hv
    exact equatorVertex_upperVertex d r (hsEq v hv)

noncomputable def equatorRidgeEquivLowerTop (d r : ℕ) :
    {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R} ≃
    RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d where
  toFun := equatorRidgeToLowerTop d r
  invFun := lowerTopToEquatorRidge d r
  left_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    ext v
    simp [equatorRidgeToLowerTop, lowerTopToEquatorRidge,
      Finset.map_map]
    exact fun hv ↦ R.2 v hv
  right_inv T := by
    apply Subtype.ext
    ext v
    have heq : ∀ a b : (iteratedBoundary d r).Vertex,
        ((equatorEquivData d r).equiv.symm a).1 =
          ((equatorEquivData d r).equiv.symm b).1 ↔ a = b := by
      intro a b
      constructor
      · intro h
        exact (equatorEquivData d r).equiv.symm.injective (Subtype.ext h)
      · rintro rfl
        rfl
    simp [equatorRidgeToLowerTop, lowerTopToEquatorRidge,
      Finset.map_map, heq]

noncomputable def equatorRestrictedLabel (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    (iteratedBoundary d r).Vertex → SignedLabel m :=
  fun v ↦ label (((equatorEquivData d r).equiv.symm v).1)

theorem image_equatorRestrictedLabel_equatorRidgeToLowerTop
    (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    (equatorRidgeToLowerTop d r R).1.image (equatorRestrictedLabel d r m label) =
      R.1.1.image label := by
  classical
  apply Finset.ext
  intro z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    refine ⟨w.1, Finset.mem_subtype.mp hw, ?_⟩
    symm
    change label (((equatorEquivData d r).equiv.symm
      ((equatorEquivData d r).equiv w)).1) = label w.1
    rw [(equatorEquivData d r).equiv.symm_apply_apply]
  · rintro ⟨v, hv, rfl⟩
    let w : {v : (iteratedBoundary (d + 1) r).Vertex //
        EquatorVertex d r v} := ⟨v, R.2 v hv⟩
    refine ⟨(equatorEquivData d r).equiv w, ?_, ?_⟩
    · exact Finset.mem_map.mpr
        ⟨w, Finset.mem_subtype.mpr hv, rfl⟩
    · change label (((equatorEquivData d r).equiv.symm
        ((equatorEquivData d r).equiv w)).1) = label v
      rw [(equatorEquivData d r).equiv.symm_apply_apply]

theorem positiveAlternating_equatorRidge_iff_lowerTop
    (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    IsPositiveAlternatingRidge label R.1 ↔
      IsPositiveAlternatingTop (equatorRestrictedLabel d r m label)
        (equatorRidgeToLowerTop d r R) := by
  unfold IsPositiveAlternatingRidge IsPositiveAlternatingTop
  rw [image_equatorRestrictedLabel_equatorRidgeToLowerTop]
  rfl

noncomputable def equatorPositiveReassociate (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) m label //
        IsEquatorRidge (E := EquatorVertex d r) R.1} ≃
    {R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) //
        IsEquatorRidge (E := EquatorVertex d r) R} //
      IsPositiveAlternatingRidge label R.1} where
  toFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  invFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl

noncomputable def positiveEquatorRidgeEquivLowerTop (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) m label //
        IsEquatorRidge (E := EquatorVertex d r) R.1} ≃
      FullPositiveAlternatingTop (iteratedBoundary d r) d m
        (equatorRestrictedLabel d r m label) :=
  (equatorPositiveReassociate d r m label).trans
    ((equatorRidgeEquivLowerTop d r).subtypeEquiv
      (positiveAlternating_equatorRidge_iff_lowerTop d r m label))

theorem odd_positiveEquatorRidge_iff_lowerTop (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    Odd (Fintype.card
      {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
        (UpperVertex d r) (d + 1) m label //
          IsEquatorRidge (E := EquatorVertex d r) R.1}) ↔
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m
        (equatorRestrictedLabel d r m label))) := by
  rw [Fintype.card_congr (positiveEquatorRidgeEquivLowerTop d r m label)]

/-! The equator equivalence is antipodal. -/

theorem equatorVertex_antipode_iff (d r : ℕ)
    (v : (iteratedBoundary (d + 1) r).Vertex) :
    EquatorVertex d r ((iteratedAntipode (d + 1) r).neg v) ↔
      EquatorVertex d r v := by
  induction r with
  | zero =>
      rcases v with ⟨i, b⟩
      cases b <;> rfl
  | succ r ih =>
      constructor
      · intro h w hw
        have hneg : (iteratedAntipode (d + 1) r).neg w ∈
            ((iteratedAntipode (d + 1) (r + 1)).neg v).1 := by
          exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
        exact (ih w).mp (h _ hneg)
      · intro h w hw
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        exact (ih u).mpr (h u hu)

noncomputable def equatorAntipodeVertex (d r : ℕ)
    (v : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v}) :
    {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v} :=
  ⟨(iteratedAntipode (d + 1) r).neg v.1,
    (equatorVertex_antipode_iff d r v.1).mpr v.2⟩

theorem equatorEquivData_antipode (d r : ℕ)
    (v : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v}) :
    (equatorEquivData d r).equiv (equatorAntipodeVertex d r v) =
      (iteratedAntipode d r).neg ((equatorEquivData d r).equiv v) := by
  induction r with
  | zero =>
      rcases v with ⟨⟨i, b⟩, hi⟩
      cases b <;> rfl
  | succ r ih =>
      apply Subtype.ext
      ext w
      constructor
      · intro hw
        rcases Finset.mem_map.mp hw with ⟨u, hu, heq⟩
        rcases Finset.mem_subtype.mp hu with hu
        rcases Finset.mem_image.mp hu with ⟨a, ha, hau⟩
        have haEq : EquatorVertex d r a := v.2 a ha
        let aE : {x : (iteratedBoundary (d + 1) r).Vertex //
            EquatorVertex d r x} := ⟨a, haEq⟩
        have hueq : equatorAntipodeVertex d r aE = u := by
          apply Subtype.ext
          exact hau
        have hcomm := ih aE
        apply Finset.mem_image.mpr
        refine ⟨(equatorEquivData d r).equiv aE, ?_, ?_⟩
        · exact Finset.mem_map.mpr
            ⟨aE, Finset.mem_subtype.mpr ha, rfl⟩
        · calc
            (iteratedAntipode d r).neg ((equatorEquivData d r).equiv aE) =
                (equatorEquivData d r).equiv (equatorAntipodeVertex d r aE) :=
              hcomm.symm
            _ = (equatorEquivData d r).equiv u := congrArg _ hueq
            _ = w := heq
      · intro hw
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        rcases Finset.mem_map.mp hu with ⟨aE, haE, rfl⟩
        have hcomm := ih aE
        apply Finset.mem_map.mpr
        let naE := equatorAntipodeVertex d r aE
        refine ⟨naE, ?_, ?_⟩
        · apply Finset.mem_subtype.mpr
          exact Finset.mem_image.mpr ⟨aE.1, Finset.mem_subtype.mp haE, rfl⟩
        · exact hcomm

theorem equatorRestrictedLabel_antipodal (d r m : ℕ)
    {label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m}
    (hanti : ∀ v, label ((iteratedAntipode (d + 1) r).neg v) = (label v).neg) :
    ∀ v, equatorRestrictedLabel d r m label ((iteratedAntipode d r).neg v) =
      (equatorRestrictedLabel d r m label v).neg := by
  intro v
  let w := (equatorEquivData d r).equiv.symm v
  have hcomm := equatorEquivData_antipode d r w
  have hpre : (equatorEquivData d r).equiv.symm
      ((iteratedAntipode d r).neg v) = equatorAntipodeVertex d r w := by
    apply (equatorEquivData d r).equiv.injective
    rw [(equatorEquivData d r).equiv.apply_symm_apply]
    simpa [w] using hcomm.symm
  change label (((equatorEquivData d r).equiv.symm
      ((iteratedAntipode d r).neg v)).1) =
    (label (((equatorEquivData d r).equiv.symm v).1)).neg
  rw [hpre]
  exact hanti w.1

theorem equatorRestrictedLabel_noComplementary (d r m : ℕ)
    {label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels (iteratedBoundary (d + 1) r) label) :
    NoComplementaryFaceLabels (iteratedBoundary d r)
      (equatorRestrictedLabel d r m label) := by
  intro s hs v hv w hw
  let D := equatorEquivData d r
  let sE := s.map D.equiv.symm.toEmbedding
  have hface : (iteratedBoundary (d + 1) r).IsFace
      (sE.map (Function.Embedding.subtype _)) := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using hs
  apply hno hface
  · exact Finset.mem_map.mpr
      ⟨D.equiv.symm v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
  · exact Finset.mem_map.mpr
      ⟨D.equiv.symm w, Finset.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩

/-! ### Maximal faces split into two antipodal hemispheres -/

abbrev FullTopFace (K : FiniteComplex) (d : ℕ) :=
  RestrictedTopFace K (fun _ ↦ True) d

noncomputable def antipodeFullTop
    {K : FiniteComplex} (A : ComplexInvolution K) {d : ℕ}
    (T : FullTopFace K d) : FullTopFace K d := by
  refine ⟨T.1.image A.neg, A.face_neg T.2.1, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr A.neg_injective.injOn, T.2.2.1]
  · simp

def IsUpperFullTop
    {K : FiniteComplex} (U : K.Vertex → Prop) {d : ℕ}
    (T : FullTopFace K d) : Prop :=
  ∀ v ∈ T.1, U v

noncomputable instance isUpperFullTopDecidable
    {K : FiniteComplex} (U : K.Vertex → Prop) [DecidablePred U] {d : ℕ} :
    DecidablePred (IsUpperFullTop U (d := d)) := by
  classical
  intro T
  infer_instance

theorem fullTopFace_coordinate_exists (d : ℕ)
    (T : FullTopFace (crossPolytopeBoundary d) d) (i : Fin d) :
    (i, false) ∈ T.1 ∨ (i, true) ∈ T.1 := by
  by_contra hnone
  push_neg at hnone
  have hinj : Set.InjOn Prod.fst
      (↑T.1 : Set (crossPolytopeBoundary d).Vertex) := by
    rintro ⟨j, b⟩ hj ⟨l, c⟩ hl heq
    simp only [Prod.fst] at heq
    subst l
    have hbc : b = c := by
      by_contra hbc
      cases b <;> cases c
      · exact hbc rfl
      · exact (T.2.1.2 j ⟨hj, hl⟩).elim
      · exact (T.2.1.2 j ⟨hl, hj⟩).elim
      · exact hbc rfl
    exact Prod.ext rfl hbc
  have hsubset : T.1.image Prod.fst ⊆ (Finset.univ : Finset (Fin d)).erase i := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨v, hv, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hvi
    rcases v with ⟨j, b⟩
    simp only [Prod.fst] at hvi
    subst j
    cases b
    · exact hnone.1 hv
    · exact hnone.2 hv
  have hc : d ≤ d - 1 := by
    calc
      d = T.1.card := T.2.2.1.symm
      _ = (T.1.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ ((Finset.univ : Finset (Fin d)).erase i).card :=
        Finset.card_le_card hsubset
      _ = d - 1 := by simp
  have hd : 0 < d := by have := i.isLt; omega
  omega

theorem baseFullTop_hemisphere_xor (k : ℕ)
    (T : FullTopFace (crossPolytopeBoundary (k + 1)) (k + 1)) :
    Xor (IsUpperFullTop (BaseUpperVertex k) T)
      (IsUpperFullTop (BaseUpperVertex k)
        (antipodeFullTop (crossPolytopeAntipode (k + 1)) T)) := by
  rcases fullTopFace_coordinate_exists (k + 1) T (Fin.last k) with hneg | hpos
  · refine Or.inr ⟨?_, ?_⟩
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      intro heq
      have hwpos : (Fin.last k, true) ∈ T.1 := by
        rcases w with ⟨i, b⟩
        cases b
        · have hbool : true = false := congrArg Prod.snd heq
          exact Bool.noConfusion hbool
        · have hi : i = Fin.last k := congrArg Prod.fst heq
          subst i
          exact hw
      exact T.2.1.2 (Fin.last k) ⟨hneg, hwpos⟩
    · intro hupper
      exact hupper (Fin.last k, false) hneg rfl
  · refine Or.inl ⟨?_, ?_⟩
    · intro v hv heq
      exact T.2.1.2 (Fin.last k) ⟨heq ▸ hv, hpos⟩
    · intro hanti
      have hmem : (Fin.last k, false) ∈
          (antipodeFullTop (crossPolytopeAntipode (k + 1)) T).1 :=
        Finset.mem_image.mpr ⟨(Fin.last k, true), hpos, rfl⟩
      exact hanti _ hmem rfl

noncomputable def baryTopRankImage
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : Finset (Fin d) :=
  T.1.image (baryRank d hcard)

def topLastRank (d : ℕ) (hd : 1 ≤ d) : Fin d :=
  ⟨d - 1, by omega⟩

theorem baryTopRankImage_eq_univ
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryTopRankImage d hcard T = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [baryTopRankImage, Finset.card_image_iff.mpr
    (baryRank_injective_on_chain d hcard T.2.1), T.2.2.1]
  simp

noncomputable def baryTopMaxFace
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : BaryVertex K :=
  Classical.choose (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))

theorem baryTopMaxFace_mem
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryTopMaxFace d hd hcard T ∈ T.1 :=
  (Classical.choose_spec (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))).1

theorem baryTopMaxFace_rank
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryRank d hcard (baryTopMaxFace d hd hcard T) = topLastRank d hd :=
  (Classical.choose_spec (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))).2

theorem baryTopMaxFace_card
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    (baryTopMaxFace d hd hcard T).1.card = d := by
  have hr := baryRank_card d hcard (baryTopMaxFace d hd hcard T)
  rw [baryTopMaxFace_rank] at hr
  dsimp [topLastRank] at hr
  omega

noncomputable def baryTopMaxOldTop
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : FullTopFace K d :=
  ⟨(baryTopMaxFace d hd hcard T).1,
    (baryTopMaxFace d hd hcard T).2,
    baryTopMaxFace_card d hd hcard T,
    by simp⟩

theorem baryTop_member_subset_max
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d)
    {G : BaryVertex K} (hG : G ∈ T.1) :
    G.1 ⊆ (baryTopMaxFace d hd hcard T).1 := by
  let M := baryTopMaxFace d hd hcard T
  have hM : M ∈ T.1 := baryTopMaxFace_mem d hd hcard T
  rcases T.2.1.2 G hG M hM with hGM | hMG
  · exact hGM
  · have hc : G.1.card ≤ M.1.card := by
      rw [baryTopMaxFace_card]
      exact hcard G.2
    have heq := Finset.eq_of_subset_of_card_le hMG hc
    simpa [M, heq]

theorem baryFullTop_upper_iff_max
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    IsUpperFullTop (BaryUpper U) T ↔
      IsUpperFullTop U (baryTopMaxOldTop d hd hcard T) := by
  constructor
  · intro h v hv
    exact h (baryTopMaxFace d hd hcard T)
      (baryTopMaxFace_mem d hd hcard T) v hv
  · intro h G hG v hv
    exact h v (baryTop_member_subset_max d hd hcard T hG hv)

theorem baryAntipodeFullTop_upper_iff_max
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    IsUpperFullTop (BaryUpper U)
        (antipodeFullTop A.barycentricLift T) ↔
      IsUpperFullTop U
        (antipodeFullTop A (baryTopMaxOldTop d hd hcard T)) := by
  constructor
  · intro h v hv
    have hM : baryTopMaxFace d hd hcard T ∈ T.1 :=
      baryTopMaxFace_mem d hd hcard T
    have hnegM : A.barycentricLift.neg (baryTopMaxFace d hd hcard T) ∈
        (antipodeFullTop A.barycentricLift T).1 :=
      Finset.mem_image.mpr ⟨_, hM, rfl⟩
    exact h _ hnegM v hv
  · intro h F hF v hv
    rcases Finset.mem_image.mp hF with ⟨G, hG, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    apply h (A.neg w)
    apply Finset.mem_image.mpr
    exact ⟨w, baryTop_member_subset_max d hd hcard T hG hw, rfl⟩

theorem baryFullTop_hemisphere_xor
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (hold : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T)))
    (T : FullTopFace (barycentricSubdivision K) d) :
    Xor (IsUpperFullTop (BaryUpper U) T)
      (IsUpperFullTop (BaryUpper U)
        (antipodeFullTop A.barycentricLift T)) := by
  rw [baryFullTop_upper_iff_max d hd hcard T,
    baryAntipodeFullTop_upper_iff_max A d hd hcard T]
  exact hold (baryTopMaxOldTop d hd hcard T)

theorem iteratedFullTop_hemisphere_xor (k r : ℕ)
    (T : FullTopFace (iteratedBoundary (k + 1) r) (k + 1)) :
    Xor (IsUpperFullTop (UpperVertex k r) T)
      (IsUpperFullTop (UpperVertex k r)
        (antipodeFullTop (iteratedAntipode (k + 1) r) T)) := by
  induction r with
  | zero => exact baseFullTop_hemisphere_xor k T
  | succ r ih =>
      exact baryFullTop_hemisphere_xor (iteratedAntipode (k + 1) r)
        (k + 1) (by omega)
        (fun {s} hs ↦ card_face_iteratedBoundary_le (k + 1) r hs)
        ih T

def IsNegativeAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  ∃ idx : Fin d → Fin m,
    StrictMono idx ∧ T.1.image label = alternatingNegLabelSetOf idx

@[simp] theorem signedLabel_neg_neg {m : ℕ} (z : SignedLabel m) :
    z.neg.neg = z := by
  rcases z with ⟨b, i⟩
  cases b <;> rfl

theorem image_neg_alternatingLabelSetOf {d m : ℕ} (idx : Fin d → Fin m) :
    (alternatingLabelSetOf idx).image SignedLabel.neg =
      alternatingNegLabelSetOf idx := by
  classical
  ext z
  simp [alternatingLabelSetOf, alternatingNegLabelSetOf]

theorem image_neg_alternatingNegLabelSetOf {d m : ℕ} (idx : Fin d → Fin m) :
    (alternatingNegLabelSetOf idx).image SignedLabel.neg =
      alternatingLabelSetOf idx := by
  classical
  ext z
  simp [alternatingLabelSetOf, alternatingNegLabelSetOf]

theorem image_label_antipodeFullTop
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    (antipodeFullTop A T).1.image label =
      (T.1.image label).image SignedLabel.neg := by
  classical
  change (T.1.image A.neg).image label =
    (T.1.image label).image SignedLabel.neg
  apply Finset.ext
  intro z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨label w, ⟨w, hw, rfl⟩, (hanti w).symm⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨A.neg w, ⟨w, hw, rfl⟩, hanti w⟩

theorem positive_antipodeFullTop_iff_negative
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    IsPositiveAlternatingTop label (antipodeFullTop A T) ↔
      IsNegativeAlternatingTop label T := by
  unfold IsPositiveAlternatingTop IsNegativeAlternatingTop
  rw [image_label_antipodeFullTop A label hanti T]
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    calc
      T.1.image label =
          ((T.1.image label).image SignedLabel.neg).image SignedLabel.neg := by
        ext z
        simp [SignedLabel.neg]
      _ = (alternatingLabelSetOf idx).image SignedLabel.neg := by rw [hset]
      _ = alternatingNegLabelSetOf idx := image_neg_alternatingLabelSetOf idx
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    rw [hset, image_neg_alternatingNegLabelSetOf]

theorem negative_antipodeFullTop_iff_positive
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    IsNegativeAlternatingTop label (antipodeFullTop A T) ↔
      IsPositiveAlternatingTop label T := by
  unfold IsNegativeAlternatingTop IsPositiveAlternatingTop
  rw [image_label_antipodeFullTop A label hanti T]
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    calc
      T.1.image label =
          ((T.1.image label).image SignedLabel.neg).image SignedLabel.neg := by
        ext z
        simp
      _ = (alternatingNegLabelSetOf idx).image SignedLabel.neg := by rw [hset]
      _ = alternatingLabelSetOf idx := image_neg_alternatingNegLabelSetOf idx
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    rw [hset, image_neg_alternatingLabelSetOf]

theorem alternatingTop_iff_positive_or_negative
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsAlternatingTop label T ↔
      IsPositiveAlternatingTop label T ∨ IsNegativeAlternatingTop label T := by
  rfl

theorem positiveAlternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsPositiveAlternatingTop label T ↔ IsAltPosLabelSeq (topLabelSeq label T) := by
  unfold IsPositiveAlternatingTop IsAltPosLabelSeq
  rw [← image_label_top_eq_labelSeqSet]

theorem negativeAlternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsNegativeAlternatingTop label T ↔ IsAltNegLabelSeq (topLabelSeq label T) := by
  unfold IsNegativeAlternatingTop IsAltNegLabelSeq
  rw [← image_label_top_eq_labelSeqSet]

theorem positiveAlternatingTop_not_negative
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ} (hd : 0 < d)
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d)
    (hpos : IsPositiveAlternatingTop label T)
    (hneg : IsNegativeAlternatingTop label T) : False :=
  IsAltPosLabelSeq.not_isAltNeg hd
    ((positiveAlternatingTop_iff_labelSeq label T).mp hpos)
    ((negativeAlternatingTop_iff_labelSeq label T).mp hneg)

noncomputable def restrictFullTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : FullTopFace K d) (hU : IsUpperFullTop U T) :
    RestrictedTopFace K U d :=
  ⟨T.1, T.2.1, T.2.2.1, hU⟩

def forgetUpperTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : RestrictedTopFace K U d) : FullTopFace K d :=
  ⟨T.1, T.2.1, T.2.2.1, by simp⟩

noncomputable def fullPositiveToUpperAlternating
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (hsplit : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T)))
    (T : FullPositiveAlternatingTop K d m label) :
    {T : RestrictedTopFace K U d // IsAlternatingTop label T} := by
  by_cases hU : IsUpperFullTop U T.1
  · exact ⟨restrictFullTop T.1 hU, Or.inl T.2⟩
  · have hAU : IsUpperFullTop U (antipodeFullTop A T.1) := by
      rcases hsplit T.1 with h | h
      · exact False.elim (hU h.1)
      · exact h.1
    refine ⟨restrictFullTop (antipodeFullTop A T.1) hAU, Or.inr ?_⟩
    exact (negative_antipodeFullTop_iff_positive A label hanti T.1).mpr T.2

noncomputable def upperAlternatingToFullPositive
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : {T : RestrictedTopFace K U d // IsAlternatingTop label T}) :
    FullPositiveAlternatingTop K d m label := by
  by_cases hpos : IsPositiveAlternatingTop label T.1
  · exact ⟨forgetUpperTop T.1, hpos⟩
  · have hneg : IsNegativeAlternatingTop label T.1 :=
      (alternatingTop_iff_positive_or_negative label T.1).mp T.2 |>.resolve_left hpos
    exact ⟨antipodeFullTop A (forgetUpperTop T.1),
      (positive_antipodeFullTop_iff_negative A label hanti _).mpr hneg⟩

noncomputable def fullPositiveEquivUpperAlternating
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (hd : 0 < d) (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (hsplit : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T))) :
    FullPositiveAlternatingTop K d m label ≃
      {T : RestrictedTopFace K U d // IsAlternatingTop label T} where
  toFun := fullPositiveToUpperAlternating A label hanti hsplit
  invFun := upperAlternatingToFullPositive A label hanti
  left_inv T := by
    classical
    unfold fullPositiveToUpperAlternating upperAlternatingToFullPositive
    split <;> rename_i hU
    · simp only
      split <;> rename_i hpos
      · apply Subtype.ext
        apply Subtype.ext
        rfl
      · exact False.elim (hpos T.2)
    · simp only
      have hnegAnti : IsNegativeAlternatingTop label
          (restrictFullTop (antipodeFullTop A T.1) (by
            rcases hsplit T.1 with h | h
            · exact False.elim (hU h.1)
            · exact h.1)) :=
        (negative_antipodeFullTop_iff_positive A label hanti T.1).mpr T.2
      split <;> rename_i hposAnti
      · exact False.elim
          (positiveAlternatingTop_not_negative hd label _ hposAnti hnegAnti)
      · apply Subtype.ext
        apply Subtype.ext
        exact A.image_neg_image_neg T.1.1
  right_inv T := by
    classical
    unfold upperAlternatingToFullPositive fullPositiveToUpperAlternating
    split <;> rename_i hpos
    · simp only
      split <;> rename_i hU
      · apply Subtype.ext
        apply Subtype.ext
        rfl
      · exact False.elim (hU T.1.2.2.2)
    · simp only
      have hneg : IsNegativeAlternatingTop label T.1 :=
        (alternatingTop_iff_positive_or_negative label T.1).mp T.2 |>.resolve_left hpos
      have hnotAntiUpper : ¬IsUpperFullTop U
          (antipodeFullTop A (forgetUpperTop T.1)) := by
        intro hAU
        rcases hsplit (forgetUpperTop T.1) with h | h
        · exact h.2 hAU
        · exact False.elim (h.2 T.1.2.2.2)
      split <;> rename_i hAU
      · exact False.elim (hnotAntiUpper hAU)
      · apply Subtype.ext
        apply Subtype.ext
        exact A.image_neg_image_neg T.1.1

/-! ### The one-dimensional base of Ky Fan parity -/

noncomputable def upperZeroVertex : ∀ r, (iteratedBoundary 1 r).Vertex
  | 0 => (Fin.last 0, true)
  | r + 1 => ⟨{upperZeroVertex r},
      (iteratedBoundary 1 r).singleton_face (upperZeroVertex r)⟩

theorem upperZeroVertex_upper (r : ℕ) : UpperVertex 0 r (upperZeroVertex r) := by
  induction r with
  | zero =>
      intro h
      exact Bool.noConfusion (congrArg Prod.snd h)
  | succ r ih => simpa [upperZeroVertex, UpperVertex] using ih

theorem upperVertex_zero_eq (r : ℕ)
    {v : (iteratedBoundary 1 r).Vertex} (hv : UpperVertex 0 r v) :
    v = upperZeroVertex r := by
  induction r with
  | zero =>
      rcases v with ⟨i, b⟩
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      cases b
      · exact False.elim (hv rfl)
      · rfl
  | succ r ih =>
      apply Subtype.ext
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · obtain ⟨w, hw⟩ := (iteratedBoundary 1 r).face_nonempty v.2
        have hweq : w = upperZeroVertex r := ih (hv w hw)
        simpa [hweq] using hw
      · intro w hw
        exact ih (hv w hw)

noncomputable instance uniqueUpperZeroVertex (r : ℕ) :
    Unique {v : (iteratedBoundary 1 r).Vertex // UpperVertex 0 r v} where
  default := ⟨upperZeroVertex r, upperZeroVertex_upper r⟩
  uniq v := by
    apply Subtype.ext
    exact upperVertex_zero_eq r v.2

noncomputable def upperTopFaceOneEquiv
    {K : FiniteComplex} (U : K.Vertex → Prop) :
    RestrictedTopFace K U 1 ≃ {v : K.Vertex // U v} where
  toFun T := ⟨faceEnum T.1 1 T.2.2.1 0,
    T.2.2.2 _ (faceEnum_mem T.1 1 T.2.2.1 0)⟩
  invFun v := ⟨{v.1}, K.singleton_face v.1, by simp, by simpa using v.2⟩
  left_inv T := by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      exact faceEnum_mem T.1 1 T.2.2.1 0
    · simp [T.2.2.1]
  right_inv v := by
    apply Subtype.ext
    have hm := faceEnum_mem ({v.1} : Finset K.Vertex) 1 (by simp) 0
    simpa using (Finset.mem_singleton.mp hm)

theorem every_one_top_alternating
    {K : FiniteComplex} {U : K.Vertex → Prop} {m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U 1) :
    IsAlternatingTop label T := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp T.2.2.1
  rcases hlabel : label v with ⟨b, i⟩
  cases b
  · right
    refine ⟨fun _ ↦ i, ?_, ?_⟩
    · intro a c hac
      omega
    · simp [hv, hlabel, alternatingNegLabelSetOf, alternatingLabelOf,
        SignedLabel.neg]
  · left
    refine ⟨fun _ ↦ i, ?_, ?_⟩
    · intro a c hac
      omega
    · simp [hv, hlabel, alternatingLabelSetOf, alternatingLabelOf]

noncomputable def upperOneAlternatingEquiv
    (r m : ℕ) (label : (iteratedBoundary 1 r).Vertex → SignedLabel m) :
    {T : RestrictedTopFace (iteratedBoundary 1 r) (UpperVertex 0 r) 1 //
      IsAlternatingTop label T} ≃
      RestrictedTopFace (iteratedBoundary 1 r) (UpperVertex 0 r) 1 where
  toFun T := T.1
  invFun T := ⟨T, every_one_top_alternating label T⟩
  left_inv T := by cases T; rfl
  right_inv T := rfl

theorem odd_fullPositiveAlternatingTop_one
    (r m : ℕ) (label : (iteratedBoundary 1 r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode 1 r).neg v) = (label v).neg) :
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary 1 r) 1 m label)) := by
  rw [Fintype.card_congr
    (fullPositiveEquivUpperAlternating (iteratedAntipode 1 r) (by omega)
      label hanti (iteratedFullTop_hemisphere_xor 0 r))]
  rw [Fintype.card_congr (upperOneAlternatingEquiv r m label)]
  rw [Fintype.card_congr (upperTopFaceOneEquiv (UpperVertex 0 r))]
  simp

/-! ### Ky Fan parity and fine Tucker lemma -/

theorem odd_fullPositiveAlternatingTop
    (d r m : ℕ) (hd : 0 < d)
    (label : (iteratedBoundary d r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode d r).neg v) = (label v).neg)
    (hno : NoComplementaryFaceLabels (iteratedBoundary d r) label) :
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m label)) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        exact odd_fullPositiveAlternatingTop_one r m label hanti
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        let lowerLabel := equatorRestrictedLabel d r m label
        have hantiLower : ∀ v,
            lowerLabel ((iteratedAntipode d r).neg v) = (lowerLabel v).neg :=
          equatorRestrictedLabel_antipodal d r m hanti
        have hnoLower : NoComplementaryFaceLabels (iteratedBoundary d r) lowerLabel :=
          equatorRestrictedLabel_noComplementary d r m hno
        have hlower : Odd (Fintype.card
            (FullPositiveAlternatingTop (iteratedBoundary d r) d m lowerLabel)) :=
          ih hdpos lowerLabel hantiLower hnoLower
        have hboundary : Odd (Fintype.card
            {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
              (UpperVertex d r) (d + 1) m label //
                IsEquatorRidge (E := EquatorVertex d r) R.1}) :=
          (odd_positiveEquatorRidge_iff_lowerTop d r m label).mpr hlower
        have H : HemisphereGeometry (iteratedBoundary (d + 1) r)
            (UpperVertex d r) (EquatorVertex d r) (d + 1) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
          exact iteratedHemisphereGeometry k r
        have hupper : Odd (Fintype.card
            {T : RestrictedTopFace (iteratedBoundary (d + 1) r)
              (UpperVertex d r) (d + 1) // IsAlternatingTop label T}) :=
          odd_alternatingTop_of_odd_equatorRidge hdpos hno H hboundary
        rw [Fintype.card_congr
          (fullPositiveEquivUpperAlternating (iteratedAntipode (d + 1) r)
            (by omega) label hanti (iteratedFullTop_hemisphere_xor d r))]
        exact hupper

/-- Fine Tucker lemma on every iterated barycentric cross-polytope: an
antipodal labeling by fewer absolute labels has a complementary pair in one
face. -/
theorem exists_complementary_face_of_antipodal_of_lt
    (d r m : ℕ) (hd : 0 < d) (hmd : m < d)
    (label : (iteratedBoundary d r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode d r).neg v) = (label v).neg) :
    ∃ (s : Finset (iteratedBoundary d r).Vertex),
      (iteratedBoundary d r).IsFace s ∧
        ∃ v ∈ s, ∃ w ∈ s, label v = (label w).neg := by
  by_contra hnone
  push Not at hnone
  have hno : NoComplementaryFaceLabels (iteratedBoundary d r) label := by
    intro s hs v hv w hw hcomp
    exact hnone s hs v hv w hw hcomp
  have hodd := odd_fullPositiveAlternatingTop d r m hd label hanti hno
  have hpos : 0 < Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m label) := by
    rcases hodd with ⟨q, hq⟩
    omega
  obtain ⟨T⟩ := Fintype.card_pos_iff.mp hpos
  rcases T.2 with ⟨idx, hidx, hlabels⟩
  have hcard := Fintype.card_le_of_injective idx hidx.injective
  simp only [Fintype.card_fin] at hcard
  omega

end FineTucker

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/StoneTukey.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Finite Stone--Tukey bisection

This file derives the finite central-hyperplane ham-sandwich theorem used by
the polynomial-partitioning construction.  The proof labels a sufficiently
fine antipodal triangulation by a strict-majority open cover and invokes the
fine Tucker lemma.
-/

open scoped BigOperators Topology

namespace StoneTukey

open Set Metric
open ProofsInTheBook.Chapter39
open Erdos95.Barycentric
open Erdos95.FineTucker
open Erdos95.Partitioning

theorem norm_faceAverage_le_one
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (F : BaryVertex K)
    (hf : ∀ v ∈ F.1, ‖f v‖ ≤ 1) :
    ‖faceAverage f F‖ ≤ 1 := by
  have hcardpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hcardne : (F.1.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcardpos)
  calc
    ‖faceAverage f F‖
        = ‖(F.1.card : ℝ)⁻¹‖ * ‖∑ v ∈ F.1, f v‖ := by
          simp only [faceAverage, norm_smul]
    _ ≤ ‖(F.1.card : ℝ)⁻¹‖ * ∑ v ∈ F.1, ‖f v‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ‖(F.1.card : ℝ)⁻¹‖ * ∑ _v ∈ F.1, (1 : ℝ) := by
          gcongr with v hv
          exact hf v hv
    _ = 1 := by
          simp [hcardne]

theorem norm_realize_le_one (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    ‖realize d r v‖ ≤ 1 := by
  induction r with
  | zero => exact norm_signedBasisVector_le_one v
  | succ r ih =>
      exact norm_faceAverage_le_one (realize d r) v
        (fun w _hw ↦ ih w)

/-- A separating sign vector for a realized face.  Unlike an arbitrary
linear separator, its coordinates all have absolute value one; this gives a
subdivision-independent lower bound on the norm of every realized vertex. -/
theorem exists_sign_separator_realize (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    ∃ σ : Fin d → ℝ,
      (∀ i, |σ i| = 1) ∧
        ∀ v ∈ s, (∑ i, σ i * realize d r v i) = 1 := by
  classical
  induction r with
  | zero =>
      let σ : Fin d → ℝ := fun i ↦ if (i, true) ∈ s then 1 else -1
      refine ⟨σ, ?_, ?_⟩
      · intro i
        by_cases hi : (i, true) ∈ s <;> simp [σ, hi]
      · rintro ⟨i, b⟩ hv
        have hnotOpp : (i, !b) ∉ s := by
          intro hopp
          cases b
          · exact hs.2 i ⟨hv, hopp⟩
          · exact hs.2 i ⟨hopp, hv⟩
        cases b
        · have htrue : (i, true) ∉ s := by simpa using hnotOpp
          rw [Finset.sum_eq_single i]
          · have hσi : σ i = -1 := if_neg htrue
            rw [hσi]
            simp [realize, signedBasisVector]
          · intro j _hj hji
            simp [realize, signedBasisVector, hji]
          · simp
        · rw [Finset.sum_eq_single i]
          · have hσi : σ i = 1 := if_pos hv
            rw [hσi]
            simp [realize, signedBasisVector]
          · intro j _hj hji
            simp [realize, signedBasisVector, hji]
          · simp
  | succ r ih =>
      obtain ⟨M, hMs, hlargest⟩ := exists_chain_largest hs
      obtain ⟨σ, hσ, hsep⟩ := ih M.2
      refine ⟨σ, hσ, ?_⟩
      intro F hFs
      have hFM : F.1 ⊆ M.1 := hlargest F hFs
      have hcardpos : 0 < F.1.card :=
        Finset.card_pos.mpr ((iteratedBoundary d r).face_nonempty F.2)
      have hcardne : (F.1.card : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcardpos)
      let L : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun y ↦ ∑ i, σ i * y i
          map_add' := by
            intro x y
            simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          map_smul' := by
            intro a y
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [RingHom.id_apply]
            ring }
      change L (faceAverage (realize d r) F) = 1
      unfold faceAverage
      rw [LinearMapClass.map_smul, map_sum]
      have hsum : (∑ x ∈ F.1, L (realize d r x)) =
          ∑ _x ∈ F.1, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hsep x (hFM hx)
      rw [hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_eq_mul]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hcardne

theorem one_le_card_mul_norm_realize (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    1 ≤ (d : ℝ) * ‖realize d r v‖ := by
  classical
  obtain ⟨σ, hσ, hsep⟩ := exists_sign_separator_realize d r
    ((iteratedBoundary d r).singleton_face v)
  have hvsep := hsep v (by simp)
  calc
    (1 : ℝ) = |∑ i, σ i * realize d r v i| := by rw [hvsep]; norm_num
    _ ≤ ∑ i, |σ i * realize d r v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _i : Fin d, |realize d r v _i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, hσ i, one_mul]
    _ ≤ (d : ℝ) * ‖realize d r v‖ := by
      simpa [nsmul_eq_mul] using
        (Pi.sum_norm_apply_le_norm (realize d r v))

/-! ## The strict-majority open cover -/

/-- Evaluation of a coefficient vector against a finite-dimensional feature
vector. -/
noncomputable def linearValueFin {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (c : Fin d → ℝ) (x : X) : ℝ :=
  ∑ j, c j * a x j

theorem linearValueFin_neg {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (c : Fin d → ℝ) (x : X) :
    linearValueFin a (-c) x = -linearValueFin a c x := by
  simp only [linearValueFin, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

theorem continuous_linearValueFin {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (x : X) :
    Continuous (fun c : Fin d → ℝ ↦ linearValueFin a c x) := by
  unfold linearValueFin
  fun_prop

/-- Coefficients for which family `i` has a strict positive majority. -/
def positiveMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    Set (Fin d → ℝ) :=
  {c | (S i).card < 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card}

/-- Coefficients for which family `i` has a strict negative majority. -/
def negativeMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    Set (Fin d → ℝ) :=
  {c | (S i).card < 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card}

theorem isOpen_positiveMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    IsOpen (positiveMajoritySet S a i) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro c hc
  let T := (S i).filter fun x ↦ 0 < linearValueFin a c x
  have hTcard : (S i).card < 2 * T.card := hc
  have hstable : ∀ᶠ z in 𝓝 c,
      ∀ x ∈ T, 0 < linearValueFin a z x := by
    apply T.eventually_all.mpr
    intro x hx
    have hxpos : 0 < linearValueFin a c x := (Finset.mem_filter.mp hx).2
    exact (isOpen_lt continuous_const (continuous_linearValueFin a x)).mem_nhds hxpos
  filter_upwards [hstable] with z hz
  have hsub : T ⊆ (S i).filter (fun x ↦ 0 < linearValueFin a z x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hz x hx⟩
  exact lt_of_lt_of_le hTcard
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))

theorem isOpen_negativeMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    IsOpen (negativeMajoritySet S a i) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro c hc
  let T := (S i).filter fun x ↦ linearValueFin a c x < 0
  have hTcard : (S i).card < 2 * T.card := hc
  have hstable : ∀ᶠ z in 𝓝 c,
      ∀ x ∈ T, linearValueFin a z x < 0 := by
    apply T.eventually_all.mpr
    intro x hx
    have hxneg : linearValueFin a c x < 0 := (Finset.mem_filter.mp hx).2
    exact (isOpen_lt (continuous_linearValueFin a x) continuous_const).mem_nhds hxneg
  filter_upwards [hstable] with z hz
  have hsub : T ⊆ (S i).filter (fun x ↦ linearValueFin a z x < 0) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hz x hx⟩
  exact lt_of_lt_of_le hTcard
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))

/-- The signed cover pairs positive and negative strict-majority sets. -/
def majorityCover {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) : Set (Fin d → ℝ) :=
  if L.positive then positiveMajoritySet S a L.index
  else negativeMajoritySet S a L.index

theorem isOpen_majorityCover {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) :
    IsOpen (majorityCover S a L) := by
  cases h : L.positive <;>
    simp [majorityCover, h, isOpen_positiveMajoritySet,
      isOpen_negativeMajoritySet]

theorem positiveMajoritySet_neg_iff_negative {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    -c ∈ positiveMajoritySet S a i ↔ c ∈ negativeMajoritySet S a i := by
  classical
  simp [positiveMajoritySet, negativeMajoritySet, linearValueFin_neg]

theorem negativeMajoritySet_neg_iff_positive {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    -c ∈ negativeMajoritySet S a i ↔ c ∈ positiveMajoritySet S a i := by
  classical
  simp [positiveMajoritySet, negativeMajoritySet, linearValueFin_neg]

theorem mem_majorityCover_neg_iff {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) :
    -c ∈ majorityCover S a L.neg ↔ c ∈ majorityCover S a L := by
  cases h : L.positive <;>
    simp [majorityCover, SignedLabel.neg, h,
      positiveMajoritySet_neg_iff_negative,
      negativeMajoritySet_neg_iff_positive]

/-- A compact annulus containing every realized subdivision vertex. -/
def coefficientAnnulus (d : ℕ) : Set (Fin d → ℝ) :=
  Metric.closedBall 0 1 ∩ {c | 1 ≤ (d : ℝ) * ‖c‖}

theorem isCompact_coefficientAnnulus (d : ℕ) :
    IsCompact (coefficientAnnulus d) := by
  apply (isCompact_closedBall (0 : Fin d → ℝ) 1).inter_right
  exact isClosed_le continuous_const (continuous_const.mul continuous_norm)

theorem realize_mem_coefficientAnnulus (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    realize d r v ∈ coefficientAnnulus d := by
  constructor
  · simpa [Metric.mem_closedBall, _root_.dist_zero_right] using norm_realize_le_one d r v
  · exact one_le_card_mul_norm_realize d r v

theorem mem_coefficientAnnulus_ne_zero {d : ℕ}
    {c : Fin d → ℝ} (hc : c ∈ coefficientAnnulus d) : c ≠ 0 := by
  intro hzero
  subst c
  have h := hc.2
  norm_num at h

theorem positive_negative_majority_disjoint {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    ¬(c ∈ positiveMajoritySet S a i ∧
      c ∈ negativeMajoritySet S a i) := by
  classical
  intro h
  let P := (S i).filter fun x ↦ 0 < linearValueFin a c x
  let N := (S i).filter fun x ↦ linearValueFin a c x < 0
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    have hp := (Finset.mem_filter.mp hxP).2
    have hn := (Finset.mem_filter.mp hxN).2
    linarith
  have hunion : P ∪ N ⊆ S i := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxN
    · exact (Finset.mem_filter.mp hxP).1
    · exact (Finset.mem_filter.mp hxN).1
  have hcard : P.card + N.card ≤ (S i).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hp : (S i).card < 2 * P.card := h.1
  have hn : (S i).card < 2 * N.card := h.2
  omega

theorem majorityCover_disjoint_neg {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) :
    ¬(c ∈ majorityCover S a L ∧ c ∈ majorityCover S a L.neg) := by
  cases h : L.positive <;>
    simp only [majorityCover, SignedLabel.neg, h, Bool.not_false,
      Bool.not_true, ↓reduceIte]
  · intro hboth
    exact positive_negative_majority_disjoint S a L.index c
      ⟨hboth.2, hboth.1⟩
  · exact positive_negative_majority_disjoint S a L.index c

theorem ball_neg_subset_majorityCover_neg {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) (δ : ℝ)
    (h : Metric.ball c δ ⊆ majorityCover S a L) :
    Metric.ball (-c) δ ⊆ majorityCover S a L.neg := by
  intro z hz
  have hz' : -z ∈ Metric.ball c δ := by
    change dist (-z) c < δ
    change dist z (-c) < δ at hz
    calc
      dist (-z) c = dist (-z) (-(-c)) := by simp
      _ = dist z (-c) := dist_neg_neg z (-c)
      _ < δ := hz
  have hmem := h hz'
  simpa using (mem_majorityCover_neg_iff S a L (-z)).mpr hmem

theorem coefficientAnnulus_covered_of_no_bisection
    {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (hnone : ¬ ∃ c : Fin d → ℝ, c ≠ 0 ∧
      ∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i)) :
    coefficientAnnulus d ⊆ ⋃ L : SignedLabel m, majorityCover S a L := by
  classical
  intro c hc
  have hcne : c ≠ 0 := mem_coefficientAnnulus_ne_zero hc
  have hnotall : ¬∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i) := by
    intro hall
    exact hnone ⟨c, hcne, hall⟩
  push Not at hnotall
  obtain ⟨i, hi⟩ := hnotall
  have hbad :
      (S i).card < 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ∨
      (S i).card < 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card := by
    change ¬(2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ≤
        (S i).card ∧
      2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card ≤
        (S i).card) at hi
    by_cases hp : 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ≤
        (S i).card
    · right
      have hn : ¬ 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card ≤
          (S i).card := fun hn ↦ hi ⟨hp, hn⟩
      omega
    · left
      omega
  rcases hbad with hpos | hneg
  · let L : SignedLabel m := ⟨true, i⟩
    exact Set.mem_iUnion.mpr ⟨L, by simpa [majorityCover, positiveMajoritySet]⟩
  · let L : SignedLabel m := ⟨false, i⟩
    exact Set.mem_iUnion.mpr ⟨L, by simpa [majorityCover, negativeMajoritySet]⟩

theorem iteratedAntipode_ne (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    (iteratedAntipode d r).neg v ≠ v := by
  intro hfixed
  have hanti := realize_antipode d r v
  rw [hfixed] at hanti
  have hzero : realize d r v = 0 := by
    funext i
    change realize d r v i = (0 : ℝ)
    have hi := congrFun hanti i
    simp only [Pi.neg_apply] at hi
    linarith
  exact realize_ne_zero d r v hzero

/-! ## Finite-dimensional Stone--Tukey -/

/-- Simultaneous bisection for families already indexed by standard finite
types. -/
theorem finiteLinearBisection_fin {X : Type*} (m d : ℕ) (hmd : m < d)
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) :
    ∃ c : Fin d → ℝ, c ≠ 0 ∧
      ∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i) := by
  classical
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le m) hmd
  by_cases hm : m = 0
  · subst m
    let j : Fin d := ⟨0, hd⟩
    let c : Fin d → ℝ := Pi.single j 1
    refine ⟨c, ?_, ?_⟩
    · intro hc
      have hj := congrFun hc j
      simp [c, j] at hj
    · intro i
      exact Fin.elim0 i
  · by_contra hnone
    have hcover : coefficientAnnulus d ⊆
        ⋃ L : SignedLabel m, majorityCover S a L :=
      coefficientAnnulus_covered_of_no_bisection S a hnone
    obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric
      (isCompact_coefficientAnnulus d)
      (fun L ↦ isOpen_majorityCover S a L) hcover
    obtain ⟨r, hmesh⟩ :=
      exists_iteratedBoundary_faceDiameter_lt d hd hδ
    let A := iteratedAntipode d r
    let eV := Fintype.equivFin (iteratedBoundary d r).Vertex
    let pick : (iteratedBoundary d r).Vertex → SignedLabel m :=
      fun v ↦ Classical.choose
        (hLeb (realize d r v) (realize_mem_coefficientAnnulus d r v))
    have hpick (v : (iteratedBoundary d r).Vertex) :
        Metric.ball (realize d r v) δ ⊆ majorityCover S a (pick v) :=
      Classical.choose_spec
        (hLeb (realize d r v) (realize_mem_coefficientAnnulus d r v))
    let label : (iteratedBoundary d r).Vertex → SignedLabel m :=
      fun v ↦ if eV v < eV (A.neg v) then pick v else (pick (A.neg v)).neg
    have hlabelAnti (v : (iteratedBoundary d r).Vertex) :
        label (A.neg v) = (label v).neg := by
      by_cases hv : eV v < eV (A.neg v)
      · have hrev : ¬ eV (A.neg v) < eV (A.neg (A.neg v)) := by
          rw [A.neg_neg]
          exact not_lt_of_ge (le_of_lt hv)
        simp only [label]
        rw [if_pos hv, if_neg hrev, A.neg_neg]
      · have hne : eV (A.neg v) ≠ eV v := by
          intro heq
          exact iteratedAntipode_ne d r v (eV.injective heq)
        have hrev : eV (A.neg v) < eV (A.neg (A.neg v)) := by
          rw [A.neg_neg]
          exact lt_of_le_of_ne (le_of_not_gt hv) hne
        simp only [label]
        rw [if_neg hv, if_pos hrev]
        apply SignedLabel.ext <;> simp [SignedLabel.neg]
    have hlabelCandidate (v : (iteratedBoundary d r).Vertex) :
        Metric.ball (realize d r v) δ ⊆ majorityCover S a (label v) := by
      by_cases hv : eV v < eV (A.neg v)
      · simpa [label, hv] using hpick v
      · have hflip := ball_neg_subset_majorityCover_neg S a
          (pick (A.neg v)) (realize d r (A.neg v)) δ (hpick (A.neg v))
        simpa [label, hv, A, realize_antipode] using hflip
    obtain ⟨s, hs, v, hv, w, hw, hcomp⟩ :=
      exists_complementary_face_of_antipodal_of_lt d r m hd hmd
        label hlabelAnti
    have hvCandidate := hlabelCandidate v
    have hwCandidate := hlabelCandidate w
    have hvw : dist (realize d r v) (realize d r w) < δ :=
      hmesh hs hv hw
    have hwBallV : realize d r w ∈ Metric.ball (realize d r v) δ := by
      simpa only [Metric.mem_ball, dist_comm] using hvw
    have hwInV := hvCandidate hwBallV
    rw [hcomp] at hwInV
    have hwInW := hwCandidate (Metric.mem_ball_self hδ)
    exact majorityCover_disjoint_neg S a (label w) (realize d r w)
      ⟨hwInW, hwInV⟩

/-- The universal finite central-hyperplane bisection theorem. -/
theorem finiteLinearBisection : FiniteLinearBisection := by
  classical
  intro I B X _instI _instB hcard S a
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let S' : Fin (Fintype.card I) → Finset X := fun i ↦ S (eI.symm i)
  let a' : X → Fin (Fintype.card B) → ℝ := fun x j ↦ a x (eB.symm j)
  obtain ⟨c', hc', hbisect⟩ :=
    finiteLinearBisection_fin (Fintype.card I) (Fintype.card B)
      hcard S' a'
  let c : B → ℝ := fun b ↦ c' (eB b)
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hc'
    funext j
    have hj := congrFun hc (eB.symm j)
    simpa [c] using hj
  · intro i
    have hsum (x : X) :
        linearValueFin a' c' x = ∑ b : B, c b * a x b := by
      unfold linearValueFin
      symm
      apply Fintype.sum_equiv eB
      intro b
      simp [a', c]
    simpa only [S', eI.symm_apply_apply, hsum] using hbisect (eI i)

end StoneTukey

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/PartitionCells.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Covering a finite point set by strict sign cells and its wall

The iterated bisection construction uses strict sign cells.  This file
records the complementary fact needed by the incidence induction: every
input point is either on the product wall or belongs to the sign cell given
by the signs of the factors at that point.
-/

namespace PartitionCells

open Erdos95.Partitioning

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space3 := Fin 3 → ℝ

/-- Points of `S` on the product partition wall. -/
noncomputable def wallPoints (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) : Finset Space3 := by
  classical
  exact S.filter fun x ↦ MvPolynomial.eval x (partitionPolynomial p) = 0

theorem mem_wallPoints_iff {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {x : Space3} :
    x ∈ wallPoints S p ↔
      x ∈ S ∧ MvPolynomial.eval x (partitionPolynomial p) = 0 := by
  classical
  simp [wallPoints]

/-- The strict sign pattern selected by a point. -/
noncomputable def pointSign {J : ℕ} (p : Fin J → Poly3)
    (x : Space3) : Fin J → Bool := fun j ↦ decide (0 < MvPolynomial.eval x (p j))

theorem mem_signCell_pointSign {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {x : Space3} (hxS : x ∈ S)
    (hxwall : MvPolynomial.eval x (partitionPolynomial p) ≠ 0) :
    x ∈ signCell S p (pointSign p x) := by
  classical
  apply mem_signCell_iff.mpr
  refine ⟨hxS, ?_⟩
  intro j
  have hj : MvPolynomial.eval x (p j) ≠ 0 := by
    intro hzero
    apply hxwall
    rw [eval_partitionPolynomial]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hzero
  unfold pointSign
  simp only [decide_eq_true_eq]
  split
  · assumption
  · have := lt_or_gt_of_ne hj
    tauto

/-- Every input point is covered by the product wall or by one strict sign
cell. -/
theorem mem_wallPoints_or_exists_mem_signCell
    {S : Finset Space3} {J : ℕ} {p : Fin J → Poly3} {x : Space3}
    (hx : x ∈ S) :
    x ∈ wallPoints S p ∨
      ∃ sign : Fin J → Bool, x ∈ signCell S p sign := by
  classical
  by_cases hwall : MvPolynomial.eval x (partitionPolynomial p) = 0
  · exact Or.inl (mem_wallPoints_iff.mpr ⟨hx, hwall⟩)
  · exact Or.inr ⟨pointSign p x, mem_signCell_pointSign hx hwall⟩

end PartitionCells

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/GuthStructure.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The finite strong incidence statement

This is the denominator-free form of Guth's Theorem 2.1 used by the
low-degree induction.  The output is a small collection of normalized
irreducible low-degree surfaces accounting for all but a controlled number
of rich points.
-/

namespace GuthStructure

open Erdos95.ES Erdos95.LineFamilies
open Erdos95.RichPointCombinatorics Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- A richness threshold comparable to `r/2`, but always at least two. -/
def reducedRichness (r : ℕ) : ℕ := max 2 ((r + 1) / 2)

theorem two_le_reducedRichness (r : ℕ) : 2 ≤ reducedRichness r := by
  simp [reducedRichness]

theorem reducedRichness_le {r : ℕ} (hr : 2 ≤ r) :
    reducedRichness r ≤ r := by
  unfold reducedRichness
  apply max_le hr
  omega

theorem richness_le_two_mul_reduced (r : ℕ) :
    r ≤ 2 * reducedRichness r := by
  unfold reducedRichness
  omega

theorem richness_le_two_mul_loss {r : ℕ} (hr : 2 ≤ r) :
    r ≤ 2 * (r - (reducedRichness r - 1)) := by
  have hs := reducedRichness_le hr
  unfold reducedRichness at hs ⊢
  omega

theorem richness_pair_le_eight_reduced_pair {r : ℕ} (hr : 2 ≤ r) :
    r * (r - 1) ≤
      8 * (reducedRichness r * (reducedRichness r - 1)) := by
  have htwo := two_le_reducedRichness r
  have hhalf := richness_le_two_mul_reduced r
  have hpred : reducedRichness r ≤ 2 * (reducedRichness r - 1) := by
    omega
  calc
    r * (r - 1) ≤
        (2 * reducedRichness r) * (2 * reducedRichness r) := by
      gcongr
      omega
    _ = 4 * reducedRichness r * reducedRichness r := by ring
    _ ≤ 4 * reducedRichness r * (2 * (reducedRichness r - 1)) := by
      gcongr
    _ = 8 * (reducedRichness r * (reducedRichness r - 1)) := by ring

/-- The rich points not accounted for by the selected surfaces. -/
noncomputable def residualRichPoints (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) : Finset Space3 := by
  classical
  exact richPoints L r \ surfaceRichPoints L F (reducedRichness r)

theorem mem_residualRichPoints_iff {L : Finset LineIndex}
    {F : Finset Poly3} {r : ℕ} {x : Space3} :
    x ∈ residualRichPoints L F r ↔
      x ∈ richPoints L r ∧
        x ∉ surfaceRichPoints L F (reducedRichness r) := by
  classical
  simp [residualRichPoints]

theorem residualRichPoints_antitone_surfaces
    (L : Finset LineIndex) {F G : Finset Poly3} (hFG : F ⊆ G) (r : ℕ) :
    residualRichPoints L G r ⊆ residualRichPoints L F r := by
  intro x hx
  have hxdata := mem_residualRichPoints_iff.mp hx
  exact mem_residualRichPoints_iff.mpr ⟨hxdata.1, fun hxF ↦
    hxdata.2 (surfaceRichPoints_mono_collection L hFG _ hxF)⟩

/-- One instance of the strong low-degree incidence conclusion. -/
structure Certificate (epsilon : ℝ) (D : ℕ) (K : ℝ)
    (L : Finset LineIndex) (r : ℕ) where
  surfaces : Finset Poly3
  irreducible : ∀ Q ∈ surfaces, Irreducible Q
  normalized : ∀ Q ∈ surfaces, normalize Q = Q
  degree_le : ∀ Q ∈ surfaces, Q.totalDegree ≤ D
  many_lines : ∀ Q ∈ surfaces,
    (L.card : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
      ((surfaceLines L Q).card : ℝ)
  surface_count :
    (surfaces.card : ℝ) ≤
      2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - epsilon)
  residual_bound :
    ((r * (r - 1) * (residualRichPoints L surfaces r).card : ℕ) : ℝ) ≤
      K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + epsilon)

/-- The structural part of a certificate, before proving its residual
incidence estimate. -/
def Admissible (epsilon : ℝ) (D : ℕ) (L : Finset LineIndex)
    (F : Finset Poly3) : Prop :=
  (∀ Q ∈ F, Irreducible Q) ∧
  (∀ Q ∈ F, normalize Q = Q) ∧
  (∀ Q ∈ F, Q.totalDegree ≤ D) ∧
  (∀ Q ∈ F,
    (L.card : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
      ((surfaceLines L Q).card : ℝ)) ∧
  ((F.card : ℝ) ≤
    2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - epsilon))

theorem admissible_empty (epsilon : ℝ) (D : ℕ)
    (L : Finset LineIndex) : Admissible epsilon D L ∅ := by
  unfold Admissible
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  norm_num
  exact Real.rpow_nonneg (by positivity) _

/-- Among all admissible collections, choose one whose unexplained rich
point set has minimum cardinality.  This well-ordering device replaces an
explicit logarithmic iteration of the bad-cell step. -/
theorem exists_minimal_admissible (epsilon : ℝ) (D : ℕ)
    (L : Finset LineIndex) (r : ℕ) :
    ∃ F : Finset Poly3, Admissible epsilon D L F ∧
      ∀ G : Finset Poly3, Admissible epsilon D L G →
        (residualRichPoints L F r).card ≤
          (residualRichPoints L G r).card := by
  classical
  let score : ℕ → Prop := fun n ↦
    ∃ F : Finset Poly3, Admissible epsilon D L F ∧
      (residualRichPoints L F r).card = n
  have hex : ∃ n, score n := by
    refine ⟨(residualRichPoints L ∅ r).card, ∅,
      admissible_empty epsilon D L, rfl⟩
  let n := Nat.find hex
  obtain ⟨F, hF, hscore⟩ := Nat.find_spec hex
  refine ⟨F, hF, ?_⟩
  intro G hG
  have hGn : score (residualRichPoints L G r).card := ⟨G, hG, rfl⟩
  rw [hscore]
  exact Nat.find_min' hex hGn

end GuthStructure

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/WallFactors.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Rich points on a reducible partition wall

A point on a product wall lies on an irreducible factor.  Applying the
external-line incidence estimate factor by factor bounds wall points not
already rich in one of the factor line subfamilies.
-/

open scoped BigOperators

namespace WallFactors

open Erdos95.ES Erdos95.LineFamilies Erdos95.SurfaceFactors
open Erdos95.RichPointCombinatorics Erdos95.WallIncidences

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Selected points on one irreducible factor wall. -/
noncomputable def pointsOnFactor (S : Finset Space3) (R : Poly3) :
    Finset Space3 := by
  classical
  exact S.filter fun x ↦ MvPolynomial.eval x R = 0

theorem mem_pointsOnFactor_iff {S : Finset Space3} {R : Poly3}
    {x : Space3} :
    x ∈ pointsOnFactor S R ↔ x ∈ S ∧ MvPolynomial.eval x R = 0 := by
  classical
  simp [pointsOnFactor]

theorem subset_biUnion_pointsOnFactor {S : Finset Space3} {Q : Poly3}
    (hQ : Q ≠ 0) (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    S ⊆ (irreducibleFactors Q).biUnion (pointsOnFactor S) := by
  classical
  intro x hx
  obtain ⟨R, hRQ, hRx⟩ := exists_factor_eval_eq_zero hQ (hwall x hx)
  exact Finset.mem_biUnion.mpr ⟨R, hRQ,
    mem_pointsOnFactor_iff.mpr ⟨hx, hRx⟩⟩

/-- Factorwise denominator-free estimate for points on a reducible wall
which are not rich on any irreducible factor. -/
theorem strict_loss_mul_card_le_wall_degree_mul_lines
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hQ : Q ≠ 0) (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (Erdos95.LineFamilies.linesThrough L x).card)
    (hSnot : ∀ x ∈ S,
      x ∉ surfaceRichPoints L (irreducibleFactors Q) r')
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (r - (r' - 1)) * S.card ≤ Q.totalDegree * L.card := by
  classical
  have hcover := subset_biUnion_pointsOnFactor hQ hwall
  calc
    (r - (r' - 1)) * S.card ≤
        (r - (r' - 1)) *
          ((irreducibleFactors Q).biUnion (pointsOnFactor S)).card := by
      exact Nat.mul_le_mul_left _ (Finset.card_le_card hcover)
    _ ≤ (r - (r' - 1)) *
          ∑ R ∈ irreducibleFactors Q, (pointsOnFactor S R).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ = ∑ R ∈ irreducibleFactors Q,
        (r - (r' - 1)) * (pointsOnFactor S R).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ R ∈ irreducibleFactors Q, R.totalDegree * L.card := by
      apply Finset.sum_le_sum
      intro R hRQ
      apply richness_strict_loss_mul_card_le_degree_mul_lines hr'
      · intro x hx
        exact hSrich x (mem_pointsOnFactor_iff.mp hx).1
      · intro x hx hxr
        exact hSnot x (mem_pointsOnFactor_iff.mp hx).1
          (mem_surfaceRichPoints_iff.mpr ⟨R, hRQ, hxr⟩)
      · intro x hx
        exact (mem_pointsOnFactor_iff.mp hx).2
    _ = (∑ R ∈ irreducibleFactors Q, R.totalDegree) * L.card := by
      rw [Finset.sum_mul]
    _ ≤ Q.totalDegree * L.card := by
      gcongr
      exact sum_totalDegree_irreducibleFactors_le hQ

end WallFactors

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SpecialFamily.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Low-degree walls for subfamilies of an Elekes--Sharir family

The non-clustering theorem is stated for the full family `P × P`.  The
incidence induction repeatedly passes to subfamilies, so this file records
the monotone form which is used at every descendant node.
-/

namespace SpecialFamily

open Erdos95.ES Erdos95.LineFamilies Erdos95.NonClustering
open Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

theorem surfaceLines_subset_lineIndicesOnSurface
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    (Q : Poly3) :
    surfaceLines L Q ⊆ lineIndicesOnSurface P Q := by
  classical
  intro l hl
  have hldata := mem_surfaceLines_iff.mp hl
  exact Finset.mem_filter.mpr ⟨hL hldata.1, hldata.2⟩

/-- Every irreducible surface of degree at most `d` contains only linearly
many lines of any subfamily of the special `P × P` line family. -/
theorem card_surfaceLines_le_degree
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    {Q : Poly3} (hQirr : Irreducible Q) {d : ℕ}
    (hdeg : Q.totalDegree ≤ d) :
    (surfaceLines L Q).card ≤
      surfaceLineConstant d * (P.card + 1) := by
  exact (Finset.card_le_card
    (surfaceLines_subset_lineIndicesOnSurface hL Q)).trans
      (card_lineIndicesOnSurface_le_degree P hQirr hdeg)

/-- A subfamily has at most `|P|` members through one point. -/
theorem card_linesThrough_le_points
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    (x : Space3) :
    (Erdos95.LineFamilies.linesThrough L x).card ≤ P.card := by
  classical
  let S := Erdos95.LineFamilies.linesThrough L x
  have hinj : Set.InjOn Prod.fst (S : Set LineIndex) := by
    intro a ha b hb hab
    have ha' := Erdos95.LineFamilies.mem_linesThrough_iff.mp ha
    have hb' := Erdos95.LineFamilies.mem_linesThrough_iff.mp hb
    have hint : Intersects a.1 a.2 b.1 b.2 :=
      ⟨x, ha'.2, hb'.2⟩
    have hdist : dist a.1 b.1 = dist a.2 b.2 :=
      sqDist_eq_iff_dist_eq.mp (sqDist_eq_of_intersects hint)
    have hsecond : a.2 = b.2 := by
      apply dist_eq_zero.mp
      simpa [hab] using hdist.symm
    exact Prod.ext hab hsecond
  have hcard : (S.image Prod.fst).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp
      (hL (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).1)).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

end SpecialFamily

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/PartitionStep.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Elementary facts for one polynomial-partitioning step

These lemmas connect a rich point in a strict sign cell with the line
subfamily entering that cell.  They deliberately make no estimates; the
cardinality bookkeeping is kept separate from the geometry.
-/

namespace PartitionStep

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

theorem cellLines_subset (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (sign : Fin J → Bool) :
    cellLines L S p sign ⊆ L := by
  intro l hl
  exact (mem_cellLines_iff.mp hl).1

theorem linesThrough_subset_cellLines_of_mem_signCell
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    (hx : x ∈ signCell S p sign) :
    Erdos95.LineFamilies.linesThrough L x ⊆ cellLines L S p sign := by
  intro l hl
  have hldata := Erdos95.LineFamilies.mem_linesThrough_iff.mp hl
  exact mem_cellLines_iff.mpr ⟨hldata.1, x, hx, hldata.2⟩

theorem linesThrough_mono_cellLines_of_mem_signCell
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    (hx : x ∈ signCell S p sign) :
    Erdos95.LineFamilies.linesThrough L x ⊆ Erdos95.LineFamilies.linesThrough (cellLines L S p sign) x := by
  intro l hl
  exact Erdos95.LineFamilies.mem_linesThrough_iff.mpr
    ⟨linesThrough_subset_cellLines_of_mem_signCell hx hl,
      (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2⟩

theorem mem_intersectionPoints_cellLines_of_mem
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    {r : ℕ} (hr : 2 ≤ r) (hxcell : x ∈ signCell S p sign)
    (hxrich : x ∈ richPoints L r) :
    x ∈ Erdos95.LineFamilies.intersectionPoints (cellLines L S p sign) := by
  classical
  have hxdata := mem_richPoints_iff.mp hxrich
  have hsub :=
    linesThrough_subset_cellLines_of_mem_signCell (L := L) hxcell
  have htwo : 2 ≤ (Erdos95.LineFamilies.linesThrough L x).card := hr.trans hxdata.2
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp (by omega :
    1 < (Erdos95.LineFamilies.linesThrough L x).card)
  unfold Erdos95.LineFamilies.intersectionPoints
  apply Finset.mem_image.mpr
  refine ⟨(l, m), ?_, ?_⟩
  · unfold intersectingPairs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hsub hl, hsub hm⟩, hlm, ?_⟩
    exact ⟨x, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2,
      (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2⟩
  · apply intersection_unique hlm
    · exact pairIntersection_on_first ⟨x,
        (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2⟩
    · exact pairIntersection_on_second ⟨x,
        (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2, (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2⟩
    · exact (Erdos95.LineFamilies.mem_linesThrough_iff.mp hl).2
    · exact (Erdos95.LineFamilies.mem_linesThrough_iff.mp hm).2

/-- A rich point lying in a strict cell remains rich for the subfamily of
lines which enters that cell. -/
theorem mem_richPoints_cellLines_of_mem
    {L : Finset LineIndex} {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {sign : Fin J → Bool} {x : Space3}
    {r : ℕ} (hr : 2 ≤ r) (hxcell : x ∈ signCell S p sign)
    (hxrich : x ∈ richPoints L r) :
    x ∈ richPoints (cellLines L S p sign) r := by
  apply mem_richPoints_iff.mpr
  refine ⟨mem_intersectionPoints_cellLines_of_mem hr hxcell hxrich, ?_⟩
  exact (mem_richPoints_iff.mp hxrich).2.trans
    (Finset.card_le_card
      (linesThrough_mono_cellLines_of_mem_signCell (L := L) hxcell))

/-- Root-rich points accounted for only by surfaces discarded at threshold
`A` have a uniform ordered-pair bound. -/
theorem root_pair_mul_card_small_surfaceRichPoints_le
    (L : Finset LineIndex) (F : Finset Poly3) (A r : ℕ) (hr : 2 ≤ r) :
    r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (GuthStructure.reducedRichness r)).card ≤
      8 * (F.card * A ^ 2) := by
  have hpair := GuthStructure.richness_pair_le_eight_reduced_pair hr
  have hgeneric := richness_mul_pred_mul_card_surfaceRichPoints_le
    L (smallSurfaces L F A) (GuthStructure.reducedRichness r)
  calc
    r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (GuthStructure.reducedRichness r)).card ≤
        8 * (GuthStructure.reducedRichness r *
          (GuthStructure.reducedRichness r - 1)) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (GuthStructure.reducedRichness r)).card := by
      gcongr
    _ = 8 * ((GuthStructure.reducedRichness r *
          (GuthStructure.reducedRichness r - 1)) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (GuthStructure.reducedRichness r)).card) := by ring
    _ ≤ 8 *
        ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 := by
      gcongr
    _ ≤ 8 * (F.card * A ^ 2) := by
      gcongr
      exact sum_sq_surfaceLines_small_le L F A

end PartitionStep

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/PartitionBookkeeping.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Cardinality bookkeeping for a partitioning step

The bad cells are those whose entering-line family is too large.  The total
line--cell incidence estimate bounds their number, while bisection bounds
their union by a fixed fraction of the point set.
-/

namespace PartitionBookkeeping

open Erdos95.ES Erdos95.Partitioning Erdos95.CellLines

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Sign cells with at least a `1/c` fraction of all lines, in
denominator-free form. -/
noncomputable def badSigns (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦
    L.card ≤ c * (cellLines L S p sign).card

theorem mem_badSigns_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {sign : Fin J → Bool} :
    sign ∈ badSigns L S p c ↔
      L.card ≤ c * (cellLines L S p sign).card := by
  classical
  simp [badSigns]

/-- The points lying in one of the bad strict sign cells. -/
noncomputable def badCellPoints (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset Space3 := by
  classical
  exact (badSigns L S p c).biUnion (signCell S p)

theorem mem_badCellPoints_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {x : Space3} :
    x ∈ badCellPoints L S p c ↔
      ∃ sign ∈ badSigns L S p c, x ∈ signCell S p sign := by
  classical
  simp [badCellPoints]

theorem sum_bad_cellLines_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) :
    ∑ sign ∈ badSigns L S p c, (cellLines L S p sign).card ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  calc
    ∑ sign ∈ badSigns L S p c, (cellLines L S p sign).card ≤
        ∑ sign : Fin J → Bool, (cellLines L S p sign).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ L.card * ((partitionPolynomial p).totalDegree + 1) :=
      sum_card_cellLines_le L S p

/-- There are at most `c(deg Q+1)` bad cells. -/
theorem card_badSigns_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) (hL : 0 < L.card) :
    (badSigns L S p c).card ≤
      c * ((partitionPolynomial p).totalDegree + 1) := by
  classical
  have hlower :
      L.card * (badSigns L S p c).card ≤
        c * ∑ sign ∈ badSigns L S p c,
          (cellLines L S p sign).card := by
    calc
      L.card * (badSigns L S p c).card =
          ∑ _sign ∈ badSigns L S p c, L.card := by
        simp [Nat.mul_comm]
      _ ≤ ∑ sign ∈ badSigns L S p c,
          c * (cellLines L S p sign).card := by
        apply Finset.sum_le_sum
        intro sign hsign
        exact mem_badSigns_iff.mp hsign
      _ = c * ∑ sign ∈ badSigns L S p c,
          (cellLines L S p sign).card := by
        rw [Finset.mul_sum]
  have hupper := Nat.mul_le_mul_left c (sum_bad_cellLines_le L S p c)
  have hcombined :
      L.card * (badSigns L S p c).card ≤
        L.card * (c * ((partitionPolynomial p).totalDegree + 1)) := by
    calc
      L.card * (badSigns L S p c).card ≤
          c * ∑ sign ∈ badSigns L S p c,
            (cellLines L S p sign).card := hlower
      _ ≤ c * (L.card * ((partitionPolynomial p).totalDegree + 1)) := hupper
      _ = L.card * (c * ((partitionPolynomial p).totalDegree + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hcombined hL

theorem card_badCellPoints_le_sum
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) :
    (badCellPoints L S p c).card ≤
      ∑ sign ∈ badSigns L S p c, (signCell S p sign).card := by
  classical
  exact Finset.card_biUnion_le

/-- If every strict cell has at most `1/R` of the input points, the union of
bad cells has at most `c(deg Q+1)/R` of them. -/
theorem mul_card_badCellPoints_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c R : ℕ) (hL : 0 < L.card)
    (hcells : ∀ sign : Fin J → Bool,
      R * (signCell S p sign).card ≤ S.card) :
    R * (badCellPoints L S p c).card ≤
      (c * ((partitionPolynomial p).totalDegree + 1)) * S.card := by
  classical
  calc
    R * (badCellPoints L S p c).card ≤
        R * ∑ sign ∈ badSigns L S p c,
          (signCell S p sign).card :=
      Nat.mul_le_mul_left R (card_badCellPoints_le_sum L S p c)
    _ = ∑ sign ∈ badSigns L S p c,
          R * (signCell S p sign).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _sign ∈ badSigns L S p c, S.card := by
      apply Finset.sum_le_sum
      intro sign _hsign
      exact hcells sign
    _ = (badSigns L S p c).card * S.card := by simp
    _ ≤ (c * ((partitionPolynomial p).totalDegree + 1)) * S.card := by
      gcongr
      exact card_badSigns_le L S p c hL

/-- A convenient half-size corollary used in the iteration. -/
theorem two_mul_card_badCellPoints_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c R : ℕ) (hL : 0 < L.card)
    (hRpos : 0 < R)
    (hR : 2 * (c * ((partitionPolynomial p).totalDegree + 1)) ≤ R)
    (hcells : ∀ sign : Fin J → Bool,
      R * (signCell S p sign).card ≤ S.card) :
    2 * (badCellPoints L S p c).card ≤ S.card := by
  let A := c * ((partitionPolynomial p).totalDegree + 1)
  have hmain := mul_card_badCellPoints_le L S p c R hL hcells
  by_cases hA : A = 0
  · have hbad : (badCellPoints L S p c).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.le_of_mul_le_mul_left
      · simpa [A, hA] using hmain
      · exact hRpos
    simp [hbad]
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA
    have hscaled :
        A * (2 * (badCellPoints L S p c).card) ≤ A * S.card := by
      calc
        A * (2 * (badCellPoints L S p c).card) =
            (2 * A) * (badCellPoints L S p c).card := by ring
        _ ≤ R * (badCellPoints L S p c).card :=
          Nat.mul_le_mul_right _ hR
        _ ≤ A * S.card := by simpa [A] using hmain
    exact Nat.le_of_mul_le_mul_left hscaled hApos

end PartitionBookkeeping

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/RpowBookkeeping.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Real-power estimates for cell line counts

This file contains the elementary maximum-times-sum estimate used to sum
the inductive contribution of the good cells.
-/

open scoped BigOperators

namespace RpowBookkeeping

/-- If `c a_i ≤ M` and `∑ a_i ≤ W M`, then the `p`-moment is bounded
by the maximum `(M/c)^(p-1)` times the first moment. -/
theorem sum_natCast_rpow_le_of_mul_le
    {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (M c W : ℕ) (p : ℝ) (hp : 1 ≤ p) (hc : 0 < c)
    (hpoint : ∀ i ∈ s, c * a i ≤ M)
    (hsum : ∑ i ∈ s, a i ≤ W * M) :
    (∑ i ∈ s, ((a i : ℕ) : ℝ) ^ p) ≤
      ((M : ℝ) / (c : ℝ)) ^ (p - 1) * ((W * M : ℕ) : ℝ) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpminus : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hterm : ∀ i ∈ s,
      ((a i : ℕ) : ℝ) ^ p ≤
        ((M : ℝ) / (c : ℝ)) ^ (p - 1) * (a i : ℝ) := by
    intro i hi
    by_cases hai : a i = 0
    · simp [hai, Real.zero_rpow hp0]
    · have haiR : 0 < (a i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hai
      have hcast : (c : ℝ) * (a i : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hpoint i hi
      have hquot : (a i : ℝ) ≤ (M : ℝ) / (c : ℝ) := by
        exact (le_div_iff₀ hcR).mpr (by simpa [mul_comm] using hcast)
      calc
        ((a i : ℕ) : ℝ) ^ p =
            (a i : ℝ) ^ (1 + (p - 1)) := by ring_nf
        _ = (a i : ℝ) * (a i : ℝ) ^ (p - 1) := by
          rw [Real.rpow_add haiR]
          simp
        _ ≤ (a i : ℝ) *
            (((M : ℝ) / (c : ℝ)) ^ (p - 1)) := by
          gcongr
        _ = ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
            (a i : ℝ) := by ring
  calc
    (∑ i ∈ s, ((a i : ℕ) : ℝ) ^ p) ≤
        ∑ i ∈ s,
          ((M : ℝ) / (c : ℝ)) ^ (p - 1) * (a i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
        ∑ i ∈ s, (a i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
        ((W * M : ℕ) : ℝ) := by
      gcongr
      exact_mod_cast hsum

end RpowBookkeeping

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/GuthParameters.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Fixed parameters for Guth's partitioning recurrence

For every positive loss `η ≤ 1/4` we choose a finite sequence of box
degrees.  Its number of sign cells dominates both the bad-cell loss and the
`(3/2+η)` moment of the good cell line counts.
-/

open scoped BigOperators

namespace GuthParameters

/-- The sum of the degree budgets for the successive cuts. -/
def wallDegree {J : ℕ} (k : Fin J → ℕ) : ℕ :=
  ∑ j, 3 * k j

/-- One more than the wall degree, the line--cell crossing budget. -/
def crossingBudget {J : ℕ} (k : Fin J → ℕ) : ℕ :=
  wallDegree k + 1

/-- Numerical data needed by one fixed-degree partitioning step. -/
structure Parameters (η : ℝ) where
  J : ℕ
  k : Fin J → ℕ
  c : ℕ
  c_pos : 0 < c
  fit : ∀ j : Fin J, 2 ^ (j : ℕ) < (k j + 1) ^ 3
  bad_half : 2 * (c * crossingBudget k) ≤ 2 ^ J
  contraction :
    16 * (((1 : ℝ) / (c : ℝ)) ^ ((1 : ℝ) / 2 + η)) *
        (crossingBudget k : ℝ) ≤ 1

theorem wallDegree_const (J K : ℕ) :
    wallDegree (fun _ : Fin J ↦ K) = J * (3 * K) := by
  simp [wallDegree]

/-- Exponential growth supplies admissible fixed parameters for every
positive `η`.  The explicit construction uses `J=3ts`, cut box degree
`2^(ts)`, and bad-cell threshold `2^((2t-1)s)`. -/
theorem exists_parameters {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ (1 : ℝ) / 4) : Nonempty (Parameters η) := by
  obtain ⟨t, ht⟩ := exists_nat_gt ((1 : ℝ) / η)
  have htpos : 0 < t := by
    by_contra ht0
    have : t = 0 := Nat.eq_zero_of_not_pos ht0
    subst t
    simp only [Nat.cast_zero] at ht
    have : 0 < (1 : ℝ) / η := one_div_pos.mpr hη
    linarith
  have hηt : 1 < η * (t : ℝ) := by
    have := (div_lt_iff₀ hη).mp ht
    simpa [mul_comm] using this
  let C : ℕ := 288 * t
  let s : ℕ := 2 * C
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hspos : 0 < s := by dsimp [s]; positivity
  have hCs : C * s ≤ 2 ^ s := by
    have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul C
    dsimp [s]
    nlinarith
  let J : ℕ := 3 * t * s
  let K : ℕ := 2 ^ (t * s)
  let k : Fin J → ℕ := fun _ ↦ K
  let c : ℕ := 2 ^ ((2 * t - 1) * s)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hwall : wallDegree k = 9 * t * s * 2 ^ (t * s) := by
    rw [show wallDegree k = J * (3 * K) by
      simpa [k] using wallDegree_const J K]
    simp only [J, K]
    ring
  have hwallpos : 0 < wallDegree k := by rw [hwall]; positivity
  have hcross_le : crossingBudget k ≤ 2 * wallDegree k := by
    simp only [crossingBudget]
    omega
  refine ⟨⟨J, k, c, hcpos, ?_, ?_, ?_⟩⟩
  · intro j
    have hjJ : (j : ℕ) < J := j.isLt
    have hpowj : 2 ^ (j : ℕ) < 2 ^ J :=
      Nat.pow_lt_pow_right (by omega) hjJ
    have hJK : 2 ^ J = K ^ 3 := by
      dsimp [J, K]
      rw [← pow_mul]
      congr 1
      ring
    calc
      2 ^ (j : ℕ) < 2 ^ J := hpowj
      _ = K ^ 3 := hJK
      _ < (K + 1) ^ 3 := by
        exact Nat.pow_lt_pow_left (Nat.lt_succ_self K) (by omega)
      _ = (k j + 1) ^ 3 := by rfl
  · have h36 : 36 * t * s ≤ 2 ^ s := by
      calc
        36 * t * s ≤ (288 * t) * s := by gcongr <;> omega
        _ = C * s := by rfl
        _ ≤ 2 ^ s := hCs
    have hbadCore :
        4 * c * wallDegree k ≤ 2 ^ J := by
      rw [hwall]
      dsimp only [c, J]
      have hexp : (2 * t - 1) * s + t * s = 3 * t * s - s := by
        have hsle' : s ≤ 2 * t * s := by
          nlinarith
        calc
          (2 * t - 1) * s + t * s =
              (2 * t * s - s) + t * s := by rw [Nat.sub_mul]; simp
          _ = 2 * t * s + t * s - s :=
            (Nat.sub_add_comm hsle').symm
          _ = 3 * t * s - s := by congr 1 <;> ring
      have hsle : s ≤ 3 * t * s := by
        nlinarith
      calc
        4 * 2 ^ ((2 * t - 1) * s) *
            (9 * t * s * 2 ^ (t * s)) =
            (36 * t * s) *
              2 ^ ((2 * t - 1) * s + t * s) := by
          rw [pow_add]
          ring
        _ ≤ 2 ^ s * 2 ^ (3 * t * s - s) :=
          by
            rw [hexp]
            exact Nat.mul_le_mul_right _ h36
        _ = 2 ^ (3 * t * s) := by
          rw [← pow_add, Nat.add_sub_of_le hsle]
    calc
      2 * (c * crossingBudget k) ≤ 2 * (c * (2 * wallDegree k)) := by
        gcongr
      _ = 4 * c * wallDegree k := by ring
      _ ≤ 2 ^ J := hbadCore
  · have h288 : 288 * t * s ≤ 2 ^ s := by
      simpa [C] using hCs
    have hleft :
        16 * (crossingBudget k : ℝ) ≤
          ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) := by
      have hnat : 16 * crossingBudget k ≤ 2 ^ ((t + 1) * s) := by
        calc
          16 * crossingBudget k ≤ 32 * wallDegree k := by
            omega
          _ = (288 * t * s) * 2 ^ (t * s) := by
            rw [hwall]
            ring
          _ ≤ 2 ^ s * 2 ^ (t * s) := by gcongr
          _ = 2 ^ ((t + 1) * s) := by
            rw [← pow_add]
            congr 1
            ring
      exact_mod_cast hnat
    have hexponent :
        (((t + 1) * s : ℕ) : ℝ) ≤
          (((2 * t - 1) * s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 + η) := by
      have hbase : (t : ℝ) + 1 ≤
          (2 * (t : ℝ) - 1) * ((1 : ℝ) / 2 + η) := by
        nlinarith [hηt, hηle]
      have hcastE : (((2 * t - 1) * s : ℕ) : ℝ) =
          (2 * (t : ℝ) - 1) * (s : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * t)]
        push_cast
        ring
      calc
        (((t + 1) * s : ℕ) : ℝ) =
            ((t : ℝ) + 1) * (s : ℝ) := by push_cast; ring
        _ ≤ ((2 * (t : ℝ) - 1) * ((1 : ℝ) / 2 + η)) *
            (s : ℝ) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = (((2 * t - 1) * s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 + η) := by
          rw [hcastE]
          ring
    have hright :
        ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) ≤
          (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
      have hpowexp := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) hexponent
      calc
        ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) ≤
            (2 : ℝ) ^
              ((((2 * t - 1) * s : ℕ) : ℝ) *
                ((1 : ℝ) / 2 + η)) := hpowexp
        _ = ((2 : ℝ) ^ (((2 * t - 1) * s : ℕ) : ℝ)) ^
              ((1 : ℝ) / 2 + η) :=
          Real.rpow_mul (by positivity) _ _
        _ = (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
          rw [Real.rpow_natCast]
          norm_cast
    have hden :
        16 * (crossingBudget k : ℝ) ≤
          (c : ℝ) ^ ((1 : ℝ) / 2 + η) := hleft.trans hright
    have hcpow : 0 < (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
      exact Real.rpow_pos_of_pos (by positivity) _
    rw [Real.div_rpow (by positivity) (by positivity)]
    rw [Real.one_rpow]
    calc
      16 * (1 / ((c : ℝ) ^ ((1 : ℝ) / 2 + η))) *
          (crossingBudget k : ℝ) =
          (16 * (crossingBudget k : ℝ)) /
            ((c : ℝ) ^ ((1 : ℝ) / 2 + η)) := by
        field_simp
      _ ≤ 1 := (div_le_one hcpow).mpr hden

end GuthParameters

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/ScaleBounds.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Large-scale real-power bounds
-/

namespace ScaleBounds

/-- A positive real power of a natural number eventually exceeds any fixed
real constant. -/
theorem exists_nat_forall_le_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C ≤ (n : ℝ) ^ a := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ a :=
    ht.eventually (Filter.eventually_ge_atTop C)
  exact Filter.eventually_atTop.mp hevent

/-- The threshold may additionally be required to be positive. -/
theorem exists_pos_nat_forall_le_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → C ≤ (n : ℝ) ^ a := by
  obtain ⟨N, hN⟩ := exists_nat_forall_le_rpow ha C
  refine ⟨max 1 N, by omega, ?_⟩
  intro n hn
  exact hN n ((le_max_right 1 N).trans hn)

end ScaleBounds

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/PruneAdmissible.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Pruning a temporary surface collection
-/

namespace PruneAdmissible

open Erdos95.ES Erdos95.LineFamilies Erdos95.GuthStructure
open Erdos95.SurfaceCollections Erdos95.SurfacePruning

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Above the degree-dependent scale, retaining precisely the surfaces with
at least `L^(1/2+η)` lines produces an admissible collection. -/
theorem admissible_largeSurfaces
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ (1 : ℝ) / 4)
    (D : ℕ) (L : Finset LineIndex) (hL : 0 < L.card)
    (F : Finset Poly3)
    (hirr : ∀ Q ∈ F, Irreducible Q)
    (hnorm : ∀ Q ∈ F, normalize Q = Q)
    (hdegree : ∀ Q ∈ F, Q.totalDegree ≤ D)
    (hscale : 4 * (commonLineConstant D : ℝ) <
      (L.card : ℝ) ^ (2 * η)) :
    Admissible η D L
      (largeSurfaces L F
        ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊) := by
  classical
  let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
  let G : Finset Poly3 := largeSurfaces L F A
  have hLR : 0 < (L.card : ℝ) := by exact_mod_cast hL
  have ha : 0 < (1 : ℝ) / 2 + η := by linarith
  have hq : 0 ≤ (1 : ℝ) / 2 - η := by linarith
  have hA : (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) ≤ (A : ℝ) := by
    exact Nat.le_ceil _
  have hquadratic :
      4 * commonLineConstant D * L.card < A ^ 2 := by
    have hmul :
        4 * (commonLineConstant D : ℝ) * (L.card : ℝ) <
          ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
      calc
        4 * (commonLineConstant D : ℝ) * (L.card : ℝ) <
            (L.card : ℝ) ^ (2 * η) * (L.card : ℝ) := by
          exact mul_lt_mul_of_pos_right hscale hLR
        _ = (L.card : ℝ) ^ (2 * η) *
            (L.card : ℝ) ^ (1 : ℝ) := by simp
        _ = (L.card : ℝ) ^ (2 * η + 1) := by
          rw [Real.rpow_add hLR]
        _ = (L.card : ℝ) ^ (1 + 2 * η) := by ring_nf
        _ = ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (le_of_lt hLR)]
          congr 2
          ring
    have hceilSq :
        ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 ≤
          (A : ℝ) ^ 2 := by gcongr
    exact_mod_cast hmul.trans_le hceilSq
  have hlargeNat : ∀ Q ∈ G, A ≤ (surfaceLines L Q).card := by
    intro Q hQ
    exact (mem_largeSurfaces_iff.mp hQ).2
  have hboundNat : A * G.card ≤ 2 * L.card := by
    apply large_surface_collection_bound L G A D
    · intro Q hQ
      exact hirr Q (mem_largeSurfaces_iff.mp hQ).1
    · intro Q hQ
      exact hnorm Q (mem_largeSurfaces_iff.mp hQ).1
    · intro Q hQ
      exact hdegree Q (mem_largeSurfaces_iff.mp hQ).1
    · exact hlargeNat
    · exact hquadratic
  have hboundReal :
      (G.card : ℝ) ≤
        2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    have hcast : (A : ℝ) * (G.card : ℝ) ≤
        2 * (L.card : ℝ) := by exact_mod_cast hboundNat
    have hleft :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (G.card : ℝ) ≤
          2 * (L.card : ℝ) :=
      (mul_le_mul_of_nonneg_right hA (by positivity)).trans hcast
    have hpow :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
          (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) =
            (L.card : ℝ) := by
      rw [← Real.rpow_add hLR]
      norm_num
    have hapos :
        0 < (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) :=
      Real.rpow_pos_of_pos hLR _
    have hrightEq :
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
          (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) =
            2 * (L.card : ℝ) := by
      calc
        (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
            (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) =
          2 * ((L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
            (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) := by ring
        _ = 2 * (L.card : ℝ) := by rw [hpow]
    nlinarith
  change Admissible η D L G
  unfold Admissible
  refine ⟨?_, ?_, ?_, ?_, hboundReal⟩
  · intro Q hQ
    exact hirr Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hnorm Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hdegree Q (mem_largeSurfaces_iff.mp hQ).1
  · intro Q hQ
    exact hA.trans (by exact_mod_cast hlargeNat Q hQ)

end PruneAdmissible

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/PartitionRemainders.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Pointwise decomposition after one partitioning step
-/

namespace PartitionRemainders

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionBookkeeping Erdos95.PartitionStep
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning
open Erdos95.SurfaceFactors Erdos95.GuthStructure

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

/-- Non-bad sign cells. -/
noncomputable def goodSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦ sign ∉ badSigns L S p c

theorem mem_goodSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {sign : Fin J → Bool} :
    sign ∈ goodSigns L S p c ↔ sign ∉ badSigns L S p c := by
  classical
  simp [goodSigns]

/-- Good cells to which the line-family induction applies. -/
noncomputable def lowSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact (goodSigns L S p c).filter fun sign ↦
    r ^ 2 ≤ 4 * (cellLines L S p sign).card

/-- Good cells in the elementary large-richness range. -/
noncomputable def highSigns (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact (goodSigns L S p c).filter fun sign ↦
    4 * (cellLines L S p sign).card < r ^ 2

theorem mem_lowSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool} :
    sign ∈ lowSigns L S p c r ↔
      sign ∈ goodSigns L S p c ∧
        r ^ 2 ≤ 4 * (cellLines L S p sign).card := by
  classical
  simp [lowSigns]

theorem mem_highSigns_iff {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool} :
    sign ∈ highSigns L S p c r ↔
      sign ∈ goodSigns L S p c ∧
        4 * (cellLines L S p sign).card < r ^ 2 := by
  classical
  simp [highSigns]

theorem mem_lowSigns_or_mem_highSigns_of_good
    {L : Finset LineIndex} {S : Finset Space}
    {J : ℕ} {p : Fin J → Poly3} {c r : ℕ} {sign : Fin J → Bool}
    (hsign : sign ∈ goodSigns L S p c) :
    sign ∈ lowSigns L S p c r ∨ sign ∈ highSigns L S p c r := by
  by_cases hlow : r ^ 2 ≤ 4 * (cellLines L S p sign).card
  · exact Or.inl (mem_lowSigns_iff.mpr ⟨hsign, hlow⟩)
  · exact Or.inr (mem_highSigns_iff.mpr
      ⟨hsign, Nat.lt_of_not_ge hlow⟩)

/-- Union of the inductive residuals in the low cells. -/
noncomputable def lowResidualPoints
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) : Finset Space := by
  classical
  exact (lowSigns L S p c r).biUnion fun sign ↦
    residualRichPoints (cellLines L S p sign) (cellF sign) r

/-- Rich points in high cells, controlled by the elementary overlap lemma. -/
noncomputable def highCellRichPoints
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) : Finset Space := by
  classical
  exact (highSigns L S p c r).biUnion fun sign ↦
    signCell S p sign ∩ richPoints (cellLines L S p sign) r

/-- Wall points not rich in the line family of an irreducible wall factor. -/
noncomputable def wallRemainder
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r : ℕ) : Finset Space := by
  classical
  exact wallPoints S p \
    surfaceRichPoints L (irreducibleFactors (partitionPolynomial p))
      (reducedRichness r)

/-- The temporary collection before root-threshold pruning. -/
noncomputable def temporarySurfaces
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) : Finset Poly3 := by
  classical
  exact F₀ ∪ (lowSigns L S p c r).biUnion cellF ∪
    irreducibleFactors (partitionPolynomial p)

/-- Pointwise decomposition of a residual set after pruning. -/
theorem subset_partition_remainders
    {L : Finset LineIndex} {S : Finset Space} {J : ℕ}
    {p : Fin J → Poly3} {c r A : ℕ} (hr : 2 ≤ r)
    (F₀ : Finset Poly3)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hSrich : S ⊆ richPoints L r)
    (havoid : ∀ x ∈ S,
      x ∉ surfaceRichPoints L
        (largeSurfaces L
          (temporarySurfaces F₀ L S p c r cellF) A)
        (reducedRichness r)) :
    S ⊆
      badCellPoints L S p c ∪
      lowResidualPoints L S p c r cellF ∪
      highCellRichPoints L S p c r ∪
      wallRemainder L S p r ∪
      surfaceRichPoints L
        (smallSurfaces L
          (temporarySurfaces F₀ L S p c r cellF) A)
        (reducedRichness r) := by
  classical
  intro x hxS
  have hxrich : x ∈ richPoints L r := hSrich hxS
  rcases mem_wallPoints_or_exists_mem_signCell hxS with hxwall | ⟨sign, hxcell⟩
  · by_cases hxFactor : x ∈
        surfaceRichPoints L (irreducibleFactors (partitionPolynomial p))
          (reducedRichness r)
    · obtain ⟨Q, hQfac, hxQ⟩ := mem_surfaceRichPoints_iff.mp hxFactor
      have hQtemp : Q ∈ temporarySurfaces F₀ L S p c r cellF := by
        simp [temporarySurfaces, hQfac]
      rcases Finset.mem_union.mp
            (surfaces_subset_large_union_small L
            (temporarySurfaces F₀ L S p c r cellF) A hQtemp) with
        hQlarge | hQsmall
      · exact (havoid x hxS
          (mem_surfaceRichPoints_iff.mpr ⟨Q, hQlarge, hxQ⟩)).elim
      · exact Finset.mem_union_right _
          (mem_surfaceRichPoints_iff.mpr ⟨Q, hQsmall, hxQ⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hxwall, hxFactor⟩))
  · by_cases hbad : sign ∈ badSigns L S p c
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_badCellPoints_iff.mpr ⟨sign, hbad, hxcell⟩))))
    · have hgood : sign ∈ goodSigns L S p c :=
        mem_goodSigns_iff.mpr hbad
      rcases mem_lowSigns_or_mem_highSigns_of_good (r := r) hgood with
          hlow | hhigh
      · have hxCellRich := mem_richPoints_cellLines_of_mem hr hxcell hxrich
        by_cases hxSurf : x ∈ surfaceRichPoints
            (cellLines L S p sign) (cellF sign) (reducedRichness r)
        · obtain ⟨Q, hQcell, hxQ⟩ := mem_surfaceRichPoints_iff.mp hxSurf
          have hQtemp : Q ∈ temporarySurfaces F₀ L S p c r cellF := by
            unfold temporarySurfaces
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨sign, hlow, hQcell⟩))
          have hsurfaceMono : surfaceLines (cellLines L S p sign) Q ⊆
              surfaceLines L Q :=
            surfaceLines_mono (cellLines_subset L S p sign) Q
          have hxQroot : x ∈ richPoints (surfaceLines L Q)
              (reducedRichness r) :=
            richPoints_mono_family hsurfaceMono _ hxQ
          rcases Finset.mem_union.mp
              (surfaces_subset_large_union_small L
                (temporarySurfaces F₀ L S p c r cellF) A hQtemp) with
            hQlarge | hQsmall
          · exact (havoid x hxS
              (mem_surfaceRichPoints_iff.mpr
                ⟨Q, hQlarge, hxQroot⟩)).elim
          · exact Finset.mem_union_right _
              (mem_surfaceRichPoints_iff.mpr
                ⟨Q, hQsmall, hxQroot⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨sign, hlow, mem_residualRichPoints_iff.mpr
                  ⟨hxCellRich, hxSurf⟩⟩))))
      · have hxCellRich := mem_richPoints_cellLines_of_mem hr hxcell hxrich
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨sign, hhigh, Finset.mem_inter.mpr
              ⟨hxcell, hxCellRich⟩⟩)))

end PartitionRemainders

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/RemainderBounds.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Cardinality bounds for the partition remainders
-/

namespace RemainderBounds

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionStep Erdos95.PartitionRemainders
open Erdos95.RichPointCombinatorics Erdos95.GuthStructure
open Erdos95.SurfaceFactors Erdos95.WallFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

theorem card_lowResidualPoints_le_sum
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    (lowResidualPoints L S p c r cellF).card ≤
      ∑ sign ∈ lowSigns L S p c r,
        (residualRichPoints (cellLines L S p sign) (cellF sign) r).card := by
  classical
  exact Finset.card_biUnion_le

/-- The large-richness lemma summed over the high cells. -/
theorem root_pair_mul_card_highCellRichPoints_le
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) :
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
      2 * r * ∑ sign ∈ highSigns L S p c r,
        (cellLines L S p sign).card := by
  classical
  calc
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
        r * (r - 1) * ∑ sign ∈ highSigns L S p c r,
          (signCell S p sign ∩ richPoints (cellLines L S p sign) r).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ ≤ r * (r - 1) * ∑ sign ∈ highSigns L S p c r,
          (richPoints (cellLines L S p sign) r).card := by
      gcongr with sign hsign
      exact (show
        signCell S p sign ∩ richPoints (cellLines L S p sign) r ⊆
          richPoints (cellLines L S p sign) r by
        exact Finset.inter_subset_right)
    _ = ∑ sign ∈ highSigns L S p c r,
          r * (r - 1) *
            (richPoints (cellLines L S p sign) r).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ sign ∈ highSigns L S p c r,
          2 * r * (cellLines L S p sign).card := by
      apply Finset.sum_le_sum
      intro sign hsign
      have hlarge := (mem_highSigns_iff.mp hsign).2
      have hprop := richness_mul_card_le_two_mul_lines
        (cellLines L S p sign) r hlarge
      calc
        r * (r - 1) *
            (richPoints (cellLines L S p sign) r).card =
            (r - 1) *
              (r * (richPoints (cellLines L S p sign) r).card) := by ring
        _ ≤ (r - 1) * (2 * (cellLines L S p sign).card) := by
          gcongr
        _ ≤ r * (2 * (cellLines L S p sign).card) := by gcongr; omega
        _ = 2 * r * (cellLines L S p sign).card := by ring
    _ = 2 * r * ∑ sign ∈ highSigns L S p c r,
        (cellLines L S p sign).card := by rw [Finset.mul_sum]

theorem root_pair_mul_card_highCellRichPoints_le_crossing
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) :
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
      2 * r * (L.card * ((partitionPolynomial p).totalDegree + 1)) := by
  refine (root_pair_mul_card_highCellRichPoints_le L S p c r).trans ?_
  gcongr
  calc
    ∑ sign ∈ highSigns L S p c r, (cellLines L S p sign).card ≤
        ∑ sign : Fin J → Bool, (cellLines L S p sign).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (show highSigns L S p c r ⊆ (Finset.univ : Finset (Fin J → Bool)) by
          exact fun _ _ ↦ Finset.mem_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ L.card * ((partitionPolynomial p).totalDegree + 1) :=
      sum_card_cellLines_le L S p

/-- The wall remainder is controlled by the lines crossing the irreducible
factors of the partition wall. -/
theorem root_pair_mul_card_wallRemainder_le
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r : ℕ) (hr : 2 ≤ r)
    (hp : ∀ j, p j ≠ 0)
    (hSrich : S ⊆ richPoints L r) :
    r * (r - 1) * (wallRemainder L S p r).card ≤
      2 * r * ((partitionPolynomial p).totalDegree * L.card) := by
  classical
  let T := wallRemainder L S p r
  have hQ : partitionPolynomial p ≠ 0 := partitionPolynomial_ne_zero p hp
  have hloss := strict_loss_mul_card_le_wall_degree_mul_lines
    hQ (two_le_reducedRichness r)
    (S := T) (L := L) (r := r) (r' := reducedRichness r)
    (fun x hx ↦ (mem_richPoints_iff.mp
      (hSrich (mem_wallPoints_iff.mp (Finset.mem_sdiff.mp hx).1).1)).2)
    (fun x hx ↦ (Finset.mem_sdiff.mp hx).2)
    (fun x hx ↦ (mem_wallPoints_iff.mp (Finset.mem_sdiff.mp hx).1).2)
  have hrLoss := richness_le_two_mul_loss hr
  calc
    r * (r - 1) * T.card = (r - 1) * (r * T.card) := by ring
    _ ≤ (r - 1) *
        (2 * (r - (reducedRichness r - 1)) * T.card) := by
      gcongr
    _ = 2 * (r - 1) *
        ((r - (reducedRichness r - 1)) * T.card) := by ring
    _ ≤ 2 * (r - 1) *
        ((partitionPolynomial p).totalDegree * L.card) := by gcongr
    _ ≤ 2 * r * ((partitionPolynomial p).totalDegree * L.card) := by
      gcongr
      omega

end RemainderBounds

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/TemporarySurfaces.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Structural properties of the temporary surface collection
-/

namespace TemporarySurfaces

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.PartitionRemainders Erdos95.GuthStructure
open Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem base_subset_temporary
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    F₀ ⊆ temporarySurfaces F₀ L S p c r cellF := by
  intro Q hQ
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ)

theorem temporary_irreducible
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : ∀ Q ∈ F₀, Irreducible Q)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, Irreducible Q) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF, Irreducible Q := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact irreducible_of_mem_irreducibleFactors hQfac

theorem temporary_normalized
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : ∀ Q ∈ F₀, normalize Q = Q)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, normalize Q = Q) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF,
      normalize Q = Q := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact normalize_eq_of_mem_irreducibleFactors hQfac

theorem temporary_degree_le
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r D : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hQ : partitionPolynomial p ≠ 0)
    (hQdeg : (partitionPolynomial p).totalDegree ≤ D)
    (hF₀ : ∀ Q ∈ F₀, Q.totalDegree ≤ D)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, Q.totalDegree ≤ D) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF,
      Q.totalDegree ≤ D := by
  intro Q hQmem
  rcases Finset.mem_union.mp hQmem with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact (totalDegree_le_of_mem_irreducibleFactors hQ hQfac).trans hQdeg

theorem card_temporary_le
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    (temporarySurfaces F₀ L S p c r cellF).card ≤
      F₀.card + ∑ sign ∈ lowSigns L S p c r, (cellF sign).card +
        (irreducibleFactors (partitionPolynomial p)).card := by
  classical
  unfold temporarySurfaces
  calc
    (F₀ ∪ (lowSigns L S p c r).biUnion cellF ∪
        irreducibleFactors (partitionPolynomial p)).card ≤
        (F₀ ∪ (lowSigns L S p c r).biUnion cellF).card +
          (irreducibleFactors (partitionPolynomial p)).card :=
      Finset.card_union_le _ _
    _ ≤ F₀.card + ((lowSigns L S p c r).biUnion cellF).card +
          (irreducibleFactors (partitionPolynomial p)).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ F₀.card +
          ∑ sign ∈ lowSigns L S p c r, (cellF sign).card +
          (irreducibleFactors (partitionPolynomial p)).card := by
      gcongr
      exact Finset.card_biUnion_le

end TemporarySurfaces

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/IncidenceArithmetic.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Real-power arithmetic for the strong incidence induction
-/

namespace IncidenceArithmetic

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionRemainders
open Erdos95.PartitionBookkeeping
open Erdos95.RpowBookkeeping Erdos95.GuthParameters

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

theorem rpow_half_sq {M : ℕ} (hM : 0 < M) :
    ((M : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (M : ℝ) := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hMR.le]
  norm_num

theorem richness_le_two_mul_rpow_half {M r : ℕ} (hM : 0 < M)
    (hrange : r ^ 2 ≤ 4 * M) :
    (r : ℝ) ≤ 2 * (M : ℝ) ^ ((1 : ℝ) / 2) := by
  have hrangeR : (r : ℝ) ^ 2 ≤ 4 * (M : ℝ) := by
    exact_mod_cast hrange
  have hsqrt := rpow_half_sq hM
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hsnonneg : 0 ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  nlinarith

theorem rpow_half_mul_self {M : ℕ} (hM : 0 < M) :
    (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) =
      (M : ℝ) ^ ((3 : ℝ) / 2) := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  calc
    (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) =
        (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ (1 : ℝ) := by simp
    _ = (M : ℝ) ^ ((1 : ℝ) / 2 + 1) :=
      (Real.rpow_add hMR ((1 : ℝ) / 2) 1).symm
    _ = (M : ℝ) ^ ((3 : ℝ) / 2) := by congr 1 <;> ring

theorem rpow_three_halves_le_with_eta {M : ℕ} (hM : 0 < M)
    {η : ℝ} (hη : 0 ≤ η) :
    (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (M : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  exact Real.rpow_le_rpow_of_exponent_le hMone (by linarith)

/-- The chosen partition parameters make the total `p`-moment of all low
good cell line counts at most one sixteenth of the root moment. -/
theorem sixteen_mul_sum_low_cell_rpow_le
    {η : ℝ} (hη : 0 < η) (par : Parameters η)
    (L : Finset LineIndex) (S : Finset Space)
    (pCuts : Fin par.J → Poly3) (r : ℕ)
    (hdeg : (partitionPolynomial pCuts).totalDegree ≤ wallDegree par.k) :
    16 * (∑ sign ∈ lowSigns L S pCuts par.c r,
      ((cellLines L S pCuts sign).card : ℝ) ^
        ((3 : ℝ) / 2 + η)) ≤
      (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  classical
  let T := lowSigns L S pCuts par.c r
  let a : (Fin par.J → Bool) → ℕ := fun sign ↦
    (cellLines L S pCuts sign).card
  have hetaExp : (3 : ℝ) / 2 + η - 1 = (1 : ℝ) / 2 + η := by ring
  have hp : 1 ≤ (3 : ℝ) / 2 + η := by linarith
  have hpoint : ∀ sign ∈ T, par.c * a sign ≤ L.card := by
    intro sign hsign
    have hgood := (mem_lowSigns_iff.mp hsign).1
    have hnotbad := mem_goodSigns_iff.mp hgood
    have hlt : par.c * (cellLines L S pCuts sign).card < L.card := by
      exact Nat.lt_of_not_ge (fun h ↦ hnotbad (mem_badSigns_iff.mpr h))
    exact hlt.le
  have hsum : ∑ sign ∈ T, a sign ≤ crossingBudget par.k * L.card := by
    calc
      ∑ sign ∈ T, a sign ≤
          ∑ sign : Fin par.J → Bool,
            (cellLines L S pCuts sign).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (show T ⊆ (Finset.univ : Finset (Fin par.J → Bool)) by
            exact fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ ↦ Nat.zero_le _)
      _ ≤ L.card * ((partitionPolynomial pCuts).totalDegree + 1) :=
        sum_card_cellLines_le L S pCuts
      _ ≤ L.card * crossingBudget par.k := by
        unfold crossingBudget
        gcongr
      _ = crossingBudget par.k * L.card := by ring
  have hmoment := sum_natCast_rpow_le_of_mul_le T a L.card par.c
    (crossingBudget par.k) ((3 : ℝ) / 2 + η) hp par.c_pos hpoint hsum
  have hcR : 0 < (par.c : ℝ) := by exact_mod_cast par.c_pos
  have hrewrite :
      (((L.card : ℝ) / (par.c : ℝ)) ^ ((1 : ℝ) / 2 + η)) *
          ((crossingBudget par.k * L.card : ℕ) : ℝ) =
        (((1 : ℝ) / (par.c : ℝ)) ^ ((1 : ℝ) / 2 + η) *
          (crossingBudget par.k : ℝ)) *
          (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
    by_cases hL : L.card = 0
    · have hexp : (3 : ℝ) / 2 + η ≠ 0 := by linarith
      simp [hL, Real.zero_rpow hexp]
    · have hLpos : 0 < L.card := Nat.pos_of_ne_zero hL
      have hLR : 0 < (L.card : ℝ) := by
        exact_mod_cast hLpos
      have hpow :
          (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (L.card : ℝ) =
            (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
        calc
          (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (L.card : ℝ) =
              (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
                (L.card : ℝ) ^ (1 : ℝ) := by simp
          _ = (L.card : ℝ) ^ ((1 : ℝ) / 2 + η + 1) :=
            (Real.rpow_add hLR ((1 : ℝ) / 2 + η) 1).symm
          _ = (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
            congr 1 <;> ring
      rw [Real.div_rpow hLR.le hcR.le]
      rw [Real.div_rpow (by positivity) hcR.le]
      simp only [Real.one_rpow]
      push_cast
      rw [← hpow]
      ring
  rw [hetaExp] at hmoment
  calc
    16 * (∑ sign ∈ T, ((a sign : ℕ) : ℝ) ^
        ((3 : ℝ) / 2 + η)) ≤
        16 * ((((L.card : ℝ) / (par.c : ℝ)) ^
          ((1 : ℝ) / 2 + η)) *
          ((crossingBudget par.k * L.card : ℕ) : ℝ)) := by gcongr
    _ = 16 * ((((1 : ℝ) / (par.c : ℝ)) ^
          ((1 : ℝ) / 2 + η) * (crossingBudget par.k : ℝ)) *
          (L.card : ℝ) ^ ((3 : ℝ) / 2 + η)) := by rw [hrewrite]
    _ ≤ 1 * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
      have hnonneg :
          0 ≤ (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) :=
        Real.rpow_nonneg (by positivity) _
      have hmul := mul_le_mul_of_nonneg_right par.contraction hnonneg
      simpa only [mul_assoc] using hmul
    _ = (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := one_mul _

end IncidenceArithmetic

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/GuthInduction.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The strong low-degree incidence induction

This file closes the finite induction underlying Guth's rich-point theorem.
The induction is organized around an admissible surface collection whose
residual rich-point set has minimum cardinality.
-/

namespace GuthInduction

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionBookkeeping Erdos95.PartitionStep
open Erdos95.PartitionRemainders Erdos95.RemainderBounds
open Erdos95.RichPointCombinatorics Erdos95.SurfacePruning
open Erdos95.SurfaceCollections
open Erdos95.SurfaceFactors Erdos95.GuthStructure
open Erdos95.GuthParameters Erdos95.ScaleBounds
open Erdos95.PruneAdmissible Erdos95.TemporarySurfaces
open Erdos95.IncidenceArithmetic

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem residual_eq_of_minimal_admissible
    {η : ℝ} {D : ℕ} {L : Finset LineIndex} {r : ℕ}
    {F G : Finset Poly3}
    (hmin : ∀ H : Finset Poly3, Admissible η D L H →
      (residualRichPoints L F r).card ≤
        (residualRichPoints L H r).card)
    (hG : Admissible η D L G) (hFG : F ⊆ G) :
    residualRichPoints L G r = residualRichPoints L F r := by
  apply Finset.eq_of_subset_of_card_le
  · exact residualRichPoints_antitone_surfaces L hFG r
  · exact hmin G hG

theorem card_le_five_of_subset_union
    {α : Type*} [DecidableEq α]
    {S A B C D E : Finset α}
    (h : S ⊆ A ∪ B ∪ C ∪ D ∪ E) :
    S.card ≤ A.card + B.card + C.card + D.card + E.card := by
  calc
    S.card ≤ (A ∪ B ∪ C ∪ D ∪ E).card := Finset.card_le_card h
    _ ≤ (A ∪ B ∪ C ∪ D).card + E.card := Finset.card_union_le _ _
    _ ≤ (A ∪ B ∪ C).card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (A ∪ B).card + C.card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ A.card + B.card + C.card + D.card + E.card := by
      gcongr
      exact Finset.card_union_le _ _

theorem ceil_rpow_le_twice {M : ℕ} (hM : 0 < M) {a : ℝ}
    (ha : 0 ≤ a) :
    (⌈(M : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (M : ℝ) ^ a := by
  have hpowone : 1 ≤ (M : ℝ) ^ a := by
    exact Real.one_le_rpow (by exact_mod_cast hM) ha
  have hceil : (⌈(M : ℝ) ^ a⌉₊ : ℝ) < (M : ℝ) ^ a + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  linarith

theorem one_le_natCast_rpow {M : ℕ} (hM : 0 < M) {a : ℝ}
    (ha : 0 ≤ a) :
    1 ≤ (M : ℝ) ^ a := by
  exact Real.one_le_rpow (by exact_mod_cast hM) ha

theorem high_remainder_real_bound
    {η : ℝ} (hη : 0 ≤ η)
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r W : ℕ)
    (hL : 0 < L.card) (hrange : r ^ 2 ≤ 4 * L.card)
    (hdeg : (partitionPolynomial p).totalDegree + 1 ≤ W) :
    ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
      4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hnat := root_pair_mul_card_highCellRichPoints_le_crossing
    L S p c r
  have hcast :
      ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
        ((2 * r * (L.card *
          ((partitionPolynomial p).totalDegree + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hr := richness_le_two_mul_rpow_half hL hrange
  have hdegR :
      (((partitionPolynomial p).totalDegree + 1 : ℕ) : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast hdeg
  have hthree := rpow_three_halves_le_with_eta hL hη
  calc
    ((r * (r - 1) * (highCellRichPoints L S p c r).card : ℕ) : ℝ) ≤
        ((2 * r * (L.card *
          ((partitionPolynomial p).totalDegree + 1)) : ℕ) : ℝ) := hcast
    _ = 2 * (r : ℝ) * (L.card : ℝ) *
        (((partitionPolynomial p).totalDegree + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ 2 * (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2)) *
        (L.card : ℝ) * (W : ℝ) := by gcongr
    _ = 4 * W * ((L.card : ℝ) ^ ((1 : ℝ) / 2) *
        (L.card : ℝ)) := by ring
    _ = 4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [rpow_half_mul_self hL]
    _ ≤ 4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem wall_remainder_real_bound
    {η : ℝ} (hη : 0 ≤ η)
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r D : ℕ)
    (hr : 2 ≤ r) (hL : 0 < L.card)
    (hrange : r ^ 2 ≤ 4 * L.card)
    (hp : ∀ j, p j ≠ 0)
    (hSrich : S ⊆ richPoints L r)
    (hdeg : (partitionPolynomial p).totalDegree ≤ D) :
    ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
      4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hnat := root_pair_mul_card_wallRemainder_le
    L S p r hr hp hSrich
  have hcast :
      ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
        ((2 * r * ((partitionPolynomial p).totalDegree * L.card) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hrroot := richness_le_two_mul_rpow_half hL hrange
  have hdegR : ((partitionPolynomial p).totalDegree : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdeg
  have hthree := rpow_three_halves_le_with_eta hL hη
  calc
    ((r * (r - 1) * (wallRemainder L S p r).card : ℕ) : ℝ) ≤
        ((2 * r * ((partitionPolynomial p).totalDegree * L.card) : ℕ) : ℝ) :=
      hcast
    _ = 2 * (r : ℝ) * (partitionPolynomial p).totalDegree *
        (L.card : ℝ) := by
      push_cast
      ring
    _ ≤ 2 * (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2)) *
        (D : ℝ) * (L.card : ℝ) := by gcongr
    _ = 4 * D * ((L.card : ℝ) ^ ((1 : ℝ) / 2) *
        (L.card : ℝ)) := by ring
    _ = 4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [rpow_half_mul_self hL]
    _ ≤ 4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem temporary_surface_count_bound
    {η : ℝ} (hηle : η ≤ (1 : ℝ) / 2)
    (D : ℕ) (L : Finset LineIndex) (hL : 0 < L.card)
    (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (F₀ : Finset Poly3)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : (F₀.card : ℝ) ≤
      2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η))
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ((cellF sign).card : ℝ) ≤
        2 * ((cellLines L S p sign).card : ℝ) ^
          ((1 : ℝ) / 2 - η))
    (hQ : partitionPolynomial p ≠ 0)
    (hQdeg : (partitionPolynomial p).totalDegree ≤ D) :
    ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
      (2 + 2 * (2 ^ J : ℕ) + D) *
        (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
  classical
  let T := lowSigns L S p c r
  let q : ℝ := (1 : ℝ) / 2 - η
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hcellcard : ∀ sign ∈ T,
      ((cellF sign).card : ℝ) ≤
        2 * (L.card : ℝ) ^ q := by
    intro sign hsign
    have hsub := cellLines_subset L S p sign
    have hcard : (cellLines L S p sign).card ≤ L.card :=
      Finset.card_le_card hsub
    have hcardR : ((cellLines L S p sign).card : ℝ) ≤
        (L.card : ℝ) := by exact_mod_cast hcard
    have hpow := Real.rpow_le_rpow (by positivity) hcardR hq
    exact (hcell sign hsign).trans (by
      dsimp [q] at hpow ⊢
      gcongr)
  have hTcard : T.card ≤ 2 ^ J := by
    calc
      T.card ≤ (Finset.univ : Finset (Fin J → Bool)).card :=
        Finset.card_le_card (fun _ _ ↦ Finset.mem_univ _)
      _ = 2 ^ J := by simp
  have hsum :
      (((∑ sign ∈ T, (cellF sign).card : ℕ)) : ℝ) ≤
        2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ q := by
    calc
      (((∑ sign ∈ T, (cellF sign).card : ℕ)) : ℝ) =
          ∑ sign ∈ T, ((cellF sign).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _sign ∈ T, 2 * (L.card : ℝ) ^ q := by
        exact Finset.sum_le_sum fun sign hsign ↦ hcellcard sign hsign
      _ = (T.card : ℝ) * (2 * (L.card : ℝ) ^ q) := by simp
      _ ≤ ((2 ^ J : ℕ) : ℝ) * (2 * (L.card : ℝ) ^ q) := by
        gcongr
      _ = 2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ q := by ring
  have hone : 1 ≤ (L.card : ℝ) ^ q := by
    exact one_le_natCast_rpow hL hq
  have hfacNat : (irreducibleFactors (partitionPolynomial p)).card ≤ D :=
    (card_irreducibleFactors_le_totalDegree hQ).trans hQdeg
  have hfac :
      ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤
        D * (L.card : ℝ) ^ q := by
    have hfacD :
        ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hfacNat
    calc
      ((irreducibleFactors (partitionPolynomial p)).card : ℝ) ≤ (D : ℝ) := hfacD
      _ ≤ D * (L.card : ℝ) ^ q := by
        have hD : 0 ≤ (D : ℝ) := by positivity
        nlinarith
  have htempNat := card_temporary_le F₀ L S p c r cellF
  have htemp :
      ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
        (F₀.card : ℝ) +
          ((∑ sign ∈ T, (cellF sign).card : ℕ) : ℝ) +
          ((irreducibleFactors (partitionPolynomial p)).card : ℝ) := by
    exact_mod_cast htempNat
  dsimp [q] at hsum hfac hone ⊢
  calc
    ((temporarySurfaces F₀ L S p c r cellF).card : ℝ) ≤
        (F₀.card : ℝ) +
          ((∑ sign ∈ T, (cellF sign).card : ℕ) : ℝ) +
          ((irreducibleFactors (partitionPolynomial p)).card : ℝ) := htemp
    _ ≤ 2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) +
        2 * (2 ^ J : ℕ) * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) +
        D * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by gcongr
    _ = (2 + 2 * (2 ^ J : ℕ) + D) *
        (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by ring

theorem small_surface_remainder_real_bound
    {η C : ℝ} (hη : 0 < η)
    (hC : 0 ≤ C)
    (L : Finset LineIndex) (hL : 0 < L.card)
    (F : Finset Poly3) (r : ℕ) (hr : 2 ≤ r)
    (hF : (F.card : ℝ) ≤
      C * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) :
    ((r * (r - 1) *
        (surfaceRichPoints L
          (smallSurfaces L F
            ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊)
          (reducedRichness r)).card : ℕ) : ℝ) ≤
      32 * C * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
  have ha : 0 ≤ (1 : ℝ) / 2 + η := by linarith
  have hceil := ceil_rpow_le_twice hL ha
  have hLR : 0 < (L.card : ℝ) := by exact_mod_cast hL
  have hAsq : (A : ℝ) ^ 2 ≤
      4 * (L.card : ℝ) ^ (1 + 2 * η) := by
    calc
      (A : ℝ) ^ 2 ≤
          (2 * (L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
        gcongr
      _ = 4 * (((L.card : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2) := by ring
      _ = 4 * (L.card : ℝ) ^ (1 + 2 * η) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hLR.le]
        congr 2
        ring
  have hnat := root_pair_mul_card_small_surfaceRichPoints_le L F A r hr
  have hcast :
      ((r * (r - 1) *
          (surfaceRichPoints L (smallSurfaces L F A)
            (reducedRichness r)).card : ℕ) : ℝ) ≤
        ((8 * (F.card * A ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpow :
      (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) *
          (L.card : ℝ) ^ (1 + 2 * η) =
        (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
    rw [← Real.rpow_add hLR]
    congr 1
    ring
  change ((r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (reducedRichness r)).card : ℕ) : ℝ) ≤ _
  calc
    ((r * (r - 1) *
        (surfaceRichPoints L (smallSurfaces L F A)
          (reducedRichness r)).card : ℕ) : ℝ) ≤
        ((8 * (F.card * A ^ 2) : ℕ) : ℝ) := hcast
    _ = 8 * (F.card : ℝ) * (A : ℝ) ^ 2 := by
      push_cast
      ring
    _ ≤ 8 *
        (C * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)) *
        (4 * (L.card : ℝ) ^ (1 + 2 * η)) := by
      gcongr
    _ = 32 * C * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
      rw [← hpow]
      ring

theorem sixteen_mul_low_remainder_le
    {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (par : Parameters η)
    (L : Finset LineIndex) (S : Finset Space)
    (p : Fin par.J → Poly3) (r : ℕ)
    (hdeg : (partitionPolynomial p).totalDegree ≤ wallDegree par.k)
    (cellF : (Fin par.J → Bool) → Finset Poly3)
    (hcell : ∀ sign ∈ lowSigns L S p par.c r,
      ((r * (r - 1) *
          (residualRichPoints (cellLines L S p sign)
            (cellF sign) r).card : ℕ) : ℝ) ≤
        K * ((cellLines L S p sign).card : ℝ) ^
          ((3 : ℝ) / 2 + η)) :
    16 * ((r * (r - 1) *
        (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
      K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  classical
  let T := lowSigns L S p par.c r
  have hcard := card_lowResidualPoints_le_sum L S p par.c r cellF
  have hnat :
      r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card ≤
        ∑ sign ∈ T,
          r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card := by
    calc
      r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card ≤
          r * (r - 1) *
            (∑ sign ∈ T,
              (residualRichPoints (cellLines L S p sign)
                (cellF sign) r).card) := by gcongr
      _ = ∑ sign ∈ T,
          r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card := by
        rw [Finset.mul_sum]
  have hcast :
      ((r * (r - 1) *
          (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
        ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsum :
      ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) ≤
        K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η) := by
    calc
      ∑ sign ∈ T,
          ((r * (r - 1) *
            (residualRichPoints (cellLines L S p sign)
              (cellF sign) r).card : ℕ) : ℝ) ≤
          ∑ sign ∈ T,
            K * ((cellLines L S p sign).card : ℝ) ^
              ((3 : ℝ) / 2 + η) := by
        exact Finset.sum_le_sum fun sign hsign ↦ hcell sign hsign
      _ = K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η) := by rw [Finset.mul_sum]
  have hmoment := sixteen_mul_sum_low_cell_rpow_le
    hη par L S p r hdeg
  calc
    16 * ((r * (r - 1) *
        (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
        16 * (K * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η)) := by
      gcongr
      exact hcast.trans hsum
    _ = K * (16 * ∑ sign ∈ T,
          ((cellLines L S p sign).card : ℝ) ^
            ((3 : ℝ) / 2 + η)) := by ring
    _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by gcongr

theorem weighted_card_le_twice_four_of_half
    {α : Type*} [DecidableEq α]
    (w : ℕ) {S A B C D E : Finset α}
    (hcover : S ⊆ A ∪ B ∪ C ∪ D ∪ E)
    (hhalf : 2 * A.card ≤ S.card) :
    ((w * S.card : ℕ) : ℝ) ≤
      2 * (((w * B.card : ℕ) : ℝ) +
        ((w * C.card : ℕ) : ℝ) +
        ((w * D.card : ℕ) : ℝ) +
        ((w * E.card : ℕ) : ℝ)) := by
  have hcard := card_le_five_of_subset_union hcover
  have htotalNat :
      w * S.card ≤
        w * A.card + w * B.card + w * C.card + w * D.card + w * E.card := by
    calc
      w * S.card ≤
          w * (A.card + B.card + C.card + D.card + E.card) := by gcongr
      _ = w * A.card + w * B.card + w * C.card + w * D.card +
          w * E.card := by ring
  have htotal :
      ((w * S.card : ℕ) : ℝ) ≤
        ((w * A.card : ℕ) : ℝ) + ((w * B.card : ℕ) : ℝ) +
        ((w * C.card : ℕ) : ℝ) + ((w * D.card : ℕ) : ℝ) +
        ((w * E.card : ℕ) : ℝ) := by exact_mod_cast htotalNat
  have hhalfNat : 2 * (w * A.card) ≤ w * S.card := by
    calc
      2 * (w * A.card) = w * (2 * A.card) := by ring
      _ ≤ w * S.card := by gcongr
  have hhalfR :
      2 * ((w * A.card : ℕ) : ℝ) ≤ ((w * S.card : ℕ) : ℝ) := by
    exact_mod_cast hhalfNat
  nlinarith [show 0 ≤ ((w * A.card : ℕ) : ℝ) by positivity]

/-- Guth's strong rich-point theorem in the finite, denominator-free form
needed for the Elekes--Sharir line family. -/
theorem exists_certificate_constant
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ (1 : ℝ) / 4)
    (par : Parameters η) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L : Finset LineIndex) (r : ℕ), 2 ≤ r →
        r ^ 2 ≤ 4 * L.card →
        Nonempty (Certificate η (wallDegree par.k) K L r) := by
  classical
  let D : ℕ := wallDegree par.k
  let W : ℕ := crossingBudget par.k
  let R : ℕ := 2 ^ par.J
  let Csurf : ℝ := 2 + 2 * R + D
  let B : ℝ := 4 * W + 4 * D + 32 * Csurf
  obtain ⟨N, hNpos, hNscale⟩ :=
    exists_pos_nat_forall_le_rpow (show 0 < 2 * η by positivity)
      (4 * (commonLineConstant D : ℝ) + 1)
  let K : ℝ := 4 * (B + (N : ℝ) ^ 2 + 1)
  have hCsurf : 0 ≤ Csurf := by
    dsimp [Csurf]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro L
  induction L using Finset.strongInduction with
  | H L ih =>
      intro r hr hrange
      have hL : 0 < L.card := by
        have hr2 : 0 < r ^ 2 := by positivity
        omega
      by_cases hsmall : L.card < N
      · obtain ⟨hirr, hnorm, hdegree, hmany, hcount⟩ :=
          admissible_empty η D L
        refine ⟨
          { surfaces := ∅
            irreducible := hirr
            normalized := hnorm
            degree_le := hdegree
            many_lines := hmany
            surface_count := hcount
            residual_bound := ?_ }⟩
        have hres : residualRichPoints L ∅ r ⊆ richPoints L r := by
          intro x hx
          exact (mem_residualRichPoints_iff.mp hx).1
        have hnat :
            r * (r - 1) * (residualRichPoints L ∅ r).card ≤
              L.card ^ 2 := by
          calc
            r * (r - 1) * (residualRichPoints L ∅ r).card ≤
                r * (r - 1) * (richPoints L r).card := by
              gcongr
            _ ≤ L.card ^ 2 := richness_mul_pred_mul_card_le_sq L r
        have hcast :
            ((r * (r - 1) * (residualRichPoints L ∅ r).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := by exact_mod_cast hnat
        have hLN : (L.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
          gcongr
        have hNK : (N : ℝ) ^ 2 ≤ K := by
          dsimp [K]
          nlinarith
        have hp : 0 ≤ (3 : ℝ) / 2 + η := by linarith
        have hone := one_le_natCast_rpow hL hp
        calc
          ((r * (r - 1) * (residualRichPoints L ∅ r).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := hcast
          _ ≤ (N : ℝ) ^ 2 := hLN
          _ ≤ K := hNK
          _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
            nlinarith [hK.le]
      · have hNL : N ≤ L.card := Nat.le_of_not_gt hsmall
        have hscaleWeak := hNscale L.card hNL
        have hscale :
            4 * (commonLineConstant D : ℝ) <
              (L.card : ℝ) ^ (2 * η) := by linarith
        obtain ⟨F₀, hF₀, hmin⟩ :=
          exists_minimal_admissible η D L r
        let S : Finset Space := residualRichPoints L F₀ r
        obtain ⟨p, hp, hcells⟩ :=
          exists_partition_cuts_of_finiteLinearBisection
            Erdos95.StoneTukey.finiteLinearBisection S par.J par.k par.fit
        have hpne : ∀ j, p j ≠ 0 := fun j ↦ (hp j).1
        have hQ : partitionPolynomial p ≠ 0 :=
          partitionPolynomial_ne_zero p hpne
        have hQdeg : (partitionPolynomial p).totalDegree ≤ D := by
          dsimp [D]
          exact totalDegree_partitionPolynomial_le_sum_three_mul p par.k
            (fun j ↦ (hp j).2)
        have hQcross : (partitionPolynomial p).totalDegree + 1 ≤ W := by
          dsimp [W, crossingBudget]
          omega
        have hbadScale :
            2 * (par.c * ((partitionPolynomial p).totalDegree + 1)) ≤
              2 ^ par.J := by
          exact (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left par.c hQcross)).trans par.bad_half
        have hbad :
            2 * (badCellPoints L S p par.c).card ≤ S.card :=
          two_mul_card_badCellPoints_le L S p par.c (2 ^ par.J)
            hL (by positivity) hbadScale hcells
        have hproper : ∀ sign ∈ lowSigns L S p par.c r,
            cellLines L S p sign ⊂ L := by
          intro sign hsign
          have hgood := (mem_lowSigns_iff.mp hsign).1
          have hnotbad := mem_goodSigns_iff.mp hgood
          have hlt :
              par.c * (cellLines L S p sign).card < L.card :=
            Nat.lt_of_not_ge (fun hge ↦
              hnotbad (mem_badSigns_iff.mpr hge))
          have hcardlt : (cellLines L S p sign).card < L.card := by
            have hcOne : 1 ≤ par.c := par.c_pos
            have hmle : (cellLines L S p sign).card ≤
                par.c * (cellLines L S p sign).card := by
              nlinarith
            omega
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨cellLines_subset L S p sign, ?_⟩
          intro heq
          have := congrArg Finset.card heq
          omega
        have hchildCert : ∀ sign
            (hsign : sign ∈ lowSigns L S p par.c r),
            Certificate η D K (cellLines L S p sign) r := by
          intro sign hsign
          exact Classical.choice <| ih (cellLines L S p sign)
            (hproper sign hsign) r hr (mem_lowSigns_iff.mp hsign).2
        let cellF : (Fin par.J → Bool) → Finset Poly3 := fun sign ↦
          if hsign : sign ∈ lowSigns L S p par.c r then
            (hchildCert sign hsign).surfaces
          else ∅
        have hcellEq : ∀ sign
            (hsign : sign ∈ lowSigns L S p par.c r),
            cellF sign = (hchildCert sign hsign).surfaces := by
          intro sign hsign
          simp [cellF, hsign]
        have hcellIrr : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, Irreducible Q := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).irreducible
        have hcellNorm : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, normalize Q = Q := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).normalized
        have hcellDegree : ∀ sign ∈ lowSigns L S p par.c r,
            ∀ Q ∈ cellF sign, Q.totalDegree ≤ D := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).degree_le
        have hcellCount : ∀ sign ∈ lowSigns L S p par.c r,
            ((cellF sign).card : ℝ) ≤
              2 * ((cellLines L S p sign).card : ℝ) ^
                ((1 : ℝ) / 2 - η) := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).surface_count
        have hcellResidual : ∀ sign ∈ lowSigns L S p par.c r,
            ((r * (r - 1) *
                (residualRichPoints (cellLines L S p sign)
                  (cellF sign) r).card : ℕ) : ℝ) ≤
              K * ((cellLines L S p sign).card : ℝ) ^
                ((3 : ℝ) / 2 + η) := by
          intro sign hsign
          rw [hcellEq sign hsign]
          exact (hchildCert sign hsign).residual_bound
        let Ftemp := temporarySurfaces F₀ L S p par.c r cellF
        have htempIrr : ∀ Q ∈ Ftemp, Irreducible Q := by
          exact temporary_irreducible F₀ L S p par.c r cellF
            hF₀.1 hcellIrr
        have htempNorm : ∀ Q ∈ Ftemp, normalize Q = Q := by
          exact temporary_normalized F₀ L S p par.c r cellF
            hF₀.2.1 hcellNorm
        have htempDegree : ∀ Q ∈ Ftemp, Q.totalDegree ≤ D := by
          exact temporary_degree_le F₀ L S p par.c r D cellF
            hQ hQdeg hF₀.2.2.1 hcellDegree
        let A : ℕ := ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊
        let G : Finset Poly3 := largeSurfaces L Ftemp A
        have hG : Admissible η D L G := by
          change Admissible η D L
            (largeSurfaces L Ftemp
              ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊)
          exact admissible_largeSurfaces hη hηle D L hL Ftemp
            htempIrr htempNorm htempDegree hscale
        have hF₀G : F₀ ⊆ G := by
          intro Q hQF
          apply mem_largeSurfaces_iff.mpr
          refine ⟨base_subset_temporary F₀ L S p par.c r cellF hQF, ?_⟩
          change ⌈(L.card : ℝ) ^ ((1 : ℝ) / 2 + η)⌉₊ ≤
            (surfaceLines L Q).card
          exact Nat.ceil_le.mpr (hF₀.2.2.2.1 Q hQF)
        have hresEq : residualRichPoints L G r = S := by
          change residualRichPoints L G r = residualRichPoints L F₀ r
          exact residual_eq_of_minimal_admissible hmin hG hF₀G
        have hSrich : S ⊆ richPoints L r := by
          intro x hx
          exact (mem_residualRichPoints_iff.mp hx).1
        have hAvoid : ∀ x ∈ S,
            x ∉ surfaceRichPoints L G (reducedRichness r) := by
          intro x hx
          have hxG : x ∈ residualRichPoints L G r := by
            rw [hresEq]
            exact hx
          exact (mem_residualRichPoints_iff.mp hxG).2
        have hcover : S ⊆
            badCellPoints L S p par.c ∪
            lowResidualPoints L S p par.c r cellF ∪
            highCellRichPoints L S p par.c r ∪
            wallRemainder L S p r ∪
            surfaceRichPoints L (smallSurfaces L Ftemp A)
              (reducedRichness r) := by
          exact subset_partition_remainders hr F₀ cellF hSrich hAvoid
        have htempCount : (Ftemp.card : ℝ) ≤
            Csurf * (L.card : ℝ) ^ ((1 : ℝ) / 2 - η) := by
          change (Ftemp.card : ℝ) ≤
            (2 + 2 * R + D) *
              (L.card : ℝ) ^ ((1 : ℝ) / 2 - η)
          have hetaHalf : η ≤ (1 : ℝ) / 2 := hηle.trans (by norm_num)
          exact temporary_surface_count_bound hetaHalf D L hL S p par.c r
            F₀ cellF hF₀.2.2.2.2 hcellCount hQ hQdeg
        have hlow16 := sixteen_mul_low_remainder_le hη hK.le par
          L S p r hQdeg cellF hcellResidual
        have hhigh := high_remainder_real_bound hη.le L S p par.c r W
          hL hrange hQcross
        have hwall := wall_remainder_real_bound hη.le L S p r D hr hL
          hrange hpne hSrich hQdeg
        have hsmallSurf := small_surface_remainder_real_bound hη hCsurf
          L hL Ftemp r hr htempCount
        have hdecomp := weighted_card_le_twice_four_of_half
          (r * (r - 1)) hcover hbad
        have hLp : 0 ≤ (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) :=
          Real.rpow_nonneg (by positivity) _
        have hlow :
            ((r * (r - 1) *
                (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) ≤
              (K / 16) * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          nlinarith
        have hrest :
            ((r * (r - 1) *
                (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (highCellRichPoints L S p par.c r).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (wallRemainder L S p r).card : ℕ) : ℝ) +
              ((r * (r - 1) *
                (surfaceRichPoints L (smallSurfaces L Ftemp A)
                  (reducedRichness r)).card : ℕ) : ℝ) ≤
              (K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          calc
            _ ≤ (K / 16) * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                4 * W * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                4 * D * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) +
                32 * Csurf * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              gcongr
            _ = (K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              dsimp [B]
              ring
        have hcoef : 2 * (K / 16 + B) ≤ K := by
          dsimp [K]
          nlinarith [hB, show 0 ≤ (N : ℝ) ^ 2 by positivity]
        have hfinal :
            ((r * (r - 1) * S.card : ℕ) : ℝ) ≤
              K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
          calc
            ((r * (r - 1) * S.card : ℕ) : ℝ) ≤
                2 * (((r * (r - 1) *
                    (lowResidualPoints L S p par.c r cellF).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (highCellRichPoints L S p par.c r).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (wallRemainder L S p r).card : ℕ) : ℝ) +
                  ((r * (r - 1) *
                    (surfaceRichPoints L (smallSurfaces L Ftemp A)
                      (reducedRichness r)).card : ℕ) : ℝ)) := hdecomp
            _ ≤ 2 * ((K / 16 + B) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η)) := by gcongr
            _ = (2 * (K / 16 + B)) *
                (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by ring
            _ ≤ K * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
              gcongr
        refine ⟨
          { surfaces := F₀
            irreducible := hF₀.1
            normalized := hF₀.2.1
            degree_le := hF₀.2.2.1
            many_lines := hF₀.2.2.2.1
            surface_count := hF₀.2.2.2.2
            residual_bound := ?_ }⟩
        change ((r * (r - 1) * S.card : ℕ) : ℝ) ≤ _
        exact hfinal

end GuthInduction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95/SpecialRichPoints.lean` -/

section
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Rich points of the Elekes--Sharir family

The strong incidence certificate has no exceptional surface when it is
applied to the full `P × P` family at a sufficiently large scale: the
Elekes--Sharir non-clustering theorem gives only `O_D(|P|)` lines on a
degree-`D` irreducible surface, whereas a certificate surface contains at
least `|P|^(1+2η)` lines.
-/

namespace SpecialRichPoints

open Erdos95.ES Erdos95.LineFamilies Erdos95.GuthStructure
open Erdos95.GuthParameters Erdos95.GuthInduction
open Erdos95.ScaleBounds Erdos95.SpecialFamily
open Erdos95.SurfaceFactors Erdos95.RichPointCombinatorics

abbrev LineIndex := PlanePoint × PlanePoint

theorem full_family_rich_point_bound :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
      ∀ (P : Finset PlanePoint) (k : ℕ), 2 ≤ k →
        ((richPoints (P.product P) k).card : ℝ) ≤
          A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2 := by
  intro δ hδ
  let η : ℝ := min (δ / 4) ((1 : ℝ) / 8)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (by norm_num)
  have hηle : η ≤ (1 : ℝ) / 4 := by
    dsimp [η]
    exact (min_le_right _ _).trans (by norm_num)
  have htwoη : 2 * η ≤ δ := by
    have hle : η ≤ δ / 4 := min_le_left _ _
    linarith
  let par : Parameters η := Classical.choice (exists_parameters hη hηle)
  obtain ⟨K, hK, hcert⟩ := exists_certificate_constant hη hηle par
  let D : ℕ := wallDegree par.k
  let Cline : ℕ := surfaceLineConstant D
  obtain ⟨N, hNpos, hNscale⟩ :=
    exists_pos_nat_forall_le_rpow (show 0 < 2 * η by positivity)
      (2 * (Cline : ℝ) + 1)
  let C₀ : ℝ := K + (N : ℝ) ^ 4 + 1
  let A : ℝ := 2 * C₀
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro P k hk
  by_cases hkn : k ≤ P.card
  · have hP : 0 < P.card := by omega
    let L : Finset LineIndex := P.product P
    have hLcard : L.card = P.card ^ 2 := by
      simp [L, pow_two]
    have hrange : k ^ 2 ≤ 4 * L.card := by
      rw [hLcard]
      nlinarith
    have hPone : 1 ≤ (P.card : ℝ) := by exact_mod_cast hP
    have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast hP
    have hexp : 0 ≤ 3 + δ := by linarith
    have hpowone : 1 ≤ (P.card : ℝ) ^ (3 + δ) :=
      Real.one_le_rpow hPone hexp
    have hpair :
        ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
          C₀ * (P.card : ℝ) ^ (3 + δ) := by
      by_cases hlarge : N ≤ P.card
      · have hscaleWeak := hNscale P.card hlarge
        have hscale :
            2 * (Cline : ℝ) < (P.card : ℝ) ^ (2 * η) := by
          linarith
        let cert : Certificate η D K L k :=
          Classical.choice (hcert L k hk hrange)
        have hsurfaces : cert.surfaces = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨Q, hQ⟩
          have hlower := cert.many_lines Q hQ
          have hupperNat : (surfaceLines L Q).card ≤
              Cline * (P.card + 1) := by
            exact card_surfaceLines_le_degree
              (show L ⊆ P.product P by simp [L])
              (cert.irreducible Q hQ) (cert.degree_le Q hQ)
          have hupper : ((surfaceLines L Q).card : ℝ) ≤
              Cline * (P.card + 1) := by exact_mod_cast hupperNat
          have hLpow :
              (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) =
                (P.card : ℝ) ^ (1 + 2 * η) := by
            rw [hLcard]
            push_cast
            rw [show (P.card : ℝ) ^ (2 : ℕ) =
              (P.card : ℝ) ^ (2 : ℝ) by
                exact (Real.rpow_natCast _ 2).symm]
            rw [← Real.rpow_mul hPpos.le]
            congr 1
            ring
          have hgrow :
              (Cline : ℝ) * (P.card + 1) <
                (P.card : ℝ) ^ (1 + 2 * η) := by
            have hmul := mul_lt_mul_of_pos_left hscale hPpos
            have hsum : (P.card : ℝ) + 1 ≤ 2 * P.card := by
              exact_mod_cast (show P.card + 1 ≤ 2 * P.card by omega)
            have hleft :
                (Cline : ℝ) * ((P.card : ℝ) + 1) ≤
                  (P.card : ℝ) * (2 * Cline) := by
              nlinarith [show 0 ≤ (Cline : ℝ) by positivity]
            have hpow :
                (P.card : ℝ) ^ (1 + 2 * η) =
                  (P.card : ℝ) * (P.card : ℝ) ^ (2 * η) := by
              rw [Real.rpow_add hPpos]
              simp
            rw [hpow]
            exact hleft.trans_lt (by simpa [mul_comm, mul_left_comm,
              mul_assoc] using hmul)
          rw [hLpow] at hlower
          linarith
        have hres : residualRichPoints L cert.surfaces k =
            richPoints L k := by
          rw [hsurfaces]
          simp [residualRichPoints, surfaceRichPoints]
        have hcertBound := cert.residual_bound
        rw [hres] at hcertBound
        have hbasepow :
            (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) =
              (P.card : ℝ) ^ (3 + 2 * η) := by
          rw [hLcard]
          push_cast
          rw [show (P.card : ℝ) ^ (2 : ℕ) =
            (P.card : ℝ) ^ (2 : ℝ) by
              exact (Real.rpow_natCast _ 2).symm]
          rw [← Real.rpow_mul hPpos.le]
          congr 1
          ring
        rw [hbasepow] at hcertBound
        have hpowmono :
            (P.card : ℝ) ^ (3 + 2 * η) ≤
              (P.card : ℝ) ^ (3 + δ) :=
          Real.rpow_le_rpow_of_exponent_le hPone (by linarith)
        calc
          ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              K * (P.card : ℝ) ^ (3 + 2 * η) := hcertBound
          _ ≤ K * (P.card : ℝ) ^ (3 + δ) := by gcongr
          _ ≤ C₀ * (P.card : ℝ) ^ (3 + δ) := by
            gcongr
            dsimp [C₀]
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
      · have hsmall : P.card < N := Nat.lt_of_not_ge hlarge
        have hnat := richness_mul_pred_mul_card_le_sq L k
        have hcast :
            ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := by exact_mod_cast hnat
        have hLn : (L.card : ℝ) ^ 2 = (P.card : ℝ) ^ 4 := by
          rw [hLcard]
          push_cast
          ring
        have hnN : (P.card : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := by
          gcongr
        calc
          ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := hcast
          _ = (P.card : ℝ) ^ 4 := hLn
          _ ≤ (N : ℝ) ^ 4 := hnN
          _ ≤ (N : ℝ) ^ 4 * (P.card : ℝ) ^ (3 + δ) := by
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
          _ ≤ C₀ * (P.card : ℝ) ^ (3 + δ) := by
            gcongr
            dsimp [C₀]
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
    have hkpairNat : k ^ 2 ≤ 2 * (k * (k - 1)) := by
      calc
        k ^ 2 = k * k := by ring
        _ ≤ k * (2 * (k - 1)) := by gcongr <;> omega
        _ = 2 * (k * (k - 1)) := by ring
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hscaled :
        (k : ℝ) ^ 2 * ((richPoints L k).card : ℝ) ≤
          2 * C₀ * (P.card : ℝ) ^ (3 + δ) := by
      have hkpair : (k : ℝ) ^ 2 ≤
          2 * ((k * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hkpairNat
      have hcardnonneg : 0 ≤ ((richPoints L k).card : ℝ) := by positivity
      calc
        (k : ℝ) ^ 2 * ((richPoints L k).card : ℝ) ≤
            (2 * ((k * (k - 1) : ℕ) : ℝ)) *
              ((richPoints L k).card : ℝ) := by gcongr
        _ = 2 *
            ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ 2 * (C₀ * (P.card : ℝ) ^ (3 + δ)) := by gcongr
        _ = 2 * C₀ * (P.card : ℝ) ^ (3 + δ) := by ring
    change ((richPoints L k).card : ℝ) ≤ _
    dsimp [A]
    apply (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  · have hempty : richPoints (P.product P) k = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      have hkline := (mem_richPoints_iff.mp hx).2
      have hcap := card_linesThrough_le_points
        (P := P) (L := P.product P) (by rfl) x
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end SpecialRichPoints

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos95.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 95.
https://www.erdosproblems.com/forum/thread/95

Informal authors:
- Larry Guth
- Nets Hawk Katz

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos95.md
-/
/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 95

For a finite set `P` of points in the Euclidean plane, let `f_P u` be the
number of unordered pairs of distinct points of `P` at distance `u`.  Erdős
Problem 95 asks for an upper bound for the second moment of these
multiplicities.  Guth and Katz proved the stronger estimate

`∑ u, f_P(u)^2 ≪ |P|^3 log |P|`.

This file formalizes the consequence requested in the problem: for every
positive real `ε`, the second moment is at most a constant depending only on
`ε` times `|P|^(3+ε)`.
-/

open scoped BigOperators

/-- The Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance, regarded as a function of an unordered pair. -/
noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ dist p q, dist_comm⟩

@[simp]
theorem pairDistance_mk (p q : Point) : pairDistance s(p, q) = dist p q :=
  rfl

/-- The finset of unordered pairs of distinct points of `P`. -/
noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.offDiag.image Sym2.mk.uncurry

/-- The set of nonzero distances determined by `P`. -/
noncomputable def distances (P : Finset Point) : Finset ℝ :=
  (pointPairs P).image pairDistance

/-- The number of unordered pairs of points of `P` at distance `u`. -/
noncomputable def distanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((pointPairs P).filter fun e ↦ pairDistance e = u).card

/-- The second moment of the distance multiplicities of `P`. -/
noncomputable def distanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ distances P, distanceMultiplicity P u ^ 2

@[simp]
theorem card_pointPairs (P : Finset Point) :
    (pointPairs P).card = P.card.choose 2 := by
  classical
  exact Sym2.card_image_offDiag P

/-! ## Ordered segments and the factor of four -/

/-- The ordered pairs of distinct points of `P`. -/
noncomputable def orderedSegments (P : Finset Point) : Finset (Point × Point) :=
  P.offDiag

/-- The distance of an ordered segment. -/
noncomputable def orderedDistance (e : Point × Point) : ℝ :=
  dist e.1 e.2

/-- The number of ordered segments of `P` at distance `u`. -/
noncomputable def orderedDistanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((orderedSegments P).filter fun e ↦ orderedDistance e = u).card

/-- The ordered equal-distance energy.  This counts ordered pairs of ordered
segments of the same nonzero length. -/
noncomputable def orderedDistanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ (orderedSegments P).image orderedDistance,
    orderedDistanceMultiplicity P u ^ 2

/-- Ordered pairs of ordered nondegenerate segments having the same length.
This is the finite set denoted `Q(P)` in the Guth--Katz argument. -/
noncomputable def orderedDistanceQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) :=
  ((orderedSegments P).product (orderedSegments P)).filter fun q ↦
    orderedDistance q.1 = orderedDistance q.2

/-- The fiber-square definition of ordered distance energy is exactly the
cardinality of the equal-distance quadruple set. -/
theorem card_orderedDistanceQuadruples (P : Finset Point) :
    (orderedDistanceQuadruples P).card = orderedDistanceEnergy P := by
  classical
  let leftDistance : ((Point × Point) × (Point × Point)) → ℝ :=
    fun q ↦ orderedDistance q.1
  rw [Finset.card_eq_sum_card_image leftDistance (orderedDistanceQuadruples P)]
  have himage :
      (orderedDistanceQuadruples P).image leftDistance =
        (orderedSegments P).image orderedDistance := by
    ext u
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      unfold orderedDistanceQuadruples at hq
      rw [Finset.mem_filter] at hq
      have hqmem := Finset.mem_product.mp hq.1
      exact ⟨q.1, hqmem.1, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨(e, e), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, he⟩, rfl⟩, rfl⟩
  rw [himage]
  simp only [orderedDistanceEnergy, orderedDistanceMultiplicity]
  apply Finset.sum_congr rfl
  intro u hu
  have hfiber :
      (orderedDistanceQuadruples P).filter (fun q ↦ leftDistance q = u) =
        ((orderedSegments P).filter fun e ↦ orderedDistance e = u).product
        ((orderedSegments P).filter fun e ↦ orderedDistance e = u) := by
    ext q
    unfold orderedDistanceQuadruples leftDistance
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hqmem, heq⟩, hleft⟩
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqmem
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hq₁, hleft⟩,
        Finset.mem_filter.mpr ⟨hq₂, heq.symm.trans hleft⟩⟩
    · intro hqmem
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqmem
      obtain ⟨hq₁mem, hq₁dist⟩ := Finset.mem_filter.mp hq₁
      obtain ⟨hq₂mem, hq₂dist⟩ := Finset.mem_filter.mp hq₂
      exact ⟨⟨Finset.mem_product.mpr ⟨hq₁mem, hq₂mem⟩,
        hq₁dist.trans hq₂dist.symm⟩, hq₁dist⟩
  rw [hfiber]
  simp [Finset.card_product, pow_two]

/-- The equal-distance quadruples which arise from a common translation of
the two ordered segments. -/
noncomputable def translationQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact (orderedDistanceQuadruples P).filter fun q ↦
    ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2

/-- The elementary exceptional-case estimate in the Elekes--Sharir
reduction: a translation quadruple is determined by its first three
points. -/
theorem card_translationQuadruples_le (P : Finset Point) :
    (translationQuadruples P).card ≤ P.card ^ 3 := by
  classical
  let forgetLast : ((Point × Point) × (Point × Point)) →
      ((Point × Point) × Point) := fun q ↦ (q.1, q.2.1)
  have hmaps : Set.MapsTo forgetLast (translationQuadruples P)
      ((P.product P).product P) := by
    intro q hq
    unfold translationQuadruples at hq
    have hQ := (Finset.mem_filter.mp hq).1
    unfold orderedDistanceQuadruples at hQ
    have hsegments := (Finset.mem_filter.mp hQ).1
    obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hsegments
    have hfirst' : q.1.1 ∈ P ∧ q.1.2 ∈ P := by
      have h := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using hfirst)
      exact ⟨h.1, h.2.1⟩
    have hsecond' : q.2.1 ∈ P ∧ q.2.2 ∈ P := by
      have h := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using hsecond)
      exact ⟨h.1, h.2.1⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_product.mpr ⟨hfirst'.1, hfirst'.2⟩, hsecond'.1⟩
  have hinj : Set.InjOn forgetLast (translationQuadruples P) := by
    intro q hq r hr heq
    unfold translationQuadruples at hq hr
    have htransq : ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2 := by
      exact (Finset.mem_filter.mp hq).2
    have htransr : ES.IsTranslation r.1.1 r.1.2 r.2.1 r.2.2 := by
      exact (Finset.mem_filter.mp hr).2
    change (q.1, q.2.1) = (r.1, r.2.1) at heq
    have hparts := Prod.ext_iff.mp heq
    have hfirst : q.1 = r.1 := hparts.1
    have hthird : q.2.1 = r.2.1 := hparts.2
    have hlast : q.2.2 = r.2.2 := by
      apply PiLp.ext
      intro i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · dsimp [ES.IsTranslation] at htransq htransr
        rw [hfirst, hthird] at htransq
        exact sub_left_injective (htransq.1.symm.trans htransr.1)
      · dsimp [ES.IsTranslation] at htransq htransr
        rw [hfirst, hthird] at htransq
        exact sub_left_injective (htransq.2.symm.trans htransr.2)
    apply Prod.ext hfirst
    exact Prod.ext hthird hlast
  calc
    (translationQuadruples P).card ≤ ((P.product P).product P).card :=
      Finset.card_le_card_of_injOn forgetLast hmaps hinj
    _ = P.card ^ 3 := by simp [pow_succ]

/-- The nontranslation part of the equal-distance quadruple set. -/
noncomputable def incidentQuadruples (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact (orderedDistanceQuadruples P).filter fun q ↦
    ¬ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2

/-- Every quadruple in the nontranslation part gives an intersection of the
two Elekes--Sharir lines indexed by `(a,c)` and `(b,d)`. -/
theorem intersects_of_mem_incidentQuadruples {P : Finset Point}
    {q : (Point × Point) × (Point × Point)}
    (hq : q ∈ incidentQuadruples P) :
    ES.Intersects q.1.1 q.2.1 q.1.2 q.2.2 := by
  classical
  unfold incidentQuadruples at hq
  obtain ⟨hQ, hnot⟩ := Finset.mem_filter.mp hq
  unfold orderedDistanceQuadruples at hQ
  have hdist := (Finset.mem_filter.mp hQ).2
  apply ES.intersects_of_sqDist_eq_of_not_translation
  · exact ES.sqDist_eq_iff_dist_eq.mpr hdist
  · exact hnot

/-- The translation and incidence cases partition all equal-distance
quadruples. -/
theorem card_translation_add_incident (P : Finset Point) :
    (translationQuadruples P).card + (incidentQuadruples P).card =
      (orderedDistanceQuadruples P).card := by
  classical
  unfold translationQuadruples incidentQuadruples
  exact Finset.card_filter_add_card_filter_not
    (s := orderedDistanceQuadruples P)
    (fun q ↦ ES.IsTranslation q.1.1 q.1.2 q.2.1 q.2.2)

/-! ## Intersecting pairs in the Elekes--Sharir line family -/

/-- Indices of the `|P|^2` Elekes--Sharir lines. -/
noncomputable def lineIndices (P : Finset Point) : Finset (Point × Point) :=
  P.product P

/-- Ordered pairs of distinct indexed Elekes--Sharir lines which meet. -/
noncomputable def intersectingLinePairs (P : Finset Point) :
    Finset ((Point × Point) × (Point × Point)) := by
  classical
  exact ((lineIndices P).product (lineIndices P)).filter fun l ↦
    l.1 ≠ l.2 ∧ ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2

@[simp]
theorem card_lineIndices (P : Finset Point) :
    (lineIndices P).card = P.card ^ 2 := by
  simp [lineIndices, pow_two]

/-! ### Rich points of the line family -/

/-- The unique common point selected for an intersecting pair of normalized
Elekes--Sharir lines.  The fallback value is irrelevant off the incidence
relation. -/
noncomputable def linePairIntersection
    (l : (Point × Point) × (Point × Point)) : ES.Space3 := by
  classical
  exact if h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2 then
    Classical.choose h
  else 0

theorem linePairIntersection_on_first
    {l : (Point × Point) × (Point × Point)}
    (h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2) :
    ES.OnLine l.1.1 l.1.2 (linePairIntersection l) := by
  classical
  simp only [linePairIntersection, dif_pos h]
  exact (Classical.choose_spec h).1

theorem linePairIntersection_on_second
    {l : (Point × Point) × (Point × Point)}
    (h : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2) :
    ES.OnLine l.2.1 l.2.2 (linePairIntersection l) := by
  classical
  simp only [linePairIntersection, dif_pos h]
  exact (Classical.choose_spec h).2

/-- Lines of the indexed family passing through a point of parameter
three-space. -/
noncomputable def linesThrough (P : Finset Point) (x : ES.Space3) :
    Finset (Point × Point) := by
  classical
  exact (lineIndices P).filter fun l ↦ ES.OnLine l.1 l.2 x

/-- The finite set of actual intersection points of distinct indexed lines. -/
noncomputable def intersectionPoints (P : Finset Point) : Finset ES.Space3 := by
  classical
  exact (intersectingLinePairs P).image linePairIntersection

theorem mem_linesThrough_iff {P : Finset Point} {x : ES.Space3}
    {l : Point × Point} :
    l ∈ linesThrough P x ↔ l ∈ lineIndices P ∧ ES.OnLine l.1 l.2 x := by
  classical
  simp [linesThrough]

/-- At a fixed rigid-motion parameter there is at most one indexed line for
each first endpoint.  Consequently every rich point of the Elekes--Sharir
family is incident to at most `|P|` lines. -/
theorem card_linesThrough_le (P : Finset Point) (x : ES.Space3) :
    (linesThrough P x).card ≤ P.card := by
  classical
  let S := linesThrough P x
  have hinj : Set.InjOn Prod.fst (S : Set (Point × Point)) := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hint : ES.Intersects a.1 a.2 b.1 b.2 :=
      ⟨x, ha'.2, hb'.2⟩
    have hdist : dist a.1 b.1 = dist a.2 b.2 :=
      ES.sqDist_eq_iff_dist_eq.mp (ES.sqDist_eq_of_intersects hint)
    have hsecond : a.2 = b.2 := by
      apply dist_eq_zero.mp
      simpa [hab] using hdist.symm
    exact Prod.ext hab hsecond
  have hcard : (S.image Prod.fst).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hl).1).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

/-- A fiber of the intersection-point map is exactly the ordered off-diagonal
of the lines through that point.  This uses uniqueness of the intersection of
two distinct normalized lines. -/
theorem intersectionPoint_fiber (P : Finset Point) (x : ES.Space3) :
    (intersectingLinePairs P).filter (fun l ↦ linePairIntersection l = x) =
      (linesThrough P x).offDiag := by
  classical
  ext l
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨hl, hlx⟩
    have hdata := Finset.mem_filter.mp hl
    have hmem := Finset.mem_product.mp hdata.1
    refine ⟨Finset.mem_filter.mpr ⟨hmem.1, ?_⟩,
      Finset.mem_filter.mpr ⟨hmem.2, ?_⟩, hdata.2.1⟩
    · rw [← hlx]
      exact linePairIntersection_on_first hdata.2.2
    · rw [← hlx]
      exact linePairIntersection_on_second hdata.2.2
  · rintro ⟨hl₁, hl₂, hne⟩
    have hl₁' := Finset.mem_filter.mp hl₁
    have hl₂' := Finset.mem_filter.mp hl₂
    have hint : ES.Intersects l.1.1 l.1.2 l.2.1 l.2.2 :=
      ⟨x, hl₁'.2, hl₂'.2⟩
    have hlmem : l ∈ intersectingLinePairs P := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hl₁'.1, hl₂'.1⟩, hne, hint⟩
    refine ⟨hlmem, ?_⟩
    exact ES.intersection_unique hne
      (linePairIntersection_on_first hint)
      (linePairIntersection_on_second hint) hl₁'.2 hl₂'.2

/-- Exact rich-point decomposition of the ordered intersecting-pair count. -/
theorem card_intersectingLinePairs_eq_sum_rich (P : Finset Point) :
    (intersectingLinePairs P).card =
      ∑ x ∈ intersectionPoints P,
        (linesThrough P x).card * ((linesThrough P x).card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_image linePairIntersection (intersectingLinePairs P)]
  change _ = ∑ x ∈ (intersectingLinePairs P).image linePairIntersection, _
  apply Finset.sum_congr rfl
  intro x hx
  rw [intersectionPoint_fiber, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Intersection points incident to at least `k` indexed lines. -/
noncomputable def richIntersectionPoints (P : Finset Point) (k : ℕ) :
    Finset ES.Space3 := by
  classical
  exact (intersectionPoints P).filter fun x ↦ k ≤ (linesThrough P x).card

/-- The presentation-level rich-point set is definitionally the same as the
generic finite line-family construction used in the incidence induction. -/
theorem richIntersectionPoints_eq_lineFamilyRichPoints
    (P : Finset Point) (k : ℕ) :
    richIntersectionPoints P k =
      LineFamilies.richPoints (P.product P) k := by
  rfl

private theorem sum_two_mul_pred (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), 2 * (k - 1) = r * (r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      cases r with
      | zero => simp
      | succ s =>
          simp only [Nat.add_sub_cancel, Nat.succ_sub_one]
          ring

private theorem sum_two_mul_pred_truncate {r n : ℕ} (hrn : r ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (if k ≤ r then 2 * (k - 1) else 0) = r * (r - 1) := by
  calc
    ∑ k ∈ Finset.range (n + 1),
          (if k ≤ r then 2 * (k - 1) else 0) =
        ∑ k ∈ Finset.range (r + 1),
          (if k ≤ r then 2 * (k - 1) else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hrn))
      intro k hkn hkr
      simp only [Finset.mem_range] at hkn hkr
      simp [Nat.not_le.mpr (by omega : r < k)]
    _ = ∑ k ∈ Finset.range (r + 1), 2 * (k - 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [show k ≤ r by omega]
    _ = r * (r - 1) := sum_two_mul_pred r

private theorem sum_indicator_eq_mul_card {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x ∈ S, if p x then c else 0) = c * (S.filter p).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases hpa : p a
      · rw [Finset.filter_insert]
        simp [ha, hpa, ih, Nat.mul_succ, Nat.add_comm]
      · rw [Finset.filter_insert]
        simp [ha, hpa, ih]

/-- Layer-cake identity for line intersections.  It reduces the desired pair
bound to estimates for `k`-rich points, with the exact weight `2(k-1)`. -/
theorem card_intersectingLinePairs_eq_sum_richLevels (P : Finset Point) :
    (intersectingLinePairs P).card =
      ∑ k ∈ Finset.range (P.card + 1),
        2 * (k - 1) * (richIntersectionPoints P k).card := by
  classical
  rw [card_intersectingLinePairs_eq_sum_rich]
  calc
    ∑ x ∈ intersectionPoints P,
          (linesThrough P x).card * ((linesThrough P x).card - 1) =
        ∑ x ∈ intersectionPoints P,
          ∑ k ∈ Finset.range (P.card + 1),
            if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (sum_two_mul_pred_truncate (card_linesThrough_le P x)).symm
    _ = ∑ k ∈ Finset.range (P.card + 1),
          ∑ x ∈ intersectionPoints P,
            if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (P.card + 1),
          2 * (k - 1) * (richIntersectionPoints P k).card := by
      apply Finset.sum_congr rfl
      intro k hk
      change (∑ x ∈ intersectionPoints P,
          if k ≤ (linesThrough P x).card then 2 * (k - 1) else 0) =
        2 * (k - 1) *
          ((intersectionPoints P).filter fun x ↦
            k ≤ (linesThrough P x).card).card
      exact sum_indicator_eq_mul_card (intersectionPoints P)
        (fun x ↦ k ≤ (linesThrough P x).card) (2 * (k - 1))

private theorem intersectingLinePairs_le_of_rich_point_bound_scale
    (P : Finset Point) (X : ℝ) (hX : 0 ≤ X)
    (hRich : ∀ k : ℕ, 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤ X / (k : ℝ) ^ 2) :
    ((intersectingLinePairs P).card : ℝ) ≤
      2 * X * (1 + Real.log P.card) := by
  classical
  have hterm : ∀ k ∈ Finset.range (P.card + 1),
      2 * ((k - 1 : ℕ) : ℝ) * ((richIntersectionPoints P k).card : ℝ) ≤
        if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := by
    intro k hk
    split_ifs with hk2
    · have hkpos_nat : 0 < k := by omega
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
      have hkm1 : (1 : ℕ) ≤ k := by omega
      push_cast [Nat.cast_sub hkm1]
      calc
        2 * ((k : ℝ) - 1) * (richIntersectionPoints P k).card ≤
            2 * (k : ℝ) * (richIntersectionPoints P k).card := by
          gcongr <;> linarith
        _ ≤ 2 * (k : ℝ) * (X / (k : ℝ) ^ 2) := by
          gcongr
          exact hRich k hk2
        _ = 2 * X * (k : ℝ)⁻¹ := by
          field_simp
    · have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl <;> simp
  have hsum :
      ((∑ k ∈ Finset.range (P.card + 1),
          2 * (k - 1) * (richIntersectionPoints P k).card : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := by
    push_cast
    exact Finset.sum_le_sum fun k hk ↦ hterm k hk
  have hfilter :
      (Finset.range (P.card + 1)).filter (fun k ↦ 2 ≤ k) =
        Finset.Icc 2 P.card := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hrange :
      (∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0) =
        2 * X * ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ := by
    rw [← hfilter]
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum]
  have hsubset : Finset.Icc 2 P.card ⊆ Finset.Icc 1 P.card := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  have hinv_nonneg : ∀ k ∈ Finset.Icc 1 P.card, 0 ≤ (k : ℝ)⁻¹ := by
    intro k hk
    positivity
  have hpartial :
      ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ ≤
        ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro k hk1 hk2
      positivity)
  have hharmonic :
      ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ ≤
        1 + Real.log P.card := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast] using harmonic_le_one_add_log P.card
  rw [card_intersectingLinePairs_eq_sum_richLevels]
  calc
    ((∑ k ∈ Finset.range (P.card + 1),
        2 * (k - 1) * (richIntersectionPoints P k).card : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.range (P.card + 1),
          if 2 ≤ k then 2 * X * (k : ℝ)⁻¹ else 0 := hsum
    _ = 2 * X * ∑ k ∈ Finset.Icc 2 P.card, (k : ℝ)⁻¹ := hrange
    _ ≤ 2 * X * ∑ k ∈ Finset.Icc 1 P.card, (k : ℝ)⁻¹ := by
      gcongr
    _ ≤ 2 * X * (1 + Real.log P.card) := by
      gcongr

/-- The same harmonic summation with a real-power scale; this is the form
used by Guth's epsilon-loss low-degree partitioning theorem. -/
theorem intersectingLinePairs_le_of_rich_point_bound_rpow
    (A : ℝ) (hA : 0 < A) (δ : ℝ)
    (hRich : ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
      ((richIntersectionPoints P k).card : ℝ) ≤
        A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2)
    (P : Finset Point) :
    ((intersectingLinePairs P).card : ℝ) ≤
      2 * A * (P.card : ℝ) ^ (3 + δ) *
        (1 + Real.log P.card) := by
  have h := intersectingLinePairs_le_of_rich_point_bound_scale P
    (A * (P.card : ℝ) ^ (3 + δ))
    (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
    (fun k hk ↦ hRich P k hk)
  convert h using 1 <;> ring

/-- Unshuffle a pair of ordered planar segments into the corresponding pair
of Elekes--Sharir line indices. -/
def toLinePair (q : (Point × Point) × (Point × Point)) :
    (Point × Point) × (Point × Point) :=
  ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- The inverse coordinate shuffle. -/
def ofLinePair (l : (Point × Point) × (Point × Point)) :
    (Point × Point) × (Point × Point) :=
  ((l.1.1, l.2.1), (l.1.2, l.2.2))

@[simp]
theorem ofLinePair_toLinePair
    (q : (Point × Point) × (Point × Point)) :
    ofLinePair (toLinePair q) = q := by
  rcases q with ⟨⟨a, b⟩, c, d⟩
  rfl

@[simp]
theorem toLinePair_ofLinePair
    (l : (Point × Point) × (Point × Point)) :
    toLinePair (ofLinePair l) = l := by
  rcases l with ⟨⟨a, c⟩, b, d⟩
  rfl

/-- Nontranslation distance quadruples are exactly ordered pairs of
distinct intersecting Elekes--Sharir lines. -/
theorem card_incidentQuadruples_eq_intersectingLinePairs (P : Finset Point) :
    (incidentQuadruples P).card = (intersectingLinePairs P).card := by
  classical
  apply Finset.card_bij (fun q _ ↦ toLinePair q)
  · intro q hq
    unfold incidentQuadruples at hq
    have hQ := (Finset.mem_filter.mp hq).1
    unfold orderedDistanceQuadruples at hQ
    have hsegments := (Finset.mem_filter.mp hQ).1
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hsegments
    have h₁' := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using h₁)
    have h₂' := Finset.mem_offDiag.mp (by simpa only [orderedSegments] using h₂)
    unfold intersectingLinePairs
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_product.mpr
      · exact ⟨h₁'.1, h₂'.1⟩
      · exact ⟨h₁'.2.1, h₂'.2.1⟩
    · constructor
      · intro heq
        exact h₁'.2.2 (congrArg Prod.fst heq)
      · exact intersects_of_mem_incidentQuadruples hq
  · intro q hq r hr heq
    exact ofLinePair_toLinePair q ▸ ofLinePair_toLinePair r ▸
      congrArg ofLinePair heq
  · intro l hl
    refine ⟨ofLinePair l, ?_, toLinePair_ofLinePair l⟩
    unfold intersectingLinePairs at hl
    obtain ⟨hlines, hne, hint⟩ := Finset.mem_filter.mp hl
    obtain ⟨hl₁, hl₂⟩ := Finset.mem_product.mp hlines
    unfold lineIndices at hl₁ hl₂
    obtain ⟨ha, hc⟩ := Finset.mem_product.mp hl₁
    obtain ⟨hb, hd⟩ := Finset.mem_product.mp hl₂
    have hdist : dist l.1.1 l.2.1 = dist l.1.2 l.2.2 :=
      ES.sqDist_eq_iff_dist_eq.mp (ES.sqDist_eq_of_intersects hint)
    have hab : l.1.1 ≠ l.2.1 := by
      intro heq
      have hcd : l.1.2 = l.2.2 := by
        apply dist_eq_zero.mp
        simpa [heq] using hdist.symm
      exact hne (Prod.ext heq hcd)
    have hcd : l.1.2 ≠ l.2.2 := by
      intro heq
      have hab' : l.1.1 = l.2.1 := by
        apply dist_eq_zero.mp
        simpa [heq] using hdist
      exact hne (Prod.ext hab' heq)
    unfold incidentQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold orderedDistanceQuadruples
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · simpa only [orderedSegments, Finset.mem_offDiag] using ⟨ha, hb, hab⟩
        · simpa only [orderedSegments, Finset.mem_offDiag] using ⟨hc, hd, hcd⟩
      · exact hdist
    · intro htrans
      exact hne (Prod.ext (ES.eq_of_intersects_of_translation hint htrans).1
        (ES.eq_of_intersects_of_translation hint htrans).2)

private theorem two_mul_card_sym2_image_of_swap_mem
    {α : Type*} [DecidableEq α] (S : Finset (α × α))
    (hswap : ∀ p ∈ S, p.swap ∈ S)
    (hne : ∀ p ∈ S, p.1 ≠ p.2) :
    2 * (S.image Sym2.mk.uncurry).card = S.card := by
  rw [Finset.card_eq_sum_card_image (Sym2.mk.uncurry : α × α → Sym2 α) S]
  have hfiber : ∀ z ∈ S.image (Sym2.mk.uncurry : α × α → Sym2 α),
      (S.filter fun p ↦ Sym2.mk.uncurry p = z).card = 2 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hps : p.swap ∈ S := hswap p hp
    have hp_ne_swap : p ≠ p.swap := by
      intro h
      exact hne p hp (congrArg Prod.fst h)
    have hset :
        S.filter (fun q ↦ Sym2.mk.uncurry q = Sym2.mk.uncurry p) =
          {p, p.swap} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      change q ∈ S ∧ s(q.1, q.2) = s(p.1, p.2) ↔ q = p ∨ q = p.swap
      rw [Sym2.mk_eq_mk_iff]
      constructor
      · exact fun h ↦ h.2
      · rintro (rfl | rfl)
        · exact ⟨hp, Or.inl rfl⟩
        · exact ⟨hps, Or.inr rfl⟩
    rw [hset]
    simp [hp_ne_swap]
  rw [Finset.sum_const_nat hfiber]
  omega

theorem distanceMultiplicity_ordered (P : Finset Point) (u : ℝ) :
    orderedDistanceMultiplicity P u = 2 * distanceMultiplicity P u := by
  classical
  let S := (orderedSegments P).filter fun e ↦ orderedDistance e = u
  have hswap : ∀ p ∈ S, p.swap ∈ S := by
    rintro ⟨p, q⟩ hpq
    change (p, q) ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u) at hpq
    change (q, p) ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u)
    rw [Finset.mem_filter] at hpq ⊢
    have hpqP : (p, q) ∈ P.offDiag := by
      simpa only [orderedSegments] using hpq.1
    have hpqData : p ∈ P ∧ q ∈ P ∧ p ≠ q := by
      simpa only [Finset.mem_offDiag] using hpqP
    refine ⟨?_, ?_⟩
    · simpa only [orderedSegments, Finset.mem_offDiag] using
        ⟨hpqData.2.1, hpqData.1, hpqData.2.2.symm⟩
    · simpa only [orderedDistance, dist_comm] using hpq.2
  have hne : ∀ p ∈ S, p.1 ≠ p.2 := by
    intro p hp
    change p ∈ (orderedSegments P).filter (fun e ↦ orderedDistance e = u) at hp
    have hpSeg : p ∈ P.offDiag := by
      simpa only [orderedSegments] using (Finset.mem_filter.mp hp).1
    exact (Finset.mem_offDiag.mp hpSeg).2.2
  have himage :
      S.image Sym2.mk.uncurry =
        (pointPairs P).filter fun e ↦ pairDistance e = u := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩, (Finset.mem_filter.mp hp).2⟩
    · intro hz
      obtain ⟨hzpair, hzdist⟩ := Finset.mem_filter.mp hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzpair
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hzdist⟩, rfl⟩
  have htwo := two_mul_card_sym2_image_of_swap_mem S hswap hne
  rw [himage] at htwo
  exact htwo.symm

theorem orderedDistanceEnergy_eq_four_mul (P : Finset Point) :
    orderedDistanceEnergy P = 4 * distanceEnergy P := by
  classical
  have himage :
      (orderedSegments P).image orderedDistance = distances P := by
    ext u
    simp only [orderedSegments, orderedDistance, distances, pointPairs,
      Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s(p.1, p.2), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  simp only [orderedDistanceEnergy, distanceEnergy, himage,
    distanceMultiplicity_ordered]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-! ## The exact asymptotic statement -/

/-- The quantifiers in Erdős Problem 95.  The power on the right is real
exponentiation; in particular, the constant is uniform in the finite point
set and depends only on `ε`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
    (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε)

/-- Once the geometric estimate for distinct intersecting Elekes--Sharir
line pairs is available, the translation estimate and the exact coordinate
shuffle give Erdős 95. -/
theorem statement_of_intersecting_line_pair_bound
    (hInc : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ P : Finset Point,
      ((intersectingLinePairs P).card : ℝ) ≤
        B * (P.card : ℝ) ^ (3 + ε)) :
    Statement := by
  intro ε hε
  obtain ⟨B, hB, hbound⟩ := hInc ε hε
  refine ⟨B + 1, by positivity, ?_⟩
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    have hexp : 0 < 3 + ε := by linarith
    simp [distanceEnergy, distances, pointPairs, distanceMultiplicity,
      Real.zero_rpow hexp.ne']
  have hnpos : 0 < (P.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hP)
  have hnone : 1 ≤ (P.card : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hP)
  have hexp : (3 : ℝ) ≤ 3 + ε := by linarith
  have hpow : (P.card : ℝ) ^ (3 : ℕ) ≤ (P.card : ℝ) ^ (3 + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hnone hexp
  have htranslation : ((translationQuadruples P).card : ℝ) ≤
      (P.card : ℝ) ^ (3 + ε) := by
    calc
      ((translationQuadruples P).card : ℝ) ≤ (P.card ^ 3 : ℕ) := by
        exact_mod_cast card_translationQuadruples_le P
      _ = (P.card : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (P.card : ℝ) ^ (3 + ε) := hpow
  have hquad : ((orderedDistanceQuadruples P).card : ℝ) ≤
      (B + 1) * (P.card : ℝ) ^ (3 + ε) := by
    rw [← card_translation_add_incident P]
    push_cast
    rw [card_incidentQuadruples_eq_intersectingLinePairs]
    nlinarith [hbound P, htranslation,
      Real.rpow_nonneg (by positivity : 0 ≤ (P.card : ℝ)) (3 + ε)]
  calc
    (distanceEnergy P : ℝ) ≤ (orderedDistanceQuadruples P).card := by
      rw [card_orderedDistanceQuadruples, orderedDistanceEnergy_eq_four_mul]
      push_cast
      have hnonneg : 0 ≤ (distanceEnergy P : ℝ) := by positivity
      linarith
    _ ≤ (B + 1) * (P.card : ℝ) ^ (3 + ε) := hquad

/-- Guth's shorter low-degree argument gives a loss in the power of `n`.
Taking half of the requested epsilon here leaves enough room to absorb the
harmonic logarithm, and yields the exact quantifiers of `Statement`. -/
theorem statement_of_epsilon_rich_point_bound
    (hRich : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
      ∀ (P : Finset Point) (k : ℕ), 2 ≤ k →
        ((richIntersectionPoints P k).card : ℝ) ≤
          A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2) :
    Statement := by
  apply statement_of_intersecting_line_pair_bound
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hrich⟩ := hRich δ hδ
  refine ⟨2 * A * (1 + δ⁻¹), by positivity, ?_⟩
  intro P
  by_cases hP : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP
    subst P
    have hexp : 0 < 3 + ε := by linarith
    rw [show (intersectingLinePairs ∅).card = 0 by
      simp [intersectingLinePairs, lineIndices]]
    push_cast
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow hexp.ne']
    positivity
  have hnpos : 0 < (P.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hP
  have hnone : 1 ≤ (P.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hP
  have hpowone : 1 ≤ (P.card : ℝ) ^ δ :=
    Real.one_le_rpow hnone hδ.le
  have hlog : Real.log P.card ≤ (P.card : ℝ) ^ δ / δ :=
    Real.log_natCast_le_rpow_div P.card hδ
  have hlogpow :
      1 + Real.log P.card ≤ (P.card : ℝ) ^ δ * (1 + δ⁻¹) := by
    calc
      1 + Real.log P.card ≤
          (P.card : ℝ) ^ δ + (P.card : ℝ) ^ δ / δ :=
        add_le_add hpowone hlog
      _ = (P.card : ℝ) ^ δ * (1 + δ⁻¹) := by
        rw [div_eq_mul_inv]
        ring
  have hpairs :=
    intersectingLinePairs_le_of_rich_point_bound_rpow A hA δ hrich P
  calc
    ((intersectingLinePairs P).card : ℝ) ≤
        2 * A * (P.card : ℝ) ^ (3 + δ) *
          (1 + Real.log P.card) := hpairs
    _ ≤ 2 * A * (P.card : ℝ) ^ (3 + δ) *
        ((P.card : ℝ) ^ δ * (1 + δ⁻¹)) := by
      gcongr
    _ = (2 * A * (1 + δ⁻¹)) * (P.card : ℝ) ^ (3 + ε) := by
      have hadd : (3 : ℝ) + ε = (3 + δ) + δ := by
        dsimp [δ]
        ring
      have hpow : (P.card : ℝ) ^ (3 + ε) =
          (P.card : ℝ) ^ (3 + δ) * (P.card : ℝ) ^ δ := by
        rw [hadd, Real.rpow_add hnpos]
      rw [hpow]
      ring

/-- Erdős Problem 95, resolved via the Guth--Katz/Elekes--Sharir incidence
method and Guth's epsilon-loss polynomial-partitioning theorem. -/
theorem erdos_95 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
      (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε) := by
  apply statement_of_epsilon_rich_point_bound
  intro δ hδ
  obtain ⟨A, hA, hrich⟩ :=
    SpecialRichPoints.full_family_rich_point_bound δ hδ
  refine ⟨A, hA, ?_⟩
  intro P k hk
  rw [richIntersectionPoints_eq_lineFamilyRichPoints]
  exact hrich P k hk

end

#print axioms erdos_95
-- 'Erdos95.erdos_95' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos95
